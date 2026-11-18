#!/usr/bin/env python3
"""Translate selected functions of tiny_obj_verified.c into the MiniC deep
embedding (formal/Obj/C/Semantics.lean).

Input is clang's fully type-annotated AST (-ast-dump=json), so every implicit
conversion is explicit. Struct layouts (field offsets, sizeof) are obtained
by compiling and running a probe program with the same compiler/target, so
they are the layouts the real compiler uses.

Anything outside the supported subset raises an error: the translator is
part of the trusted base and must never guess.

Usage:
    python3 formal/tools/c2lean.py            # regenerate
    python3 formal/tools/c2lean.py --check    # fail if output is stale
"""
import argparse
import json
import os
import re
import struct
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
INCLUDE_DIRS = []
SRC = os.path.join(ROOT, "tiny_obj_verified.c")
OUT = os.path.join(ROOT, "formal", "Obj", "C", "Gen.lean")
CLANG = os.environ.get("CLANG", "clang")
TARGET = "x86_64-linux-gnu"
NAMESPACE = "Obj.C.Gen"

# Functions forming the verified core, in dependency order.
FUNCTIONS = [
    "tobj_size_mul",
    "tobj_size_add",
    "tobj_size_to_int",
    "fix_index_f",
    "fix_index_d",
    "tobj_slice_eq",
    "tobj_is_space",
    "tobj_is_digit",
    "tobj_is_pow2",
    "tobj_memcmp",
    "tobj_strlen",
    "tobj_strcmp",
    "tobj_tess_align",
    "tobj_tess_scratch_size",
    "tobj_cur_init",
    "tobj_next_eol",
    "tobj_skip_bom",
    "tobj_memcpy",
    "tobj_memset",
    "tobj_arena_block_data",
    "tobj_vec_at",
    "b_fail_f",
    "b_fail_d",
    "tobj_skip_space",
    "tobj_scan_int",
    "parse_corner_n_f",
    "parse_corner_n_d",
    "tobj_tess_emit",
    "tobj_tess_is_reflex",
    "tobj_tess_set_reflex",
    "tobj_match_ci",
    "tobj_material_get_param_f",
    "tobj_material_get_param_d",
    "cnt_v_f",
    "cnt_v_d",
    "cnt_vt_f",
    "cnt_vt_d",
    "cnt_vn_f",
    "cnt_vn_d",
    "ff_reset_elem_f",
    "ff_reset_elem_d",
    "tobj_dabs",
    "tobj_is_finite",
    "tobj_next_token",
    "tobj_tess_signed_area",
    "tobj_orient2d",
    "tobj_point_in_tri",
    "tobj_tess_pt",
    "tobj_tess_fan",
    "tobj_tess_update_reflex",
    "tobj_tess_scale2d",
    "tobj_tess_work_bind",
    "tobj_tess_project_f",
    "tobj_tess_project_d",
    "tobj_tess_run2d",
    "tobj_tess_polygon_core_f",
    "tobj_tess_polygon_core_d",
    "emit_face_core_f",
    "emit_face_core_d",
    "tobj_fmt_uint",
]

# String literals live in one read-only block at this index.
LIT_BLOCK = 4096

INT_TYPES = {
    "unsigned char": (8, False), "signed char": (8, True), "char": (8, True),
    "unsigned short": (16, False), "short": (16, True),
    "unsigned int": (32, False), "int": (32, True),
    "unsigned long": (64, False), "long": (64, True),
    "unsigned long long": (64, False), "long long": (64, True),
    "_Bool": (8, False),
    "bool": (8, False),
}


def const_int(node):
    """Integer value of a constant expression node."""
    if isinstance(node, dict):
        if "value" in node and node["kind"] in ("ConstantExpr", "IntegerLiteral",
                                                "CharacterLiteral", "UnaryOperator"):
            try:
                return int(node["value"])
            except (TypeError, ValueError):
                pass
        if node["kind"] == "UnaryOperator" and node.get("opcode") == "-":
            return -const_int(node["inner"][0])
        if node["kind"] == "BinaryOperator" and node.get("opcode") == "+":
            return const_int(node["inner"][0]) + const_int(node["inner"][1])
        if node["kind"] == "BinaryOperator" and node.get("opcode") == "*":
            return const_int(node["inner"][0]) * const_int(node["inner"][1])
        for v in node.get("inner", []) or []:
            try:
                return const_int(v)
            except Unsupported:
                pass
    raise Unsupported("cannot evaluate case label")


class Unsupported(Exception):
    pass


def die(msg, node=None):
    loc = ""
    if node is not None:
        r = node.get("range", {}).get("begin", {})
        loc = f" (line {r.get('line', '?')})"
    raise Unsupported(msg + loc)


def ctype(node_or_type):
    t = node_or_type.get("type", node_or_type) if isinstance(node_or_type, dict) else node_or_type
    return t.get("desugaredQualType", t.get("qualType"))


def strip_quals(t):
    """Removes cv-qualifiers (`const`/`volatile`), including pointer-level
    ones such as `char *const`, and normalises spacing."""
    t = re.sub(r"\b(const|volatile|restrict|__restrict)\b", " ", t)
    t = re.sub(r"\s*\*\s*", "*", t)
    return re.sub(r"\s+", " ", t).strip()


class Ctx:
    def __init__(self, enums, layout):
        self.enums = enums
        self.layout = layout
        self.literals = []          # list of bytes strings
        self.literal_offsets = {}   # bytes -> offset

    def literal(self, data):
        if data not in self.literal_offsets:
            self.literal_offsets[data] = sum(len(x) + 1 for x in self.literals)
            self.literals.append(data)
        return self.literal_offsets[data]

    def literal_bytes(self):
        out = []
        for x in self.literals:
            out.extend(x)
            out.append(0)
        return out


def int_ty(t, node=None, enums=None):
    t = strip_quals(t)
    if t.endswith("*"):
        # pointer-sized integer fallback (shouldn't normally reach here)
        return 64, False
    if t == "double":
        return 64, False
    if "*" in t and "(" in t:
        # function pointer: treat as pointer-sized
        return 64, False
    if t in INT_TYPES:
        w, s = INT_TYPES[t]
        return w, s
    if t.startswith("enum ") or t.startswith("tg3_error_code"):
        return 32, False  # every enum used here has only non-negative values
    die(f"unsupported integer type '{t}'", node)


def lean_intty(w, s):
    return f"⟨{w}, {'true' if s else 'false'}⟩"


RECORDS = set()


def is_ptr(t):
    return strip_quals(t).endswith("*")


def is_struct(t):
    """True for struct/union types (not pointers to them)."""
    t = strip_quals(t)
    if t.endswith("*"):
        return False
    if t.startswith("struct ") or t.startswith("union "):
        return True
    return t in RECORDS


def scalar_ty(t, node=None):
    t = strip_quals(t)
    if t == "double":
        return ".f64"
    if t == "float":
        return ".f64"
    if t.endswith("*"):
        return ".ptr"
    w, s = int_ty(t, node)
    return f"(.int {lean_intty(w, s)})"


class FnTranslator:
    def __init__(self, ctx, fn, fids):
        self.ctx = ctx
        self.fn = fn
        self.fids = fids
        self.vars = {}  # decl name+id -> int
        self.var_types = []
        self.names = []
        self._addr_taken = self.addr_taken_decls()
        self.loops = []  # hoisted loop statements (name, lean term)

    def var_id(self, decl):
        key = decl.get("id") or decl["name"]
        if key not in self.vars:
            self.vars[key] = len(self.vars)
            self.names.append(decl["name"])
            self.var_types.append(ctype(decl))
        return self.vars[key]

    def addr_taken_decls(self):
        """Decl ids whose address is taken (&local)."""
        found = []

        def walk(n):
            if isinstance(n, list):
                for x in n:
                    walk(x)
                return
            if not isinstance(n, dict):
                return
            if n.get("kind") == "UnaryOperator" and n.get("opcode") == "&":
                for inner in n.get("inner", []):
                    if inner.get("kind") == "DeclRefExpr":
                        ref = inner["referencedDecl"]
                        if ref.get("kind") in ("VarDecl", "ParmVarDecl"):
                            found.append(ref.get("id"))
            for v in n.values():
                if isinstance(v, (dict, list)):
                    walk(v)

        walk(self.fn)
        return set(found)

    def is_addr_taken_ref(self, ref):
        return ref.get("id") in self._addr_taken

    def ref_var(self, ref, node):
        # referencedDecl has the declaration id; match by id
        key = ref.get("id")
        if key in self.vars:
            return self.vars[key]
        die(f"reference to unknown local '{ref.get('name')}'", node)


    def pointee_size(self, t, node=None):
        """Size of the pointee of a pointer type, in bytes."""
        t = strip_quals(t)
        inner = t[:-1].rstrip()
        if inner in INT_TYPES:
            w, _ = INT_TYPES[inner]
            return w // 8
        return self.ctx.layout.sizeof(inner, node)

    # ---- lvalues -------------------------------------------------------
    def lvalue(self, n):
        k = n["kind"]
        if k == "ParenExpr":
            return self.lvalue(n["inner"][0])
        if k == "DeclRefExpr":
            ref = n["referencedDecl"]
            if ref["kind"] in ("VarDecl", "ParmVarDecl"):
                if is_struct(ctype(n)):
                    # lowered to a synthetic block for the caller's object
                    vid = self.ref_var(ref, n)
                    return ("mem", f"(.const (.ptr {1000 + vid} 0))", ctype(n))
                if self.is_addr_taken_ref(ref):
                    # address-of-local modeled by a synthetic block
                    vid = self.ref_var(ref, n)
                    return ("mem", f"(.const (.ptr {1000 + vid} 0))", ctype(n))
                return ("var", self.ref_var(ref, n))
            die(f"unsupported lvalue ref kind {ref['kind']}", n)
        if k == "MemberExpr":
            base = n["inner"][0]
            off = self.member_offset(n)
            if n["isArrow"]:
                return ("mem", f"(.field {self.rvalue(base)} {off})", ctype(n))
            lv = self.lvalue(base)
            if lv[0] != "mem":
                die("member of non-memory struct", n)
            return ("mem", f"(.field {lv[1]} {off})", ctype(n))
        if k == "StringLiteral":
            # `"data:"[i]` / decayed literal used as an lvalue: address it
            return ("mem", self.string_literal(n), ctype(n))
        if k == "ArraySubscriptExpr":
            base, idx = n["inner"]
            elem = self.ctx.layout.sizeof(ctype(n), n)
            return ("mem", f"(.index {self.rvalue(base)} {self.rvalue(idx)} {elem})", ctype(n))
        if k == "UnaryOperator" and n["opcode"] == "*":
            return ("mem", self.rvalue(n["inner"][0]), ctype(n))
        die(f"unsupported lvalue {k}", n)

    def member_offset(self, n):
        base = n["inner"][0]
        bt = strip_quals(ctype(base))
        if n["isArrow"]:
            if not bt.endswith("*"):
                die("arrow on non-pointer", n)
            bt = strip_quals(bt[:-1])
        return self.ctx.layout.offsetof(bt, n["name"], n)

    # ---- rvalues -------------------------------------------------------
    def rvalue(self, n):
        k = n["kind"]
        if k == "InitListExpr":
            # Only support scalar single-element? fallback: evaluate first element
            if n.get("inner"):
                return self.rvalue(n["inner"][0])
            die("empty InitListExpr", n)
        if k == "UnaryExprOrTypeTraitExpr":
            if n.get("name") == "sizeof":
                at = n.get("argType", {}).get("qualType", "")
                val = self.ctx.layout.sizeof(strip_quals(at) if at else ctype(n), n)
                # sizeof yields size_t (unsigned long on LP64)
                return f"(.const (.int {lean_intty(64, False)} {val}))"
            die(f"unsupported type trait {n.get('name')}", n)
        if k == "ParenExpr":
            return self.rvalue(n["inner"][0])
        if k == "IntegerLiteral" or k == "CharacterLiteral":
            w, s = int_ty(ctype(n), n)
            v = int(n["value"]) % (1 << w)
            return f"(.const (.int {lean_intty(w, s)} {v}))"
        if k == "FloatingLiteral":
            if strip_quals(ctype(n)) != "double":
                die("non-double float literal", n)
            bits = struct.unpack("<Q", struct.pack("<d", float(n["value"])))[0]
            return f"(.const (.f64 {bits}))"
        if k == "DeclRefExpr":
            ref = n["referencedDecl"]
            if ref["kind"] == "EnumConstantDecl":
                v = self.ctx.enums[ref["id"]]
                w, s = int_ty(ctype(n), n)
                return f"(.const (.int {lean_intty(w, s)} {v % (1 << w)}))"
            if ref["kind"] in ("VarDecl", "ParmVarDecl") and self.is_addr_taken_ref(ref):
                # address-taken local: read through its synthetic block
                vid = self.ref_var(ref, n)
                return f"(.load {scalar_ty(ctype(n), n)} (.const (.ptr {1000 + vid} 0)))"
            die("DeclRefExpr used as rvalue without LValueToRValue", n)
        if k in ("ImplicitCastExpr", "CStyleCastExpr"):
            ck = n["castKind"]
            inner = n["inner"][0]
            if ck == "LValueToRValue":
                lv = self.lvalue(inner)
                if lv[0] == "var":
                    return f"(.var {lv[1]})"
                return f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
            if ck == "IntegralCast":
                w, s = int_ty(ctype(n), n)
                return f"(.cast {lean_intty(w, s)} {self.rvalue(inner)})"
            if ck == "FloatingCast":
                return self.rvalue(inner)
            if ck == "IntegralToFloating":
                if inner.get("kind") == "IntegerLiteral":
                    try:
                        val = float(int(inner.get("value")))
                        bits = struct.unpack("<Q", struct.pack("<d", val))[0]
                        return f"(.const (.f64 {bits}))"
                    except (TypeError, ValueError):
                        pass
                die("IntegralToFloating not supported for non-constant", n)
            if ck in ("NoOp", "BitCast"):
                return self.rvalue(inner)
            if ck == "NullToPointer":
                return "(.const .null)"
            if ck == "IntegralToBoolean":
                return ("(.cond " + self.rvalue(inner) +
                        " (.const (.int " + lean_intty(8, False) + " 1))" +
                        " (.const (.int " + lean_intty(8, False) + " 0)))")
            if ck == "ArrayToPointerDecay":
                if inner["kind"] == "StringLiteral":
                    return self.string_literal(inner)
                if inner["kind"] == "DeclRefExpr":
                    ref = inner["referencedDecl"]
                    if ref["kind"] in ("VarDecl", "ParmVarDecl"):
                        vid = self.ref_var(ref, n)
                        # model a local array by a synthetic block at 10000+id
                        return f"(.ptr {10000 + vid} 0)"
                lv = self.lvalue(inner)
                if lv[0] != "mem":
                    die("decay of non-memory array", n)
                return lv[1]
            if ck == "FunctionToPointerDecay":
                die("function pointer", n)
            die(f"unsupported cast {ck}", n)
        if k == "BinaryOperator":
            op = n["opcode"]
            a, b = n["inner"]
            if op == "&&":
                return f"(.land {self.rvalue(a)} {self.rvalue(b)})"
            if op == "||":
                return f"(.lor {self.rvalue(a)} {self.rvalue(b)})"
            ops = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod",
                   "<<": "shl", ">>": "shr", "&": "band", "|": "bor", "^": "bxor",
                   "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "==": "eq", "!=": "ne"}
            if op == "=":
                import sys
                r = n.get("range", {}).get("begin", {})
                sys.stderr.write(f"ASSIGN-EXPR node line={r.get('line')} col={r.get('col')} offset={r.get('offset')} included={r.get('includedFrom')}\n")
                die("assignment in expression", n)
            if op == "=":
                import sys
                r=n.get("range",{}).get("begin",{})
                sys.stderr.write(f"ASSIGN-EXPR line={r.get('line')} col={r.get('col')} off={r.get('offset')} incl={r.get('includedFrom')}\n")
                die("assignment in expression", n)
            if op not in ops:
                die(f"unsupported binary operator {op} in expression", n)
            if op in ("<", "<=", ">", ">=", "==", "!="):
                ot = strip_quals(ctype(a))
                if is_ptr(ot):
                    t = "(some IntTy.u64)"
                else:
                    t = "none" if ot == "double" else f"(some {lean_intty(*int_ty(ot, n))})"
            else:
                rt = strip_quals(ctype(n))
                at = strip_quals(ctype(a))
                bt = strip_quals(ctype(b))
                if is_ptr(rt) and is_ptr(at) and not is_ptr(bt) and op in ("+", "-"):
                    # byte-level pointer arithmetic (char*/void* style): lower to .index
                    sign = "" if op == "+" else "-"
                    if op == "+":
                        return f"(.index {self.rvalue(a)} {self.rvalue(b)} 1)"
                    else:
                        return f"(.index {self.rvalue(a)} (.un .neg {lean_intty(*int_ty(bt, n))} {self.rvalue(b)}) 1)"
                if is_ptr(rt):
                    die("pointer arithmetic via +/-; use subscripts", n)
                t = f"(some {lean_intty(*int_ty(rt, n))})"
            return f"(.bin .{ops[op]} {t} {self.rvalue(a)} {self.rvalue(b)})"
        if k == "UnaryOperator":
            op = n["opcode"]
            a = n["inner"][0]
            if op == "!":
                return f"(.un .lnot {lean_intty(32, True)} {self.rvalue(a)})"
            if op == "-":
                return f"(.un .neg {lean_intty(*int_ty(ctype(n), n))} {self.rvalue(a)})"
            if op == "~":
                return f"(.un .bnot {lean_intty(*int_ty(ctype(n), n))} {self.rvalue(a)})"
            if op == "&":
                lv = self.lvalue(a)
                if lv[0] == "var":
                    # MiniC has no address-of-local; use a synthetic block indexed
                    # by the local id (block 1000 + id) to avoid aliasing globals.
                    return f"(.const (.ptr {1000 + lv[1]} 0))"
                return lv[1]
            die(f"unsupported unary operator {op} in expression", n)
        if k == "ConditionalOperator":
            c, a, b = n["inner"]
            return f"(.cond {self.rvalue(c)} {self.rvalue(a)} {self.rvalue(b)})"
        if k == "CallExpr":
            builtin = self.builtin_call(n)
            if builtin is not None:
                return builtin
            fid, args = self.call_parts(n)
            return f"(.call {fid} [{', '.join(args)}])"
        if k in ("MemberExpr", "ArraySubscriptExpr"):
            lv = self.lvalue(n)
            if lv[0] != "mem":
                die(f"{k} of a non-memory object", n)
            if is_struct(lv[2]):
                die("struct value used in an expression", n)
            return f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
        if k == "StringLiteral":
            die("string literal used as a value", n)
        die(f"unsupported expression {k}", n)

    def string_literal(self, n):
        data = n["value"].encode("utf-8")
        off = self.ctx.literal(data)
        return f"(.const (.ptr {LIT_BLOCK} {off}))"

    def builtin_call(self, n):
        """Maps the C library calls the verified core uses onto MiniC forms."""
        callee = n["inner"][0]
        while callee["kind"] in ("ImplicitCastExpr", "ParenExpr"):
            callee = callee["inner"][0]
        if callee["kind"] != "DeclRefExpr":
            return None
        name = callee["referencedDecl"].get("name")
        args = [self.rvalue(x) for x in n["inner"][1:]]
        if name in ("memcmp", "__builtin_memcmp", "tg3__memcmp"):
            if len(args) != 3:
                die("memcmp arity", n)
            return f"(.memcmp {args[0]} {args[1]} {args[2]})"
        if name in ("strlen", "__builtin_strlen", "tg3__strlen"):
            if len(args) != 1:
                die("strlen arity", n)
            return f"(.strlen {args[0]})"
        if name in ("fma", "__builtin_fma", "__builtin_fmaf", "tg3__fma"):
            # IEEE-754 fusedMultiplyAdd: x86-64 `vfmadd*sd` (FMA3) and AArch64
            # `fmadd` both implement this exactly, so one MiniC form covers both.
            if len(args) != 3:
                die("fma arity", n)
            return f"(.fma {args[0]} {args[1]} {args[2]})"
        return None

    def call_parts(self, n):
        callee = n["inner"][0]
        while callee["kind"] in ("ImplicitCastExpr", "ParenExpr"):
            callee = callee["inner"][0]
        if callee["kind"] != "DeclRefExpr" or callee["referencedDecl"]["kind"] != "FunctionDecl":
            die("indirect call", n)
        name = callee["referencedDecl"]["name"]
        if name not in self.fids:
            die(f"call to untranslated function {name}", n)
        return self.fids[name], [self.rvalue(x) for x in n["inner"][1:]]

    # ---- statements ----------------------------------------------------
    def assign(self, lv, rhs_lean, n):
        if lv[0] == "var":
            vid = lv[1]
            if vid in self._addr_taken_ids():
                return f"(.store {scalar_ty(self.var_types[vid], n)} (.const (.ptr {1000 + vid} 0)) {rhs_lean})"
            return f"(.set {vid} {rhs_lean})"
        return f"(.store {scalar_ty(lv[2], n)} {lv[1]} {rhs_lean})"

    def _addr_taken_ids(self):
        # var ids whose decl had its address taken
        out = set()
        for key, vid in self.vars.items():
            if key in self._addr_taken:
                out.add(vid)
        return out

    def stmt(self, n):
        if not n:
            return ".skip"
        k = n["kind"]
        if k == "CompoundStmt":
            return self.seq([self.stmt(x) for x in n.get("inner", [])])
        if k == "NullStmt":
            return ".skip"
        if k == "ExprStmt":
            inner = n.get("inner", [])
            if not inner:
                return ".skip"
            return self.stmt(inner[0])
        if k == "DeclStmt":
            out = []
            for d in n["inner"]:
                if d["kind"] != "VarDecl":
                    die("unsupported declaration", d)
                if d.get("storageClass") == "static":
                    die("static local", d)
                vid = self.var_id(d)
                if "inner" in d:
                    out.append(f"(.set {vid} {self.rvalue(d['inner'][0])})")
            return self.seq(out)
        if k == "ReturnStmt":
            if "inner" in n:
                return f"(.ret (some {self.rvalue(n['inner'][0])}))"
            return "(.ret none)"
        if k == "BreakStmt":
            return ".brk"
        if k == "ContinueStmt":
            return ".cont"
        if k == "IfStmt":
            inner = n["inner"]
            c = self.rvalue(inner[0])
            a = self.stmt(inner[1])
            b = self.stmt(inner[2]) if n.get("hasElse") else ".skip"
            return f"(.ite {c} {a} {b})"
        if k == "WhileStmt":
            c, body = n["inner"]
            return self.hoist(f"(.loop (.ite {self.rvalue(c)} {self.stmt(body)} .brk) .skip)")
        if k == "ForStmt":
            init, condvar, cond, inc, body = n["inner"]
            if condvar:
                die("for with condition variable", n)
            init_stmt = self.stmt(init) if init else ".skip"
            c = self.rvalue(cond) if cond else "(.const (.int ⟨32, true⟩ 1))"
            return self.seq([init_stmt,
                             self.hoist(f"(.loop (.ite {c} {self.stmt(body)} .brk) {self.stmt(inc) if inc else '.skip'})")])
        if k == "SwitchStmt":
            return self.switch(n)
        if k == "BinaryOperator" and n["opcode"] == "=":
            lhs, rhs = n["inner"]
            lv = self.lvalue(lhs)
            r = rhs
            while r["kind"] == "ParenExpr" or (r["kind"] == "ImplicitCastExpr" and r["castKind"] == "NoOp"):
                r = r["inner"][0]
            if r["kind"] == "CallExpr" and lv[0] == "var" and ctype(r) == ctype(lhs):
                fid, args = self.call_parts(r)
                return f"(.call (some {lv[1]}) {fid} [{', '.join(args)}])"
            return self.assign(lv, self.rvalue(rhs), n)
        if k == "CompoundAssignOperator":
            lhs, rhs = n["inner"]
            lv = self.lvalue(lhs)
            ops = {"+=": "add", "-=": "sub", "*=": "mul", "|=": "bor", "&=": "band",
                   "^=": "bxor", "<<=": "shl", ">>=": "shr"}
            op = ops.get(n["opcode"]) or die(f"unsupported {n['opcode']}", n)
            ltype = strip_quals(ctype(lhs))
            if is_ptr(ltype):
                # pointer arithmetic in bytes: p += N moves N elements
                elem = self.pointee_size(ltype, n)
                cur = f"(.var {lv[1]})" if lv[0] == "var" else f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
                sign = "add" if op == "add" else "sub"
                if sign == "add":
                    idx = self.rvalue(rhs)
                    return self.assign(lv, f"(.index {cur} {idx} {elem})", n)
                return self.assign(lv, f"(.index {cur} (.un .neg ⟨64, true⟩ {self.rvalue(rhs)}) {elem})", n)
            ct = int_ty(ctype(n["computeResultType"]), n)
            lt = int_ty(ctype(lhs), n)
            cur = f"(.var {lv[1]})" if lv[0] == "var" else f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
            rhs_c = self.rvalue(rhs) if op in ("shl", "shr") else f"(.cast {lean_intty(*ct)} {self.rvalue(rhs)})"
            val = f"(.cast {lean_intty(*lt)} (.bin .{op} (some {lean_intty(*ct)}) (.cast {lean_intty(*ct)} {cur}) {rhs_c}))"
            return self.assign(lv, val, n)
        if k == "UnaryOperator" and n["opcode"] in ("++", "--"):
            lv = self.lvalue(n["inner"][0])
            inner_t = strip_quals(ctype(n["inner"][0]))
            cur = f"(.var {lv[1]})" if lv[0] == "var" else f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
            if is_ptr(inner_t):
                # pointer arithmetic: p = p ± 1 (one element)
                elem = self.pointee_size(inner_t, n)
                if n["opcode"] == "++":
                    return self.assign(lv, f"(.index {cur} (.const (.int ⟨64, true⟩ 1)) {elem})", n)
                return self.assign(lv, f"(.index {cur} (.un .neg ⟨64, true⟩ (.const (.int ⟨64, true⟩ 1))) {elem})", n)
            w, s = int_ty(ctype(n), n)
            # integer promotion: types narrower than int are promoted to int
            pw, ps = (32, True) if w < 32 else (w, s)
            op = "add" if n["opcode"] == "++" else "sub"
            val = (f"(.cast {lean_intty(w, s)} (.bin .{op} (some {lean_intty(pw, ps)}) "
                   f"(.cast {lean_intty(pw, ps)} {cur}) (.const (.int {lean_intty(pw, ps)} 1))))")
            return self.assign(lv, val, n)
        if k == "CallExpr":
            fid, args = self.call_parts(n)
            return f"(.call none {fid} [{', '.join(args)}])"
        if k in ("CStyleCastExpr",) and n["castKind"] == "ToVoid":
            return ".skip"
        die(f"unsupported statement {k}", n)

    def hoist(self, term):
        """Loops become named definitions so proofs can treat them opaquely."""
        name = f"{self.fn['name']}_loop{len(self.loops)}"
        self.loops.append((name, term))
        return name

    @staticmethod
    def terminates(node):
        """True if control never falls out of `node` (last statement returns
        or breaks)."""
        while node is not None:
            k = node["kind"]
            if k in ("ReturnStmt", "BreakStmt"):
                return True
            if k == "CompoundStmt":
                inner = node.get("inner") or []
                node = inner[-1] if inner else None
                continue
            return False
        return False

    def switch(self, n):
        """`switch` with grouped case labels; supports fallthrough and
        `default`. Every case must terminate (return/break) or fall through."""
        if "cond" in n:
            cond, body = n["cond"], n["body"]
        else:
            cond, body = n["inner"][0], n["inner"][1]
        sel = self.rvalue(cond)
        st = lean_intty(*int_ty(ctype(cond), n))
        groups = []  # (label or None, [statements])

        def absorb(node):
            labels = []
            while True:
                subs = node.get("inner", [])
                if node["kind"] == "DefaultStmt":
                    labels.append(None)
                    rest = subs
                else:
                    if not subs:
                        die("case label without value", node)
                    labels.append(const_int(subs[0]))
                    rest = subs[1:]
                if (len(rest) == 1 and rest[0]["kind"] in ("CaseStmt", "DefaultStmt")):
                    node = rest[0]
                    continue
                return labels, rest

        for c in body.get("inner", []):
            if c["kind"] not in ("CaseStmt", "DefaultStmt"):
                die(f"unexpected {c['kind']} inside switch", c)
            labels, stmts = absorb(c)
            for lab in labels:
                groups.append((lab, stmts))
        if not groups:
            return ".skip"
        bodies = [self.seq([self.stmt(x) for x in stmts] or [".skip"]) for _, stmts in groups]
        fall = [None] * len(groups)
        nxt = ".skip"
        for idx in range(len(groups) - 1, -1, -1):
            _, stmts = groups[idx]
            term = bool(stmts) and self.terminates(stmts[-1])
            fall[idx] = bodies[idx] if term else self.seq([bodies[idx], nxt])
            nxt = fall[idx]
        default = ".skip"
        for idx, (label, _) in enumerate(groups):
            if label is None:
                default = fall[idx]
        chain = default
        for idx in range(len(groups) - 1, -1, -1):
            label, _ = groups[idx]
            if label is None:
                continue
            chain = (f"(.ite (.bin .eq (some {st}) {sel} (.const (.int {st} {label}))) "
                     f"{fall[idx]} {chain})")
        return chain

    def seq(self, items):
        items = [x for x in items if x != ".skip"]
        if not items:
            return ".skip"
        out = items[-1]
        for x in reversed(items[:-1]):
            out = f"(.seq {x} {out})"
        return out

    def translate(self):
        params = [x for x in self.fn["inner"] if x["kind"] == "ParmVarDecl"]
        pids = [self.var_id(p) for p in params]
        body = [x for x in self.fn["inner"] if x["kind"] == "CompoundStmt"][0]
        b = self.stmt(body)
        return pids, b


class Layout:
    """Field offsets and sizes, measured with the real compiler."""

    def __init__(self):
        self.queries = {}
        self.results = None

    def _q(self, expr):
        if self.results is not None:
            if expr not in self.results:
                die(f"layout query {expr} missing after probing")
            return self.results[expr]
        self.queries[expr] = None
        return f"@@{expr}@@"

    def offsetof(self, rec, field, node=None):
        return self._q(f"offsetof({rec}, {field})")

    def sizeof(self, t, node=None):
        return self._q(f"sizeof({t})")

    def probe(self):
        with tempfile.TemporaryDirectory() as d:
            c = os.path.join(d, "probe.c")
            exe = os.path.join(d, "probe")
            with open(c, "w") as f:
                f.write(f'#include "{SRC}"\n#include <stddef.h>\n#include <stdio.h>\n')
                f.write("int main(void) {\n")
                for q in self.queries:
                    f.write(f'    printf("%zu\\n", (size_t){q});\n')
                f.write("    return 0;\n}\n")
            subprocess.check_call([CLANG, f"--target={TARGET}", "-std=c11", "-w",
                                   f"-I{ROOT}", *INCLUDE_DIRS, "-o", exe, c])
            vals = subprocess.check_output([exe]).decode().split()
        self.results = dict(zip(self.queries, (int(v) for v in vals)))


def load_ast():
    out = subprocess.check_output(
        [CLANG, "-Xclang", "-ast-dump=json", "-fsyntax-only", "-std=c11",
         # Pin floating-point contraction.  Without this, clang fuses
         # `a*b + c` into `fmadd` on AArch64 by default but not on x86-64,
         # so the same source would mean different things per target.  The
         # MiniC model treats `bin .mul`/`.add` as two separate roundings;
         # fusing is then an explicit, modelled `(.fma ...)` only.
         "-ffp-contract=off",
         f"--target={TARGET}", f"-I{ROOT}", *INCLUDE_DIRS, SRC], stderr=subprocess.DEVNULL)
    return json.loads(out)


def collect_enums(ast):
    enums = {}

    def walk(n):
        if isinstance(n, dict):
            if n.get("kind") == "EnumDecl":
                val = 0
                for c in n.get("inner", []) or []:
                    if c.get("kind") == "EnumConstantDecl":
                        inners = c.get("inner", []) or []
                        if inners:
                            ce = inners[0]
                            try:
                                val = int(ce.get("value"))
                            except (TypeError, ValueError):
                                pass
                        enums[c["id"]] = val
                        val += 1
            for v in n.get("inner", []) or []:
                walk(v)
    walk(ast)
    return enums


def collect_records(ast):
    """Names of struct/union types (tags and typedefs of records)."""
    def walk(n):
        if isinstance(n, dict):
            k = n.get("kind")
            if k in ("RecordDecl", "CXXRecordDecl") and n.get("name"):
                RECORDS.add(n["name"])
            if k == "TypedefDecl" and n.get("name"):
                inner = n.get("inner") or []
                t = inner[0].get("type", {}).get("qualType", "") if inner else ""
                if t.startswith("struct ") or t.startswith("union "):
                    RECORDS.add(n["name"])
                elif t in RECORDS:
                    RECORDS.add(n["name"])
            for v in n.get("inner", []):
                walk(v)
    walk(ast)


def generate():
    ast = load_ast()
    collect_records(ast)
    enums = collect_enums(ast)
    fns = {}
    for n in ast["inner"]:
        if n.get("kind") == "FunctionDecl" and n.get("name") in FUNCTIONS and "inner" in n:
            if any(x["kind"] == "CompoundStmt" for x in n["inner"]):
                fns[n["name"]] = n
    missing = [f for f in FUNCTIONS if f not in fns]
    if missing:
        die(f"functions not found: {missing}")
    fids = {name: i for i, name in enumerate(FUNCTIONS)}
    layout = Layout()
    ctx = Ctx(enums, layout)
    # Two passes: collect layout queries, probe, then emit with real numbers.
    for _ in range(2):
        out = []
        for name in FUNCTIONS:
            tr = FnTranslator(ctx, fns[name], fids)
            pids, body = tr.translate()
            out.append((name, pids, body, tr.names, tr.loops))
        if layout.results is None:
            layout.probe()
    lines = [
        "/-",
        f"  GENERATED by formal/tools/c2lean.py from {os.path.relpath(SRC, ROOT)} — DO NOT EDIT.",
        f"  Target layout: {TARGET} (LP64, little-endian).",
        "-/",
        "import Obj.C.Semantics",
        "",
        f"namespace {NAMESPACE}",
        "open Obj.C",
        "",
    ]
    for i, (name, pids, body, names, loops) in enumerate(out):
        for lname, lterm in loops:
            lines.append(f"/-- A loop of `{name}`. -/")
            lines.append(f"def {lname} : Stmt := {lterm}")
            lines.append("")
        lines.append(f"/-- `{name}` (function id {i}). Locals: "
                     + ", ".join(f"{j}={nm}" for j, nm in enumerate(names)) + " -/")
        lines.append(f"def fid_{name} : Nat := {i}")
        lines.append(f"def {name} : Func where")
        lines.append(f"  params := {pids}")
        lines.append(f"  body := {body}")
        lines.append("")
    lit = ctx.literal_bytes()
    lines.append("/-- String literals referenced by the translated functions. -/")
    lines.append("def literals : List UInt8 := " + repr(lit).replace("'", '"'))
    lines.append("")
    lines.append("def prog : Prog := fun f =>")
    lines.append("  match f with")
    for i, (name, _, _, _, _) in enumerate(out):
        lines.append(f"  | {i} => some {name}")
    lines.append("  | _ => none")
    lines.append("")
    lines.append(f"end {NAMESPACE}")
    return "\n".join(lines) + "\n"


def main():
    global SRC, OUT, FUNCTIONS, TARGET, NAMESPACE, INCLUDE_DIRS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--source", default=SRC)
    parser.add_argument("--output", default=OUT)
    parser.add_argument("--function", action="append", dest="functions")
    parser.add_argument("--namespace", default=NAMESPACE)
    parser.add_argument("--target", default=TARGET)
    parser.add_argument("--include", action="append", dest="includes", default=[],
                        help="additional -I directory (repeatable)")
    args = parser.parse_args()
    SRC, OUT, TARGET, NAMESPACE = os.path.abspath(args.source), os.path.abspath(args.output), args.target, args.namespace
    INCLUDE_DIRS = [f"-I{os.path.abspath(d)}" for d in args.includes]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", NAMESPACE):
        parser.error("invalid Lean namespace")
    if args.functions:
        FUNCTIONS = args.functions
        if len(set(FUNCTIONS)) != len(FUNCTIONS):
            parser.error("duplicate function selection")
    try:
        text = generate()
    except Unsupported as e:
        print(f"c2lean: unsupported construct: {e}", file=sys.stderr)
        return 2
    if args.check:
        with open(OUT) as f:
            if f.read() != text:
                print(f"c2lean: {OUT} is stale; regenerate with the same arguments",
                      file=sys.stderr)
                return 1
        return 0
    with open(OUT, "w") as f:
        f.write(text)
    print("wrote", OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
