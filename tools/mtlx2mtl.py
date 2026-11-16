#!/usr/bin/env python3
"""Convert a MaterialX document to MaterialX-in-MTL lines (see mtlx-mtl.md).

Supports documents whose materials are a surface shader plus single-output
nodes (top-level or inside nodegraphs without nodedef/interface). Document
`fileprefix` is baked into file names; inherited `colorspace` is emitted as
explicit `mtlx_colorspace` lines. Unsupported documents exit with status 3 and
a reason on stderr.

usage: mtlx2mtl.py IN.mtlx > OUT.mtl
"""
import sys
import xml.etree.ElementTree as ET

VALUE_TYPES = {
    "integer", "boolean", "float", "color3", "color4", "vector2", "vector3", "vector4",
    "matrix33", "matrix44", "string", "filename", "integerarray", "floatarray",
    "color3array", "color4array", "vector2array", "vector3array", "vector4array", "stringarray"}
INPUT_ATTRS = {"name", "type", "value", "nodename", "nodegraph", "output", "colorspace",
               "uiname", "uifolder", "uimin", "uimax", "uisoftmin", "uisoftmax", "uistep", "doc",
               "uniform"}
DEFAULT_CS = "lin_rec709"


class Unsupported(Exception):
    pass


def tokens_of(ty, value):
    if ty in ("string", "filename"):
        if '"' in value or value == "":
            raise Unsupported(f"string value {value!r} cannot be tokenized")
        if value.startswith("@"):
            value = "@" + value  # `@@` escapes a literal leading '@'
        return [f'"{value}"' if (" " in value or "\t" in value) else value]
    toks = [t for t in value.replace(",", " ").split() if t]
    if not toks:
        raise Unsupported("empty value")
    return toks


def convert(path):
    root = ET.parse(path).getroot()
    doc_cs = root.get("colorspace")
    doc_prefix = root.get("fileprefix", "")
    version = root.get("version")
    top = {e.get("name"): e for e in root}
    if root.findall("nodedef") or [g for g in root.findall("nodegraph") if g.get("nodedef")]:
        raise Unsupported("document defines nodedefs; put them in a library "
                          "and reference it with mtlx_include")
    out = []

    for mat in root.findall("surfacematerial"):
        mname = mat.get("name")
        ss = [i for i in mat.findall("input") if i.get("name") == "surfaceshader"]
        if len(ss) != 1 or not ss[0].get("nodename"):
            raise Unsupported(f"{mname}: surfaceshader input")
        surf = top.get(ss[0].get("nodename"))
        if surf is None or surf.get("type") != "surfaceshader":
            raise Unsupported(f"{mname}: surface shader node not found")

        nodes = []          # (name, elem, scope_attrs)
        names = {}
        inputs, conns, css = [], [], []

        def scope_attr(chain, key, default=None):
            for e in chain:
                if e.get(key) is not None:
                    return e.get(key)
            return default

        def visit(elem, chain, scope_nodes):
            """Register `elem` (a node) and recurse into its node inputs."""
            n = elem.get("name")
            if n in names:
                if names[n] is not elem:
                    raise Unsupported(f"{mname}: node name {n} used in two scopes")
                return
            if elem is not surf:
                if elem.get("type") not in VALUE_TYPES:
                    raise Unsupported(f"{mname}: node {n} has type {elem.get('type')}")
                nodes.append((n, elem))
            names[n] = elem
            for inp in elem.findall("input"):
                extra = set(inp.attrib) - INPUT_ATTRS
                if extra:
                    raise Unsupported(f"{mname}: input attributes {sorted(extra)}")
                port, ty = inp.get("name"), inp.get("type")
                ichain = [inp, elem] + chain
                src = None
                if inp.get("nodename"):
                    if inp.get("output") and inp.get("output") != "out":
                        raise Unsupported(f"{mname}: multi-output source")
                    src = scope_nodes.get(inp.get("nodename"))
                    src_chain = chain
                    src_scope = scope_nodes
                elif inp.get("nodegraph"):
                    ng = top.get(inp.get("nodegraph"))
                    if ng is None or ng.tag != "nodegraph" or ng.get("nodedef"):
                        raise Unsupported(f"{mname}: nodegraph {inp.get('nodegraph')}")
                    outs = [o for o in ng.findall("output") if o.get("name") == inp.get("output")]
                    if len(outs) != 1 or not outs[0].get("nodename"):
                        raise Unsupported(f"{mname}: nodegraph output {inp.get('output')}")
                    if outs[0].get("output"):
                        raise Unsupported(f"{mname}: multi-output graph output")
                    ng_nodes = {e.get("name"): e for e in ng if e.tag not in ("input", "output")}
                    if ng.findall("input"):
                        raise Unsupported(f"{mname}: nodegraph interface inputs")
                    src = ng_nodes.get(outs[0].get("nodename"))
                    src_chain = [ng, root]
                    src_scope = ng_nodes
                if src is not None:
                    visit(src, src_chain, src_scope)
                    conns.append(f"mtlx_input {n}.{port} {ty} @{src.get('name')}")
                    continue
                if inp.get("nodename") or inp.get("nodegraph"):
                    raise Unsupported(f"{mname}: dangling connection on {n}.{port}")
                if inp.get("value") is None:
                    continue
                value = inp.get("value")
                if ty == "filename":
                    value = scope_attr(ichain, "fileprefix", doc_prefix) + value
                inputs.append(f"mtlx_input {n}.{port} {ty} " + " ".join(tokens_of(ty, value)))
                if ty == "filename" or ty.startswith("color"):
                    cs = scope_attr(ichain, "colorspace", doc_cs)
                    if cs and cs != DEFAULT_CS:
                        css.append(f"mtlx_colorspace {n}.{port} {cs}")

        visit(surf, [root], {k: v for k, v in top.items()})
        if " " in mname or "\t" in mname:
            raise Unsupported("material name with blanks")
        out.append(f"newmtl {mname}")
        if version:
            out.append(f"mtlx_version {version}")
        out.append(f"mtlx_surface {surf.get('name')} {surf.tag}")
        for n, e in nodes:
            out.append(f"mtlx_node {n} {e.tag} {e.get('type')}")
        out += inputs + css + conns
        out.append("")
    if not out:
        raise Unsupported("no surfacematerial")
    return "\n".join(out)


def main():
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    try:
        sys.stdout.write(convert(sys.argv[1]))
    except Unsupported as e:
        print(f"unsupported: {e}", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
