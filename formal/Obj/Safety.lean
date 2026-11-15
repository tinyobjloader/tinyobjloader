/-
  Properties of the validation specification (no C involved).

  * `validate_ok_iff_safe` / `validate_strict_ok_iff`: the parser's verdict
    under default options is exactly `WellFormedSafe` (resp.
    `WellFormedStrict` under `TG3_STRICT`).
  * `accessor_element_in_buffer`: in a `WellFormedSafe` model every element
    of every accessor lies inside its buffer, i.e. naive indexing
    `buffer + bv.byteOffset + a.byteOffset + i * stride` is in bounds.
  * `*_resolves`: every index a consumer follows resolves to an element.
-/
import Obj.Validate

namespace Obj
namespace Validate

theorem validate_ok_iff_safe (m : Model) :
    validate {} m = .ok ↔ WellFormedSafe m := by
  unfold validate WellFormedSafe
  cases hi : indicesOk m <;> cases hr : rangesOk m <;> simp

theorem validate_strict_ok_iff (m : Model) :
    validate { strictness := .strict } m = .ok ↔ WellFormedStrict m := by
  unfold validate WellFormedStrict WellFormedSafe
  cases hi : indicesOk m <;> cases hr : rangesOk m <;> cases hs : specOk m <;> simp

theorem strict_safe {m : Model} (h : WellFormedStrict m) : WellFormedSafe m := h.1

/-- Spec violations never make the permissive parser fail. -/
theorem permissive_ignores_spec (m : Model) (h : WellFormedSafe m) :
    validate {} m = .ok := (validate_ok_iff_safe m).2 h

theorem getIdx?_mem {α} {l : List α} {i : Int32} {x : α} (h : getIdx? l i = some x) : x ∈ l := by
  unfold getIdx? at h
  split at h
  · exact List.mem_of_getElem? h
  · contradiction

theorem getIdx?_of_valid {α} (l : List α) (i : Int32) (h : validIdx i l.length = true) :
    ∃ x, getIdx? l i = some x := by
  unfold validIdx at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold getIdx?
  simp only [h.1, ite_true]
  have : i.toInt.toNat < l.length := by omega
  exact ⟨l[i.toInt.toNat], List.getElem?_eq_getElem this⟩

theorem getIdx?_of_validOpt {α} (l : List α) (i : Int32) (h : validOptIdx i l.length = true)
    (hne : i ≠ -1) : ∃ x, getIdx? l i = some x := by
  unfold validOptIdx at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd h hne
  · exact getIdx?_of_valid l i h

/-- **Accessor safety.** In a `WellFormedSafe` model, for every accessor
    stored in a buffer view, element `i < count` occupies bytes
    `[start, start + elemSize)` of the buffer with
    `start = bv.byteOffset + a.byteOffset + i * stride`, and that range is
    inside the buffer. -/
theorem accessor_element_in_buffer (m : Model) (h : WellFormedSafe m)
    (a : Accessor) (ha : a ∈ m.accessors)
    (bv : BufferView) (hbv : getIdx? m.bufferViews a.bufferView = some bv)
    (b : Buffer) (hb : getIdx? m.buffers bv.buffer = some b)
    (i : Nat) (hi : i < a.count.toNat) :
    bv.byteOffset.toNat + a.byteOffset.toNat + i * stride a bv + elemSize a ≤ bufSize b := by
  have hr := h.2
  unfold rangesOk at hr
  simp only [Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨_, hbvs⟩, haccs⟩ := hr
  have hacc := haccs a ha
  unfold accessorOk at hacc
  simp only [Bool.and_eq_true] at hacc
  obtain ⟨⟨_, habv⟩, _⟩ := hacc
  unfold accessorBVOk at habv
  rw [hbv] at habv
  simp only [Bool.and_eq_true, decide_eq_true_eq, fits] at habv
  obtain ⟨⟨hstride, _⟩, hfit⟩ := habv
  have hbvok := hbvs bv (getIdx?_mem hbv)
  unfold bufferViewOk at hbvok
  rw [hb] at hbvok
  simp only [fits, decide_eq_true_eq] at hbvok
  have hspan : i * stride a bv + elemSize a ≤ span a bv := by
    unfold span
    have hc : a.count.toNat ≠ 0 := by omega
    simp only [hc, ite_false]
    have : i * stride a bv ≤ (a.count.toNat - 1) * stride a bv :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  omega

/-- Every primitive attribute of a `WellFormedSafe` model names an accessor. -/
theorem attribute_resolves (m : Model) (h : WellFormedSafe m)
    (me : Mesh) (hme : me ∈ m.meshes) (p : Primitive) (hp : p ∈ me.primitives)
    (kv : Bytes × Int32) (hkv : kv ∈ p.attributes) :
    ∃ a, getIdx? m.accessors kv.2 = some a := by
  have hi := h.1
  unfold indicesOk at hi
  simp only [Bool.and_eq_true, List.all_eq_true] at hi
  have := hi.1.1.1.1.1.1.1.1.1.1.2 me hme p hp
  exact getIdx?_of_valid _ _ (this.1.2 kv hkv)

/-- Every scene node of a `WellFormedSafe` model resolves. -/
theorem scene_node_resolves (m : Model) (h : WellFormedSafe m)
    (sc : Scene) (hsc : sc ∈ m.scenes) (n : Int32) (hn : n ∈ sc.nodes) :
    ∃ x, getIdx? m.nodes n = some x := by
  have hi := h.1
  unfold indicesOk at hi
  simp only [Bool.and_eq_true, List.all_eq_true] at hi
  have := hi.1.1.1.1.2 sc hsc
  exact getIdx?_of_valid _ _ (this.1 n hn)

end Validate
end Obj
