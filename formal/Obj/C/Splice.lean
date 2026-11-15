/-
  Byte-range algebra for `C.store`.

  `splice blk o bs` is "`blk` with the `|bs|` bytes at `o` replaced by `bs`",
  exactly what `C.store` does to a block. The lemmas below give what the
  proofs need: the overwritten range reads back as `bs`, everything outside is
  unchanged, and two adjacent writes compose into one.
-/
import Obj.C.Lemmas

set_option linter.deprecated false

namespace Obj.C

def splice (blk : Block) (o : Nat) (bs : Block) : Block :=
  blk.take o ++ bs ++ blk.drop (o + bs.length)

theorem splice_take_length (blk : Block) (o : Nat) (ho : o ≤ blk.length) :
    (blk.take o).length = o := by
  rw [List.length_take, Nat.min_eq_left ho]

theorem splice_length (blk : Block) (o : Nat) (bs : Block)
    (h : o + bs.length ≤ blk.length) : (splice blk o bs).length = blk.length := by
  have h1 := splice_take_length blk o (by omega)
  simp only [splice, List.length_append, List.length_drop, h1]
  omega

/-- Characterisation of `splice` as a pointwise function. -/
theorem splice_getElem? (blk : Block) (o : Nat) (bs : Block)
    (h : o + bs.length ≤ blk.length) (j : Nat) :
    (splice blk o bs)[j]? =
      (if j < o then blk[j]?
       else if j < o + bs.length then bs[j - o]?
       else blk[j]?) := by
  have h1 : (blk.take o).length = o := splice_take_length blk o (by omega)
  have h2 : (blk.take o ++ bs).length = o + bs.length := by simp [h1]
  have ho : o ≤ blk.length := by omega
  simp only [splice, List.getElem?_append, List.getElem?_drop, List.getElem?_take, h1, h2,
    Nat.min_eq_left ho]
  by_cases c1 : j < o
  · simp only [show j < o + bs.length from by omega, c1, if_true]
  · by_cases c2 : j < o + bs.length
    · simp only [c1, c2, if_false, if_true]
    · simp only [c1, c2, if_false, if_true]
      congr 1
      omega

/-- The overwritten range reads back as `bs`. -/
theorem splice_inside (blk : Block) (o : Nat) (bs : Block)
    (h : o + bs.length ≤ blk.length) :
    List.take bs.length ((splice blk o bs).drop o) = bs := by
  have h1 : (blk.take o).length = o := splice_take_length blk o (by omega)
  have hd : List.drop (blk.take o).length (blk.take o ++ (bs ++ List.drop (o + bs.length) blk))
      = bs ++ List.drop (o + bs.length) blk := List.drop_left
  rw [h1] at hd
  simp only [splice, List.append_assoc]
  rw [hd, List.take_left]

/-- A read entirely before the overwritten range is unchanged. -/
theorem read_prefix (blk : Block) (o : Nat) (bs : Block) (h : o + bs.length ≤ blk.length)
    (j n : Nat) (hj : j + n ≤ o) :
    List.take n ((splice blk o bs).drop j) = List.take n (blk.drop j) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < n
  · rw [if_pos hi, if_pos (by omega), splice_getElem? _ _ _ h, if_pos (by omega)]
  · rw [if_neg hi, if_neg (by omega)]

/-- A read entirely after the overwritten range is unchanged. -/
theorem read_suffix (blk : Block) (o : Nat) (bs : Block) (h : o + bs.length ≤ blk.length)
    (j n : Nat) (hj : o + bs.length ≤ j) :
    List.take n ((splice blk o bs).drop j) = List.take n (blk.drop j) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < n
  · rw [if_pos hi, if_pos (by omega), splice_getElem? _ _ _ h, if_neg (by omega),
      if_neg (by omega)]
  · rw [if_neg hi, if_neg (by omega)]

theorem writeBytes_eq(m : Mem) (b o : Nat) (blk : Block) (hm : m b = some blk) (bs : Block)
    (h : o + bs.length ≤ blk.length) :
    writeBytes m b o bs = .ok (m.upd b (splice blk o bs)) := by
  simp only [writeBytes, hm, splice]
  rw [if_pos h]

/-- Storing an integer of type `t` overwrites exactly its bytes. -/
theorem store_int (m : Mem) (b o : Nat) (blk : Block) (hm : m b = some blk) (t : IntTy)
    (v : Nat) (h : o + t.bytes ≤ blk.length) :
    C.store m (.int t) (.ptr b o) (.int t v)
      = .ok (m.upd b (splice blk o (encodeLE t.bytes v))) := by
  have h' : o + (encodeLE t.bytes v).length ≤ blk.length := by
    rw [encodeLE_length]; exact h
  simp only [C.store, if_true]
  exact writeBytes_eq m b o blk hm (encodeLE t.bytes v) h'

end Obj.C

namespace Obj.C

/-- Two adjacent writes are one write of the concatenation. -/
theorem splice_append (blk : Block) (o : Nat) (xs ys : Block)
    (h : o + xs.length + ys.length ≤ blk.length) :
    splice (splice blk o xs) (o + xs.length) ys = splice blk o (xs ++ ys) := by
  have hx : o + xs.length ≤ blk.length := by omega
  have hlen : (splice blk o xs).length = blk.length := splice_length blk o xs hx
  have hout : (o + xs.length) + ys.length ≤ (splice blk o xs).length := by
    rw [hlen]; omega
  have hcc : (xs ++ ys).length = xs.length + ys.length := List.length_append
  have hconc : o + (xs ++ ys).length ≤ blk.length := by rw [hcc]; omega
  apply List.ext_getElem?
  intro j
  rw [splice_getElem? (blk := splice blk o xs) (o := o + xs.length) (bs := ys) (h := hout)]
  rw [splice_getElem? (blk := blk) (o := o) (bs := xs ++ ys) (h := hconc)]
  simp only [splice_getElem? (blk := blk) (o := o) (bs := xs) (h := hx), hcc]
  rw [show o + (xs.length + ys.length) = o + xs.length + ys.length from by omega]
  by_cases c1 : j < o
  · simp only [c1, (by omega : j < o + xs.length),
      (by omega : j < o + xs.length + ys.length), if_true]
  · simp only [c1, if_false]
    by_cases c2 : j < o + xs.length
    · simp only [c2, (by omega : j < o + xs.length + ys.length), if_true]
      rw [List.getElem?_append, if_pos (by omega : j - o < xs.length)]
    · simp only [c2, if_false]
      by_cases c3 : j < o + xs.length + ys.length
      · simp only [c3, if_true]
        rw [List.getElem?_append, if_neg (by omega : ¬ j - o < xs.length)]
        congr 1
        omega
      · simp only [c3, if_false]

end Obj.C
