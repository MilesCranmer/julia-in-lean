import JuliaLean.BitArrays.Basic
import JuliaLean.BitArrays.CopyProof

/-!
# Range operations on `BitVector`

Proofs of `AppendPrependAgrees`, `DeleteatRangeInsideAgrees`, `ResizeNonnegAgrees`,
`ShiftAgrees`, `CircshiftNonemptyAgrees` and `ReverseDimsNonemptyAgrees`. Each model
function is first rewritten by `rfl` into its chunk-level steps (`grow` for
`_growend!` with the zeroed last chunk, `trim` for the final `_deleteend!` and
masking of `deleteat!`, and `copyChunks`); the bits of each step come from
`copyChunks_spec` and the lemmas of `Basic.lean`.
-/

namespace JuliaLean.BitArrays

open BV

namespace RangeSpec

/-! ## Lists -/

theorem getD_take' (l : List Bool) (a k : Nat) :
    (l.take a).getD k false = if k < a then l.getD k false else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  split <;> rfl

theorem getD_drop' (l : List Bool) (a k : Nat) : (l.drop a).getD k false = l.getD (a + k) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_map_range (n : Nat) (f : Nat → Bool) (k : Nat) :
    ((List.range n).map f).getD k false = if k < n then f k else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < n
  · rw [List.getElem?_range h, if_pos h]; rfl
  · rw [List.getElem?_eq_none_iff.mpr (by rw [List.length_range]; omega), if_neg h]; rfl

theorem length_unpack (cs : List U64) (n : Nat) : (unpack cs n).length = n := by
  simp [unpack]

theorem getD_unpack (cs : List U64) (n k : Nat) :
    (unpack cs n).getD k false = if k < n then bitOf cs k else false :=
  getD_map_range n (bitOf cs) k

theorem list_ext (a b : List Bool) (hl : a.length = b.length)
    (h : ∀ k, k < a.length → a.getD k false = b.getD k false) : a = b := by
  apply List.ext_getElem hl
  intro k h1 h2
  have := h k h1
  rwa [getD_lt h1, getD_lt h2] at this

theorem bitOf_replicate_zero (m k : Nat) : bitOf (List.replicate m (0 : U64)) k = false := by
  rw [bitOf_def, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> exact getLsbD_zero64 _

/-! ## Growing and trimming chunk vectors -/

/-- `_growend!(Bc, num_bit_chunks(n) - length(Bc)); Bc[end] = 0` when chunks are missing. -/
def grow (cs : List U64) (n : Nat) (dirty : U64) : List U64 :=
  if numBitChunks n > cs.length then csetEnd (growend cs (numBitChunks n - cs.length) dirty) 0 else cs

theorem grow_spec (l : List Bool) (n : Nat) (dirty : U64) (hn : l.length ≤ n) :
    (grow (pack l) n dirty).length = numBitChunks n ∧
    ∀ k, (k < l.length ∨ n ≤ k) → bitOf (grow (pack l) n dirty) k = l.getD k false := by
  have hmono : numBitChunks l.length ≤ numBitChunks n := by
    simp only [numBitChunks_eq]; omega
  unfold grow
  constructor
  · split
    · rw [length_csetEnd, length_growend]; omega
    · rw [pack_length] at *; omega
  · intro k hk
    split
    · rename_i hg
      rw [pack_length] at hg
      rw [bitOf_csetEnd, length_growend, bitOf_growend, pack_length, bitOf_pack, getLsbD_zero64]
      simp only [numBitChunks_eq] at hg hmono ⊢
      bfin
    · rw [bitOf_pack]

/-- `_deleteend!` down to `num_bit_chunks(newL)` chunks. -/
def trim1 (bc : List U64) (newL : Nat) : List U64 :=
  if numBitChunks newL < bc.length then deleteend bc (bc.length - numBitChunks newL) else bc

/-- The end of `deleteat!(B, r)`: drop the extra chunks, then clear the unused bits. -/
def trim (bc : List U64) (newL : Nat) : List U64 :=
  if newL > 0 then csetEnd (trim1 bc newL) (cgetEnd (trim1 bc newL) &&& mskEnd newL) else trim1 bc newL

theorem trim_spec (bc : List U64) (newL : Nat) (h : numBitChunks newL ≤ bc.length) :
    (trim bc newL).length = numBitChunks newL ∧
    ∀ k, bitOf (trim bc newL) k = if k < newL then bitOf bc k else false := by
  have h1l : (trim1 bc newL).length = numBitChunks newL := by
    unfold trim1
    split
    · rw [length_deleteend]; omega
    · omega
  have h1b : ∀ k, bitOf (trim1 bc newL) k =
      if k / 64 < numBitChunks newL then bitOf bc k else false := by
    intro k
    unfold trim1
    split
    · rw [bitOf_deleteend]; bfin
    · split
      · rfl
      · exact bitOf_ge (by omega)
  unfold trim
  constructor
  · split
    · rw [length_csetEnd, h1l]
    · exact h1l
  · intro k
    split
    · rw [bitOf_csetEnd, h1l, cgetEnd_eq, h1l, BitVec.getLsbD_and, getLsbD_cget, getLsbD_mskEnd_ite]
      simp only [h1b, numBitChunks_eq]
      bfin
    · rw [h1b]
      simp only [numBitChunks_eq]
      bfin

/-! ## `append!` and `prepend!` -/

theorem append_some_eq (l m : List Bool) (dirty : U64) :
    append (ofList l) (some (ofList m)) dirty =
      if m.length = 0 then ofList l else
      ⟨copyChunks (grow (pack l) (l.length + m.length) dirty) (l.length + 1) (.other (pack m)) 1 m.length,
        l.length + m.length⟩ := rfl

theorem append_none_eq (l : List Bool) (dirty : U64) :
    append (ofList l) none dirty =
      if l.length = 0 then ofList l else
      ⟨copyChunks (grow (pack l) (l.length + l.length) dirty) (l.length + 1) .self 1 l.length,
        l.length + l.length⟩ := rfl

theorem prepend_some_eq (l m : List Bool) (dirty : U64) :
    prepend (ofList l) (some (ofList m)) dirty =
      if m.length = 0 then ofList l else
      ⟨copyChunks (copyChunks (grow (pack l) (l.length + m.length) dirty) (1 + m.length) .self 1 l.length)
        1 (.other (pack m)) 1 m.length, l.length + m.length⟩ := rfl

theorem prepend_none_eq (l : List Bool) (dirty : U64) :
    prepend (ofList l) none dirty =
      if l.length = 0 then ofList l else
      ⟨copyChunks (copyChunks (grow (pack l) (l.length + l.length) dirty) (1 + l.length) .self 1 l.length)
        1 .self 1 l.length, l.length + l.length⟩ := rfl

theorem append_some_spec (l m : List Bool) (dirty : U64) :
    append (ofList l) (some (ofList m)) dirty = ofList (l ++ m) := by
  rw [append_some_eq]
  split
  · rename_i hm
    rw [List.eq_nil_of_length_eq_zero hm, List.append_nil]
  · have hG := grow_spec l (l.length + m.length) dirty (by omega)
    have hC := copyChunks_spec (grow (pack l) (l.length + m.length) dirty) (l.length + 1)
      (.other (pack m)) 1 m.length (by omega) (by omega) (by rw [hG.1, numBitChunks_eq]; omega)
    apply eq_ofList_of_bits
    · simp
    · dsimp only
      rw [hC.1, hG.1, List.length_append]
    · intro k
      dsimp only
      rw [hC.2 k, getD_append]
      simp only [Src.read, bitOf_pack]
      (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin

theorem append_none_spec (l : List Bool) (dirty : U64) :
    append (ofList l) none dirty = ofList (l ++ l) := by
  rw [append_none_eq]
  split
  · rename_i hl
    rw [List.eq_nil_of_length_eq_zero hl]
    rfl
  · have hG := grow_spec l (l.length + l.length) dirty (by omega)
    have hC := copyChunks_spec (grow (pack l) (l.length + l.length) dirty) (l.length + 1) .self 1
      l.length (by omega) (by omega) (by rw [hG.1, numBitChunks_eq]; omega)
    apply eq_ofList_of_bits
    · simp
    · dsimp only
      rw [hC.1, hG.1, List.length_append]
    · intro k
      dsimp only
      rw [hC.2 k, getD_append]
      simp only [Src.read]
      (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin

theorem prepend_some_spec (l m : List Bool) (dirty : U64) :
    prepend (ofList l) (some (ofList m)) dirty = ofList (m ++ l) := by
  rw [prepend_some_eq]
  split
  · rename_i hm
    rw [List.eq_nil_of_length_eq_zero hm, List.nil_append]
  · have hG := grow_spec l (l.length + m.length) dirty (by omega)
    have hC1 := copyChunks_spec (grow (pack l) (l.length + m.length) dirty) (1 + m.length) .self 1
      l.length (by omega) (by omega) (by rw [hG.1, numBitChunks_eq]; omega)
    have hC2 := copyChunks_spec
      (copyChunks (grow (pack l) (l.length + m.length) dirty) (1 + m.length) .self 1 l.length)
      1 (.other (pack m)) 1 m.length (by omega) (by omega)
      (by rw [hC1.1, hG.1, numBitChunks_eq]; omega)
    apply eq_ofList_of_bits
    · simp only [List.length_append]; omega
    · dsimp only
      rw [hC2.1, hC1.1, hG.1, List.length_append]
      congr 1; omega
    · intro k
      dsimp only
      rw [hC2.2 k, hC1.2 k, getD_append]
      simp only [Src.read, bitOf_pack]
      (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin

theorem prepend_none_spec (l : List Bool) (dirty : U64) :
    prepend (ofList l) none dirty = ofList (l ++ l) := by
  rw [prepend_none_eq]
  split
  · rename_i hl
    rw [List.eq_nil_of_length_eq_zero hl]
    rfl
  · have hG := grow_spec l (l.length + l.length) dirty (by omega)
    have hC1 := copyChunks_spec (grow (pack l) (l.length + l.length) dirty) (1 + l.length) .self 1
      l.length (by omega) (by omega) (by rw [hG.1, numBitChunks_eq]; omega)
    have hC2 := copyChunks_spec
      (copyChunks (grow (pack l) (l.length + l.length) dirty) (1 + l.length) .self 1 l.length)
      1 .self 1 l.length (by omega) (by omega) (by rw [hC1.1, hG.1, numBitChunks_eq]; omega)
    apply eq_ofList_of_bits
    · simp
    · dsimp only
      rw [hC2.1, hC1.1, hG.1, List.length_append]
    · intro k
      dsimp only
      rw [hC2.2 k, getD_append]
      simp only [Src.read, hC1.2]
      (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin

/-! ## `deleteat!` with a range -/

theorem deleteatRange_ofList (l : List Bool) (r : URange) :
    deleteatRange (ofList l) r =
      if ¬ (1 ≤ r.first.val) then .error .boundsError else
      if ¬ (r.last.val ≤ l.length) then .error .boundsError else
      .ok ⟨trim (copyChunks (pack l) r.first.val.toNat .self (r.last.val.toNat + 1)
          (l.length - r.last.val.toNat)) (l.length - r.length.toNat), l.length - r.length.toNat⟩ := rfl

theorem deleteatRange_ok (l : List Bool) (r : URange) (h1 : 1 ≤ r.first.val)
    (h2 : r.first.val - 1 ≤ r.last.val) (h3 : r.last.val ≤ l.length) :
    deleteatRange (ofList l) r =
      .ok (ofList (l.take (r.first.val.toNat - 1) ++ l.drop (r.first.val.toNat - 1 + r.length.toNat))) := by
  rw [deleteatRange_ofList, if_neg (not_not_intro h1), if_neg (not_not_intro h3)]
  congr 1
  simp only [URange.length]
  have hC := copyChunks_spec (pack l) r.first.val.toNat .self (r.last.val.toNat + 1)
    (l.length - r.last.val.toNat) (by omega) (by omega) (by rw [pack_length, numBitChunks_eq]; omega)
  have hT := trim_spec (copyChunks (pack l) r.first.val.toNat .self (r.last.val.toNat + 1)
    (l.length - r.last.val.toNat)) (l.length - (r.last.val - r.first.val + 1).toNat)
    (by rw [hC.1, pack_length]; simp only [numBitChunks_eq]; omega)
  apply eq_ofList_of_bits
  · simp only [List.length_append, List.length_take, List.length_drop]; omega
  · dsimp only
    rw [hT.1, List.length_append, List.length_take, List.length_drop]
    congr 1; omega
  · intro k
    dsimp only
    rw [hT.2 k, hC.2 k, getD_append, getD_take', getD_drop']
    simp only [Src.read, bitOf_pack, List.length_take]
    bfin

theorem deleteatRange_proof : DeleteatRangeInsideAgrees := by
  intro l r _ h1 h2
  by_cases hok : 1 ≤ r.first.val ∧ r.last.val ≤ l.length
  · rw [deleteatRange_ok l r hok.1 h1 hok.2]
    unfold Ref.deleteatRange
    by_cases hz : r.length = 0
    · rw [if_pos hz]
      have e : l.take (r.first.val.toNat - 1) ++ l.drop (r.first.val.toNat - 1 + r.length.toNat) = l := by
        simp [hz]
      rw [e]
      rfl
    · have c1 : 1 ≤ r.first.val ∧ r.first.val ≤ ↑l.length := by
        refine ⟨hok.1, ?_⟩
        simp only [URange.length] at hz
        omega
      have c2 : r.first.val + r.length ≤ ↑l.length + 1 := by
        simp only [URange.length]
        omega
      rw [if_neg hz, if_neg (not_not_intro c1), if_neg (not_not_intro c2)]
      rfl
  · have hz : ¬ r.length = 0 := by
      intro hz
      simp only [URange.length] at hz h2
      omega
    rw [deleteatRange_ofList]
    unfold Ref.deleteatRange
    rw [if_neg hz]
    by_cases hf : 1 ≤ r.first.val
    · have hL : ¬ r.last.val ≤ ↑l.length := fun h => hok ⟨hf, h⟩
      rw [if_neg (not_not_intro hf), if_pos hL]
      by_cases hfl : r.first.val ≤ ↑l.length
      · rw [if_neg (not_not_intro (show 1 ≤ r.first.val ∧ r.first.val ≤ ↑l.length from ⟨hf, hfl⟩)),
          if_pos (show ¬ (r.first.val + r.length ≤ ↑l.length + 1) by simp only [URange.length]; omega)]
        rfl
      · rw [if_pos (show ¬ (1 ≤ r.first.val ∧ r.first.val ≤ ↑l.length) from fun h => hfl h.2)]
        rfl
    · rw [if_pos hf, if_pos (show ¬ (1 ≤ r.first.val ∧ r.first.val ≤ ↑l.length) from fun h => hf h.1)]
      rfl

/-! ## `resize!` -/

theorem lit_val (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    (JInt.lit .i64 x).val = x := by
  show wrapInt .i64 x = x
  simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem deleteatRange_ok' (l : List Bool) (r : URange) (a b : Int) (ha : r.first.val = a)
    (hb : r.last.val = b) (h1 : 1 ≤ a) (h2 : a - 1 ≤ b) (h3 : b ≤ l.length) :
    deleteatRange (ofList l) r =
      .ok (ofList (l.take (a.toNat - 1) ++ l.drop (a.toNat - 1 + (b - a + 1).toNat))) := by
  rw [deleteatRange_ok l r (by omega) (by omega) (by omega)]
  simp only [URange.length, ha, hb]

theorem resize_true_eq (l : List Bool) (n : JInt64) (dirty : U64) :
    resize (ofList l) n true dirty =
      if n.val = l.length then .ok (ofList l) else
      if ¬ (n.val ≥ 0) then .error .boundsError else
      if n.val.toNat < l.length then
        deleteatRange (ofList l) ⟨JInt.lit .i64 1, JInt.lit .i64 (l.length - n.val.toNat)⟩
      else .ok ⟨copyChunks (grow (pack l) n.val.toNat dirty) (1 + n.val.toNat - l.length) .self 1
          l.length, n.val.toNat⟩ := rfl

theorem resize_false_eq (l : List Bool) (n : JInt64) (dirty : U64) :
    resize (ofList l) n false dirty =
      if n.val = l.length then .ok (ofList l) else
      if ¬ (n.val ≥ 0) then .error .boundsError else
      if n.val.toNat < l.length then
        deleteatRange (ofList l) ⟨JInt.lit .i64 (n.val.toNat + 1), JInt.lit .i64 l.length⟩
      else .ok ⟨grow (pack l) n.val.toNat dirty, n.val.toNat⟩ := rfl

/-- The conclusion of `ResizeNonnegAgrees` for a result `BV.ofList L`. -/
theorem resize_concl (l L : List Bool) (m : Nat) (first : Bool) (hL : L.length = m)
    (hfirst : first = true → ∀ k, k < min m l.length →
      L.getD (m - min m l.length + k) false = l.getD (l.length - min m l.length + k) false)
    (hlast : first = false → ∀ k, k < min m l.length → L.getD k false = l.getD k false) :
    ofList L = ofList (ofList L).toList ∧ (ofList L).len = m ∧
      (if first then (ofList L).toList.drop ((ofList L).len - min (ofList L).len l.length) =
          l.drop (l.length - min (ofList L).len l.length)
       else (ofList L).toList.take (min (ofList L).len l.length) = l.take (min (ofList L).len l.length)) := by
  rw [toList_ofList, ofList_len, hL]
  refine ⟨rfl, rfl, ?_⟩
  cases first with
  | false =>
    rw [if_neg Bool.false_ne_true]
    apply list_ext
    · simp only [List.length_take]; omega
    · intro k hk
      simp only [List.length_take] at hk
      have hk' : k < min m l.length := by omega
      rw [getD_take', getD_take', if_pos hk', if_pos hk']
      exact hlast rfl k hk'
  | true =>
    rw [if_pos rfl]
    apply list_ext
    · simp only [List.length_drop]; omega
    · intro k hk
      simp only [List.length_drop] at hk
      rw [getD_drop', getD_drop']
      exact hfirst rfl k (by omega)

theorem resize_proof : ResizeNonnegAgrees := by
  intro l n first dirty hl hn
  cases first with
  | true =>
    rw [resize_true_eq]
    by_cases h0 : n.val = l.length
    · rw [if_pos h0]
      exact resize_concl l l n.val.toNat true (by omega) (fun _ k _ => by congr 1; omega)
        (fun h => by cases h)
    · rw [if_neg h0, if_neg (not_not_intro hn)]
      by_cases hlt : n.val.toNat < l.length
      · rw [if_pos hlt]
        have e1 : (JInt.lit .i64 1).val = 1 := lit_val 1 (by omega) (by omega)
        have e2 : (JInt.lit .i64 (l.length - n.val.toNat)).val = l.length - n.val.toNat :=
          lit_val _ (by omega) (by omega)
        rw [deleteatRange_ok' l ⟨JInt.lit .i64 1, JInt.lit .i64 (l.length - n.val.toNat)⟩ 1
          (l.length - n.val.toNat) e1 e2 (by omega) (by omega) (by omega)]
        refine resize_concl l _ n.val.toNat true ?_ (fun _ k hk => ?_) (fun h => by cases h)
        · simp only [List.length_append, List.length_take, List.length_drop]; omega
        · rw [getD_append, getD_take', getD_drop']
          simp only [List.length_take]
          bfin
      · rw [if_neg hlt]
        have hG := grow_spec l n.val.toNat dirty (by omega)
        have hC := copyChunks_spec (grow (pack l) n.val.toNat dirty) (1 + n.val.toNat - l.length) .self 1
          l.length (by omega) (by omega) (by rw [hG.1, numBitChunks_eq]; omega)
        have hB : (⟨copyChunks (grow (pack l) n.val.toNat dirty) (1 + n.val.toNat - l.length) .self 1
            l.length, n.val.toNat⟩ : BV) = ofList (unpack (copyChunks (grow (pack l) n.val.toNat dirty)
              (1 + n.val.toNat - l.length) .self 1 l.length) n.val.toNat) := by
          apply eq_ofList_of_bits
          · rw [length_unpack]
          · dsimp only; rw [length_unpack, hC.1, hG.1]
          · intro k
            dsimp only
            rw [getD_unpack, hC.2 k]
            simp only [Src.read]
            (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin
        rw [hB]
        refine resize_concl l _ n.val.toNat true (length_unpack _ _) (fun _ k hk => ?_)
          (fun h => by cases h)
        rw [getD_unpack, hC.2]
        simp only [Src.read]
        (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin
  | false =>
    rw [resize_false_eq]
    by_cases h0 : n.val = l.length
    · rw [if_pos h0]
      exact resize_concl l l n.val.toNat false (by omega) (fun h => by cases h) (fun _ _ _ => rfl)
    · rw [if_neg h0, if_neg (not_not_intro hn)]
      by_cases hlt : n.val.toNat < l.length
      · rw [if_pos hlt]
        have e1 : (JInt.lit .i64 (n.val.toNat + 1)).val = n.val.toNat + 1 := lit_val _ (by omega) (by omega)
        have e2 : (JInt.lit .i64 l.length).val = l.length := lit_val _ (by omega) (by omega)
        rw [deleteatRange_ok' l ⟨JInt.lit .i64 (n.val.toNat + 1), JInt.lit .i64 l.length⟩
          (n.val.toNat + 1) l.length e1 e2 (by omega) (by omega) (by omega)]
        refine resize_concl l _ n.val.toNat false ?_ (fun h => by cases h) (fun _ k hk => ?_)
        · simp only [List.length_append, List.length_take, List.length_drop]; omega
        · rw [getD_append, getD_take', getD_drop']
          simp only [List.length_take]
          bfin
      · rw [if_neg hlt]
        have hG := grow_spec l n.val.toNat dirty (by omega)
        have hB : (⟨grow (pack l) n.val.toNat dirty, n.val.toNat⟩ : BV) =
            ofList (unpack (grow (pack l) n.val.toNat dirty) n.val.toNat) := by
          apply eq_ofList_of_bits
          · rw [length_unpack]
          · dsimp only; rw [length_unpack, hG.1]
          · intro k
            dsimp only
            rw [getD_unpack]
            (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin
        rw [hB]
        refine resize_concl l _ n.val.toNat false (length_unpack _ _) (fun h => by cases h)
          (fun _ k hk => ?_)
        rw [getD_unpack]
        (repeat' split) <;> (try simp (disch := omega) only [hG.2]) <;> bfin

/-! ## Shifts -/

theorem unsignedI_val (k : JInt64) (h : 0 ≤ k.val) : (unsignedI k).val = k.val := by
  have hk := k.property
  show wrapInt .u64 k.val = k.val
  simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hk ⊢
  omega

theorem unsignedI_neg_val (k : JInt64) (h : k.val < 0) : (unsignedI (-k)).val = -k.val := by
  have hk := k.property
  show wrapInt .u64 (wrapInt .i64 (-k.val)) = -k.val
  simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hk ⊢
  omega

theorem shlU_ofList (l : List Bool) (u : JInt .u64) :
    shlU (ofList l) u =
      if u.val = 0 then ofList l else
      if u.val < l.length then
        ⟨copyChunks (List.replicate (numBitChunks l.length) 0) 1 (.other (pack l)) (u.val.toNat + 1)
          (l.length - u.val.toNat), l.length⟩
      else ⟨List.replicate (numBitChunks l.length) 0, l.length⟩ := rfl

theorem shrU_ofList (l : List Bool) (u : JInt .u64) :
    shrU (ofList l) u =
      if u.val = 0 then ofList l else
      if u.val < l.length then
        ⟨copyChunks (List.replicate (numBitChunks l.length) 0) (u.val.toNat + 1) (.other (pack l)) 1
          (l.length - u.val.toNat), l.length⟩
      else ⟨List.replicate (numBitChunks l.length) 0, l.length⟩ := rfl

theorem shlU_spec (l : List Bool) (u : JInt .u64) :
    shlU (ofList l) u = ofList ((List.range l.length).map fun t => l.getD (t + u.val.toNat) false) := by
  have hu := u.property
  rw [shlU_ofList]
  split
  · rename_i h0
    apply eq_ofList_of_bits
    · simp [ofList_len]
    · rw [ofList_chunks, pack_length]; simp
    · intro k
      rw [ofList_chunks, bitOf_pack, getD_map_range]
      bfin
  · rename_i h0
    split
    · rename_i h1
      have hC := copyChunks_spec (List.replicate (numBitChunks l.length) 0) 1 (.other (pack l))
        (u.val.toNat + 1) (l.length - u.val.toNat) (by omega) (by omega)
        (by simp only [List.length_replicate, numBitChunks_eq]; omega)
      apply eq_ofList_of_bits
      · simp
      · dsimp only; rw [hC.1]; simp
      · intro k
        dsimp only
        rw [hC.2 k, getD_map_range]
        simp only [Src.read, bitOf_pack, bitOf_replicate_zero]
        bfin
    · rename_i h1
      apply eq_ofList_of_bits
      · simp
      · simp
      · intro k
        dsimp only
        rw [bitOf_replicate_zero, getD_map_range]
        bfin

theorem shrU_spec (l : List Bool) (u : JInt .u64) :
    shrU (ofList l) u = ofList ((List.range l.length).map fun t =>
      if u.val.toNat ≤ t then l.getD (t - u.val.toNat) false else false) := by
  have hu := u.property
  rw [shrU_ofList]
  split
  · rename_i h0
    apply eq_ofList_of_bits
    · simp [ofList_len]
    · rw [ofList_chunks, pack_length]; simp
    · intro k
      rw [ofList_chunks, bitOf_pack, getD_map_range]
      bfin
  · rename_i h0
    split
    · rename_i h1
      have hC := copyChunks_spec (List.replicate (numBitChunks l.length) 0) (u.val.toNat + 1)
        (.other (pack l)) 1 (l.length - u.val.toNat) (by omega) (by omega)
        (by simp only [List.length_replicate, numBitChunks_eq]; omega)
      apply eq_ofList_of_bits
      · simp
      · dsimp only; rw [hC.1]; simp
      · intro k
        dsimp only
        rw [hC.2 k, getD_map_range]
        simp only [Src.read, bitOf_pack, bitOf_replicate_zero]
        bfin
    · rename_i h1
      apply eq_ofList_of_bits
      · simp
      · simp
      · intro k
        dsimp only
        rw [bitOf_replicate_zero, getD_map_range]
        bfin

theorem shift_proof : ShiftAgrees := by
  intro l k _
  have hk := k.property
  constructor
  · unfold shl
    split
    · rename_i hk0
      rw [shlU_spec, unsignedI_val k hk0]
      congr 1
      apply List.map_congr_left
      intro t _
      bfin
    · rename_i hk0
      rw [shrU_spec, unsignedI_neg_val k (by omega)]
      congr 1
      apply List.map_congr_left
      intro t _
      bfin
  · unfold shr
    split
    · rename_i hk0
      rw [shrU_spec, unsignedI_val k hk0]
      congr 1
      apply List.map_congr_left
      intro t _
      bfin
    · rename_i hk0
      rw [shlU_spec, unsignedI_neg_val k (by omega)]
      congr 1
      apply List.map_congr_left
      intro t _
      bfin

/-! ## `circshift!` -/

theorem remInt_len (k : JInt64) (n : Nat) (hn : 0 < n) (hl : n < 2 ^ 62) :
    JInt.remInt k (JInt.lit .i64 n) = pure (JInt.wrap .i64 (k.val.tmod n)) := by
  unfold JInt.remInt
  rw [lit_val (n : Int) (by omega) (by omega), if_neg (show ¬ ((n : Int) = 0) by omega)]
  rfl

/-- `rem(k, n)` (truncated) and `mod(k, n)` (floored) for `n > 0`. -/
theorem tmod_emod (k : Int) (n : Nat) (hn : 0 < n) :
    -(n : Int) < k.tmod n ∧ k.tmod n < n ∧
      k % n = (if 0 ≤ k.tmod n then k.tmod n else k.tmod n + n) := by
  have h1 := Int.lt_tmod_of_pos k (show (0 : Int) < n by omega)
  have h2 := Int.tmod_lt_of_pos k (show (0 : Int) < n by omega)
  have h3 := Int.emod_nonneg k (show (n : Int) ≠ 0 by omega)
  have h4 := Int.emod_lt_of_pos k (show (0 : Int) < n by omega)
  have h5 := @Int.tmod_eq_emod k n
  refine ⟨h1, h2, ?_⟩
  split at h5 <;> simp at h5 <;> split <;> omega

theorem circshift_none_eq (l : List Bool) (k R : JInt64)
    (hrem : JInt.remInt k (JInt.lit .i64 l.length) = pure R) :
    circshift (ofList l) none k =
      if R.val = 0 then pure (ofList l) else
      if R.val > 0 then pure ⟨copyChunks (copyChunks (pack l) (R.val.toNat + 1) (.other (pack l)) 1
          (l.length - R.val.toNat)) 1 (.other (pack l)) (l.length - R.val.toNat + 1) R.val.toNat, l.length⟩
      else pure ⟨copyChunks (copyChunks (pack l) 1 (.other (pack l)) ((-R.val).toNat + 1)
          (l.length - (-R.val).toNat)) (l.length - (-R.val).toNat + 1) (.other (pack l)) 1 (-R.val).toNat,
          l.length⟩ := by
  unfold circshift
  simp only [Option.getD, ne_eq, ofList_len, ofList_chunks, not_true_eq_false, ↓reduceIte, hrem,
    pure_bind] <;> rfl

theorem circshift_some_eq (l d : List Bool) (k R : JInt64) (hd : d.length = l.length)
    (hrem : JInt.remInt k (JInt.lit .i64 l.length) = pure R) :
    circshift (ofList d) (some (ofList l)) k =
      if R.val = 0 then copyto (ofList d) (ofList l) else
      if R.val > 0 then pure ⟨copyChunks (copyChunks (pack d) (R.val.toNat + 1) (.other (pack l)) 1
          (l.length - R.val.toNat)) 1 (.other (pack l)) (l.length - R.val.toNat + 1) R.val.toNat, l.length⟩
      else pure ⟨copyChunks (copyChunks (pack d) 1 (.other (pack l)) ((-R.val).toNat + 1)
          (l.length - (-R.val).toNat)) (l.length - (-R.val).toNat + 1) (.other (pack l)) 1 (-R.val).toNat,
          l.length⟩ := by
  unfold circshift
  simp only [Option.getD, ne_eq, ofList_len, ofList_chunks, hd, not_true_eq_false, ↓reduceIte, hrem,
    pure_bind, bind_pure] <;> rfl

theorem circ_ref (l : List Bool) (k R : JInt64) (hn : 0 < l.length)
    (t1 : -(l.length : Int) < R.val) (t2 : R.val < l.length)
    (t3 : k.val % l.length = if 0 ≤ R.val then R.val else R.val + l.length) :
    Ref.circshift l k =
      if R.val = 0 then l else
      if R.val > 0 then l.drop (l.length - R.val.toNat) ++ l.take (l.length - R.val.toNat)
      else l.drop (-R.val).toNat ++ l.take (-R.val).toNat := by
  unfold Ref.circshift
  dsimp only
  rw [if_neg (show ¬ (l.length = 0) by omega), t3]
  by_cases h0 : R.val = 0
  · rw [if_pos h0, if_pos (show 0 ≤ R.val by omega), h0]
    simp
  · rw [if_neg h0]
    by_cases hp : R.val > 0
    · rw [if_pos hp, if_pos (show 0 ≤ R.val by omega)]
    · rw [if_neg hp, if_neg (show ¬ 0 ≤ R.val by omega),
        show l.length - (R.val + ↑l.length).toNat = (-R.val).toNat by omega]

theorem rot_pos (l : List Bool) (d0 : List U64) (r : Nat) (hd0 : d0.length = numBitChunks l.length)
    (hd0b : ∀ p, l.length ≤ p → bitOf d0 p = false) (hr1 : 0 < r) (hr2 : r < l.length) :
    (⟨copyChunks (copyChunks d0 (r + 1) (.other (pack l)) 1 (l.length - r)) 1 (.other (pack l))
        (l.length - r + 1) r, l.length⟩ : BV) = ofList (l.drop (l.length - r) ++ l.take (l.length - r)) := by
  have hC1 := copyChunks_spec d0 (r + 1) (.other (pack l)) 1 (l.length - r) (by omega) (by omega)
    (by rw [hd0, numBitChunks_eq]; omega)
  have hC2 := copyChunks_spec (copyChunks d0 (r + 1) (.other (pack l)) 1 (l.length - r)) 1
    (.other (pack l)) (l.length - r + 1) r (by omega) (by omega) (by rw [hC1.1, hd0, numBitChunks_eq]; omega)
  apply eq_ofList_of_bits
  · simp only [List.length_append, List.length_drop, List.length_take]; omega
  · dsimp only
    rw [hC2.1, hC1.1, hd0, List.length_append, List.length_drop, List.length_take]
    congr 1; omega
  · intro p
    dsimp only
    rw [hC2.2 p, hC1.2 p, getD_append, getD_drop', getD_take']
    simp only [Src.read, bitOf_pack, List.length_drop]
    (repeat' split) <;> (try simp (disch := omega) only [hd0b]) <;> bfin

theorem rot_neg (l : List Bool) (d0 : List U64) (r : Nat) (hd0 : d0.length = numBitChunks l.length)
    (hd0b : ∀ p, l.length ≤ p → bitOf d0 p = false) (hr1 : 0 < r) (hr2 : r < l.length) :
    (⟨copyChunks (copyChunks d0 1 (.other (pack l)) (r + 1) (l.length - r)) (l.length - r + 1)
        (.other (pack l)) 1 r, l.length⟩ : BV) = ofList (l.drop r ++ l.take r) := by
  have hC1 := copyChunks_spec d0 1 (.other (pack l)) (r + 1) (l.length - r) (by omega) (by omega)
    (by rw [hd0, numBitChunks_eq]; omega)
  have hC2 := copyChunks_spec (copyChunks d0 1 (.other (pack l)) (r + 1) (l.length - r)) (l.length - r + 1)
    (.other (pack l)) 1 r (by omega) (by omega) (by rw [hC1.1, hd0, numBitChunks_eq]; omega)
  apply eq_ofList_of_bits
  · simp only [List.length_append, List.length_drop, List.length_take]; omega
  · dsimp only
    rw [hC2.1, hC1.1, hd0, List.length_append, List.length_drop, List.length_take]
    congr 1; omega
  · intro p
    dsimp only
    rw [hC2.2 p, hC1.2 p, getD_append, getD_drop', getD_take']
    simp only [Src.read, bitOf_pack, List.length_drop]
    (repeat' split) <;> (try simp (disch := omega) only [hd0b]) <;> bfin

theorem copyto_fold (dst src : List U64) (m : Nat) :
    ((List.range m).foldl (fun d j => cset d (j + 1) (cget src (j + 1))) dst).length = dst.length ∧
    ∀ p, m ≤ dst.length →
      bitOf ((List.range m).foldl (fun d j => cset d (j + 1) (cget src (j + 1))) dst) p =
        if p / 64 < m then bitOf src p else bitOf dst p := by
  induction m with
  | zero => exact ⟨rfl, fun p _ => by simp⟩
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [length_cset, ih.1], fun p hm => ?_⟩
    rw [bitOf_cset, ih.1, ih.2 p (by omega), getLsbD_cget]
    bfin

theorem copyto_ofList (l d : List Bool) (hd : d.length = l.length) (hn : 0 < l.length) :
    copyto (ofList d) (ofList l) = .ok (ofList l) := by
  have hpd : (pack d).length = (pack l).length := by rw [pack_length, pack_length, hd]
  have hpos : ¬ (pack l).length = 0 := by rw [pack_length, numBitChunks_eq]; omega
  have hF := copyto_fold (pack d) (pack l) ((pack l).length - 1)
  unfold copyto
  simp only [ofList_len, ofList_chunks, hd, hpd, Nat.min_self, gt_iff_lt, Nat.lt_irrefl, hpos,
    eq_self_iff_true, ↓reduceIte]
  congr 1
  apply eq_ofList_of_bits
  · rfl
  · dsimp only
    rw [length_cset, hF.1, hpd]
    exact pack_length l
  · intro p
    dsimp only
    rw [bitOf_cset, hF.1, hpd, hF.2 p (by omega), getLsbD_cget]
    simp only [bitOf_pack, pack_length, numBitChunks_eq] at *
    bfin

theorem circshift_proof : CircshiftNonemptyAgrees := by
  intro l d k hl hd hne
  have hn : 0 < l.length := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => simp
  have hrem := remInt_len k l.length hn hl
  obtain ⟨t1, t2, t3⟩ := tmod_emod k.val l.length hn
  have hR : (JInt.wrap .i64 (k.val.tmod ↑l.length)).val = k.val.tmod ↑l.length :=
    lit_val _ (by omega) (by omega)
  generalize JInt.wrap .i64 (k.val.tmod ↑l.length) = R at hrem hR
  rw [← hR] at t1 t2 t3
  have hpb : ∀ p, l.length ≤ p → bitOf (pack l) p = false := fun p hp => by
    rw [bitOf_pack]; exact getD_ge hp
  have hdb : ∀ p, l.length ≤ p → bitOf (pack d) p = false := fun p hp => by
    rw [bitOf_pack]; exact getD_ge (by omega)
  have hdl : (pack d).length = numBitChunks l.length := by rw [pack_length, hd]
  rw [circ_ref l k R hn t1 t2 t3]
  constructor
  · rw [circshift_none_eq l k R hrem]
    by_cases h0 : R.val = 0
    · rw [if_pos h0, if_pos h0]; rfl
    · rw [if_neg h0, if_neg h0]
      by_cases hp : R.val > 0
      · rw [if_pos hp, if_pos hp, rot_pos l (pack l) R.val.toNat (pack_length l) hpb (by omega) (by omega)]
        rfl
      · rw [if_neg hp, if_neg hp,
          rot_neg l (pack l) (-R.val).toNat (pack_length l) hpb (by omega) (by omega)]
        rfl
  · rw [circshift_some_eq l d k R hd hrem]
    by_cases h0 : R.val = 0
    · rw [if_pos h0, if_pos h0, copyto_ofList l d hd hn]; rfl
    · rw [if_neg h0, if_neg h0]
      by_cases hp : R.val > 0
      · rw [if_pos hp, if_pos hp, rot_pos l (pack d) R.val.toNat hdl hdb (by omega) (by omega)]
        rfl
      · rw [if_neg hp, if_neg hp, rot_neg l (pack d) (-R.val).toNat hdl hdb (by omega) (by omega)]
        rfl

/-! ## `reverse(B; dims)` -/

theorem foldl_mul_eq (xs : List Nat) : ∀ a, xs.foldl (· * ·) a = a * xs.foldl (· * ·) 1 := by
  induction xs with
  | nil => intro a; simp
  | cons x xs ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih (a * x), ih (1 * x), Nat.one_mul, Nat.mul_assoc]

theorem foldl_mul_pos : ∀ xs : List Nat, (∀ s ∈ xs, 0 < s) → 0 < xs.foldl (· * ·) 1
  | [], _ => Nat.one_pos
  | x :: xs, h => by
    simp only [List.foldl_cons]
    rw [foldl_mul_eq, Nat.one_mul]
    exact Nat.mul_pos (h x (by simp)) (foldl_mul_pos xs (fun s hs => h s (by simp [hs])))

theorem foldl_mul_one : ∀ xs : List Nat, (∀ s ∈ xs, s = 1) → xs.foldl (· * ·) 1 = 1
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp), Nat.one_mul]
    exact foldl_mul_one xs (fun s hs => h s (by simp [hs]))

theorem getD_nat (l : List Nat) (i : Nat) (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- `prod(dims) = prod(dims[1:e]) * dims[e+1] * prod(dims[e+2:end])`. -/
theorem foldl_mul_split (dims : List Nat) (e : Nat) (he : e < dims.length) :
    dims.foldl (· * ·) 1 =
      (dims.take e).foldl (· * ·) 1 * dims.getD e 0 * (dims.drop (e + 1)).foldl (· * ·) 1 := by
  have h : dims = dims.take e ++ dims[e] :: dims.drop (e + 1) := by
    rw [← List.drop_eq_getElem_cons he, List.take_append_drop]
  rw [getD_nat dims e he]
  conv => lhs; rw [h]
  simp only [List.foldl_append, List.foldl_cons]
  rw [foldl_mul_eq (dims.drop (e + 1))]

theorem all_of_filter_length {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, x, hx => by cases hx
  | a :: l, h, x, hx => by
    have hle := List.length_filter_le p l
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, ↓reduceIte, List.length_cons] at h
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]; exact hp
      · exact all_of_filter_length p l (by omega) x hx
    · simp only [List.filter_cons, hp, ↓reduceIte, List.length_cons, Bool.false_eq_true] at h
      omega

theorem mul_le_aux (M a b : Nat) (h : a + 1 ≤ b) : a * M + M ≤ M * b := by
  have := Nat.mul_le_mul_right M h
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm b M] at this
  exact this

/-- Position `k` in block `t` (of `M * sd` elements) at coordinate `c` along the
reversed dimension has `(k ÷ M) mod sd = c`. -/
theorem block_index (M sd t c k : Nat) (hM : 0 < M) (hc : c < sd)
    (hlo : M * sd * t + c * M ≤ k) (hhi : k < M * sd * t + c * M + M) : k / M % sd = c := by
  have e : k = M * (sd * t + c) + (k - (M * sd * t + c * M)) := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm M c]; omega
  rw [e, Nat.mul_add_div hM, Nat.div_eq_of_lt (show k - (M * sd * t + c * M) < M by omega), Nat.add_zero,
    Nat.add_comm (sd * t) c,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- Every position below `M * sd * R` lies in some block `t < R` at some coordinate `c < sd`. -/
theorem block_cover (M sd R k : Nat) (hM : 0 < M) (hsd : 0 < sd) (hk : k < M * sd * R) :
    ∃ t c, t < R ∧ c < sd ∧ M * sd * t + c * M ≤ k ∧ k < M * sd * t + c * M + M := by
  have h1 := Nat.div_add_mod k M
  have h2 := Nat.div_add_mod (k / M) sd
  have h3 : M * (k / M) = M * sd * (k / M / sd) + k / M % sd * M := by
    conv => lhs; rw [← h2]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm M (k / M % sd)]
  have h4 := Nat.mod_lt k hM
  refine ⟨k / M / sd, k / M % sd, ?_, Nat.mod_lt _ hsd, by omega, by omega⟩
  apply Nat.lt_of_not_le
  intro hcon
  have := Nat.mul_le_mul_left (M * sd) hcon
  omega

theorem stepRange_eq (S R N : Nat) (hS : 0 < S) (hR : 0 < R) (hN : N = S * R) :
    stepRange 0 (S : Int) ((N : Int) - (S : Int)) =
      pure ((List.range R).map (fun t : Nat => ((S * t : Nat) : Int))) := by
  have hSN : S ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right S hR
  unfold stepRange
  rw [if_neg (show ¬ ((S : Int) = 0) by omega), if_pos (show (S : Int) > 0 by omega),
    if_neg (show ¬ ((N : Int) - (S : Int) < 0) by omega)]
  have hdiv : ((N : Int) - (S : Int) - 0) / (S : Int) = (R : Int) - 1 := by
    rw [Int.sub_zero, hN, Int.natCast_mul,
      show (S : Int) * (R : Int) - (S : Int) = (S : Int) * ((R : Int) - 1) by rw [Int.mul_sub, Int.mul_one]]
    exact Int.mul_ediv_cancel_left _ (by omega)
  rw [hdiv, Int.sub_add_cancel, Int.toNat_natCast]
  show Except.ok _ = Except.ok _
  congr 1
  apply List.map_congr_left
  intro t _
  rw [Int.natCast_mul, Int.zero_add]

theorem kindOf_pure {α : Type} (x : α) : kindOf (pure x : Jl α) = .ok x := rfl

theorem foldlM_pure {α β : Type} (g : β → α → β) : ∀ (xs : List α) (b : β),
    xs.foldlM (m := Except JlError) (fun b a => pure (g b a)) b = pure (xs.foldl g b)
  | [], _ => rfl
  | a :: xs, b => by
    simp only [List.foldlM_cons, List.foldl_cons, pure_bind]
    exact foldlM_pure g xs (g b a)

theorem undef_len (n : Nat) (dirty : U64) : (BV.undef n dirty).len = n := rfl

theorem undef_chunks_length (n : Nat) (dirty : U64) :
    (BV.undef n dirty).chunks.length = numBitChunks n := by
  show (if numBitChunks n > 0 then csetEnd (List.replicate (numBitChunks n) dirty) 0
    else List.replicate (numBitChunks n) dirty).length = _
  split
  · rw [length_csetEnd, List.length_replicate]
  · rw [List.length_replicate]

theorem undef_bit_ge (n : Nat) (dirty : U64) (k : Nat) (hk : n ≤ k) :
    bitOf (BV.undef n dirty).chunks k = false := by
  show bitOf (if numBitChunks n > 0 then csetEnd (List.replicate (numBitChunks n) dirty) 0
    else List.replicate (numBitChunks n) dirty) k = false
  have hrep : ∀ k, bitOf (List.replicate (numBitChunks n) dirty) k =
      if k / 64 < numBitChunks n then dirty.getLsbD (k % 64) else false := by
    intro k
    rw [bitOf_def, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    by_cases h : k / 64 < numBitChunks n <;> simp [h]
  have hnc := numBitChunks_eq n
  split
  · rw [bitOf_csetEnd, List.length_replicate]
    split
    · exact getLsbD_zero64 _
    · rw [hrep]
      split
      · exfalso; omega
      · rfl
  · rw [hrep]
    split
    · exfalso; omega
    · rfl

/-- A fold whose every step writes the bits `P x` of a fixed pattern `f` and keeps the
others writes the bits of `f` at the union of the `P x`. -/
theorem fold_writes {α : Type} (g : BV → α → BV) (P : α → Nat → Prop) (f : Nat → Bool) (L n : Nat) :
    ∀ (xs : List α) (B : BV), B.chunks.length = L → B.len = n →
    (∀ x, x ∈ xs → ∀ B : BV, B.chunks.length = L → B.len = n →
      (g B x).chunks.length = L ∧ (g B x).len = n ∧
      ∀ k, (P x k → bitOf (g B x).chunks k = f k) ∧ (¬ P x k → bitOf (g B x).chunks k = bitOf B.chunks k)) →
    (xs.foldl g B).chunks.length = L ∧ (xs.foldl g B).len = n ∧
      ∀ k, ((∃ x ∈ xs, P x k) → bitOf (xs.foldl g B).chunks k = f k) ∧
        ((¬ ∃ x ∈ xs, P x k) → bitOf (xs.foldl g B).chunks k = bitOf B.chunks k)
  | [], B, hL, hn, _ => ⟨hL, hn, fun _ => ⟨fun ⟨_, hx, _⟩ => (by cases hx), fun _ => rfl⟩⟩
  | x :: xs, B, hL, hn, hg => by
    obtain ⟨hL1, hn1, hb1⟩ := hg x (by simp) B hL hn
    obtain ⟨hL2, hn2, hb2⟩ := fold_writes g P f L n xs (g B x) hL1 hn1
      (fun y hy => hg y (List.mem_cons_of_mem _ hy))
    rw [List.foldl_cons]
    refine ⟨hL2, hn2, fun k => ⟨fun hex => ?_, fun hno => ?_⟩⟩
    · obtain ⟨y, hy, hP⟩ := hex
      by_cases hrest : ∃ z ∈ xs, P z k
      · exact (hb2 k).1 hrest
      · rw [(hb2 k).2 hrest]
        rcases List.mem_cons.mp hy with hy | hy
        · rw [hy] at hP; exact (hb1 k).1 hP
        · exact absurd ⟨y, hy, hP⟩ hrest
    · have h1 : ¬ ∃ z ∈ xs, P z k := fun ⟨z, hz, hP⟩ => hno ⟨z, List.mem_cons_of_mem _ hz, hP⟩
      have h2 : ¬ P x k := fun hP => hno ⟨x, by simp, hP⟩
      rw [(hb2 k).2 h1, (hb1 k).2 h2]

/-- Such a fold started from `similar(B)` that writes exactly the positions `0:N-1` gives
the valid `BitVector` holding `f(0), …, f(N-1)`. -/
theorem fold_writes_eq {α : Type} (g : BV → α → BV) (P : α → Nat → Prop) (f : Nat → Bool) (N : Nat)
    (dirty : U64) (xs : List α)
    (hg : ∀ x, x ∈ xs → ∀ B : BV, B.chunks.length = numBitChunks N → B.len = N →
      (g B x).chunks.length = numBitChunks N ∧ (g B x).len = N ∧
      ∀ k, (P x k → bitOf (g B x).chunks k = f k) ∧ (¬ P x k → bitOf (g B x).chunks k = bitOf B.chunks k))
    (hcov : ∀ k, k < N → ∃ x ∈ xs, P x k)
    (hin : ∀ x k, x ∈ xs → P x k → k < N) :
    xs.foldl g (BV.undef N dirty) = ofList ((List.range N).map f) := by
  obtain ⟨hL, hn, hb⟩ := fold_writes g P f (numBitChunks N) N xs (BV.undef N dirty)
    (undef_chunks_length N dirty) (undef_len N dirty) hg
  apply eq_ofList_of_bits
  · rw [hn, List.length_map, List.length_range]
  · rw [hL, List.length_map, List.length_range]
  · intro k
    rw [getD_map_range]
    by_cases hk : k < N
    · rw [if_pos hk]
      exact (hb k).1 (hcov k hk)
    · rw [if_neg hk, (hb k).2 (fun ⟨x, hx, hP⟩ => hk (hin x k hx hP)), undef_bit_ge N dirty k (by omega)]

theorem reverseDims_proof : ReverseDimsNonemptyAgrees := by
  intro l dims d dirty _ hN h1 h2 hpos
  have hDl : d.val.toNat - 1 < dims.length := by omega
  have hsplit := foldl_mul_split dims (d.val.toNat - 1) hDl
  have hsd : 0 < dims.getD (d.val.toNat - 1) 0 := by
    rw [getD_nat dims _ hDl]
    exact hpos _ (List.getElem_mem hDl)
  have hM : 0 < (dims.take (d.val.toNat - 1)).foldl (· * ·) 1 :=
    foldl_mul_pos _ (fun s hs => hpos s (List.mem_of_mem_take hs))
  have hR : 0 < (dims.drop (d.val.toNat - 1 + 1)).foldl (· * ·) 1 :=
    foldl_mul_pos _ (fun s hs => hpos s (List.mem_of_mem_drop hs))
  have hones : ((List.range dims.length).filter
        (fun i => decide (dims.getD i 0 = 1 ∨ i + 1 = d.val.toNat))).length = dims.length →
      (dims.take (d.val.toNat - 1)).foldl (· * ·) 1 = 1 ∧
        (dims.drop (d.val.toNat - 1 + 1)).foldl (· * ·) 1 = 1 := by
    intro hf
    have hall := all_of_filter_length _ (List.range dims.length) (by rw [hf, List.length_range])
    have hi : ∀ i, i < dims.length → i ≠ d.val.toNat - 1 → dims.getD i 0 = 1 := by
      intro i hi hne
      have := of_decide_eq_true (hall i (List.mem_range.mpr hi))
      omega
    constructor
    · apply foldl_mul_one
      intro s hs
      obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hs
      have hi2 : i < d.val.toNat - 1 ∧ i < dims.length := by rw [List.length_take] at hi'; omega
      rw [List.getElem_take]
      exact (getD_nat dims i hi2.2).symm.trans (hi i hi2.2 (by omega))
    · apply foldl_mul_one
      intro s hs
      obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hs
      have hi2 : d.val.toNat - 1 + 1 + i < dims.length := by rw [List.length_drop] at hi'; omega
      rw [List.getElem_drop]
      exact (getD_nat dims _ hi2).symm.trans (hi _ hi2 (by omega))
  unfold dimsProd at hN
  rw [hsplit] at hN
  unfold reverseDims Ref.reverseDims dimsProd
  simp only [h1, h2, and_self, not_true_eq_false, ↓reduceIte, ofList_len, ofList_chunks]
  generalize dims.getD (d.val.toNat - 1) 0 = sd at hsd hN ⊢
  generalize (dims.take (d.val.toNat - 1)).foldl (· * ·) 1 = M at hM hN hones ⊢
  generalize (dims.drop (d.val.toNat - 1 + 1)).foldl (· * ·) 1 = R at hR hN hones
  have hjs := stepRange_eq (M * sd) R l.length (Nat.mul_pos hM hsd) hR hN
  have hnb := numBitChunks_eq l.length
  have hnc : l.length ≤ 64 * numBitChunks l.length := by omega
  split
  · -- `size(A, d) == 1`: a copy
    rename_i hs1
    subst hs1
    rw [kindOf_pure]
    congr 1
    show ofList l = _
    congr 1
    apply list_ext _ _ (by simp)
    intro k hk
    rw [getD_map_range, if_pos hk]
    show l.getD k false = l.getD (k - k / M % 1 * M + (1 - 1 - k / M % 1) * M) false
    simp only [Nat.mod_one, Nat.zero_mul, Nat.sub_zero, Nat.sub_self, Nat.add_zero]
  · split
    · -- every other dimension is a singleton: reverse the elements
      rename_i _ hf
      obtain ⟨hM1, hR1⟩ := hones hf
      subst hM1 hR1
      rw [kindOf_pure]
      congr 1
      apply fold_writes_eq (P := fun i k => k = i)
      · intro i hi B hL hn
        have hi' := List.mem_range.mp hi
        refine ⟨(length_unsafeBitset _ _ _).trans hL, hn, fun k => ⟨fun hP => ?_, fun hP => ?_⟩⟩
        · have hP' : k = i := hP
          show bitOf (unsafeBitset B.chunks (unsafeBitget (pack l) (sd - i)) (i + 1)) k =
            l.getD (k - k / 1 % sd * 1 + (sd - 1 - k / 1 % sd) * 1) false
          rw [bitOf_unsafeBitset]
          split
          · rw [unsafeBitget_eq, bitOf_pack, block_index 1 sd 0 k k (by omega) (by omega) (by omega) (by omega)]
            congr 1
            omega
          · exfalso; omega
        · have hP' : ¬ k = i := hP
          show bitOf (unsafeBitset B.chunks (unsafeBitget (pack l) (sd - i)) (i + 1)) k = bitOf B.chunks k
          rw [bitOf_unsafeBitset]
          split
          · exfalso; omega
          · rfl
      · intro k hk
        exact ⟨k, List.mem_range.mpr (by omega), rfl⟩
      · intro i k hi hP
        have hP' : k = i := hP
        have := List.mem_range.mp hi
        omega
    · split
      · -- `M == 1`: element loops
        rename_i _ _ hM1
        subst hM1
        rw [hjs]
        simp only [pure_bind]
        rw [kindOf_pure]
        congr 1
        apply fold_writes_eq (P := fun (j : Int) k => ∃ i ∈ List.range sd, k = j.toNat + (sd - i) - 1)
        · intro j hj B hL hn
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
          have ht' := List.mem_range.mp ht
          have hS := Nat.mul_le_mul_left (1 * sd) (show t + 1 ≤ R by omega)
          rw [Nat.mul_add, Nat.mul_one] at hS
          refine fold_writes _ (fun i k => k = 1 * sd * t + (sd - i) - 1) _ _ _ _ B hL hn ?_
          intro i hi B hL hn
          have hi' := List.mem_range.mp hi
          refine ⟨(length_unsafeBitset _ _ _).trans hL, hn, fun k => ⟨fun hP => ?_, fun hP => ?_⟩⟩
          · have hP' : k = 1 * sd * t + (sd - i) - 1 := hP
            show bitOf (unsafeBitset B.chunks (unsafeBitget (pack l) (1 * sd * t + i + 1))
                (1 * sd * t + (sd - i))) k =
              l.getD (k - k / 1 % sd * 1 + (sd - 1 - k / 1 % sd) * 1) false
            rw [bitOf_unsafeBitset]
            split
            · rw [unsafeBitget_eq, bitOf_pack,
                block_index 1 sd t (sd - 1 - i) k (by omega) (by omega) (by omega) (by omega),
                show sd - 1 - (sd - 1 - i) = i by omega]
              congr 1
              omega
            · exfalso; omega
          · have hP' : ¬ k = 1 * sd * t + (sd - i) - 1 := hP
            show bitOf (unsafeBitset B.chunks (unsafeBitget (pack l) (1 * sd * t + i + 1))
                (1 * sd * t + (sd - i))) k = bitOf B.chunks k
            rw [bitOf_unsafeBitset]
            split
            · exfalso; omega
            · rfl
        · intro k hk
          obtain ⟨t, c, ht, hc, hlo, hhi⟩ := block_cover 1 sd R k (by omega) hsd (by omega)
          refine ⟨((1 * sd * t : Nat) : Int), List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩,
            sd - 1 - c, List.mem_range.mpr (by omega), ?_⟩
          show k = 1 * sd * t + (sd - (sd - 1 - c)) - 1
          omega
        · intro j k hj hP
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
          obtain ⟨i, hi, hk⟩ := hP
          have ht' := List.mem_range.mp ht
          have hi' := List.mem_range.mp hi
          have hk' : k = 1 * sd * t + (sd - i) - 1 := hk
          have hS := Nat.mul_le_mul_left (1 * sd) (show t + 1 ≤ R by omega)
          rw [Nat.mul_add, Nat.mul_one] at hS
          omega
      · -- general case: block copies
        simp only [hjs, pure_bind]
        rw [foldlM_pure, kindOf_pure]
        congr 1
        apply fold_writes_eq (P := fun i k => ∃ j ∈ (List.range R).map (fun t : Nat => ((M * sd * t : Nat) : Int)),
            j.toNat + (sd - i - 1) * M ≤ k ∧ k < j.toNat + (sd - i - 1) * M + M)
        · intro i hi B hL hn
          have hi' := List.mem_range.mp hi
          have hb1 := mul_le_aux M (sd - i - 1) sd (by omega)
          have hb2 := mul_le_aux M i sd (by omega)
          refine fold_writes _ (fun (j : Int) k => j.toNat + (sd - i - 1) * M ≤ k ∧ k < j.toNat + (sd - i - 1) * M + M)
            _ _ _ _ B hL hn ?_
          intro j hj B hL hn
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
          have ht' := List.mem_range.mp ht
          have hS := Nat.mul_le_mul_left (M * sd) (show t + 1 ≤ R by omega)
          rw [Nat.mul_add, Nat.mul_one] at hS
          obtain ⟨hcl, hcb⟩ := copyChunks_spec B.chunks (M * sd * t + 1 + (sd - i - 1) * M) (.other (pack l))
            (M * sd * t + 1 + i * M) M (by omega) (by omega) (by rw [hL]; omega)
          refine ⟨hcl.trans hL, hn, fun k => ⟨fun hP => ?_, fun hP => ?_⟩⟩
          · have hP' : M * sd * t + (sd - i - 1) * M ≤ k ∧ k < M * sd * t + (sd - i - 1) * M + M := hP
            show bitOf (copyChunks B.chunks (M * sd * t + 1 + (sd - i - 1) * M) (.other (pack l))
                (M * sd * t + 1 + i * M) M) k =
              l.getD (k - k / M % sd * M + (sd - 1 - k / M % sd) * M) false
            rw [hcb k]
            split
            · show bitOf (pack l) _ = _
              rw [bitOf_pack, block_index M sd t (sd - i - 1) k hM (by omega) (by omega) (by omega),
                show sd - 1 - (sd - i - 1) = i by omega]
              congr 1
              omega
            · exfalso; omega
          · have hP' : ¬ (M * sd * t + (sd - i - 1) * M ≤ k ∧ k < M * sd * t + (sd - i - 1) * M + M) := hP
            show bitOf (copyChunks B.chunks (M * sd * t + 1 + (sd - i - 1) * M) (.other (pack l))
                (M * sd * t + 1 + i * M) M) k = bitOf B.chunks k
            rw [hcb k]
            split
            · exfalso; omega
            · rfl
        · intro k hk
          obtain ⟨t, c, ht, hc, hlo, hhi⟩ := block_cover M sd R k hM hsd (by omega)
          refine ⟨sd - 1 - c, List.mem_range.mpr (by omega), ((M * sd * t : Nat) : Int),
            List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩, ?_⟩
          show M * sd * t + (sd - (sd - 1 - c) - 1) * M ≤ k ∧ k < M * sd * t + (sd - (sd - 1 - c) - 1) * M + M
          rw [show sd - (sd - 1 - c) - 1 = c by omega]
          exact ⟨hlo, hhi⟩
        · intro i k hi hP
          obtain ⟨j, hj, hP⟩ := hP
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
          have ht' := List.mem_range.mp ht
          have hi' := List.mem_range.mp hi
          have hP' : M * sd * t + (sd - i - 1) * M ≤ k ∧ k < M * sd * t + (sd - i - 1) * M + M := hP
          have hS := Nat.mul_le_mul_left (M * sd) (show t + 1 ≤ R by omega)
          rw [Nat.mul_add, Nat.mul_one] at hS
          have hb1 := mul_le_aux M (sd - i - 1) sd (by omega)
          omega

end RangeSpec

open RangeSpec

theorem appendPrependAgrees : AppendPrependAgrees := fun l m dirty _ =>
  ⟨append_some_spec l m dirty, prepend_some_spec l m dirty, append_none_spec l dirty,
    prepend_none_spec l dirty⟩

theorem deleteatRangeInsideAgrees : DeleteatRangeInsideAgrees := deleteatRange_proof

theorem resizeNonnegAgrees : ResizeNonnegAgrees := resize_proof

theorem shiftAgrees : ShiftAgrees := shift_proof

theorem circshiftNonemptyAgrees : CircshiftNonemptyAgrees := circshift_proof

theorem reverseDimsNonemptyAgrees : ReverseDimsNonemptyAgrees := reverseDims_proof

end JuliaLean.BitArrays
