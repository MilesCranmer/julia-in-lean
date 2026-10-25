import JuliaLean.BitArrays.Basic

/-!
# Proof of `ReverseAgrees`

With `nc` chunks `D`, `k = mod64(n + 63) + 1` valid bits in the last chunk and
`h = 64 - k`, the reversed vector has chunk `c` (1-based)
`T c = (bitreverse(D[nc+1-c]) >>> h) | (bitreverse(D[nc-c]) << k)`, where `D[0]` counts
as `0`. After `m` iterations, `reverseLoop` has written `T` into chunks `1:m` and
`nc-m+1:nc`, holds `bitreverse(D[m]) << k` in chunk `nc-m`, and leaves the chunks
between untouched (`S`).
-/

namespace JuliaLean.BitArrays

namespace ReverseProof

/-- `bitreverse(D[x])`, `0` for `x = 0`. -/
def Rv (D : List U64) (x : Nat) : U64 := if x = 0 then 0 else bitreverse (cget D x)

/-- Chunk `c` of the result. -/
def T (D : List U64) (k h c : Nat) : U64 :=
  (Rv D (D.length + 1 - c) >>> h) ||| (Rv D (D.length - c) <<< k)

/-- Chunk `c` after `m` loop iterations. -/
def S (D : List U64) (k h m c : Nat) : U64 :=
  if c ≤ m ∨ D.length - m < c then T D k h c
  else if c = D.length - m then Rv D m <<< k
  else cget D c

/-- The step after the loop, `base/bitarray.jl:1307-1311`. -/
def Fin (nc k h : Nat) : Nat × Nat × U64 × U64 × List U64 → List U64
  | (i, _, u, v, bc) =>
    if nc % 2 = 1 then cset bc i (cget bc i ||| (v >>> h)) else cset bc i (cget bc i ||| (u <<< k))

theorem zero_or64 (x : U64) : (0 : U64) ||| x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

theorem zero_shl64 (n : Nat) : (0 : U64) <<< n = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

theorem cget_cset_eq {cs : List U64} {x y : Nat} {v : U64} (hxy : y = x) (hx : 1 ≤ x)
    (hl : x ≤ cs.length) : cget (cset cs x v) y = v := by
  subst hxy
  unfold cget cset
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl, if_pos (by omega)]
  rfl

theorem cget_cset_ne {cs : List U64} {x y : Nat} {v : U64} (hxy : y ≠ x) (hx : 1 ≤ x)
    (hy : 1 ≤ y) : cget (cset cs x v) y = cget cs y := by
  unfold cget cset
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_neg (by omega),
    ← List.getD_eq_getElem?_getD]

theorem loop_spec (D : List U64) (k h : Nat) : ∀ (fuel m j : Nat) (u v : U64) (bc : List U64),
    2 * m < D.length → D.length ≤ 2 * (m + fuel) → j = D.length - m → u = Rv D m →
    v = Rv D (D.length - m) → bc.length = D.length →
    (∀ c, 1 ≤ c → c ≤ D.length → cget bc c = S D k h m c) →
    (Fin D.length k h (reverseLoop k h fuel m j u v bc)).length = D.length ∧
    ∀ c, 1 ≤ c → c ≤ D.length → cget (Fin D.length k h (reverseLoop k h fuel m j u v bc)) c = T D k h c := by
  intro fuel
  induction fuel with
  | zero => intro m j u v bc h1 h2; omega
  | succ fuel ih =>
    intro m j u v bc hm hf hj hu hv hbc hinv
    subst hj hu hv
    simp only [reverseLoop]
    by_cases s1 : m + 1 = D.length - m
    · rw [if_pos s1]
      simp only [Fin]
      rw [if_pos (by omega)]
      refine ⟨by rw [length_cset, hbc], fun c hc1 hc2 => ?_⟩
      by_cases hc : c = m + 1
      · subst hc
        have e1 : D.length + 1 - (m + 1) = D.length - m := by omega
        have e2 : D.length - (m + 1) = m := by omega
        simp (disch := first | omega | (simp only [length_cset]; omega)) only
          [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, T, Rv, zero_or64,
            hinv, e1, e2] <;>
          first | rfl | exact BitVec.or_comm _ _
      · simp (disch := first | omega | (simp only [length_cset]; omega)) only
          [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, hinv]
    · rw [if_neg s1]
      by_cases s2 : m + 1 = D.length - m - 1
      · rw [if_pos s2]
        simp only [Fin]
        rw [if_neg (by omega)]
        refine ⟨by simp only [length_cset, hbc], fun c hc1 hc2 => ?_⟩
        by_cases hc : c = m + 1
        · subst hc
          have e1 : D.length + 1 - (m + 1) = D.length - m := by omega
          have e2 : D.length - (m + 1) = m + 1 := by omega
          simp (disch := first | omega | (simp only [length_cset]; omega)) only
            [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, T, Rv, zero_or64,
              hinv, e1, e2] <;>
            first | rfl | exact BitVec.or_comm _ _
        · by_cases hc' : c = D.length - m
          · subst hc'
            have e1 : D.length + 1 - (D.length - m) = m + 1 := by omega
            have e2 : D.length - (D.length - m) = m := by omega
            simp (disch := first | omega | (simp only [length_cset]; omega)) only
              [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, T, Rv, zero_or64,
                hinv, e1, e2] <;>
              first | rfl | exact BitVec.or_comm _ _
          · simp (disch := first | omega | (simp only [length_cset]; omega)) only
              [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, hinv]
      · rw [if_neg s2]
        have e3 : D.length - m - 1 = D.length - (m + 1) := by omega
        apply ih (m + 1) (D.length - m - 1)
        · omega
        · omega
        · exact e3
        · simp (disch := first | omega | (simp only [length_cset]; omega)) only
            [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, Rv, hinv]
        · rw [← e3]
          simp (disch := first | omega | (simp only [length_cset]; omega)) only
            [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, Rv, hinv]
        · simp only [length_cset, hbc]
        · intro c hc1 hc2
          by_cases hA : c = m + 1
          · subst hA
            have e1 : D.length + 1 - (m + 1) = D.length - m := by omega
            have e2 : D.length - (m + 1) = D.length - m - 1 := by omega
            simp (disch := first | omega | (simp only [length_cset]; omega)) only
              [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, T, Rv, zero_or64,
                hinv, e1, e2] <;>
              first | rfl | exact BitVec.or_comm _ _
          by_cases hB : c = D.length - m
          · subst hB
            have e1 : D.length + 1 - (D.length - m) = m + 1 := by omega
            have e2 : D.length - (D.length - m) = m := by omega
            simp (disch := first | omega | (simp only [length_cset]; omega)) only
              [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, T, Rv, zero_or64,
                hinv, e1, e2] <;>
              first | rfl | exact BitVec.or_comm _ _
          by_cases hC : c = D.length - m - 1
          · subst hC
            simp (disch := first | omega | (simp only [length_cset]; omega)) only
              [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, Rv, zero_or64,
                hinv, ← e3] <;>
              first | rfl | exact BitVec.or_comm _ _
          · by_cases hD : c ≤ m ∨ D.length - m < c
            · simp (disch := first | omega | (simp only [length_cset]; omega)) only
                [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, hinv]
            · simp (disch := first | omega | (simp only [length_cset]; omega)) only
                [cget_cset_eq, cget_cset_ne, length_cset, if_pos, if_neg, S, hinv]

theorem getD_reverse (l : List Bool) (p : Nat) :
    l.reverse.getD p false = if p < l.length then l.getD (l.length - 1 - p) false else false := by
  by_cases hp : p < l.length
  · rw [if_pos hp, List.getD_eq_getElem?_getD, List.getElem?_reverse hp, ← List.getD_eq_getElem?_getD]
  · rw [if_neg hp, getD_ge (by simp only [List.length_reverse]; omega)]

theorem Rv_bit (l : List Bool) (x s : Nat) (hx : 1 ≤ x) (hs : s < 64) :
    (Rv (pack l) x).getLsbD s = l.getD (64 * (x - 1) + (63 - s)) false := by
  unfold Rv bitreverse
  rw [if_neg (by omega), BitVec.getLsbD_reverse]
  simp only [BitVec.getMsbD, hs, decide_true, Bool.true_and]
  rw [getLsbD_cget, if_pos (by omega), bitOf_pack, show 64 - 1 - s = 63 - s by omega]

theorem T_bit (l : List Bool) (n k h c t : Nat) (hn0 : n ≠ 0) (hln : l.length = n)
    (hk : k = (n + 63) % 64 + 1) (hh : h = 64 - k)
    (hc1 : 1 ≤ c) (hc2 : c ≤ (pack l).length) (ht : t < 64) :
    (T (pack l) k h c).getLsbD t = l.reverse.getD (64 * (c - 1) + t) false := by
  have hnc := pack_length l
  rw [numBitChunks_eq, hln] at hnc
  unfold T
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, getLsbD_shl, getD_reverse, hln]
  by_cases hA : t < k
  · rw [Rv_bit l _ _ (by omega) (by omega), if_neg (by omega), Bool.or_false, if_pos (by omega)]
    congr 1
    omega
  · rw [getLsbD_ge64 _ (by omega), Bool.false_or, if_pos ⟨ht, by omega⟩]
    by_cases hB : c = (pack l).length
    · rw [show (pack l).length - c = 0 by omega]
      unfold Rv
      rw [if_pos rfl, getLsbD_zero64, if_neg (by omega)]
    · rw [Rv_bit l _ _ (by omega) (by omega), if_pos (by omega)]
      congr 1
      omega

end ReverseProof

open ReverseProof in
theorem reverseAgrees : ReverseAgrees := by
  intro l _
  by_cases hn : l.length = 0
  · have : l = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    rfl
  have hnc := pack_length l
  rw [numBitChunks_eq] at hnc
  have hnc0 : (pack l).length ≠ 0 := by omega
  have key := loop_spec (pack l) (mod64 (l.length + 63) + 1) (64 - (mod64 (l.length + 63) + 1))
    ((pack l).length + 1) 0 (pack l).length 0 (bitreverse (cget (pack l) (pack l).length))
    (cset (pack l) (pack l).length 0) (by omega) (by omega) (by omega)
    (by simp [Rv])
    (by simp only [Rv, Nat.sub_zero, if_neg hnc0])
    (by rw [length_cset])
    (fun c hc1 hc2 => by
      by_cases hc : c = (pack l).length
      · subst hc
        rw [cget_cset_eq rfl (by omega) (by omega)]
        unfold S Rv
        rw [if_neg (by omega), if_pos (by omega), if_pos rfl, zero_shl64]
      · rw [cget_cset_ne hc (by omega) hc1]
        unfold S
        rw [if_neg (by omega), if_neg (by omega)])
  obtain ⟨hFl, hFv⟩ := key
  have hrev : reverse (BV.ofList l) = ⟨Fin (pack l).length (mod64 (l.length + 63) + 1)
      (64 - (mod64 (l.length + 63) + 1))
      (reverseLoop (mod64 (l.length + 63) + 1) (64 - (mod64 (l.length + 63) + 1))
        ((pack l).length + 1) 0 (pack l).length 0 (bitreverse (cget (pack l) (pack l).length))
        (cset (pack l) (pack l).length 0)), l.length⟩ := by
    simp only [reverse, BV.ofList, hn, ↓reduceIte]
    generalize reverseLoop (mod64 (l.length + 63) + 1) (64 - (mod64 (l.length + 63) + 1))
        ((pack l).length + 1) 0 (pack l).length 0 (bitreverse (cget (pack l) (pack l).length))
        (cset (pack l) (pack l).length 0) = r
    obtain ⟨i, j, u, v, bc⟩ := r
    rfl
  rw [hrev]
  apply eq_ofList_of_bits
  · simp
  · rw [hFl, List.length_reverse, pack_length]
  · intro p
    by_cases hp : p / 64 < (pack l).length
    · rw [bitOf_def, show p / 64 = p / 64 + 1 - 1 by omega]
      show (cget _ (p / 64 + 1)).getLsbD (p % 64) = _
      rw [hFv (p / 64 + 1) (by omega) (by omega),
        T_bit l l.length _ _ _ _ hn rfl (by unfold mod64; rfl) rfl (by omega) (by omega)
          (Nat.mod_lt _ (by decide)),
        show 64 * (p / 64 + 1 - 1) + p % 64 = p by omega]
    · rw [bitOf_ge (by rw [hFl]; omega), getD_ge (by simp only [List.length_reverse]; omega)]

end JuliaLean.BitArrays
