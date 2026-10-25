import JuliaLean.BitArrays.Properties

/-!
# Proof of `MapAgrees`

`bit_map!` rewrites the chunks `1:lenAc-1` with `f` of the source chunk and merges
the last one under `_msk_end`. The chunk-level effect is `final_spec`; the bit-level
comparison with the `Vector{Bool}` result goes through `ext_pack`.
-/

namespace JuliaLean.BitArrays

namespace MapProof

theorem numBitChunks_eq (n : Nat) : numBitChunks n = (n + 63) / 64 := by
  unfold numBitChunks div64 mod64
  split <;> omega

theorem getD_ge {α : Type} (l : List α) (d : α) (i : Nat) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getLsbD_foldl_twoPow (f : Nat → Bool) : ∀ (L : List Nat) (acc : U64) (i : Nat),
    (L.foldl (fun acc j => if f j then acc ||| BitVec.twoPow 64 j else acc) acc).getLsbD i =
      (acc.getLsbD i || (decide (i ∈ L) && f i && decide (i < 64)))
  | [], acc, i => by simp
  | a :: L, acc, i => by
    rw [List.foldl_cons, getLsbD_foldl_twoPow f L]
    by_cases hia : i = a
    · subst hia
      cases hf : f i <;> by_cases hi : i < 64 <;> simp [hf, hi, BitVec.getLsbD_or, BitVec.getLsbD_twoPow]
    · have hai : a ≠ i := fun h => hia h.symm
      cases hf : f a <;> simp [hf, hia, hai, BitVec.getLsbD_or, BitVec.getLsbD_twoPow]

theorem chunkAt_getLsbD (l : List Bool) (c j : Nat) :
    (chunkAt l c).getLsbD j = (decide (j < 64) && l.getD (64 * c + j) false) := by
  have h := getLsbD_foldl_twoPow (fun j => l.getD (64 * c + j) false) (List.range 64) 0 j
  unfold chunkAt
  rw [h]
  by_cases hj : j < 64 <;> simp [hj]

theorem liftBits_getLsbD (g : Bool → Bool → Bool) (x y : U64) (j : Nat) :
    (liftBits g x y).getLsbD j = (decide (j < 64) && g (x.getLsbD j) (y.getLsbD j)) := by
  have h := getLsbD_foldl_twoPow (fun j => g (x.getLsbD j) (y.getLsbD j)) (List.range 64) 0 j
  unfold liftBits
  rw [h]
  by_cases hj : j < 64 <;> simp [hj]

theorem pack_length (l : List Bool) : (pack l).length = numBitChunks l.length := by
  simp [pack]

theorem pack_getD (l : List Bool) (c : Nat) :
    (pack l).getD c 0 = if c < numBitChunks l.length then chunkAt l c else 0 := by
  by_cases h : c < numBitChunks l.length
  · rw [if_pos h]
    simp [pack, List.getD_eq_getElem?_getD, h]
  · rw [if_neg h, getD_ge _ _ _ (by rw [pack_length]; omega)]

theorem pack_bit (l : List Bool) (c j : Nat) :
    ((pack l).getD c 0).getLsbD j = (decide (j < 64) && l.getD (64 * c + j) false) := by
  rw [pack_getD]
  split
  · exact chunkAt_getLsbD l c j
  · rename_i h
    rw [numBitChunks_eq] at h
    rw [getD_ge l false _ (by omega)]
    simp

theorem bitOf_pack (l : List Bool) (k : Nat) : bitOf (pack l) k = l.getD k false := by
  unfold bitOf
  rw [pack_bit, show 64 * (k / 64) + k % 64 = k by omega]
  simp [Nat.mod_lt k (by decide : 64 > 0)]

theorem ext_pack (cs : List U64) (l : List Bool) (hlen : cs.length = numBitChunks l.length)
    (hbits : ∀ k, bitOf cs k = l.getD k false) : cs = pack l := by
  apply List.ext_getElem
  · rw [hlen, pack_length]
  · intro c h1 h2
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have e1 := hbits (64 * c + j)
    unfold bitOf at e1
    rw [show (64 * c + j) / 64 = c by omega, show (64 * c + j) % 64 = j by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e1
    have e2 := pack_bit l c j
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e2
    rw [e1, e2]
    simp [hj]

theorem getLsbD_mskEnd (n j : Nat) :
    (mskEnd n).getLsbD j = decide ((64 - n % 64) % 64 + j < 64) := by
  unfold mskEnd msk64
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]

theorem getD_set (v : U64) : ∀ (l : List U64) (d i : Nat),
    (l.set d v).getD i 0 = if i = d ∧ d < l.length then v else l.getD i 0
  | [], _, _ => by simp
  | _ :: _, 0, 0 => by simp
  | _ :: _, 0, _ + 1 => by simp
  | _ :: _, _ + 1, 0 => by simp
  | _ :: xs, d + 1, i + 1 => by
    rw [List.set_cons_succ, List.getD_cons_succ, List.getD_cons_succ, getD_set v xs d i]
    by_cases hid : i = d
    · subst hid
      by_cases hl : i < xs.length
      · simp [hl]
      · have : ¬ (i + 1 < xs.length + 1) := by omega
        simp [hl, this]
    · have : ¬ (i + 1 = d + 1) := by omega
      simp [hid, this]

theorem length_cset (cs : List U64) (k : Nat) (v : U64) : (cset cs k v).length = cs.length := by
  simp [cset]

theorem getD_cset (cs : List U64) (k : Nat) (v : U64) (c : Nat) (hk : 1 ≤ k) :
    (cset cs k v).getD c 0 = if c = k - 1 ∧ k - 1 < cs.length then v else cs.getD c 0 := by
  unfold cset
  rw [getD_set]

/-- The loop `for j in 1:n; dest[j] = F(j-1, dest[j]); end` on chunks. -/
theorem fold_spec (F : Nat → U64 → U64) (step : List U64 → Nat → List U64)
    (hstep : ∀ d j, step d j = cset d (j + 1) (F j (cget d (j + 1)))) (cs : List U64) :
    ∀ n, ((List.range n).foldl step cs).length = cs.length ∧
      ∀ c, ((List.range n).foldl step cs).getD c 0 =
        if c < n ∧ c < cs.length then F c (cs.getD c 0) else cs.getD c 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hstep]
    obtain ⟨h1, h2⟩ := fold_spec F step hstep cs n
    refine ⟨by rw [length_cset, h1], fun c => ?_⟩
    rw [getD_cset _ _ _ _ (by omega), h1, Nat.add_sub_cancel]
    unfold cget
    rw [Nat.add_sub_cancel, h2, h2]
    by_cases hc : c = n
    · subst hc
      by_cases hl : c < cs.length
      · simp [hl]
      · simp [hl]
    · have : (c < n + 1) ↔ c < n := by omega
      simp [hc, this]

theorem final_spec (F : Nat → U64 → U64) (step : List U64 → Nat → List U64)
    (hstep : ∀ d j, step d j = cset d (j + 1) (F j (cget d (j + 1)))) (D : List U64) (L : Nat)
    (hL : 1 ≤ L) (hLD : L ≤ D.length) (Y : U64) :
    cget ((List.range (L - 1)).foldl step D) L = D.getD (L - 1) 0 ∧
    (cset ((List.range (L - 1)).foldl step D) L Y).length = D.length ∧
    ∀ c, (cset ((List.range (L - 1)).foldl step D) L Y).getD c 0 =
      if c < L - 1 then F c (D.getD c 0) else if c = L - 1 then Y else D.getD c 0 := by
  obtain ⟨h1, h2⟩ := fold_spec F step hstep D (L - 1)
  refine ⟨?_, by rw [length_cset, h1], fun c => ?_⟩
  · unfold cget
    rw [h2, if_neg (by omega)]
  · rw [getD_cset _ _ _ _ hL, h1, h2]
    by_cases hc : c < L - 1
    · rw [if_neg (fun h => by omega), if_pos ⟨hc, by omega⟩, if_pos hc]
    · rw [if_neg hc]
      by_cases he : c = L - 1
      · rw [if_pos ⟨he, by omega⟩, if_pos he]
      · rw [if_neg (fun h => he h.1), if_neg (fun h => hc h.1), if_neg he]

theorem tgt1_getD (a d : List Bool) (ha : a.length ≤ d.length) (k : Nat) :
    (a.map (!·) ++ d.drop a.length).getD k false =
      if k < a.length then !(a.getD k false) else d.getD k false := by
  by_cases h : k < a.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_eq_getElem h]
    rfl
  · rw [if_neg h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop, List.length_map,
      show a.length + (k - a.length) = k by omega]

theorem tgt2_getD (a b d : List Bool) (g : Bool → Bool → Bool) (k : Nat) :
    (List.zipWith g (a.take b.length) (b.take a.length) ++ d.drop (min a.length b.length)).getD k false =
      if k < min a.length b.length then g (a.getD k false) (b.getD k false) else d.getD k false := by
  have hlen : (List.zipWith g (a.take b.length) (b.take a.length)).length = min a.length b.length := by
    simp [List.length_zipWith, List.length_take]
    omega
  by_cases h : k < min a.length b.length
  · rw [if_pos h]
    have ha : k < a.length := by omega
    have hb : k < b.length := by omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega), List.getElem?_zipWith, List.getElem?_take,
      List.getElem?_take, if_pos hb, if_pos ha, List.getElem?_eq_getElem ha,
      List.getElem?_eq_getElem hb]
    rfl
  · rw [if_neg h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_drop, hlen,
      show min a.length b.length + (k - min a.length b.length) = k by omega]

/-- The chunks produced by `bit_map!(!, dest, A)` hold `[.!A; dest[length(A)+1:end]]`. -/
theorem map1_result (a d : List Bool) (ha : a.length ≤ d.length) (ha0 : a.length ≠ 0) (R : List U64)
    (hRl : R.length = (pack d).length)
    (hR : ∀ c, R.getD c 0 = if c < numBitChunks a.length - 1 then ~~~((pack a).getD c 0)
      else if c = numBitChunks a.length - 1 then
        ((pack d).getD c 0 &&& ~~~(mskEnd a.length)) ||| (~~~((pack a).getD c 0) &&& mskEnd a.length)
      else (pack d).getD c 0) :
    R = pack (a.map (!·) ++ d.drop a.length) := by
  have htl : (a.map (!·) ++ d.drop a.length).length = d.length := by simp; omega
  apply ext_pack
  · rw [hRl, pack_length, htl]
  · intro k
    unfold bitOf
    have hj : k % 64 < 64 := Nat.mod_lt _ (by decide)
    have hk : 64 * (k / 64) + k % 64 = k := by omega
    have hn := numBitChunks_eq a.length
    rw [hR, tgt1_getD a d ha]
    by_cases h1 : k / 64 < numBitChunks a.length - 1
    · rw [if_pos h1, BitVec.getLsbD_not, pack_bit, hk, if_pos (by omega)]
      simp [hj]
    · rw [if_neg h1]
      by_cases h2 : k / 64 = numBitChunks a.length - 1
      · rw [if_pos h2, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and,
          BitVec.getLsbD_not, BitVec.getLsbD_not, getLsbD_mskEnd, pack_bit, pack_bit, hk]
        by_cases h3 : k < a.length
        · rw [if_pos h3, decide_eq_true (show (64 - a.length % 64) % 64 + k % 64 < 64 by omega)]
          simp [hj]
        · rw [if_neg h3, decide_eq_false (show ¬ ((64 - a.length % 64) % 64 + k % 64 < 64) by omega)]
          simp [hj]
      · rw [if_neg h2, pack_bit, hk, if_neg (by omega)]
        simp [hj]

theorem map1_some (d a : List Bool) (ha : a.length ≤ d.length) :
    bitMap1 (fun x => ~~~x) (BV.ofList d) (some (BV.ofList a)) =
      .ok (BV.ofList (a.map (!·) ++ d.drop a.length)) := by
  by_cases ha0 : a.length = 0
  · have : a = [] := List.eq_nil_of_length_eq_zero ha0
    subst this
    simp [bitMap1, BV.ofList]
  · have hn := numBitChunks_eq a.length
    have hnd := numBitChunks_eq d.length
    obtain ⟨hlast, hl, hg⟩ := final_spec (fun j _ => ~~~(cget (pack a) (j + 1)))
      (fun d j => cset d (j + 1) (~~~(cget (pack a) (j + 1)))) (fun _ _ => rfl) (pack d)
      (numBitChunks a.length) (by omega) (by rw [pack_length]; omega)
      (((pack d).getD (numBitChunks a.length - 1) 0 &&& ~~~(mskEnd a.length)) |||
        (~~~(cget (pack a) (numBitChunks a.length)) &&& mskEnd a.length))
    simp only [bitMap1, BV.ofList, Option.getD_some, Option.elim, pack_length]
    rw [if_neg (by omega), if_neg ha0, hlast]
    have htl : (a.map (!·) ++ d.drop a.length).length = d.length := by simp; omega
    rw [htl, map1_result a d ha ha0 _ hl (fun c => by
      rw [hg c]
      unfold cget
      rw [Nat.add_sub_cancel]
      by_cases h1 : c < numBitChunks a.length - 1
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : c = numBitChunks a.length - 1
        · rw [if_pos h2, if_pos h2, h2]
        · rw [if_neg h2, if_neg h2])]

theorem map1_none (d : List Bool) :
    bitMap1 (fun x => ~~~x) (BV.ofList d) none = .ok (BV.ofList (d.map (!·))) := by
  have hdd : d.map (!·) = d.map (!·) ++ d.drop d.length := by simp
  by_cases hd0 : d.length = 0
  · have : d = [] := List.eq_nil_of_length_eq_zero hd0
    subst this
    simp [bitMap1, BV.ofList]
  · have hnd := numBitChunks_eq d.length
    obtain ⟨hlast, hl, hg⟩ := final_spec (fun _ x => ~~~x)
      (fun d j => cset d (j + 1) (~~~(cget d (j + 1)))) (fun _ _ => rfl) (pack d)
      (numBitChunks d.length) (by omega) (by rw [pack_length]; omega)
      (((pack d).getD (numBitChunks d.length - 1) 0 &&& ~~~(mskEnd d.length)) |||
        (~~~((pack d).getD (numBitChunks d.length - 1) 0) &&& mskEnd d.length))
    simp only [bitMap1, BV.ofList, Option.getD_none, Option.elim, pack_length]
    rw [if_neg (by omega), if_neg hd0, hlast]
    have htl : (d.map (!·)).length = d.length := by simp
    rw [htl, hdd, map1_result d d (Nat.le_refl _) hd0 _ hl (fun c => by
      rw [hg c]
      by_cases h1 : c < numBitChunks d.length - 1
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : c = numBitChunks d.length - 1
        · rw [if_pos h2, if_pos h2, h2]
        · rw [if_neg h2, if_neg h2])]

theorem map2_eq (d a b : List Bool) (g : Bool → Bool → Bool) (ha : a.length ≤ d.length)
    (hb : b.length ≤ d.length) :
    bitMap2 (liftBits g) (BV.ofList d) (BV.ofList a) (BV.ofList b) =
      .ok (BV.ofList (List.zipWith g (a.take b.length) (b.take a.length) ++
        d.drop (min a.length b.length))) := by
  have htl : (List.zipWith g (a.take b.length) (b.take a.length) ++
      d.drop (min a.length b.length)).length = d.length := by
    simp [List.length_zipWith, List.length_take]
    omega
  by_cases ha0 : a.length = 0
  · have : a = [] := List.eq_nil_of_length_eq_zero ha0
    subst this
    simp [bitMap2, BV.ofList]
  by_cases hb0 : b.length = 0
  · have : b = [] := List.eq_nil_of_length_eq_zero hb0
    subst this
    simp [bitMap2, BV.ofList]
  have hna := numBitChunks_eq a.length
  have hnb := numBitChunks_eq b.length
  have hnd := numBitChunks_eq d.length
  have hnm := numBitChunks_eq (min a.length b.length)
  have hL : min (numBitChunks a.length) (numBitChunks b.length) = numBitChunks (min a.length b.length) := by
    omega
  obtain ⟨hlast, hl, hg⟩ := final_spec
    (fun j _ => liftBits g (cget (pack a) (j + 1)) (cget (pack b) (j + 1)))
    (fun d j => cset d (j + 1) (liftBits g (cget (pack a) (j + 1)) (cget (pack b) (j + 1))))
    (fun _ _ => rfl) (pack d)
    (numBitChunks (min a.length b.length)) (by omega) (by rw [pack_length]; omega)
    (((pack d).getD (numBitChunks (min a.length b.length) - 1) 0 &&& ~~~(mskEnd (min a.length b.length))) |||
      (liftBits g (cget (pack a) (numBitChunks (min a.length b.length)))
        (cget (pack b) (numBitChunks (min a.length b.length))) &&& mskEnd (min a.length b.length)))
  simp only [bitMap2, BV.ofList, pack_length]
  rw [if_neg (by omega), if_neg ha0, if_neg hb0, hL, hlast, htl]
  congr 2
  apply ext_pack
  · rw [hl, pack_length, htl]
  · intro k
    unfold bitOf
    have hj : k % 64 < 64 := Nat.mod_lt _ (by decide)
    have hk : 64 * (k / 64) + k % 64 = k := by omega
    rw [hg, tgt2_getD]
    unfold cget
    by_cases h1 : k / 64 < numBitChunks (min a.length b.length) - 1
    · rw [if_pos h1, Nat.add_sub_cancel, liftBits_getLsbD, pack_bit, pack_bit, hk, if_pos (by omega)]
      simp [hj]
    · rw [if_neg h1]
      by_cases h2 : k / 64 = numBitChunks (min a.length b.length) - 1
      · rw [if_pos h2, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and,
          BitVec.getLsbD_not, getLsbD_mskEnd, liftBits_getLsbD, ← h2, pack_bit, pack_bit,
          pack_bit, hk]
        by_cases h3 : k < min a.length b.length
        · rw [if_pos h3, decide_eq_true (show (64 - min a.length b.length % 64) % 64 + k % 64 < 64 by omega)]
          simp [hj]
        · rw [if_neg h3,
            decide_eq_false (show ¬ ((64 - min a.length b.length % 64) % 64 + k % 64 < 64) by omega)]
          simp [hj]
      · rw [if_neg h2, pack_bit, hk, if_neg (by omega)]
        simp [hj]

end MapProof

open MapProof in
theorem mapAgrees : MapAgrees := by
  intro d a b g _ ha hb
  exact ⟨map1_some d a ha, map1_none d, map2_eq d a b g ha hb⟩

end JuliaLean.BitArrays
