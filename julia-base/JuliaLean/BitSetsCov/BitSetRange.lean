import JuliaLean.BitSetsCov.BitSetMatched2

/-!
# `union!(s::BitSet, a:b)`

The growth steps keep the chunk view; the three masks of the update set
exactly the bits of `a:b` in the first and last chunk and every bit in
between.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

theorem Cg_appendZeros (b : List U64) (k : Nat) (B c : Int) :
    Cg (b ++ List.replicate k 0) B c = Cg b B c := by
  rw [Cg_def, Cg_def]
  split
  · exact getD_append_zeros k b _
  · rfl

theorem Cg_zerosAppend (b : List U64) (k : Nat) (B B' c : Int) (h : B' = B - k) :
    Cg (List.replicate k 0 ++ b) B' c = Cg b B c := by
  subst h
  rw [Cg_def, Cg_def, getD_zeros_append]
  by_cases hc : 0 ≤ c - B
  · rw [if_pos (by omega), if_pos hc, if_neg (by omega), show (c - (B - k)).toNat - k = (c - B).toNat by omega]
  · rw [if_neg hc]
    split
    · rw [if_pos (by omega)]
    · rfl

theorem Cg_orAt (b : List U64) (i : Nat) (m : U64) (B c : Int) (hi : 1 ≤ i) (hl : i ≤ b.length) :
    Cg (orAt b i m) B c = if c = B + i - 1 then Cg b B c ||| m else Cg b B c := by
  unfold orAt
  by_cases hc : 0 ≤ c - B
  · have e1 : ∀ a : List U64, Cg a B c = a.getD (c - B).toNat 0 := fun a => by rw [Cg_def, if_pos hc]
    rw [e1, e1, getD_vset _ _ _ _ hi (by omega)]
    by_cases h : c = B + i - 1
    · rw [if_pos (by omega), if_pos h]
      unfold vget
      rw [show i - 1 = (c - B).toNat by omega]
    · rw [if_neg (by omega), if_neg h]
  · rw [Cg_out _ _ _ (Or.inl (by omega)), Cg_out b _ _ (Or.inl (by omega)), if_neg (by omega)]

def fillF (u : U64) (_i : Nat) (_v : U64) : U64 := u

theorem Cg_fill (b : List U64) (lo n : Nat) (u : U64) (B c : Int) (hlo : 1 ≤ lo)
    (hn : n ≠ 0 → lo - 1 + n ≤ b.length) :
    Cg (vfold lo (fillF u) n b) B c = if B + lo - 1 ≤ c ∧ c < B + lo - 1 + n then u else Cg b B c := by
  have hf := (fold_vset b lo hlo (fillF u) n hn).2
  by_cases hc : 0 ≤ c - B
  · have e1 : ∀ a : List U64, Cg a B c = a.getD (c - B).toNat 0 := fun a => by rw [Cg_def, if_pos hc]
    rw [e1, e1, hf]
    by_cases hr : B + lo - 1 ≤ c ∧ c < B + lo - 1 + n
    · rw [if_pos (by omega), if_pos hr]; rfl
    · rw [if_neg (by omega), if_neg hr]
  · rw [Cg_out _ _ _ (Or.inl (by omega)), Cg_out b _ _ (Or.inl (by omega)), if_neg (by omega)]

theorem length_fill (b : List U64) (lo n : Nat) (u : U64) (hlo : 1 ≤ lo) (hn : n ≠ 0 → lo - 1 + n ≤ b.length) :
    (vfold lo (fillF u) n b).length = b.length := (fold_vset b lo hlo (fillF u) n hn).1

theorem length_orAt (b : List U64) (i : Nat) (m : U64) : (orAt b i m).length = b.length := by
  unfold orAt; exact length_vset _ _ _

/-! ## The three masks -/

theorem getLsbD_ones (k : Nat) : (~~~(0 : U64)).getLsbD k = decide (k < 64) := by
  change msk64.getLsbD k = decide (k < 64)
  unfold msk64
  rw [BitVec.getLsbD_allOnes]

theorem mask_both (i j k : Nat) (hj : j < 64) (hk : k < 64) :
    (((~~~(0 : U64) >>> i) <<< (i + 63 - j)) >>> (63 - j)).getLsbD k = decide (i ≤ k ∧ k ≤ j) := by
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_ones]
  by_cases h1 : k ≤ j
  · by_cases h2 : i ≤ k
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega
  · simp [h1]; omega

theorem mask_low (i k : Nat) (hk : k < 64) :
    ((~~~(0 : U64) >>> i) <<< i).getLsbD k = decide (i ≤ k) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_ones]
  by_cases h2 : i ≤ k
  · simp [h2]; omega
  · simp [h2]

theorem mask_high (j k : Nat) (hj : j < 64) (hk : k < 64) :
    ((~~~(0 : U64) <<< (63 - j)) >>> (63 - j)).getLsbD k = decide (k ≤ j) := by
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, getLsbD_ones]
  by_cases h1 : k ≤ j
  · simp [h1]; omega
  · simp [h1]; omega

/-- The update part of `union!(s, a:b)` once the chunks cover `a` and `b`. -/
def urTail (bits : List U64) (off diffa diffb : Int) (i j : Nat) : BitSetS :=
  let u : U64 := ~~~0
  let bits :=
    if diffa = diffb then
      orAt bits (diffa + 1).toNat (((u >>> i) <<< (i + 63 - j)) >>> (63 - j))
    else
      let bits := orAt bits (diffa + 1).toNat ((u >>> i) <<< i)
      let bits := orAt bits (diffb + 1).toNat ((u <<< (63 - j)) >>> (63 - j))
      (List.range (diffb - diffa - 1).toNat).foldl (fun bits (k : Nat) => vset bits (diffa + 2 + (k : Int)).toNat u) bits
  ⟨bits, off⟩

theorem unionRangeBits_eq (s : BitSetS) (a b : JInt64) (dirty : U64) :
    unionRangeBits s a b dirty =
      let cidxa := a.val / 64
      let cidxb := b.val / 64
      let off := if s.offset = noOffset then cidxa else s.offset
      let len : Int := s.bits.length
      let diffa := cidxa - off
      let diffb := cidxb - off
      let bits := if diffb ≥ len then growend0 s.bits (diffb - len + 1).toNat dirty else s.bits
      match (if diffa < 0 then (growbeg0 bits (-diffa).toNat dirty, cidxa, (0 : Int), diffb - diffa)
          else (bits, off, diffa, diffb)) with
      | (bits, off, diffa, diffb) => urTail bits off diffa diffb (a.val % 64).toNat (b.val % 64).toNat := rfl

theorem fill_eq (bits : List U64) (d : Int) (n : Nat) (u : U64) (hd : 0 ≤ d) :
    (List.range n).foldl (fun bits (k : Nat) => vset bits (d + 2 + (k : Int)).toNat u) bits =
      vfold (d + 2).toNat (fillF u) n bits := by
  unfold vfold fillF
  congr 1
  funext bs k
  rw [show (d + 2 + (k : Int)).toNat = (d + 2).toNat + k by omega]

/-- `urTail` adds the integers of `a:b` to the chunks. -/
theorem Cg_urTail (bits : List U64) (off a b : Int) (hab : a ≤ b)
    (ha : off ≤ a / 64) (hb : b / 64 < off + bits.length) (c : Int) (k : Nat) (hk : k < 64) :
    let r := urTail bits off (a / 64 - off) (b / 64 - off) (a % 64).toNat (b % 64).toNat
    (Cg r.bits r.offset c).getLsbD k = ((Cg bits off c).getLsbD k || decide (a ≤ 64 * c + k ∧ 64 * c + k ≤ b)) := by
  intro r
  have hj : (b % 64).toNat < 64 := by omega
  show (Cg (urTail bits off (a / 64 - off) (b / 64 - off) (a % 64).toNat (b % 64).toNat).bits off c).getLsbD k = _
  unfold urTail
  simp only []
  by_cases he : a / 64 - off = b / 64 - off
  · rw [if_pos he, Cg_orAt _ _ _ _ _ (by omega) (by omega)]
    by_cases hc : c = off + ((a / 64 - off + 1).toNat : Int) - 1
    · rw [if_pos hc, BitVec.getLsbD_or, mask_both _ _ _ hj hk]
      congr 1
      apply decide_eq_decide.mpr
      omega
    · rw [if_neg hc]
      have : ¬ (a ≤ 64 * c + k ∧ 64 * c + k ≤ b) := by omega
      simp [this]
  · rw [if_neg he, fill_eq _ _ _ _ (by omega),
      Cg_fill _ _ _ _ _ _ (by omega) (by intro; rw [length_orAt, length_orAt]; omega),
      Cg_orAt _ _ _ _ _ (by omega) (by rw [length_orAt]; omega), Cg_orAt _ _ _ _ _ (by omega) (by omega)]
    by_cases h1 : off + ((a / 64 - off + 2).toNat : Int) - 1 ≤ c ∧
        c < off + ((a / 64 - off + 2).toNat : Int) - 1 + ((b / 64 - off - (a / 64 - off) - 1).toNat : Int)
    · rw [if_pos h1, getLsbD_ones]
      have : a ≤ 64 * c + k ∧ 64 * c + k ≤ b := by omega
      simp [this, hk]
    · rw [if_neg h1]
      by_cases h2 : c = off + ((b / 64 - off + 1).toNat : Int) - 1
      · rw [if_pos h2, if_neg (by omega), BitVec.getLsbD_or, mask_high _ _ hj hk]
        congr 1
        apply decide_eq_decide.mpr
        omega
      · rw [if_neg h2]
        by_cases h3 : c = off + ((a / 64 - off + 1).toNat : Int) - 1
        · rw [if_pos h3, BitVec.getLsbD_or, mask_low _ _ hk]
          congr 1
          apply decide_eq_decide.mpr
          omega
        · rw [if_neg h3]
          have : ¬ (a ≤ 64 * c + k ∧ 64 * c + k ≤ b) := by omega
          simp [this]

theorem length_urTail (bits : List U64) (off a b : Int) (hab : a ≤ b)
    (ha : off ≤ a / 64) (hb : b / 64 < off + bits.length) :
    (urTail bits off (a / 64 - off) (b / 64 - off) (a % 64).toNat (b % 64).toNat).bits.length = bits.length ∧
    (urTail bits off (a / 64 - off) (b / 64 - off) (a % 64).toNat (b % 64).toNat).offset = off := by
  unfold urTail
  simp only []
  refine ⟨?_, trivial⟩
  split
  · exact length_orAt _ _ _
  · rw [fill_eq _ _ _ _ (by omega), length_fill _ _ _ _ (by omega) (by intro; rw [length_orAt, length_orAt]; omega),
      length_orAt, length_orAt]

theorem unionRangeBits_spec (s : BitSetS) (hs : WF s) (a b : JInt64) (hab : a.val ≤ b.val) (dirty : U64) :
    WF (unionRangeBits s a b dirty) ∧
    ∀ x, mem (unionRangeBits s a b dirty) x = (mem s x || decide (a.val ≤ x ∧ x ≤ b.val)) := by
  have hab' := jint64_bounds' a
  have hbb' := jint64_bounds' b
  have hn := noOffset_val
  rw [unionRangeBits_eq]
  simp only []
  generalize hoff : (if s.offset = noOffset then a.val / 64 else s.offset) = off
  have hview0 : ∀ c, Cg s.bits off c = Cg s.bits s.offset c := by
    intro c
    by_cases ho : s.offset = noOffset
    · rw [hs.1 ho, Cg_nil, Cg_nil]
    · rw [if_neg ho] at hoff; rw [hoff]
  have hoffb : s.offset ≠ noOffset → off = s.offset := fun ho => by rw [if_neg ho] at hoff; exact hoff.symm
  have hoffa : s.offset = noOffset → off = a.val / 64 := fun ho => by rw [if_pos ho] at hoff; exact hoff.symm
  have hlen0 : s.offset = noOffset → s.bits.length = 0 := fun ho => by rw [hs.1 ho]; rfl
  generalize hb1 : (if b.val / 64 - off ≥ (s.bits.length : Int) then
    growend0 s.bits (b.val / 64 - off - s.bits.length + 1).toNat dirty else s.bits) = bits1
  have hv1 : ∀ c, Cg bits1 off c = Cg s.bits off c := by
    intro c; rw [← hb1]; split
    · rw [growend0_eq, Cg_appendZeros]
    · rfl
  have hl1 : (bits1.length : Int) = max (s.bits.length : Int) (b.val / 64 - off + 1) := by
    rw [← hb1]; split
    · rw [growend0_eq]; simp; omega
    · omega
  have key : ∀ bits2 off2, (∀ c, Cg bits2 off2 c = Cg s.bits s.offset c) → off2 ≤ a.val / 64 →
      b.val / 64 < off2 + bits2.length → off2 = min off (a.val / 64) →
      (bits2.length : Int) + off2 = max (bits1.length + off) (b.val / 64 + 1) →
      WF (urTail bits2 off2 (a.val / 64 - off2) (b.val / 64 - off2) (a.val % 64).toNat (b.val % 64).toNat) ∧
      ∀ x, mem (urTail bits2 off2 (a.val / 64 - off2) (b.val / 64 - off2) (a.val % 64).toNat (b.val % 64).toNat) x =
        (mem s x || decide (a.val ≤ x ∧ x ≤ b.val)) := by
    intro bits2 off2 hv2 h1 h2 h3 h4
    obtain ⟨hl, ho⟩ := length_urTail bits2 off2 a.val b.val hab h1 h2
    constructor
    · constructor
      · intro h; rw [ho] at h
        by_cases hs0 : s.offset = noOffset
        · have := hoffa hs0; omega
        · have := hoffb hs0; have := hs.2 hs0; omega
      · intro _; rw [hl, ho]
        by_cases hs0 : s.offset = noOffset
        · have := hoffa hs0; have := hlen0 hs0; omega
        · have := hoffb hs0; have := hs.2 hs0; omega
    · intro x
      rw [mem_Cg, mem_Cg]
      have := Cg_urTail bits2 off2 a.val b.val hab h1 h2 (x / 64) (x % 64).toNat (by omega)
      simp only [] at this
      rw [this, hv2, show 64 * (x / 64) + ((x % 64).toNat : Int) = x by omega]
  by_cases hd : a.val / 64 - off < 0
  · rw [if_pos hd]
    simp only []
    rw [show b.val / 64 - off - (a.val / 64 - off) = b.val / 64 - a.val / 64 by omega,
      show (0 : Int) = a.val / 64 - a.val / 64 by omega]
    rw [show b.val / 64 - a.val / 64 = b.val / 64 - a.val / 64 by rfl]
    apply key
    · intro c; rw [growbeg0_eq, Cg_zerosAppend _ _ off _ _ (by omega), hv1, hview0]
    · omega
    · rw [growbeg0_eq]; simp; omega
    · omega
    · rw [growbeg0_eq]; simp; omega
  · rw [if_neg hd]
    simp only []
    apply key
    · intro c; rw [hv1, hview0]
    · omega
    · omega
    · omega
    · omega

theorem unionRange_spec : BitSetUnionRangeSpec := by
  intro s a b dirty hs
  refine ⟨fun h => by unfold unionRange; rw [if_pos h], fun hab ha hb => ?_, fun hab hn => ?_⟩
  · unfold unionRange
    rw [if_neg (by omega), toInt_ok ha, toInt_ok hb]
    obtain ⟨hw, hm⟩ := unionRangeBits_spec s hs ⟨a, (inIntRange_iff a).mp ha⟩ ⟨b, (inIntRange_iff b).mp hb⟩ hab dirty
    exact ⟨_, rfl, hw, hm⟩
  · unfold unionRange
    rw [if_neg (by omega)]
    by_cases ha : inIntRange a
    · rcases hn with h | h
      · exact absurd ha h
      · rw [toInt_ok ha, toInt_err h]; rfl
    · rw [toInt_err ha]; rfl

theorem unionOne_spec (c : BitSetS) (dirty : U64) (hc : WF c) (a : Arg) (ha : a.ok) :
    ∃ c', unionOne c dirty a = .ok c' ∧ WF c' ∧ ∀ x, mem c' x = (mem c x || a.mem x) := by
  cases a with
  | bitset t =>
    obtain ⟨c', h, hw, hm⟩ := matchedMap_spec .or c t dirty hc ha
    exact ⟨c', h, hw, fun x => by rw [hm]; rfl⟩
  | range a b =>
    by_cases hba : b < a
    · refine ⟨c, (unionRange_spec c a b dirty hc).1 hba, hc, fun x => ?_⟩
      have : ¬ (a ≤ x ∧ x ≤ b) := by omega
      simp [Arg.mem, this]
    · rcases ha with h | ⟨h1, h2⟩
      · exact absurd h hba
      · obtain ⟨c', h, hw, hm⟩ := (unionRange_spec c a b dirty hc).2.1 (by omega) h1 h2
        exact ⟨c', h, hw, fun x => by rw [hm]; rfl⟩
  | itr xs =>
    obtain ⟨c', h, hw, hm⟩ := unionItr_spec xs c hc ha
    exact ⟨c', h, hw, fun x => by rw [hm]; rfl⟩

theorem unionFold_spec (dirty : U64) : ∀ (sets : List Arg) (c : BitSetS), WF c → (∀ a ∈ sets, a.ok) →
    ∃ s', sets.foldlM (fun c a => unionOne c dirty a) c = .ok s' ∧ WF s' ∧
      ∀ x, mem s' x = (mem c x || sets.any (fun a => a.mem x))
  | [], c, hc, _ => ⟨c, rfl, hc, fun x => by simp⟩
  | a :: rest, c, hc, hok => by
    obtain ⟨c', h1, hw1, hm1⟩ := unionOne_spec c dirty hc a (hok a (List.mem_cons_self ..))
    obtain ⟨s', h2, hw2, hm2⟩ := unionFold_spec dirty rest c' hw1 (fun b hb => hok b (List.mem_cons_of_mem _ hb))
    refine ⟨s', ?_, hw2, fun x => ?_⟩
    · rw [List.foldlM_cons, h1]; exact h2
    · rw [hm2, hm1, List.any_cons, Bool.or_assoc]

end BS

theorem bitSetUnionRangeSpec : BitSetUnionRangeSpec := BS.unionRange_spec

theorem bitSetUnionSpec : BitSetUnionSpec := by
  intro s sets dirty hs hok
  unfold BS.union
  rw [(bitSetCopySpec BS.new s dirty).2.1]
  exact BS.unionFold_spec dirty sets s hs hok

theorem bitSetMatchedSpec : BitSetMatchedSpec :=
  ⟨BS.matchedMap_spec, fun s1 s2 dirty h1 h2 =>
    ⟨BS.matchedMap_spec .or s1 s2 dirty h1 h2, BS.matchedMap_spec .and s1 s2 dirty h1 h2,
      BS.matchedMap_spec .andNot s1 s2 dirty h1 h2, BS.matchedMap_spec .xor s1 s2 dirty h1 h2,
      BS.intersect_spec s1 s2 dirty h1 h2⟩⟩

end JuliaLean.BitSetsCov
