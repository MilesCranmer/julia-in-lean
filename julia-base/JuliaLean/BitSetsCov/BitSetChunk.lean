import JuliaLean.BitSetsCov.BitSetProof1

/-!
# Chunk-level view of `BitSet` membership

`ch a k` is the 0-based chunk `k` of a chunk vector (zero outside it) and
`Cg bits off c` the chunk holding the global chunk index `c`. Two states have
the same members exactly when they have the same chunks everywhere, which
reduces `==` and `issubset` to chunk comparisons.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

/-- 0-based chunk `k` of `a`, zero outside `a`. -/
def ch (a : List U64) (k : Int) : U64 := if 0 ≤ k then a.getD k.toNat 0 else 0

/-- The chunk with global chunk index `c`. -/
def Cg (bits : List U64) (off c : Int) : U64 := ch bits (c - off)

theorem ch_neg (a : List U64) {k : Int} (h : k < 0) : ch a k = 0 := by
  unfold ch; rw [if_neg (by omega)]

theorem ch_ge (a : List U64) {k : Int} (h : (a.length : Int) ≤ k) : ch a k = 0 := by
  unfold ch; rw [if_pos (by omega), getD_ge _ _ (by omega)]

theorem getD_ch (a : List U64) {k : Int} (h : 0 ≤ k) : a.getD k.toNat 0 = ch a k := by
  unfold ch; rw [if_pos h]

theorem ch_nat (a : List U64) (k : Nat) : ch a k = a.getD k 0 := by
  unfold ch; rw [if_pos (by omega)]; rfl

theorem vget_ch (a : List U64) {k : Int} (h : 1 ≤ k) : vget a k.toNat = ch a (k - 1) := by
  unfold vget ch; rw [if_pos (by omega), show k.toNat - 1 = (k - 1).toNat by omega]

theorem G_Cg (bits : List U64) (off c : Int) (j : Nat) : G bits off c j = (Cg bits off c).getLsbD j := by
  unfold G Cg ch
  split
  · rfl
  · simp

theorem mem_Cg (s : BitSetS) (x : Int) :
    mem s x = (Cg s.bits s.offset (x / 64)).getLsbD (x % 64).toNat := G_Cg _ _ _ _

/-- Membership is determined by the chunks, and conversely. -/
theorem mem_ext (s t : BitSetS) :
    (∀ x, mem s x = mem t x) ↔ ∀ c, Cg s.bits s.offset c = Cg t.bits t.offset c := by
  constructor
  · intro h c
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have := h (64 * c + j)
    rw [mem_Cg, mem_Cg, show (64 * c + j) / 64 = c by omega,
      show ((64 * c + (j : Int)) % 64).toNat = j by omega] at this
    exact this
  · intro h x
    rw [mem_Cg, mem_Cg, h]

/-- Inclusion of members is bitwise inclusion of the chunks. -/
theorem mem_sub (s t : BitSetS) :
    (∀ x, mem s x = true → mem t x = true) ↔
      ∀ c (j : Nat), (Cg s.bits s.offset c).getLsbD j = true → (Cg t.bits t.offset c).getLsbD j = true := by
  constructor
  · intro h c j hj
    by_cases hj64 : j < 64
    · have := h (64 * c + j)
      rw [mem_Cg, mem_Cg, show (64 * c + j) / 64 = c by omega,
        show ((64 * c + (j : Int)) % 64).toNat = j by omega] at this
      exact this hj
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)] at hj; exact absurd hj (by simp)
  · intro h x hx
    rw [mem_Cg] at hx ⊢
    exact h _ _ hx

/-! ## Loops over integer ranges -/

theorem check0_ch (a : List U64) (b e : Int) (hb : 1 ≤ b) :
    check0 a b e = true ↔ ∀ i : Int, b ≤ i → i ≤ e → ch a (i - 1) = 0 := by
  rw [check0_iff a b e hb]
  constructor
  · intro h i h1 h2; rw [← getD_ch _ (by omega)]; exact h i h1 h2
  · intro h i h1 h2; rw [getD_ch _ (by omega)]; exact h i h1 h2

theorem memeq_ch (a1 : List U64) (i : Int) (a2 : List U64) (n : Int) (hi : 1 ≤ i) :
    memeq a1 i a2 n = true ↔ ∀ k : Int, 0 ≤ k → k < n → ch a1 (i - 1 + k) = ch a2 k := by
  unfold memeq
  rw [List.all_eq_true]
  constructor
  · intro h k h1 h2
    have := h k.toNat (List.mem_range.mpr (by omega))
    rw [vget_ch _ (by omega), show (1 + k.toNat : Nat) = k.toNat + 1 by omega] at this
    simp only [beq_iff_eq] at this
    rw [show i + (k.toNat : Int) - 1 = i - 1 + k by omega] at this
    rw [this]
    unfold vget ch; rw [if_pos h1]; rfl
  · intro h k hk
    have hk' := List.mem_range.mp hk
    have := h k (by omega) (by omega)
    rw [vget_ch _ (by omega), show i + (k : Int) - 1 = i - 1 + k by omega, this]
    simp only [beq_iff_eq]
    unfold vget ch; rw [if_pos (by omega)]; simp

theorem rngAll (lo hi : Int) (P : Int → Bool) :
    ((List.range (hi - lo + 1).toNat).map (fun (k : Nat) => lo + (k : Int))).all P = true ↔
      ∀ k : Int, lo ≤ k → k ≤ hi → P k = true := by
  rw [List.all_eq_true]
  constructor
  · intro h k h1 h2
    have := h k (List.mem_map.mpr ⟨(k - lo).toNat, List.mem_range.mpr (by omega), by omega⟩)
    exact this
  · intro h k hk
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hk
    have := List.mem_range.mp hm
    exact h _ (by omega) (by omega)

/-! ## `==` -/

/-- The body of `==(s1, s2)` after the swap that makes `b1 ≤ b2`. -/
def eqBody (a1 : List U64) (b1 : Int) (a2 : List U64) (b2 : Int) : Bool :=
  let l1 : Int := a1.length
  let l2 : Int := a2.length
  let e1 := l1 + b1
  let overlap0 := max 0 (e1 - b2)
  let included := decide (overlap0 ≥ l2)
  let overlap := if included then l2 else overlap0
  if !check0 a1 1 (l1 - overlap0) then false
  else if (if included then !check0 a1 (b2 - b1 + l2 + 1) l1 else !check0 a2 (1 + overlap) l2) then false
  else if overlap > 0 then memeq a1 (b2 - b1 + 1) a2 overlap
  else true

theorem eq_body (s1 s2 : BitSetS) :
    eq s1 s2 = if s1.offset > s2.offset then eqBody s2.bits s2.offset s1.bits s1.offset
      else eqBody s1.bits s1.offset s2.bits s2.offset := by
  unfold eq eqBody
  by_cases h : s1.offset > s2.offset
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem ite3 (c1 c2 m : Bool) (p : Prop) [Decidable p] :
    (if (!c1) = true then false else if (!c2) = true then false else if p then m else true) = true ↔
      c1 = true ∧ c2 = true ∧ (p → m = true) := by
  cases c1 <;> cases c2 <;> by_cases hp : p <;> simp [hp]

theorem eqBody_iff (a1 : List U64) (b1 : Int) (a2 : List U64) (b2 : Int) (hb : b1 ≤ b2) :
    eqBody a1 b1 a2 b2 = true ↔ ∀ c, Cg a1 b1 c = Cg a2 b2 c := by
  unfold eqBody Cg
  simp only []
  have z1 : ∀ k, (k < 0 ∨ (a1.length : Int) ≤ k) → ch a1 k = 0 := fun k h => by
    rcases h with h | h
    · exact ch_neg _ h
    · exact ch_ge _ h
  have z2 : ∀ k, (k < 0 ∨ (a2.length : Int) ≤ k) → ch a2 k = 0 := fun k h => by
    rcases h with h | h
    · exact ch_neg _ h
    · exact ch_ge _ h
  by_cases hinc : max 0 ((a1.length : Int) + b1 - b2) ≥ (a2.length : Int)
  · have hd : decide (max 0 ((a1.length : Int) + b1 - b2) ≥ (a2.length : Int)) = true := decide_eq_true hinc
    rw [if_pos hd, if_pos hd, ite3, check0_ch _ _ _ (by omega), check0_ch _ _ _ (by omega),
      memeq_ch _ _ _ _ (by omega)]
    constructor
    · intro ⟨h1, h2, h⟩ c
      by_cases hc1 : c - b1 < 0
      · rw [z1 _ (Or.inl hc1), z2 _ (Or.inl (by omega))]
      by_cases hc2 : c < b2
      · rw [z2 _ (Or.inl (by omega))]
        by_cases hc3 : (a1.length : Int) ≤ c - b1
        · exact z1 _ (Or.inr hc3)
        · have := h1 (c - b1 + 1) (by omega) (by omega)
          rwa [show c - b1 + 1 - 1 = c - b1 by omega] at this
      by_cases hc4 : c - b2 < (a2.length : Int)
      · have := h (by omega) (c - b2) (by omega) hc4
        rwa [show b2 - b1 + 1 - 1 + (c - b2) = c - b1 by omega] at this
      · rw [z2 _ (Or.inr (by omega))]
        by_cases hc3 : (a1.length : Int) ≤ c - b1
        · exact z1 _ (Or.inr hc3)
        · have := h2 (c - b1 + 1) (by omega) (by omega)
          rwa [show c - b1 + 1 - 1 = c - b1 by omega] at this
    · intro h
      have e : ∀ k, ch a1 k = ch a2 (k + b1 - b2) := fun k => by
        have := h (k + b1); rwa [show k + b1 - b1 = k by omega] at this
      refine ⟨?_, ?_, ?_⟩
      · intro i h1 h2
        rw [e, z2 _ (Or.inl (by omega))]
      · intro i h1 h2
        rw [e, z2 _ (Or.inr (by omega))]
      · intro _ k h1 h2
        rw [e, show b2 - b1 + 1 - 1 + k + b1 - b2 = k by omega]
  · have hd : decide (max 0 ((a1.length : Int) + b1 - b2) ≥ (a2.length : Int)) = false := decide_eq_false hinc
    have hd' : ¬ (decide (max 0 ((a1.length : Int) + b1 - b2) ≥ (a2.length : Int)) = true) := by
      rw [hd]; simp
    rw [if_neg hd', if_neg hd', ite3, check0_ch _ _ _ (by omega),
      check0_ch _ _ _ (by omega), memeq_ch _ _ _ _ (by omega)]
    constructor
    · intro ⟨h1, h2, h⟩ c
      by_cases hc1 : c - b1 < 0
      · rw [z1 _ (Or.inl hc1), z2 _ (Or.inl (by omega))]
      by_cases hc2 : c < b2
      · rw [z2 _ (Or.inl (by omega))]
        by_cases hc3 : (a1.length : Int) ≤ c - b1
        · exact z1 _ (Or.inr hc3)
        · have := h1 (c - b1 + 1) (by omega) (by omega)
          rwa [show c - b1 + 1 - 1 = c - b1 by omega] at this
      by_cases hc4 : c - b2 < max 0 ((a1.length : Int) + b1 - b2)
      · have := h (by omega) (c - b2) (by omega) hc4
        rwa [show b2 - b1 + 1 - 1 + (c - b2) = c - b1 by omega] at this
      · rw [z1 _ (Or.inr (by omega))]
        by_cases hc5 : (a2.length : Int) ≤ c - b2
        · exact (z2 _ (Or.inr hc5)).symm
        · have := h2 (c - b2 + 1) (by omega) (by omega)
          rw [show c - b2 + 1 - 1 = c - b2 by omega] at this
          exact this.symm
    · intro h
      have e : ∀ k, ch a1 k = ch a2 (k + b1 - b2) := fun k => by
        have := h (k + b1); rwa [show k + b1 - b1 = k by omega] at this
      have e2 : ∀ k, ch a2 k = ch a1 (k + b2 - b1) := fun k => by
        rw [e, show k + b2 - b1 + b1 - b2 = k by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro i h1 h2
        rw [e, z2 _ (Or.inl (by omega))]
      · intro i h1 h2
        rw [e2, z1 _ (Or.inr (by omega))]
      · intro _ k h1 h2
        rw [e, show b2 - b1 + 1 - 1 + k + b1 - b2 = k by omega]


theorem eq_iff (s1 s2 : BitSetS) : eq s1 s2 = true ↔ ∀ x, mem s1 x = mem s2 x := by
  rw [mem_ext, eq_body]
  split
  · rw [eqBody_iff _ _ _ _ (by omega)]
    exact ⟨fun h c => (h c).symm, fun h c => (h c).symm⟩
  · exact eqBody_iff _ _ _ _ (by omega)

/-! ## `issubset` -/

theorem subChunk_iff (x y : U64) : subChunk x y = true ↔ ∀ j, x.getLsbD j = true → y.getLsbD j = true := by
  unfold subChunk
  rw [beq_iff_eq]
  constructor
  · intro h j hj
    have := congrArg (fun z => z.getLsbD j) h
    simp only [BitVec.getLsbD_and] at this
    rw [hj] at this
    simpa using this.symm
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j _
    rw [BitVec.getLsbD_and]
    cases hx : x.getLsbD j
    · rfl
    · rw [h j hx]; rfl

theorem subChunk_zero (x : U64) : subChunk x 0 = true ↔ x = 0 := by
  unfold subChunk; simp

theorem issubset_iff (a b : BitSetS) :
    issubset a b = true ↔ ∀ c, subChunk (Cg a.bits a.offset c) (Cg b.bits b.offset c) = true := by
  unfold issubset Cg
  simp only [Bool.and_eq_true]
  rw [rngAll, rngAll, rngAll]
  have za : ∀ k, (k < 0 ∨ (a.bits.length : Int) ≤ k) → ch a.bits k = 0 := fun k h => by
    rcases h with h | h
    · exact ch_neg _ h
    · exact ch_ge _ h
  have zb : ∀ k, (k < 0 ∨ (b.bits.length : Int) ≤ k) → ch b.bits k = 0 := fun k h => by
    rcases h with h | h
    · exact ch_neg _ h
    · exact ch_ge _ h
  constructor
  · intro ⟨⟨h1, h2⟩, h3⟩ c
    by_cases hc : c - a.offset < 0 ∨ (a.bits.length : Int) ≤ c - a.offset
    · rw [za _ hc]; unfold subChunk; simp
    · have k1 : 1 ≤ c - a.offset + 1 := by omega
      by_cases hb1 : c - b.offset < 0
      · have := h1 (c - a.offset + 1) k1 (by omega)
        rw [vget_ch _ k1, show c - a.offset + 1 - 1 = c - a.offset by omega, beq_iff_eq] at this
        rw [this]; unfold subChunk; simp
      by_cases hb2 : (b.bits.length : Int) ≤ c - b.offset
      · have := h3 (c - a.offset + 1) (by omega) (by omega)
        rw [vget_ch _ k1, show c - a.offset + 1 - 1 = c - a.offset by omega, beq_iff_eq] at this
        rw [this]; unfold subChunk; simp
      · have := h2 (c - a.offset + 1) (by omega) (by omega)
        rw [vget_ch _ k1, vget_ch _ (by omega), show c - a.offset + 1 - 1 = c - a.offset by omega,
          show c - a.offset + 1 - (b.offset - a.offset) - 1 = c - b.offset by omega] at this
        exact this
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k h1 h2
      have := h (k - 1 + a.offset)
      rw [show k - 1 + a.offset - a.offset = k - 1 by omega, zb _ (Or.inl (by omega)),
        subChunk_zero] at this
      rw [vget_ch _ h1, this]; rfl
    · intro k h1 h2
      have := h (k - 1 + a.offset)
      rw [show k - 1 + a.offset - a.offset = k - 1 by omega,
        show k - 1 + a.offset - b.offset = k - (b.offset - a.offset) - 1 by omega] at this
      rw [vget_ch _ (by omega), vget_ch _ (by omega)]
      exact this
    · intro k h1 h2
      have := h (k - 1 + a.offset)
      rw [show k - 1 + a.offset - a.offset = k - 1 by omega, zb _ (Or.inr (by omega)),
        subChunk_zero] at this
      rw [vget_ch _ (by omega), this]; rfl

theorem issubset_mem (a b : BitSetS) :
    issubset a b = true ↔ ∀ x, mem a x = true → mem b x = true := by
  rw [issubset_iff, mem_sub]
  constructor
  · intro h c j hj; exact (subChunk_iff _ _).mp (h c) j hj
  · intro h c; exact (subChunk_iff _ _).mpr (h c)

end BS

theorem bitSetEqSpec : BitSetEqSpec := fun s1 s2 _ _ => BS.eq_iff s1 s2

theorem bitSetSubsetSpec : BitSetSubsetSpec := by
  refine ⟨BS.subChunk_iff, fun a b _ _ => ⟨BS.issubset_mem a b, ?_⟩⟩
  unfold BS.psubset
  rw [Bool.and_eq_true, BS.issubset_mem, Bool.not_eq_true', ← Bool.not_eq_true, BS.eq_iff]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    exact Classical.byContradiction fun hn => h2 fun x => Classical.byContradiction fun hx => hn ⟨x, hx⟩
  · intro ⟨h1, ⟨x, hx⟩⟩
    exact ⟨h1, fun h => hx (h x)⟩

end JuliaLean.BitSetsCov
