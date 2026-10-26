import JuliaLean.BitSetsCov.BitSetMatched

/-!
# `union!`, `intersect!`, `setdiff!`, `symdiff!`, `intersect` and `union` on `BitSet`s

The chunk-level result of `BitSetMatched.lean` gives the elementwise
membership; the bounds below show the result stays inside the chunk range of
the two arguments, so the type invariant is kept.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

theorem stB_len (A a2 : List U64) (b1 b2 : Int) (l1 l2 : Nat) (lff rff : Bool) (dirty : U64)
    (hAl : A.length = l1) (aB : List U64) (lB : Int)
    (h : stB A a2 b1 b2 l1 l2 lff rff dirty = (aB, lB)) :
    (aB.length : Int) + b1 ≤ max ((l1 : Int) + b1) ((l2 : Int) + b2) := by
  unfold stB at h
  simp only [] at h
  by_cases he : (l2 : Int) + b2 - ((l1 : Int) + b1) > 0
  · rw [if_pos he] at h
    cases hl : lff
    · rw [hl] at h
      simp only [Bool.false_eq_true, if_false] at h
      by_cases hz : (l1 : Int) + 1 ≤ b2 - b1
      · rw [if_pos hz] at h
        simp only [] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        rw [length_copy _ _ _ _ _ (by omega)
            (by rw [length_zeroRange _ _ _ (by omega) (by rw [length_growend, hAl]; omega), length_growend, hAl]; omega),
          length_zeroRange _ _ _ (by omega) (by rw [length_growend, hAl]; omega), length_growend, hAl]
        omega
      · rw [if_neg hz] at h
        simp only [] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        rw [length_copy _ _ _ _ _ (by omega) (by rw [length_growend, hAl]; omega), length_growend, hAl]
        omega
    · rw [hl] at h
      simp only [if_true] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1 h2
      omega
  · rw [if_neg he] at h
    by_cases he2 : (l2 : Int) + b2 - ((l1 : Int) + b1) < 0
    · rw [if_pos he2] at h
      cases hr : rff
      · rw [hr] at h
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        omega
      · rw [hr] at h
        simp only [if_true] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        rw [length_deleteend, hAl]
        omega
    · rw [if_neg he2] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1 h2
      omega

theorem matchedMapBits_bounds (f : MapOp) (a1 : List U64) (b1 : Int) (a2 : List U64) (b2 : Int)
    (lff rff : Bool) (dirty : U64) (hf : OpFacts f lff rff) :
    min b1 b2 ≤ (matchedMapBits f a1 b1 a2 b2 lff rff dirty).2 ∧
    (matchedMapBits f a1 b1 a2 b2 lff rff dirty).2 + (matchedMapBits f a1 b1 a2 b2 lff rff dirty).1.length ≤
      max ((a1.length : Int) + b1) ((a2.length : Int) + b2) := by
  have hAl := length_mapCommon f a1 a2 (b2 - b1) (max 1 (1 + (b2 - b1)))
    (min (a1.length : Int) ((a2.length : Int) + (b2 - b1))) (by omega) (by omega)
  have hAv := fun c => Cg_mapCommon f a1 a2 b1 b2 (max 1 (1 + (b2 - b1)))
    (min (a1.length : Int) ((a2.length : Int) + (b2 - b1))) c (by omega) (by omega) (by omega)
  rw [matchedMapBits_eq]
  generalize mapCommon f a1 a2 (b2 - b1) (max 1 (1 + (b2 - b1)))
    (min (a1.length : Int) ((a2.length : Int) + (b2 - b1))) = A at hAl hAv ⊢
  rcases hB : stB A a2 b1 b2 a1.length a2.length lff rff dirty with ⟨aB, lB⟩
  have hlen := stB_len A a2 b1 b2 a1.length a2.length lff rff dirty hAl aB lB hB
  obtain ⟨-, -, P3⟩ := stB_spec f a1 A a2 b1 b2 lff rff dirty hf hAl hAv aB lB hB
  simp only []
  unfold stC
  simp only []
  by_cases hb : b2 - b1 < 0
  · rw [if_pos hb]
    cases hl : lff
    · simp only [Bool.false_eq_true, if_false]
      have hgl : (growbeg aB (-(b2 - b1)).toNat dirty).length = (-(b2 - b1)).toNat + aB.length :=
        length_growbeg _ _ _
      rw [length_copy _ _ _ _ _ (by omega)
          (by rw [length_zeroRange _ _ _ (by omega) (by rw [hgl]; omega), hgl]; omega),
        length_zeroRange _ _ _ (by omega) (by rw [hgl]; omega), hgl]
      (try dsimp only); omega
    · simp only [if_true]
      (try dsimp only); omega
  · rw [if_neg hb]
    by_cases hb2 : b2 - b1 > 0
    · rw [if_pos hb2]
      cases hr : rff
      · simp only [Bool.false_eq_true, if_false]
        (try dsimp only); omega
      · simp only [if_true]
        rw [length_deletebeg]
        obtain ⟨hlB, hlen2⟩ := P3 (hf.rl hr)
        (try dsimp only); omega
    · rw [if_neg hb2]
      (try dsimp only); omega

theorem and_ones (x : U64) : x &&& ~~~(0 : U64) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  have h0 : BitVec.getLsbD (0 : U64) i = false := BitVec.getLsbD_zero
  rw [h0]
  simp [hi]

theorem opFacts (f : MapOp) :
    OpFacts f (f.bool false false == f.bool false true && f.bool false true == false)
      (f.bool false false == f.bool true false && f.bool true false == false) := by
  cases f
  · constructor <;> simp [MapOp.bool, MapOp.chunk]
  · constructor <;> simp [MapOp.bool, MapOp.chunk]
  · constructor
    · simp [MapOp.chunk]
    · intro _ y; simp [MapOp.chunk]
    · intro h; simp [MapOp.bool] at h
    · intro h; simp [MapOp.bool] at h
    · intro _ x; exact and_ones x
    · intro _; rfl
  · constructor <;> simp [MapOp.bool, MapOp.chunk]

theorem getLsbD_chunk (f : MapOp) (x y : U64) (j : Nat) :
    (f.chunk x y).getLsbD j = f.bool (x.getLsbD j) (y.getLsbD j) := by
  by_cases hj : j < 64
  · cases f <;> simp [MapOp.chunk, MapOp.bool, hj]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega),
      BitVec.getLsbD_of_ge _ _ (by omega)]
    cases f <;> rfl

theorem mem_of_Cg (s : BitSetS) (f : MapOp) (s1 s2 : BitSetS)
    (h : ∀ c, Cg s.bits s.offset c = f.chunk (Cg s1.bits s1.offset c) (Cg s2.bits s2.offset c)) (x : Int) :
    mem s x = f.bool (mem s1 x) (mem s2 x) := by
  rw [mem_Cg, mem_Cg, mem_Cg, h, getLsbD_chunk]

theorem Cg_empty_state (s : BitSetS) (h : WF s) (ho : s.offset = noOffset) (c : Int) : Cg s.bits s.offset c = 0 := by
  rw [h.1 ho]; exact Cg_nil _ _

theorem matchedMap_spec (f : MapOp) (s1 s2 : BitSetS) (dirty : U64) (h1 : WF s1) (h2 : WF s2) :
    ∃ s', matchedMap f s1 s2 dirty = .ok s' ∧ WF s' ∧ ∀ x, mem s' x = f.bool (mem s1 x) (mem s2 x) := by
  have hf := opFacts f
  unfold matchedMap
  simp only []
  by_cases ho1 : s1.offset = noOffset
  · rw [if_pos ho1]
    cases hl : (f.bool false false == f.bool false true && f.bool false true == false)
    · simp only [Bool.false_eq_true, if_false]
      refine ⟨s2, (bitSetCopySpec s1 s2 dirty).1, h2, fun x => ?_⟩
      rw [mem_Cg s1, Cg_empty_state s1 h1 ho1]
      have := hf.l0 hl (Cg s2.bits s2.offset (x / 64))
      rw [mem_Cg s2, ← getLsbD_chunk, this]
    · simp only [if_true]
      refine ⟨s1, rfl, h1, fun x => ?_⟩
      rw [mem_Cg s1, Cg_empty_state s1 h1 ho1]
      have := hf.l1 hl (Cg s2.bits s2.offset (x / 64))
      rw [mem_Cg s2, ← getLsbD_chunk, this]
  · rw [if_neg ho1]
    by_cases ho2 : s2.offset = noOffset
    · rw [if_pos ho2]
      cases hr : (f.bool false false == f.bool true false && f.bool true false == false)
      · simp only [Bool.false_eq_true, if_false]
        refine ⟨s1, rfl, h1, fun x => ?_⟩
        rw [mem_Cg s2, Cg_empty_state s2 h2 ho2]
        have := hf.r0 hr (Cg s1.bits s1.offset (x / 64))
        rw [mem_Cg s1, ← getLsbD_chunk, this]
      · simp only [if_true]
        refine ⟨emptyBang s1, rfl, ⟨fun _ => rfl, fun h => absurd rfl h⟩, fun x => ?_⟩
        rw [mem_Cg s2, Cg_empty_state s2 h2 ho2]
        have := hf.r1 hr (Cg s1.bits s1.offset (x / 64))
        rw [mem_Cg s1, ← getLsbD_chunk, this, show emptyBang s1 = ⟨[], noOffset⟩ from rfl, mem_Cg, Cg_nil]
    · rw [if_neg ho2]
      refine ⟨_, rfl, ?_, fun x => mem_of_Cg _ f s1 s2
        (fun c => Cg_matchedMapBits f s1.bits s1.offset s2.bits s2.offset _ _ dirty hf c) x⟩
      have hb := matchedMapBits_bounds f s1.bits s1.offset s2.bits s2.offset _ _ dirty hf
      have w1 := h1.2 ho1
      have w2 := h2.2 ho2
      have hn := noOffset_val
      constructor
      · intro h; simp only [] at h; omega
      · intro _; simp only []; omega

theorem intersect_spec (s1 s2 : BitSetS) (dirty : U64) (h1 : WF s1) (h2 : WF s2) :
    ∃ s', intersect s1 s2 dirty = .ok s' ∧ WF s' ∧ ∀ x, mem s' x = (mem s1 x && mem s2 x) := by
  unfold intersect
  split
  · rw [(bitSetCopySpec new s1 dirty).2.1]
    obtain ⟨s', h, hw, hm⟩ := matchedMap_spec .and s1 s2 dirty h1 h2
    exact ⟨s', h, hw, hm⟩
  · rw [(bitSetCopySpec new s2 dirty).2.1]
    obtain ⟨s', h, hw, hm⟩ := matchedMap_spec .and s2 s1 dirty h2 h1
    refine ⟨s', h, hw, fun x => ?_⟩
    rw [hm]; simp [MapOp.bool, Bool.and_comm]

end BS

end JuliaLean.BitSetsCov
