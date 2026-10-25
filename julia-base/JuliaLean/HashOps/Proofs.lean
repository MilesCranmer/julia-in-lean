import JuliaLean.HashOps.Props
import JuliaLean.Tuples.ProofsCompare

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

theorem smallIntegerHashConsistency_proven : SmallIntegerHashConsistency := by
  intro t s x y h ht1 ht2 hs1 hs2 hv
  cases t <;> cases s <;>
    simp_all [hashNum, hashI64, wrapInt, IntTy.signed, IntTy.bits]
  all_goals
    apply congrArg Int.toNat
    have hx := x.property
    have hy := y.property
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx hy
    omega

theorem decomposedHashConsistency_proven : DecomposedHashConsistency := by
  intro α eqv decompose numTy lawful x y h hxy
  obtain ⟨hd, ht⟩ := lawful x y hxy
  rw [hd, ht]

theorem stringHashConsistency_proven : StringHashConsistency := by
  rintro ⟨ac, ar, ab⟩ ⟨bc, br, bb⟩ ha hb hc h
  cases ab <;> cases bb <;>
    simp_all [Text.Valid, hashText, Text.utf8units, Text.canonicalBytes]

theorem annotatedStringOrder_refuted : ¬ AnnotatedStringOrder := by
  intro h
  have bad := h
    ⟨[120], [⟨1, 1⟩]⟩
    ⟨[120], [⟨1, 2⟩]⟩
  revert bad
  decide

theorem annotatedStringHash_refuted : ¬ AnnotatedStringHash := by
  intro h
  have bad := h [104, 233] 0
  simp [hashNonByteAnnotated, hashNonByteUnderlying] at bad

theorem arrayHashConsistency_proven : ArrayHashConsistency := by
  rintro ⟨aa, av⟩ ⟨ba, bv⟩ ha hv h
  simp_all

theorem tupleHashConsistency_proven : TupleHashConsistency :=
  JuliaLean.Tuples.hashIsequal

private theorem foldl_xor_perm (xs ys : List Nat) (h : xs.Perm ys) (seed : Nat) :
    xs.foldl Nat.xor seed = ys.foldl Nat.xor seed := by
  induction h generalizing seed with
  | nil => rfl
  | cons x h ih =>
      simp only [List.foldl]
      exact ih _
  | swap x y l =>
      simp only [List.foldl]
      congr 1
      calc
        (Nat.xor seed y).xor x = Nat.xor seed (Nat.xor y x) := Nat.xor_assoc _ _ _
        _ = Nat.xor seed (Nat.xor x y) := congrArg (Nat.xor seed) (Nat.xor_comm y x)
        _ = (Nat.xor seed x).xor y := (Nat.xor_assoc _ _ _).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ seed).trans (ih₂ seed)

private theorem map_perm {α β : Type} (f : α → β) {xs ys : List α} (h : xs.Perm ys) :
    (xs.map f).Perm (ys.map f) := h.map f

private theorem dictHash_perm (a b : List (Nat × Nat)) (h : a.Perm b) (seed : Nat) :
    dictHash a seed = dictHash b seed := by
  unfold dictHash
  congr 1
  simpa [List.foldl_map] using
    foldl_xor_perm (a.map pairContribution) (b.map pairContribution) (map_perm pairContribution h)
      0x6d35bb51952d5539

private theorem setHash_perm (a b : List Nat) (h : a.Perm b) (seed : Nat) :
    setHash a seed = setHash b seed := by
  unfold setHash
  congr 1
  let f := fun x => mixNat x 0
  simpa [List.foldl_map, f] using
    foldl_xor_perm (a.map f) (b.map f) (map_perm f h) 0x852ada37cfe8e0ce

theorem unorderedHashConsistency_proven : UnorderedHashConsistency := by
  constructor
  · intro a b hp h; exact dictHash_perm a b hp h
  · intro a b hp h; exact setHash_perm a b hp h

theorem comparisonFallbacks_proven : ComparisonFallbacks := by
  intro α o h
  exact ⟨h, fun _ _ => rfl⟩

theorem operatorFallbacks_proven : OperatorFallbacks := by
  intro α o x y
  simp [isequalFallback, neFallback, leFallback, geFallback]

theorem numberFallbacks_proven : NumberFallbacks := by
  intro α o pow x y z
  simp [zeroFallback, oneFallback, oneunitFallback, iszeroFallback, isoneFallback,
    signbitFallback, absFallback, signFallback, muladdFallback, fmaNumberFallback, fmaIntegerFallback,
    invFallback, literalPowHW] <;> rfl

theorem widenNoLoss_refuted : ¬ WidenNoLoss := by
  intro h
  have bad := (h .u8 (JInt.lit .u8 0) (JInt.lit .u8 255)).2
  revert bad
  decide

theorem widenAdditionNoLoss_proven : WidenAdditionNoLoss := by
  intro t x y
  have hx := x.property
  have hy := y.property
  cases t <;>
    simp [widenAdd, widenTarget, wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx hy ⊢ <;>
    omega

end JuliaLean.HashOps
