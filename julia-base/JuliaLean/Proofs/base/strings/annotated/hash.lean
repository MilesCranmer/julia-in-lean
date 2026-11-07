import JuliaLean.base.strings.annotated

namespace JuliaLean.HashOps

open JuliaLean

/-- AnnotatedString ordering must use the equivalence classes of isequal. -/
def AnnotatedStringOrder : Prop :=
  ∀ a b : AnnotatedText,
    [annotatedIsless a b, annotatedIsless b a, annotatedIsequal a b].count true = 1

/-- An annotation-free wrapper around a non-UInt8 AbstractString is isequal to
the underlying string and must make the same hash call. -/
def AnnotatedStringHash : Prop :=
  ∀ chars h,
    hashNonByteAnnotated ⟨chars, []⟩ h = hashNonByteUnderlying chars h
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
end JuliaLean.HashOps
