import JuliaLean.Proofs.Compiler.src.typelimits.Small

/-!
The type-size limits of `Compiler/src/typelimits.jl:14-313`: `limit_type_size`,
`is_derived_type`, `is_derived_type_from_any` and `type_more_complex`.
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## Assumptions on subtyping -/

/-- `t <: Any` for every type `t` (`Any` is the greatest type). -/
def SubAnyTop : Prop :=
  ∀ n E t s r s', t.isType = true → (issub n E t anyType).run s = .ok (r, s') → r = true

/-- The answer of `a <: b` does not depend on the fresh-variable counter (subtyping is a function
of its arguments). -/
def SubStateFree : Prop :=
  ∀ n E a b s₁ s₂ r₁ r₂ s₁' s₂', (issub n E a b).run s₁ = .ok (r₁, s₁') →
    (issub n E a b).run s₂ = .ok (r₂, s₂') → r₁ = r₂

/-! ## `limit_type_size` -/

/-- `limit_type_size(t, compare, source, ...)` returns a supertype of `t`: either `t` itself,
the limited type when `t <: r` holds, the type limited against `Any`, or `Any`
(`Compiler/src/typelimits.jl:14-33`, "no new values may be introduced"). Assumes subtyping is
reflexive, has `Any` on top, and does not depend on the fresh-variable counter. -/
def LimitTypeSizeUpper : Prop :=
  SubReflexive → SubAnyTop → SubStateFree →
  ∀ n E tm (t c src : Val) (d l : Int) s r s', t.isType = true →
    (limitTypeSize n E tm t c src d l).run s = .ok (r, s') → Returns (issub n E t r) (· = true)

theorem limitTypeSize_cases {n E tm} {t c src : Val} {d l : Int} {s r s'}
    (h : (limitTypeSize n E tm t c src d l).run s = .ok (r, s')) :
    r = t ∨ r = anyType ∨ ∃ s₁ s₂, (issub n E t r).run s₁ = .ok (true, s₂) := by
  unfold limitTypeSize at h
  obtain ⟨_, _, _, h⟩ := bind_ok_inv h
  simp only at h
  split at h <;>
  · obtain ⟨m, _, _, h⟩ := bind_ok_inv h
    cases m
    · simp only [Bool.not_false, if_true] at h
      obtain ⟨h1, -⟩ := pure_ok_inv h; exact .inl h1
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    obtain ⟨r1, _, _, h⟩ := bind_ok_inv h
    obtain ⟨b1, s₃, hb1, h⟩ := bind_ok_inv h
    cases b1
    · simp only [Bool.not_false, if_true] at h
      obtain ⟨r2, _, _, h⟩ := bind_ok_inv h
      obtain ⟨b2, s₅, hb2, h⟩ := bind_ok_inv h
      cases b2
      · simp only [Bool.not_false, if_true] at h
        obtain ⟨h1, -⟩ := pure_ok_inv h; exact .inr (.inl h1)
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
        exact .inr (.inr ⟨_, _, hb2⟩)
    · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      exact .inr (.inr ⟨_, _, hb1⟩)

theorem limitTypeSizeUpper_proven : LimitTypeSizeUpper := by
  intro hrefl htop hfree n E tm t c src d l s r s' ht h s₀ b s₀' hb
  rcases limitTypeSize_cases h with h1 | h1 | ⟨s₁, s₂, h1⟩
  · subst h1; exact hrefl n E r s₀ b s₀' ht hb
  · subst h1; exact htop n E t s₀ b s₀' ht hb
  · exact (hfree n E t r _ _ _ _ _ _ h1 hb).symm

/-! ## `is_derived_type` and `is_derived_type_from_any` -/

/-- `is_derived_type(t, c, mindepth)` refuses types with free type variables (it returns `false`
without looking further, `Compiler/src/typelimits.jl:38-43`), and finds every type without free
type variables in itself exactly at `mindepth ≤ 1` (the `t === c` test, lines 44-46). Assumes `===` is
reflexive. -/
def IsDerivedTypeBase : Prop :=
  (∀ n E (t c : Val) d s,
    (JuliaLean.Compiler.hasFreeTypevars t || JuliaLean.Compiler.hasFreeTypevars c) = true →
    (isDerivedType (n + 1) E t c d).run s = .ok (false, s)) ∧
  (EgalReflexive → ∀ n E (t : Val) d s r s', JuliaLean.Compiler.hasFreeTypevars t = false →
    (isDerivedType n E t t d).run s = .ok (r, s') → r = decide (d ≤ 1))

theorem isDerivedTypeBase_proven : IsDerivedTypeBase := by
  refine ⟨fun n E t c d s h => ?_, fun hrefl n E t d s r s' hf h => ?_⟩
  · simp only [isDerivedType, h, if_true]; rfl
  · cases n with
    | zero => cases h
    | succ n =>
      simp only [isDerivedType, hf, Bool.or_self, Bool.false_eq_true, if_false] at h
      obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
      have := hrefl n E t s e s₁ he
      subst this
      simp only [if_true] at h
      exact (pure_ok_inv h).1

theorem isDerivedTypeFromAny_cons (n : Nat) (E : CEnv) (t x : Val) (xs : List Val) (d : Int) :
    isDerivedTypeFromAny n E t (x :: xs) d =
      (do if ← isDerivedType n E t x d then return true
          isDerivedTypeFromAny n E t xs d) := by
  simp only [isDerivedTypeFromAny, List.forIn_cons, bind_assoc]
  apply bind_congr; intro b
  cases b <;> simp

/-- `is_derived_type_from_any(t, sources, mindepth)` is `true` exactly when `is_derived_type`
answers `true` for one of the sources (`Compiler/src/typelimits.jl:79-84`). -/
def IsDerivedTypeFromAnySpec : Prop :=
  ∀ n E (t : Val) (srcs : List Val) d s r s', (isDerivedTypeFromAny n E t srcs d).run s = .ok (r, s') →
    (r = true → ∃ x ∈ srcs, ∃ s₁ s₂, (isDerivedType n E t x d).run s₁ = .ok (true, s₂)) ∧
    (r = false → ∀ x ∈ srcs, ∃ s₁ s₂, (isDerivedType n E t x d).run s₁ = .ok (false, s₂))

theorem isDerivedTypeFromAnySpec_proven : IsDerivedTypeFromAnySpec := by
  intro n E t srcs d
  induction srcs with
  | nil =>
    intro s r s' h
    have : r = false := by
      simp only [isDerivedTypeFromAny, List.forIn_nil] at h
      exact (pure_ok_inv h).1
    subst this
    exact ⟨fun h => absurd h (by decide), fun _ x hx => absurd hx List.not_mem_nil⟩
  | cons x xs ih =>
    intro s r s' h
    rw [isDerivedTypeFromAny_cons] at h
    obtain ⟨b, s₁, hb, h⟩ := bind_ok_inv h
    cases b
    · simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨i1, i2⟩ := ih _ _ _ h
      refine ⟨fun hr => ?_, fun hr y hy => ?_⟩
      · obtain ⟨z, hz, rest⟩ := i1 hr
        exact ⟨z, List.mem_cons_of_mem _ hz, rest⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨s, s₁, hb⟩
        · exact i2 hr y hy
    · simp only [if_true] at h
      obtain ⟨h1, -⟩ := pure_ok_inv h; subst h1
      exact ⟨fun _ => ⟨x, List.mem_cons_self .., s, s₁, hb⟩, fun h => absurd h (by decide)⟩

/-! ## `type_more_complex` -/

/-- `type_more_complex(t, c, ...)` is `false` in the trivial cases it checks first
(`Compiler/src/typelimits.jl:230-237`): `t === c`, `t === Union{}`, and `t` a `DataType` without
parameters. In particular no type is more complex than itself, so `limit_type_size(t, t, ...)`
returns `t`. Assumes `===` is reflexive. -/
def TypeMoreComplexTrivial : Prop :=
  EgalReflexive → ∀ n E (t c : Val) srcs (d td l : Int) s r s',
    (c = t ∨ t = .bottom ∨ (t.isDatatype = true ∧ t.params = [])) →
    (typeMoreComplex n E t c srcs d td l).run s = .ok (r, s') → r = false

theorem typeMoreComplexTrivial_proven : TypeMoreComplexTrivial := by
  intro hrefl n E t c srcs d td l s r s' hc h
  cases n with
  | zero => cases h
  | succ n =>
    unfold typeMoreComplex at h
    obtain ⟨e, s₁, he, h⟩ := bind_ok_inv h
    cases e
    · simp only [Bool.false_eq_true, if_false] at h
      rcases hc with hc | hc | ⟨h1, h2⟩
      · subst hc; exact absurd (hrefl n E _ s false s₁ he) (by decide)
      · subst hc
        rw [if_pos (show (Val.bottom == Val.bottom) = true from rfl)] at h
        exact (pure_ok_inv h).1
      · by_cases hb : (t == Val.bottom) = true
        · rw [if_pos hb] at h; exact (pure_ok_inv h).1
        · rw [if_neg hb] at h
          rw [if_pos (show (t.isDatatype && t.params.isEmpty) = true by simp [h1, h2])] at h
          exact (pure_ok_inv h).1
    · simp only [if_true] at h
      exact (pure_ok_inv h).1

/-- `limit_type_size(t, t, source, ...)` returns `t`: nothing is limited against itself. -/
def LimitTypeSizeSelf : Prop :=
  EgalReflexive → ∀ n E tm (t src : Val) (d l : Int) s r s',
    (limitTypeSize n E tm t t src d l).run s = .ok (r, s') → r = t

theorem limitTypeSizeSelf_proven : LimitTypeSizeSelf := by
  intro hrefl n E tm t src d l s r s' h
  unfold limitTypeSize at h
  obtain ⟨_, _, _, h⟩ := bind_ok_inv h
  simp only at h
  split at h <;>
  · obtain ⟨m, _, hm, h⟩ := bind_ok_inv h
    have := typeMoreComplexTrivial_proven hrefl n E t t _ 1 d l _ m _ (.inl rfl) hm
    subst this
    simp only [Bool.not_false, if_true] at h
    exact (pure_ok_inv h).1

/-- With no sources, `type_more_complex(t, c)` is `true` when `c` is a `UnionAll` and `t` is a
non-trivial type that is not, at tuple depth 0 ("allow wrapping type with fewer UnionAlls than
comparison only if in a covariant context", `Compiler/src/typelimits.jl:242-246`). -/
def TypeMoreComplexUnionAll : Prop :=
  ∀ n E (t c : Val) (d l : Int) s r s', Returns (JuliaLean.Compiler.egal n E t c) (· = false) →
    (t == .bottom) = false → (t.isDatatype && t.params.isEmpty) = false →
    isvarargtype t = false → isvarargtype c = false → t.isUnionall = false → c.isUnionall = true →
    (typeMoreComplex (n + 1) E t c [] d 0 l).run s = .ok (r, s') → r = true

theorem typeMoreComplexUnionAll_proven : TypeMoreComplexUnionAll := by
  intro n E t c d l s r s' he hb hd hvt hvc hut huc h
  unfold typeMoreComplex at h
  obtain ⟨e, s₁, he', h⟩ := bind_ok_inv h
  have := he _ _ _ he'; subst this
  simp only [Bool.false_eq_true, if_false, hb, hd] at h
  obtain ⟨f, s₂, hf, h⟩ := bind_ok_inv h
  have : f = false := by
    simp only [isDerivedTypeFromAny, List.forIn_nil] at hf
    exact (pure_ok_inv hf).1
  subst this
  simp only [Bool.false_eq_true, if_false, hvt, hvc, huc, hut, if_true, Bool.not_false,
    beq_self_eq_true, Bool.and_self] at h
  exact (pure_ok_inv h).1

end JuliaLean.Proofs.Compiler.src.typelimits
