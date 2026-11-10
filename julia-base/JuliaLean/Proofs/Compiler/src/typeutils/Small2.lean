import JuliaLean.Proofs.Compiler.src.typeutils.Loops

/-!
Properties of `isconstType`, `isnotbrokensubtype`, `has_concrete_subtype`, `valid_typeof_tparam`
and `valid_tparam` (`Compiler/src/typeutils.jl`).
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- `isconstType(t)` holds only for `TypeEgal{T}` (the type of exactly one type object) and for
`Type{Union{}}` (`Compiler/src/typeutils.jl:12`), and for every `TypeEgal{T}`. -/
def IsconstTypeSpec : Prop :=
  (∀ t : Val, isconstType t = true → t.isTypeegal = true ∨ t = .typeeq .bottom ∨
      (t.isTypeeq = true ∧ t.someTypeT == .bottom)) ∧
  (∀ T : Val, isconstType (.typeegal T) = true) ∧
  (∀ T : Val, (T == .bottom) = false → isconstType (.typeeq T) = false)

theorem isconstTypeSpec_proven : IsconstTypeSpec := by
  refine ⟨fun t h => ?_, fun _ => rfl, fun T hT => ?_⟩
  · cases t with
    | typeegal => exact .inl rfl
    | typeeq T =>
      simp only [isconstType, isTypeEgal, isTypeEq, Val.isTypeegal, Val.isTypeeq, Bool.false_or,
        Bool.true_and, Val.someTypeT] at h
      exact .inr (.inr ⟨rfl, h⟩)
    | _ => simp [isconstType, isTypeEgal, isTypeEq, Val.isTypeegal, Val.isTypeeq] at h
  · simp only [isconstType, isTypeEgal, isTypeEq, Val.isTypeegal, Val.isTypeeq, Bool.false_or,
      Bool.true_and, Val.someTypeT, hT]

/-- `isnotbrokensubtype(a, b)` (`Compiler/src/typeutils.jl:34-38`) only guards the kind types:
it is `true` when `b` is not a kind or `a` is not `Type{T}`/`TypeEgal{T}`, and otherwise asks
`b <: a`. -/
def IsnotbrokensubtypeSpec : Prop :=
  ∀ n E (a b : Val),
    (iskindtype b = false → ∀ s, (isnotbrokensubtype n E a b).run s = .ok (true, s)) ∧
    (isType a = false → ∀ s, (isnotbrokensubtype n E a b).run s = .ok (true, s)) ∧
    (iskindtype b = true → isType a = true → isnotbrokensubtype n E a b = subtypeChecked n E b a)

theorem isnotbrokensubtypeSpec_proven : IsnotbrokensubtypeSpec := by
  intro n E a b
  refine ⟨fun hb s => ?_, fun ha s => ?_, fun hb ha => ?_⟩
  · simp only [isnotbrokensubtype, hb, Bool.not_false, if_true]; rfl
  · simp only [isnotbrokensubtype]
    split
    · rfl
    · simp only [ha, Bool.not_false, if_true]; rfl
  · simp only [isnotbrokensubtype, hb, ha, Bool.not_true, Bool.false_eq_true, if_false]

/-- `has_concrete_subtype(d)` (`Compiler/src/typeutils.jl:53`) is a `MethodError` for anything but
a `DataType`, and is `true` for every non-concrete `DataType` other than a `Tuple` (the flag is
only cleared for concrete types and tuples with uninhabited parameters). -/
def HasConcreteSubtypeSpec : Prop :=
  (∀ n E d, d.isDatatype = false → ThrowsJulia "MethodError" (hasConcreteSubtypeDT n E d)) ∧
  (∀ n E name ps s s', name ≠ tupleName →
    (isConcreteType E.types (.datatype name ps)).run s = .ok (false, s') →
    (hasConcreteSubtypeDT n E (.datatype name ps)).run s = .ok (true, s'))

theorem hasConcreteSubtypeSpec_proven : HasConcreteSubtypeSpec := by
  refine ⟨fun n E d hd s => ?_, fun n E name ps s s' hn hc => ?_⟩
  · simp only [hasConcreteSubtypeDT, hd, Bool.not_false, if_true]; exact ⟨_, rfl⟩
  · simp only [hasConcreteSubtypeDT, Val.isDatatype, Bool.not_true, Bool.false_eq_true, if_false,
      hasConcreteSubtype]
    rw [StateT.run_bind, hc]
    have hn' : (name != tupleName) = true := by simpa using hn
    simp only [Bool.false_eq_true, if_false, hn', if_true]
    rfl

/-- `valid_typeof_tparam(t)` (`Compiler/src/typeutils.jl:83-98`) accepts only types whose values
can parameterize a type: `Symbol`, `Module`, bits types, and concrete `Tuple`s and `NamedTuple`s
(whose elements it checks in turn). `valid_tparam(x)` is `valid_typeof_tparam(typeof(x))`. -/
def ValidTypeofTparamSpec : Prop :=
  (∀ n E t, Returns (validTypeofTparam n E t) (fun r => r = true →
    (t == symbolType || t == .datatype "Core.Module" []) = true ∨
    (∃ s s', (isBits (n - 1) E.types t).run s = .ok (true, s')) ∨
    ((∃ s s', (isConcreteType E.types t).run s = .ok (true, s')) ∧
      (t.isTupleType = true ∨ t.name? = some "Core.NamedTuple")))) ∧
  (∀ n E x, validTparam n E x = validTypeofTparam n E (typeOf x))

theorem validTypeofTparamSpec_proven : ValidTypeofTparamSpec := by
  refine ⟨fun n E t s r s' h hr => ?_, fun _ _ _ => rfl⟩
  subst hr
  cases n with
  | zero => cases h
  | succ n =>
    simp only [validTypeofTparam, Nat.add_sub_cancel] at h ⊢
    by_cases hs : (t == symbolType || t == .datatype "Core.Module" []) = true
    · exact .inl hs
    · simp only [Bool.or_eq_true, not_or] at hs
      obtain ⟨hs1, hs2⟩ := hs
      simp only [hs1, hs2, Bool.false_or, Bool.or_false] at h
      obtain ⟨b, s₁, hb, h⟩ := run_bind_inv h
      cases b
      · right; right
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨c, s₂, hc, h⟩ := run_bind_inv h
        cases c
        · simp only [Bool.not_false, if_true] at h; cases h
        · refine ⟨⟨_, _, hc⟩, ?_⟩
          by_cases htup : t.isTupleType = true
          · exact .inl htup
          by_cases hnt : t.name? = some "Core.NamedTuple"
          · exact .inr hnt
          exfalso
          have hnt' : (t.name? == some "Core.NamedTuple") = false := by simpa using hnt
          have htup' : t.isTupleType = false := by simpa using htup
          simp only [Bool.not_true, Bool.false_eq_true, if_false, hnt', htup'] at h
          cases h
      · exact .inr (.inl ⟨_, _, hb⟩)

/-- `valid_as_lattice(x, astag)` (`Compiler/src/typeutils.jl:55-81`): `Union{}` is not a valid
element (the no-op first line `x === Bottom && false` does not change that), every `Union` is,
`Type{v}` is valid only for a type or `TypeVar` `v`, a `TypeVar` is judged by its upper bound, and
without `astag` every `DataType` is valid. -/
def ValidAsLatticeSpec : Prop :=
  (∀ n E astag s, (validAsLattice (n + 1) E .bottom astag).run s = .ok (false, s)) ∧
  (∀ n E a b astag s, (validAsLattice (n + 1) E (.union a b) astag).run s = .ok (true, s)) ∧
  (∀ n E T astag s, T.isType = false → T.isTypevar = false →
    (validAsLattice (n + 1) E (.typeeq T) astag).run s = .ok (false, s)) ∧
  (∀ n E id nm lb ub astag,
    validAsLattice (n + 1) E (.typevar id nm lb ub) astag = validAsLattice n E ub astag) ∧
  (∀ n E name ps s, (validAsLattice (n + 1) E (.datatype name ps) false).run s = .ok (true, s))

theorem validAsLatticeSpec_proven : ValidAsLatticeSpec := by
  refine ⟨fun n E astag s => rfl, fun n E a b astag s => rfl, fun n E T astag s h1 h2 => ?_,
    fun _ _ _ _ _ _ _ => rfl, fun n E name ps s => rfl⟩
  have hc : (!(T.isType || T.isTypevar)) = true := by simp [h1, h2]
  simp only [validAsLattice, Val.isUnionall, Val.isUnion, isType, isTypeEq,
    Val.isTypeeq, Bool.true_or, if_true, Val.someTypeT]
  split
  · rename_i hv; simp [Val.isTypevar] at hv
  · simp only [Bool.false_eq_true, if_false]
    rw [if_pos hc]; rfl

/-- `compute_alias_groups(na, fargs, argtypes)` "returns `nothing` when no aliasing is possible"
(`Compiler/src/typeutils.jl:187-191`): with no `fargs` and no `MustAlias` argument the cheap
`any_alias_candidate` test fails and the identity grouping is returned as `nothing`. -/
def AliasGroupsNoneSpec : Prop :=
  ∀ (argtypes : List LElt) (ats : Option (List LElt)), (ats = none ∨ ats = some argtypes) →
    NoMustAlias argtypes → Returns (computeAliasGroups argtypes.length none ats) (· = none)

theorem aliasGroupsNoneSpec_proven : AliasGroupsNoneSpec :=
  fun argtypes ats hats h => computeAliasGroups_none argtypes ats hats h

end JuliaLean.Proofs.Compiler.src.typeutils
