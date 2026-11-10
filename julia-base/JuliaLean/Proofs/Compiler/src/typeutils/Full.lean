import JuliaLean.Proofs.Compiler.src.typeutils.Small
import JuliaLean.Proofs.Compiler.src.typeutils.Small2
import JuliaLean.Proofs.Compiler.src.typeutils.ArgtypesToType

/-!
Full statements of the small helpers of `Compiler/src/typeutils.jl`: each one extends a statement
of `Small.lean` or `Small2.lean` with the branches that one leaves open, so that every branch of
the body is fixed.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `isconstType` -/

/-- `isconstType(t)` (`Compiler/src/typeutils.jl:12`) is true exactly for every `TypeEgal{T}` and
for `Type{Union{}}`: it is true on `Type{Union{}}`, false on every other `Type{T}`, and false on
every object that is neither a `Type{T}` nor a `TypeEgal{T}`. -/
def IsconstTypeFull : Prop :=
  IsconstTypeSpec ∧ isconstType (.typeeq .bottom) = true ∧
    ∀ t : Val, t.isTypeegal = false → t.isTypeeq = false → isconstType t = false

theorem isconstTypeFull_proven : IsconstTypeFull := by
  refine ⟨isconstTypeSpec_proven, rfl, fun t h1 h2 => ?_⟩
  simp [isconstType, isTypeEgal, isTypeEq, h1, h2]

/-! ## `_typename` -/

/-- `_typename` (`Compiler/src/typeutils.jl:164-176`) on every input. On top of `TypenameSpec`:
the fallback gives `Union{}` for everything that is not a `TypeVar`, `Union`, `UnionAll`,
`DataType` or `Type{T}` (so for `Union{}`, a `TypeEgal{T}`, a `Vararg` and a non-type value); and a
`Union` whose members disagree gives `Union{}` when one member gives `Union{}` (line 170), `Union{}`
when both give different `Const` names (line 171), and `Core.TypeName` otherwise (line 172). -/
def TypenameFull : Prop :=
  TypenameSpec ∧
  (∀ t : Val, t.isTypevar = false → t.isUnion = false → t.isUnionall = false →
    t.isDatatype = false → t.isTypeeq = false → typenameT t = .bottom) ∧
  (∀ a b : Val, typenameT a ≠ typenameT b →
    (typenameT a = .bottom ∨ typenameT b = .bottom) → typenameT (.union a b) = .bottom) ∧
  (∀ (a b : Val) (x y : String), typenameT a = .const x → typenameT b = .const y → x ≠ y →
    typenameT (.union a b) = .bottom) ∧
  (∀ a b : Val, typenameT a ≠ typenameT b → typenameT a ≠ .bottom → typenameT b ≠ .bottom →
    (typenameT a = .typeName ∨ typenameT b = .typeName) → typenameT (.union a b) = .typeName)

theorem typenameT_ne_beq {x y : TypenameT} (h : x ≠ y) : (x == y) = false := by
  cases hb : (x == y)
  · rfl
  · exact absurd (typenameT_eq_of_beq hb) h

theorem typenameFull_proven : TypenameFull := by
  refine ⟨typenameSpec_proven, fun t h1 h2 h3 h4 h5 => ?_, fun a b hne hb => ?_,
    fun a b x y ha hb hxy => ?_, fun a b hne ha hb ht => ?_⟩
  · cases t <;> simp_all [typenameT, Val.isTypevar, Val.isUnion, Val.isUnionall, Val.isDatatype,
      Val.isTypeeq]
  · simp only [typenameT, typenameT_ne_beq hne, Bool.false_eq_true, if_false]
    rcases hb with hb | hb <;> simp [hb]
  · have hne : typenameT a ≠ typenameT b := by rw [ha, hb]; simpa using hxy
    simp only [typenameT, Bool.false_eq_true, if_false, ha, hb, tnb_cb, tnb_cc,
      beq_false_of_ne hxy, Bool.or_self]
  · simp only [typenameT, typenameT_ne_beq hne, Bool.false_eq_true, if_false]
    have h1 : (typenameT a == .bottom) = false := typenameT_ne_beq ha
    have h2 : (typenameT b == .bottom) = false := typenameT_ne_beq hb
    simp only [h1, h2, Bool.or_self, Bool.false_eq_true, if_false]
    rcases ht with ht | ht
    · rw [ht]
    · rw [ht]; cases typenameT a <;> rfl

/-! ## `unioncomplexity` -/

/-- The loop of `_unioncomplexity` over a `Tuple`'s parameters: its result is the largest of the
parameters' complexities, or 0. -/
theorem forIn_max_run (n : Nat) (ps : List Val) (f : Val → Nat → CM (ForInStep Nat))
    (hf : ∀ p c s st s', (f p c).run s = .ok (st, s') →
      ∃ k, (unioncomplexity n p).run s = .ok (k, s') ∧ st = .yield (max c k)) :
    ∀ c s r s', (forIn ps c f).run s = .ok (r, s') →
      ∃ ks : List Nat, ListRel (fun p k => ∃ s₁ s₂, (unioncomplexity n p).run s₁ = .ok (k, s₂)) ps ks ∧
        r = ks.foldl max c := by
  induction ps with
  | nil => intro c s r s' h; cases h; exact ⟨[], .nil, rfl⟩
  | cons p ps ih =>
    intro c s r s' h
    obtain ⟨st, s₁, h1, h2⟩ := forIn_cons_run h
    obtain ⟨k, hk, rfl⟩ := hf p c s st s₁ h1
    obtain ⟨ks, hrel, hr⟩ := ih (max c k) s₁ r s' h2
    exact ⟨k :: ks, .cons ⟨_, _, hk⟩ hrel, hr⟩

/-- `unioncomplexity(x)` (`Compiler/src/typeutils.jl:394-414`) on every input. On top of
`UnioncomplexitySpec`: on a `Tuple` it is the largest of the parameters' complexities (0 for no
parameters), on a `UnionAll` it is `max(body, var.ub)`, on `Vararg{T}` it is `T`'s plus one, on a
`Vararg` without `T` it is 1, and on every other object it is 0. -/
def UnioncomplexityFull : Prop :=
  UnioncomplexitySpec ∧
  (∀ n ps, Returns (unioncomplexity (n + 1) (.datatype tupleName ps)) (fun c =>
    ∃ ks : List Nat,
      ListRel (fun p k => ∃ s₁ s₂, (unioncomplexity n p).run s₁ = .ok (k, s₂)) ps ks ∧
      c = ks.foldl max 0)) ∧
  (∀ n id nm lb ub body, unioncomplexity (n + 1) (.unionall id nm lb ub body) =
    (do return max (← unioncomplexity n body) (← unioncomplexity n ub))) ∧
  (∀ n T N, unioncomplexity (n + 1) (.vararg (some T) N) = (do return (← unioncomplexity n T) + 1)) ∧
  (∀ n N s, (unioncomplexity (n + 1) (.vararg none N)).run s = .ok (1, s)) ∧
  (∀ n (x : Val) s, x.isDatatype = false → x.isUnion = false → x.isUnionall = false →
    x.isVararg = false → (unioncomplexity (n + 1) x).run s = .ok (0, s))

theorem unioncomplexityFull_proven : UnioncomplexityFull := by
  refine ⟨unioncomplexitySpec_proven, fun n ps s r s' h => ?_, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun n x s h1 h2 h3 h4 => ?_⟩
  · simp only [unioncomplexity, bne_self_eq_false, Bool.false_eq_true, if_false] at h
    obtain ⟨c, s₁, hc, h⟩ := run_bind_inv h
    have h' : (Except.ok (c, s₁) : Except String (Nat × Nat)) = .ok (r, s') := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    refine forIn_max_run n ps _ ?_ 0 s c s₁ hc
    intro p c s st s' h
    obtain ⟨k, s₁, hk, h⟩ := run_bind_inv h
    have h' : (Except.ok (ForInStep.yield (max c k), s₁) : Except String (ForInStep Nat × Nat)) =
      .ok (st, s') := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨k, hk, rfl⟩
  · cases x <;> simp_all [Val.isDatatype, Val.isUnion, Val.isUnionall, Val.isVararg] <;> rfl

/-! ## `valid_as_lattice` -/

theorem unwrapUnionall_not_unionall : ∀ v : Val, v.unwrapUnionall.isUnionall = false
  | .unionall _ _ _ _ b => by simpa [Val.unwrapUnionall] using unwrapUnionall_not_unionall b
  | .datatype .. | .union .. | .intersect .. | .typeeq .. | .typeegal .. | .typevar ..
  | .vararg .. | .bottom | .typeapp .. | .long .. | .symbol .. | .bits .. | .imm ..
  | .mutableRef .. | .module .. => rfl

theorem unwrapUnionall_of_not_unionall (v : Val) (h : v.isUnionall = false) :
    v.unwrapUnionall = v := by
  cases v <;> simp_all [Val.isUnionall, Val.unwrapUnionall]

/-- `valid_as_lattice(x, astag)` (`Compiler/src/typeutils.jl:55-81`) on every input. On top of
`ValidAsLatticeSpec`: `Type{v}` and `TypeEgal{v}` are valid when `v` is a type or a `TypeVar`; a
`UnionAll` is judged by its unwrapped body (unless that is a `TypeVar`); with `astag`, a struct
`DataType` is valid exactly when `has_concrete_subtype` holds and any other `DataType` is valid;
every object that is no `TypeVar`, `UnionAll`, `Union`, `Type{v}` or `DataType` is invalid. -/
def ValidAsLatticeFull : Prop :=
  ValidAsLatticeSpec ∧
  (∀ n E T astag s, (T.isType = true ∨ T.isTypevar = true) →
    (validAsLattice (n + 1) E (.typeeq T) astag).run s = .ok (true, s) ∧
    (validAsLattice (n + 1) E (.typeegal T) astag).run s = .ok (true, s)) ∧
  (∀ n E (x : Val) astag, x.isUnionall = true → x.unwrapUnionall.isTypevar = false →
    validAsLattice (n + 1) E x astag = validAsLattice (n + 1) E x.unwrapUnionall astag) ∧
  (∀ n E name ps s s₁, (isstructtype E (.datatype name ps)).run s = .ok (true, s₁) →
    (validAsLattice (n + 1) E (.datatype name ps) true).run s =
      (hasConcreteSubtype n E.types (.datatype name ps)).run s₁) ∧
  (∀ n E name ps s s₁, (isstructtype E (.datatype name ps)).run s = .ok (false, s₁) →
    (validAsLattice (n + 1) E (.datatype name ps) true).run s = .ok (true, s₁)) ∧
  (∀ n E (x : Val) astag s, x.isTypevar = false → x.isUnionall = false → x.isUnion = false →
    isType x = false → x.isDatatype = false → (validAsLattice (n + 1) E x astag).run s = .ok (false, s))

theorem validAsLatticeFull_proven : ValidAsLatticeFull := by
  refine ⟨validAsLatticeSpec_proven, fun n E T astag s hT => ?_, fun n E x astag h1 h2 => ?_,
    fun n E name ps s s₁ h => ?_, fun n E name ps s s₁ h => ?_,
    fun n E x astag s h1 h2 h3 h4 h5 => ?_⟩
  · have hc : (!(T.isType || T.isTypevar)) = false := by
      rcases hT with h | h <;> simp [h]
    have e1 : (Val.typeeq T).isTypevar = false := rfl
    have e2 : (Val.typeegal T).isTypevar = false := rfl
    constructor
    · simp only [validAsLattice, e1, Val.isUnionall, Val.isUnion, isType, isTypeEq,
        isTypeEgal, Val.isTypeeq, Val.isTypeegal, Bool.true_or, Val.someTypeT, hc,
        Bool.false_eq_true, if_false, if_true]
      rfl
    · simp only [validAsLattice, e2, Val.isUnionall, Val.isUnion, isType, isTypeEq,
        isTypeEgal, Val.isTypeeq, Val.isTypeegal, Bool.or_true, Val.someTypeT, hc,
        Bool.false_eq_true, if_false, if_true]
      rfl
  · have hx : x.isTypevar = false := by cases x <;> simp_all [Val.isUnionall, Val.isTypevar]
    have hu := unwrapUnionall_not_unionall x
    simp only [validAsLattice, hx, h1, h2, hu, Bool.false_eq_true, if_false, if_true]
  · simp only [validAsLattice, Val.isTypevar, Val.isUnionall, Val.isUnion, isType, isTypeEq,
      isTypeEgal, Val.isTypeeq, Val.isTypeegal, Val.isDatatype, Bool.or_self, Bool.false_eq_true,
      if_false, if_true]
    rw [StateT.run_bind, h]; rfl
  · simp only [validAsLattice, Val.isTypevar, Val.isUnionall, Val.isUnion, isType, isTypeEq,
      isTypeEgal, Val.isTypeeq, Val.isTypeegal, Val.isDatatype, Bool.or_self, Bool.false_eq_true,
      if_false, if_true]
    rw [StateT.run_bind, h]; rfl
  · simp only [validAsLattice, h1, h2, h3, h4, h5, Bool.false_eq_true, if_false]; rfl

/-! ## `has_concrete_subtype` -/

/-- Whether a tuple parameter allows instances (the C model's flag computation for a non-concrete
`Tuple`, `src/jltypes.c`): the parameter (a `Vararg`'s element type, if it has one) is a type or
`TypeVar` and is not `Union{}`. -/
def tupleParamInhabitable (p : Val) : Bool :=
  match (if p.isVararg then p.varargT? else some p) with
  | none => true
  | some q => (q.isType || q.isTypevar) && !(q == .bottom)

/-- A loop that stops with `some v` at the first element failing `P`, and otherwise ends with
`none`. -/
theorem forIn_all_run {α γ : Type} (l : List α) (P : α → Bool) (v : γ)
    (F : α → Option γ × Unit → CM (ForInStep (Option γ × Unit)))
    (hF : ∀ x ∈ l, ∀ s, (F x (none, ())).run s =
      .ok (if P x then .yield (none, ()) else .done (some v, ()), s)) :
    ∀ s, (forIn l (none, ()) F).run s = .ok ((if l.all P then none else some v, ()), s) := by
  induction l with
  | nil => intro s; rfl
  | cons x l ih =>
    intro s
    rw [List.forIn_cons, run_bind_ok (hF x (List.mem_cons_self ..) s)]
    cases hx : P x
    · simp only [hx, List.all_cons, Bool.false_and, Bool.false_eq_true, if_false]; rfl
    · simp only [hx, List.all_cons, Bool.true_and, if_true]
      exact ih (fun y hy => hF y (List.mem_cons_of_mem _ hy)) s

/-- `has_concrete_subtype(d)` (`Compiler/src/typeutils.jl:53`) on every `DataType`. On top of
`HasConcreteSubtypeSpec`: for a concrete `DataType` it is the layout's flag; for a non-concrete
`Tuple` it holds exactly when every parameter allows instances. -/
def HasConcreteSubtypeFull : Prop :=
  HasConcreteSubtypeSpec ∧
  (∀ n E name ps s s₁, (isConcreteType E.types (.datatype name ps)).run s = .ok (true, s₁) →
    (hasConcreteSubtypeDT n E (.datatype name ps)).run s =
      ((fun l => l.concreteSubtype) <$> layoutOf n E.types (.datatype name ps)).run s₁) ∧
  (∀ n E ps s s₁, (isConcreteType E.types (.datatype tupleName ps)).run s = .ok (false, s₁) →
    (hasConcreteSubtypeDT n E (.datatype tupleName ps)).run s = .ok (ps.all tupleParamInhabitable, s₁))

theorem hasConcreteSubtypeFull_proven : HasConcreteSubtypeFull := by
  refine ⟨hasConcreteSubtypeSpec_proven, fun n E name ps s s₁ hc => ?_, fun n E ps s s₁ hc => ?_⟩
  · simp only [hasConcreteSubtypeDT, Val.isDatatype, Bool.not_true, Bool.false_eq_true, if_false,
      hasConcreteSubtype]
    rw [StateT.run_bind, hc]
    rfl
  · simp only [hasConcreteSubtypeDT, Val.isDatatype, Bool.not_true, Bool.false_eq_true, if_false,
      hasConcreteSubtype]
    rw [run_bind_ok hc]
    simp only [Bool.false_eq_true, if_false, bne_self_eq_false]
    rw [run_bind_ok (forIn_all_run ps tupleParamInhabitable false _ ?_ s₁)]
    · cases ps.all tupleParamInhabitable <;> rfl
    · intro x _ s
      cases hq : (if x.isVararg = true then x.varargT? else some x) with
      | none => simp only [tupleParamInhabitable, hq]; rfl
      | some q =>
        simp only [tupleParamInhabitable, hq]
        cases h1 : q.isType <;> cases h2 : q.isTypevar <;> cases h3 : (q == Val.bottom) <;>
          simp [h1, h2, h3] <;> rfl

/-! ## `valid_typeof_tparam` -/

/-- `Core.Module`. -/
def moduleType : Val := .datatype "Core.Module" []

/-- `valid_typeof_tparam(t)` (`Compiler/src/typeutils.jl:83-98`) on every input. On top of
`ValidTypeofTparamSpec`: `Symbol` and `Module` are valid; a bits type is valid; a type that is not
concrete is invalid; a concrete type that is neither a `Tuple` nor a `NamedTuple` (nor `Symbol`,
`Module` or bits) is invalid; and a concrete non-bits `Tuple` is valid exactly when each of its
parameters is, checked in order.

The model evaluates `isbitstype(t)` before testing `t === Symbol || t === Module` (it lifts the
call out of the `||`), so each statement assumes that call returns. -/
def ValidTypeofTparamFull : Prop :=
  ValidTypeofTparamSpec ∧
  (∀ n E (t : Val) b s s₁, (t == symbolType || t == moduleType) = true →
    (isBits n E.types t).run s = .ok (b, s₁) → (validTypeofTparam (n + 1) E t).run s = .ok (true, s₁)) ∧
  (∀ n E (t : Val) s s₁, (isBits n E.types t).run s = .ok (true, s₁) →
    (validTypeofTparam (n + 1) E t).run s = .ok (true, s₁)) ∧
  (∀ n E (t : Val) s s₁ s₂, (t == symbolType || t == moduleType) = false →
    (isBits n E.types t).run s = .ok (false, s₁) → (isConcreteType E.types t).run s₁ = .ok (false, s₂) →
    (validTypeofTparam (n + 1) E t).run s = .ok (false, s₂)) ∧
  (∀ n E (t : Val) s s₁ s₂, (t == symbolType || t == moduleType) = false →
    (isBits n E.types t).run s = .ok (false, s₁) → (isConcreteType E.types t).run s₁ = .ok (true, s₂) →
    (t.name? == some "Core.NamedTuple") = false → t.isTupleType = false →
    (validTypeofTparam (n + 1) E t).run s = .ok (false, s₂)) ∧
  (∀ n E (ps : List Val) s s₁ s₂ r s',
    (Val.datatype tupleName ps == symbolType || Val.datatype tupleName ps == moduleType) = false →
    (isBits n E.types (.datatype tupleName ps)).run s = .ok (false, s₁) →
    (isConcreteType E.types (.datatype tupleName ps)).run s₁ = .ok (true, s₂) →
    (validTypeofTparam (n + 1) E (.datatype tupleName ps)).run s = .ok (r, s') →
    (r = true ∧ ∀ p ∈ ps, ∃ s₃ s₄, (validTypeofTparam n E p).run s₃ = .ok (true, s₄)) ∨
    (r = false ∧ ∃ p ∈ ps, ∃ s₃ s₄, (validTypeofTparam n E p).run s₃ = .ok (false, s₄)))

theorem validTypeofTparamFull_proven : ValidTypeofTparamFull := by
  refine ⟨validTypeofTparamSpec_proven, fun n E t b s s₁ hsm hb => ?_, fun n E t s s₁ hb => ?_,
    fun n E t s s₁ s₂ hsm hb hc => ?_, fun n E t s s₁ s₂ hsm hb hc hnt htup => ?_,
    fun n E ps s s₁ s₂ r s' hsm hb hc h => ?_⟩
  · simp only [validTypeofTparam]
    rw [run_bind_ok hb]
    simp only [moduleType] at hsm
    simp only [hsm, Bool.true_or, if_true]; rfl
  · simp only [validTypeofTparam]
    rw [run_bind_ok hb]
    simp only [Bool.or_true, if_true]; rfl
  · simp only [moduleType] at hsm
    simp only [validTypeofTparam]
    rw [run_bind_ok hb]
    simp only [hsm, Bool.or_false, Bool.false_eq_true, if_false]
    rw [run_bind_ok hc]
    simp only [Bool.not_false, if_true]; rfl
  · simp only [moduleType] at hsm
    simp only [validTypeofTparam]
    rw [run_bind_ok hb]
    simp only [hsm, Bool.or_false, Bool.false_eq_true, if_false]
    rw [run_bind_ok hc]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hnt, htup]; rfl
  · simp only [moduleType] at hsm
    simp only [validTypeofTparam] at h
    rw [run_bind_ok hb] at h
    simp only [hsm, Bool.or_false, Bool.false_eq_true, if_false] at h
    rw [run_bind_ok hc] at h
    have hnt : ((Val.datatype tupleName ps).name? == some "Core.NamedTuple") = false := by
      simp [Val.name?, tupleName]
    have htup : (Val.datatype tupleName ps).isTupleType = true := by
      simp [Val.isTupleType, Val.name?]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hnt, htup, if_true, Val.params] at h
    obtain ⟨st, s₃, hst, h⟩ := run_bind_inv h
    have key := forIn_test ps (fun p => validTypeofTparam n E p) false _ (by
      intro x _ s₀ st₀ s₀' hx
      obtain ⟨b, s₄, hb, hx⟩ := run_bind_inv hx
      cases b
      · simp only [Bool.not_false, if_true] at hx
        cases hx; exact ⟨false, hb, rfl⟩
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at hx
        cases hx; exact ⟨true, hb, rfl⟩) s₂ st s₃ hst
    rcases key with ⟨h5, h4⟩ | ⟨h5, y, hy, h4⟩
    · simp only [h5] at h
      cases h
      exact .inl ⟨rfl, h4⟩
    · simp only [h5] at h
      cases h
      exact .inr ⟨rfl, y, hy, h4⟩

/-! ## `is_immutable_argtype` -/

/-- `is_immutable_argtype(argtype)` (`Compiler/src/typeutils.jl:461`) is `is_immutable_type` of
`widenconst_split(ignorelimited(argtype))`: a native type is used as it is, a `LimitedAccuracy` is
looked through, a non-type `Const(v)` gives `typeof(v)`, a `PartialStruct` gives its `typ`, and a
`Conditional` gives `Bool`. -/
def IsImmutableArgtypeWiden : Prop :=
  (∀ n E (t : Val), t.isType = true → isImmutableArgtype n E (.ty t) = isImmutableType E t) ∧
  (∀ n E (x : LElt) cs cid, x.isLimited = false →
    isImmutableArgtype n E (.limitedAccuracy x cs cid) = isImmutableArgtype n E x) ∧
  (∀ n E (v : Val), v.isType = false → isImmutableArgtype (n + 1) E (.const v) = isImmutableType E (typeOf v)) ∧
  (∀ n E typ u fs ui fi, isImmutableArgtype (n + 1) E (.partialStruct typ u fs ui fi) = isImmutableType E typ) ∧
  (∀ n E sl d a b i, isImmutableArgtype n E (.conditional sl d a b i) = isImmutableType E boolTy)

theorem isImmutableArgtypeWiden_proven : IsImmutableArgtypeWiden := by
  refine ⟨fun n E t ht => ?_, fun n E x cs cid hx => ?_, fun n E v hv => ?_,
    fun n E typ u fs ui fi => ?_, fun n E sl d a b i => ?_⟩
  · simp [isImmutableArgtype, ignorelimited, widenconstSplit, ht]
  · have : ignorelimited x = x := by cases x <;> simp_all [LElt.isLimited, ignorelimited]
    simp only [isImmutableArgtype]
    rw [show ignorelimited (.limitedAccuracy x cs cid) = x from rfl, this]
  · simp [isImmutableArgtype, ignorelimited, widenconstSplit, LElt.isConst, widenconst, hv]
  · simp [isImmutableArgtype, ignorelimited, widenconstSplit, LElt.isConst, LElt.isPartialStruct,
      widenconst]
  · simp [isImmutableArgtype, ignorelimited, widenconstSplit, LElt.isConst, LElt.isPartialStruct,
      LElt.isAnyConditional, LElt.isConditional]

/-! ## `switchtupleunion(ty)` -/

/-- The type of a `.ty` lattice element. -/
def tyVal : LElt → Val
  | .ty v => v
  | _ => .bottom

theorem mapM_tyVal_run (f : LElt → CM Val) (hf : ∀ v s, (f (.ty v)).run s = .ok (v, s)) :
    ∀ l : List LElt, (∀ e ∈ l, ∃ v, e = .ty v) → ∀ s, (l.mapM f).run s = .ok (l.map tyVal, s) := by
  intro l
  induction l with
  | nil => intro _ s; rfl
  | cons e l ih =>
    intro hl s
    obtain ⟨v, rfl⟩ := hl e (List.mem_cons_self ..)
    rw [List.mapM_cons, run_bind_ok (hf v s)]
    show (List.mapM f l >>= fun l' => pure (v :: l')).run s = _
    rw [run_bind_ok (ih (fun e he => hl e (List.mem_cons_of_mem _ he)) s)]
    rfl

theorem ListRel.mono_mem {α β : Type} {R R' : α → β → Prop} {l : List α} {r : List β}
    (h : ListRel R l r) (hm : ∀ a ∈ l, ∀ b, R a b → R' a b) : ListRel R' l r := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (hm _ (List.mem_cons_self ..) _ hab)
      (ih (fun a ha b h => hm a (List.mem_cons_of_mem _ ha) b h))

/-- Every argument list of `cart` over native types holds native types only. -/
theorem cart_all_ty (ps : List Val) :
    ∀ c ∈ cart (ps.map LElt.ty).toArray ps.length, ∀ e ∈ c.toList, ∃ v, e = .ty v := by
  intro c hc e he
  have hlen : (ps.map LElt.ty).toArray.size = ps.length := by simp
  obtain ⟨hs, -, hb⟩ := (mem_cart ps.length _ (by simp) c).mp hc
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
  have hk' : k < ps.length := by simp at hk; omega
  have hck : c[k]? = some e := by
    rw [Array.getElem?_eq_getElem (by simpa using hk)]; simp [← hke]
  have hta : (ps.map LElt.ty).toArray[k]? = some (.ty ps[k]) := by simp [hk']
  obtain ⟨h1, h2⟩ := hb k hk' _ hta
  cases hp : partsPure (.ty ps[k]) with
  | none => rw [h1 hp] at hck; cases hck; exact ⟨_, rfl⟩
  | some qs =>
    obtain ⟨y, -, hy⟩ := h2 qs hp
    rw [hy] at hck; cases hck; exact ⟨_, rfl⟩

/-- `switchtupleunion(ty)` (`Compiler/src/typeutils.jl:321-324`) for every `ty` whose unwrapped
body is a `DataType`: the result lists, in the order of `cart`, one tuple per member choice of the
`Union` parameters, namely `rewrap_unionall(Tuple{c...}, ty)` for the choice `c` (by `mem_cart` and
`cart_no_union`, each choice replaces every `Union` parameter by one of its members and keeps the
others). -/
def SwitchtupleunionTyFull : Prop :=
  SwitchtupleunionCount ∧
  ∀ n E (ty : Val) name ps, ty.unwrapUnionall = .datatype name ps →
    Returns (switchtupleunion n E ty) (fun r => ListRel (fun c v =>
      ∃ tp s₁ s₂ s₃ s₄, (jlTuple n E (c.toList.map tyVal)).run s₁ = .ok (tp, s₂) ∧
        (rewrapUnionallJ n E tp ty).run s₃ = .ok (v, s₄)) (cart (ps.map LElt.ty).toArray ps.length) r)

theorem switchtupleunionTyFull_proven : SwitchtupleunionTyFull := by
  refine ⟨switchtupleunionCount_proven, fun n E ty name ps hty s r s' h => ?_⟩
  simp only [switchtupleunion, hty] at h
  obtain ⟨res, s₁, hres, h⟩ := run_bind_inv h
  obtain ⟨rs, hrs, hrel⟩ := switchtupleunion_cart n E .jlType _
    (fun c v => (∀ e ∈ c.toList, ∃ v, e = .ty v) → ∃ tp s₁ s₂ s₃ s₄,
      (jlTuple n E (c.toList.map tyVal)).run s₁ = .ok (tp, s₂) ∧
        (rewrapUnionallJ n E tp ty).run s₃ = .ok (v, s₄))
    (fun c s v s' he hall => by
      obtain ⟨l, s₂, hl, he⟩ := run_bind_inv he
      rw [mapM_tyVal_run _ (fun v s => rfl) c.toList hall s] at hl
      simp only [Except.ok.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      obtain ⟨tp, s₃, htp, he⟩ := run_bind_inv he
      exact ⟨tp, _, _, _, _, htp, he⟩)
    ps.length (ps.map LElt.ty).toArray #[] (by simp)
    (fun hext => by simp [hasExtendedUnionsplit] at hext) s res s₁ hres
  have h' : (Except.ok (res.toList, s₁) : Except String (List Val × Nat)) = .ok (r, s') := h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  simp only [List.nil_append, Array.toList_empty] at hrs
  rw [hrs]
  exact hrel.mono_mem (fun c hc v hv => hv (cart_all_ty ps c hc))

end JuliaLean.Proofs.Compiler.src.typeutils
