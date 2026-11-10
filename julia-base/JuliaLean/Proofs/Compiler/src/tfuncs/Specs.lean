import JuliaLean.Proofs.Compiler.src.tfuncs.Common

/-!
What the tfuncs of `ifelse`, `===`, `typeof`, `has_free_typevars`, `nfields`, `tuple` and the
argument checks of `getfield` return, branch by branch, next to what the builtin returns at run
time where the model has it.
-/

namespace JuliaLean.Proofs.Compiler.Tfuncs

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `ifelse` -/

/-- `ifelse_tfunc` (`Compiler/src/tfuncs.jl:344-358`) on a constant condition gives the branch
the runtime takes: `x` for `true`, `y` for `false`, and `Union{}` for a non-`Bool`, for which
`jl_f_ifelse` throws a `TypeError` (`src/builtins.c:734-739`). On a non-constant condition it
is `Union{}` when the condition's type does not intersect `Bool`, and `tmerge(x, y)` otherwise. -/
def IfelseTfuncBase : Prop :=
  ∀ n E L x y s,
    (∀ v, (ifelseTfunc n E L (.const v) x y).run s =
      .ok (match asBool? v with | some true => x | some false => y | none => .ty .bottom, s)) ∧
    (∀ c a b, (builtinRT n E "ifelse" [c, a, b]).run s =
      match asBool? c with
      | some true => .ok (a, s)
      | some false => .ok (b, s)
      | none => (jlThrow "TypeError" "ifelse" : CM Val).run s) ∧
    (∀ t s₁ s₂, (widenconst n E (.ty t)).run s = .ok (t, s₁) →
      (hasintersect n E t boolTy).run s₁ = .ok (false, s₂) →
      (ifelseTfunc n E L (.ty t) x y).run s = .ok (.ty .bottom, s₂)) ∧
    (∀ t s₁ s₂, (widenconst n E (.ty t)).run s = .ok (t, s₁) →
      (hasintersect n E t boolTy).run s₁ = .ok (true, s₂) →
      (ifelseTfunc n E L (.ty t) x y).run s = (tmerge n E L x y).run s₂)

theorem ifelseTfuncBase_proven : IfelseTfuncBase := by
  intro n E L x y s
  refine ⟨fun v => ?_, fun c a b => ?_, fun t s₁ s₂ hw hi => ?_, fun t s₁ s₂ hw hi => ?_⟩
  · cases h : asBool? v with
    | none => simp [ifelseTfunc, widenslotwrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
        LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias, h]; rfl
    | some b => cases b <;>
        simp [ifelseTfunc, widenslotwrapper, LElt.isAnyConditional, LElt.isAnyMustAlias,
          LElt.isConditional, LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias, h] <;>
        rfl
  · cases h : asBool? c with
    | none => simp [builtinRT, h]
    | some b => cases b <;> simp [builtinRT, h] <;> rfl
  · show ((widenconst n E (.ty t)) >>= fun w => hasintersect n E w boolTy >>= fun i =>
        if !i then pure (LElt.ty .bottom) else tmerge n E L x y).run s = _
    rw [run_bind_ok hw, run_bind_ok hi]; rfl
  · show ((widenconst n E (.ty t)) >>= fun w => hasintersect n E w boolTy >>= fun i =>
        if !i then pure (LElt.ty .bottom) else tmerge n E L x y).run s = _
    rw [run_bind_ok hw, run_bind_ok hi]; rfl

/-! ## `===` -/

/-- `egal_tfunc` (`Compiler/src/tfuncs.jl:366-400`) layer by layer. On `typeinf_lattice` two
constants fold to `Const(x === y)`. On the conditionals layer, a `Conditional` compared with
`Const(false)` is the `Conditional` with its branches swapped, with `Const(true)` the
`Conditional` itself, and with any other constant `Const(false)`. On the native-type layer,
types that do not intersect give `Const(false)` and the rest `Bool`. -/
def EgalTfuncBase : Prop :=
  ∀ n E s,
    (∀ a b, (egalTfunc (n + 5) E typeinfLattice (.const a) (.const b)).run s =
      (JuliaLean.Compiler.egal n E a b >>= fun r => pure (constBool r)).run s) ∧
    (∀ p sl d th el isd, (egalTfunc (n + 1) E (.conditionals p) (.conditional sl d th el isd)
        (.const (boolVal false))).run s = (mkConditional sl d el th).run s) ∧
    (∀ p sl d th el isd, (egalTfunc (n + 1) E (.conditionals p) (.conditional sl d th el isd)
        (.const (boolVal true))).run s = .ok (.conditional sl d th el isd, s)) ∧
    (∀ p sl d th el isd v, asBool? v = none →
      (egalTfunc (n + 1) E (.conditionals p) (.conditional sl d th el isd) (.const v)).run s =
        .ok (constBool false, s)) ∧
    (∀ x y tx ty s₁ s₂ s₃, (widenconst n E x).run s = .ok (tx, s₁) →
      (widenconst n E y).run s₁ = .ok (ty, s₂) →
      (hasintersect n E tx ty).run s₂ = .ok (false, s₃) →
      (egalTfunc (n + 1) E .jlType x y).run s = .ok (constBool false, s₃)) ∧
    (∀ x y tx ty s₁ s₂ s₃, (widenconst n E x).run s = .ok (tx, s₁) →
      (widenconst n E y).run s₁ = .ok (ty, s₂) →
      (hasintersect n E tx ty).run s₂ = .ok (true, s₃) →
      (egalTfunc (n + 1) E .jlType x y).run s = .ok (.ty boolTy, s₃))

theorem egalTfuncBase_proven : EgalTfuncBase := by
  intro n E s
  refine ⟨fun a b => rfl, fun p sl d th el isd => rfl, fun p sl d th el isd => rfl,
    fun p sl d th el isd v hv => ?_, fun x y tx ty s₁ s₂ s₃ h₁ h₂ h₃ => ?_,
    fun x y tx ty s₁ s₂ s₃ h₁ h₂ h₃ => ?_⟩
  · simp [egalTfunc, widenconditional, hv, constBool]; rfl
  · show (widenconst n E x >>= fun tx => widenconst n E y >>= fun ty =>
        hasintersect n E tx ty >>= fun i =>
        if !i then pure (constBool false) else pure (LElt.ty boolTy)).run s = _
    rw [run_bind_ok h₁, run_bind_ok h₂, run_bind_ok h₃]; rfl
  · show (widenconst n E x >>= fun tx => widenconst n E y >>= fun ty =>
        hasintersect n E tx ty >>= fun i =>
        if !i then pure (constBool false) else pure (LElt.ty boolTy)).run s = _
    rw [run_bind_ok h₁, run_bind_ok h₂, run_bind_ok h₃]; rfl

/-! ## `typeof`, `has_free_typevars` -/

/-- `typeof_tfunc` (`Compiler/src/tfuncs.jl:882-920`) on a constant is `Const(typeof(v))`, which
is what `jl_f_typeof` returns (`src/builtins.c:612-616`), and on the egality type
`TypeEgal{T}` it is `Const(typeof(T))`. `_typeof_tfunc` (922-927) of a `TypeVar` bounded only by
`Any` is `DataType`, and of any other `TypeVar` is `_typeof_tfunc` of its upper bound. -/
def TypeofTfuncBase : Prop :=
  ∀ n E s,
    (∀ v, (typeofTfunc (n + 1) E (.const v)).run s = .ok (.const (typeOf v), s)) ∧
    (∀ v, (builtinRT n E "typeof" [v]).run s = .ok (typeOf v, s)) ∧
    (∀ T, T.isType = true → (typeofTfunc (n + 2) E (.ty (.typeegal T))).run s =
      .ok (.const (typeOf T), s)) ∧
    (∀ id nm lb, (typeofTfunc_ (n + 1) E (.typevar id nm lb anyType)).run s =
      .ok (.ty datatypeType, s)) ∧
    (∀ id nm lb ub, ub != anyType → (typeofTfunc_ (n + 1) E (.typevar id nm lb ub)).run s =
      (typeofTfunc_ n E ub).run s)

theorem typeofTfuncBase_proven : TypeofTfuncBase := by
  intro n E s
  refine ⟨fun v => rfl, fun v => rfl, fun T hT => ?_, fun id nm lb => rfl,
    fun id nm lb ub hub => ?_⟩
  · have hw : (widenconst (n + 1) E (.ty (.typeegal T))).run s = .ok (.typeegal T, s) := rfl
    show (widenconst (n + 1) E (.ty (.typeegal T)) >>= _).run s = _
    rw [run_bind_ok hw]; rfl
  · simp [typeofTfunc_, hub]

/-- `has_free_typevars_tfunc` (`Compiler/src/tfuncs.jl:930-944`): a constant folds to what
`jl_f_has_free_typevars` returns on it (`src/builtins.c:618-622`); `Type{p}` and `TypeEgal{p}`
with a closed `p` are `Const(false)`, and with a free variable in `p` are `Bool`, because the
variable stands for closed runtime values; `TypeVar` is `Const(true)`. -/
def HasFreeTypevarsTfuncBase : Prop :=
  ∀ n E s,
    (∀ v, (hasFreeTypevarsTfunc n E (.const v)).run s = .ok (constBool (hasFreeTypevars v), s)) ∧
    (∀ v, (builtinRT n E "has_free_typevars" [v]).run s = .ok (boolVal (hasFreeTypevars v), s)) ∧
    (∀ p, JuliaLean.Compiler.hasFreeTypevars p = false →
      (hasFreeTypevarsTfunc (n + 1) E (.ty (.typeeq p))).run s = .ok (constBool false, s) ∧
      (hasFreeTypevarsTfunc (n + 1) E (.ty (.typeegal p))).run s = .ok (constBool false, s)) ∧
    (∀ p, JuliaLean.Compiler.hasFreeTypevars p = true →
      (hasFreeTypevarsTfunc (n + 1) E (.ty (.typeeq p))).run s = .ok (.ty boolTy, s) ∧
      (hasFreeTypevarsTfunc (n + 1) E (.ty (.typeegal p))).run s = .ok (.ty boolTy, s)) ∧
    ((hasFreeTypevarsTfunc (n + 1) E (.ty tvarType)).run s = .ok (constBool true, s))

theorem hasFreeTypevarsTfuncBase_proven : HasFreeTypevarsTfuncBase := by
  intro n E s
  refine ⟨fun v => rfl, fun v => rfl, fun p hp => ⟨?_, ?_⟩, fun p hp => ⟨?_, ?_⟩, rfl⟩
  all_goals
    first
      | (have hw : (widenconst (n + 1) E (.ty (.typeeq p))).run s = .ok (.typeeq p, s) := rfl
         show (widenconst (n + 1) E (.ty (.typeeq p)) >>= _).run s = _
         rw [run_bind_ok hw]
         simp [isType, isTypeEq, Val.isTypeeq, typeParameter, hp]; rfl)
      | (have hw : (widenconst (n + 1) E (.ty (.typeegal p))).run s = .ok (.typeegal p, s) := rfl
         show (widenconst (n + 1) E (.ty (.typeegal p)) >>= _).run s = _
         rw [run_bind_ok hw]
         simp [isType, isTypeEq, isTypeEgal, Val.isTypeeq, Val.isTypeegal, typeParameter, hp]; rfl)

/-! ## `nfields` -/

/-- `nfields_tfunc` (`Compiler/src/tfuncs.jl:620-645`): a constant folds to `nfields` of its
value, which `jl_f_nfields` returns (`src/builtins.c:1457-1462`); a `Conditional` is `Const(0)`
(a `Bool` has no fields); a non-abstract tuple type without a `Vararg` is `Const` of its length
and with one is `Int`; a `Union` whose first member gives `Int` is `Int`. -/
def NfieldsTfuncBase : Prop :=
  ∀ n T L s,
    (∀ v, (nfieldsTfunc (n + 1) T L (.const v)).run s =
      (nfieldsRT T.E v >>= fun k => pure (LElt.const (.long k))).run s) ∧
    (∀ v, (builtinRT n T.E "nfields" [v]).run s =
      (nfieldsRT T.E v >>= fun k => pure (Val.long k)).run s) ∧
    (∀ sl d th el isd, (nfieldsTfunc (n + 1) T L (.conditional sl d th el isd)).run s =
      .ok (.const (.long 0), s)) ∧
    (∀ ps, (isabstracttype T.E (.datatype tupleName ps)).run s = .ok (false, s) →
      isvatuple (.datatype tupleName ps) = false →
      (nfieldsTfunc (n + 2) T L (.ty (.datatype tupleName ps))).run s =
        .ok (.const (.long ps.length), s)) ∧
    (∀ ps, (isabstracttype T.E (.datatype tupleName ps)).run s = .ok (false, s) →
      isvatuple (.datatype tupleName ps) = true →
      (nfieldsTfunc (n + 2) T L (.ty (.datatype tupleName ps))).run s = .ok (.ty longType, s))

theorem nfieldsTfuncBase_proven : NfieldsTfuncBase := by
  intro n T L s
  refine ⟨fun v => rfl, fun v => rfl, fun _ _ _ _ _ => rfl, fun ps ha hv => ?_,
    fun ps ha hv => ?_⟩
  · have hw : (widenconst (n + 1) T.E (.ty (.datatype tupleName ps))).run s =
        .ok (.datatype tupleName ps, s) := rfl
    show (widenconst (n + 1) T.E (.ty (.datatype tupleName ps)) >>= _).run s = _
    rw [run_bind_ok hw]
    show (isabstracttype T.E (.datatype tupleName ps) >>= _).run s = _
    rw [run_bind_ok ha]
    simp only [unwrapUnionall, Val.unwrapUnionall, hv]; rfl
  · have hw : (widenconst (n + 1) T.E (.ty (.datatype tupleName ps))).run s =
        .ok (.datatype tupleName ps, s) := rfl
    show (widenconst (n + 1) T.E (.ty (.datatype tupleName ps)) >>= _).run s = _
    rw [run_bind_ok hw]
    show (isabstracttype T.E (.datatype tupleName ps) >>= _).run s = _
    rw [run_bind_ok ha]
    simp only [unwrapUnionall, Val.unwrapUnionall, hv]; rfl

/-! ## `tuple` -/

/-- `tuple_tfunc` (`Compiler/src/tfuncs.jl:2305-2366`) of no arguments is `Const(())`, the value
`jl_f_tuple` returns (`src/builtins.c:1125-1130`). -/
def TupleTfuncBase : Prop :=
  ∀ n E L s,
    (tupleTfunc n E L []).run s = .ok (.const (.imm emptytupleType []), s) ∧
    (builtinRT n E "tuple" []).run s = .ok (.imm emptytupleType [], s)

theorem tupleTfuncBase_proven : TupleTfuncBase := fun _ _ _ _ => ⟨rfl, rfl⟩

/-! ## `getfield` argument checks -/

/-- `getfield_tfunc` (`Compiler/src/tfuncs.jl:1169-1185`): the two-argument form is
`_getfield_tfunc(s00, name, false)`; with three arguments the third (a boundscheck flag or a
memory order) must intersect `Symbol` or `Bool`, and with four the third (the order) must
intersect `Symbol` and the fourth (the flag) `Bool`, or the call is `Union{}`. -/
def GetfieldTfuncArgsBase : Prop :=
  ∀ n T L s00 name s,
    (getfieldTfunc n T L [s00, name]).run s = (getfieldTfuncL n T L s00 name false).run s ∧
    (∀ bo t s₁ s₂ s₃, bo.isVarargElt = false → (widenconst n T.E bo).run s = .ok (t, s₁) →
      (hasintersect n T.E t symbolType).run s₁ = .ok (false, s₂) →
      (hasintersect n T.E t boolTy).run s₂ = .ok (false, s₃) →
      (getfieldTfunc n T L [s00, name, bo]).run s = .ok (.ty .bottom, s₃)) ∧
    (∀ order bc t s₁ s₂, (widenconst n T.E order).run s = .ok (t, s₁) →
      (hasintersect n T.E t symbolType).run s₁ = .ok (false, s₂) →
      (getfieldTfunc n T L [s00, name, order, bc]).run s = .ok (.ty .bottom, s₂)) ∧
    (∀ order bc t s₁ s₂, bc.isVarargElt = true → (widenconst n T.E order).run s = .ok (t, s₁) →
      (hasintersect n T.E t symbolType).run s₁ = .ok (true, s₂) →
      (getfieldTfunc n T L [s00, name, order, bc]).run s =
        (getfieldTfuncL n T L s00 name false).run s₂)

theorem getfieldTfuncArgsBase_proven : GetfieldTfuncArgsBase := by
  intro n T L s00 name s
  refine ⟨rfl, fun bo t s₁ s₂ s₃ hv hw h₁ h₂ => ?_, fun order bc t s₁ s₂ hw h₁ => ?_,
    fun order bc t s₁ s₂ hv hw h₁ => ?_⟩
  · simp only [getfieldTfunc, hv, Bool.not_false, ite_true]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    have hor : (JuliaLean.Compiler.orM (hasintersect n T.E t symbolType)
        (hasintersect n T.E t boolTy)).run s₁ = .ok (false, s₃) := by
      unfold JuliaLean.Compiler.orM; rw [run_bind_ok h₁]; exact h₂
    refine (stbind_run_ok hor).trans ?_; rfl
  · simp only [getfieldTfunc]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    refine (stbind_run_ok h₁).trans ?_; rfl
  · simp only [getfieldTfunc, hv]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    refine (stbind_run_ok h₁).trans ?_; rfl

/-- `getfield_boundscheck` (`Compiler/src/tfuncs.jl:1045-1069`): `:unsafe` for a `Vararg`
in the name or flag position and for other argument counts; `:on` with two arguments and with a
`Symbol` third argument (an order); a constant `Bool` flag gives `:on` or `:off`. -/
def GetfieldBoundscheckBase : Prop :=
  ∀ n E s a b c d,
    (b.isVarargElt = true → (getfieldBoundscheck n E [a, b]).run s = .ok ("unsafe", s)) ∧
    (b.isVarargElt = false → (getfieldBoundscheck n E [a, b]).run s = .ok ("on", s)) ∧
    (c.isVarargElt = true → (getfieldBoundscheck n E [a, b, c]).run s = .ok ("unsafe", s)) ∧
    (d.isVarargElt = true → (getfieldBoundscheck n E [a, b, c, d]).run s = .ok ("unsafe", s)) ∧
    (∀ bc, (getfieldBoundscheck (n + 1) E [a, b, c, .const (boolVal bc)]).run s =
      .ok (if bc then "on" else "off", s)) ∧
    (∀ bc, (getfieldBoundscheck (n + 1) E [a, b, .const (boolVal bc)]).run s =
      .ok (if bc then "on" else "off", s)) ∧
    ((getfieldBoundscheck n E []).run s = .ok ("unsafe", s)) ∧
    ((getfieldBoundscheck n E [a]).run s = .ok ("unsafe", s)) ∧
    (∀ e rest, (getfieldBoundscheck n E (a :: b :: c :: d :: e :: rest)).run s = .ok ("unsafe", s))

theorem getfieldBoundscheckBase_proven : GetfieldBoundscheckBase := by
  intro n E s a b c d
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun bc => ?_, fun bc => ?_, rfl, rfl,
    fun e rest => rfl⟩
  · simp [getfieldBoundscheck, h]; rfl
  · simp [getfieldBoundscheck, h]; rfl
  · simp [getfieldBoundscheck, h]; rfl
  · simp [getfieldBoundscheck, h]; rfl
  · cases bc <;> rfl
  · cases bc <;> rfl

/-- `_getfield_fieldindex(s, name)` (`Compiler/src/tfuncs.jl:1187-1196`): a `Symbol` name is its
`fieldindex` (0 when absent), an `Int` is itself, and anything else is `nothing`. -/
def GetfieldFieldindexSpec : Prop :=
  ∀ T st s,
    (∀ sym, (getfieldFieldindex T st (.symbol sym)).run s =
      (fieldindexDT T st sym >>= fun k => pure (some (Int.ofNat k))).run s) ∧
    (∀ k, (getfieldFieldindex T st (.long k)).run s = .ok (some k, s)) ∧
    (∀ v, v.isSymbol = false → v.isLong = false → (getfieldFieldindex T st v).run s = .ok (none, s))

theorem getfieldFieldindexSpec_proven : GetfieldFieldindexSpec := by
  intro T st s
  refine ⟨fun sym => rfl, fun k => rfl, fun v h₁ h₂ => ?_⟩
  cases v <;> simp [Val.isSymbol, Val.isLong] at h₁ h₂ <;> rfl

end JuliaLean.Proofs.Compiler.Tfuncs
