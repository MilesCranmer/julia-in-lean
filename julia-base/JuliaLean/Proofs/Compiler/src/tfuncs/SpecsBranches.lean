import JuliaLean.Proofs.Compiler.src.tfuncs.Specs
import JuliaLean.Proofs.Compiler.src.tfuncs.Nothrow

/-!
The remaining branches of the tfuncs in `Specs.lean`: slot-wrapper arguments of `ifelse` and
`===`, the `===` singleton rule, the non-constant cases of `nfields`, `typeof` and
`has_free_typevars`, the closed-type check of `typeassert_nothrow`, the flag cases of
`getfield_boundscheck` and `getfield_tfunc`, and the paths of `tuple_tfunc` after its empty case.

Each statement fixes what a branch returns given what its sub-calls return. The sub-calls
(`hasintersect`, `isconcretetype`, the type constructors) run the subtyping and type-construction
models, whose `while` loops are `partial` and opaque to the kernel, so they appear as hypotheses.
Each `*Spec` below is the conjunction of the `*Base` statement in `Specs.lean` (or
`Nothrow.lean`) and the branches here.
-/

namespace JuliaLean.Proofs.Compiler.Tfuncs

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

theorem exc_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

/-- A `Conditional` whose branches are both possible widens to `Bool`. -/
theorem widenconditional_bool (sl d : Int) (th el : LElt) (isd : Bool)
    (h1 : th.isBottom = false) (h2 : el.isBottom = false) :
    widenconditional (.conditional sl d th el isd) = pure (.ty boolTy) := by
  simp only [widenconditional]
  split <;> simp_all [LElt.isBottom]

/-- `widenmustalias` is the identity off `MustAlias` and `LimitedAccuracy`. -/
theorem widenmustalias_id (y : LElt) (h1 : y.isAnyMustAlias = false) (h2 : y.isLimited = false) :
    widenmustalias y = pure y := by
  cases y <;> simp_all [widenmustalias, LElt.isAnyMustAlias, LElt.isMustAlias,
    LElt.isInterMustAlias, LElt.isLimited]

/-! ## `ifelse` -/

/-- `ifelse_tfunc` (`Compiler/src/tfuncs.jl:344-358`) on slot wrappers, which `widenslotwrapper`
unwraps first (line 345): a `Conditional` that cannot be true is the `y` branch, one that cannot
be false the `x` branch, and one that can be either is `tmerge(x, y)` (`Bool` intersects `Bool`);
a `MustAlias` (or `InterMustAlias`) condition is treated as its field type. -/
def IfelseTfuncWrappers : Prop :=
  ∀ n E L x y s,
    (∀ sl d el isd, (ifelseTfunc n E L (.conditional sl d (.ty .bottom) el isd) x y).run s =
      .ok (y, s)) ∧
    (∀ sl d th isd, th.isBottom = false →
      (ifelseTfunc n E L (.conditional sl d th (.ty .bottom) isd) x y).run s = .ok (x, s)) ∧
    (∀ sl d th el isd s₁, th.isBottom = false → el.isBottom = false →
      (hasintersect (n + 1) E boolTy boolTy).run s = .ok (true, s₁) →
      (ifelseTfunc (n + 1) E L (.conditional sl d th el isd) x y).run s = (tmerge (n + 1) E L x y).run s₁) ∧
    (∀ sl d vt fi f, f.isAnyConditional = false → f.isAnyMustAlias = false →
      (ifelseTfunc n E L (.mustAlias sl d vt fi f) x y).run s = (ifelseTfunc n E L f x y).run s) ∧
    (∀ sl vt fi f, f.isAnyConditional = false → f.isAnyMustAlias = false →
      (ifelseTfunc n E L (.interMustAlias sl vt fi f) x y).run s = (ifelseTfunc n E L f x y).run s)

theorem ifelseTfuncWrappers_proven : IfelseTfuncWrappers := by
  intro n E L x y s
  refine ⟨fun sl d el isd => rfl, fun sl d th isd hth => ?_, fun sl d th el isd s₁ h1 h2 hi => ?_,
    fun sl d vt fi f h1 h2 => ?_, fun sl vt fi f h1 h2 => ?_⟩
  · cases th <;> simp_all [LElt.isBottom, ifelseTfunc, widenslotwrapper, widenconditional,
      LElt.isAnyConditional, LElt.isConditional] <;>
      first | rfl | (rename_i t; cases t <;> simp_all [LElt.isBottom] <;> rfl)
  · have hw := widenconditional_bool sl d th el isd h1 h2
    simp only [ifelseTfunc, widenslotwrapper, LElt.isAnyConditional, LElt.isConditional,
      Bool.true_or, ite_true, hw]
    show ((widenconst (n + 1) E (.ty boolTy)) >>= fun w => hasintersect (n + 1) E w boolTy >>=
      fun i => if !i then pure (LElt.ty .bottom) else tmerge (n + 1) E L x y).run s = _
    rw [run_bind_ok (show (widenconst (n + 1) E (.ty boolTy)).run s = .ok (boolTy, s) from rfl),
      run_bind_ok hi]
    try rfl
  · have hw : widenslotwrapper f = pure f := by simp [widenslotwrapper, h1, h2]
    have hm : widenslotwrapper (.mustAlias sl d vt fi f) = pure f := rfl
    simp only [ifelseTfunc, hm, hw]
  · have hw : widenslotwrapper f = pure f := by simp [widenslotwrapper, h1, h2]
    have hm : widenslotwrapper (.interMustAlias sl vt fi f) = pure f := rfl
    simp only [ifelseTfunc, hm, hw]

def IfelseTfuncSpec : Prop := IfelseTfuncBase ∧ IfelseTfuncWrappers

theorem ifelseTfuncSpec_proven : IfelseTfuncSpec := ⟨ifelseTfuncBase_proven, ifelseTfuncWrappers_proven⟩

/-! ## `===` -/

/-- The rest of `egal_tfunc` (`Compiler/src/tfuncs.jl:366-400`). The `MustAliases` layer passes
the field types of `MustAlias` arguments on either side to the next layer. On the conditionals
layer a constant on the left of a `Conditional` is handled as on the right; a `Conditional`
against a native type goes to the next layer unchanged, and against another `Conditional` that
can be either the other is widened to `Bool` first. On the constants layer a `Const(v)` against
`typeof(v)` that is a singleton type is `Const(true)`, from either side, and otherwise the
native-type layer decides. -/
def EgalTfuncBranches : Prop :=
  ∀ n E s,
    (∀ p sl d vt fi f y, y.isAnyMustAlias = false → y.isLimited = false →
      (egalTfunc (n + 1) E (.mustAliases p) (.mustAlias sl d vt fi f) y).run s =
        (egalTfunc n E p f y).run s) ∧
    (∀ p x sl vt fi f, x.isAnyMustAlias = false → x.isLimited = false →
      (egalTfunc (n + 1) E (.mustAliases p) x (.interMustAlias sl vt fi f)).run s =
        (egalTfunc n E p x f).run s) ∧
    (∀ p sl d th el isd, (egalTfunc (n + 1) E (.conditionals p) (.const (boolVal false))
        (.conditional sl d th el isd)).run s = (mkConditional sl d el th).run s) ∧
    (∀ p sl d th el isd, (egalTfunc (n + 1) E (.conditionals p) (.const (boolVal true))
        (.conditional sl d th el isd)).run s = .ok (.conditional sl d th el isd, s)) ∧
    (∀ p sl d th el isd v, asBool? v = none →
      (egalTfunc (n + 1) E (.conditionals p) (.const v) (.conditional sl d th el isd)).run s =
        .ok (constBool false, s)) ∧
    (∀ p sl d th el isd t,
      (egalTfunc (n + 1) E (.conditionals p) (.conditional sl d th el isd) (.ty t)).run s =
        (egalTfunc n E p (.conditional sl d th el isd) (.ty t)).run s) ∧
    (∀ p sl d th el isd t,
      (egalTfunc (n + 1) E (.conditionals p) (.ty t) (.conditional sl d th el isd)).run s =
        (egalTfunc n E p (.ty t) (.conditional sl d th el isd)).run s) ∧
    (∀ p sl d th el isd sl' d' th' el' isd', th'.isBottom = false → el'.isBottom = false →
      (egalTfunc (n + 1) E (.conditionals p) (.conditional sl d th el isd)
        (.conditional sl' d' th' el' isd')).run s =
        (egalTfunc n E p (.conditional sl d th el isd) (.ty boolTy)).run s) ∧
    (∀ a yt s₁ s₂, (JuliaLean.Compiler.egal n E yt (typeOf a)).run s = .ok (true, s₁) →
      (issingletontype n E yt).run s₁ = .ok (true, s₂) →
      (egalTfunc (n + 1) E .consts (.const a) (.ty yt)).run s = .ok (constBool true, s₂)) ∧
    (∀ xt b s₁ s₂, (JuliaLean.Compiler.egal n E xt (typeOf b)).run s = .ok (true, s₁) →
      (issingletontype n E xt).run s₁ = .ok (true, s₂) →
      (egalTfunc (n + 1) E .consts (.ty xt) (.const b)).run s = .ok (constBool true, s₂)) ∧
    (∀ a yt s₁, (JuliaLean.Compiler.egal n E yt (typeOf a)).run s = .ok (false, s₁) →
      (egalTfunc (n + 1) E .consts (.const a) (.ty yt)).run s =
        (egalTfunc n E .jlType (.const a) (.ty yt)).run s₁) ∧
    (∀ a yt s₁ s₂, (JuliaLean.Compiler.egal n E yt (typeOf a)).run s = .ok (true, s₁) →
      (issingletontype n E yt).run s₁ = .ok (false, s₂) →
      (egalTfunc (n + 1) E .consts (.const a) (.ty yt)).run s =
        (egalTfunc n E .jlType (.const a) (.ty yt)).run s₂)

/-- The singleton test of `egal_tfunc(::ConstsLattice, ...)`: `t === u && issingletontype(t)`. -/
def egalSingleCheck (n : Nat) (E : CEnv) (t u : Val) : CM Bool := do
  if !(← JuliaLean.Compiler.egal n E t u) then return false
  issingletontype n E t

theorem egalTfuncBranches_proven : EgalTfuncBranches := by
  intro n E s
  refine ⟨fun p sl d vt fi f y h1 h2 => ?_, fun p x sl vt fi f h1 h2 => ?_,
    fun p sl d th el isd => rfl, fun p sl d th el isd => rfl,
    fun p sl d th el isd v hv => ?_, fun p sl d th el isd t => rfl, fun p sl d th el isd t => rfl,
    fun p sl d th el isd sl' d' th' el' isd' h1 h2 => ?_,
    fun a yt s₁ s₂ h1 h2 => ?_, fun xt b s₁ s₂ h1 h2 => ?_, fun a yt s₁ h1 => ?_,
    fun a yt s₁ s₂ h1 h2 => ?_⟩
  · have hw := widenmustalias_id y h1 h2
    have hm : widenmustalias (.mustAlias sl d vt fi f) = pure f := rfl
    simp only [egalTfunc, hm, hw, pure_bind]
  · have hw := widenmustalias_id x h1 h2
    have hm : widenmustalias (.interMustAlias sl vt fi f) = pure f := rfl
    simp only [egalTfunc, hm, hw, pure_bind]
  · simp [egalTfunc, widenconditional, hv, constBool]; try rfl
  · have hw := widenconditional_bool sl' d' th' el' isd' h1 h2
    simp only [egalTfunc, hw]; try rfl
  · have hcx : (egalSingleCheck n E yt (typeOf a)).run s = .ok (true, s₂) := by
      unfold egalSingleCheck; rw [run_bind_ok h1]; exact h2
    have hor : (JuliaLean.Compiler.orM (egalSingleCheck n E yt (typeOf a)) (pure false)).run s =
        .ok (true, s₂) := by
      unfold JuliaLean.Compiler.orM; rw [run_bind_ok hcx]; try rfl
    show (JuliaLean.Compiler.orM (egalSingleCheck n E yt (typeOf a)) (pure false) >>= _).run s = _
    rw [run_bind_ok hor]; try rfl
  · have hcy : (egalSingleCheck n E xt (typeOf b)).run s = .ok (true, s₂) := by
      unfold egalSingleCheck; rw [run_bind_ok h1]; exact h2
    have hor : (JuliaLean.Compiler.orM (pure false) (egalSingleCheck n E xt (typeOf b))).run s =
        .ok (true, s₂) := hcy
    show (JuliaLean.Compiler.orM (pure false) (egalSingleCheck n E xt (typeOf b)) >>= _).run s = _
    rw [run_bind_ok hor]; try rfl
  · have hcx : (egalSingleCheck n E yt (typeOf a)).run s = .ok (false, s₁) := by
      unfold egalSingleCheck; rw [run_bind_ok h1]; try rfl
    have hor : (JuliaLean.Compiler.orM (egalSingleCheck n E yt (typeOf a)) (pure false)).run s =
        .ok (false, s₁) := by
      unfold JuliaLean.Compiler.orM; rw [run_bind_ok hcx]; try rfl
    show (JuliaLean.Compiler.orM (egalSingleCheck n E yt (typeOf a)) (pure false) >>= _).run s = _
    rw [run_bind_ok hor]; try rfl
  · have hcx : (egalSingleCheck n E yt (typeOf a)).run s = .ok (false, s₂) := by
      unfold egalSingleCheck; rw [run_bind_ok h1]; exact h2
    have hor : (JuliaLean.Compiler.orM (egalSingleCheck n E yt (typeOf a)) (pure false)).run s =
        .ok (false, s₂) := by
      unfold JuliaLean.Compiler.orM; rw [run_bind_ok hcx]; try rfl
    show (JuliaLean.Compiler.orM (egalSingleCheck n E yt (typeOf a)) (pure false) >>= _).run s = _
    rw [run_bind_ok hor]; try rfl

def EgalTfuncSpec : Prop := EgalTfuncBase ∧ EgalTfuncBranches

theorem egalTfuncSpec_proven : EgalTfuncSpec := ⟨egalTfuncBase_proven, egalTfuncBranches_proven⟩

/-! ## `nfields` -/

/-- The result is the native type `Int`. -/
def isLongTy : LElt → Bool
  | .ty t => t == longType
  | _ => false

/-- The branches of `nfields_tfunc` (`Compiler/src/tfuncs.jl:620-645`) on a native-type argument,
by its unwrapped `widenconst`: `Type{T}` with a unique `T` folds to `nfields(T)`; an abstract
`DataType` is `Int`; a concrete struct type other than a tuple is `Const` of its field count; a
tuple type is `Const` of its length without a `Vararg` and `Int` with one; a `Union` is `Int` when
its first member gives `Int`, and otherwise the `tmerge` of both members; anything else
(`Union{}`, a `TypeVar`) is `Int`. -/
def NfieldsTfuncBranches : Prop :=
  ∀ n T L t0 s xt s₁, (widenconst n T.E (.ty t0)).run s = .ok (xt, s₁) →
    (isconstType (unwrapUnionall xt) = true → ∀ p s₂,
      (typeParameter (unwrapUnionall xt)).run s₁ = .ok (p, s₂) →
      (nfieldsTfunc (n + 1) T L (.ty t0)).run s =
        (nfieldsRT T.E p >>= fun k => pure (LElt.const (.long k))).run s₂) ∧
    (∀ name ps, unwrapUnionall xt = .datatype name ps →
      (∀ s₂, (isabstracttype T.E (.datatype name ps)).run s₁ = .ok (true, s₂) →
        (nfieldsTfunc (n + 1) T L (.ty t0)).run s = .ok (.ty longType, s₂)) ∧
      (∀ s₂, (isabstracttype T.E (.datatype name ps)).run s₁ = .ok (false, s₂) →
        (name == tupleName) = false → (name == namedTupleName) = false →
        (nfieldsTfunc (n + 1) T L (.ty t0)).run s =
          (T.tn name >>= fun i => pure (LElt.const (.long i.names.length))).run s₂) ∧
      (∀ s₂, (isabstracttype T.E (.datatype name ps)).run s₁ = .ok (false, s₂) →
        (name == tupleName) = true → isvatuple (.datatype name ps) = true →
        (nfieldsTfunc (n + 1) T L (.ty t0)).run s = .ok (.ty longType, s₂)) ∧
      (∀ s₂, (isabstracttype T.E (.datatype name ps)).run s₁ = .ok (false, s₂) →
        (name == tupleName) = true → isvatuple (.datatype name ps) = false →
        (nfieldsTfunc (n + 1) T L (.ty t0)).run s = .ok (.const (.long ps.length), s₂))) ∧
    (∀ a b, unwrapUnionall xt = .union a b → ∀ a' s₂ na s₃,
      (unwraptv n a).run s₁ = .ok (a', s₂) → (nfieldsTfunc n T L (.ty a')).run s₂ = .ok (na, s₃) →
      (isLongTy na = true → (nfieldsTfunc (n + 1) T L (.ty t0)).run s = .ok (.ty longType, s₃)) ∧
      (isLongTy na = false → (nfieldsTfunc (n + 1) T L (.ty t0)).run s =
        (do return ← tmerge n T.E L na (← nfieldsTfunc n T L (.ty (← unwraptv n b)))).run s₃)) ∧
    (isconstType (unwrapUnionall xt) = false → (unwrapUnionall xt).isDatatype = false →
      (unwrapUnionall xt).isUnion = false →
      (nfieldsTfunc (n + 1) T L (.ty t0)).run s = .ok (.ty longType, s₁))

theorem nfieldsTfuncBranches_proven : NfieldsTfuncBranches := by
  intro n T L t0 s xt s₁ hw
  refine ⟨fun hc p s₂ hp => ?_, fun name ps hu => ⟨fun s₂ ha => ?_, fun s₂ ha h1 h2 => ?_,
    fun s₂ ha h1 h2 => ?_, fun s₂ ha h1 h2 => ?_⟩, fun a b hu a' s₂ na s₃ ha hn => ⟨fun hl => ?_,
    fun hl => ?_⟩, fun hc hd hun => ?_⟩
  all_goals
    show (widenconst n T.E (.ty t0) >>= _).run s = _
    rw [run_bind_ok hw]
  · simp only [hc, ite_true]
    show (typeParameter (unwrapUnionall xt) >>= _).run s₁ = _
    rw [run_bind_ok hp]; try rfl
  all_goals try simp only [hu]
  · show (isabstracttype T.E (.datatype name ps) >>= _).run s₁ = _
    rw [run_bind_ok ha]; try rfl
  · show (isabstracttype T.E (.datatype name ps) >>= _).run s₁ = _
    rw [run_bind_ok ha]
    simp only [h1, h2, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]; try rfl
  · show (isabstracttype T.E (.datatype name ps) >>= _).run s₁ = _
    rw [run_bind_ok ha]
    simp only [h1, h2, Bool.not_false, ite_true]; try rfl
  · show (isabstracttype T.E (.datatype name ps) >>= _).run s₁ = _
    rw [run_bind_ok ha]
    simp only [h1, h2, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]; try rfl
  · show (unwraptv n a >>= _).run s₁ = _
    rw [run_bind_ok ha]
    show (nfieldsTfunc n T L (.ty a') >>= _).run s₂ = _
    rw [run_bind_ok hn]
    cases na with
    | ty t => simp only [isLongTy] at hl; simp only [hl, ite_true]; try rfl
    | _ => simp [isLongTy] at hl
  · show (unwraptv n a >>= _).run s₁ = _
    rw [run_bind_ok ha]
    show (nfieldsTfunc n T L (.ty a') >>= _).run s₂ = _
    rw [run_bind_ok hn]
    cases na with
    | ty t => simp only [isLongTy] at hl; simp only [hl, Bool.false_eq_true, ite_false]; try rfl
    | _ => rfl
  · simp only [hc, Bool.false_eq_true, ite_false]
    generalize hx : unwrapUnionall xt = u at hd hun ⊢
    cases u <;> simp_all [Val.isDatatype, Val.isUnion] <;> try rfl

def NfieldsTfuncSpec : Prop := NfieldsTfuncBase ∧ NfieldsTfuncBranches

theorem nfieldsTfuncSpec_proven : NfieldsTfuncSpec := ⟨nfieldsTfuncBase_proven, nfieldsTfuncBranches_proven⟩

/-! ## `typeof` -/

/-- The branches of `typeof_tfunc` (`Compiler/src/tfuncs.jl:882-920`) on a native-type argument,
by its `widenconst` `tt` (not a `Type{T}` with unique `T`, which `TypeofTfuncBase` covers):
`TypeEq{T}` is `DataType` (its value is only `== T`, #61323); a concrete `DataType` is `Const`
of itself; `Any` is `DataType`; a tuple type abstract only in its length gives the
`typeof_concrete_vararg` type; any other abstract `DataType` is `Type{<:tt}`; a `Union` is the
`Union` of the widened `_typeof_tfunc` of its members; a `UnionAll` over a concrete non-tuple
type is `Type{u}` rewrapped, and over an abstract type the rewrapped `typeof_tfunc` of the body;
anything else (`Union{}`) is `DataType`. `_typeof_tfunc` of a non-`TypeVar` is `typeof_tfunc`. -/
def TypeofTfuncBranches : Prop :=
  ∀ n E s,
    (∀ t, t.isTypevar = false → (typeofTfunc_ (n + 1) E t).run s = (typeofTfunc n E (.ty t)).run s) ∧
    ∀ t0 tt s₁, (widenconst n E (.ty t0)).run s = .ok (tt, s₁) → isconstType tt = false →
    (isTypeEq tt = true → (typeofTfunc (n + 1) E (.ty t0)).run s = .ok (.ty datatypeType, s₁)) ∧
    (isTypeEq tt = false → tt.isDatatype = true →
      (∀ s₂, (isconcretetype E tt).run s₁ = .ok (true, s₂) →
        (typeofTfunc (n + 1) E (.ty t0)).run s = .ok (.const tt, s₂)) ∧
      (∀ s₂, (isconcretetype E tt).run s₁ = .ok (false, s₂) → (tt == anyType) = true →
        (typeofTfunc (n + 1) E (.ty t0)).run s = .ok (.ty datatypeType, s₂)) ∧
      (∀ s₂, (isconcretetype E tt).run s₁ = .ok (false, s₂) → (tt == anyType) = false →
        (tt.name? == some tupleName) = false →
        (typeofTfunc (n + 1) E (.ty t0)).run s =
          (do let tv ← jlNewTypeVar typeofTypevarName tt
              return LElt.ty (← jlUnionAll n E tv (← mkTypeEq n E tv))).run s₂) ∧
      (∀ s₂ tt' s₃, (isconcretetype E tt).run s₁ = .ok (false, s₂) → (tt == anyType) = false →
        (tt.name? == some tupleName) = true → (typeofConcreteVararg n E tt).run s₂ = .ok (some tt', s₃) →
        (typeofTfunc (n + 1) E (.ty t0)).run s = .ok (.ty tt', s₃)) ∧
      (∀ s₂ s₃, (isconcretetype E tt).run s₁ = .ok (false, s₂) → (tt == anyType) = false →
        (tt.name? == some tupleName) = true → (typeofConcreteVararg n E tt).run s₂ = .ok (none, s₃) →
        (typeofTfunc (n + 1) E (.ty t0)).run s =
          (do let tv ← jlNewTypeVar typeofTypevarName tt
              return LElt.ty (← jlUnionAll n E tv (← mkTypeEq n E tv))).run s₃)) ∧
    (∀ a b, tt = .union a b → (typeofTfunc (n + 1) E (.ty t0)).run s =
      (do let a ← widenconst n E (← typeofTfunc_ n E a)
          let b ← widenconst n E (← typeofTfunc_ n E b)
          return LElt.ty (← jlUnion n E [a, b])).run s₁) ∧
    (∀ id nm lb ub body, tt = .unionall id nm lb ub body →
      (unwrapUnionall tt).isDatatype = true →
      (∀ s₂, (isabstracttype E (unwrapUnionall tt)).run s₁ = .ok (false, s₂) →
        ((unwrapUnionall tt).name? == some tupleName) = false →
        (typeofTfunc (n + 1) E (.ty t0)).run s =
          (do return LElt.ty (← rewrapUnionallJ n E (← mkTypeEq n E (unwrapUnionall tt)) tt)).run s₂) ∧
      (∀ s₂, (isabstracttype E (unwrapUnionall tt)).run s₁ = .ok (true, s₂) →
        (typeofTfunc (n + 1) E (.ty t0)).run s =
          (do return LElt.ty (← rewrapUnionallJ n E
            (← widenconst n E (← typeofTfunc n E (.ty (unwrapUnionall tt)))) tt)).run s₂)) ∧
    (isTypeEq tt = false → tt.isDatatype = false → tt.isUnion = false → tt.isUnionall = false →
      (typeofTfunc (n + 1) E (.ty t0)).run s = .ok (.ty datatypeType, s₁))

theorem typeofTfuncBranches_proven : TypeofTfuncBranches := by
  intro n E s
  refine ⟨fun t ht => ?_, fun t0 tt s₁ hw hc => ⟨fun he => ?_, fun he hd => ⟨fun s₂ hk => ?_,
    fun s₂ hk ha => ?_, fun s₂ hk ha htu => ?_, fun s₂ tt' s₃ hk ha htu hv => ?_,
    fun s₂ s₃ hk ha htu hv => ?_⟩, fun a b hu => ?_, fun id nm lb ub body hu hd =>
    ⟨fun s₂ hk htu => ?_, fun s₂ hk => ?_⟩, fun he hd hun hua => ?_⟩⟩
  · cases t <;> simp_all [Val.isTypevar, typeofTfunc_]
  all_goals
    show (widenconst n E (.ty t0) >>= _).run s = _
    rw [run_bind_ok hw]
    simp only [hc, Bool.false_eq_true, ite_false]
  · simp only [he, ite_true]; try rfl
  all_goals try simp only [he, hd, Bool.false_eq_true, ite_false, ite_true]
  · show (isconcretetype E tt >>= _).run s₁ = _
    rw [run_bind_ok hk]; try rfl
  · show (isconcretetype E tt >>= _).run s₁ = _
    rw [run_bind_ok hk]; simp only [ha, Bool.false_eq_true, ite_false, ite_true]; try rfl
  · show (isconcretetype E tt >>= _).run s₁ = _
    rw [run_bind_ok hk]; simp only [ha, htu, Bool.false_eq_true, ite_false]; try rfl
  · show (isconcretetype E tt >>= _).run s₁ = _
    rw [run_bind_ok hk]; simp only [ha, htu, Bool.false_eq_true, ite_false, ite_true]
    show (typeofConcreteVararg n E tt >>= _).run s₂ = _
    rw [run_bind_ok hv]; try rfl
  · show (isconcretetype E tt >>= _).run s₁ = _
    rw [run_bind_ok hk]; simp only [ha, htu, Bool.false_eq_true, ite_false, ite_true]
    show (typeofConcreteVararg n E tt >>= _).run s₂ = _
    rw [run_bind_ok hv]; try rfl
  · subst hu; try rfl
  · subst hu
    show (isabstracttype E (unwrapUnionall (.unionall id nm lb ub body)) >>= _).run s₁ = _
    rw [run_bind_ok hk]
    simp only [hd, htu, Bool.not_false, Bool.true_and, Bool.and_true, ite_true,
      Bool.false_eq_true, ite_false]
    try rfl
  · subst hu
    show (isabstracttype E (unwrapUnionall (.unionall id nm lb ub body)) >>= _).run s₁ = _
    rw [run_bind_ok hk]
    simp only [hd, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
    try rfl
  · cases tt <;> simp_all [Val.isDatatype, Val.isUnion, Val.isUnionall, isTypeEq] <;> try rfl

def TypeofTfuncSpec : Prop := TypeofTfuncBase ∧ TypeofTfuncBranches

theorem typeofTfuncSpec_proven : TypeofTfuncSpec := ⟨typeofTfuncBase_proven, typeofTfuncBranches_proven⟩

/-! ## `has_free_typevars` -/

/-- The last branches of `has_free_typevars_tfunc` (`Compiler/src/tfuncs.jl:930-944`): when the
widened argument is neither `Type{p}` nor `TypeVar`, the result is `Const(false)` exactly when it
intersects none of `Type`, `TypeVar` and `TypeofVararg` (whose values can have free variables),
and `Bool` otherwise. -/
def HasFreeTypevarsTfuncBranches : Prop :=
  ∀ n E t0 tt s s₁, (widenconst n E (.ty t0)).run s = .ok (tt, s₁) → isType tt = false →
    (tt == tvarType) = false →
    ∀ b1 b2 b3 s₂ s₃ s₄, (hasintersect n E tt typeTypeVal).run s₁ = .ok (b1, s₂) →
      (hasintersect n E tt tvarType).run s₂ = .ok (b2, s₃) →
      (hasintersect n E tt varargType).run s₃ = .ok (b3, s₄) →
      (hasFreeTypevarsTfunc n E (.ty t0)).run s =
        .ok (if !b1 && !b2 && !b3 then constBool false else .ty boolTy, s₄)

theorem hasFreeTypevarsTfuncBranches_proven : HasFreeTypevarsTfuncBranches := by
  intro n E t0 tt s s₁ hw ht hv b1 b2 b3 s₂ s₃ s₄ h1 h2 h3
  show (widenconst n E (.ty t0) >>= _).run s = _
  rw [run_bind_ok hw]
  simp only [ht, hv, Bool.false_eq_true, ite_false]
  show (hasintersect n E tt typeTypeVal >>= _).run s₁ = _
  rw [run_bind_ok h1]
  show (hasintersect n E tt tvarType >>= _).run s₂ = _
  rw [run_bind_ok h2]
  show (hasintersect n E tt varargType >>= _).run s₃ = _
  rw [run_bind_ok h3]
  cases b1 <;> cases b2 <;> cases b3 <;> try rfl

def HasFreeTypevarsTfuncSpec : Prop := HasFreeTypevarsTfuncBase ∧ HasFreeTypevarsTfuncBranches

theorem hasFreeTypevarsTfuncSpec_proven : HasFreeTypevarsTfuncSpec :=
  ⟨hasFreeTypevarsTfuncBase_proven, hasFreeTypevarsTfuncBranches_proven⟩

/-! ## `typeassert_nothrow` -/

/-- `typeassert_nothrow` (`Compiler/src/tfuncs.jl:957`) is false for `Type{P}` or `TypeEgal{P}`
with a free type variable in `P` (from a static parameter, for example), whatever `v` is. -/
def TypeassertNothrowFree : Prop :=
  ∀ n E L v s P,
    (JuliaLean.Compiler.hasFreeTypevars (.typeeq P) = true →
      (typeassertNothrow n E L v (.ty (.typeeq P))).run s = .ok (false, s)) ∧
    (JuliaLean.Compiler.hasFreeTypevars (.typeegal P) = true →
      (typeassertNothrow n E L v (.ty (.typeegal P))).run s = .ok (false, s))

theorem typeassertNothrowFree_proven : TypeassertNothrowFree := by
  intro n E L v s P
  refine ⟨fun hP => ?_, fun hP => ?_⟩ <;>
    simp [typeassertNothrow, isType, isTypeEq, isTypeEgal, Val.isTypeeq, Val.isTypeegal, hP] <;> try rfl

def TypeassertNothrowSpec : Prop := TypeassertNothrowBase ∧ TypeassertNothrowFree

theorem typeassertNothrowSpec_proven : TypeassertNothrowSpec :=
  ⟨typeassertNothrowBase_proven, typeassertNothrowFree_proven⟩

/-! ## `getfield_boundscheck` -/

/-- The flag cases of `getfield_boundscheck` (`Compiler/src/tfuncs.jl:1045-1069`). With three
arguments a third of type `Symbol` (an order) is `:on`, and any other non-`Vararg` third goes to
the flag check, as does a non-`Vararg` fourth argument. The flag check widens a `Conditional`
first: one that can be either is `:unknown`, one that cannot be true is `:off`; a native type is
`:unknown` when it is `Bool` and `:unsafe` otherwise; a non-`Bool` constant is `:unsafe`. -/
def GetfieldBoundscheckFlags : Prop :=
  ∀ n E s a b c d,
    (∀ s₁, c.isVarargElt = false → (widenconst n E c).run s = .ok (symbolType, s₁) →
      (getfieldBoundscheck n E [a, b, c]).run s = .ok ("on", s₁)) ∧
    (∀ t s₁, c.isVarargElt = false → (widenconst n E c).run s = .ok (t, s₁) →
      (t == symbolType) = false →
      (getfieldBoundscheck n E [a, b, c]).run s = (getfieldBoundscheckTail n E c).run s₁) ∧
    (d.isVarargElt = false →
      (getfieldBoundscheck n E [a, b, c, d]).run s = (getfieldBoundscheckTail n E d).run s) ∧
    (∀ t t' s₁, (widenconst n E (.ty t)).run s = .ok (t', s₁) →
      (getfieldBoundscheckTail n E (.ty t)).run s =
        .ok (if t' == boolTy then "unknown" else "unsafe", s₁)) ∧
    (∀ sl dd th el isd, th.isBottom = false → el.isBottom = false →
      (getfieldBoundscheckTail (n + 1) E (.conditional sl dd th el isd)).run s = .ok ("unknown", s)) ∧
    (∀ sl dd el isd,
      (getfieldBoundscheckTail (n + 1) E (.conditional sl dd (.ty .bottom) el isd)).run s =
        .ok ("off", s)) ∧
    (∀ v t s₁, (widenconst n E (.const v)).run s = .ok (t, s₁) → (t == boolTy) = false →
      (getfieldBoundscheckTail n E (.const v)).run s = .ok ("unsafe", s₁))

theorem getfieldBoundscheckFlags_proven : GetfieldBoundscheckFlags := by
  intro n E s a b c d
  refine ⟨fun s₁ hv hw => ?_, fun t s₁ hv hw ht => ?_, fun hv => ?_, fun t t' s₁ hw => ?_,
    fun sl dd th el isd h1 h2 => ?_, fun sl dd el isd => rfl, fun v t s₁ hw ht => ?_⟩
  · simp only [getfieldBoundscheck, hv, Bool.false_eq_true, ite_false]
    show (widenconst n E c >>= _).run s = _
    rw [run_bind_ok hw]; try rfl
  · simp only [getfieldBoundscheck, hv, Bool.false_eq_true, ite_false]
    show (widenconst n E c >>= _).run s = _
    rw [run_bind_ok hw]; simp only [ht, Bool.false_eq_true, ite_false]
  · simp only [getfieldBoundscheck, hv, Bool.false_eq_true, ite_false]
  · show (widenconditional (.ty t) >>= _).run s = _
    rw [run_bind_ok (show (widenconditional (.ty t)).run s = .ok (.ty t, s) from rfl)]
    show (widenconst n E (.ty t) >>= _).run s = _
    rw [run_bind_ok hw]
    cases h : t' == boolTy <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] <;> try rfl
  · have hw := widenconditional_bool sl dd th el isd h1 h2
    unfold getfieldBoundscheckTail
    rw [hw]; try rfl
  · show (widenconditional (.const v) >>= _).run s = _
    rw [run_bind_ok (show (widenconditional (.const v)).run s = .ok (.const v, s) from rfl)]
    show (widenconst n E (.const v) >>= _).run s = _
    rw [run_bind_ok hw]
    simp only [ht, Bool.false_eq_true, ite_false]; try rfl

def GetfieldBoundscheckSpec : Prop := GetfieldBoundscheckBase ∧ GetfieldBoundscheckFlags

theorem getfieldBoundscheckSpec_proven : GetfieldBoundscheckSpec :=
  ⟨getfieldBoundscheckBase_proven, getfieldBoundscheckFlags_proven⟩

/-! ## `getfield_tfunc` argument checks -/

/-- The passing cases of the `getfield_tfunc` argument checks (`Compiler/src/tfuncs.jl:1169-1182`):
a three-argument call whose third argument intersects `Symbol`, or `Bool`, or is a `Vararg`, is
`_getfield_tfunc(s00, name, false)`; a four-argument call whose order intersects `Symbol` and whose
non-`Vararg` flag does not intersect `Bool` is `Union{}`, and one whose flag does is
`_getfield_tfunc(s00, name, false)`. -/
def GetfieldTfuncArgsPass : Prop :=
  ∀ n T L s00 name s,
    (∀ bo t s₁ s₂, bo.isVarargElt = false → (widenconst n T.E bo).run s = .ok (t, s₁) →
      (hasintersect n T.E t symbolType).run s₁ = .ok (true, s₂) →
      (getfieldTfunc n T L [s00, name, bo]).run s = (getfieldTfuncL n T L s00 name false).run s₂) ∧
    (∀ bo t s₁ s₂ s₃, bo.isVarargElt = false → (widenconst n T.E bo).run s = .ok (t, s₁) →
      (hasintersect n T.E t symbolType).run s₁ = .ok (false, s₂) →
      (hasintersect n T.E t boolTy).run s₂ = .ok (true, s₃) →
      (getfieldTfunc n T L [s00, name, bo]).run s = (getfieldTfuncL n T L s00 name false).run s₃) ∧
    (∀ bo, bo.isVarargElt = true →
      (getfieldTfunc n T L [s00, name, bo]).run s = (getfieldTfuncL n T L s00 name false).run s) ∧
    (∀ order bc t s₁ s₂ u s₃ s₄, bc.isVarargElt = false → (widenconst n T.E order).run s = .ok (t, s₁) →
      (hasintersect n T.E t symbolType).run s₁ = .ok (true, s₂) →
      (widenconst n T.E bc).run s₂ = .ok (u, s₃) →
      (hasintersect n T.E u boolTy).run s₃ = .ok (false, s₄) →
      (getfieldTfunc n T L [s00, name, order, bc]).run s = .ok (.ty .bottom, s₄)) ∧
    (∀ order bc t s₁ s₂ u s₃ s₄, bc.isVarargElt = false → (widenconst n T.E order).run s = .ok (t, s₁) →
      (hasintersect n T.E t symbolType).run s₁ = .ok (true, s₂) →
      (widenconst n T.E bc).run s₂ = .ok (u, s₃) →
      (hasintersect n T.E u boolTy).run s₃ = .ok (true, s₄) →
      (getfieldTfunc n T L [s00, name, order, bc]).run s = (getfieldTfuncL n T L s00 name false).run s₄)

theorem getfieldTfuncArgsPass_proven : GetfieldTfuncArgsPass := by
  intro n T L s00 name s
  refine ⟨fun bo t s₁ s₂ hv hw h₁ => ?_, fun bo t s₁ s₂ s₃ hv hw h₁ h₂ => ?_, fun bo hv => ?_,
    fun order bc t s₁ s₂ u s₃ s₄ hv hw h₁ hu h₂ => ?_,
    fun order bc t s₁ s₂ u s₃ s₄ hv hw h₁ hu h₂ => ?_⟩
  · simp only [getfieldTfunc, hv, Bool.not_false, ite_true]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    have hor : (JuliaLean.Compiler.orM (hasintersect n T.E t symbolType)
        (hasintersect n T.E t boolTy)).run s₁ = .ok (true, s₂) := by
      unfold JuliaLean.Compiler.orM; rw [run_bind_ok h₁]; try rfl
    refine (stbind_run_ok hor).trans ?_; try rfl
  · simp only [getfieldTfunc, hv, Bool.not_false, ite_true]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    have hor : (JuliaLean.Compiler.orM (hasintersect n T.E t symbolType)
        (hasintersect n T.E t boolTy)).run s₁ = .ok (true, s₃) := by
      unfold JuliaLean.Compiler.orM; rw [run_bind_ok h₁]; exact h₂
    refine (stbind_run_ok hor).trans ?_; try rfl
  · simp only [getfieldTfunc, hv, Bool.not_true, Bool.false_eq_true, ite_false]
  · simp only [getfieldTfunc]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    refine (stbind_run_ok h₁).trans ?_
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, hv, Bool.not_false, ite_true]
    refine (stbind_run_ok hu).trans ?_
    refine (stbind_run_ok h₂).trans ?_; try rfl
  · simp only [getfieldTfunc]
    rw [StateT.run_bind, hw]
    dsimp only [bind, Except.bind]
    refine (stbind_run_ok h₁).trans ?_
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, hv, Bool.not_false, ite_true]
    refine (stbind_run_ok hu).trans ?_
    refine (stbind_run_ok h₂).trans ?_; try rfl

def GetfieldTfuncArgsSpec : Prop := GetfieldTfuncArgsBase ∧ GetfieldTfuncArgsPass

theorem getfieldTfuncArgsSpec_proven : GetfieldTfuncArgsSpec :=
  ⟨getfieldTfuncArgsBase_proven, getfieldTfuncArgsPass_proven⟩

/-! ## `tuple` -/

/-- The paths of `tuple_tfunc` (`Compiler/src/tfuncs.jl:2305-2366`) after the empty case. The
arguments are unwrapped by `widenslotwrapper` and a trailing `Vararg{Union{}}` is dropped (it
must be empty). All-constant arguments fold to `Const(tuple(args...))`; otherwise a `Union{}`
parameter makes the result `Union{}`; a singleton tuple type is the `Const` of its instance; with
extended information the result is a `PartialStruct` of the tuple type over the updated argument
types, and without it the tuple type itself. -/
def TupleTfuncPaths : Prop :=
  (∀ pre N, tupleDropBottomVararg (pre ++ [.ty (.vararg (some .bottom) N)]) = pre) ∧
  (∀ args, hasVararg args = false → tupleDropBottomVararg args = args) ∧
  ∀ n E L args s ws s₁, args ≠ [] → (args.mapM widenslotwrapper).run s = .ok (ws, s₁) →
    (∀ s₂, (isAllConstArg n E (tupleDropBottomVararg ws)).run s₁ = .ok (true, s₂) →
      (tupleTfunc n E L args).run s =
        (do return LElt.const (← tupleRT n E (← collectConstArgs E (tupleDropBottomVararg ws)))).run s₂) ∧
    (∀ s₂ s₃, (isAllConstArg n E (tupleDropBottomVararg ws)).run s₁ = .ok (false, s₂) →
      (tupleTfuncParams n E L (tupleDropBottomVararg ws)).run s₂ = .ok (none, s₃) →
      (tupleTfunc n E L args).run s = .ok (.ty .bottom, s₃)) ∧
    (∀ s₂ ps ai na s₃ typ s₄, (isAllConstArg n E (tupleDropBottomVararg ws)).run s₁ = .ok (false, s₂) →
      (tupleTfuncParams n E L (tupleDropBottomVararg ws)).run s₂ = .ok (some (ps, ai, na), s₃) →
      (jlTuple n E ps).run s₃ = .ok (typ, s₄) →
      (∀ s₅, (issingletontype n E typ).run s₄ = .ok (true, s₅) →
        (tupleTfunc n E L args).run s = .ok (.const (singletonInstance E typ), s₅)) ∧
      (∀ s₅, (issingletontype n E typ).run s₄ = .ok (false, s₅) → ai = false →
        (tupleTfunc n E L args).run s = .ok (.ty typ, s₅)) ∧
      (∀ s₅ u s₆, (issingletontype n E typ).run s₄ = .ok (false, s₅) → ai = true →
        (partialstructInitUndefs E typ na).run s₅ = .ok (some u, s₆) →
        (tupleTfunc n E L args).run s = (mkPartialStruct n E typ u na).run s₆))

theorem tupleTfuncPaths_proven : TupleTfuncPaths := by
  refine ⟨fun pre N => ?_, fun args hv => ?_, fun n E L args s ws s₁ hne hws => ?_⟩
  · simp [tupleDropBottomVararg] <;> rfl
  · unfold tupleDropBottomVararg
    split
    · rename_i va N h
      simp [hasVararg, h, LElt.isVarargElt, Val.isVararg] at hv
    · rfl
  · have hemp : args.isEmpty = false := by cases args <;> simp_all
    have pre : (tupleTfunc n E L args).run s = (do
        let argtypes := tupleDropBottomVararg ws
        if ← isAllConstArg n E argtypes then
          return LElt.const (← tupleRT n E (← collectConstArgs E argtypes))
        let some (params, anyinfo, newArgtypes) ← tupleTfuncParams n E L argtypes
          | return .ty .bottom
        let typ ← jlTuple n E params
        if ← issingletontype n E typ then return .const (singletonInstance E typ)
        if anyinfo then
          let some undefs ← partialstructInitUndefs E typ newArgtypes
            | jlThrow "TypeError" "typeassert Vector"
          return ← mkPartialStruct n E typ undefs newArgtypes
        return .ty typ : CM LElt).run s₁ := by
      simp only [tupleTfunc, hemp, Bool.false_eq_true, ite_false]
      rw [StateT.run_bind, hws]; try rfl
    rw [pre]
    refine ⟨fun s₂ ha => ?_, fun s₂ s₃ ha hp => ?_, fun s₂ ps ai na s₃ typ s₄ ha hp ht =>
      ⟨fun s₅ hs => ?_, fun s₅ hs hai => ?_, fun s₅ u s₆ hs hai hu => ?_⟩⟩
    · show (isAllConstArg n E (tupleDropBottomVararg ws) >>= _).run s₁ = _
      rw [run_bind_ok ha]; try rfl
    all_goals
      show (isAllConstArg n E (tupleDropBottomVararg ws) >>= _).run s₁ = _
      rw [run_bind_ok ha]
      show (tupleTfuncParams n E L (tupleDropBottomVararg ws) >>= _).run s₂ = _
      rw [run_bind_ok hp]
    · rfl
    all_goals
      show (jlTuple n E ps >>= _).run s₃ = _
      rw [run_bind_ok ht]
      show (issingletontype n E typ >>= _).run s₄ = _
      rw [run_bind_ok hs]
    · rfl
    · subst hai; try rfl
    · subst hai
      show (partialstructInitUndefs E typ na >>= _).run s₅ = _
      rw [run_bind_ok hu]

def TupleTfuncSpec : Prop := TupleTfuncBase ∧ TupleTfuncPaths

theorem tupleTfuncSpec_proven : TupleTfuncSpec := ⟨tupleTfuncBase_proven, tupleTfuncPaths_proven⟩

end JuliaLean.Proofs.Compiler.Tfuncs
