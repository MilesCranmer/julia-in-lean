import JuliaLean.Compiler.src.tfuncs
import JuliaLean.Proofs.Compiler.src.typelattice.Common

/-!
Shared vocabulary for the properties of `Compiler/src/tfuncs.jl`.

The soundness of a tfunc relates lattice elements to runtime values through a concretization
`γ`: `inGamma n E v e` says the value `v` is one of the values the lattice element `e` stands
for. It is exact for `Const` (egality, `===`) and for native types (`isa`); for the other
wrappers it uses `widenconst`, which over-approximates `γ`. The statements here only put `Const`
and native-type elements on the argument side, where an over-approximation would make a
counterexample unconvincing.

As in `typelattice/Common.lean`, the statements are partial-correctness statements: they
constrain what a call returns when it returns, and say nothing about runs that end in a model
failure (exhausted fuel, `unmodelled:`).

Kernel evaluation of the concrete counterexamples. `jl_egal` is defined by well-founded recursion,
and the `while` loops of the subtyping and type-construction models are `partial`, so `rfl` does
not reduce through them. The counterexamples below avoid those loops; each `jl_egal` call is
rewritten with a lemma proved by unfolding `jl_egal` once.
-/

namespace JuliaLean.Proofs.Compiler.Tfuncs

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- `v ∈ γ(e)`: `v === c` for `Const(c)`, `isa(v, t)` for a native type `t`, and
`isa(v, widenconst(e))` for every other element. No value is in `γ(Union{})`. -/
def inGamma (n : Nat) (E : CEnv) (v : Val) : LElt → CM Bool
  | .const c => JuliaLean.Compiler.egal n E v c
  | .ty .bottom => pure false
  | .ty t => isa n E v t
  | e => do isa n E v (← widenconst n E e)

/-- The argument values `vals` lie in the concretization of `argtypes`. A trailing
`Vararg{T}` (or `Vararg{T, N}`, whose length is not checked) matches any number of values of
`γ(T)`. -/
def argsIn (n : Nat) (E : CEnv) : List Val → List LElt → CM Bool
  | [], [] => pure true
  | vs, [.ty (.vararg T _)] => vs.allM fun v => inGamma n E v (.ty (T.getD anyType))
  | v :: vs, a :: as => JuliaLean.Compiler.andM (inGamma n E v a) (argsIn n E vs as)
  | _, _ => pure false

/-- `argsIn` returns `true` from some state. -/
def ArgsHold (n : Nat) (E : CEnv) (vals : List Val) (argtypes : List LElt) : Prop :=
  ∃ s s', (argsIn n E vals argtypes).run s = .ok (true, s')

/-- Soundness of `builtin_tfunction` for the builtin `f` on the lattice `L`: for argument
values in the concretization of the argument types, a call that returns gives a value in the
concretization of the tfunc result. In particular a `Union{}` result means the call never
returns. -/
def TfuncSound (L : Lattice) (f : String) : Prop :=
  ∀ n T argtypes vals, ArgsHold n T.E vals argtypes →
    Returns (builtinRT n T.E f vals) fun r =>
      Returns (builtinTfunction n T L f argtypes) fun R =>
        Returns (inGamma n T.E r R) (· = true)

/-! ## A small type universe for counterexamples -/

def integerTy : Val := .datatype "Core.Integer" []
def stringTy : Val := .datatype "Core.String" []

/-- The `Core` type names the counterexamples reach (`src/jltypes.c:3592-3803`), plus
`Integer`, `Int64`, `Bool` and `String`. -/
def cxNames : List TypeName :=
  [ { name := "Core.Integer", abstract := true, mutable := false, wrapper := integerTy, super := some anyType }
  , { name := "Core.Int64", abstract := false, mutable := false, wrapper := longType, super := some integerTy }
  , { name := "Core.Bool", abstract := false, mutable := false, wrapper := boolTy, super := some integerTy }
  , { name := "Core.String", abstract := false, mutable := true, wrapper := stringTy, super := some anyType }
  , { name := "Core.Any", abstract := true, mutable := false, wrapper := anyType, super := none }
  , { name := "Core.AnyType", abstract := true, mutable := false, wrapper := anytypeType, super := some anyType }
  , { name := "Core.TypeofBottom", abstract := false, mutable := false, wrapper := typeofbottomType, super := some anytypeType }
  , { name := "Core.TypeEq", abstract := false, mutable := false, wrapper := typeeqType, super := some anytypeType }
  , { name := "Core.TypeEgal", abstract := false, mutable := false, wrapper := typeegalType, super := some anytypeType }
  , { name := "Core.DataType", abstract := false, mutable := true, wrapper := datatypeType, super := some anytypeType }
  , { name := "Core.Union", abstract := false, mutable := false, wrapper := uniontypeType, super := some anytypeType }
  , { name := "Core.UnionAll", abstract := false, mutable := false, wrapper := unionallType, super := some anytypeType }
  , { name := "Core.Intersect", abstract := false, mutable := false, wrapper := intersectType, super := some anytypeType }
  , { name := "Core.TypeVar", abstract := false, mutable := true, wrapper := tvarType, super := some anyType }
  , { name := "Core.TypeofVararg", abstract := false, mutable := false, wrapper := varargType, super := some anyType }
  , { name := "Core.Symbol", abstract := false, mutable := true, wrapper := symbolType, super := some anyType }
  , { name := "Core.Tuple", abstract := false, mutable := false, wrapper := anytupleType, super := some anyType }
  ]

def cxLayouts : List Layout :=
  [ { dt := longType, isbits := true, singleton := false, concreteSubtype := true }
  , { dt := boolTy, isbits := true, singleton := false, concreteSubtype := true }
  , { dt := stringTy, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := typeofbottomType, isbits := true, singleton := true, concreteSubtype := true }
  , { dt := datatypeType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := uniontypeType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := unionallType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := typeeqType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := typeegalType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := intersectType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := tvarType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := varargType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := symbolType, isbits := false, singleton := false, concreteSubtype := true }
  ]

def cxE : CEnv := { types := { names := cxNames, layouts := cxLayouts } }
def cxT : TEnv := { E := cxE }

/-! ## `jl_egal` on the counterexamples' values -/

theorem egal_self_long (n : Nat) (T : Types) (k : Int) :
    JuliaLean.C.egal (n + 1) T (.long k) (.long k) = pure true := by
  unfold JuliaLean.C.egal; simp [BEq.beq, Val.beq]

theorem egal_self_bits (n : Nat) (T : Types) (t : Val) (k : Int) (ht : (t == t) = true) :
    JuliaLean.C.egal (n + 1) T (.bits t k) (.bits t k) = pure true := by
  unfold JuliaLean.C.egal
  have : (Val.bits t k == Val.bits t k) = true := by
    simp only [BEq.beq, Val.beq] at ht ⊢; simp [ht]
  simp [this]

theorem egal_bool_true_false (n : Nat) (T : Types) :
    JuliaLean.C.egal (n + 1) T (boolVal true) (boolVal false) = pure false := by
  unfold JuliaLean.C.egal; rfl

theorem egal_self_datatype0 (n : Nat) (T : Types) (name : String) :
    JuliaLean.C.egal (n + 1) T (.datatype name []) (.datatype name []) = pure true := by
  unfold JuliaLean.C.egal; simp [BEq.beq, Val.beq, Val.beqList]

/-- An exception thrown by `jlThrow` is a Julia exception. -/
theorem isJuliaError_jl (exc msg : String) : isJuliaError s!"julia:{exc}: {msg}" = true := by
  simp [isJuliaError]
  exact List.prefix_append _ _

theorem jlThrow_isJuliaError {α : Type} (exc msg : String) (s : Nat) :
    ∃ e, (jlThrow exc msg : CM α).run s = .error e ∧ isJuliaError e = true :=
  ⟨_, rfl, isJuliaError_jl exc msg⟩

theorem stbind_run_ok {α β : Type} {x : CM α} {f : α → CM β} {s : Nat} {a : α} {s₁ : Nat}
    (h : x.run s = .ok (a, s₁)) : (StateT.bind x f).run s = (f a).run s₁ :=
  run_bind_ok (k := f) h

theorem stbind_run_error {α β : Type} {x : CM α} {f : α → CM β} {s : Nat} {e : String}
    (h : x.run s = .error e) : (StateT.bind x f).run s = .error e :=
  run_bind_error (k := f) h

theorem tryCatch_run {α : Type} (x : CM α) (h : String → CM α) (s : Nat) :
    (tryCatch x h : CM α).run s =
      match x.run s with
      | .ok p => .ok p
      | .error e => (h e).run s := by
  show Except.tryCatch (x s) (fun e => h e s) = match x s with | .ok p => .ok p | .error e => h e s
  cases x s <;> rfl

/-- `a && b` returns what `b` returns once `a` returned `true`. -/
theorem andM_ok {a b : CM Bool} {s s₁ s₂ : Nat} {r : Bool} (ha : a.run s = .ok (true, s₁))
    (hb : b.run s₁ = .ok (r, s₂)) : (JuliaLean.Compiler.andM a b).run s = .ok (r, s₂) := by
  unfold JuliaLean.Compiler.andM
  rw [run_bind_ok ha]
  exact hb

theorem inGamma_const_long (n : Nat) (E : CEnv) (k : Int) (s : Nat) :
    (inGamma (n + 2) E (.long k) (.const (.long k))).run s = .ok (true, s) := by
  show (JuliaLean.C.egal (n + 2) E.types (.long k) (.long k)).run s = _
  rw [egal_self_long]; rfl

theorem inGamma_const_bool (n : Nat) (E : CEnv) (b : Bool) (s : Nat) :
    (inGamma (n + 2) E (boolVal b) (.const (boolVal b))).run s = .ok (true, s) := by
  show (JuliaLean.C.egal (n + 2) E.types (.bits boolTy _) (.bits boolTy _)).run s = _
  rw [egal_self_bits _ _ _ _ (by rfl)]; rfl

end JuliaLean.Proofs.Compiler.Tfuncs
