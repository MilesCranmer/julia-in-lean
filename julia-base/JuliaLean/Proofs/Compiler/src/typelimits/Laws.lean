import JuliaLean.Proofs.Compiler.src.typelimits.Bottom

/-!
Lattice laws of `tmerge` (`Compiler/src/typelimits.jl:450-789`) that inference relies on: the
result is an upper bound of both arguments, and `tmerge(a, a) ⊑ a`.

Both are stated in the partial-correctness form of `Lattice.Returns`: they constrain the results
that the calls return, for any fuel, and say nothing about runs that end in a model failure.
-/

namespace JuliaLean.Proofs.Compiler.src.typelimits

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## Evaluating counterexamples

`jl_egal` (`JuliaLean.C.egal`) is defined by well-founded recursion, so neither `rfl` nor the
kernel reduces it. The concrete counterexamples below are evaluated by `rfl` up to each `jl_egal`
call, which is rewritten with a lemma proved by unfolding `jl_egal` once. -/

theorem eltEgal_ty_run (n : Nat) (E : CEnv) (x y : Val) (s : Nat) :
    eltEgal (n + 1) E (.ty x) (.ty y) s = JuliaLean.C.egal n E.types x y s := rfl

theorem cegal_long_long (n : Nat) (T : Types) :
    JuliaLean.C.egal (n + 1) T longType longType = pure true := by
  unfold JuliaLean.C.egal; rfl

/-- Reduce the left-hand side to weak head normal form and rewrite the call it is stuck on with
the given lemmas; repeat until `rfl` closes the goal. -/
syntax "eval_with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| eval_with [$ls,*]) =>
    `(tactic| repeat (first | rfl |
        ((conv => lhs; whnf); simp only [eltEgal_ty_run, cegal_long_long, $ls,*])))

theorem fastPath_long_long (n : Nat) (E : CEnv) (L : Lattice) (s : Nat) :
    tmergeFastPath (n + 2) E L (.ty longType) (.ty longType) s = .ok (some (.ty longType), s) := by
  eval_with []

theorem tmerge_partials_long_long (n : Nat) (E : CEnv) (p : Lattice) (s : Nat) :
    tmerge (n + 3) E (.partials p) (.ty longType) (.ty longType) s = .ok (.ty longType, s) := by
  eval_with [fastPath_long_long]

theorem tmerge_simple_long_long (n : Nat) (E : CEnv) (s : Nat) :
    tmerge (n + 3) E simpleInferenceLattice (.ty longType) (.ty longType) s = .ok (.ty longType, s) :=
  tmerge_partials_long_long n E .consts s

/-! ## Upper bound -/

/-- `tmerge(𝕃, a, b)` is an upper bound of both arguments: `a ⊑ r` and `b ⊑ r`. Losing this
means a merged state that does not cover one of the incoming states. The docstring calls
`tmerge` "a lattice join", which "need not be the least upper bound"
(`Compiler/src/abstractlattice.jl:115-122`); an upper bound it must be. -/
def TmergeUpperBound (L : Lattice) : Prop :=
  ∀ n₁ n₂ E a b s r s', (tmerge n₁ E L a b).run s = .ok (r, s') →
    Returns (sqsub n₂ E L a r) (· = true) ∧ Returns (sqsub n₂ E L b r) (· = true)

/-- The upper-bound law on `typeinf_lattice`. -/
def TmergeUpperBoundTypeinf : Prop := TmergeUpperBound typeinfLattice

/-- The upper-bound law on `JLTypeLattice`, where `⊑` is subtyping. -/
def TmergeUpperBoundJLType : Prop := TmergeUpperBound .jlType

/-- `tuplemerge(a, b)` is a supertype of both tuple types (`Compiler/src/typelimits.jl:942-1022`). -/
def TuplemergeUpper : Prop :=
  ∀ n E (a b : Val) s r s', (tuplemerge n E a b).run s = .ok (r, s') →
    Returns (issub n E a r) (· = true) ∧ Returns (issub n E b r) (· = true)

/-- `tmerge_types_slow(a, b)` is a supertype of both types (`Compiler/src/typelimits.jl:818-940`). -/
def TmergeTypesSlowUpper : Prop :=
  ∀ n E (a b : Val) s r s', (tmergeTypesSlow n E a b).run s = .ok (r, s') →
    Returns (issub n E a r) (· = true) ∧ Returns (issub n E b r) (· = true)

/-- `_limit_type_size(t, c, ...)` returns a supertype of `t` ("a type of greater size",
`Compiler/src/typelimits.jl:86-87`). The caller does not rely on it: `limit_type_size` re-checks
`t <: r` (lines 22-28, citing #36407). -/
def LimitTypeSizeInnerUpper : Prop :=
  ∀ n E tm (t c : Val) srcs (d l : Int) s r s', t.isType = true → c.isType = true →
    (limitTypeSize_ n E tm t c srcs d l).run s = .ok (r, s') → Returns (issub n E t r) (· = true)

/-- `tmerge_partial_struct(𝕃, a, b)`, when it returns a `PartialStruct`, returns an upper bound of
both arguments on `PartialsLattice(ConstsLattice())` (`Compiler/src/typelimits.jl:609-700`). -/
def TmergePartialStructUpper : Prop :=
  ∀ n₁ n₂ E a b s r s', (tmergePartialStruct n₁ E (.partials .consts) a b).run s = .ok (some r, s') →
    Returns (sqsub n₂ E (.partials .consts) a r) (· = true) ∧
    Returns (sqsub n₂ E (.partials .consts) b r) (· = true)

/-- The upper-bound law on `typeinf_lattice`, for two `LimitedAccuracy` arguments (the
`tmerge_limited` path, `Compiler/src/typelimits.jl:450-499`). -/
def TmergeUpperBoundLimited : Prop :=
  ∀ n₁ n₂ E a b s r s', a.isLimited = true → b.isLimited = true →
    (tmerge n₁ E typeinfLattice a b).run s = .ok (r, s') →
    Returns (sqsub n₂ E typeinfLattice a r) (· = true) ∧
    Returns (sqsub n₂ E typeinfLattice b r) (· = true)

/-- `LimitedAccuracy(Int, {s₁})` and `LimitedAccuracy(Int, {s₂})`, two distinct causes. -/
def limA : LElt := .limitedAccuracy (.ty longType) [1] 10
def limB : LElt := .limitedAccuracy (.ty longType) [2] 11

/-- Counterexample: for `a = LimitedAccuracy(Int, {s₁})` and `b = LimitedAccuracy(Int, {s₂})`
the types are lattice-equal, so `tmerge_limited` returns `LimitedAccuracy(Int,
merge_causes(...))`; the cause sets have the same length, so `merge_causes` returns their union
`{s₁, s₂}` (`Compiler/src/typelimits.jl:437-448`). But `⊑(::InferenceLattice)` puts
`a ⊑ LimitedAccuracy(T, c)` only when `c ⊆ a.causes` (`Compiler/src/typelattice.jl:401-418`), so the
result is below both arguments rather than above them. -/
theorem tmergeUpperBoundLimited_refuted : ¬ TmergeUpperBoundLimited := by
  intro h
  have h₁ := (h 20 20 default limA limB 0 (.limitedAccuracy (.ty longType) [1, 2] 0) 1
    rfl rfl (by rfl)).1 0 false 0 (by rfl)
  exact Bool.false_ne_true h₁

/-! ## Idempotence -/

/-- `tmerge(𝕃, a, a) ⊑ a`: merging a state with itself loses nothing. -/
def TmergeIdempotent (L : Lattice) : Prop :=
  ∀ n₁ n₂ E a s r s', (tmerge n₁ E L a a).run s = .ok (r, s') →
    Returns (sqsub n₂ E L r a) (· = true)

/-- Idempotence on `typeinf_lattice`. -/
def TmergeIdempotentTypeinf : Prop := TmergeIdempotent typeinfLattice

/-- `Conditional(1, 0, Int, Int; isdefined=true)`, the element `@isdefined x` gives for a slot
`x::Int` (`Compiler/src/abstractinterpretation.jl:3715`). -/
def condIsdefined : LElt := .conditional 1 0 (.ty longType) (.ty longType) true

theorem tmerge_condIsdefined :
    (tmerge 20 default typeinfLattice condIsdefined condIsdefined).run 0 = .ok (.ty boolTy, 0) := by
  eval_with [tmerge_simple_long_long]

theorem sqsub_bool_condIsdefined :
    (sqsub 20 default typeinfLattice (.ty boolTy) condIsdefined).run 0 = .ok (false, 0) := by
  eval_with []

/-- Counterexample: `tmerge(typeinf_lattice, c, c)` for the `@isdefined` conditional `c` returns
`Bool`. `tmerge(::ConditionalsLattice)` (`Compiler/src/typelimits.jl:509-547`) merges the then and
else types, finds them equal and falls through to `Bool`, and even when they differ it rebuilds
the `Conditional` without `isdefined`. `Bool ⋢ c`. -/
theorem tmergeIdempotentTypeinf_refuted : ¬ TmergeIdempotentTypeinf := by
  intro h
  have h₁ := h 20 20 default condIsdefined 0 (.ty boolTy) 0 tmerge_condIsdefined 0 false 0
    sqsub_bool_condIsdefined
  exact Bool.false_ne_true h₁

end JuliaLean.Proofs.Compiler.src.typelimits
