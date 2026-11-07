import JuliaLean.base.experimental
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.experimental
open JuliaLean JuliaLean.base.experimental JuliaLean.base.expr JuliaLean.Registry

/-- Wrapping an array as Const does not change its size or axes. -/
def ConstShapeContract : Prop :=
  ∀ (Element Array Size Axes : Type) (rank : Nat) (size : Array → Size) (axes : Array → Axes)
    (storage : Array),
    constSize size (Const.mk (Element := Element) (Rank := rank) storage) = size storage ∧
      constAxes axes (Const.mk (Element := Element) (Rank := rank) storage) = axes storage

theorem constShapeContract_proven : ConstShapeContract := by
  intro Element Array Size Axes rank size axes storage
  exact ⟨rfl, rfl⟩

/-- A failed bounds check prevents a Const element read. -/
def ConstBoundsContract : Prop :=
  ∀ (Element Array Ref Value Size Axes Error : Type) (rank : Nat)
    (ops : ConstArrayOps Array Ref Value Size Axes Error) (array : Const Element rank Array),
    (∀ (index : JInt64) (err : Error), ops.checkBoundsOne array.a index = .error err →
      constGetIndex ops array index = .error err) ∧
    (∀ (i1 i2 : JInt64) (rest : List JInt64) (err : Error),
      ops.checkBoundsMany array.a (i1 :: i2 :: rest) = .error err →
      constGetIndexManyNative ops array i1 i2 rest = .error err)

theorem constBoundsContract_proven : ConstBoundsContract := by
  intro Element Array Ref Value Size Axes Error rank ops array
  constructor
  · intro index err failed
    simp [constGetIndex, failed, bind, Except.bind]
  · intro i1 i2 rest err failed
    simp [constGetIndexManyNative, failed, bind, Except.bind]

/-- Tasks created without timing collection have neither running nor wall timing data. -/
def MetricsDisabledContract : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m] (Task : Type) (ops : TaskTimeOps m Task)
    (task : Task), ops.metricsEnabled task = false →
    taskRunningTimeNs ops (some task) = pure none ∧ taskWallTimeNs ops (some task) = pure none

theorem metricsDisabledContract_proven : MetricsDisabledContract := by
  intro m instMonad instLawful Task ops task disabled
  simp [taskRunningTimeNs, taskWallTimeNs, disabled]

/-- A task that has never entered the run queue has zero runnable time. -/
def NeverEnqueuedContract : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m] (Task : Type) (ops : TaskTimeOps m Task)
    (task : Task), ops.metricsEnabled task = true → (ops.firstEnqueuedAt task).val = 0 →
    taskWallTimeNs ops (some task) = pure (some (JInt.lit .u64 0))

theorem neverEnqueuedContract_proven : NeverEnqueuedContract := by
  intro m instMonad instLawful Task ops task enabled start
  simp [taskWallTimeNs, enabled, start]

/-- Entrypoints are not registered when Julia is not generating output. -/
def EntrypointContract : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m]
    (Function FunctionType ArgumentType Signature : Type)
    (ops : EntrypointOps m Function FunctionType ArgumentType Signature) (signature : Signature),
    ops.generatingOutput = pure false → entrypointType ops signature = pure ()

theorem entrypointContract_proven : EntrypointContract := by
  intro m instMonad instLawful Function FunctionType ArgumentType Signature ops signature ordinary
  simp [entrypointType, ordinary]

/-- Hint emission does nothing while the recursion guard is active. -/
def HintRecursionContract : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m]
    (ExceptionType Handler IO Exception Argument : Type) [MonadExceptOf Exception m]
    (ops : ErrorHintOps m ExceptionType Handler IO Exception Argument)
    (io : IO) (ex : Exception) (args : List Argument),
    ops.hintsDisabled = pure true → showErrorHints ops io ex args = pure ()

theorem hintRecursionContract_proven : HintRecursionContract := by
  intro m instMonad instLawful ExceptionType Handler IO Exception Argument instExcept ops io ex args disabled
  simp [showErrorHints, disabled]

/-- A disabled native object cache is not pruned or copied. -/
def DisabledCacheContract : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m] (Directory Age Pointer Error : Type)
    [MonadExceptOf Error m] (ops : ObjectCacheOps m Directory Age Pointer Error)
    (directory : Directory) (age : Option Age),
    ops.cacheEnabled = pure (JInt.lit .i32 0) → pruneObjCache ops directory age = pure none

theorem disabledCacheContract_proven : DisabledCacheContract := by
  intro m instMonad instLawful Directory Age Pointer Error instExcept ops directory age disabled
  simp [pruneObjCache, disabled, JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]


/-- The documented maximum-method settings are exactly the values accepted by the macro. -/
def MaxMethodsRangeContract : Prop :=
  ∀ (L : Type) (lo : LeafOps L) (n : JInt64),
    (∃ expansion, maxMethodsMacro lo n = .ok expansion) ↔ 1 ≤ n.val ∧ n.val ≤ 4

theorem maxMethodsRangeContract_proven : MaxMethodsRangeContract := by
  intro L lo n
  by_cases allowed : 1 ≤ n.val ∧ n.val ≤ 4
  · simp [maxMethodsMacro, allowed, pure, Except.pure]
  · simp [maxMethodsMacro, allowed, bind, throw, throwThe, MonadExceptOf.throw, Except.bind]

/-- Selective using statements are explicitly unsupported by reexport. -/
def ReexportColonContract : Prop :=
  ∀ (L : Type) (a : MacroAtoms L) (paths : List (Value L)),
    paths ≠ [] → paths.any (fun path => isexpr path ":") = true →
    reexportMacro a (.expr "using" paths) =
      .error (.errorException "@reexport does not support `using Module: names` syntax")

theorem reexportColonContract_proven : ReexportColonContract := by
  intro L a paths nonempty colon
  simp [reexportMacro, nonempty, colon, bind, throw, throwThe, MonadExceptOf.throw, Except.bind]

def macroEntries : List Entry := [
  { id := "experimental-max-methods-range", juliaFile := "base/experimental.jl"
    juliaFns := ["@max_methods", "@compiler_options"]
    statement := "The module-level max_methods macro accepts exactly integer values 1 through 4."
    source := "base/experimental.jl:162-183", status := .proven
    prop := ``MaxMethodsRangeContract, thm := some ``maxMethodsRangeContract_proven },
  { id := "experimental-reexport-colon", juliaFile := "base/experimental.jl"
    juliaFns := ["@reexport"]
    statement := "Reexport rejects selective using statements with its documented diagnostic."
    source := "base/experimental.jl:751-770", status := .proven
    prop := ``ReexportColonContract, thm := some ``reexportColonContract_proven }
]


def entries : List Entry := [
  { id := "experimental-const-shape", juliaFile := "base/experimental.jl"
    juliaFns := ["IndexStyle(::Type{<:Const})", "size(::Const)", "axes(::Const)"]
    statement := "Const wrappers preserve the size and axes of their underlying array."
    source := "base/experimental.jl:29-31", status := .proven
    prop := ``ConstShapeContract, thm := some ``constShapeContract_proven },
  { id := "experimental-const-bounds", juliaFile := "base/experimental.jl"
    juliaFns := ["getindex(::Const, ::Int)", "getindex(::Const, ::Int, ::Int, ::Int...)"]
    statement := "Const element indexing propagates a failed bounds check before reading storage."
    source := "base/experimental.jl:32-41", status := .proven
    prop := ``ConstBoundsContract, thm := some ``constBoundsContract_proven },
  { id := "experimental-metrics-disabled", juliaFile := "base/experimental.jl"
    juliaFns := ["task_metrics", "task_running_time_ns", "task_wall_time_ns"]
    statement := "Tasks without timing collection return nothing for running and runnable time."
    source := "base/experimental.jl:630-662", status := .proven
    prop := ``MetricsDisabledContract, thm := some ``metricsDisabledContract_proven },
  { id := "experimental-never-enqueued", juliaFile := "base/experimental.jl"
    juliaFns := ["task_wall_time_ns"]
    statement := "A task that has never entered the run queue has zero runnable time."
    source := "base/experimental.jl:655-662", status := .proven
    prop := ``NeverEnqueuedContract, thm := some ``neverEnqueuedContract_proven },
  { id := "experimental-entrypoint-output", juliaFile := "base/experimental.jl"
    juliaFns := ["entrypoint"]
    statement := "Entrypoints are registered only when Julia is generating output."
    source := "base/experimental.jl:573-579", status := .proven
    prop := ``EntrypointContract, thm := some ``entrypointContract_proven },
  { id := "experimental-hint-recursion", juliaFile := "base/experimental.jl"
    juliaFns := ["show_error_hints", "register_error_hint"]
    statement := "The hint recursion guard suppresses hint execution during hint-failure reporting."
    source := "base/experimental.jl:354-374", status := .proven
    prop := ``HintRecursionContract, thm := some ``hintRecursionContract_proven },
  { id := "experimental-cache-disabled", juliaFile := "base/experimental.jl"
    juliaFns := ["prune_objcache"]
    statement := "A disabled object cache returns nothing without pruning or copying the cache."
    source := "base/experimental.jl:853-861", status := .proven
    prop := ``DisabledCacheContract, thm := some ``disabledCacheContract_proven }
] ++ macroEntries

end JuliaLean.Proofs.base.experimental
