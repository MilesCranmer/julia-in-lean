import JuliaLean.Proofs.base.array.common.index_bounds

namespace JuliaLean.MemSafety.G5

/-- Results of the symbol and task-pool branches that can reach
`_nthreads_in_pool`; foreign and invalid requests return before the table load. -/
inductive RuntimePoolRequest where
  | interactive
  | default
  | foreign
  | invalid
  deriving DecidableEq

/-- `_sym_to_tpid`, `threadpoolsize`, `threadpooltids`, `multiq_size`, and the
`@spawn` branch, followed by the one-based `tpid + 1` at line 64. -/
def runtimePoolIndex : RuntimePoolRequest → Option Nat
  | .interactive => some 1
  | .default => some 2
  | .foreign | .invalid => none

/-- Scalar `cglobal` loads at lines 47, 63, 124, and 169 have one cell. The
pool-count pointer loaded at line 63 names the runtime's two-entry table. -/
def ThreadRuntimeAccessesInBounds : Prop :=
  OneBasedInBounds 1 1 ∧
  ∀ request index, runtimePoolIndex request = some index → OneBasedInBounds 2 index

theorem threadRuntimeAccessesInBounds : ThreadRuntimeAccessesInBounds := by
  constructor
  · simp [OneBasedInBounds]
  · intro request index h
    cases request <;> simp [runtimePoolIndex] at h
    all_goals subst index <;> simp [OneBasedInBounds]


/-! ## `base/threadingconstructs.jl` -/

/-- The valid linear indices of the result passed from a threaded comprehension
to `_comprehension_result`, `base/threadingconstructs.jl:356-370`. -/
structure ComprehensionResult where
  indices : List (JInt .i64)

/-- The first unchecked read reached by the widening path. This includes the
empty-result and concrete-eltype branches at lines 357-362, the wrapping
`firstindex(result) + 1`, and the `for j in i:lastindex(result)` emptiness test
at lines 368-370. -/
def comprehensionWidenFirstRead (result : ComprehensionResult) (concreteEltype : Bool) :
    Option (JInt .i64) :=
  match result.indices with
  | [] => none
  | first :: rest =>
    if concreteEltype then none
    else
      let last := rest.getLastD first
      let i := first + JInt.lit .i64 1
      if i.val ≤ last.val then some i else none

/-- Every read selected by the public threaded-comprehension widening path is
an index of the result array. -/
def ComprehensionWidenAccessesInBounds : Prop :=
  ∀ result concreteEltype,
    match comprehensionWidenFirstRead result concreteEltype with
    | none => True
    | some i => i.val ∈ result.indices.map (·.val)

theorem comprehensionWidenAccessesInBounds_refuted : ¬ ComprehensionWidenAccessesInBounds := by
  intro h
  have hwrap : (JInt.typemax .i64 + JInt.lit .i64 1).val = IntTy.i64.min := by decide
  have hmax : (JInt.typemax .i64).val = IntTy.i64.max := by decide
  have bad := h ⟨[JInt.typemax .i64]⟩ false
  simp [comprehensionWidenFirstRead, hwrap, hmax, IntTy.min, IntTy.max,
    IntTy.signed, IntTy.bits] at bad


end JuliaLean.MemSafety.G5
