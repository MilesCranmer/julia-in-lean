import JuliaLean.base.threadingconstructs
import JuliaLean.base.range
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.threadingconstructs

open JuliaLean JuliaLean.base.threadingconstructs

private def readIndex (axis : JuliaLean.base.range.UnitRange JInt64) (index : JInt64) :
    JuliaLean.base.locks_mt.M JlError (List JInt64) Unit := fun reads =>
  if axis.start.val ≤ index.val ∧ index.val ≤ axis.stop.val then
    some (.ok ((), reads ++ [index]))
  else some (.error (.boundsError, reads ++ [index]))

private def unitComprehension : Comprehension JlError (List JInt64)
    (JuliaLean.base.range.UnitRange JInt64) Unit Bool where
  isEmpty := fun axis => pure (decide (axis.stop.val < axis.start.val))
  promoteTypejoinUnion := fun _ => pure true
  elementType := fun _ => pure false
  sameType := fun a b => a == b
  similar := fun axis _ => pure axis
  concreteType := id
  first := fun axis => readIndex axis axis.start
  firstIndex := fun axis => pure axis.start
  lastIndex := fun axis => pure axis.stop
  getInbounds := readIndex
  typeOf := fun _ => true
  isa := fun _ tag => tag
  promoteTypejoin := fun a b => pure (a || b)
  copyTo := fun out _ => pure out

def ComprehensionWidenAccessesInBounds : Prop :=
  ∀ (axis : JuliaLean.base.range.UnitRange JInt64) (tag : Bool),
    match comprehensionResult unitComprehension axis tag [] with
    | none => True
    | some (.ok (_, reads)) | some (.error (_, reads)) =>
      ∀ index ∈ reads, axis.start.val ≤ index.val ∧ index.val ≤ axis.stop.val

private def extremeAxis : JuliaLean.base.range.UnitRange JInt64 :=
  ⟨JInt.typemax .i64, JInt.typemax .i64⟩

private theorem widening_reaches_bad_index :
    comprehensionWidenedEltype unitComprehension extremeAxis true (JInt.typemin .i64)
      [JInt.typemax .i64] =
        some (.error (.boundsError, [JInt.typemax .i64, JInt.typemin .i64])) := by
  unfold comprehensionWidenedEltype
  rw [JuliaLean.base.locks_mt.loop.eq_def]
  dsimp only [unitComprehension, bind, pure]
  rw [JuliaLean.base.locks_mt.loop.eq_def]
  rfl

private theorem result_reaches_bad_index :
    comprehensionResult unitComprehension extremeAxis false [] =
      some (.error (.boundsError, [JInt.typemax .i64, JInt.typemin .i64])) := by
  have he : unitComprehension.isEmpty extremeAxis =
      (pure false : JuliaLean.base.locks_mt.M JlError (List JInt64) Bool) := rfl
  have hf : unitComprehension.first extremeAxis =
      (fun reads => some (.ok ((), reads ++ [JInt.typemax .i64]))) := rfl
  have hi : unitComprehension.firstIndex extremeAxis =
      (pure (JInt.typemax .i64) : JuliaLean.base.locks_mt.M JlError (List JInt64) JInt64) := rfl
  have hc : unitComprehension.concreteType false = false := rfl
  have ht : unitComprehension.typeOf () = true := rfl
  simp only [comprehensionResult, he, hf, hi, hc, ht, bind, pure,
    Bool.false_eq_true, ↓reduceIte]
  have hw : JInt.typemax .i64 + int 1 = JInt.typemin .i64 := by decide
  rw [hw, List.nil_append, widening_reaches_bad_index]

theorem comprehensionWidenAccessesInBounds_refuted : ¬ ComprehensionWidenAccessesInBounds := by
  intro h
  have bad := h extremeAxis false
  rw [result_reaches_bad_index] at bad
  have hr := bad (JInt.typemin .i64) (by simp)
  have hn : ¬ (JInt.typemax .i64).val ≤ (JInt.typemin .i64).val := by decide
  exact hn hr.1

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-threads-comprehension-firstindex-overflow"
    juliaFile := "base/threadingconstructs.jl"
    juliaFns := ["Threads.@threads comprehension", "_comprehension_result", "_comprehension_widened_eltype"]
    statement := "The threaded-comprehension widening scan reads only an index of its result array."
    source := "AbstractArray index invariant; base/threadingconstructs.jl:356-370,391-421"
    status := .refuted, prop := ``ComprehensionWidenAccessesInBounds
    thm := some ``comprehensionWidenAccessesInBounds_refuted
    issue := "none found (queries: threaded comprehension firstindex overflow; _comprehension_widened_eltype; typemax firstindex @threads; PRs same)"
    notes := "The installed comprehensionResult and comprehensionWidenedEltype methods record an unchecked read at typemin(Int) for a singleton typemax(Int) result axis. The callback records both the initial valid read and the widening scan's invalid read. Julia master reproduces; Julia 1.13.2 has no threaded comprehensions." }
]

end JuliaLean.Proofs.base.threadingconstructs
