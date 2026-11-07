import JuliaLean.base.Terminals
import JuliaLean.Proofs.base.terminfo.retained
import JuliaLean.Proofs.base.coreio.showSupport


namespace JuliaLean.ShowCov

open Terminals TermInfo

/-- `print`/`println` without a stream write to `stdout`, `println` appends
`"\n"`, `println(io)` writes `"\n"`; `DevNull` accepts every write (returning
the byte count, which must fit an `Int`), is empty, and `wait_close` blocks;
the `CoreSTDOUT`/`CoreSTDERR`/`DevNull` read side is at end of file
(`base/coreio.jl:6-40`). -/
def CoreIOBehaviour : Prop :=
  ∀ (xs : List String) (io : Stream) (b : UInt8) (n : Nat) (bytes : List UInt8) (nb : Int),
    print0 xs = xs.map (Stream.stdout, ·) ∧
    println0 xs = xs.map (Stream.stdout, ·) ++ [(.stdout, "\n")] ∧
    printlnIO io = [(io, "\n")] ∧
    writeDevNull b = 1 ∧
    (n ≤ int64Max → unsafeWriteDevNull n = .ok n) ∧
    (n > int64Max → unsafeWriteDevNull n = .error (.inexactError "Int64")) ∧
    bytesavailableDevNull = 0 ∧ closewriteDevNull = .returns ∧ closeDevNull = .returns ∧
    waitCloseDevNull = .blocksForever ∧ writeCore bytes = bytes ∧
    readCore = .error .eofError ∧ isopenCore = true ∧ isreadableCore = false ∧
    iswritableCore = true ∧ flushCore = () ∧ eofCore = true ∧ waitReadnbCore nb = ()

theorem coreIOBehaviour_proven : CoreIOBehaviour := by
  intro xs io b n bytes nb
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [println0, printIO]
  · intro h; simp [unsafeWriteDevNull, h]
  · intro h
    have : ¬ n ≤ int64Max := by omega
    simp [unsafeWriteDevNull, this]

/-! ## `base/terminfo.jl` -/

end JuliaLean.ShowCov
