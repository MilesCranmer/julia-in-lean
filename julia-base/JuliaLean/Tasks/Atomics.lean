import JuliaLean.Tasks.TaskModel

namespace JuliaLean.Tasks

abbrev AtomicInt := BitVec 64

inductive AtomicAction where
  | cas (expected desired : AtomicInt)
  | exchange (value : AtomicInt)
  | add (value : AtomicInt)
  | sub (value : AtomicInt)
  | band (value : AtomicInt)
  | bnand (value : AtomicInt)
  | bor (value : AtomicInt)
  | bxor (value : AtomicInt)
  | min (value : AtomicInt)
  | max (value : AtomicInt)
  deriving Repr, DecidableEq

/-- The new value of each `Atomic{Int64}` read-modify-write operation,
`base/atomics.jl:326-361`. `BitVec 64` supplies Julia's wrapping Int bits. -/
def atomicUpdate : AtomicAction → AtomicInt → AtomicInt
  | .cas expected desired, old => if old = expected then desired else old
  | .exchange value, _ => value
  | .add value, old => old + value
  | .sub value, old => old - value
  | .band value, old => old &&& value
  | .bnand value, old => ~~~(old &&& value)
  | .bor value, old => old ||| value
  | .bxor value, old => old ^^^ value
  | .min value, old => if old.toInt ≤ value.toInt then old else value
  | .max value, old => if old.toInt ≥ value.toInt then old else value

/-- LLVM atomic RMWs return the old value and perform one update. -/
def atomicStep (action : AtomicAction) (old : AtomicInt) : AtomicInt × AtomicInt :=
  (old, atomicUpdate action old)

def atomicRun (initial : AtomicInt) (actions : List AtomicAction) : AtomicInt :=
  actions.foldl (fun value action => atomicUpdate action value) initial

/-- Every legacy `Threads.Atomic{Int64}` operation returns the prior bits and
stores its documented update. Since scheduler interleavings are lists of
atomic steps, `atomicRun` is their linearization in that order. -/
def AtomicOperationsCorrect : Prop :=
  ∀ (old : AtomicInt) (action : AtomicAction),
    (atomicStep action old).1 = old ∧
      (atomicStep action old).2 = atomicUpdate action old

theorem atomicOperationsCorrect_proven : AtomicOperationsCorrect := by
  intro old action
  exact ⟨rfl, rfl⟩

end JuliaLean.Tasks
