import JuliaLean.base.iterators
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.iterators.ZipSharedStatefulCompletion

open JuliaLean JuliaLean.base.iterators

/-- Two publicly constructed Stateful objects have separate cells. The inner zip
uses the same handle twice; the outer zip's first handle is independent. -/
structure Cell where
  input : List JInt64 := []
  pending : Option (JInt64 × Nat) := none

structure Heap where
  cells : Nat → Cell := fun _ => {}
  next : Nat := 0

private def writeCell (heap : Heap) (handle : Nat) (cell : Cell) : Heap :=
  { heap with cells := fun address => if address = handle then cell else heap.cells address }

abbrev M := Exec IteratorError Heap

/-- Concrete field storage for Stateful{Vector{Int64},Any}. The source constructor
establishes every handle used below; the cache type Any accepts each iterator result. -/
def statefulOps : StatefulOps IteratorError Heap Nat (List JInt64)
    (JInt64 × Nat) Unit where
  allocate input _ pending := fun heap =>
    some (.ok heap.next, { writeCell heap heap.next ⟨input, pending⟩ with next := heap.next + 1 })
  iterator handle := fun heap => some (.ok (heap.cells handle).input, heap)
  pending handle := fun heap => some (.ok (heap.cells handle).pending, heap)
  declaredCacheType _ := pure ()
  setIterator handle input := fun heap =>
    some (.ok (), writeCell heap handle { heap.cells handle with input := input })
  writeCacheRaw handle pending := fun heap =>
    some (.ok (), writeCell heap handle { heap.cells handle with pending := pending })
  assertCache pending _ := pure pending

/-- The existing finite vector iterator binding supplies all input elements and states. -/
def vectorRun (input : List JInt64) (state : Option Nat) : M (Option (JInt64 × Nat)) :=
  fun heap => some (((listIterator input).run state).mapError IteratorError.julia, heap)

def construct (input : List JInt64) : M Nat :=
  statefulAny statefulOps (fun input => vectorRun input none) () input

def runStateful (handle : Nat) (_ : Option Unit) : M (Option (JInt64 × Unit)) :=
  iterateStateful statefulOps (fun input state => vectorRun input (some state)) .eofError handle

def statefulCalls : ZipCalls M (fun _ : Unit => Nat)
    (fun _ => JInt64) (fun _ => Unit) where
  run _ := runStateful
  done _ := statefulDone statefulOps

abbrev PairValues := TupleVals (fun _ : Unit => JInt64) [(), ()]
abbrev PairStates := TupleVals (fun _ : Unit => Unit) [(), ()]
abbrev Inner := Zip (TupleVals (fun _ : Unit => Nat) [(), ()])

def sharedPair (handle : Nat) : Inner := zipModel (.cons handle (.cons handle .nil))

def OuterInput : Bool → Type
  | false => Nat
  | true => Inner

def OuterValue : Bool → Type
  | false => JInt64
  | true => PairValues

def OuterState : Bool → Type
  | false => Unit
  | true => PairStates

def outerCalls : ZipCalls M OuterInput OuterValue OuterState where
  run key := match key with
    | false => runStateful
    | true => fun inner state => match state with
      | none => zipStart statefulCalls inner
      | some state => zipState statefulCalls inner state
  done key := match key with
    | false => statefulDone statefulOps
    | true => fun inner state => match state with
      | none => zipIsdoneStart statefulCalls inner
      | some state => zipIsdoneState statefulCalls inner state

/-- Public call sequence: construct two Stateful objects, try one outer zip row,
then inspect the independent first object's next value. No custom iterator is used. -/
def attempt (left right : List JInt64) : M (Bool × Option JInt64) := do
  let a ← construct left
  let s ← construct right
  let outer : Zip (TupleVals OuterInput [false, true]) :=
    zipModel (.cons a (.cons (sharedPair s) .nil))
  let row ← zipStart outerCalls outer
  let next ← peekStateful statefulOps a ()
  pure (row.isNone, match next with | .inl value => some value | .inr _ => none)

def observation (left right : List JInt64) : Option (Except IteratorError (Bool × Option JInt64)) :=
  (attempt left right {}).map Prod.fst

/-- If a zip attempt yields no row, an independent Stateful input does not
advance. This is the no-advance promise in base/iterators.jl:347-348, restricted
to two valid finite inputs and one built-in nested zip composition. -/
def NoAdvanceOnCompletion : Prop :=
  ∀ (first : JInt64) (tail right : List JInt64) (next : Option JInt64),
    observation (first :: tail) right = some (.ok (true, next)) → next = some first

theorem singleton_shared_inner_finishes :
    observation [JInt.lit .i64 10, JInt.lit .i64 20] [JInt.lit .i64 1] =
      some (.ok (true, some (JInt.lit .i64 20))) := by
  decide

theorem noAdvanceOnCompletion_refuted : ¬ NoAdvanceOnCompletion := by
  intro promise
  have wrong := promise (JInt.lit .i64 10) [JInt.lit .i64 20]
    [JInt.lit .i64 1] (some (JInt.lit .i64 20)) singleton_shared_inner_finishes
  have different : (some (JInt.lit .i64 20) : Option JInt64) ≠ some (JInt.lit .i64 10) := by
    decide
  exact different wrong

open JuliaLean.Registry

def entries : List Entry := [
  { id := "iterators-zip-shared-stateful-completion"
    juliaFile := "base/iterators.jl"
    juliaFns := ["iterate(::Zip)", "isdone(::Zip)", "_zip_iterate_all", "_zip_iterate_rest"]
    statement := "When a zip attempt ends without a row, an independent Stateful input retains its next value, including when another input is a nested zip of a shared Stateful object."
    source := "base/iterators.jl:347-348 (zip no-advance promise)"
    status := .refuted
    prop := ``NoAdvanceOnCompletion
    thm := some ``noAdvanceOnCompletion_refuted
    issue := "Related: JuliaLang/julia#47790 (shared Stateful zip length); no exact nested completion report found."
    notes := "The outer zip's isdone scan sees false for the shared inner zip before either inner call runs. It advances the independent first input, then the inner zip consumes its sole shared element and ends without a row." }
]

end JuliaLean.Proofs.base.iterators.ZipSharedStatefulCompletion
