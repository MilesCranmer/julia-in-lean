import JuliaLean.base.missing
import JuliaLean.base.iterators
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.missing.memory_safety
open JuliaLean

abbrev IndexFilter (Index : Type) :=
  JuliaLean.base.iterators.Filter (Index → Bool) (List Index)

-- A complete traversal of the parent's index iterator supplies the predicate inputs.
def filterIndexRun {Index : Type} (indices : List Index) (state : Option Nat) :
    JuliaLean.base.iterators.Exec JlError Unit (Option (Index × Nat)) :=
  fun world => some (.ok ((indices[state.getD 0]?).map
    (fun index => (index, state.getD 0 + 1))), world)

def checkedFilterTest {Index : Type} [DecidableEq Index]
    (indices : List Index) (predicate : Index → Bool) (index : Index) :
    JuliaLean.base.iterators.Exec JlError Unit Bool :=
  fun world => if index ∈ indices then some (.ok (predicate index), world)
    else some (.error .boundsError, world)

def filterIterationSafe {Index : Type} [DecidableEq Index]
    (filter : IndexFilter Index) : Prop :=
  ∀ state, JuliaLean.base.iterators.filterScan filterIndexRun
    (fun pair world => some (.ok pair, world))
    (checkedFilterTest filter.itr) (fun _ => true) Prod.mk filter state () ≠
      some (.error .boundsError, ())

theorem filterIterationSafe_proven {Index : Type} [DecidableEq Index]
    (filter : IndexFilter Index) : filterIterationSafe filter := by
  have safe : ∀ state world, JuliaLean.base.iterators.filterScan filterIndexRun
      (fun pair world => some (.ok pair, world))
      (checkedFilterTest filter.itr) (fun _ => true) Prod.mk filter state world ≠
        some (.error JlError.boundsError, ()) := by
    apply JuliaLean.base.iterators.filterScan.fixpoint_induct filterIndexRun
      (fun pair world => some (.ok pair, world))
      (checkedFilterTest filter.itr) (fun _ => true) Prod.mk filter
      (fun loop => ∀ state world, loop state world ≠ some (.error JlError.boundsError, ()))
    · refine Lean.Order.admissible_pi_apply
        (fun (_state : Option Nat)
          (action : Unit → Option (Except JlError (Option (Index × Nat)) × Unit)) =>
            ∀ world, action world = some (.error JlError.boundsError, ()) → False) (fun state => ?_)
      exact Lean.Order.admissible_pi_apply
        (fun (_world : Unit) (result : Option (Except JlError (Option (Index × Nat)) × Unit)) =>
          result = some (.error JlError.boundsError, ()) → False)
        (fun world => Lean.Order.Option.admissible_eq_some False
          ((Except.error JlError.boundsError : Except JlError (Option (Index × Nat))), ()))
    · intro loop ih state world bad
      cases world
      cases hx : filter.itr[state.getD 0]? with
      | none => simpa [filterIndexRun, hx] using bad
      | some index =>
        have mem := List.mem_of_getElem? hx
        cases hp : filter.flt index with
        | false =>
          exact ih (some (state.getD 0 + 1)) ()
            (by simpa [filterIndexRun, hx, checkedFilterTest, mem, hp] using bad)
        | true => simpa [filterIndexRun, hx, checkedFilterTest, mem, hp] using bad
  exact fun state => safe state ()

-- The constructors used below are the installed Iterators.filter source model.
def SkipMissingEachindexInBounds : Prop :=
  ∀ (α : Type) (parent : List (Option α)),
    filterIterationSafe (JuliaLean.base.missing.eachindexSkipMissingFilter
      JuliaLean.base.iterators.sourceMethod576
      (fun values => List.range values.length)
      (fun values index => (values[index]?).join) Option.isNone
      (JuliaLean.base.missing.skipmissing parent))

def SkipMissingKeysInBounds : Prop :=
  ∀ (Index α : Type) [DecidableEq Index]
    (keys : List Index) (getindex : Unit → Index → Option α),
    filterIterationSafe (JuliaLean.base.missing.keysSkipMissingFilter
      JuliaLean.base.iterators.sourceMethod576 (fun _ => keys)
      getindex Option.isNone (JuliaLean.base.missing.skipmissing ()))

theorem skipMissingEachindexInBounds : SkipMissingEachindexInBounds := by
  unfold SkipMissingEachindexInBounds
  intro α parent
  exact filterIterationSafe_proven _

theorem skipMissingKeysInBounds : SkipMissingKeysInBounds := by
  unfold SkipMissingKeysInBounds
  intro Index α _ keys getindex
  exact filterIterationSafe_proven _

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-missing-skipmissing-eachindex", juliaFile := "base/missing.jl"
    juliaFns := ["eachindex(::SkipMissing)"]
    statement := "SkipMissing evaluates its filter only at indices computed by the wrapped IndexLinear array's eachindex."
    source := "base/missing.jl:253-254; base/iterators.jl:578-592"
    status := .proven, prop := ``SkipMissingEachindexInBounds
    thm := some ``skipMissingEachindexInBounds },
  { id := "memsafety-missing-skipmissing-keys", juliaFile := "base/missing.jl"
    juliaFns := ["keys(::SkipMissing)"]
    statement := "SkipMissing evaluates its keys filter only at Cartesian keys computed from the wrapped array's axes."
    source := "base/missing.jl:255-256; base/iterators.jl:578-592"
    status := .proven, prop := ``SkipMissingKeysInBounds
    thm := some ``skipMissingKeysInBounds }
]
end JuliaLean.Proofs.base.missing.memory_safety
