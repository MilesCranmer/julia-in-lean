import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.array.LegacyCartesianFilter
open JuliaLean JuliaLean.base.array JuliaLean.Registry

/-- A zero-element Cartesian array returns its empty selection without evaluating
or inferring a predicate result. The Cartesian branch uses the installed map! body. -/
def EmptyCartesianFilter : Prop :=
  ∀ (A Mask E PredicateResult Result Indices : Type)
    (similarBool : A → Except Error Mask)
    (eachDest : Mask → Except Error (List Nat)) (eachSource : A → Except Error (List Nat))
    (read : A → Nat → Except Error E) (write : Mask → Nat → Bool → Except Error Unit)
    (getMask : A → Mask → Except Error Result)
    (length : A → Except Error I) (allocateIndices : I → Except Error Indices)
    (eachIndex : A → Except Error (List Nat)) (setIndex : Indices → Nat → I → Except Error Unit)
    (resize : Indices → I → Except Error Unit) (getIndices : A → Indices → Except Error Result)
    (empty : Indices → Except Error Unit) (sizehint : Indices → I → Except Error Unit)
    (predicate : E → Except Error PredicateResult) (assertBool : PredicateResult → Except Error Bool)
    (array : A) (mask : Mask) (result : Result),
    similarBool array = .ok mask → eachDest mask = .ok [] → eachSource array = .ok [] →
    getMask array mask = .ok result →
    filterAbstractArray (fun _ => pure false) similarBool
      (fun test dest src => JuliaLean.base.abstractarray.mapInplaceOne eachDest eachSource
        (fun ds ss => pure (ds.zip ss)) read write test dest src)
      getMask length allocateIndices eachIndex setIndex read
      (fun value => do assertBool (← predicate value)) resize getIndices empty sizehint array = .ok result

theorem emptyCartesianFilter_proven : EmptyCartesianFilter := by
  intro A Mask E PredicateResult Result Indices similarBool eachDest eachSource read write getMask
    length allocateIndices eachIndex setIndex resize getIndices empty sizehint predicate assertBool
    array mask result similar destEmpty sourceEmpty selected
  simp [filterAbstractArray, JuliaLean.base.abstractarray.mapInplaceOne,
    similar, destEmpty, sourceEmpty, selected, bind, Except.bind, pure, Except.pure]

def entries : List Entry := [
  { id := "multidimcov-filter-cartesian-empty", juliaFile := "base/array.jl"
    juliaFns := ["filter(f, a::AbstractArray)"]
    statement := "Filtering an empty Cartesian-indexed array returns its empty selection without evaluating the predicate, even when the predicate's return type is not inferred to be Bool."
    source := "base/array.jl:3027-3028; base/abstractarray.jl:3482-3488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``EmptyCartesianFilter, thm := some ``emptyCartesianFilter_proven
    notes := "The pinned source replaces the allocating map and result-type assertion with map!(x -> f(x)::Bool, similar(a, Bool), a). The native proof composes that map! implementation. The historical bug still reproduces on release 1.13.3 but not nightly 1.15.0-DEV.307." }
]

end JuliaLean.Proofs.base.array.LegacyCartesianFilter
