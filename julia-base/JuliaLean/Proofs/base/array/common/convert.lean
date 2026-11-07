import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials


/-!
# Properties of `base/array.jl`

These statements refer only to the source-mirrored definitions in `JuliaLean.base.array`.
The search specifications use the ordered finite sequence returned by a collection's `pairs`.
Layout fields and their well-formedness are the runtime invariants of concrete Julia types.
-/

local instance JuliaLean.Proofs.base.array.layoutAllocationProjection :
    Coe JuliaLean.base.array.MemoryLayoutMetadata (Option JuliaLean.base.array.MemoryLayout) :=
  ⟨fun layout => layout.allocation⟩

local instance JuliaLean.Proofs.base.array.nativeAllocationProjection :
    Coe JuliaLean.src.genericmemory_c.DictLayout JuliaLean.base.array.MemoryLayout :=
  ⟨JuliaLean.base.array.allocationSummary⟩

local instance JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection {Tag : Type} :
    Coe (Tag → JuliaLean.base.array.MemoryLayoutMetadata)
      (Tag → Option JuliaLean.base.array.MemoryLayout) :=
  ⟨fun layout tag => (layout tag).allocation⟩

local instance JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection {Tag : Type} :
    Coe (Tag → JuliaLean.src.genericmemory_c.DictLayout)
      (Tag → JuliaLean.base.array.MemoryLayout) :=
  ⟨fun layout tag => JuliaLean.base.array.allocationSummary (layout tag)⟩


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)

namespace JuliaLean.Proofs.base.array

open JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section FindallFamily

/-- `findall(f, A::AbstractArray)` (array.jl:2791) broadcasts `f` and then runs the `Bool`
`findall`: the keys whose values pass `f`, in iteration order, in a fresh heap vector. `f.(A)` is
required to return the `Bool` array with the same keys and `f` of each value, and `count` the
number of `true` values. -/
instance instForInVectorMBoolPairs {K : Type} : ForIn (VectorM K) (VectorM K (List (K × Bool))) (K × Bool) where
  forIn act init f := do
    let xs ← act
    forIn xs init f
end FindallFamily
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)

namespace JuliaLean.Proofs.base.array

open JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

instance optionSlotAssignedDecidable {α : Type} (o : Option (Option α)) :
    Decidable (∃ x, o = some (some x)) :=
  match o with
  | some (some x) => isTrue ⟨x, rfl⟩
  | some none => isFalse (fun ⟨_, h⟩ => by cases h)
  | none => isFalse (fun ⟨_, h⟩ => by cases h)

instance unitRangeIsAbstractUnitRange {t : IntTy} :
    JuliaLean.base.range.JIsAbstractUnitRange (JuliaLean.base.range.UnitRange (JInt t)) := ⟨true⟩
end round4
end JuliaLean.Proofs.base.array

