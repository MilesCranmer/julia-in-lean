import JuliaLean.Compiler.src.reinfer.State

/-!
The binding queries of `Compiler/src/reinfer.jl` (`binding_access_range_at`,
`binding_changed_since_require_world`), kept apart from `reinfer.lean` because the source scan
of `Compiler/src/bindinginvalidations.jl` calls them and `reinfer.lean` imports that model.
-/

namespace JuliaLean.Compiler.Reinfer

open JuliaLean.C JuliaLean.Compiler.CICache

variable {W : Type}

/-- `binding_access_range_at(b, world)`

Julia source: Compiler/src/reinfer.jl:97-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function binding_access_range_at(b::Core.Binding, world::UInt)
    wr, _ = binding_access_range(b, WorldWithRange(world, WorldRange(get_require_world(), world)), false)
    return wr
end
```
`binding_access_range` (`Compiler/src/abstractinterpretation.jl:4241-4285`) is the oracle's
`bindingAccessRange`. `WorldWithRange` throws an `ErrorException` when `world` is outside
`[require_world, world]`, that is when `world < require_world`.
-/
def bindingAccessRangeAt (O : Oracle) (b : Nat) (world : Nat) : RM W WorldRange := do
  let H ← getHeap
  if !(H.requireWorld ≤ world) then jlThrow "ErrorException" "invalid age range update"
  liftE (O.bindingAccessRange b world)

/-- `binding_changed_since_require_world(b, world)`

Julia source: Compiler/src/reinfer.jl:102-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whether an access to `b` can resolve differently now than it did in any process that serialized code against it.
function binding_changed_since_require_world(b::Core.Binding, world::UInt)
    require_world = get_require_world()
    # Fast path: this binding has not been repartitioned since the require world at all, and it
    # resolves without crossing an import, so no walk is needed to know its range reaches back.
    # A non-leaf partition has to take the slow path: the walk continues into the binding it
    # imports, which may itself have been repartitioned after the require world even though `b`
    # was not.
    if isdefined(b, :partitions)
        p = b.partitions
        p.min_world <= require_world && is_leaf_partition(p) && return false
    end
    return min_world(binding_access_range_at(b, world)) > require_world
end
```
-/
def bindingChangedSinceRequireWorld (O : Oracle) (b : Nat) (world : Nat) : RM W Bool := do
  let H ← getHeap
  let br ← liftE (H.bindingR b)
  let requireWorld := H.requireWorld
  if let p :: _ := br.partitions then
    if p.minWorld ≤ requireWorld && isLeafPartition p then return false
  return (← bindingAccessRangeAt O b world).minWorld > requireWorld

end JuliaLean.Compiler.Reinfer
