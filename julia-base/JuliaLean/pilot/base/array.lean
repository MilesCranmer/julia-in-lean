import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Array

open JuliaLean
open JuliaLean.C

/--
Julia source: base/array.jl:974-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array, i1::Int, i2::Int, I::Int...)
    @inline
    @boundscheck checkbounds(A, i1, i2, I...) # generally _to_linear_index requires bounds checking
    return @inbounds A[_to_linear_index(A, i1, i2, I...)]
end
```
-/
def getindexArrayMultiInt : Body := fun call args => do
  let A :: i1 :: i2 :: I := args
    | throwMethodError "getindex(A::Array, i1::Int, i2::Int, I::Int...): arity"
  let _ ← call "Base.checkbounds" (A :: i1 :: i2 :: I)
  let lin ← call "Base._to_linear_index" (A :: i1 :: i2 :: I)
  call "Base.getindex" [A, lin]

def bodies : List (String × Body) :=
  [ ("base/array.jl:974", getindexArrayMultiInt)
  ]

end JuliaLean.Pilot.Base.Array
