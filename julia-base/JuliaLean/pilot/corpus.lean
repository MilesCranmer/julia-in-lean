import Std
import JuliaLean.src.dispatch

/-!
Corpus module `P` for the Base dispatch pilot.

```julia
module P
struct LinV{T} <: AbstractVector{T}; n::Int; end
Base.size(A::LinV) = (A.n,)
Base.getindex(A::LinV{T}, i::Int) where {T} = T(10i)
Base.IndexStyle(::Type{<:LinV}) = IndexLinear()
struct CartM <: AbstractMatrix{Int}; m::Int; n::Int; end
Base.size(A::CartM) = (A.m, A.n)
Base.getindex(A::CartM, i::Int, j::Int) = 100i + j
struct NoSize <: AbstractVector{Int} end
end
```
-/

namespace JuliaLean.Pilot.Corpus

open JuliaLean
open JuliaLean.C

/-- `Base.size(A::LinV) = (A.n,)` (`corpus:3`). -/
def sizeLinV : Body := fun _ args => do
  let [A] := args | throwMethodError "size(A::LinV): arity"
  let n ← getfieldSym A "n"
  mkTupleR [n]

/-- `Base.getindex(A::LinV{T}, i::Int) where {T} = T(10i)` (`corpus:4`). -/
def getindexLinV : Body := fun call args => do
  let [A, i] := args | throwMethodError "getindex(A::LinV{T}, i::Int): arity"
  let .datatype _ [T] ← typeOfObj A | throwTypeError "expected LinV{T}"
  let prod ← call "Base.*" [mkInt 10, i]
  callObj call (.type T) [prod]

/-- `Base.IndexStyle(::Type{<:LinV}) = IndexLinear()` (`corpus:5`). -/
def indexStyleLinV : Body := fun _ args => do
  let [_] := args | throwMethodError "IndexStyle(::Type{<:LinV}): arity"
  return indexLinearObj

/-- `Base.size(A::CartM) = (A.m, A.n)` (`corpus:7`). -/
def sizeCartM : Body := fun _ args => do
  let [A] := args | throwMethodError "size(A::CartM): arity"
  let m ← getfieldSym A "m"
  let n ← getfieldSym A "n"
  mkTupleR [m, n]

/-- `Base.getindex(A::CartM, i::Int, j::Int) = 100i + j` (`corpus:8`). -/
def getindexCartM : Body := fun call args => do
  let [_A, i, j] := args | throwMethodError "getindex(A::CartM, i::Int, j::Int): arity"
  let p ← call "Base.*" [mkInt 100, i]
  call "Base.+" [p, j]

def bodies : List (String × Body) :=
  [ ("corpus:3", sizeLinV)
  , ("corpus:4", getindexLinV)
  , ("corpus:5", indexStyleLinV)
  , ("corpus:7", sizeCartM)
  , ("corpus:8", getindexCartM)
  ]

end JuliaLean.Pilot.Corpus
