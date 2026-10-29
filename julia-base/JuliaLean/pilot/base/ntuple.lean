import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.NTuple

open JuliaLean
open JuliaLean.C

/--
Julia source: base/ntuple.jl:17-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function ntuple(f::F, n::Int) where F
    # marked inline since this benefits from constant propagation of `n`
    t = n == 0  ? () :
        n == 1  ? (f(1),) :
        n == 2  ? (f(1), f(2)) :
        n == 3  ? (f(1), f(2), f(3)) :
        n == 4  ? (f(1), f(2), f(3), f(4)) :
        n == 5  ? (f(1), f(2), f(3), f(4), f(5)) :
        n == 6  ? (f(1), f(2), f(3), f(4), f(5), f(6)) :
        n == 7  ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7)) :
        n == 8  ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8)) :
        n == 9  ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8), f(9)) :
        n == 10 ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8), f(9), f(10)) :
        _ntuple(f, n)
    return t
end
```
-/
def ntupleInt : Body := fun call args => do
  let [f, nObj] := args | throwMethodError "ntuple(f, n::Int): arity"
  let n ← asInt nObj
  if n < 0 then
    throwArgumentError "tuple length should be >= 0"
  let mut acc : List Obj := []
  for i in [1 : n.toNat + 1] do
    let v ← callObj call f [mkInt (Int.ofNat i)]
    acc := acc ++ [v]
  mkTupleR acc

/--
Julia source: base/ntuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ntuple(f::F, n::Integer) where F = ntuple(f, convert(Int, n)::Int)
```
-/
def ntupleInteger : Body := fun call args => do
  let [f, n] := args | throwMethodError "ntuple(f, n::Integer): arity"
  let nInt ← call "Base.convert" [.type int64Type, n]
  if !(← isaObj nInt int64Type) then
    throwTypeError "ntuple: expected Int"
  call "Base.ntuple" [f, nInt]

/--
Julia source: base/ntuple.jl:65-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function ntuple(f::F, ::Val{N}) where {F,N}
    (N::Int >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", N)))
    if @generated
        :(@ntuple $N i -> f(i))
    else
        Tuple(f(i) for i = 1:(N::Int))
    end
end
```
-/
def ntupleVal : Body := fun call args => do
  let [f, valObj] := args | throwMethodError "ntuple(f, ::Val{N}): arity"
  let .datatype "Base.Val" [.long n] ← typeOfObj valObj
    | throwTypeError "ntuple(::Val{N}): expected Int parameter N"
  let ge0 ← call "Base.>=" [mkInt n, mkInt 0]
  if !(← asBool ge0) then
    throwArgumentError "tuple length should be >= 0"
  let mut acc : List Obj := []
  for i in [1 : n.toNat + 1] do
    let v ← callObj call f [mkInt (Int.ofNat i)]
    acc := acc ++ [v]
  mkTupleR acc

def bodies : List (String × Body) :=
  [ ("base/ntuple.jl:17", ntupleInt)
  , ("base/ntuple.jl:33", ntupleInteger)
  , ("base/ntuple.jl:65", ntupleVal)
  ]

end JuliaLean.Pilot.Base.NTuple
