import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Multidimensional

open JuliaLean
open JuliaLean.C

/--
Julia source: base/multidimensional.jl:523-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function split(t, V::Val)
        ref = ntuple(Returns(true), V)  # create a reference tuple of length N
        _split1(t, ref), _splitrest(t, ref)
    end
```
-/
def splitTupleVal : Body := fun call args => do
  let [t, V] := args | throwMethodError "IteratorsMD.split(t, V::Val): arity"
  let returnsTrue : Obj := .imm (.datatype "Base.Returns" [boolType]) [mkBool true]
  let ref ← call "Base.ntuple" [returnsTrue, V]
  let s1 ← call "Base.IteratorsMD._split1" [t, ref]
  let srest ← call "Base.IteratorsMD._splitrest" [t, ref]
  mkTupleR [s1, srest]

/--
Julia source: base/multidimensional.jl:527-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline _split1(t, ref) = (t[1], _split1(tail(t), tail(ref))...)
```
-/
def split1Step : Body := fun call args => do
  let [t, ref] := args | throwMethodError "_split1(t, ref): arity"
  let t1 ← call "Base.getindex" [t, mkInt 1]
  let tt ← call "Base.tail" [t]
  let tref ← call "Base.tail" [ref]
  let restTup ← call "Base.IteratorsMD._split1" [tt, tref]
  let rest ← unpackTuple restTup
  mkTupleR (t1 :: rest)

/--
Julia source: base/multidimensional.jl:528-528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline _splitrest(t, ref) = _splitrest(tail(t), tail(ref))
```
-/
def splitrestStep : Body := fun call args => do
  let [t, ref] := args | throwMethodError "_splitrest(t, ref): arity"
  let tt ← call "Base.tail" [t]
  let tref ← call "Base.tail" [ref]
  call "Base.IteratorsMD._splitrest" [tt, tref]

/--
Julia source: base/multidimensional.jl:530-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _split1(::Tuple{}, ::Tuple{}) = ()
```
-/
def split1EmptyEmpty : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_split1(::Tuple{}, ::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/multidimensional.jl:531-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _split1(::Tuple{}, ref) = ()
```
-/
def split1EmptyRef : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_split1(::Tuple{}, ref): arity"
  mkTupleR []

/--
Julia source: base/multidimensional.jl:532-532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _split1(t, ::Tuple{}) = ()
```
-/
def split1TEmpty : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_split1(t, ::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/multidimensional.jl:533-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _splitrest(::Tuple{}, ::Tuple{}) = ()
```
-/
def splitrestEmptyEmpty : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_splitrest(::Tuple{}, ::Tuple{}): arity"
  mkTupleR []

/--
Julia source: base/multidimensional.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _splitrest(t, ::Tuple{}) = t
```
-/
def splitrestTEmpty : Body := fun _ args => do
  let [t, _] := args | throwMethodError "_splitrest(t, ::Tuple{}): arity"
  return t

/--
Julia source: base/multidimensional.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _splitrest(::Tuple{}, ref) = ()
```
-/
def splitrestEmptyRef : Body := fun _ args => do
  let [_, _] := args | throwMethodError "_splitrest(::Tuple{}, ref): arity"
  mkTupleR []

/--
Julia source: base/multidimensional.jl:772-773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds getindex(A::Array, i1::Union{Integer, CartesianIndex}, I::Union{Integer, CartesianIndex}...) =
    A[to_indices(A, (i1, I...))...]
```
-/
def getindexArrayIntOrCart : Body := fun call args => do
  let A :: i1 :: I := args | throwMethodError "getindex(A::Array, i1, I...): arity"
  let iTup ← mkTupleR (i1 :: I)
  let indsTup ← call "Base.to_indices" [A, iTup]
  let inds ← unpackTuple indsTup
  call "Base.getindex" (A :: inds)

/--
Julia source: base/multidimensional.jl:928-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline to_indices(A, I::Tuple{Vararg{Union{Integer, CartesianIndex}}}) = to_indices(A, (), I)
```
-/
def toIndicesIntOrCart : Body := fun call args => do
  let [A, I] := args | throwMethodError "to_indices(A, I::Tuple{Vararg{Union{Integer, CartesianIndex}}}): arity"
  let emptyTup ← mkTupleR []
  call "Base.to_indices" [A, emptyTup, I]

/--
Julia source: base/multidimensional.jl:929-929 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_drop_zerodim(I::Tuple{CartesianIndex{0}, Vararg}) = (@inline; _drop_zerodim(tail(I)))
```
-/
def dropZerodimCart0 : Body := fun call args => do
  let [I] := args | throwMethodError "_drop_zerodim(I::Tuple{CartesianIndex{0}, Vararg}): arity"
  let tI ← call "Base.tail" [I]
  call "Base._drop_zerodim" [tI]

def bodies : List (String × Body) :=
  [ ("base/multidimensional.jl:523", splitTupleVal)
  , ("base/multidimensional.jl:527", split1Step)
  , ("base/multidimensional.jl:528", splitrestStep)
  , ("base/multidimensional.jl:530", split1EmptyEmpty)
  , ("base/multidimensional.jl:531", split1EmptyRef)
  , ("base/multidimensional.jl:532", split1TEmpty)
  , ("base/multidimensional.jl:533", splitrestEmptyEmpty)
  , ("base/multidimensional.jl:534", splitrestTEmpty)
  , ("base/multidimensional.jl:535", splitrestEmptyRef)
  , ("base/multidimensional.jl:772", getindexArrayIntOrCart)
  , ("base/multidimensional.jl:928", toIndicesIntOrCart)
  , ("base/multidimensional.jl:929", dropZerodimCart0)
  ]

end JuliaLean.Pilot.Base.Multidimensional
