import JuliaLean.Core
import JuliaLean.base.int

namespace JuliaLean.base.ntuple

open JuliaLean JuliaLean.base.int

/-!
# Model of `base/ntuple.jl`

Typed model of every method at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit
platform. Tuple fields carry their individual element types, and each source method keeps its
control flow and call order. Operations owned by other Base files are typed function parameters.
-/

abbrev I64 := JInt .i64
abbrev TupleField := Sigma fun α : Type => α
abbrev TupleValue := List TupleField

inductive NtupleError where
  | base (error : JlError)
  | typeError
  | external (name message : String)
  deriving Repr, DecidableEq

universe u
abbrev NtupleResult (α : Type u) := Except NtupleError α

/--
Julia source: base/ntuple.jl:36-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ntuple(f::F, n::Int) where F
    @noinline
    (n >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", n)))
    ([f(i) for i = 1:n]...,)
end
```
-/
def _ntuple (f : I64 → NtupleResult TupleField) (n : I64)
    (oneTo : I64 → NtupleResult (ULift (List I64))) : NtupleResult TupleValue :=
  if n.val ≥ 0 then
    match oneTo n with
    | .ok indices => List.mapM f indices.down
    | .error e => .error e
  else
    .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString n.val)))

/--
Julia source: base/ntuple.jl:5-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    ntuple(f, n::Integer)

Create a tuple of length `n`, computing each element as `f(i)`,
where `i` is the index of the element.

# Examples
```jldoctest
julia> ntuple(i -> 2*i, 4)
(2, 4, 6, 8)
```
"""
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
````
-/
def ntupleInt (f : I64 → NtupleResult TupleField) (n : I64)
    (oneTo : I64 → NtupleResult (ULift (List I64))) : NtupleResult TupleValue :=
  if n.val = 0 then .ok []
  else if n.val = 1 then do
    let x1 ← f (lit .i64 1)
    pure [x1]
  else if n.val = 2 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    pure [x1, x2]
  else if n.val = 3 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    pure [x1, x2, x3]
  else if n.val = 4 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    pure [x1, x2, x3, x4]
  else if n.val = 5 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    pure [x1, x2, x3, x4, x5]
  else if n.val = 6 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    pure [x1, x2, x3, x4, x5, x6]
  else if n.val = 7 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    pure [x1, x2, x3, x4, x5, x6, x7]
  else if n.val = 8 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    let x8 ← f (lit .i64 8)
    pure [x1, x2, x3, x4, x5, x6, x7, x8]
  else if n.val = 9 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    let x8 ← f (lit .i64 8)
    let x9 ← f (lit .i64 9)
    pure [x1, x2, x3, x4, x5, x6, x7, x8, x9]
  else if n.val = 10 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    let x8 ← f (lit .i64 8)
    let x9 ← f (lit .i64 9)
    let x10 ← f (lit .i64 10)
    pure [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10]
  else
    _ntuple f n oneTo

/--
Julia source: base/ntuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ntuple(f::F, n::Integer) where F = ntuple(f, convert(Int, n)::Int)
```
-/
def ntupleInteger {I : Type} (f : I64 → NtupleResult TupleField)
    (convertInt : I → Jl I64) (n : I)
    (oneTo : I64 → NtupleResult (ULift (List I64))) : NtupleResult TupleValue :=
  match convertInt n with
  | .ok nInt => ntupleInt f nInt oneTo
  | .error e => .error (.base e)

/--
Julia source: base/ntuple.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ntupleany(f, n)
    @noinline
    (n >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", n)))
    (Any[f(i) for i = 1:n]...,)
end
```
-/
def ntupleAny {N I : Type} (f : I → NtupleResult TupleField) (n : N)
    (isNonnegative : N → NtupleResult (ULift Bool))
    (oneTo : N → NtupleResult (ULift (List I)))
    (showValue : N → String) : NtupleResult TupleValue := do
  let nonnegative ← isNonnegative n
  if nonnegative.down then
    let indices ← oneTo n
    List.mapM f indices.down
  else
    .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ showValue n)))

/--
Julia source: base/ntuple.jl:48-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    ntuple(f, ::Val{N})

Create a tuple of length `N`, computing each element as `f(i)`,
where `i` is the index of the element. By taking a `Val(N)`
argument, it is possible that this version of ntuple may
generate more efficient code than the version taking the
length as an integer. But `ntuple(f, N)` is preferable to
`ntuple(f, Val(N))` in cases where `N` cannot be determined
at compile time.

# Examples
```jldoctest
julia> ntuple(i -> 2*i, Val(4))
(2, 4, 6, 8)
```
"""
@inline function ntuple(f::F, ::Val{N}) where {F,N}
    (N::Int >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", N)))
    if @generated
        :(@ntuple $N i -> f(i))
    else
        Tuple(f(i) for i = 1:(N::Int))
    end
end
````
-/
def ntupleVal {N : Type} (f : I64 → NtupleResult TupleField) (n : N)
    (assertInt : N → NtupleResult (ULift I64))
    (generated : Bool)
    (generatedNtuple : I64 → (I64 → NtupleResult TupleField) → NtupleResult TupleValue)
    (oneTo : I64 → NtupleResult (ULift (List I64))) : NtupleResult TupleValue := do
  let sizeLift ← assertInt n
  let size := sizeLift.down
  if size.val ≥ 0 then
    if generated then
      generatedNtuple size f
    else do
      let rangeSizeLift ← assertInt n
      let indices ← oneTo rangeSizeLift.down
      List.mapM f indices.down
  else
    .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString size.val)))

/--
Julia source: base/ntuple.jl:74-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function fill_to_length(t::Tuple, val, ::Val{_N}) where {_N}
    M = length(t)
    N = _N::Int
    M > N && throw(ArgumentError(LazyString("input tuple of length ", M, ", requested ", N)))
    if @generated
        quote
            (t..., $(fill(:val, (_N::Int) - length(t.parameters))...))
        end
    else
        (t..., fill(val, N-M)...)
    end
end
```
-/
def fillToLength {N : Type} (t : TupleValue) (val : TupleField) (n : N)
    (length : TupleValue → NtupleResult (ULift I64))
    (assertInt : N → NtupleResult (ULift I64))
    (fill : TupleField → I64 → NtupleResult TupleValue)
    (generated : Bool) : NtupleResult TupleValue := do
  let lengthLift ← length t
  let m := lengthLift.down
  let requestedLift ← assertInt n
  let requested := requestedLift.down
  if m.val > requested.val then
    .error (.base (.argumentError ("input tuple of length " ++ toString m.val ++
      ", requested " ++ toString requested.val)))
  else if generated then
    let count := sub_int requested (lit .i64 (Int.ofNat t.length))
    let padding ← fill val count
    pure (t ++ padding)
  else
    let count := sub_int requested m
    let padding ← fill val count
    pure (t ++ padding)

/--
Julia source: base/ntuple.jl:89-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reverse(t::NTuple{N}) where N
    ntuple(Val{N}()) do i
        t[end+1-i]
    end::typeof(t)
end
```
-/
def reverseNTuple {α : Type} (t : List α) (n : I64)
    (oneTo : I64 → NtupleResult (ULift (List I64)))
    (generated : Bool)
    (generatedNtuple : I64 → (I64 → NtupleResult TupleField) → NtupleResult TupleValue)
    (endIndex : List α → I64)
    (getindex : List α → I64 → NtupleResult (ULift α))
    (asNTuple : TupleValue → NtupleResult (ULift (List α))) :
    NtupleResult (ULift (List α)) := do
  let result ← ntupleVal (fun i => do
      let last := endIndex t
      let endPlusOne := add_int last (lit .i64 1)
      let index := sub_int endPlusOne i
      let value ← getindex t index
      pure ⟨α, value.down⟩)
    n (fun size => .ok (.up size)) generated generatedNtuple oneTo
  asNTuple result

end JuliaLean.base.ntuple
