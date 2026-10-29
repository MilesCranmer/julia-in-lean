import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Range

open JuliaLean
open JuliaLean.C

/--
Julia source: base/range.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(:)(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
```
-/
def colonReal : Body := fun call args => do
  let [start, stop] := args | throwMethodError "(:)(start::T, stop::T): arity"
  let T ← typeOfObj start
  let lastVal ← call "Base.unitrange_last" [start, stop]
  return .imm (.datatype "Base.UnitRange" [T]) [start, lastVal]

/--
Julia source: base/range.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range_wrapping_sub(x::_RangeWrappingInteger, y::_RangeWrappingInteger) = x -% y
```
-/
def rangeWrappingSubInt : Body := fun call args => do
  let [x, y] := args | throwMethodError "_range_wrapping_sub(x, y): arity"
  call "Base.-%" [x, y]

/--
Julia source: base/range.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_range_wrapping_sub(x, y) = x - y
```
-/
def rangeWrappingSubGeneric : Body := fun call args => do
  let [x, y] := args | throwMethodError "_range_wrapping_sub(x, y): arity"
  call "Base.-" [x, y]

/--
Julia source: base/range.jl:439-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unitrange_last(start::Integer, stop::Integer) =
    stop >= start ? stop : convert(typeof(stop),
        _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
```
-/
def unitrangeLastInteger : Body := fun call args => do
  let [start, stop] := args | throwMethodError "unitrange_last(start::Integer, stop::Integer): arity"
  let cmp ← call "Base.>=" [stop, start]
  if ← asBool cmp then
    return stop
  else
    let tStop ← typeOfObj stop
    let diff ← call "Base._range_wrapping_sub" [start, stop]
    let oneU ← call "Base.oneunit" [diff]
    let sub ← call "Base._range_wrapping_sub" [start, oneU]
    call "Base.convert" [.type tStop, sub]

/--
Julia source: base/range.jl:487-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function OneTo{T}(stop) where {T<:Integer}
        throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
        T === Bool && throwbool(stop)
        return new(max(zero(T), stop))
    end
```

Julia source: base/range.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
OneTo(stop::T) where {T<:Integer} = OneTo{T}(stop)
```
-/
def oneToCtor : Body := fun call args => do
  let [stop] := args | throwMethodError "OneTo(stop): arity"
  let T ← typeOfObj stop
  if T == boolType then
    throwArgumentError "invalid index of type Bool"
  let z ← call "Base.zero" [.type T]
  let m ← call "Base.max" [z, stop]
  return .imm (oneToType T) [m]

/--
Julia source: base/range.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
```
-/
def uncheckedOneto : Body := fun _ args => do
  let [stop] := args | throwMethodError "unchecked_oneto(stop::Integer): arity"
  let T ← typeOfObj stop
  return .imm (oneToType T) [stop]

/--
Julia source: base/range.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oneto(r) = OneTo(r)
```
-/
def onetoGeneric : Body := fun call args => do
  let [r] := args | throwMethodError "oneto(r): arity"
  call "Base.OneTo" [r]

/--
Julia source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(r::AbstractUnitRange{T}) where T
    @inline
    start, stop = first(r), last(r)
    a = oneunit(zero(stop) - zero(start))
    if a isa Signed || stop >= start
        a += stop - start # Signed are allowed to go negative
    else
        a = zero(a) # Unsigned don't necessarily underflow
    end
    return Integer(a)
end
```
-/
def lengthUnitRange : Body := fun call args => do
  let [r] := args | throwMethodError "length(r::AbstractUnitRange{T}): arity"
  let start ← call "Base.first" [r]
  let stop ← call "Base.last" [r]
  let zStop ← call "Base.zero" [stop]
  let zStart ← call "Base.zero" [start]
  let zDiff ← call "Base.-" [zStop, zStart]
  let a0 ← call "Base.oneunit" [zDiff]
  let isSigned ← isaObj a0 (.datatype "Core.Signed" [])
  let ge ← if isSigned then pure true else do
    let c ← call "Base.>=" [stop, start]
    asBool c
  if ge then
    let diff ← call "Base.-" [stop, start]
    call "Base.+" [a0, diff]
  else
    call "Base.zero" [a0]

/--
Julia source: base/range.jl:806-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(r::OneTo) = Integer(r.stop - zero(r.stop))
```
-/
def lengthOneToGeneric : Body := fun call args => do
  let [r] := args | throwMethodError "length(r::OneTo): arity"
  let stop ← getfieldSym r "stop"
  let z ← call "Base.zero" [stop]
  call "Base.-" [stop, z]

/--
Julia source: base/range.jl:817-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    length(r::OneTo{T}) where {T<:bigints} = r.stop
```
-/
def lengthOneToBigint : Body := fun _ args => do
  let [r] := args | throwMethodError "length(r::OneTo{T}): arity"
  getfieldSym r "stop"

/--
Julia source: base/range.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    length(r::OneTo{<:smallints}) = Int(r.stop)
```
-/
def lengthOneToSmallint : Body := fun call args => do
  let [r] := args | throwMethodError "length(r::OneTo{<:smallints}): arity"
  let stop ← getfieldSym r "stop"
  call "Core.Int64" [stop]

/--
Julia source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
```
-/
def firstOrdinalRange : Body := fun call args => do
  let [r] := args | throwMethodError "first(r::OrdinalRange{T}): arity"
  let .datatype _ (T :: _) ← typeOfObj r | throwTypeError "expected OrdinalRange{T}"
  let st ← getfieldSym r "start"
  call "Base.convert" [.type T, st]

/--
Julia source: base/range.jl:868-868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(r::OneTo{T}) where {T} = oneunit(T)
```
-/
def firstOneTo : Body := fun call args => do
  let [r] := args | throwMethodError "first(r::OneTo{T}): arity"
  let .datatype _ [T] ← typeOfObj r | throwTypeError "expected OneTo{T}"
  call "Base.oneunit" [.type T]

/--
Julia source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
```
-/
def lastOrdinalRange : Body := fun call args => do
  let [r] := args | throwMethodError "last(r::OrdinalRange{T}): arity"
  let .datatype _ (T :: _) ← typeOfObj r | throwTypeError "expected OrdinalRange{T}"
  let st ← getfieldSym r "stop"
  call "Base.convert" [.type T, st]

/--
Julia source: base/range.jl:1489-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(x::Integer, r::AbstractUnitRange{<:Integer}) = (first(r) <= x) & (x <= last(r))
```
-/
def inIntegerUnitRange : Body := fun call args => do
  let [x, r] := args | throwMethodError "in(x::Integer, r::AbstractUnitRange{<:Integer}): arity"
  let f ← call "Base.first" [r]
  let c1 ← call "Base.<=" [f, x]
  let l ← call "Base.last" [r]
  let c2 ← call "Base.<=" [x, l]
  call "Base.&" [c1, c2]

/--
Julia source: base/range.jl:706-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(r::AbstractRange) = (@inline; (length(r),))
```
-/
def sizeAbstractRange : Body := fun call args => do
  let [r] := args | throwMethodError "size(r::AbstractRange): arity"
  let len ← call "Base.length" [r]
  mkTupleR [len]

def bodies : List (String × Body) :=
  [ ("base/range.jl:5", colonReal)
  , ("base/range.jl:36", rangeWrappingSubInt)
  , ("base/range.jl:37", rangeWrappingSubGeneric)
  , ("base/range.jl:439", unitrangeLastInteger)
  , ("Base.OneTo", oneToCtor)
  , ("base/range.jl:503", uncheckedOneto)
  , ("base/range.jl:507", onetoGeneric)
  , ("base/range.jl:706", sizeAbstractRange)
  , ("base/range.jl:794", lengthUnitRange)
  , ("base/range.jl:806", lengthOneToGeneric)
  , ("base/range.jl:817", lengthOneToBigint)
  , ("base/range.jl:860", lengthOneToSmallint)
  , ("base/range.jl:867", firstOrdinalRange)
  , ("base/range.jl:868", firstOneTo)
  , ("base/range.jl:877", lastOrdinalRange)
  , ("base/range.jl:1489", inIntegerUnitRange)
  ]

end JuliaLean.Pilot.Base.Range
