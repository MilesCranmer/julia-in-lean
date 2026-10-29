import Std
import JuliaLean.src.dispatch

namespace JuliaLean.Pilot.Base.Float

open JuliaLean
open JuliaLean.C

def asFloat64 (o : Obj) : R Float := do
  let v ← asInt o
  return Float.ofBits (UInt64.ofNat (wrapUInt64 v).toNat)

def mkFloat64 (f : Float) : Obj :=
  .bits float64Type (Int.ofNat f.toBits.toNat)

/-- `Float64(Int64(typemax(Int64)))` = `2^63` (`0x43e0000000000000`). -/
def float64TypemaxInt64 : Obj :=
  .bits float64Type (Int.ofNat (0x43e0000000000000 : UInt64).toNat)

/--
Julia source: base/float.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            (::Type{$t1})(x::($st)) = sitofp($t1, x)
```
-/
def float64Ctor : Body := fun _ args => do
  let [x] := args | throwMethodError "Float64(x): arity"
  let ty ← typeOfObj x
  if ty == float64Type then
    return x
  else if ty == int64Type then
    let v ← asInt x
    let f : Float :=
      if v < 0 then -(Float.ofNat (-v).toNat)
      else Float.ofNat v.toNat
    return mkFloat64 f
  else if ty == boolType then
    return mkFloat64 (if (← asInt x) != 0 then 1.0 else 0.0)
  else
    throwMethodError s!"MethodError: no method matching Float64({repr ty})"

/--
Julia source: base/float.jl:410-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        unsafe_trunc(::Type{$Ti}, x::IEEEFloat) = fptosi($Ti, x)
```
-/
def unsafeTruncSignedFloat : Body := fun _ args => do
  let [.type Ti, x] := args | throwMethodError "unsafe_trunc(::Type{Ti}, x::IEEEFloat): arity"
  let f ← asFloat64 x
  let i : Int :=
    if f < 0.0 then -Int.ofNat ((-f).toUInt64.toNat)
    else Int.ofNat f.toUInt64.toNat
  return .bits Ti (wrapInt64 i)

/--
Julia source: base/float.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        unsafe_trunc(::Type{$Ti}, x::IEEEFloat) = fptoui($Ti, x)
```
-/
def unsafeTruncUnsignedFloat : Body := fun _ args => do
  let [.type Ti, x] := args | throwMethodError "unsafe_trunc(::Type{Ti}, x::IEEEFloat): arity"
  let f ← asFloat64 x
  return .bits Ti (Int.ofNat f.toUInt64.toNat)

/--
Julia source: base/float.jl:485-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::IEEEFloat) = neg_float(x)
```
-/
def negFloat : Body := fun _ args => do
  let [x] := args | throwMethodError "-(x::IEEEFloat): arity"
  return mkFloat64 (-(← asFloat64 x))

/--
Julia source: base/float.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::T, y::T) where {T<:IEEEFloat} = add_float(x, y)
```
-/
def addFloat : Body := fun _ args => do
  let [x, y] := args | throwMethodError "+(x::T, y::T): arity"
  return mkFloat64 ((← asFloat64 x) + (← asFloat64 y))

/--
Julia source: base/float.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::T, y::T) where {T<:IEEEFloat} = sub_float(x, y)
```
-/
def subFloat : Body := fun _ args => do
  let [x, y] := args | throwMethodError "-(x::T, y::T): arity"
  return mkFloat64 ((← asFloat64 x) - (← asFloat64 y))

/--
Julia source: base/float.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(x::T, y::T) where {T<:IEEEFloat} = mul_float(x, y)
```
-/
def mulFloat : Body := fun _ args => do
  let [x, y] := args | throwMethodError "*(x::T, y::T): arity"
  return mkFloat64 ((← asFloat64 x) * (← asFloat64 y))

/--
Julia source: base/float.jl:615-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::T, y::T) where {T<:IEEEFloat} = eq_float(x, y)
```
-/
def eqFloat : Body := fun _ args => do
  let [x, y] := args | throwMethodError "==(x::T, y::T): arity"
  return mkBool ((← asFloat64 x) == (← asFloat64 y))

/--
Julia source: base/float.jl:616-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::T, y::T) where {T<:IEEEFloat} = lt_float(x, y)
```
-/
def ltFloat : Body := fun _ args => do
  let [x, y] := args | throwMethodError "<(x::T, y::T): arity"
  return mkBool ((← asFloat64 x) < (← asFloat64 y))

/--
Julia source: base/float.jl:617-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::T, y::T) where {T<:IEEEFloat} = le_float(x, y)
```
-/
def leFloat : Body := fun _ args => do
  let [x, y] := args | throwMethodError "<=(x::T, y::T): arity"
  return mkBool ((← asFloat64 x) ≤ (← asFloat64 y))

/--
Julia source: base/float.jl:652-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function ==(x::$Tf, y::$Ti)
                fy = ($Tf)(y)
                (x == fy) & (fy != $(Tf(typemax(Ti)))) & (y == unsafe_trunc($Ti,fy))
            end
```
-/
def eqFloatInt : Body := fun call args => do
  let [x, y] := args | throwMethodError "==(x::Float64, y::Int64): arity"
  let ti ← typeOfObj y
  let fy ← call "Core.Float64" [y]
  let c1 ← call "Base.==" [x, fy]
  let c2 ← call "Base.!=" [fy, float64TypemaxInt64]
  let tr ← call "Base.unsafe_trunc" [.type ti, fy]
  let c3 ← call "Base.==" [y, tr]
  let c12 ← call "Base.&" [c1, c2]
  call "Base.&" [c12, c3]

/--
Julia source: base/float.jl:656-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            ==(y::$Ti, x::$Tf) = x==y
```
-/
def eqIntFloat : Body := fun call args => do
  let [y, x] := args | throwMethodError "==(y::Int64, x::Float64): arity"
  call "Base.==" [x, y]

/--
Julia source: base/float.jl:658-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <(x::$Ti, y::$Tf)
                fx = ($Tf)(x)
                (fx < y) | ((fx == y) & ((fx == $(Tf(typemax(Ti)))) | (x < unsafe_trunc($Ti,fx)) ))
            end
```
-/
def ltIntFloat : Body := fun call args => do
  let [x, y] := args | throwMethodError "<(x::Int64, y::Float64): arity"
  let ti ← typeOfObj x
  let fx ← call "Core.Float64" [x]
  let c1 ← call "Base.<" [fx, y]
  let c2 ← call "Base.==" [fx, y]
  let c3 ← call "Base.==" [fx, float64TypemaxInt64]
  let tr ← call "Base.unsafe_trunc" [.type ti, fx]
  let c4 ← call "Base.<" [x, tr]
  let c34 ← call "Base.|" [c3, c4]
  let c234 ← call "Base.&" [c2, c34]
  call "Base.|" [c1, c234]

/--
Julia source: base/float.jl:662-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <=(x::$Ti, y::$Tf)
                fx = ($Tf)(x)
                (fx < y) | ((fx == y) & ((fx == $(Tf(typemax(Ti)))) | (x <= unsafe_trunc($Ti,fx)) ))
            end
```
-/
def leIntFloat : Body := fun call args => do
  let [x, y] := args | throwMethodError "<=(x::Int64, y::Float64): arity"
  let ti ← typeOfObj x
  let fx ← call "Core.Float64" [x]
  let c1 ← call "Base.<" [fx, y]
  let c2 ← call "Base.==" [fx, y]
  let c3 ← call "Base.==" [fx, float64TypemaxInt64]
  let tr ← call "Base.unsafe_trunc" [.type ti, fx]
  let c4 ← call "Base.<=" [x, tr]
  let c34 ← call "Base.|" [c3, c4]
  let c234 ← call "Base.&" [c2, c34]
  call "Base.|" [c1, c234]

/--
Julia source: base/float.jl:667-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <(x::$Tf, y::$Ti)
                fy = ($Tf)(y)
                (x < fy) | ((x == fy) & (fy < $(Tf(typemax(Ti)))) & (unsafe_trunc($Ti,fy) < y))
            end
```
-/
def ltFloatInt : Body := fun call args => do
  let [x, y] := args | throwMethodError "<(x::Float64, y::Int64): arity"
  let ti ← typeOfObj y
  let fy ← call "Core.Float64" [y]
  let c1 ← call "Base.<" [x, fy]
  let c2 ← call "Base.==" [x, fy]
  let c3 ← call "Base.<" [fy, float64TypemaxInt64]
  let tr ← call "Base.unsafe_trunc" [.type ti, fy]
  let c4 ← call "Base.<" [tr, y]
  let c23 ← call "Base.&" [c2, c3]
  let c234 ← call "Base.&" [c23, c4]
  call "Base.|" [c1, c234]

/--
Julia source: base/float.jl:671-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            function <=(x::$Tf, y::$Ti)
                fy = ($Tf)(y)
                (x < fy) | ((x == fy) & (fy < $(Tf(typemax(Ti)))) & (unsafe_trunc($Ti,fy) <= y))
            end
```
-/
def leFloatInt : Body := fun call args => do
  let [x, y] := args | throwMethodError "<=(x::Float64, y::Int64): arity"
  let ti ← typeOfObj y
  let fy ← call "Core.Float64" [y]
  let c1 ← call "Base.<" [x, fy]
  let c2 ← call "Base.==" [x, fy]
  let c3 ← call "Base.<" [fy, float64TypemaxInt64]
  let tr ← call "Base.unsafe_trunc" [.type ti, fy]
  let c4 ← call "Base.<=" [tr, y]
  let c23 ← call "Base.&" [c2, c3]
  let c234 ← call "Base.&" [c23, c4]
  call "Base.|" [c1, c234]

def bodies : List (String × Body) :=
  [ ("Core.Float64", float64Ctor)
  , ("base/float.jl:410", unsafeTruncSignedFloat)
  , ("base/float.jl:415", unsafeTruncUnsignedFloat)
  , ("base/float.jl:485", negFloat)
  , ("base/float.jl:487", addFloat)
  , ("base/float.jl:488", subFloat)
  , ("base/float.jl:489", mulFloat)
  , ("base/float.jl:615", eqFloat)
  , ("base/float.jl:616", ltFloat)
  , ("base/float.jl:617", leFloat)
  , ("base/float.jl:652", eqFloatInt)
  , ("base/float.jl:656", eqIntFloat)
  , ("base/float.jl:658", ltIntFloat)
  , ("base/float.jl:662", leIntFloat)
  , ("base/float.jl:667", ltFloatInt)
  , ("base/float.jl:671", leFloatInt)
  ]

end JuliaLean.Pilot.Base.Float
