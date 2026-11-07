-- Source: base/ryu/Ryu.jl:1-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- module Ryu
-- 
-- using .Base.Libc
-- using .Base: significand_bits, significand_mask, exponent_mask, exponent_bias, exponent_max, uinttype
-- 
-- include("utils.jl")
-- include("shortest.jl")
-- include("fixed.jl")
-- include("exp.jl")
-- 
-- /Source
-- Source: base/ryu/Ryu.jl:147-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end # module
-- /Source
import JuliaLean.Core
import JuliaLean.base.rounding
import JuliaLean.Runtime.Float
import JuliaLean.base.ryu.utils
import JuliaLean.base.ryu.shortest
import JuliaLean.base.ryu.fixed
import JuliaLean.base.ryu.exp
/-!
# Model of `base/ryu/Ryu.jl`

Public methods return UTF-8 byte lists. `show` and `print` receive the relevant
stream flags and a writer callback, so numeric formatting stays separate from I/O.
-/

namespace JuliaLean.base.ryu.Ryu

open JuliaLean JuliaLean.Promotion

abbrev FloatType := JuliaLean.MiscCov.RyuUtils.FT

def neededdigits : FloatType → Nat
  | .f64 => 309 + 17
  | .f32 => 39 + 9 + 2
  | .f16 => 9 + 5 + 9

def neededfloatdigits : FloatType → Nat
  | .f64 => 24
  | .f32 => 17
  | .f16 => 20
def outputSizeOverflows (precision : Int) (needed : Nat) : Bool :=
  precision > IntTy.max .i64 - Int.ofNat needed

def writeshortestString16 (x : Fl half) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (typed compact : Bool) :
    JuliaLean.Jl (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else if precision ≥ 0 && outputSizeOverflows precision (neededdigits .f16) then
    .error (.overflowError "checked_add")
  else writeshortest16 x plus space hash precision expchar padexp decchar typed compact

def writeshortestString32 (x : Fl single) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (typed compact : Bool) :
    JuliaLean.Jl (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else if precision ≥ 0 && outputSizeOverflows precision (neededdigits .f32) then
    .error (.overflowError "checked_add")
  else writeshortest32 x plus space hash precision expchar padexp decchar typed compact

def writeshortestString64 (x : JuliaLean.Float.F64) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (compact : Bool) :
    JuliaLean.Jl (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else if precision ≥ 0 && outputSizeOverflows precision (neededdigits .f64) then
    .error (.overflowError "checked_add")
  else writeshortest64 x plus space hash precision expchar padexp decchar compact

def writefixedString16 (x : Fl half) (precision : Int) (plus space hash : Bool)
    (decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
  else if outputSizeOverflows precision (neededdigits .f16) then
    .error (.julia (.overflowError "checked_add"))
  else writefixed16 x precision plus space hash decchar trimtrailingzeros

def writefixedString32 (x : Fl single) (precision : Int) (plus space hash : Bool)
    (decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
  else if outputSizeOverflows precision (neededdigits .f32) then
    .error (.julia (.overflowError "checked_add"))
  else writefixed32 x precision plus space hash decchar trimtrailingzeros

def writefixedString64 (x : JuliaLean.Float.F64) (precision : Int) (plus space hash : Bool)
    (decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
  else if outputSizeOverflows precision (neededdigits .f64) then
    .error (.julia (.overflowError "checked_add"))
  else writefixed64 x precision plus space hash decchar trimtrailingzeros

def writeexpString16 (x : Fl half) (precision : Int) (plus space hash : Bool)
    (expchar decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
  else if outputSizeOverflows precision (neededdigits .f16) then
    .error (.julia (.overflowError "checked_add"))
  else writeexp16 x precision plus space hash expchar decchar trimtrailingzeros

def writeexpString32 (x : Fl single) (precision : Int) (plus space hash : Bool)
    (expchar decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
  else if outputSizeOverflows precision (neededdigits .f32) then
    .error (.julia (.overflowError "checked_add"))
  else writeexp32 x precision plus space hash expchar decchar trimtrailingzeros

def writeexpString64 (x : JuliaLean.Float.F64) (precision : Int) (plus space hash : Bool)
    (expchar decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
  else if outputSizeOverflows precision (neededdigits .f64) then
    .error (.julia (.overflowError "checked_add"))
  else writeexp64 x precision plus space hash expchar decchar trimtrailingzeros

def show16 (writeBytes : List Nat → JuliaLean.Jl Unit) (compact forceuntyped _fromprint : Bool)
    (hasMatchingTypeInfo : Bool) (x : Fl half) : JuliaLean.Jl Unit := do
  let typed := !forceuntyped && !compact && !hasMatchingTypeInfo
  let bytes ← writeshortest16 x false false true (-1) 101 false 46 typed compact
  writeBytes bytes

def show32 (writeBytes : List Nat → JuliaLean.Jl Unit) (compact forceuntyped fromprint : Bool)
    (hasMatchingTypeInfo : Bool) (x : Fl single) : JuliaLean.Jl Unit := do
  let typed := !forceuntyped && !compact && !hasMatchingTypeInfo
  let expchar := if fromprint then 101 else 102
  let bytes ← writeshortest32 x false false true (-1) expchar false 46 typed compact
  writeBytes bytes

def show64 (writeBytes : List Nat → JuliaLean.Jl Unit) (compact : Bool)
    (x : JuliaLean.Float.F64) : JuliaLean.Jl Unit := do
  let bytes ← writeshortest64 x false false true (-1) 101 false 46 compact
  writeBytes bytes

def print16 (writeBytes : List Nat → JuliaLean.Jl Unit) (compact : Bool)
    (x : Fl half) : JuliaLean.Jl Unit :=
  show16 writeBytes compact true true false x

def print32 (writeBytes : List Nat → JuliaLean.Jl Unit) (compact : Bool)
    (x : Fl single) : JuliaLean.Jl Unit :=
  show32 writeBytes compact true true false x

def string16 (x : Fl half) : JuliaLean.Jl (List Nat) :=
  writeshortest16 x false false true (-1) 101 false 46 false false

def string32 (x : Fl single) : JuliaLean.Jl (List Nat) :=
  writeshortest32 x false false true (-1) 101 false 46 false false

def string64 (x : JuliaLean.Float.F64) : JuliaLean.Jl (List Nat) :=
  writeshortest64 x false false true (-1) 101 false 46 false

/--
Julia source: base/ryu/Ryu.jl:12-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ryu.neededdigits(T)

Number of digits necessary to represent type `T` in fixed-precision decimal.
"""
neededdigits(::Type{Float64}) = 309 + 17
```
-/
def neededdigitsFloat64 : Nat := 309 + 17


/--
Julia source: base/ryu/Ryu.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
neededdigits(::Type{Float32}) = 39 + 9 + 2
```
-/
def neededdigitsFloat32 : Nat := 39 + 9 + 2


/--
Julia source: base/ryu/Ryu.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
neededdigits(::Type{Float16}) = 9 + 5 + 9
```
-/
def neededdigitsFloat16 : Nat := 9 + 5 + 9


/--
Julia source: base/ryu/Ryu.jl:21-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Ryu.neededfloatdigits(T)

Number of digits necessary to represent type `T` in shortest precision.
"""
neededfloatdigits(::Type{Float64}) = 24
```
-/
def neededfloatdigitsFloat64 : Nat := 24


/--
Julia source: base/ryu/Ryu.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
neededfloatdigits(::Type{Float32}) = 17
```
-/
def neededfloatdigitsFloat32 : Nat := 17


/--
Julia source: base/ryu/Ryu.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
neededfloatdigits(::Type{Float16}) = 20
```
-/
def neededfloatdigitsFloat16 : Nat := 20


/--
Julia source: base/ryu/Ryu.jl:48-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writeshortest(x::T,
        plus::Bool=false,
        space::Bool=false,
        hash::Bool=true,
        precision::Integer=-1,
        expchar::UInt8=UInt8('e'),
        padexp::Bool=false,
        decchar::UInt8=UInt8('.'),
        typed::Bool=false,
        compact::Bool=false) where {T <: Base.IEEEFloat}
    precision = Int(precision)
    precision >= -1 || throw(ArgumentError("precision must be at least -1"))
    bufsize = precision < 0 ? neededdigits(T) : Base.checked_add(precision, neededdigits(T))
    buf = Base.StringVector(bufsize)
    pos = writeshortest(buf, 1, x, plus, space, hash, precision, expchar, padexp, decchar, typed, compact)
    return String(resize!(buf, pos - 1))
end
```
-/
inductive RyuFloat where
  | float16 (value : Fl half)
  | float32 (value : Fl single)
  | float64 (value : JuliaLean.Float.F64)

def writeshortest (x : RyuFloat) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (typed compact : Bool) :
    JuliaLean.Jl (List Nat) :=
  match x with
  | .float16 value => writeshortestString16 value plus space hash precision expchar padexp decchar typed compact
  | .float32 value => writeshortestString32 value plus space hash precision expchar padexp decchar typed compact
  | .float64 value => writeshortestString64 value plus space hash precision expchar padexp decchar compact


/--
Julia source: base/ryu/Ryu.jl:82-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writefixed(x::T,
    precision::Integer,
    plus::Bool=false,
    space::Bool=false,
    hash::Bool=false,
    decchar::UInt8=UInt8('.'),
    trimtrailingzeros::Bool=false) where {T <: Base.IEEEFloat}
    precision = Int(precision)
    precision >= 0 || throw(ArgumentError("precision must be non-negative"))
    buf = Base.StringVector(Base.checked_add(precision, neededdigits(T)))
    pos = writefixed(buf, 1, x, precision, plus, space, hash, decchar, trimtrailingzeros)
    return String(resize!(buf, pos - 1))
end
```
-/
def writefixed (x : RyuFloat) (precision : Int) (plus space hash : Bool)
    (decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  match x with
  | .float16 value => writefixedString16 value precision plus space hash decchar trimtrailingzeros
  | .float32 value => writefixedString32 value precision plus space hash decchar trimtrailingzeros
  | .float64 value => writefixedString64 value precision plus space hash decchar trimtrailingzeros


/--
Julia source: base/ryu/Ryu.jl:113-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writeexp(x::T,
    precision::Integer,
    plus::Bool=false,
    space::Bool=false,
    hash::Bool=false,
    expchar::UInt8=UInt8('e'),
    decchar::UInt8=UInt8('.'),
    trimtrailingzeros::Bool=false) where {T <: Base.IEEEFloat}
    precision = Int(precision)
    precision >= 0 || throw(ArgumentError("precision must be non-negative"))
    buf = Base.StringVector(Base.checked_add(precision, neededdigits(T)))
    pos = writeexp(buf, 1, x, precision, plus, space, hash, expchar, decchar, trimtrailingzeros)
    return String(resize!(buf, pos - 1))
end
```
-/
def writeexp (x : RyuFloat) (precision : Int) (plus space hash : Bool)
    (expchar decchar : Nat) (trimtrailingzeros : Bool) : JuliaLean.Printf.Result (List Nat) :=
  match x with
  | .float16 value => writeexpString16 value precision plus space hash expchar decchar trimtrailingzeros
  | .float32 value => writeexpString32 value precision plus space hash expchar decchar trimtrailingzeros
  | .float64 value => writeexpString64 value precision plus space hash expchar decchar trimtrailingzeros


/--
Julia source: base/ryu/Ryu.jl:128-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, x::T, forceuntyped::Bool=false, fromprint::Bool=false) where {T <: Base.IEEEFloat}
    compact = get(io, :compact, false)::Bool
    buf = Memory{UInt8}(undef, neededfloatdigits(T))
    typed = !forceuntyped && !compact && Base.nonnothing_nonmissing_typeinfo(io) !== typeof(x)
    pos = writeshortest(buf, 1, x, false, false, true, -1,
        (x isa Float32 && !fromprint) ? UInt8('f') : UInt8('e'), false, UInt8('.'), typed, compact)
    write(io, view(buf, 1:pos - 1))
    return
end
```
-/
def baseShow (writeBytes : List Nat → JuliaLean.Jl Unit)
    (compact forceuntyped fromprint : Bool) (hasMatchingTypeInfo : Bool)
    (x : RyuFloat) : JuliaLean.Jl Unit :=
  match x with
  | .float16 value => show16 writeBytes compact forceuntyped fromprint hasMatchingTypeInfo value
  | .float32 value => show32 writeBytes compact forceuntyped fromprint hasMatchingTypeInfo value
  | .float64 value => show64 writeBytes compact value


/--
Julia source: base/ryu/Ryu.jl:138-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.string(x::T) where {T <: Base.IEEEFloat}
    buf = Base.StringVector(neededfloatdigits(T))
    pos = writeshortest(buf, 1, x, false, false, true, -1,
        UInt8('e'), false, UInt8('.'), false, false)
    return String(resize!(buf, pos - 1))
end
```
-/
def baseString (x : RyuFloat) : JuliaLean.Jl (List Nat) :=
  match x with
  | .float16 value => string16 value
  | .float32 value => string32 value
  | .float64 value => string64 value


/--
Julia source: base/ryu/Ryu.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.print(io::IO, x::Union{Float16, Float32}) = show(io, x, true, true)
```
-/
inductive RyuPrintFloat where
  | float16 (value : Fl half)
  | float32 (value : Fl single)

def basePrint (writeBytes : List Nat → JuliaLean.Jl Unit) (compact : Bool)
    (x : RyuPrintFloat) : JuliaLean.Jl Unit :=
  match x with
  | .float16 value => print16 writeBytes compact value
  | .float32 value => print32 writeBytes compact value

end JuliaLean.base.ryu.Ryu

namespace JuliaLean.MiscCov.RyuWrap

open JuliaLean.MiscCov
open JuliaLean.MiscCov.RyuUtils

/-- `neededdigits`, `base/ryu/Ryu.jl:16-18`. -/
def neededdigits : FT → Nat | .f64 => 309 + 17 | .f32 => 39 + 9 + 2 | .f16 => 9 + 5 + 9

/-- `neededfloatdigits`, `base/ryu/Ryu.jl:25-27`. -/
def neededfloatdigits : FT → Nat | .f64 => 24 | .f32 => 17 | .f16 => 20

structure ShortOpts where
  plus : Bool := false
  space : Bool := false
  hash : Bool := true
  expchar : Nat := 0x65
  padexp : Bool := false
  decchar : Nat := 0x2e
  typed : Bool := false
  compact : Bool := false
  deriving DecidableEq, Repr

structure FixedOpts where
  plus : Bool := false
  space : Bool := false
  hash : Bool := false
  expchar : Nat := 0x65
  decchar : Nat := 0x2e
  trim : Bool := false
  deriving DecidableEq, Repr

/-- A lower-level Ryu writer. It receives the allocated buffer size and returns
the buffer and Julia's one-past-the-end position. -/
abbrev Writer (X O : Type) := Nat → X → Int → O → List Nat × Nat

def finish (r : List Nat × Nat) : List Nat := r.1.take (r.2 - 1)

/-- `writeshortest(x, ...)`, `base/ryu/Ryu.jl:48-64`. -/
def writeshortest {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X)
    (precision : Int) (opts : ShortOpts := {}) : M (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else
    let size := if precision < 0 then neededdigits ft else precision.toNat + neededdigits ft
    .ok (finish (write size x precision opts))

/-- `writefixed(x, ...)`, `base/ryu/Ryu.jl:82-94`. -/
def writefixed {X : Type} (write : Writer X FixedOpts) (ft : FT) (x : X)
    (precision : Int) (opts : FixedOpts := {}) : M (List Nat) :=
  if precision < 0 then .error (.argumentError "precision must be non-negative")
  else .ok (finish (write (precision.toNat + neededdigits ft) x precision opts))

/-- `writeexp(x, ...)`, `base/ryu/Ryu.jl:113-126`. -/
def writeexp {X : Type} (write : Writer X FixedOpts) (ft : FT) (x : X)
    (precision : Int) (opts : FixedOpts := {}) : M (List Nat) :=
  if precision < 0 then .error (.argumentError "precision must be non-negative")
  else .ok (finish (write (precision.toNat + neededdigits ft) x precision opts))

/-- `Base.show(io, x, forceuntyped, fromprint)`, `base/ryu/Ryu.jl:128-136`.
The result is the bytes written to `io`. -/
def showFloat {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X)
    (compact forceuntyped fromprint typeinfoSame isF32 : Bool) : List Nat :=
  let typed := !forceuntyped && !compact && !typeinfoSame
  let expchar := if isF32 && !fromprint then 0x66 else 0x65
  finish (write (neededfloatdigits ft) x (-1)
    { hash := true, expchar := expchar, typed := typed, compact := compact })

/-- `Base.string(x)`, `base/ryu/Ryu.jl:138-143`. -/
def stringFloat {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X) : List Nat :=
  finish (write (neededfloatdigits ft) x (-1) {})

/-- `Base.print(io, x::Union{Float16,Float32})`, `base/ryu/Ryu.jl:145`. -/
def printFloat {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X)
    (compact typeinfoSame isF32 : Bool) : List Nat :=
  showFloat write ft x compact true true typeinfoSame isF32
end JuliaLean.MiscCov.RyuWrap

namespace JuliaLean.ParsePrint.Ryu

open JuliaLean JuliaLean.Float JuliaLean.ParsePrint
/-- `base/ryu/Ryu.jl:138-143`: `string(x::Float64)`. -/
def string (x : F64) : List Nat := writeshortest x false false true (-1) chE false chDot false

/-- `base/ryu/Ryu.jl:128-136`: `show(io, x::Float64)`, with `compact = get(io, :compact, false)`. -/
def showFloat (compact : Bool) (x : F64) : List Nat :=
  writeshortest x false false true (-1) chE false chDot compact

end JuliaLean.ParsePrint.Ryu
