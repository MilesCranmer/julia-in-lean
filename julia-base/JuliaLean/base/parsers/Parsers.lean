import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int

/-!
# Model of `base/parsers/Parsers.jl`

The `Base.Parsers` module of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`: the
`ParseFailure` values that `parsevalue` returns instead of throwing. The integer and float
parsers are modelled in `JuliaLean.base.parsers.ints` and `JuliaLean.base.parsers.floats`.
-/

namespace JuliaLean.base.parsers.Parsers

open JuliaLean
open JuliaLean.base.io (M)

-- Reason: The module declaration, its docstring and its imports are load-time structure.
-- UNTRANSLATED
-- Source: base/parsers/Parsers.jl:1-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     Base.Parsers
-- 
-- Parsing values from bytes. [`parsevalue`](@ref Base.Parsers.parsevalue) parses a value from
-- all of a byte vector and returns a [`ParseFailure`](@ref Base.Parsers.ParseFailure) instead
-- of throwing, for callers that already know where a field starts and ends. [`parse`](@ref)
-- and [`tryparse`](@ref) are built on the same code.
-- """
-- module Parsers
-- 
-- using ..Base: BitInteger, CodeUnits, DenseUTF8String, FastContiguousSubArray, IEEEFloat,
--     exponent_bias, exponent_raw_max, require_one_based_indexing, significand_bits, uinttype
-- using ..Base.Checked: add_with_overflow, mul_with_overflow
-- 
-- /Source

/--
Julia source: base/parsers/Parsers.jl:17-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Parsers.ParseFailure

Returned by [`parsevalue`](@ref Base.Parsers.parsevalue) instead of a value. It is
[`INVALID`](@ref Base.Parsers.INVALID), [`OVERFLOW`](@ref Base.Parsers.OVERFLOW) or
[`UNDERFLOW`](@ref Base.Parsers.UNDERFLOW); more kinds may be added, so check
`x isa ParseFailure` to test for any failure.
"""
struct ParseFailure
    kind::UInt8
end

```
-/
structure ParseFailure where
  kind : JInt .u8
  deriving DecidableEq

/-- A `Union{T, ParseFailure}` result. -/
inductive ParseResult (α : Type) where
  | value (x : α)
  | failure (f : ParseFailure)

/--
Julia source: base/parsers/Parsers.jl:29-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Parsers.INVALID

The [`ParseFailure`](@ref Base.Parsers.ParseFailure) for bytes that are not a valid value.
"""
const INVALID = ParseFailure(0x00)

```
-/
def INVALID : ParseFailure := ⟨JInt.lit .u8 0x00⟩

/--
Julia source: base/parsers/Parsers.jl:36-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Parsers.OVERFLOW

The [`ParseFailure`](@ref Base.Parsers.ParseFailure) for a well-formed value too large in
magnitude for the type.
"""
const OVERFLOW = ParseFailure(0x01)

```
-/
def OVERFLOW : ParseFailure := ⟨JInt.lit .u8 0x01⟩

/--
Julia source: base/parsers/Parsers.jl:44-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Parsers.UNDERFLOW

The [`ParseFailure`](@ref Base.Parsers.ParseFailure) for a nonzero floating-point value that
rounds to zero in the type.
"""
const UNDERFLOW = ParseFailure(0x02)

```
-/
def UNDERFLOW : ParseFailure := ⟨JInt.lit .u8 0x02⟩

/--
Julia source: base/parsers/Parsers.jl:52-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.show(io::IO, x::ParseFailure) =
    print(io, "Base.Parsers.", ("INVALID", "OVERFLOW", "UNDERFLOW")[x.kind + 1])

```
-/
def showParseFailure {World IO : Type} (print : IO → String → M World Unit) (io : IO)
    (x : ParseFailure) : M World Unit := do
  let names := ["INVALID", "OVERFLOW", "UNDERFLOW"]
  let index := (JuliaLean.base.int.add x.kind (JInt.lit .u8 1)).val
  let name ← match (if index ≥ 1 then names[(index - 1).toNat]? else none) with
    | some name => pure name
    | none => throw (.jl .boundsError)
  print io "Base.Parsers."
  print io name

-- Reason: The docstring attaches to `function parsevalue end`, which declares the generic function; its methods, included from `ints.jl` and `floats.jl`, are modelled in those files. The `include`s and the module end are load-time structure.
-- UNTRANSLATED
-- Source: base/parsers/Parsers.jl:55-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Base.Parsers.parsevalue(T, bytes; kw...) -> Union{T, ParseFailure}
-- 
-- Parse all of `bytes`, a one-based `AbstractVector{UInt8}`, as a `T`, or return a
-- [`ParseFailure`](@ref Base.Parsers.ParseFailure) instead of throwing. Pass a view, such as
-- `view(buf, i:j)`, to parse part of a buffer.
-- 
-- For integer types, the bytes are an optional `-` or `+` (signed types only) followed by
-- digits in `base` (keyword, 2 to 62, default 10), with letters for digits above 9 as in
-- [`parse`](@ref).
-- 
-- For `Float64`, `Float32` and `Float16`, the bytes are a number as [`parse`](@ref) reads it,
-- without surrounding whitespace: an optional sign and a decimal or hexadecimal
-- floating-point number, or `inf`, `infinity` or `nan` in any case. A number is rounded to
-- the nearest value, ties to even; one too large for the type is `OVERFLOW`, and a nonzero
-- one that rounds to zero is `UNDERFLOW`. `nan(n)` puts the unsigned integer `n` (decimal,
-- `0x` hexadecimal or `0` octal) in the NaN's payload.
-- 
-- For `UUID`, the bytes are 32 hexadecimal digits in groups of 8, 4, 4, 4 and 12 separated
-- by `-`, as [`string`](@ref) writes them, in either case.
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.Parsers.parsevalue(Int, codeunits("-42"))
-- -42
-- 
-- julia> Base.Parsers.parsevalue(UInt8, view(codeunits("x=256;"), 3:5))
-- Base.Parsers.OVERFLOW
-- 
-- julia> Base.Parsers.parsevalue(Int, UInt8[0x37, 0x66]; base = 16)
-- 127
-- 
-- julia> Base.Parsers.parsevalue(Float64, codeunits("-1.5e-3"))
-- -0.0015
-- ```
-- """
-- function parsevalue end
-- 
-- include("parsers/ints.jl")
-- include("parsers/floats.jl")
-- 
-- end # module Parsers
-- /Source

end JuliaLean.base.parsers.Parsers


namespace JuliaLean.MiscCov.Parsers

open JuliaLean.MiscCov

inductive Failure where
  | invalid | overflow | underflow
  deriving DecidableEq, Repr

inductive Result where
  | failure (f : Failure)
  | value (n : Int)
  deriving DecidableEq, Repr

/-- `Base.show(io, x::ParseFailure)`, `base/parsers/Parsers.jl:52-53`. -/
def showFailure : Failure → String
  | .invalid => "Base.Parsers.INVALID"
  | .overflow => "Base.Parsers.OVERFLOW"
  | .underflow => "Base.Parsers.UNDERFLOW"

end JuliaLean.MiscCov.Parsers

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean

/-- A `ParseFailure` or a value, `base/parsers/Parsers.jl:25-50`. -/
inductive PR (t : IntTy) where
  | val (v : JInt t)
  | invalid
  | overflow
  deriving DecidableEq, Repr

end JuliaLean.ParsePrint.IntParse
