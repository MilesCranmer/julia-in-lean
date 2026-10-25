import JuliaLean.Float.Extras

/-!
Shared helpers for the `base/math.jl` and `base/special/*.jl` models, Julia master
`bbfa0ce4150`. Floating-point values are `JuliaLean.Float.F64`; all arithmetic uses
the named `F64` operations. Fixed-width integer intermediates use `JInt`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

deriving instance DecidableEq for Except

/-- `reinterpret(UInt64, x)`. -/
def bitsOf (x : F64) : Nat := F64.toBits x

/-- `reinterpret(Float64, u)` for a UInt64 value, reducing modulo 2^64. -/
def ofBitsU (u : Nat) : F64 := F64.ofBits (u % 2^64)

/-- `reinterpret(Int64, x)`. -/
def toInt64 (x : F64) : Int :=
  let b := F64.toBits x
  if b ≥ 2^63 then (b : Int) - 2^64 else (b : Int)

/-- `reinterpret(Float64, i)` for an Int64 value, reducing modulo 2^64. -/
def ofInt64 (i : Int) : F64 := F64.ofBits (i % 2^64).toNat

/-- A Float64 literal given by its bit pattern. -/
def lit (u : Nat) : F64 := F64.ofBits u

/-- `copysign_float`; `base/floatfuncs.jl:5`. -/
def copysign (x y : F64) : F64 :=
  F64.ofBits (F64.toBits x % 2^63 + (if F64.signbit y then 2^63 else 0))

/-- `flipsign(x::Float64, y::Float64)`: xor with the sign of `y`; `base/floatfuncs.jl:10`. -/
def flipsign (x y : F64) : F64 := if F64.signbit y then F64.neg x else x

/-- `two_mul(x::Float64, y::Float64)` with hardware fma; `base/floatfuncs.jl:376-380`. -/
def twoMul (x y : F64) : F64 × F64 :=
  let xy := F64.mul x y
  (xy, F64.fma x y (F64.neg xy))

/-- `canonicalize2(big, little)`; `base/twiceprecision.jl:48-51`. -/
def canonicalize2 (big little : F64) : F64 × F64 :=
  let h := F64.add big little
  (h, F64.add (F64.sub big h) little)

/-- Horner loop of `evalpoly(x, p::Tuple)` for a nonempty coefficient list: start from
`p[end]`, then `muladd(x, ex, p[i])` for `i = N-1:-1:1`; `base/math.jl:75-86`. -/
def horner (x : F64) : List F64 → F64
  | [] => F64.zero
  | [c] => c
  | c :: cs => F64.muladd x (horner x cs) c

/-- `evalpoly(x::Float64, p)` for a tuple or vector `p`; an empty `p` makes `p[end]`
throw `BoundsError`; `base/math.jl:75-98`. -/
def evalpoly (x : F64) (p : List F64) : Jl F64 :=
  if p.isEmpty then .error .boundsError else .ok (horner x p)

end JuliaLean.MathFuncs
