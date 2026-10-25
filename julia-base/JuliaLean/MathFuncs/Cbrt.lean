import JuliaLean.MathFuncs.Prelude

/-!
`cbrt(::Float64)` from `base/special/cbrt.jl`, Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `highword(x::Float64) = (reinterpret(UInt64, x) >>> 32) % UInt32`; `base/math.jl:1275-1276`. -/
private def highword (x : F64) : Nat := bitsOf x / 2^32

/-- `fromhighword(Float64, u) = reinterpret(Float64, UInt64(u) << 32)`; `base/math.jl:1279`. -/
private def fromhighword (u : Nat) : F64 := ofBitsU (u * 2^32)

/-- `floor(UInt32, y)` for finite `0 ≤ y < 2^32`; `base/special/cbrt.jl:70,76`. -/
private def floorU32 (y : F64) : Nat :=
  let q := F64.toRat y
  (q.1 / (q.2 : Int)).toNat

/-- `_approx_cbrt(x::Float64)`; `base/special/cbrt.jl:63-79`. -/
def approxCbrt (x : F64) : F64 :=
  let adj := F64.sub (F64.div (F64.ofInt (1023 * 2)) (F64.ofInt 3)) (lit 0x3fa0ed8c97e0d750)
  let e2k := F64.ofInt (2^20)
  let u := highword x % 2^31
  if u ≥ highword F64.floatmin then
    let v := (u / 3 + floorU32 (F64.mul adj e2k)) % 2^32
    copysign (fromhighword v) x
  else
    let x := F64.mul x (lit 0x4340000000000000)
    let adj := F64.sub adj (F64.div (F64.ofInt 53) (F64.ofInt 3))
    let u := highword x % 2^31
    let v := (u / 3 + floorU32 (F64.mul adj e2k)) % 2^32
    copysign (fromhighword v) x

/-- `_improve_cbrt(x::Float64, t::Float64)`; `base/special/cbrt.jl:103-142`. -/
def improveCbrt (x t : F64) : F64 :=
  let r := F64.mul (F64.mul t t) (F64.div t x)
  let p := horner r [lit 0x3ffe03e60f61e692, lit 0xbffe28e092f02420, lit 0x3ff9f1604a49d6c2]
  let q := horner r [lit 0xbfe844cbbee751d9, lit 0x3fc2b000d4e4edd7]
  let t := F64.mul t (F64.add p (F64.mul (F64.mul (F64.mul r r) r) q))
  let u := ((bitsOf t + 0x80000000) % 2^64) &&& 0xffffffffc0000000
  let t := ofBitsU u
  let s := F64.mul t t
  let r := F64.div x s
  let w := F64.add t t
  let r := F64.div (F64.sub r t) (F64.add w r)
  F64.muladd t r t

/-- `cbrt(x::Float64)`; `base/special/cbrt.jl:144-150`. -/
def cbrt (x : F64) : F64 :=
  if !F64.isfinite x || F64.iszero x then x
  else improveCbrt x (approxCbrt x)

end JuliaLean.MathFuncs
