import JuliaLean.Float.Properties

/-!
Exact, kernel-computable Float64 API for float ranges and twice-precision models.

`F64 := BitVec 64`; `F64.ofBits : Nat → F64` and `F64.toBits : F64 → Nat`
reinterpret storage. `F64.toRat : F64 → Int × Nat` gives exact finite values;
the denominator is zero for nonfinite inputs. `F64.roundRat : Int → Nat → Bool → F64`
rounds nearest, ties even, with the final argument supplying the sign of exact zero.
Use the named `F64` arithmetic and comparison functions: Lean's inherited
`BitVec` operators act on storage bits, rather than floating-point values.

Arithmetic: `F64.add/sub/mul/div : F64 → F64 → F64`,
`F64.fma/muladd : F64 → F64 → F64 → F64`, `F64.sqrt : F64 → Jl F64`.
`muladd` fixes the fused interpretation permitted by Julia's compiler.
`neg/abs`, `eq/lt/le/isequal/isless`, and classification are in namespace `F64`.
Bit-only operations preserve NaN payloads; arithmetic NaNs should be compared
with `isnan`, because LLVM permits target-dependent payload selection.

Range helpers: `F64.nextfloat/prevfloat : F64 → Int → F64` (step defaults to 1),
`F64.ldexp : F64 → Int → F64`, `F64.exponent : F64 → Jl Int`,
`F64.significand : F64 → F64`, `F64.frexp : F64 → F64 × Int`, and `F64.eps`.
`floatmin/floatmax` are constants. `F64.ofJInt : JInt t → F64` mirrors Julia's
integer conversion branches. `F64.int/truncInt/floorInt/ceilInt` take an `IntTy`
and an `F64`, returning `Jl (JInt t)`; `roundInt` additionally takes `Rounding`.
`F64.round : F64 → Rounding → F64` defaults to nearest ties even.
`F64.rem/mod/divInteger/fld/cld` model Julia's float quotient and remainder
algorithms, including intermediate floating-point rounding.
The `Release` suffix variants return `Jl F64` and preserve Julia 1.13.2's
subtraction-before-division algorithm and missing ties-away remainder method.

`JuliaLean.Float.Validation.differential` prints a deterministic 2,194-input
bit-pattern corpus for every operation. The model assumes default nearest-even
arithmetic and gradual underflow. Registry properties are in `Float.Properties`.
-/

namespace JuliaLean.Float

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := propertyEntries

end JuliaLean.Float
