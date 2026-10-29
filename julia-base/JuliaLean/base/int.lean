import JuliaLean.Core
import JuliaLean.src.runtime_intrinsics_c

/-!
# Model of `base/int.jl`

Typed model of every method of `base/int.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform (`Int === Int64`). Each method is a Lean definition whose docstring carries
the method's verbatim source; its body follows the Julia body call by call.

* BitInteger values are `JInt t` (`JuliaLean.Core`), `Bool` is Lean `Bool` and IEEE floats are
  `JuliaLean.Promotion.Fl`. BitInteger methods cover every width `t : IntTy`.
  `Generic` methods accept arbitrary Integer, Signed and Unsigned types through typed callees;
  the existing JInt names instantiate those methods with BitInteger operations.
* Intrinsics (`add_int`, `checked_sdiv_int`, `ctlz_int`, ...) are the C runtime models of
  `JuliaLean.src.runtime_intrinsics_c` applied to a value's bit pattern (`fromJInt`/`toJInt`).
* Julia's dispatch is trusted. Definitions marked *dispatch* select, for BitInteger argument
  types, the method Julia selects; they are not models of Julia code.
* Calls into functions defined later in Julia's load order (`fld`, `div(a, b)` and `divrem` of
  `base/div.jl`, `float`, value-level `widen`, `parse`, `tryparse`) and calls whose argument is
  of an abstract, user-extensible type are function parameters.
* The `Callees` section gives the earlier-file methods (`boot.jl` constructors and `convert`,
  same-signedness `promote` of `promotion.jl`, `zero`, `oftype`, `ifelse`) that int.jl's
  methods call on BitInteger arguments.
-/

namespace JuliaLean.base.int

open JuliaLean JuliaLean.C JuliaLean.Promotion

inductive UnionBottom where
  | type
  deriving DecidableEq

inductive InvalidFunction where
  | signed | rem | mod | unsafeTrunc | typemin | typemax
  deriving DecidableEq

structure InvalidMethodError (Args : Type) where
  function : InvalidFunction
  arguments : Args

/-! ## Intrinsics on BitInteger values -/

/-- `neg_int`. -/
def neg_int {t : IntTy} (x : JInt t) : JInt t := toJInt t (jlNegInt (fromJInt x))
/-- `not_int`. -/
def not_int {t : IntTy} (x : JInt t) : JInt t := toJInt t (jlNotInt (fromJInt x))
/-- `add_int`. -/
def add_int {t : IntTy} (x y : JInt t) : JInt t := toJInt t (jlAddInt (fromJInt x) (fromJInt y))
/-- `sub_int`. -/
def sub_int {t : IntTy} (x y : JInt t) : JInt t := toJInt t (jlSubInt (fromJInt x) (fromJInt y))
/-- `mul_int`. -/
def mul_int {t : IntTy} (x y : JInt t) : JInt t := toJInt t (jlMulInt (fromJInt x) (fromJInt y))
/-- `and_int`. -/
def and_int {t : IntTy} (x y : JInt t) : JInt t := toJInt t (jlAndInt (fromJInt x) (fromJInt y))
/-- `or_int`. -/
def or_int {t : IntTy} (x y : JInt t) : JInt t := toJInt t (jlOrInt (fromJInt x) (fromJInt y))
/-- `xor_int`. -/
def xor_int {t : IntTy} (x y : JInt t) : JInt t := toJInt t (jlXorInt (fromJInt x) (fromJInt y))
/-- `eq_int`. -/
def eq_int {t : IntTy} (x y : JInt t) : Bool := jlEqInt (fromJInt x) (fromJInt y)
/-- `slt_int`. -/
def slt_int {t : IntTy} (x y : JInt t) : Bool := jlSltInt (fromJInt x) (fromJInt y)
/-- `sle_int`. -/
def sle_int {t : IntTy} (x y : JInt t) : Bool := jlSleInt (fromJInt x) (fromJInt y)
/-- `ult_int`. -/
def ult_int {t : IntTy} (x y : JInt t) : Bool := jlUltInt (fromJInt x) (fromJInt y)
/-- `ule_int`. -/
def ule_int {t : IntTy} (x y : JInt t) : Bool := jlUleInt (fromJInt x) (fromJInt y)
/-- `flipsign_int`. -/
def flipsign_int {t : IntTy} (x y : JInt t) : JInt t :=
  toJInt t (jlFlipsignInt (fromJInt x) (fromJInt y))

/-- The checked division intrinsics throw nothing but `DivideError`. -/
theorem integerDivide_checked_error {w : Nat} (s r : Bool) (a b : BitVec w) (e : IntrinsicError)
    (h : integerDivide s r true a b = .error e) : e = .divideError := by
  unfold integerDivide at h
  simp only [Bool.true_or] at h
  by_cases h0 : ((if s = true then b.toInt else (b.toNat : Int)) == 0) = true
  · simp only [h0, ite_true] at h
    cases h
    rfl
  · simp only [h0] at h
    by_cases h1 : (s && (if s = true then a.toInt else (a.toNat : Int)) == -((2 ^ (w - 1) : Nat) : Int) &&
        (if s = true then b.toInt else (b.toNat : Int)) == -1) = true
    · simp only [h1] at h
      cases r <;> simp [pure, Except.pure] at h
      cases h
      rfl
    · simp only [h1] at h
      simp [pure, Except.pure] at h

/-- A checked division intrinsic result; by `integerDivide_checked_error` every error is a
`DivideError`. -/
def divideResult (t : IntTy) (r : IntrinsicResult (BitVec t.bits)) : Jl (JInt t) :=
  match r with
  | .ok b => .ok (toJInt t b)
  | .error _ => .error .divideError

/-- `checked_sdiv_int`. -/
def checked_sdiv_int {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  divideResult t (jlCheckedSdivInt (fromJInt x) (fromJInt y))
/-- `checked_srem_int`. -/
def checked_srem_int {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  divideResult t (jlCheckedSremInt (fromJInt x) (fromJInt y))
/-- `checked_udiv_int`. -/
def checked_udiv_int {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  divideResult t (jlCheckedUdivInt (fromJInt x) (fromJInt y))
/-- `checked_urem_int`. -/
def checked_urem_int {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  divideResult t (jlCheckedUremInt (fromJInt x) (fromJInt y))

/-- `shl_int` with a shift count of any BitInteger type. -/
def shl_int {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t :=
  toJInt t (jlShlInt (fromJInt x) (fromJInt y))
/-- `lshr_int`. -/
def lshr_int {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t :=
  toJInt t (jlLshrInt (fromJInt x) (fromJInt y))
/-- `ashr_int`. -/
def ashr_int {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t :=
  toJInt t (jlAshrInt (fromJInt x) (fromJInt y))
/-- `ctpop_int`. -/
def ctpop_int {t : IntTy} (x : JInt t) : JInt t := toJInt t (jlCtpopInt (fromJInt x))
/-- `ctlz_int`. -/
def ctlz_int {t : IntTy} (x : JInt t) : JInt t := toJInt t (jlCtlzInt (fromJInt x))
/-- `cttz_int`. -/
def cttz_int {t : IntTy} (x : JInt t) : JInt t := toJInt t (jlCttzInt (fromJInt x))

/-- The value of an intrinsic call that cannot fail on its arguments. -/
def okOf {ε α : Type} (r : Except ε α) (h : ∀ e, r ≠ .error e) : α :=
  match r, h with
  | .ok a, _ => a
  | .error e, h => absurd rfl (h e)

/-- `bswap_int`, which requires a bit size that is a multiple of 16. -/
def bswap_int {t : IntTy} (x : JInt t) (h : t.bits % 16 = 0) : JInt t :=
  toJInt t (okOf (jlBswapInt (fromJInt x)) (by intro e he; simp [jlBswapInt, h, pure, Except.pure] at he))
/-- `trunc_int(T, x)`, defined for a narrower `T`. -/
def trunc_int (T : IntTy) {t : IntTy} (x : JInt t) (h : T.bits < t.bits) : JInt T :=
  toJInt T (okOf (jlTruncInt T.bits (fromJInt x))
    (by intro e he; simp [jlTruncInt, Nat.not_le.mpr h, pure, Except.pure] at he))
/-- `sext_int(T, x)`, defined for a wider `T`. -/
def sext_int (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits < T.bits) : JInt T :=
  toJInt T (okOf (jlSextInt T.bits (fromJInt x))
    (by intro e he; simp [jlSextInt, Nat.not_le.mpr h, pure, Except.pure] at he))
/-- `zext_int(T, x)`, defined for a wider `T`. -/
def zext_int (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits < T.bits) : JInt T :=
  toJInt T (okOf (jlZextInt T.bits (fromJInt x))
    (by intro e he; simp [jlZextInt, Nat.not_le.mpr h, pure, Except.pure] at he))
/-- `bitcast(T, x)` between BitInteger types of the same size. -/
def bitcast (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits = T.bits) : JInt T :=
  toJInt T (BitVec.cast h (jlBitcast (fromJInt x)))
/-- `bitcast(T, y)` of a float to the BitInteger type of its size: the stored bits. -/
def bitcastFloat (T : IntTy) {f : Fmt} (y : Fl f) : JInt T :=
  toJInt T (jlBitcast (BitVec.ofNat T.bits y.toBits))

/-! ## Callees from earlier Base files, on BitInteger arguments -/

/-- A literal or a constant of type `t` whose value is representable in `t`, e.g. `T(0)`,
`Int8(-128)`, an `Int` literal. -/
def lit (t : IntTy) (z : Int) : JInt t := JInt.wrap t z

/-- `Core.sizeof(T)` in bytes. -/
def sizeofT (t : IntTy) : Nat := t.bits / 8

/-- `sizeof(x)`, an `Int`. -/
def sizeof {t : IntTy} (_x : JInt t) : JInt .i64 := lit .i64 (sizeofT t)

theorem bits_lt_of_sizeofT_lt {a b : IntTy} (h : sizeofT a < sizeofT b) : a.bits < b.bits := by
  cases a <;> cases b <;> simp_all [sizeofT, IntTy.bits]

theorem bits_eq_of_sizeofT {a b : IntTy} (h1 : ¬ sizeofT a < sizeofT b)
    (h2 : ¬ sizeofT b < sizeofT a) : b.bits = a.bits := by
  cases a <;> cases b <;> simp_all [sizeofT, IntTy.bits]

/-- `convert(T, x)` / `T(x)` between BitInteger types (`boot.jl` `toInt8` … `toUInt128`):
the same value, or `InexactError` when `T` cannot represent it. -/
def convert (T : IntTy) {S : IntTy} (x : JInt S) : Jl (JInt T) := JInt.convert T x.val

/-- `T(x)` / `convert(T, x)` / `oftype` when `x`'s type is unsigned or has `T`'s signedness and
`T` is at least as wide: `boot.jl` selects `zext_int`, `sext_int` or the identity, which keep
the value and never throw. -/
def widenTo (T : IntTy) {S : IntTy} (x : JInt S) : JInt T := lit T x.val

/-- `convert(T, b::Bool)` / `oftype(x, b)` (`boot.jl` `toInt8(x::Bool) = bitcast(Int8, x)`,
`toInt16(x::Bool) = zext_int(Int16, x)`, ...). -/
def ofBool (T : IntTy) (b : Bool) : JInt T := lit T (if b then 1 else 0)

/-- `zero(x)` (`number.jl`: `oftype(x, 0)`). -/
def zero {t : IntTy} (_x : JInt t) : JInt t := lit t 0

/-- `promote(x, y)` (`promotion.jl:397-401,423-428`) for two BitIntegers of the same
signedness: both are converted to `promote_type`, which widens and never throws. -/
def promoteSameSign {S T : IntTy} (x : JInt S) (y : JInt T) :
    JInt (S.promote T) × JInt (S.promote T) :=
  (widenTo _ x, widenTo _ y)

/-- `ifelse(c, x, y)` (`essentials.jl:894`): both arguments are already evaluated. -/
def ifelse {α : Type} (c : Bool) (x y : α) : α := if c then x else y

namespace Generic

/--
Julia source: base/int.jl:97-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
negate(x::Unsigned) = -convert(Signed, x)
#widenegate(x) = -convert(widen(signed(typeof(x))), x)
```
-/
def negate_Unsigned {U S : Type} (convert : U → Jl S) (neg : S → S) (x : U) : Jl S := do
  let s ← convert x
  pure (neg s)

/--
Julia source: base/int.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Integer) = x < 0
```
-/
def signbit_Integer {I : Type} (lt : I → Int → Bool) (x : I) : Bool := lt x 0

/--
Julia source: base/int.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Unsigned) = false
```
-/
def signbit_Unsigned {U : Type} (_x : U) : Bool := false

/--
Julia source: base/int.jl:185-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

isnegative(x::Unsigned) = false
```
-/
def isnegative_Unsigned {U : Type} (_x : U) : Bool := false

/--
Julia source: base/int.jl:191-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Float16) = flipsign(x, bitcast(Int16, y))
```
-/
def flipsign_Float16 {S : Type} (flipsign : S → JInt .i16 → S) (x : S) (y : Fl half) : S :=
  flipsign x (bitcastFloat .i16 y)

/--
Julia source: base/int.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Float32) = flipsign(x, bitcast(Int32, y))
```
-/
def flipsign_Float32 {S : Type} (flipsign : S → JInt .i32 → S) (x : S) (y : Fl single) : S :=
  flipsign x (bitcastFloat .i32 y)

/--
Julia source: base/int.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Float64) = flipsign(x, bitcast(Int64, y))
```
-/
def flipsign_Float64 {S : Type} (flipsign : S → JInt .i64 → S) (x : S) (y : Fl double) : S :=
  flipsign x (bitcastFloat .i64 y)

/--
Julia source: base/int.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Real)    = flipsign(x, -oftype(x, signbit(y)))
```
-/
def flipsign_Real {S R : Type} (signbit : R → Bool) (oftype : S → Bool → S)
    (neg : S → S) (flipsign : S → S → S) (x : S) (y : R) : S :=
  flipsign x (neg (oftype x (signbit y)))

/--
Julia source: base/int.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Signed)  = flipsign(x, x ⊻ y)
```
-/
def copysign_Signed {S T R : Type} (xor : S → T → R) (flipsign : S → R → S)
    (x : S) (y : T) : S := flipsign x (xor x y)

/--
Julia source: base/int.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Float16) = copysign(x, bitcast(Int16, y))
```
-/
def copysign_Float16 {S : Type} (copysign : S → JInt .i16 → S) (x : S) (y : Fl half) : S :=
  copysign x (bitcastFloat .i16 y)

/--
Julia source: base/int.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Float32) = copysign(x, bitcast(Int32, y))
```
-/
def copysign_Float32 {S : Type} (copysign : S → JInt .i32 → S) (x : S) (y : Fl single) : S :=
  copysign x (bitcastFloat .i32 y)

/--
Julia source: base/int.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Float64) = copysign(x, bitcast(Int64, y))
```
-/
def copysign_Float64 {S : Type} (copysign : S → JInt .i64 → S) (x : S) (y : Fl double) : S :=
  copysign x (bitcastFloat .i64 y)

/--
Julia source: base/int.jl:200-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Real)    = copysign(x, -oftype(x, signbit(y)))

```
-/
def copysign_Real {S R : Type} (signbit : R → Bool) (oftype : S → Bool → S)
    (neg : S → S) (copysign : S → S → S) (x : S) (y : R) : S :=
  copysign x (neg (oftype x (signbit y)))

/--
Julia source: base/int.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::Unsigned) = x
```
-/
def abs_Unsigned {U : Type} (x : U) : U := x

/--
Julia source: base/int.jl:234-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::Signed) = flipsign(x,x)

```
-/
def abs_Signed {S : Type} (flipsign : S → S → S) (x : S) : S := flipsign x x

/--
Julia source: base/int.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x) = x % typeof(convert(Unsigned, zero(x)))
```
-/
def unsigned {I Z U Ty : Type} (zero : I → Z) (convert : Z → U) (typeof : U → Ty)
    (rem : I → Ty → U) (x : I) : U := rem x (typeof (convert (zero x)))

/--
Julia source: base/int.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x::BitSigned) = reinterpret(typeof(convert(Unsigned, zero(x))), x)
```
-/
def unsigned_BitSigned {s : IntTy} {Z U Ty : Type} (zero : JInt s → Z)
    (convert : Z → U) (typeof : U → Ty) (reinterpret : Ty → JInt s → U) (x : JInt s) : U :=
  reinterpret (typeof (convert (zero x))) x

/--
Julia source: base/int.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(x) = x % typeof(convert(Signed, zero(x)))
```
-/
def signed {I Z S Ty : Type} (zero : I → Z) (convert : Z → S) (typeof : S → Ty)
    (rem : I → Ty → S) (x : I) : S := rem x (typeof (convert (zero x)))

/--
Julia source: base/int.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(x::BitUnsigned) = reinterpret(typeof(convert(Signed, zero(x))), x)
```
-/
def signed_BitUnsigned {u : IntTy} {Z S Ty : Type} (zero : JInt u → Z)
    (convert : Z → S) (typeof : S → Ty) (reinterpret : Ty → JInt u → S) (x : JInt u) : S :=
  reinterpret (typeof (convert (zero x))) x

/--
Julia source: base/int.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::BitSigned, y::Unsigned) = flipsign(signed(div(unsigned(abs(x)), y)), x)
```
-/
def div_BitSigned_Unsigned {s : IntTy} {U A Q S : Type} (abs : JInt s → JInt s)
    (unsigned : JInt s → A) (div : A → U → Jl Q) (signed : Q → S)
    (flipsign : S → JInt s → S) (x : JInt s) (y : U) : Jl S := do
  let q ← div (unsigned (abs x)) y
  pure (flipsign (signed q) x)

/--
Julia source: base/int.jl:276-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::Unsigned, y::BitSigned) = unsigned(flipsign(signed(div(x, unsigned(abs(y)))), y))
```
-/
def div_Unsigned_BitSigned {s : IntTy} {U A Q S R : Type} (abs : JInt s → JInt s)
    (unsignedArg : JInt s → A) (div : U → A → Jl Q) (signed : Q → S)
    (flipsign : S → JInt s → S) (unsignedResult : S → R) (x : U) (y : JInt s) : Jl R := do
  let q ← div x (unsignedArg (abs y))
  pure (unsignedResult (flipsign (signed q) y))

/--
Julia source: base/int.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::BitSigned, y::Unsigned) = flipsign(signed(rem(unsigned(abs(x)), y)), x)
```
-/
def rem_BitSigned_Unsigned {s : IntTy} {U A Q S : Type} (abs : JInt s → JInt s)
    (unsigned : JInt s → A) (rem : A → U → Jl Q) (signed : Q → S)
    (flipsign : S → JInt s → S) (x : JInt s) (y : U) : Jl S := do
  let r ← rem (unsigned (abs x)) y
  pure (flipsign (signed r) x)

/--
Julia source: base/int.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Unsigned, y::BitSigned) = rem(x, unsigned(abs(y)))
```
-/
def rem_Unsigned_BitSigned {s : IntTy} {U A R : Type} (abs : JInt s → JInt s)
    (unsigned : JInt s → A) (rem : U → A → Jl R) (x : U) (y : JInt s) : Jl R :=
  rem x (unsigned (abs y))

/--
Julia source: base/int.jl:281-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x::BitSigned, y::Unsigned)
    q, r = divrem(unsigned(abs(x)), y)
    flipsign(signed(q), x), flipsign(signed(r), x)
end

```
-/
def divrem_BitSigned_Unsigned {s : IntTy} {U A Q S : Type} (abs : JInt s → JInt s)
    (unsigned : JInt s → A) (divrem : A → U → Jl (Q × Q)) (signed : Q → S)
    (flipsign : S → JInt s → S) (x : JInt s) (y : U) : Jl (S × S) := do
  let (q, r) ← divrem (unsigned (abs x)) y
  pure (flipsign (signed q) x, flipsign (signed r) x)

/--
Julia source: base/int.jl:286-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x::Unsigned, y::BitSigned)
    q, r = divrem(x, unsigned(abs(y)))
    unsigned(flipsign(signed(q), y)), r
end

```
-/
def divrem_Unsigned_BitSigned {s : IntTy} {U A Q S R : Type} (abs : JInt s → JInt s)
    (unsignedArg : JInt s → A) (divrem : U → A → Jl (Q × Q)) (signed : Q → S)
    (flipsign : S → JInt s → S) (unsignedResult : S → R) (x : U) (y : JInt s) : Jl (R × Q) := do
  let (q, r) ← divrem x (unsignedArg (abs y))
  pure (unsignedResult (flipsign (signed q) y), r)

/--
Julia source: base/int.jl:342-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod(x::BitSigned, y::Unsigned)
    remval = rem(x, y) # correct iff  remval>=0
    # the addition re-wraps the negative remainder into the unsigned domain
    return unsigned(remval +% (remval<zero(remval))*y)
end
```
-/
def mod_BitSigned_Unsigned {s : IntTy} {U R P V O : Type} (rem : JInt s → U → Jl R)
    (zero : R → R) (lt : R → R → Bool) (mul : Bool → U → P)
    (addWrap : R → P → V) (unsigned : V → O) (x : JInt s) (y : U) : Jl O := do
  let remval ← rem x y
  pure (unsigned (addWrap remval (mul (lt remval (zero remval)) y)))

/--
Julia source: base/int.jl:347-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod(x::Unsigned, y::Signed)
    remval =  signed(rem(x, y)) #remval>0 so correct iff y>0 or remval==0
    return remval + (!iszero(remval) && y<zero(y))*y
end
```
-/
def mod_Unsigned_Signed {U S R V P O : Type} (rem : U → S → Jl R) (signed : R → V)
    (iszero : V → Bool) (zero : S → S) (lt : S → S → Bool) (mul : Bool → S → P)
    (add : V → P → O) (x : U) (y : S) : Jl O := do
  let r ← rem x y
  let remval := signed r
  pure (add remval (mul ((!iszero remval) && (lt y (zero y))) y))

/--
Julia source: base/int.jl:351-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x::T, y::T) where {T<:Unsigned} = rem(x, y)

# Don't promote integers for div/rem/mod since there is no danger of overflow,
```
-/
def mod_Unsigned {U : Type} (rem : U → U → Jl U) (x y : U) : Jl U := rem x y

/--
Julia source: base/int.jl:696-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Signed, ::Type{Unsigned}) = x % unsigned(typeof(x))
```
-/
def rem_Signed_Unsigned {S U Ty : Type} (typeof : S → Ty) (unsigned : Ty → Ty)
    (rem : S → Ty → U) (x : S) : U := rem x (unsigned (typeof x))

/--
Julia source: base/int.jl:697-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Unsigned, ::Type{Signed}) = x % signed(typeof(x))
```
-/
def rem_Unsigned_Signed {U S Ty : Type} (typeof : U → Ty) (signed : Ty → Ty)
    (rem : U → Ty → S) (x : U) : S := rem x (signed (typeof x))

/--
Julia source: base/int.jl:699-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Integer, ::Type{Bool}) = ((x & 1) != 0)
```
-/
def rem_Integer_Bool {I R : Type} (band : I → Int → R) (neq : R → Int → Bool) (x : I) : Bool :=
  neq (band x 1) 0

/--
Julia source: base/int.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x::Integer, ::Type{T}) where {T<:Integer} = rem(x, T)
```
-/
def mod_Integer_Type {I R Ty : Type} (rem : I → Ty → R) (T : Ty) (x : I) : R := rem x T

/--
Julia source: base/int.jl:704-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_trunc(::Type{T}, x::Integer) where {T<:Integer} = rem(x, T)
```
-/
def unsafe_trunc {I R Ty : Type} (rem : I → Ty → R) (T : Ty) (x : I) : R := rem x T

/--
Julia source: base/int.jl:923-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widemul(x::Signed,y::Unsigned) = widen(x) * signed(widen(y))
```
-/
def widemul_Signed_Unsigned {S U WS WU SU R : Type} (widenS : S → WS) (widenU : U → WU)
    (signed : WU → SU) (mul : WS → SU → R) (x : S) (y : U) : R :=
  mul (widenS x) (signed (widenU y))

/--
Julia source: base/int.jl:924-924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widemul(x::Unsigned,y::Signed) = signed(widen(x)) * widen(y)
```
-/
def widemul_Unsigned_Signed {U S WU WS SU R : Type} (widenU : U → WU) (widenS : S → WS)
    (signed : WU → SU) (mul : SU → WS → R) (x : U) (y : S) : R :=
  mul (signed (widenU x)) (widenS y)

/--
Julia source: base/int.jl:926-926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widemul(x::Bool,y::Bool) = x * y
```
-/
def widemul_Bool_Bool (mul : Bool → Bool → Bool) (x y : Bool) : Bool := mul x y

/--
Julia source: base/int.jl:123-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mul_hi(a::T, b::T) where {T<:Integer}
    ((widen(a)*b) >>> Base.top_set_bit(-1 % T)) % T
end
```
-/
def mul_hi_Integer {I W P K : Type} (widen : I → W) (mul : W → I → P)
    (remLiteral : Int → I) (top_set_bit : I → K) (lshr : P → K → P)
    (rem : P → I) (a b : I) : I :=
  rem (lshr (mul (widen a) b) (top_set_bit (remLiteral (-1))))

attribute [reducible] negate_Unsigned signbit_Integer signbit_Unsigned isnegative_Unsigned
  flipsign_Float16 flipsign_Float32 flipsign_Float64 flipsign_Real copysign_Signed
  copysign_Float16 copysign_Float32 copysign_Float64 copysign_Real abs_Unsigned abs_Signed
  unsigned unsigned_BitSigned signed signed_BitUnsigned rem_Signed_Unsigned rem_Unsigned_Signed
  mod_Integer_Type unsafe_trunc widemul_Signed_Unsigned widemul_Unsigned_Signed

end Generic

/-! ## Type tuples and unions -/

/-- The type tuples of lines 10-24 as lists of `IntTy`, and the unions of lines 26-45 as
membership tests.

Julia source: base/int.jl:1-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

## integer arithmetic ##

# The tuples and types that do not include 128 bit sizes are necessary to handle
# certain issues on 32-bit machines, and also to simplify promotion rules, as
# they are also used elsewhere where Int128/UInt128 support is separated out,
# such as in hashing2.jl

const BitSigned32_types      = (Int8, Int16, Int32)
const BitUnsigned32_types    = (UInt8, UInt16, UInt32)
const BitInteger32_types     = (BitSigned32_types..., BitUnsigned32_types...)

const BitSigned64_types      = (BitSigned32_types..., Int64)
const BitUnsigned64_types    = (BitUnsigned32_types..., UInt64)
const BitInteger64_types     = (BitSigned64_types..., BitUnsigned64_types...)

const BitSigned_types        = (BitSigned64_types..., Int128)
const BitUnsigned_types      = (BitUnsigned64_types..., UInt128)
const BitInteger_types       = (BitSigned_types..., BitUnsigned_types...)

const BitSignedSmall_types   = Int === Int64 ? ( Int8,  Int16,  Int32) : ( Int8,  Int16)
const BitUnsignedSmall_types = Int === Int64 ? (UInt8, UInt16, UInt32) : (UInt8, UInt16)
const BitIntegerSmall_types  = (BitSignedSmall_types..., BitUnsignedSmall_types...)

const BitSigned32      = Union{BitSigned32_types...}
const BitUnsigned32    = Union{BitUnsigned32_types...}
const BitInteger32     = Union{BitInteger32_types...}

const BitSigned64      = Union{BitSigned64_types...}
const BitUnsigned64    = Union{BitUnsigned64_types...}
const BitInteger64     = Union{BitInteger64_types...}

const BitSigned        = Union{BitSigned_types...}
const BitUnsigned      = Union{BitUnsigned_types...}
const BitInteger       = Union{BitInteger_types...}

const BitSignedSmall   = Union{BitSignedSmall_types...}
const BitUnsignedSmall = Union{BitUnsignedSmall_types...}
const BitIntegerSmall  = Union{BitIntegerSmall_types...}

const BitSigned64T     = Union{Type{Int8}, Type{Int16}, Type{Int32}, Type{Int64}}
const BitUnsigned64T   = Union{Type{UInt8}, Type{UInt16}, Type{UInt32}, Type{UInt64}}

const BitIntegerType = Union{map(T->Type{T}, BitInteger_types)...}

```
-/
def BitSigned32_types : List IntTy := [.i8, .i16, .i32]
def BitUnsigned32_types : List IntTy := [.u8, .u16, .u32]
def BitInteger32_types : List IntTy := BitSigned32_types ++ BitUnsigned32_types
def BitSigned64_types : List IntTy := BitSigned32_types ++ [.i64]
def BitUnsigned64_types : List IntTy := BitUnsigned32_types ++ [.u64]
def BitInteger64_types : List IntTy := BitSigned64_types ++ BitUnsigned64_types
def BitSigned_types : List IntTy := BitSigned64_types ++ [.i128]
def BitUnsigned_types : List IntTy := BitUnsigned64_types ++ [.u128]
def BitInteger_types : List IntTy := BitSigned_types ++ BitUnsigned_types
/-- `Int === Int64` holds on the modelled 64-bit platform. -/
def BitSignedSmall_types : List IntTy := [.i8, .i16, .i32]
def BitUnsignedSmall_types : List IntTy := [.u8, .u16, .u32]
def BitIntegerSmall_types : List IntTy := BitSignedSmall_types ++ BitUnsignedSmall_types
def BitSigned32 (t : IntTy) : Bool := BitSigned32_types.contains t
def BitUnsigned32 (t : IntTy) : Bool := BitUnsigned32_types.contains t
def BitInteger32 (t : IntTy) : Bool := BitInteger32_types.contains t
def BitSigned64 (t : IntTy) : Bool := BitSigned64_types.contains t
def BitUnsigned64 (t : IntTy) : Bool := BitUnsigned64_types.contains t
def BitInteger64 (t : IntTy) : Bool := BitInteger64_types.contains t
def BitSigned (t : IntTy) : Bool := BitSigned_types.contains t
def BitUnsigned (t : IntTy) : Bool := BitUnsigned_types.contains t
def BitInteger (t : IntTy) : Bool := BitInteger_types.contains t
def BitSignedSmall (t : IntTy) : Bool := BitSignedSmall_types.contains t
def BitUnsignedSmall (t : IntTy) : Bool := BitUnsignedSmall_types.contains t
def BitIntegerSmall (t : IntTy) : Bool := BitIntegerSmall_types.contains t
def BitSigned64T (t : IntTy) : Bool := BitSigned64 t
def BitUnsigned64T (t : IntTy) : Bool := BitUnsigned64 t
def BitIntegerType (t : IntTy) : Bool := BitInteger t

/-! ## `signed(::Type)` -/

/--
Julia source: base/int.jl:47-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
# >> this use of `unsigned` is defined somewhere else << the docstring should migrate there
"""
    unsigned(T::Integer)

Convert an integer bitstype to the unsigned type of the same size.
# Examples
```jldoctest
julia> unsigned(Int16)
UInt16
julia> unsigned(UInt64)
UInt64
```
""" unsigned

"""
    signed(T::Integer)

Convert an integer bitstype to the signed type of the same size.
# Examples
```jldoctest
julia> signed(UInt16)
Int16
julia> signed(UInt64)
Int64
```
"""
signed(::Type{Bool}) = Int
````
-/
def signed_Type_Bool : IntTy := .i64
/--
Julia source: base/int.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(::Type{UInt8}) = Int8
```
-/
def signed_Type_UInt8 : IntTy := .i8
/--
Julia source: base/int.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(::Type{UInt16}) = Int16
```
-/
def signed_Type_UInt16 : IntTy := .i16
/--
Julia source: base/int.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(::Type{UInt32}) = Int32
```
-/
def signed_Type_UInt32 : IntTy := .i32
/--
Julia source: base/int.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(::Type{UInt64}) = Int64
```
-/
def signed_Type_UInt64 : IntTy := .i64
/--
Julia source: base/int.jl:78-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(::Type{UInt128}) = Int128
```
-/
def signed_Type_UInt128 : IntTy := .i128
/--
Julia source: base/int.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(::Type{T}) where {T<:Signed} = T
```
-/
def signed_Type_Signed {Ty : Type} (T : Ty) : Ty := T
/--
Julia source: base/int.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(::Type{Union{}}, slurp...) = throw(MethodError(signed, (Union{}, slurp...)))
```
-/
def signed_Type_Union {Tail α : Type} (_type : UnionBottom) (slurp : Tail) :
    Except (InvalidMethodError (UnionBottom × Tail)) α :=
  .error { function := .signed, arguments := (.type, slurp) }

/-- *dispatch*: `signed(T)` for a BitInteger type `T`. -/
def signedType : IntTy → IntTy
  | .u8 => signed_Type_UInt8
  | .u16 => signed_Type_UInt16
  | .u32 => signed_Type_UInt32
  | .u64 => signed_Type_UInt64
  | .u128 => signed_Type_UInt128
  | T => signed_Type_Signed T

/-! ## Primitive arithmetic -/

/--
Julia source: base/int.jl:82-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## integer comparisons ##

(<)(x::T, y::T) where {T<:BitSigned}  = slt_int(x, y)
```
-/
def lt_BitSigned {t : IntTy} (x y : JInt t) : Bool := slt_int x y
/--
Julia source: base/int.jl:85-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

(-)(x::BitInteger)                    = neg_int(x)
```
-/
def neg {t : IntTy} (x : JInt t) : JInt t := neg_int x
/--
Julia source: base/int.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::T, y::T) where {T<:BitInteger} = sub_int(x, y)
```
-/
def sub {t : IntTy} (x y : JInt t) : JInt t := sub_int x y
/--
Julia source: base/int.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(+)(x::T, y::T) where {T<:BitInteger} = add_int(x, y)
```
-/
def add {t : IntTy} (x y : JInt t) : JInt t := add_int x y
/--
Julia source: base/int.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(*)(x::T, y::T) where {T<:BitInteger} = mul_int(x, y)
```
-/
def mul {t : IntTy} (x y : JInt t) : JInt t := mul_int x y
/--
Julia source: base/int.jl:90-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

(-%)(x::BitInteger)                    = neg_int(x)
```
-/
def negWrap {t : IntTy} (x : JInt t) : JInt t := neg_int x
/--
Julia source: base/int.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-%)(x::T, y::T) where {T<:BitInteger} = sub_int(x, y)
```
-/
def subWrap {t : IntTy} (x y : JInt t) : JInt t := sub_int x y
/--
Julia source: base/int.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(+%)(x::T, y::T) where {T<:BitInteger} = add_int(x, y)
```
-/
def addWrap {t : IntTy} (x y : JInt t) : JInt t := add_int x y
/--
Julia source: base/int.jl:94-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(*%)(x::T, y::T) where {T<:BitInteger} = mul_int(x, y)
```
-/
def mulWrap {t : IntTy} (x y : JInt t) : JInt t := mul_int x y

/-! ## Bitwise operations (lines 360-433) -/

/--
Julia source: base/int.jl:360-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
## integer bitwise operations ##

"""
    ~(x)

Bitwise not.

See also: [`!`](@ref), [`&`](@ref), [`|`](@ref).

# Examples
```jldoctest
julia> ~4
-5

julia> ~10
-11

julia> ~true
false
```
"""
(~)(x::BitInteger)             = not_int(x)
````
-/
def bnot {t : IntTy} (x : JInt t) : JInt t := not_int x
/--
Julia source: base/int.jl:382-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    x & y

Bitwise and. Implements [three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic),
returning [`missing`](@ref) if one operand is `missing` and the other is `true`. Add parentheses for
function application form: `(&)(x, y)`.

See also: [`|`](@ref), [`xor`](@ref), [`&&`](@ref).

# Examples
```jldoctest
julia> 4 & 10
0

julia> 4 & 12
4

julia> true & missing
missing

julia> false & missing
false
```
"""
(&)(x::T, y::T) where {T<:BitInteger} = and_int(x, y)
````
-/
def band {t : IntTy} (x y : JInt t) : JInt t := and_int x y
/--
Julia source: base/int.jl:408-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    x | y

Bitwise or. Implements [three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic),
returning [`missing`](@ref) if one operand is `missing` and the other is `false`.

See also: [`&`](@ref), [`xor`](@ref), [`||`](@ref).

# Examples
```jldoctest
julia> 4 | 10
14

julia> 4 | 1
5

julia> true | missing
true

julia> false | missing
missing
```
"""
(|)(x::T, y::T) where {T<:BitInteger} = or_int(x, y)
````
-/
def bor {t : IntTy} (x y : JInt t) : JInt t := or_int x y
/--
Julia source: base/int.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
xor(x::T, y::T) where {T<:BitInteger} = xor_int(x, y)
```
-/
def bxor {t : IntTy} (x y : JInt t) : JInt t := xor_int x y

/-! ## Comparisons (lines 571-575) -/

/--
Julia source: base/int.jl:571-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## integer comparisons ##

(< )(x::T, y::T) where {T<:BitUnsigned} = ult_int(x, y)
```
-/
def lt_BitUnsigned {t : IntTy} (x y : JInt t) : Bool := ult_int x y
/--
Julia source: base/int.jl:574-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<=)(x::T, y::T) where {T<:BitSigned}   = sle_int(x, y)
```
-/
def le_BitSigned {t : IntTy} (x y : JInt t) : Bool := sle_int x y
/--
Julia source: base/int.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<=)(x::T, y::T) where {T<:BitUnsigned} = ule_int(x, y)
```
-/
def le_BitUnsigned {t : IntTy} (x y : JInt t) : Bool := ule_int x y

/-- *dispatch*: same-type `<` (lines 84, 573). -/
def ltSame {t : IntTy} (x y : JInt t) : Bool := if t.signed then lt_BitSigned x y else lt_BitUnsigned x y
/-- *dispatch*: same-type `<=` (lines 574-575). -/
def leSame {t : IntTy} (x y : JInt t) : Bool := if t.signed then le_BitSigned x y else le_BitUnsigned x y
/-- Same-type `==` on BitIntegers (`boot.jl:884`: `x == y = eq_int(x, y)`). -/
def eqSame {t : IntTy} (x y : JInt t) : Bool := eq_int x y

/-- `<`, `<=`, `==` of two BitIntegers of the same signedness (`promotion.jl:516-518`):
promote, then compare in the common type. -/
def ltPromote {s t : IntTy} (x : JInt s) (y : JInt t) : Bool :=
  let p := promoteSameSign x y
  ltSame p.1 p.2
def lePromote {s t : IntTy} (x : JInt s) (y : JInt t) : Bool :=
  let p := promoteSameSign x y
  leSame p.1 p.2
def eqPromote {s t : IntTy} (x : JInt s) (y : JInt t) : Bool :=
  let p := promoteSameSign x y
  eqSame p.1 p.2

/-! ## `x % T` between BitInteger types (lines 618-634, 695) -/

/-!
Julia source: base/int.jl:618-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for to in BitInteger_types, from in (BitInteger_types..., Bool)
    if !(to === from)
        if Core.sizeof(to) < Core.sizeof(from)
            @eval rem(x::($from), ::Type{$to}) = trunc_int($to, x)
        elseif from === Bool
            @eval rem(x::($from), ::Type{$to}) = convert($to, x)
        elseif Core.sizeof(from) < Core.sizeof(to)
            if from <: Signed
                @eval rem(x::($from), ::Type{$to}) = sext_int($to, x)
            else
                @eval rem(x::($from), ::Type{$to}) = convert($to, x)
            end
        else
            @eval rem(x::($from), ::Type{$to}) = bitcast($to, x)
        end
    end
end
```
-/
namespace Generated

/--
Julia source: base/int.jl:621-621 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            @eval rem(x::($from), ::Type{$to}) = trunc_int($to, x)
```
-/
def rem_trunc (to : IntTy) {fr : IntTy} (h : to.bits < fr.bits) (x : JInt fr) : JInt to :=
  trunc_int to x h

/--
Julia source: base/int.jl:623-623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            @eval rem(x::($from), ::Type{$to}) = convert($to, x)
```
-/
def rem_bool (to : IntTy) (convert : Bool → JInt to) (x : Bool) : JInt to := convert x

/--
Julia source: base/int.jl:626-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
                @eval rem(x::($from), ::Type{$to}) = sext_int($to, x)
```
-/
def rem_sext (to : IntTy) {fr : IntTy} (h : fr.bits < to.bits) (x : JInt fr) : JInt to :=
  sext_int to x h

/--
Julia source: base/int.jl:628-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
                @eval rem(x::($from), ::Type{$to}) = convert($to, x)
```
-/
def rem_convert (to : IntTy) {fr : IntTy} (convert : JInt fr → JInt to) (x : JInt fr) :
    JInt to := convert x

/--
Julia source: base/int.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            @eval rem(x::($from), ::Type{$to}) = bitcast($to, x)
```
-/
def rem_bitcast (to : IntTy) {fr : IntTy} (h : fr.bits = to.bits) (x : JInt fr) : JInt to :=
  bitcast to x h

attribute [reducible] rem_trunc rem_bool rem_sext rem_convert rem_bitcast
end Generated

/-- Dispatch between the generated methods, selected by the static source and target types. -/
def rem_BitInteger_Type (to : IntTy) {fr : IntTy} (x : JInt fr) : JInt to :=
  if h : sizeofT to < sizeofT fr then
    Generated.rem_trunc to (bits_lt_of_sizeofT_lt h) x
  else if h2 : sizeofT fr < sizeofT to then
    if fr.signed then Generated.rem_sext to (bits_lt_of_sizeofT_lt h2) x
    else Generated.rem_convert to (widenTo to) x
  else
    Generated.rem_bitcast to (bits_eq_of_sizeofT h h2) x

/-- `rem(x::Bool, ::Type{to}) = convert(to, x)`, the `from === Bool` branch of the loop at
lines 618-634. -/
def rem_Bool_Type (to : IntTy) (x : Bool) : JInt to := Generated.rem_bool to (ofBool to) x

/--
Julia source: base/int.jl:695-695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::T, ::Type{T}) where {T<:Integer} = x
```
-/
def rem_same {α : Type} (x : α) : α := x

/-- *dispatch*: `x % T` for BitInteger `x` and BitInteger type `T`. -/
def remT (to : IntTy) {fr : IntTy} (x : JInt fr) : JInt to :=
  if h : fr = to then rem_same (h ▸ x) else rem_BitInteger_Type to x

/-! ## `unsigned(x)`, `signed(x)` -/

/--
Julia source: base/int.jl:238-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    unsigned(x)

Convert a number to an unsigned integer. If the argument is signed, it is reinterpreted as
unsigned without checking for negative values.

See also: [`signed`](@ref), [`sign`](@ref), [`signbit`](@ref).

# Examples
```jldoctest
julia> unsigned(-2)
0xfffffffffffffffe

julia> unsigned(Int8(2))
0x02

julia> typeof(ans)
UInt8

julia> signed(unsigned(-2))
-2
```
"""
unsigned(x) = x % typeof(convert(Unsigned, zero(x)))
````
-/
def unsigned_any {t : IntTy} (x : JInt t) : JInt t.toUnsigned :=
  Generic.unsigned zero (widenTo t.toUnsigned) (fun _ => ()) (fun x _ => remT t.toUnsigned x) x
/--
Julia source: base/int.jl:262-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x::BitSigned) = reinterpret(typeof(convert(Unsigned, zero(x))), x)
```
-/
def unsigned_BitSigned {t : IntTy} (x : JInt t) : JInt t.toUnsigned :=
  Generic.unsigned_BitSigned zero (widenTo t.toUnsigned) (fun _ => ())
    (fun _ x => bitcast t.toUnsigned x (by cases t <;> rfl)) x
/--
Julia source: base/int.jl:264-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    signed(x)

Convert a number to a signed integer. If the argument is unsigned, it is reinterpreted as
signed without checking for overflow.

See also: [`unsigned`](@ref), [`sign`](@ref), [`signbit`](@ref).
"""
signed(x) = x % typeof(convert(Signed, zero(x)))
```
-/
def signed_any {t : IntTy} (x : JInt t) : JInt t.toSigned :=
  Generic.signed zero (widenTo t.toSigned) (fun _ => ()) (fun x _ => remT t.toSigned x) x
/--
Julia source: base/int.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(x::BitUnsigned) = reinterpret(typeof(convert(Signed, zero(x))), x)
```
-/
def signed_BitUnsigned {t : IntTy} (x : JInt t) : JInt t.toSigned :=
  Generic.signed_BitUnsigned zero (widenTo t.toSigned) (fun _ => ())
    (fun _ x => bitcast t.toSigned x (by cases t <;> rfl)) x

/-- *dispatch*: `unsigned(x)` for a BitInteger `x`. -/
def unsigned {t : IntTy} (x : JInt t) : JInt t.toUnsigned :=
  if t.signed then unsigned_BitSigned x else unsigned_any x
/-- *dispatch*: `signed(x)` for a BitInteger `x`. -/
def signed {t : IntTy} (x : JInt t) : JInt t.toSigned :=
  if t.signed then signed_any x else signed_BitUnsigned x

/-! ## Mixed-signedness comparisons (lines 577-589) -/

/--
Julia source: base/int.jl:581-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:(==), :<, :<=)
    @eval function $op(x::BitUnsigned, y::BitSigned)
        if Core.sizeof(x) < Core.sizeof(y)
            $op(typeof(y)(x), y)
        else
            (y >= 0) & $op(x, unsigned(y) % typeof(x))
        end
    end
end
```
-/
def cmp_BitUnsigned_BitSigned (op : {r : IntTy} → JInt r → JInt r → Bool) {u s : IntTy}
    (x : JInt u) (y : JInt s) : Bool :=
  if sizeofT u < sizeofT s then
    -- `typeof(y)(x)` from a narrower unsigned type selects `boot.jl`'s `zext_int`.
    op (widenTo s x) y
  else
    -- `y >= 0` is `0 <= y` (`operators.jl`), promoted between the two signed types.
    (lePromote (lit .i64 0) y) && op x (remT u (unsigned y))

/--
Julia source: base/int.jl:581-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:(==), :<, :<=)
    @eval function $op(x::BitUnsigned, y::BitSigned)
        if Core.sizeof(x) < Core.sizeof(y)
            $op(typeof(y)(x), y)
        else
            (y >= 0) & $op(x, unsigned(y) % typeof(x))
        end
    end
end
```
-/
def eq_BitUnsigned_BitSigned {u s : IntTy} (x : JInt u) (y : JInt s) : Bool :=
  if sizeofT u < sizeofT s then eqSame (widenTo s x) y
  else Bool.and (lePromote (lit .i64 0) y) (eqSame x (remT u (unsigned y)))

/--
Julia source: base/int.jl:581-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:(==), :<, :<=)
    @eval function $op(x::BitUnsigned, y::BitSigned)
        if Core.sizeof(x) < Core.sizeof(y)
            $op(typeof(y)(x), y)
        else
            (y >= 0) & $op(x, unsigned(y) % typeof(x))
        end
    end
end
```
-/
def lt_BitUnsigned_BitSigned {u s : IntTy} (x : JInt u) (y : JInt s) : Bool :=
  if sizeofT u < sizeofT s then ltSame (widenTo s x) y
  else Bool.and (lePromote (lit .i64 0) y) (ltSame x (remT u (unsigned y)))

/--
Julia source: base/int.jl:581-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:(==), :<, :<=)
    @eval function $op(x::BitUnsigned, y::BitSigned)
        if Core.sizeof(x) < Core.sizeof(y)
            $op(typeof(y)(x), y)
        else
            (y >= 0) & $op(x, unsigned(y) % typeof(x))
        end
    end
end
```
-/
def le_BitUnsigned_BitSigned {u s : IntTy} (x : JInt u) (y : JInt s) : Bool :=
  if sizeofT u < sizeofT s then leSame (widenTo s x) y
  else Bool.and (lePromote (lit .i64 0) y) (leSame x (remT u (unsigned y)))

/--
Julia source: base/int.jl:577-577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::BitSigned, y::BitUnsigned) = y == x
```
-/
def eq_BitSigned_BitUnsigned {s u : IntTy} (x : JInt s) (y : JInt u) : Bool :=
  eq_BitUnsigned_BitSigned y x
/--
Julia source: base/int.jl:578-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<(x::BitSigned, y::BitUnsigned) = !(y <= x)
```
-/
def lt_BitSigned_BitUnsigned {s u : IntTy} (x : JInt s) (y : JInt u) : Bool :=
  !(le_BitUnsigned_BitSigned y x)
/--
Julia source: base/int.jl:579-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::BitSigned, y::BitUnsigned) = !(y < x)
```
-/
def le_BitSigned_BitUnsigned {s u : IntTy} (x : JInt s) (y : JInt u) : Bool :=
  !(lt_BitUnsigned_BitSigned y x)

/-- *dispatch*: `x < y` for any two BitIntegers. -/
def lt {s t : IntTy} (x : JInt s) (y : JInt t) : Bool :=
  if s.signed = t.signed then ltPromote x y
  else if s.signed then lt_BitSigned_BitUnsigned x y
  else lt_BitUnsigned_BitSigned x y
/-- *dispatch*: `x <= y` for any two BitIntegers. -/
def le {s t : IntTy} (x : JInt s) (y : JInt t) : Bool :=
  if s.signed = t.signed then lePromote x y
  else if s.signed then le_BitSigned_BitUnsigned x y
  else le_BitUnsigned_BitSigned x y
/-- *dispatch*: `x == y` for any two BitIntegers. -/
def eq {s t : IntTy} (x : JInt s) (y : JInt t) : Bool :=
  if s.signed = t.signed then eqPromote x y
  else if s.signed then eq_BitSigned_BitUnsigned x y
  else eq_BitUnsigned_BitSigned x y

/-! ## Promoted binary operations (lines 1092-1100) -/

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def op_Integer {A B : Type} (T : IntTy) (op : JInt T → JInt T → JInt T)
    (remA : A → JInt T) (remB : B → JInt T) (a : A) (b : B) : JInt T :=
  -- `T = promote_typeof(a, b)` is the argument `T`; `aT, bT = a % T, b % T`.
  let aT := remA a
  let bT := remB b
  -- `not_sametype((a, b), (aT, bT))` returns `nothing`: this method is reached only with
  -- argument types other than `(T, T)`, since same-type calls select the methods above.
  op aT bT

/-- *dispatch*: a binary operator of lines 87-94 and 407-433 on two BitIntegers: the same-type
method, or the promoted method of lines 1092-1100. -/
def binop (op : {r : IntTy} → JInt r → JInt r → JInt r) {s t : IntTy} (x : JInt s) (y : JInt t) :
    JInt (s.promote t) :=
  if s = t then op (remT _ x) (remT _ y)
  else op_Integer (s.promote t) op (remT _) (remT _) x y

/-- *dispatch*: `b * y` with `b::Bool` and BitInteger `y` (the promoted method of lines
1092-1100, since `promote_type(Bool, T) == T`). -/
def mulBool {t : IntTy} (b : Bool) (y : JInt t) : JInt t :=
  op_Integer t mul (rem_Bool_Type t) (remT t) b y

/-! ## `negate`, `inv`, `/` -/

/--
Julia source: base/int.jl:95-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

negate(x) = -x
```
-/
def negate {α : Type} (neg : α → α) (x : α) : α := neg x
/--
Julia source: base/int.jl:97-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
negate(x::Unsigned) = -convert(Signed, x)
#widenegate(x) = -convert(widen(signed(typeof(x))), x)
```
-/
def negate_Unsigned {t : IntTy} (x : JInt t) : Jl (JInt t.toSigned) :=
  Generic.negate_Unsigned (convert t.toSigned) neg x
/--
Julia source: base/int.jl:99-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

inv(x::Integer) = float(one(x)) / float(x)
```
-/
def inv_Integer {I F : Type} (one : I → I) (float : I → F) (fdiv : F → F → F) (x : I) : F :=
  fdiv (float (one x)) (float x)
/--
Julia source: base/int.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(/)(x::T, y::T) where {T<:Integer} = float(x) / float(y)
```
-/
def fdiv_Integer {I F : Type} (float : I → F) (fdiv : F → F → F) (x y : I) : F :=
  fdiv (float x) (float y)
/--
Julia source: base/int.jl:102-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# skip promotion for system integer types
(/)(x::BitInteger, y::BitInteger) = float(x) / float(y)

```
-/
def fdiv_BitInteger {s t : IntTy} {F : Type} (floatS : JInt s → F) (floatT : JInt t → F)
    (fdiv : F → F → F) (x : JInt s) (y : JInt t) : F :=
  fdiv (floatS x) (floatT y)

/-! ## Shifts (lines 601-616) -/

/--
Julia source: base/int.jl:601-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## integer shifts ##

# unsigned shift counts always shift in the same direction
>>(x::BitSigned,   y::BitUnsigned) = ashr_int(x, y)
```
-/
def shr_BitSigned_BitUnsigned {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t := ashr_int x y
/--
Julia source: base/int.jl:605-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>>(x::BitUnsigned, y::BitUnsigned) = lshr_int(x, y)
```
-/
def shr_BitUnsigned_BitUnsigned {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t := lshr_int x y
/--
Julia source: base/int.jl:606-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<<(x::BitInteger,  y::BitUnsigned) = shl_int(x, y)
```
-/
def shl_BitInteger_BitUnsigned {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t := shl_int x y
/--
Julia source: base/int.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>>>(x::BitInteger, y::BitUnsigned) = lshr_int(x, y)
```
-/
def lshr_BitInteger_BitUnsigned {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t := lshr_int x y

/-- *dispatch*: `x >> y` with `y::BitUnsigned`. -/
def shrU {t u : IntTy} (x : JInt t) (y : JInt u) : JInt t :=
  if t.signed then shr_BitSigned_BitUnsigned x y else shr_BitUnsigned_BitUnsigned x y

/--
Julia source: base/int.jl:608-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# signed shift counts can shift in either direction
# note: this early during bootstrap, `>=` is not yet available
# note: we only define Int shift counts here; the generic case is handled later
>>(x::BitInteger, y::Int) =
    ifelse(0 <= y, x >> unsigned(y), x << unsigned(-y))
```
-/
def shr_Int {t : IntTy} (x : JInt t) (y : JInt .i64) : JInt t :=
  ifelse (le_BitSigned (lit .i64 0) y) (shrU x (unsigned y))
    (shl_BitInteger_BitUnsigned x (unsigned (neg y)))
/--
Julia source: base/int.jl:613-614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<<(x::BitInteger, y::Int) =
    ifelse(0 <= y, x << unsigned(y), x >> unsigned(-y))
```
-/
def shl_Int {t : IntTy} (x : JInt t) (y : JInt .i64) : JInt t :=
  ifelse (le_BitSigned (lit .i64 0) y) (shl_BitInteger_BitUnsigned x (unsigned y))
    (shrU x (unsigned (neg y)))
/--
Julia source: base/int.jl:615-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
>>>(x::BitInteger, y::Int) =
    ifelse(0 <= y, x >>> unsigned(y), x << unsigned(-y))

```
-/
def lshr_Int {t : IntTy} (x : JInt t) (y : JInt .i64) : JInt t :=
  ifelse (le_BitSigned (lit .i64 0) y) (lshr_BitInteger_BitUnsigned x (unsigned y))
    (shl_BitInteger_BitUnsigned x (unsigned (neg y)))

/-! ## Sign operations (lines 183-236) -/

/--
Julia source: base/int.jl:182-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

signbit(x::Integer) = x < 0
```
-/
def signbit_Integer {t : IntTy} (x : JInt t) : Bool :=
  Generic.signbit_Integer (fun x n => lt x (lit .i64 n)) x
/--
Julia source: base/int.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Unsigned) = false
```
-/
def signbit_Unsigned {t : IntTy} (x : JInt t) : Bool := Generic.signbit_Unsigned x
/--
Julia source: base/int.jl:185-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

isnegative(x::Unsigned) = false
```
-/
def isnegative_Unsigned {t : IntTy} (x : JInt t) : Bool := Generic.isnegative_Unsigned x

/-- *dispatch*: `signbit(x)` for a BitInteger `x`. -/
def signbit {t : IntTy} (x : JInt t) : Bool := if t.signed then signbit_Integer x else signbit_Unsigned x

/--
Julia source: base/int.jl:187-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

flipsign(x::T, y::T) where {T<:BitSigned} = flipsign_int(x, y)
```
-/
def flipsign_same {t : IntTy} (x y : JInt t) : JInt t := flipsign_int x y
/--
Julia source: base/int.jl:189-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::BitSigned, y::BitSigned) = flipsign_int(promote(x, y)...) % typeof(x)

```
-/
def flipsign_BitSigned {s t : IntTy} (x : JInt s) (y : JInt t) : JInt s :=
  let p := promoteSameSign x y
  remT s (flipsign_int p.1 p.2)
/--
Julia source: base/int.jl:194-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Real)    = flipsign(x, -oftype(x, signbit(y)))

```
-/
def flipsign_Real {s : IntTy} {R : Type} (signbit : R → Bool) (x : JInt s) (y : R) : JInt s :=
  Generic.flipsign_Real signbit (fun _ => ofBool s) neg flipsign_same x y

/-- *dispatch*: `flipsign(x, y)` for a BitSigned `x` and a BitInteger `y`. -/
def flipsign {s t : IntTy} (x : JInt s) (y : JInt t) : JInt s :=
  if t.signed then (if s = t then flipsign_same x (remT s y) else flipsign_BitSigned x y)
  else flipsign_Real signbit_Unsigned x y

/--
Julia source: base/int.jl:191-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Float16) = flipsign(x, bitcast(Int16, y))
```
-/
def flipsign_Float16 {s : IntTy} (x : JInt s) (y : Fl half) : JInt s :=
  Generic.flipsign_Float16 flipsign x y
/--
Julia source: base/int.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Float32) = flipsign(x, bitcast(Int32, y))
```
-/
def flipsign_Float32 {s : IntTy} (x : JInt s) (y : Fl single) : JInt s :=
  Generic.flipsign_Float32 flipsign x y
/--
Julia source: base/int.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign(x::Signed, y::Float64) = flipsign(x, bitcast(Int64, y))
```
-/
def flipsign_Float64 {s : IntTy} (x : JInt s) (y : Fl double) : JInt s :=
  Generic.flipsign_Float64 flipsign x y

/--
Julia source: base/int.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Signed)  = flipsign(x, x ⊻ y)
```
-/
def copysign_Signed {s t : IntTy} (x : JInt s) (y : JInt t) : JInt s :=
  Generic.copysign_Signed (binop bxor) flipsign x y
/--
Julia source: base/int.jl:200-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Real)    = copysign(x, -oftype(x, signbit(y)))

```
-/
def copysign_Real {s : IntTy} {R : Type} (signbit : R → Bool) (x : JInt s) (y : R) : JInt s :=
  Generic.copysign_Real signbit (fun _ => ofBool s) neg copysign_Signed x y

/-- *dispatch*: `copysign(x, y)` for a BitSigned `x` and a BitInteger `y`. -/
def copysign {s t : IntTy} (x : JInt s) (y : JInt t) : JInt s :=
  if t.signed then copysign_Signed x y else copysign_Real signbit_Unsigned x y

/--
Julia source: base/int.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Float16) = copysign(x, bitcast(Int16, y))
```
-/
def copysign_Float16 {s : IntTy} (x : JInt s) (y : Fl half) : JInt s :=
  Generic.copysign_Float16 copysign x y
/--
Julia source: base/int.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Float32) = copysign(x, bitcast(Int32, y))
```
-/
def copysign_Float32 {s : IntTy} (x : JInt s) (y : Fl single) : JInt s :=
  Generic.copysign_Float32 copysign x y
/--
Julia source: base/int.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copysign(x::Signed, y::Float64) = copysign(x, bitcast(Int64, y))
```
-/
def copysign_Float64 {s : IntTy} (x : JInt s) (y : Fl double) : JInt s :=
  Generic.copysign_Float64 copysign x y

/--
Julia source: base/int.jl:202-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    abs(x)

The absolute value of `x`.

When `abs` is applied to signed integers, overflow may occur,
resulting in the return of a negative value. This overflow occurs only
when `abs` is applied to the minimum representable value of a signed
integer. That is, when `x == typemin(typeof(x))`, `abs(x) == x < 0`,
not `-x` as might be expected.

See also: [`abs2`](@ref), [`unsigned`](@ref), [`sign`](@ref), [`Base.uabs`](@ref), [`Base.Checked.checked_abs`](@ref).

# Examples
```jldoctest
julia> abs(-3)
3

julia> abs(1 + im)
1.4142135623730951

julia> abs.(Int8[-128 -127 -126 0 126 127])  # overflow at typemin(Int8)
1×6 Matrix{Int8}:
 -128  127  126  0  126  127

julia> maximum(abs, [1, -2, 3, -4])
4
```
"""
function abs end

abs(x::Unsigned) = x
````
-/
def abs_Unsigned {t : IntTy} (x : JInt t) : JInt t := Generic.abs_Unsigned x
/--
Julia source: base/int.jl:234-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::Signed) = flipsign(x,x)

```
-/
def abs_Signed {t : IntTy} (x : JInt t) : JInt t :=
  Generic.abs_Signed flipsign_same x

/-- *dispatch*: `abs(x)` for a BitInteger `x`. -/
def abs {t : IntTy} (x : JInt t) : JInt t := if t.signed then abs_Signed x else abs_Unsigned x

/--
Julia source: base/int.jl:236-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
~(n::Integer) = -n-1

```
-/
def bnot_Integer {I : Type} (neg : I → I) (sub : I → JInt .i64 → I) (n : I) : I :=
  sub (neg n) (lit .i64 1)

/-! ## Mixed-signedness division (lines 275-289) -/

/-- `div(a, b)` / `rem(a, b)` of two BitIntegers (`base/div.jl` and `promotion.jl`, later or
user-extensible): a parameter. -/
abbrev BinOpJl := {a b : IntTy} → JInt a → JInt b → Jl (JInt (a.promote b))
/-- `divrem(a, b)` of two BitIntegers (`base/div.jl`): a parameter. -/
abbrev DivremJl := {a b : IntTy} → JInt a → JInt b → Jl (JInt (a.promote b) × JInt (a.promote b))

/--
Julia source: base/int.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::BitSigned, y::Unsigned) = flipsign(signed(div(unsigned(abs(x)), y)), x)
```
-/
def div_BitSigned_Unsigned (div : BinOpJl) {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.toUnsigned.promote u).toSigned) :=
  Generic.div_BitSigned_Unsigned abs unsigned div signed flipsign x y
/--
Julia source: base/int.jl:276-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::Unsigned, y::BitSigned) = unsigned(flipsign(signed(div(x, unsigned(abs(y)))), y))

```
-/
def div_Unsigned_BitSigned (div : BinOpJl) {u s : IntTy} (x : JInt u) (y : JInt s) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned) :=
  Generic.div_Unsigned_BitSigned abs unsigned div signed flipsign unsigned x y
/--
Julia source: base/int.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::BitSigned, y::Unsigned) = flipsign(signed(rem(unsigned(abs(x)), y)), x)
```
-/
def rem_BitSigned_Unsigned (rem : BinOpJl) {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.toUnsigned.promote u).toSigned) :=
  Generic.rem_BitSigned_Unsigned abs unsigned rem signed flipsign x y
/--
Julia source: base/int.jl:279-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Unsigned, y::BitSigned) = rem(x, unsigned(abs(y)))

```
-/
def rem_Unsigned_BitSigned (rem : BinOpJl) {u s : IntTy} (x : JInt u) (y : JInt s) :
    Jl (JInt (u.promote s.toUnsigned)) :=
  Generic.rem_Unsigned_BitSigned abs unsigned rem x y
/--
Julia source: base/int.jl:281-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x::BitSigned, y::Unsigned)
    q, r = divrem(unsigned(abs(x)), y)
    flipsign(signed(q), x), flipsign(signed(r), x)
end

```
-/
def divrem_BitSigned_Unsigned (divrem : DivremJl) {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt (s.toUnsigned.promote u).toSigned × JInt (s.toUnsigned.promote u).toSigned) :=
  Generic.divrem_BitSigned_Unsigned abs unsigned divrem signed flipsign x y
/--
Julia source: base/int.jl:286-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divrem(x::Unsigned, y::BitSigned)
    q, r = divrem(x, unsigned(abs(y)))
    unsigned(flipsign(signed(q), y)), r
end


```
-/
def divrem_Unsigned_BitSigned (divrem : DivremJl) {u s : IntTy} (x : JInt u) (y : JInt s) :
    Jl (JInt (u.promote s.toUnsigned).toSigned.toUnsigned × JInt (u.promote s.toUnsigned)) :=
  Generic.divrem_Unsigned_BitSigned abs unsigned divrem signed flipsign unsigned x y

/-! ## Same-type `div` and `rem` (lines 353-358, 1082-1090) -/

/--
Julia source: base/int.jl:353-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Don't promote integers for div/rem/mod since there is no danger of overflow,
# while there is a substantial performance penalty to 64-bit promotion.
div(x::T, y::T) where {T<:BitSigned64} = checked_sdiv_int(x, y)
```
-/
def div_BitSigned64 {t : IntTy} (x y : JInt t) : Jl (JInt t) := checked_sdiv_int x y
/--
Julia source: base/int.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::T, y::T) where {T<:BitSigned64} = checked_srem_int(x, y)
```
-/
def rem_BitSigned64 {t : IntTy} (x y : JInt t) : Jl (JInt t) := checked_srem_int x y
/--
Julia source: base/int.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::T, y::T) where {T<:BitUnsigned64} = checked_udiv_int(x, y)
```
-/
def div_BitUnsigned64 {t : IntTy} (x y : JInt t) : Jl (JInt t) := checked_udiv_int x y
/--
Julia source: base/int.jl:358-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::T, y::T) where {T<:BitUnsigned64} = checked_urem_int(x, y)

```
-/
def rem_BitUnsigned64 {t : IntTy} (x y : JInt t) : Jl (JInt t) := checked_urem_int x y
/--
Julia source: base/int.jl:1083-1083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    *(x::T, y::T) where {T<:Union{Int128,UInt128}}  = mul_int(x, y)
```
-/
def mul_128 {t : IntTy} (x y : JInt t) : JInt t := mul_int x y
/--
Julia source: base/int.jl:1084-1085 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    div(x::Int128,  y::Int128)  = checked_sdiv_int(x, y)
```
-/
def div_Int128 (x y : JInt .i128) : Jl (JInt .i128) := checked_sdiv_int x y
/--
Julia source: base/int.jl:1086-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    div(x::UInt128, y::UInt128) = checked_udiv_int(x, y)
```
-/
def div_UInt128 (x y : JInt .u128) : Jl (JInt .u128) := checked_udiv_int x y
/--
Julia source: base/int.jl:1087-1088 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    rem(x::Int128,  y::Int128)  = checked_srem_int(x, y)
```
-/
def rem_Int128 (x y : JInt .i128) : Jl (JInt .i128) := checked_srem_int x y
/--
Julia source: base/int.jl:1089-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    rem(x::UInt128, y::UInt128) = checked_urem_int(x, y)
end
```
-/
def rem_UInt128 (x y : JInt .u128) : Jl (JInt .u128) := checked_urem_int x y

/-- *dispatch*: same-type `div(x, y)` on a BitInteger type. -/
def divSame : {t : IntTy} → JInt t → JInt t → Jl (JInt t)
  | .i128, x, y => div_Int128 x y
  | .u128, x, y => div_UInt128 x y
  | .i8, x, y | .i16, x, y | .i32, x, y | .i64, x, y => div_BitSigned64 x y
  | .u8, x, y | .u16, x, y | .u32, x, y | .u64, x, y => div_BitUnsigned64 x y
/-- *dispatch*: same-type `rem(x, y)` on a BitInteger type. -/
def remSame : {t : IntTy} → JInt t → JInt t → Jl (JInt t)
  | .i128, x, y => rem_Int128 x y
  | .u128, x, y => rem_UInt128 x y
  | .i8, x, y | .i16, x, y | .i32, x, y | .i64, x, y => rem_BitSigned64 x y
  | .u8, x, y | .u16, x, y | .u32, x, y | .u64, x, y => rem_BitUnsigned64 x y
/-- *dispatch*: same-type `*` on a BitInteger type (line 1083 for 128 bits, else line 89). -/
def mulSame : {t : IntTy} → JInt t → JInt t → JInt t
  | .i128, x, y | .u128, x, y => mul_128 x y
  | .i8, x, y | .i16, x, y | .i32, x, y | .i64, x, y => mul x y
  | .u8, x, y | .u16, x, y | .u32, x, y | .u64, x, y => mul x y

/-! ## `mod` (lines 292-351) -/

/--
Julia source: base/int.jl:292-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    mod(x, y)
    rem(x, y, RoundDown)

The reduction of `x` modulo `y`, or equivalently, the remainder of `x` after floored
division by `y`, i.e. `x - y*fld(x,y)` if computed without intermediate rounding.

The result will have the same sign as `y` if `isfinite(y)`, and magnitude less than `abs(y)` (with some
exceptions, see note below).

!!! note

    When used with floating point values, the exact result may not be representable by the
    type, and so rounding error may occur. In particular, if the exact result is very
    close to `y`, then it may be rounded to `y`.

See also: [`rem`](@ref), [`fld`](@ref), [`mod1`](@ref), [`fldmod`](@ref), [`invmod`](@ref).

```jldoctest
julia> mod(8, 3)
2

julia> mod(9, 3)
0

julia> mod(8.9, 3)
2.9000000000000004

julia> mod(eps(), 3)
2.220446049250313e-16

julia> mod(-eps(), 3)
3.0

julia> mod.(-5:5, 3)'
1×11 adjoint(::Vector{Int64}) with eltype Int64:
 1  2  0  1  2  0  1  2  0  1  2
```
"""
function mod(x::T, y::T) where T<:Integer
    y == -1 && return T(0)   # avoid potential overflow in fld
    return x - fld(x, y) * y
end
````
-/
def mod_Integer {T : Type} (isMinusOne : T → Bool) (zeroT : T) (fld : T → T → Jl T)
    (sub mul : T → T → T) (x y : T) : Jl T :=
  if isMinusOne y then pure zeroT
  else do
    let q ← fld x y
    pure (sub x (mul q y))
/--
Julia source: base/int.jl:335-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# For fixed-width integers the subtraction and product above wrap on valid
# inputs (`fld(x, y)*y` lies in `(x - y, x + y]`, e.g. `mod(typemin(Int), 3)`)
# and the result is correct only through the double wrap-cancellation.
function mod(x::T, y::T) where T<:BitSigned
    y == -1 && return T(0)   # avoid potential overflow in fld
    return x -% fld(x, y) *% y
end
```
-/
def mod_BitSigned {t : IntTy} (fld : JInt t → JInt t → Jl (JInt t)) (x y : JInt t) : Jl (JInt t) :=
  if eq y (lit .i64 (-1)) then pure (lit t 0)
  else do
    let q ← fld x y
    pure (subWrap x (mulWrap q y))
/--
Julia source: base/int.jl:342-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod(x::BitSigned, y::Unsigned)
    remval = rem(x, y) # correct iff  remval>=0
    # the addition re-wraps the negative remainder into the unsigned domain
    return unsigned(remval +% (remval<zero(remval))*y)
end
```
-/
def mod_BitSigned_Unsigned (rem : BinOpJl) {s u : IntTy} (x : JInt s) (y : JInt u) :
    Jl (JInt ((s.toUnsigned.promote u).toSigned.promote u).toUnsigned) :=
  Generic.mod_BitSigned_Unsigned (rem_BitSigned_Unsigned rem) zero lt mulBool (binop addWrap)
    unsigned x y
/--
Julia source: base/int.jl:347-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mod(x::Unsigned, y::Signed)
    remval =  signed(rem(x, y)) #remval>0 so correct iff y>0 or remval==0
    return remval + (!iszero(remval) && y<zero(y))*y
end
```
-/
def mod_Unsigned_Signed (rem : BinOpJl) {u s : IntTy} (x : JInt u) (y : JInt s) :
    Jl (JInt ((u.promote s.toUnsigned).toSigned.promote s)) := do
  let r ← rem_Unsigned_BitSigned rem x y
  let remval := signed r
  pure (binop add remval (mulBool (!(eq remval (zero remval)) && lt y (zero y)) y))
/--
Julia source: base/int.jl:351-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x::T, y::T) where {T<:Unsigned} = rem(x, y)

```
-/
def mod_Unsigned {t : IntTy} (x y : JInt t) : Jl (JInt t) := Generic.mod_Unsigned remSame x y

/-! ## Byte and bit counts (lines 435-569) -/

/--
Julia source: base/int.jl:435-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    bswap(n)

Reverse the byte order of `n`.

(See also [`ntoh`](@ref) and [`hton`](@ref) to convert between the current native byte order and big-endian order.)

# Examples
```jldoctest
julia> a = bswap(0x10203040)
0x40302010

julia> bswap(a)
0x10203040

julia> string(1, base = 2)
"1"

julia> string(bswap(1), base = 2)
"100000000000000000000000000000000000000000000000000000000"
```
"""
bswap(x::Union{Int8, UInt8, Bool}) = x
````
-/
def bswap_small {α : Type} (x : α) : α := x
/--
Julia source: base/int.jl:458-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bswap(x::Union{Int16, UInt16, Int32, UInt32, Int64, UInt64, Int128, UInt128}) =
    bswap_int(x)

```
-/
def bswap_wide {t : IntTy} (x : JInt t) (h : t.bits % 16 = 0) : JInt t := bswap_int x h

/-- *dispatch*: `bswap(x)` for a BitInteger `x`. -/
def bswap {t : IntTy} (x : JInt t) : JInt t :=
  if h : t.bits % 16 = 0 then bswap_wide x h else bswap_small x

/--
Julia source: base/int.jl:461-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    count_ones(x::Integer)::Integer

Number of ones in the binary representation of `x`.

# Examples
```jldoctest
julia> count_ones(7)
3

julia> count_ones(Int32(-1))
32
```
"""
count_ones(x::BitInteger) = (ctpop_int(x) % Int)::Int

````
-/
def count_ones {t : IntTy} (x : JInt t) : JInt .i64 := remT .i64 (ctpop_int x)
/--
Julia source: base/int.jl:477-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    leading_zeros(x::Integer)::Integer

Number of zeros leading the binary representation of `x`.

# Examples
```jldoctest
julia> leading_zeros(Int32(1))
31
```
"""
leading_zeros(x::BitInteger) = (ctlz_int(x) % Int)::Int

````
-/
def leading_zeros {t : IntTy} (x : JInt t) : JInt .i64 := remT .i64 (ctlz_int x)
/--
Julia source: base/int.jl:490-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    trailing_zeros(x::Integer)::Integer

Number of zeros trailing the binary representation of `x`.

# Examples
```jldoctest
julia> trailing_zeros(2)
1
```
"""
trailing_zeros(x::BitInteger) = (cttz_int(x) % Int)::Int

````
-/
def trailing_zeros {t : IntTy} (x : JInt t) : JInt .i64 := remT .i64 (cttz_int x)
/--
Julia source: base/int.jl:503-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    count_zeros(x::Integer)::Integer

Number of zeros in the binary representation of `x`.

# Examples
```jldoctest
julia> count_zeros(Int32(2 ^ 16 - 1))
16

julia> count_zeros(-1)
0
```
"""
count_zeros(x::Integer) = count_ones(~x)

````
-/
def count_zeros_Integer {I : Type} (count_ones : I → JInt .i64) (bnot : I → I) (x : I) : JInt .i64 :=
  count_ones (bnot x)
/--
Julia source: base/int.jl:519-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    leading_ones(x::Integer)::Integer

Number of ones leading the binary representation of `x`.

# Examples
```jldoctest
julia> leading_ones(UInt32(2 ^ 32 - 2))
31
```
"""
leading_ones(x::Integer) = leading_zeros(~x)

````
-/
def leading_ones_Integer {I : Type} (leading_zeros : I → JInt .i64) (bnot : I → I) (x : I) :
    JInt .i64 :=
  leading_zeros (bnot x)
/--
Julia source: base/int.jl:532-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    trailing_ones(x::Integer)::Integer

Number of ones trailing the binary representation of `x`.

# Examples
```jldoctest
julia> trailing_ones(3)
2
```
"""
trailing_ones(x::Integer) = trailing_zeros(~x)

````
-/
def trailing_ones_Integer {I : Type} (trailing_zeros : I → JInt .i64) (bnot : I → I) (x : I) :
    JInt .i64 :=
  trailing_zeros (bnot x)
/--
Julia source: base/int.jl:545-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    top_set_bit(x::Integer)::Integer

The number of bits in `x`'s binary representation, excluding leading zeros.

Equivalently, the position of the most significant set bit in `x`'s binary
representation, measured from the least significant side.

Negative `x` are only supported when `x::BitSigned`.

See also: [`ndigits0z`](@ref), [`ndigits`](@ref).

# Examples
```jldoctest
julia> Base.top_set_bit(4)
3

julia> Base.top_set_bit(0)
0

julia> Base.top_set_bit(-1)
64
```
"""
top_set_bit(x::BitInteger) = 8sizeof(x) - leading_zeros(x)

````
-/
def top_set_bit {t : IntTy} (x : JInt t) : JInt .i64 :=
  sub (mul (lit .i64 8) (sizeof x)) (leading_zeros x)

/-! ## Parity (lines 143-181) -/

/--
Julia source: base/int.jl:143-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isodd(x::Number)::Bool

Return `true` if `x` is an odd integer (that is, an integer not divisible by 2), and `false` otherwise.

!!! compat "Julia 1.7"
    Non-`Integer` arguments require Julia 1.7 or later.

# Examples
```jldoctest
julia> isodd(9)
true

julia> isodd(10)
false
```
"""
isodd(n::Number) = isreal(n) && isodd(real(n))
````
-/
def isodd_Number {N R : Type} (isreal : N → Bool) (real : N → R) (isodd : R → Bool) (n : N) : Bool :=
  isreal n && isodd (real n)
/--
Julia source: base/int.jl:161-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isodd(n::Real) = isinteger(n) && !iszero(rem(Integer(n), 2))

```
-/
def isodd_Real {R I J : Type} (isinteger : R → Bool) (Integer : R → I) (rem : I → JInt .i64 → J)
    (iszero : J → Bool) (n : R) : Bool :=
  isinteger n && !(iszero (rem (Integer n) (lit .i64 2)))
/--
Julia source: base/int.jl:163-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    iseven(x::Number)::Bool

Return `true` if `x` is an even integer (that is, an integer divisible by 2), and `false` otherwise.

!!! compat "Julia 1.7"
    Non-`Integer` arguments require Julia 1.7 or later.

# Examples
```jldoctest
julia> iseven(9)
false

julia> iseven(10)
true
```
"""
iseven(n::Number) = isreal(n) && iseven(real(n))
````
-/
def iseven_Number {N R : Type} (isreal : N → Bool) (real : N → R) (iseven : R → Bool) (n : N) : Bool :=
  isreal n && iseven (real n)
/--
Julia source: base/int.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iseven(n::Real) = isinteger(n) && iszero(rem(Integer(n), 2))
```
-/
def iseven_Real {R I J : Type} (isinteger : R → Bool) (Integer : R → I) (rem : I → JInt .i64 → J)
    (iszero : J → Bool) (n : R) : Bool :=
  isinteger n && iszero (rem (Integer n) (lit .i64 2))

/-! ## `max`, `min`, `minmax` (lines 591-599) -/

/--
Julia source: base/int.jl:591-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function max(x::S, y::T) where {S <: BitInteger, T <: BitInteger}
    R = promote_type(S, T)
    ifelse(x < y, y % R, x % R)
end

```
-/
def max_BitInteger {s t : IntTy} (x : JInt s) (y : JInt t) : JInt (s.promote t) :=
  -- `R = promote_type(S, T)`
  ifelse (lt x y) (remT (s.promote t) y) (remT (s.promote t) x)
/--
Julia source: base/int.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::S, y::BitUnsigned) where S <: BitSigned = ifelse(x < y, x, y % S)
```
-/
def min_BitSigned_BitUnsigned {s u : IntTy} (x : JInt s) (y : JInt u) : JInt s :=
  ifelse (lt x y) x (remT s y)
/--
Julia source: base/int.jl:597-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::BitUnsigned, y::T) where T <: BitSigned = ifelse(x < y, x % T, y)

```
-/
def min_BitUnsigned_BitSigned {u s : IntTy} (x : JInt u) (y : JInt s) : JInt s :=
  ifelse (lt x y) (remT s x) y

/-- Result type of `min(x::S, y::T)` for BitIntegers. -/
def minType (s t : IntTy) : IntTy :=
  if s.signed = t.signed then s.promote t else if s.signed then s else t

/-- *dispatch*: `min(x, y)` for two BitIntegers; same-signedness arguments are promoted
(`promotion.jl:527`) and compared by `min(x::T, y::T) = ifelse(y < x, y, x)`. -/
def jmin {s t : IntTy} (x : JInt s) (y : JInt t) : JInt (minType s t) :=
  if s.signed = t.signed then
    let p := promoteSameSign x y
    remT _ (ifelse (ltSame p.2 p.1) p.2 p.1)
  else if s.signed then remT _ (min_BitSigned_BitUnsigned x y)
  else remT _ (min_BitUnsigned_BitSigned x y)
/-- *dispatch*: `max(x, y)` for two BitIntegers. -/
def jmax {s t : IntTy} (x : JInt s) (y : JInt t) : JInt (s.promote t) :=
  if s = t then remT _ (ifelse (lt y x) x (remT s y)) else max_BitInteger x y

/--
Julia source: base/int.jl:599-600 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax(x::BitInteger, y::BitInteger) = (min(x, y), max(x, y))

```
-/
def minmax_BitInteger {s t : IntTy} (x : JInt s) (y : JInt t) :
    JInt (minType s t) × JInt (s.promote t) :=
  (jmin x y, jmax x y)

/-! ## `bitrotate` (lines 636-665) -/

/--
Julia source: base/int.jl:636-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
## integer bitwise rotations ##

"""
    bitrotate(x::Base.BitInteger, k::Integer)

`bitrotate(x, k)` implements bitwise rotation.
It returns the value of `x` with its bits rotated left `k` times.
A negative value of `k` will rotate to the right instead.

!!! compat "Julia 1.5"
    This function requires Julia 1.5 or later.

See also: [`<<`](@ref), [`circshift`](@ref), [`BitArray`](@ref).

```jldoctest
julia> bitrotate(UInt8(114), 2)
0xc9

julia> bitstring(bitrotate(0b01110010, 2))
"11001001"

julia> bitstring(bitrotate(0b01110010, -2))
"10011100"

julia> bitstring(bitrotate(0b01110010, 8))
"01110010"
```
"""
bitrotate(x::T, k::Integer) where {T <: BitInteger} =
    (x << ((sizeof(T) << 3 - 1) & k)) | (x >>> ((sizeof(T) << 3 - 1) & -k))

````
-/
def bitrotate {t : IntTy} {K M : Type} (land : JInt .i64 → K → M) (neg : K → K)
    (shl lshr : JInt t → M → JInt t) (x : JInt t) (k : K) : JInt t :=
  -- `sizeof(T) << 3 - 1` parses as `(sizeof(T) << 3) - 1`; `&`, unary `-`, `<<` and `>>>` on
  -- `k`'s type are the parameters.
  let m := sub (shl_Int (lit .i64 (sizeofT t)) (lit .i64 3)) (lit .i64 1)
  bor (shl x (land m k)) (lshr x (land m (neg k)))

/-! ## Remainders to types (lines 667-705) -/

/--
Julia source: base/int.jl:667-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
for fname in (:mod, :rem)
    @eval @doc """
        rem(x::Integer, T::Type{<:Integer})::T
        mod(x::Integer, T::Type{<:Integer})::T
        %(x::Integer, T::Type{<:Integer})::T

    Find `y::T` such that `x` ≡ `y` (mod n), where n is the number of integers representable
    in `T`, and `y` is an integer in `[typemin(T),typemax(T)]`.
    If `T` can represent any integer (e.g. `T == BigInt`), then this operation corresponds to
    a conversion to `T`.

    # Examples
    ```jldoctest
    julia> x = 129 % Int8
    -127

    julia> typeof(x)
    Int8

    julia> x = 129 % BigInt
    129

    julia> typeof(x)
    BigInt
    ```
    """ $fname(x::Integer, T::Type{<:Integer})
end

````

Julia source: base/int.jl:696-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Signed, ::Type{Unsigned}) = x % unsigned(typeof(x))
```
-/
def rem_Signed_Unsigned {t : IntTy} (x : JInt t) : JInt t.toUnsigned :=
  Generic.rem_Signed_Unsigned (fun _ => ()) id (fun x _ => remT t.toUnsigned x) x
/--
Julia source: base/int.jl:697-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Unsigned, ::Type{Signed}) = x % signed(typeof(x))
```
-/
def rem_Unsigned_Signed {t : IntTy} (x : JInt t) : JInt (signedType t) :=
  Generic.rem_Unsigned_Signed (fun _ => ()) id (fun x _ => remT (signedType t) x) x
/--
Julia source: base/int.jl:698-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Integer, T::Type{<:Integer}) = convert(T, x)  # `x % T` falls back to `convert`
```
-/
def rem_Integer_Type {I T : Type} (convert : I → Jl T) (x : I) : Jl T := convert x
/--
Julia source: base/int.jl:699-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Integer, ::Type{Bool}) = ((x & 1) != 0)
```
-/
def rem_Integer_Bool {t : IntTy} (x : JInt t) : Bool :=
  Generic.rem_Integer_Bool (fun x n => binop band x (lit .i64 n))
    (fun r n => !(eq r (lit .i64 n))) x
/--
Julia source: base/int.jl:700-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x, ::Type{Union{}}, slurp...) = throw(MethodError(rem, (x, Union{}, slurp...)))
```
-/
def rem_Union {I Tail α : Type} (x : I) (_type : UnionBottom) (slurp : Tail) :
    Except (InvalidMethodError (I × UnionBottom × Tail)) α :=
  .error { function := .rem, arguments := (x, .type, slurp) }
/--
Julia source: base/int.jl:701-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x::Integer, ::Type{T}) where {T<:Integer} = rem(x, T)
```
-/
def mod_Integer_Type (T : IntTy) {t : IntTy} (x : JInt t) : JInt T :=
  Generic.mod_Integer_Type (fun x (_ : Unit) => remT T x) () x
/--
Julia source: base/int.jl:702-703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod(x, ::Type{Union{}}, slurp...) = throw(MethodError(mod, (x, Union{}, slurp...)))

```
-/
def mod_Union {I Tail α : Type} (x : I) (_type : UnionBottom) (slurp : Tail) :
    Except (InvalidMethodError (I × UnionBottom × Tail)) α :=
  .error { function := .mod, arguments := (x, .type, slurp) }
/--
Julia source: base/int.jl:704-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_trunc(::Type{T}, x::Integer) where {T<:Integer} = rem(x, T)
```
-/
def unsafe_trunc (T : IntTy) {t : IntTy} (x : JInt t) : JInt T :=
  Generic.unsafe_trunc (fun x (_ : Unit) => remT T x) () x
/--
Julia source: base/int.jl:705-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_trunc(::Type{Union{}}, slurp...) = throw(MethodError(unsafe_trunc, (Union{}, slurp...)))

```
-/
def unsafe_trunc_Union {Tail α : Type} (_type : UnionBottom) (slurp : Tail) :
    Except (InvalidMethodError (UnionBottom × Tail)) α :=
  .error { function := .unsafeTrunc, arguments := (.type, slurp) }

/-! ## String macros (lines 707-804) -/

/--
Julia source: base/int.jl:707-727 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
## integer construction ##

"""
    @int128_str str

Parse `str` as an [`Int128`](@ref).
Throw an `ArgumentError` if the string is not a valid integer.

# Examples
```jldoctest
julia> int128"123456789123"
123456789123

julia> int128"123456789123.4"
ERROR: LoadError: ArgumentError: invalid base 10 digit '.' in "123456789123.4"
[...]
```
"""
macro int128_str(s::String)
    return parse(Int128, s)
end
````
-/
def int128_str {α : Type} (parse : String → Jl α) (s : String) : Jl α := parse s
/--
Julia source: base/int.jl:728-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @uint128_str str

Parse `str` as an [`UInt128`](@ref).
Throw an `ArgumentError` if the string is not a valid integer.

# Examples
```
julia> uint128"123456789123"
0x00000000000000000000001cbe991a83

julia> uint128"-123456789123"
ERROR: LoadError: ArgumentError: invalid base 10 digit '-' in "-123456789123"
[...]
```
"""
macro uint128_str(s::String)
    return parse(UInt128, s)
end
````
-/
def uint128_str {α : Type} (parse : String → Jl α) (s : String) : Jl α := parse s

/-- The loop of `@big_str` over the characters between the first and the last: the printed
characters, or `none` at the first `_` next to a `.`. -/
def big_str_loop : List Char → Bool → Bool → Option (List Char)
  | [], _, _ => some []
  | c :: cs, is_prev_underscore, is_prev_dot =>
    let printed := if c != '_' then [c] else []
    if c == '_' && is_prev_dot then none
    else if c == '.' && is_prev_underscore then none
    else (big_str_loop cs (c == '_') (c == '.')).map (printed ++ ·)

/--
Julia source: base/int.jl:748-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @big_str str

Parse a string into a [`BigInt`](@ref) or [`BigFloat`](@ref),
and throw an `ArgumentError` if the string is not a valid number.
For integers `_` is allowed in the string as a separator.

# Examples
```jldoctest
julia> big"123_456"
123456

julia> big"7891.5"
7891.5

julia> big"_"
ERROR: ArgumentError: invalid number format _ for BigInt or BigFloat
[...]
```

!!! warning
    Using `@big_str` for constructing [`BigFloat`](@ref) values may not result
    in the behavior that might be naively expected: as a macro, `@big_str`
    obeys the global precision ([`setprecision`](@ref)) and rounding mode
    ([`setrounding`](@ref)) settings as they are at *load time*. Thus, a
    function like `() -> precision(big"0.3")` returns a constant whose value
    depends on the value of the precision at the point when the function is
    defined, **not** at the precision at the time when the function is called.
"""
macro big_str(s::String)
    message = "invalid number format $s for BigInt or BigFloat"
    throw_error =  :(throw(ArgumentError($message)))
    if '_' in s
        # remove _ in s[2:end-1].
        # Do not allow '_' right before or after dot.
        bf = IOBuffer(sizehint=ncodeunits(s))
        c = s[1]
        print(bf, c)
        is_prev_underscore = (c == '_')
        is_prev_dot = (c == '.')
        for c in SubString(s, nextind(s, 1), prevind(s, lastindex(s)))
            c != '_' && print(bf, c)
            c == '_' && is_prev_dot && return throw_error
            c == '.' && is_prev_underscore && return throw_error
            is_prev_underscore = (c == '_')
            is_prev_dot = (c == '.')
        end
        print(bf, s[end])
        s = unsafe_takestring!(bf)
    end
    n = tryparse(BigInt, s)
    n === nothing || return n
    n = tryparse(BigFloat, s)
    n === nothing || return n
    return throw_error
end

````
-/
def big_str {α : Type} (tryparseBigInt tryparseBigFloat : List Char → Option α) (s : List Char) :
    Jl α :=
  let throw_error : Jl α :=
    .error (.argumentError s!"invalid number format {String.ofList s} for BigInt or BigFloat")
  let normalized : Option (List Char) :=
    if s.contains '_' then
      match s with
      | [] => some []
      | c :: _ =>
        -- `SubString(s, nextind(s, 1), prevind(s, lastindex(s)))`, then `print(bf, s[end])`
        (big_str_loop ((s.drop 1).dropLast) (c == '_') (c == '.')).map
          (fun mid => c :: mid ++ [s.getLast!])
    else some s
  match normalized with
  | none => throw_error
  | some s =>
    match tryparseBigInt s with
    | some n => .ok n
    | none =>
      match tryparseBigFloat s with
      | some n => .ok n
      | none => throw_error

/-! ## Promotion rules (lines 806-822) -/

/--
Julia source: base/int.jl:806-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## integer promotions ##

# with different sizes, promote to larger type
promote_rule(::Type{Int16}, ::Union{Type{Int8}, Type{UInt8}}) = Int16
```
-/
def promote_rule_Int16 (_T : IntTy) : IntTy := .i16
/--
Julia source: base/int.jl:810-810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Int32}, ::Union{Type{Int16}, Type{Int8}, Type{UInt16}, Type{UInt8}}) = Int32
```
-/
def promote_rule_Int32 (_T : IntTy) : IntTy := .i32
/--
Julia source: base/int.jl:811-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Int64}, ::Union{Type{Int16}, Type{Int32}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt8}}) = Int64
```
-/
def promote_rule_Int64 (_T : IntTy) : IntTy := .i64
/--
Julia source: base/int.jl:812-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Int128}, ::Union{Type{Int16}, Type{Int32}, Type{Int64}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt64}, Type{UInt8}}) = Int128
```
-/
def promote_rule_Int128 (_T : IntTy) : IntTy := .i128
/--
Julia source: base/int.jl:813-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt16}, ::Union{Type{Int8}, Type{UInt8}}) = UInt16
```
-/
def promote_rule_UInt16 (_T : IntTy) : IntTy := .u16
/--
Julia source: base/int.jl:814-814 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt32}, ::Union{Type{Int16}, Type{Int8}, Type{UInt16}, Type{UInt8}}) = UInt32
```
-/
def promote_rule_UInt32 (_T : IntTy) : IntTy := .u32
/--
Julia source: base/int.jl:815-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt64}, ::Union{Type{Int16}, Type{Int32}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt8}}) = UInt64
```
-/
def promote_rule_UInt64 (_T : IntTy) : IntTy := .u64
/--
Julia source: base/int.jl:816-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt128}, ::Union{Type{Int16}, Type{Int32}, Type{Int64}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt64}, Type{UInt8}}) = UInt128
```
-/
def promote_rule_UInt128 (_T : IntTy) : IntTy := .u128
/--
Julia source: base/int.jl:817-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# with mixed signedness and same size, Unsigned wins
promote_rule(::Type{UInt8},   ::Type{Int8}  ) = UInt8
```
-/
def promote_rule_UInt8_Int8 : IntTy := .u8
/--
Julia source: base/int.jl:819-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt16},  ::Type{Int16} ) = UInt16
```
-/
def promote_rule_UInt16_Int16 : IntTy := .u16
/--
Julia source: base/int.jl:820-820 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt32},  ::Type{Int32} ) = UInt32
```
-/
def promote_rule_UInt32_Int32 : IntTy := .u32
/--
Julia source: base/int.jl:821-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt64},  ::Type{Int64} ) = UInt64
```
-/
def promote_rule_UInt64_Int64 : IntTy := .u64
/--
Julia source: base/int.jl:822-823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{UInt128}, ::Type{Int128}) = UInt128

```
-/
def promote_rule_UInt128_Int128 : IntTy := .u128

/-- *dispatch*: `promote_rule(T, S)` for BitInteger types: the method of lines 809-822 whose
signature matches, or `none` for `promotion.jl`'s fallback `Bottom`. -/
def promote_rule (T S : IntTy) : Option IntTy :=
  match T, S with
  | .i16, .i8 | .i16, .u8 => some (promote_rule_Int16 S)
  | .i32, .i16 | .i32, .i8 | .i32, .u16 | .i32, .u8 => some (promote_rule_Int32 S)
  | .i64, .i16 | .i64, .i32 | .i64, .i8 | .i64, .u16 | .i64, .u32 | .i64, .u8 =>
    some (promote_rule_Int64 S)
  | .i128, .i16 | .i128, .i32 | .i128, .i64 | .i128, .i8 | .i128, .u16 | .i128, .u32
  | .i128, .u64 | .i128, .u8 => some (promote_rule_Int128 S)
  | .u16, .i8 | .u16, .u8 => some (promote_rule_UInt16 S)
  | .u32, .i16 | .u32, .i8 | .u32, .u16 | .u32, .u8 => some (promote_rule_UInt32 S)
  | .u64, .i16 | .u64, .i32 | .u64, .i8 | .u64, .u16 | .u64, .u32 | .u64, .u8 =>
    some (promote_rule_UInt64 S)
  | .u128, .i16 | .u128, .i32 | .u128, .i64 | .u128, .i8 | .u128, .u16 | .u128, .u32
  | .u128, .u64 | .u128, .u8 => some (promote_rule_UInt128 S)
  | .u8, .i8 => some promote_rule_UInt8_Int8
  | .u16, .i16 => some promote_rule_UInt16_Int16
  | .u32, .i32 => some promote_rule_UInt32_Int32
  | .u64, .i64 => some promote_rule_UInt64_Int64
  | .u128, .i128 => some promote_rule_UInt128_Int128
  | _, _ => none

/-! ## `typemin`, `typemax` (lines 824-908) -/

/--
Julia source: base/int.jl:824-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
## traits ##

"""
    typemin(T)
    typemin(::T)

The lowest value representable by the given (real) numeric type `T`.
The argument can alternatively be an instance of `T`.

See also: [`floatmin`](@ref), [`maxintfloat`](@ref), [`typemax`](@ref), [`eps`](@ref).

# Examples
```jldoctest
julia> typemin(Int8)
-128

julia> typemin(UInt32)
0x00000000

julia> typemin(Float16)
-Inf16

julia> typemin(Float32)
-Inf32

julia> floatmin(Float32)  # smallest positive finite Float32 floating point number
1.1754944f-38

julia> nextfloat(-Inf32) == -floatmax(Float32)  # equivalent ways of getting the lowest finite Float32 floating point number
true
```
"""
function typemin end

"""
    typemax(T)
    typemax(::T)

The highest value representable by the given (real) numeric type `T`.
The argument can alternatively be an instance of `T`.

See also: [`floatmax`](@ref), [`maxintfloat`](@ref), [`typemin`](@ref), [`eps`](@ref).

# Examples
```jldoctest
julia> typemax(Int8)
127

julia> typemax(UInt32)
0xffffffff

julia> typemax(Float64)
Inf

julia> typemax(Float32)
Inf32

julia> floatmax(Float32)  # largest positive finite Float32 floating point number
3.4028235f38
```
"""
function typemax end

typemin(::Type{Int8  }) = Int8(-128)
````
-/
def typemin_Int8 : JInt .i8 := lit .i8 (-128)
/--
Julia source: base/int.jl:888-888 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Int8  }) = Int8(127)
```
-/
def typemax_Int8 : JInt .i8 := lit .i8 127
/--
Julia source: base/int.jl:889-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{UInt8 }) = UInt8(0)
```
-/
def typemin_UInt8 : JInt .u8 := lit .u8 0
/--
Julia source: base/int.jl:890-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{UInt8 }) = UInt8(255)
```
-/
def typemax_UInt8 : JInt .u8 := lit .u8 255
/--
Julia source: base/int.jl:891-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Int16 }) = Int16(-32768)
```
-/
def typemin_Int16 : JInt .i16 := lit .i16 (-32768)
/--
Julia source: base/int.jl:892-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Int16 }) = Int16(32767)
```
-/
def typemax_Int16 : JInt .i16 := lit .i16 32767
/--
Julia source: base/int.jl:893-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{UInt16}) = UInt16(0)
```
-/
def typemin_UInt16 : JInt .u16 := lit .u16 0
/--
Julia source: base/int.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{UInt16}) = UInt16(65535)
```
-/
def typemax_UInt16 : JInt .u16 := lit .u16 65535
/--
Julia source: base/int.jl:895-895 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Int32 }) = Int32(-2147483648)
```
-/
def typemin_Int32 : JInt .i32 := lit .i32 (-2147483648)
/--
Julia source: base/int.jl:896-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Int32 }) = Int32(2147483647)
```
-/
def typemax_Int32 : JInt .i32 := lit .i32 2147483647
/--
Julia source: base/int.jl:897-897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{UInt32}) = UInt32(0)
```
-/
def typemin_UInt32 : JInt .u32 := lit .u32 0
/--
Julia source: base/int.jl:898-898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{UInt32}) = UInt32(4294967295)
```
-/
def typemax_UInt32 : JInt .u32 := lit .u32 4294967295
/--
Julia source: base/int.jl:899-899 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Int64 }) = -9223372036854775808
```
-/
def typemin_Int64 : JInt .i64 := lit .i64 (-9223372036854775808)
/--
Julia source: base/int.jl:900-900 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Int64 }) = 9223372036854775807
```
-/
def typemax_Int64 : JInt .i64 := lit .i64 9223372036854775807
/--
Julia source: base/int.jl:901-901 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{UInt64}) = UInt64(0)
```
-/
def typemin_UInt64 : JInt .u64 := lit .u64 0
/--
Julia source: base/int.jl:902-902 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{UInt64}) = 0xffffffffffffffff
```
-/
def typemax_UInt64 : JInt .u64 := lit .u64 0xffffffffffffffff
/--
Julia source: base/int.jl:903-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval typemin(::Type{UInt128}) = $(convert(UInt128, 0))
```
-/
def typemin_UInt128 : JInt .u128 := lit .u128 0
/--
Julia source: base/int.jl:904-904 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval typemax(::Type{UInt128}) = $(bitcast(UInt128, convert(Int128, -1)))
```
-/
def typemax_UInt128 : JInt .u128 := bitcast .u128 (lit .i128 (-1)) rfl
/--
Julia source: base/int.jl:905-905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval typemin(::Type{Int128} ) = $(convert(Int128, 1) << 127)
```
-/
def typemin_Int128 : JInt .i128 := shl_Int (lit .i128 1) (lit .i64 127)
/--
Julia source: base/int.jl:906-906 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval typemax(::Type{Int128} ) = $(bitcast(Int128, typemax(UInt128) >> 1))
```
-/
def typemax_Int128 : JInt .i128 := bitcast .i128 (shr_Int typemax_UInt128 (lit .i64 1)) rfl
/--
Julia source: base/int.jl:907-907 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Union{}}, slurp...) = throw(MethodError(typemin, (Union{}, slurp...)))
```
-/
def typemin_Union {Tail α : Type} (_type : UnionBottom) (slurp : Tail) :
    Except (InvalidMethodError (UnionBottom × Tail)) α :=
  .error { function := .typemin, arguments := (.type, slurp) }
/--
Julia source: base/int.jl:908-910 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Union{}}, slurp...) = throw(MethodError(typemax, (Union{}, slurp...)))


```
-/
def typemax_Union {Tail α : Type} (_type : UnionBottom) (slurp : Tail) :
    Except (InvalidMethodError (UnionBottom × Tail)) α :=
  .error { function := .typemax, arguments := (.type, slurp) }

/-- *dispatch*: `typemin(T)` for a BitInteger type `T`. -/
def typemin : (t : IntTy) → JInt t
  | .i8 => typemin_Int8 | .u8 => typemin_UInt8 | .i16 => typemin_Int16 | .u16 => typemin_UInt16
  | .i32 => typemin_Int32 | .u32 => typemin_UInt32 | .i64 => typemin_Int64
  | .u64 => typemin_UInt64 | .i128 => typemin_Int128 | .u128 => typemin_UInt128
/-- *dispatch*: `typemax(T)` for a BitInteger type `T`. -/
def typemax : (t : IntTy) → JInt t
  | .i8 => typemax_Int8 | .u8 => typemax_UInt8 | .i16 => typemax_Int16 | .u16 => typemax_UInt16
  | .i32 => typemax_Int32 | .u32 => typemax_UInt32 | .i64 => typemax_Int64
  | .u64 => typemax_UInt64 | .i128 => typemax_Int128 | .u128 => typemax_UInt128

/-! ## `widen`, `widemul` (lines 911-928) -/

/--
Julia source: base/int.jl:911-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Int8}) = Int16
```
-/
def widen_Int8 : IntTy := .i16
/--
Julia source: base/int.jl:912-912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Int16}) = Int32
```
-/
def widen_Int16 : IntTy := .i32
/--
Julia source: base/int.jl:913-913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Int32}) = Int64
```
-/
def widen_Int32 : IntTy := .i64
/--
Julia source: base/int.jl:914-914 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Int64}) = Int128
```
-/
def widen_Int64 : IntTy := .i128
/--
Julia source: base/int.jl:915-915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{UInt8}) = UInt16
```
-/
def widen_UInt8 : IntTy := .u16
/--
Julia source: base/int.jl:916-916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{UInt16}) = UInt32
```
-/
def widen_UInt16 : IntTy := .u32
/--
Julia source: base/int.jl:917-917 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{UInt32}) = UInt64
```
-/
def widen_UInt32 : IntTy := .u64
/--
Julia source: base/int.jl:918-919 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{UInt64}) = UInt128

```
-/
def widen_UInt64 : IntTy := .u128

/-- *dispatch*: `widen(T)` for a BitInteger type of at most 64 bits; `none` for the 128-bit
types, whose `widen` is `BigInt` (`gmp.jl`). -/
def widenType : IntTy → Option IntTy
  | .i8 => some widen_Int8 | .i16 => some widen_Int16 | .i32 => some widen_Int32
  | .i64 => some widen_Int64 | .u8 => some widen_UInt8 | .u16 => some widen_UInt16
  | .u32 => some widen_UInt32 | .u64 => some widen_UInt64 | .i128 | .u128 => none

/--
Julia source: base/int.jl:920-923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# a few special cases,
# Int64*UInt64 => Int128
# |x|<=2^(k-1), |y|<=2^k-1   =>   |x*y|<=2^(2k-1)-1
widemul(x::Signed,y::Unsigned) = widen(x) * signed(widen(y))
```
-/
def widemul_Signed_Unsigned {s u ws wu : IntTy} (widenS : JInt s → JInt ws)
    (widenU : JInt u → JInt wu) (x : JInt s) (y : JInt u) : JInt (ws.promote wu.toSigned) :=
  Generic.widemul_Signed_Unsigned widenS widenU signed (binop mulSame) x y
/--
Julia source: base/int.jl:924-924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widemul(x::Unsigned,y::Signed) = signed(widen(x)) * widen(y)
```
-/
def widemul_Unsigned_Signed {u s wu ws : IntTy} (widenU : JInt u → JInt wu)
    (widenS : JInt s → JInt ws) (x : JInt u) (y : JInt s) : JInt (wu.toSigned.promote ws) :=
  Generic.widemul_Unsigned_Signed widenU widenS signed (binop mulSame) x y
/--
Julia source: base/int.jl:925-926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# multiplication by Bool doesn't require widening
widemul(x::Bool,y::Bool) = x * y
```
-/
def widemul_Bool_Bool (x y : Bool) : Bool :=
  -- `x * y` is `bool.jl`'s `*(x::Bool, y::Bool) = x & y`.
  x && y
/--
Julia source: base/int.jl:927-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widemul(x::Bool,y::Number) = x * y
```
-/
def widemul_Bool_Number {N P : Type} (mul : Bool → N → P) (x : Bool) (y : N) : P := mul x y
/--
Julia source: base/int.jl:928-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widemul(x::Number,y::Bool) = x * y


```
-/
def widemul_Number_Bool {N P : Type} (mul : N → Bool → P) (x : N) (y : Bool) : P := mul x y

/-! ## `mul_hi` (lines 106-141) -/

/--
Julia source: base/int.jl:105-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    mul_hi(a::T, b::T) where {T<:Base.Integer}

Return the higher half of the product of `a` and `b` where `T` is a fixed size integer.

# Examples
```jldoctest
julia> Base.mul_hi(12345678987654321, 123456789)
82624

julia> (widen(12345678987654321) * 123456789) >> 64
82624

julia> Base.mul_hi(0xff, 0xff)
0xfe
```
"""
function mul_hi(a::T, b::T) where {T<:Integer}
    ((widen(a)*b) >>> Base.top_set_bit(-1 % T)) % T
end
````
-/
def mul_hi_Integer {t w : IntTy} (widen : JInt t → JInt w) (a b : JInt t) : JInt t :=
  Generic.mul_hi_Integer widen (binop mulSame) (fun n => remT t (lit .i64 n)) top_set_bit
    lshr_Int (remT t) a b
/--
Julia source: base/int.jl:126-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function mul_hi(a::UInt128, b::UInt128)
    shift = sizeof(a)*4
    mask = typemax(UInt128) >> shift
    a1, a2 = a >>> shift, a & mask
    b1, b2 = b >>> shift, b & mask
    a1b1, a1b2, a2b1, a2b2 = a1*b1, a1*b2, a2*b1, a2*b2
    carry = ((a1b2 & mask) + (a2b1 & mask) + (a2b2 >>> shift)) >>> shift
    a1b1 + (a1b2 >>> shift) + (a2b1 >>> shift) + carry
end
```
-/
def mul_hi_UInt128 (a b : JInt .u128) : JInt .u128 :=
  let shift := mul (sizeof a) (lit .i64 4)
  let mask := shr_Int typemax_UInt128 shift
  let a1 := lshr_Int a shift
  let a2 := band a mask
  let b1 := lshr_Int b shift
  let b2 := band b mask
  let a1b1 := mul_128 a1 b1
  let a1b2 := mul_128 a1 b2
  let a2b1 := mul_128 a2 b1
  let a2b2 := mul_128 a2 b2
  let carry := lshr_Int (add (add (band a1b2 mask) (band a2b1 mask)) (lshr_Int a2b2 shift)) shift
  add (add (add a1b1 (lshr_Int a1b2 shift)) (lshr_Int a2b1 shift)) carry
/--
Julia source: base/int.jl:136-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function mul_hi(a::Int128, b::Int128)
    shift = sizeof(a)*8 - 1
    t1, t2 = (a >> shift) & b % UInt128, (b >> shift) & a % UInt128
    (mul_hi(a % UInt128, b % UInt128) -% t1 -% t2) % Int128
end

```
-/
def mul_hi_Int128 (a b : JInt .i128) : JInt .i128 :=
  let shift := sub (mul (sizeof a) (lit .i64 8)) (lit .i64 1)
  -- `(a >> shift) & b % UInt128` parses as `((a >> shift) & b) % UInt128`.
  let t1 := remT .u128 (band (shr_Int a shift) b)
  let t2 := remT .u128 (band (shr_Int b shift) a)
  remT .i128 (subWrap (subWrap (mul_hi_UInt128 (remT .u128 a) (remT .u128 b)) t1) t2)

/-! ## 32-bit platforms (lines 931-1081) -/

-- UNTRANSLATED
-- defined only when Int === Int32; not defined on the 64-bit target
-- Source: base/int.jl:931-1082 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ## wide multiplication, Int128 multiply and divide ##
-- 
-- if Core.sizeof(Int) == 4
--     function widemul(u::Int64, v::Int64)
--         local u0::UInt64, v0::UInt64, w0::UInt64
--         local u1::Int64, v1::Int64, w1::UInt64, w2::Int64, t::UInt64
-- 
--         u0 = u & 0xffffffff; u1 = u >> 32
--         v0 = v & 0xffffffff; v1 = v >> 32
--         w0 = u0 *% v0
--         t = reinterpret(UInt64, u1) *% v0 +% (w0 >>> 32)
--         w2 = reinterpret(Int64, t) >> 32
--         w1 = u0 *% reinterpret(UInt64, v1) +% (t & 0xffffffff)
--         hi = u1 *% v1 +% w2 +% (reinterpret(Int64, w1) >> 32)
--         lo = (w0 & 0xffffffff) +% (w1 << 32)
--         return (Int128(hi) << 64) +% Int128(lo)
--     end
-- 
--     function widemul(u::UInt64, v::UInt64)
--         local u0::UInt64, v0::UInt64, w0::UInt64
--         local u1::UInt64, v1::UInt64, w1::UInt64, w2::UInt64, t::UInt64
-- 
--         u0 = u & 0xffffffff; u1 = u >>> 32
--         v0 = v & 0xffffffff; v1 = v >>> 32
--         w0 = u0 *% v0
--         t = u1 *% v0 +% (w0 >>> 32)
--         w2 = t >>> 32
--         w1 = u0 *% v1 +% (t & 0xffffffff)
--         hi = u1 *% v1 +% w2 +% (w1 >>> 32)
--         lo = (w0 & 0xffffffff) +% (w1 << 32)
--         return (UInt128(hi) << 64) +% UInt128(lo)
--     end
-- 
--     function *(u::Int128, v::Int128)
--         u0 = u % UInt64; u1 = Int64(u >> 64)
--         v0 = v % UInt64; v1 = Int64(v >> 64)
--         lolo = widemul(u0, v0)
--         lohi = widemul(reinterpret(Int64, u0), v1)
--         hilo = widemul(u1, reinterpret(Int64, v0))
--         t = reinterpret(UInt128, hilo) +% (lolo >>> 64)
--         w1 = reinterpret(UInt128, lohi) +% (t & 0xffffffffffffffff)
--         return Int128(lolo & 0xffffffffffffffff) +% (reinterpret(Int128, w1) << 64)
--     end
-- 
--     function *(u::UInt128, v::UInt128)
--         u0 = u % UInt64; u1 = UInt64(u>>>64)
--         v0 = v % UInt64; v1 = UInt64(v>>>64)
--         lolo = widemul(u0, v0)
--         lohi = widemul(u0, v1)
--         hilo = widemul(u1, v0)
--         t = hilo +% (lolo >>> 64)
--         w1 = lohi +% (t & 0xffffffffffffffff)
--         return (lolo & 0xffffffffffffffff) +% (UInt128(w1) << 64)
--     end
-- 
--     function _setbit(x::UInt128, i)
--         # faster version of `return x | (UInt128(1) << i)`
--         j = i >> 5
--         y = UInt128(one(UInt32) << (i & 0x1f))
--         if j == 0
--             return x | y
--         elseif j == 1
--             return x | (y << 32)
--         elseif j == 2
--             return x | (y << 64)
--         elseif j == 3
--             return x | (y << 96)
--         end
--         return x
--     end
-- 
--     function divrem(x::UInt128, y::UInt128)
--         iszero(y) && throw(DivideError())
--         if (x >> 64) % UInt64 == 0
--             if (y >> 64) % UInt64 == 0
--                 # fast path: upper 64 bits are zero, so we can fallback to UInt64 division
--                 q64, x64 = divrem(x % UInt64, y % UInt64)
--                 return UInt128(q64), UInt128(x64)
--             else
--                 # this implies y>x, so
--                 return zero(UInt128), x
--             end
--         end
--         n = leading_zeros(y) - leading_zeros(x)
--         q = zero(UInt128)
--         ys = y << n
--         while n >= 0
--             # ys == y * 2^n
--             if ys <= x
--                 x -= ys
--                 q = _setbit(q, n)
--                 if (x >> 64) % UInt64 == 0
--                     # exit early, similar to above fast path
--                     if (y >> 64) % UInt64 == 0
--                         q64, x64 = divrem(x % UInt64, y % UInt64)
--                         q |= q64
--                         x = UInt128(x64)
--                     end
--                     return q, x
--                 end
--             end
--             ys >>>= 1
--             n -= 1
--         end
--         return q, x
--     end
-- 
--     function div(x::Int128, y::Int128)
--         (x == typemin(Int128)) & (y == -1) && throw(DivideError())
--         return Int128(div(BigInt(x), BigInt(y)))::Int128
--     end
--     div(x::UInt128, y::UInt128) = divrem(x, y)[1]
-- 
--     function rem(x::Int128, y::Int128)
--         return Int128(rem(BigInt(x), BigInt(y)))::Int128
--     end
-- 
--     function rem(x::UInt128, y::UInt128)
--         iszero(y) && throw(DivideError())
--         if (x >> 64) % UInt64 == 0
--             if (y >> 64) % UInt64 == 0
--                 # fast path: upper 64 bits are zero, so we can fallback to UInt64 division
--                 return UInt128(rem(x % UInt64, y % UInt64))
--             else
--                 # this implies y>x, so
--                 return x
--             end
--         end
--         n = leading_zeros(y) - leading_zeros(x)
--         ys = y << n
--         while n >= 0
--             # ys == y * 2^n
--             if ys <= x
--                 x -= ys
--                 if (x >> 64) % UInt64 == 0
--                     # exit early, similar to above fast path
--                     if (y >> 64) % UInt64 == 0
--                         x = UInt128(rem(x % UInt64, y % UInt64))
--                     end
--                     return x
--                 end
--             end
--             ys >>>= 1
--             n -= 1
--         end
--         return x
--     end
-- 
--     function mod(x::Int128, y::Int128)
--         return Int128(mod(BigInt(x), BigInt(y)))::Int128
--     end
-- else
-- /Source

/-! ## `bitreverse` (lines 1102-1134) -/

/--
Julia source: base/int.jl:1101-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const _mask1_uint128 = (UInt128(0x5555555555555555) << 64) | UInt128(0x5555555555555555)
```
-/
def _mask1_uint128 : JInt .u128 :=
  bor (shl_Int (widenTo .u128 (lit .u64 0x5555555555555555)) (lit .i64 64))
    (widenTo .u128 (lit .u64 0x5555555555555555))
/--
Julia source: base/int.jl:1103-1103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _mask2_uint128 = (UInt128(0x3333333333333333) << 64) | UInt128(0x3333333333333333)
```
-/
def _mask2_uint128 : JInt .u128 :=
  bor (shl_Int (widenTo .u128 (lit .u64 0x3333333333333333)) (lit .i64 64))
    (widenTo .u128 (lit .u64 0x3333333333333333))
/--
Julia source: base/int.jl:1104-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _mask4_uint128 = (UInt128(0x0f0f0f0f0f0f0f0f) << 64) | UInt128(0x0f0f0f0f0f0f0f0f)

```
-/
def _mask4_uint128 : JInt .u128 :=
  bor (shl_Int (widenTo .u128 (lit .u64 0x0f0f0f0f0f0f0f0f)) (lit .i64 64))
    (widenTo .u128 (lit .u64 0x0f0f0f0f0f0f0f0f))

/--
Julia source: base/int.jl:1106-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    bitreverse(x)

Reverse the order of bits in integer `x`. `x` must have a fixed bit width,
e.g. be an `Int16` or `Int32`.

!!! compat "Julia 1.5"
    This function requires Julia 1.5 or later.

# Examples
```jldoctest
julia> bitreverse(0x8080808080808080)
0x0101010101010101

julia> reverse(bitstring(0xa06e)) == bitstring(bitreverse(0xa06e))
true
```
"""
function bitreverse(x::BitInteger)
    # TODO: consider using llvm.bitreverse intrinsic
    z = unsigned(x)
    mask1 = _mask1_uint128 % typeof(z)
    mask2 = _mask2_uint128 % typeof(z)
    mask4 = _mask4_uint128 % typeof(z)
    z = ((z & mask1) << 1) | ((z >> 1) & mask1)
    z = ((z & mask2) << 2) | ((z >> 2) & mask2)
    z = ((z & mask4) << 4) | ((z >> 4) & mask4)
    return bswap(z) % typeof(x)
end
````
-/
def bitreverse {t : IntTy} (x : JInt t) : JInt t :=
  let z := unsigned x
  let mask1 := remT t.toUnsigned _mask1_uint128
  let mask2 := remT t.toUnsigned _mask2_uint128
  let mask4 := remT t.toUnsigned _mask4_uint128
  let z := bor (shl_Int (band z mask1) (lit .i64 1)) (band (shr_Int z (lit .i64 1)) mask1)
  let z := bor (shl_Int (band z mask2) (lit .i64 2)) (band (shr_Int z (lit .i64 2)) mask2)
  let z := bor (shl_Int (band z mask4) (lit .i64 4)) (band (shr_Int z (lit .i64 4)) mask4)
  remT t (bswap z)

namespace Generic
structure BigStringOps (B : Type) where
  ncodeunits : String → Nat
  getindex : String → Nat → Char
  nextind : String → Nat → Nat
  prevind : String → Nat → Nat
  lastindex : String → Nat
  substring : String → Nat → Nat → List Char
  ioBuffer : Nat → B
  print : B → Char → B
  unsafe_takestring : B → String

def big_str_print_loop {B : Type} (print : B → Char → B) :
    List Char → B → Bool → Bool → Option B
  | [], bf, _, _ => some bf
  | c :: cs, bf, is_prev_underscore, is_prev_dot =>
    let bf := if c != '_' then print bf c else bf
    if c == '_' && is_prev_dot then none
    else if c == '.' && is_prev_underscore then none
    else big_str_print_loop print cs bf (c == '_') (c == '.')

/--
Julia source: base/int.jl:748-805 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @big_str str

Parse a string into a [`BigInt`](@ref) or [`BigFloat`](@ref),
and throw an `ArgumentError` if the string is not a valid number.
For integers `_` is allowed in the string as a separator.

# Examples
```jldoctest
julia> big"123_456"
123456

julia> big"7891.5"
7891.5

julia> big"_"
ERROR: ArgumentError: invalid number format _ for BigInt or BigFloat
[...]
```

!!! warning
    Using `@big_str` for constructing [`BigFloat`](@ref) values may not result
    in the behavior that might be naively expected: as a macro, `@big_str`
    obeys the global precision ([`setprecision`](@ref)) and rounding mode
    ([`setrounding`](@ref)) settings as they are at *load time*. Thus, a
    function like `() -> precision(big"0.3")` returns a constant whose value
    depends on the value of the precision at the point when the function is
    defined, **not** at the precision at the time when the function is called.
"""
macro big_str(s::String)
    message = "invalid number format $s for BigInt or BigFloat"
    throw_error =  :(throw(ArgumentError($message)))
    if '_' in s
        # remove _ in s[2:end-1].
        # Do not allow '_' right before or after dot.
        bf = IOBuffer(sizehint=ncodeunits(s))
        c = s[1]
        print(bf, c)
        is_prev_underscore = (c == '_')
        is_prev_dot = (c == '.')
        for c in SubString(s, nextind(s, 1), prevind(s, lastindex(s)))
            c != '_' && print(bf, c)
            c == '_' && is_prev_dot && return throw_error
            c == '.' && is_prev_underscore && return throw_error
            is_prev_underscore = (c == '_')
            is_prev_dot = (c == '.')
        end
        print(bf, s[end])
        s = unsafe_takestring!(bf)
    end
    n = tryparse(BigInt, s)
    n === nothing || return n
    n = tryparse(BigFloat, s)
    n === nothing || return n
    return throw_error
end

````
-/


def big_str {α B : Type} (ops : BigStringOps B)
    (tryparseBigInt tryparseBigFloat : String → Option α) (s : String) : Jl α :=
  let throw_error : Jl α :=
    .error (.argumentError s!"invalid number format {s} for BigInt or BigFloat")
  let normalized : Option String :=
    if s.contains '_' then
      let bf := ops.ioBuffer (ops.ncodeunits s)
      let c := ops.getindex s 1
      let bf := ops.print bf c
      let is_prev_underscore := c == '_'
      let is_prev_dot := c == '.'
      match big_str_print_loop ops.print
          (ops.substring s (ops.nextind s 1) (ops.prevind s (ops.lastindex s)))
          bf is_prev_underscore is_prev_dot with
      | none => none
      | some bf =>
        let bf := ops.print bf (ops.getindex s (ops.lastindex s))
        some (ops.unsafe_takestring bf)
    else some s
  match normalized with
  | none => throw_error
  | some s =>
    match tryparseBigInt s with
    | some n => .ok n
    | none =>
      match tryparseBigFloat s with
      | some n => .ok n
      | none => throw_error

end Generic

namespace Generated
/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def add_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def sub_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def mul_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def and_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def or_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def xor_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def addWrap_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def subWrap_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

/--
Julia source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# issue #15489: since integer ops are unchecked, they shouldn't check promotion
for op in (:+, :-, :*, :&, :|, :xor, Symbol("+%"), Symbol("-%"), Symbol("*%"))
    @eval function $op(a::Integer, b::Integer)
        T = promote_typeof(a, b)
        aT, bT = a % T, b % T
        not_sametype((a, b), (aT, bT))
        return $op(aT, bT)
    end
end
```
-/
def mulWrap_Integer {A B Ty : Type} {V : Ty → Type}
    (promote_typeof : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (not_sametype : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)) (a : A) (b : B) :
    Jl (V (promote_typeof a b)) := do
  let T := promote_typeof a b
  let aT ← remA a T
  let bT ← remB b T
  let _ ← not_sametype (a, b) T (aT, bT)
  op T aT bT

end Generated

end JuliaLean.base.int
