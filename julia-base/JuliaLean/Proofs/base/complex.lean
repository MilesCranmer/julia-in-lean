import JuliaLean.base.complex
import JuliaLean.Registry.Types

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 5000

/-!
# Properties of `base/complex.jl`

Specifications of the methods modelled in `JuliaLean.base.complex`, stated from the
docstrings, the manual, and mathematical/IEEE invariants, with their proofs and refutations.

## Nothing to promise (pure forwarding / plumbing / empty generic declarations)
- `Complex@17`: `Complex(x::Real, y::Real) = Complex(promote(x,y)...)` — pure forwarding to `promote` and the inner struct constructor (also covered in `complex-type-algebra`).
- `Complex@47`: `Complex(z::Complex) = z` — identity constructor on an already-complex argument (also covered in `complex-type-algebra`).
- `float@56`: `float(::Type{Complex{T}}) where {T<:AbstractFloat} = Complex{T}` — identity type mapping on complex float types (also covered in `complex-type-algebra`).
- `float@57`: `float(::Type{Complex{T}}) where {T} = Complex{float(T)}` — pure forwarding of `float(T)` into `Complex{...}` (also covered in `complex-type-algebra`).
- `real@120`: `real(T::Type) = typeof(real(zero(T)))` — pure fallback forwarding `zero`, `real`, and `typeof`.
- `real@121`: `real(::Type{T}) where {T<:Real} = T` — identity type mapping on real types (also covered in `complex-type-algebra`).
- `real@123`: `real(::Type{Union{}}) = Union{}` — bottom-type dispatch identity (also covered in `complex-type-algebra`).
- `real@124`: `real(::Type{Union{}}, slurp...) = throw(MethodError(real, (Union{}, slurp...)))` — bottom-type arity pruning throwing `MethodError` (also covered in `complex-type-algebra`).
- `complex@168`: `complex(z::Complex) = z` — identity conversion on an already-complex value (also covered in `complex-type-algebra`).
- `complex@169`: `complex(x::Real) = Complex(x)` — pure forwarding to `Complex(x)` (also covered in `complex-type-algebra`).
- `complex@170`: `complex(x::Real, y::Real) = Complex(x, y)` — pure forwarding to `Complex(x, y)` (also covered in `complex-type-algebra`).
- `complex@190`: `complex(::Type{T}) where {T<:Real} = Complex{T}` — wraps a real type `T` in `Complex{T}` (also covered in `complex-type-algebra`).
- `complex@191`: `complex(::Type{Complex{T}}) where {T<:Real} = Complex{T}` — identity on `Complex{T}` (also covered in `complex-type-algebra`).
- `complex@192`: `complex(::Type{Union{}}) = Union{}` — bottom-type dispatch identity (also covered in `complex-type-algebra`).
- `complex@195`: `complex(::Type{Union{}}, slurp...) = throw(MethodError(complex, (Union{}, slurp...)))` — bottom-type arity pruning throwing `MethodError` (also covered in `complex-type-algebra`).
- `inv@288`: `inv(z::Complex{<:Integer}) = inv(float(z))` — pure forwarding to `float` and `inv` (also covered in `complex-inv-properties`).
- `+@290`: `+(z::Complex) = Complex(+real(z), +imag(z))` — unary `+` forwarding to componentwise unary `+` (also covered in `complex-gaussian-ring`).
- `_mulsub@303`: `_mulsub(a, b, c) = _mulsub(promote(a, b, c)...)` — pure promotion forwarding helper (also covered in `complex-gaussian-ring`).
- `muladd@348`: `muladd(x::Real, z::Complex, y::Union{Real,Complex}) = muladd(z, x, y)` — argument-commuting forwarding wrapper (also covered in `complex-gaussian-ring`).
- `/@357`: `/(a::R, z::S) where {R<:Real,S<:Complex} = (T = promote_type(R,S); a*inv(T(z)))` — pure forwarding to `promote_type`, conversion, `inv`, and `*` (also covered in `complex-div-scaling-and-inf`).
- `cis@586`: `function cis end` — empty generic function declaration with no method body.
- `cispi@617`: `function cispi end` — empty generic function declaration with no method body.
- `log10@695`: `log10(z::Complex) = (a = log(z); a/log(oftype(real(a),10)))` — pure scaling of `log(z)` by `log(10)` (also covered in `complex-exp-log-special-values`).
- `log2@699`: `log2(z::Complex) = (a = log(z); a/log(oftype(real(a),2)))` — pure scaling of `log(z)` by `log(2)` (also covered in `complex-exp-log-special-values`).
- `^@882`: `^(z::Complex{T}, p::Complex{T}) where T<:Real = _cpow(z, p)` — pure forwarding to `_cpow` (also covered in `complex-pow-bool-and-zero`).
- `^@883`: `^(z::Complex{T}, p::T) where T<:Real = _cpow(z, p)` — pure forwarding to `_cpow` (also covered in `complex-pow-bool-and-zero`).
- `^@884`: `^(z::T, p::Complex{T}) where T<:Real = _cpow(z, p)` — pure forwarding to `_cpow` (also covered in `complex-pow-bool-and-zero`).
- `^@886`: `^(z::Complex, n::Bool) = n ? z : one(z)` — ambiguity-resolving forwarding to `one(z)` (also covered in `complex-pow-bool-and-zero`).
- `^@887`: `^(z::Complex, n::Integer) = z^Complex(n)` — pure forwarding to `Complex(n)` and `^` (also covered in `complex-pow-bool-and-zero`).
- `^@889`: `^(z::Complex{<:AbstractFloat}, n::Bool) = n ? z : one(z)` — ambiguity-resolving forwarding to `one(z)` (also covered in `complex-pow-bool-and-zero`).
- `^@890`: `^(z::Complex{<:Integer}, n::Bool) = n ? z : one(z)` — ambiguity-resolving forwarding to `one(z)` (also covered in `complex-pow-bool-and-zero`).
- `^@896`: `^(z::Complex{T}, p::S) where {T<:Real,S<:Real}` — pure promotion forwarding to `promote_type(T,S)` and `^` (also covered in `complex-pow-bool-and-zero`).
- `^@900`: `^(z::T, p::Complex{S}) where {T<:Real,S<:Real}` — pure promotion forwarding to `promote_type(T,S)` and `^` (also covered in `complex-pow-bool-and-zero`).
- `tan@943`: `tan(z::Complex) = (w = tanh(Complex(-zi, zr)); Complex(imag(w), -real(w)))` — rotation wrapper around `tanh` (also unfolded with `tanh_Complex` in `complex-trig-hyperbolic-identities`).
- `atan@986`: `atan(z::Complex) = (w = atanh(Complex(-imag(z),real(z))); Complex(imag(w),-real(w)))` — rotation wrapper around `atanh` (also unfolded with `atanh_Complex` in `complex-trig-hyperbolic-identities`).
- `sinh@991`: `sinh(z::Complex) = (w = sin(Complex(zi, zr)); Complex(imag(w),real(w)))` — rotation wrapper around `sin` (also unfolded with `sin_Complex` in `complex-trig-hyperbolic-identities`).
- `cosh@997`: `cosh(z::Complex) = cos(Complex(zi,-zr))` — rotation wrapper around `cos` (also unfolded with `cos_Complex` in `complex-trig-hyperbolic-identities`).
- `asinh@1024`: `asinh(z::Complex) = (w = asin(Complex(-imag(z),real(z))); Complex(imag(w),-real(w)))` — rotation wrapper around `asin` (also unfolded with `asin_Complex` in `complex-trig-hyperbolic-identities`).
- `float@1129`: `float(z::Complex{<:AbstractFloat}) = z` — identity on complex floats (also covered in `complex-round-array-eps`).
- `float@1130`: `float(z::Complex) = Complex(float(real(z)), float(imag(z)))` — componentwise forwarding to `float` (also covered in `complex-round-array-eps`).
- `big@1132`: `big(::Type{Complex{T}}) where {T<:Real} = Complex{big(T)}` — pure type forwarding to `big(T)` (also covered in `complex-round-array-eps`).
- `big@1133`: `big(z::Complex{T}) where {T<:Real} = Complex{big(T)}(z)` — pure forwarding to `Complex{big(T)}(z)` (also covered in `complex-round-array-eps`).
- `complex@1153`: `complex(A::AbstractArray{<:Complex}) = A` — identity on complex arrays (also covered in `complex-round-array-eps`).
-/

namespace JuliaLean.Proofs.base.complex

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.Registry JuliaLean.base.complex

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun hc => Except.ok.inj hc |> h)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun hc => Except.error.inj hc |> h)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-! ## Specification vocabulary -/

/-- Whether a `Jl` computation returned normally. -/
def jlOk {α : Type} : Jl α → Bool
  | .ok _ => true
  | .error _ => false

/-- Exact value of a finite binary64 number as a fraction `(num, den)` with `den > 0`. -/
def ratOf (x : F64) : Int × Int := ((F64.toRat x).1, ((F64.toRat x).2 : Int))

/-- Numerator and denominator of the exact real part `(ac + bd)/(c² + d²)` of `z / w`. -/
def exactDivRe (z w : ComplexF64) : Int × Int :=
  let (na, da) := ratOf z.re
  let (nb, db) := ratOf z.im
  let (nc, dc) := ratOf w.re
  let (nd, dd) := ratOf w.im
  ((na * nc * db * dd + nb * nd * da * dc) * dc * dd,
   da * db * (nc * nc * dd * dd + nd * nd * dc * dc))

/-- Exact `x * y`: the binary64 product is finite and equal to the rational product. -/
def exactMul (x y : F64) : Bool :=
  let p := ratOf (F64.mul x y)
  let a := ratOf x
  let b := ratOf y
  F64.isfinite (F64.mul x y) && p.1 * (a.2 * b.2) == a.1 * b.1 * p.2

/-- Exact `x + y` (`sign = 1`) or `x - y` (`sign = -1`): finite and equal to the rational sum. -/
def exactAdd (x y : F64) (sign : Int) : Bool :=
  let s := if sign < 0 then F64.sub x y else F64.add x y
  let p := ratOf s
  let a := ratOf x
  let b := ratOf y
  F64.isfinite s && p.1 * (a.2 * b.2) == (a.1 * b.2 + sign * b.1 * a.2) * p.2

/-- Exact Gaussian-integer product. -/
def gmul (a b : Int × Int) : Int × Int := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Exact Gaussian-integer power by repeated multiplication. -/
def gpow (a : Int × Int) : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => gmul (gpow a n) a

/-- `t` can represent the mathematical integer `z` without overflow. -/
def fits (t : IntTy) (z : Int) : Prop := t.min ≤ z ∧ z ≤ t.max

/-- Widening map on signed `IntTy` below 128 bits (`base/int.jl:911-914`). -/
def widenSignedInt : IntTy → Option IntTy
  | .i8 => some .i16
  | .i16 => some .i32
  | .i32 => some .i64
  | .i64 => some .i128
  | _ => none

/-! ## Two's-complement modular reduction lemmas -/

theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp at h ⊢ <;> omega

theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

@[simp] theorem wrapInt_wrapInt (t : IntTy) (z : Int) : wrapInt t (wrapInt t z) = wrapInt t z :=
  wrapInt_congr t (wrapInt_emod_self t z)

@[simp] theorem wrapInt_val {t : IntTy} (x : JInt t) : wrapInt t x.val = x.val :=
  wrapInt_of_inRange t x.val x.property

@[simp] theorem wrapInt_add_left (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a + b) = wrapInt t (a + b) :=
  wrapInt_congr t (by rw [Int.add_emod, wrapInt_emod_self, ← Int.add_emod])

@[simp] theorem wrapInt_add_right (t : IntTy) (a b : Int) : wrapInt t (a + wrapInt t b) = wrapInt t (a + b) :=
  wrapInt_congr t (by rw [Int.add_emod, wrapInt_emod_self, ← Int.add_emod])

@[simp] theorem wrapInt_sub_left (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a - b) = wrapInt t (a - b) :=
  wrapInt_congr t (by rw [Int.sub_emod, wrapInt_emod_self, ← Int.sub_emod])

@[simp] theorem wrapInt_sub_right (t : IntTy) (a b : Int) : wrapInt t (a - wrapInt t b) = wrapInt t (a - b) :=
  wrapInt_congr t (by rw [Int.sub_emod, wrapInt_emod_self, ← Int.sub_emod])

@[simp] theorem wrapInt_mul_left (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a * b) = wrapInt t (a * b) :=
  wrapInt_congr t (by rw [Int.mul_emod, wrapInt_emod_self, ← Int.mul_emod])

@[simp] theorem wrapInt_mul_right (t : IntTy) (a b : Int) : wrapInt t (a * wrapInt t b) = wrapInt t (a * b) :=
  wrapInt_congr t (by rw [Int.mul_emod, wrapInt_emod_self, ← Int.mul_emod])

@[simp] theorem wrapInt_neg (t : IntTy) (a : Int) : wrapInt t (-wrapInt t a) = wrapInt t (-a) :=
  wrapInt_congr t (by cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega)

@[simp] theorem jint_add_val {t : IntTy} (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
@[simp] theorem jint_sub_val {t : IntTy} (a b : JInt t) : (a - b).val = wrapInt t (a.val - b.val) := rfl
@[simp] theorem jint_mul_val {t : IntTy} (a b : JInt t) : (a * b).val = wrapInt t (a.val * b.val) := rfl
@[simp] theorem jint_neg_val {t : IntTy} (a : JInt t) : (-a).val = wrapInt t (-a.val) := rfl
@[simp] theorem jint_wrap_val (t : IntTy) (x : Int) : (JInt.wrap t x).val = wrapInt t x := rfl
@[simp] theorem jint_lit_val (t : IntTy) (x : Int) : (JInt.lit t x).val = wrapInt t x := rfl

/-! ## Binary64 bit-level lemmas -/

theorem neg_neg_f64 (x : F64) : F64.neg (F64.neg x) = x := by
  have hx : x.toNat < 2^64 := x.isLt
  by_cases h : x.toNat ≥ 2^63
  · have h1 : F64.neg x = BitVec.ofNat 64 (x.toNat - 2^63) := by
      simp [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h]
    have h2 : ¬ ((BitVec.ofNat 64 (x.toNat - 2^63)).toNat ≥ 2^63) := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1]
    simp only [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h2, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  · have h1 : F64.neg x = BitVec.ofNat 64 (x.toNat + 2^63) := by
      simp [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h]
    have h2 : (BitVec.ofNat 64 (x.toNat + 2^63)).toNat ≥ 2^63 := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1]
    simp only [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h2, decide_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem abs_neg_f64 (x : F64) : F64.abs (F64.neg x) = F64.abs x := by
  have hx : x.toNat < 2^64 := x.isLt
  unfold F64.abs F64.neg F64.signbit F64.toBits F64.ofBits
  apply BitVec.eq_of_toNat_eq
  by_cases h : x.toNat ≥ 2^63
  · simp only [h, decide_true, ↓reduceIte, BitVec.toNat_ofNat]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]; omega

theorem exponentField_neg (x : F64) : F64.exponentField (F64.neg x) = F64.exponentField x := by
  have hx : x.toNat < 2^64 := x.isLt
  unfold F64.exponentField F64.neg F64.signbit F64.toBits F64.ofBits
  by_cases h : x.toNat ≥ 2^63
  · simp only [h, decide_true, ↓reduceIte, BitVec.toNat_ofNat]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]; omega

theorem fraction_neg (x : F64) : F64.fraction (F64.neg x) = F64.fraction x := by
  have hx : x.toNat < 2^64 := x.isLt
  unfold F64.fraction F64.neg F64.signbit F64.toBits F64.ofBits
  by_cases h : x.toNat ≥ 2^63
  · simp only [h, decide_true, ↓reduceIte, BitVec.toNat_ofNat]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]; omega

theorem signbit_neg (x : F64) : F64.signbit (F64.neg x) = !F64.signbit x := by
  have hx : x.toNat < 2^64 := x.isLt
  unfold F64.neg F64.signbit F64.toBits F64.ofBits
  by_cases h : x.toNat ≥ 2^63
  · simp only [h, decide_true, ↓reduceIte, BitVec.toNat_ofNat, Bool.not_true, decide_eq_false_iff_not]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat, Bool.not_false, decide_eq_true_eq]; omega

theorem isnan_neg (x : F64) : F64.isnan (F64.neg x) = F64.isnan x := by
  simp [F64.isnan, exponentField_neg, fraction_neg]

theorem isinf_neg (x : F64) : F64.isinf (F64.neg x) = F64.isinf x := by
  simp [F64.isinf, abs_neg_f64]

theorem isfinite_neg (x : F64) : F64.isfinite (F64.neg x) = F64.isfinite x := by
  simp [F64.isfinite, exponentField_neg]

theorem iszero_neg (x : F64) : F64.iszero (F64.neg x) = F64.iszero x := by
  simp [F64.iszero, abs_neg_f64]

theorem isfinite_iff_not_nan_not_inf (x : F64) :
    F64.isfinite x = (!F64.isnan x && !F64.isinf x) := by
  have hx : x.toNat < 2^64 := x.isLt
  unfold F64.isfinite F64.isnan F64.isinf F64.exponentField F64.fraction F64.abs F64.toBits F64.ofBits
  simp only [BitVec.toNat_ofNat]
  by_cases he : x.toNat / 2^52 % 2048 = 2047
  · by_cases hf : x.toNat % 2^52 = 0
    · have hinf : x.toNat % 2^63 % 2^64 = 0x7ff0000000000000 := by omega
      simp [he, hf, hinf]
    · have hinf : x.toNat % 2^63 % 2^64 ≠ 0x7ff0000000000000 := by omega
      simp [he, hf, hinf]
  · have h1 : (x.toNat / 2^52 % 2048 != 2047) = true := bne_iff_ne.mpr he
    have h2 : (x.toNat / 2^52 % 2048 == 2047) = false := beq_eq_false_iff_ne.mpr he
    have h3 : (x.toNat % 2^63 % 2^64 == 0x7ff0000000000000) = false := by
      rw [beq_eq_false_iff_ne]; omega
    simp [h1, h2, h3]

theorem isfinite_Complex_iff (z : ComplexF64) :
    isfinite_Complex F64.isfinite z = (!isnan_Complex F64.isnan z && !isinf_Complex F64.isinf z) := by
  simp only [isfinite_Complex, isnan_Complex, isinf_Complex, real_Complex, imag_Complex,
    isfinite_iff_not_nan_not_inf]
  cases F64.isnan z.re <;> cases F64.isnan z.im <;> cases F64.isinf z.re <;> cases F64.isinf z.im <;> rfl

theorem toRat_neg (x : F64) : F64.toRat (F64.neg x) = (-(F64.toRat x).1, (F64.toRat x).2) := by
  unfold F64.toRat
  rw [isfinite_neg, exponentField_neg, fraction_neg, signbit_neg]
  by_cases hf : F64.isfinite x = true
  · simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize F64.exponentField x = e
    generalize (F64.fraction x + if e == 0 then 0 else 2^52) = m
    generalize (if e == 0 then (-1074 : Int) else (e : Int) - 1075) = p
    cases F64.signbit x <;> split <;> simp [Int.neg_mul]
  · simp [hf]

theorem mul_neg_neg_of_not_nan (x y : F64) (hx : F64.isnan x = false) (hy : F64.isnan y = false) :
    F64.mul (F64.neg x) (F64.neg y) = F64.mul x y := by
  unfold F64.mul
  rw [isnan_neg, isnan_neg, hx, hy, isinf_neg, isinf_neg, iszero_neg, iszero_neg,
    signbit_neg, signbit_neg, toRat_neg, toRat_neg]
  have hb : ((!F64.signbit x) != (!F64.signbit y)) = (F64.signbit x != F64.signbit y) := by
    cases F64.signbit x <;> cases F64.signbit y <;> rfl
  have hm : (-(F64.toRat x).1) * (-(F64.toRat y).1) = (F64.toRat x).1 * (F64.toRat y).1 := by grind
  simp only [hb, hm, Bool.false_eq_true, ↓reduceIte]

theorem muladd_neg_neg_of_not_nan (x y z : F64) (hx : F64.isnan x = false) (hy : F64.isnan y = false) :
    F64.muladd (F64.neg x) (F64.neg y) z = F64.muladd x y z := by
  unfold F64.muladd F64.fma
  rw [isnan_neg, isnan_neg, hx, hy, isinf_neg, isinf_neg, iszero_neg, iszero_neg,
    signbit_neg, signbit_neg, toRat_neg, toRat_neg]
  have hb : ((!F64.signbit x) != (!F64.signbit y)) = (F64.signbit x != F64.signbit y) := by
    cases F64.signbit x <;> cases F64.signbit y <;> rfl
  have hm : (-(F64.toRat x).1) * (-(F64.toRat y).1) = (F64.toRat x).1 * (F64.toRat y).1 := by grind
  simp only [hb, hm, Bool.false_eq_true, ↓reduceIte]


theorem mul_neg_right_eq_mul_neg_left (x y : F64) (hx : F64.isnan x = false) (hy : F64.isnan y = false) :
    F64.mul x (F64.neg y) = F64.mul (F64.neg x) y := by
  unfold F64.mul
  rw [isnan_neg, isnan_neg, hx, hy, isinf_neg, isinf_neg, iszero_neg, iszero_neg,
    signbit_neg, signbit_neg, toRat_neg, toRat_neg]
  have hb : (F64.signbit x != (!F64.signbit y)) = ((!F64.signbit x) != F64.signbit y) := by
    cases F64.signbit x <;> cases F64.signbit y <;> rfl
  have hm : (F64.toRat x).1 * (-(F64.toRat y).1) = (-(F64.toRat x).1) * (F64.toRat y).1 := by grind
  simp only [hb, hm, Bool.false_eq_true, ↓reduceIte]

theorem toRat_zero_fst (s : Bool) : (F64.toRat (F64.zero s)).1 = 0 := by
  unfold F64.toRat
  have hf : F64.isfinite (F64.zero s) = true := by cases s <;> decide
  have he : F64.exponentField (F64.zero s) = 0 := by cases s <;> decide
  have hfr : F64.fraction (F64.zero s) = 0 := by cases s <;> decide
  simp [hf, he, hfr]

theorem toRat_snd_pos (x : F64) (hfin : F64.isfinite x = true) : 0 < (F64.toRat x).2 := by
  unfold F64.toRat
  simp only [hfin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hp : (if F64.exponentField x == 0 then (-1074 : Int) else (F64.exponentField x : Int) - 1075) ≥ 0
  · simp only [hp, ↓reduceIte]; decide
  · simp only [hp, ↓reduceIte]; exact Nat.two_pow_pos _
theorem mul_zero_f64 (x : F64) (s : Bool) (hfin : F64.isfinite x = true) :
    F64.mul x (F64.zero s) = F64.zero (F64.signbit x != s) := by
  have hnx : F64.isnan x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hfin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin; exact hfin.1
  have hix : F64.isinf x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hfin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin; exact hfin.2
  have hn0 : F64.isnan (F64.zero s) = false := by cases s <;> decide
  have hi0 : F64.isinf (F64.zero s) = false := by cases s <;> decide
  have hsb0 : F64.signbit (F64.zero s) = s := by cases s <;> decide
  have hd : ((F64.toRat x).2 * (F64.toRat (F64.zero s)).2 == 0) = false := by
    have h1 := toRat_snd_pos x hfin
    have h2 := toRat_snd_pos (F64.zero s) (by cases s <;> decide)
    have hpos := Nat.mul_pos h1 h2
    rw [beq_eq_false_iff_ne]; omega
  unfold F64.mul F64.roundRat
  simp [hnx, hix, hn0, hi0, hsb0, toRat_zero_fst, hd]

theorem zero_mul_f64 (x : F64) (s : Bool) (hfin : F64.isfinite x = true) :
    F64.mul (F64.zero s) x = F64.zero (s != F64.signbit x) := by
  have hnx : F64.isnan x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hfin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin; exact hfin.1
  have hix : F64.isinf x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hfin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin; exact hfin.2
  have hn0 : F64.isnan (F64.zero s) = false := by cases s <;> decide
  have hi0 : F64.isinf (F64.zero s) = false := by cases s <;> decide
  have hsb0 : F64.signbit (F64.zero s) = s := by cases s <;> decide
  have hd : ((F64.toRat (F64.zero s)).2 * (F64.toRat x).2 == 0) = false := by
    have h1 := toRat_snd_pos (F64.zero s) (by cases s <;> decide)
    have h2 := toRat_snd_pos x hfin
    have hpos := Nat.mul_pos h1 h2
    rw [beq_eq_false_iff_ne]; omega
  unfold F64.mul F64.roundRat
  simp [hnx, hix, hn0, hi0, hsb0, toRat_zero_fst, hd]

def f64Fl2 (n d : Nat) : Int :=
  let e : Int := (n.log2 : Int) - (d.log2 : Int)
  let below := if e ≥ 0 then n < d * 2^e.toNat else n * 2^(-e).toNat < d
  if below then e - 1 else e

def f64Rq (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2*r > d || (2*r == d && q % 2 == 1) then q + 1 else q

def f64Pack (negative : Bool) (q : Nat) (k : Int) : F64 :=
  if q == 0 then F64.zero negative
  else
    let carry := q ≥ 2^53
    let m := if carry then q / 2 else q
    let p := if carry then k + 1 else k
    let exponent := p + 1075
    if exponent ≥ 2047 then F64.inf negative
    else
      let magnitude :=
        if m < 2^52 then m
        else exponent.toNat * 2^52 + (m - 2^52)
      F64.ofBits ((if negative then 2^63 else 0) + magnitude)

theorem f64_roundRat_eq (n : Int) (d : Nat) (z : Bool) : F64.roundRat n d z =
    if d == 0 then if n == 0 then F64.nan else F64.inf (decide (n < 0))
    else if n == 0 then F64.zero z
    else
      let negative := decide (n < 0)
      let a := n.natAbs
      let e := f64Fl2 a d
      if e ≥ 1024 then F64.inf negative
      else if e < -1075 then F64.zero negative
      else
        let k := max (e - 52) (-1074)
        let scaled :=
          if k ≥ 0 then (a, d * 2^k.toNat)
          else (a * 2^(-k).toNat, d)
        f64Pack negative (f64Rq scaled.1 scaled.2) k := rfl

theorem neg_ofBits_sign (b : Bool) (mag : Nat) :
    F64.neg (F64.ofBits ((if b then 2^63 else 0) + mag)) =
      F64.ofBits ((if !b then 2^63 else 0) + mag) := by
  unfold F64.neg F64.signbit F64.ofBits F64.toBits
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false]
  · by_cases h : (BitVec.ofNat 64 (0 + mag)).toNat ≥ 2^63
    · simp only [h, decide_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat] at h ⊢; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat] at h ⊢; omega
  · by_cases h : (BitVec.ofNat 64 (2^63 + mag)).toNat ≥ 2^63
    · simp only [h, decide_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat] at h ⊢; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat] at h ⊢; omega

theorem f64Pack_neg (b : Bool) (q : Nat) (k : Int) :
    f64Pack (!b) q k = F64.neg (f64Pack b q k) := by
  have hz : F64.zero (!b) = F64.neg (F64.zero b) := by cases b <;> decide
  have hi : F64.inf (!b) = F64.neg (F64.inf b) := by cases b <;> decide
  unfold f64Pack
  by_cases hq : (q == 0) = true
  · simp [hq, hz]
  · simp only [hq, Bool.false_eq_true, ↓reduceIte]
    by_cases hexp : (if q ≥ 2^53 then k + 1 else k) + 1075 ≥ 2047
    · simp only [hexp, ↓reduceIte]; exact hi
    · simp only [hexp, ↓reduceIte]; exact (neg_ofBits_sign b _).symm

theorem roundRat_neg_of_den_ne_zero (n : Int) (d : Nat) (z : Bool) (hd : (d == 0) = false) :
    F64.roundRat (-n) d (!z) = F64.neg (F64.roundRat n d z) := by
  have hz : ∀ b : Bool, F64.zero (!b) = F64.neg (F64.zero b) := by intro b; cases b <;> decide
  have hi : ∀ b : Bool, F64.inf (!b) = F64.neg (F64.inf b) := by intro b; cases b <;> decide
  rw [f64_roundRat_eq (-n) d (!z), f64_roundRat_eq n d z]
  simp only [hd, Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg]
  by_cases hn : n = 0
  · subst hn; simp [hz]
  · have hn1 : ((-n == 0) = true) ↔ False := by simp [hn]
    have hn2 : ((n == 0) = true) ↔ False := by simp [hn]
    have hdec : decide (-n < 0) = !decide (n < 0) := by
      by_cases hlt : n < 0
      · rw [decide_eq_false (by omega), decide_eq_true hlt]; rfl
      · rw [decide_eq_true (by omega), decide_eq_false hlt]; rfl
    simp only [hn1, hn2, ↓reduceIte, hdec]
    generalize f64Fl2 n.natAbs d = e
    by_cases he1 : e ≥ 1024
    · simp only [he1, ↓reduceIte]; exact hi _
    · simp only [he1, ↓reduceIte]
      by_cases he2 : e < -1075
      · simp only [he2, ↓reduceIte]; exact hz _
      · simp only [he2, ↓reduceIte]; exact f64Pack_neg _ _ _
theorem toRat_fst_ne_zero (y : F64) (hfin : F64.isfinite y = true) (hnz : F64.iszero y = false) :
    (F64.toRat y).1 ≠ 0 := by
  have hm : F64.fraction y + (if F64.exponentField y == 0 then 0 else 2^52) > 0 := by
    by_cases he : (F64.exponentField y == 0) = true
    · simp only [he, ↓reduceIte, Nat.add_zero]
      unfold F64.exponentField F64.toBits at he
      unfold F64.iszero F64.abs F64.toBits F64.ofBits at hnz
      unfold F64.fraction F64.toBits
      simp only [BitVec.toNat_ofNat, beq_iff_eq, beq_eq_false_iff_ne] at he hnz
      omega
    · simp only [he, Bool.false_eq_true, ↓reduceIte]; omega
  unfold F64.toRat
  simp only [hfin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize F64.fraction y + (if F64.exponentField y == 0 then 0 else 2^52) = m at hm
  generalize (if F64.exponentField y == 0 then (-1074 : Int) else (F64.exponentField y : Int) - 1075) = p
  have hs : (if F64.signbit y = true then -(m : Int) else (m : Int)) ≠ 0 := by
    cases F64.signbit y <;> simp <;> omega
  by_cases hp : p ≥ 0
  · simp only [hp, ↓reduceIte]
    have h2 : (2 ^ p.toNat : Nat) > 0 := Nat.two_pow_pos _
    intro hmul
    rcases Int.mul_eq_zero.mp hmul with h1 | h1
    · exact hs h1
    · omega
  · simp only [hp, ↓reduceIte]; exact hs

def f64QuietNaN (x : F64) : F64 :=
  if F64.fraction x < 2^51 then F64.ofBits (F64.toBits x + 2^51) else x

def f64InvalidNaN : F64 := F64.ofBits 0xfff8000000000000

theorem f64_div_eq (x y : F64) : F64.div x y =
    let negative := F64.signbit x != F64.signbit y
    if F64.isnan x then f64QuietNaN x
    else if F64.isnan y then f64QuietNaN y
    else if (F64.isinf x && F64.isinf y) || (F64.iszero x && F64.iszero y) then f64InvalidNaN
    else if F64.isinf x then F64.inf negative
    else if F64.isinf y then F64.zero negative
    else if F64.iszero y then F64.inf negative
    else
      let a := F64.toRat x
      let b := F64.toRat y
      let numerator := a.1 * (b.2 : Int)
      F64.roundRat (if b.1 < 0 then -numerator else numerator)
        (a.2 * b.1.natAbs) negative := rfl

theorem f64QuietNaN_neg (x : F64) : f64QuietNaN (F64.neg x) = F64.neg (f64QuietNaN x) := by
  have hx : x.toNat < 2^64 := x.isLt
  unfold f64QuietNaN
  rw [fraction_neg]
  by_cases hf : F64.fraction x < 2^51
  · simp only [hf, ↓reduceIte]
    have hfrac : x.toNat % 2^52 < 2^51 := hf
    unfold F64.neg F64.signbit F64.toBits F64.ofBits
    by_cases hs : x.toNat ≥ 2^63
    · have hs2 : (BitVec.ofNat 64 (x.toNat + 2^51)).toNat ≥ 2^63 := by
        rw [BitVec.toNat_ofNat]; omega
      simp only [hs, hs2, decide_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
    · have hs2 : ¬ ((BitVec.ofNat 64 (x.toNat + 2^51)).toNat ≥ 2^63) := by
        rw [BitVec.toNat_ofNat]; omega
      simp only [hs, hs2, decide_false, Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  · simp [hf]

theorem div_neg_left_of_not_inf_zero (x y : F64)
    (hinf : (F64.isinf x && F64.isinf y) = false)
    (hzero : (F64.iszero x && F64.iszero y) = false)
    (hy_nan : F64.isnan y = false) :
    F64.div (F64.neg x) y = F64.neg (F64.div x y) := by
  have hz : ∀ b : Bool, F64.zero (!b) = F64.neg (F64.zero b) := by intro b; cases b <;> decide
  have hi : ∀ b : Bool, F64.inf (!b) = F64.neg (F64.inf b) := by intro b; cases b <;> decide
  have hb : ((!F64.signbit x) != F64.signbit y) = !(F64.signbit x != F64.signbit y) := by
    cases F64.signbit x <;> cases F64.signbit y <;> rfl
  rw [f64_div_eq (F64.neg x) y, f64_div_eq x y]
  simp only [isnan_neg, isinf_neg, iszero_neg, signbit_neg, toRat_neg,
    hy_nan, hinf, hzero, hb, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  by_cases hnx : F64.isnan x = true
  · simp [hnx, f64QuietNaN_neg]
  · simp only [hnx, Bool.false_eq_true, ↓reduceIte]
    by_cases hix : F64.isinf x = true
    · simp [hix, hi]
    · simp only [hix, Bool.false_eq_true, ↓reduceIte]
      by_cases hiy : F64.isinf y = true
      · simp [hiy, hz]
      · simp only [hiy, Bool.false_eq_true, ↓reduceIte]
        by_cases hzy : F64.iszero y = true
        · simp [hzy, hi]
        · simp only [hzy, Bool.false_eq_true, ↓reduceIte]
          have hfx : F64.isfinite x = true := by
            rw [isfinite_iff_not_nan_not_inf]; simp [hnx, hix]
          have hfy : F64.isfinite y = true := by
            rw [isfinite_iff_not_nan_not_inf]; simp [hy_nan, hiy]
          have hzy' : F64.iszero y = false := Bool.eq_false_iff.mpr hzy
          have hb1 : (F64.toRat y).1 ≠ 0 := toRat_fst_ne_zero y hfy hzy'
          have hd : ((F64.toRat x).2 * (F64.toRat y).1.natAbs == 0) = false := by
            have h1 := toRat_snd_pos x hfx
            have h2 : (F64.toRat y).1.natAbs > 0 := Int.natAbs_pos.mpr hb1
            have hpos := Nat.mul_pos h1 h2
            rw [beq_eq_false_iff_ne]; omega
          have hnum : (if (F64.toRat y).1 < 0 then -(-((F64.toRat x).1) * ((F64.toRat y).2 : Int))
              else -((F64.toRat x).1) * ((F64.toRat y).2 : Int)) =
              -(if (F64.toRat y).1 < 0 then -((F64.toRat x).1 * ((F64.toRat y).2 : Int))
                else (F64.toRat x).1 * ((F64.toRat y).2 : Int)) := by
            split <;> simp only [Int.neg_mul]
          rw [hnum]
          exact roundRat_neg_of_den_ne_zero _ _ _ hd

theorem div_two_neg (x : F64) : F64.div (F64.neg x) Fl64.two = F64.neg (F64.div x Fl64.two) := by
  have hi2 : F64.isinf Fl64.two = false := by decide
  have hz2 : F64.iszero Fl64.two = false := by decide
  have hn2 : F64.isnan Fl64.two = false := by decide
  exact div_neg_left_of_not_inf_zero x Fl64.two (by simp [hi2]) (by simp [hz2]) hn2

theorem mul_neg_left_of_finite (x y : F64) (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    F64.mul (F64.neg x) y = F64.neg (F64.mul x y) := by
  have hnx : F64.isnan x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hx; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.1
  have hix : F64.isinf x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hx; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.2
  have hny : F64.isnan y = false := by
    rw [isfinite_iff_not_nan_not_inf] at hy; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy; exact hy.1
  have hiy : F64.isinf y = false := by
    rw [isfinite_iff_not_nan_not_inf] at hy; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy; exact hy.2
  have hd : ((F64.toRat x).2 * (F64.toRat y).2 == 0) = false := by
    have hpos := Nat.mul_pos (toRat_snd_pos x hx) (toRat_snd_pos y hy)
    rw [beq_eq_false_iff_ne]; omega
  have hb : ((!F64.signbit x) != F64.signbit y) = !(F64.signbit x != F64.signbit y) := by
    cases F64.signbit x <;> cases F64.signbit y <;> rfl
  unfold F64.mul
  simp only [isnan_neg, isinf_neg, signbit_neg, toRat_neg, hnx, hix, hny, hiy,
    Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Int.neg_mul, hb]
  exact roundRat_neg_of_den_ne_zero _ _ _ hd

theorem mul_neg_right_of_finite (x y : F64) (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    F64.mul x (F64.neg y) = F64.neg (F64.mul x y) := by
  have hnx : F64.isnan x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hx; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.1
  have hix : F64.isinf x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hx; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.2
  have hny : F64.isnan y = false := by
    rw [isfinite_iff_not_nan_not_inf] at hy; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy; exact hy.1
  have hiy : F64.isinf y = false := by
    rw [isfinite_iff_not_nan_not_inf] at hy; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy; exact hy.2
  have hd : ((F64.toRat x).2 * (F64.toRat y).2 == 0) = false := by
    have hpos := Nat.mul_pos (toRat_snd_pos x hx) (toRat_snd_pos y hy)
    rw [beq_eq_false_iff_ne]; omega
  have hb : (F64.signbit x != (!F64.signbit y)) = !(F64.signbit x != F64.signbit y) := by
    cases F64.signbit x <;> cases F64.signbit y <;> rfl
  unfold F64.mul
  simp only [isnan_neg, isinf_neg, signbit_neg, toRat_neg, hnx, hix, hny, hiy,
    Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Int.mul_neg, hb]
  exact roundRat_neg_of_den_ne_zero _ _ _ hd

theorem eq_inf_false_of_isinf_false (x y : F64) (hx : F64.isinf x = false)
    (hy_inf : F64.isinf y = true) (hy_nz : F64.iszero y = false) :
    F64.eq x y = false := by
  unfold F64.eq
  simp only [hy_nz, Bool.and_false, Bool.or_false]
  by_cases hb : (F64.toBits x == F64.toBits y) = true
  · have heq : x = y := by
      apply BitVec.eq_of_toNat_eq
      exact beq_iff_eq.mp hb
    subst heq; rw [hx] at hy_inf; contradiction
  · simp [hb]

theorem abs_ofBits_sign (b : Bool) (mag : Nat) :
    F64.abs (F64.ofBits ((if b then 2^63 else 0) + mag)) = F64.abs (F64.ofBits mag) := by
  unfold F64.abs F64.ofBits F64.toBits
  apply BitVec.eq_of_toNat_eq
  cases b <;> simp only [↓reduceIte, Bool.false_eq_true, BitVec.toNat_ofNat] <;> omega

theorem abs_f64Pack (b1 b2 : Bool) (q : Nat) (k : Int) :
    F64.abs (f64Pack b1 q k) = F64.abs (f64Pack b2 q k) := by
  have hz : F64.abs (F64.zero b1) = F64.abs (F64.zero b2) := by cases b1 <;> cases b2 <;> decide
  have hi : F64.abs (F64.inf b1) = F64.abs (F64.inf b2) := by cases b1 <;> cases b2 <;> decide
  unfold f64Pack
  by_cases hq : (q == 0) = true
  · simp [hq, hz]
  · simp only [hq, Bool.false_eq_true, ↓reduceIte]
    by_cases hexp : (if q ≥ 2^53 then k + 1 else k) + 1075 ≥ 2047
    · simp only [hexp, ↓reduceIte]; exact hi
    · simp only [hexp, ↓reduceIte]; rw [abs_ofBits_sign b1, abs_ofBits_sign b2]

theorem abs_roundRat_neg (n : Int) (d : Nat) (s1 s2 : Bool) :
    F64.abs (F64.roundRat (-n) d s1) = F64.abs (F64.roundRat n d s2) := by
  have hz : ∀ a b : Bool, F64.abs (F64.zero a) = F64.abs (F64.zero b) := by intro a b; cases a <;> cases b <;> decide
  have hi : ∀ a b : Bool, F64.abs (F64.inf a) = F64.abs (F64.inf b) := by intro a b; cases a <;> cases b <;> decide
  rw [f64_roundRat_eq (-n) d s1, f64_roundRat_eq n d s2]
  simp only [Int.natAbs_neg]
  by_cases hd : (d == 0) = true
  · by_cases hn : n = 0
    · subst hn; simp [hd]
    · have hn1 : ((-n == 0) = true) ↔ False := by simp [hn]
      have hn2 : ((n == 0) = true) ↔ False := by simp [hn]
      simp only [hd, hn1, hn2, ↓reduceIte]
      exact hi _ _
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]
    by_cases hn : n = 0
    · subst hn; simp only [BEq.rfl, ↓reduceIte]; exact hz _ _
    · have hn1 : ((-n == 0) = true) ↔ False := by simp [hn]
      have hn2 : ((n == 0) = true) ↔ False := by simp [hn]
      simp only [hn1, hn2, ↓reduceIte]
      generalize f64Fl2 n.natAbs d = e
      by_cases he1 : e ≥ 1024
      · simp only [he1, ↓reduceIte]; exact hi _ _
      · simp only [he1, ↓reduceIte]
        by_cases he2 : e < -1075
        · simp only [he2, ↓reduceIte]; exact hz _ _
        · simp only [he2, ↓reduceIte]; exact abs_f64Pack _ _ _ _
theorem abs_add_neg_neg_of_finite (x y : F64) (hx : F64.isfinite x = true) (hy : F64.isfinite y = true) :
    F64.abs (F64.add (F64.neg x) (F64.neg y)) = F64.abs (F64.add x y) := by
  have hnx : F64.isnan x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hx; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.1
  have hix : F64.isinf x = false := by
    rw [isfinite_iff_not_nan_not_inf] at hx; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx; exact hx.2
  have hny : F64.isnan y = false := by
    rw [isfinite_iff_not_nan_not_inf] at hy; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy; exact hy.1
  have hiy : F64.isinf y = false := by
    rw [isfinite_iff_not_nan_not_inf] at hy; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy; exact hy.2
  unfold F64.add
  simp only [isnan_neg, isinf_neg, signbit_neg, toRat_neg, hnx, hix, hny, hiy,
    Bool.false_eq_true, ↓reduceIte]
  have hnum : -((F64.toRat x).1) * ((F64.toRat y).2 : Int) + -((F64.toRat y).1) * ((F64.toRat x).2 : Int) =
      -((F64.toRat x).1 * ((F64.toRat y).2 : Int) + (F64.toRat y).1 * ((F64.toRat x).2 : Int)) := by
    simp only [Int.neg_mul]; omega
  rw [hnum]
  exact abs_roundRat_neg _ _ _ _

theorem copysign_eq_of_abs_eq (x1 x2 y : F64) (h : F64.abs x1 = F64.abs x2) :
    Fl64.copysign x1 y = Fl64.copysign x2 y := by
  unfold Fl64.copysign; rw [h]
theorem hypot_neg_right (x y : F64) : Fl64.hypot x (F64.neg y) = Fl64.hypot x y := by
  unfold Fl64.hypot
  rw [abs_neg_f64]

theorem hypot_neg_left (x y : F64) : Fl64.hypot (F64.neg x) y = Fl64.hypot x y := by
  unfold Fl64.hypot
  rw [abs_neg_f64]

theorem signbit_copysign (x y : F64) : F64.signbit (Fl64.copysign x y) = F64.signbit y := by
  have hy : y.toNat < 2^64 := y.isLt
  have habs : (F64.abs x).toNat < 2^63 := by
    simp only [F64.abs, F64.ofBits, F64.toBits, BitVec.toNat_ofNat]; omega
  unfold Fl64.copysign F64.signbit F64.toBits F64.ofBits
  by_cases hs : y.toNat ≥ 2^63
  · simp [hs]; omega
  · simp [hs]; omega

theorem neg_copysign_neg (x y : F64) : F64.neg (Fl64.copysign x (F64.neg y)) = Fl64.copysign x y := by
  have habs : (F64.abs x).toNat < 2^63 := by
    simp only [F64.abs, F64.ofBits, F64.toBits, BitVec.toNat_ofNat]; omega
  by_cases hs : F64.signbit y = true
  · have h1 : Fl64.copysign x (F64.neg y) = BitVec.ofNat 64 (F64.abs x).toNat := by
      simp [Fl64.copysign, signbit_neg, hs, F64.toBits, F64.ofBits]
    have h2 : Fl64.copysign x y = BitVec.ofNat 64 ((F64.abs x).toNat + 2^63) := by
      simp [Fl64.copysign, hs, F64.toBits, F64.ofBits]
    have h3 : ¬ ((BitVec.ofNat 64 (F64.abs x).toNat).toNat ≥ 2^63) := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1, h2]
    simp only [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h3, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]; omega
  · have h1 : Fl64.copysign x (F64.neg y) = BitVec.ofNat 64 ((F64.abs x).toNat + 2^63) := by
      simp [Fl64.copysign, signbit_neg, hs, F64.toBits, F64.ofBits]
    have h2 : Fl64.copysign x y = BitVec.ofNat 64 (F64.abs x).toNat := by
      simp [Fl64.copysign, hs, F64.toBits, F64.ofBits]
    have h3 : (BitVec.ofNat 64 ((F64.abs x).toNat + 2^63)).toNat ≥ 2^63 := by
      rw [BitVec.toNat_ofNat]; omega
    rw [h1, h2]
    simp only [F64.neg, F64.signbit, F64.toBits, F64.ofBits, h3, decide_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]; omega
theorem eq_self_of_not_nan (x : F64) (h : F64.isnan x = false) : F64.eq x x = true := by
  simp [F64.eq, h]

theorem neg_neg_jint {t : IntTy} (x : JInt t) : -(-x) = x := by
  apply Subtype.ext
  change wrapInt t (-wrapInt t (-x.val)) = x.val
  rw [wrapInt_neg, Int.neg_neg, wrapInt_val]

/-! ## Gaussian-integer power lemmas -/

theorem gmul_assoc (a b c : Int × Int) : gmul (gmul a b) c = gmul a (gmul b c) := by
  simp only [gmul, Prod.mk.injEq]
  constructor <;> grind

theorem gmul_comm (a b : Int × Int) : gmul a b = gmul b a := by
  simp only [gmul, Prod.mk.injEq]
  constructor <;> grind

theorem gmul_one (a : Int × Int) : gmul a (1, 0) = a := by
  simp only [gmul]; ext <;> simp

theorem one_gmul (a : Int × Int) : gmul (1, 0) a = a := by
  rw [gmul_comm, gmul_one]

theorem gpow_one (a : Int × Int) : gpow a 1 = a := by
  simp [gpow, one_gmul]

theorem gpow_add (a : Int × Int) (m n : Nat) : gpow a (m + n) = gmul (gpow a m) (gpow a n) := by
  induction n with
  | zero => simp [gpow, gmul_one]
  | succ n ih => rw [← Nat.add_assoc, gpow, gpow, ih, gmul_assoc]

theorem gpow_mul (a : Int × Int) (m n : Nat) : gpow a (m * n) = gpow (gpow a m) n := by
  induction n with
  | zero => simp [gpow]
  | succ n ih => rw [Nat.mul_succ, gpow_add, ih, gpow]

theorem gpow_two (a : Int × Int) : gpow a 2 = gmul a a := by
  simp [gpow, one_gmul]

/-- Gaussian operations seen by `power_by_squaring`. -/
def gops : MulOps (Int × Int) := ⟨gmul, (1, 0), fun a => a == (1, 0), fun a => (-a.1, -a.2)⟩

theorem squareN_gpow (k : Nat) (x : Int × Int) : squareN gmul k x = gpow x (2 ^ k) := by
  induction k generalizing x with
  | zero => simp [squareN, gpow_one]
  | succ k ih => rw [squareN, ih, ← gpow_two, ← gpow_mul, Nat.pow_succ, Nat.mul_comm]

theorem trailingZeros_spec : ∀ (fuel n : Nat), 0 < n → n < 2 ^ fuel →
    n = 2 ^ trailingZeros fuel n * (2 * (n / 2 ^ (trailingZeros fuel n + 1)) + 1)
  | 0, n, _, h1 => by simp at h1; omega
  | fuel + 1, n, _, h1 => by
    by_cases hodd : n % 2 = 0
    · have hne : (n != 0 && n % 2 == 0) = true := by simp [hodd]; omega
      have hpos : 0 < n / 2 := by omega
      have hlt : n / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at h1; omega
      have ih := trailingZeros_spec fuel (n / 2) hpos hlt
      simp only [trailingZeros, hne, ↓reduceIte]
      generalize hs : trailingZeros fuel (n / 2) = s at ih
      have hdiv : n / 2 ^ (s + 1 + 1) = n / 2 / 2 ^ (s + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ 2 (s + 1), Nat.mul_comm]
      rw [hdiv]
      generalize n / 2 / 2 ^ (s + 1) = q at ih ⊢
      rw [Nat.pow_succ, Nat.mul_right_comm, ← ih]
      omega
    · have hne : (n != 0 && n % 2 == 0) = false := by simp [hodd]
      simp only [trailingZeros, hne, Bool.false_eq_true, ↓reduceIte, Nat.pow_zero, Nat.one_mul,
        Nat.zero_add, Nat.pow_one]
      omega

theorem pbsLoop_gpow : ∀ (fuel : Nat) (x y : Int × Int) (p : Nat),
    p < 2 ^ fuel → p < 2 ^ 64 → pbsLoop gmul fuel x y p = gmul y (gpow x (2 * p))
  | 0, _, y, p, h1, _ => by
    simp at h1; subst h1; simp [pbsLoop, gpow, gmul_one]
  | fuel + 1, x, y, p, h1, h2 => by
    by_cases hp : p = 0
    · subst hp; simp [pbsLoop, gpow, gmul_one]
    · simp only [pbsLoop, hp, ↓reduceIte]
      have hspec := trailingZeros_spec 64 p (by omega) h2
      generalize hs : trailingZeros 64 p = s at hspec
      have hshift : p >>> (s + 1) = p / 2 ^ (s + 1) := Nat.shiftRight_eq_div_pow p (s + 1)
      rw [hshift]
      generalize hq : p / 2 ^ (s + 1) = q at hspec
      have hqle : q ≤ p / 2 := by
        rw [← hq, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        exact Nat.div_le_self _ _
      have hq1 : q < 2 ^ fuel := by rw [Nat.pow_succ] at h1; omega
      rw [pbsLoop_gpow fuel _ _ q hq1 (by omega), squareN_gpow, ← gpow_mul, gmul_assoc, ← gpow_add]
      congr 2
      rw [hspec, Nat.pow_succ]
      generalize 2 ^ s = t
      have e : t * 2 * (2 * q) = 2 * (t * (2 * q)) := by rw [Nat.mul_comm t 2, Nat.mul_assoc]
      rw [e, Nat.mul_add, Nat.mul_one, Nat.mul_add]
      omega

theorem pbs_gpow (x : Int × Int) (p : JInt .i64) (hp : 0 ≤ p.val) :
    power_by_squaring gops x p = .ok (gpow x p.val.toNat) := by
  have hb := p.property
  simp only [IntTy.max, IntTy.min, IntTy.signed, IntTy.bits] at hb
  unfold power_by_squaring
  by_cases h1 : p.val = 1
  · simp [h1, gpow_one]
  by_cases h0 : p.val = 0
  · simp [h0, gpow, gops]
  by_cases h2 : p.val = 2
  · simp [h2, gpow_two, gops]
  have hneg : ¬ p.val < 0 := by omega
  simp only [h1, h0, h2, hneg, ↓reduceIte]
  generalize hn : p.val.toNat = n
  have hn0 : 0 < n := by omega
  have hn64 : n < 2 ^ 64 := by omega
  have hspec := trailingZeros_spec 64 n hn0 hn64
  generalize hs : trailingZeros 64 n = s at hspec
  have hx2 : squareN gops.mul (s + 1 - 2) (if s + 1 - 1 > 0 then gops.mul x x else x)
      = gpow x (2 ^ s) := by
    simp only [gops]
    by_cases hs0 : s = 0
    · subst hs0; simp [squareN, gpow_one]
    · have hgt : s + 1 - 1 > 0 := by omega
      simp only [hgt, ↓reduceIte, squareN_gpow, ← gpow_two, ← gpow_mul]
      congr 1; rw [← Nat.pow_succ']; congr 1; omega
  rw [hx2]
  have hshift : n >>> (s + 1) = n / 2 ^ (s + 1) := Nat.shiftRight_eq_div_pow n (s + 1)
  rw [hshift]
  generalize hq : n / 2 ^ (s + 1) = q at hspec
  have hq64 : q < 2 ^ 64 := by
    have : q ≤ n := by rw [← hq]; exact Nat.div_le_self _ _
    omega
  simp only [gops]
  rw [pbsLoop_gpow 64 _ _ q hq64 hq64, ← gpow_mul, ← gpow_add]
  congr 1
  conv => rhs; rw [hspec]
  rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- Componentwise `JInt.wrap t` of an exact Gaussian integer. -/
def W (t : IntTy) (p : Int × Int) : Complex (JInt t) := ⟨JInt.wrap t p.1, JInt.wrap t p.2⟩

/-- Multiplication on `Complex (JInt t)`. -/
abbrev cmulJInt (t : IntTy) (z w : Complex (JInt t)) : Complex (JInt t) :=
  mul_Complex (· * ·) (· - ·) (· + ·) z w

theorem W_mul (t : IntTy) (p q : Int × Int) :
    cmulJInt t (W t p) (W t q) = W t (gmul p q) := by
  ext <;> simp [cmulJInt, mul_Complex, real_Complex, imag_Complex, W, gmul]

theorem squareN_W (t : IntTy) (k : Nat) (x : Int × Int) :
    squareN (cmulJInt t) k (W t x) = W t (squareN gmul k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [squareN]
    rw [W_mul, ih]

theorem pbsLoop_W (t : IntTy) : ∀ (fuel : Nat) (x y : Int × Int) (p : Nat),
    pbsLoop (cmulJInt t) fuel (W t x) (W t y) p = W t (pbsLoop gmul fuel x y p)
  | 0, _, _, _ => rfl
  | fuel + 1, x, y, p => by
    simp only [pbsLoop]
    split
    · rfl
    · rw [squareN_W, W_mul, pbsLoop_W t fuel]

theorem W_self {t : IntTy} (z : Complex (JInt t)) : W t (z.re.val, z.im.val) = z := by
  cases z with
  | mk a b =>
    simp only [W, Complex.mk.injEq]
    exact ⟨Subtype.ext (wrapInt_val a), Subtype.ext (wrapInt_val b)⟩

/-! ## 1-6: Refuted properties (preserved from `JuliaLean.Complex`) -/

/-- `49.0`. -/
def f49 : F64 := F64.ofBits 0x4048800000000000
/-- `2.0^1000`. -/
def f2p1000 : F64 := F64.ofBits 0x7e70000000000000
/-- `2.0^-40`. -/
def f2m40 : F64 := F64.ofBits 0x3d70000000000000
/-- `2.0^30`. -/
def f2p30 : F64 := F64.ofBits 0x41d0000000000000
/-- `2.0^600`. -/
def f2p600 : F64 := F64.ofBits 0x6570000000000000
/-- `2.0^-600`. -/
def f2m600 : F64 := F64.ofBits 0x1a70000000000000
/-- `2.0^1023`. -/
def f2p1023 : F64 := F64.ofBits 0x7fe0000000000000
/-- `2.0^-1023`. -/
def f2m1023 : F64 := F64.ofBits 0x0008000000000000
/-- `2.0^-1000`. -/
def f2m1000 : F64 := F64.ofBits 0x0170000000000000
/-- `3.0`. -/
def f3 : F64 := F64.ofInt 3
/-- `4.0`. -/
def f4 : F64 := F64.ofInt 4

/-- For finite `z` and finite nonzero real `x`, `z / complex(x, 0.0)` equals the componentwise quotient `z / x`. -/
def DivRealDivisor : Prop := ∀ z : ComplexF64, ∀ x : F64,
  isfinite_Complex F64.isfinite z = true → F64.isfinite x = true → F64.iszero x = false →
  isequal_Complex F64.isequal (div_ComplexF64 z ⟨x, Fl64.pzero⟩) (div_Complex_Real F64.div z x) = true

theorem divRealDivisor_refuted : ¬ DivRealDivisor := by
  intro h
  have hh := h ⟨f49, Fl64.pzero⟩ f49 (by decide) (by decide) (by decide)
  revert hh
  decide

/-- For finite `z` and finite nonzero `w`, `real(z / w)` is not NaN when the exact real part of `z / w` is at most `floatmax(Float64)` in magnitude. -/
def DivNoSpuriousNaN : Prop := ∀ z w : ComplexF64,
  isfinite_Complex F64.isfinite z = true → isfinite_Complex F64.isfinite w = true →
  iszero_Complex F64.iszero w = false →
  (exactDivRe z w).1.natAbs ≤ (F64.toRat F64.floatmax).1.natAbs * (exactDivRe z w).2.natAbs →
  F64.isnan (real_Complex (div_ComplexF64 z w)) = false

theorem divNoSpuriousNaN_refuted : ¬ DivNoSpuriousNaN := by
  intro h
  have hh := h ⟨F64.one, f2p1000⟩ ⟨f2m40, Fl64.pzero⟩ (by decide) (by decide) (by decide) (by decide)
  revert hh
  decide

/-- For finite `z` and finite nonzero `w` whose exact real part `q` is a normal binary64 magnitude, `real(z / w)` is finite with relative error at most `2^-20`. -/
def DivComponentAccurate : Prop := ∀ z w : ComplexF64,
  isfinite_Complex F64.isfinite z = true → isfinite_Complex F64.isfinite w = true →
  iszero_Complex F64.iszero w = false →
  let q := exactDivRe z w
  q.2.natAbs ≤ q.1.natAbs * 2^1022 →
  q.1.natAbs ≤ (F64.toRat F64.floatmax).1.natAbs * q.2.natAbs →
  let p := ratOf (real_Complex (div_ComplexF64 z w))
  F64.isfinite (real_Complex (div_ComplexF64 z w)) = true ∧
    (p.1 * q.2 - q.1 * p.2).natAbs * 2^20 ≤ q.1.natAbs * p.2.natAbs

theorem divComponentAccurate_refuted : ¬ DivComponentAccurate := by
  intro h
  have hh := h ⟨f2p1000, Fl64.pzero⟩ ⟨F64.ofBits 3, Fl64.two⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  revert hh
  decide

/-- `Complex{Int}` division by a nonzero divisor never returns a NaN component. -/
def IntDivNoNaN : Prop := ∀ a b : Complex (JInt .i64),
  ¬ (b.re.val = 0 ∧ b.im.val = 0) → isnan_Complex F64.isnan (div_Complex_JInt a b) = false

theorem intDivNoNaN_refuted : ¬ IntDivNoNaN := by
  intro h
  have hh := h ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩ ⟨JInt.typemin .i64, JInt.lit .i64 0⟩ (by decide)
  revert hh
  decide

/-- `z^n` for `z::ComplexF64` and `n::Int` returns normally for every `z` and `n`. -/
def PowIntTotal : Prop := ∀ z : ComplexF64, ∀ n : JInt .i64, jlOk (pow_ComplexF64_Int z n) = true

theorem powIntTotal_refuted : ¬ PowIntTotal := by
  intro h
  have hh := h ⟨Fl64.two, Fl64.pzero⟩ (JInt.typemin .i64)
  revert hh
  decide

/-- When every product, difference and sum in `z*w + x` is exact, `muladd(z, w, x) == z*w + x`. -/
def MuladdExact : Prop := ∀ z w x : ComplexF64,
  exactMul z.re w.re = true → exactMul z.im w.im = true →
  exactMul z.re w.im = true → exactMul z.im w.re = true →
  exactAdd (F64.mul z.re w.re) (F64.mul z.im w.im) (-1) = true →
  exactAdd (F64.mul z.re w.im) (F64.mul z.im w.re) 1 = true →
  exactAdd (real_Complex (mul_Complex F64.mul F64.sub F64.add z w)) x.re 1 = true →
  exactAdd (imag_Complex (mul_Complex F64.mul F64.sub F64.add z w)) x.im 1 = true →
  eq_Complex F64.eq
    (muladd_Complex_Complex_Complex F64.muladd F64.neg z w x)
    (add_Complex F64.add (mul_Complex F64.mul F64.sub F64.add z w) x) = true

theorem muladdExact_refuted : ¬ MuladdExact := by
  intro h
  have hh := h ⟨f2p30, f2p30⟩ ⟨f2p30, f2p30⟩ ⟨F64.one, Fl64.pzero⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert hh
  decide

/-! ## 7-14: Proven properties (preserved and strengthened from `JuliaLean.Complex`) -/

/-- `conj(conj(z))` is bit-identical to `z` on `ComplexF64` and `Complex (JInt t)`, and `conj` is a ring automorphism on `Complex (JInt t)`. -/
def ConjInvolution : Prop :=
  (∀ z : ComplexF64, conj_Complex F64.neg (conj_Complex F64.neg z) = z) ∧
  (∀ (t : IntTy) (z : Complex (JInt t)), conj_Complex Neg.neg (conj_Complex Neg.neg z) = z) ∧
  (∀ (t : IntTy) (z w : Complex (JInt t)),
    conj_Complex Neg.neg (add_Complex (· + ·) z w) =
      add_Complex (· + ·) (conj_Complex Neg.neg z) (conj_Complex Neg.neg w) ∧
    conj_Complex Neg.neg (sub_Complex (· - ·) z w) =
      sub_Complex (· - ·) (conj_Complex Neg.neg z) (conj_Complex Neg.neg w) ∧
    conj_Complex Neg.neg (mul_Complex (· * ·) (· - ·) (· + ·) z w) =
      mul_Complex (· * ·) (· - ·) (· + ·) (conj_Complex Neg.neg z) (conj_Complex Neg.neg w))

theorem conjInvolution_proven : ConjInvolution := by
  refine ⟨?_, ?_, ?_⟩
  · intro z; cases z; simp [conj_Complex, real_Complex, imag_Complex, neg_neg_f64]
  · intro t z; cases z; simp [conj_Complex, real_Complex, imag_Complex, neg_neg_jint]
  · intro t z w
    refine ⟨?_, ?_, ?_⟩
    · ext <;> simp [conj_Complex, add_Complex, real_Complex, imag_Complex]
      congr 1; omega
    · ext <;> simp [conj_Complex, sub_Complex, real_Complex, imag_Complex]
      congr 1; omega
    · ext <;> simp [conj_Complex, mul_Complex, real_Complex, imag_Complex]
      · congr 1; grind
      · congr 1; grind

/-- `isequal` implies equal `hash` for complex/complex and complex/real pairs in both argument orders. -/
def HashIsequal : Prop := ∀ H : F64 → UInt64 → UInt64,
  (∀ x y h, F64.isequal x y = true → H x h = H y h) →
  ∀ hImag h : UInt64,
    let h0 := hash_0_imag H Fl64.pzero
    (∀ z w : ComplexF64,
      isequal_Complex F64.isequal z w = true →
      hash_Complex H hImag (H Fl64.pzero hImag) z h = hash_Complex H hImag (H Fl64.pzero hImag) w h) ∧
    (∀ (z : ComplexF64) (x : F64),
      isequal_Complex_Real F64.isequal zero_F64 z x = true →
      hash_Complex H hImag (H Fl64.pzero hImag) z h = H x h) ∧
    (∀ (x : F64) (z : ComplexF64),
      isequal_Real_Complex F64.isequal zero_F64 x z = true →
      hash_Complex H hImag (H Fl64.pzero hImag) z h = H x h) ∧
    h0 = H Fl64.pzero h_imag

theorem hashIsequal_proven : HashIsequal := by
  intro H hH hImag h
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro z w hzw
    simp only [isequal_Complex, real_Complex, imag_Complex, Bool.and_eq_true] at hzw
    unfold hash_Complex real_Complex imag_Complex
    rw [hH z.im w.im hImag hzw.2, hH z.re w.re _ hzw.1]
  · intro z x hzx
    simp only [isequal_Complex_Real, zero_F64, real_Complex, imag_Complex, Bool.and_eq_true] at hzx
    unfold hash_Complex real_Complex imag_Complex
    rw [hH z.im Fl64.pzero hImag hzx.2, hH z.re x _ hzx.1]
    simp [UInt64.xor_assoc, UInt64.xor_self]
  · intro x z hxz
    simp only [isequal_Real_Complex, zero_F64, real_Complex, imag_Complex, Bool.and_eq_true] at hxz
    unfold hash_Complex real_Complex imag_Complex
    rw [← hH Fl64.pzero z.im hImag hxz.2, ← hH x z.re _ hxz.1]
    simp [UInt64.xor_assoc, UInt64.xor_self]

/-- `isequal(z, real(z))` implies `isreal(z)`, for non-NaN real part `isreal(z) == (z == real(z))`, complex/real equality is symmetric, range membership `z in r` requires `isreal(z)`, and converting a complex number to a real type succeeds iff `isreal(z)`. -/
def IsrealDoc : Prop := ∀ z : ComplexF64,
  (isequal_Complex_Real F64.isequal zero_F64 z (real_Complex z) = true →
    isreal_Complex F64.iszero z = true) ∧
  (F64.isnan (real_Complex z) = false →
    isreal_Complex F64.iszero z = eq_Complex_Real F64.iszero F64.eq z (real_Complex z)) ∧
  (∀ x : F64, eq_Complex_Real F64.iszero F64.eq z x = eq_Real_Complex F64.iszero F64.eq x z) ∧
  (∀ w : ComplexF64, eq_Complex F64.eq z w = (F64.eq z.re w.re && F64.eq z.im w.im)) ∧
  (∀ (r : List F64), isreal_Complex F64.iszero z = false →
    in_Complex_AbstractRange F64.iszero mem_List_F64 z r = false) ∧
  (Type_T_Complex (isreal_Complex F64.iszero) .ok "Float64" z =
    if isreal_Complex F64.iszero z then .ok (real_Complex z) else .error (.inexactError "Float64"))

theorem isrealDoc_proven : IsrealDoc := by
  intro z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    simp only [isequal_Complex_Real, zero_F64, real_Complex, imag_Complex, Bool.and_eq_true] at hz
    have h2 := hz.2
    have hn : F64.isnan Fl64.pzero = false := by decide
    simp only [F64.isequal, hn, Bool.and_false, Bool.false_or, beq_iff_eq] at h2
    have him : z.im = Fl64.pzero := BitVec.eq_of_toNat_eq h2
    simp only [isreal_Complex, imag_Complex, him]
    decide
  · intro hn
    simp only [eq_Complex_Real, real_Complex, eq_self_of_not_nan z.re hn, Bool.and_true]
  · intro x; rfl
  · intro w; rfl
  · intro r hnr
    simp [in_Complex_AbstractRange, hnr]
  · rfl

/-- `false * z` and `z * false` are signed zeros in both components (retaining component signbits and clearing NaNs/Infs), and `true * z = z * true = z`. -/
def FalseStrongZero : Prop := ∀ z : ComplexF64,
  iszero_Complex F64.iszero (mul_Bool_Complex Fl64.mulBool false z) = true ∧
  isnan_Complex F64.isnan (mul_Bool_Complex Fl64.mulBool false z) = false ∧
  F64.signbit (real_Complex (mul_Bool_Complex Fl64.mulBool false z)) = F64.signbit (real_Complex z) ∧
  F64.signbit (imag_Complex (mul_Bool_Complex Fl64.mulBool false z)) = F64.signbit (imag_Complex z) ∧
  iszero_Complex F64.iszero (mul_Complex_Bool Fl64.mulBoolRight z false) = true ∧
  isnan_Complex F64.isnan (mul_Complex_Bool Fl64.mulBoolRight z false) = false ∧
  mul_Bool_Complex Fl64.mulBool true z = z ∧
  mul_Complex_Bool Fl64.mulBoolRight z true = z

theorem falseStrongZero_proven : FalseStrongZero := by
  have key : ∀ y : F64,
      F64.iszero (Fl64.mulBool false y) = true ∧ F64.isnan (Fl64.mulBool false y) = false := by
    intro y
    simp only [Fl64.mulBool, Fl64.copysign, Bool.false_eq_true, ↓reduceIte]
    split <;> decide
  have keyR : ∀ y : F64,
      F64.iszero (Fl64.mulBoolRight y false) = true ∧ F64.isnan (Fl64.mulBoolRight y false) = false := by
    intro y
    simp only [Fl64.mulBoolRight, Fl64.copysign, Bool.false_eq_true, ↓reduceIte]
    split <;> decide
  intro z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [iszero_Complex, mul_Bool_Complex, real_Complex, imag_Complex, (key z.re).1, (key z.im).1]
  · simp [isnan_Complex, mul_Bool_Complex, real_Complex, imag_Complex, (key z.re).2, (key z.im).2]
  · simp [mul_Bool_Complex, real_Complex, Fl64.mulBool, signbit_copysign]
  · simp [mul_Bool_Complex, imag_Complex, Fl64.mulBool, signbit_copysign]
  · simp [iszero_Complex, mul_Complex_Bool, real_Complex, imag_Complex, (keyR z.re).1, (keyR z.im).1]
  · simp [isnan_Complex, mul_Complex_Bool, real_Complex, imag_Complex, (keyR z.re).2, (keyR z.im).2]
  · cases z; rfl
  · cases z; rfl

/-- `Complex{Bool}` multiplication and mixed `Bool`/`Real`/`Complex{Bool}` and `Bool`/`Complex` arithmetic agree with promotion to integer complex numbers, and `im * im == -1 + 0im`. -/
def BoolMulPromotes : Prop :=
  (∀ z w : Complex Bool,
    mul_ComplexBool z w =
      mul_Complex (· * ·) (· - ·) (· + ·) (toComplexInt_Bool z) (toComplexInt_Bool w)) ∧
  mul_ComplexBool im im = ⟨JInt.lit .i64 (-1), JInt.lit .i64 0⟩ ∧
  (∀ (b : Bool) (z : Complex Bool),
    let bi : Complex (JInt .i64) := ⟨JInt.lit .i64 (if b then 1 else 0), JInt.lit .i64 0⟩
    add_Bool_ComplexBool b z = add_Complex (· + ·) bi (toComplexInt_Bool z) ∧
    add_ComplexBool_Bool z b = add_Complex (· + ·) (toComplexInt_Bool z) bi ∧
    sub_Bool_ComplexBool b z = sub_Complex (· - ·) bi (toComplexInt_Bool z) ∧
    sub_ComplexBool_Bool z b = sub_Complex (· - ·) (toComplexInt_Bool z) bi ∧
    toComplexInt_Bool (mul_Bool_ComplexBool b z) =
      mul_Complex (· * ·) (· - ·) (· + ·) bi (toComplexInt_Bool z) ∧
    toComplexInt_Bool (mul_ComplexBool_Bool z b) =
      mul_Complex (· * ·) (· - ·) (· + ·) (toComplexInt_Bool z) bi) ∧
  (∀ (x : JInt .i64) (z : Complex Bool),
    let xi : Complex (JInt .i64) := ⟨x, JInt.lit .i64 0⟩
    add_Real_ComplexBool add_JInt_Bool promote_Int_Bool x z =
      add_Complex (· + ·) xi (toComplexInt_Bool z) ∧
    add_ComplexBool_Real add_Bool_JInt promote_Int_Bool z x =
      add_Complex (· + ·) (toComplexInt_Bool z) xi ∧
    sub_Real_ComplexBool sub_JInt_Bool oftype_JInt_Bool Neg.neg x z =
      sub_Complex (· - ·) xi (toComplexInt_Bool z) ∧
    sub_ComplexBool_Real sub_Bool_JInt promote_Int_Bool z x =
      sub_Complex (· - ·) (toComplexInt_Bool z) xi ∧
    mul_Real_ComplexBool mul_JInt_Bool x z =
      mul_Complex (· * ·) (· - ·) (· + ·) xi (toComplexInt_Bool z) ∧
    mul_ComplexBool_Real mul_Bool_JInt z x =
      mul_Complex (· * ·) (· - ·) (· + ·) (toComplexInt_Bool z) xi) ∧
  (∀ (t : IntTy) (b : Bool) (z : Complex (JInt t)),
    let bi : Complex (JInt t) := ⟨ofBool_JInt t b, JInt.lit t 0⟩
    add_Bool_Complex add_Bool_JInt promote_same b z =
      add_Complex (· + ·) bi z ∧
    add_Complex_Bool add_JInt_Bool promote_same z b =
      add_Complex (· + ·) z bi ∧
    sub_Bool_Complex sub_Bool_JInt Neg.neg promote_same b z =
      sub_Complex (· - ·) bi z ∧
    sub_Complex_Bool sub_JInt_Bool promote_same z b =
      sub_Complex (· - ·) z bi)

theorem boolMulPromotes_proven : BoolMulPromotes := by
  refine ⟨?_, by decide, ?_, ?_, ?_⟩
  · intro z w
    cases z with | mk a b => cases w with | mk c d =>
      cases a <;> cases b <;> cases c <;> cases d <;> decide
  · intro b z
    cases z with | mk re im =>
      cases b <;> cases re <;> cases im <;> decide
  · intro x z
    cases z with | mk re im =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (cases re <;> cases im <;> ext <;>
          simp [add_Real_ComplexBool, add_ComplexBool_Real, sub_Real_ComplexBool,
            sub_ComplexBool_Real, mul_Real_ComplexBool, mul_ComplexBool_Real,
            add_JInt_Bool, add_Bool_JInt, sub_JInt_Bool, sub_Bool_JInt,
            mul_JInt_Bool, mul_Bool_JInt, oftype_JInt_Bool, ofBool_JInt,
            Complex_Real_Real, promote_Int_Bool, toComplexInt_Bool, Complex_T_Complex,
            add_Complex, sub_Complex, mul_Complex, real_Complex, imag_Complex] <;>
          try (congr 1; decide))
  · intro t b z
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      ext <;> simp [add_Bool_Complex, add_Complex_Bool, sub_Bool_Complex, sub_Complex_Bool,
        add_Bool_JInt, add_JInt_Bool, sub_Bool_JInt, sub_JInt_Bool, ofBool_JInt, promote_same,
        Complex_Real_Real, add_Complex, sub_Complex, real_Complex, imag_Complex]

/-- Branch cut and conjugation/negation symmetry of `sqrt` and `ssqs`:
1. For `real(z) < 0` (including `-Inf`), `imag(sqrt(z))` has the signbit of `imag(z)` (`-0.0im` lies below the branch cut).
2. For all non-NaN `x, y : F64` and `tr : F64Transcendentals` with `ldexp(-y, k) = -ldexp(y, k)`:
   - `ssqs(x, -y) = ssqs(x, y)` and `ssqs(-x, -y) = ssqs(x, y)` across all three scaling branches of `ssqs`
   - For `x ≥ 0` (`!(x < 0)`), `real(sqrt(conj(z))) = real(sqrt(z))`
   - For `x < 0` (along the entire left half-plane and negative real branch cut), `imag(sqrt(conj(z))) = -imag(sqrt(z))` (exact 64-bit negation). -/
def SqrtBranchCut : Prop :=
  (∀ x y : F64,
    F64.lt x Fl64.pzero = true →
    F64.signbit (imag_Complex (sqrt_ComplexF64 ⟨x, y⟩)) = F64.signbit y) ∧
  (∀ (tr : F64Transcendentals),
    (∀ v k, F64.isnan v = false → tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false) →
    ∀ x y : F64, F64.isnan x = false → F64.isnan y = false →
      ssqs_F64_tr tr x (F64.neg y) = ssqs_F64_tr tr x y ∧
      ssqs_F64_tr tr (F64.neg x) (F64.neg y) = ssqs_F64_tr tr x y ∧
      (F64.lt x Fl64.pzero = false →
        real_Complex (sqrt_ComplexF64_tr tr (conj_Complex F64.neg ⟨x, y⟩)) =
          real_Complex (sqrt_ComplexF64_tr tr ⟨x, y⟩)) ∧
      (F64.lt x Fl64.pzero = true →
        imag_Complex (sqrt_ComplexF64_tr tr (conj_Complex F64.neg ⟨x, y⟩)) =
          F64.neg (imag_Complex (sqrt_ComplexF64_tr tr ⟨x, y⟩))))

theorem toBits_zero_false_of_iszero_false (x : F64) (hx : F64.iszero x = false) :
    (F64.toBits x == F64.toBits Fl64.pzero) = false := by
  have h : x.toNat % 2^63 ≠ 0 := by
    unfold F64.iszero F64.abs F64.toBits F64.ofBits at hx
    simp only [BitVec.toNat_ofNat, beq_eq_false_iff_ne] at hx
    omega
  have hz0 : F64.toBits Fl64.pzero = 0 := by decide
  rw [hz0]
  unfold F64.toBits
  simp only [beq_eq_false_iff_ne]
  omega

theorem eq_zero_neg (x : F64) : F64.eq (F64.neg x) Fl64.pzero = F64.eq x Fl64.pzero := by
  unfold F64.eq
  rw [isnan_neg, iszero_neg]
  have hz : F64.iszero Fl64.pzero = true := by decide
  have hn : F64.isnan Fl64.pzero = false := by decide
  simp only [hz, hn, Bool.not_false, Bool.and_true]
  by_cases hx : F64.iszero x = true
  · simp [hx]
  · have hx' : F64.iszero x = false := Bool.eq_false_iff.mpr hx
    have hng : F64.iszero (F64.neg x) = false := by rw [iszero_neg, hx']
    rw [toBits_zero_false_of_iszero_false x hx', toBits_zero_false_of_iszero_false (F64.neg x) hng]

theorem ssqs_F64_tr_symm (tr : F64Transcendentals)
    (hld : ∀ v k, F64.isnan v = false → tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false)
    (x y : F64) (hx : F64.isnan x = false) (hy : F64.isnan y = false) :
    ssqs_F64_tr tr x (F64.neg y) = ssqs_F64_tr tr x y ∧
    ssqs_F64_tr tr (F64.neg x) (F64.neg y) = ssqs_F64_tr tr x y := by
  have hxx : F64.mul (F64.neg x) (F64.neg x) = F64.mul x x := mul_neg_neg_of_not_nan x x hx hx
  have hyy : F64.mul (F64.neg y) (F64.neg y) = F64.mul y y := mul_neg_neg_of_not_nan y y hy hy
  have hldx : ∀ k, F64.mul (tr.ldexp (F64.neg x) k) (tr.ldexp (F64.neg x) k) =
      F64.mul (tr.ldexp x k) (tr.ldexp x k) := by
    intro k
    rw [(hld x k hx).1]
    exact mul_neg_neg_of_not_nan _ _ (hld x k hx).2 (hld x k hx).2
  have hldy : ∀ k, F64.mul (tr.ldexp (F64.neg y) k) (tr.ldexp (F64.neg y) k) =
      F64.mul (tr.ldexp y k) (tr.ldexp y k) := by
    intro k
    rw [(hld y k hy).1]
    exact mul_neg_neg_of_not_nan _ _ (hld y k hy).2 (hld y k hy).2
  unfold ssqs_F64_tr ssqs
  simp only [hxx, hyy, isinf_neg, eq_zero_neg, abs_neg_f64, hldx, hldy, and_self]


theorem ssqs_F64_tr_conj_right (tr : F64Transcendentals)
    (hld : ∀ v k, F64.isnan v = false → tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false)
    (x y : F64) (hy : F64.isnan y = false) :
    ssqs_F64_tr tr x (F64.neg y) = ssqs_F64_tr tr x y := by
  have hyy : F64.mul (F64.neg y) (F64.neg y) = F64.mul y y := mul_neg_neg_of_not_nan y y hy hy
  have hldy : ∀ k, F64.mul (tr.ldexp (F64.neg y) k) (tr.ldexp (F64.neg y) k) =
      F64.mul (tr.ldexp y k) (tr.ldexp y k) := by
    intro k
    rw [(hld y k hy).1]
    exact mul_neg_neg_of_not_nan _ _ (hld y k hy).2 (hld y k hy).2
  unfold ssqs_F64_tr ssqs
  simp only [hyy, isinf_neg, eq_zero_neg, abs_neg_f64, hldy]
theorem iszero_of_eq_pzero (y : F64) (h : F64.eq y Fl64.pzero = true) : F64.iszero y = true := by
  by_cases hz : F64.iszero y = true
  · exact hz
  · have hz' : F64.iszero y = false := Bool.eq_false_iff.mpr hz
    unfold F64.eq at h
    rw [toBits_zero_false_of_iszero_false y hz'] at h
    simp [hz'] at h

theorem toBits_ne_of_iszero_false_iszero_true (x y : F64)
    (hx : F64.iszero x = false) (hy : F64.iszero y = true) :
    (F64.toBits x == F64.toBits y) = false := by
  unfold F64.iszero F64.abs F64.toBits F64.ofBits at hx hy
  unfold F64.toBits
  simp only [BitVec.toNat_ofNat, beq_eq_false_iff_ne, beq_iff_eq] at hx hy ⊢
  omega

theorem eq_of_iszero_right (x y : F64) (hy_nan : F64.isnan y = false) (hy_zero : F64.iszero y = true) :
    F64.eq x y = (!F64.isnan x && F64.iszero x) := by
  unfold F64.eq
  simp only [hy_nan, hy_zero, Bool.not_false, Bool.and_true]
  by_cases hx : F64.iszero x = true
  · simp [hx]
  · have hx' : F64.iszero x = false := Bool.eq_false_iff.mpr hx
    rw [toBits_ne_of_iszero_false_iszero_true x y hx' hy_zero]
    simp [hx']

theorem eq_conj_zero_iff (x y : F64) (hy : F64.isnan y = false) :
    (F64.eq x (F64.neg y) && F64.eq (F64.neg y) Fl64.pzero) =
    (F64.eq x y && F64.eq y Fl64.pzero) := by
  rw [eq_zero_neg]
  by_cases hy0 : F64.eq y Fl64.pzero = true
  · have hiz := iszero_of_eq_pzero y hy0
    have hiz_neg : F64.iszero (F64.neg y) = true := by rw [iszero_neg, hiz]
    have hnan_neg : F64.isnan (F64.neg y) = false := by rw [isnan_neg, hy]
    rw [eq_of_iszero_right x y hy hiz, eq_of_iszero_right x (F64.neg y) hnan_neg hiz_neg]
  · simp [hy0]

theorem sqrtBranchCut_proven : SqrtBranchCut := by
  have hbr : ∀ (c : Bool) (ξ ρ y : F64),
      F64.signbit (if c then ({ re := ξ, im := Fl64.copysign ρ y } : ComplexF64) else { re := ρ, im := y }).im =
      F64.signbit y := by
    intro c _ _ _; cases c <;> simp [signbit_copysign]
  have hbr_re : ∀ (c : Bool) (η1 η2 y1 y2 ρ : F64),
      (if c then ({ re := ρ, im := η1 } : ComplexF64) else { re := ρ, im := y1 }).re =
      (if c then ({ re := ρ, im := η2 } : ComplexF64) else { re := ρ, im := y2 }).re := by
    intro c _ _ _ _ _; cases c <;> rfl
  have hbr_im : ∀ (c : Bool) (ξ1 ξ2 ρ y : F64),
      (if c then ({ re := ξ1, im := Fl64.copysign ρ (F64.neg y) } : ComplexF64) else { re := ρ, im := F64.neg y }).im =
      F64.neg (if c then ({ re := ξ2, im := Fl64.copysign ρ y } : ComplexF64) else { re := ρ, im := y }).im := by
    intro c _ _ _ _; cases c
    · rfl
    · simp only [↓reduceIte]
      rw [← neg_copysign_neg, neg_neg_f64]
  constructor
  · intro x y hx
    unfold sqrt_ComplexF64 sqrt_Complex reim real_Complex imag_Complex
    by_cases h1 : (F64.eq x y && F64.eq y Fl64.pzero) = true
    · simp [h1]
    · simp only [id_eq, h1, hx, Bool.false_eq_true, ↓reduceIte]
      apply hbr
  · intro tr hld x y hx hy
    have hss := ssqs_F64_tr_symm tr hld x y hx hy
    have hss_raw :
        ssqs F64.isfinite F64.isinf F64.eq F64.lt Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
          Fl64.max F64.add F64.mul F64.div F64.nextfloat tr.exponent tr.ldexp x (F64.neg y) =
        ssqs F64.isfinite F64.isinf F64.eq F64.lt Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
          Fl64.max F64.add F64.mul F64.div F64.nextfloat tr.exponent tr.ldexp x y := hss.1
    have heq := eq_conj_zero_iff x y hy
    refine ⟨hss.1, hss.2, ?_, ?_⟩
    · intro hlt
      unfold sqrt_ComplexF64_tr sqrt_Complex conj_Complex reim real_Complex imag_Complex
      simp only [id_eq, heq, hss_raw, hlt, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : (F64.eq x y && F64.eq y Fl64.pzero) = true
      · simp [h1]
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        apply hbr_re
    · intro hlt
      unfold sqrt_ComplexF64_tr sqrt_Complex conj_Complex reim real_Complex imag_Complex
      simp only [id_eq, heq, hss_raw, hlt, ↓reduceIte]
      by_cases h1 : (F64.eq x y && F64.eq y Fl64.pzero) = true
      · simp [h1]
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        apply hbr_im

theorem sqrt_tail_conj (x y ρ : F64) (_hy : F64.isnan y = false) (hρ_nan : F64.isnan ρ = false) :
    (if !F64.eq ρ Fl64.pzero then
      let η := if F64.isfinite (F64.neg y) then F64.div (F64.div (F64.neg y) ρ) Fl64.two else F64.neg y
      if F64.lt x Fl64.pzero then (⟨F64.abs η, Fl64.copysign ρ (F64.neg y)⟩ : ComplexF64)
      else ⟨ρ, η⟩
    else ⟨ρ, F64.neg y⟩) =
    conj_Complex F64.neg
      (if !F64.eq ρ Fl64.pzero then
        let η := if F64.isfinite y then F64.div (F64.div y ρ) Fl64.two else y
        if F64.lt x Fl64.pzero then ⟨F64.abs η, Fl64.copysign ρ y⟩
        else ⟨ρ, η⟩
      else ⟨ρ, y⟩) := by
  by_cases hρ0 : F64.eq ρ Fl64.pzero = true
  · simp [hρ0, conj_Complex, real_Complex, imag_Complex]
  · have hρ_nz : F64.iszero ρ = false := by
      by_cases hz : F64.iszero ρ = true
      · have heq : F64.eq ρ Fl64.pzero = true := by
          unfold F64.eq
          simp [hρ_nan, hz, show F64.isnan Fl64.pzero = false by decide, show F64.iszero Fl64.pzero = true by decide]
        rw [heq] at hρ0; contradiction
      · exact Bool.eq_false_iff.mpr hz
    have hη : (if F64.isfinite (F64.neg y) then F64.div (F64.div (F64.neg y) ρ) Fl64.two else F64.neg y) =
        F64.neg (if F64.isfinite y then F64.div (F64.div y ρ) Fl64.two else y) := by
      rw [isfinite_neg]
      by_cases hfy : F64.isfinite y = true
      · have hiy : F64.isinf y = false := by
          rw [isfinite_iff_not_nan_not_inf] at hfy; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfy; exact hfy.2
        have h1 : F64.div (F64.neg y) ρ = F64.neg (F64.div y ρ) :=
          div_neg_left_of_not_inf_zero y ρ (by simp [hiy]) (by simp [hρ_nz]) hρ_nan
        simp [hfy, h1, div_two_neg]
      · simp [hfy]
    simp only [hρ0, Bool.not_false, ↓reduceIte, hη]
    by_cases hlt : F64.lt x Fl64.pzero = true
    · simp only [hlt, ↓reduceIte, conj_Complex, real_Complex, imag_Complex, abs_neg_f64]
      rw [← neg_copysign_neg, neg_neg_f64]
    · simp [hlt, conj_Complex, real_Complex, imag_Complex]
theorem sqrt_ComplexF64_tr_conj (tr : F64Transcendentals)
    (hld : ∀ v k, F64.isnan v = false → tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false)
    (hsq : ∀ v, F64.isnan (tr.sqrt v) = false)
    (x y : F64) (hy : F64.isnan y = false) :
    sqrt_ComplexF64_tr tr (conj_Complex F64.neg ⟨x, y⟩) =
      conj_Complex F64.neg (sqrt_ComplexF64_tr tr ⟨x, y⟩) := by
  have hss :
      ssqs F64.isfinite F64.isinf F64.eq F64.lt Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
        Fl64.max F64.add F64.mul F64.div F64.nextfloat tr.exponent tr.ldexp x (F64.neg y) =
      ssqs F64.isfinite F64.isinf F64.eq F64.lt Fl64.pzero Fl64.two Fl64.inf Fl64.eps F64.abs
        Fl64.max F64.add F64.mul F64.div F64.nextfloat tr.exponent tr.ldexp x y :=
    ssqs_F64_tr_conj_right tr hld x y hy
  have heq := eq_conj_zero_iff x y hy
  unfold sqrt_ComplexF64_tr sqrt_Complex conj_Complex reim real_Complex imag_Complex
  dsimp only [id_eq]
  rw [heq, hss]
  by_cases h1 : (F64.eq x y && F64.eq y Fl64.pzero) = true
  · simp [h1]
  · have h1f : (F64.eq x y && F64.eq y Fl64.pzero) = false := Bool.eq_false_iff.mpr h1
    rw [h1f]
    exact sqrt_tail_conj x y _ hy (hld _ _ (hsq _)).2
/-- For `z::Complex{T}` (`T` any `BitInteger`) and `n ≥ 0`, `z^n` is the exact Gaussian-integer power modulo `2^T.bits`; for `n < 0`, `z^n` succeeds only on `±1 + 0im` and throws `DomainError` otherwise. -/
def IntPowWraps : Prop :=
  (∀ (t : IntTy) (z : Complex (JInt t)) (n : JInt .i64), 0 ≤ n.val →
    pow_ComplexInteger_Integer z n =
      .ok ⟨JInt.wrap t (gpow (z.re.val, z.im.val) n.val.toNat).1,
           JInt.wrap t (gpow (z.re.val, z.im.val) n.val.toNat).2⟩) ∧
  (∀ (z : Complex (JInt .i64)) (n : JInt .i64), n.val < 0 →
    pow_ComplexInteger_Integer z n =
      if (z.re.val == 1 && z.im.val == 0) then .ok z
      else if ((-z.re).val == 1 && (-z.im).val == 0) then
        .ok (if n.val % 2 = 0 then ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩ else z)
      else .error (.domainError "Cannot raise an integer x to a negative power"))

theorem pbs_W (t : IntTy) (x : Int × Int) (p : JInt .i64) (hp : 0 ≤ p.val) :
    pow_ComplexInteger_Integer (W t x) p = (power_by_squaring gops x p).map (W t) := by
  unfold pow_ComplexInteger_Integer power_by_squaring
  by_cases h1 : p.val = 1
  · simp [h1, Except.map]
  by_cases h0 : p.val = 0
  · simp [h0, Except.map, gops, W, JInt.lit]
  by_cases h2 : p.val = 2
  · simp [h2, Except.map, gops]
    exact W_mul t x x
  have hneg : ¬ p.val < 0 := by omega
  simp only [h1, h0, h2, hneg, ↓reduceIte, Except.map, gops]
  congr 1
  have hstart :
      squareN (cmulJInt t) (trailingZeros 64 p.val.toNat + 1 - 2)
        (if trailingZeros 64 p.val.toNat + 1 - 1 > 0 then cmulJInt t (W t x) (W t x) else W t x) =
      W t (squareN gmul (trailingZeros 64 p.val.toNat + 1 - 2)
        (if trailingZeros 64 p.val.toNat + 1 - 1 > 0 then gmul x x else x)) := by
    split
    · rw [W_mul, squareN_W]
    · rw [squareN_W]
  change pbsLoop (cmulJInt t) 64 _ _ _ = _
  rw [hstart, pbsLoop_W t]

theorem intPowWraps_proven : IntPowWraps := by
  constructor
  · intro t z n hn
    have h := pbs_W t (z.re.val, z.im.val) n hn
    rw [pbs_gpow _ n hn, W_self] at h
    exact h
  · intro z n hn
    unfold pow_ComplexInteger_Integer power_by_squaring
    simp only [show ¬ n.val = 1 by omega, show ¬ n.val = 0 by omega, show ¬ n.val = 2 by omega,
      hn, ↓reduceIte, isone_Complex, neg_Complex, real_Complex, imag_Complex]

/-- `abs(conj(z))` and `abs(-z)` are bit-identical to `abs(z)` on `ComplexF64`, and `abs2(conj(z)) = abs2(-z) = abs2(z)` on `Complex (JInt t)` and non-NaN `ComplexF64`. -/
def AbsConjNeg : Prop :=
  (∀ z : ComplexF64,
    abs_Complex Fl64.hypot (conj_Complex F64.neg z) = abs_Complex Fl64.hypot z ∧
    abs_Complex Fl64.hypot (neg_Complex F64.neg z) = abs_Complex Fl64.hypot z) ∧
  (∀ z : ComplexF64, F64.isnan z.re = false → F64.isnan z.im = false →
    abs2_Complex F64.mul F64.add (conj_Complex F64.neg z) = abs2_Complex F64.mul F64.add z ∧
    abs2_Complex F64.mul F64.add (neg_Complex F64.neg z) = abs2_Complex F64.mul F64.add z) ∧
  (∀ (t : IntTy) (z : Complex (JInt t)),
    abs2_Complex (· * ·) (· + ·) (conj_Complex Neg.neg z) = abs2_Complex (· * ·) (· + ·) z ∧
    abs2_Complex (· * ·) (· + ·) (neg_Complex Neg.neg z) = abs2_Complex (· * ·) (· + ·) z)

theorem absConjNeg_proven : AbsConjNeg := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    unfold abs_Complex conj_Complex neg_Complex real_Complex imag_Complex
    exact ⟨hypot_neg_right z.re z.im, (hypot_neg_left z.re (F64.neg z.im)).trans (hypot_neg_right z.re z.im)⟩
  · intro z hre him
    unfold abs2_Complex conj_Complex neg_Complex real_Complex imag_Complex
    rw [mul_neg_neg_of_not_nan z.im z.im him him, mul_neg_neg_of_not_nan z.re z.re hre hre]
    exact ⟨rfl, rfl⟩
  · intro t z
    have hsq : ∀ x : JInt t, (-x) * (-x) = x * x := by
      intro x
      apply Subtype.ext
      change wrapInt t (wrapInt t (-x.val) * wrapInt t (-x.val)) = wrapInt t (x.val * x.val)
      rw [wrapInt_mul_left, wrapInt_mul_right]
      have : (-x.val) * (-x.val) = x.val * x.val := by grind
      rw [this]
    constructor <;>
      simp only [abs2_Complex, conj_Complex, neg_Complex, real_Complex, imag_Complex, hsq]

/-! ## 15-24: Additional specification properties across `base/complex.jl` -/

/-- `Complex (JInt t)` satisfies commutative ring identities, `z * conj(z) = ⟨abs2(z), 0⟩`, Brahmagupta-Fibonacci multiplicativity `abs2(z * w) = abs2(z) * abs2(w)`, wrapping operator agreement, mixed `Real` embedding, and `muladd` / `_mulsub` agreement. -/
def GaussianRingLaws : Prop := ∀ (t : IntTy) (z w x : Complex (JInt t)) (r s : JInt t),
  let ri : Complex (JInt t) := ⟨r, JInt.lit t 0⟩
  let mma (a b c : JInt t) : JInt t := a * b + c
  pos_Complex id z = z ∧
  add_Complex (· + ·) z w = add_Complex (· + ·) w z ∧
  add_Complex (· + ·) z (neg_Complex Neg.neg z) = ⟨JInt.lit t 0, JInt.lit t 0⟩ ∧
  mul_Complex (· * ·) (· - ·) (· + ·) z w = mul_Complex (· * ·) (· - ·) (· + ·) w z ∧
  mul_Complex (· * ·) (· - ·) (· + ·) z ⟨JInt.lit t 1, JInt.lit t 0⟩ = z ∧
  mul_Complex (· * ·) (· - ·) (· + ·) z (conj_Complex Neg.neg z) =
    ⟨abs2_Complex (· * ·) (· + ·) z, JInt.lit t 0⟩ ∧
  abs2_Complex (· * ·) (· + ·) (mul_Complex (· * ·) (· - ·) (· + ·) z w) =
    abs2_Complex (· * ·) (· + ·) z * abs2_Complex (· * ·) (· + ·) w ∧
  negWrap_Complex Neg.neg z = neg_Complex Neg.neg z ∧
  addWrap_Complex (· + ·) z w = add_Complex (· + ·) z w ∧
  subWrap_Complex (· - ·) z w = sub_Complex (· - ·) z w ∧
  mulWrap_Complex (· * ·) (· - ·) (· + ·) z w = mul_Complex (· * ·) (· - ·) (· + ·) z w ∧
  add_Real_Complex (· + ·) promote_same r z = add_Complex (· + ·) ri z ∧
  add_Complex_Real (· + ·) promote_same z r = add_Complex (· + ·) z ri ∧
  sub_Real_Complex (· - ·) oftype_JInt Neg.neg r z = sub_Complex (· - ·) ri z ∧
  sub_Complex_Real (· - ·) promote_same z r = sub_Complex (· - ·) z ri ∧
  mul_Real_Complex (· * ·) r z = mul_Complex (· * ·) (· - ·) (· + ·) ri z ∧
  mul_Complex_Real (· * ·) z r = mul_Complex (· * ·) (· - ·) (· + ·) z ri ∧
  muladd_Complex_Complex_Complex mma Neg.neg z w x =
    add_Complex (· + ·) (mul_Complex (· * ·) (· - ·) (· + ·) z w) x ∧
  muladd_Complex_Real_Real mma (· * ·) promote_same z r s =
    add_Complex (· + ·) (mul_Complex_Real (· * ·) z r) ⟨s, JInt.lit t 0⟩ ∧
  muladd_Complex_Real_Complex mma z r w =
    add_Complex (· + ·) (mul_Complex_Real (· * ·) z r) w ∧
  muladd_Real_Real_Complex mma promote_same r s z =
    add_Real_Complex (· + ·) promote_same (r * s) z ∧
  muladd_Complex_Complex_Real mma (_mulsub_Real mma Neg.neg) Neg.neg (· * ·) z w r =
    add_Complex_Real (· + ·) promote_same (mul_Complex (· * ·) (· - ·) (· + ·) z w) r

theorem gaussianRingLaws_proven : GaussianRingLaws := by
  intro t z w x r s
  refine ⟨by cases z; rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp [add_Complex, real_Complex, imag_Complex] <;> congr 1 <;> omega
  · ext <;> simp [add_Complex, neg_Complex, real_Complex, imag_Complex] <;> congr 1 <;> omega
  · ext <;> simp [mul_Complex, real_Complex, imag_Complex] <;> congr 1 <;> grind
  · cases z; ext <;> simp [mul_Complex, real_Complex, imag_Complex]
  · ext <;> simp [mul_Complex, conj_Complex, abs2_Complex, real_Complex, imag_Complex] <;> congr 1 <;> grind
  · apply Subtype.ext
    simp [mul_Complex, abs2_Complex, real_Complex, imag_Complex]
    congr 1; grind
  · ext <;> simp [add_Real_Complex, promote_same, Complex_Real_Real, add_Complex, real_Complex, imag_Complex]
  · ext <;> simp [add_Complex_Real, promote_same, Complex_Real_Real, add_Complex, real_Complex, imag_Complex] <;> congr 1 <;> omega
  · ext <;> simp [sub_Real_Complex, oftype_JInt, sub_Complex, real_Complex, imag_Complex]
  · ext <;> simp [sub_Complex_Real, promote_same, Complex_Real_Real, sub_Complex, real_Complex, imag_Complex]
  · ext <;> simp [mul_Real_Complex, mul_Complex, real_Complex, imag_Complex]
  · ext <;> simp [mul_Complex_Real, mul_Complex, real_Complex, imag_Complex] <;> congr 1 <;> grind
  · ext <;> simp [muladd_Complex_Complex_Complex, _mulsub_Real, add_Complex, mul_Complex, real_Complex, imag_Complex] <;>
      congr 1 <;> omega
  · ext <;> simp [muladd_Complex_Real_Real, promote_same, Complex_Real_Real, add_Complex, mul_Complex_Real, real_Complex, imag_Complex] <;>
      congr 1 <;> grind
  · ext <;> simp [muladd_Complex_Real_Complex, add_Complex, mul_Complex_Real, real_Complex, imag_Complex] <;>
      congr 1 <;> grind
  · rfl
  · ext <;> simp [muladd_Complex_Complex_Real, promote_same, _mulsub_Real, add_Complex_Real, Complex_Real_Real, mul_Complex, real_Complex, imag_Complex] <;>
      congr 1 <;> omega

/-- Widening a signed `Complex (JInt t)` (`t` below 128 bits) via `widen(::Type{Complex{T}})` prevents overflow in complex `+` and `-`, and `promote_rule` on `Complex` is commutative, associative, and idempotent. -/
def WidenPromoteLaws : Prop :=
  (∀ (t w : IntTy), widenSignedInt t = some w → ∀ z u : Complex (JInt t),
    let zw := Complex_T_Complex (widen_JInt w) z
    let uw := Complex_T_Complex (widen_JInt w) u
    widen_Type_Complex widen_IntTy t = .complex w ∧
    fits w (z.re.val + u.re.val) ∧ fits w (z.im.val + u.im.val) ∧
    fits w (z.re.val - u.re.val) ∧ fits w (z.im.val - u.im.val) ∧
    (add_Complex (· + ·) zw uw).re.val = z.re.val + u.re.val ∧
    (add_Complex (· + ·) zw uw).im.val = z.im.val + u.im.val ∧
    (sub_Complex (· - ·) zw uw).re.val = z.re.val - u.re.val ∧
    (sub_Complex (· - ·) zw uw).im.val = z.im.val - u.im.val) ∧
  (∀ t s u : IntTy,
    promote_rule_Complex_Complex IntTy.promote t s = promote_rule_Complex_Real IntTy.promote t s ∧
    promote_rule_Complex_Complex IntTy.promote t s = promote_rule_Complex_Complex IntTy.promote s t ∧
    promote_rule_Complex_Complex IntTy.promote t t = .complex t ∧
    IntTy.promote (IntTy.promote t s) u = IntTy.promote t (IntTy.promote s u))

theorem widenPromoteLaws_proven : WidenPromoteLaws := by
  constructor
  · intro t w hw z u
    have hzr := z.re.property
    have hzi := z.im.property
    have hur := u.re.property
    have hui := u.im.property
    have hadd_re : (JInt.lit w z.re.val + JInt.lit w u.re.val).val = wrapInt w (z.re.val + u.re.val) := by
      change wrapInt w (wrapInt w z.re.val + wrapInt w u.re.val) = _
      rw [wrapInt_add_left, wrapInt_add_right]
    have hadd_im : (JInt.lit w z.im.val + JInt.lit w u.im.val).val = wrapInt w (z.im.val + u.im.val) := by
      change wrapInt w (wrapInt w z.im.val + wrapInt w u.im.val) = _
      rw [wrapInt_add_left, wrapInt_add_right]
    have hsub_re : (JInt.lit w z.re.val - JInt.lit w u.re.val).val = wrapInt w (z.re.val - u.re.val) := by
      change wrapInt w (wrapInt w z.re.val - wrapInt w u.re.val) = _
      rw [wrapInt_sub_left, wrapInt_sub_right]
    have hsub_im : (JInt.lit w z.im.val - JInt.lit w u.im.val).val = wrapInt w (z.im.val - u.im.val) := by
      change wrapInt w (wrapInt w z.im.val - wrapInt w u.im.val) = _
      rw [wrapInt_sub_left, wrapInt_sub_right]
    simp only [widen_Type_Complex, Complex_T_Complex, widen_JInt, add_Complex, sub_Complex, real_Complex,
      imag_Complex, hadd_re, hadd_im, hsub_re, hsub_im, fits]
    cases t <;> simp [widenSignedInt] at hw <;> subst hw <;>
      simp_all [widen_IntTy, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, wrapInt] <;> omega
  · intro t s u
    cases t <;> cases s <;> cases u <;> decide

/-- `isfinite(z) == (!isnan(z) && !isinf(z))` on `ComplexF64`, `isinteger(z)` holds iff `z.im == 0` and `isinteger(z.re)`, embedding a real `x` via `complex(x)` round-trips through `(::Type{T})(z)` while nonzero imaginary parts throw `InexactError`, and type-level `real` and `complex` satisfy `real(complex(T)) = real(T)` and `complex(complex(T)) = complex(T)`. -/
def TypeAndPredicateAlgebra : Prop :=
  (∀ z : ComplexF64,
    isfinite_Complex F64.isfinite z = (!isnan_Complex F64.isnan z && !isinf_Complex F64.isinf z) ∧
    (isinf_Complex F64.isinf z = true → isfinite_Complex F64.isfinite z = false)) ∧
  (∀ (t : IntTy) (z : Complex (JInt t)) (isint : JInt t → Bool),
    (z.im.val ≠ 0 → isinteger_Complex iszero_JInt isint z = false) ∧
    (isinteger_Complex iszero_JInt isint z = true ↔ (z.im.val = 0 ∧ isint z.re = true))) ∧
  (∀ (t : IntTy) (x : JInt t),
    let z := complex_Real zero_JInt x
    Complex_Complex z = z ∧
    complex_Complex z = z ∧
    Complex_T_Real id (JInt.lit t 0) x = z ∧
    real_Real x = x ∧
    imag_Real zero_JInt x = JInt.lit t 0 ∧
    isreal_Real x = true ∧
    reim real_Complex imag_Complex z = (x, JInt.lit t 0) ∧
    isreal_Complex iszero_JInt z = true ∧
    iszero_Complex iszero_JInt z = (x.val == 0) ∧
    isone_Complex isone_JInt iszero_JInt z = (x.val == 1) ∧
    Type_T_Complex (isreal_Complex iszero_JInt) convert_JInt_ok t.name z = .ok x) ∧
  (∀ (t : IntTy) (x y : JInt t), y.val ≠ 0 →
    Type_T_Complex (isreal_Complex iszero_JInt) convert_JInt_ok t.name ⟨x, y⟩ =
      .error (.inexactError t.name)) ∧
  (∀ t : IntTy,
    complex_Type_Complex t = complex_Type_Real t ∧
    float_Type_Complex_AbstractFloat t = .complex t ∧
    float_Type_Complex id t = .complex t ∧
    real_Type_Complex fieldtype1_ComplexTy (complex_Type_Real t) =
      real_Type_Real t ∧
    (real_Type_Bottom (R := IntTy)) = .bottom ∧
    (complex_Type_Bottom (R := IntTy)) = .bottom ∧
    real_Type_Bottom_slurp (R := IntTy) [t] = .error (.methodError "real") ∧
    complex_Type_Bottom_slurp (R := IntTy) [t] = .error (.methodError "complex"))

theorem typeAndPredicateAlgebra_proven : TypeAndPredicateAlgebra := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [isfinite_Complex_iff z]
    refine ⟨rfl, ?_⟩
    intro hinf
    simp [hinf]
  · intro t z isint
    constructor
    · intro him
      simp [isinteger_Complex, isreal_Complex, iszero_JInt, imag_Complex, him]
    · simp [isinteger_Complex, isreal_Complex, iszero_JInt, real_Complex, imag_Complex]
  · intro t x
    have h0 : wrapInt t 0 = 0 := by cases t <;> decide
    simp [complex_Real, Complex_Real, Complex_Complex, complex_Complex, Complex_T_Real,
      real_Real, imag_Real, isreal_Real, reim, real_Complex, imag_Complex,
      isreal_Complex, iszero_Complex, isone_Complex, Type_T_Complex,
      zero_JInt, iszero_JInt, isone_JInt, convert_JInt_ok, h0]
  · intro t x y hy
    simp [Type_T_Complex, isreal_Complex, iszero_JInt, imag_Complex, hy]
  · intro t
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `flipsign` and `bswap` are involutions, `read` after `write` on a stream recovers `(z, rest)`, `show` formats compact vs non-compact spacing, strips the leading `'-'` of negative imaginary parts (when `signbit(im) && !isnan(im)`, including `-0.0` and `-Inf`), and inserts `"*"` before `"im"` iff `!(isaSigned || (isaAbstractFloat && isfinite(im)))` (distinguishing `Signed`, `Unsigned`, finite `AbstractFloat`, and non-finite `AbstractFloat` `Inf`/`NaN`), `show_unquoted` wraps `show(z)` in `"(" ... ")"` when `prec >= operator_precedence(:+)` and leaves it unparenthesized when `prec < operator_precedence(:+)`, and `show(io, z::Complex{Bool})` prints `"im"` iff `z = im`. -/
def FlipsignBswapIO : Prop :=
  (∀ (z : ComplexF64) (y : F64),
    flipsign_Complex_Real F64.signbit F64.neg (flipsign_Complex_Real F64.signbit F64.neg z y) y = z) ∧
  (∀ (t : IntTy) (z : Complex (JInt t)) (y : JInt t),
    flipsign_Complex_Real signbit_JInt Neg.neg
      (flipsign_Complex_Real signbit_JInt Neg.neg z y) y = z) ∧
  (∀ (z : ComplexF64),
    bswap_Complex F64.neg (bswap_Complex F64.neg z) = z) ∧
  (∀ (t : IntTy) (z : Complex (JInt t)) (rest : List (JInt t)),
    read_Complex read_List (write_Complex write2_List rest z) = .ok (z, rest)) ∧
  (∀ z : Complex Bool, show_Complex_Bool z = "im" ↔ z = im) ∧
  (∀ (z : ComplexF64) (compact isaSigned isaAbstractFloat : Bool),
    let s := show_Complex show_F64 compact isaSigned isaAbstractFloat F64.isfinite z
    let sep :=
      if F64.signbit z.im && !F64.isnan z.im then (if compact then "-" else " - ")
      else (if compact then "+" else " + ")
    let star := if !(isaSigned || (isaAbstractFloat && (!F64.isnan z.im && !F64.isinf z.im))) then "*" else ""
    s = show_F64 z.re ++ sep ++ show_F64 (F64.abs z.im) ++ star ++ "im" ∧
    s.startsWith "(" = false) ∧
  (∀ (z : ComplexF64) (indent prec : JInt .i64),
    let plusPrec := JInt.lit .i64 11
    let s := show_Complex show_F64 false false true F64.isfinite z
    let u := show_unquoted_Complex plusPrec (show_Complex show_F64 false false true F64.isfinite) z indent prec
    (11 ≤ prec.val → u.startsWith "(" = true ∧ u = "(" ++ s ++ ")") ∧
    (prec.val < 11 → u.startsWith "(" = false ∧ u = s))

theorem show_F64_abs (x : F64) :
    show_F64 (F64.abs x) =
      if F64.isnan x then "NaN"
      else if F64.isinf x then "Inf"
      else if F64.iszero x then "0.0"
      else "1.0" := by
  have hs : F64.signbit (F64.abs x) = false := by
    unfold F64.signbit F64.abs F64.toBits F64.ofBits
    simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hn : F64.isnan (F64.abs x) = F64.isnan x := by
    unfold F64.isnan F64.exponentField F64.fraction F64.abs F64.toBits F64.ofBits
    simp only [BitVec.toNat_ofNat]
    have h1 : x.toNat % 2^63 % 2^64 / 2^52 % 2048 = x.toNat / 2^52 % 2048 := by omega
    have h2 : x.toNat % 2^63 % 2^64 % 2^52 = x.toNat % 2^52 := by omega
    rw [h1, h2]
  have hi : F64.isinf (F64.abs x) = F64.isinf x := by
    unfold F64.isinf F64.abs F64.toBits F64.ofBits
    simp only [BitVec.toNat_ofNat]
    have : x.toNat % 2^63 % 2^64 % 2^63 % 2^64 = x.toNat % 2^63 % 2^64 := by omega
    rw [this]
  have hz : F64.iszero (F64.abs x) = F64.iszero x := by
    unfold F64.iszero F64.abs F64.toBits F64.ofBits
    simp only [BitVec.toNat_ofNat]
    have : x.toNat % 2^63 % 2^64 % 2^63 % 2^64 = x.toNat % 2^63 % 2^64 := by omega
    rw [this]
  unfold show_F64
  simp [hs, hn, hi, hz]

theorem show_Complex_show_F64_Format (sr nr ir zr si ni ii zi compact isaSigned isaAbstractFloat : Bool) :
    let rStr := (if sr && !nr then "-" else "") ++ (if nr then "NaN" else if ir then "Inf" else if zr then "0.0" else "1.0")
    let iMag := if ni then "NaN" else if ii then "Inf" else if zi then "0.0" else "1.0"
    let iBuf := (if si && !ni then "-" else "") ++ iMag
    let mid :=
      if iBuf.toList.head? == some '-' then
        (if compact then "-" else " - ") ++ String.ofList iBuf.toList.tail
      else
        (if compact then "+" else " + ") ++ iBuf
    let star := if !(isaSigned || (isaAbstractFloat && (!ni && !ii))) then "*" else ""
    let sep := if si && !ni then (if compact then "-" else " - ") else (if compact then "+" else " + ")
    let s := rStr ++ mid ++ star ++ "im"
    (s = rStr ++ sep ++ iMag ++ star ++ "im" ∧ s.startsWith "(" = false) ∧
    ("(" ++ s ++ ")").startsWith "(" = true := by
  cases sr <;> cases nr <;> cases ir <;> cases zr <;>
    cases si <;> cases ni <;> cases ii <;> cases zi <;>
    cases compact <;> cases isaSigned <;> cases isaAbstractFloat <;> simp

theorem flipsignBswapIO_proven : FlipsignBswapIO := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z y
    cases z
    by_cases hs : F64.signbit y = true
    · simp [flipsign_Complex_Real, real_Complex, imag_Complex, hs, neg_neg_f64]
    · simp [flipsign_Complex_Real, hs]
  · intro t z y
    cases z
    by_cases hs : signbit_JInt y = true
    · simp [flipsign_Complex_Real, real_Complex, imag_Complex, hs, neg_neg_jint]
    · simp [flipsign_Complex_Real, hs]
  · intro z
    cases z
    simp [bswap_Complex, real_Complex, imag_Complex, neg_neg_f64]
  · intro t z rest
    cases z
    rfl
  · intro z
    cases z with | mk a b => cases a <;> cases b <;> decide
  · intro z compact isaSigned isaAbstractFloat
    cases z with | mk r i =>
      have hfmt := (show_Complex_show_F64_Format r.signbit r.isnan r.isinf r.iszero
        i.signbit i.isnan i.isinf i.iszero compact isaSigned isaAbstractFloat).1
      rw [show_F64_abs i]
      simp only [show_Complex, show_F64, reim, real_Complex, imag_Complex,
        isfinite_iff_not_nan_not_inf i] at hfmt ⊢
      exact hfmt
  · intro z indent prec
    cases z with | mk r i =>
      have hfmt := show_Complex_show_F64_Format r.signbit r.isnan r.isinf r.iszero
        i.signbit i.isnan i.isinf i.iszero false false true
      constructor
      · intro hp
        have hle : (JInt.lit .i64 11 ≤ prec) := by change 11 ≤ prec.val; exact hp
        unfold show_unquoted_Complex
        simp only [hle, ↓reduceIte, and_true]
        have h2 := hfmt.2
        simp only [show_Complex, show_F64, reim, real_Complex, imag_Complex,
          isfinite_iff_not_nan_not_inf i] at h2 ⊢
        exact h2
      · intro hp
        have hle : ¬ (JInt.lit .i64 11 ≤ prec) := by change ¬ (11 ≤ prec.val); omega
        unfold show_unquoted_Complex
        simp only [hle, ↓reduceIte, and_true]
        have h12 := hfmt.1.2
        simp only [show_Complex, show_F64, reim, real_Complex, imag_Complex,
          isfinite_iff_not_nan_not_inf i] at h12 ⊢
        exact h12

/-- Trigonometric, hyperbolic, inverse-trigonometric, inverse-hyperbolic, `cis`, and `cispi` laws on `ComplexF64` (using `f64Ops tr`, `sqrt_ComplexF64_tr tr`, and `inv_Complex_F64` from `JuliaLean.base.complex`):
1. For all `theta, zr, zi : F64` and `tr : F64Transcendentals` with odd `sin`/`sinpi` and even `cos`/`cospi`:
   - `cis_Real(-theta) = conj(cis_Real(theta))` and `cispi_Real(-theta) = conj(cispi_Real(theta))`
   - `(cis_Complex(-zr + zi*im)).re = (cis_Complex(zr + zi*im)).re` and `(cispi_Complex(-zr + zi*im)).re = (cispi_Complex(zr + zi*im)).re`
   - On the real axis `⟨theta, +0.0⟩` (when `exp(-0.0) = 1.0`), `cis_Complex` and `cispi_Complex` have modulus squared `abs2 = cos^2 + sin^2`.
2. For all `zr, zi : F64`:
   - `sinh(zr + zi*im) = -i * sin(zi + zr*im)` and `cosh(zr + zi*im) = cos(zi - zr*im)`
   - On the imaginary axis `⟨±0.0, zi⟩` (non-NaN `zi`), `sin(±0.0 + zi*im) = ±0.0 + sinh(zi)*im` (`sin(-z) = -sin(z)`, `sin(conj z) = conj(sin z)`) and `cos(±0.0 + zi*im) = cosh(zi) - flipsign(±0.0, zi)*im` (`cos(-z) = cos(z)`, `cos(conj z) = conj(cos z)`), and on the real axis `⟨zr, ±0.0⟩` (non-NaN `zr`), `sinh(zr ± 0.0im) = sinh(zr) ± 0.0im` and `cosh(zr ± 0.0im) = cosh(zr) - flipsign(±0.0, -zr)*im`
   - On the general finite branch (`zr != 0 && isfinite(zr)`), `(sin(conj z)).re = (sin z).re`, `(cos(conj z)).re = (cos z).re`, and `(cosh(conj z)).re = (cosh z).re`
   - On the C99 Annex G infinite classes `⟨±Inf, ±0.0⟩` and `⟨±Inf, ±Inf⟩`, `sin` and `cos` return their exact IEEE 754 limits.
3. In `tanh_Complex` and `tan_Complex`:
   - Across ALL non-NaN inputs `⟨ξ, η⟩` (both the normal `tan`/`sinh` branch and the overflow branch), `(tanh(conj z)).re = (tanh z).re` and `(tan(-zr + zi*im)).im = (tan(zr + zi*im)).im`
   - In the overflow-prevention regime `4 * |zi| > asinh(Ω)`, `tanh` returns `re = copysign(1.0, zi)` and signed-zero `im`, and `tan` returns signed-zero `re` and `im = copysign(1.0, zi)`.
4. In `asin_Complex`, `asinh_Complex`, `acos_Complex`, `acosh_Complex`, `atanh_Complex`, and `atan_Complex` (instantiated with the real `sqrt_ComplexF64_tr tr` and `inv_Complex_F64`):
   - Along the entire imaginary axis `⟨±0.0, zi⟩` (for non-infinite `zi`), `(asin(±0.0 + zi*im)).re = ±0.0`, and along the entire real axis `⟨zr, ±0.0⟩` (for non-infinite `zr`), `(asinh(zr ± 0.0im)).im = ±0.0`
   - Along the infinite lines `⟨±Inf, zi⟩` (finite `zi`) and `⟨±Inf, ±Inf⟩`, `asin` and `asinh` return `±pi/2` and `±pi/4`
   - `acos` and `acosh` satisfy all C99 Annex G special-value rules on `⟨±0.0, ±0.0⟩`, `⟨+Inf, +0.0⟩`, `⟨-Inf, -0.0⟩`, and `NaN`/`Inf` combinations
   - `atanh` and `atan` preserve the exact signed zero `±0.0` along the entire imaginary axis `|y| <= θ` (for `atanh`) and real axis `|x| <= θ` (for `atan`), take `⟨±Inf, ±0.0⟩` / `⟨±0.0, ±Inf⟩` at the poles `(±1.0, ±0.0)` and `(±0.0, ±1.0)`, and in the overflow regime `|x| > θ || |y| > θ` call `inv_Complex_F64` for `re` with `im = copysign(pi/2, y)`. -/
def TrigHyperbolicIdentities : Prop :=
  ∀ (tr : F64Transcendentals),
    (∀ x : F64, F64.isnan x = false →
      tr.sincos (F64.neg x) = (F64.neg (tr.sincos x).1, (tr.sincos x).2) ∧
      tr.sincospi (F64.neg x) = (F64.neg (tr.sincospi x).1, (tr.sincospi x).2) ∧
      tr.sinh (F64.neg x) = F64.neg (tr.sinh x) ∧
      tr.cosh (F64.neg x) = tr.cosh x ∧
      tr.tan (F64.neg x) = F64.neg (tr.tan x) ∧
      F64.isnan (tr.tan x) = false) →
    let o := f64Ops tr
    let sq := sqrt_ComplexF64_tr tr
    let θ := F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)
    F64.lt θ F64.one = false →
    (∀ s : Bool, F64.lt θ (F64.abs (F64.zero s)) = false) →
    (∀ (theta zr zi : F64), F64.isnan theta = false → F64.isnan zr = false →
      cis_Real o.sincos (F64.neg theta) = conj_Complex F64.neg (cis_Real o.sincos theta) ∧
      cispi_Real o.sincospi (F64.neg theta) = conj_Complex F64.neg (cispi_Real o.sincospi theta) ∧
      (cis_Complex F64.neg o.exp o.sincos F64.mul ⟨F64.neg zr, zi⟩).re =
        (cis_Complex F64.neg o.exp o.sincos F64.mul ⟨zr, zi⟩).re ∧
      (cispi_Complex Fl64.pi F64.mul F64.neg o.exp o.sincospi F64.mul ⟨F64.neg zr, zi⟩).re =
        (cispi_Complex Fl64.pi F64.mul F64.neg o.exp o.sincospi F64.mul ⟨zr, zi⟩).re) ∧
    (∀ (zr zi : F64),
      sinh_Complex o id ⟨zr, zi⟩ = ⟨(sin_Complex o id ⟨zi, zr⟩).im, (sin_Complex o id ⟨zi, zr⟩).re⟩ ∧
      cosh_Complex o F64.neg id ⟨zr, zi⟩ = cos_Complex o id ⟨zi, F64.neg zr⟩) ∧
    (∀ (s : Bool) (zi : F64), F64.isnan zi = false →
      let zr := F64.zero s
      sin_Complex o id ⟨zr, zi⟩ = ⟨zr, tr.sinh zi⟩ ∧
      sin_Complex o id (neg_Complex F64.neg ⟨zr, zi⟩) = neg_Complex F64.neg (sin_Complex o id ⟨zr, zi⟩) ∧
      sin_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩) = conj_Complex F64.neg (sin_Complex o id ⟨zr, zi⟩) ∧
      cos_Complex o id ⟨zr, zi⟩ = ⟨tr.cosh zi, F64.neg (Fl64.flipsign zr zi)⟩ ∧
      cos_Complex o id (neg_Complex F64.neg ⟨zr, zi⟩) = cos_Complex o id ⟨zr, zi⟩ ∧
      cos_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩) = conj_Complex F64.neg (cos_Complex o id ⟨zr, zi⟩) ∧
      sinh_Complex o id ⟨zi, zr⟩ = ⟨tr.sinh zi, zr⟩ ∧
      (cosh_Complex o F64.neg id ⟨zi, zr⟩).re = tr.cosh zi ∧
      F64.iszero (cosh_Complex o F64.neg id ⟨zi, zr⟩).im = true) ∧
    (∀ (zr zi : F64), F64.isnan zr = false → F64.isnan zi = false →
      (sin_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (sin_Complex o id ⟨zr, zi⟩).re ∧
      (cos_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (cos_Complex o id ⟨zr, zi⟩).re ∧
      (tanh_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (tanh_Complex o id ⟨zr, zi⟩).re ∧
      (tan_Complex o F64.neg id ⟨F64.neg zr, zi⟩).im = (tan_Complex o F64.neg id ⟨zr, zi⟩).im) ∧
    (∀ (zr zi : F64),
      F64.lt (o.asinh (o.prevfloat o.inf)) (F64.mul (F64.ofInt 4) (F64.abs zi)) = true →
      F64.isnan zi = false →
      (tanh_Complex o id ⟨zi, zr⟩).re = Fl64.copysign F64.one zi ∧
      F64.iszero (tanh_Complex o id ⟨zi, zr⟩).im = true ∧
      F64.iszero (tan_Complex o F64.neg id ⟨zr, zi⟩).re = true ∧
      (tan_Complex o F64.neg id ⟨zr, zi⟩).im = Fl64.copysign F64.one zi) ∧
    (∀ (s : Bool) (zi : F64), F64.isinf zi = false →
      (asin_Complex o sq ⟨F64.zero s, zi⟩).re = F64.zero s ∧
      (asinh_Complex o sq ⟨zi, F64.zero s⟩).im = F64.zero s) ∧
    (∀ (sr si : Bool),
      let zr := F64.inf sr
      let zi := F64.inf si
      sin_Complex o id ⟨zr, F64.zero si⟩ = ⟨F64.nan, F64.zero si⟩ ∧
      sin_Complex o id ⟨zr, zi⟩ = ⟨F64.nan, zi⟩ ∧
      cos_Complex o id ⟨zr, F64.zero si⟩ = ⟨F64.nan, F64.zero (sr == si)⟩ ∧
      cos_Complex o id ⟨zr, zi⟩ = ⟨Fl64.inf, F64.nan⟩ ∧
      (asin_Complex o sq ⟨zr, zi⟩).im = zi ∧
      F64.signbit (asin_Complex o sq ⟨zr, zi⟩).re = sr ∧
      (asinh_Complex o sq ⟨zr, zi⟩).re = zr ∧
      (asinh_Complex o sq ⟨zr, zi⟩).im = Fl64.copysign (F64.div Fl64.pi (F64.ofInt 4)) zi ∧
      acos_Complex o id sq ⟨F64.zero sr, F64.zero si⟩ = ⟨F64.div Fl64.pi Fl64.two, F64.zero (!si)⟩ ∧
      acos_Complex o id sq ⟨Fl64.inf, Fl64.pzero⟩ = ⟨Fl64.pzero, Fl64.ninf⟩ ∧
      acos_Complex o id sq ⟨Fl64.ninf, Fl64.nzero⟩ = ⟨Fl64.pi, Fl64.inf⟩ ∧
      acosh_Complex o sq ⟨Fl64.ninf, Fl64.nzero⟩ = ⟨Fl64.inf, F64.neg Fl64.pi⟩ ∧
      acosh_Complex o sq ⟨F64.nan, zi⟩ = ⟨Fl64.inf, F64.nan⟩) ∧
    (∀ (s : Bool) (x y : F64),
      atanh_Complex o id inv_Complex_F64 ⟨F64.one, F64.zero s⟩ = ⟨Fl64.inf, F64.zero s⟩ ∧
      atanh_Complex o id inv_Complex_F64 ⟨F64.neg F64.one, F64.zero s⟩ = ⟨Fl64.ninf, F64.zero s⟩ ∧
      atan_Complex o F64.neg id inv_Complex_F64 ⟨F64.zero s, F64.one⟩ = ⟨F64.zero s, Fl64.inf⟩ ∧
      atan_Complex o F64.neg id inv_Complex_F64 ⟨F64.zero s, F64.neg F64.one⟩ = ⟨F64.zero s, Fl64.ninf⟩ ∧
      (F64.lt θ (F64.abs y) = false →
        (atanh_Complex o id inv_Complex_F64 ⟨F64.zero s, y⟩).re = F64.zero s ∧
        (atan_Complex o F64.neg id inv_Complex_F64 ⟨y, F64.zero s⟩).im = F64.zero s) ∧
      ((F64.lt θ (F64.abs x) || F64.lt θ (F64.abs y)) = true → F64.isnan y = false → F64.isinf y = false →
        atanh_Complex o id inv_Complex_F64 ⟨x, y⟩ =
          ⟨(inv_Complex_F64 ⟨x, y⟩).re, Fl64.copysign (F64.div Fl64.pi Fl64.two) y⟩)) ∧
    ((∀ v k, F64.isnan v = false →
        tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false) →
     (∀ v, F64.isnan (tr.sqrt v) = false) →
     (∀ y x,
        tr.atan2 (F64.neg y) x = F64.neg (tr.atan2 y x) ∧ F64.isfinite (tr.atan2 y x) = true) →
     (∀ x, tr.asinh (F64.neg x) = F64.neg (tr.asinh x)) →
     ∀ (zr zi : F64), F64.isfinite zr = true → F64.isfinite zi = true →
      let z : ComplexF64 := ⟨zr, zi⟩
      let oneMinusZ : ComplexF64 := sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one z
      let onePlusZ : ComplexF64 := add_Real_Complex F64.add (fun a b => (a, b)) F64.one z
      let zMinus1 : ComplexF64 := sub_Complex_Real F64.sub (fun a b => (a, b)) z F64.one
      let zPlus1 : ComplexF64 := add_Complex_Real F64.add (fun a b => (a, b)) z F64.one
      let iz : ComplexF64 := ⟨F64.neg zi, zr⟩
      let oneMinusIz : ComplexF64 := sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one iz
      let onePlusIz : ComplexF64 := add_Real_Complex F64.add (fun a b => (a, b)) F64.one iz
      (F64.eq zr Fl64.pzero = false →
        asin_Complex o sq z =
          ⟨tr.atan2 zr (real_Complex (mul_Complex F64.mul F64.sub F64.add (sq oneMinusZ) (sq onePlusZ))),
           tr.asinh (Fl64.copysign (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg oneMinusZ)) (sq onePlusZ))) zi)⟩) ∧
      (F64.eq zi Fl64.pzero = false →
        asinh_Complex o sq z =
          ⟨tr.asinh (Fl64.copysign (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg oneMinusIz)) (sq onePlusIz))) zr),
           F64.neg (tr.atan2 (F64.neg zi) (real_Complex (mul_Complex F64.mul F64.sub F64.add (sq oneMinusIz) (sq onePlusIz))))⟩) ∧
      ((F64.eq zr zi && F64.eq zi Fl64.pzero) = false →
        acos_Complex o id sq z =
          ⟨F64.mul Fl64.two (tr.atan2 (real_Complex (sq oneMinusZ)) (real_Complex (sq onePlusZ))),
           tr.asinh (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg onePlusZ)) (sq oneMinusZ)))⟩) ∧
      acosh_Complex o sq z =
        ⟨tr.asinh (real_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg zMinus1)) (sq zPlus1))),
         F64.mul Fl64.two (tr.atan2 (imag_Complex (sq zMinus1)) (real_Complex (sq zPlus1)))⟩ ∧
      (acos_Complex o id sq (conj_Complex F64.neg z)).re = (acos_Complex o id sq z).re ∧
      (acosh_Complex o sq (conj_Complex F64.neg z)).im = F64.neg (acosh_Complex o sq z).im ∧
      (F64.isnan (sq oneMinusZ).im = false → F64.isnan (sq onePlusZ).im = false →
        (asin_Complex o sq (conj_Complex F64.neg z)).re = (asin_Complex o sq z).re) ∧
      (F64.isnan (sq oneMinusIz).im = false → F64.isnan (sq onePlusIz).im = false →
        (asinh_Complex o sq ⟨F64.neg zr, zi⟩).im = (asinh_Complex o sq z).im) ∧
      (F64.isnan (sq (conj_Complex F64.neg zMinus1)).im = false → F64.isnan (sq zPlus1).im = false →
        acosh_Complex o sq (conj_Complex F64.neg z) = conj_Complex F64.neg (acosh_Complex o sq z)) ∧
      (let s1c := sq (conj_Complex F64.neg oneMinusZ)
       let s2 := sq onePlusZ
       F64.isfinite s1c.re = true → F64.isfinite s1c.im = true →
       F64.isfinite s2.re = true → F64.isfinite s2.im = true →
       F64.isfinite (F64.mul s1c.re s2.im) = true → F64.isfinite (F64.mul s1c.im s2.re) = true →
       F64.isnan (sq oneMinusZ).im = false →
        asin_Complex o sq (conj_Complex F64.neg z) = conj_Complex F64.neg (asin_Complex o sq z)) ∧
      (let s1c := sq (conj_Complex F64.neg oneMinusIz)
       let s2 := sq onePlusIz
       F64.isfinite s1c.re = true → F64.isfinite s1c.im = true →
       F64.isfinite s2.re = true → F64.isfinite s2.im = true →
       F64.isfinite (F64.mul s1c.re s2.im) = true → F64.isfinite (F64.mul s1c.im s2.re) = true →
       F64.isnan (sq oneMinusIz).im = false →
        asinh_Complex o sq ⟨F64.neg zr, zi⟩ = ⟨F64.neg (asinh_Complex o sq z).re, (asinh_Complex o sq z).im⟩))
private theorem ite_true_of_eq_true {α : Type} (b : Bool) (t e : α) (h : b = true) :
    (if b = true then t else e) = t := by subst h; rfl

private theorem ite_false_of_eq_false {α : Type} (b : Bool) (t e : α) (h : b = false) :
    (if b = true then t else e) = e := by subst h; rfl

@[simp] theorem flipsign_neg_left (x y : F64) :
    Fl64.flipsign (F64.neg x) y = F64.neg (Fl64.flipsign x y) := by
  unfold Fl64.flipsign
  by_cases h : F64.signbit y = true <;> simp [h]

@[simp] theorem flipsign_neg_right (x y : F64) :
    Fl64.flipsign x (F64.neg y) = F64.neg (Fl64.flipsign x y) := by
  unfold Fl64.flipsign; rw [signbit_neg]
  by_cases h : F64.signbit y = true <;> simp [h, neg_neg_f64]

@[simp] theorem iszero_flipsign_zero (s : Bool) (y : F64) :
    F64.iszero (Fl64.flipsign (F64.zero s) y) = true := by
  unfold Fl64.flipsign
  have hz : F64.iszero (F64.zero s) = true := by cases s <;> decide
  by_cases h : F64.signbit y = true <;> simp [h, iszero_neg, hz]

theorem sin_Complex_not_fin (o : FloatOps F64) (zr zi : F64)
    (h1 : o.eq zr o.zero = false) (h2 : o.isfinite zr = false)
    (h3 : (o.eq zi o.zero || o.isinf zi) = true) :
    sin_Complex o id ⟨zr, zi⟩ = ⟨o.nan, zi⟩ := by
  unfold sin_Complex real_Complex imag_Complex id
  dsimp only
  have hc2 : (!o.isfinite zr) = true := by simp [h2]
  rw [ite_false_of_eq_false _ _ _ h1, ite_true_of_eq_true _ _ _ hc2, ite_true_of_eq_true _ _ _ h3]

theorem cos_Complex_not_fin_zero (o : FloatOps F64) (zr zi : F64)
    (h1 : o.eq zr o.zero = false) (h2 : o.isfinite zr = false)
    (h3 : o.eq zi o.zero = true) (h4 : o.isnan zr = false) :
    cos_Complex o id ⟨zr, zi⟩ = ⟨o.nan, o.neg (o.flipsign zi zr)⟩ := by
  unfold cos_Complex real_Complex imag_Complex id
  dsimp only
  have hc2 : (!o.isfinite zr) = true := by simp [h2]
  rw [ite_false_of_eq_false _ _ _ h1, ite_true_of_eq_true _ _ _ hc2,
      ite_true_of_eq_true _ _ _ h3, ite_false_of_eq_false _ _ _ h4]

theorem cos_Complex_not_fin_inf (o : FloatOps F64) (zr zi : F64)
    (h1 : o.eq zr o.zero = false) (h2 : o.isfinite zr = false)
    (h3 : o.eq zi o.zero = false) (h4 : o.isinf zi = true) :
    cos_Complex o id ⟨zr, zi⟩ = ⟨o.inf, o.nan⟩ := by
  unfold cos_Complex real_Complex imag_Complex id
  dsimp only
  have hc2 : (!o.isfinite zr) = true := by simp [h2]
  rw [ite_false_of_eq_false _ _ _ h1, ite_true_of_eq_true _ _ _ hc2,
      ite_false_of_eq_false _ _ _ h3, ite_true_of_eq_true _ _ _ h4]

theorem asin_Complex_re_of_not_isinf (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isinf zr = false) (h2 : o.eq zr o.zero = true) :
    (asin_Complex o sq ⟨zr, zi⟩).re = zr := by
  unfold asin_Complex reim real_Complex imag_Complex
  dsimp only
  have hc1 : (o.isinf zr && o.isinf zi) = false := by simp [h1]
  have hc2 : (o.isnan zi && o.isinf zr) = false := by simp [h1]
  rw [ite_false_of_eq_false _ _ _ hc1, ite_false_of_eq_false _ _ _ hc2]
  dsimp only
  rw [ite_true_of_eq_true _ _ _ h2]

theorem asin_Complex_inf_inf (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isinf zr = true) (h2 : o.isinf zi = true) :
    asin_Complex o sq ⟨zr, zi⟩ = ⟨o.copysign (o.div o.pi (o.ofInt 4)) zr, zi⟩ := by
  unfold asin_Complex reim real_Complex imag_Complex
  dsimp only
  have hc1 : (o.isinf zr && o.isinf zi) = true := by simp [h1, h2]
  rw [ite_true_of_eq_true _ _ _ hc1]

theorem asinh_Complex_inf_inf (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isinf (o.neg zi) = true) (h2 : o.isinf zr = true) :
    asinh_Complex o sq ⟨zr, zi⟩ = ⟨zr, o.neg (o.copysign (o.div o.pi (o.ofInt 4)) (o.neg zi))⟩ := by
  unfold asinh_Complex real_Complex imag_Complex
  dsimp only
  rw [asin_Complex_inf_inf o sq (o.neg zi) zr h1 h2]

theorem acos_Complex_zero_zero (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isnan zr = false) (h2 : o.isnan zi = false)
    (h3 : o.eq zr zi = true) (h4 : o.eq zi o.zero = true) :
    acos_Complex o id sq ⟨zr, zi⟩ = ⟨o.div o.pi o.two, o.neg zi⟩ := by
  unfold acos_Complex reim real_Complex imag_Complex id
  dsimp only
  have hc3 : (o.eq zr zi && o.eq zi o.zero) = true := by simp [h3, h4]
  rw [ite_false_of_eq_false _ _ _ h1, ite_false_of_eq_false _ _ _ h2, ite_true_of_eq_true _ _ _ hc3]

theorem acos_Complex_inf_zero (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isnan zr = false) (h2 : o.isnan zi = false)
    (h3 : o.eq zr zi = false) (h4 : o.eq zr o.inf = true) (h5 : o.identical zi o.zero = true) :
    acos_Complex o id sq ⟨zr, zi⟩ = ⟨zi, o.neg zr⟩ := by
  unfold acos_Complex reim real_Complex imag_Complex id
  dsimp only
  have hc3 : (o.eq zr zi && o.eq zi o.zero) = false := by simp [h3]
  have hc4 : (o.eq zr o.inf && o.identical zi o.zero) = true := by simp [h4, h5]
  rw [ite_false_of_eq_false _ _ _ h1, ite_false_of_eq_false _ _ _ h2,
      ite_false_of_eq_false _ _ _ hc3, ite_true_of_eq_true _ _ _ hc4]

theorem acos_Complex_ninf_nzero (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isnan zr = false) (h2 : o.isnan zi = false)
    (h3 : o.eq zr zi = false) (h4 : o.eq zr o.inf = false)
    (h5 : o.eq zr o.ninf = true) (h6 : o.identical zi o.nzero = true) :
    acos_Complex o id sq ⟨zr, zi⟩ = ⟨o.pi, o.neg zr⟩ := by
  unfold acos_Complex reim real_Complex imag_Complex id
  dsimp only
  have hc3 : (o.eq zr zi && o.eq zi o.zero) = false := by simp [h3]
  have hc4 : (o.eq zr o.inf && o.identical zi o.zero) = false := by simp [h4]
  have hc5 : (o.eq zr o.ninf && o.identical zi o.nzero) = true := by simp [h5, h6]
  rw [ite_false_of_eq_false _ _ _ h1, ite_false_of_eq_false _ _ _ h2,
      ite_false_of_eq_false _ _ _ hc3, ite_false_of_eq_false _ _ _ hc4, ite_true_of_eq_true _ _ _ hc5]

theorem acosh_Complex_ninf_nzero (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isnan zr = false) (h2 : o.isnan zi = false)
    (h3 : o.eq zr o.ninf = true) (h4 : o.identical zi o.nzero = true) :
    acosh_Complex o sq ⟨zr, zi⟩ = ⟨o.inf, o.neg o.pi⟩ := by
  unfold acosh_Complex reim real_Complex imag_Complex
  dsimp only
  have hc1 : (o.isnan zr || o.isnan zi) = false := by simp [h1, h2]
  have hc2 : (o.eq zr o.ninf && o.identical zi o.nzero) = true := by simp [h3, h4]
  rw [ite_false_of_eq_false _ _ _ hc1, ite_true_of_eq_true _ _ _ hc2]

theorem acosh_Complex_nan_inf (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isnan zr = true) (h2 : o.isinf zi = true) :
    acosh_Complex o sq ⟨zr, zi⟩ = ⟨o.inf, o.nan⟩ := by
  unfold acosh_Complex reim real_Complex imag_Complex
  dsimp only
  have hc1 : (o.isnan zr || o.isnan zi) = true := by simp [h1]
  have hc2 : (o.isinf zr || o.isinf zi) = true := by simp [h2]
  rw [ite_true_of_eq_true _ _ _ hc1, ite_true_of_eq_true _ _ _ hc2]

theorem asin_Complex_finite (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isinf zr = false) (h2 : o.isfinite zr = true) :
    let oneMinusZ : ComplexF64 := sub_Real_Complex o.sub (fun _ y => y) o.neg o.one ⟨zr, zi⟩
    let onePlusZ : ComplexF64 := add_Real_Complex o.add (fun a b => (a, b)) o.one ⟨zr, zi⟩
    asin_Complex o sq ⟨zr, zi⟩ =
      ⟨if o.eq zr o.zero then zr
       else o.atan2 zr (real_Complex (mul_Complex o.mul o.sub o.add (sq oneMinusZ) (sq onePlusZ))),
       o.asinh (o.copysign (imag_Complex (mul_Complex o.mul o.sub o.add (sq (conj_Complex o.neg oneMinusZ)) (sq onePlusZ))) zi)⟩ := by
  unfold asin_Complex reim real_Complex imag_Complex
  dsimp only
  have hc1 : (o.isinf zr && o.isinf zi) = false := by simp [h1]
  have hc2 : (o.isnan zi && o.isinf zr) = false := by simp [h1]
  have hc3 : (!o.isfinite zr) = false := by simp [h2]
  rw [ite_false_of_eq_false _ _ _ hc1, ite_false_of_eq_false _ _ _ hc2,
      ite_false_of_eq_false _ _ _ hc3]

theorem asin_Complex_general (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isinf zr = false) (h2 : o.eq zr o.zero = false) (h3 : o.isfinite zr = true) :
    let oneMinusZ : ComplexF64 := sub_Real_Complex o.sub (fun _ y => y) o.neg o.one ⟨zr, zi⟩
    let onePlusZ : ComplexF64 := add_Real_Complex o.add (fun a b => (a, b)) o.one ⟨zr, zi⟩
    asin_Complex o sq ⟨zr, zi⟩ =
      ⟨o.atan2 zr (real_Complex (mul_Complex o.mul o.sub o.add (sq oneMinusZ) (sq onePlusZ))),
       o.asinh (o.copysign (imag_Complex (mul_Complex o.mul o.sub o.add (sq (conj_Complex o.neg oneMinusZ)) (sq onePlusZ))) zi)⟩ := by
  dsimp only
  rw [asin_Complex_finite o sq zr zi h1 h3, ite_false_of_eq_false _ _ _ h2]

theorem acos_Complex_general (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isnan zr = false) (h2 : o.isnan zi = false)
    (h3 : (o.eq zr zi && o.eq zi o.zero) = false)
    (h4 : o.eq zr o.inf = false) (h5 : o.eq zr o.ninf = false)
    (h6 : o.isinf zr = false) :
    let oneMinusZ : ComplexF64 := sub_Real_Complex o.sub (fun _ y => y) o.neg o.one ⟨zr, zi⟩
    let onePlusZ : ComplexF64 := add_Real_Complex o.add (fun a b => (a, b)) o.one ⟨zr, zi⟩
    acos_Complex o id sq ⟨zr, zi⟩ =
      ⟨o.mul o.two (o.atan2 (real_Complex (sq oneMinusZ)) (real_Complex (sq onePlusZ))),
       o.asinh (imag_Complex (mul_Complex o.mul o.sub o.add (sq (conj_Complex o.neg onePlusZ)) (sq oneMinusZ)))⟩ := by
  unfold acos_Complex reim real_Complex imag_Complex id
  dsimp only
  have hc4 : (o.eq zr o.inf && o.identical zi o.zero) = false := by simp [h4]
  have hc5 : (o.eq zr o.ninf && o.identical zi o.nzero) = false := by simp [h5]
  have hc6 : (o.isinf zr && o.isinf zi) = false := by simp [h6]
  rw [ite_false_of_eq_false _ _ _ h1, ite_false_of_eq_false _ _ _ h2,
      ite_false_of_eq_false _ _ _ h3, ite_false_of_eq_false _ _ _ hc4,
      ite_false_of_eq_false _ _ _ hc5, ite_false_of_eq_false _ _ _ hc6]

theorem acosh_Complex_general (o : FloatOps F64) (sq : ComplexF64 → ComplexF64) (zr zi : F64)
    (h1 : o.isnan zr = false) (h2 : o.isnan zi = false)
    (h3 : o.eq zr o.ninf = false) (h4 : o.isinf zr = false) :
    let zMinus1 : ComplexF64 := sub_Complex_Real o.sub (fun a b => (a, b)) ⟨zr, zi⟩ o.one
    let zPlus1 : ComplexF64 := add_Complex_Real o.add (fun a b => (a, b)) ⟨zr, zi⟩ o.one
    acosh_Complex o sq ⟨zr, zi⟩ =
      ⟨o.asinh (real_Complex (mul_Complex o.mul o.sub o.add (sq (conj_Complex o.neg zMinus1)) (sq zPlus1))),
       o.mul o.two (o.atan2 (imag_Complex (sq zMinus1)) (real_Complex (sq zPlus1)))⟩ := by
  unfold acosh_Complex reim real_Complex imag_Complex
  dsimp only
  have hc1 : (o.isnan zr || o.isnan zi) = false := by simp [h1, h2]
  have hc2 : (o.eq zr o.ninf && o.identical zi o.nzero) = false := by simp [h3]
  have hc3 : (o.isinf zr && o.isinf zi) = false := by simp [h4]
  rw [ite_false_of_eq_false _ _ _ hc1, ite_false_of_eq_false _ _ _ hc2,
      ite_false_of_eq_false _ _ _ hc3]

theorem conj_conj_f64 (w : ComplexF64) :
    conj_Complex F64.neg (conj_Complex F64.neg w) = w := by
  cases w; simp [conj_Complex, real_Complex, imag_Complex, neg_neg_f64]

theorem mul_Complex_conj_re (u v : ComplexF64)
    (hu : F64.isnan u.im = false) (hv : F64.isnan v.im = false) :
    real_Complex (mul_Complex F64.mul F64.sub F64.add (conj_Complex F64.neg u) (conj_Complex F64.neg v)) =
      real_Complex (mul_Complex F64.mul F64.sub F64.add u v) := by
  unfold mul_Complex conj_Complex real_Complex imag_Complex
  dsimp only
  rw [mul_neg_neg_of_not_nan u.im v.im hu hv]

theorem mul_Complex_conj_im_abs (u v : ComplexF64)
    (hu_re : F64.isfinite u.re = true) (hu_im : F64.isfinite u.im = true)
    (hv_re : F64.isfinite v.re = true) (hv_im : F64.isfinite v.im = true)
    (hp1 : F64.isfinite (F64.mul u.re v.im) = true)
    (hp2 : F64.isfinite (F64.mul u.im v.re) = true) :
    F64.abs (imag_Complex (mul_Complex F64.mul F64.sub F64.add (conj_Complex F64.neg u) (conj_Complex F64.neg v))) =
      F64.abs (imag_Complex (mul_Complex F64.mul F64.sub F64.add u v)) := by
  unfold mul_Complex conj_Complex real_Complex imag_Complex
  dsimp only
  rw [mul_neg_right_of_finite u.re v.im hu_re hv_im,
      mul_neg_left_of_finite u.im v.re hu_im hv_re,
      abs_add_neg_neg_of_finite _ _ hp1 hp2]

theorem atanh_Complex_pole (o : FloatOps F64) (invC : ComplexF64 → ComplexF64) (x y : F64)
    (h1 : (o.lt (o.div (o.sqrt o.floatmax) (o.ofInt 4)) (o.abs x) ||
           o.lt (o.div (o.sqrt o.floatmax) (o.ofInt 4)) (o.abs y)) = false)
    (h2 : o.eq (o.mul (o.copysign o.one x) x) o.one = true)
    (h3 : o.eq (o.mul (o.copysign o.one x) y) o.zero = true) :
    atanh_Complex o id invC ⟨x, y⟩ =
      ⟨o.mul (o.copysign o.one x) o.inf,
       o.mul (o.copysign o.one x) (o.mul (o.copysign o.one x) y)⟩ := by
  unfold atanh_Complex mul_Complex_Real mul_Real_Complex reim real_Complex imag_Complex id
  dsimp only
  rw [ite_false_of_eq_false _ _ _ h1, ite_true_of_eq_true _ _ _ h2, ite_true_of_eq_true _ _ _ h3]

theorem atanh_Complex_re_zero (o : FloatOps F64) (invC : ComplexF64 → ComplexF64) (x y : F64)
    (h1 : (o.lt (o.div (o.sqrt o.floatmax) (o.ofInt 4)) (o.abs x) ||
           o.lt (o.div (o.sqrt o.floatmax) (o.ofInt 4)) (o.abs y)) = false)
    (h2 : o.eq (o.mul (o.copysign o.one x) x) o.one = false)
    (h3 : o.eq (o.mul (o.copysign o.one x) x) o.zero = true) :
    (atanh_Complex o id invC ⟨x, y⟩).re =
      o.mul (o.copysign o.one x) (o.mul (o.copysign o.one x) x) := by
  unfold atanh_Complex mul_Complex_Real mul_Real_Complex reim real_Complex imag_Complex id
  dsimp only
  rw [ite_false_of_eq_false _ _ _ h1, ite_false_of_eq_false _ _ _ h2, ite_true_of_eq_true _ _ _ h3]

theorem atanh_Complex_large (o : FloatOps F64) (invC : ComplexF64 → ComplexF64) (x y : F64)
    (h1 : (o.lt (o.div (o.sqrt o.floatmax) (o.ofInt 4)) (o.abs x) ||
           o.lt (o.div (o.sqrt o.floatmax) (o.ofInt 4)) (o.abs y)) = true)
    (h2 : o.isnan y = false) (h3 : o.isinf y = false) :
    atanh_Complex o id invC ⟨x, y⟩ =
      ⟨(invC ⟨x, y⟩).re, o.copysign (o.div o.pi o.two) y⟩ := by
  unfold atanh_Complex reim real_Complex imag_Complex id
  dsimp only
  rw [ite_true_of_eq_true _ _ _ h1, ite_false_of_eq_false _ _ _ h2, ite_false_of_eq_false _ _ _ h3]

private theorem trig_part1 (tr : F64Transcendentals)
    (htr : ∀ x : F64, F64.isnan x = false →
      tr.sincos (F64.neg x) = (F64.neg (tr.sincos x).1, (tr.sincos x).2) ∧
      tr.sincospi (F64.neg x) = (F64.neg (tr.sincospi x).1, (tr.sincospi x).2) ∧
      tr.sinh (F64.neg x) = F64.neg (tr.sinh x) ∧
      tr.cosh (F64.neg x) = tr.cosh x ∧
      tr.tan (F64.neg x) = F64.neg (tr.tan x) ∧
      F64.isnan (tr.tan x) = false) :
    ∀ (theta zr zi : F64), F64.isnan theta = false → F64.isnan zr = false →
      cis_Real (f64Ops tr).sincos (F64.neg theta) = conj_Complex F64.neg (cis_Real (f64Ops tr).sincos theta) ∧
      cispi_Real (f64Ops tr).sincospi (F64.neg theta) = conj_Complex F64.neg (cispi_Real (f64Ops tr).sincospi theta) ∧
      (cis_Complex F64.neg (f64Ops tr).exp (f64Ops tr).sincos F64.mul ⟨F64.neg zr, zi⟩).re =
        (cis_Complex F64.neg (f64Ops tr).exp (f64Ops tr).sincos F64.mul ⟨zr, zi⟩).re ∧
      (cispi_Complex Fl64.pi F64.mul F64.neg (f64Ops tr).exp (f64Ops tr).sincospi F64.mul ⟨F64.neg zr, zi⟩).re =
        (cispi_Complex Fl64.pi F64.mul F64.neg (f64Ops tr).exp (f64Ops tr).sincospi F64.mul ⟨zr, zi⟩).re := by
  intro theta zr zi hth hzr
  have hsc := (htr theta hth).1
  have hscpi := (htr theta hth).2.1
  have hzr_sc := (htr zr hzr).1
  have hzr_scpi := (htr zr hzr).2.1
  simp [cis_Real, cispi_Real, cis_Complex, cispi_Complex, conj_Complex,
    real_Complex, imag_Complex, hsc, hscpi, hzr_sc, hzr_scpi]

private theorem trig_part3 (tr : F64Transcendentals)
    (htr : ∀ x : F64, F64.isnan x = false →
      tr.sincos (F64.neg x) = (F64.neg (tr.sincos x).1, (tr.sincos x).2) ∧
      tr.sincospi (F64.neg x) = (F64.neg (tr.sincospi x).1, (tr.sincospi x).2) ∧
      tr.sinh (F64.neg x) = F64.neg (tr.sinh x) ∧
      tr.cosh (F64.neg x) = tr.cosh x ∧
      tr.tan (F64.neg x) = F64.neg (tr.tan x) ∧
      F64.isnan (tr.tan x) = false) :
    ∀ (s : Bool) (zi : F64), F64.isnan zi = false →
      let zr := F64.zero s
      sin_Complex (f64Ops tr) id ⟨zr, zi⟩ = ⟨zr, tr.sinh zi⟩ ∧
      sin_Complex (f64Ops tr) id (neg_Complex F64.neg ⟨zr, zi⟩) = neg_Complex F64.neg (sin_Complex (f64Ops tr) id ⟨zr, zi⟩) ∧
      sin_Complex (f64Ops tr) id (conj_Complex F64.neg ⟨zr, zi⟩) = conj_Complex F64.neg (sin_Complex (f64Ops tr) id ⟨zr, zi⟩) ∧
      cos_Complex (f64Ops tr) id ⟨zr, zi⟩ = ⟨tr.cosh zi, F64.neg (Fl64.flipsign zr zi)⟩ ∧
      cos_Complex (f64Ops tr) id (neg_Complex F64.neg ⟨zr, zi⟩) = cos_Complex (f64Ops tr) id ⟨zr, zi⟩ ∧
      cos_Complex (f64Ops tr) id (conj_Complex F64.neg ⟨zr, zi⟩) = conj_Complex F64.neg (cos_Complex (f64Ops tr) id ⟨zr, zi⟩) ∧
      sinh_Complex (f64Ops tr) id ⟨zi, zr⟩ = ⟨tr.sinh zi, zr⟩ ∧
      (cosh_Complex (f64Ops tr) F64.neg id ⟨zi, zr⟩).re = tr.cosh zi ∧
      F64.iszero (cosh_Complex (f64Ops tr) F64.neg id ⟨zi, zr⟩).im = true := by
  intro s zi hnan
  have heq0 : F64.eq (F64.zero s) Fl64.pzero = true := by cases s <;> decide
  have heq0_neg : F64.eq (F64.neg (F64.zero s)) Fl64.pzero = true := by cases s <;> decide
  have hnan_neg : F64.isnan (F64.neg zi) = false := by rw [isnan_neg, hnan]
  have hsh := (htr zi hnan).2.2.1
  have hch := (htr zi hnan).2.2.2.1
  simp only [sin_Complex, sinh_Complex, cos_Complex, cosh_Complex, neg_Complex, conj_Complex,
    f64Ops_isnan, f64Ops_eq, f64Ops_zero, f64Ops_neg, f64Ops_flipsign, f64Ops_sinh, f64Ops_cosh,
    reim, real_Complex, imag_Complex, id_eq, heq0, heq0_neg, hnan, hnan_neg,
    hsh, hch, neg_neg_f64, flipsign_neg_left, flipsign_neg_right, iszero_flipsign_zero,
    Bool.false_eq_true, ↓reduceIte, and_self]

private theorem trig_part4 (tr : F64Transcendentals)
    (htr : ∀ x : F64, F64.isnan x = false →
      tr.sincos (F64.neg x) = (F64.neg (tr.sincos x).1, (tr.sincos x).2) ∧
      tr.sincospi (F64.neg x) = (F64.neg (tr.sincospi x).1, (tr.sincospi x).2) ∧
      tr.sinh (F64.neg x) = F64.neg (tr.sinh x) ∧
      tr.cosh (F64.neg x) = tr.cosh x ∧
      tr.tan (F64.neg x) = F64.neg (tr.tan x) ∧
      F64.isnan (tr.tan x) = false) :
    ∀ (zr zi : F64), F64.isnan zr = false → F64.isnan zi = false →
      (sin_Complex (f64Ops tr) id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (sin_Complex (f64Ops tr) id ⟨zr, zi⟩).re ∧
      (cos_Complex (f64Ops tr) id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (cos_Complex (f64Ops tr) id ⟨zr, zi⟩).re ∧
      (tanh_Complex (f64Ops tr) id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (tanh_Complex (f64Ops tr) id ⟨zr, zi⟩).re ∧
      (tan_Complex (f64Ops tr) F64.neg id ⟨F64.neg zr, zi⟩).im = (tan_Complex (f64Ops tr) F64.neg id ⟨zr, zi⟩).im := by
  intro zr zi hzr hzi
  have hzi_neg : F64.isnan (F64.neg zi) = false := by rw [isnan_neg, hzi]
  have hch := (htr zi hzi).2.2.2.1
  have htan := (htr zi hzi).2.2.2.2.1
  have htan_nan := (htr zi hzi).2.2.2.2.2
  have htan_zr := (htr zr hzr).2.2.2.2.1
  have htan_zr_nan := (htr zr hzr).2.2.2.2.2
  have htt : F64.mul (F64.neg (tr.tan zi)) (F64.neg (tr.tan zi)) = F64.mul (tr.tan zi) (tr.tan zi) :=
    mul_neg_neg_of_not_nan _ _ htan_nan htan_nan
  have htt_zr : F64.mul (F64.neg (tr.tan zr)) (F64.neg (tr.tan zr)) = F64.mul (tr.tan zr) (tr.tan zr) :=
    mul_neg_neg_of_not_nan _ _ htan_zr_nan htan_zr_nan
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sin_Complex conj_Complex real_Complex imag_Complex
    simp only [f64Ops_eq, f64Ops_zero, f64Ops_isfinite, f64Ops_isinf, f64Ops_nan,
      f64Ops_mul, f64Ops_sinh, f64Ops_cosh, id_eq, eq_zero_neg, isinf_neg, hch]
    by_cases h1 : F64.eq zr Fl64.pzero = true
    · simp [h1]
    · by_cases h2 : F64.isfinite zr = true
      · simp [h1, h2]
      · by_cases h3 : (F64.eq zi Fl64.pzero || F64.isinf zi) = true <;> simp [h1, h2, h3]
  · unfold cos_Complex conj_Complex real_Complex imag_Complex
    simp only [f64Ops_eq, f64Ops_zero, f64Ops_isfinite, f64Ops_isinf, f64Ops_nan, f64Ops_neg,
      f64Ops_mul, f64Ops_sinh, f64Ops_cosh, f64Ops_flipsign, id_eq, eq_zero_neg, isinf_neg, hch]
    by_cases h1 : F64.eq zr Fl64.pzero = true
    · simp [h1]
    · by_cases h2 : F64.isfinite zr = true
      · simp [h1, h2]
      · by_cases h3 : F64.eq zi Fl64.pzero = true
        · simp [h1, h2, h3]
        · by_cases h4 : F64.isinf zi = true <;> simp [h1, h2, h3, h4]
  · unfold tanh_Complex conj_Complex div_Complex_Real reim real_Complex imag_Complex
    simp only [f64Ops_isnan, f64Ops_eq, f64Ops_zero, f64Ops_lt, f64Ops_asinh, f64Ops_prevfloat,
      f64Ops_inf, f64Ops_mul, f64Ops_ofInt, f64Ops_abs, f64Ops_copysign, f64Ops_one, f64Ops_tan,
      f64Ops_isinf, f64Ops_sinh, f64Ops_add, f64Ops_div,
      id_eq, hzr, eq_zero_neg, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      htan, htt, isinf_neg]
    by_cases hc1 : F64.lt (tr.asinh (F64.prevfloat Fl64.inf)) (F64.mul (F64.ofInt 4) (F64.abs zr)) = true
    · simp [hc1]
    · by_cases hc2 : F64.isinf (tr.tan zi) = true <;> simp [hc1, hc2]
  · unfold tan_Complex tanh_Complex div_Complex_Real reim real_Complex imag_Complex
    simp only [f64Ops_isnan, f64Ops_eq, f64Ops_zero, f64Ops_lt, f64Ops_asinh, f64Ops_prevfloat,
      f64Ops_inf, f64Ops_mul, f64Ops_ofInt, f64Ops_abs, f64Ops_copysign, f64Ops_one, f64Ops_tan,
      f64Ops_isinf, f64Ops_sinh, f64Ops_add, f64Ops_div, f64Ops_neg,
      id_eq, hzi_neg, eq_zero_neg, abs_neg_f64, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      htan_zr, htt_zr, isinf_neg]
    by_cases hc1 : F64.lt (tr.asinh (F64.prevfloat Fl64.inf)) (F64.mul (F64.ofInt 4) (F64.abs zi)) = true
    · simp [hc1]
    · by_cases hc2 : F64.isinf (tr.tan zr) = true <;> simp [hc1, hc2]

private theorem trig_part5 (tr : F64Transcendentals) :
    ∀ (zr zi : F64),
      F64.lt ((f64Ops tr).asinh ((f64Ops tr).prevfloat (f64Ops tr).inf)) (F64.mul (F64.ofInt 4) (F64.abs zi)) = true →
      F64.isnan zi = false →
      (tanh_Complex (f64Ops tr) id ⟨zi, zr⟩).re = Fl64.copysign F64.one zi ∧
      F64.iszero (tanh_Complex (f64Ops tr) id ⟨zi, zr⟩).im = true ∧
      F64.iszero (tan_Complex (f64Ops tr) F64.neg id ⟨zr, zi⟩).re = true ∧
      (tan_Complex (f64Ops tr) F64.neg id ⟨zr, zi⟩).im = Fl64.copysign F64.one zi := by
  intro zr zi hlt hnan
  have hnan_neg : (F64.isnan (F64.neg zi) && F64.eq zr Fl64.pzero) = false := by
    rw [isnan_neg, hnan]; rfl
  have hnan_zi : (F64.isnan zi && F64.eq zr Fl64.pzero) = false := by
    rw [hnan]; rfl
  have hlt_neg : F64.lt ((f64Ops tr).asinh ((f64Ops tr).prevfloat (f64Ops tr).inf))
      (F64.mul (F64.ofInt 4) (F64.abs (F64.neg zi))) = true := by
    rw [abs_neg_f64]; exact hlt
  have hzero_copysign : ∀ y : F64, F64.iszero (Fl64.copysign Fl64.pzero y) = true := by
    intro y; unfold Fl64.copysign; split <;> decide
  unfold tan_Complex tanh_Complex reim real_Complex imag_Complex
  simp only [f64Ops_isnan, f64Ops_eq, f64Ops_zero, f64Ops_lt, f64Ops_asinh, f64Ops_prevfloat,
    f64Ops_inf, f64Ops_mul, f64Ops_ofInt, f64Ops_abs, f64Ops_copysign, f64Ops_one, f64Ops_neg] at hlt hlt_neg ⊢
  simp only [id_eq, hnan_zi, hnan_neg, Bool.false_eq_true, ↓reduceIte,
    hlt, hlt_neg, hzero_copysign, neg_copysign_neg, and_self]

private theorem trig_part6 (tr : F64Transcendentals) (sq : ComplexF64 → ComplexF64) :
    ∀ (s : Bool) (zi : F64), F64.isinf zi = false →
      (asin_Complex (f64Ops tr) sq ⟨F64.zero s, zi⟩).re = F64.zero s ∧
      (asinh_Complex (f64Ops tr) sq ⟨zi, F64.zero s⟩).im = F64.zero s := by
  intro s zi _
  have hz0 : (f64Ops tr).isinf (F64.zero s) = false := by rw [f64Ops_isinf]; cases s <;> decide
  have heq0 : (f64Ops tr).eq (F64.zero s) (f64Ops tr).zero = true := by rw [f64Ops_eq, f64Ops_zero]; cases s <;> decide
  have hz0_neg : (f64Ops tr).isinf (F64.neg (F64.zero s)) = false := by rw [f64Ops_isinf]; cases s <;> decide
  have heq0_neg : (f64Ops tr).eq (F64.neg (F64.zero s)) (f64Ops tr).zero = true := by rw [f64Ops_eq, f64Ops_zero]; cases s <;> decide
  have h1 := asin_Complex_re_of_not_isinf (f64Ops tr) sq (F64.zero s) zi hz0 heq0
  have h2 : (asinh_Complex (f64Ops tr) sq ⟨zi, F64.zero s⟩).im = F64.zero s := by
    unfold asinh_Complex real_Complex imag_Complex
    dsimp only
    rw [f64Ops_neg, asin_Complex_re_of_not_isinf (f64Ops tr) sq (F64.neg (F64.zero s)) zi hz0_neg heq0_neg, neg_neg_f64]
  exact ⟨h1, h2⟩

private theorem trig_part7 (tr : F64Transcendentals) (sq : ComplexF64 → ComplexF64) :
    ∀ (sr si : Bool),
      let zr := F64.inf sr
      let zi := F64.inf si
      let o := f64Ops tr
      sin_Complex o id ⟨zr, F64.zero si⟩ = ⟨F64.nan, F64.zero si⟩ ∧
      sin_Complex o id ⟨zr, zi⟩ = ⟨F64.nan, zi⟩ ∧
      cos_Complex o id ⟨zr, F64.zero si⟩ = ⟨F64.nan, F64.zero (sr == si)⟩ ∧
      cos_Complex o id ⟨zr, zi⟩ = ⟨Fl64.inf, F64.nan⟩ ∧
      (asin_Complex o sq ⟨zr, zi⟩).im = zi ∧
      F64.signbit (asin_Complex o sq ⟨zr, zi⟩).re = sr ∧
      (asinh_Complex o sq ⟨zr, zi⟩).re = zr ∧
      (asinh_Complex o sq ⟨zr, zi⟩).im = Fl64.copysign (F64.div Fl64.pi (F64.ofInt 4)) zi ∧
      acos_Complex o id sq ⟨F64.zero sr, F64.zero si⟩ = ⟨F64.div Fl64.pi Fl64.two, F64.zero (!si)⟩ ∧
      acos_Complex o id sq ⟨Fl64.inf, Fl64.pzero⟩ = ⟨Fl64.pzero, Fl64.ninf⟩ ∧
      acos_Complex o id sq ⟨Fl64.ninf, Fl64.nzero⟩ = ⟨Fl64.pi, Fl64.inf⟩ ∧
      acosh_Complex o sq ⟨Fl64.ninf, Fl64.nzero⟩ = ⟨Fl64.inf, F64.neg Fl64.pi⟩ ∧
      acosh_Complex o sq ⟨F64.nan, zi⟩ = ⟨Fl64.inf, F64.nan⟩ := by
  intro sr si
  dsimp only
  have hi_eq0 : (f64Ops tr).eq (F64.inf sr) (f64Ops tr).zero = false := by
    rw [f64Ops_eq, f64Ops_zero]; cases sr <;> decide
  have hi_fin : (f64Ops tr).isfinite (F64.inf sr) = false := by
    rw [f64Ops_isfinite]; cases sr <;> decide
  have hi_nan : (f64Ops tr).isnan (F64.inf sr) = false := by
    rw [f64Ops_isnan]; cases sr <;> decide
  have hi_inf : (f64Ops tr).isinf (F64.inf sr) = true := by
    rw [f64Ops_isinf]; cases sr <;> decide
  have hi_inf2 : (f64Ops tr).isinf (F64.inf si) = true := by
    rw [f64Ops_isinf]; cases si <;> decide
  have hi_eq0_2 : (f64Ops tr).eq (F64.inf si) (f64Ops tr).zero = false := by
    rw [f64Ops_eq, f64Ops_zero]; cases si <;> decide
  have hz_eq0 : (f64Ops tr).eq (F64.zero si) (f64Ops tr).zero = true := by
    rw [f64Ops_eq, f64Ops_zero]; cases si <;> decide
  have hsin1 : sin_Complex (f64Ops tr) id ⟨F64.inf sr, F64.zero si⟩ = ⟨F64.nan, F64.zero si⟩ := by
    have h3 : ((f64Ops tr).eq (F64.zero si) (f64Ops tr).zero || (f64Ops tr).isinf (F64.zero si)) = true := by
      rw [hz_eq0, Bool.true_or]
    rw [sin_Complex_not_fin (f64Ops tr) (F64.inf sr) (F64.zero si) hi_eq0 hi_fin h3, f64Ops_nan]
  have hsin2 : sin_Complex (f64Ops tr) id ⟨F64.inf sr, F64.inf si⟩ = ⟨F64.nan, F64.inf si⟩ := by
    have h3 : ((f64Ops tr).eq (F64.inf si) (f64Ops tr).zero || (f64Ops tr).isinf (F64.inf si)) = true := by
      rw [hi_inf2, Bool.or_true]
    rw [sin_Complex_not_fin (f64Ops tr) (F64.inf sr) (F64.inf si) hi_eq0 hi_fin h3, f64Ops_nan]
  have hcos1 : cos_Complex (f64Ops tr) id ⟨F64.inf sr, F64.zero si⟩ = ⟨F64.nan, F64.zero (sr == si)⟩ := by
    have hflip : F64.neg (Fl64.flipsign (F64.zero si) (F64.inf sr)) = F64.zero (sr == si) := by
      cases sr <;> cases si <;> decide
    rw [cos_Complex_not_fin_zero (f64Ops tr) (F64.inf sr) (F64.zero si) hi_eq0 hi_fin hz_eq0 hi_nan,
      f64Ops_nan, f64Ops_neg, f64Ops_flipsign, hflip]
  have hcos2 : cos_Complex (f64Ops tr) id ⟨F64.inf sr, F64.inf si⟩ = ⟨Fl64.inf, F64.nan⟩ := by
    rw [cos_Complex_not_fin_inf (f64Ops tr) (F64.inf sr) (F64.inf si) hi_eq0 hi_fin hi_eq0_2 hi_inf2,
      f64Ops_inf, f64Ops_nan]
  have hasin_im : (asin_Complex (f64Ops tr) sq ⟨F64.inf sr, F64.inf si⟩).im = F64.inf si := by
    rw [asin_Complex_inf_inf (f64Ops tr) sq (F64.inf sr) (F64.inf si) hi_inf hi_inf2]
  have hasin_re : F64.signbit (asin_Complex (f64Ops tr) sq ⟨F64.inf sr, F64.inf si⟩).re = sr := by
    have hsb : F64.signbit (F64.inf sr) = sr := by cases sr <;> decide
    rw [asin_Complex_inf_inf (f64Ops tr) sq (F64.inf sr) (F64.inf si) hi_inf hi_inf2]
    dsimp only
    rw [f64Ops_copysign, signbit_copysign, hsb]
  have hinf_neg : (f64Ops tr).isinf ((f64Ops tr).neg (F64.inf si)) = true := by
    rw [f64Ops_isinf, f64Ops_neg]; cases si <;> decide
  have hasinh_re : (asinh_Complex (f64Ops tr) sq ⟨F64.inf sr, F64.inf si⟩).re = F64.inf sr := by
    rw [asinh_Complex_inf_inf (f64Ops tr) sq (F64.inf sr) (F64.inf si) hinf_neg hi_inf]
  have hasinh_im :
      (asinh_Complex (f64Ops tr) sq ⟨F64.inf sr, F64.inf si⟩).im =
        Fl64.copysign (F64.div Fl64.pi (F64.ofInt 4)) (F64.inf si) := by
    rw [asinh_Complex_inf_inf (f64Ops tr) sq (F64.inf sr) (F64.inf si) hinf_neg hi_inf]
    dsimp only
    rw [f64Ops_neg, f64Ops_copysign, f64Ops_div, f64Ops_pi, f64Ops_ofInt, neg_copysign_neg]
  have hacos1 :
      acos_Complex (f64Ops tr) id sq ⟨F64.zero sr, F64.zero si⟩ = ⟨F64.div Fl64.pi Fl64.two, F64.zero (!si)⟩ := by
    have h1 : (f64Ops tr).isnan (F64.zero sr) = false := by rw [f64Ops_isnan]; cases sr <;> decide
    have h2 : (f64Ops tr).isnan (F64.zero si) = false := by rw [f64Ops_isnan]; cases si <;> decide
    have h3 : (f64Ops tr).eq (F64.zero sr) (F64.zero si) = true := by rw [f64Ops_eq]; cases sr <;> cases si <;> decide
    have h4 : (f64Ops tr).eq (F64.zero si) (f64Ops tr).zero = true := hz_eq0
    have hz_neg : F64.neg (F64.zero si) = F64.zero (!si) := by cases si <;> decide
    rw [acos_Complex_zero_zero (f64Ops tr) sq (F64.zero sr) (F64.zero si) h1 h2 h3 h4,
      f64Ops_div, f64Ops_pi, f64Ops_two, f64Ops_neg, hz_neg]
  have hacos2 :
      acos_Complex (f64Ops tr) id sq ⟨Fl64.inf, Fl64.pzero⟩ = ⟨Fl64.pzero, Fl64.ninf⟩ := by
    have h1 : (f64Ops tr).isnan Fl64.inf = false := by rw [f64Ops_isnan]; decide
    have h2 : (f64Ops tr).isnan Fl64.pzero = false := by rw [f64Ops_isnan]; decide
    have h3 : (f64Ops tr).eq Fl64.inf Fl64.pzero = false := by rw [f64Ops_eq]; decide
    have h4 : (f64Ops tr).eq Fl64.inf (f64Ops tr).inf = true := by rw [f64Ops_eq, f64Ops_inf]; decide
    have h5 : (f64Ops tr).identical Fl64.pzero (f64Ops tr).zero = true := by rw [f64Ops_identical, f64Ops_zero]; decide
    have hn : F64.neg Fl64.inf = Fl64.ninf := by decide
    rw [acos_Complex_inf_zero (f64Ops tr) sq Fl64.inf Fl64.pzero h1 h2 h3 h4 h5, f64Ops_neg, hn]
  have hacos3 :
      acos_Complex (f64Ops tr) id sq ⟨Fl64.ninf, Fl64.nzero⟩ = ⟨Fl64.pi, Fl64.inf⟩ := by
    have h1 : (f64Ops tr).isnan Fl64.ninf = false := by rw [f64Ops_isnan]; decide
    have h2 : (f64Ops tr).isnan Fl64.nzero = false := by rw [f64Ops_isnan]; decide
    have h3 : (f64Ops tr).eq Fl64.ninf Fl64.nzero = false := by rw [f64Ops_eq]; decide
    have h4 : (f64Ops tr).eq Fl64.ninf (f64Ops tr).inf = false := by rw [f64Ops_eq, f64Ops_inf]; decide
    have h5 : (f64Ops tr).eq Fl64.ninf (f64Ops tr).ninf = true := by rw [f64Ops_eq, f64Ops_ninf]; decide
    have h6 : (f64Ops tr).identical Fl64.nzero (f64Ops tr).nzero = true := by rw [f64Ops_identical, f64Ops_nzero]; decide
    have hn : F64.neg Fl64.ninf = Fl64.inf := by decide
    rw [acos_Complex_ninf_nzero (f64Ops tr) sq Fl64.ninf Fl64.nzero h1 h2 h3 h4 h5 h6,
      f64Ops_pi, f64Ops_neg, hn]
  have hacosh1 :
      acosh_Complex (f64Ops tr) sq ⟨Fl64.ninf, Fl64.nzero⟩ = ⟨Fl64.inf, F64.neg Fl64.pi⟩ := by
    have h1 : (f64Ops tr).isnan Fl64.ninf = false := by rw [f64Ops_isnan]; decide
    have h2 : (f64Ops tr).isnan Fl64.nzero = false := by rw [f64Ops_isnan]; decide
    have h3 : (f64Ops tr).eq Fl64.ninf (f64Ops tr).ninf = true := by rw [f64Ops_eq, f64Ops_ninf]; decide
    have h4 : (f64Ops tr).identical Fl64.nzero (f64Ops tr).nzero = true := by rw [f64Ops_identical, f64Ops_nzero]; decide
    rw [acosh_Complex_ninf_nzero (f64Ops tr) sq Fl64.ninf Fl64.nzero h1 h2 h3 h4,
      f64Ops_inf, f64Ops_neg, f64Ops_pi]
  have hacosh2 :
      acosh_Complex (f64Ops tr) sq ⟨F64.nan, F64.inf si⟩ = ⟨Fl64.inf, F64.nan⟩ := by
    have h1 : (f64Ops tr).isnan F64.nan = true := by rw [f64Ops_isnan]; decide
    rw [acosh_Complex_nan_inf (f64Ops tr) sq F64.nan (F64.inf si) h1 hi_inf2,
      f64Ops_inf, f64Ops_nan]
  exact ⟨hsin1, hsin2, hcos1, hcos2, hasin_im, hasin_re, hasinh_re, hasinh_im,
    hacos1, hacos2, hacos3, hacosh1, hacosh2⟩

private theorem trig_part8 (tr : F64Transcendentals)
    (hθ1 : F64.lt (F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)) F64.one = false)
    (hθ0 : ∀ s : Bool, F64.lt (F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)) (F64.abs (F64.zero s)) = false) :
    ∀ (s : Bool) (x y : F64),
      atanh_Complex (f64Ops tr) id inv_Complex_F64 ⟨F64.one, F64.zero s⟩ = ⟨Fl64.inf, F64.zero s⟩ ∧
      atanh_Complex (f64Ops tr) id inv_Complex_F64 ⟨F64.neg F64.one, F64.zero s⟩ = ⟨Fl64.ninf, F64.zero s⟩ ∧
      atan_Complex (f64Ops tr) F64.neg id inv_Complex_F64 ⟨F64.zero s, F64.one⟩ = ⟨F64.zero s, Fl64.inf⟩ ∧
      atan_Complex (f64Ops tr) F64.neg id inv_Complex_F64 ⟨F64.zero s, F64.neg F64.one⟩ = ⟨F64.zero s, Fl64.ninf⟩ ∧
      (F64.lt (F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)) (F64.abs y) = false →
        (atanh_Complex (f64Ops tr) id inv_Complex_F64 ⟨F64.zero s, y⟩).re = F64.zero s ∧
        (atan_Complex (f64Ops tr) F64.neg id inv_Complex_F64 ⟨y, F64.zero s⟩).im = F64.zero s) ∧
      ((F64.lt (F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)) (F64.abs x) ||
        F64.lt (F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)) (F64.abs y)) = true →
        F64.isnan y = false → F64.isinf y = false →
        atanh_Complex (f64Ops tr) id inv_Complex_F64 ⟨x, y⟩ =
          ⟨(inv_Complex_F64 ⟨x, y⟩).re, Fl64.copysign (F64.div Fl64.pi Fl64.two) y⟩) := by
  intro s x y
  have h1 : F64.lt (F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)) (F64.abs (F64.zero s)) = false := hθ0 s
  have habs1 : F64.abs F64.one = F64.one := by decide
  have habs_n1 : F64.abs (F64.neg F64.one) = F64.one := by decide
  have hcs1 : Fl64.copysign F64.one F64.one = F64.one := by decide
  have hcs_n1 : Fl64.copysign F64.one (F64.neg F64.one) = F64.neg F64.one := by decide
  have hfin1 : F64.isfinite F64.one = true := by decide
  have hfin_n1 : F64.isfinite (F64.neg F64.one) = true := by decide
  have hmul_1_1 : F64.mul F64.one F64.one = F64.one := by decide
  have hmul_n1_n1 : F64.mul (F64.neg F64.one) (F64.neg F64.one) = F64.one := by decide
  have heq_1_1 : F64.eq F64.one F64.one = true := by decide
  have heq_z_0 : ∀ b : Bool, F64.eq (F64.zero b) Fl64.pzero = true := by intro b; cases b <;> decide
  have heq_z_1 : ∀ b : Bool, F64.eq (F64.zero b) F64.one = false := by intro b; cases b <;> decide
  have hmul_1_inf : F64.mul F64.one Fl64.inf = Fl64.inf := by decide
  have hmul_n1_inf : F64.mul (F64.neg F64.one) Fl64.inf = Fl64.ninf := by decide
  have hneg_inf : F64.neg Fl64.inf = Fl64.ninf := by decide
  have hneg_ninf : F64.neg Fl64.ninf = Fl64.inf := by decide
  have hsb1 : F64.signbit F64.one = false := by decide
  have hsb_n1 : F64.signbit (F64.neg F64.one) = true := by decide
  have hneg_z : ∀ b : Bool, F64.neg (F64.zero b) = F64.zero (!b) := by
    intro b; cases b <;> decide
  have hcs_z : ∀ b : Bool, F64.isfinite (Fl64.copysign F64.one (F64.zero b)) = true := by
    intro b; cases b <;> decide
  have hsb_cs : ∀ b : Bool, F64.signbit (Fl64.copysign F64.one (F64.zero b)) = b := by
    intro b; cases b <;> decide
  have hp_pos :
      atanh_Complex (f64Ops tr) id inv_Complex_F64 ⟨F64.one, F64.zero s⟩ = ⟨Fl64.inf, F64.zero s⟩ := by
    have hc1 : ((f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs F64.one) ||
                (f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs (F64.zero s))) = false := by
      simp only [f64Ops_lt, f64Ops_div, f64Ops_sqrt, f64Ops_floatmax, f64Ops_ofInt, f64Ops_abs, habs1, hθ1, h1, Bool.or_self]
    have hc2 : (f64Ops tr).eq ((f64Ops tr).mul ((f64Ops tr).copysign (f64Ops tr).one F64.one) F64.one) (f64Ops tr).one = true := by
      simp only [f64Ops_eq, f64Ops_mul, f64Ops_copysign, f64Ops_one, hcs1, hmul_1_1, heq_1_1]
    have hc3 : (f64Ops tr).eq ((f64Ops tr).mul ((f64Ops tr).copysign (f64Ops tr).one F64.one) (F64.zero s)) (f64Ops tr).zero = true := by
      simp only [f64Ops_eq, f64Ops_mul, f64Ops_copysign, f64Ops_one, f64Ops_zero, hcs1, mul_zero_f64 F64.one s hfin1, heq_z_0]
    rw [atanh_Complex_pole (f64Ops tr) inv_Complex_F64 F64.one (F64.zero s) hc1 hc2 hc3]
    simp only [f64Ops_mul, f64Ops_copysign, f64Ops_one, f64Ops_inf, hcs1, hmul_1_inf,
      mul_zero_f64 F64.one _ hfin1, hsb1, Bool.false_bne]
  have hp_neg :
      ∀ b : Bool, atanh_Complex (f64Ops tr) id inv_Complex_F64 ⟨F64.neg F64.one, F64.zero b⟩ = ⟨Fl64.ninf, F64.zero b⟩ := by
    intro b
    have hc1 : ((f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs (F64.neg F64.one)) ||
                (f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs (F64.zero b))) = false := by
      simp only [f64Ops_lt, f64Ops_div, f64Ops_sqrt, f64Ops_floatmax, f64Ops_ofInt, f64Ops_abs, habs_n1, hθ1, hθ0 b, Bool.or_self]
    have hc2 : (f64Ops tr).eq ((f64Ops tr).mul ((f64Ops tr).copysign (f64Ops tr).one (F64.neg F64.one)) (F64.neg F64.one)) (f64Ops tr).one = true := by
      simp only [f64Ops_eq, f64Ops_mul, f64Ops_copysign, f64Ops_one, hcs_n1, hmul_n1_n1, heq_1_1]
    have hc3 : (f64Ops tr).eq ((f64Ops tr).mul ((f64Ops tr).copysign (f64Ops tr).one (F64.neg F64.one)) (F64.zero b)) (f64Ops tr).zero = true := by
      simp only [f64Ops_eq, f64Ops_mul, f64Ops_copysign, f64Ops_one, f64Ops_zero, hcs_n1, mul_zero_f64 (F64.neg F64.one) b hfin_n1, heq_z_0]
    rw [atanh_Complex_pole (f64Ops tr) inv_Complex_F64 (F64.neg F64.one) (F64.zero b) hc1 hc2 hc3]
    simp only [f64Ops_mul, f64Ops_copysign, f64Ops_one, f64Ops_inf, hcs_n1, hmul_n1_inf,
      mul_zero_f64 (F64.neg F64.one) _ hfin_n1, hsb_n1]
    cases b <;> rfl
  have hatan_pos :
      atan_Complex (f64Ops tr) F64.neg id inv_Complex_F64 ⟨F64.zero s, F64.one⟩ = ⟨F64.zero s, Fl64.inf⟩ := by
    unfold atan_Complex real_Complex imag_Complex
    dsimp only
    rw [f64Ops_neg, hp_neg s]
    dsimp only
    rw [hneg_ninf]
  have hatan_neg :
      atan_Complex (f64Ops tr) F64.neg id inv_Complex_F64 ⟨F64.zero s, F64.neg F64.one⟩ = ⟨F64.zero s, Fl64.ninf⟩ := by
    have hnn1 : F64.neg (F64.neg F64.one) = F64.one := by decide
    unfold atan_Complex real_Complex imag_Complex
    dsimp only
    rw [f64Ops_neg, hnn1, hp_pos]
    dsimp only
    rw [hneg_inf]
  refine ⟨hp_pos, hp_neg s, hatan_pos, hatan_neg, ?_, ?_⟩
  · intro hy
    have haxis : ∀ (b : Bool) (v : F64),
        F64.lt (F64.div (tr.sqrt F64.floatmax) (F64.ofInt 4)) (F64.abs v) = false →
        (atanh_Complex (f64Ops tr) id inv_Complex_F64 ⟨F64.zero b, v⟩).re = F64.zero b := by
      intro b v hv
      have hc1 : ((f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs (F64.zero b)) ||
                  (f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs v)) = false := by
        simp only [f64Ops_lt, f64Ops_div, f64Ops_sqrt, f64Ops_floatmax, f64Ops_ofInt, f64Ops_abs, hθ0 b, hv, Bool.or_self]
      have hc2 : (f64Ops tr).eq ((f64Ops tr).mul ((f64Ops tr).copysign (f64Ops tr).one (F64.zero b)) (F64.zero b)) (f64Ops tr).one = false := by
        simp only [f64Ops_eq, f64Ops_mul, f64Ops_copysign, f64Ops_one, mul_zero_f64 _ b (hcs_z b), heq_z_1]
      have hc3 : (f64Ops tr).eq ((f64Ops tr).mul ((f64Ops tr).copysign (f64Ops tr).one (F64.zero b)) (F64.zero b)) (f64Ops tr).zero = true := by
        simp only [f64Ops_eq, f64Ops_mul, f64Ops_copysign, f64Ops_one, f64Ops_zero, mul_zero_f64 _ b (hcs_z b), heq_z_0]
      rw [atanh_Complex_re_zero (f64Ops tr) inv_Complex_F64 (F64.zero b) v hc1 hc2 hc3]
      simp only [f64Ops_mul, f64Ops_copysign, f64Ops_one, mul_zero_f64 _ _ (hcs_z b), hsb_cs]
      cases b <;> rfl
    refine ⟨haxis s y hy, ?_⟩
    unfold atan_Complex real_Complex imag_Complex
    dsimp only
    rw [f64Ops_neg, hneg_z s, haxis (!s) y hy, hneg_z (!s)]
    cases s <;> rfl
  · intro hxy hny hiy
    have hc1 : ((f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs x) ||
                (f64Ops tr).lt ((f64Ops tr).div ((f64Ops tr).sqrt (f64Ops tr).floatmax) ((f64Ops tr).ofInt 4)) ((f64Ops tr).abs y)) = true := by
      simpa only [f64Ops_lt, f64Ops_div, f64Ops_sqrt, f64Ops_floatmax, f64Ops_ofInt, f64Ops_abs] using hxy
    have hc2 : (f64Ops tr).isnan y = false := by rw [f64Ops_isnan]; exact hny
    have hc3 : (f64Ops tr).isinf y = false := by rw [f64Ops_isinf]; exact hiy
    rw [atanh_Complex_large (f64Ops tr) inv_Complex_F64 x y hc1 hc2 hc3,
      f64Ops_copysign, f64Ops_div, f64Ops_pi, f64Ops_two]

private theorem trig_part9 (tr : F64Transcendentals) :
    let o := f64Ops tr
    let sq := sqrt_ComplexF64_tr tr
    (∀ v k, F64.isnan v = false →
        tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false) →
    (∀ v, F64.isnan (tr.sqrt v) = false) →
    (∀ y x,
        tr.atan2 (F64.neg y) x = F64.neg (tr.atan2 y x) ∧ F64.isfinite (tr.atan2 y x) = true) →
    (∀ x, tr.asinh (F64.neg x) = F64.neg (tr.asinh x)) →
    ∀ (zr zi : F64), F64.isfinite zr = true → F64.isfinite zi = true →
      let z : ComplexF64 := ⟨zr, zi⟩
      let oneMinusZ : ComplexF64 := sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one z
      let onePlusZ : ComplexF64 := add_Real_Complex F64.add (fun a b => (a, b)) F64.one z
      let zMinus1 : ComplexF64 := sub_Complex_Real F64.sub (fun a b => (a, b)) z F64.one
      let zPlus1 : ComplexF64 := add_Complex_Real F64.add (fun a b => (a, b)) z F64.one
      let iz : ComplexF64 := ⟨F64.neg zi, zr⟩
      let oneMinusIz : ComplexF64 := sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one iz
      let onePlusIz : ComplexF64 := add_Real_Complex F64.add (fun a b => (a, b)) F64.one iz
      (F64.eq zr Fl64.pzero = false →
        asin_Complex o sq z =
          ⟨tr.atan2 zr (real_Complex (mul_Complex F64.mul F64.sub F64.add (sq oneMinusZ) (sq onePlusZ))),
           tr.asinh (Fl64.copysign (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg oneMinusZ)) (sq onePlusZ))) zi)⟩) ∧
      (F64.eq zi Fl64.pzero = false →
        asinh_Complex o sq z =
          ⟨tr.asinh (Fl64.copysign (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg oneMinusIz)) (sq onePlusIz))) zr),
           F64.neg (tr.atan2 (F64.neg zi) (real_Complex (mul_Complex F64.mul F64.sub F64.add (sq oneMinusIz) (sq onePlusIz))))⟩) ∧
      ((F64.eq zr zi && F64.eq zi Fl64.pzero) = false →
        acos_Complex o id sq z =
          ⟨F64.mul Fl64.two (tr.atan2 (real_Complex (sq oneMinusZ)) (real_Complex (sq onePlusZ))),
           tr.asinh (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg onePlusZ)) (sq oneMinusZ)))⟩) ∧
      acosh_Complex o sq z =
        ⟨tr.asinh (real_Complex (mul_Complex F64.mul F64.sub F64.add (sq (conj_Complex F64.neg zMinus1)) (sq zPlus1))),
         F64.mul Fl64.two (tr.atan2 (imag_Complex (sq zMinus1)) (real_Complex (sq zPlus1)))⟩ ∧
      (acos_Complex o id sq (conj_Complex F64.neg z)).re = (acos_Complex o id sq z).re ∧
      (acosh_Complex o sq (conj_Complex F64.neg z)).im = F64.neg (acosh_Complex o sq z).im ∧
      (F64.isnan (sq oneMinusZ).im = false → F64.isnan (sq onePlusZ).im = false →
        (asin_Complex o sq (conj_Complex F64.neg z)).re = (asin_Complex o sq z).re) ∧
      (F64.isnan (sq oneMinusIz).im = false → F64.isnan (sq onePlusIz).im = false →
        (asinh_Complex o sq ⟨F64.neg zr, zi⟩).im = (asinh_Complex o sq z).im) ∧
      (F64.isnan (sq (conj_Complex F64.neg zMinus1)).im = false → F64.isnan (sq zPlus1).im = false →
        acosh_Complex o sq (conj_Complex F64.neg z) = conj_Complex F64.neg (acosh_Complex o sq z)) ∧
      (let s1c := sq (conj_Complex F64.neg oneMinusZ)
       let s2 := sq onePlusZ
       F64.isfinite s1c.re = true → F64.isfinite s1c.im = true →
       F64.isfinite s2.re = true → F64.isfinite s2.im = true →
       F64.isfinite (F64.mul s1c.re s2.im) = true → F64.isfinite (F64.mul s1c.im s2.re) = true →
       F64.isnan (sq oneMinusZ).im = false →
        asin_Complex o sq (conj_Complex F64.neg z) = conj_Complex F64.neg (asin_Complex o sq z)) ∧
      (let s1c := sq (conj_Complex F64.neg oneMinusIz)
       let s2 := sq onePlusIz
       F64.isfinite s1c.re = true → F64.isfinite s1c.im = true →
       F64.isfinite s2.re = true → F64.isfinite s2.im = true →
       F64.isfinite (F64.mul s1c.re s2.im) = true → F64.isfinite (F64.mul s1c.im s2.re) = true →
       F64.isnan (sq oneMinusIz).im = false →
        asinh_Complex o sq ⟨F64.neg zr, zi⟩ = ⟨F64.neg (asinh_Complex o sq z).re, (asinh_Complex o sq z).im⟩) := by
  dsimp only
  intro hld hsq hatan hasinh_odd
  have hasin_laws : ∀ (zr zi : F64), F64.isfinite zr = true → F64.isfinite zi = true →
      let z : ComplexF64 := ⟨zr, zi⟩
      let oneMinusZ : ComplexF64 := sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one z
      let onePlusZ : ComplexF64 := add_Real_Complex F64.add (fun a b => (a, b)) F64.one z
      let sq := sqrt_ComplexF64_tr tr
      (F64.isnan (sq oneMinusZ).im = false → F64.isnan (sq onePlusZ).im = false →
        (asin_Complex (f64Ops tr) sq (conj_Complex F64.neg z)).re = (asin_Complex (f64Ops tr) sq z).re) ∧
      (let s1c := sq (conj_Complex F64.neg oneMinusZ)
       let s2 := sq onePlusZ
       F64.isfinite s1c.re = true → F64.isfinite s1c.im = true →
       F64.isfinite s2.re = true → F64.isfinite s2.im = true →
       F64.isfinite (F64.mul s1c.re s2.im) = true → F64.isfinite (F64.mul s1c.im s2.re) = true →
       F64.isnan (sq oneMinusZ).im = false →
        asin_Complex (f64Ops tr) sq (conj_Complex F64.neg z) =
          conj_Complex F64.neg (asin_Complex (f64Ops tr) sq z)) := by
    intro zr zi hzr hzi
    dsimp only
    have hizr : F64.isinf zr = false := by
      rw [isfinite_iff_not_nan_not_inf] at hzr; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hzr; exact hzr.2
    have hnzi : F64.isnan zi = false := by
      rw [isfinite_iff_not_nan_not_inf] at hzi; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hzi; exact hzi.1
    have ho_izr : (f64Ops tr).isinf zr = false := by rw [f64Ops_isinf]; exact hizr
    have ho_fzr : (f64Ops tr).isfinite zr = true := by rw [f64Ops_isfinite]; exact hzr
    have hfin1 := asin_Complex_finite (f64Ops tr) (sqrt_ComplexF64_tr tr) zr zi ho_izr ho_fzr
    have hfin2 := asin_Complex_finite (f64Ops tr) (sqrt_ComplexF64_tr tr) zr (F64.neg zi) ho_izr ho_fzr
    dsimp only at hfin1 hfin2
    have hsq_1m :
        sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, F64.neg zi⟩) =
        conj_Complex F64.neg (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩)) := by
      have hn : F64.isnan (F64.neg zi) = false := by rw [isnan_neg]; exact hnzi
      exact sqrt_ComplexF64_tr_conj tr hld hsq (F64.sub F64.one zr) (F64.neg zi) hn
    have hsq_1p :
        sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, F64.neg zi⟩) =
        conj_Complex F64.neg (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩)) :=
      sqrt_ComplexF64_tr_conj tr hld hsq (F64.add F64.one zr) zi hnzi
    have h_1mc :
        sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, F64.neg zi⟩)) =
        conj_Complex F64.neg (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩))) := by
      change sqrt_ComplexF64_tr tr (conj_Complex F64.neg ⟨F64.sub F64.one zr, F64.neg (F64.neg zi)⟩) =
        conj_Complex F64.neg (sqrt_ComplexF64_tr tr ⟨F64.sub F64.one zr, F64.neg (F64.neg zi)⟩)
      exact sqrt_ComplexF64_tr_conj tr hld hsq _ _ (by rw [neg_neg_f64]; exact hnzi)
    have hre_law :
        F64.isnan (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩)).im = false →
        F64.isnan (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩)).im = false →
        (asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨zr, zi⟩)).re =
          (asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩).re := by
      intro hu hv
      change (asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, F64.neg zi⟩).re = _
      rw [hfin1, hfin2]
      change (if F64.eq zr Fl64.pzero then zr else tr.atan2 zr
        (real_Complex (mul_Complex F64.mul F64.sub F64.add
          (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, F64.neg zi⟩))
          (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, F64.neg zi⟩))))) = _
      rw [hsq_1m, hsq_1p, mul_Complex_conj_re _ _ hu hv]
      rfl
    refine ⟨hre_law, ?_⟩
    intro h1r h1i h2r h2i hp1 hp2 hu
    have hv : F64.isnan (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩)).im = false := by
      rw [isfinite_iff_not_nan_not_inf] at h2i; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2i; exact h2i.1
    have hre := hre_law hu hv
    have him :
        (asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨zr, zi⟩)).im =
          F64.neg (asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩).im := by
      change (asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, F64.neg zi⟩).im = _
      rw [hfin1, hfin2]
      change tr.asinh (Fl64.copysign (imag_Complex (mul_Complex F64.mul F64.sub F64.add
        (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, F64.neg zi⟩)))
        (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, F64.neg zi⟩)))) (F64.neg zi)) = _
      rw [h_1mc, hsq_1p]
      have habs := mul_Complex_conj_im_abs _ _ h1r h1i h2r h2i hp1 hp2
      rw [copysign_eq_of_abs_eq _ _ (F64.neg zi) habs, ← neg_copysign_neg, neg_neg_f64, hasinh_odd]
      rfl
    cases h_lhs : asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨zr, zi⟩) with
    | mk rl il =>
      cases h_rhs : asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩ with
      | mk rr ir =>
        rw [h_lhs, h_rhs] at hre him
        dsimp only at hre him
        simp [conj_Complex, real_Complex, imag_Complex, hre, him]
  intro zr zi hzr hzi
  have hnzr : F64.isnan zr = false := by
    rw [isfinite_iff_not_nan_not_inf] at hzr; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hzr; exact hzr.1
  have hizr : F64.isinf zr = false := by
    rw [isfinite_iff_not_nan_not_inf] at hzr; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hzr; exact hzr.2
  have hnzi : F64.isnan zi = false := by
    rw [isfinite_iff_not_nan_not_inf] at hzi; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hzi; exact hzi.1
  have hizi : F64.isinf zi = false := by
    rw [isfinite_iff_not_nan_not_inf] at hzi; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hzi; exact hzi.2
  have hzr_inf : F64.eq zr Fl64.inf = false :=
    eq_inf_false_of_isinf_false zr Fl64.inf hizr (by decide) (by decide)
  have hzr_ninf : F64.eq zr Fl64.ninf = false :=
    eq_inf_false_of_isinf_false zr Fl64.ninf hizr (by decide) (by decide)
  have ho_izr : (f64Ops tr).isinf zr = false := by rw [f64Ops_isinf]; exact hizr
  have ho_fzr : (f64Ops tr).isfinite zr = true := by rw [f64Ops_isfinite]; exact hzr
  have ho_nzr : (f64Ops tr).isnan zr = false := by rw [f64Ops_isnan]; exact hnzr
  have ho_nzi : (f64Ops tr).isnan zi = false := by rw [f64Ops_isnan]; exact hnzi
  have ho_nnzi : (f64Ops tr).isnan (F64.neg zi) = false := by rw [f64Ops_isnan, isnan_neg]; exact hnzi
  have ho_inf : (f64Ops tr).eq zr (f64Ops tr).inf = false := by rw [f64Ops_eq, f64Ops_inf]; exact hzr_inf
  have ho_ninf : (f64Ops tr).eq zr (f64Ops tr).ninf = false := by rw [f64Ops_eq, f64Ops_ninf]; exact hzr_ninf
  have ho_inzi : (f64Ops tr).isinf (F64.neg zi) = false := by rw [f64Ops_isinf, isinf_neg]; exact hizi
  have ho_fnzi : (f64Ops tr).isfinite (F64.neg zi) = true := by rw [f64Ops_isfinite, isfinite_neg]; exact hzi
  have h1 : F64.eq zr Fl64.pzero = false →
      asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩ =
        ⟨tr.atan2 zr (real_Complex (mul_Complex F64.mul F64.sub F64.add (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩)) (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩)))),
         tr.asinh (Fl64.copysign (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩))) (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩)))) zi)⟩ := by
    intro hzr0
    have ho_zr0 : (f64Ops tr).eq zr (f64Ops tr).zero = false := by rw [f64Ops_eq, f64Ops_zero]; exact hzr0
    have hgen := asin_Complex_general (f64Ops tr) (sqrt_ComplexF64_tr tr) zr zi ho_izr ho_zr0 ho_fzr
    dsimp only at hgen
    rw [hgen]
    simp only [f64Ops_atan2, f64Ops_mul, f64Ops_sub, f64Ops_add, f64Ops_neg, f64Ops_one, f64Ops_asinh, f64Ops_copysign]
  have h2 : F64.eq zi Fl64.pzero = false →
      asinh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩ =
        ⟨tr.asinh (Fl64.copysign (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨F64.neg zi, zr⟩))) (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨F64.neg zi, zr⟩)))) zr),
         F64.neg (tr.atan2 (F64.neg zi) (real_Complex (mul_Complex F64.mul F64.sub F64.add (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨F64.neg zi, zr⟩)) (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨F64.neg zi, zr⟩)))))⟩ := by
    intro hzi0
    have ho_nzi0 : (f64Ops tr).eq (F64.neg zi) (f64Ops tr).zero = false := by
      rw [f64Ops_eq, f64Ops_zero, eq_zero_neg]; exact hzi0
    have hgen := asin_Complex_general (f64Ops tr) (sqrt_ComplexF64_tr tr) (F64.neg zi) zr ho_inzi ho_nzi0 ho_fnzi
    dsimp only at hgen
    unfold asinh_Complex real_Complex imag_Complex
    dsimp only
    rw [f64Ops_neg, hgen]
    simp only [f64Ops_atan2, f64Ops_mul, f64Ops_sub, f64Ops_add, f64Ops_neg, f64Ops_one, f64Ops_asinh, f64Ops_copysign,
      real_Complex, imag_Complex]
  have h3 : (F64.eq zr zi && F64.eq zi Fl64.pzero) = false →
      acos_Complex (f64Ops tr) id (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩ =
        ⟨F64.mul Fl64.two (tr.atan2 (real_Complex (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩))) (real_Complex (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩)))),
         tr.asinh (imag_Complex (mul_Complex F64.mul F64.sub F64.add (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩))) (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩))))⟩ := by
    intro hzz0
    have ho_zz0 : ((f64Ops tr).eq zr zi && (f64Ops tr).eq zi (f64Ops tr).zero) = false := by
      rw [f64Ops_eq, f64Ops_zero]; exact hzz0
    have hgen := acos_Complex_general (f64Ops tr) (sqrt_ComplexF64_tr tr) zr zi ho_nzr ho_nzi ho_zz0 ho_inf ho_ninf ho_izr
    dsimp only at hgen
    rw [hgen]
    simp only [f64Ops_mul, f64Ops_two, f64Ops_atan2, f64Ops_sub, f64Ops_add, f64Ops_neg, f64Ops_one, f64Ops_asinh]
  have h4 :
      acosh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩ =
        ⟨tr.asinh (real_Complex (mul_Complex F64.mul F64.sub F64.add (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, zi⟩ F64.one))) (sqrt_ComplexF64_tr tr (add_Complex_Real F64.add (fun a b => (a, b)) ⟨zr, zi⟩ F64.one)))),
         F64.mul Fl64.two (tr.atan2 (imag_Complex (sqrt_ComplexF64_tr tr (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, zi⟩ F64.one))) (real_Complex (sqrt_ComplexF64_tr tr (add_Complex_Real F64.add (fun a b => (a, b)) ⟨zr, zi⟩ F64.one))))⟩ := by
    have hgen := acosh_Complex_general (f64Ops tr) (sqrt_ComplexF64_tr tr) zr zi ho_nzr ho_nzi ho_ninf ho_izr
    dsimp only at hgen
    rw [hgen]
    simp only [f64Ops_asinh, f64Ops_mul, f64Ops_sub, f64Ops_add, f64Ops_neg, f64Ops_one, f64Ops_two, f64Ops_atan2]
  have hsq_1m :
      sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, F64.neg zi⟩) =
      conj_Complex F64.neg (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨zr, zi⟩)) := by
    have hn : F64.isnan (F64.neg zi) = false := by rw [isnan_neg]; exact hnzi
    exact sqrt_ComplexF64_tr_conj tr hld hsq (F64.sub F64.one zr) (F64.neg zi) hn
  have hsq_1p :
      sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, F64.neg zi⟩) =
      conj_Complex F64.neg (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨zr, zi⟩)) :=
    sqrt_ComplexF64_tr_conj tr hld hsq (F64.add F64.one zr) zi hnzi
  have hsq_m1 :
      sqrt_ComplexF64_tr tr (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, F64.neg zi⟩ F64.one) =
      conj_Complex F64.neg (sqrt_ComplexF64_tr tr (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, zi⟩ F64.one)) :=
    sqrt_ComplexF64_tr_conj tr hld hsq (F64.sub zr F64.one) zi hnzi
  have hsq_p1 :
      sqrt_ComplexF64_tr tr (add_Complex_Real F64.add (fun a b => (a, b)) ⟨zr, F64.neg zi⟩ F64.one) =
      conj_Complex F64.neg (sqrt_ComplexF64_tr tr (add_Complex_Real F64.add (fun a b => (a, b)) ⟨zr, zi⟩ F64.one)) :=
    sqrt_ComplexF64_tr_conj tr hld hsq (F64.add F64.one zr) zi hnzi
  have hacos_re :
      (acos_Complex (f64Ops tr) id (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨zr, zi⟩)).re =
      (acos_Complex (f64Ops tr) id (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩).re := by
    by_cases hzz0 : (F64.eq zr zi && F64.eq zi Fl64.pzero) = true
    · have hzz0_c : (F64.eq zr (F64.neg zi) && F64.eq (F64.neg zi) Fl64.pzero) = true := by
        rw [eq_conj_zero_iff zr zi hnzi]; exact hzz0
      simp only [Bool.and_eq_true] at hzz0 hzz0_c
      have ha1 := acos_Complex_zero_zero (f64Ops tr) (sqrt_ComplexF64_tr tr) zr zi ho_nzr ho_nzi
        (by rw [f64Ops_eq]; exact hzz0.1) (by rw [f64Ops_eq, f64Ops_zero]; exact hzz0.2)
      have ha2 := acos_Complex_zero_zero (f64Ops tr) (sqrt_ComplexF64_tr tr) zr (F64.neg zi) ho_nzr ho_nnzi
        (by rw [f64Ops_eq]; exact hzz0_c.1) (by rw [f64Ops_eq, f64Ops_zero]; exact hzz0_c.2)
      change (acos_Complex (f64Ops tr) id (sqrt_ComplexF64_tr tr) ⟨zr, F64.neg zi⟩).re = _
      rw [ha1, ha2]
    · have hzz0_f : (F64.eq zr zi && F64.eq zi Fl64.pzero) = false := Bool.eq_false_iff.mpr hzz0
      have hzz0_cf : ((f64Ops tr).eq zr (F64.neg zi) && (f64Ops tr).eq (F64.neg zi) (f64Ops tr).zero) = false := by
        rw [f64Ops_eq, f64Ops_zero, eq_conj_zero_iff zr zi hnzi]; exact hzz0_f
      have ha2 := acos_Complex_general (f64Ops tr) (sqrt_ComplexF64_tr tr) zr (F64.neg zi)
        ho_nzr ho_nnzi hzz0_cf ho_inf ho_ninf ho_izr
      dsimp only at ha2
      change (acos_Complex (f64Ops tr) id (sqrt_ComplexF64_tr tr) ⟨zr, F64.neg zi⟩).re = _
      rw [h3 hzz0_f, ha2]
      simp only [f64Ops_mul, f64Ops_two, f64Ops_atan2, f64Ops_sub, f64Ops_add, f64Ops_neg, f64Ops_one,
        hsq_1m, hsq_1p, conj_Complex, real_Complex]
  have hacosh_conj_eq :
      acosh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨zr, zi⟩) =
        ⟨tr.asinh (real_Complex (mul_Complex F64.mul F64.sub F64.add
            (conj_Complex F64.neg (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, zi⟩ F64.one))))
            (conj_Complex F64.neg (sqrt_ComplexF64_tr tr (add_Complex_Real F64.add (fun a b => (a, b)) ⟨zr, zi⟩ F64.one))))),
         F64.neg (F64.mul Fl64.two (tr.atan2 (imag_Complex (sqrt_ComplexF64_tr tr (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, zi⟩ F64.one)))
            (real_Complex (sqrt_ComplexF64_tr tr (add_Complex_Real F64.add (fun a b => (a, b)) ⟨zr, zi⟩ F64.one)))))⟩ := by
    have hgen := acosh_Complex_general (f64Ops tr) (sqrt_ComplexF64_tr tr) zr (F64.neg zi) ho_nzr ho_nnzi ho_ninf ho_izr
    dsimp only at hgen
    change acosh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, F64.neg zi⟩ = _
    rw [hgen]
    have h_m1c :
        sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, F64.neg zi⟩ F64.one)) =
        conj_Complex F64.neg (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, zi⟩ F64.one))) := by
      change sqrt_ComplexF64_tr tr (conj_Complex F64.neg ⟨F64.sub zr F64.one, F64.neg zi⟩) =
        conj_Complex F64.neg (sqrt_ComplexF64_tr tr ⟨F64.sub zr F64.one, F64.neg zi⟩)
      exact sqrt_ComplexF64_tr_conj tr hld hsq (F64.sub zr F64.one) (F64.neg zi) (by rw [isnan_neg]; exact hnzi)
    simp only [f64Ops_asinh, f64Ops_mul, f64Ops_sub, f64Ops_add, f64Ops_neg, f64Ops_one, f64Ops_two, f64Ops_atan2]
    rw [h_m1c, hsq_p1, hsq_m1]
    dsimp only [real_Complex, imag_Complex, conj_Complex]
    rw [(hatan _ _).1, mul_neg_right_of_finite Fl64.two _ (by decide) (hatan _ _).2]
  have hacosh_im :
      (acosh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨zr, zi⟩)).im =
      F64.neg (acosh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩).im := by
    rw [hacosh_conj_eq, h4]
  have hacosh_full :
      F64.isnan (sqrt_ComplexF64_tr tr (conj_Complex F64.neg (sub_Complex_Real F64.sub (fun a b => (a, b)) ⟨zr, zi⟩ F64.one))).im = false →
      F64.isnan (sqrt_ComplexF64_tr tr (add_Complex_Real F64.add (fun a b => (a, b)) ⟨zr, zi⟩ F64.one)).im = false →
      acosh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨zr, zi⟩) =
        conj_Complex F64.neg (acosh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩) := by
    intro hu hv
    rw [hacosh_conj_eq, h4, mul_Complex_conj_re _ _ hu hv]
    rfl
  have hasin_both := hasin_laws zr zi hzr hzi
  have hasinh_both := hasin_laws (F64.neg zi) zr (by rw [isfinite_neg]; exact hzi) hzr
  dsimp only at hasin_both hasinh_both
  have hasinh_im :
      F64.isnan (sqrt_ComplexF64_tr tr (sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨F64.neg zi, zr⟩)).im = false →
      F64.isnan (sqrt_ComplexF64_tr tr (add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨F64.neg zi, zr⟩)).im = false →
      (asinh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨F64.neg zr, zi⟩).im =
        (asinh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩).im := by
    intro hu hv
    unfold asinh_Complex real_Complex imag_Complex
    dsimp only
    rw [f64Ops_neg]
    exact congrArg F64.neg (hasinh_both.1 hu hv)
  have hasinh_full :
      let oneMinusIz : ComplexF64 := sub_Real_Complex F64.sub (fun _ y => y) F64.neg F64.one ⟨F64.neg zi, zr⟩
      let onePlusIz : ComplexF64 := add_Real_Complex F64.add (fun a b => (a, b)) F64.one ⟨F64.neg zi, zr⟩
      let s1c := sqrt_ComplexF64_tr tr (conj_Complex F64.neg oneMinusIz)
      let s2 := sqrt_ComplexF64_tr tr onePlusIz
      F64.isfinite s1c.re = true → F64.isfinite s1c.im = true →
      F64.isfinite s2.re = true → F64.isfinite s2.im = true →
      F64.isfinite (F64.mul s1c.re s2.im) = true → F64.isfinite (F64.mul s1c.im s2.re) = true →
      F64.isnan (sqrt_ComplexF64_tr tr oneMinusIz).im = false →
      asinh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨F64.neg zr, zi⟩ =
        ⟨F64.neg (asinh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩).re,
         (asinh_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) ⟨zr, zi⟩).im⟩ := by
    dsimp only
    intro h1r h1i h2r h2i hp1 hp2 hu
    have hconj := hasinh_both.2 h1r h1i h2r h2i hp1 hp2 hu
    unfold asinh_Complex real_Complex imag_Complex
    dsimp only
    rw [f64Ops_neg]
    change (⟨(asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨F64.neg zi, zr⟩)).im,
             F64.neg (asin_Complex (f64Ops tr) (sqrt_ComplexF64_tr tr) (conj_Complex F64.neg ⟨F64.neg zi, zr⟩)).re⟩ : ComplexF64) = _
    rw [hconj]
    rfl
  exact ⟨h1, h2, h3, h4, hacos_re, hacosh_im, hasin_both.1, hasinh_im, hacosh_full, hasin_both.2, hasinh_full⟩

theorem trigHyperbolicIdentities_proven : TrigHyperbolicIdentities := by
  intro tr htr
  dsimp only
  intro hθ1 hθ0
  exact ⟨trig_part1 tr htr, fun _ _ => ⟨rfl, rfl⟩, trig_part3 tr htr, trig_part4 tr htr,
    trig_part5 tr, trig_part6 tr (sqrt_ComplexF64_tr tr), trig_part7 tr (sqrt_ComplexF64_tr tr),
    trig_part8 tr hθ1 hθ0, trig_part9 tr⟩
/-- Across all three `^(::Complex, ::Bool)` methods and `_cpow` (with `f64Ops tr` and `inv_ComplexF64` from `JuliaLean.base.complex`):
1. For all `z : ComplexF64` and `t : IntTy, w : Complex (JInt t)`:
   - `z ^ true = z` across all three `Bool` power methods, `pow_ComplexFloat_Bool F64.one Fl64.pzero z false = ⟨1.0, copysign(0.0, z.im)⟩` (preserving the signbit of `z.im` in `±0.0`), and `.ok (z ^ b) = z ^ Int(b)` (`power_by_squaring`).
2. For all `z : ComplexF64` and `sp, spi : Bool` (zero exponent `p = ±0.0 ± 0.0im`):
   `pow_Complex_Complex` returns `.ok ⟨1.0, flipsign(±0.0, z.im)⟩` with `signbit(r.im) = (sp != signbit(z.im))`.
3. For EVERY small integer real exponent `pr : F64` and `ip : JInt .i64` (`isinteger_F64 pr = true`, `|pr| < 2147483647`, `pr != 0`, `toInt_F64 pr = .ok ip`) and every non-real `z : ComplexF64` (`iszero(z.im) = false`):
   both `pow_Complex_Complex` at `⟨pr, ±0.0⟩` and `pow_Complex_Real_same` at `pr` delegate to `pow_ComplexF64_Int z ip` (`power_by_squaring`).
4. For EVERY positive real base `zr : F64` (`0 < zr`) and EVERY non-small-integer real exponent `pr : F64` (`!(isinteger_F64 pr && |pr| < 2147483647)`):
   `pow_Real_Complex_same` (`z isa Real`) sets `imag = (zr < 1 ? -p.im : p.im)`, whereas `pow_Complex_Complex` (`!(z isa Real)`) sets `imag = flipsign(z.im, pr)`.
5. For EVERY zero base `z = ⟨±0.0, ±0.0⟩` and EVERY non-small-integer or complex exponent `p = ⟨pr, pi⟩` (`!(iszero pi && isinteger_F64 pr && |pr| < 2147483647)`):
   `pow_Complex_Complex` returns `.ok z` (preserving both zero signs) when `0 < pr` and `.ok ⟨NaN, NaN⟩` when `!(0 < pr)`. -/
def PowBoolAndZero : Prop :=
  ∀ (tr : F64Transcendentals),
    let o := f64Ops tr
    (∀ (z : ComplexF64) (b : Bool),
      let nb := JInt.lit .i64 (if b then 1 else 0)
      pow_Complex_Bool one_ComplexF64 z true = z ∧
      pow_Complex_Bool one_ComplexF64 z false = ⟨F64.one, Fl64.pzero⟩ ∧
      pow_ComplexFloat_Bool F64.one Fl64.pzero z true = z ∧
      pow_ComplexFloat_Bool F64.one Fl64.pzero z false = ⟨F64.one, Fl64.pzero⟩ ∧
      .ok (pow_ComplexFloat_Bool F64.one Fl64.pzero z b) = pow_ComplexF64_Int z nb) ∧
    (∀ (t : IntTy) (z : Complex (JInt t)) (b : Bool),
      pow_ComplexInteger_Bool z true = z ∧
      pow_ComplexInteger_Bool z false = ⟨JInt.lit t 1, JInt.lit t 0⟩ ∧
      .ok (pow_ComplexInteger_Bool z b) =
        pow_ComplexInteger_Integer z (JInt.lit .i64 (if b then 1 else 0))) ∧
    (∀ (z : ComplexF64) (sp spi : Bool),
      ∃ r,
        pow_Complex_Complex o floatArg_F64 inv_ComplexF64 z ⟨F64.zero sp, F64.zero spi⟩ = .ok r ∧
        r.re = F64.one ∧
        F64.iszero r.im = true ∧
        F64.signbit r.im = (sp != F64.signbit z.im)) ∧
    (∀ (z : ComplexF64) (pr : F64) (spi : Bool) (ip : JInt .i64),
      F64.iszero z.im = false →
      isinteger_F64 pr = true →
      F64.lt (F64.abs pr) (F64.ofInt 2147483647) = true →
      F64.iszero pr = false →
      toInt_F64 pr = .ok ip →
      pow_Complex_Complex o floatArg_F64 inv_ComplexF64 z ⟨pr, F64.zero spi⟩ =
        pow_ComplexF64_Int z ip ∧
      pow_Complex_Real_same o floatArg_F64 inv_ComplexF64 z pr =
        pow_ComplexF64_Int z ip) ∧
    (∀ (zr pr : F64) (sz sp : Bool),
      F64.lt Fl64.pzero zr = true →
      (isinteger_F64 pr && F64.lt (F64.abs pr) (F64.ofInt 2147483647)) = false →
      pow_Real_Complex_same o (floatArg_F64_zero sz) inv_ComplexF64 zr ⟨pr, F64.zero sp⟩ =
        .ok ⟨tr.pow zr pr, if F64.lt zr F64.one then F64.neg (F64.zero sp) else F64.zero sp⟩ ∧
      pow_Complex_Complex o floatArg_F64 inv_ComplexF64 ⟨zr, F64.zero sz⟩ ⟨pr, F64.zero sp⟩ =
        .ok ⟨tr.pow zr pr, Fl64.flipsign (F64.zero sz) pr⟩) ∧
    (∀ (pr pi : F64) (szr szi : Bool),
      (F64.iszero pi && (isinteger_F64 pr && F64.lt (F64.abs pr) (F64.ofInt 2147483647))) = false →
      pow_Complex_Complex o floatArg_F64 inv_ComplexF64 ⟨F64.zero szr, F64.zero szi⟩ ⟨pr, pi⟩ =
        .ok (if F64.lt Fl64.pzero pr then ⟨F64.zero szr, F64.zero szi⟩ else ⟨F64.nan, F64.nan⟩))

theorem powBoolAndZero_proven : PowBoolAndZero := by
  intro tr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z b
    refine ⟨rfl, rfl, by cases z; rfl, rfl, ?_⟩
    cases b
    · rfl
    · cases z; rfl
  · intro t z b
    refine ⟨by cases z; rfl, rfl, ?_⟩
    cases b
    · rfl
    · cases z; rfl
  · intro z sp spi
    refine ⟨⟨F64.one, Fl64.flipsign (Fl64.copysign Fl64.pzero (F64.zero sp)) z.im⟩, ?_, rfl, ?_, ?_⟩
    · have h0 :
          isreal_Complex F64.iszero ⟨F64.zero sp, F64.zero spi⟩ = true ∧
          (isinteger_F64 (F64.zero sp) && F64.lt (F64.abs (F64.zero sp)) (F64.ofInt 2147483647)) = true ∧
          F64.iszero (F64.zero sp) = true := by
        cases sp <;> cases spi <;> decide
      unfold pow_Complex_Complex _cpow floatArg_F64 f64Ops
      simp only [real_Complex, imag_Complex, h0.1, h0.2.1, h0.2.2, ↓reduceIte, pure, Except.pure]
    · cases sp <;> by_cases hs : z.im.toNat ≥ 2^63 <;>
        simp [Fl64.flipsign, Fl64.copysign, Fl64.pzero, F64.zero, F64.signbit,
          F64.iszero, F64.neg, F64.abs, F64.toBits, F64.ofBits, hs]
    · cases sp <;> by_cases hs : z.im.toNat ≥ 2^63 <;>
        simp [Fl64.flipsign, Fl64.copysign, Fl64.pzero, F64.zero, F64.signbit,
          F64.neg, F64.abs, F64.toBits, F64.ofBits, hs]
  · intro z pr spi ip hzim hint hlt hnz hto
    have hspi : F64.iszero (F64.zero spi) = true := by cases spi <;> decide
    have hpz0 : F64.iszero Fl64.pzero = true := by decide
    unfold pow_Complex_Complex pow_Complex_Real_same _cpow floatArg_F64
      pow_ComplexF64_Int pow_ComplexFloat_Integer isreal_Complex f64Ops
    simp only [real_Complex, imag_Complex, hspi, hpz0, hint, hlt, Bool.and_self,
      hnz, hto, hzim, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, and_self]
    by_cases hip : ip.val < 0
    · have hge : ¬ (0 ≤ ip.val) := by omega
      simp [hip, hge, ops_ComplexF64]
      rfl
    · have hge : 0 ≤ ip.val := by omega
      simp [hip, hge, ops_ComplexF64]
      rfl
  · intro zr pr sz sp hzr hni
    have hsz : F64.iszero (F64.zero sz) = true := by cases sz <;> decide
    have hsp : F64.iszero (F64.zero sp) = true := by cases sp <;> decide
    have hzr0 : F64.iszero zr = false := by
      unfold F64.lt Fl64.pzero F64.zero at hzr
      unfold F64.iszero F64.abs F64.toBits F64.ofBits at hzr ⊢
      by_cases hiz : (zr.toNat % 2^63 % 2^64 == 0) = true
      · simp [hiz] at hzr
      · exact Bool.eq_false_iff.mpr hiz
    unfold pow_Real_Complex_same pow_Complex_Complex _cpow floatArg_F64 floatArg_F64_zero
      isreal_Complex f64Ops
    simp [real_Complex, imag_Complex, hsz, hsp, hni, hzr0, hzr, pure, Except.pure]
    rfl
  · intro pr pi szr szi hnp
    have hszr : F64.iszero (F64.zero szr) = true := by cases szr <;> decide
    have hszi : F64.iszero (F64.zero szi) = true := by cases szi <;> decide
    unfold pow_Complex_Complex _cpow floatArg_F64 isreal_Complex iszero_Complex f64Ops
    simp only [real_Complex, imag_Complex, hszr, hszi, Bool.and_self]
    by_cases hpi : F64.iszero pi = true
    · simp only [hpi, Bool.true_and] at hnp ⊢
      simp [hnp, pure, Except.pure]
      rfl
    · simp [hpi, pure, Except.pure]
      rfl

/-- Properties of `inv(z::Complex)`, `inv(z::Complex{T}) where T<:Union{Float16,Float32}`, `inv(w::ComplexF64)`, and `robust_cinv`:
1. For ALL `c, d : F64` with `isinf(c) || isinf(d)`, `inv_Complex_F64`, `inv_Complex_SmallFloat_F64`, and `inv_ComplexF64` return the signed zero `⟨copysign(0.0, c), flipsign(-0.0, d)⟩` with conjugate signbits `(signbit(c), !signbit(d))`.
2. For ALL non-NaN, non-infinite `c, d : F64`:
   - `inv_Complex_F64 ⟨c, d⟩ = ⟨c / (c*c + d*d), (-d) / (c*c + d*d)⟩` and `inv_Complex_F64 (conj ⟨c, d⟩) = ⟨c / (c*c + d*d), d / (c*c + d*d)⟩` (both real and imaginary parts)
   - `inv_Complex_SmallFloat_F64 ⟨c, d⟩ = ⟨c * (1 / muladd(c, c, d*d)), (-d) * (1 / muladd(c, c, d*d))⟩` and `inv_Complex_SmallFloat_F64 (conj ⟨c, d⟩) = ⟨c * (1 / muladd(c, c, d*d)), d * (1 / muladd(c, c, d*d))⟩`
   - In `inv_ComplexF64`:
     - when `sqrt(floatmin/2) <= max(|c|, |d|) <= sqrt(floatmax/2)`, `inv_ComplexF64 ⟨c, d⟩ = .ok ⟨c / den, (-d) / den⟩` and `inv_ComplexF64 (conj ⟨c, d⟩) = .ok ⟨c / den, d / den⟩` where `den = muladd(cd, cd, dc*dc)`
     - when `max(|c|, |d|) >= floatmax/2`, `inv_ComplexF64` scales `(c, d)` by `0.5` (`s = 0.5`) and dispatches to `robust_cinv`
     - when `max(|c|, |d|) <= 2*floatmin/eps` (and `< sqrt(floatmin/2)`), `inv_ComplexF64` scales `(c, d)` by `bs = 2/eps^2` and dispatches to `robust_cinv`.
3. In `robust_cinv`:
   - For ALL finite non-zero `d : F64`, calling `robust_cinv 0.0 d` directly produces `(0.0, NaN)` (because `r = d / 0.0 = ±Inf` and `-r / z = ±Inf / Inf = NaN`), which is why `inv_ComplexF64` swaps to `q, p = robust_cinv(-d, -c)` whenever `|d| > |c|`
   - For ALL non-NaN `c, d : F64` with `d = ±0.0` (`iszero d = true`) and finite non-zero `c`, `(robust_cinv c d).2` is a signed zero. -/
def InvProperties : Prop :=
  ∀ (lo hi : F64),
    F64.sqrt (F64.div F64.floatmin Fl64.two) = .ok lo →
    F64.sqrt (F64.div F64.floatmax Fl64.two) = .ok hi →
    hi.toNat < 0x7ff0000000000000 →
    F64.isnan hi = false →
    F64.iszero hi = false →
    (∀ (c d : F64), (F64.isinf c || F64.isinf d) = true →
      let w : ComplexF64 := ⟨c, d⟩
      let expected : ComplexF64 := ⟨Fl64.copysign Fl64.pzero c, Fl64.flipsign Fl64.nzero d⟩
      inv_Complex_F64 w = expected ∧
      inv_Complex_SmallFloat_F64 w = expected ∧
      inv_ComplexF64 w = .ok expected ∧
      iszero_Complex F64.iszero expected = true ∧
      F64.signbit expected.re = F64.signbit c ∧
      F64.signbit expected.im = !F64.signbit d) ∧
    (∀ (c d : F64), F64.isnan c = false → F64.isnan d = false → (F64.isinf c || F64.isinf d) = false →
      let den := F64.add (F64.mul c c) (F64.mul d d)
      let mag := F64.div F64.one (F64.muladd c c (F64.mul d d))
      inv_Complex_F64 ⟨c, d⟩ = ⟨F64.div c den, F64.div (F64.neg d) den⟩ ∧
      inv_Complex_F64 (conj_Complex F64.neg ⟨c, d⟩) = ⟨F64.div c den, F64.div d den⟩ ∧
      inv_Complex_SmallFloat_F64 ⟨c, d⟩ = ⟨F64.mul c mag, F64.mul (F64.neg d) mag⟩ ∧
      inv_Complex_SmallFloat_F64 (conj_Complex F64.neg ⟨c, d⟩) = ⟨F64.mul c mag, F64.mul d mag⟩) ∧
    (∀ (c d : F64), F64.isnan c = false → F64.isnan d = false →
      let cd := if F64.lt (F64.abs d) (F64.abs c) then F64.abs c else F64.abs d
      let dc := if F64.lt (F64.abs d) (F64.abs c) then F64.abs d else F64.abs c
      let den := F64.muladd cd cd (F64.mul dc dc)
      (F64.le lo cd && F64.le cd hi) = true →
      inv_ComplexF64 ⟨c, d⟩ = .ok ⟨F64.div c den, F64.div (F64.neg d) den⟩ ∧
      inv_ComplexF64 (conj_Complex F64.neg ⟨c, d⟩) = .ok ⟨F64.div c den, F64.div d den⟩) ∧
    (∀ (c d : F64),
      let cd := if F64.lt (F64.abs d) (F64.abs c) then F64.abs c else F64.abs d
      (F64.le lo cd && F64.le cd hi) = false →
      (F64.isinf c || F64.isinf d) = false →
      F64.le (F64.div F64.floatmax Fl64.two) cd = true →
      F64.le (F64.abs d) (F64.abs c) = true →
      let (p, q) := robust_cinv (F64.mul c Fl64.half) (F64.mul d Fl64.half)
      inv_ComplexF64 ⟨c, d⟩ = .ok ⟨F64.mul p Fl64.half, F64.mul q Fl64.half⟩) ∧
    (∀ (d : F64), F64.isfinite d = true → F64.iszero d = false →
      robust_cinv Fl64.pzero d = (Fl64.pzero, F64.ofBits 0xfff8000000000000))

theorem invProperties_proven : InvProperties := by
  intro lo hi hlo hhi hhi_val hhi_nan hhi_zero
  have hhi_sb : F64.signbit hi = false := by
    unfold F64.signbit F64.toBits
    simp only [decide_eq_false_iff_not]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c d hinf
    have h0 : F64.iszero (Fl64.copysign Fl64.pzero c) = true := by
      unfold Fl64.copysign; split <;> decide
    have h1 : F64.iszero (Fl64.flipsign Fl64.nzero d) = true := by
      unfold Fl64.flipsign; split <;> decide
    have h2 : F64.signbit (Fl64.flipsign Fl64.nzero d) = !F64.signbit d := by
      unfold Fl64.flipsign
      by_cases hs : F64.signbit d = true <;> simp [hs] <;> decide
    have hneg0 : F64.neg Fl64.pzero = Fl64.nzero := by decide
    have hcd_hi :
        ∀ cd : F64, cd.toNat < 2^63 → cd.toNat ≥ 0x7ff0000000000000 →
        (F64.le lo cd && F64.le cd hi) = false := by
      intro cd hbound hge
      have hle_false : F64.le cd hi = false := by
        unfold F64.le F64.lt F64.eq
        by_cases hnc : F64.isnan cd = true
        · simp [hnc]
        · have hzc : F64.iszero cd = false := by
            unfold F64.iszero F64.abs F64.toBits F64.ofBits
            simp only [BitVec.toNat_ofNat, beq_eq_false_iff_ne]; omega
          have hsbc : F64.signbit cd = false := by
            unfold F64.signbit F64.toBits
            simp only [decide_eq_false_iff_not]; omega
          have hlt_c : ¬ (F64.toBits cd < F64.toBits hi) := by
            unfold F64.toBits; omega
          have heq_c : (F64.toBits cd == F64.toBits hi) = false := by
            unfold F64.toBits
            rw [beq_eq_false_iff_ne]; omega
          simp [hnc, hhi_nan, hzc, hhi_zero, hsbc, hhi_sb, hlt_c, heq_c]
      simp [hle_false]
    have hge_cd :
        (if F64.lt (F64.abs d) (F64.abs c) then (F64.abs c, F64.abs d) else (F64.abs d, F64.abs c)).1.toNat < 2^63 ∧
        (if F64.lt (F64.abs d) (F64.abs c) then (F64.abs c, F64.abs d) else (F64.abs d, F64.abs c)).1.toNat ≥ 0x7ff0000000000000 := by
      have hc_bound : (F64.abs c).toNat < 2^63 := by
        simp only [F64.abs, F64.ofBits, F64.toBits, BitVec.toNat_ofNat]; omega
      have hd_bound : (F64.abs d).toNat < 2^63 := by
        simp only [F64.abs, F64.ofBits, F64.toBits, BitVec.toNat_ofNat]; omega
      refine ⟨by split <;> assumption, ?_⟩
      have hinf' : (F64.abs c).toNat = 0x7ff0000000000000 ∨ (F64.abs d).toNat = 0x7ff0000000000000 := by
        unfold F64.isinf F64.toBits at hinf
        simp only [Bool.or_eq_true, beq_iff_eq] at hinf
        exact hinf
      have hsbc : F64.signbit (F64.abs c) = false := by
        unfold F64.signbit F64.toBits; simp only [decide_eq_false_iff_not]; omega
      have hsbd : F64.signbit (F64.abs d) = false := by
        unfold F64.signbit F64.toBits; simp only [decide_eq_false_iff_not]; omega
      by_cases hlt : F64.lt (F64.abs d) (F64.abs c) = true
      · simp only [hlt, ↓reduceIte]
        rcases hinf' with hc | hd
        · omega
        · unfold F64.lt F64.toBits at hlt
          simp only [hsbc, hsbd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hlt
          split at hlt
          · contradiction
          · simp only [decide_eq_true_eq] at hlt; omega
      · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
        rcases hinf' with hc | hd
        · have hnc : F64.isnan (F64.abs c) = false := by
            unfold F64.isnan F64.exponentField F64.fraction F64.toBits
            rw [hc]; decide
          have hzc : F64.iszero (F64.abs c) = false := by
            have hc' : c.toNat % 2^63 % 2^64 = 0x7ff0000000000000 := hc
            unfold F64.iszero F64.abs F64.toBits F64.ofBits
            simp only [BitVec.toNat_ofNat, beq_eq_false_iff_ne]
            omega
          unfold F64.lt F64.toBits at hlt
          simp only [hsbc, hsbd, hnc, hzc, Bool.or_false, Bool.and_false, bne_self_eq_false,
            Bool.false_eq_true, ↓reduceIte] at hlt
          by_cases hnd : F64.isnan (F64.abs d) = true
          · unfold F64.isnan F64.exponentField F64.fraction F64.toBits at hnd
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hnd
            omega
          · simp [hnd, hc] at hlt
            omega
        · omega
    refine ⟨?_, ?_, ?_, ?_, signbit_copysign _ _, h2⟩
    · simp [inv_Complex_F64, inv_Complex, reim, real_Complex, imag_Complex, hinf, hneg0]
    · simp [inv_Complex_SmallFloat_F64, inv_Complex_SmallFloat, reim, real_Complex, imag_Complex, hinf, hneg0]
    · unfold inv_ComplexF64 reim real_Complex imag_Complex
      simp only [hlo, hhi, bind, Except.bind, pure, Except.pure, hcd_hi _ hge_cd.1 hge_cd.2,
        hinf, Bool.false_eq_true, ↓reduceIte]
    · simp [iszero_Complex, real_Complex, imag_Complex, h0, h1]
  · intro c d hc hd hni
    have hinf_neg : F64.isinf (F64.neg d) = F64.isinf d := isinf_neg d
    have hmul_neg : F64.mul (F64.neg d) (F64.neg d) = F64.mul d d := mul_neg_neg_of_not_nan d d hd hd
    simp [inv_Complex_F64, inv_Complex, inv_Complex_SmallFloat_F64, inv_Complex_SmallFloat,
      conj_Complex, reim, real_Complex, imag_Complex,
      hinf_neg, hmul_neg, hni, neg_neg_f64]
  · intro c d hc hd
    dsimp only
    intro hcd
    unfold inv_ComplexF64 conj_Complex div_Complex_Real reim real_Complex imag_Complex
    simp only [hlo, hhi, bind, Except.bind, pure, Except.pure, abs_neg_f64, neg_neg_f64]
    by_cases hlt : F64.lt (F64.abs d) (F64.abs c) = true <;>
      simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hcd ⊢ <;>
      simp [hcd]
  · intro c d
    dsimp only
    intro hcd hni hov hle
    unfold inv_ComplexF64 reim real_Complex imag_Complex
    simp only [hlo, hhi, bind, Except.bind, pure, Except.pure]
    by_cases hlt : F64.lt (F64.abs d) (F64.abs c) = true <;>
      simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hcd hov ⊢ <;>
      simp [hcd, hni, hov, hle]
  · intro d hfin hnz
    have hnan : F64.isnan d = false := by
      rw [isfinite_iff_not_nan_not_inf] at hfin
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
      exact hfin.1
    have hinf : F64.isinf d = false := by
      rw [isfinite_iff_not_nan_not_inf] at hfin
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
      exact hfin.2
    have hdiv0 : F64.div d Fl64.pzero = F64.inf (F64.signbit d) := by
      unfold F64.div
      have hn0 : F64.isnan Fl64.pzero = false := by decide
      have hi0 : F64.isinf Fl64.pzero = false := by decide
      have hz0 : F64.iszero Fl64.pzero = true := by decide
      have hs0 : F64.signbit Fl64.pzero = false := by decide
      simp [hnan, hn0, hinf, hi0, hnz, hz0, hs0]
    have hma : ∀ s : Bool, F64.muladd d (F64.inf s) Fl64.pzero = F64.inf (F64.signbit d != s) := by
      intro s
      unfold F64.muladd F64.fma
      have hn_inf : F64.isnan (F64.inf s) = false := by cases s <;> decide
      have hi_inf : F64.isinf (F64.inf s) = true := by cases s <;> decide
      have hz_inf : F64.iszero (F64.inf s) = false := by cases s <;> decide
      have hs_inf : F64.signbit (F64.inf s) = s := by cases s <;> decide
      have hn0 : F64.isnan Fl64.pzero = false := by decide
      have hi0 : F64.isinf Fl64.pzero = false := by decide
      simp [hnan, hinf, hnz, hn_inf, hi_inf, hz_inf, hs_inf, hn0, hi0]
    unfold robust_cinv
    change (let r := F64.div d Fl64.pzero; let z := F64.muladd d r Fl64.pzero; (F64.div F64.one z, F64.div (F64.neg r) z)) = _
    rw [hdiv0]
    dsimp only
    rw [hma]
    cases F64.signbit d <;> decide
/-- Division scaling and special-value laws across `div_ComplexF64`, `div_Complex_same`, `div_Complex_SmallFloat_F64`, `cdiv`, `scaling_cdiv`, and `scaleargs_cdiv`:
1. When the divisor `w` has an infinite component (`isinf(w.re) || isinf(w.im)`), `div_ComplexF64`, `div_Complex_same`, and `div_Complex_SmallFloat_F64` agree on all finite `z` and return `NaN + NaN*im` on all non-finite `z`.
2. For ALL non-NaN `a, b, c, d : F64` with non-infinite divisor `w = ⟨c, d⟩`:
   - `(div_Complex_SmallFloat_F64 ⟨a, b⟩ w).im = (div_Complex_SmallFloat_F64 ⟨b, -a⟩ w).re` (`im(z / w) = re((-i * z) / w)`)
   - `(div_Complex_SmallFloat_F64 (conj z) (conj w)).re = (div_Complex_SmallFloat_F64 z w).re`
   - `(cdiv a b c d).2 = (cdiv b (-a) c d).1` (`im(z / w) = re((-i * z) / w)` across both branches of `cdiv`).
3. In `scaleargs_cdiv` and `scaling_cdiv` across all scaling regimes (for all `a, b, c, d, ab, cd : F64`):
   - Normal dividend & normal divisor: `(a, b, c, d, 1.0)`
   - Overflow dividend & normal divisor: `(0.5*a, 0.5*b, c, d, 2.0)`
   - Normal dividend & overflow divisor: `(a, b, 0.5*c, 0.5*d, 0.5)`
   - Both overflow (`ab >= halfov, cd >= halfov`): `(0.5*a, 0.5*b, 0.5*c, 0.5*d, 1.0)` (scale factors cancel). -/
def DivScalingAndInf : Prop :=
  let halfov := F64.mul Fl64.half F64.floatmax
  let twounEps := F64.div (F64.mul F64.floatmin Fl64.two) Fl64.eps
  (∀ (z w : ComplexF64), (F64.isinf w.re || F64.isinf w.im) = true →
    let q64 := div_ComplexF64 z w
    let qsame := div_Complex_same F64.isinf F64.isfinite Fl64.pzero F64.neg F64.nan Fl64.sign F64.abs F64.le
      F64.div F64.mul F64.mul F64.add F64.add F64.sub F64.sub F64.div F64.mul z w
    let qsmall := div_Complex_SmallFloat_F64 z w
    (isfinite_Complex F64.isfinite z = true → q64 = qsame ∧ qsmall = qsame) ∧
    (isfinite_Complex F64.isfinite z = false →
      isnan_Complex F64.isnan q64 = true ∧
      isnan_Complex F64.isnan qsame = true ∧
      isnan_Complex F64.isnan qsmall = true)) ∧
  (∀ (a b c d : F64),
    (robust_cdiv1 a b c d).2 = (robust_cdiv1 b (F64.neg a) c d).1 ∧
    (F64.le (F64.abs d) (F64.abs c) = true →
      (cdiv a b c d).2 = (cdiv b (F64.neg a) c d).1) ∧
    (F64.le (F64.abs d) (F64.abs c) = false → F64.le (F64.abs c) (F64.abs d) = true →
      cdiv a b c d = ((cdiv b a d c).1, F64.neg (cdiv b a d c).2)) ∧
    ((F64.isinf c || F64.isinf d) = false →
      (div_Complex_SmallFloat_F64 ⟨a, b⟩ ⟨c, d⟩).im =
        (div_Complex_SmallFloat_F64 ⟨b, F64.neg a⟩ ⟨c, d⟩).re) ∧
    (F64.isnan b = false → F64.isnan d = false →
      (F64.isinf c || F64.isinf d) = false →
      (div_Complex_SmallFloat_F64 (conj_Complex F64.neg ⟨a, b⟩) (conj_Complex F64.neg ⟨c, d⟩)).re =
        (div_Complex_SmallFloat_F64 ⟨a, b⟩ ⟨c, d⟩).re)) ∧
  (∀ (a b c d ab cd : F64),
    (F64.le halfov ab = false → F64.le ab twounEps = false →
     F64.le halfov cd = false → F64.le cd twounEps = false →
      scaleargs_cdiv a b c d ab cd = (a, b, c, d, F64.one)) ∧
    (F64.le halfov ab = true → F64.le ab twounEps = false →
     F64.le halfov cd = false → F64.le cd twounEps = false →
      scaleargs_cdiv a b c d ab cd = (F64.mul a Fl64.half, F64.mul b Fl64.half, c, d, Fl64.two)) ∧
    (F64.le halfov ab = false → F64.le ab twounEps = false →
     F64.le halfov cd = true → F64.le cd twounEps = false →
      scaleargs_cdiv a b c d ab cd = (a, b, F64.mul c Fl64.half, F64.mul d Fl64.half, Fl64.half)) ∧
    (F64.le halfov ab = true → F64.le ab twounEps = false →
     F64.le halfov cd = true → F64.le cd twounEps = false →
      scaleargs_cdiv a b c d ab cd =
        (F64.mul a Fl64.half, F64.mul b Fl64.half, F64.mul c Fl64.half, F64.mul d Fl64.half, F64.one)))

theorem divScalingAndInf_proven : DivScalingAndInf := by
  refine ⟨?_, ?_, ?_⟩
  · intro z w hinf
    have hneg0 : F64.neg Fl64.pzero = Fl64.nzero := by decide
    constructor
    · intro hfin
      simp [div_ComplexF64, div_Complex_same, div_Complex_SmallFloat_F64, div_Complex_SmallFloat, reim,
        real_Complex, imag_Complex, hinf, hfin, hneg0]
    · intro hnf
      simp [div_ComplexF64, div_Complex_same, div_Complex_SmallFloat_F64, div_Complex_SmallFloat, reim,
        real_Complex, imag_Complex, hinf, hnf, isnan_Complex]
      decide
  · intro a b c d
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro hle
      unfold cdiv
      simp [hle, robust_cdiv1]
    · intro h1 h2
      unfold cdiv
      simp [h1, h2]
    · intro hni
      simp [div_Complex_SmallFloat_F64, div_Complex_SmallFloat, reim, real_Complex, imag_Complex, hni]
    · intro hb hd hni
      have hinf_neg : F64.isinf (F64.neg d) = F64.isinf d := isinf_neg d
      have hdd : F64.mul (F64.neg d) (F64.neg d) = F64.mul d d := mul_neg_neg_of_not_nan d d hd hd
      have hbd : F64.mul (F64.neg b) (F64.neg d) = F64.mul b d := mul_neg_neg_of_not_nan b d hb hd
      simp [div_Complex_SmallFloat_F64, div_Complex_SmallFloat, conj_Complex, reim, real_Complex, imag_Complex,
        hinf_neg, hni, hdd, hbd]
  · intro a b c d ab cd
    have hs1 : F64.mul F64.one Fl64.two = Fl64.two := by decide
    have hs2 : F64.mul F64.one Fl64.half = Fl64.half := by decide
    have hs3 : F64.mul (F64.mul F64.one Fl64.two) Fl64.half = F64.one := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h1 h2 h3 h4
      unfold scaleargs_cdiv; simp [h1, h2, h3, h4]
    · intro h1 _ h3 h4
      unfold scaleargs_cdiv; simp [h1, h3, h4, hs1]
    · intro h1 h2 h3 _
      unfold scaleargs_cdiv; simp [h1, h2, h3, hs2]
    · intro h1 _ h3 _
      unfold scaleargs_cdiv; simp [h1, h3, hs3]

/-- Exponential and logarithmic laws across `angle`, `log`, `log10`, `log2`, `exp`, `expm1`, `log1p`, `exp2`, and `exp10` (using `f64Ops tr` and the real `ssqs_F64_tr tr` from `JuliaLean.base.complex`):
1. For all `tr : F64Transcendentals` with odd `sin`, even `cos`, `ldexp(-y, k) = -ldexp(y, k)`, and `atan2(-y, x) = -atan2(y, x)`:
   - For all non-NaN `zr, zi : F64`, `(exp_Complex(conj z)).re = (exp_Complex z).re` and `(expm1_Complex(conj z)).re = (expm1_Complex z).re` across BOTH the half-angle `erm1 - 2*er*sin(0.5*zi)^2` branch and the `er * sincos(zi)` branch, and `(exp2_Complex(conj z)).re = (exp2_Complex z).re` and `(exp10_Complex(conj z)).re = (exp10_Complex z).re` on the real axis `zi = +0.0`
   - On the real axis `⟨zr, ±0.0⟩`, `exp_Complex` and `expm1_Complex` preserve the exact signed zero `±0.0` in `imag`
   - For `zr = -Inf` and any non-finite `zi`, `exp(-Inf + zi*im) = -0.0 + copysign(0.0, zi)*im` and `expm1(-Inf + zi*im) = -1.0 + copysign(0.0, zi)*im`, while for `zr = +Inf` and non-finite `zi`, `exp` and `expm1` return `-Inf + NaN*im`.
2. In `angle_Complex`, `log_Complex`, `log10_Complex`, and `log2_Complex` (instantiated with the real `ssqs_F64_tr tr`):
   - For all non-NaN `z : ComplexF64`:
     - `angle_Complex (conj z) = -angle_Complex z`
     - `log_Complex (conj z) = conj (log_Complex z)` (both real AND imaginary parts!)
     - `(log_Complex (-z)).re = (log_Complex z).re`
     - `(log10_Complex (conj z)).re = (log10_Complex z).re` and `(log10_Complex (-z)).re = (log10_Complex z).re`
     - `(log2_Complex (conj z)).re = (log2_Complex z).re` and `(log2_Complex (-z)).re = (log2_Complex z).re`.
3. In `log1p_Complex` (instantiated with the real `ssqs_F64_tr tr`):
   - All 4 signed zeros `(±0.0, ±0.0)` are fixed points via Kahan's `1 + z == 1` branch
   - For all non-NaN `zr, zi : F64` with `isfinite zr && isinf zi`, `log1p_Complex (conj z) = conj (log1p_Complex z)`
   - For all finite `zi : F64`, `log1p(+Inf + zi*im) = +Inf + copysign(0.0, zi)*im` and `log1p(-Inf + zi*im) = +Inf + copysign(pi, zi)*im`, and for non-finite `zi`, `log1p(±Inf + zi*im) = +Inf + NaN*im`. -/
def ExpLogSpecialValues : Prop :=
  ∀ (tr : F64Transcendentals),
    (∀ x y : F64, F64.isnan x = false → F64.isnan y = false →
      tr.sincos (F64.neg x) = (F64.neg (tr.sincos x).1, (tr.sincos x).2) ∧
      (tr.sincos (F64.mul Fl64.half (F64.neg x))).1 = F64.neg (tr.sincos (F64.mul Fl64.half x)).1 ∧
      F64.isnan (tr.sincos (F64.mul Fl64.half x)).1 = false ∧
      tr.atan2 (F64.neg y) x = F64.neg (tr.atan2 y x) ∧
      (∀ k, tr.ldexp (F64.neg y) k = F64.neg (tr.ldexp y k) ∧ F64.isnan (tr.ldexp y k) = false)) →
    let o := f64Ops tr
    let sqs := ssqs_F64_tr tr
    (∀ (zr zi : F64), F64.isnan zr = false → F64.isnan zi = false →
      (exp_Complex o (conj_Complex F64.neg ⟨zr, zi⟩)).re = (exp_Complex o ⟨zr, zi⟩).re ∧
      (expm1_Complex o (conj_Complex F64.neg ⟨zr, zi⟩)).re = (expm1_Complex o ⟨zr, zi⟩).re) ∧
    (∀ (zr : F64) (s : Bool), F64.isnan zr = false →
      exp_Complex o ⟨zr, F64.zero s⟩ = ⟨tr.exp zr, F64.zero s⟩ ∧
      expm1_Complex o ⟨zr, F64.zero s⟩ = ⟨tr.expm1 zr, F64.zero s⟩) ∧
    (∀ (zr zi : F64),
      let theta2 := F64.mul zi (tr.log (F64.ofInt 2))
      let theta10 := F64.mul zi (tr.log (F64.ofInt 10))
      exp2_Complex o id ⟨zr, zi⟩ =
        mul_Real_Complex F64.mul (tr.exp2 zr) (cis_Real tr.sincos theta2) ∧
      exp10_Complex o id ⟨zr, zi⟩ =
        mul_Real_Complex F64.mul (tr.exp10 zr) (cis_Real tr.sincos theta10) ∧
      (F64.isfinite zi = true →
       F64.isfinite (tr.log (F64.ofInt 2)) = true →
       F64.isnan theta2 = false →
        (exp2_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (exp2_Complex o id ⟨zr, zi⟩).re ∧
        (F64.isfinite (tr.exp2 zr) = true → F64.isfinite (tr.sincos theta2).1 = true →
          exp2_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩) =
            conj_Complex F64.neg (exp2_Complex o id ⟨zr, zi⟩))) ∧
      (F64.isfinite zi = true →
       F64.isfinite (tr.log (F64.ofInt 10)) = true →
       F64.isnan theta10 = false →
        (exp10_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩)).re = (exp10_Complex o id ⟨zr, zi⟩).re ∧
        (F64.isfinite (tr.exp10 zr) = true → F64.isfinite (tr.sincos theta10).1 = true →
          exp10_Complex o id (conj_Complex F64.neg ⟨zr, zi⟩) =
            conj_Complex F64.neg (exp10_Complex o id ⟨zr, zi⟩)))) ∧
    (∀ zi : F64, F64.isfinite zi = false →
      exp_Complex o ⟨Fl64.ninf, zi⟩ = ⟨Fl64.nzero, Fl64.copysign Fl64.pzero zi⟩ ∧
      expm1_Complex o ⟨Fl64.ninf, zi⟩ = ⟨F64.neg F64.one, Fl64.copysign Fl64.pzero zi⟩ ∧
      exp_Complex o ⟨Fl64.inf, zi⟩ = ⟨Fl64.ninf, F64.nan⟩ ∧
      expm1_Complex o ⟨Fl64.inf, zi⟩ = ⟨Fl64.ninf, F64.nan⟩) ∧
    (∀ (z : ComplexF64), F64.isnan z.re = false → F64.isnan z.im = false →
      imag_Complex (log_Complex o id sqs z) = angle_Complex o.atan2 z ∧
      angle_Complex o.atan2 (conj_Complex F64.neg z) = F64.neg (angle_Complex o.atan2 z) ∧
      log_Complex o id sqs (conj_Complex F64.neg z) = conj_Complex F64.neg (log_Complex o id sqs z) ∧
      real_Complex (log_Complex o id sqs (neg_Complex F64.neg z)) = real_Complex (log_Complex o id sqs z) ∧
      real_Complex (log10_Complex o id sqs (conj_Complex F64.neg z)) = real_Complex (log10_Complex o id sqs z) ∧
      real_Complex (log10_Complex o id sqs (neg_Complex F64.neg z)) = real_Complex (log10_Complex o id sqs z) ∧
      real_Complex (log2_Complex o id sqs (conj_Complex F64.neg z)) = real_Complex (log2_Complex o id sqs z) ∧
      real_Complex (log2_Complex o id sqs (neg_Complex F64.neg z)) = real_Complex (log2_Complex o id sqs z)) ∧
    (∀ (zr : F64) (si : Bool), F64.isfinite zr = true → F64.eq (F64.add F64.one zr) F64.one = true →
      log1p_Complex o sqs ⟨zr, F64.zero si⟩ = ⟨zr, F64.zero si⟩) ∧
    (∀ (zr zi : F64), F64.isfinite zr = true → F64.isinf zi = true →
      log1p_Complex o sqs (conj_Complex F64.neg ⟨zr, zi⟩) =
        conj_Complex F64.neg (log1p_Complex o sqs ⟨zr, zi⟩)) ∧
    (∀ zi : F64,
      (F64.isfinite zi = true →
        log1p_Complex o sqs ⟨Fl64.inf, zi⟩ = ⟨Fl64.inf, Fl64.copysign Fl64.pzero zi⟩ ∧
        log1p_Complex o sqs ⟨Fl64.ninf, zi⟩ = ⟨Fl64.inf, Fl64.copysign Fl64.pi zi⟩) ∧
      (F64.isfinite zi = false →
        log1p_Complex o sqs ⟨Fl64.inf, zi⟩ = ⟨Fl64.inf, F64.nan⟩ ∧
        log1p_Complex o sqs ⟨Fl64.ninf, zi⟩ = ⟨Fl64.inf, F64.nan⟩))

theorem expLogSpecialValues_proven : ExpLogSpecialValues := by
  intro tr htr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro zr zi hzr hzi
    have hsc := (htr zi zr hzi hzr).1
    have hsh := (htr zi zr hzi hzr).2.1
    have hsh_nan := (htr zi zr hzi hzr).2.2.1
    have hsh_sq :
        F64.mul (F64.neg (tr.sincos (F64.mul Fl64.half zi)).1) (F64.neg (tr.sincos (F64.mul Fl64.half zi)).1) =
        F64.mul (tr.sincos (F64.mul Fl64.half zi)).1 (tr.sincos (F64.mul Fl64.half zi)).1 :=
      mul_neg_neg_of_not_nan _ _ hsh_nan hsh_nan
    constructor
    · unfold exp_Complex conj_Complex f64Ops reim real_Complex imag_Complex
      simp only [hzr, isfinite_neg, iszero_neg, hsc, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : F64.isfinite zi = true
      · by_cases h2 : F64.iszero zi = true <;> simp [h1, h2]
      · by_cases h2 : F64.eq zr Fl64.inf = true
        · simp [h1, h2]
        · by_cases h3 : F64.eq zr Fl64.ninf = true <;> simp [h1, h2, h3]
    · unfold expm1_Complex conj_Complex f64Ops reim real_Complex imag_Complex
      simp only [hzr, isfinite_neg, eq_zero_neg, hsc, hsh, hsh_sq, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : F64.isfinite zi = true
      · by_cases h2 : F64.eq zi Fl64.pzero = true
        · simp [h1, h2]
        · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          split <;> rfl
      · by_cases h2 : F64.eq zr Fl64.inf = true
        · simp [h1, h2]
        · by_cases h3 : F64.eq zr Fl64.ninf = true <;> simp [h1, h2, h3]
  · intro zr s hnan
    have hfin0 : F64.isfinite (F64.zero s) = true := by cases s <;> decide
    have hz0 : F64.iszero (F64.zero s) = true := by cases s <;> decide
    have heq0 : F64.eq (F64.zero s) Fl64.pzero = true := by cases s <;> decide
    unfold exp_Complex expm1_Complex f64Ops reim real_Complex imag_Complex
    simp [hnan, hfin0, hz0, heq0]
  · intro zr zi
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro hzi hlog2 hth2
      have hsc := (htr (F64.mul zi (tr.log (F64.ofInt 2))) Fl64.pzero hth2 (by decide)).1
      have hmul_neg := mul_neg_left_of_finite zi (tr.log (F64.ofInt 2)) hzi hlog2
      unfold exp2_Complex conj_Complex real_Complex imag_Complex id
      simp only [f64Ops_exp2, f64Ops_mul, f64Ops_log, f64Ops_ofInt, f64Ops_sincos, hmul_neg, hsc]
      refine ⟨trivial, ?_⟩
      intro hexp2 hs2
      simp only [mul_neg_right_of_finite (tr.exp2 zr) _ hexp2 hs2]
    · intro hzi hlog10 hth10
      have hsc := (htr (F64.mul zi (tr.log (F64.ofInt 10))) Fl64.pzero hth10 (by decide)).1
      have hmul_neg := mul_neg_left_of_finite zi (tr.log (F64.ofInt 10)) hzi hlog10
      unfold exp10_Complex conj_Complex real_Complex imag_Complex id
      simp only [f64Ops_exp10, f64Ops_mul, f64Ops_log, f64Ops_ofInt, f64Ops_sincos, hmul_neg, hsc]
      refine ⟨trivial, ?_⟩
      intro hexp10 hs10
      simp only [mul_neg_right_of_finite (tr.exp10 zr) _ hexp10 hs10]
  · intro zi hnf
    have h1 : F64.isnan Fl64.ninf = false := by decide
    have h2 : F64.eq Fl64.ninf Fl64.inf = false := by decide
    have h3 : F64.eq Fl64.ninf Fl64.ninf = true := by decide
    have h4 : F64.neg Fl64.pzero = Fl64.nzero := by decide
    have h5 : F64.isnan Fl64.inf = false := by decide
    have h6 : F64.eq Fl64.inf Fl64.inf = true := by decide
    have h7 : F64.neg Fl64.inf = Fl64.ninf := by decide
    unfold exp_Complex expm1_Complex f64Ops reim real_Complex imag_Complex
    simp [h1, hnf, h2, h3, h4, h5, h6, h7]
  · intro z hzr hzi
    have hld : ∀ v k, F64.isnan v = false →
        tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false := by
      intro v k hv
      exact (htr v v hv hv).2.2.2.2 k
    have hss := ssqs_F64_tr_symm tr hld z.re z.im hzr hzi
    have hatan := (htr z.re z.im hzr hzi).2.2.2.1
    unfold log10_Complex log2_Complex log_Complex div_Complex_Real angle_Complex
      conj_Complex neg_Complex f64Ops reim real_Complex imag_Complex
    simp only [id_eq, abs_neg_f64, hatan]
    change True ∧ True ∧
      ({ re := (let (ρ, k) := ssqs_F64_tr tr z.re (F64.neg z.im); _), im := F64.neg (tr.atan2 z.im z.re) } : ComplexF64) = _ ∧
      (let (ρ, k) := ssqs_F64_tr tr (F64.neg z.re) (F64.neg z.im); _) = (let (ρ, k) := ssqs_F64_tr tr z.re z.im; _) ∧
      F64.div (let (ρ, k) := ssqs_F64_tr tr z.re (F64.neg z.im); _) _ = _ ∧
      F64.div (let (ρ, k) := ssqs_F64_tr tr (F64.neg z.re) (F64.neg z.im); _) _ = _ ∧
      F64.div (let (ρ, k) := ssqs_F64_tr tr z.re (F64.neg z.im); _) _ = _ ∧
      F64.div (let (ρ, k) := ssqs_F64_tr tr (F64.neg z.re) (F64.neg z.im); _) _ = _
    rw [hss.1, hss.2]
    exact ⟨trivial, trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro zr si hfin heq1
    have hinf : F64.isinf (F64.zero si) = false := by cases si <;> decide
    have hz0 : F64.iszero (F64.zero si) = true := by cases si <;> decide
    unfold log1p_Complex eq_Complex_Real isreal_Complex reim real_Complex imag_Complex
    simp [hfin, hinf, hz0, heq1]
  · intro zr zi hfin hinf
    have hzr : F64.isnan zr = false := by
      rw [isfinite_iff_not_nan_not_inf] at hfin
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
      exact hfin.1
    have hzi : F64.isnan zi = false := by
      unfold F64.isinf F64.abs F64.toBits F64.ofBits at hinf
      unfold F64.isnan F64.exponentField F64.fraction F64.toBits
      simp only [BitVec.toNat_ofNat, beq_iff_eq] at hinf ⊢
      have : zi.toNat % 2^52 = 0 := by omega
      simp [this]
    have hld : ∀ v k, F64.isnan v = false →
        tr.ldexp (F64.neg v) k = F64.neg (tr.ldexp v k) ∧ F64.isnan (tr.ldexp v k) = false := by
      intro v k hv
      exact (htr v v hv hv).2.2.2.2 k
    have hss := (ssqs_F64_tr_symm tr hld zr zi hzr hzi).1
    have hatan := (htr zr zi hzr hzi).2.2.2.1
    have hinf_neg : F64.isinf (F64.neg zi) = true := by rw [isinf_neg, hinf]
    unfold log1p_Complex log_Complex angle_Complex conj_Complex f64Ops reim real_Complex imag_Complex
    simp only [hfin, hinf, hinf_neg, ↓reduceIte, id_eq, abs_neg_f64, hatan]
    change ({ re := (let (ρ, k) := ssqs_F64_tr tr zr (F64.neg zi); _), im := _ } : ComplexF64) = _
    rw [hss]
  · intro zi
    have h1 : F64.isfinite Fl64.inf = false := by decide
    have h2 : F64.isnan Fl64.inf = false := by decide
    have h3 : F64.lt Fl64.pzero Fl64.inf = true := by decide
    have h4 : F64.isfinite Fl64.ninf = false := by decide
    have h5 : F64.isnan Fl64.ninf = false := by decide
    have h6 : F64.lt Fl64.pzero Fl64.ninf = false := by decide
    constructor
    · intro hfin
      unfold log1p_Complex f64Ops reim real_Complex imag_Complex
      simp [h1, h2, h3, h4, h5, h6, hfin]
    · intro hnf
      unfold log1p_Complex f64Ops reim real_Complex imag_Complex
      simp [h1, h2, h4, h5, hnf]

/-- `3.5` and `4.5` in binary64 (`base/complex.jl:1110-1115` docstring examples). -/
def f3_5 : F64 := F64.ofBits 0x400c000000000000
def f4_5 : F64 := F64.ofBits 0x4012000000000000
def f5_0 : F64 := F64.ofInt 5

/-- Properties of `round`, `float`, `big`, `complex(::AbstractArray)`, and `eps`:
1. For ALL `z : ComplexF64`, `rr, ri : Rounding`, `kw : Unit`, and any scalar `roundElem : F64 → Rounding → Unit → F64` satisfying the documented scalar rounding symmetries (`round(-x, Up) = -round(x, Down)`, `round(-x, Nearest) = -round(x, Nearest)`, `round(-x, ToZero) = -round(x, ToZero)`, and idempotence `round(round(x, m), m) = round(x, m)`):
   - `round_Complex roundElem z rr rr kw = round_Complex roundElem z rr (kw := kw)` (default `ri = rr` agreement)
   - `round_Complex roundElem (round_Complex roundElem z rr ri kw) rr ri kw = round_Complex roundElem z rr ri kw` (idempotence on all `z`)
   - `round_Complex roundElem (-z) .RoundUp .RoundDown kw = -round_Complex roundElem z .RoundDown .RoundUp kw` (negation swaps `RoundUp` and `RoundDown` on all `z`)
   - `round_Complex roundElem (conj z) .RoundNearest .RoundUp kw = conj (round_Complex roundElem z .RoundNearest .RoundDown kw)` (conjugation swaps `ri = RoundUp` and `ri = RoundDown` on all `z`)
   - `round_Complex roundElem (-z) .RoundToZero .RoundNearest kw = -round_Complex roundElem z .RoundToZero .RoundNearest kw`
   - With concrete `round_F64` (`F64.round`), `round_Complex` preserves all 4 signed-zero combinations `(±0.0, ±0.0)` and all 4 infinite combinations `(±Inf, ±Inf)` under every pair `(rr, ri : Rounding)`, rounds `3.5 + 4.5im` under `(RoundNearest, RoundNearest)` to `4.0 + 4.0im` and under `(RoundUp, RoundNearestTiesAway)` to `4.0 + 5.0im`, and satisfies `round(-z, RoundUp, RoundDown) = -round(z, RoundDown, RoundUp)`.
2. For ALL `t : IntTy`, `z : Complex (JInt t)`, and `A : List (JInt t)`:
   - `float_Complex_AbstractFloat z = z`, `float_Complex F64.ofJInt z = ⟨F64.ofJInt z.re, F64.ofJInt z.im⟩`, `big_Complex (widen_JInt .i128) z = ⟨JInt.lit .i128 z.re.val, JInt.lit .i128 z.im.val⟩`, and `big_Type_Complex widen_IntTy t = .complex (widen_IntTy t)`
   - `complex_AbstractArray` rejects non-concrete element types with `ArgumentError`, and on concrete element types preserves array length, maps `real_Complex` to `.ok A`, and maps `imag_Complex` to zeros.
3. For ALL `z = ⟨x, y⟩ : ComplexF64` and any scalar `epsF : F64 → F64` satisfying `epsF(-x) = epsF(x)`, `epsF(|x|) = epsF(x)`, and `(!isfinite x → epsF x = NaN)`, with concrete `Fl64.hypot`:
   - `eps_Complex epsF Fl64.hypot (conj z) = eps_Complex epsF Fl64.hypot z`
   - `eps_Complex epsF Fl64.hypot (-z) = eps_Complex epsF Fl64.hypot z`
   - `eps_Complex epsF Fl64.hypot ⟨|z.re|, |z.im|⟩ = eps_Complex epsF Fl64.hypot z`
   - `isfinite_Complex F64.isfinite z = false → eps_Complex epsF Fl64.hypot z = .ok F64.nan`
   - With concrete `epsOf_F64` (`F64.eps`) and `Fl64.hypot`, `eps_Complex epsOf_F64 Fl64.hypot ⟨a, b⟩ = eps_Complex epsOf_F64 Fl64.hypot ⟨b, a⟩` whenever `epsOf_F64 a = epsOf_F64 b`, equals `eps_Type_Complex` (`sqrt(2.0) * eps(Float64)`) at `(±1.0, ±1.0)`, and equals `.ok F64.eps` at `(±1.0, ±0.0)` and `(±0.0, ±1.0)`. -/
def RoundArrayEps : Prop :=
  (∀ (roundElem : F64 → Rounding → Unit → F64),
    (∀ x m, roundElem (roundElem x m ()) m () = roundElem x m ()) →
    (∀ x, roundElem (F64.neg x) .RoundUp () = F64.neg (roundElem x .RoundDown ()) ∧
          roundElem (F64.neg x) .RoundDown () = F64.neg (roundElem x .RoundUp ()) ∧
          roundElem (F64.neg x) .RoundNearest () = F64.neg (roundElem x .RoundNearest ()) ∧
          roundElem (F64.neg x) .RoundToZero () = F64.neg (roundElem x .RoundToZero ())) →
    ∀ (z : ComplexF64) (rr ri : Rounding),
      round_Complex roundElem z rr rr () = round_Complex roundElem z rr (kw := ()) ∧
      round_Complex roundElem (round_Complex roundElem z rr ri ()) rr ri () =
        round_Complex roundElem z rr ri () ∧
      round_Complex roundElem (neg_Complex F64.neg z) .RoundUp .RoundDown () =
        neg_Complex F64.neg (round_Complex roundElem z .RoundDown .RoundUp ()) ∧
      round_Complex roundElem (conj_Complex F64.neg z) .RoundNearest .RoundUp () =
        conj_Complex F64.neg (round_Complex roundElem z .RoundNearest .RoundDown ()) ∧
      round_Complex roundElem (neg_Complex F64.neg z) .RoundToZero .RoundNearest () =
        neg_Complex F64.neg (round_Complex roundElem z .RoundToZero .RoundNearest ())) ∧
  (∀ (sr si : Bool) (rr ri : Rounding),
    let u1 := if sr then F64.neg F64.one else F64.one
    let u2 := if si then F64.neg Fl64.two else Fl64.two
    round_Complex round_F64 ⟨u1, u2⟩ rr ri () = ⟨u1, u2⟩ ∧
    round_Complex round_F64 ⟨F64.inf sr, F64.inf si⟩ rr ri () = ⟨F64.inf sr, F64.inf si⟩) ∧
  round_Complex round_F64 ⟨f3_5, f4_5⟩ .RoundNearest .RoundNearest () = ⟨f4, f4⟩ ∧
  round_Complex round_F64 ⟨f3_5, f4_5⟩ .RoundUp .RoundNearestTiesAway () = ⟨f4, f5_0⟩ ∧
  round_Complex round_F64 (neg_Complex F64.neg ⟨f3_5, f4_5⟩) .RoundUp .RoundDown () =
    neg_Complex F64.neg (round_Complex round_F64 ⟨f3_5, f4_5⟩ .RoundDown .RoundUp ()) ∧
  (∀ (t : IntTy) (z : Complex (JInt t)) (A : List (JInt t)),
    float_Complex_AbstractFloat z = z ∧
    float_Complex F64.ofJInt z = ⟨F64.ofJInt z.re, F64.ofJInt z.im⟩ ∧
    big_Complex (widen_JInt .i128) z = ⟨JInt.lit .i128 z.re.val, JInt.lit .i128 z.im.val⟩ ∧
    big_Type_Complex widen_IntTy t = .complex (widen_IntTy t) ∧
    complex_AbstractArray_Complex (complex_List_JInt t A) = complex_List_JInt t A ∧
    complex_AbstractArray false (complex_List_JInt t) A =
      .error (.argumentError "`complex` not defined on abstractly-typed arrays; please convert to a more specific type") ∧
    (complex_AbstractArray true (complex_List_JInt t) A).map (List.map real_Complex) = .ok A ∧
    (complex_List_JInt t A).length = A.length) ∧
  (∀ (epsF : F64 → F64) (hypotF : F64 → F64 → F64),
    (∀ x y, hypotF y x = hypotF x y ∧ hypotF F64.nan y = F64.nan ∧ hypotF x F64.nan = F64.nan) →
    (∀ x, epsF (F64.neg x) = epsF x ∧ epsF (F64.abs x) = epsF x ∧ (F64.isfinite x = false → epsF x = F64.nan)) →
    ∀ (z : ComplexF64),
      eps_Complex epsF hypotF (conj_Complex F64.neg z) = eps_Complex epsF hypotF z ∧
      eps_Complex epsF hypotF (neg_Complex F64.neg z) = eps_Complex epsF hypotF z ∧
      eps_Complex epsF hypotF ⟨F64.abs z.re, F64.abs z.im⟩ = eps_Complex epsF hypotF z ∧
      eps_Complex epsF hypotF ⟨z.im, z.re⟩ = eps_Complex epsF hypotF z ∧
      (isfinite_Complex F64.isfinite z = false → eps_Complex epsF hypotF z = F64.nan)) ∧
  (∀ (a b : F64), epsOf_F64 a = epsOf_F64 b →
    eps_Complex epsOf_F64 Fl64.hypot ⟨a, b⟩ = eps_Complex epsOf_F64 Fl64.hypot ⟨b, a⟩) ∧
  (∀ (sr si : Bool) (hypotF : F64 → F64 → F64) (sqrtF : F64 → F64),
    hypotF F64.eps F64.eps = F64.mul (sqrtF (F64.mul Fl64.two F64.one)) F64.eps →
    let u1 := if sr then F64.neg F64.one else F64.one
    let u2 := if si then F64.neg F64.one else F64.one
    let t2 := if si then F64.neg Fl64.two else Fl64.two
    eps_Complex epsOf_F64 hypotF ⟨u1, u2⟩ =
      eps_Type_Complex (F64.mul Fl64.two F64.one) F64.eps sqrtF F64.mul ∧
    eps_Complex epsOf_F64 hypotF ⟨u1, t2⟩ = hypotF F64.eps (F64.ofBits 0x3cc0000000000000) ∧
    eps_Complex epsOf_F64 hypotF ⟨t2, u1⟩ = hypotF (F64.ofBits 0x3cc0000000000000) F64.eps ∧
    F64.isnan (epsOf_F64 (F64.inf sr)) = true)

theorem map_real_complex_Real {t : IntTy} (A : List (JInt t)) :
    (complex_List_JInt t A).map real_Complex = A := by
  unfold complex_List_JInt
  induction A with
  | nil => rfl
  | cons x xs ih => simp [complex_Real, Complex_Real, real_Complex, ih]

theorem roundArrayEps_proven : RoundArrayEps := by
  refine ⟨?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro roundElem hidem hneg z rr ri
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · simp [round_Complex, real_Complex, imag_Complex, hidem]
    · simp [round_Complex, neg_Complex, real_Complex, imag_Complex,
        (hneg z.re).1, (hneg z.im).2.1]
    · simp [round_Complex, conj_Complex, real_Complex, imag_Complex,
        (hneg z.im).1]
    · simp [round_Complex, neg_Complex, real_Complex, imag_Complex,
        (hneg z.re).2.2.2, (hneg z.im).2.2.1]
  · intro sr si rr ri
    cases sr <;> cases si <;> cases rr <;> cases ri <;> decide
  · intro t z A
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, List.length_map _⟩
    simp [complex_AbstractArray, Except.map, map_real_complex_Real]
  · intro epsF hypotF hhyp heps z
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [eps_Complex, conj_Complex, real_Complex, imag_Complex, (heps z.im).1]
    · simp [eps_Complex, neg_Complex, real_Complex, imag_Complex, (heps z.re).1, (heps z.im).1]
    · simp [eps_Complex, real_Complex, imag_Complex, (heps z.re).2.1, (heps z.im).2.1]
    · simp [eps_Complex, real_Complex, imag_Complex, (hhyp (epsF z.re) (epsF z.im)).1]
    · intro hnf
      unfold isfinite_Complex real_Complex imag_Complex at hnf
      by_cases hre : F64.isfinite z.re = true
      · simp only [hre, Bool.true_and] at hnf
        unfold eps_Complex real_Complex imag_Complex
        rw [(heps z.im).2.2 hnf, (hhyp (epsF z.re) F64.nan).2.2]
      · have hre' : F64.isfinite z.re = false := Bool.eq_false_iff.mpr hre
        unfold eps_Complex real_Complex imag_Complex
        rw [(heps z.re).2.2 hre', (hhyp F64.nan (epsF z.im)).2.1]
  · intro a b hab
    simp [eps_Complex, real_Complex, imag_Complex, hab]
  · intro sr si hypotF sqrtF hhyp
    have he1 : ∀ s : Bool, epsOf_F64 (if s then F64.neg F64.one else F64.one) = F64.eps := by
      intro s; cases s <;> decide
    have he2 : ∀ s : Bool, epsOf_F64 (if s then F64.neg Fl64.two else Fl64.two) = F64.ofBits 0x3cc0000000000000 := by
      intro s; cases s <;> decide
    have heinf : ∀ s : Bool, F64.isnan (epsOf_F64 (F64.inf s)) = true := by
      intro s; cases s <;> decide
    unfold eps_Complex eps_Type_Complex real_Complex imag_Complex
    simp [he1, he2, heinf, hhyp]

/-!
Nothing to promise:
- Complex@17: pure struct constructor forwarding through `promote(x, y)`.
- Complex@47: identity constructor returning `z` unchanged.
- float@56: identity type mapping `Complex{T}` on `T<:AbstractFloat`.
- float@57: pure type-level wrapper `Complex{float(T)}`.
- real@120: fallback `real(T::Type) = T`.
- real@121: identity type mapping `real(::Type{T}) = T` on `T<:Real`.
- real@123: bottom type mapping `real(::Type{Union{}}) = Union{}`.
- real@124: bottom type arity guard throwing `MethodError`.
- complex@168: identity conversion `complex(z::Complex) = z`.
- complex@170: pure wrapper `complex(x::Real, y::Real) = Complex(x, y)`.
- complex@190: pure type constructor `complex(::Type{T}) = Complex{T}`.
- complex@191: pure type wrapper `complex(::Type{Complex{T}}) = Complex{T}`.
- complex@192: bottom type mapping `complex(::Type{Union{}}) = Union{}`.
- complex@195: bottom type arity guard throwing `MethodError`.
- inv@288: pure forwarding `inv(z::Complex{<:Integer}) = inv(float(z))`.
- +@290: unary plus forwarding `(+(real(z)), +(imag(z)))`.
- _mulsub@303: internal generic fallback `a*b - c`.
- muladd@348: argument-commuting forwarding `muladd(x, z, y) = muladd(z, x, y)`.
- /@357: pure forwarding `a * inv(T(z))`.
- cis@586: empty generic function declaration `function cis end`.
- cispi@617: empty generic function declaration `function cispi end`.
- ^@887: pure forwarding `power_by_squaring(z, n)`.
- ^@896: pure promotion wrapper `^(promote(z, p)...)`.
- ^@900: pure promotion wrapper `^(promote(z, p)...)`.
- float@1129: identity conversion `float(z::Complex{<:AbstractFloat}) = z`.
- float@1130: pure componentwise wrapper `Complex(float(real(z)), float(imag(z)))`.
- big@1132: pure type-level wrapper `Complex{big(T)}`.
- big@1133: pure constructor forwarding `Complex{big(T)}(z)`.
- complex@1153: identity array return `complex(A::AbstractArray{<:Complex}) = A`.
-/

/-! ## Registry entries for `base/complex.jl` -/

def entries : List Entry := [
  -- Refuted (6)
  { id := "complex-div-real-divisor", juliaFile := "base/complex.jl"
    juliaFns := ["/(::ComplexF64, ::ComplexF64)", "/(::Complex, ::Real)"]
    statement := "For finite z and finite nonzero real x, z / complex(x, 0.0) equals the componentwise quotient z / x."
    source := "invariant (real-valued complex divisor behaves like real division); issue #48457"
    status := .refuted, prop := ``DivRealDivisor, thm := some ``divRealDivisor_refuted
    issue := "#48457 (closed, same 49.0 example)"
    notes := "complex(49.0,0.0)/complex(49.0,0.0) == 0.9999999999999999+0.0im because robust_cdiv2 multiplies by t = 1/c. The / docstring defines x/y as x*inv(y), so P3." },
  { id := "complex-div-spurious-nan", juliaFile := "base/complex.jl"
    juliaFns := ["/(::ComplexF64, ::ComplexF64)", "robust_cdiv2", "scaling_cdiv", "scaleargs_cdiv"]
    statement := "For finite z and finite nonzero w, real(z/w) is not NaN when the exact real part of z/w is at most floatmax in magnitude."
    source := "invariant; base/complex.jl:394-396 (scaled robust division); issue #5979"
    status := .refuted, prop := ``DivNoSpuriousNaN, thm := some ``divNoSpuriousNaN_refuted
    issue := "related #5979 (closed), #22983 (closed); none found for this case"
    notes := "complex(1.0, 2.0^1000)/complex(2.0^-40, 0.0) == NaN + Inf*im: robust_cdiv2's r == 0 branch evaluates 0*(b/c) = 0*Inf. Also (Inf+0im)/(1+0im) == Inf + NaN*im." },
  { id := "complex-div-subnormal-ratio", juliaFile := "base/complex.jl"
    juliaFns := ["/(::ComplexF64, ::ComplexF64)", "robust_cdiv1", "cdiv", "scaling_cdiv", "scaleargs_cdiv"]
    statement := "For finite z and nonzero finite w whose exact real part is a normal binary64 magnitude, real(z/w) is finite with relative error at most 2^-20."
    source := "base/complex.jl:394-396 (robust division, arXiv:1210.4539)"
    status := .refuted, prop := ``DivComponentAccurate, thm := some ``divComponentAccurate_refuted
    issue := "none found (queries: complex division accuracy, complex division underflow, complex division subnormal, robust complex division); related #5072"
    notes := "complex(2.0^1000, 0.0)/complex(3*nextfloat(0.0), 2.0) has real part 2^-74 instead of about 3*2^-76: r = c/d underflows gradually. Normwise accurate, so P3." },
  { id := "complex-int-div-typemin", juliaFile := "base/complex.jl"
    juliaFns := ["/(::Complex{T}, ::Complex{T}) where T<:Real"]
    statement := "Complex{Int} division by a nonzero divisor never returns a NaN component."
    source := "invariant; base/docs/basedocs.jl:3552 (floating-point results for integer arguments)"
    status := .refuted, prop := ``IntDivNoNaN, thm := some ``intDivNoNaN_refuted
    issue := "none found (queries: complex typemin, Complex Int division, complex integer division NaN, complex division NaN)"
    notes := "Complex(1,0)/Complex(typemin(Int),0) == NaN + NaN*im: abs(typemin) wraps negative, so base/complex.jl:368 takes the branch dividing by the zero component." },
  { id := "complex-pow-typemin", juliaFile := "base/complex.jl"
    juliaFns := ["^(::Complex{<:AbstractFloat}, ::Integer)", "power_by_squaring"]
    statement := "z^n for z::ComplexF64 and n::Int returns normally for every z and n."
    source := "invariant; real analogue fixed in #57464"
    status := .refuted, prop := ``PowIntTotal, thm := some ``powIntTotal_refuted
    issue := "none found (queries: complex power typemin, power_by_squaring typemin, complex typemin); related #57464 (closed, Float32/Float16)"
    notes := "complex(2.0,0.0)^typemin(Int) throws DomainError because -typemin(Int) wraps; 2.0^typemin(Int) == 0.0." },
  { id := "complex-muladd-exact", juliaFile := "base/complex.jl"
    juliaFns := ["muladd(::Complex, ::Complex, ::Complex)", "_mulsub(a::T, b::T, c::T) where {T<:Real}"]
    statement := "When every product, difference and sum in z*w + x is exact, muladd(z, w, x) == z*w + x."
    source := "base/math.jl:1248-1252 (muladd docstring)"
    status := .refuted, prop := ``MuladdExact, thm := some ``muladdExact_refuted
    issue := "none found (queries: complex muladd, muladd complex, PR complex muladd); related #59684 (closed), PR #62005 (open)"
    notes := "z = w = 2^30 + 2^30im, x = 1: muladd gives 0 + 2^61im, z*w + x gives 1 + 2^61im. The complex muladd reassociates real(z)*real(w) - (imag(z)*imag(w) - real(x))." },
  -- Proven (18)
  { id := "complex-conj-involution", juliaFile := "base/complex.jl"
    juliaFns := ["conj(::Complex)"]
    statement := "conj(conj(z)) is bit-identical to z for every ComplexF64 and Complex{T}, and conj is a ring automorphism on Gaussian integers Complex{T}."
    source := "base/complex.jl:268-280 (conj docstring)"
    status := .proven, prop := ``ConjInvolution, thm := some ``conjInvolution_proven },
  { id := "complex-isequal-hash", juliaFile := "base/complex.jl"
    juliaFns := ["hash(::Complex, ::UInt)", "isequal(::Complex, ::Complex)", "isequal(::Complex, ::Real)", "isequal(::Real, ::Complex)"]
    statement := "isequal(z, w) implies hash(z, h) == hash(w, h), and isequal(z, x) or isequal(x, z) for real x implies hash(z, h) == hash(x, h), given a real hash that respects isequal."
    source := "hash docstring (isequal(x,y) implies hash(x)==hash(y)); base/complex.jl:250-263"
    status := .proven, prop := ``HashIsequal, thm := some ``hashIsequal_proven
    notes := "Holds for -0.0 and NaN components: complex isequal is componentwise isequal." },
  { id := "complex-isreal-doc", juliaFile := "base/complex.jl"
    juliaFns := ["isreal(::Complex)", "==(::Complex, ::Complex)", "==(::Complex, ::Real)", "==(::Real, ::Complex)", "in(::Complex, ::AbstractRange{<:Real})", "(::Type{T})(::Complex) where T<:Real"]
    statement := "isequal(z, real(z)) implies isreal(z); for non-NaN real part, isreal(z) == (z == real(z)); range membership requires isreal(z); and converting Complex to Real succeeds iff isreal(z)."
    source := "base/complex.jl:44-45,126-131,246-248,254 (isreal docstring)"
    status := .proven, prop := ``IsrealDoc, thm := some ``isrealDoc_proven },
  { id := "complex-false-strong-zero", juliaFile := "base/complex.jl"
    juliaFns := ["*(::Bool, ::Complex)", "*(::Complex, ::Bool)"]
    statement := "false * z and z * false are signed zeros in both components (retaining component signbits and clearing Inf/NaN), while true * z == z * true == z."
    source := "Bool docstring (false is a strong zero); base/complex.jl:322-323, base/bool.jl:161-165"
    status := .proven, prop := ``FalseStrongZero, thm := some ``falseStrongZero_proven },
  { id := "complex-bool-mul-promotes", juliaFile := "base/complex.jl"
    juliaFns := ["*(::Complex{Bool}, ::Complex{Bool})", "im", "+(::Bool, ::Complex{Bool})", "+(::Complex{Bool}, ::Bool)", "-(::Bool, ::Complex{Bool})", "-(::Complex{Bool}, ::Bool)", "*(::Bool, ::Complex{Bool})", "*(::Complex{Bool}, ::Bool)", "+(::Bool, ::Complex)", "+(::Complex, ::Bool)", "-(::Bool, ::Complex)", "-(::Complex, ::Bool)", "+(::Real, ::Complex{Bool})", "+(::Complex{Bool}, ::Real)", "-(::Real, ::Complex{Bool})", "-(::Complex{Bool}, ::Real)", "*(::Real, ::Complex{Bool})", "*(::Complex{Bool}, ::Real)"]
    statement := "Complex{Bool} multiplication and mixed Bool/Real/Complex{Bool} and Bool/Complex arithmetic equal the operations on operands promoted to integer complex numbers; im*im == -1 + 0im."
    source := "base/complex.jl:20-36,311-334 (im docstring: im * im == -1 + 0im)"
    status := .proven, prop := ``BoolMulPromotes, thm := some ``boolMulPromotes_proven },
  { id := "complex-sqrt-branch-cut", juliaFile := "base/complex.jl"
    juliaFns := ["sqrt(::Complex)", "ssqs"]
    statement := "For real(z) < 0 (including -Inf), imag(sqrt(z)) has the signbit of imag(z) and imag(sqrt(conj(z))) == -imag(sqrt(z)), while for real(z) >= 0, real(sqrt(conj(z))) == real(sqrt(z)), and ssqs(x, -y) == ssqs(-x, -y) == ssqs(x, y)."
    source := "base/math.jl:644-646 (sqrt branch-cut note); base/complex.jl:519-558"
    status := .proven, prop := ``SqrtBranchCut, thm := some ``sqrtBranchCut_proven },
  { id := "complex-int-pow-wraps", juliaFile := "base/complex.jl"
    juliaFns := ["^(::Complex{<:Integer}, ::Integer)", "power_by_squaring"]
    statement := "For z::Complex{T} (T any BitInteger) and n >= 0, z^n is the exact Gaussian-integer power modulo 2^T.bits; for n < 0, z^n succeeds iff z is +-1 + 0im and throws DomainError otherwise."
    source := "manual (integer arithmetic wraps on overflow); base/complex.jl:894"
    status := .proven, prop := ``IntPowWraps, thm := some ``intPowWraps_proven
    notes := "No checked_pow exists for Complex; overflow wraps like repeated integer multiplication." },
  { id := "complex-abs-conj-neg", juliaFile := "base/complex.jl"
    juliaFns := ["abs(::Complex)", "abs2(::Complex)", "conj(::Complex)", "-(::Complex)"]
    statement := "abs(conj(z)) and abs(-z) are bit-identical to abs(z) on ComplexF64, and abs2(conj(z)) == abs2(-z) == abs2(z) on Complex{T} and non-NaN ComplexF64."
    source := "invariant |conj z| = |-z| = |z|; base/complex.jl:280-282,291"
    status := .proven, prop := ``AbsConjNeg, thm := some ``absConjNeg_proven },
  { id := "complex-gaussian-ring", juliaFile := "base/complex.jl"
    juliaFns := ["+(::Complex)", "-(::Complex)", "+(::Complex, ::Complex)", "-(::Complex, ::Complex)", "*(::Complex, ::Complex)", "-%(::Complex)", "+%(::Complex, ::Complex)", "-%(::Complex, ::Complex)", "*%(::Complex, ::Complex)", "+(::Real, ::Complex)", "+(::Complex, ::Real)", "-(::Real, ::Complex)", "-(::Complex, ::Real)", "*(::Real, ::Complex)", "*(::Complex, ::Real)", "_mulsub", "muladd(::Complex, ::Complex, ::Complex)", "muladd(::Real, ::Complex, ::Union{Real,Complex})", "muladd(::Complex, ::Real, ::Real)", "muladd(::Complex, ::Real, ::Complex)", "muladd(::Real, ::Real, ::Complex)", "muladd(::Complex, ::Complex, ::Real)"]
    statement := "For every BitInteger width T, Complex{T} satisfies commutative ring identities, z * conj(z) == Complex(abs2(z), 0), Brahmagupta-Fibonacci multiplicativity abs2(z * w) == abs2(z) * abs2(w), wrapping operator agreement, mixed scalar embedding, and exact muladd association."
    source := "base/complex.jl:280-355; Gaussian integer ring and norm multiplicativity invariants"
    status := .proven, prop := ``GaussianRingLaws, thm := some ``gaussianRingLaws_proven },
  { id := "complex-widen-no-overflow", juliaFile := "base/complex.jl"
    juliaFns := ["widen(::Type{Complex{T}})", "promote_rule(::Type{Complex{T}}, ::Type{S})", "promote_rule(::Type{Complex{T}}, ::Type{Complex{S}})", "Complex{T}(::Complex)"]
    statement := "Widening Complex{T} for signed BitInteger T below 128 bits prevents overflow in complex addition and subtraction, and complex promote_rule is commutative, associative, and idempotent."
    source := "base/complex.jl:43,49-54; widen docstring (base/operators.jl:955-962)"
    status := .proven, prop := ``WidenPromoteLaws, thm := some ``widenPromoteLaws_proven },
  { id := "complex-type-algebra", juliaFile := "base/complex.jl"
    juliaFns := ["Complex(::Real, ::Real)", "Complex(::Real)", "Complex{T}(::Real)", "Complex(::Complex)", "float(::Type{Complex{T}})", "real(::Complex)", "imag(::Complex)", "real(::Real)", "imag(::Real)", "reim", "real(::Type)", "isreal(::Real)", "isreal(::Complex)", "isinteger(::Complex)", "isfinite(::Complex)", "isnan(::Complex)", "isinf(::Complex)", "iszero(::Complex)", "isone(::Complex)", "complex(::Complex)", "complex(::Real)", "complex(::Real, ::Real)", "complex(::Type)"]
    statement := "isfinite(z) == (!isnan(z) && !isinf(z)) on ComplexF64, isinteger(z) holds iff z.im == 0 and isinteger(z.re), embedding a real x via complex(x) round-trips through T(z) while nonzero imaginary parts throw InexactError, and type-level real/complex satisfy real(complex(T)) == real(T) and complex(complex(T)) == complex(T)."
    source := "base/complex.jl:17-18,42-57,72-195; Complex, real, imag, reim, isreal, and complex docstrings"
    status := .proven, prop := ``TypeAndPredicateAlgebra, thm := some ``typeAndPredicateAlgebra_proven },
  { id := "complex-flipsign-bswap-io", juliaFile := "base/complex.jl"
    juliaFns := ["flipsign(::Complex, ::Real)", "show(::IO, ::Complex)", "show(::IO, ::Complex{Bool})", "show_unquoted(::IO, ::Complex, ::Int, ::Int)", "read(::IO, ::Type{Complex{T}})", "write(::IO, ::Complex)", "bswap(::Complex)"]
    statement := "flipsign(flipsign(z, y), y) == z on ComplexF64 and Complex{T}, bswap is an involution, read after write on a stream recovers z, show strips leading '-' of negative imaginary parts (including -0.0 and -Inf) and inserts '*' iff !(isaSigned || (isaAbstractFloat && isfinite(im))), show_unquoted wraps show(z) in parentheses iff prec >= plusPrec, and show on Complex{Bool} prints \"im\" iff z == im."
    source := "base/complex.jl:197-242; flipsign, bswap, read, write, and show invariants"
    status := .proven, prop := ``FlipsignBswapIO, thm := some ``flipsignBswapIO_proven },
  { id := "complex-trig-hyperbolic-identities", juliaFile := "base/complex.jl"
    juliaFns := ["cis(::Real)", "cis(::Complex)", "cispi(::Real)", "cispi(::Complex)", "sin(::Complex)", "cos(::Complex)", "tan(::Complex)", "asin(::Complex)", "acos(::Complex)", "atan(::Complex)", "sinh(::Complex)", "cosh(::Complex)", "tanh(::Complex)", "asinh(::Complex)", "acosh(::Complex)", "atanh(::Complex)"]
    statement := "cis(-theta) == conj(cis(theta)) and cispi(-theta) == conj(cispi(theta)), sin/cos/sinh/cosh/tanh/tan satisfy conjugation symmetry and exact rotation and signed-zero identities across all non-NaN inputs, and asin/asinh/acos/acosh/atanh/atan (instantiated with real sqrt_ComplexF64_tr and inv_Complex_F64) satisfy their general finite branch formulas and conjugation/reflection symmetries (asin(conj z) == conj(asin z), asinh(-zr + zi*im) == (-real(asinh z), imag(asinh z)), real(acos(conj z)) == real(acos z), acosh(conj z) == conj(acosh z)) across all finite inputs as well as all C99 Annex G branch-cut, pole, and infinity limits."
    source := "base/complex.jl:573-624,905-1089; Euler formula, conjugation/parity symmetries, and C99 Annex G special-value rules"
    status := .proven, prop := ``TrigHyperbolicIdentities, thm := some ``trigHyperbolicIdentities_proven },
  { id := "complex-pow-bool-and-zero", juliaFile := "base/complex.jl"
    juliaFns := ["_cpow", "^(::Complex{T}, ::Complex{T})", "^(::Complex{T}, ::T)", "^(::T, ::Complex{T})", "^(::Complex, ::Bool)", "^(::Complex, ::Integer)", "^(::Complex{<:AbstractFloat}, ::Bool)", "^(::Complex{<:Integer}, ::Bool)", "^(::Complex{T}, ::S)", "^(::T, ::Complex{S})"]
    statement := "z^true == z and .ok (z^b) == z^Int(b) across all Bool power methods (with Complex{<:AbstractFloat}^false preserving signbit(z.im) in +-0.0), _cpow(z, +-0.0 +- 0.0im) has imaginary zero signbit equal to signbit(p.re) != signbit(z.im), _cpow delegates every small integer real exponent on non-real z to power_by_squaring, _cpow distinguishes Real vs Complex positive bases (< 1) in its imaginary zero sign for every non-integer real exponent, and _cpow maps every zero base with non-integer/complex exponent p to z (if p.re > 0) or NaN + NaN*im."
    source := "base/complex.jl:792-903; Bool power, integer power delegation, and signed-zero rules of _cpow"
    status := .proven, prop := ``PowBoolAndZero, thm := some ``powBoolAndZero_proven },
  { id := "complex-inv-properties", juliaFile := "base/complex.jl"
    juliaFns := ["inv(::Complex)", "inv(::Complex{<:Integer})", "inv(::Complex{T}) where T<:Union{Float16,Float32}", "inv(::ComplexF64)", "robust_cinv"]
    statement := "Across all complex inv methods (generic, Float16/Float32, and ComplexF64), any input with an infinite component maps to signed zero with conjugate signbits (signbit(re), !signbit(im)), all finite non-NaN inputs satisfy inv(conj(z)) == conj(inv(z)) in both real and imaginary components, inv_ComplexF64 scales by 0.5 in the overflow regime and dispatches to robust_cinv, and naive robust_cinv(0.0, d) produces (0.0, NaN) on every finite nonzero d."
    source := "base/complex.jl:283-288,476-517; complex reciprocal conjugation, scaling, and special-value invariants"
    status := .proven, prop := ``InvProperties, thm := some ``invProperties_proven },
  { id := "complex-div-scaling-and-inf", juliaFile := "base/complex.jl"
    juliaFns := ["/(::Real, ::Complex)", "/(::Complex, ::Real)", "/(::Complex{T}, ::Complex{T}) where T<:Real", "/(::Complex{T}, ::Complex{T}) where T<:Union{Float16,Float32}", "/(::ComplexF64, ::ComplexF64)", "cdiv", "scaling_cdiv", "scaleargs_cdiv"]
    statement := "Complex division by an infinite divisor agrees across generic, Float16/Float32, and ComplexF64 methods on all finite dividends and returns NaN + NaN*im on all nonfinite dividends; div_Complex_SmallFloat and cdiv satisfy im(z / w) == re((-i * z) / w) and re(conj(z) / conj(w)) == re(z / w) for all inputs; and scaleargs_cdiv scales across all normal and overflow regimes."
    source := "base/complex.jl:357-459; complex division algebraic, scaling, and special-value invariants"
    status := .proven, prop := ``DivScalingAndInf, thm := some ``divScalingAndInf_proven },
  { id := "complex-exp-log-special-values", juliaFile := "base/complex.jl"
    juliaFns := ["angle(::Complex)", "log(::Complex)", "log10(::Complex)", "log2(::Complex)", "exp(::Complex)", "expm1(::Complex)", "log1p(::Complex)", "exp2(::Complex)", "exp10(::Complex)"]
    statement := "Using real ssqs_F64_tr, angle(conj(z)) == -angle(z), log(conj(z)) == conj(log(z)) in both components, real(log(-z)) == real(log(z)) (and likewise for log10 and log2), exp2(z) == exp2(z.re) * cis(z.im * log(2)) and exp10(z) == exp10(z.re) * cis(z.im * log(10)) satisfy full conjugation symmetry exp2(conj z) == conj(exp2 z) and exp10(conj z) == conj(exp10 z) across all finite inputs, real(exp(conj(z))) == real(exp(z)) and real(expm1(conj(z))) == real(expm1(z)) across all non-NaN inputs, exp and expm1 preserve signed zeros on the real axis and map +-Inf + nonfinite*im to their C99 Annex G limits, and log1p fixes all four signed zeros via Kahan's 1 + z == 1 branch and satisfies log1p(conj(z)) == conj(log1p(z)) on infinite-imaginary inputs."
    source := "base/complex.jl:651-789; complex logarithm and exponential conjugation, accuracy, and C99 Annex G special-value invariants"
    status := .proven, prop := ``ExpLogSpecialValues, thm := some ``expLogSpecialValues_proven },
  { id := "complex-round-array-eps", juliaFile := "base/complex.jl"
    juliaFns := ["round(::Complex, ::RoundingMode, ::RoundingMode)", "float(::Complex{<:AbstractFloat})", "float(::Complex)", "big(::Type{Complex{T}})", "big(::Complex{T})", "complex(::AbstractArray{<:Complex})", "complex(::AbstractArray{T})", "eps(::Complex{<:AbstractFloat})", "eps(::Type{Complex{T}})"]
    statement := "round on Complex is idempotent and satisfies round(-z, RoundUp, RoundDown) == -round(z, RoundDown, RoundUp), round(conj(z), RoundNearest, RoundUp) == conj(round(z, RoundNearest, RoundDown)), and round(-z, RoundToZero, RoundNearest) == -round(z, RoundToZero, RoundNearest) for all z; complex(A::AbstractArray{T}) rejects non-concrete element types with ArgumentError and round-trips concrete arrays under map(real); and eps_Complex is invariant under conj, neg, and component abs for all z, returns NaN on all non-finite z, and equals eps_Type_Complex at (+-1.0, +-1.0)."
    source := "base/complex.jl:1091-1166; round, complex(::AbstractArray), and eps docstrings"
    status := .proven, prop := ``RoundArrayEps, thm := some ``roundArrayEps_proven }
]

end JuliaLean.Proofs.base.complex
