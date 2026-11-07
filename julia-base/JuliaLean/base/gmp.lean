import JuliaLean.base.combinatorics
import JuliaLean.base.parse
import JuliaLean.base.hashing
import JuliaLean.base.intfuncs
import JuliaLean.base.version
import JuliaLean.base.number
import JuliaLean.base.io
import JuliaLean.base.abstractarray
import JuliaLean.base.rounding
import JuliaLean.base.bool
import JuliaLean.Core
import JuliaLean.base.float
import JuliaLean.base.rational

/-!
# Model of `base/gmp.jl`

Julia f755f49a9e41380d7da126b3c1db9fe7f83dd027, 64-bit Unix ABI.
BigInt keeps its mathematical value and GMP's signed limb count, allocated
capacity and little-endian limb storage. Pointer identity and spare allocation
are abstracted; output primitives retain capacity and use the minimum additional
capacity needed for their documented result. `Valid` records representation
consistency for inputs obtained by unsafe operations. In-place methods return
the updated output record; callers thread that record through subsequent calls.
GMP calls below are mathematical primitives specified by the cited GMP 6.3 manual
sections. Julia wrappers retain their source checks and call order.
-/

namespace JuliaLean.base.gmp
open JuliaLean

abbrev Limb := JInt .u64
abbrev Cint := JInt .i32
abbrev Culong := JInt .u64
abbrev Clong := JInt .i64

def bitsPerLimb : Nat := 64

def limbsOfNat (n : Nat) : List Limb :=
  if h : n = 0 then [] else
    JInt.wrap .u64 (Int.ofNat (n % 2^64)) :: limbsOfNat (n / 2^64)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def limbMagnitude : List Limb → Nat
  | [] => 0
  | l :: ls => l.val.toNat + 2^64 * limbMagnitude ls


/--
Julia source: base/gmp.jl:64-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    BigInt <: Signed

Arbitrary precision integer type.
"""
mutable struct BigInt <: Signed
    alloc::Cint
    size::Cint
    d::Ptr{Limb}

    function BigInt(; nbits::Integer=0)
        b = MPZ.init2!(new(), nbits)
        finalizer(cglobal((:__gmpz_clear, libgmp)), b)
        return b
    end
end
```
-/
structure BigInt where
  val : Int
  alloc : Cint
  size : Cint
  d : List Limb
  deriving Repr, DecidableEq

def Valid (x : BigInt) : Prop :=
  x.size.val.natAbs ≤ x.d.length ∧ x.size.val.natAbs ≤ x.alloc.val.toNat ∧
  x.val = (if x.size.val < 0 then -(limbMagnitude (x.d.take x.size.val.natAbs) : Int)
    else (limbMagnitude (x.d.take x.size.val.natAbs) : Int)) ∧
  (x.size.val = 0 ↔ x.val = 0) ∧
  (x.size.val ≠ 0 → ((x.d[x.size.val.natAbs - 1]?).getD (JInt.wrap .u64 0)).val ≠ 0)

def ofInt (n : Int) (nbits : Nat := 0) : BigInt :=
  let limbs := limbsOfNat n.natAbs
  let count := Int.ofNat limbs.length
  ⟨n, JInt.wrap .i32 (Int.ofNat (max limbs.length ((nbits + 63) / 64))),
    JInt.wrap .i32 (if n < 0 then -count else count), limbs⟩

def writeValue (out : BigInt) (n : Int) : BigInt :=
  let r := ofInt n
  { r with alloc := JInt.wrap .i32 (max out.alloc.val r.alloc.val) }

def initBigInt : BigInt := ofInt 0

def sgn (n : Int) : Int := if n < 0 then -1 else if n > 0 then 1 else 0

def factorialNat : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorialNat n

def chooseLoop (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, result => result
  | left+1, i, result => chooseLoop n left (i+1) (result*(n-i)/(i+1))

def chooseNat (n k : Nat) : Nat := chooseLoop n k 0 1

def egcdNat (a b : Nat) : Int × Int × Int :=
  if h : b = 0 then (a, 1, 0)
  else
    let (g,s,t) := egcdNat b (a % b)
    (g, t, s - (a / b : Nat) * t)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

def gmpGcdext (a b : Int) : Int × Int × Int :=
  let g := Int.ofNat (Nat.gcd a.natAbs b.natAbs)
  if a.natAbs = b.natAbs then (g, 0, sgn b)
  else if b = 0 then (g, sgn a, 0)
  else if a = 0 then (g, 0, sgn b)
  else if (b.natAbs : Int) = 2*g then
    let s := sgn a
    (g, s, (g-a*s).tdiv b)
  else if (a.natAbs : Int) = 2*g then
    let t := sgn b
    (g, (g-b*t).tdiv a, t)
  else
    let (_,s0,_) := egcdNat a.natAbs b.natAbs
    let modulus := (b.natAbs : Int).tdiv g
    let s0 := (s0 * sgn a) % modulus
    let s := if 2*s0 > modulus then s0-modulus else s0
    (g,s,(g-a*s).tdiv b)

def bitwiseInt (op : Nat → Nat → Nat) (a b : Int) : Int :=
  let width := max a.natAbs.log2 b.natAbs.log2 + 2
  let modulus := (2 : Int)^width
  let result := op (a % modulus).toNat (b % modulus).toNat
  if result ≥ 2^(width-1) then (result : Int)-modulus else result

def bitAt (a : Int) (i : Nat) : Bool := decide ((a.fdiv ((2 : Int)^i)) % 2 = 1)

def countBits (n : Nat) : Nat := (List.range (n.log2+1)).foldl
  (fun count i => count + if n / 2^i % 2 = 1 then 1 else 0) 0

def scanBit (a : Int) (start : Nat) (wanted : Bool) : Int :=
  let width := max start (a.natAbs.log2+2)
  match ((List.range (width-start+1)).find? (fun j => bitAt a (start+j) == wanted)) with
  | some j => Int.ofNat (start+j)
  | none => -1

def radixDigits (n base : Nat) : List Nat :=
  if h : base ≥ 2 ∧ n ≥ base then
    n % base :: radixDigits (n / base) base
  else [n]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

def digitChar (base d : Nat) : Char :=
  Char.ofNat (if d < 10 then 48+d else if base ≤ 36 then 87+d
    else if d < 36 then 55+d else 61+d)

def renderMagnitude (n base : Nat) : String :=
  String.ofList ((radixDigits n base).reverse.map (digitChar base))

namespace MPZ


/--
GMP manual §5.1 Initialization Functions, `mpz_init`, `mpz_init2`, `mpz_realloc2`: https://gmplib.org/manual/Initializing-Integers

Julia source: base/gmp.jl:163-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
init!(x::BigInt) = (ccall((:__gmpz_init, libgmp), Cvoid, (mpz_t,), x); x)
init2!(x::BigInt, a) = (ccall((:__gmpz_init2, libgmp), Cvoid, (mpz_t, bitcnt_t), x, a); x)

realloc2!(x, a) = (ccall((:__gmpz_realloc2, libgmp), Cvoid, (mpz_t, bitcnt_t), x, a); x)
realloc2(a) = realloc2!(BigInt(), a)
```
-/
def init (x : BigInt) : BigInt := writeValue x 0
-- Source: base/gmp.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- init2!(x::BigInt, a) = (ccall((:__gmpz_init2, libgmp), Cvoid, (mpz_t, bitcnt_t), x, a); x)
-- /Source
def init2 (x : BigInt) (nbits : Culong) : BigInt :=
  ofInt 0 nbits.val.toNat

-- Source: base/gmp.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- realloc2!(x, a) = (ccall((:__gmpz_realloc2, libgmp), Cvoid, (mpz_t, bitcnt_t), x, a); x)
-- /Source
def realloc2 (x : BigInt) (nbits : Culong) : BigInt :=
  let capacity := (nbits.val.toNat + 63) / 64
  let n := if x.val.natAbs < 2^nbits.val.toNat then x.val else 0
  { (ofInt n) with alloc := JInt.wrap .i32 (capacity : Int) }

-- Source: base/gmp.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- realloc2(a) = realloc2!(BigInt(), a)
-- /Source
def realloc (nbits : Culong) : BigInt := realloc2 (initBigInt) nbits

/--
GMP manual §5.13 Miscellaneous Functions, `mpz_sizeinbase`: exact for power-of-two bases; `oneHigh` selects the documented possible one-digit overestimate for other bases: https://gmplib.org/manual/Miscellaneous-Integer-Functions

Julia source: base/gmp.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeinbase(a::BigInt, b) = Int(ccall((:__gmpz_sizeinbase, libgmp), Csize_t, (mpz_t, Cint), a, b))
```
-/
-- Source: base/gmp.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sizeinbase(a::BigInt, b) = Int(ccall((:__gmpz_sizeinbase, libgmp), Csize_t, (mpz_t, Cint), a, b))
-- /Source
def sizeinbase (a : BigInt) (base : Cint) (oneHigh : Bool) : Clong :=
  let radix := base.val.toNat
  let exact := (radixDigits a.val.natAbs radix).length
  let power2 := radix > 0 ∧ Nat.land radix (radix-1) = 0
  let extra := if a.val ≠ 0 ∧ ¬power2 ∧ oneHigh then 1 else 0
  JInt.wrap .i64 ((exact+extra : Nat) : Int)

inductive BinaryOp where
  | add | sub | mul | fdivQ | tdivQ | cdivQ | fdivR | tdivR | cdivR
  | gcd | lcm | and | ior | xor
  deriving DecidableEq, Repr

def binaryValue (op : BinaryOp) (a b : Int) : Jl Int :=
  match op with
  | .add => pure (a+b)
  | .sub => pure (a-b)
  | .mul => pure (a*b)
  | .gcd => pure (Int.ofNat (Nat.gcd a.natAbs b.natAbs))
  | .lcm => pure (Int.ofNat ((a.natAbs * b.natAbs) / Nat.gcd a.natAbs b.natAbs))
  | .and => pure (bitwiseInt Nat.land a b)
  | .ior => pure (bitwiseInt Nat.lor a b)
  | .xor => pure (bitwiseInt Nat.xor a b)
  | .fdivQ | .tdivQ | .cdivQ | .fdivR | .tdivR | .cdivR =>
    if b = 0 then .error .divideError else
      let q := if op = .tdivQ ∨ op = .tdivR then a.tdiv b
        else if op = .fdivQ ∨ op = .fdivR then a.fdiv b else -((-a).fdiv b)
      pure (if op = .fdivR ∨ op = .tdivR ∨ op = .cdivR then a-q*b else q)


/--
GMP manual §§5.5 Arithmetic, 5.6 Division, 5.9 Number Theoretic, 5.11 Logical and Bit Manipulation Functions: https://gmplib.org/manual/Integer-Functions

Julia source: base/gmp.jl:171-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op, nbits) in (:add => :(BITS_PER_LIMB*(1 + max(abs(a.size), abs(b.size)))),
                    :sub => :(BITS_PER_LIMB*(1 + max(abs(a.size), abs(b.size)))),
                    :mul => 0, :fdiv_q => 0, :tdiv_q => 0, :cdiv_q => 0,
                    :fdiv_r => 0, :tdiv_r => 0, :cdiv_r => 0,
                    :gcd => 0, :lcm => 0, :and => 0, :ior => 0, :xor => 0)
    op! = Symbol(op, :!)
    fname = Symbol(:__gmpz_, op)
    @eval begin
        $op!(x::BigInt, a::BigInt, b::BigInt) =
            (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.$fname(x::mpz_t, a::mpz_t, b::mpz_t)::Cvoid); x)
        $op(a::BigInt, b::BigInt) = $op!(BigInt(nbits=$nbits), a, b)
        $op!(x::BigInt, b::BigInt) = $op!(x, x, b)
    end
end
```
-/
-- Source: base/gmp.jl:179-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, a::BigInt, b::BigInt) =
--             (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.$fname(x::mpz_t, a::mpz_t, b::mpz_t)::Cvoid); x)
-- /Source
def binaryBang (op : BinaryOp) (x a b : BigInt) : Jl BigInt := do
  pure (writeValue x (← binaryValue op a.val b.val))
-- Source: base/gmp.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a::BigInt, b::BigInt) = $op!(BigInt(nbits=$nbits), a, b)
-- /Source
def binary (op : BinaryOp) (a b : BigInt) : Jl BigInt :=
  let nbits := if op = .add ∨ op = .sub then
    64 * (1 + max a.size.val.natAbs b.size.val.natAbs) else 0
  binaryBang op (ofInt 0 nbits) a b
-- Source: base/gmp.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, b::BigInt) = $op!(x, x, b)
-- /Source
def binaryInplace (op : BinaryOp) (x b : BigInt) : Jl BigInt := binaryBang op x x b

/--
GMP manual §5.9 `mpz_invert`: success returns least nonnegative inverse; failed output is unspecified and retained here: https://gmplib.org/manual/Number-Theoretic-Functions

Julia source: base/gmp.jl:186-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
invert!(x::BigInt, a::BigInt, b::BigInt) =
    (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall libgmp.__gmpz_invert(x::mpz_t, a::mpz_t, b::mpz_t)::Cint)
invert!(x::BigInt, b::BigInt) = invert!(x, x, b)
invert(a::BigInt, b::BigInt) = (ret=BigInt(); invert!(ret, a, b); ret)
```
-/
-- Source: base/gmp.jl:186-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invert!(x::BigInt, a::BigInt, b::BigInt) =
--     (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall libgmp.__gmpz_invert(x::mpz_t, a::mpz_t, b::mpz_t)::Cint)
-- /Source
def invertBang (x a b : BigInt) : Jl (BigInt × Cint) :=
  if b.val = 0 then .error .divideError else
  let (g,s,_) := gmpGcdext a.val b.val
  if g = 1 then pure (writeValue x (s % (b.val.natAbs : Int)), JInt.wrap .i32 1)
  else pure (x, JInt.wrap .i32 0)
-- Source: base/gmp.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invert!(x::BigInt, b::BigInt) = invert!(x, x, b)
-- /Source
def invertInplace (x b : BigInt) := invertBang x x b
-- Source: base/gmp.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- invert(a::BigInt, b::BigInt) = (ret=BigInt(); invert!(ret, a, b); ret)
-- /Source
def invert (a b : BigInt) : Jl BigInt := do
  let (ret,_) ← invertBang initBigInt a b
  pure ret

inductive UnsignedOp where
  | add | sub | mul | mul2exp | fdivQ2exp | pow | bin
  deriving DecidableEq, Repr

def unsignedValue (op : UnsignedOp) (a : Int) (b : Culong) : Int :=
  let n := b.val.toNat
  match op with
  | .add => a+b.val
  | .sub => a-b.val
  | .mul => a*b.val
  | .mul2exp => a*(2 : Int)^n
  | .fdivQ2exp => a.fdiv ((2 : Int)^n)
  | .pow => a^n
  | .bin => if a < 0 then (-1 : Int)^n * Int.ofNat (chooseNat (a.natAbs+n-1) n)
    else Int.ofNat (chooseNat a.toNat n)


/--
GMP manual §§5.5 Arithmetic, 5.6 Division, 5.7 Exponentiation, 5.9 Number Theoretic Functions: https://gmplib.org/manual/Integer-Functions

Julia source: base/gmp.jl:191-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:add_ui, :sub_ui, :mul_ui, :mul_2exp, :fdiv_q_2exp, :pow_ui, :bin_ui)
    op! = Symbol(op, :!)
    fname = Symbol(:__gmpz_, op)
    @eval begin
        $op!(x::BigInt, a::BigInt, b) =
            (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.$fname(x::mpz_t, a::mpz_t, b::Culong)::Cvoid); x)
        $op(a::BigInt, b) = $op!(BigInt(), a, b)
        $op!(x::BigInt, b) = $op!(x, x, b)
    end
end
```
-/
-- Source: base/gmp.jl:195-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, a::BigInt, b) =
--             (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.$fname(x::mpz_t, a::mpz_t, b::Culong)::Cvoid); x)
-- /Source
def unsignedBang (op : UnsignedOp) (x a : BigInt) (b : Culong) : BigInt :=
  writeValue x (unsignedValue op a.val b)
-- Source: base/gmp.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a::BigInt, b) = $op!(BigInt(), a, b)
-- /Source
def unsigned (op : UnsignedOp) (a : BigInt) (b : Culong) : BigInt :=
  unsignedBang op initBigInt a b
-- Source: base/gmp.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, b) = $op!(x, x, b)
-- /Source
def unsignedInplace (op : UnsignedOp) (x : BigInt) (b : Culong) : BigInt :=
  unsignedBang op x x b

/--
GMP manual §5.5 `mpz_ui_sub`: https://gmplib.org/manual/Integer-Arithmetic

Julia source: base/gmp.jl:202-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ui_sub!(x::BigInt, a, b::BigInt) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_ui_sub(x::mpz_t, a::Culong, b::mpz_t)::Cvoid); x)
ui_sub(a, b::BigInt) = ui_sub!(BigInt(), a, b)
```
-/
-- Source: base/gmp.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ui_sub!(x::BigInt, a, b::BigInt) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_ui_sub(x::mpz_t, a::Culong, b::mpz_t)::Cvoid); x)
-- /Source
def uiSubBang (x : BigInt) (a : Culong) (b : BigInt) := writeValue x (a.val-b.val)
-- Source: base/gmp.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ui_sub(a, b::BigInt) = ui_sub!(BigInt(), a, b)
-- /Source
def uiSub (a : Culong) (b : BigInt) := uiSubBang initBigInt a b

/--
GMP manual §5.11 `mpz_scan0`, `mpz_scan1`: two-complement infinite sign extension, ULONG_MAX if no bit: https://gmplib.org/manual/Integer-Logic-and-Bit-Fiddling

Julia source: base/gmp.jl:205-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:scan1, :scan0)
    # when there is no meaningful answer, ccall returns typemax(Culong), where Culong can
    # be UInt32 (Windows) or UInt64; we return -1 in this case for all architectures
    @eval $op(a::BigInt, b) = Int(signed(ccall($(gmpz(op)), Culong, (mpz_t, Culong), a, b)))
end
```
-/
def scan (wanted : Bool) (a : BigInt) (b : Culong) : Clong :=
  JInt.wrap .i64 (scanBit a.val b.val.toNat wanted)

/--
GMP manual §5.5 `mpz_mul_si`: https://gmplib.org/manual/Integer-Arithmetic

Julia source: base/gmp.jl:211-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_si!(x::BigInt, a::BigInt, b) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_mul_si(x::mpz_t, a::mpz_t, b::Clong)::Cvoid); x)
mul_si(a::BigInt, b) = mul_si!(BigInt(), a, b)
mul_si!(x::BigInt, b) = mul_si!(x, x, b)
```
-/
-- Source: base/gmp.jl:211-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mul_si!(x::BigInt, a::BigInt, b) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_mul_si(x::mpz_t, a::mpz_t, b::Clong)::Cvoid); x)
-- /Source
def mulSiBang (x a : BigInt) (b : Clong) := writeValue x (a.val*b.val)
-- Source: base/gmp.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mul_si(a::BigInt, b) = mul_si!(BigInt(), a, b)
-- /Source
def mulSi (a : BigInt) (b : Clong) := mulSiBang initBigInt a b
-- Source: base/gmp.jl:213-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mul_si!(x::BigInt, b) = mul_si!(x, x, b)
-- /Source
def mulSiInplace (x : BigInt) (b : Clong) := mulSiBang x x b

inductive UnaryOp where
  | neg | com | sqrt | set
  deriving DecidableEq, Repr


/--
GMP manual §§5.2 Assignment, 5.5 Arithmetic, 5.8 Root Extraction, 5.11 Logical Functions. Negative sqrt invokes the GMP arithmetic fault: https://gmplib.org/manual/Integer-Functions

Julia source: base/gmp.jl:215-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for op in (:neg, :com, :sqrt, :set)
    op! = Symbol(op, :!)
    fname = Symbol(:__gmpz_, op)
    @eval begin
        $op!(x::BigInt, a::BigInt) =
            (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.$fname(x::mpz_t, a::mpz_t)::Cvoid); x)
        $op(a::BigInt) = $op!(BigInt(), a)
    end
    op === :set && continue # MPZ.set!(x) would make no sense
    @eval $op!(x::BigInt) = $op!(x, x)
end
```
-/
-- Source: base/gmp.jl:219-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, a::BigInt) =
--             (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.$fname(x::mpz_t, a::mpz_t)::Cvoid); x)
-- /Source
def unaryBang (op : UnaryOp) (x a : BigInt) : Jl BigInt :=
  match op with
  | .neg => pure (writeValue x (-a.val))
  | .com => pure (writeValue x (-a.val-1))
  | .set => pure (writeValue x a.val)
  | .sqrt => if a.val < 0 then .error .divideError
    else pure (writeValue x (Nat.sqrt a.val.toNat))
-- Source: base/gmp.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a::BigInt) = $op!(BigInt(), a)
-- /Source
def unary (op : UnaryOp) (a : BigInt) := unaryBang op initBigInt a
-- Source: base/gmp.jl:224-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @eval $op!(x::BigInt) = $op!(x, x)
-- /Source
def unaryInplace (op : UnaryOp) (x : BigInt) := unaryBang op x x

/--
GMP manual §5.9 `mpz_fac_ui`: https://gmplib.org/manual/Number-Theoretic-Functions

Julia source: base/gmp.jl:227-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fac_ui!(x::BigInt, a) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_fac_ui(x::mpz_t, a::Culong)::Cvoid); x)
fac_ui(a) = fac_ui!(BigInt(), a)
```
-/
-- Source: base/gmp.jl:227-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fac_ui!(x::BigInt, a) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_fac_ui(x::mpz_t, a::Culong)::Cvoid); x)
-- /Source
def facUiBang (x : BigInt) (a : Culong) := writeValue x (factorialNat a.val.toNat)
-- Source: base/gmp.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fac_ui(a) = fac_ui!(BigInt(), a)
-- /Source
def facUi (a : Culong) := facUiBang initBigInt a

/--
GMP manual §5.2 `mpz_set_ui`, `mpz_set_si`; `set_d` remains untranslated below: https://gmplib.org/manual/Assigning-Integers

Julia source: base/gmp.jl:230-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op, T) in ((:set_ui, Culong), (:set_si, Clong), (:set_d, Cdouble))
    op! = Symbol(op, :!)
    @eval begin
        $op!(x::BigInt, a) = (ccall($(gmpz(op)), Cvoid, (mpz_t, $T), x, a); x)
        $op(a) = $op!(BigInt(), a)
    end
end
```
-/
-- Source: base/gmp.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, a) = (ccall($(gmpz(op)), Cvoid, (mpz_t, $T), x, a); x)
-- /Source
def setUiBang (x : BigInt) (a : Culong) := writeValue x a.val
-- Source: base/gmp.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, a) = (ccall($(gmpz(op)), Cvoid, (mpz_t, $T), x, a); x)
-- /Source
def setSiBang (x : BigInt) (a : Clong) := writeValue x a.val
-- Source: base/gmp.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a) = $op!(BigInt(), a)
-- /Source
def setUi (a : Culong) := setUiBang initBigInt a
-- Source: base/gmp.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a) = $op!(BigInt(), a)
-- /Source
def setSi (a : Clong) := setSiBang initBigInt a

/--
GMP manual §5.11 `mpz_popcount`, §8 Low-level Functions `mpn_popcount`: https://gmplib.org/manual/Integer-Logic-and-Bit-Fiddling

Julia source: base/gmp.jl:238-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
popcount(a::BigInt) = Int(signed(ccall((:__gmpz_popcount, libgmp), Culong, (mpz_t,), a)))

mpn_popcount(d::Ptr{Limb}, s::Integer) = Int(ccall((:__gmpn_popcount, libgmp), Culong, (Ptr{Limb}, Csize_t), d, s))
mpn_popcount(a::BigInt) = mpn_popcount(a.d, abs(a.size))
```
-/
def popcount (a : BigInt) : Clong :=
  JInt.wrap .i64 (if a.val < 0 then -1 else (countBits a.val.toNat : Int))
-- Source: base/gmp.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mpn_popcount(d::Ptr{Limb}, s::Integer) = Int(ccall((:__gmpn_popcount, libgmp), Culong, (Ptr{Limb}, Csize_t), d, s))
-- /Source
def mpnPopcountLimbs (d : List Limb) (s : Clong) : Clong :=
  JInt.wrap .i64 (((d.take s.val.toNat).foldl (fun c l => c + countBits l.val.toNat) 0 : Nat) : Int)
-- Source: base/gmp.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mpn_popcount(a::BigInt) = mpn_popcount(a.d, abs(a.size))
-- /Source
def mpnPopcount (a : BigInt) := mpnPopcountLimbs a.d (JInt.wrap .i64 a.size.val.natAbs)

/--
GMP manual §5.6 `mpz_tdiv_qr`, quotient truncates towards zero: https://gmplib.org/manual/Integer-Division

Julia source: base/gmp.jl:243-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tdiv_qr!(x::BigInt, y::BigInt, a::BigInt, b::BigInt)
    Base.@cancel_check
    Base.@assume_effects :reset_safe @ccall libgmp.__gmpz_tdiv_qr(x::mpz_t, y::mpz_t, a::mpz_t, b::mpz_t)::Cvoid
    x, y
end
tdiv_qr(a::BigInt, b::BigInt) = tdiv_qr!(BigInt(), BigInt(), a, b)
```
-/
-- Source: base/gmp.jl:243-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function tdiv_qr!(x::BigInt, y::BigInt, a::BigInt, b::BigInt)
--     Base.@cancel_check
--     Base.@assume_effects :reset_safe @ccall libgmp.__gmpz_tdiv_qr(x::mpz_t, y::mpz_t, a::mpz_t, b::mpz_t)::Cvoid
--     x, y
-- end
-- /Source
def tdivQrBang (x y a b : BigInt) : Jl (BigInt × BigInt) := do
  let q ← binaryValue .tdivQ a.val b.val
  pure (writeValue x q, writeValue y (a.val-q*b.val))
-- Source: base/gmp.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- tdiv_qr(a::BigInt, b::BigInt) = tdiv_qr!(BigInt(), BigInt(), a, b)
-- /Source
def tdivQr (a b : BigInt) := tdivQrBang initBigInt initBigInt a b

/--
GMP manual §5.7 `mpz_powm`: negative exponent uses inverse, missing inverse raises divide-by-zero: https://gmplib.org/manual/Integer-Exponentiation

Julia source: base/gmp.jl:250-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
powm!(x::BigInt, a::BigInt, b::BigInt, c::BigInt) =
    (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_powm(x::mpz_t, a::mpz_t, b::mpz_t, c::mpz_t)::Cvoid); x)
powm(a::BigInt, b::BigInt, c::BigInt) = powm!(BigInt(), a, b, c)
powm!(x::BigInt, b::BigInt, c::BigInt) = powm!(x, x, b, c)
```
-/
def powModNat (a : Int) (exponent : Nat) (modulus : Int) : Int :=
  if h : exponent = 0 then 1 % modulus else
    let half := powModNat a (exponent/2) modulus
    let square := (half*half) % modulus
    if exponent % 2 = 1 then (square*a) % modulus else square
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

-- Source: base/gmp.jl:250-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- powm!(x::BigInt, a::BigInt, b::BigInt, c::BigInt) =
--     (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_powm(x::mpz_t, a::mpz_t, b::mpz_t, c::mpz_t)::Cvoid); x)
-- /Source
def powmBang (x a b c : BigInt) : Jl BigInt := do
  if c.val = 0 then throw .divideError
  let modulus := (c.val.natAbs : Int)
  let base ← if b.val < 0 then do
    let (inverse,status) ← invertBang initBigInt a c
    if status.val = 0 then throw .divideError
    pure inverse.val
    else pure a.val
  pure (writeValue x (powModNat (base % modulus) b.val.natAbs modulus))
-- Source: base/gmp.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- powm(a::BigInt, b::BigInt, c::BigInt) = powm!(BigInt(), a, b, c)
-- /Source
def powm (a b c : BigInt) := powmBang initBigInt a b c
-- Source: base/gmp.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- powm!(x::BigInt, b::BigInt, c::BigInt) = powm!(x, x, b, c)
-- /Source
def powmInplace (x b c : BigInt) := powmBang x x b c

/--
GMP manual §5.9 `mpz_gcdext`, including the documented coefficient normalization and exceptional cases: https://gmplib.org/manual/Number-Theoretic-Functions

Julia source: base/gmp.jl:255-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcdext!(x::BigInt, y::BigInt, z::BigInt, a::BigInt, b::BigInt)
    Base.@cancel_check
    Base.@assume_effects :reset_safe @ccall libgmp.__gmpz_gcdext(x::mpz_t, y::mpz_t, z::mpz_t, a::mpz_t, b::mpz_t)::Cvoid
    x, y, z
end
gcdext(a::BigInt, b::BigInt) = gcdext!(BigInt(), BigInt(), BigInt(), a, b)
```
-/
-- Source: base/gmp.jl:255-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcdext!(x::BigInt, y::BigInt, z::BigInt, a::BigInt, b::BigInt)
--     Base.@cancel_check
--     Base.@assume_effects :reset_safe @ccall libgmp.__gmpz_gcdext(x::mpz_t, y::mpz_t, z::mpz_t, a::mpz_t, b::mpz_t)::Cvoid
--     x, y, z
-- end
-- /Source
def gcdextBang (x y z a b : BigInt) : BigInt × BigInt × BigInt :=
  let (g,s,t) := gmpGcdext a.val b.val
  (writeValue x g, writeValue y s, writeValue z t)
-- Source: base/gmp.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gcdext(a::BigInt, b::BigInt) = gcdext!(BigInt(), BigInt(), BigInt(), a, b)
-- /Source
def gcdext (a b : BigInt) := gcdextBang initBigInt initBigInt initBigInt a b

/--
GMP manual §5.10 Comparison Functions: only the sign of the C result is specified: https://gmplib.org/manual/Integer-Comparisons

Julia source: base/gmp.jl:262-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(a::BigInt, b::BigInt) = Int(ccall((:__gmpz_cmp, libgmp), Cint, (mpz_t, mpz_t), a, b))
cmp_si(a::BigInt, b) = Int(ccall((:__gmpz_cmp_si, libgmp), Cint, (mpz_t, Clong), a, b))
cmp_ui(a::BigInt, b) = Int(ccall((:__gmpz_cmp_ui, libgmp), Cint, (mpz_t, Culong), a, b))
```
-/
def cmp (a b : BigInt) : Clong := JInt.wrap .i64 (sgn (a.val-b.val))
def cmpSi (a : BigInt) (b : Clong) : Clong := JInt.wrap .i64 (sgn (a.val-b.val))
def cmpUi (a : BigInt) (b : Culong) : Clong := JInt.wrap .i64 (sgn (a.val-b.val))

/--
GMP manual §8 Low-level Functions, `mpn_cmp`: https://gmplib.org/manual/Low_002dlevel-Functions

Julia source: base/gmp.jl:267-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mpn_cmp(a::Ptr{Limb}, b::Ptr{Limb}, c) = ccall((:__gmpn_cmp, libgmp), Cint, (Ptr{Limb}, Ptr{Limb}, Clong), a, b, c)
mpn_cmp(a::BigInt, b::BigInt, c) = mpn_cmp(a.d, b.d, c)
```
-/
def mpnCmpLimbs (a b : List Limb) (count : Clong) : Cint :=
  JInt.wrap .i32 (sgn ((limbMagnitude (a.take count.val.toNat) : Int) -
    (limbMagnitude (b.take count.val.toNat) : Int)))
def mpnCmp (a b : BigInt) (count : Clong) := mpnCmpLimbs a.d b.d count

/--
GMP manual §5.4 `mpz_get_str`, valid positive bases 2..62 (negative bases select uppercase letters): https://gmplib.org/manual/Converting-Integers

Julia source: base/gmp.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_str!(x, a, b::BigInt) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_get_str(x::Ptr{Cchar}, a::Cint, b::mpz_t)::Ptr{Cchar}); x)
```
-/
-- Source: base/gmp.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- get_str!(x, a, b::BigInt) = (Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_get_str(x::Ptr{Cchar}, a::Cint, b::mpz_t)::Ptr{Cchar}); x)
-- /Source
def getStr (base : Cint) (b : BigInt) : String :=
  let magnitude := renderMagnitude b.val.natAbs base.val.natAbs
  let magnitude := if base.val < 0 then String.ofList (magnitude.toList.map Char.toUpper) else magnitude
  (if b.val < 0 then "-" else "") ++ magnitude

def parseDigit (base : Nat) (c : Char) : Option Nat :=
  let n := c.toNat
  let d := if 48 ≤ n ∧ n ≤ 57 then some (n-48)
    else if 65 ≤ n ∧ n ≤ 90 then some (n-55)
    else if 97 ≤ n ∧ n ≤ 122 then some (n - if base ≤ 36 then 87 else 61)
    else none
  d.bind (fun d => if d < base then some d else none)

def cWhitespace (c : Char) : Bool := decide (c.toNat = 32 ∨ (9 ≤ c.toNat ∧ c.toNat ≤ 13))

def parseMagnitude (chars : List Char) (base : Nat) : Option Nat :=
  let digits := chars.filter (fun c => !cWhitespace c)
  if digits.isEmpty then none else
    digits.foldlM (fun acc c => (parseDigit base c).map (fun d => acc*base+d)) 0


/--
GMP manual §5.2 `mpz_set_str`, base 0 or 2..62, whitespace ignored and failure -1: https://gmplib.org/manual/Assigning-Integers

Julia source: base/gmp.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
set_str!(x::BigInt, a, b) = Int(begin Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_set_str(x::mpz_t, a::Ptr{UInt8}, b::Cint)::Cint) end)
```
-/
-- Source: base/gmp.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- set_str!(x::BigInt, a, b) = Int(begin Base.@cancel_check; Base.@assume_effects :reset_safe @ccall(libgmp.__gmpz_set_str(x::mpz_t, a::Ptr{UInt8}, b::Cint)::Cint) end)
-- /Source
def setStrBang (x : BigInt) (a : String) (base : Cint) : BigInt × Clong :=
  let chars := (a.toUTF8.toList.map (fun b => Char.ofNat b.toNat)).filter (fun c => !cWhitespace c)
  let (negative,chars) := match chars with
    | '-' :: tail => (true,tail)
    | _ => (false,chars)
  let (radix,chars) := if base.val = 0 then
    match chars with
    | '0' :: 'x' :: tail | '0' :: 'X' :: tail => (16,tail)
    | '0' :: 'b' :: tail | '0' :: 'B' :: tail => (2,tail)
    | '0' :: tail => (8,if tail.isEmpty then ['0'] else tail)
    | _ => (10,chars)
    else (base.val.toNat,chars)
  match parseMagnitude chars radix with
  | none => (x, JInt.wrap .i64 (-1))
  | some n => (writeValue x (if negative then -(n : Int) else n), JInt.wrap .i64 0)

/--
GMP manual §5.16 Integer Special Functions, `mpz_limbs_write`, `mpz_limbs_finish`: caller writes limbs before finishing: https://gmplib.org/manual/Integer-Special-Functions

Julia source: base/gmp.jl:286-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
limbs_write!(x::BigInt, a) = ccall((:__gmpz_limbs_write, libgmp), Ptr{Limb}, (mpz_t, Clong), x, a)
limbs_finish!(x::BigInt, a) = ccall((:__gmpz_limbs_finish, libgmp), Cvoid, (mpz_t, Clong), x, a)
```
-/
-- Source: base/gmp.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- limbs_write!(x::BigInt, a) = ccall((:__gmpz_limbs_write, libgmp), Ptr{Limb}, (mpz_t, Clong), x, a)
-- /Source
def limbsWrite (x : BigInt) (count : Clong) : BigInt :=
  { x with
    alloc := JInt.wrap .i32 (max x.alloc.val count.val)
    d := x.d ++ List.replicate (count.val.toNat-x.d.length) (JInt.wrap .u64 0) }
-- Source: base/gmp.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- limbs_finish!(x::BigInt, a) = ccall((:__gmpz_limbs_finish, libgmp), Cvoid, (mpz_t, Clong), x, a)
-- /Source
def limbsFinish (x : BigInt) (count : Clong) : BigInt :=
  let magnitude := limbMagnitude (x.d.take count.val.natAbs)
  let normalized := ofInt (if count.val < 0 then -(magnitude : Int) else magnitude)
  { normalized with alloc := x.alloc, d := x.d }

/--
GMP manual §5.11 `mpz_setbit`, `mpz_tstbit`, infinite two-complement representation: https://gmplib.org/manual/Integer-Logic-and-Bit-Fiddling

Julia source: base/gmp.jl:289-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setbit!(x, a) = (ccall((:__gmpz_setbit, libgmp), Cvoid, (mpz_t, bitcnt_t), x, a); x)
tstbit(a::BigInt, b) = ccall((:__gmpz_tstbit, libgmp), Cint, (mpz_t, bitcnt_t), a, b) % Bool
```
-/
-- Source: base/gmp.jl:289-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- setbit!(x, a) = (ccall((:__gmpz_setbit, libgmp), Cvoid, (mpz_t, bitcnt_t), x, a); x)
-- /Source
def setbitBang (x : BigInt) (a : Culong) : BigInt :=
  writeValue x (if bitAt x.val a.val.toNat then x.val else x.val + (2 : Int)^a.val.toNat)
def tstbit (a : BigInt) (b : Culong) : Bool := bitAt a.val b.val.toNat

end MPZ


/--
Julia source: base/gmp.jl:294-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const ZERO = BigInt()
const ONE  = BigInt()
const _ONE = Limb[1]
```
-/
def ZERO : BigInt := initBigInt
def ONE : BigInt := ofInt 1
def oneLimbs : List Limb := [JInt.wrap .u64 1]

/--
Julia source: base/gmp.jl:298-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Int128})  = BigInt
widen(::Type{UInt128}) = BigInt
widen(::Type{BigInt})  = BigInt

signed(x::BigInt) = x

BigInt(x::BigInt) = x
Signed(x::BigInt) = x
```
-/
inductive BigIntType where | type
  deriving DecidableEq, Repr
def widen128 (_signed : Bool) : BigIntType := .type
def widenBigInt : BigIntType := .type
def signed (x : BigInt) := x
def fromBigInt (x : BigInt) := x
def signedBigInt (x : BigInt) := x

/--
Julia source: base/gmp.jl:735-735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iszero(x::BigInt) = x.size == 0
```
-/
def iszero (x : BigInt) : Bool := decide (x.size.val = 0)
/--
Julia source: base/gmp.jl:749-749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnegative(x::BigInt) = x.size < 0
```
-/
def isnegative (x : BigInt) : Bool := decide (x.size.val < 0)
/--
Julia source: base/gmp.jl:750-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispositive(x::BigInt) = x.size > 0
```
-/
def ispositive (x : BigInt) : Bool := decide (x.size.val > 0)
def neg (x : BigInt) : BigInt := writeValue initBigInt (-x.val)
/--
Julia source: base/gmp.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flipsign!(x::BigInt, y::Integer) = (signbit(y) && (x.size = -x.size); x)
```
-/
def flipsignBang (x : BigInt) (negative : Bool) : BigInt :=
  if negative then { x with val := -x.val, size := -x.size } else x


/--
Julia source: base/gmp.jl:307-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse_internal(::Type{BigInt}, s::AbstractString, startpos::Int, endpos::Int, base_::Integer, raise::Bool)
    # don't make a copy in the common case where we are parsing a whole String
    bstr = startpos == firstindex(s) && endpos == lastindex(s) ? String(s) : String(SubString(s,startpos,endpos))

    sgn, base, i = Base.parseint_preamble(true,Int(base_),bstr,firstindex(bstr),ncodeunits(bstr))
    if !(2 <= base <= 62)
        raise && throw(ArgumentError("invalid base: base must be 2 ≤ base ≤ 62, got $base"))
        return nothing
    end
    if i == 0
        raise && throw(ArgumentError("premature end of integer: $(repr(bstr))"))
        return nothing
    end
    z = BigInt()
    if Base.containsnul(bstr)
        err = -1 # embedded NUL char (not handled correctly by GMP)
    else
        err = GC.@preserve bstr MPZ.set_str!(z, pointer(bstr)+(i-firstindex(bstr)), base)
    end
    if err != 0
        raise && throw(ArgumentError("invalid BigInt: $(repr(bstr))"))
        return nothing
    end
    flipsign!(z, sgn)
end
```
-/
def tryparseInternal {S B : Type}
    (firstIndex lastIndex : S → Clong) (wholeString : S → Jl String)
    (substring : S → Clong → Clong → Jl String) (baseToInt : B → Jl Clong)
    (parsePreamble : Bool → Clong → String → Clong → Clong → Jl (Bool × Clong × Clong))
    (s : S) (startpos endpos : Clong) (base : B) (raise : Bool) :
    Jl (Option BigInt) := do
  let bstr ← if startpos.val = (firstIndex s).val ∧ endpos.val = (lastIndex s).val then
    wholeString s else substring s startpos endpos
  let base ← baseToInt base
  let (negative,base,i) ← parsePreamble true base bstr (JInt.wrap .i64 1)
    (JInt.wrap .i64 (bstr.toUTF8.size : Int))
  if !(2 ≤ base.val ∧ base.val ≤ 62) then
    if raise then throw (.argumentError "invalid base") else return none
  if i.val = 0 then
    if raise then throw (.argumentError "premature end of integer") else return none
  let z := initBigInt
  let (z,err) := if bstr.toList.contains (Char.ofNat 0) then (z,JInt.wrap .i64 (-1))
    else MPZ.setStrBang z (String.ofList ((bstr.toUTF8.toList.drop (i.val-1).toNat).map (fun b => Char.ofNat b.toNat)))
      (JInt.wrap .i32 base.val)
  if err.val ≠ 0 then
    if raise then throw (.argumentError "invalid BigInt") else return none
  return some (flipsignBang z negative)

/--
Julia source: base/gmp.jl:333-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BigInt(x::Union{Clong,Int32}) = MPZ.set_si(x)
BigInt(x::Union{Culong,UInt32}) = MPZ.set_ui(x)
BigInt(x::Bool) = BigInt(UInt(x))
```
-/
-- Source: base/gmp.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::Union{Clong,Int32}) = MPZ.set_si(x)
-- /Source
def fromSignedLong (x : Clong) : BigInt := MPZ.setSi x
-- Source: base/gmp.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::Union{Culong,UInt32}) = MPZ.set_ui(x)
-- /Source
def fromUnsignedLong (x : Culong) : BigInt := MPZ.setUi x
-- Source: base/gmp.jl:335-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::Bool) = BigInt(UInt(x))
-- /Source
def fromBool (x : Bool) : BigInt := fromUnsignedLong (JInt.wrap .u64 (if x then 1 else 0))

structure IntegerInput (I : Type) (U : Type) where
  isbits : I → Bool
  fitsLong : I → Bool
  remLong : I → Clong
  ndigits2 : I → Clong
  negative : I → Bool
  negWrap : I → I
  unsigned : I → U
  lowLimb : U → Limb
  shiftRight : U → U

def fillLimbs {U : Type} (low : U → Limb) (shift : U → U) : Nat → U → List Limb
  | 0, _ => []
  | n+1, u => low u :: fillLimbs low shift n (shift u)


/--
Julia source: base/gmp.jl:347-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BigInt(x::Integer)
    # On 64-bit Windows, `Clong` is `Int32`, not `Int64`, so construction of
    # `Int64` constants, e.g. `BigInt(3)`, uses this method.
    isbits(x) && typemin(Clong) <= x <= typemax(Clong) && return BigInt((x % Clong)::Clong)
    nd = ndigits(x, base=2)
    z = MPZ.realloc2(nd)
    ux = unsigned(x < 0 ? -%(x) : x)
    size = 0
    limbnbits = sizeof(Limb) << 3
    while nd > 0
        size += 1
        unsafe_store!(z.d, ux % Limb, size)
        ux >>= limbnbits
        nd -= limbnbits
    end
    z.size = x < 0 ? -size : size
    z
end
```
-/
-- Source: base/gmp.jl:347-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function BigInt(x::Integer)
--     # On 64-bit Windows, `Clong` is `Int32`, not `Int64`, so construction of
--     # `Int64` constants, e.g. `BigInt(3)`, uses this method.
--     isbits(x) && typemin(Clong) <= x <= typemax(Clong) && return BigInt((x % Clong)::Clong)
--     nd = ndigits(x, base=2)
--     z = MPZ.realloc2(nd)
--     ux = unsigned(x < 0 ? -%(x) : x)
--     size = 0
--     limbnbits = sizeof(Limb) << 3
--     while nd > 0
--         size += 1
--         unsafe_store!(z.d, ux % Limb, size)
--         ux >>= limbnbits
--         nd -= limbnbits
--     end
--     z.size = x < 0 ? -size : size
--     z
-- end
-- /Source
def fromInteger {I U : Type} (ops : IntegerInput I U) (x : I) : BigInt :=
  if ops.isbits x && ops.fitsLong x then fromSignedLong (ops.remLong x) else
    let nd := ops.ndigits2 x
    let z := MPZ.realloc (JInt.wrap .u64 nd.val)
    let ux := ops.unsigned (if ops.negative x then ops.negWrap x else x)
    let limbs := fillLimbs ops.lowLimb ops.shiftRight ((nd.val.toNat+63)/64) ux
    let count := Int.ofNat limbs.length
    let size := if ops.negative x then -count else count
    { z with val := if ops.negative x then -(limbMagnitude limbs : Int)
      else limbMagnitude limbs, size := JInt.wrap .i32 size, d := limbs }

def bitIntegerInput (t : IntTy) : IntegerInput (JInt t) Int where
  isbits := fun _ => true
  fitsLong := fun x => decide (IntTy.min .i64 ≤ x.val ∧ x.val ≤ IntTy.max .i64)
  remLong := fun x => JInt.wrap .i64 x.val
  ndigits2 := fun x => JInt.wrap .i64 (if x.val = 0 then 1 else (x.val.natAbs.log2+1 : Nat))
  negative := fun x => decide (x.val < 0)
  negWrap := Neg.neg
  unsigned := fun x => wrapInt t.toUnsigned x.val
  lowLimb := JInt.wrap .u64
  shiftRight := fun x => x / (2 : Int)^64

def fromBits {t : IntTy} (x : JInt t) := fromInteger (bitIntegerInput t) x

/--
Julia source: base/gmp.jl:367-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::BigInt, ::Type{Bool}) = !iszero(x) & unsafe_load(x.d) % Bool # never unsafe here

rem(x::BigInt, ::Type{T}) where T<:Union{SLimbMax,ULimbMax} =
    iszero(x) ? zero(T) : flipsign(unsafe_load(x.d) % T, x.size)

function rem(x::BigInt, ::Type{T}) where T<:Union{Base.BitUnsigned,Base.BitSigned}
    u = zero(T)
    for l = 1:min(abs(x.size), cld(sizeof(T), sizeof(Limb)))
        u += (unsafe_load(x.d, l) % T) << ((sizeof(Limb)<<3)*(l-1))
    end
    flipsign(u, x.size)
end
```
-/
def remBool (x : BigInt) : Bool :=
  !iszero x && decide (((x.d[0]?).getD (JInt.wrap .u64 0)).val % 2 = 1)

def remLimb (t : IntTy) (x : BigInt) : JInt t :=
  if iszero x then JInt.wrap t 0 else
    let low := JInt.wrap t ((x.d[0]?).getD (JInt.wrap .u64 0)).val
    if isnegative x then -low else low

def remBits (t : IntTy) (x : BigInt) : JInt t :=
  let n := min x.size.val.natAbs ((t.bits+63)/64)
  let u := (List.range n).foldl (fun u l =>
    u + JInt.wrap t (((x.d[l]?).getD (JInt.wrap .u64 0)).val * (2 : Int)^(64*l)))
    (JInt.wrap t 0)
  if isnegative x then -u else u

/--
Julia source: base/gmp.jl:380-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rem(x::Integer, ::Type{BigInt}) = BigInt(x)

clamp(x, ::Type{BigInt}) = convert(BigInt, x)

isodd(x::BigInt) = MPZ.tstbit(x, 0)
iseven(x::BigInt) = !isodd(x)

```
-/
def remToBigInt {I U : Type} (ops : IntegerInput I U) (x : I) := fromInteger ops x
def clampBigInt {X : Type} (convert : X → Jl BigInt) (x : X) := convert x
def isodd (x : BigInt) : Bool := MPZ.tstbit x (JInt.wrap .u64 0)
def iseven (x : BigInt) : Bool := !isodd x

/--
Julia source: base/gmp.jl:387-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (::Type{T})(x::BigInt) where T<:Base.BitUnsigned
    if sizeof(T) < sizeof(Limb)
        convert(T, convert(Limb,x))
    else
        0 <= x.size <= cld(sizeof(T),sizeof(Limb)) || throw(InexactError(nameof(T), T, x))
        x % T
    end
end

function (::Type{T})(x::BigInt) where T<:Base.BitSigned
    n = abs(x.size)
    if sizeof(T) < sizeof(Limb)
        SLimb = typeof(Signed(one(Limb)))
        convert(T, convert(SLimb, x))
    else
        0 <= n <= cld(sizeof(T),sizeof(Limb)) || throw(InexactError(nameof(T), T, x))
        y = x % T
        ispositive(x) ⊻ (y > 0) && throw(InexactError(nameof(T), T, x)) # catch overflow
        y
    end
end
```
-/
def convertUnsignedLarge (t : IntTy) (x : BigInt) : Jl (JInt t) :=
  if 0 ≤ x.size.val ∧ x.size.val ≤ ((t.bits+63)/64 : Nat) then pure (remBits t x)
  else .error (.inexactError t.name)

def convertSignedLarge (t : IntTy) (x : BigInt) : Jl (JInt t) := do
  let n := x.size.val.natAbs
  if n > (t.bits+63)/64 then throw (.inexactError t.name)
  let y := remBits t x
  if ispositive x != decide (y.val > 0) then throw (.inexactError t.name)
  pure y

def convertUnsigned (t : IntTy) (x : BigInt) : Jl (JInt t) := do
  if t.bits < 64 then
    let limb ← convertUnsignedLarge .u64 x
    JInt.convert t.name t limb.val
  else convertUnsignedLarge t x

def convertSigned (t : IntTy) (x : BigInt) : Jl (JInt t) := do
  if t.bits < 64 then
    let limb ← convertSignedLarge .i64 x
    JInt.convert t.name t limb.val
  else convertSignedLarge t x

def convertBits (t : IntTy) (x : BigInt) : Jl (JInt t) :=
  if t.signed then convertSigned t x else convertUnsigned t x

open JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

namespace MPZ


/--
GMP manual §5.2 `mpz_set_d`, truncation of a finite double: https://gmplib.org/manual/Assigning-Integers

Julia source: base/gmp.jl:230-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op, T) in ((:set_ui, Culong), (:set_si, Clong), (:set_d, Cdouble))
    op! = Symbol(op, :!)
    @eval begin
        $op!(x::BigInt, a) = (ccall($(gmpz(op)), Cvoid, (mpz_t, $T), x, a); x)
        $op(a) = $op!(BigInt(), a)
    end
end
```
-/
-- Source: base/gmp.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op!(x::BigInt, a) = (ccall($(gmpz(op)), Cvoid, (mpz_t, $T), x, a); x)
-- /Source
def setDBang (x : BigInt) (a : FV .f64) (_finite : a.isfinite = true) : BigInt :=
  writeValue x a.truncVal
-- Source: base/gmp.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a) = $op!(BigInt(), a)
-- /Source
def setD (a : FV .f64) (finite : a.isfinite = true) : BigInt :=
  setDBang initBigInt a finite

/--
GMP manual §5.10 `mpz_cmp_d`: ordered comparison, defined for non-NaN input: https://gmplib.org/manual/Integer-Comparisons

Julia source: base/gmp.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp_d(a::BigInt, b) = Int(ccall((:__gmpz_cmp_d, libgmp), Cint, (mpz_t, Cdouble), a, b))
```
-/
-- Source: base/gmp.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp_d(a::BigInt, b) = Int(ccall((:__gmpz_cmp_d, libgmp), Cint, (mpz_t, Cdouble), a, b))
-- /Source
def cmpD (a : BigInt) (b : FV .f64) : Clong :=
  if b.isinf then JInt.wrap .i64 (if b.signbit then 1 else -1)
  else
    let (n,d) := b.toRat
    JInt.wrap .i64 (sgn (a.val*(d : Int)-n))

end MPZ

/--
Julia source: base/gmp.jl:337-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_trunc(::Type{BigInt}, x::Union{Float16,Float32,Float64}) = MPZ.set_d(x)
```
-/
-- Source: base/gmp.jl:337-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_trunc(::Type{BigInt}, x::Union{Float16,Float32,Float64}) = MPZ.set_d(x)
-- /Source
def unsafeTruncFloat {T : FTy} (x : FV T)
    (finite : (convertFloat .f64 x).isfinite = true) : BigInt :=
  MPZ.setD (convertFloat .f64 x) finite

/--
Julia source: base/gmp.jl:339-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BigInt(x::Float64)
    isinteger(x) || throw(InexactError(:BigInt, BigInt, x))
    unsafe_trunc(BigInt,x)
end

BigInt(x::Float16) = BigInt(Float64(x))
BigInt(x::Float32) = BigInt(Float64(x))
```
-/
-- Source: base/gmp.jl:339-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function BigInt(x::Float64)
--     isinteger(x) || throw(InexactError(:BigInt, BigInt, x))
--     unsafe_trunc(BigInt,x)
-- end
-- /Source
def fromFloat64 (x : FV .f64) : Jl BigInt :=
  if h : x.isinteger = true then
    pure (MPZ.setD x (by
      have hh := h
      simp only [Fl.isinteger, Bool.and_eq_true] at hh
      exact hh.1))
  else .error (.inexactError "BigInt")
-- Source: base/gmp.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::Float16) = BigInt(Float64(x))
-- /Source
def fromFloat16 (x : FV .f16) : Jl BigInt := fromFloat64 (convertFloat .f64 x)
-- Source: base/gmp.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::Float32) = BigInt(Float64(x))
-- /Source
def fromFloat32 (x : FV .f32) : Jl BigInt := fromFloat64 (convertFloat .f64 x)

def roundsNearest : RoundingMode → Bool
  | .Nearest | .NearestTiesAway | .NearestTiesUp => true
  | _ => false

def roundsAway (r : RoundingMode) (negative : Bool) : Bool :=
  match r with
  | .FromZero => true
  | .Down => negative
  | .Up => !negative
  | _ => false

def loadLimb (x : BigInt) (i : Nat) : Nat :=
  ((x.d[i]?).getD (JInt.wrap .u64 0)).val.toNat

def fillWindow (x : BigInt) : Nat → Nat → Nat → Nat × Nat × Nat
  | 0, m, filled => (m,filled,0)
  | i+1, m, filled =>
    if filled+64 ≤ 64 then
      fillWindow x i ((m*2^64+loadLimb x i) % 2^64) (filled+64)
    else (m,filled,i+1)


/--
Julia source: base/gmp.jl:409-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Correctly rounded conversion to `T` under any rounding mode. The result is computed
# directly from the limbs of `x` so that only a single rounding step ever happens.
function (::Type{T})(x::BigInt, r::RoundingMode) where T<:IEEEFloat
    xsize = abs(x.size)
    xsize == 0 && return zero(T)
    sb = isnegative(x)
    top = unsafe_load(x.d, xsize)
    s = top_set_bit(top)
    nbits = s + (xsize - 1) * BITS_PER_LIMB # abs(x) is in [2^(nbits-1), 2^nbits)
    if nbits > exponent_max(T) + 1
        # abs(x) ≥ 2^(exponent_max(T) + 1), which is beyond the finite range of T
        overflow = rounds_to_nearest(r)::Bool || rounds_away_from_zero(r, sb)::Bool
        u = overflow ? ieee754_representation(T, sb, Val(:inf)) : ieee754_representation(T, sb, Val(:omega))
        return reinterpret(T, u)
    end
    # Left-align the leading bits of abs(x) in the window m, and track whether any lower
    # bit is set. The window holds at least precision(T) + 1 bits and at least one limb.
    W = promote_type(Limb, uinttype(T))
    wbits = 8 * sizeof(W)
    m = top % W
    filled = s
    i = xsize - 1
    while i > 0 && filled + BITS_PER_LIMB <= wbits
        m = m << BITS_PER_LIMB | unsafe_load(x.d, i)
        filled += BITS_PER_LIMB
        i -= 1
    end
    sticky = false
    if i > 0 && filled < wbits
        l = unsafe_load(x.d, i)
        k = wbits - filled
        m = m << k | l >> (BITS_PER_LIMB - k)
        sticky = l << k != 0
        filled = wbits
        i -= 1
    end
    while !sticky && i > 0
        sticky = unsafe_load(x.d, i) != 0
        i -= 1
    end
    m <<= wbits - filled
    # round the leading precision(T) bits of m, using the bits below them
    p = precision(T)
    q = m >> (wbits - p)
    rest = m << p
    round_bit = rest >> (wbits - 1) != 0
    sticky |= rest << 1 != 0
    incr = if rounds_to_nearest(r)
        tie_up = tie_breaker_is_to_even(r) ? isodd(q) : tie_breaker_rounds_away_from_zero(r, sb)
        round_bit & (sticky | tie_up)
    else
        rounds_away_from_zero(r, sb)::Bool & (round_bit | sticky)
    end
    # a carry out of the significand correctly bumps the exponent, possibly up to infinity
    signif = q % uinttype(T) & significand_mask(T)
    u = ieee754_representation(T, sb, nbits - 1 + exponent_bias(T), signif) + incr
    return reinterpret(T, u)
end
```
-/
def toFloat (T : FTy) (x : BigInt) (r : RoundingMode) : FV T :=
  let xsize := x.size.val.natAbs
  if xsize = 0 then Fl.zero false else
    let sb := isnegative x
    let top := loadLimb x (xsize-1)
    let s := if top = 0 then 0 else top.log2+1
    let nbits := s+(xsize-1)*64
    if (nbits : Int) > (exponent_max T).val+1 then
      let overflow := roundsNearest r || roundsAway r sb
      let u := if overflow then ieee754_representation_inf T sb
        else ieee754_representation_omega T sb
      Fl.ofBits u.val.toNat
    else
      let (m,filled,i) := fillWindow x (xsize-1) top s
      let (m,filled,i,sticky) := if i > 0 ∧ filled < 64 then
        let l := loadLimb x (i-1)
        let k := 64-filled
        ((m*2^k + l / 2^(64-k)) % 2^64,64,i-1,decide ((l*2^k)%2^64 ≠ 0))
        else (m,filled,i,false)
      let sticky := (List.range i).foldl (fun st j => st || decide (loadLimb x j ≠ 0)) sticky
      let m := (m*2^(64-filled)) % 2^64
      let p := T.fmt.sb+1
      let q := m / 2^(64-p)
      let rest := (m*2^p) % 2^64
      let roundBit := decide (rest / 2^63 ≠ 0)
      let sticky := sticky || decide ((rest*2)%2^64 ≠ 0)
      let incr := if roundsNearest r then
        let tieUp := if r = .Nearest then decide (q%2 = 1)
          else if r = .NearestTiesAway then true else !sb
        roundBit && (sticky || tieUp)
        else roundsAway r sb && (roundBit || sticky)
      let signif : Nat := q % 2^T.fmt.sb
      let u := ieee754_representation T sb
        (JInt.wrap .i64 ((nbits : Int)-1+(exponent_bias T).val))
        (JInt.wrap T.uintTy (signif : Int))
      Fl.ofBits ((u.val.toNat + if incr then 1 else 0) % 2^(T.bytes*8))

/--
Julia source: base/gmp.jl:468-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float64(n::BigInt) = Float64(n, RoundNearest)
Float32(n::BigInt) = Float32(n, RoundNearest)
Float16(n::BigInt) = Float16(n, RoundNearest)
```
-/
def toFloat64 (n : BigInt) : FV .f64 := toFloat .f64 n .Nearest
def toFloat32 (n : BigInt) : FV .f32 := toFloat .f32 n .Nearest
def toFloat16 (n : BigInt) : FV .f16 := toFloat .f16 n .Nearest

/--
GMP manual §5.4 `mpz_get_d`, truncating conversion: https://gmplib.org/manual/Converting-Integers

Julia source: base/gmp.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_d(a::BigInt) = ccall((:__gmpz_get_d, libgmp), Cdouble, (mpz_t,), a)
```
-/
def MPZ.getD (a : BigInt) : FV .f64 := toFloat .f64 a .ToZero

/--
Julia source: base/gmp.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{BigInt}, ::Type{<:Integer}) = BigInt
```
-/
def promoteRuleInteger : BigIntType := .type

/--
Julia source: base/gmp.jl:489-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(::Type{<:Integer})  = BigInt
big(::Type{<:Rational}) = Rational{BigInt}

big(n::Integer) = convert(BigInt, n)
```
-/
def bigIntegerType : BigIntType := .type
def bigRationalType {R : Type} (rationalType : BigIntType → R) : R := rationalType .type
def bigInteger {I U : Type} (ops : IntegerInput I U) (n : I) := fromInteger ops n

/--
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fJ, fC) in ((:+, :add), (:-,:sub), (:*, :mul),
                 (:+%, :add), (:-%,:sub), (:*%, :mul),
                 (:mod, :fdiv_r), (:rem, :tdiv_r),
                 (:gcd, :gcd), (:lcm, :lcm),
                 (:&, :and), (:|, :ior), (:xor, :xor))
    @eval begin
        ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
    end
end
```
-/
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def add (x y : BigInt) := MPZ.binary .add x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def sub (x y : BigInt) := MPZ.binary .sub x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def mul (x y : BigInt) := MPZ.binary .mul x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def addWrap (x y : BigInt) := MPZ.binary .add x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def subWrap (x y : BigInt) := MPZ.binary .sub x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def mulWrap (x y : BigInt) := MPZ.binary .mul x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def mod (x y : BigInt) := MPZ.binary .fdivR x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def rem (x y : BigInt) := MPZ.binary .tdivR x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def gcd (x y : BigInt) := MPZ.binary .gcd x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def lcm (x y : BigInt) := MPZ.binary .lcm x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def bitand (x y : BigInt) := MPZ.binary .and x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def bitor (x y : BigInt) := MPZ.binary .ior x y
-- Source: base/gmp.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(x::BigInt, y::BigInt) = MPZ.$fC(x, y)
-- /Source
def bitxor (x y : BigInt) := MPZ.binary .xor x y

/--
Julia source: base/gmp.jl:505-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (r, f) in ((RoundToZero, :tdiv_q),
               (RoundDown, :fdiv_q),
               (RoundUp, :cdiv_q))
    @eval div(x::BigInt, y::BigInt, ::typeof($r)) = MPZ.$f(x, y)
end
```
-/
inductive DivisionMode where | toZero | down | up
  deriving DecidableEq, Repr
-- Source: base/gmp.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @eval div(x::BigInt, y::BigInt, ::typeof($r)) = MPZ.$f(x, y)
-- /Source
def divRound (x y : BigInt) (r : DivisionMode) : Jl BigInt :=
  MPZ.binary (match r with | .toZero => .tdivQ | .down => .fdivQ | .up => .cdivQ) x y

/--
Julia source: base/gmp.jl:512-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::BigInt, y::BigInt) = div(x, y, RoundToZero)
fld(x::BigInt, y::BigInt) = div(x, y, RoundDown)
cld(x::BigInt, y::BigInt) = div(x, y, RoundUp)
```
-/
-- Source: base/gmp.jl:512-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- div(x::BigInt, y::BigInt) = div(x, y, RoundToZero)
-- /Source
def div (x y : BigInt) := divRound x y .toZero
-- Source: base/gmp.jl:513-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fld(x::BigInt, y::BigInt) = div(x, y, RoundDown)
-- /Source
def fld (x y : BigInt) := divRound x y .down
-- Source: base/gmp.jl:514-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cld(x::BigInt, y::BigInt) = div(x, y, RoundUp)
-- /Source
def cld (x y : BigInt) := divRound x y .up

/--
Julia source: base/gmp.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(x::BigInt, y::BigInt) = float(x)/float(y)
```
-/
def divide {F : Type} (float : BigInt → Jl F) (divide : F → F → Jl F)
    (x y : BigInt) : Jl F := do
  let fx ← float x
  let fy ← float y
  divide fx fy

/--
Julia source: base/gmp.jl:518-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invmod(x::BigInt, y::BigInt)
    z = zero(BigInt)
    ya = abs(y)
    if ya == 1
        return z
    end
    if (y==0 || MPZ.invert!(z, x, ya) == 0)
        throw(DomainError(y))
    end
    # GMP always returns a positive inverse; we instead want to
    # normalize such that div(z, y) == 0, i.e. we want a negative z
    # when y is negative.
    if y < 0
        MPZ.add!(z, y)
    end
    # The postcondition is: mod(z * x, y) == mod(big(1), y) && div(z, y) == 0
    return z
end
```
-/
-- Source: base/gmp.jl:518-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function invmod(x::BigInt, y::BigInt)
--     z = zero(BigInt)
--     ya = abs(y)
--     if ya == 1
--         return z
--     end
--     if (y==0 || MPZ.invert!(z, x, ya) == 0)
--         throw(DomainError(y))
--     end
--     # GMP always returns a positive inverse; we instead want to
--     # normalize such that div(z, y) == 0, i.e. we want a negative z
--     # when y is negative.
--     if y < 0
--         MPZ.add!(z, y)
--     end
--     # The postcondition is: mod(z * x, y) == mod(big(1), y) && div(z, y) == 0
--     return z
-- end
-- /Source
def invmod (x y : BigInt) : Jl BigInt := do
  let z := ofInt 0
  let ya := ofInt (y.val.natAbs : Int)
  if ya.val = 1 then return z
  if y.val = 0 then throw (.domainError "invmod")
  let (z,status) ← MPZ.invertBang z x ya
  if status.val = 0 then throw (.domainError "invmod")
  if y.val < 0 then MPZ.binaryInplace .add z y else pure z

/--
Julia source: base/gmp.jl:538-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fJ, fC) in ((:+, :add), (:*, :mul), (:&, :and), (:|, :ior), (:xor, :xor))
    fC! = Symbol(fC, :!)
    @eval begin
        ($fJ)(a::BigInt, b::BigInt, c::BigInt) = MPZ.$fC!(MPZ.$fC(a, b), c)
        ($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt) = MPZ.$fC!(MPZ.$fC!(MPZ.$fC(a, b), c), d)
        ($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt, e::BigInt) =
            MPZ.$fC!(MPZ.$fC!(MPZ.$fC!(MPZ.$fC(a, b), c), d), e)
    end
end
```
-/
-- Source: base/gmp.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(a::BigInt, b::BigInt, c::BigInt) = MPZ.$fC!(MPZ.$fC(a, b), c)
-- /Source
def commutative3 (op : MPZ.BinaryOp) (a b c : BigInt) : Jl BigInt := do
  MPZ.binaryInplace op (← MPZ.binary op a b) c
-- Source: base/gmp.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt) = MPZ.$fC!(MPZ.$fC!(MPZ.$fC(a, b), c), d)
-- /Source
def commutative4 (op : MPZ.BinaryOp) (a b c d : BigInt) : Jl BigInt := do
  MPZ.binaryInplace op (← commutative3 op a b c) d
-- Source: base/gmp.jl:543-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt, e::BigInt) =
--             MPZ.$fC!(MPZ.$fC!(MPZ.$fC!(MPZ.$fC(a, b), c), d), e)
-- /Source
def commutative5 (op : MPZ.BinaryOp) (a b c d e : BigInt) : Jl BigInt := do
  MPZ.binaryInplace op (← commutative4 op a b c d) e

/--
Julia source: base/gmp.jl:549-563 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::BigInt, c::CulongMax) = MPZ.add_ui(x, c)
+(c::CulongMax, x::BigInt) = x + c

-(x::BigInt, c::CulongMax) = MPZ.sub_ui(x, c)
-(c::CulongMax, x::BigInt) = MPZ.ui_sub(c, x)

+(x::BigInt, c::ClongMax) = c < 0 ? -(x, -%(c % Culong)) : x + convert(Culong, c)
+(c::ClongMax, x::BigInt) = c < 0 ? -(x, -%(c % Culong)) : x + convert(Culong, c)
-(x::BigInt, c::ClongMax) = c < 0 ? +(x, -%(c % Culong)) : -(x, convert(Culong, c))
-(c::ClongMax, x::BigInt) = c < 0 ? -(x + -%(c % Culong)) : -(convert(Culong, c), x)

*(x::BigInt, c::CulongMax) = MPZ.mul_ui(x, c)
*(c::CulongMax, x::BigInt) = x * c
*(x::BigInt, c::ClongMax) = MPZ.mul_si(x, c)
*(c::ClongMax, x::BigInt) = x * c
```
-/
def addUnsigned (x : BigInt) (c : Culong) := MPZ.unsigned .add x c
def unsignedAdd (c : Culong) (x : BigInt) := addUnsigned x c
def subUnsigned (x : BigInt) (c : Culong) := MPZ.unsigned .sub x c
def unsignedSub (c : Culong) (x : BigInt) := MPZ.uiSub c x

def addSigned (x : BigInt) (c : Clong) : BigInt :=
  if c.val < 0 then subUnsigned x (-(JInt.rem .u64 c))
  else addUnsigned x (JInt.wrap .u64 c.val)
def signedAdd (c : Clong) (x : BigInt) : BigInt :=
  if c.val < 0 then subUnsigned x (-(JInt.rem .u64 c))
  else addUnsigned x (JInt.wrap .u64 c.val)
def subSigned (x : BigInt) (c : Clong) : BigInt :=
  if c.val < 0 then addUnsigned x (-(JInt.rem .u64 c))
  else subUnsigned x (JInt.wrap .u64 c.val)
def signedSub (c : Clong) (x : BigInt) : BigInt :=
  if c.val < 0 then neg (addUnsigned x (-(JInt.rem .u64 c)))
  else unsignedSub (JInt.wrap .u64 c.val) x

def mulUnsigned (x : BigInt) (c : Culong) := MPZ.unsigned .mul x c
def unsignedMul (c : Culong) (x : BigInt) := mulUnsigned x c
def mulSigned (x : BigInt) (c : Clong) := MPZ.mulSi x c
def signedMul (c : Clong) (x : BigInt) := mulSigned x c

/--
Julia source: base/gmp.jl:565-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(x::BigInt, y::Union{ClongMax,CulongMax}) = float(x)/y
/(x::Union{ClongMax,CulongMax}, y::BigInt) = x/float(y)
```
-/
def divideMixedRightM {m : Type → Type} [Monad m] {I F R : Type}
    (float : BigInt → m F) (divide : F → I → m R) (x : BigInt) (y : I) : m R := do
  divide (← float x) y
def divideMixedLeftM {m : Type → Type} [Monad m] {I F R : Type}
    (float : BigInt → m F) (divide : I → F → m R) (x : I) (y : BigInt) : m R := do
  divide x (← float y)

def divideMixedRight {I F R : Type} (float : BigInt → Jl F)
    (divide : F → I → Jl R) (x : BigInt) (y : I) : Jl R :=
  divideMixedRightM float divide x y
def divideMixedLeft {I F R : Type} (float : BigInt → Jl F)
    (divide : I → F → Jl R) (x : I) (y : BigInt) : Jl R :=
  divideMixedLeftM float divide x y

/--
Julia source: base/gmp.jl:569-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::BigInt) = MPZ.neg(x)
(~)(x::BigInt) = MPZ.com(x)

<<(x::BigInt, c::UInt) = c == 0 ? x : MPZ.mul_2exp(x, c)
>>(x::BigInt, c::UInt) = c == 0 ? x : MPZ.fdiv_q_2exp(x, c)
>>>(x::BigInt, c::UInt) = x >> c
```
-/
-- Source: base/gmp.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (-)(x::BigInt) = MPZ.neg(x)
-- /Source
def unaryNeg (x : BigInt) := MPZ.unary .neg x
-- Source: base/gmp.jl:570-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (~)(x::BigInt) = MPZ.com(x)
-- /Source
def complement (x : BigInt) := MPZ.unary .com x
-- Source: base/gmp.jl:572-572 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <<(x::BigInt, c::UInt) = c == 0 ? x : MPZ.mul_2exp(x, c)
-- /Source
def shiftLeft (x : BigInt) (c : Culong) : BigInt :=
  if c.val = 0 then x else MPZ.unsigned .mul2exp x c
-- Source: base/gmp.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- >>(x::BigInt, c::UInt) = c == 0 ? x : MPZ.fdiv_q_2exp(x, c)
-- /Source
def shiftRight (x : BigInt) (c : Culong) : BigInt :=
  if c.val = 0 then x else MPZ.unsigned .fdivQ2exp x c
-- Source: base/gmp.jl:574-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- >>>(x::BigInt, c::UInt) = x >> c
-- /Source
def logicalShiftRight (x : BigInt) (c : Culong) := shiftRight x c

/--
Julia source: base/gmp.jl:576-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function trailing_zeros(x::BigInt)
    c = MPZ.scan1(x, 0)
    c == -1 && throw(DomainError(x, "`x` must be non-zero"))
    c
end

function trailing_ones(x::BigInt)
    c = MPZ.scan0(x, 0)
    c == -1 && throw(DomainError(x, "`x` must not be equal to -1"))
    c
end

function count_ones(x::BigInt)
    c = MPZ.popcount(x)
    c == -1 && throw(DomainError(x, "`x` cannot be negative"))
    c
end

# generic definition is not used to provide a better error message
function count_zeros(x::BigInt)
    c = MPZ.popcount(~x)
    c == -1 && throw(DomainError(x, "`x` must be negative"))
    c
end
```
-/
def trailingZeros (x : BigInt) : Jl Clong := do
  let c := MPZ.scan true x (JInt.wrap .u64 0)
  if c.val = -1 then throw (.domainError "`x` must be non-zero")
  pure c
def trailingOnes (x : BigInt) : Jl Clong := do
  let c := MPZ.scan false x (JInt.wrap .u64 0)
  if c.val = -1 then throw (.domainError "`x` must not be equal to -1")
  pure c
def countOnes (x : BigInt) : Jl Clong := do
  let c := MPZ.popcount x
  if c.val = -1 then throw (.domainError "`x` cannot be negative")
  pure c
-- Source: base/gmp.jl:595-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function count_zeros(x::BigInt)
--     c = MPZ.popcount(~x)
--     c == -1 && throw(DomainError(x, "`x` must be negative"))
--     c
-- end
-- /Source
def countZeros (x : BigInt) : Jl Clong := do
  let c := MPZ.popcount (← complement x)
  if c.val = -1 then throw (.domainError "`x` must be negative")
  pure c

/--
Julia source: base/gmp.jl:601-623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    count_ones_abs(x::BigInt)

Number of ones in the binary representation of abs(x).
"""
count_ones_abs(x::BigInt) = iszero(x) ? 0 : MPZ.mpn_popcount(x)

# all uses of _bit_magnitude MUST ensure at callsite that `x` is nonzero, otherwise it is UB
function _bit_magnitude(x::BigInt)
    n = abs(x.size)
    return n * sizeof(Limb) << 3 - leading_zeros(GC.@preserve x unsafe_load(x.d, n))
end

function exponent(x::BigInt)
    iszero(x) && throw(DomainError(x, "cannot be zero"))
    return _bit_magnitude(x) - 1
end

function top_set_bit(x::BigInt)
    isnegative(x) && throw(DomainError(x, "top_set_bit only supports negative arguments when they have type BitSigned."))
    iszero(x) && return 0
    return _bit_magnitude(x)
end
```
-/
def countOnesAbs (x : BigInt) : Clong :=
  if iszero x then JInt.wrap .i64 0 else MPZ.mpnPopcount x

def bitMagnitude (x : BigInt) : Clong :=
  let n := x.size.val.natAbs
  let top := loadLimb x (n-1)
  let leading := if top = 0 then 64 else 63-top.log2
  JInt.wrap .i64 ((n*64 : Nat)-leading : Int)

def exponent (x : BigInt) : Jl Clong :=
  if iszero x then .error (.domainError "cannot be zero")
  else pure (bitMagnitude x - JInt.wrap .i64 1)

def topSetBit (x : BigInt) : Jl Clong :=
  if isnegative x then .error (.domainError "top_set_bit")
  else if iszero x then pure (JInt.wrap .i64 0) else pure (bitMagnitude x)

/--
Julia source: base/gmp.jl:625-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
divrem(x::BigInt, y::BigInt,  ::typeof(RoundToZero) = RoundToZero) = MPZ.tdiv_qr(x, y)
divrem(x::BigInt, y::Integer, ::typeof(RoundToZero) = RoundToZero) = MPZ.tdiv_qr(x, BigInt(y))
```
-/
-- Source: base/gmp.jl:625-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- divrem(x::BigInt, y::BigInt,  ::typeof(RoundToZero) = RoundToZero) = MPZ.tdiv_qr(x, y)
-- /Source
def divrem (x y : BigInt) := MPZ.tdivQr x y
-- Source: base/gmp.jl:626-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- divrem(x::BigInt, y::Integer, ::typeof(RoundToZero) = RoundToZero) = MPZ.tdiv_qr(x, BigInt(y))
-- /Source
def divremInteger {I B R : Type} (construct : I → Jl B)
    (quotientRemainder : BigInt → B → Jl R) (x : BigInt) (y : I) : Jl R := do
  quotientRemainder x (← construct y)

/--
Julia source: base/gmp.jl:628-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(x::BigInt, y::BigInt) = sign(MPZ.cmp(x, y))
cmp(x::BigInt, y::ClongMax) = sign(MPZ.cmp_si(x, y))
cmp(x::BigInt, y::CulongMax) = sign(MPZ.cmp_ui(x, y))
cmp(x::BigInt, y::Integer) = cmp(x, big(y))
cmp(x::Integer, y::BigInt) = -cmp(y, x)

cmp(x::BigInt, y::CdoubleMax) = isnan(y) ? -1 : sign(MPZ.cmp_d(x, y))
cmp(x::CdoubleMax, y::BigInt) = -cmp(y, x)

isqrt(x::BigInt) = MPZ.sqrt(x)
```
-/
def cmp (x y : BigInt) : Clong := JInt.wrap .i64 (sgn (MPZ.cmp x y).val)
def cmpSigned (x : BigInt) (y : Clong) : Clong := JInt.wrap .i64 (sgn (MPZ.cmpSi x y).val)
def cmpUnsigned (x : BigInt) (y : Culong) : Clong := JInt.wrap .i64 (sgn (MPZ.cmpUi x y).val)
def cmpInteger {I U : Type} (ops : IntegerInput I U) (x : BigInt) (y : I) :=
  cmp x (fromInteger ops y)
def integerCmp {I U : Type} (ops : IntegerInput I U) (x : I) (y : BigInt) :=
  -(cmpInteger ops y x)
def cmpFloat {T : FTy} (x : BigInt) (y : FV T) : Clong :=
  if y.isnan then JInt.wrap .i64 (-1)
  else JInt.wrap .i64 (sgn (MPZ.cmpD x (convertFloat .f64 y)).val)
def floatCmp {T : FTy} (x : FV T) (y : BigInt) := -(cmpFloat y x)
-- Source: base/gmp.jl:637-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isqrt(x::BigInt) = MPZ.sqrt(x)
-- /Source
def isqrt (x : BigInt) := MPZ.unary .sqrt x

/--
Julia source: base/gmp.jl:639-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::BigInt, y::Culong) = MPZ.pow_ui(x, y)
```
-/
-- Source: base/gmp.jl:639-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::BigInt, y::Culong) = MPZ.pow_ui(x, y)
-- /Source
def powUnsigned (x : BigInt) (y : Culong) := MPZ.unsigned .pow x y

/--
Julia source: base/gmp.jl:641-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bigint_pow(x::BigInt, y::Integer)
    x == 1 && return x
    x == -1 && return isodd(y) ? x : -x
    if y<0; throw(DomainError(y, "`y` cannot be negative.")); end
    @noinline throw1(y) =
        throw(OverflowError("exponent $y is too large and computation will overflow"))
    if y>typemax(Culong)
       x==0 && return x

       #At this point, x is not 1, 0 or -1 and it is not possible to use
       #gmpz_pow_ui to compute the answer. Note that the magnitude of the
       #answer is:
       #- at least 2^(2^32-1) ≈ 10^(1.3e9) (if Culong === UInt32).
       #- at least 2^(2^64-1) ≈ 10^(5.5e18) (if Culong === UInt64).
       #
       #Assume that the answer will definitely overflow.

       throw1(y)
    end
    return x^convert(Culong, y)
end
```
-/
-- Source: base/gmp.jl:645-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @noinline throw1(y) =
--         throw(OverflowError("exponent $y is too large and computation will overflow"))
-- /Source
def bigintPowThrow1 {I A : Type} (_y : I) : Jl A :=
  .error (.overflowError "exponent is too large")

def bigintPow {I : Type} (value : I → Int) (odd : I → Bool) (y : I)
    (x : BigInt) : Jl BigInt := do
  if x.val = 1 then return x
  if x.val = -1 then return if odd y then x else neg x
  if value y < 0 then throw (.domainError "`y` cannot be negative.")
  if value y > IntTy.max .u64 then
    if x.val = 0 then return x
    bigintPowThrow1 y
  return powUnsigned x (JInt.wrap .u64 (value y))

/--
Julia source: base/gmp.jl:663-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::BigInt , y::BigInt ) = bigint_pow(x, y)
^(x::BigInt , y::Bool   ) = y ? x : one(x)
^(x::BigInt , y::Integer) = bigint_pow(x, y)
^(x::Integer, y::BigInt ) = bigint_pow(BigInt(x), y)
^(x::Bool   , y::BigInt ) = Base.power_by_squaring(x, y)
```
-/
-- Source: base/gmp.jl:663-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::BigInt , y::BigInt ) = bigint_pow(x, y)
-- /Source
def powBigInt (x y : BigInt) := bigintPow BigInt.val isodd y x
-- Source: base/gmp.jl:664-664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::BigInt , y::Bool   ) = y ? x : one(x)
-- /Source
def powBool (x : BigInt) (y : Bool) := if y then x else ofInt 1
-- Source: base/gmp.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::BigInt , y::Integer) = bigint_pow(x, y)
-- /Source
def powInteger {I R : Type} (power : BigInt → I → Jl R)
    (x : BigInt) (y : I) : Jl R := power x y
-- Source: base/gmp.jl:666-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::Integer, y::BigInt ) = bigint_pow(BigInt(x), y)
-- /Source
def integerPowBigInt {I B R : Type} (construct : I → Jl B)
    (power : B → BigInt → Jl R) (x : I) (y : BigInt) : Jl R := do
  power (← construct x) y
-- Source: base/gmp.jl:667-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(x::Bool   , y::BigInt ) = Base.power_by_squaring(x, y)
-- /Source
def boolPowBigInt (x : Bool) (y : BigInt) : Jl Bool :=
  JuliaLean.base.intfuncs.powerBool_Integer BigInt.val x y

/--
Julia source: base/gmp.jl:669-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function powermod(x::BigInt, p::BigInt, m::BigInt)
    r = MPZ.powm(x, p, m)
    return m < 0 && r > 0 ? MPZ.add!(r, m) : r # choose sign consistent with mod(x^p, m)
end

powermod(x::Integer, p::Integer, m::BigInt) = powermod(big(x), big(p), m)
```
-/
-- Source: base/gmp.jl:669-672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function powermod(x::BigInt, p::BigInt, m::BigInt)
--     r = MPZ.powm(x, p, m)
--     return m < 0 && r > 0 ? MPZ.add!(r, m) : r # choose sign consistent with mod(x^p, m)
-- end
-- /Source
def powermod (x p m : BigInt) : Jl BigInt := do
  let r ← MPZ.powm x p m
  if m.val < 0 ∧ r.val > 0 then MPZ.binaryInplace .add r m else pure r
-- Source: base/gmp.jl:674-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- powermod(x::Integer, p::Integer, m::BigInt) = powermod(big(x), big(p), m)
-- /Source
def powermodInteger {I P X Y R : Type} (bigX : I → Jl X) (bigP : P → Jl Y)
    (powerMod : X → Y → BigInt → Jl R) (x : I) (p : P) (m : BigInt) : Jl R := do
  let bx ← bigX x
  let bp ← bigP p
  powerMod bx bp m

/--
Julia source: base/gmp.jl:676-687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcdx(a::BigInt, b::BigInt)
    g, s, t = MPZ.gcdext(a, b)
    if t == 0
        # work around a difference in some versions of GMP
        if a == b
            return g, t, s
        elseif abs(a)==abs(b)
            return g, t, -s
        end
    end
    g, s, t
end
```
-/
-- Source: base/gmp.jl:676-687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcdx(a::BigInt, b::BigInt)
--     g, s, t = MPZ.gcdext(a, b)
--     if t == 0
--         # work around a difference in some versions of GMP
--         if a == b
--             return g, t, s
--         elseif abs(a)==abs(b)
--             return g, t, -s
--         end
--     end
--     g, s, t
-- end
-- /Source
def gcdx (a b : BigInt) : BigInt × BigInt × BigInt :=
  let (g,s,t) := MPZ.gcdext a b
  if t.val = 0 then
    if a.val = b.val then (g,t,s)
    else if a.val.natAbs = b.val.natAbs then (g,t,neg s)
    else (g,s,t)
  else (g,s,t)

/--
Julia source: base/gmp.jl:689-691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::BigInt, y::BigInt, rest::BigInt...) = sum(tuple(x, y, rest...))
sum(arr::Union{AbstractArray{BigInt}, Tuple{BigInt, Vararg{BigInt}}}) =
    foldl(MPZ.add!, arr; init=BigInt(0))
```
-/
-- Source: base/gmp.jl:690-691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sum(arr::Union{AbstractArray{BigInt}, Tuple{BigInt, Vararg{BigInt}}}) =
--     foldl(MPZ.add!, arr; init=BigInt(0))
-- /Source
def sum (arr : List BigInt) : Jl BigInt :=
  arr.foldlM (MPZ.binaryInplace .add) (ofInt 0)
-- Source: base/gmp.jl:689-689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::BigInt, y::BigInt, rest::BigInt...) = sum(tuple(x, y, rest...))
-- /Source
def addVariadic (x y : BigInt) (rest : List BigInt) : Jl BigInt := sum (x :: y :: rest)

/--
Julia source: base/gmp.jl:697-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prod(arr::AbstractArray{BigInt}, lo, hi)
    if hi - lo + 1 <= 16
        # compute first the needed number of bits for the result,
        # to avoid re-allocations
        nlimbs = 0
        for i in lo:hi
            nlimbs += abs(arr[i].size)
        end
        init = BigInt(; nbits=nlimbs*BITS_PER_LIMB)
        MPZ.set_si!(init, 1)
        for i in lo:hi
            MPZ.mul!(init, arr[i])
        end
        init
    else
        mid = (lo + hi) ÷ 2
        MPZ.mul!(_prod(arr, lo, mid), _prod(arr, mid+1, hi))
    end
end
```
-/
def productSegment (arr : List BigInt) : Jl BigInt :=
    if h : arr.length ≤ 16 then do
      let nlimbs := arr.foldl (fun n x => n + x.size.val.natAbs) 0
      let init := ofInt 0 (nlimbs*64)
      let init := MPZ.setSiBang init (JInt.wrap .i64 1)
      arr.foldlM (MPZ.binaryInplace .mul) init
    else do
      let middle := (arr.length+1)/2
      let left ← productSegment (arr.take middle)
      let right ← productSegment (arr.drop middle)
      MPZ.binaryInplace .mul left right
termination_by arr.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega


/--
Julia source: base/gmp.jl:693-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function prod(arr::AbstractArray{BigInt})
    any(iszero, arr) && return zero(BigInt)
    _prod(arr, firstindex(arr), lastindex(arr))
end
function _prod(arr::AbstractArray{BigInt}, lo, hi)
    if hi - lo + 1 <= 16
        # compute first the needed number of bits for the result,
        # to avoid re-allocations
        nlimbs = 0
        for i in lo:hi
            nlimbs += abs(arr[i].size)
        end
        init = BigInt(; nbits=nlimbs*BITS_PER_LIMB)
        MPZ.set_si!(init, 1)
        for i in lo:hi
            MPZ.mul!(init, arr[i])
        end
        init
    else
        mid = (lo + hi) ÷ 2
        MPZ.mul!(_prod(arr, lo, mid), _prod(arr, mid+1, hi))
    end
end
```
-/
def prod (arr : List BigInt) : Jl BigInt :=
  if arr.any iszero then pure (ofInt 0) else productSegment arr
def prodRange (arr : List BigInt) (lo hi : Clong) : Jl BigInt :=
  productSegment ((arr.drop (lo.val-1).toNat).take (hi.val-lo.val+1).toNat)

/--
Julia source: base/gmp.jl:717-717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
factorial(n::BigInt) = !isnegative(n) ? MPZ.fac_ui(n) : throw(DomainError(n, "`n` must not be negative."))
```
-/
-- Source: base/gmp.jl:717-717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- factorial(n::BigInt) = !isnegative(n) ? MPZ.fac_ui(n) : throw(DomainError(n, "`n` must not be negative."))
-- /Source
def factorial (n : BigInt) : Jl BigInt := do
  if isnegative n then throw (.domainError "`n` must not be negative.")
  let c ← convertUnsigned .u64 n
  pure (MPZ.facUi c)

def binomialLargeNonnegative (n k : BigInt) : Jl BigInt := do
  let κ ← sub n k
  if κ.val < 0 then return ofInt 0
  if κ.val ≤ IntTy.max .u64 then return MPZ.unsigned .bin n (JInt.wrap .u64 κ.val)
  throw (.overflowError "Computation would exceed memory")


/--
Julia source: base/gmp.jl:719-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function binomial(n::BigInt, k::Integer)
    k < 0 && return BigInt(0)
    k <= typemax(Culong) && return binomial(n, Culong(k))
    n < 0 && return isodd(k) ? -binomial(k - n - 1, k) : binomial(k - n - 1, k)
    κ = n - k
    κ < 0 && return BigInt(0)
    κ <= typemax(Culong) && return binomial(n, Culong(κ))
    throw(OverflowError("Computation would exceed memory"))
end
binomial(n::BigInt, k::Culong) = MPZ.bin_ui(n, k)
```
-/
def binomial {I U : Type} (ops : IntegerInput I U) (value : I → Int)
    (odd : I → Bool) (n : BigInt) (k : I) : Jl BigInt := do
  if value k < 0 then return ofInt 0
  if value k ≤ IntTy.max .u64 then return MPZ.unsigned .bin n (JInt.wrap .u64 (value k))
  let kb := fromInteger ops k
  if n.val < 0 then
    let transformed ← sub (← sub kb n) (ofInt 1)
    let result ← binomialLargeNonnegative transformed kb
    return if odd k then neg result else result
  binomialLargeNonnegative n kb

-- Source: base/gmp.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- binomial(n::BigInt, k::Culong) = MPZ.bin_ui(n, k)
-- /Source
def binomialUnsigned (n : BigInt) (k : Culong) := MPZ.unsigned .bin n k

/--
Julia source: base/gmp.jl:730-750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::BigInt, y::BigInt) = cmp(x,y) == 0
==(x::BigInt, i::Integer) = cmp(x,i) == 0
==(i::Integer, x::BigInt) = cmp(x,i) == 0
==(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) == 0
==(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) == 0
iszero(x::BigInt) = x.size == 0
isone(x::BigInt) = x == Culong(1)

<=(x::BigInt, y::BigInt) = cmp(x,y) <= 0
<=(x::BigInt, i::Integer) = cmp(x,i) <= 0
<=(i::Integer, x::BigInt) = cmp(x,i) >= 0
<=(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) <= 0
<=(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) >= 0

<(x::BigInt, y::BigInt) = cmp(x,y) < 0
<(x::BigInt, i::Integer) = cmp(x,i) < 0
<(i::Integer, x::BigInt) = cmp(x,i) > 0
<(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) < 0
<(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) > 0
isnegative(x::BigInt) = x.size < 0
ispositive(x::BigInt) = x.size > 0
```
-/
def equal (x y : BigInt) : Bool := decide ((cmp x y).val = 0)
def equalInteger {I U : Type} (ops : IntegerInput I U) (x : BigInt) (i : I) : Bool :=
  decide ((cmpInteger ops x i).val = 0)
def integerEqual {I U : Type} (ops : IntegerInput I U) (i : I) (x : BigInt) : Bool :=
  equalInteger ops x i

def equalFloat {T : FTy} (x : BigInt) (f : FV T) : Bool :=
  if f.isnan then false else decide ((cmpFloat x f).val = 0)
def floatEqual {T : FTy} (f : FV T) (x : BigInt) : Bool :=
  if f.isnan then false else decide ((cmpFloat x f).val = 0)

def isone (x : BigInt) : Bool := decide ((cmpUnsigned x (JInt.wrap .u64 1)).val = 0)
def lessEqual (x y : BigInt) : Bool := decide ((cmp x y).val ≤ 0)
def lessEqualInteger {I U : Type} (ops : IntegerInput I U) (x : BigInt) (i : I) : Bool :=
  decide ((cmpInteger ops x i).val ≤ 0)
def integerLessEqual {I U : Type} (ops : IntegerInput I U) (i : I) (x : BigInt) : Bool :=
  decide ((cmpInteger ops x i).val ≥ 0)
def lessEqualFloat {T : FTy} (x : BigInt) (f : FV T) : Bool :=
  if f.isnan then false else decide ((cmpFloat x f).val ≤ 0)
def floatLessEqual {T : FTy} (f : FV T) (x : BigInt) : Bool :=
  if f.isnan then false else decide ((cmpFloat x f).val ≥ 0)

def less (x y : BigInt) : Bool := decide ((cmp x y).val < 0)
def lessInteger {I U : Type} (ops : IntegerInput I U) (x : BigInt) (i : I) : Bool :=
  decide ((cmpInteger ops x i).val < 0)
def integerLess {I U : Type} (ops : IntegerInput I U) (i : I) (x : BigInt) : Bool :=
  decide ((cmpInteger ops x i).val > 0)
def lessFloat {T : FTy} (x : BigInt) (f : FV T) : Bool :=
  if f.isnan then false else decide ((cmpFloat x f).val < 0)
def floatLess {T : FTy} (f : FV T) (x : BigInt) : Bool :=
  if f.isnan then false else decide ((cmpFloat x f).val > 0)

/--
Julia source: base/gmp.jl:752-761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::BigInt) = isnegative(x)
flipsign!(x::BigInt, y::Integer) = (signbit(y) && (x.size = -x.size); x)
flipsign( x::BigInt, y::Integer) = signbit(y) ? -x : x
flipsign( x::BigInt, y::BigInt)  = signbit(y) ? -x : x
# above method to resolving ambiguities with flipsign(::T, ::T) where T<:Signed
function sign(x::BigInt)
    isnegative(x) && return -one(x)
    ispositive(x) && return one(x)
    return x
end
```
-/
def signbit (x : BigInt) := isnegative x
-- Source: base/gmp.jl:754-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign( x::BigInt, y::Integer) = signbit(y) ? -x : x
-- /Source
def flipsignInteger {I : Type} (signbit : I → Bool) (x : BigInt) (y : I) :=
  if signbit y then neg x else x
-- Source: base/gmp.jl:755-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign( x::BigInt, y::BigInt)  = signbit(y) ? -x : x
-- /Source
def flipsign (x y : BigInt) := if signbit y then neg x else x
-- Source: base/gmp.jl:757-761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sign(x::BigInt)
--     isnegative(x) && return -one(x)
--     ispositive(x) && return one(x)
--     return x
-- end
-- /Source
def sign (x : BigInt) :=
  if isnegative x then neg (ofInt 1)
  else if ispositive x then ofInt 1 else x

/--
Julia source: base/gmp.jl:765-782 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string(n::BigInt; base::Integer = 10, pad::Integer = 1)
    base < 0 && return Base._base(Int(base), n, pad, (base>0) & (n.size<0))
    2 <= base <= 62 || throw(ArgumentError("base must be 2 ≤ base ≤ 62, got $base"))
    iszero(n) && pad < 1 && return ""
    nd1 = ndigits(n, base=base)
    nd  = max(nd1, pad)
    str = Base._string_n(nd + isnegative(n))
    GC.@preserve str begin
        p = pointer(str)
        MPZ.get_str!(p + nd - nd1, base, n)
        pad_len = nd - nd1
        if pad_len > 0
            Base.memset(p + isnegative(n), UInt8('0'), pad_len)
        end
        isnegative(n) && unsafe_store!(p, UInt8('-'))
    end
    return str
end
```
-/
def string (negativeBase : Clong → BigInt → Clong → Bool → Jl String)
    (ndigits : BigInt → Clong → Jl Clong)
    (n : BigInt) (base : Clong := JInt.wrap .i64 10)
    (pad : Clong := JInt.wrap .i64 1) : Jl String := do
  if base.val < 0 then
    return ← negativeBase base n pad (decide (base.val > 0) && isnegative n)
  if !(2 ≤ base.val ∧ base.val ≤ 62) then throw (.argumentError "invalid base")
  if iszero n && decide (pad.val < 1) then return ""
  let nd1 ← ndigits n base
  let nd := max nd1.val pad.val
  let digits := MPZ.getStr (JInt.wrap .i32 base.val) n
  let padding := String.ofList (List.replicate (nd-nd1.val).toNat '0')
  if isnegative n then
    return "-" ++ padding ++ String.ofList (digits.toList.drop 1)
  else return padding ++ digits

/--
Julia source: base/gmp.jl:763-763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, x::BigInt) = print(io, string(x))
```
-/
def showBigInt {IO : Type} (string : BigInt → Jl String) (print : IO → String → Jl IO)
    (io : IO) (x : BigInt) : Jl IO := do print io (← string x)

structure DigitVector (T : Type) where
  data : List T
  firstIndex : Clong
  strided : Bool
  stride : Clong

inductive ExportError where
  | julia (error : JlError)
  | assertionError
  deriving Repr

def endianWord (t : IntTy) (bigEndian : Bool) (n : Nat) : JInt t :=
  let bytes := List.range (t.bits/8)
  let n := if bigEndian then bytes.foldl
    (fun result i => result*256 + n / 256^i % 256) 0 else n
  JInt.wrap t (n : Int)

namespace MPZ


/--
GMP manual §5.14 `mpz_export`, magnitude words, order, byte endian, nails, zero count: https://gmplib.org/manual/Integer-Import-and-Export

Julia source: base/gmp.jl:274-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function export!(a::AbstractVector{T}, n::BigInt; order::Integer=-1, nails::Integer=0, endian::Integer=0) where {T<:Base.BitInteger}
    stride(a, 1) == 1 || throw(ArgumentError("a must have stride 1"))
    ndigits = cld(sizeinbase(n, 2), 8*sizeof(T) - nails)
    length(a) < ndigits && resize!(a, ndigits)
    fill!(a, zero(T))
    count = Ref{Csize_t}()
    ccall((:__gmpz_export, libgmp), Ptr{T}, (Ptr{T}, Ref{Csize_t}, Cint, Csize_t, Cint, Csize_t, mpz_t),
        a, count, order, sizeof(T), endian, nails, n)
    @assert count[] ≤ length(a) "count[] > length(a)"
    return a, Int(count[])
end
```
-/
def exportWords (t : IntTy) (a : DigitVector (JInt t)) (n : BigInt)
    (mostSignificantFirst : Bool := false) (nails : Nat := 0)
    (bigEndian : Bool := false) : Except ExportError (DigitVector (JInt t) × Clong) := do
  if a.stride.val ≠ 1 then throw (.julia (.argumentError "a must have stride 1"))
  let bits := t.bits-nails
  let bitLength := if n.val = 0 then 1 else n.val.natAbs.log2+1
  let ndigits := (bitLength+bits-1)/bits
  let capacity := max a.data.length ndigits
  let count := if n.val = 0 then 0 else ndigits
  let words := (List.range count).map (fun i => endianWord t bigEndian
    (n.val.natAbs / 2^(bits*i) % 2^bits))
  let words := if mostSignificantFirst then words.reverse else words
  let output := words ++ List.replicate (capacity-count) (JInt.wrap t 0)
  if count > output.length then throw .assertionError
  return ({ a with data := output }, JInt.wrap .i64 (count : Int))

end MPZ

structure DigitOps (T : Type) where
  zero : T
  fromByte : Nat → Jl T
  neg : T → Jl T
  bitType : Option IntTy
  maxValue : Int
  exportWords : DigitVector T → BigInt → Nat → Except ExportError (DigitVector T × Clong)

def gmpDigitOps (t : IntTy) : DigitOps (JInt t) where
  zero := JInt.wrap t 0
  fromByte := fun n => JInt.convert t.name t (n : Int)
  neg := fun x => pure (-x)
  bitType := some t
  maxValue := t.max
  exportWords := fun a n nails => MPZ.exportWords t a n false nails false

def decodeOutputDigit (base : Int) (x : Char) : Nat :=
  let c := x.toNat
  if base ≤ 36 then (if c > 0x39 then c-0x57 else c-0x30)
  else if c > 0x39 then (if c > 0x60 then c-0x3d else c-0x37) else c-0x30

def powerOfTwo (n : Int) : Bool :=
  decide (n > 0) && decide (Nat.land n.toNat (n.toNat-1) = 0)


/--
Julia source: base/gmp.jl:784-810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function digits!(a::AbstractVector{T}, n::BigInt; base::Integer = 10) where {T<:Integer}
    if base ≥ 2
        if base ≤ 62
            # fast path using mpz_get_str via string(n; base)
            s = codeunits(string(n; base))
            i, j = firstindex(a)-1, length(s)+1
            lasti = min(lastindex(a), firstindex(a) + length(s)-1 - isnegative(n))
            while i < lasti
                # base ≤ 36: 0-9, plus a-z for 10-35
                # base > 36: 0-9, plus A-Z for 10-35 and a-z for 36..61
                x = s[j -= 1]
                a[i += 1] = base ≤ 36 ? (x>0x39 ? x-0x57 : x-0x30) : (x>0x39 ? (x>0x60 ? x-0x3d : x-0x37) : x-0x30)
            end
            lasti = lastindex(a)
            while i < lasti; a[i+=1] = zero(T); end
            return isnegative(n) ? map!(-,a,a) : a
        elseif a isa StridedVector{<:Base.BitInteger} && stride(a,1) == 1 && ispow2(base) && base-1 ≤ typemax(T)
            # fast path using mpz_export
            origlen = length(a)
            _, writelen = MPZ.export!(a, n; nails = 8sizeof(T) - trailing_zeros(base))
            length(a) != origlen && resize!(a, origlen) # truncate to least-significant digits
            a[begin+writelen:end] .= zero(T)
            return isnegative(n) ? map!(-,a,a) : a
        end
    end
    return invoke(digits!, Tuple{typeof(a), Integer}, a, n; base) # slow generic fallback
end
```
-/
def digitsBang {T : Type} (ops : DigitOps T)
    (string : BigInt → Clong → Jl String)
    (generic : DigitVector T → BigInt → Clong → Except ExportError (DigitVector T))
    (a : DigitVector T) (n : BigInt) (base : Clong := JInt.wrap .i64 10) :
    Except ExportError (DigitVector T) := do
  if base.val ≥ 2 then
    if base.val ≤ 62 then
      let s ← (string n base).mapError ExportError.julia
      let chars := s.toList.reverse
      let count := min a.data.length (chars.length - if isnegative n then 1 else 0)
      let values ← (chars.take count).mapM
        (fun c => (ops.fromByte (decodeOutputDigit base.val c)).mapError ExportError.julia)
      let values := values ++ List.replicate (a.data.length-count) ops.zero
      let values ← if isnegative n then values.mapM (fun x => (ops.neg x).mapError ExportError.julia)
        else pure values
      return { a with data := values }
    else if a.strided && decide (a.stride.val = 1) && powerOfTwo base.val &&
        decide (base.val-1 ≤ ops.maxValue) && ops.bitType.isSome then
      let origlen := a.data.length
      let bits := (scanBit base.val 0 true).toNat
      let width := (ops.bitType.getD .u64).bits
      let (a,writelen) ← ops.exportWords a n (width-bits)
      let data := a.data.take origlen
      let data := data.take writelen.val.toNat ++
        List.replicate (data.length-writelen.val.toNat) ops.zero
      let data ← if isnegative n then data.mapM (fun x => (ops.neg x).mapError ExportError.julia)
        else pure data
      return { a with data := data }
  generic a n base

/--
Julia source: base/gmp.jl:812-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ndigits0zpb(x::BigInt, b::Integer)
    b < 2 && throw(DomainError(b, "`b` cannot be less than 2."))
    x.size == 0 && return 0 # for consistency with other ndigits0z methods
    if ispow2(b) && 2 <= b <= 62 # GMP assumes b is in this range
        MPZ.sizeinbase(x, b)
    else
        # non-base 2 mpz_sizeinbase might return an answer 1 too big
        # use property that log(b, x) < ndigits(x, base=b) <= log(b, x) + 1
        n = MPZ.sizeinbase(x, 2)
        lb = log2(b) # assumed accurate to <1ulp (true for openlibm)
        q,r = divrem(n,lb)
        iq = Int(q)
        maxerr = q*eps(lb) # maximum error in remainder
        if r-1.0 < maxerr
            abs(x) >= big(b)^iq ? iq+1 : iq
        elseif lb-r < maxerr
            abs(x) >= big(b)^(iq+1) ? iq+2 : iq+1
        else
            iq+1
        end
    end
end
```
-/
def ndigits0zpb {B : Type}
    (value : B → Int) (pow2 : B → Bool) (log2 : B → FV .f64)
    (divremFloat : Clong → FV .f64 → Jl (FV .f64 × FV .f64))
    (toInt : FV .f64 → Jl Clong) (eps : FV .f64 → FV .f64)
    (big : B → Jl BigInt)
    (x : BigInt) (b : B) : Jl Clong := do
  if value b < 2 then throw (.domainError "`b` cannot be less than 2.")
  if x.size.val = 0 then return JInt.wrap .i64 0
  if pow2 b && decide (2 ≤ value b ∧ value b ≤ 62) then
    return MPZ.sizeinbase x (JInt.wrap .i32 (value b)) false
  let n := MPZ.sizeinbase x (JInt.wrap .i32 2) false
  let lb := log2 b
  let (q,r) ← divremFloat n lb
  let iq ← toInt q
  let maxerr := mul_IEEEFloat q (eps lb)
  let one : FV .f64 := Fl.roundRat 1 1 false
  if lt_IEEEFloat (sub_IEEEFloat r one) maxerr then
    let power ← bigintPow (fun x : Clong => x.val) (fun x => decide (x.val%2 = 1)) iq (← big b)
    return if x.val.natAbs ≥ power.val.toNat then iq+JInt.wrap .i64 1 else iq
  else if lt_IEEEFloat (sub_IEEEFloat lb r) maxerr then
    let power ← bigintPow (fun x : Clong => x.val) (fun x => decide (x.val%2 = 1))
      (iq+JInt.wrap .i64 1) (← big b)
    return if x.val.natAbs ≥ power.val.toNat then iq+JInt.wrap .i64 2 else iq+JInt.wrap .i64 1
  else return iq+JInt.wrap .i64 1

/--
Julia source: base/gmp.jl:838-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prevpow2(x::BigInt) = -2 <= x <= 2 ? x : flipsign!(ONE << (ndigits(x, base=2) - 1), x)
_nextpow2(x::BigInt) = count_ones_abs(x) <= 1 ? x : flipsign!(ONE << ndigits(x, base=2), x)
```
-/
def prevpow2 (ndigits : BigInt → Jl Clong) (x : BigInt) : Jl BigInt := do
  if -2 ≤ x.val ∧ x.val ≤ 2 then return x
  let shift := (← ndigits x) - JInt.wrap .i64 1
  return flipsignBang (shiftLeft ONE (JInt.wrap .u64 shift.val)) (signbit x)
def nextpow2 (ndigits : BigInt → Jl Clong) (x : BigInt) : Jl BigInt := do
  if (countOnesAbs x).val ≤ 1 then return x
  let shift ← ndigits x
  return flipsignBang (shiftLeft ONE (JInt.wrap .u64 shift.val)) (signbit x)

/--
Julia source: base/gmp.jl:841-858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.checked_abs(x::BigInt) = abs(x)
Base.checked_neg(x::BigInt) = -x
Base.checked_add(a::BigInt, b::BigInt) = a + b
Base.checked_sub(a::BigInt, b::BigInt) = a - b
Base.checked_mul(a::BigInt, b::BigInt) = a * b
Base.checked_div(a::BigInt, b::BigInt) = div(a, b)
Base.checked_rem(a::BigInt, b::BigInt) = rem(a, b)
Base.checked_fld(a::BigInt, b::BigInt) = fld(a, b)
Base.checked_mod(a::BigInt, b::BigInt) = mod(a, b)
Base.checked_cld(a::BigInt, b::BigInt) = cld(a, b)
Base.add_with_overflow(a::BigInt, b::BigInt) = a + b, false
Base.sub_with_overflow(a::BigInt, b::BigInt) = a - b, false
Base.mul_with_overflow(a::BigInt, b::BigInt) = a * b, false

# checked_pow doesn't follow the same promotion rules as the others, above.
Base.checked_pow(x::BigInt, p::Integer) = x^p
Base.checked_pow(x::Integer, p::BigInt) = x^p
Base.checked_pow(x::BigInt, p::BigInt) = x^p
```
-/
-- Source: base/gmp.jl:841-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_abs(x::BigInt) = abs(x)
-- /Source
def checkedAbs (x : BigInt) := if isnegative x then neg x else x
-- Source: base/gmp.jl:842-842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_neg(x::BigInt) = -x
-- /Source
def checkedNeg (x : BigInt) := unaryNeg x
-- Source: base/gmp.jl:843-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_add(a::BigInt, b::BigInt) = a + b
-- /Source
def checkedAdd (a b : BigInt) := add a b
-- Source: base/gmp.jl:844-844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_sub(a::BigInt, b::BigInt) = a - b
-- /Source
def checkedSub (a b : BigInt) := sub a b
-- Source: base/gmp.jl:845-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_mul(a::BigInt, b::BigInt) = a * b
-- /Source
def checkedMul (a b : BigInt) := mul a b
-- Source: base/gmp.jl:846-846 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_div(a::BigInt, b::BigInt) = div(a, b)
-- /Source
def checkedDiv (a b : BigInt) := div a b
-- Source: base/gmp.jl:847-847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_rem(a::BigInt, b::BigInt) = rem(a, b)
-- /Source
def checkedRem (a b : BigInt) := rem a b
-- Source: base/gmp.jl:848-848 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_fld(a::BigInt, b::BigInt) = fld(a, b)
-- /Source
def checkedFld (a b : BigInt) := fld a b
-- Source: base/gmp.jl:849-849 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_mod(a::BigInt, b::BigInt) = mod(a, b)
-- /Source
def checkedMod (a b : BigInt) := mod a b
-- Source: base/gmp.jl:850-850 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_cld(a::BigInt, b::BigInt) = cld(a, b)
-- /Source
def checkedCld (a b : BigInt) := cld a b
-- Source: base/gmp.jl:851-851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.add_with_overflow(a::BigInt, b::BigInt) = a + b, false
-- /Source
def addWithOverflow (a b : BigInt) : Jl (BigInt × Bool) := do return (← add a b, false)
-- Source: base/gmp.jl:852-852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.sub_with_overflow(a::BigInt, b::BigInt) = a - b, false
-- /Source
def subWithOverflow (a b : BigInt) : Jl (BigInt × Bool) := do return (← sub a b, false)
-- Source: base/gmp.jl:853-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.mul_with_overflow(a::BigInt, b::BigInt) = a * b, false
-- /Source
def mulWithOverflow (a b : BigInt) : Jl (BigInt × Bool) := do return (← mul a b, false)
-- Source: base/gmp.jl:856-856 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_pow(x::BigInt, p::Integer) = x^p
-- /Source
def checkedPow {I R : Type} (power : BigInt → I → Jl R)
    (x : BigInt) (p : I) : Jl R := power x p
-- Source: base/gmp.jl:857-857 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_pow(x::Integer, p::BigInt) = x^p
-- /Source
def checkedIntegerPow {I R : Type} (power : I → BigInt → Jl R)
    (x : I) (p : BigInt) : Jl R := power x p
-- Source: base/gmp.jl:858-858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.checked_pow(x::BigInt, p::BigInt) = x^p
-- /Source
def checkedBigPow (x p : BigInt) := powBigInt x p

/--
Julia source: base/gmp.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.deepcopy_internal(x::BigInt, stackdict::IdDict) = get!(() -> MPZ.set(x), stackdict, x)::BigInt
```
-/
def deepcopyInternal {D : Type}
    (getOrInsert : (Unit → Jl BigInt) → D → BigInt → Jl (BigInt × D))
    (x : BigInt) (stackdict : D) : Jl (BigInt × D) :=
  getOrInsert (fun _ => MPZ.unary .set x) stackdict x

/--
Julia source: base/gmp.jl:864-864 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base._hash_shl!(x::BigInt, n) = MPZ.mul_2exp!(x, n)
```
-/
-- Source: base/gmp.jl:864-864 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base._hash_shl!(x::BigInt, n) = MPZ.mul_2exp!(x, n)
-- /Source
def hashShiftBang (x : BigInt) (n : Culong) := MPZ.unsignedInplace .mul2exp x n

/--
Julia source: base/gmp.jl:873-901 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    # UnsafeLimbView provides a safe iterator interface to BigInt limb data
    struct UnsafeLimbView <: AbstractVector{UInt8}
        bigint::BigInt
        start_byte::Int
        num_bytes::Int
    end

    function Base.size(view::UnsafeLimbView)
        return (view.num_bytes,)
    end

    function Base.getindex(view::UnsafeLimbView, i::Int)
        @boundscheck checkbounds(view, i)
        GC.@preserve view begin
            limb_index = div(view.start_byte + i - 2, 8) + 1
            byte_in_limb = (view.start_byte + i - 2) % 8
            limb = unsafe_load(view.bigint.d, limb_index)
            return UInt8((limb >> (8 * byte_in_limb)) & 0xff)
        end
    end

    function Base.iterate(view::UnsafeLimbView, state::Int = 1)
        state > view.num_bytes && return nothing
        return @inbounds(view[state]), state + 1
    end

    function Base.length(view::UnsafeLimbView)
        return view.num_bytes
    end
```
-/
structure UnsafeLimbView where
  bigint : BigInt
  startByte : Clong
  numBytes : Clong

def limbViewSize (view : UnsafeLimbView) : Clong := view.numBytes

def limbViewGetindex (view : UnsafeLimbView) (i : Clong) : Jl (JInt .u8) := do
  if i.val < 1 ∨ i.val > view.numBytes.val then throw .boundsError
  let offset := view.startByte + i - JInt.wrap .i64 2
  let limbIndex := offset.val.tdiv 8 + 1
  let byteInLimb := offset.val % 8
  let limb := loadLimb view.bigint (limbIndex-1).toNat
  return JInt.wrap .u8 ((limb / 2^(8*byteInLimb.toNat) % 256 : Nat) : Int)

def limbViewIterate (view : UnsafeLimbView) (state : Clong := JInt.wrap .i64 1) :
    Jl (Option (JInt .u8 × Clong)) := do
  if state.val > view.numBytes.val then return none
  return some (← limbViewGetindex view state, state + JInt.wrap .i64 1)

def limbViewLength (view : UnsafeLimbView) : Clong := view.numBytes

/--
Julia source: base/gmp.jl:903-915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function hash_integer(n::BigInt, h::UInt)
        iszero(n) && return hash_integer(0, h)
        s = n.size
        h ⊻= (s < 0)

        us = abs(s)
        leading_zero_bytes = div(leading_zeros(unsafe_load(n.d, us)), 8)
        num_bytes = 8 * us - leading_zero_bytes

        # Use UnsafeLimbView for safe iterator-based access
        limb_view = UnsafeLimbView(n, 1, num_bytes)
        return hash_bytes(limb_view, h, HASH_SECRET)
    end
```
-/
def hashInteger (hashIntegerSmall : Clong → Culong → Culong)
    (hashBytes : UnsafeLimbView → Culong → Culong) (n : BigInt) (h : Culong) : Culong :=
  if iszero n then hashIntegerSmall (JInt.wrap .i64 0) h else
    let s := n.size
    let h := JInt.wrap .u64 (Nat.xor h.val.toNat (if s.val < 0 then 1 else 0))
    let us := s.val.natAbs
    let top := loadLimb n (us-1)
    let leadingZeroBytes := (if top = 0 then 64 else 63-top.log2)/8
    let numBytes := JInt.wrap .i64 ((8*us-leadingZeroBytes : Nat) : Int)
    let view := UnsafeLimbView.mk n (JInt.wrap .i64 1) numBytes
    hashBytes view h

/--
Julia source: base/gmp.jl:917-955 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function hash(x::BigInt, h::UInt)
        GC.@preserve x begin
            sz = x.size
            sz == 0 && return hash(0, h)
            ptr = Ptr{UInt64}(x.d)
            if sz == 1
                return hash(unsafe_load(ptr), h)
            elseif sz == -1
                limb = unsafe_load(ptr)
                limb <= typemin(Int) % UInt && return hash(-%(limb % Int), h)
            end
            pow = trailing_zeros(x)
            nd = Base.ndigits0z(x, 2)
            idx = (pow >>> 6) + 1
            shift = (pow & 63) % UInt
            upshift = BITS_PER_LIMB - shift
            asz = abs(sz)
            if shift == 0
                limb = unsafe_load(ptr, idx)
            else
                limb1 = unsafe_load(ptr, idx)
                limb2 = idx < asz ? unsafe_load(ptr, idx+1) : UInt(0)
                limb = limb2 << upshift | limb1 >> shift
            end
            if nd <= 1024 && nd - pow <= 53
                return hash(ldexp(flipsign(Float64(limb), sz), pow), h)
            end
            h = hash_integer(pow, h)

            h ⊻= (sz < 0)
            leading_zero_bytes = div(leading_zeros(unsafe_load(x.d, asz)), 8)
            trailing_zero_bytes = div(pow, 8)
            num_bytes = 8 * asz - (leading_zero_bytes + trailing_zero_bytes)

            # Use UnsafeLimbView for safe iterator-based access
            limb_view = UnsafeLimbView(x, trailing_zero_bytes + 1, num_bytes)
            return hash_bytes(limb_view, h, HASH_SECRET)
        end
    end
```
-/
def hash (hashInt : Clong → Culong → Culong) (hashUInt : Culong → Culong → Culong)
    (hashFloat : FV .f64 → Culong → Culong)
    (ldexp : FV .f64 → Clong → FV .f64)
    (ndigits0z : BigInt → Jl Clong)
    (hashBytes : UnsafeLimbView → Culong → Culong)
    (x : BigInt) (h : Culong) : Jl Culong := do
  let sz := x.size
  if sz.val = 0 then return hashInt (JInt.wrap .i64 0) h
  if sz.val = 1 then return hashUInt (JInt.wrap .u64 (loadLimb x 0 : Int)) h
  else if sz.val = -1 then
    let limb := JInt.wrap .u64 (loadLimb x 0 : Int)
    if limb.val ≤ (JInt.rem .u64 (JInt.typemin .i64)).val then
      return hashInt (-(JInt.rem .i64 limb)) h
  let pow ← trailingZeros x
  let nd ← ndigits0z x
  let idx := pow.val.toNat / 64 + 1
  let shift := pow.val.toNat % 64
  let upshift := 64-shift
  let asz := sz.val.natAbs
  let limb := if shift = 0 then loadLimb x (idx-1)
    else
      let limb1 := loadLimb x (idx-1)
      let limb2 := if idx < asz then loadLimb x idx else 0
      (limb2*2^upshift + limb1 / 2^shift) % 2^64
  if nd.val ≤ 1024 ∧ nd.val-pow.val ≤ 53 then
    let f : FV .f64 := Fl.roundRat (if sz.val < 0 then -(limb : Int) else limb) 1 false
    return hashFloat (ldexp f pow) h
  let h := hashInt pow h
  let h := JInt.wrap .u64 (Nat.xor h.val.toNat (if sz.val < 0 then 1 else 0))
  let top := loadLimb x (asz-1)
  let leadingZeroBytes := (if top = 0 then 64 else 63-top.log2)/8
  let trailingZeroBytes := pow.val.toNat/8
  let numBytes := JInt.wrap .i64 ((8*asz-(leadingZeroBytes+trailingZeroBytes) : Nat) : Int)
  let view := UnsafeLimbView.mk x (JInt.wrap .i64 (trailingZeroBytes+1 : Nat)) numBytes
  return hashBytes view h

namespace MPQ

abbrev Rational := JuliaLean.base.rational.Rational BigInt


/--
Julia source: base/gmp.jl:966-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct _MPQ
    num_alloc::Cint
    num_size::Cint
    num_d::Ptr{Limb}
    den_alloc::Cint
    den_size::Cint
    den_d::Ptr{Limb}
    # to prevent GC
    rat::Rational{BigInt}
end
```
-/
structure RawRational where
  numAlloc : Cint
  numSize : Cint
  numD : List Limb
  denAlloc : Cint
  denSize : Cint
  denD : List Limb
  rat : Rational

/--
Julia source: base/gmp.jl:979-983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_MPQ(x::BigInt,y::BigInt) = _MPQ(x.alloc, x.size, x.d,
                                 y.alloc, y.size, y.d,
                                 unsafe_rational(BigInt, x, y))
_MPQ() = _MPQ(BigInt(), BigInt())
_MPQ(x::Rational{BigInt}) = _MPQ(x.num, x.den)
```
-/
-- Source: base/gmp.jl:979-981 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _MPQ(x::BigInt,y::BigInt) = _MPQ(x.alloc, x.size, x.d,
--                                  y.alloc, y.size, y.d,
--                                  unsafe_rational(BigInt, x, y))
-- /Source
def rawPair (x y : BigInt) : RawRational :=
  ⟨x.alloc,x.size,x.d,y.alloc,y.size,y.d,⟨x,y⟩⟩
-- Source: base/gmp.jl:982-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _MPQ() = _MPQ(BigInt(), BigInt())
-- /Source
def rawEmpty : RawRational := rawPair initBigInt initBigInt
-- Source: base/gmp.jl:983-983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _MPQ(x::Rational{BigInt}) = _MPQ(x.num, x.den)
-- /Source
def rawRational (x : Rational) := rawPair x.num x.den

/--
Julia source: base/gmp.jl:985-992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# GMP allows aliasing only via the same mpq_t, so copy BigInts `x` shares with the output (e.g. `x = inv(z)`)
function _MPQ(zq::_MPQ, x::Rational{BigInt})
    z = zq.rat
    x === z && return zq
    num = x.num === z.num || x.num === z.den ? MPZ.set(x.num) : x.num
    den = x.den === z.num || x.den === z.den ? MPZ.set(x.den) : x.den
    return _MPQ(num, den)
end
```
-/
-- Source: base/gmp.jl:986-992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _MPQ(zq::_MPQ, x::Rational{BigInt})
--     z = zq.rat
--     x === z && return zq
--     num = x.num === z.num || x.num === z.den ? MPZ.set(x.num) : x.num
--     den = x.den === z.num || x.den === z.den ? MPZ.set(x.den) : x.den
--     return _MPQ(num, den)
-- end
-- /Source
def rawAliased (zq : RawRational) (x : Rational)
    (sameRational sameNumNum sameNumDen sameDenNum sameDenDen : Bool) : Jl RawRational := do
  if sameRational then return zq
  let num ← if sameNumNum || sameNumDen then MPZ.unary .set x.num else pure x.num
  let den ← if sameDenNum || sameDenDen then MPZ.unary .set x.den else pure x.den
  return rawPair num den

/--
Julia source: base/gmp.jl:994-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sync_rational!(xq::_MPQ)
    xq.rat.num.alloc = xq.num_alloc
    xq.rat.num.size  = xq.num_size
    xq.rat.num.d     = xq.num_d
    xq.rat.den.alloc = xq.den_alloc
    xq.rat.den.size  = xq.den_size
    xq.rat.den.d     = xq.den_d
    return xq.rat
end
```
-/
def syncRational (xq : RawRational) : Rational :=
  let n := limbMagnitude (xq.numD.take xq.numSize.val.natAbs)
  let d := limbMagnitude (xq.denD.take xq.denSize.val.natAbs)
  ⟨⟨if xq.numSize.val < 0 then -(n : Int) else n, xq.numAlloc,xq.numSize,xq.numD⟩,
   ⟨if xq.denSize.val < 0 then -(d : Int) else d, xq.denAlloc,xq.denSize,xq.denD⟩⟩

/-- GMP manual chapter 6, `mpq_canonicalize`: divide common factors and make
    the denominator positive. https://gmplib.org/manual/Rational-Number-Functions -/
def canonicalize (out : Rational) (n d : Int) : Jl Rational :=
  if d = 0 then .error .divideError else
    let g := Int.ofNat (Nat.gcd n.natAbs d.natAbs)
    let sign := sgn d
    pure ⟨writeValue out.num (sign * n.tdiv g), writeValue out.den (sign * d.tdiv g)⟩

/-- GMP manual §6.1, `mpq_set_si`, `mpq_set_ui`: assignment does not canonicalize.
    https://gmplib.org/manual/Initializing-Rationals -/
def setPair (out : Rational) (n d : Int) : Rational :=
  ⟨writeValue out.num n,writeValue out.den d⟩


/--
Julia source: base/gmp.jl:1004-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Rational{BigInt}(num::BigInt, den::BigInt)
    if iszero(den)
        iszero(num) && __throw_rational_argerror_zero(BigInt)
        return set_si(flipsign(1, num), 0)
    end
    xq = _MPQ(MPZ.set(num), MPZ.set(den))
    ccall((:__gmpq_canonicalize, libgmp), Cvoid, (mpq_t,), xq)
    return sync_rational!(xq)
end
```
-/
-- Source: base/gmp.jl:1004-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Rational{BigInt}(num::BigInt, den::BigInt)
--     if iszero(den)
--         iszero(num) && __throw_rational_argerror_zero(BigInt)
--         return set_si(flipsign(1, num), 0)
--     end
--     xq = _MPQ(MPZ.set(num), MPZ.set(den))
--     ccall((:__gmpq_canonicalize, libgmp), Cvoid, (mpq_t,), xq)
--     return sync_rational!(xq)
-- end
-- /Source
def construct (num den : BigInt) : Jl Rational := do
  if iszero den then
    if iszero num then throw (.argumentError "invalid rational: zero // zero")
    return setPair ⟨initBigInt,initBigInt⟩ (if signbit num then -1 else 1) 0
  let n ← MPZ.unary .set num
  let d ← MPZ.unary .set den
  canonicalize ⟨n,d⟩ n.val d.val

/--
GMP manual §6.1 `mpq_set`, `mpq_set_z`: exact assignments: https://gmplib.org/manual/Initializing-Rationals

Julia source: base/gmp.jl:1015-1030 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function set!(z::Rational{BigInt}, x::Rational{BigInt})
    zq = _MPQ(z)
    ccall((:__gmpq_set, libgmp), Cvoid, (mpq_t, mpq_t), zq, _MPQ(zq, x))
    return sync_rational!(zq)
end

function set_z!(z::Rational{BigInt}, x::BigInt)
    zq = _MPQ(z)
    ccall((:__gmpq_set_z, libgmp), Cvoid, (mpq_t, MPZ.mpz_t), zq, x)
    return sync_rational!(zq)
end

for (op, T) in ((:set, Rational{BigInt}), (:set_z, BigInt))
    op! = Symbol(op, :!)
    @eval $op(a::$T) = $op!(unsafe_rational(BigInt(), BigInt()), a)
end
```
-/
-- Source: base/gmp.jl:1015-1019 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function set!(z::Rational{BigInt}, x::Rational{BigInt})
--     zq = _MPQ(z)
--     ccall((:__gmpq_set, libgmp), Cvoid, (mpq_t, mpq_t), zq, _MPQ(zq, x))
--     return sync_rational!(zq)
-- end
-- /Source
def setBang (z x : Rational) : Rational :=
  let zq := rawRational z
  let result := setPair zq.rat x.num.val x.den.val
  syncRational (rawRational result)
-- Source: base/gmp.jl:1021-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function set_z!(z::Rational{BigInt}, x::BigInt)
--     zq = _MPQ(z)
--     ccall((:__gmpq_set_z, libgmp), Cvoid, (mpq_t, MPZ.mpz_t), zq, x)
--     return sync_rational!(zq)
-- end
-- /Source
def setZBang (z : Rational) (x : BigInt) : Rational :=
  let zq := rawRational z
  syncRational (rawRational (setPair zq.rat x.val 1))
-- Source: base/gmp.jl:1029-1029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @eval $op(a::$T) = $op!(unsafe_rational(BigInt(), BigInt()), a)
-- /Source
def set (a : Rational) := setBang ⟨initBigInt,initBigInt⟩ a
-- Source: base/gmp.jl:1029-1029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @eval $op(a::$T) = $op!(unsafe_rational(BigInt(), BigInt()), a)
-- /Source
def setZ (a : BigInt) := setZBang ⟨initBigInt,initBigInt⟩ a

/--
GMP manual §6.1 `mpq_set_ui`, `mpq_set_si`: unchecked assignment: https://gmplib.org/manual/Initializing-Rationals

Julia source: base/gmp.jl:1032-1044 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# note that rationals returned from set_ui and set_si are not checked,
# set_ui(0, 0) will return 0//0 without errors, just like unsafe_rational
for (op, T1, T2) in ((:set_ui, Culong, Culong), (:set_si, Clong, Culong))
    op! = Symbol(op, :!)
    @eval begin
        function $op!(z::Rational{BigInt}, a, b)
            zq = _MPQ(z)
            ccall($(gmpq(op)), Cvoid, (mpq_t, $T1, $T2), zq, a, b)
            return sync_rational!(zq)
        end
        $op(a, b) = $op!(unsafe_rational(BigInt(), BigInt()), a, b)
    end
end
```
-/
-- Source: base/gmp.jl:1037-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function $op!(z::Rational{BigInt}, a, b)
--             zq = _MPQ(z)
--             ccall($(gmpq(op)), Cvoid, (mpq_t, $T1, $T2), zq, a, b)
--             return sync_rational!(zq)
--         end
-- /Source
def setUiBang (z : Rational) (a b : Culong) := setPair z a.val b.val
-- Source: base/gmp.jl:1037-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function $op!(z::Rational{BigInt}, a, b)
--             zq = _MPQ(z)
--             ccall($(gmpq(op)), Cvoid, (mpq_t, $T1, $T2), zq, a, b)
--             return sync_rational!(zq)
--         end
-- /Source
def setSiBang (z : Rational) (a : Clong) (b : Culong) := setPair z a.val b.val
-- Source: base/gmp.jl:1042-1042 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a, b) = $op!(unsafe_rational(BigInt(), BigInt()), a, b)
-- /Source
def setUi (a b : Culong) := setUiBang ⟨initBigInt,initBigInt⟩ a b
-- Source: base/gmp.jl:1042-1042 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         $op(a, b) = $op!(unsafe_rational(BigInt(), BigInt()), a, b)
-- /Source
def setSi (a : Clong) (b : Culong) := setSiBang ⟨initBigInt,initBigInt⟩ a b

inductive Arithmetic where | add | sub | mul | div
  deriving DecidableEq, Repr

/-- GMP manual §6.3 `mpq_add`, `mpq_sub`, `mpq_mul`, `mpq_div`:
    canonical arithmetic on finite rational inputs.
    https://gmplib.org/manual/Rational-Arithmetic -/
def arithmetic (op : Arithmetic) (z x y : Rational) : Jl Rational :=
  let a := x.num.val
  let b := x.den.val
  let c := y.num.val
  let d := y.den.val
  match op with
  | .add => canonicalize z (a*d+c*b) (b*d)
  | .sub => canonicalize z (a*d-c*b) (b*d)
  | .mul => canonicalize z (a*c) (b*d)
  | .div => canonicalize z (a*d) (b*c)


/--
Julia source: base/gmp.jl:1047-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function add!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
    if iszero(x.den) || iszero(y.den)
        if iszero(x.den) && iszero(y.den) && isnegative(x.num) != isnegative(y.num)
            throw(DivideError())
        end
        return set!(z, iszero(x.den) ? x : y)
    end
    zq = _MPQ(z)
    ccall((:__gmpq_add, libgmp), Cvoid,
          (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
    return sync_rational!(zq)
end
```
-/
-- Source: base/gmp.jl:1047-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function add!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
--     if iszero(x.den) || iszero(y.den)
--         if iszero(x.den) && iszero(y.den) && isnegative(x.num) != isnegative(y.num)
--             throw(DivideError())
--         end
--         return set!(z, iszero(x.den) ? x : y)
--     end
--     zq = _MPQ(z)
--     ccall((:__gmpq_add, libgmp), Cvoid,
--           (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
--     return sync_rational!(zq)
-- end
-- /Source
def addBang (z x y : Rational) : Jl Rational := do
  if iszero x.den || iszero y.den then
    if iszero x.den && iszero y.den && (isnegative x.num != isnegative y.num) then
      throw .divideError
    return setBang z (if iszero x.den then x else y)
  arithmetic .add z x y

/--
Julia source: base/gmp.jl:1060-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sub!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
    if iszero(x.den) || iszero(y.den)
        if iszero(x.den) && iszero(y.den) && isnegative(x.num) == isnegative(y.num)
            throw(DivideError())
        end
        iszero(x.den) && return set!(z, x)
        return set_si!(z, flipsign(-1, y.num), 0)
    end
    zq = _MPQ(z)
    ccall((:__gmpq_sub, libgmp), Cvoid,
          (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
    return sync_rational!(zq)
end
```
-/
-- Source: base/gmp.jl:1060-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sub!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
--     if iszero(x.den) || iszero(y.den)
--         if iszero(x.den) && iszero(y.den) && isnegative(x.num) == isnegative(y.num)
--             throw(DivideError())
--         end
--         iszero(x.den) && return set!(z, x)
--         return set_si!(z, flipsign(-1, y.num), 0)
--     end
--     zq = _MPQ(z)
--     ccall((:__gmpq_sub, libgmp), Cvoid,
--           (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
--     return sync_rational!(zq)
-- end
-- /Source
def subBang (z x y : Rational) : Jl Rational := do
  if iszero x.den || iszero y.den then
    if iszero x.den && iszero y.den && (isnegative x.num == isnegative y.num) then
      throw .divideError
    if iszero x.den then return setBang z x
    return setSiBang z (JInt.wrap .i64 (if signbit y.num then 1 else -1)) (JInt.wrap .u64 0)
  arithmetic .sub z x y

/--
Julia source: base/gmp.jl:1074-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mul!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
    if iszero(x.den) || iszero(y.den)
        if iszero(x.num) || iszero(y.num)
            throw(DivideError())
        end
        return set_si!(z, ifelse(xor(isnegative(x.num), isnegative(y.num)), -1, 1), 0)
    end
    zq = _MPQ(z)
    ccall((:__gmpq_mul, libgmp), Cvoid,
          (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
    return sync_rational!(zq)
end

```
-/
-- Source: base/gmp.jl:1074-1085 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function mul!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
--     if iszero(x.den) || iszero(y.den)
--         if iszero(x.num) || iszero(y.num)
--             throw(DivideError())
--         end
--         return set_si!(z, ifelse(xor(isnegative(x.num), isnegative(y.num)), -1, 1), 0)
--     end
--     zq = _MPQ(z)
--     ccall((:__gmpq_mul, libgmp), Cvoid,
--           (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
--     return sync_rational!(zq)
-- end
-- /Source
def mulBang (z x y : Rational) : Jl Rational := do
  if iszero x.den || iszero y.den then
    if iszero x.num || iszero y.num then throw .divideError
    return setSiBang z (JInt.wrap .i64 (if isnegative x.num != isnegative y.num then -1 else 1))
      (JInt.wrap .u64 0)
  arithmetic .mul z x y

/--
Julia source: base/gmp.jl:1087-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
    if iszero(x.den)
        if iszero(y.den)
            throw(DivideError())
        end
        isnegative(y.num) || return set!(z, x)
        return set_si!(z, flipsign(-1, x.num), 0)
    elseif iszero(y.den)
        return set_si!(z, 0, 1)
    elseif iszero(y.num)
        if iszero(x.num)
            throw(DivideError())
        end
        return set_si!(z, flipsign(1, x.num), 0)
    end
    zq = _MPQ(z)
    ccall((:__gmpq_div, libgmp), Cvoid,
          (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
    return sync_rational!(zq)
end
```
-/
-- Source: base/gmp.jl:1087-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function div!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})
--     if iszero(x.den)
--         if iszero(y.den)
--             throw(DivideError())
--         end
--         isnegative(y.num) || return set!(z, x)
--         return set_si!(z, flipsign(-1, x.num), 0)
--     elseif iszero(y.den)
--         return set_si!(z, 0, 1)
--     elseif iszero(y.num)
--         if iszero(x.num)
--             throw(DivideError())
--         end
--         return set_si!(z, flipsign(1, x.num), 0)
--     end
--     zq = _MPQ(z)
--     ccall((:__gmpq_div, libgmp), Cvoid,
--           (mpq_t,mpq_t,mpq_t), zq, _MPQ(zq, x), _MPQ(zq, y))
--     return sync_rational!(zq)
-- end
-- /Source
def divBang (z x y : Rational) : Jl Rational := do
  if iszero x.den then
    if iszero y.den then throw .divideError
    if !isnegative y.num then return setBang z x
    return setSiBang z (JInt.wrap .i64 (if signbit x.num then 1 else -1)) (JInt.wrap .u64 0)
  else if iszero y.den then return setSiBang z (JInt.wrap .i64 0) (JInt.wrap .u64 1)
  else if iszero y.num then
    if iszero x.num then throw .divideError
    return setSiBang z (JInt.wrap .i64 (if signbit x.num then -1 else 1)) (JInt.wrap .u64 0)
  arithmetic .div z x y

/--
Julia source: base/gmp.jl:1108-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fJ, fC) in ((:+, :add), (:-, :sub), (:*, :mul), (://, :div))
    fC! = Symbol(fC, :!)
    @eval begin
        ($fC!)(x::Rational{BigInt}, y::Rational{BigInt}) = $fC!(x, x, y)
        (Base.$fJ)(x::Rational{BigInt}, y::Rational{BigInt}) = $fC!(unsafe_rational(BigInt(), BigInt()), x, y)
    end
end
```
-/
def binaryBang (op : Arithmetic) (z x y : Rational) : Jl Rational :=
  match op with
  | .add => addBang z x y
  | .sub => subBang z x y
  | .mul => mulBang z x y
  | .div => divBang z x y
-- Source: base/gmp.jl:1111-1111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         ($fC!)(x::Rational{BigInt}, y::Rational{BigInt}) = $fC!(x, x, y)
-- /Source
def binaryInplace (op : Arithmetic) (x y : Rational) := binaryBang op x x y
-- Source: base/gmp.jl:1112-1112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         (Base.$fJ)(x::Rational{BigInt}, y::Rational{BigInt}) = $fC!(unsafe_rational(BigInt(), BigInt()), x, y)
-- /Source
def binary (op : Arithmetic) (x y : Rational) := binaryBang op ⟨initBigInt,initBigInt⟩ x y

/--
GMP manual §6.4 `mpq_cmp`: sign of the difference on canonical finite inputs: https://gmplib.org/manual/Comparing-Rationals

Julia source: base/gmp.jl:1116-1123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.cmp(x::Rational{BigInt}, y::Rational{BigInt})
    if iszero(x.den) || iszero(y.den)
        iszero(y.den) || return flipsign(1, x.num)
        iszero(x.den) || return flipsign(-1, y.num)
        return cmp(isnegative(y.num), isnegative(x.num))
    end
    sign(Int(ccall((:__gmpq_cmp, libgmp), Cint, (mpq_t, mpq_t), _MPQ(x), _MPQ(y))))
end
```
-/
def cmp (x y : Rational) : Clong :=
  if iszero x.den || iszero y.den then
    if !iszero y.den then JInt.wrap .i64 (if signbit x.num then -1 else 1)
    else if !iszero x.den then JInt.wrap .i64 (if signbit y.num then 1 else -1)
    else JInt.wrap .i64 (sgn ((if isnegative y.num then 1 else 0) -
      (if isnegative x.num then 1 else 0)))
  else JInt.wrap .i64 (sgn (x.num.val*y.den.val-y.num.val*x.den.val))

end MPQ

/--
Julia source: base/gmp.jl:39-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_version() = unsafe_string(unsafe_load(cglobal((:__gmp_version, libgmp), Ptr{Cchar})))
version() = VersionNumber(_version())
major_version() = _version()[1]
bits_per_limb() = Int(unsafe_load(cglobal((:__gmp_bits_per_limb, libgmp), Cint)))

const VERSION = version()
const MAJOR_VERSION = major_version()
const BITS_PER_LIMB = bits_per_limb()
```
-/
structure LibraryGlobals where
  versionString : String
  limbBits : Cint

def versionString (globals : LibraryGlobals) : String := globals.versionString
def version {V : Type} (versionNumber : String → Jl V) (globals : LibraryGlobals) : Jl V :=
  versionNumber (versionString globals)
def majorVersion (globals : LibraryGlobals) : Jl Char :=
  match (versionString globals).toList with
  | [] => .error .boundsError
  | c :: _ => .ok c
def libraryBitsPerLimb (globals : LibraryGlobals) : Clong :=
  JInt.wrap .i64 globals.limbBits.val

/-- `Expr(:tuple, QuoteNode(symbol), GlobalRef(module, binding))`. -/
structure CalleeExpr where
  symbol : String
  moduleName : String
  binding : String
  deriving DecidableEq, Repr

/--
Julia source: base/gmp.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gmpz(op::Symbol) = Expr(:tuple, QuoteNode(Symbol(:__gmpz_, op)), GlobalRef(MPZ, :libgmp))
```
-/
-- Source: base/gmp.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gmpz(op::Symbol) = Expr(:tuple, QuoteNode(Symbol(:__gmpz_, op)), GlobalRef(MPZ, :libgmp))
-- /Source
def MPZ.gmpz (op : String) : CalleeExpr := ⟨"__gmpz_" ++ op, "MPZ", "libgmp"⟩

/--
Julia source: base/gmp.jl:964-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gmpq(op::Symbol) = Expr(:tuple, QuoteNode(Symbol(:__gmpq_, op)), GlobalRef(MPZ, :libgmp))
```
-/
-- Source: base/gmp.jl:964-964 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- gmpq(op::Symbol) = Expr(:tuple, QuoteNode(Symbol(:__gmpq_, op)), GlobalRef(MPZ, :libgmp))
-- /Source
def MPQ.gmpq (op : String) : CalleeExpr := ⟨"__gmpq_" ++ op, "MPZ", "libgmp"⟩

structure MemoryFunctions where
  malloc : Nat
  realloc : Nat
  free : Nat
  deriving DecidableEq, Repr

structure LibraryRuntime where
  memoryFunctions : MemoryFunctions
  allocationOverflowHook : Option Nat
  deriving DecidableEq, Repr


/--
GMP manual chapter 13 Custom Allocation, `mp_set_memory_functions`: register the three allocator function pointers: https://gmplib.org/manual/Custom-Allocation

Julia source: base/gmp.jl:124-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ccall((:__gmp_set_memory_functions, libgmp), Cvoid,
              (Ptr{Cvoid},Ptr{Cvoid},Ptr{Cvoid}),
              cglobal(:jl_gmp_counted_malloc),
              cglobal(:jl_gmp_counted_realloc_with_old_size),
              cglobal(:jl_gmp_counted_free_with_size))
```
-/
def setMemoryFunctions (runtime : LibraryRuntime) (functions : MemoryFunctions) : LibraryRuntime :=
  { runtime with memoryFunctions := functions }

/--
Julia patched-GMP extension `__gmp_set_alloc_overflow_function`, outside the GMP manual. The standard allocator interface is GMP manual chapter 13 Custom Allocation: https://gmplib.org/manual/Custom-Allocation

Julia source: base/gmp.jl:136-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ccall((:__gmp_set_alloc_overflow_function, libgmp), Cvoid,
              (Ptr{Cvoid},),
              cglobal(:jl_throw_out_of_memory_error))
```
-/
def setAllocOverflowFunction (runtime : LibraryRuntime) (handler : Nat) : LibraryRuntime :=
  { runtime with allocationOverflowHook := some handler }

/--
Julia source: base/gmp.jl:333-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BigInt(x::Union{Clong,Int32}) = MPZ.set_si(x)
BigInt(x::Union{Culong,UInt32}) = MPZ.set_ui(x)
```
-/
-- Source: base/gmp.jl:333-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::Union{Clong,Int32}) = MPZ.set_si(x)
-- /Source
def fromInt32 (x : JInt .i32) := MPZ.setSi (JInt.wrap .i64 x.val)
-- Source: base/gmp.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::Union{Culong,UInt32}) = MPZ.set_ui(x)
-- /Source
def fromUInt32 (x : JInt .u32) := MPZ.setUi (JInt.wrap .u64 x.val)

def IsClongMax (t : IntTy) : Prop := t.signed = true ∧ t.bits ≤ 64
def IsCulongMax (t : IntTy) : Prop := t.signed = false ∧ t.bits ≤ 64


/--
Julia source: base/gmp.jl:549-563 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::BigInt, c::CulongMax) = MPZ.add_ui(x, c)
+(c::CulongMax, x::BigInt) = x + c

-(x::BigInt, c::CulongMax) = MPZ.sub_ui(x, c)
-(c::CulongMax, x::BigInt) = MPZ.ui_sub(c, x)

+(x::BigInt, c::ClongMax) = c < 0 ? -(x, -%(c % Culong)) : x + convert(Culong, c)
+(c::ClongMax, x::BigInt) = c < 0 ? -(x, -%(c % Culong)) : x + convert(Culong, c)
-(x::BigInt, c::ClongMax) = c < 0 ? +(x, -%(c % Culong)) : -(x, convert(Culong, c))
-(c::ClongMax, x::BigInt) = c < 0 ? -(x + -%(c % Culong)) : -(convert(Culong, c), x)

*(x::BigInt, c::CulongMax) = MPZ.mul_ui(x, c)
*(c::CulongMax, x::BigInt) = x * c
*(x::BigInt, c::ClongMax) = MPZ.mul_si(x, c)
*(c::ClongMax, x::BigInt) = x * c
```
-/
-- Source: base/gmp.jl:549-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::BigInt, c::CulongMax) = MPZ.add_ui(x, c)
-- /Source
def addCulongMax {t : IntTy} (_dispatch : IsCulongMax t) (x : BigInt) (c : JInt t) :=
  MPZ.unsigned .add x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:550-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(c::CulongMax, x::BigInt) = x + c
-- /Source
def culongMaxAdd {t : IntTy} (_dispatch : IsCulongMax t) (c : JInt t) (x : BigInt) :=
  addUnsigned x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:552-552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::BigInt, c::CulongMax) = MPZ.sub_ui(x, c)
-- /Source
def subCulongMax {t : IntTy} (_dispatch : IsCulongMax t) (x : BigInt) (c : JInt t) :=
  MPZ.unsigned .sub x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:553-553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(c::CulongMax, x::BigInt) = MPZ.ui_sub(c, x)
-- /Source
def culongMaxSub {t : IntTy} (_dispatch : IsCulongMax t) (c : JInt t) (x : BigInt) :=
  MPZ.uiSub (JInt.wrap .u64 c.val) x

-- Source: base/gmp.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::BigInt, c::ClongMax) = c < 0 ? -(x, -%(c % Culong)) : x + convert(Culong, c)
-- /Source
def addClongMax {t : IntTy} (_dispatch : IsClongMax t) (x : BigInt) (c : JInt t) :=
  if c.val < 0 then subUnsigned x (-(JInt.rem .u64 c))
  else addUnsigned x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:556-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(c::ClongMax, x::BigInt) = c < 0 ? -(x, -%(c % Culong)) : x + convert(Culong, c)
-- /Source
def clongMaxAdd {t : IntTy} (_dispatch : IsClongMax t) (c : JInt t) (x : BigInt) :=
  if c.val < 0 then subUnsigned x (-(JInt.rem .u64 c))
  else addUnsigned x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:557-557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::BigInt, c::ClongMax) = c < 0 ? +(x, -%(c % Culong)) : -(x, convert(Culong, c))
-- /Source
def subClongMax {t : IntTy} (_dispatch : IsClongMax t) (x : BigInt) (c : JInt t) :=
  if c.val < 0 then addUnsigned x (-(JInt.rem .u64 c))
  else subUnsigned x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:558-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(c::ClongMax, x::BigInt) = c < 0 ? -(x + -%(c % Culong)) : -(convert(Culong, c), x)
-- /Source
def clongMaxSub {t : IntTy} (_dispatch : IsClongMax t) (c : JInt t) (x : BigInt) :=
  if c.val < 0 then neg (addUnsigned x (-(JInt.rem .u64 c)))
  else unsignedSub (JInt.wrap .u64 c.val) x

-- Source: base/gmp.jl:560-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::BigInt, c::CulongMax) = MPZ.mul_ui(x, c)
-- /Source
def mulCulongMax {t : IntTy} (_dispatch : IsCulongMax t) (x : BigInt) (c : JInt t) :=
  MPZ.unsigned .mul x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:561-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(c::CulongMax, x::BigInt) = x * c
-- /Source
def culongMaxMul {t : IntTy} (_dispatch : IsCulongMax t) (c : JInt t) (x : BigInt) :=
  mulUnsigned x (JInt.wrap .u64 c.val)
-- Source: base/gmp.jl:562-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(x::BigInt, c::ClongMax) = MPZ.mul_si(x, c)
-- /Source
def mulClongMax {t : IntTy} (_dispatch : IsClongMax t) (x : BigInt) (c : JInt t) :=
  MPZ.mulSi x (JInt.wrap .i64 c.val)
-- Source: base/gmp.jl:563-563 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(c::ClongMax, x::BigInt) = x * c
-- /Source
def clongMaxMul {t : IntTy} (_dispatch : IsClongMax t) (c : JInt t) (x : BigInt) :=
  mulSigned x (JInt.wrap .i64 c.val)

/--
Julia source: base/gmp.jl:629-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(x::BigInt, y::ClongMax) = sign(MPZ.cmp_si(x, y))
cmp(x::BigInt, y::CulongMax) = sign(MPZ.cmp_ui(x, y))
```
-/
def cmpClongMax {t : IntTy} (_dispatch : IsClongMax t) (x : BigInt) (y : JInt t) : Clong :=
  JInt.wrap .i64 (sgn (MPZ.cmpSi x (JInt.wrap .i64 y.val)).val)
def cmpCulongMax {t : IntTy} (_dispatch : IsCulongMax t) (x : BigInt) (y : JInt t) : Clong :=
  JInt.wrap .i64 (sgn (MPZ.cmpUi x (JInt.wrap .u64 y.val)).val)

structure GMPInitOps (M : Type → Type) (E : Type) where
  majorVersion : M Char
  bitsPerLimb : M Cint
  version : M String
  expectedMajorVersion : Char
  expectedBitsPerLimb : Cint
  buildVersion : String
  memoryFunctions : MemoryFunctions
  allocationOverflowHook : Nat
  readLibraryRuntime : M LibraryRuntime
  writeLibraryRuntime : LibraryRuntime → M Unit
  /-- `__gmp_set_memory_functions` registers GMP's custom allocator callbacks. -/
  callSetMemoryFunctions : MemoryFunctions → M Unit
  /-- Julia's patched-GMP `__gmp_set_alloc_overflow_function` registers an OOM callback. -/
  callSetAllocOverflowFunction : Nat → M Unit
  readZero : M BigInt
  writeZero : BigInt → M Unit
  readOne : M BigInt
  writeOne : BigInt → M Unit
  writeOverflowFlag : Bool → M Unit
  warn : String → M Unit
  logError : String → M Unit
  showErrorNostdio : E → String → M Unit
  isErrorException : E → Bool
  tryCatch : {A : Type} → M A → (E → M A) → M A
  throw : {A : Type} → E → M A

/-!
Julia source: base/gmp.jl:112-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __init__()
    try
        if major_version() != MAJOR_VERSION || bits_per_limb() != BITS_PER_LIMB
            msg = """The dynamically loaded GMP library (v\"$(version())\" with __gmp_bits_per_limb == $(bits_per_limb()))
                     does not correspond to the compile time version (v\"$VERSION\" with __gmp_bits_per_limb == $BITS_PER_LIMB).
                     Please rebuild Julia."""
            bits_per_limb() != BITS_PER_LIMB ? @error(msg) : @warn(msg)
        end

        # GMP calls may run under a reset region and re-enter the runtime
        # through these allocation hooks. The hooks unpublish the region
        # around the allocator.
        ccall((:__gmp_set_memory_functions, libgmp), Cvoid,
              (Ptr{Cvoid},Ptr{Cvoid},Ptr{Cvoid}),
              cglobal(:jl_gmp_counted_malloc),
              cglobal(:jl_gmp_counted_realloc_with_old_size),
              cglobal(:jl_gmp_counted_free_with_size))
        ZERO.alloc, ZERO.size, ZERO.d = 0, 0, C_NULL
        ONE.alloc, ONE.size, ONE.d = 1, 1, pointer(_ONE)
    catch ex
        Base.showerror_nostdio(ex, "WARNING: Error during initialization of module GMP")
    end
    # This only works with a patched version of GMP, ignore otherwise
    try
        ccall((:__gmp_set_alloc_overflow_function, libgmp), Cvoid,
              (Ptr{Cvoid},),
              cglobal(:jl_throw_out_of_memory_error))
        ALLOC_OVERFLOW_FUNCTION[] = true
    catch ex
        # ErrorException("ccall: could not find function...")
        if typeof(ex) != ErrorException
            rethrow()
        end
    end
end
```
-/
def initModule {M : Type → Type} [Monad M] {E : Type} (ops : GMPInitOps M E) : M Unit := do
  ops.tryCatch (do
    let major ← ops.majorVersion
    let differs ← if major != ops.expectedMajorVersion then pure true
      else pure ((← ops.bitsPerLimb) != ops.expectedBitsPerLimb)
    if differs then
      let version ← ops.version
      let messageBits ← ops.bitsPerLimb
      let message :=
        "The dynamically loaded GMP library (v\"" ++ version ++
        "\" with __gmp_bits_per_limb == " ++ toString messageBits.val ++ ")\n" ++
        "does not correspond to the compile time version (v\"" ++ ops.buildVersion ++
        "\" with __gmp_bits_per_limb == " ++ toString ops.expectedBitsPerLimb.val ++ ").\n" ++
        "Please rebuild Julia."
      if (← ops.bitsPerLimb) != ops.expectedBitsPerLimb then ops.logError message
      else ops.warn message
    ops.callSetMemoryFunctions ops.memoryFunctions
    let library ← ops.readLibraryRuntime
    ops.writeLibraryRuntime (setMemoryFunctions library ops.memoryFunctions)
    let zero ← ops.readZero
    ops.writeZero { zero with
      alloc := JInt.wrap .i32 0
      size := JInt.wrap .i32 0
      d := [] }
    let one ← ops.readOne
    ops.writeOne { one with
      alloc := JInt.wrap .i32 1
      size := JInt.wrap .i32 1
      d := oneLimbs })
    (fun error => ops.showErrorNostdio error "WARNING: Error during initialization of module GMP")
  ops.tryCatch (do
    ops.callSetAllocOverflowFunction ops.allocationOverflowHook
    let library ← ops.readLibraryRuntime
    ops.writeLibraryRuntime (setAllocOverflowFunction library ops.allocationOverflowHook)
    ops.writeOverflowFlag true)
    (fun error => if ops.isErrorException error then pure () else ops.throw error)


/--
Julia source: base/gmp.jl:73-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function BigInt(; nbits::Integer=0)
        b = MPZ.init2!(new(), nbits)
        finalizer(cglobal((:__gmpz_clear, libgmp)), b)
        return b
    end
end
```
-/
def constructBigInt {I : Type} (value : I → Int) (nbits : I) : Jl BigInt := do
  let nbits ← JInt.convert "UInt64" .u64 (value nbits)
  let b := MPZ.init2 initBigInt nbits
  return b

/--
Julia source: base/gmp.jl:765-782 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string(n::BigInt; base::Integer = 10, pad::Integer = 1)
    base < 0 && return Base._base(Int(base), n, pad, (base>0) & (n.size<0))
    2 <= base <= 62 || throw(ArgumentError("base must be 2 ≤ base ≤ 62, got $base"))
    iszero(n) && pad < 1 && return ""
    nd1 = ndigits(n, base=base)
    nd  = max(nd1, pad)
    str = Base._string_n(nd + isnegative(n))
    GC.@preserve str begin
        p = pointer(str)
        MPZ.get_str!(p + nd - nd1, base, n)
        pad_len = nd - nd1
        if pad_len > 0
            Base.memset(p + isnegative(n), UInt8('0'), pad_len)
        end
        isnegative(n) && unsafe_store!(p, UInt8('-'))
    end
    return str
end
```
-/
def stringGeneric {B P : Type} (baseValue : B → Int) (padValue : P → Int)
    (baseToInt : B → Jl Clong)
    (negativeBase : Clong → BigInt → P → Bool → Jl String)
    (ndigits : BigInt → B → Jl Clong)
    (n : BigInt) (base : B) (pad : P) : Jl String := do
  if baseValue base < 0 then
    return ← negativeBase (← baseToInt base) n pad
      (decide (baseValue base > 0) && isnegative n)
  if !(2 ≤ baseValue base ∧ baseValue base ≤ 62) then throw (.argumentError "invalid base")
  if iszero n && decide (padValue pad < 1) then return ""
  let nd1 ← ndigits n base
  let nd := max nd1.val (padValue pad)
  let digits := MPZ.getStr (JInt.wrap .i32 (baseValue base)) n
  let padding := String.ofList (List.replicate (nd-nd1.val).toNat '0')
  if isnegative n then
    return "-" ++ padding ++ String.ofList (digits.toList.drop 1)
  else return padding ++ digits

/--
Julia source: base/gmp.jl:784-810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function digits!(a::AbstractVector{T}, n::BigInt; base::Integer = 10) where {T<:Integer}
    if base ≥ 2
        if base ≤ 62
            # fast path using mpz_get_str via string(n; base)
            s = codeunits(string(n; base))
            i, j = firstindex(a)-1, length(s)+1
            lasti = min(lastindex(a), firstindex(a) + length(s)-1 - isnegative(n))
            while i < lasti
                # base ≤ 36: 0-9, plus a-z for 10-35
                # base > 36: 0-9, plus A-Z for 10-35 and a-z for 36..61
                x = s[j -= 1]
                a[i += 1] = base ≤ 36 ? (x>0x39 ? x-0x57 : x-0x30) : (x>0x39 ? (x>0x60 ? x-0x3d : x-0x37) : x-0x30)
            end
            lasti = lastindex(a)
            while i < lasti; a[i+=1] = zero(T); end
            return isnegative(n) ? map!(-,a,a) : a
        elseif a isa StridedVector{<:Base.BitInteger} && stride(a,1) == 1 && ispow2(base) && base-1 ≤ typemax(T)
            # fast path using mpz_export
            origlen = length(a)
            _, writelen = MPZ.export!(a, n; nails = 8sizeof(T) - trailing_zeros(base))
            length(a) != origlen && resize!(a, origlen) # truncate to least-significant digits
            a[begin+writelen:end] .= zero(T)
            return isnegative(n) ? map!(-,a,a) : a
        end
    end
    return invoke(digits!, Tuple{typeof(a), Integer}, a, n; base) # slow generic fallback
end
```
-/
def digitsBangGeneric {T B : Type} (ops : DigitOps T) (baseValue : B → Int)
    (string : BigInt → B → Jl String)
    (generic : DigitVector T → BigInt → B → Except ExportError (DigitVector T))
    (a : DigitVector T) (n : BigInt) (base : B) :
    Except ExportError (DigitVector T) := do
  if (baseValue base) ≥ 2 then
    if (baseValue base) ≤ 62 then
      let s ← (string n base).mapError ExportError.julia
      let chars := s.toList.reverse
      let count := min a.data.length (chars.length - if isnegative n then 1 else 0)
      let values ← (chars.take count).mapM
        (fun c => (ops.fromByte (decodeOutputDigit (baseValue base) c)).mapError ExportError.julia)
      let values := values ++ List.replicate (a.data.length-count) ops.zero
      let values ← if isnegative n then values.mapM (fun x => (ops.neg x).mapError ExportError.julia)
        else pure values
      return { a with data := values }
    else if a.strided && decide (a.stride.val = 1) && powerOfTwo (baseValue base) &&
        decide ((baseValue base)-1 ≤ ops.maxValue) && ops.bitType.isSome then
      let origlen := a.data.length
      let bits := (scanBit (baseValue base) 0 true).toNat
      let width := (ops.bitType.getD .u64).bits
      let (a,writelen) ← ops.exportWords a n (width-bits)
      let data := a.data.take origlen
      let data := data.take writelen.val.toNat ++
        List.replicate (data.length-writelen.val.toNat) ops.zero
      let data ← if isnegative n then data.mapM (fun x => (ops.neg x).mapError ExportError.julia)
        else pure data
      return { a with data := data }
  generic a n base

def sourceIndices (lo hi : Clong) : List Clong :=
  (List.range (hi.val-lo.val+1).toNat).map (fun (i : Nat) => JInt.wrap .i64 (lo.val+Int.ofNat i))

inductive ProductContinuation where
  | done
  | right (lo hi : Clong) (next : ProductContinuation)
  | multiply (left : BigInt) (next : ProductContinuation)

inductive ProductState where
  | descend (lo hi : Clong) (continuation : ProductContinuation)
  | returnValue (value : BigInt) (continuation : ProductContinuation)

/--
Julia source: base/gmp.jl:697-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _prod(arr::AbstractArray{BigInt}, lo, hi)
    if hi - lo + 1 <= 16
        # compute first the needed number of bits for the result,
        # to avoid re-allocations
        nlimbs = 0
        for i in lo:hi
            nlimbs += abs(arr[i].size)
        end
        init = BigInt(; nbits=nlimbs*BITS_PER_LIMB)
        MPZ.set_si!(init, 1)
        for i in lo:hi
            MPZ.mul!(init, arr[i])
        end
        init
    else
        mid = (lo + hi) ÷ 2
        MPZ.mul!(_prod(arr, lo, mid), _prod(arr, mid+1, hi))
    end
end
```
-/
-- Source: base/gmp.jl:697-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _prod(arr::AbstractArray{BigInt}, lo, hi)
--     if hi - lo + 1 <= 16
--         # compute first the needed number of bits for the result,
--         # to avoid re-allocations
--         nlimbs = 0
--         for i in lo:hi
--             nlimbs += abs(arr[i].size)
--         end
--         init = BigInt(; nbits=nlimbs*BITS_PER_LIMB)
--         MPZ.set_si!(init, 1)
--         for i in lo:hi
--             MPZ.mul!(init, arr[i])
--         end
--         init
--     else
--         mid = (lo + hi) ÷ 2
--         MPZ.mul!(_prod(arr, lo, mid), _prod(arr, mid+1, hi))
--     end
-- end
-- /Source
def prodRangeGeneric {A : Type} (getindex : A → Clong → Jl BigInt)
    (arr : A) (lo hi : Clong) : Option (Jl BigInt) :=
  JuliaLean.base.reduce.whileLoop (fun state => do
    match state with
    | .descend lo hi continuation =>
      if (hi-lo+JInt.wrap .i64 1).val ≤ 16 then
        let indices := sourceIndices lo hi
        let nlimbs ← indices.foldlM (fun count i => do
          let x ← getindex arr i
          pure (count + JInt.wrap .i64 (x.size.val.natAbs : Int))) (JInt.wrap .i64 0)
        let init ← constructBigInt (fun x : Clong => x.val) (nlimbs*JInt.wrap .i64 64)
        let init := MPZ.setSiBang init (JInt.wrap .i64 1)
        let result ← indices.foldlM (fun result i => do
          MPZ.binaryInplace .mul result (← getindex arr i)) init
        return .inr (.returnValue result continuation)
      else
        let mid := JInt.wrap .i64 ((lo+hi).val.tdiv 2)
        return .inr (.descend lo mid (.right (mid+JInt.wrap .i64 1) hi continuation))
    | .returnValue value .done => return .inl value
    | .returnValue value (.right lo hi continuation) =>
      return .inr (.descend lo hi (.multiply value continuation))
    | .returnValue value (.multiply left continuation) =>
      let result ← MPZ.binaryInplace .mul left value
      return .inr (.returnValue result continuation))
    (ProductState.descend lo hi .done)

/--
Julia source: base/gmp.jl:693-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function prod(arr::AbstractArray{BigInt})
    any(iszero, arr) && return zero(BigInt)
    _prod(arr, firstindex(arr), lastindex(arr))
end
```
-/
-- Source: base/gmp.jl:693-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function prod(arr::AbstractArray{BigInt})
--     any(iszero, arr) && return zero(BigInt)
--     _prod(arr, firstindex(arr), lastindex(arr))
-- end
-- /Source
def prodGeneric {A : Type} (anyZero : A → Jl Bool)
    (firstindex lastindex : A → Clong) (getindex : A → Clong → Jl BigInt)
    (arr : A) : Option (Jl BigInt) :=
  match anyZero arr with
  | .error error => some (.error error)
  | .ok true => some (.ok (ofInt 0))
  | .ok false => prodRangeGeneric getindex arr (firstindex arr) (lastindex arr)

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module GMP
-- 
-- export BigInt
-- 
-- import .Base: *, *%, +, +%, -, -%, /, <, <<, >>, >>>, <=, ==, >, >=, ^, ~, &, |, xor,
--              binomial, cmp, convert, div, divrem, factorial, cld, fld, gcd, gcdx, lcm, mod,
--              ndigits, promote_rule, rem, show, isqrt, string, powermod, sum, prod,
--              trailing_zeros, trailing_ones, count_ones, count_zeros, tryparse_internal,
--              invmod, _prevpow2, _nextpow2, ndigits0zpb,
--              widen, signed, unsafe_trunc, iszero, isone, big, flipsign, signbit,
--              sign, isodd, iseven, digits!, hash, hash_integer, top_set_bit, exponent,
--              ispositive, isnegative, clamp
-- 
-- import Core: Signed, Float16, Float32, Float64
-- 
-- using .Base: IEEEFloat, uinttype, exponent_bias, exponent_max, significand_mask, ieee754_representation
-- using .Base.Rounding: rounds_to_nearest, rounds_away_from_zero, tie_breaker_is_to_even,
--     tie_breaker_rounds_away_from_zero
-- 
-- if Clong == Int32
--     const ClongMax = Union{Int8, Int16, Int32}
--     const CulongMax = Union{UInt8, UInt16, UInt32}
-- else
--     const ClongMax = Union{Int8, Int16, Int32, Int64}
--     const CulongMax = Union{UInt8, UInt16, UInt32, UInt64}
-- end
-- const CdoubleMax = Union{Float16, Float32, Float64}
-- 
-- if Sys.iswindows()
--     const libgmp = "libgmp-10.dll"
-- elseif Sys.isapple()
--     const libgmp = "@rpath/libgmp.10.dylib"
-- else
--     const libgmp = "libgmp.so.10"
-- end
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:47-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # GMP's mp_limb_t is by default a typedef of `unsigned long`, but can also be configured to be either
-- # `unsigned int` or `unsigned long long int`. The correct unsigned type is here named Limb, and must
-- # be used whenever mp_limb_t is in the signature of ccall'ed GMP functions.
-- if BITS_PER_LIMB == 32
--     const Limb = UInt32
--     const SLimbMax = Union{Int8, Int16, Int32}
--     const ULimbMax = Union{UInt8, UInt16, UInt32}
-- elseif BITS_PER_LIMB == 64
--     const Limb = UInt64
--     const SLimbMax = Union{Int8, Int16, Int32, Int64}
--     const ULimbMax = Union{UInt8, UInt16, UInt32, UInt64}
-- else
--     error("GMP: cannot determine the type mp_limb_t (__gmp_bits_per_limb == $BITS_PER_LIMB)")
-- end
-- 
-- """
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:79-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     BigInt(x)
-- 
-- Create an arbitrary precision integer. `x` may be an `Int` (or anything that can be
-- converted to an `Int`). The usual mathematical operators are defined for this type, and
-- results are promoted to a [`BigInt`](@ref).
-- 
-- Instances can be constructed from strings via [`parse`](@ref), or using the `big`
-- string literal.
-- 
-- # Examples
-- ```jldoctest
-- julia> parse(BigInt, "42")
-- 42
-- 
-- julia> big"313"
-- 313
-- 
-- julia> BigInt(10)^19
-- 10000000000000000000
-- ```
-- """
-- BigInt(x)
-- 
-- """
--     ALLOC_OVERFLOW_FUNCTION
-- 
-- A reference that holds a boolean, if true, indicating julia is linked with a patched GMP that
-- does not abort on huge allocation and throws OutOfMemoryError instead.
-- """
-- const ALLOC_OVERFLOW_FUNCTION = Ref(false)
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:147-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- module MPZ
-- # wrapping of libgmp functions
-- # - "output parameters" are labeled x, y, z, and are returned when appropriate
-- # - constant input parameters are labeled a, b, c
-- # - a method modifying its input has a "!" appended to its name, according to Julia's conventions
-- # - some convenient methods are added (in addition to the pure MPZ ones), e.g. `add(a, b) = add!(BigInt(), a, b)`
-- #   and `add!(x, a) = add!(x, x, a)`.
-- using ..GMP: BigInt, Limb, BITS_PER_LIMB, libgmp
-- 
-- const mpz_t = Ref{BigInt}
-- const bitcnt_t = Culong
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:204-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:210-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:214-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:226-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:229-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:237-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:249-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:261-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:266-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:269-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:285-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:291-293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end # module MPZ
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:336-336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:365-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:379-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:408-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:471-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:473-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     big(x)
-- 
-- Convert a number to a maximum precision representation (typically [`BigInt`](@ref) or
-- `BigFloat`). See [`BigFloat`](@ref BigFloat(::Any, rounding::RoundingMode)) for
-- information about some pitfalls with floating-point numbers.
-- 
-- !!! note "big(x::BigFloat)"
--     Unlike `BigFloat(x)`, `big(x)` is a no-op when `x` is already a `BigFloat`,
--     ie. when doing `x = big(x)`, the precision of `x` remains unchanged even if the
--     current `BigFloat` precision is different.
--     ```
-- """
-- function big end
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:493-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Binary ops
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:510-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # For compat only. Remove in 2.0.
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:536-537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # More efficient commutative operations
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:547-548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Basic arithmetic without promotion
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:564-564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:567-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # unary ops
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:600-600 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:624-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:627-627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:638-638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:640-640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:662-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:668-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:675-675 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:688-688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:692-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:716-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:729-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:764-764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:783-783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:811-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:834-837 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Fast paths for nextpow(2, x::BigInt)
-- # below, ONE is always left-shifted by at least one digit, so a new BigInt is
-- # allocated, which can be safely mutated
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:840-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:859-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:861-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## streamlined hashing for BigInt, by avoiding allocation from shifts ##
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:865-872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if Limb === UInt64 === UInt
--     # On 64 bit systems we can define
--     # an optimized version for BigInt of hash_integer (used e.g. for Rational{BigInt}),
--     # and of hash
-- 
--     using .Base: HASH_SECRET, hash_bytes
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:902-902 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:916-916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:956-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- module MPQ
-- 
-- # Rational{BigInt}
-- import .Base: unsafe_rational, __throw_rational_argerror_zero
-- import ..GMP: BigInt, MPZ, Limb, libgmp
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:965-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:976-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const mpq_t = Ref{_MPQ}
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:984-984 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:993-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1003-1003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1013-1014 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # define set, set_ui, set_si, set_z, and their inplace versions
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1031-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1045-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # define add, sub, mul, div, and their inplace versions
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1059-1059 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1073-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1115-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Untranslated: ABI selection, declarations, docstrings, or module/import scaffolding.
-- UNTRANSLATED
-- Source: base/gmp.jl:1124-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end # MPQ module
-- 
-- end # module
-- /Source

end JuliaLean.base.gmp


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- `GMP.version()` at base/gmp.jl:40, using the installed concrete
`VersionNumber` parser. `LibraryGlobals` is the baseline's decoded external
global representation; GMP documents its version global as a NUL-terminated
ASCII `i.j.k` string, or `i.j` before GMP 4.3.0. No parser correctness law or
uninterpreted concrete-callee callback is supplied here. The pre-existing
wrapper, parser, regex matcher, machine-sized components, and exceptions are
all reused. The source comment below is the complete queued Julia method. -/
-- Source: base/gmp.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- version() = VersionNumber(_version())
-- /Source
def libraryVersion (globals : LibraryGlobals) : Jl JuliaLean.VersionNumbers.VersionNumber :=
  JuliaLean.base.gmp.version
    (fun text => JuliaLean.VersionNumbers.parse text.toList) globals

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2
open JuliaLean

/-- A native object reference preserves the identity of the concrete mutable
BigInt argument at base/gmp.jl:163. Addresses have the packet's UInt64 ABI. -/
-- Source: base/gmp.jl:68-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BigInt <: Signed
--     alloc::Cint
--     size::Cint
--     d::Ptr{Limb}
-- 
--     function BigInt(; nbits::Integer=0)
--         b = MPZ.init2!(new(), nbits)
--         finalizer(cglobal((:__gmpz_clear, libgmp)), b)
--         return b
--     end
-- end
-- /Source
structure InitBigIntRef where
  address : JInt .u64
  deriving DecidableEq

/-- A heap cell keeps the canonical numeric/limb record and the separately
observable native data pointer. The backing storage snapshot is `value.d`.
Source reference: base/gmp.jl:68-71. -/
-- Source: base/gmp.jl:68-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BigInt <: Signed
--     alloc::Cint
--     size::Cint
--     d::Ptr{Limb}
-- /Source
structure InitHeapCell where
  value : BigInt
  dataPointer : JInt .u64

/-- Typed native-memory image for the concrete init! call. `objects` maps
valid BigInt object identities to their headers; `limbs` is the native limb
memory. The externally linked GMP static dummy limb's address is data, not
a callback. A GMP 6.3 image has limb 0xc1a0 at that static address.
`rest` contains unrelated represented source-level state, excluding temporary
GC-root allocator bookkeeping. `liveObjects` records the live-object representation invariant; an actual Julia
BigInt argument must have a live address in that memory image.
Source reference: base/gmp.jl:163. -/
-- Source: base/gmp.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- init!(x::BigInt) = (ccall((:__gmpz_init, libgmp), Cvoid, (mpz_t,), x); x)
-- /Source
structure InitHeap (Rest : Type) where
  objects : JInt .u64 → InitHeapCell
  liveObjects : JInt .u64 → Bool
  limbs : JInt .u64 → Limb
  dummyPointer : JInt .u64
  rest : Rest

/-- The ephemeral RefValue{BigInt} root introduced by cconvert. Its identity
does not escape the C call; it retains the actual mutable object reference.
Source reference: base/refvalue.jl:5-10; called by base/gmp.jl:163. -/
-- Source: base/refvalue.jl:5-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct RefValue{T} <: Ref{T}
--     x::T
--     RefValue{T}() where {T} = new()
--     RefValue{T}(x) where {T} = new(x)
-- end
-- RefValue(x::T) where {T} = RefValue{T}(x)
-- /Source
structure InitRefRoot where
  object : InitBigIntRef

/-- Closed concrete `cconvert(Ref{BigInt}, x)` adapter. The source fallback
selects convert(Ref{BigInt}, x), which constructs RefValue{BigInt}(x); the
field conversion is identity because x already has the concrete BigInt type.
Temporary GC-root allocation is represented by the retained root value, as
in the installed RefValue model. No user-dispatch callback is substituted.
Source reference: base/essentials.jl:739; base/refpointer.jl:113;
base/refvalue.jl:8; invoked at base/gmp.jl:163. -/
-- Source: base/essentials.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cconvert(::Type{T}, x) where {T} = x isa T ? x : convert(T, x) # do the conversion eagerly in most cases
-- /Source
-- Source: base/refpointer.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{Ref{T}}, x) where {T} = RefValue{T}(x)::RefValue{T}
-- /Source
-- Source: base/refvalue.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     RefValue{T}(x) where {T} = new(x)
-- /Source
def initCconvert (x : InitBigIntRef) : InitRefRoot := ⟨x⟩

/-- Closed `unsafe_convert(Ref{BigInt}, root)`: the Ref{BigInt}-typed
adapter is selected because RefValue{BigInt} is a subtype of Ref{BigInt}.
It selects Ptr{BigInt}; BigInt is not allocated inline, is concrete, and is mutable,
so the installed RefValue control flow selects pointer_from_objref(root.x).
The retained root is assigned by construction; no UndefRefError case is lost.
Source reference: base/refpointer.jl:110; base/refvalue.jl:38-54;
invoked at base/gmp.jl:163. -/
-- Source: base/refpointer.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ref{T}}, x::Ref{T}) where {T} = unsafe_convert(Ptr{T}, x)
-- /Source
-- Source: base/refvalue.jl:38-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_convert(P::Union{Type{Ptr{T}},Type{Ptr{Cvoid}}}, b::RefValue{T})::P where T
--     if allocatedinline(T)
--         p = pointer_from_objref(b)
--     elseif isconcretetype(T) && ismutabletype(T)
--         p = pointer_from_objref(b.x)
--     else
--         # If the slot is not leaf type, it could be either immutable or not.
--         # If it is actually an immutable, then we can't take its pointer directly
--         # Instead, explicitly load the pointer from the `RefValue`,
--         # which also ensures this returns same pointer as the one rooted in the `RefValue` object.
--         p = atomic_pointerref(Ptr{Ptr{Cvoid}}(pointer_from_objref(b)), :monotonic)
--         if p == C_NULL
--             throw(UndefRefError())
--         end
--     end
--     return p
-- end
-- /Source
def initUnsafeConvert (root : InitRefRoot) : JInt .u64 :=
  root.object.address

/-- GMP 6.3.0's concrete __gmpz_init primitive: store alloc=0, the static
dummy pointer, then size=0. The mathematical value is zero once size is zero.
It neither allocates nor frees limb storage. Existing canonical MPZ.init
retains the old allocation, so it is deliberately not reused as this primitive.
GMP source: gmp-6.3.0/mpz/init.c, lines 35-41, official release archive
https://gmplib.org/download/gmp/gmp-6.3.0.tar.xz
SHA256 a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898.
Source reference: base/gmp.jl:163. -/
-- Source: base/gmp.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- init!(x::BigInt) = (ccall((:__gmpz_init, libgmp), Cvoid, (mpz_t,), x); x)
-- /Source
def initNative {Rest : Type} (pointer : JInt .u64)
    (heap : InitHeap Rest) : InitHeap Rest :=
  let old := heap.objects pointer
  let allocated := { old with value := { old.value with alloc := JInt.wrap .i32 0 } }
  let pointed := { allocated with
    value := { allocated.value with d := [heap.limbs heap.dummyPointer] }
    dataPointer := heap.dummyPointer }
  let initialized := { pointed with
    value := { pointed.value with size := JInt.wrap .i32 0, val := 0 } }
  { heap with objects := fun other => if other = pointer then initialized else heap.objects other }

/-- MPZ.init!(x::BigInt), with concrete C argument conversion and an explicit
heap. Object aliases retain their identity and observe the same updated header;
the method returns the original x after the native call. The GMP static pointer
and heap image are the native runtime boundary, not caller-supplied algorithms.
Source reference: base/gmp.jl:163. -/
-- Source: base/gmp.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- init!(x::BigInt) = (ccall((:__gmpz_init, libgmp), Cvoid, (mpz_t,), x); x)
-- /Source
def initBang {Rest : Type} (x : InitBigIntRef)
    (heap : InitHeap Rest) : InitBigIntRef × InitHeap Rest :=
  let root := initCconvert x
  let pointer := initUnsafeConvert root
  let heap := initNative pointer heap
  (x, heap)

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- The two dispatch-selected scalar conversions inserted by a foreign call.
The Julia input and intermediate root types are not fixed by an untyped source
argument. Each action may mutate state, throw, or diverge. `Other` preserves a
wrong-type return from unsafe_convert so that the foreign-call type assertion
occurs at its source position. No correctness law is imposed on either action.
Source reference: base/gmp.jl:205-209; implicit conversion order documented in
doc/src/manual/calling-c-and-fortran-code.md:248-265. -/
-- Source: base/gmp.jl:205-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:scan1, :scan0)
--     # when there is no meaningful answer, ccall returns typemax(Culong), where Culong can
--     # be UInt32 (Windows) or UInt64; we return -1 in this case for all architectures
--     @eval $op(a::BigInt, b) = Int(signed(ccall($(gmpz(op)), Culong, (mpz_t, Culong), a, b)))
-- end
-- /Source
structure ScalarConversionOps (m : Type → Type) (Input Root Native Other : Type) where
  cconvert : Input → m Root
  unsafeConvert : Root → m (Sum Native Other)

/-- The foreign-call scalar assertion preserves a correctly typed result and
raises Julia TypeError for a differently typed return. The installed IO error
interface retains that exception class and the state at the throw point.
Source reference: base/gmp.jl:208; the implicit `::Culong` assertion follows the
foreign-call expansion in doc/src/manual/calling-c-and-fortran-code.md:248-265.
-/
-- Source: base/gmp.jl:205-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:scan1, :scan0)
--     # when there is no meaningful answer, ccall returns typemax(Culong), where Culong can
--     # be UInt32 (Windows) or UInt64; we return -1 in this case for all architectures
--     @eval $op(a::BigInt, b) = Int(signed(ccall($(gmpz(op)), Culong, (mpz_t, Culong), a, b)))
-- end
-- /Source
def assertForeignScalar {World Native Other : Type}
    (converted : Sum Native Other) : JuliaLean.base.io.M World Native :=
  match converted with
  | .inl value => pure value
  | .inr _ => throw (.foreignError "TypeError" "foreign-call scalar argument type assertion")

/-- Concrete GMP scan primitive with its source's constant-time sign-extension
branch. GMP 6.3.0 mpz/scan0.c:43-55 and mpz/scan1.c:43-55 divide the unsigned
starting index by GMP_NUMB_BITS and compare it with the absolute signed size.
Past the stored limbs, a matching sign bit is immediately at the start, and
the opposite bit never occurs. The remaining branch reuses installed MPZ.scan.

The explicit early branch keeps all UInt64 starts executable, including values
at or above 2^63, without constructing the impossible intermediate integer
2^start used by the baseline's mathematical bit observer. Machine division
uses the installed JInt primitive. The quotient is at most 2^58-1, so its
conversion to native signed mp_size_t is exact; the Cint size is widened before
absolute value. A valid Cint limb count places the stored-limb boundary
below 2^37, so only immediate sign extension can return a very large unsigned
starting index. The returned Culong bit pattern is reinterpreted by `signed`
and then retained by same-type native Int conversion, exactly as the wrapper.
The ABI is the installed 64-bit Unix/64-bit-limb boundary.
Source reference: base/gmp.jl:205-209. -/
-- Source: base/gmp.jl:205-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:scan1, :scan0)
--     # when there is no meaningful answer, ccall returns typemax(Culong), where Culong can
--     # be UInt32 (Windows) or UInt64; we return -1 in this case for all architectures
--     @eval $op(a::BigInt, b) = Int(signed(ccall($(gmpz(op)), Culong, (mpz_t, Culong), a, b)))
-- end
-- /Source
def scanNative (wanted : Bool) (a : BigInt) (start : Culong) : Jl Clong := do
  let size : Clong := JInt.wrap .i64 a.size.val
  let absoluteSize := if size.val < 0 then -size else size
  let startingLimbUnsigned ← JInt.div start (JInt.wrap .u64 64)
  let startingLimb : Clong := JInt.wrap .i64 startingLimbUnsigned.val
  if startingLimb ≥ absoluteSize then
    let nativeResult : Culong :=
      if wanted then
        if size.val ≥ 0 then JInt.typemax .u64 else start
      else
        if size.val ≥ 0 then start else JInt.typemax .u64
    pure (JInt.rem .i64 nativeResult)
  else
    pure (JuliaLean.base.gmp.MPZ.scan wanted a start)

/-- The generated scan1/scan0 wrappers, including full untyped-b conversion.
First retain the concrete BigInt Ref root, then run b's cconvert; next obtain
the concrete BigInt pointer, then run b's unsafe_convert and scalar assertion.
Only afterward read the pointed-to BigInt and execute the concrete primitive,
so conversion effects that mutate an alias of a are observed by the scan.
All errors and divergent conversion actions retain their source positions;
the native scan itself makes no mutation or allocation. The Boolean selector
is true for scan1 and false for scan0. The generator's gmpz AST expression
chooses the fixed native symbol before these runtime methods are called.
Source reference: base/gmp.jl:205-209. -/
-- Source: base/gmp.jl:205-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for op in (:scan1, :scan0)
--     # when there is no meaningful answer, ccall returns typemax(Culong), where Culong can
--     # be UInt32 (Windows) or UInt64; we return -1 in this case for all architectures
--     @eval $op(a::BigInt, b) = Int(signed(ccall($(gmpz(op)), Culong, (mpz_t, Culong), a, b)))
-- end
-- /Source
def scanDispatch {Rest Input Root Other : Type}
    (ops : ScalarConversionOps (JuliaLean.base.io.M (InitHeap Rest)) Input Root Culong Other)
    (wanted : Bool) (a : InitBigIntRef) (b : Input) :
    JuliaLean.base.io.M (InitHeap Rest) Clong := do
  let aRoot := initCconvert a
  let bRoot ← ops.cconvert b
  let aPointer := initUnsafeConvert aRoot
  let nativeB ← assertForeignScalar (← ops.unsafeConvert bRoot)
  let heap ← JuliaLean.base.io.getWorld
  JuliaLean.base.io.liftJl (scanNative wanted (heap.objects aPointer).value nativeB)

/-- The concrete native UInt64 instance. cconvert's same-type branch retains
the original UInt64 value; unsafe_convert invokes the installed same-type
identity model. All 64-bit values are included, with no signed-range check.
The generic wrapper above additionally retains arbitrary other input types
through their actual selected conversion actions.
Source reference: base/essentials.jl:739,742; invoked by base/gmp.jl:208. -/
-- Source: base/essentials.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cconvert(::Type{T}, x) where {T} = x isa T ? x : convert(T, x) # do the conversion eagerly in most cases
-- /Source
-- Source: base/essentials.jl:742-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{T}, x::T) where {T} = x # unsafe_convert (like convert) defaults to assuming the convert occurred
-- /Source
def nativeCulongConversion (Rest : Type) :
    ScalarConversionOps (JuliaLean.base.io.M (InitHeap Rest)) Culong Culong Culong Empty where
  cconvert := fun value => pure value
  unsafeConvert := fun value => pure (.inl (JuliaLean.base.essentials.unsafeConvertIdentity value))

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- Exact GMP 6.3.0 no-nails __gmpz_cmp_si, including its unnormalized Cint
result. The signed Cint limb count is widened to mp_size_t (native Clong),
while the scalar sign is the difference of two Cint comparisons. A differing
limb count returns their native difference narrowed to Cint. Only the equal,
nonzero-size branch reads the low limb through the object's actual data pointer.
Unsigned ABS_CAST avoids signed negation overflow at typemin(Clong).

The result is not normalized: a three-limb positive number compared with a
positive scalar yields 2, and compared with zero yields 3. The final Cint
conversion can also change sign at extreme signed-size differences, so the
registered unconditional property promises exact equality detection and the
heap frame rather than an incorrect full-domain sign contract.
The ABI is 64-bit Unix, 64-bit GMP limbs, and GMP_NAIL_BITS=0, as installed.
Source reference: base/gmp.jl:263; native GMP 6.3.0 mpz/cmp_si.c:35-69,
gmp-impl.h:536-538 (ABS_CAST/NEG_CAST). -/
-- Source: base/gmp.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp_si(a::BigInt, b) = Int(ccall((:__gmpz_cmp_si, libgmp), Cint, (mpz_t, Clong), a, b))
-- /Source
def cmpSiNative {Rest : Type} (heap : InitHeap Rest) (aPointer : JInt .u64)
    (b : Clong) : Cint :=
  let cell := heap.objects aPointer
  let usize : Clong := JInt.wrap .i64 cell.value.size.val
  let positive : Cint := JInt.wrap .i32 (if b.val > 0 then 1 else 0)
  let negative : Cint := JInt.wrap .i32 (if b.val < 0 then 1 else 0)
  let vsize : Clong := JInt.wrap .i64 (positive - negative).val
  let isZero := decide (usize.val = 0)
  let differentSize := decide (usize ≠ vsize)
  if isZero || differentSize then
    JInt.rem .i32 (usize - vsize)
  else
    let uDigit := heap.limbs cell.dataPointer
    let absoluteB : Culong :=
      if b.val ≥ 0 then JInt.rem .u64 b
      else -(JInt.rem .u64 (b + JInt.wrap .i64 1) - JInt.wrap .u64 1)
    if uDigit = absoluteB then JInt.wrap .i32 0
    else if uDigit > absoluteB then JInt.rem .i32 usize
    else JInt.rem .i32 (-usize)

/-- The full untyped-scalar cmp_si wrapper. Concrete BigInt rooting precedes
scalar cconvert; concrete pointer extraction precedes scalar unsafe_convert
and its Clong assertion. The heap is read only after both conversion stages,
so mutations through aliases made by either stage are visible to the native
comparison. The actual Cint result is sign-extended to native Julia Int.
No cancellation, allocation, or result normalization is added.
Source reference: base/gmp.jl:263; implicit conversion protocol:
doc/src/manual/calling-c-and-fortran-code.md:248-265. -/
-- Source: base/gmp.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp_si(a::BigInt, b) = Int(ccall((:__gmpz_cmp_si, libgmp), Cint, (mpz_t, Clong), a, b))
-- /Source
def cmpSiDispatch {Rest Input Root Other : Type}
    (ops : ScalarConversionOps (JuliaLean.base.io.M (InitHeap Rest)) Input Root Clong Other)
    (a : InitBigIntRef) (b : Input) : JuliaLean.base.io.M (InitHeap Rest) Clong := do
  let aRoot := initCconvert a
  let bRoot ← ops.cconvert b
  let aPointer := initUnsafeConvert aRoot
  let nativeB ← assertForeignScalar (← ops.unsafeConvert bRoot)
  let heap ← JuliaLean.base.io.getWorld
  let nativeResult : Cint := cmpSiNative heap aPointer nativeB
  pure (JInt.wrap .i64 nativeResult.val)

/-- The full untyped-scalar cmp_ui wrapper with the same left-to-right two-
stage foreign conversions and post-conversion heap read. The installed MPZ.cmpUi
numeric observer is reused: GMP 6.3.0 mpz/cmp_ui.c actually returns only -1,0,1
on this no-nails ABI, so its normalized mathematical implementation is faithful.
The intermediate Cint and its exact widening to Julia Int remain explicit.
Source reference: base/gmp.jl:264; native GMP 6.3.0 mpz/cmp_ui.c:35-77;
implicit conversion protocol: doc/src/manual/calling-c-and-fortran-code.md:248-265. -/
-- Source: base/gmp.jl:264-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp_ui(a::BigInt, b) = Int(ccall((:__gmpz_cmp_ui, libgmp), Cint, (mpz_t, Culong), a, b))
-- /Source
def cmpUiDispatch {Rest Input Root Other : Type}
    (ops : ScalarConversionOps (JuliaLean.base.io.M (InitHeap Rest)) Input Root Culong Other)
    (a : InitBigIntRef) (b : Input) : JuliaLean.base.io.M (InitHeap Rest) Clong := do
  let aRoot := initCconvert a
  let bRoot ← ops.cconvert b
  let aPointer := initUnsafeConvert aRoot
  let nativeB ← assertForeignScalar (← ops.unsafeConvert bRoot)
  let heap ← JuliaLean.base.io.getWorld
  let nativeResult : Cint :=
    JInt.rem .i32 (JuliaLean.base.gmp.MPZ.cmpUi (heap.objects aPointer).value nativeB)
  pure (JInt.wrap .i64 nativeResult.val)

/-- Concrete Clong cconvert and unsafe_convert retain every native signed
64-bit value, including its minimum. The unsafe conversion calls the installed
same-type identity. Generic cmp_si additionally accepts all other scalar inputs
through their actual dispatch-selected conversion actions and type assertion.
Source reference: base/essentials.jl:739,742; invoked by base/gmp.jl:263. -/
-- Source: base/essentials.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cconvert(::Type{T}, x) where {T} = x isa T ? x : convert(T, x) # do the conversion eagerly in most cases
-- /Source
-- Source: base/essentials.jl:742-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{T}, x::T) where {T} = x # unsafe_convert (like convert) defaults to assuming the convert occurred
-- /Source
def nativeClongConversion (Rest : Type) :
    ScalarConversionOps (JuliaLean.base.io.M (InitHeap Rest)) Clong Clong Clong Empty where
  cconvert := fun value => pure value
  unsafeConvert := fun value => pure (.inl (JuliaLean.base.essentials.unsafeConvertIdentity value))

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

/-- `base/gmp.jl:272`: the concrete GMP 6.3.0 `mpz_get_d` primitive on the
installed 64-bit Unix ABI with 64-bit limbs and IEEE binary64 Cdouble.

The source wrapper makes one nonmutating native call. At the existing GMP
primitive boundary, normalized `Valid` storage has mathematical magnitude
`a.val.natAbs`. GMP `mpz/get_d.c:35-44` returns positive zero for size zero
and otherwise enters `mpn_get_d` with the signed size and exponent zero.
`mpn/generic/get_d.c:154-202,271-277,304-308` obtains the leading-bit exponent,
truncates the 53-bit significand, and encodes signed infinity if that exponent
is at least 1024. Since the signed size is Cint, its product with the limb
width cannot overflow the native 64-bit exponent accumulator.

For the finite branch the installed concrete converter already extracts and
truncates the same significand; reuse it. The overflow branch must be explicit:
the baseline `MPZ.getD` uses Julia's ToZero overflow convention (largest finite
value), whereas GMP returns infinity. This additive declaration leaves that
baseline definition unchanged. There is no custom dispatch, mutation, or
Julia exception in the native primitive's valid-storage domain. `Int` here is
the existing mathematical BigInt value, not a replacement for machine arithmetic.
-/
-- Source: base/gmp.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- get_d(a::BigInt) = ccall((:__gmpz_get_d, libgmp), Cdouble, (mpz_t,), a)
-- /Source
def mpzGetD (a : JuliaLean.base.gmp.BigInt) : FV .f64 :=
  if a.val.natAbs ≥ (2 : Nat)^1024 then
    Fl.inf (decide (a.val < 0))
  else
    JuliaLean.base.gmp.MPZ.getD a

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- Concrete GMP 6.3.0 bit-test primitive on the installed 64-bit Unix/no-nails ABI.
mpz/tstbit.c:49-81 widens the signed Cint size to mp_size_t, takes its absolute
value into unsigned int, divides the unsigned bit position by GMP_NUMB_BITS,
and returns the sign bit immediately when that limb is beyond the live prefix.
This includes zero and every UInt64 position, including 2^63 and ULONG_MAX.
The quotient is at most 2^58-1, so its signed Clong conversion is exact.

The finite live-prefix branch reuses installed MPZ.tstbit as the documented
infinite two's-complement mathematical primitive. Its negative case agrees
with GMP's unsigned-limb negation and lower-limb borrow correction. Both native
branches return Cint 0 or 1. The explicit sign-extension branch ensures huge
positions never construct the impossible 2^position intermediate of bitAt.
GMP's local pointer calculation does not escape, and the large-index branch
has no limb dereference; it is inside the established native numeric boundary.
Source reference: base/gmp.jl:290; bitcnt_t=Culong: base/gmp.jl:159.
Native contract: GMP manual, Integer Logic and Bit Fiddling, mpz_tstbit. -/
-- Source: base/gmp.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- tstbit(a::BigInt, b) = ccall((:__gmpz_tstbit, libgmp), Cint, (mpz_t, bitcnt_t), a, b) % Bool
-- /Source
-- Source: base/gmp.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const bitcnt_t = Culong
-- /Source
def tstbitNative (input : BigInt) (position : Culong) : Jl Cint := do
  let size : Clong := JInt.wrap .i64 input.size.val
  let magnitude := if size.val < 0 then -size else size
  let absoluteSize : JInt .u32 := JInt.rem .u32 magnitude
  let limbUnsigned ← JInt.div position (JInt.wrap .u64 64)
  let limbIndex : Clong := JInt.wrap .i64 limbUnsigned.val
  let absoluteSizeLong : Clong := JInt.wrap .i64 absoluteSize.val
  if limbIndex ≥ absoluteSizeLong then
    pure (JInt.wrap .i32 (if size.val < 0 then 1 else 0))
  else
    pure (JInt.wrap .i32 (if MPZ.tstbit input position then 1 else 0))

/-- Complete untyped-second-argument wrapper. Retain the concrete BigInt Ref
root, then perform b's selected cconvert; obtain the concrete BigInt pointer,
then perform b's selected unsafe_convert and the native scalar type assertion.
Read the current object only afterward, so mutations through aliases during
conversion are visible. Preserve each conversion's effects, errors, wrong-type
return and divergence. The exact native Cint result then passes through the
installed Cint % Bool method, including its promoted bitwise-and/inequality
body, not a substituted nonzero test or Bool conversion.
Source reference: base/gmp.jl:290; conversion order:
doc/src/manual/calling-c-and-fortran-code.md:248-265; Bool remainder:
base/int.jl:699. No GMP allocation or cancellation occurs in this method. -/
-- Source: base/gmp.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- tstbit(a::BigInt, b) = ccall((:__gmpz_tstbit, libgmp), Cint, (mpz_t, bitcnt_t), a, b) % Bool
-- /Source
-- Source: base/int.jl:699-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::Integer, ::Type{Bool}) = ((x & 1) != 0)
-- /Source
def tstbitDispatch {Rest Input Root Other : Type}
    (ops : ScalarConversionOps (JuliaLean.base.io.M (InitHeap Rest))
      Input Root Culong Other)
    (input : InitBigIntRef) (position : Input) :
    JuliaLean.base.io.M (InitHeap Rest) Bool := do
  let inputRoot := initCconvert input
  let positionRoot ← ops.cconvert position
  let inputPointer := initUnsafeConvert inputRoot
  let nativePosition ← assertForeignScalar (← ops.unsafeConvert positionRoot)
  let heap ← JuliaLean.base.io.getWorld
  let nativeResult ← JuliaLean.base.io.liftJl
    (tstbitNative (heap.objects inputPointer).value nativePosition)
  pure (JuliaLean.base.int.rem_Integer_Bool nativeResult)

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean JuliaLean.BootCov

/-- Concrete reification of the installed `BigIntType` tag into the existing
runtime type-object representation. `base/gmp.jl:298` returns the concrete
BigInt DataType, with no type parameters; its declaration is at lines64-78.
This is a representation adapter, not a new Julia method or a supplied callee.
Its broad `JType` codomain can also express incorrect type results, so the
independent range properties can reject a wrong reification.
-/
-- Source: base/gmp.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Int128})  = BigInt
-- /Source
def reifyBigIntType : JuliaLean.base.gmp.BigIntType → JType
  | .type => .dt "BigInt" false []

/-- `base/gmp.jl:298`: reify the existing signed Int128 widening result into
the installed runtime type universe, retaining the canonical method model. -/
-- Source: base/gmp.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Int128})  = BigInt
-- /Source
def widenInt128TypeView : JType :=
  reifyBigIntType (JuliaLean.base.gmp.widen128 true)

/-- `base/gmp.jl:299`: reify the existing unsigned Int128 widening result. -/
-- Source: base/gmp.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{UInt128}) = BigInt
-- /Source
def widenUInt128TypeView : JType :=
  reifyBigIntType (JuliaLean.base.gmp.widen128 false)

/-- `base/gmp.jl:300`: reify the existing BigInt widening result. -/
-- Source: base/gmp.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{BigInt})  = BigInt
-- /Source
def widenBigIntTypeView : JType :=
  reifyBigIntType JuliaLean.base.gmp.widenBigInt

/-- `base/gmp.jl:472`: the selected Base method ignores its other integer
type argument and returns its canonical BigInt type tag. The arbitrary runtime
type argument retains the full post-dispatch domain, including custom integer
types and UnionAlls; the method invokes no operation on that argument. -/
-- Source: base/gmp.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{BigInt}, ::Type{<:Integer}) = BigInt
-- /Source
def promoteIntegerTypeView (_sourceType : JType) : JType :=
  reifyBigIntType JuliaLean.base.gmp.promoteRuleInteger

/-- `base/gmp.jl:489`: retain the ignored runtime integer type argument and
reify the existing canonical `big(::Type{<:Integer})` result. This is the body
after selection of this Base method; custom method selection remains external. -/
-- Source: base/gmp.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(::Type{<:Integer})  = BigInt
-- /Source
def bigIntegerTypeView (_sourceType : JType) : JType :=
  reifyBigIntType JuliaLean.base.gmp.bigIntegerType

/-- `base/gmp.jl:490`: instantiate the installed `bigRationalType` with the
concrete Rational type-object constructor, rather than an arbitrary callback.
`Rational{T}` has one integer type parameter and is concrete here
(`base/rational.jl:4-15`). The ignored source type is kept for the full selected
method domain. Only the runtime type-object representation is expanded. -/
-- Source: base/gmp.jl:490-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(::Type{<:Rational}) = Rational{BigInt}
-- /Source
def bigRationalTypeView (_sourceType : JType) : JType :=
  JuliaLean.base.gmp.bigRationalType
    (fun component => .dt "Rational" false [reifyBigIntType component])

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- Dispatch targets selected on the argument type that the three forwarding
methods do not fix. Constructor dispatch and convert dispatch are separate:
custom Julia methods may distinguish them, return arbitrary results, throw,
mutate state, or diverge. The effect type and result type therefore stay open.
There is no callee-correctness assumption, and no known concrete body is
replaced by an interface field. The concrete BigInt instance below closes both
fields with the existing installed identity models.
Source reference: base/gmp.jl:380,382,492. -/
-- Source: base/gmp.jl:380-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::Integer, ::Type{BigInt}) = BigInt(x)
-- 
-- clamp(x, ::Type{BigInt}) = convert(BigInt, x)
-- /Source
-- Source: base/gmp.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(n::Integer) = convert(BigInt, n)
-- /Source
structure BigIntDispatchOps (m : Type → Type) (I R : Type) where
  constructBigInt : I → m R
  convertBigInt : I → m R

/-- The BigInt-target remainder wrapper calls the constructor selected on x's
Integer subtype. No extra integer conversion, normalization, type assertion,
error handling, or state transition is inserted.
Source reference: base/gmp.jl:380. -/
-- Source: base/gmp.jl:380-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::Integer, ::Type{BigInt}) = BigInt(x)
-- /Source
def remBigIntDispatch {m : Type → Type} {I R : Type}
    (ops : BigIntDispatchOps m I R) (x : I) : m R :=
  ops.constructBigInt x

/-- The untyped clamp wrapper forwards x to the selected convert(BigInt, x).
The input may be any Julia value; its selected conversion may have arbitrary
return type, effects, or errors, all retained by the returned action.
Source reference: base/gmp.jl:382. -/
-- Source: base/gmp.jl:382-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- clamp(x, ::Type{BigInt}) = convert(BigInt, x)
-- /Source
def clampBigIntDispatch {m : Type → Type} {I R : Type}
    (ops : BigIntDispatchOps m I R) (x : I) : m R :=
  ops.convertBigInt x

/-- The Integer big wrapper uses convert dispatch, distinct from direct
BigInt-constructor dispatch. Its complete source body forwards the original
argument once and returns the selected action unchanged.
Source reference: base/gmp.jl:492. -/
-- Source: base/gmp.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(n::Integer) = convert(BigInt, n)
-- /Source
def bigIntegerDispatch {m : Type → Type} {I R : Type}
    (ops : BigIntDispatchOps m I R) (n : I) : m R :=
  ops.convertBigInt n

/-- Concrete Base dispatch for an existing BigInt. The source constructor is
the installed fromBigInt identity at gmp.jl:304; same-type numeric convert is
the installed base.number.convertSame at number.jl:6. Lifting these actual
callees into the installed state-and-error monad introduces no effects and
assumes no correctness law. The full input record is passed through, including
otherwise malformed raw fields; these source methods perform no inspection.
Source reference: base/gmp.jl:304,380,382,492; base/number.jl:6. -/
-- Source: base/gmp.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::BigInt) = x
-- /Source
-- Source: base/number.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T)      where {T<:Number} = x
-- /Source
def bigIntIdentityDispatch (World : Type) :
    BigIntDispatchOps (JuliaLean.base.io.M World) BigInt BigInt where
  constructBigInt := fun x => pure (JuliaLean.base.gmp.fromBigInt x)
  convertBigInt := fun x => pure (JuliaLean.base.number.convertSame x)

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- Public signed-small-integer comparison, covering every member of ClongMax
on the installed 64-bit Unix ABI: Int8, Int16, Int32, and Int64. Their concrete
foreign scalar conversion is an exact widening to Clong. The actual cmp_si
wrapper and its exact native Cint result are used before the installed native
integer sign implementation normalizes that result. signBitInteger instantiates
base.number.signReal with the concrete machine operations, including its eager
ifelse arguments; no custom sign or comparison callback is introduced.

The final value is -1, 0, or 1 and detects mathematical equality exactly. At
extreme native limb counts, the Cint conversion inside GMP cmp_si may reverse
the raw result's sign. Normalizing afterward retains that source behavior;
there is no unconditional mathematical-order assertion here.
Source reference: base/gmp.jl:629; sign: base/number.jl:212; implicit scalar
conversion: base/essentials.jl:739,742; native GMP 6.3.0 mpz/cmp_si.c:35-69. -/
-- Source: base/gmp.jl:629-629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::ClongMax) = sign(MPZ.cmp_si(x, y))
-- /Source
def cmpClongMaxHeap {Rest : Type} {t : IntTy}
    (_dispatch : IsClongMax t) (input : InitBigIntRef) (scalar : JInt t) :
    JuliaLean.base.io.M (InitHeap Rest) Clong := do
  let nativeScalar : Clong := JInt.wrap .i64 scalar.val
  let rawResult ← cmpSiDispatch (nativeClongConversion Rest) input nativeScalar
  JuliaLean.base.io.liftJl (JuliaLean.base.rational.signBitInteger rawResult)

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2
open JuliaLean

/-- Open dispatch on the unfixed Integer subtype and unrestricted result of big. All effects and errors remain; no callee law is assumed.
Source reference: base/gmp.jl:631. -/
-- Source: base/gmp.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::Integer) = cmp(x, big(y))
-- /Source
structure IntegerComparisonOps (m : Type → Type) (I B C : Type) where
  big : I → m B
  compare : InitBigIntRef → B → m C

/-- Complete fallback: big runs before the comparison, preserving arbitrary result types, mutations, errors and divergence.
Source reference: base/gmp.jl:631. -/
-- Source: base/gmp.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::Integer) = cmp(x, big(y))
-- /Source
def cmpIntegerDispatch {m : Type → Type} [Monad m] {I B C : Type}
    (ops : IntegerComparisonOps m I B C) (x : InitBigIntRef) (y : I) : m C := do
  let bigY ← ops.big y
  ops.compare x bigY

/-- Open comparison and negation selected on its unrestricted result.
Source reference: base/gmp.jl:632. -/
-- Source: base/gmp.jl:632-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::Integer, y::BigInt) = -cmp(y, x)
-- /Source
structure ReverseComparisonOps (m : Type → Type) (I C R : Type) where
  compare : InitBigIntRef → I → m C
  negate : C → m R

/-- Complete reverse fallback: compare in reverse order then negate the exact returned value, retaining both calls and their effects.
Source reference: base/gmp.jl:632. -/
-- Source: base/gmp.jl:632-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::Integer, y::BigInt) = -cmp(y, x)
-- /Source
def integerCmpDispatch {m : Type → Type} [Monad m] {I C R : Type}
    (ops : ReverseComparisonOps m I C R) (x : I) (y : InitBigIntRef) : m R := do
  let comparison ← ops.compare y x
  ops.negate comparison

/-- Concrete Base reference instance: big invokes the installed Integer
forwarder and same-type numeric conversion; comparison reads both live objects
after prior effects. Heap references retain mutable alias identity. The
constructBigInt interface field is unused by bigIntegerDispatch; its identity
action agrees with the concrete BigInt identity constructor. The selected
convertBigInt field calls the installed convertSame, lifted to references.
Source reference: base/gmp.jl:304,492,628,631; base/number.jl:6. -/
-- Source: base/gmp.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::Integer) = cmp(x, big(y))
-- /Source
-- Source: base/gmp.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BigInt(x::BigInt) = x
-- /Source
-- Source: base/gmp.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(n::Integer) = convert(BigInt, n)
-- /Source
-- Source: base/gmp.jl:628-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::BigInt) = sign(MPZ.cmp(x, y))
-- /Source
-- Source: base/number.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T)      where {T<:Number} = x
-- /Source
def bigIntIntegerComparisonOps (Rest : Type) :
    IntegerComparisonOps (JuliaLean.base.io.M (InitHeap Rest)) InitBigIntRef InitBigIntRef Clong where
  big := fun y => bigIntegerDispatch
    { constructBigInt := fun ref => pure ref,
      convertBigInt := fun ref => pure (JuliaLean.base.number.convertSame ref) } y
  compare := fun x y => do
    let heap ← JuliaLean.base.io.getWorld
    pure (JuliaLean.base.gmp.cmp (heap.objects x.address).value (heap.objects y.address).value)

/-- Concrete Base reverse instance reads pointed-to BigInts at the call
point, then uses installed native JInt negation. The comparison is the
installed concrete BigInt method, including sign normalization; arbitrary
custom comparison-result types remain available in the generic ops above.
Source reference: base/gmp.jl:628,632. -/
-- Source: base/gmp.jl:632-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::Integer, y::BigInt) = -cmp(y, x)
-- /Source
-- Source: base/gmp.jl:628-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::BigInt) = sign(MPZ.cmp(x, y))
-- /Source
def bigIntReverseComparisonOps (Rest : Type) :
    ReverseComparisonOps (JuliaLean.base.io.M (InitHeap Rest)) InitBigIntRef Clong Clong where
  compare := fun y x => do
    let heap ← JuliaLean.base.io.getWorld
    pure (JuliaLean.base.gmp.cmp (heap.objects y.address).value (heap.objects x.address).value)
  negate := fun c => pure (-c)

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

/-- Closed non-NaN CdoubleMax instance needed by the guarded public comparison
at base/gmp.jl:634. The witness comes directly from that method's NaN branch.
All three IEEE source formats widen exactly to Cdouble, preserving finiteness,
infinity, signed zero, and non-NaN classification. The concrete conversion has
no user dispatch or side effects on this fixed union.

GMP 6.3.0 mpz/cmp_d.c:68-77 handles infinity before reading the signed size,
widens that size to native mp_size_t, and returns it for either floating zero.
That result is narrowed to Cint, then widened exactly to Julia Int. Every
other non-NaN branch returns only -1, 0, or 1, so installed MPZ.cmpD supplies its
exact numeric result on that branch. This repairs the otherwise unobservable
raw-result difference before the public caller applies sign.

This helper is only a necessary closed callee for the complete public methods
at lines 634-635. It does not claim coverage of generic MPZ.cmp_d(a::BigInt,b)
at line 265: custom foreign conversions and native NaN invalid-operation/abort
remain outside this helper's domain. No exception or default result replaces
that native abort behavior.
Source reference: base/gmp.jl:265,634; concrete widening: base/float.jl:345-347;
native GMP 6.3.0 mpz/cmp_d.c:59-147. -/
-- Source: base/gmp.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp_d(a::BigInt, b) = Int(ccall((:__gmpz_cmp_d, libgmp), Cint, (mpz_t, Cdouble), a, b))
-- /Source
-- Source: base/float.jl:345-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Float32(x::Float16) = fpext(Float32, x)
-- Float64(x::Float32) = fpext(Float64, x)
-- Float64(x::Float16) = fpext(Float64, x)
-- /Source
def cmpDNonNaN {T : FTy} (input : BigInt) (scalar : FV T)
    (_nonNaN : ¬ scalar.isnan = true) : Clong :=
  let nativeScalar := convertFloat .f64 scalar
  let nativeResult : Cint :=
    if nativeScalar.isinf then JInt.rem .i32 (MPZ.cmpD input nativeScalar)
    else
      let nativeSize : Clong := JInt.wrap .i64 input.size.val
      if nativeScalar.iszero then JInt.rem .i32 nativeSize
      else JInt.rem .i32 (MPZ.cmpD input nativeScalar)
  JInt.wrap .i64 nativeResult.val

/-- Complete BigInt/IEEE public comparison for Float16, Float32, and Float64.
The NaN guard runs before scalar conversion or any native GMP call, returning
native Int -1 for every NaN sign/payload. The other branch invokes the exact
closed non-NaN native comparison and the installed concrete integer sign model.
Both floating zeros compare equal to BigInt zero, as in the pinned source.
Source reference: base/gmp.jl:634; sign: base/number.jl:212. -/
-- Source: base/gmp.jl:634-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::CdoubleMax) = isnan(y) ? -1 : sign(MPZ.cmp_d(x, y))
-- /Source
-- Source: base/number.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sign(x::Real) = ifelse(x < zero(x), oftype(one(x),-1), ifelse(x > zero(x), one(x), typeof(one(x))(x)))
-- /Source
def cmpFloatExact {T : FTy} (input : BigInt) (scalar : FV T) : Jl Clong :=
  if h : scalar.isnan = true then .ok (JInt.wrap .i64 (-1))
  else JuliaLean.base.rational.signBitInteger (cmpDNonNaN input scalar h)

/-- Complete reversed IEEE/BigInt public comparison. Its sole comparison call
is the complete guarded method above; successful return is followed by native
Julia Int negation. All IEEE bit patterns, including either zero, either
infinity, and every NaN payload/sign, remain in the domain.
Source reference: base/gmp.jl:635. -/
-- Source: base/gmp.jl:635-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::CdoubleMax, y::BigInt) = -cmp(y, x)
-- /Source
def floatCmpExact {T : FTy} (scalar : FV T) (input : BigInt) : Jl Clong := do
  let result ← cmpFloatExact input scalar
  pure (-result)

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean JuliaLean.base.float

/-- Exact operator selected on the generic comparison result. This tag indexes
its dispatch interface, retaining the source >= and > targets in reverse calls.
Source reference: base/gmp.jl:731-732,739-740,745-746. -/
-- Source: base/gmp.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::BigInt, i::Integer) = cmp(x,i) == 0
-- /Source
-- Source: base/gmp.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(i::Integer, x::BigInt) = cmp(x,i) == 0
-- /Source
-- Source: base/gmp.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(x::BigInt, i::Integer) = cmp(x,i) <= 0
-- /Source
-- Source: base/gmp.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(i::Integer, x::BigInt) = cmp(x,i) >= 0
-- /Source
-- Source: base/gmp.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(x::BigInt, i::Integer) = cmp(x,i) < 0
-- /Source
-- Source: base/gmp.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(i::Integer, x::BigInt) = cmp(x,i) > 0
-- /Source
inductive IntegerRelationTag where
  | equal | lessEqual | greaterEqual | less | greater
  deriving DecidableEq, Repr

/-- Two open selected calls, retaining arbitrary input, comparison-result and
final-result types. Both actions preserve effects, errors and divergence. The
source does not assert Bool on the final result, so neither does this interface.
The fixed BigInt is an object reference throughout, preserving mutable aliases.
Source reference: base/gmp.jl:731-732,739-740,745-746. -/
-- Source: base/gmp.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::BigInt, i::Integer) = cmp(x,i) == 0
-- /Source
-- Source: base/gmp.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(i::Integer, x::BigInt) = cmp(x,i) == 0
-- /Source
-- Source: base/gmp.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(x::BigInt, i::Integer) = cmp(x,i) <= 0
-- /Source
-- Source: base/gmp.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(i::Integer, x::BigInt) = cmp(x,i) >= 0
-- /Source
-- Source: base/gmp.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(x::BigInt, i::Integer) = cmp(x,i) < 0
-- /Source
-- Source: base/gmp.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(i::Integer, x::BigInt) = cmp(x,i) > 0
-- /Source
structure IntegerRelationOps (_operation : IntegerRelationTag)
    (m : Type → Type) (I C R : Type) where
  compare : InitBigIntRef → I → m C
  selectedRelation : C → Clong → m R

/-- Complete relation body: compare the BigInt first, then pass the exact
result and native Int zero to the selected equal call. Both calls retain
all errors/effects and the final value has unrestricted type R.
Source reference: base/gmp.jl:731. -/
-- Source: base/gmp.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::BigInt, i::Integer) = cmp(x,i) == 0
-- /Source
def equalIntegerDispatch {m : Type → Type} [Monad m] {I C R : Type}
    (ops : IntegerRelationOps .equal m I C R)
    (x : InitBigIntRef) (i : I) : m R := do
  let comparison ← ops.compare x i
  ops.selectedRelation comparison (JInt.wrap .i64 0)

/-- Complete relation body: compare the BigInt first, then pass the exact
result and native Int zero to the selected equal call. Both calls retain
all errors/effects and the final value has unrestricted type R.
Source reference: base/gmp.jl:732. -/
-- Source: base/gmp.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(i::Integer, x::BigInt) = cmp(x,i) == 0
-- /Source
def integerEqualDispatch {m : Type → Type} [Monad m] {I C R : Type}
    (ops : IntegerRelationOps .equal m I C R)
    (i : I) (x : InitBigIntRef) : m R := do
  let comparison ← ops.compare x i
  ops.selectedRelation comparison (JInt.wrap .i64 0)

/-- Complete fixed IEEE relation: its outer NaN guard precedes the concrete
public cmp call, then the installed machine relation compares with Int zero.
All Float16/32/64 bit patterns are included. Known concrete callees stay fixed;
reversed > and >= use the source's known operand-reversing Base forwarders.
Source reference: base/gmp.jl:733; concrete cmp: base/gmp.jl:634. -/
-- Source: base/gmp.jl:733-733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) == 0
-- /Source
def equalFloatExact {T : FTy} (x : BigInt) (f : FV T) : Jl Bool := do
  if f.isnan then pure false
  else
    let comparison ← cmpFloatExact x f
    let zero := JInt.wrap .i64 0
    pure (JuliaLean.base.int.eqSame comparison zero)

/-- Complete fixed IEEE relation: its outer NaN guard precedes the concrete
public cmp call, then the installed machine relation compares with Int zero.
All Float16/32/64 bit patterns are included. Known concrete callees stay fixed;
reversed > and >= use the source's known operand-reversing Base forwarders.
Source reference: base/gmp.jl:734; concrete cmp: base/gmp.jl:634. -/
-- Source: base/gmp.jl:734-734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) == 0
-- /Source
def floatEqualExact {T : FTy} (f : FV T) (x : BigInt) : Jl Bool := do
  if f.isnan then pure false
  else
    let comparison ← cmpFloatExact x f
    let zero := JInt.wrap .i64 0
    pure (JuliaLean.base.int.eqSame comparison zero)

/-- Complete relation body: compare the BigInt first, then pass the exact
result and native Int zero to the selected lessEqual call. Both calls retain
all errors/effects and the final value has unrestricted type R.
Source reference: base/gmp.jl:739. -/
-- Source: base/gmp.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(x::BigInt, i::Integer) = cmp(x,i) <= 0
-- /Source
def lessEqualIntegerDispatch {m : Type → Type} [Monad m] {I C R : Type}
    (ops : IntegerRelationOps .lessEqual m I C R)
    (x : InitBigIntRef) (i : I) : m R := do
  let comparison ← ops.compare x i
  ops.selectedRelation comparison (JInt.wrap .i64 0)

/-- Complete relation body: compare the BigInt first, then pass the exact
result and native Int zero to the selected greaterEqual call. Both calls retain
all errors/effects and the final value has unrestricted type R.
Source reference: base/gmp.jl:740. -/
-- Source: base/gmp.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(i::Integer, x::BigInt) = cmp(x,i) >= 0
-- /Source
def integerLessEqualDispatch {m : Type → Type} [Monad m] {I C R : Type}
    (ops : IntegerRelationOps .greaterEqual m I C R)
    (i : I) (x : InitBigIntRef) : m R := do
  let comparison ← ops.compare x i
  ops.selectedRelation comparison (JInt.wrap .i64 0)

/-- Complete fixed IEEE relation: its outer NaN guard precedes the concrete
public cmp call, then the installed machine relation compares with Int zero.
All Float16/32/64 bit patterns are included. Known concrete callees stay fixed;
reversed > and >= use the source's known operand-reversing Base forwarders.
Source reference: base/gmp.jl:741; concrete cmp: base/gmp.jl:634. -/
-- Source: base/gmp.jl:741-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) <= 0
-- /Source
def lessEqualFloatExact {T : FTy} (x : BigInt) (f : FV T) : Jl Bool := do
  if f.isnan then pure false
  else
    let comparison ← cmpFloatExact x f
    let zero := JInt.wrap .i64 0
    pure (JuliaLean.base.int.le_BitSigned comparison zero)

/-- Complete fixed IEEE relation: its outer NaN guard precedes the concrete
public cmp call, then the installed machine relation compares with Int zero.
All Float16/32/64 bit patterns are included. Known concrete callees stay fixed;
reversed > and >= use the source's known operand-reversing Base forwarders.
Source reference: base/gmp.jl:742; concrete cmp: base/gmp.jl:634. -/
-- Source: base/gmp.jl:742-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) >= 0
-- /Source
def floatLessEqualExact {T : FTy} (f : FV T) (x : BigInt) : Jl Bool := do
  if f.isnan then pure false
  else
    let comparison ← cmpFloatExact x f
    let zero := JInt.wrap .i64 0
    pure (JuliaLean.base.int.le_BitSigned zero comparison)

/-- Complete relation body: compare the BigInt first, then pass the exact
result and native Int zero to the selected less call. Both calls retain
all errors/effects and the final value has unrestricted type R.
Source reference: base/gmp.jl:745. -/
-- Source: base/gmp.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(x::BigInt, i::Integer) = cmp(x,i) < 0
-- /Source
def lessIntegerDispatch {m : Type → Type} [Monad m] {I C R : Type}
    (ops : IntegerRelationOps .less m I C R)
    (x : InitBigIntRef) (i : I) : m R := do
  let comparison ← ops.compare x i
  ops.selectedRelation comparison (JInt.wrap .i64 0)

/-- Complete relation body: compare the BigInt first, then pass the exact
result and native Int zero to the selected greater call. Both calls retain
all errors/effects and the final value has unrestricted type R.
Source reference: base/gmp.jl:746. -/
-- Source: base/gmp.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(i::Integer, x::BigInt) = cmp(x,i) > 0
-- /Source
def integerLessDispatch {m : Type → Type} [Monad m] {I C R : Type}
    (ops : IntegerRelationOps .greater m I C R)
    (i : I) (x : InitBigIntRef) : m R := do
  let comparison ← ops.compare x i
  ops.selectedRelation comparison (JInt.wrap .i64 0)

/-- Complete fixed IEEE relation: its outer NaN guard precedes the concrete
public cmp call, then the installed machine relation compares with Int zero.
All Float16/32/64 bit patterns are included. Known concrete callees stay fixed;
reversed > and >= use the source's known operand-reversing Base forwarders.
Source reference: base/gmp.jl:747; concrete cmp: base/gmp.jl:634. -/
-- Source: base/gmp.jl:747-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(x::BigInt, f::CdoubleMax) = isnan(f) ? false : cmp(x,f) < 0
-- /Source
def lessFloatExact {T : FTy} (x : BigInt) (f : FV T) : Jl Bool := do
  if f.isnan then pure false
  else
    let comparison ← cmpFloatExact x f
    let zero := JInt.wrap .i64 0
    pure (JuliaLean.base.int.lt_BitSigned comparison zero)

/-- Complete fixed IEEE relation: its outer NaN guard precedes the concrete
public cmp call, then the installed machine relation compares with Int zero.
All Float16/32/64 bit patterns are included. Known concrete callees stay fixed;
reversed > and >= use the source's known operand-reversing Base forwarders.
Source reference: base/gmp.jl:748; concrete cmp: base/gmp.jl:634. -/
-- Source: base/gmp.jl:748-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(f::CdoubleMax, x::BigInt) = isnan(f) ? false : cmp(x,f) > 0
-- /Source
def floatLessExact {T : FTy} (f : FV T) (x : BigInt) : Jl Bool := do
  if f.isnan then pure false
  else
    let comparison ← cmpFloatExact x f
    let zero := JInt.wrap .i64 0
    pure (JuliaLean.base.int.lt_BitSigned zero comparison)

/-- Concrete Base instance. Installed cmp reads both live object records at
the call point, preserving aliases rather than capturing earlier numeric
snapshots. Same-type JInt relations implement the selected native operators;
> and >= retain their known reverse-operand definitions. The closed instance
preserves the whole represented heap. No callee law or custom stub is used.
Source reference: base/gmp.jl:628,731-732,739-740,745-746; base/boot.jl:884;
base/int.jl:84,574; base/operators.jl:443,499. -/
-- Source: base/gmp.jl:628-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cmp(x::BigInt, y::BigInt) = sign(MPZ.cmp(x, y))
-- /Source
-- Source: base/gmp.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::BigInt, i::Integer) = cmp(x,i) == 0
-- /Source
-- Source: base/gmp.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(i::Integer, x::BigInt) = cmp(x,i) == 0
-- /Source
-- Source: base/gmp.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(x::BigInt, i::Integer) = cmp(x,i) <= 0
-- /Source
-- Source: base/gmp.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <=(i::Integer, x::BigInt) = cmp(x,i) >= 0
-- /Source
-- Source: base/gmp.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(x::BigInt, i::Integer) = cmp(x,i) < 0
-- /Source
-- Source: base/gmp.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <(i::Integer, x::BigInt) = cmp(x,i) > 0
-- /Source
def nativeIntegerRelationOps (operation : IntegerRelationTag) (Rest : Type) :
    IntegerRelationOps operation (JuliaLean.base.io.M (InitHeap Rest))
      InitBigIntRef Clong Bool where
  compare := (bigIntIntegerComparisonOps Rest).compare
  selectedRelation := fun left right => pure <|
    match operation with
    | .equal => JuliaLean.base.int.eqSame left right
    | .lessEqual => JuliaLean.base.int.le_BitSigned left right
    | .greaterEqual => JuliaLean.base.int.le_BitSigned right left
    | .less => JuliaLean.base.int.lt_BitSigned left right
    | .greater => JuliaLean.base.int.lt_BitSigned right left

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2
open JuliaLean

/-- The selected signbit on an unfixed Integer subtype may mutate aliases, throw, diverge, or return a non-Bool. Its result type remains explicit; no law is imposed.
Source reference: base/gmp.jl:753. -/
-- Source: base/gmp.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign!(x::BigInt, y::Integer) = (signbit(y) && (x.size = -x.size); x)
-- /Source
structure SignbitDispatchOps (m : Type → Type) (I Other : Type) where
  signbit : I → m (Sum Bool Other)

/-- The source Boolean condition rejects a non-Bool at the condition, preserving the state from signbit. The installed error interface retains TypeError.
Source reference: base/gmp.jl:753. -/
-- Source: base/gmp.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign!(x::BigInt, y::Integer) = (signbit(y) && (x.size = -x.size); x)
-- /Source
def assertSignbitCondition {World Other : Type} (result : Sum Bool Other) :
    JuliaLean.base.io.M World Bool :=
  match result with
  | .inl bit => pure bit
  | .inr _ => throw (.foreignError "TypeError" "non-boolean used in boolean context")

/-- The one native Cint header assignment preserves pointer identity, allocation and all limb storage. The mathematical val is a representation shadow recomputed from the unchanged limb snapshot and new signed header; it is not another Julia store. Cint negation wraps even for raw invalid headers.
Source reference: base/gmp.jl:753. -/
-- Source: base/gmp.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign!(x::BigInt, y::Integer) = (signbit(y) && (x.size = -x.size); x)
-- /Source
def negateSizeHeader {Rest : Type} (heap : InitHeap Rest) (x : InitBigIntRef) : InitHeap Rest :=
  let cell := heap.objects x.address
  let size := -cell.value.size
  let magnitude := limbMagnitude (cell.value.d.take size.val.natAbs)
  let value := { cell.value with
    size := size
    val := if size.val < 0 then -(magnitude : Int) else (magnitude : Int) }
  { heap with objects := fun address =>
      if address = x.address then { cell with value := value } else heap.objects address }

/-- Complete effectful flipsign!: evaluate signbit and its Bool assertion first, read x.size only in the true branch after any alias mutations, perform exactly its Cint negation/store, then return the original object reference.
Source reference: base/gmp.jl:753. -/
-- Source: base/gmp.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign!(x::BigInt, y::Integer) = (signbit(y) && (x.size = -x.size); x)
-- /Source
def flipsignBangDispatch {Rest I Other : Type}
    (ops : SignbitDispatchOps (JuliaLean.base.io.M (InitHeap Rest)) I Other)
    (x : InitBigIntRef) (y : I) : JuliaLean.base.io.M (InitHeap Rest) InitBigIntRef := do
  let negative ← assertSignbitCondition (← ops.signbit y)
  if negative then
    let heap ← JuliaLean.base.io.getWorld
    JuliaLean.base.io.setWorld (negateSizeHeader heap x)
  pure x

/-- Concrete Base BigInt signbit reads its current header from the heap and invokes the installed signbit/isnegative implementation. Both references may identify the same object.
Source reference: base/gmp.jl:749,752. -/
-- Source: base/gmp.jl:752-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- signbit(x::BigInt) = isnegative(x)
-- /Source
-- Source: base/gmp.jl:749-749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isnegative(x::BigInt) = x.size < 0
-- /Source
def bigIntSignbitDispatch (Rest : Type) :
    SignbitDispatchOps (JuliaLean.base.io.M (InitHeap Rest)) InitBigIntRef Empty where
  signbit := fun y => do
    let heap ← JuliaLean.base.io.getWorld
    pure (.inl (JuliaLean.base.gmp.signbit (heap.objects y.address).value))

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- The immutable view retains the identity of its mutable BigInt, so each
load observes that object's current data pointer. Both Int fields retain all
raw native values; construction does not validate or normalize either one.
This is the installed 64-bit Limb/UInt branch of base/gmp.jl:866-901.
Source reference: base/gmp.jl:874-878. -/
-- Source: base/gmp.jl:874-878 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     struct UnsafeLimbView <: AbstractVector{UInt8}
--         bigint::BigInt
--         start_byte::Int
--         num_bytes::Int
--     end
-- /Source
structure HeapLimbView where
  bigint : InitBigIntRef
  startByte : Clong
  numBytes : Clong

/-- Explicit native memory for view loads. The underlying InitHeap contains
the current object headers and actual UInt64 limb contents at native addresses.
readableLimb records that all eight bytes of a load are live and readable; it
is a memory-domain predicate, not an extra check performed by unsafe_load.
No default word or invented Julia exception is supplied for invalid memory.
Correctness claims require readability only on paths that perform a load.
Source reference: base/pointer.jl:132-151; called by base/gmp.jl:889. -/
-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
structure LimbViewMemory (Rest : Type) where
  heap : InitHeap Rest
  readableLimb : JInt .u64 → Bool

/-- size returns a singleton tuple, represented by the existing homogeneous
tuple convention List Clong. Its arity is exactly one even when num_bytes is
zero, negative, or an extreme raw Int. No heap read or field normalization occurs.
Source reference: base/gmp.jl:880-882. -/
-- Source: base/gmp.jl:880-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function Base.size(view::UnsafeLimbView)
--         return (view.num_bytes,)
--     end
-- /Source
def limbViewSizeExact (view : HeapLimbView) : List Clong := [view.numBytes]

/-- Closed bounds predicate for this concrete AbstractVector. axes1 selects
the first axis from map(unchecked_oneto, size(view)), so raw negative num_bytes
is preserved rather than clamped. The installed OneTo checkindex model compares
the unsigned wrapped i-1 against the unsigned raw count. For nonnegative counts
this is exactly 1 <= i <= num_bytes. For negative counts it accepts positive
indices and indices <= num_bytes; that unusual raw-field behavior is retained.
Source reference: base/gmp.jl:885; base/abstractarray.jl:100-104,141,396,690-693,753;
base/range.jl:503; base/essentials.jl:389-393. -/
-- Source: base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
-- /Source
def limbViewInBoundsExact (view : HeapLimbView) (index : Clong) : Bool :=
  JuliaLean.base.abstractarray.checkindexOneTo view.numBytes index

/-- Closed UInt64 pointerref address calculation. The one-based index offset,
element-size multiplication, signed-to-unsigned address conversion, and pointer
addition all use the native wrapping operations. Alignment is one, as in
unsafe_load; valid/readable memory remains the caller's native-domain obligation.
Source reference: base/pointer.jl:151; installed pointer.indexedPointer/ptrAddI64;
invoked at base/gmp.jl:889. -/
-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
def limbViewLoadAddress (pointer : JInt .u64) (index : Clong) : JInt .u64 :=
  let byteOffset : Clong := JInt.wrap .i64 8 * (index - JInt.wrap .i64 1)
  (JuliaLean.base.pointer.ptrAddI64 (T := Limb) ⟨pointer⟩ byteOffset).address

/-- Concrete native word read from the supplied memory image. This is a read
of actual memory at the computed pointer; no list indexing or default zero is
used. Readability is an explicit representation-domain premise in the registered
properties, as required by unsafe_load's documented pointer-validity contract.
Source reference: base/pointer.jl:151; base/gmp.jl:889. -/
-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
def limbViewLoadWord {Rest : Type} (memory : LimbViewMemory Rest)
    (pointer : JInt .u64) (index : Clong) : Limb :=
  memory.heap.limbs (limbViewLoadAddress pointer index)

/-- Pure native unchecked byte primitive for consumers whose byte-array adapter
is pure. Its input is the same current object/limb heap, rather than a copied
BigInt snapshot. This is the exact closed fixed-divisor-eight specialization:
signed Int division and remainder by positive eight cannot raise DivideError,
and their native results are the wrapped truncating quotient/remainder below.
The installed signed-count shift and promoted mask are reused. After &0xff,
UInt8 conversion is always exact, so the native wrapping constructor preserves
every possible result without discarding an error or inserting a default.

The complete effect wrapper below separately retains the installed checked
div/rem/UInt8 calls at their source positions. Both have the same native-read
domain; this pure adapter is independently specified by a base-256 byte property.
Source reference: base/gmp.jl:887-890; fixed native arithmetic: base/int.jl:355-356,
608-612; unsafe_load: base/pointer.jl:151. -/
-- Source: base/gmp.jl:887-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             limb_index = div(view.start_byte + i - 2, 8) + 1
--             byte_in_limb = (view.start_byte + i - 2) % 8
--             limb = unsafe_load(view.bigint.d, limb_index)
--             return UInt8((limb >> (8 * byte_in_limb)) & 0xff)
-- /Source
def limbViewByteUnchecked {Rest : Type} (heap : InitHeap Rest)
    (view : HeapLimbView) (index : Clong) : JInt .u8 :=
  let offset := view.startByte + index - JInt.wrap .i64 2
  let quotient : Clong := JInt.wrap .i64 (offset.val.tdiv 8)
  let limbIndex := quotient + JInt.wrap .i64 1
  let remainderOffset := view.startByte + index - JInt.wrap .i64 2
  let byteInLimb : Clong := JInt.wrap .i64 (remainderOffset.val.tmod 8)
  let pointer := (heap.objects view.bigint.address).dataPointer
  let limb := heap.limbs (limbViewLoadAddress pointer limbIndex)
  let shifted := JuliaLean.base.int.shr_Int limb (JInt.wrap .i64 8 * byteInLimb)
  let masked := JuliaLean.base.int.binop JuliaLean.base.int.band shifted (JInt.wrap .u8 0xff)
  JInt.wrap .u8 masked.val

/-- Complete view indexing, with explicit bounds-check context. The default
retains @boundscheck; false represents its source-level elision under @inbounds.
The view root retains the mutable object identity throughout the load. Both
offset expressions, div, signed rem, byte-count multiplication, signed-count
shift, UInt8 mask promotion, and checked UInt8 conversion use installed native
machine models. In particular, a negative remainder shifts left, as Julia >>
requires for a negative count. The current heap pointer is read after the offset
calculations, and every success or Julia error preserves the entire memory.
Source reference: base/gmp.jl:884-892; native load contract: base/pointer.jl:132-151. -/
-- Source: base/gmp.jl:884-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function Base.getindex(view::UnsafeLimbView, i::Int)
--         @boundscheck checkbounds(view, i)
--         GC.@preserve view begin
--             limb_index = div(view.start_byte + i - 2, 8) + 1
--             byte_in_limb = (view.start_byte + i - 2) % 8
--             limb = unsafe_load(view.bigint.d, limb_index)
--             return UInt8((limb >> (8 * byte_in_limb)) & 0xff)
--         end
--     end
-- /Source
def limbViewGetindexExact {Rest : Type} (view : HeapLimbView) (index : Clong)
    (checkBounds : Bool := true) : JuliaLean.base.io.M (LimbViewMemory Rest) (JInt .u8) := do
  if checkBounds then
    if !(limbViewInBoundsExact view index) then throw (.jl .boundsError)
  let rootedView := view
  let quotient ← JuliaLean.base.io.liftJl (JuliaLean.base.int.divSame
    (rootedView.startByte + index - JInt.wrap .i64 2) (JInt.wrap .i64 8))
  let limbIndex : Clong := quotient + JInt.wrap .i64 1
  let byteInLimb ← JuliaLean.base.io.liftJl (JuliaLean.base.int.remSame
    (rootedView.startByte + index - JInt.wrap .i64 2) (JInt.wrap .i64 8))
  let memory ← JuliaLean.base.io.getWorld
  let pointer := (memory.heap.objects rootedView.bigint.address).dataPointer
  let limb := limbViewLoadWord memory pointer limbIndex
  let shifted := JuliaLean.base.int.shr_Int limb (JInt.wrap .i64 8 * byteInLimb)
  let masked := JuliaLean.base.int.binop JuliaLean.base.int.band shifted (JInt.wrap .u8 0xff)
  JuliaLean.base.io.liftJl (JInt.convert "UInt8" .u8 masked.val)

/-- Complete iterator, including its default native Int state. Exhaustion
checks only state > num_bytes. Every other raw state uses unchecked indexing,
then increments with wrapping Int addition. No lower-bound check is inserted:
negative/zero states can reach a native read when supplied explicitly, and
typemax(Int) wraps to typemin(Int) after a successful final read.
Source reference: base/gmp.jl:894-897. -/
-- Source: base/gmp.jl:894-897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function Base.iterate(view::UnsafeLimbView, state::Int = 1)
--         state > view.num_bytes && return nothing
--         return @inbounds(view[state]), state + 1
--     end
-- /Source
def limbViewIterateExact {Rest : Type} (view : HeapLimbView)
    (state : Clong := JInt.wrap .i64 1) :
    JuliaLean.base.io.M (LimbViewMemory Rest) (Option (JInt .u8 × Clong)) := do
  if state.val > view.numBytes.val then return none
  let byte ← limbViewGetindexExact view state false
  pure (some (byte, state + JInt.wrap .i64 1))

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- Native GMP6.3 limb comparison loop on the installed 64-bit Unix/no-nails
ABI. The signed mp_size_t counter is decremented before its guard; each pass
reads the left word then the right word and stops at the first unequal pair.
The result is exactly native Cint -1,0,1, not an unsigned limb subtraction.
GMP explicitly allows count zero. Native interpretation requires nonnegative
count and real readable contiguous source spans; negative counts, invalid
pointers, and non-native memory states have no claimed Julia/C behavior.

Fuel only makes this finite native loop structurally recursive in Lean. The
entry supplies count.toNat+1, enough to perform every iteration and the final
negative-counter guard. Its zero-fuel initial result is unreachable before
termination on the native domain and is not an added source limit or error.
Source reference: base/gmp.jl:267; native GMP6.3 gmp-h.in:2080-2103,2171-2176;
mpn/generic/cmp.c:31-32 selects this implementation. -/
-- Source: base/gmp.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mpn_cmp(a::Ptr{Limb}, b::Ptr{Limb}, c) = ccall((:__gmpn_cmp, libgmp), Cint, (Ptr{Limb}, Ptr{Limb}, Clong), a, b, c)
-- /Source
def mpnCmpLoop {Rest : Type} (memory : LimbViewMemory Rest)
    (left right : JuliaLean.base.pointer.Ptr Limb) (counter : Clong) : Nat → Cint
  | 0 => JInt.wrap .i32 0
  | fuel + 1 =>
      let index : Clong := counter - JInt.wrap .i64 1
      if index.val < 0 then JInt.wrap .i32 0
      else
        let leftWord := limbViewLoadWord memory left.address (index + JInt.wrap .i64 1)
        let rightWord := limbViewLoadWord memory right.address (index + JInt.wrap .i64 1)
        if leftWord ≠ rightWord then
          if JuliaLean.base.int.lt rightWord leftWord then JInt.wrap .i32 1
          else JInt.wrap .i32 (-1)
        else mpnCmpLoop memory left right index fuel

/-- Concrete native entry for the full nonnegative count/readable-span domain.
The fuel bound is mathematical termination accounting only; the source counter,
indexed address calculations, loaded words and Cint return remain native.
No zero-count memory access, added negative-count error, snapshot list lookup,
or missing-word default occurs.
Source reference: base/gmp.jl:267; GMP6.3 gmp-h.in:2080-2103,2171-2176. -/
-- Source: base/gmp.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mpn_cmp(a::Ptr{Limb}, b::Ptr{Limb}, c) = ccall((:__gmpn_cmp, libgmp), Cint, (Ptr{Limb}, Ptr{Limb}, Clong), a, b, c)
-- /Source
def mpnCmpNative {Rest : Type} (memory : LimbViewMemory Rest)
    (left right : JuliaLean.base.pointer.Ptr Limb) (count : Clong) : Cint :=
  mpnCmpLoop memory left right count (count.val.toNat + 1)

/-- Complete pointer overload, including both generic count conversion stages.
Concrete left/right pointer cconvert calls precede count cconvert; concrete
left/right unsafe_convert calls precede count unsafe_convert and its Clong
assertion. Native memory is observed only afterward. Count conversion may
mutate aliases, throw, diverge, or return a wrong type; all effects/order are
retained. The source returns Cint directly without widening or cancellation.
Source reference: base/gmp.jl:267; base/essentials.jl:741,743; foreign-call conversion
order: doc/src/manual/calling-c-and-fortran-code.md:248-265. -/
-- Source: base/gmp.jl:267-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mpn_cmp(a::Ptr{Limb}, b::Ptr{Limb}, c) = ccall((:__gmpn_cmp, libgmp), Cint, (Ptr{Limb}, Ptr{Limb}, Clong), a, b, c)
-- /Source
def mpnCmpPointerDispatch {Rest Input Root Other : Type}
    (ops : ScalarConversionOps (JuliaLean.base.io.M (LimbViewMemory Rest)) Input Root Clong Other)
    (left right : JuliaLean.base.pointer.Ptr Limb) (count : Input) :
    JuliaLean.base.io.M (LimbViewMemory Rest) Cint := do
  let leftRoot := JuliaLean.base.essentials.cconvertPointer left
  let rightRoot := JuliaLean.base.essentials.cconvertPointer right
  let countRoot ← ops.cconvert count
  let leftPointer := JuliaLean.base.essentials.unsafeConvertPointerIdentity leftRoot
  let rightPointer := JuliaLean.base.essentials.unsafeConvertPointerIdentity rightRoot
  let nativeCount ← assertForeignScalar (← ops.unsafeConvert countRoot)
  let memory ← JuliaLean.base.io.getWorld
  pure (mpnCmpNative memory leftPointer rightPointer nativeCount)

/-- Complete BigInt forwarding overload. Both native data pointers are captured
from the live headers before entering any count-conversion stage. A custom
conversion may retarget either object afterward; this call still uses the
original pointers and the updated pointed-to memory. No numeric validity,
signed size, or allocated-capacity check is present in this source method.
Source reference: base/gmp.jl:268,267. -/
-- Source: base/gmp.jl:268-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mpn_cmp(a::BigInt, b::BigInt, c) = mpn_cmp(a.d, b.d, c)
-- /Source
def mpnCmpBigIntDispatch {Rest Input Root Other : Type}
    (ops : ScalarConversionOps (JuliaLean.base.io.M (LimbViewMemory Rest)) Input Root Clong Other)
    (left right : InitBigIntRef) (count : Input) :
    JuliaLean.base.io.M (LimbViewMemory Rest) Cint := do
  let memory ← JuliaLean.base.io.getWorld
  let leftPointer : JuliaLean.base.pointer.Ptr Limb :=
    ⟨(memory.heap.objects left.address).dataPointer⟩
  let rightPointer : JuliaLean.base.pointer.Ptr Limb :=
    ⟨(memory.heap.objects right.address).dataPointer⟩
  mpnCmpPointerDispatch ops leftPointer rightPointer count

/-- Concrete native Clong conversion instance for the limb-memory world. Every
Clong value is already of the required type and cconvert returns it directly;
unsafe_convert calls the installed same-type identity. Generic dispatch remains
fully effectful and is not constrained by any laws about custom conversions.
Source reference: base/essentials.jl:739,742; invoked by base/gmp.jl:267. -/
-- Source: base/essentials.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cconvert(::Type{T}, x) where {T} = x isa T ? x : convert(T, x) # do the conversion eagerly in most cases
-- /Source
-- Source: base/essentials.jl:742-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{T}, x::T) where {T} = x # unsafe_convert (like convert) defaults to assuming the convert occurred
-- /Source
def mpnNativeClongConversion (Rest : Type) :
    ScalarConversionOps (JuliaLean.base.io.M (LimbViewMemory Rest)) Clong Clong Clong Empty where
  cconvert := fun value => pure value
  unsafeConvert := fun value =>
    pure (.inl (JuliaLean.base.essentials.unsafeConvertIdentity value))

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2
open JuliaLean JuliaLean.base.float

/-- State/error interface for the complete conversion; Julia source: base/gmp.jl:411-466. -/
-- Source: base/gmp.jl:411-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (::Type{T})(x::BigInt, r::RoundingMode) where T<:IEEEFloat
--     xsize = abs(x.size)
--     xsize == 0 && return zero(T)
--     sb = isnegative(x)
--     top = unsafe_load(x.d, xsize)
--     s = top_set_bit(top)
--     nbits = s + (xsize - 1) * BITS_PER_LIMB # abs(x) is in [2^(nbits-1), 2^nbits)
--     if nbits > exponent_max(T) + 1
--         # abs(x) ≥ 2^(exponent_max(T) + 1), which is beyond the finite range of T
--         overflow = rounds_to_nearest(r)::Bool || rounds_away_from_zero(r, sb)::Bool
--         u = overflow ? ieee754_representation(T, sb, Val(:inf)) : ieee754_representation(T, sb, Val(:omega))
--         return reinterpret(T, u)
--     end
--     # Left-align the leading bits of abs(x) in the window m, and track whether any lower
--     # bit is set. The window holds at least precision(T) + 1 bits and at least one limb.
--     W = promote_type(Limb, uinttype(T))
--     wbits = 8 * sizeof(W)
--     m = top % W
--     filled = s
--     i = xsize - 1
--     while i > 0 && filled + BITS_PER_LIMB <= wbits
--         m = m << BITS_PER_LIMB | unsafe_load(x.d, i)
--         filled += BITS_PER_LIMB
--         i -= 1
--     end
--     sticky = false
--     if i > 0 && filled < wbits
--         l = unsafe_load(x.d, i)
--         k = wbits - filled
--         m = m << k | l >> (BITS_PER_LIMB - k)
--         sticky = l << k != 0
--         filled = wbits
--         i -= 1
--     end
--     while !sticky && i > 0
--         sticky = unsafe_load(x.d, i) != 0
--         i -= 1
--     end
--     m <<= wbits - filled
--     # round the leading precision(T) bits of m, using the bits below them
--     p = precision(T)
--     q = m >> (wbits - p)
--     rest = m << p
--     round_bit = rest >> (wbits - 1) != 0
--     sticky |= rest << 1 != 0
--     incr = if rounds_to_nearest(r)
--         tie_up = tie_breaker_is_to_even(r) ? isodd(q) : tie_breaker_rounds_away_from_zero(r, sb)
--         round_bit & (sticky | tie_up)
--     else
--         rounds_away_from_zero(r, sb)::Bool & (round_bit | sticky)
--     end
--     # a carry out of the significand correctly bumps the exponent, possibly up to infinity
--     signif = q % uinttype(T) & significand_mask(T)
--     u = ieee754_representation(T, sb, nbits - 1 + exponent_bias(T), signif) + incr
--     return reinterpret(T, u)
-- end
-- /Source
abbrev RoundingM (Rest A : Type) := JuliaLean.base.io.M (InitHeap Rest) A

/-- Full open query and subsequent result dispatch. Bool/native-word tags use
concrete Base code; all other return types remain open, including the final
reinterpret result. Julia source: base/gmp.jl:411-466. -/
-- Source: base/gmp.jl:411-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (::Type{T})(x::BigInt, r::RoundingMode) where T<:IEEEFloat
--     xsize = abs(x.size)
--     xsize == 0 && return zero(T)
--     sb = isnegative(x)
--     top = unsafe_load(x.d, xsize)
--     s = top_set_bit(top)
--     nbits = s + (xsize - 1) * BITS_PER_LIMB # abs(x) is in [2^(nbits-1), 2^nbits)
--     if nbits > exponent_max(T) + 1
--         # abs(x) ≥ 2^(exponent_max(T) + 1), which is beyond the finite range of T
--         overflow = rounds_to_nearest(r)::Bool || rounds_away_from_zero(r, sb)::Bool
--         u = overflow ? ieee754_representation(T, sb, Val(:inf)) : ieee754_representation(T, sb, Val(:omega))
--         return reinterpret(T, u)
--     end
--     # Left-align the leading bits of abs(x) in the window m, and track whether any lower
--     # bit is set. The window holds at least precision(T) + 1 bits and at least one limb.
--     W = promote_type(Limb, uinttype(T))
--     wbits = 8 * sizeof(W)
--     m = top % W
--     filled = s
--     i = xsize - 1
--     while i > 0 && filled + BITS_PER_LIMB <= wbits
--         m = m << BITS_PER_LIMB | unsafe_load(x.d, i)
--         filled += BITS_PER_LIMB
--         i -= 1
--     end
--     sticky = false
--     if i > 0 && filled < wbits
--         l = unsafe_load(x.d, i)
--         k = wbits - filled
--         m = m << k | l >> (BITS_PER_LIMB - k)
--         sticky = l << k != 0
--         filled = wbits
--         i -= 1
--     end
--     while !sticky && i > 0
--         sticky = unsafe_load(x.d, i) != 0
--         i -= 1
--     end
--     m <<= wbits - filled
--     # round the leading precision(T) bits of m, using the bits below them
--     p = precision(T)
--     q = m >> (wbits - p)
--     rest = m << p
--     round_bit = rest >> (wbits - 1) != 0
--     sticky |= rest << 1 != 0
--     incr = if rounds_to_nearest(r)
--         tie_up = tie_breaker_is_to_even(r) ? isodd(q) : tie_breaker_rounds_away_from_zero(r, sb)
--         round_bit & (sticky | tie_up)
--     else
--         rounds_away_from_zero(r, sb)::Bool & (round_bit | sticky)
--     end
--     # a carry out of the significand correctly bumps the exponent, possibly up to infinity
--     signif = q % uinttype(T) & significand_mask(T)
--     u = ieee754_representation(T, sb, nbits - 1 + exponent_bias(T), signif) + incr
--     return reinterpret(T, u)
-- end
-- /Source
structure RoundingOps (T : FTy) (Rest Mode Wrong Tie Or Inc Added Custom : Type) where
  nearest : Mode → RoundingM Rest (Sum Bool Wrong)
  away : Mode → Bool → RoundingM Rest (Sum Bool Wrong)
  evenTie : Mode → RoundingM Rest (Sum Bool Wrong)
  awayTie : Mode → Bool → RoundingM Rest (Sum Bool Tie)
  orCustom : Bool → Tie → RoundingM Rest (Sum Bool Or)
  andCustom : Bool → Or → RoundingM Rest (Sum Bool Inc)
  addCustom : JInt T.uintTy → Inc → RoundingM Rest (Sum (JInt T.uintTy) Added)
  reinterpretCustom : Added → RoundingM Rest (Sum (FV T) Custom)

/-- Preserve Bool assertion/condition TypeError at the source call point.
Source reference: base/gmp.jl:420,454-458. -/
-- Source: base/gmp.jl:454-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     round_bit = rest >> (wbits - 1) != 0
--     sticky |= rest << 1 != 0
--     incr = if rounds_to_nearest(r)
--         tie_up = tie_breaker_is_to_even(r) ? isodd(q) : tie_breaker_rounds_away_from_zero(r, sb)
--         round_bit & (sticky | tie_up)
--     else
-- /Source
def roundingBool {Rest Other : Type} (context : String) (value : Sum Bool Other) : RoundingM Rest Bool :=
  match value with
  | .inl b => pure b
  | .inr _ => throw (.foreignError "TypeError" context)

/-- One-based native limb load at the actual object data pointer. The native
readability domain and active-prefix coherence are explicit in the registered
property; no snapshot indexing or default word is supplied for invalid memory.
Source reference: base/gmp.jl:415,431,437,445; base/pointer.jl:151. -/
-- Source: base/gmp.jl:425-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # bit is set. The window holds at least precision(T) + 1 bits and at least one limb.
--     W = promote_type(Limb, uinttype(T))
--     wbits = 8 * sizeof(W)
--     m = top % W
--     filled = s
--     i = xsize - 1
--     while i > 0 && filled + BITS_PER_LIMB <= wbits
--         m = m << BITS_PER_LIMB | unsafe_load(x.d, i)
--         filled += BITS_PER_LIMB
--         i -= 1
--     end
--     sticky = false
--     if i > 0 && filled < wbits
--         l = unsafe_load(x.d, i)
--         k = wbits - filled
--         m = m << k | l >> (BITS_PER_LIMB - k)
--         sticky = l << k != 0
--         filled = wbits
--         i -= 1
--     end
--     while !sticky && i > 0
--         sticky = unsafe_load(x.d, i) != 0
--         i -= 1
-- /Source
def roundingLoad {Rest : Type} (heap : InitHeap Rest) (pointer : Culong)
    (index : Clong) : Limb :=
  heap.limbs (limbViewLoadAddress pointer index)

/-- Native window/counter loop. Nat fuel is only a recursion certificate,
initialized to the positive native index and decremented once per source
iteration. W=UInt64 on this ABI. Julia source: base/gmp.jl:429-434. -/
-- Source: base/gmp.jl:425-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     # bit is set. The window holds at least precision(T) + 1 bits and at least one limb.
--     W = promote_type(Limb, uinttype(T))
--     wbits = 8 * sizeof(W)
--     m = top % W
--     filled = s
--     i = xsize - 1
--     while i > 0 && filled + BITS_PER_LIMB <= wbits
--         m = m << BITS_PER_LIMB | unsafe_load(x.d, i)
--         filled += BITS_PER_LIMB
--         i -= 1
-- /Source
def roundingFill {Rest : Type} (heap : InitHeap Rest) (pointer : Culong) :
    Nat → Limb → Clong → Clong → Limb × Clong × Clong
  | 0, window, filled, index => (window, filled, index)
  | fuel+1, window, filled, index =>
    let bits : Clong := JInt.wrap .i64 64
    if index.val > 0 ∧ (filled + bits).val ≤ bits.val then
      let window := JuliaLean.base.int.bor
        (JuliaLean.base.int.shl_Int window bits) (roundingLoad heap pointer index)
      roundingFill heap pointer fuel window (filled + bits) (index - JInt.wrap .i64 1)
    else (window, filled, index)

/-- Descending sticky scan stops at the first nonzero limb. All arithmetic
uses JInt; fuel certifies termination. Julia source: base/gmp.jl:444-447. -/
-- Source: base/gmp.jl:444-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     end
--     while !sticky && i > 0
--         sticky = unsafe_load(x.d, i) != 0
--         i -= 1
-- /Source
def roundingSticky {Rest : Type} (heap : InitHeap Rest) (pointer : Culong) :
    Nat → Bool → Clong → Bool
  | 0, sticky, _ => sticky
  | fuel+1, sticky, index =>
    if !sticky && decide (index.val > 0) then
      let next := !(JuliaLean.base.int.eqSame (roundingLoad heap pointer index) (JInt.wrap .u64 0))
      roundingSticky heap pointer fuel next (index - JInt.wrap .i64 1)
    else sticky

/-- Concrete UInt64 parity, retaining isinteger, identity Integer constructor,
checked native remainder by the known positive literal two and native zero
test. The literal's UInt64 conversion is exact. Julia source: base/int.jl:161;
base/boot.jl:1220; called at base/gmp.jl:455. -/
-- Source: base/int.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isodd(n::Real) = isinteger(n) && !iszero(rem(Integer(n), 2))
-- /Source
-- Source: base/boot.jl:1220-1220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Integer(x::Integer) = x
-- /Source
-- Source: base/int.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::Unsigned, y::BitSigned) = rem(x, unsigned(abs(y)))
-- /Source
def roundingOdd (value : Limb) : Jl Bool := do
  if JuliaLean.base.number.isintegerInteger value then
    let integer := value
    let remainder ← JuliaLean.base.int.Generic.rem_Unsigned_BitSigned (s := .i64)
      JuliaLean.base.int.abs JuliaLean.base.int.unsigned JuliaLean.base.int.remSame
      integer (JInt.wrap .i64 2)
    pure (!(JuliaLean.base.int.eqSame remainder (JInt.wrap .u64 0)))
  else pure false

/-- Complete body with all reads before the first selected query, and the
source early overflow branch. Fixed Bool operations, UInt+Bool and native
reinterpret call installed models. Unfixed results alone use open dispatch;
awayTie and its downstream operators have no Bool/result assertion.
Source reference: base/gmp.jl:411-466. -/
-- Source: base/gmp.jl:411-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (::Type{T})(x::BigInt, r::RoundingMode) where T<:IEEEFloat
--     xsize = abs(x.size)
--     xsize == 0 && return zero(T)
--     sb = isnegative(x)
--     top = unsafe_load(x.d, xsize)
--     s = top_set_bit(top)
--     nbits = s + (xsize - 1) * BITS_PER_LIMB # abs(x) is in [2^(nbits-1), 2^nbits)
--     if nbits > exponent_max(T) + 1
--         # abs(x) ≥ 2^(exponent_max(T) + 1), which is beyond the finite range of T
--         overflow = rounds_to_nearest(r)::Bool || rounds_away_from_zero(r, sb)::Bool
--         u = overflow ? ieee754_representation(T, sb, Val(:inf)) : ieee754_representation(T, sb, Val(:omega))
--         return reinterpret(T, u)
--     end
--     # Left-align the leading bits of abs(x) in the window m, and track whether any lower
--     # bit is set. The window holds at least precision(T) + 1 bits and at least one limb.
--     W = promote_type(Limb, uinttype(T))
--     wbits = 8 * sizeof(W)
--     m = top % W
--     filled = s
--     i = xsize - 1
--     while i > 0 && filled + BITS_PER_LIMB <= wbits
--         m = m << BITS_PER_LIMB | unsafe_load(x.d, i)
--         filled += BITS_PER_LIMB
--         i -= 1
--     end
--     sticky = false
--     if i > 0 && filled < wbits
--         l = unsafe_load(x.d, i)
--         k = wbits - filled
--         m = m << k | l >> (BITS_PER_LIMB - k)
--         sticky = l << k != 0
--         filled = wbits
--         i -= 1
--     end
--     while !sticky && i > 0
--         sticky = unsafe_load(x.d, i) != 0
--         i -= 1
--     end
--     m <<= wbits - filled
--     # round the leading precision(T) bits of m, using the bits below them
--     p = precision(T)
--     q = m >> (wbits - p)
--     rest = m << p
--     round_bit = rest >> (wbits - 1) != 0
--     sticky |= rest << 1 != 0
--     incr = if rounds_to_nearest(r)
--         tie_up = tie_breaker_is_to_even(r) ? isodd(q) : tie_breaker_rounds_away_from_zero(r, sb)
--         round_bit & (sticky | tie_up)
--     else
--         rounds_away_from_zero(r, sb)::Bool & (round_bit | sticky)
--     end
--     # a carry out of the significand correctly bumps the exponent, possibly up to infinity
--     signif = q % uinttype(T) & significand_mask(T)
--     u = ieee754_representation(T, sb, nbits - 1 + exponent_bias(T), signif) + incr
--     return reinterpret(T, u)
-- end
-- /Source
def explicitFloatDispatch {T : FTy} {Rest Mode Wrong Tie Or Inc Added Custom : Type}
    (ops : RoundingOps T Rest Mode Wrong Tie Or Inc Added Custom)
    (input : InitBigIntRef) (mode : Mode) : RoundingM Rest (Sum (FV T) Custom) := do
  let heap ← JuliaLean.base.io.getWorld
  let cell := heap.objects input.address
  let x := cell.value
  let pointer := cell.dataPointer
  let xsize : Cint := if x.size.val < 0 then -x.size else x.size
  if xsize.val = 0 then return .inl (zero_float T)
  let sb := JuliaLean.base.gmp.isnegative x
  let top := roundingLoad heap pointer (JInt.wrap .i64 xsize.val)
  let s := JuliaLean.base.int.top_set_bit top
  let one : Clong := JInt.wrap .i64 1
  let bits : Clong := JInt.wrap .i64 64
  let nbits := s + (JInt.wrap .i64 xsize.val - one) * bits
  if nbits > exponent_max T + one then
    let near ← roundingBool "rounds_to_nearest ::Bool" (← ops.nearest mode)
    let overflow ← if near then pure true else
      roundingBool "rounds_away_from_zero ::Bool" (← ops.away mode sb)
    let u := if overflow then ieee754_representation_inf T sb
      else ieee754_representation_omega T sb
    return .inl (reinterpret_Float_Int T u)
  let wbits := JuliaLean.base.int.mul (JInt.wrap .i64 8) (JInt.wrap .i64 8)
  let m : Limb := JuliaLean.base.int.remT .u64 top
  let index := JInt.wrap .i64 xsize.val - one
  let (m, filled, index) := roundingFill heap pointer index.val.toNat m s index
  let (m, filled, index, sticky) :=
    if index.val > 0 ∧ filled < wbits then
      let limb := roundingLoad heap pointer index
      let k := wbits - filled
      let m := JuliaLean.base.int.bor (JuliaLean.base.int.shl_Int m k)
        (JuliaLean.base.int.shr_Int limb (bits - k))
      let sticky := !(JuliaLean.base.int.eqSame (JuliaLean.base.int.shl_Int limb k) (JInt.wrap .u64 0))
      (m, wbits, index - one, sticky)
    else (m, filled, index, false)
  let sticky := roundingSticky heap pointer index.val.toNat sticky index
  let m := JuliaLean.base.int.shl_Int m (wbits - filled)
  let p := precision_Type_default T
  let q := JuliaLean.base.int.shr_Int m (wbits - p)
  let rest := JuliaLean.base.int.shl_Int m p
  let roundBit := !(JuliaLean.base.int.eqSame
    (JuliaLean.base.int.shr_Int rest (wbits - one)) (JInt.wrap .u64 0))
  let sticky := JuliaLean.base.bool.orBool sticky
    (!(JuliaLean.base.int.eqSame (JuliaLean.base.int.shl_Int rest one) (JInt.wrap .u64 0)))
  let near ← roundingBool "if rounds_to_nearest" (← ops.nearest mode)
  let increment : Sum Bool Inc ← if near then do
      let even ← roundingBool "condition tie_breaker_is_to_even" (← ops.evenTie mode)
      let tie : Sum Bool Tie ← if even then do
          let odd ← JuliaLean.base.io.liftJl (roundingOdd q)
          pure (.inl odd)
        else ops.awayTie mode sb
      let joined : Sum Bool Or ← match tie with
        | .inl b => pure (.inl (JuliaLean.base.bool.orBool sticky b))
        | .inr custom => ops.orCustom sticky custom
      match joined with
      | .inl b => pure (.inl (JuliaLean.base.bool.andBool roundBit b))
      | .inr custom => ops.andCustom roundBit custom
    else do
      let away ← roundingBool "rounds_away_from_zero ::Bool" (← ops.away mode sb)
      pure (.inl (JuliaLean.base.bool.andBool away (JuliaLean.base.bool.orBool roundBit sticky)))
  let signif := JuliaLean.base.int.band (JuliaLean.base.int.remT T.uintTy q) (significand_mask T)
  let packed := ieee754_representation T sb (nbits - one + exponent_bias T) signif
  let added : Sum (JInt T.uintTy) Added ← match increment with
    | .inl b => pure (.inl (JuliaLean.base.int.op_Integer T.uintTy JuliaLean.base.int.add
        (JuliaLean.base.int.remT T.uintTy) (JuliaLean.base.int.rem_Bool_Type T.uintTy) packed b))
    | .inr custom => ops.addCustom packed custom
  match added with
  | .inl u => pure (.inl (reinterpret_Float_Int T u))
  | .inr custom => ops.reinterpretCustom custom

/-- Seven public modes use installed source constants; the generic Mode
parameter above retains arbitrary extension tags. Julia source: base/rounding.jl:50-110. -/
-- Source: base/rounding.jl:50-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     RoundNearest
-- 
-- The default rounding mode. Rounds to the nearest integer, with ties (fractional values of
-- 0.5) being rounded to the nearest even integer.
-- """
-- const RoundNearest = RoundingMode{:Nearest}()
-- 
-- """
--     RoundToZero
-- 
-- [`round`](@ref) using this rounding mode is an alias for [`trunc`](@ref).
-- """
-- const RoundToZero = RoundingMode{:ToZero}()
-- 
-- """
--     RoundUp
-- 
-- [`round`](@ref) using this rounding mode is an alias for [`ceil`](@ref).
-- """
-- const RoundUp = RoundingMode{:Up}()
-- 
-- """
--     RoundDown
-- 
-- [`round`](@ref) using this rounding mode is an alias for [`floor`](@ref).
-- """
-- const RoundDown = RoundingMode{:Down}()
-- 
-- """
--     RoundFromZero
-- 
-- Rounds away from zero.
-- 
-- !!! compat "Julia 1.9"
--     `RoundFromZero` requires at least Julia 1.9. Prior versions support
--     `RoundFromZero` for `BigFloat`s only.
-- 
-- # Examples
-- ```jldoctest
-- julia> BigFloat("1.0000000000000001", 5, RoundFromZero)
-- 1.06
-- ```
-- """
-- const RoundFromZero = RoundingMode{:FromZero}()
-- 
-- """
--     RoundNearestTiesAway
-- 
-- Rounds to nearest integer, with ties rounded away from zero (C/C++
-- [`round`](@ref) behaviour).
-- """
-- const RoundNearestTiesAway = RoundingMode{:NearestTiesAway}()
-- 
-- """
--     RoundNearestTiesUp
-- 
-- Rounds to nearest integer, with ties rounded toward positive infinity (Java/JavaScript
-- [`round`](@ref) behaviour).
-- """
-- const RoundNearestTiesUp = RoundingMode{:NearestTiesUp}()
-- /Source
def roundingBaseMode : RoundingMode → JuliaLean.base.rounding.RoundingMode
  | .Nearest => JuliaLean.base.rounding.RoundNearest
  | .ToZero => JuliaLean.base.rounding.RoundToZero
  | .Up => JuliaLean.base.rounding.RoundUp
  | .Down => JuliaLean.base.rounding.RoundDown
  | .FromZero => JuliaLean.base.rounding.RoundFromZero
  | .NearestTiesAway => JuliaLean.base.rounding.RoundNearestTiesAway
  | .NearestTiesUp => JuliaLean.base.rounding.RoundNearestTiesUp

/-- Concrete adapter calls actual installed mode queries, with no callee
laws. Empty custom-result branches are unreachable by construction.
Source reference: base/rounding.jl:115-127; base/gmp.jl:420,454-459. -/
-- Source: base/rounding.jl:115-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rounds_to_nearest(::RoundingMode) = false
-- rounds_to_nearest(::RoundingMode{:Nearest}) = true
-- rounds_to_nearest(::RoundingMode{:NearestTiesUp}) = true
-- rounds_to_nearest(::RoundingMode{:NearestTiesAway}) = true
-- rounds_away_from_zero(::RoundingMode{:Up},   sign_bit::Bool) = !sign_bit
-- rounds_away_from_zero(::RoundingMode{:Down}, sign_bit::Bool) = sign_bit
-- rounds_away_from_zero(::RoundingMode{:FromZero}, ::Bool) = true
-- rounds_away_from_zero(::RoundingMode{:ToZero},   ::Bool) = false
-- tie_breaker_is_to_even(::RoundingMode{:Nearest}) = true
-- tie_breaker_is_to_even(::RoundingMode{:NearestTiesUp}) = false
-- tie_breaker_is_to_even(::RoundingMode{:NearestTiesAway}) = false
-- tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesUp}, sign_bit::Bool) = !sign_bit
-- tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesAway},       ::Bool) = true
-- /Source
def nativeRoundingOps (T : FTy) (Rest : Type) :
    RoundingOps T Rest RoundingMode Empty Empty Empty Empty Empty Empty where
  nearest := fun mode => pure (.inl (JuliaLean.base.rounding.roundsToNearest (roundingBaseMode mode)))
  away := fun mode sign => do
    pure (.inl (← JuliaLean.base.io.liftJl
      (JuliaLean.base.rounding.roundsAwayFromZero (roundingBaseMode mode) sign)))
  evenTie := fun mode => do
    pure (.inl (← JuliaLean.base.io.liftJl
      (JuliaLean.base.rounding.tieBreakerIsToEven (roundingBaseMode mode))))
  awayTie := fun mode sign => do
    pure (.inl (← JuliaLean.base.io.liftJl
      (JuliaLean.base.rounding.tieBreakerRoundsAway (roundingBaseMode mode) sign)))
  orCustom := fun _ impossible => nomatch impossible
  andCustom := fun _ impossible => nomatch impossible
  addCustom := fun _ impossible => nomatch impossible
  reinterpretCustom := fun impossible => nomatch impossible

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2

open JuliaLean

/-- Complete concrete Bool remainder, including its eager native read at zero.
The left Bool is evaluated before unsafe_load, but there is no conditional
branch around the load. The current object's actual pointer is read and its
first UInt64 word is passed through the installed Integer % Bool method;
the two concrete Bool operands then pass through installed bitwise &.
The native memory domain therefore requires a readable first word even for
zero, where GMP's initialized dummy pointer supplies it. No snapshot default,
invented invalid-memory exception, or short-circuit replacement is used.
Source reference: base/gmp.jl:367; unsafe_load: base/pointer.jl:151;
native remainder: base/int.jl:699; Bool &: base/bool.jl:14. -/
-- Source: base/gmp.jl:367-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::BigInt, ::Type{Bool}) = !iszero(x) & unsafe_load(x.d) % Bool # never unsafe here
-- /Source
def remBoolHeapExact {Rest : Type} (input : InitBigIntRef) :
    JuliaLean.base.io.M (LimbViewMemory Rest) Bool := do
  let memory ← JuliaLean.base.io.getWorld
  let nonzero := JuliaLean.base.bool.notBool
    (JuliaLean.base.gmp.iszero (memory.heap.objects input.address).value)
  let pointer := (memory.heap.objects input.address).dataPointer
  let word := limbViewLoadWord memory pointer (JInt.wrap .i64 1)
  let lowBit := JuliaLean.base.int.rem_Integer_Bool word
  pure (JuliaLean.base.bool.andBool nonzero lowBit)

end JuliaLean.base.gmp.Models2Group2


namespace JuliaLean.base.gmp.Models2Group2
open JuliaLean

/-- An immutable Rational{BigInt} retains references to its two mutable integers. Equal references are allowed, including numerator/denominator aliasing.
Source reference: base/rational.jl:9-15; the rooted MPQ field is base/gmp.jl:966-975. -/
-- Source: base/rational.jl:9-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Rational{T<:Integer} <: Real
--     num::T
--     den::T
-- 
--     # Unexported inner constructor of Rational that bypasses all checks
--     global unsafe_rational(::Type{T}, num, den) where {T} = new{T}(num, den)
-- end
-- /Source
-- Source: base/gmp.jl:966-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct _MPQ
--     num_alloc::Cint
--     num_size::Cint
--     num_d::Ptr{Limb}
--     den_alloc::Cint
--     den_size::Cint
--     den_d::Ptr{Limb}
--     # to prevent GC
--     rat::Rational{BigInt}
-- end
-- /Source
structure RationalReferences where
  numerator : InitBigIntRef
  denominator : InitBigIntRef
  deriving DecidableEq

/-- The source mutable _MPQ header keeps native allocation/count/pointer fields and the rooted Rational references. This describes existing objects only; it does not model or claim a constructor.
Source reference: base/gmp.jl:966-975. -/
-- Source: base/gmp.jl:966-975 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct _MPQ
--     num_alloc::Cint
--     num_size::Cint
--     num_d::Ptr{Limb}
--     den_alloc::Cint
--     den_size::Cint
--     den_d::Ptr{Limb}
--     # to prevent GC
--     rat::Rational{BigInt}
-- end
-- /Source
structure MPQHeaderCell where
  numAlloc : Cint
  numSize : Cint
  numPointer : Culong
  denAlloc : Cint
  denSize : Cint
  denPointer : Culong
  rat : RationalReferences

/-- A typed reference identifies the existing mutable _MPQ object.
Source reference: base/gmp.jl:977-977. -/
-- Source: base/gmp.jl:977-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const mpq_t = Ref{_MPQ}
-- /Source
structure MPQHeaderRef where
  address : Culong
  deriving DecidableEq

/-- Separate typed object maps retain MPQ identity, BigInt identity, native limb memory, and unrelated state. Header synchronization does not allocate or alter the MPQ map.
Source reference: base/gmp.jl:994-1002. -/
-- Source: base/gmp.jl:994-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sync_rational!(xq::_MPQ)
--     xq.rat.num.alloc = xq.num_alloc
--     xq.rat.num.size  = xq.num_size
--     xq.rat.num.d     = xq.num_d
--     xq.rat.den.alloc = xq.den_alloc
--     xq.rat.den.size  = xq.den_size
--     xq.rat.den.d     = xq.den_d
--     return xq.rat
-- end
-- /Source
structure RationalSyncHeap (Rest : Type) where
  integers : InitHeap Rest
  rawObjects : Culong → MPQHeaderCell
  liveRawObjects : Culong → Bool

/-- Update only the mathematical representation shadow after a size/pointer store. The computation adds no Julia memory access or store.
Source reference: base/gmp.jl:994-1002. -/
-- Source: base/gmp.jl:994-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sync_rational!(xq::_MPQ)
--     xq.rat.num.alloc = xq.num_alloc
--     xq.rat.num.size  = xq.num_size
--     xq.rat.num.d     = xq.num_d
--     xq.rat.den.alloc = xq.den_alloc
--     xq.rat.den.size  = xq.den_size
--     xq.rat.den.d     = xq.den_d
--     return xq.rat
-- end
-- /Source
def syncValueShadow (value : BigInt) : BigInt :=
  let magnitude := limbMagnitude (value.d.take value.size.val.natAbs)
  { value with val := if value.size.val < 0 then -(magnitude : Int) else (magnitude : Int) }

/-- One concrete alloc-field assignment. Every other object and source field is preserved.
Source reference: base/gmp.jl:994-1002. -/
-- Source: base/gmp.jl:994-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sync_rational!(xq::_MPQ)
--     xq.rat.num.alloc = xq.num_alloc
--     xq.rat.num.size  = xq.num_size
--     xq.rat.num.d     = xq.num_d
--     xq.rat.den.alloc = xq.den_alloc
--     xq.rat.den.size  = xq.den_size
--     xq.rat.den.d     = xq.den_d
--     return xq.rat
-- end
-- /Source
def syncStoreAlloc {Rest : Type} (heap : InitHeap Rest)
    (target : InitBigIntRef) (alloc : Cint) : InitHeap Rest :=
  let cell := heap.objects target.address
  { heap with objects := fun a => if a = target.address then
      { cell with value := { cell.value with alloc := alloc } } else heap.objects a }

/-- One concrete size-field assignment, with only the redundant mathematical shadow recomputed.
Source reference: base/gmp.jl:994-1002. -/
-- Source: base/gmp.jl:994-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sync_rational!(xq::_MPQ)
--     xq.rat.num.alloc = xq.num_alloc
--     xq.rat.num.size  = xq.num_size
--     xq.rat.num.d     = xq.num_d
--     xq.rat.den.alloc = xq.den_alloc
--     xq.rat.den.size  = xq.den_size
--     xq.rat.den.d     = xq.den_d
--     return xq.rat
-- end
-- /Source
def syncStoreSize {Rest : Type} (heap : InitHeap Rest)
    (target : InitBigIntRef) (size : Cint) : InitHeap Rest :=
  let cell := heap.objects target.address
  let value := syncValueShadow { cell.value with size := size }
  { heap with objects := fun a => if a = target.address then
      { cell with value := value } else heap.objects a }

/-- One native pointer-field assignment. The finite list is the representation view of the current allocation at that pointer, obtained from the existing native memory map; constructing this Lean view allocates no Julia object and writes no limb. Addresses use wrapping native UInt64 arithmetic. Raw nonpositive allocation has an empty shadow view; the native fields are still copied verbatim.
Source reference: base/gmp.jl:994-1002. -/
-- Source: base/gmp.jl:994-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sync_rational!(xq::_MPQ)
--     xq.rat.num.alloc = xq.num_alloc
--     xq.rat.num.size  = xq.num_size
--     xq.rat.num.d     = xq.num_d
--     xq.rat.den.alloc = xq.den_alloc
--     xq.rat.den.size  = xq.den_size
--     xq.rat.den.d     = xq.den_d
--     return xq.rat
-- end
-- /Source
def syncStorePointer {Rest : Type} (heap : InitHeap Rest)
    (target : InitBigIntRef) (pointer : Culong) : InitHeap Rest :=
  let cell := heap.objects target.address
  let storage := (List.range cell.value.alloc.val.toNat).map fun (i : Nat) =>
    heap.limbs (pointer + JInt.wrap .u64 8 * JInt.wrap .u64 (Int.ofNat i))
  let value := syncValueShadow { cell.value with d := storage }
  { heap with objects := fun a => if a = target.address then
      { cell with value := value, dataPointer := pointer } else heap.objects a }

/-- Complete synchronization: the six field writes occur in source order and always use the current integer heap. If numerator and denominator alias, the later denominator writes win. The original rooted Rational references are returned. The MPQ object and all native limb memory remain unchanged.
Source reference: base/gmp.jl:994-1002. -/
-- Source: base/gmp.jl:994-1002 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sync_rational!(xq::_MPQ)
--     xq.rat.num.alloc = xq.num_alloc
--     xq.rat.num.size  = xq.num_size
--     xq.rat.num.d     = xq.num_d
--     xq.rat.den.alloc = xq.den_alloc
--     xq.rat.den.size  = xq.den_size
--     xq.rat.den.d     = xq.den_d
--     return xq.rat
-- end
-- /Source
def syncRationalBang {Rest : Type} (heap : RationalSyncHeap Rest)
    (source : MPQHeaderRef) : RationalReferences × RationalSyncHeap Rest :=
  let raw := heap.rawObjects source.address
  let h1 := syncStoreAlloc heap.integers raw.rat.numerator raw.numAlloc
  let h2 := syncStoreSize h1 raw.rat.numerator raw.numSize
  let h3 := syncStorePointer h2 raw.rat.numerator raw.numPointer
  let h4 := syncStoreAlloc h3 raw.rat.denominator raw.denAlloc
  let h5 := syncStoreSize h4 raw.rat.denominator raw.denSize
  let h6 := syncStorePointer h5 raw.rat.denominator raw.denPointer
  (raw.rat, { heap with integers := h6 })

end JuliaLean.base.gmp.Models2Group2

namespace JuliaLean.IntArith.NumberTheory

open JuliaLean

/-- Semantic primitive boundary for `MPZ.gcdext`,
`base/gmp.jl:255-260,676-677`. GMP's documented centered coefficients,
including `abs(a)=abs(b)` and the half-period tie, are selected from an
exact Euclidean witness. This models the external primitive's result,
not GMP's internal implementation. Specification:
https://gmplib.org/manual/Number-Theoretic-Functions#index-mpz_005fgcdext -/
def gmpGcdext (a b : Int) : Jl (Int × Int × Int) := do
  let (g, s, _) ← gcdxVal none a b
  if a.natAbs = b.natAbs then pure (g, 0, b.sign)
  else if b = 0 then pure (g, a.sign, 0)
  else
    let period := ((b.tdiv g).natAbs : Int)
    let u := s % period
    let u := if 2 * u > period then u - period
      else if 2 * u = period ∧ a < 0 then -u else u
    pure (g, u, (g - a * u).tdiv b)

/-- Julia's BigInt coefficient normalization after the GMP primitive,
`base/gmp.jl:676-687`. -/
def gmpGcdx (a b : Int) : Jl (Int × Int × Int) := do
  let (g, s, t) ← gmpGcdext a b
  if t = 0 then
    if a = b then pure (g, t, s)
    else if a.natAbs = b.natAbs then pure (g, t, -s)
    else pure (g, s, t)
  else pure (g, s, t)

/-- Semantic primitive boundary for `MPZ.powm`, `base/gmp.jl:250-253`.
The external GMP API computes modular exponentiation, including inversion
for negative exponents. The executable specification uses exact integers;
it does not claim to model GMP's internal exponentiation implementation.
Zero modulus and a missing negative-power inverse raise DivideError.
Specification: https://gmplib.org/manual/Integer-Exponentiation -/
def gmpPowm (x p m : Int) : Jl Int := do
  if m = 0 then .error .divideError
  else
    let mm := (m.natAbs : Int)
    if p = 0 then pure (1 % mm)
    else
      let bb ← if p < 0 then do
          let (g, s, _) ← gmpGcdext x mm
          if g ≠ 1 then .error .divideError else pure (s % mm)
        else pure (x % mm)
      powermodLoop none none p.natAbs mm 1 bb

/-- BigInt powermod sign normalization, `base/gmp.jl:669-674`. -/
def gmpPowermod (x p m : Int) : Jl Int := do
  let r ← gmpPowm x p m
  pure (if m < 0 ∧ r > 0 then r + m else r)

end JuliaLean.IntArith.NumberTheory

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-! ## Limbs -/

/-- Number of 64-bit limbs of `abs(x)`, i.e. `abs(x.size)` (`base/gmp.jl:68-72`). -/
def nlimbs (x : Int) : Nat := if x = 0 then 0 else x.natAbs.log2 / 64 + 1

/-- `unsafe_load(x.d, l + 1)`: limb `l` (least significant first) of `abs(x)`. -/
def limb (x : Int) (l : Nat) : Nat := x.natAbs / 2 ^ (64 * l) % 2 ^ 64

/-- `x.size`: signed limb count. -/
def size (x : Int) : Int := if x < 0 then -(nlimbs x : Int) else nlimbs x

/-! ## Division (`base/gmp.jl:495-514,625-626`) -/

/-- `mpz_tdiv_q` (GMP manual 5.6 "Division Functions": `tdiv` truncates `q` toward zero);
division by zero raises `DivideError`. -/
def tdivQ (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.tdiv d)
/-- `mpz_tdiv_r`: `r = n - q*d` with `q` truncated, so `r` has the sign of `n`. -/
def tdivR (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.tmod d)
/-- `mpz_fdiv_q`: `q` rounded toward minus infinity. -/
def fdivQ (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.fdiv d)
/-- `mpz_fdiv_r`: `r = n - q*d` with `q` floored, so `r` has the sign of `d`. -/
def fdivR (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (n.fmod d)
/-- `mpz_cdiv_q`: `q` rounded toward plus infinity. -/
def cdivQ (n d : Int) : Jl Int := if d = 0 then .error .divideError else .ok (-((-n).fdiv d))

/-- `div(x::BigInt, y::BigInt) = div(x, y, RoundToZero)`, `base/gmp.jl:505-512`. -/
def div (x y : Int) : Jl Int := tdivQ x y
/-- `rem(x::BigInt, y::BigInt) = MPZ.tdiv_r(x, y)`, `base/gmp.jl:495-503`. -/
def rem (x y : Int) : Jl Int := tdivR x y
/-- `mod(x::BigInt, y::BigInt) = MPZ.fdiv_r(x, y)`, `base/gmp.jl:495-503`. -/
def mod (x y : Int) : Jl Int := fdivR x y
/-- `fld(x::BigInt, y::BigInt) = div(x, y, RoundDown)`, `base/gmp.jl:513`. -/
def fld (x y : Int) : Jl Int := fdivQ x y
/-- `cld(x::BigInt, y::BigInt) = div(x, y, RoundUp)`, `base/gmp.jl:514`. -/
def cld (x y : Int) : Jl Int := cdivQ x y
/-- `divrem(x::BigInt, y::BigInt) = MPZ.tdiv_qr(x, y)`, `base/gmp.jl:625`. -/
def divrem (x y : Int) : Jl (Int × Int) := do pure (← tdivQ x y, ← tdivR x y)

/-! ## isqrt (`base/gmp.jl:637`) -/

/-- Floor square root of a natural number. -/
def natSqrt (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc k => if k * k ≤ n then k else acc) 0

/-- `mpz_sqrt` (GMP manual 5.8: "Set rop to the truncated integer part of the square root of
op"). A negative operand raises GMP's `SQRT_OF_NEGATIVE` exception (`SIGFPE`), reported as
`DivideError`. -/
def mpzSqrt (x : Int) : Jl Int := if x < 0 then .error .divideError else .ok (natSqrt x.toNat)

/-- `isqrt(x::BigInt) = MPZ.sqrt(x)`, `base/gmp.jl:637`. -/
def isqrt (x : Int) : Jl Int := mpzSqrt x

/-! ## Powers (`base/gmp.jl:639-674`) -/

/-- `bigint_pow(x::BigInt, y::Integer)`, `base/gmp.jl:641-661`, for exponents that fit
`Culong` (`x^convert(Culong, y)` is `mpz_pow_ui`, the exact power). -/
def bigintPow (x y : Int) : Jl Int :=
  if x = 1 then .ok x
  else if x = -1 then .ok (if y % 2 ≠ 0 then x else -x)
  else if y < 0 then .error (.domainError "`y` cannot be negative.")
  else if y > 2 ^ 64 - 1 then
    if x = 0 then .ok x else .error (.overflowError "exponent is too large")
  else .ok (x ^ y.toNat)

/-- `powermod(x::BigInt, p::BigInt, m::BigInt)`, `base/gmp.jl:669-672`, reusing the GMP
`mpz_powm` primitive of the IntArith area. -/
def powermod (x p m : Int) : Jl Int := IntArith.NumberTheory.gmpPowermod x p m

/-! ## invmod (`base/gmp.jl:518-535`) -/

/-- `mpz_invert` (GMP manual 5.9 "Number Theoretic Functions"): if an inverse of `a` modulo
`b` exists, return it in `[0, abs(b))`; otherwise report failure. The documented result is
the unique such residue (`b ≠ 0`; Julia never calls it with `b = 0`). -/
def mpzInvert (a b : Int) : Option Int :=
  ((List.range b.natAbs).find? (fun (z : Nat) => ((z : Int) * a - 1) % (b.natAbs : Int) = 0)).map
    (fun (z : Nat) => (z : Int))

/-- `invmod(x::BigInt, y::BigInt)`, `base/gmp.jl:518-535`. -/
def invmod (x y : Int) : Jl Int :=
  let ya := (y.natAbs : Int)
  if ya = 1 then .ok 0
  else if y = 0 then .error (.domainError "")
  else match mpzInvert x ya with
    | none => .error (.domainError "")
    | some z => .ok (if y < 0 then z + y else z)

/-! ## Conversion to machine integers (`base/gmp.jl:367-407`) -/

/-- `flipsign(u, x.size)` for a `BitInteger` `u`: negation (wrapping) when `x < 0`. -/
def flipsignTy {t : IntTy} (u : JInt t) (x : Int) : JInt t := if x < 0 then -u else u

/-- `rem(x::BigInt, ::Type{T})`, `base/gmp.jl:369-378`: the least significant limb for types of
at most 64 bits, else the two low limbs shifted into place, then `flipsign`. -/
def remTy (t : IntTy) (x : Int) : JInt t :=
  if t.bits ≤ 64 then
    if x = 0 then JInt.lit t 0 else flipsignTy (JInt.wrap t (limb x 0)) x
  else
    let n := min (nlimbs x) ((t.bits / 8 + 7) / 8)
    let u := (List.range n).foldl
      (fun u l => u + JInt.wrap t (limb x l) * JInt.wrap t (2 ^ (64 * l))) (JInt.lit t 0)
    flipsignTy u x

/-- `(::Type{T})(x::BigInt)` for unsigned `T` of at least 64 bits, `base/gmp.jl:390-393`. -/
def toUnsignedWide (t : IntTy) (x : Int) : Jl (JInt t) :=
  if 0 ≤ size x ∧ size x ≤ ((t.bits / 8 + 7) / 8 : Nat) then .ok (remTy t x)
  else .error (.inexactError t.name)

/-- `(::Type{T})(x::BigInt)` for signed `T` of at least 64 bits, `base/gmp.jl:396-407`. -/
def toSignedWide (t : IntTy) (x : Int) : Jl (JInt t) :=
  let n := nlimbs x
  if n ≤ (t.bits / 8 + 7) / 8 then
    let y := remTy t x
    if decide (0 < x) != decide (0 < y.val) then .error (.inexactError t.name) else .ok y
  else .error (.inexactError t.name)

/-- `T(x::BigInt)` for every `BitInteger` `T`, `base/gmp.jl:387-407`. Types narrower than a
limb go through `convert(Limb, x)` or `convert(Int64, x)` and then `convert(T, ·)`. -/
def toIntTy (t : IntTy) (x : Int) : Jl (JInt t) :=
  if t.signed then
    if t.bits < 64 then do
      let y ← toSignedWide .i64 x
      JInt.convert (t.name) t y.val
    else toSignedWide t x
  else
    if t.bits < 64 then do
      let y ← toUnsignedWide .u64 x
      JInt.convert (t.name) t y.val
    else toUnsignedWide t x

/-! ## Hashing (`base/gmp.jl:917-955`) -/

/-- `trailing_zeros(x::BigInt)` for nonzero `x` (`mpz_scan1(x, 0)`). -/
def trailingZerosBig (x : Int) : Nat := go x.natAbs (x.natAbs.log2 + 1)
where
  go (m : Nat) : Nat → Nat
    | 0 => 0
    | k + 1 => if m % 2 == 1 || m == 0 then 0 else 1 + go (m / 2) k

/-- `hash(x::BigInt, h)` on 64-bit systems, `base/gmp.jl:917-955`, in the hash-term model of
`JuliaLean.Promotion.Hash`. The byte-hashing tail `h ⊻= (sz < 0); hash_bytes(limb_view, h)` is
`hash_integer` (`base/hashing.jl:147-160`) of the signed integer whose magnitude is
`abs(x) >> (8 * trailing_zero_bytes)`; it is the term `.int v h`. -/
def hashBig (x : Int) (h : HTerm) : HTerm :=
  let sz := size x
  if sz = 0 then hashI64 0 h
  else if sz = 1 then .u64 (limb x 0) h
  else if sz = -1 ∧ limb x 0 ≤ 2 ^ 63 then hashI64 (-(limb x 0 : Int)) h
  else
    let pow := trailingZerosBig x
    let nd := x.natAbs.log2 + 1
    let idx := pow / 64
    let shift := pow % 64
    let lw := if shift = 0 then limb x idx
      else (limb x (idx + 1) * 2 ^ (64 - shift) % 2 ^ 64 + limb x idx / 2 ^ shift) % 2 ^ 64
    if nd ≤ 1024 ∧ nd - pow ≤ 53 then
      let v : Int := if x < 0 then -(lw : Int) else lw
      hashF64 (Fl.roundRat (v * 2 ^ pow) 1 false) h
    else
      let h := HTerm.int pow h
      let v : Int := (if x < 0 then -1 else 1) * (x.natAbs / 2 ^ (8 * (pow / 8)) : Nat)
      HTerm.int v h

/-! ## digits (`base/gmp.jl:784-810`, `base/intfuncs.jl:1249-1281`) -/


/-- `digits(T, n::BigInt; base)` for `2 ≤ base ≤ 62`, `base/gmp.jl:784-799`: the digit values of
`string(n; base)` (magnitudes) are stored, then `map!(-, a, a)` negates them for negative `n`,
wrapping in `T`. -/
def digitsBig (t : IntTy) (n : Int) (b : Nat) : Jl (List (JInt t)) :=
  .ok ((absDigits n.natAbs b).map fun (d : Nat) =>
    let v := JInt.lit t (d : Int)
    if n < 0 then -v else v)

/-- An output vector for `digits!`: its length, and whether it is resizable (a `Vector`) or
not (a view or other fixed-size `StridedVector`, which has no `resize!` method). -/
structure Vec where
  len : Nat
  resizable : Bool
  deriving DecidableEq, Repr

/-- The `len` least significant base-`2^k` digits of `n ≥ 0`, as the docstring promises. -/
def lowDigits (len : Nat) (n : Int) (k : Nat) : List Int :=
  (List.range len).map fun i => (n.toNat / 2 ^ (k * i) % 2 ^ k : Nat)

/-- `digits!(a::Vector{Int64}, n::BigInt; base = 2^k)` for `base > 62`, `base/gmp.jl:800-806`
with `MPZ.export!` (`base/gmp.jl:274-284`): when `a` is shorter than the digit count, export!
calls `resize!(a, ndigits)`, a `MethodError` for non-resizable vectors; the exported words are
then truncated back to the original length. Restricted to `n ≥ 0`. -/
def digitsBangBig (a : Vec) (n : Int) (k : Nat) : Jl (List Int) :=
  let nd := ((n.natAbs.log2 + 1) + k - 1) / k
  if a.len < nd ∧ !a.resizable then .error (.methodError "resize!")
  else .ok (lowDigits a.len n k)

/-- A `Rational{BigInt}` as Julia stores it: `den ≥ 0`, coprime components, and `±1//0` for the
infinities. -/
structure QBig where
  num : Int
  den : Nat
  deriving DecidableEq, Repr

/-- `count_leading_zeros` of a nonzero 64-bit limb. -/
def clz (w : Nat) : Nat := 64 - (w.log2 + 1)

/-- The most significant limb of `abs(x)` (`PTR(x)[size - 1]`), for `x ≠ 0`. -/
def topLimb (x : Int) : Nat := limb x (nlimbs x - 1)

/-- `mpq_cmp(op1, op2)` as implemented in GMP 6.3 `mpq/cmp.c` (`mpq_cmp_numden`). -/
def mpqCmp (a b : QBig) : Option Int :=
  let n1 := size a.num
  let n2 := size b.num
  let d1 := nlimbs a.den
  let d2 := nlimbs b.den
  if n1 = 0 then some (-n2)
  else if n2 = 0 then some n1
  else if decide (n1 < 0) != decide (n2 < 0) then some n1
  else if d1 = 0 ∨ d2 = 0 then none
  else
    let sign1 := n1
    let a1 := n1.natAbs
    let d1h := topLimb a.den
    let d2h := topLimb b.den
    let op2Int := d2 = 1 ∧ d2h = 1
    let op1Int := d1 = 1 ∧ d1h = 1
    if op2Int ∧ op1Int then
      if sign1 ≠ n2 then some (if sign1 > n2 then 1 else -1)
      else
        let c : Int := if a.num.natAbs < b.num.natAbs then -1
          else if a.num.natAbs = b.num.natAbs then 0 else 1
        some (if sign1 > 0 then c else -c)
    else
      let a2 := n2.natAbs
      let oi : Nat := if op2Int then 1 else 0
      let t1 := a1 + d2
      let t2 := a2 + d1
      if t1 > t2 + 1 then some sign1
      else if t2 + oi > t1 + 1 then some (-sign1)
      else
        let bits1 := t1 * 64 - clz (topLimb a.num) - clz d2h
        let bits2 := t2 * 64 - clz (topLimb b.num) - clz d1h
        if bits1 > bits2 + 1 then some sign1
        else if bits2 + oi > bits1 + 1 then some (-sign1)
        else
          -- step 3: exact cross products; `cc` is their limb-count difference or `mpn_cmp`
          let p1 := a.num.natAbs * b.den
          let p2 := b.num.natAbs * a.den
          let s1 : Int := nlimbs p1
          let s2 : Int := nlimbs p2
          let cc : Int := if s1 ≠ s2 then s1 - s2
            else if p1 < p2 then -1 else if p1 = p2 then 0 else 1
          some (if sign1 < 0 then -cc else cc)

/-- `cmp(x::Rational{BigInt}, y::Rational{BigInt})`, `base/gmp.jl:1116-1124`. -/
def cmpQ (a b : QBig) : Option Int :=
  if a.den = 0 then
    if b.den = 0 then
      some (if b.num < 0 then (if a.num < 0 then 0 else 1)
            else if a.num < 0 then -1 else 0)
    else some (if a.num < 0 then -1 else 1)
  else if b.den = 0 then some (if b.num < 0 then 1 else -1)
  else (mpqCmp a b).map Int.sign
/-- The value of a digit character in `base`, or `99` for a non-digit: GMP's `digit_value`
table (`mpz/set_str.c`), which agrees with Julia's `Parsers.digitvalue`: case-insensitive
letters for bases up to 36; above, upper-case letters are 10..35 and lower-case 36..61. -/
def digitVal (c : Char) (base : Nat) : Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then n - 48
  else if 65 ≤ n ∧ n ≤ 90 then n - 55
  else if 97 ≤ n ∧ n ≤ 122 then (if base ≤ 36 then n - 87 else n - 61)
  else 99
/-- `mpz_set_str(rop, str, base)` for `2 ≤ base ≤ 62`, as implemented in GMP 6.3
`mpz/set_str.c`: leading whitespace, an optional `-`, a first character that must be a digit,
and then digits with whitespace anywhere ignored (GMP manual §5.2: "White space is allowed in
the string, and is simply ignored"). -/
def mpzSetStr (s : List Char) (base : Nat) : Option Int :=
  let s := s.dropWhile isSpace
  let (neg, s) := match s with
    | '-' :: t => (true, t)
    | _ => (false, s)
  match s with
  | [] => none
  | c :: _ =>
    if digitVal c base ≥ base then none
    else
      let ds := s.filter (fun c => !isSpace c)
      if ds.any (fun c => digitVal c base ≥ base) then none
      else
        let v : Int := ds.foldl (fun acc c => acc * base + digitVal c base) 0
        some (if neg then -v else v)
/-- `tryparse_internal(::Type{BigInt}, s, ..., base, raise = true)` (`parse(BigInt, s; base)`),
`base/gmp.jl:307-331`. -/
def parseBig (s : List Char) (base : Nat) : Jl Int :=
  let (sgn, b, rest) := preamble base s
  if ¬ (2 ≤ b ∧ b ≤ 62) then .error (.argumentError "invalid base")
  else match rest with
    | none => .error (.argumentError "premature end of integer")
    | some r =>
      if s.contains (Char.ofNat 0) then .error (.argumentError "invalid BigInt")
      else match mpzSetStr r b with
        | none => .error (.argumentError "invalid BigInt")
        | some v => .ok (if sgn < 0 then -v else v)
/-- `string(n::BigInt; base, pad)`, `base/gmp.jl:765-782`. -/
def stringBig (n : Int) (base pad : Int) : Jl (List Char) :=
  if base < 0 then baseNeg base n pad
  else if ¬ (2 ≤ base ∧ base ≤ 62) then .error (.argumentError "base must be 2 ≤ base ≤ 62")
  else .ok (renderPos n base.toNat pad)
end JuliaLean.BigNums

namespace JuliaLean.Combinatorics

open JuliaLean

def cULongMax : Int := 2^64 - 1

/-- `factorial(::BigInt)`, `base/gmp.jl:717`: GMP's `fac_ui` on nonnegative
inputs, with the source `DomainError` on negative inputs. -/
def factorialBig (n : Int) : Jl Int :=
  if n < 0 then .error (.domainError "n must not be negative")
  else if cULongMax < n then .error (.inexactError "UInt64")
  else .ok (factorialNat n.toNat)

private def chooseNat : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chooseNat n k + chooseNat n (k + 1)

def binomialExact (n k : Int) : Int :=
  if k < 0 then 0
  else if 0 ≤ n then
    if k ≤ n then chooseNat n.toNat k.toNat else 0
  else
    let magnitude : Int := chooseNat (k - n - 1).toNat k.toNat
    if k % 2 = 0 then magnitude else -magnitude

def binomialBigFinish (n k : Int) : Jl Int :=
  let κ := n - k
  if κ < 0 then .ok 0
  else if κ ≤ cULongMax then .ok (binomialExact n k)
  else .error (.overflowError "Computation would exceed memory")

/-- `binomial(::BigInt, ::Integer)`, `base/gmp.jl:719-728`, including the
`Culong` exponent limit and its explicit resource `OverflowError`. -/
def binomialBig (n k : Int) : Jl Int :=
  if k < 0 then .ok 0
  else if k ≤ cULongMax then .ok (binomialExact n k)
  else if n < 0 then
    match binomialBigFinish (k - n - 1) k with
    | .ok r => .ok (if k % 2 = 0 then r else -r)
    | .error e => .error e
  else binomialBigFinish n k

end JuliaLean.Combinatorics
