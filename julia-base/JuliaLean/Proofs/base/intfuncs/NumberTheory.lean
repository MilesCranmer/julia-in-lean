import JuliaLean.base.intfuncs
import JuliaLean.base.gmp
import JuliaLean.Registry.Types

namespace JuliaLean.IntArith.NumberTheory








/-- Truncating remainder magnitude lemma used to justify the loop's
unwrapped remainder state, `base/intfuncs.jl:249-250`. -/
theorem remainder_magnitude (a b : Int) (hb : b ≠ 0) :
    (a.tmod b).natAbs < b.natAbs := by
  rw [Int.natAbs_tmod]
  exact Nat.mod_lt _ (by omega)










private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- A signed typemin gcd with itself is unrepresentable and must throw. -/
def GcdTypeminOverflow : Prop := ∀ t : IntTy, t.signed = true →
  gcd (JInt.typemin t) (JInt.typemin t) = .error (.overflowError "")

theorem gcdTypeminOverflow : GcdTypeminOverflow := by
  intro t
  cases t <;> decide

/-- The documented lcm exists in the promoted type for these inputs,
regardless of argument order. -/
def MixedLcmRepresentable : Prop := ∀ (a : JInt .u16) (b : JInt .i8),
  Int.lcm a.val b.val ≤ IntTy.max .u16 →
  (mixedLcm a b).map Subtype.val = .ok (Int.lcm a.val b.val)

theorem mixedLcmRepresentable_refuted : ¬ MixedLcmRepresentable := by
  intro h
  have hbad := h (JInt.lit .u16 1) (JInt.lit .i8 (-128)) (by decide)
  have hneq : (mixedLcm (JInt.lit .u16 1) (JInt.lit .i8 (-128))).map Subtype.val ≠
      .ok (Int.lcm (JInt.lit .u16 1).val (JInt.lit .i8 (-128)).val) := by decide
  exact hneq hbad

/-- Exact signed Bézout identity and the strict coefficient inequalities
printed in the gcdx docstring. Both inputs are explicitly nonzero. -/
def GcdxStrictBounds : Prop := ∀ (a b d u v : JInt .i8),
  a.val ≠ 0 → b.val ≠ 0 → gcdx a b = .ok (d, u, v) →
  u.val * a.val + v.val * b.val = d.val ∧
  u.val.natAbs < (b.val.tdiv d.val).natAbs ∧
  v.val.natAbs < (a.val.tdiv d.val).natAbs

theorem gcdxStrictBounds_refuted : ¬ GcdxStrictBounds := by
  intro h
  have hb := h (JInt.lit .i8 2) (JInt.lit .i8 2) (JInt.lit .i8 2)
    (JInt.lit .i8 0) (JInt.lit .i8 1) (by decide) (by decide) (by decide +kernel)
  exact (by decide : ¬ ((JInt.lit .i8 1).val.natAbs <
    ((JInt.lit .i8 2).val.tdiv (JInt.lit .i8 2).val).natAbs)) hb.2.2

/-- Byte edge grid includes zero, signed typemin, and unsigned typemax. -/
def byteEdge (n : Fin 16) : Int :=
  if n.val = 0 then 0 else if n.val = 1 then 128 else n.val * 17

/-- General inverse correctness postcondition, `base/intfuncs.jl:309`. -/
def inversePost {t : IntTy} (a m : Int) (result : Jl (JInt t)) : Prop :=
  match result with
  | .error _ => m = 0 ∨ Nat.gcd a.natAbs m.natAbs ≠ 1
  | .ok y => m ≠ 0 ∧ (y.val * a - 1).tmod m = 0 ∧ y.val.tdiv m = 0

private instance {t : IntTy} (a m : Int) (result : Jl (JInt t)) :
    Decidable (inversePost a m result) := by
  cases result <;> unfold inversePost <;> infer_instance

/-- invmod's documented congruence and truncating-division range on a
signed/unsigned byte edge grid. Errors are permitted exactly when the
modulus is zero or the inputs are not relatively prime. -/
def InvmodByteRange : Prop := ∀ (sn sm : Bool) (n m : Fin 16),
  let a := JInt.lit (if sn then .i8 else .u8) (byteEdge n)
  let b := JInt.lit (if sm then .i8 else .u8) (byteEdge m)
  inversePost a.val b.val (invmod gmpGcdx a b)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem invmodByteRange : InvmodByteRange := by unfold InvmodByteRange; decide +kernel

/-- Exhaustive ring inverse contract for all 256 UInt8 bit patterns:
even inputs throw and odd inputs multiply to one in the machine ring. -/
def RingInverseUInt8 : Prop := ∀ n : Fin 256,
  let a := JInt.lit .u8 n.val
  if a.val % 2 = 0 then invmodRing a = .error (.domainError "")
  else (invmodRing a).map (fun x => (a * x).val) = .ok 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem ringInverseUInt8 : RingInverseUInt8 := by unfold RingInverseUInt8; decide +kernel

/-- Exhaustive signed Int8 bit patterns, including negative odd inputs. -/
def RingInverseInt8 : Prop := ∀ n : Fin 256,
  let a := JInt.lit .i8 n.val
  if a.val % 2 = 0 then invmodRing a = .error (.domainError "")
  else (invmodRing a).map (fun x => (a * x).val) = .ok 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem ringInverseInt8 : RingInverseInt8 := by unfold RingInverseInt8; decide +kernel

/-- All odd Int8 residues have x^(-128) congruent to one modulo -128;
the returned representative has the modulus's negative sign. -/
def PowermodTypeminNegative : Prop := ∀ n : Fin 128,
  let a := JInt.lit .i8 n.val
  a.val % 2 ≠ 0 →
  (powermod gmpGcdx gmpPowermod a (JInt.lit .i8 (-128)) (JInt.lit .i8 (-128))).map Subtype.val = .ok (-127)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem powermodTypeminNegative : PowermodTypeminNegative := by unfold PowermodTypeminNegative; decide +kernel

/-- Small nonnegative exponents against exact integer exponentiation.
Negative moduli exercise the final sign correction and the optimized
magic-number branch whenever p > 2*sizeof(Int8). -/
def PowermodNegativeModulus : Prop := ∀ (x : Fin 8) (p : Fin 8) (m : Fin 8),
  m.val ≠ 0 →
  (powermod gmpGcdx gmpPowermod (JInt.lit .i8 x.val) (JInt.lit .i8 p.val)
    (JInt.lit .i8 (-(m.val : Int)))).map Subtype.val =
    .ok (if ((x.val : Int) ^ p.val) % (m.val : Int) = 0 then 0
      else ((x.val : Int) ^ p.val) % (m.val : Int) - m.val)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem powermodNegativeModulus : PowermodNegativeModulus := by unfold PowermodNegativeModulus; decide +kernel

/-- UInt128 inputs close to typemax exercise the BigInt gcdext widening
and conversion back to UInt128 in the general inverse implementation. -/
def InvmodUInt128Range : Prop := ∀ n : Fin 8,
  let a := JInt.lit .u128 (IntTy.max .u128 - 2 * n.val)
  let m := JInt.typemax .u128
  inversePost a.val m.val (invmod gmpGcdx a m)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem invmodUInt128Range : InvmodUInt128Range := by unfold InvmodUInt128Range; decide +kernel

/-- The Int128 overload must send the original negative exponent and
modulus to GMP. Odd residues raised to -2^127 are one modulo 2^127. -/
def PowermodInt128Typemin : Prop := ∀ n : Fin 8,
  (powermod gmpGcdx gmpPowermod (JInt.lit .i128 (2 * n.val + 1)) (JInt.typemin .i128)
    (JInt.typemin .i128)).map Subtype.val = .ok (IntTy.min .i128 + 1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem powermodInt128Typemin : PowermodInt128Typemin := by unfold PowermodInt128Typemin; decide +kernel

def entries : List JuliaLean.Registry.Entry := []

end JuliaLean.IntArith.NumberTheory
