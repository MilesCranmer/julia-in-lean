import JuliaLean.Core

set_option maxRecDepth 100000

/-!
Fixed-width and arbitrary-precision integer combinatorics. The fixed-width models
mirror `base/combinatorics.jl:21-40` and `base/intfuncs.jl:1373-1402` on a
64-bit Julia build. `Int` values model `BigInt` results where GMP computes the
mathematical integer exactly.
-/

namespace JuliaLean.Combinatorics

open JuliaLean

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

structure FixedInteger where
  ty : IntTy
  val : Int
  deriving Repr, DecidableEq

def factorialNat : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialNat n

def factorialResultType : IntTy → IntTy
  | .i8 | .u8 | .i16 | .u16 | .i32 | .u32 => .i64
  | t => t

def factorialLimit : IntTy → Int
  | .i128 => 33
  | .u128 => 34
  | _ => 20

/-- `factorial_lookup`, `base/combinatorics.jl:21-30`, including its eager
conversion to machine `Int` before the sign and table-limit checks. -/
def factorialFixed (t : IntTy) (n : JInt t) : Jl FixedInteger := do
  let idx ← JInt.convert .i64 n.val
  if idx.val < 0 then
    .error (.domainError "n must not be negative")
  else if idx.val > factorialLimit t then
    .error (.overflowError "too large for factorial table")
  else
    .ok ⟨factorialResultType t, factorialNat idx.val.toNat⟩

/-- The documented classification, without the premature conversion to `Int`. -/
def factorialSpec (t : IntTy) (n : JInt t) : Jl FixedInteger :=
  if n.val < 0 then
    .error (.domainError "n must not be negative")
  else if n.val > factorialLimit t then
    .error (.overflowError "too large for factorial table")
  else
    .ok ⟨factorialResultType t, factorialNat n.val.toNat⟩

/-- Fixed-width factorial returns the exact table value, rejects negative inputs
with `DomainError`, and rejects every value beyond the representable table with
`OverflowError`. -/
def cULongMax : Int := 2^64 - 1

/-- `factorial(::BigInt)`, `base/gmp.jl:717`: GMP's `fac_ui` on nonnegative
inputs, with the source `DomainError` on negative inputs. -/
def factorialBig (n : Int) : Jl Int :=
  if n < 0 then .error (.domainError "n must not be negative")
  else if cULongMax < n then .error (.inexactError "UInt64")
  else .ok (factorialNat n.toNat)

def factorialBigSpec (n : Int) : Jl Int :=
  if n < 0 then .error (.domainError "n must not be negative")
  else if cULongMax < n then .error (.overflowError "factorial resource limit")
  else .ok (factorialNat n.toNat)

def FactorialContract : Prop :=
  (∀ (t : IntTy) (n : JInt t), factorialFixed t n = factorialSpec t n) ∧
  ∀ n : Int, factorialBig n = factorialBigSpec n

theorem factorialContract_refuted : ¬ FactorialContract := by
  intro h
  have bad := h.2 (cULongMax + 1)
  revert bad
  decide

def FactorialBigWithinCulong : Prop :=
  (∀ n : Int, 0 ≤ n → n ≤ cULongMax → factorialBig n = .ok (factorialNat n.toNat)) ∧
  ∀ n : Int, n < 0 → factorialBig n = .error (.domainError "n must not be negative")

theorem factorialBigWithinCulong_proven : FactorialBigWithinCulong := by
  constructor
  · intro n hn hmax
    have hnneg : ¬n < 0 := by omega
    have hlimit : ¬cULongMax < n := by omega
    simp [factorialBig, hnneg, hlimit]
  · intro n hn
    simp [factorialBig, hn]

private def checkedValue (t : IntTy) (x : Int) : Jl (JInt t) :=
  if h : t.min ≤ x ∧ x ≤ t.max then .ok ⟨x, h⟩
  else .error (.overflowError "binomial overflows")

private def binomialLoop (t : IntTy) : Nat → JInt t → JInt t → JInt t → Jl (JInt t)
  | 0, x, _, _ => .ok x
  | fuel + 1, x, nn, rr => do
      let xt := (x.val * nn.val) / rr.val
      let x' ← checkedValue t xt
      binomialLoop t fuel x' (nn + JInt.lit t 1) (rr + JInt.lit t 1)

/-- Same-type `binomial`, `base/intfuncs.jl:1375-1402`. The loop counter is
the post-symmetry `k-1`; `widemul` is exact in the mathematical `Int` used for
`xt`, followed by the source range check `x == xt`. -/
def binomialFixed (t : IntTy) (n0 k0 : JInt t) : Jl (JInt t) :=
  if k0.val < 0 then .ok (JInt.lit t 0)
  else
    let sgn := if n0.val < 0 ∧ k0.val % 2 ≠ 0 then JInt.lit t (-1) else JInt.lit t 1
    let n := if n0.val < 0 then -n0 + k0 - JInt.lit t 1 else n0
    if k0.val > n.val then .ok (JInt.lit t 0)
    else if k0.val = 0 ∨ k0.val = n.val then .ok sgn
    else if k0.val = 1 then .ok (sgn * n)
    else
      let k := if k0.val > n.val / 2 then n - k0 else k0
      let x := n - k + JInt.lit t 1
      let nn := x + JInt.lit t 1
      match binomialLoop t (k.val - 1).toNat x nn (JInt.lit t 2) with
      | .error e => .error e
      | .ok r => .ok (if sgn.val < 0 then -r else r)

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

def binomialSpec (t : IntTy) (n k : JInt t) : Jl (JInt t) :=
  checkedValue t (binomialExact n.val k.val)

/-- For every fixed-width integer type and all same-type arguments, `binomial`
returns the mathematical generalized coefficient when it fits and throws
`OverflowError` exactly when it does not. -/
def BinomialContract : Prop :=
  ∀ (t : IntTy) (n k : JInt t), binomialFixed t n k = binomialSpec t n k

theorem binomialContract_refuted : ¬ BinomialContract := by
  intro h
  have bad := h .i8 (JInt.typemin .i8) (JInt.lit .i8 1)
  revert bad
  decide

/-- The source's documented edge identities for nonnegative upper arguments. -/
def BinomialNonnegativeEdges : Prop := ∀ (t : IntTy) (n k : JInt t), 0 ≤ n.val →
  (k.val < 0 → binomialFixed t n k = .ok (JInt.lit t 0)) ∧
  (n.val < k.val → binomialFixed t n k = .ok (JInt.lit t 0)) ∧
  (k.val = 0 → binomialFixed t n k = .ok (JInt.lit t 1))

theorem binomialNonnegativeEdges_proven : BinomialNonnegativeEdges := by
  intro t n k hn
  constructor
  · intro hk
    simp [binomialFixed, hk]
  constructor
  · intro hk
    have hnneg : ¬n.val < 0 := by omega
    have hkneg : ¬k.val < 0 := by omega
    simp [binomialFixed, hnneg, hkneg, hk]
  · intro hk
    have hnneg : ¬n.val < 0 := by omega
    simp [binomialFixed, hnneg, hk]

private def binomialBigFinish (n k : Int) : Jl Int :=
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

def BinomialBigExact : Prop := ∀ n k : Int,
  (k < 0 → binomialBig n k = .ok 0) ∧
  (0 ≤ k → k ≤ cULongMax → binomialBig n k = .ok (binomialExact n k)) ∧
  (0 ≤ n → n < k → binomialBig n k = .ok 0)

theorem binomialBigExact_proven : BinomialBigExact := by
  intro n k
  constructor
  · intro hk
    simp [binomialBig, hk]
  constructor
  · intro hk hmax
    have hkneg : ¬k < 0 := by omega
    simp [binomialBig, hkneg, hmax]
  · intro hn hnk
    have hk : 0 ≤ k := by omega
    have hkn : ¬k ≤ n := by omega
    by_cases hmax : k ≤ cULongMax
    · have hkneg : ¬k < 0 := by omega
      simp [binomialBig, hkneg, hmax, binomialExact, hn, hkn]
    · have hnneg : ¬n < 0 := by omega
      have hkneg : ¬k < 0 := by omega
      have hkmax : ¬k ≤ cULongMax := hmax
      have hkappa : n - k < 0 := by omega
      simp [binomialBig, hkneg, hkmax, hnneg, binomialBigFinish, hkappa]

end JuliaLean.Combinatorics
