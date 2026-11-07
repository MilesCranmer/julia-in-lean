import JuliaLean.Core
import JuliaLean.base.combinatorics
import JuliaLean.base.intfuncs
import JuliaLean.base.gmp

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


/-- The documented classification, without the premature conversion to `Int`. -/
def factorialSpec (t : IntTy) (n : JInt t) : Jl FixedInteger :=
  if n.val < 0 then
    .error (.domainError "n must not be negative")
  else if n.val > factorialLimit t then
    .error (.overflowError "too large for factorial table")
  else
    .ok ⟨factorialResultType t, factorialNat n.val.toNat⟩


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
