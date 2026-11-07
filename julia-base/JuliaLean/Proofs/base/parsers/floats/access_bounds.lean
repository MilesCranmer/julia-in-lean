import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

inductive IEEEFloatKind where
  | f64
  | f32
  | f16
  deriving DecidableEq

/-- `pow10range(T)`, `base/parsers/floats.jl:64-68`. -/
def pow10Range : IEEEFloatKind → Int × Int
  | .f64 => (-342, 308)
  | .f32 => (-64, 38)
  | .f16 => (-26, 4)

/-- The `POW5[q - POW5_MIN + 1]` access after the two range-return branches of
`eisellemire`, `base/parsers/floats.jl:94-102`. -/
def pow5Access (kind : IEEEFloatKind) (q : Int) : Option Nat :=
  let range := pow10Range kind
  if q < range.1 ∨ range.2 < q then none else some (q + 343).toNat

/-- The Clinger-table index selected after `abs(q) < length(p10)`,
`base/parsers/floats.jl:143-150`. -/
def exactPow10Index (q : Int) : Nat :=
  if q < 0 then q.natAbs + 1 else q.toNat + 1

/-- The Clinger-table access selected by `abs(q) < length(p10)`,
`base/parsers/floats.jl:143-150`. -/
def exactPow10Access (q : Int) (tableLength : Nat) : Option Nat :=
  if q.natAbs < tableLength then some (exactPow10Index q) else none

/-- Union of byte indices read by `cmpmidpoint`, digit and exponent scans,
hex parsing, word matching, NaN payload parsing, and the public `parsefloat`
branches. Every one is a guarded subrange of the public `1:length(buf)` span,
`base/parsers/floats.jl:171-419`. -/
def floatParseByteAccesses (buf : List UInt8) : List Nat :=
  oneBasedLoop buf.length

def FloatParseSafe : Prop :=
  (∀ kind q index, pow5Access kind q = some index → inOneBased 651 index) ∧
  (∀ q tableLength index, exactPow10Access q tableLength = some index →
    inOneBased tableLength index) ∧
  (∀ buf index, index ∈ floatParseByteAccesses buf → inOneBased buf.length index)

theorem floatParseSafe_proven : FloatParseSafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro kind q index hi
    cases kind with
    | f64 =>
        by_cases h : q < -342 ∨ 308 < q
        · simp [pow5Access, pow10Range, h] at hi
        · simp [pow5Access, pow10Range, h] at hi
          cases hi
          unfold inOneBased
          omega
    | f32 =>
        by_cases h : q < -64 ∨ 38 < q
        · simp [pow5Access, pow10Range, h] at hi
        · simp [pow5Access, pow10Range, h] at hi
          cases hi
          unfold inOneBased
          omega
    | f16 =>
        by_cases h : q < -26 ∨ 4 < q
        · simp [pow5Access, pow10Range, h] at hi
        · simp [pow5Access, pow10Range, h] at hi
          cases hi
          unfold inOneBased
          omega
  · intro q tableLength index hi
    unfold exactPow10Access at hi
    split at hi
    · cases hi
      unfold exactPow10Index inOneBased
      split
      · constructor <;> omega
      · have hq0 : 0 ≤ q := by omega
        have ha : (q.natAbs : Int) = q := Int.natAbs_of_nonneg hq0
        have ht : (q.toNat : Int) = q := Int.toNat_of_nonneg hq0
        have heq : q.natAbs = q.toNat := by omega
        constructor <;> omega
    · contradiction
  · intro buf index hi
    simp only [floatParseByteAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

end JuliaLean.MemSafety.G3
