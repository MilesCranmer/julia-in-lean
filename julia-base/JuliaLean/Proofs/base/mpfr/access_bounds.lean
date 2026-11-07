import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## MPFR storage -/

inductive BigFloatAbi where
  | lp64
  | win64
  deriving DecidableEq, Repr

def BigFloatAbi.limbBytes : BigFloatAbi → Nat
  | .lp64 => 8
  | .win64 => 4

def BigFloatAbi.headerLimbs : BigFloatAbi → Nat
  | .lp64 => 4
  | .win64 => 6

def BigFloatAbi.fieldSpans : BigFloatAbi → List (Nat × Nat)
  | .lp64 => [(0, 8), (8, 4), (16, 8), (24, 8)]
  | .win64 => [(0, 4), (4, 4), (8, 4), (16, 8)]

/-- `mpfr_custom_get_size(precision)` is a whole number of MPFR limbs. -/
def mpfrPayloadLimbs (abi : BigFloatAbi) (precision : Nat) : Nat :=
  (precision + 8 * abi.limbBytes - 1) / (8 * abi.limbBytes)

/-- Algebraic normal form of lines 156-158: `nb` payload bytes plus the aligned header,
rounded up to `sizeof(Limb)`. -/
def bigFloatAllocatedLimbs (abi : BigFloatAbi) (precision : Nat) : Nat :=
  abi.headerLimbs + mpfrPayloadLimbs abi precision

def fieldSpanInBounds (bytes : Nat) (field : Nat × Nat) : Prop :=
  field.1 + field.2 ≤ bytes

/-- `BigFloat(; precision)` throws before allocation when `precision < 1`; otherwise it writes
all four ABI fields at lines 165-168. -/
def bigFloatHeaderAccesses (abi : BigFloatAbi) (precision : Nat) : List (Nat × Nat) :=
  if precision < 1 then [] else abi.fieldSpans

/-- The payload writes of `BigFloat(::Float64)` at lines 330-370. The fast ccall branch and
zero/nonfinite branch perform no payload writes; otherwise both ABI branches fill payload
indices `1:nlimbs` (with different loop grouping on Win64). -/
def bigFloatFloat64PayloadAccesses
    (abi : BigFloatAbi) (precision : Nat) (finiteNonzero : Bool) : List Int :=
  if precision ≤ 53 ∨ !finiteNonzero then [] else span 1 (mpfrPayloadLimbs abi precision)

def BigFloatStorageAccessesInBounds : Prop :=
  (∀ abi precision field, field ∈ bigFloatHeaderAccesses abi precision →
      fieldSpanInBounds (abi.limbBytes * bigFloatAllocatedLimbs abi precision) field) ∧
  (∀ abi precision finiteNonzero i,
    i ∈ bigFloatFloat64PayloadAccesses abi precision finiteNonzero →
      inBounds (mpfrPayloadLimbs abi precision) i)

theorem bigFloatStorageAccessesInBounds_proven : BigFloatStorageAccessesInBounds := by
  constructor
  · intro abi precision field hf
    unfold bigFloatHeaderAccesses at hf
    split at hf
    · simp_all
    · rename_i hp
      cases abi <;> simp [BigFloatAbi.fieldSpans] at hf <;>
        rcases hf with rfl | rfl | rfl | rfl <;>
        simp [fieldSpanInBounds, BigFloatAbi.limbBytes, bigFloatAllocatedLimbs,
          BigFloatAbi.headerLimbs, mpfrPayloadLimbs] <;> omega
  · intro abi precision finiteNonzero i hi
    unfold bigFloatFloat64PayloadAccesses at hi
    split at hi
    · simp_all
    · obtain ⟨k, hk, rfl⟩ := mem_span hi
      simp [inBounds]
      omega

inductive MpfrPrintfResult where
  | failure
  | success (chars : Nat)
  deriving DecidableEq, Repr

/-- On success `mpfr_asprintf` returns the number of non-NUL bytes and owns `chars+1` bytes;
the loop at lines 1228-1231 scans `1:chars` and may store at the first comma. -/
def stringMpfrAccesses : MpfrPrintfResult → Nat × List Int
  | .failure => (0, [])
  | .success chars => (chars + 1, span 1 chars)

def StringMpfrAccessesInBounds : Prop :=
  ∀ result i, i ∈ (stringMpfrAccesses result).2 →
    inBounds (stringMpfrAccesses result).1 i

theorem stringMpfrAccessesInBounds_proven : StringMpfrAccessesInBounds := by
  intro result i hi
  cases result with
  | failure => simp [stringMpfrAccesses] at hi
  | success chars =>
      obtain ⟨k, hk, rfl⟩ := mem_span hi
      simp [stringMpfrAccesses, inBounds]
      omega
end JuliaLean.MemSafety.G6
end
