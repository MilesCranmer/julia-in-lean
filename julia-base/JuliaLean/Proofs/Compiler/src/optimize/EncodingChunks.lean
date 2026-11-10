import JuliaLean.Compiler.src.optimize

/-!
The exhaustive kernel check behind `Encoding.lean`: the encoding facts at every `UInt16`, in
sixteen chunks of 4096 costs (one chunk per declaration keeps the kernel's memory use low). This
module is separate so that it is rebuilt only when the encoding model changes.
-/

namespace JuliaLean.Proofs.Compiler.src.optimize

open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize

/-- `P n` holds for every `n` in `lo ..< lo + 2^d`. A tree keeps the kernel's recursion depth at
`d`. -/
def allTree (P : Nat → Bool) : Nat → Nat → Bool
  | 0, lo => P lo
  | d + 1, lo => allTree P d lo && allTree P d (lo + 2 ^ d)

theorem allTree_spec (P : Nat → Bool) :
    ∀ d lo, allTree P d lo = true → ∀ n, lo ≤ n → n < lo + 2 ^ d → P n = true := by
  intro d
  induction d with
  | zero =>
    intro lo h n h1 h2
    have : n = lo := by simp at h2; omega
    subst this; simpa [allTree] using h
  | succ d ih =>
    intro lo h n h1 h2
    simp only [allTree, Bool.and_eq_true] at h
    by_cases hn : n < lo + 2 ^ d
    · exact ih lo h.1 n h1 hn
    · exact ih (lo + 2 ^ d) h.2 n (by omega) (by rw [Nat.pow_succ] at h2; omega)

/-- `enc` and `dec` on `Nat`. -/
def encN (n : Nat) : Nat := (jlEncodeInliningCost (UInt16.ofNat n)).toNat
def decN (n : Nat) : Nat := (jlDecodeInliningCost (UInt8.ofNat n)).toNat

/-- The facts checked at each cost `n`: rounding up within 1/32 below 3969, the never-inline
marker above, exactness below 64, and `enc n ≤ enc (n + 1)`. -/
def encFacts (n : Nat) : Bool :=
  let d := (jlDecodeInliningCost (jlEncodeInliningCost (UInt16.ofNat n))).toNat
  (n ≤ 3968 → n ≤ d) && (n ≤ 3968 → d * 32 ≤ n * 33) && (3968 < n → d = 65535) &&
  (n < 64 → d = n) && (n = 65535 || encN n ≤ encN (n + 1))

theorem encFacts_c0 : allTree encFacts 12 0 = true := by decide +kernel
theorem encFacts_c1 : allTree encFacts 12 4096 = true := by decide +kernel
theorem encFacts_c2 : allTree encFacts 12 8192 = true := by decide +kernel
theorem encFacts_c3 : allTree encFacts 12 12288 = true := by decide +kernel
theorem encFacts_c4 : allTree encFacts 12 16384 = true := by decide +kernel
theorem encFacts_c5 : allTree encFacts 12 20480 = true := by decide +kernel
theorem encFacts_c6 : allTree encFacts 12 24576 = true := by decide +kernel
theorem encFacts_c7 : allTree encFacts 12 28672 = true := by decide +kernel
theorem encFacts_c8 : allTree encFacts 12 32768 = true := by decide +kernel
theorem encFacts_c9 : allTree encFacts 12 36864 = true := by decide +kernel
theorem encFacts_c10 : allTree encFacts 12 40960 = true := by decide +kernel
theorem encFacts_c11 : allTree encFacts 12 45056 = true := by decide +kernel
theorem encFacts_c12 : allTree encFacts 12 49152 = true := by decide +kernel
theorem encFacts_c13 : allTree encFacts 12 53248 = true := by decide +kernel
theorem encFacts_c14 : allTree encFacts 12 57344 = true := by decide +kernel
theorem encFacts_c15 : allTree encFacts 12 61440 = true := by decide +kernel

end JuliaLean.Proofs.Compiler.src.optimize
