import JuliaLean.MathFuncs.PropsUniversal

/-!
Boolean per-offset checks and chunk lemmas shared by the kernel-evaluation proofs of
`log2Pow2Exact` and `exp2IntegerExact`. The cases are split over several modules so
that lake checks them in parallel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `log2Pow2Exact` at the offset `n`, as a Boolean check. -/
def log2Pow2Check (n : Nat) : Bool :=
  decide (log2 (F64.ldexp F64.one ((n : Int) - 1074)) = .ok (F64.ofInt ((n : Int) - 1074)))

/-- `exp2IntegerExact` at the offset `n`, as a Boolean check. -/
def exp2IntegerCheck (n : Nat) : Bool :=
  decide (exp2 (F64.ofInt ((n : Int) - 1074)) = F64.ldexp F64.one ((n : Int) - 1074))

/-- Every offset in `[off, off + len)` passes `c`. -/
def chunkOk (c : Nat → Bool) (off len : Nat) : Bool :=
  (List.range len).all fun i => c (i + off)

theorem chunkOk_spec {c : Nat → Bool} {off len : Nat} (h : chunkOk c off len = true)
    {n : Nat} (h1 : off ≤ n) (h2 : n < off + len) : c n = true := by
  unfold chunkOk at h
  rw [List.all_eq_true] at h
  have := h (n - off) (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h1] at this

end JuliaLean.MathFuncs
