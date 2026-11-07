import JuliaLean.stdlib.Random.src.generation
import JuliaLean.stdlib.Random.src.misc

namespace JuliaLean.RandomSampling

open JuliaLean JuliaLean.Float

/-- State after answering `i` identical requests `q` starting from `st`. -/
def Rng.stateAfter {σ : Type} (g : Rng σ) (q : Req) (st : σ) : Nat → σ
  | 0 => st
  | i + 1 => (g.next (g.stateAfter q st i) q).2

/-- The `i`-th answer (from zero) to repeated requests `q` starting from `st`. -/
def Rng.wordAt {σ : Type} (g : Rng σ) (q : Req) (st : σ) (i : Nat) : q.Out :=
  (g.next (g.stateAfter q st i) q).1

/-- Number of `x < n` with `p x`. -/
def countBelow (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countBelow p n + (if p n then 1 else 0)

/-- Rejection-sampling view of `ndlRand`: the value one word `x` yields, or `none` when
the word is rejected. Not Julia code; `NdlUniform` proves `ndlRand` returns the value
of the first word this accepts. -/
def ndlStep {t : IntTy} (sp : NDL t) (x : JInt (uintSup t)) : Option (JInt t) :=
  let N := 2 ^ (uintSup t).bits
  let s := sp.s.val.toNat
  let m := x.val.toNat * s
  if s = 0 then some (JInt.rem t x + sp.a)
  else if m % N < (N - s) % s then none
  else some (JInt.wrap t ((m / N : Nat) : Int) + sp.a)

/-- Rejection-sampling view of `fastRand` for one word of type `fastWord sp.bw`. -/
def fastStep {t : IntTy} (sp : Fast t) (w : JInt (fastWord sp.bw)) : Option (JInt t) :=
  let x := w.val.toNat % 2 ^ sp.bw
  if x ≤ sp.m.val.toNat then some (JInt.wrap t x + sp.a) else none

/-- `a` restricted to `1..n` is a permutation of `1..n`. -/
def IsPerm (n : Nat) (a : Nat → Int) : Prop :=
  (∀ k, 1 ≤ k → k ≤ n → 1 ≤ a k ∧ a k ≤ n) ∧
  (∀ k l, 1 ≤ k → k ≤ n → 1 ≤ l → l ≤ n → a k = a l → k = l)

/-- `m` applications of the permutation `k ↦ a[k]` to `x`. -/
def iterPerm (a : Nat → Int) : Nat → Nat → Nat
  | 0, x => x
  | m + 1, x => (a (iterPerm a m x)).toNat

end JuliaLean.RandomSampling
