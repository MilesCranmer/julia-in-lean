import JuliaLean.base.iterators
import JuliaLean.Proofs.base.generator.iterator_protocol

/-!
# `Iterators.countfrom` (base/iterators.jl:743-774)

Numbers are `Bool`, `Int64` and `Char` (a non-`Number` with `+(::Char, ::Integer)`).
`Bool + Bool` is an `Int` (base/bool.jl: `+(x::Bool, y::Bool) = Int(x) + Int(y)`),
`Bool + Int` promotes to `Int`, `Int + Int` wraps, and `Char + Int` is the
`Char` with the shifted code point (base/char.jl), which throws for a negative
or too large code point.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Every element `countfrom(start, step)`, `countfrom(start)` and
`countfrom()` yield is an `eltype` of the iterator (`eltype(::Count{T}) = T`). -/
def CountfromEltype : Prop :=
  ∀ (start step : Num) (k : Nat),
    (∀ c xs, countfrom2 start step = .ok c → countPrefix c k = .ok xs → ∀ x ∈ xs, x.ty = c.eltype) ∧
    (∀ c xs, countfrom1 start = .ok c → countPrefix c k = .ok xs → ∀ x ∈ xs, x.ty = c.eltype) ∧
    (∀ xs, countPrefix countfrom0 k = .ok xs → ∀ x ∈ xs, x.ty = countfrom0.eltype)

/-- `countfrom(true)` is a `Count{Bool,Bool}`, but its second element is
`true + true == 2`. -/
theorem countfromEltype_refuted : ¬ CountfromEltype := by
  intro h
  have := (h (.bool true) (.bool true) 2).2.1 ⟨.bool, .bool true, .bool true⟩
    [.bool true, .int (i64 2)] rfl rfl (.int (i64 2)) (by simp)
  exact absurd this (by decide)

/-- `s, s + d, s + d + d, ...` with `Int` wraparound: the first `k` terms. -/
def addChain (d : JInt64) : Nat → JInt64 → List Num
  | 0, _ => []
  | k + 1, s => .int s :: addChain d k (s + d)

/-- `countfrom(start, step)` and `countfrom(start)` of `Int`s, and `countfrom()`,
count forever (`IteratorSize` `IsInfinite`, base/iterators.jl:774): every
prefix exists and consists of `start`, `start + step`, `start + 2step`, ...
with `Int` wraparound, `Int`s as `eltype` says (base/iterators.jl:751). -/
def CountfromInts : Prop :=
  ∀ (s d : JInt64) (k : Nat),
    (∃ c, countfrom2 (.int s) (.int d) = .ok c ∧ countPrefix c k = .ok (addChain d k s) ∧
      c.eltype = .int) ∧
    (∃ c, countfrom1 (.int s) = .ok c ∧ countPrefix c k = .ok (addChain (i64 1) k s) ∧
      c.eltype = .int) ∧
    countPrefix countfrom0 k = .ok (addChain (i64 1) k (i64 1))

theorem countRun_int (T : NTy) (s0 d : JInt64) : ∀ (k : Nat) (s : JInt64),
    countRun ⟨T, .int s0, .int d⟩ k (.int s) = .ok (addChain d k s) := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [countRun, numAdd, bind, Except.bind, pure, Except.pure, ih] <;> rfl

theorem countfromInts : CountfromInts := by
  intro s d k
  refine ⟨⟨⟨.int, .int s, .int d⟩, rfl, countRun_int _ _ _ _ _, rfl⟩,
    ⟨⟨.int, .int s, .int (i64 1)⟩, rfl, countRun_int _ _ _ _ _, rfl⟩, countRun_int _ _ _ _ _⟩

end JuliaLean.IteratorsCov
