import JuliaLean.base.idset
import JuliaLean.Proofs.base.idset.OperationHistories

namespace JuliaLean.IdDicts
/-! ## `IdSet` -/

/-- Call sequences on an `IdSet{Any}` (with fewer than `2^62` mentioned
elements, so `union!`'s `max_values` exit cannot fire) agree with a reference
`===` set: iteration yields the reference elements, each once, in insertion
order, `length` is their number, and no internal `@assert` fails. -/
def IdSetOpsAgree : Prop :=
  ∀ ops : List SOp, (ops.map SOp.size).sum < 2 ^ 62 →
    let s := runS .any ops
    s.iterate = .ok (refS ops) ∧ s.length = (refS ops).length ∧ (refS ops).Nodup ∧
    ∀ x, s.mem x = decide (x ∈ refS ops)

/-- Every element of an `IdSet{T}` has type `T`, so iteration (`collect`)
never throws. -/
def IdSetElemsHaveEltype : Prop :=
  ∀ (T : JTy) (ops : List SOp), ∃ xs, (runS T ops).iterate = .ok xs

end JuliaLean.IdDicts
