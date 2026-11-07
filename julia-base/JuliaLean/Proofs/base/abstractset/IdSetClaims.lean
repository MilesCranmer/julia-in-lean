import JuliaLean.Proofs.base.idset.OperationHistories
import JuliaLean.base.abstractset

namespace JuliaLean.IdDicts

/-- `symdiff!(s, itr)` on an `IdSet{Any}`: `x` is in the result exactly when
it is in `s` or `===` an element of `itr`, but not both. -/
def IdSetSymdiffIdentity : Prop :=
  ∀ (ops : List SOp) (itr : List JVal) (x : JVal),
    let s := runS .any ops
    (s.symdiffVec itr).mem x = (s.mem x != decide (x ∈ itr))

/-- `issetequal(a, b) == (a ⊆ b && b ⊆ a)` for an `IdSet{Any}` `a` and a
vector `b`, in both argument orders. -/
def IdSetIssetequalSubsets : Prop :=
  ∀ (ops : List SOp) (b : List JVal),
    let a := Coll.ids (runS .any ops)
    issetequal a (.vec b) = (issubset a (.vec b) && issubset (.vec b) a) ∧
    issetequal (.vec b) a = (issubset (.vec b) a && issubset a (.vec b))

/-- `issubset(a, b) == all(x -> x in b, a)` for an `IdSet{Any}` `a` and a
`Set` or vector `b`. -/
def IdSetIssubsetIn : Prop :=
  ∀ (ops : List SOp) (b : List JVal),
    let a := Coll.ids (runS .any ops)
    issubset a (.set (jsetOf b)) = a.elems.all (Coll.set (jsetOf b)).mem ∧
    issubset a (.vec b) = a.elems.all (Coll.vec b).mem

/-- `a = [1]; b = [1]; symdiff!(IdSet{Any}(), [a, b])` loses `a`. -/
theorem idSetSymdiffIdentity_refuted : ¬ IdSetSymdiffIdentity := by
  intro h
  have := h [] [.vec 0 1, .vec 1 1] (.vec 0 1)
  revert this
  decide

/-- `issetequal(IdSet{Any}(Any[1, 1.0]), Any[1, 1.0])` -/
theorem idSetIssetequalSubsets_refuted : ¬ IdSetIssetequalSubsets := by
  intro h
  have := (h [.push (.int 1), .push (.flt 1)] [.int 1, .flt 1]).1
  revert this
  decide

/-- `IdSet{Any}(Any[1, 1.0]) ⊆ Set([1])` -/
theorem idSetIssubsetIn_refuted : ¬ IdSetIssubsetIn := by
  intro h
  have := (h [.push (.int 1), .push (.flt 1)] [.int 1]).1
  revert this
  decide

end JuliaLean.IdDicts
