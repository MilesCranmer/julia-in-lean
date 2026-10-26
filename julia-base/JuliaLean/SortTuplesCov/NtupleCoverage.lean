import JuliaLean.SortTuplesCov.TupleCoverage

namespace JuliaLean.SortTuplesCov

open JuliaLean

/-- `ntupleany(f, n)`, `base/ntuple.jl:42-46`: reject negative lengths,
otherwise call `f` at the one-based indices and erase the element types to Any. -/
def ntupleAny {V : Type} (f : Nat → V) (n : Int) : Jl (List V) :=
  if n ≥ 0 then .ok ((List.range n.toNat).map fun i => f (i + 1))
  else .error (.argumentError "tuple length should be ≥ 0")

def NtupleAnyCorrect : Prop :=
  ∀ (V : Type) (f : Nat → V) (n : Int),
    ntupleAny f n = if n ≥ 0 then .ok ((List.range n.toNat).map fun i => f (i + 1))
      else .error (.argumentError "tuple length should be ≥ 0")

theorem ntupleAnyCorrect : NtupleAnyCorrect := by
  intro V f n
  rfl

/-- `reverse(t::NTuple{N})`, `base/ntuple.jl:89-93`, calls `ntuple` with
`t[end+1-i]`. -/
def NtupleReverseCorrect : Prop :=
  ∀ (V : Type) (t : List V), JuliaLean.Tuples.reverseNTuple t =
    (List.range t.length).mapM fun (k : Nat) =>
      JuliaLean.Tuples.getfield t ((t.length : Int) + 1 - ((k : Int) + 1))

theorem ntupleReverseCorrect : NtupleReverseCorrect := by
  unfold NtupleReverseCorrect
  intros
  rfl

end JuliaLean.SortTuplesCov
