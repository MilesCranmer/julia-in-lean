import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

def ArrayIndcopyRangeCorrect : Prop :=
  (∀ mul find sizes indices, array2970Indcopy mul find sizes indices =
      let n := indices.length
      if n = 0 then .error .boundsError
      else
        let trailing := indcopyTrailing mul sizes (n - 1)
        let destination := (List.range n).map fun i =>
          find (indices.getD i [])
            (List.range (if i + 1 < n then (sizes.getD i 0).toNat else trailing.toNat) |>.map
              fun x => ((x + 1 : Nat) : Int))
        let source := (List.range n).map fun i =>
          let positions := destination.getD i []
          positions.map fun position => (indices.getD i []).getD (position - 1).toNat 0
        .ok (destination, source)) ∧
  (∀ mul find sizes indices, array2981IndcopyTuple mul find sizes indices =
      array2970Indcopy mul find sizes indices) ∧
  (∀ get range index, array3224RangeGet get range index =
      match index with
      | .bool _ => .error (.argumentError "invalid Bool index")
      | .integer value => get range value)

theorem arrayIndcopyRangeCorrect : ArrayIndcopyRangeCorrect := by
  simp [ArrayIndcopyRangeCorrect, array2970Indcopy, array2981IndcopyTuple,
    array3224RangeGet]
  intros
  rfl

end JuliaLean.ArrayCov
