import JuliaLean.Core

namespace JuliaLean.ArrayCov

def indcopyTrailing (mulWrap : Int → Int → Int)
    (sizes : List Int) (start : Nat) : Int :=
  (sizes.drop start).foldl mulWrap 1

def array2970Indcopy (mulWrap : Int → Int → Int)
    (findin : List Int → List Int → List Int)
    (sizes : List Int) (indices : List (List Int)) :
    Jl (List (List Int) × List (List Int)) :=
  let n := indices.length
  if n = 0 then .error .boundsError
  else
    let trailing := indcopyTrailing mulWrap sizes (n - 1)
    let destination := (List.range n).map fun i =>
      findin (indices.getD i [])
        (List.range (if i + 1 < n then (sizes.getD i 0).toNat else trailing.toNat) |>.map
          fun x => ((x + 1 : Nat) : Int))
    let source := (List.range n).map fun i =>
      let positions := destination.getD i []
      positions.map fun position => (indices.getD i []).getD (position - 1).toNat 0
    .ok (destination, source)

def array2981IndcopyTuple := array2970Indcopy

inductive RangeIndexInput where
  | bool (value : Bool)
  | integer (value : Int)
  deriving Repr, DecidableEq

def array3224RangeGet (getindex : List Int → Int → Jl Int)
    (range : List Int) (index : RangeIndexInput) : Jl Int :=
  match index with
  | .bool _ => .error (.argumentError "invalid Bool index")
  | .integer value => getindex range value

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

end JuliaLean.ArrayCov
