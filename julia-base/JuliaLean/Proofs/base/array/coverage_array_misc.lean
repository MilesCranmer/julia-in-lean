import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

def ArrayComparisonCorrect : Prop :=
  (∀ delete array, array2155Empty delete array = delete array array.length) ∧
  (∀ pointer memcmp cmp left right, array2161CmpBytes pointer memcmp cmp left right =
      let result := memcmp (pointer left) (pointer right) (min left.length right.length)
      if result < 0 then -1 else if result > 0 then 1 else cmp left.length right.length) ∧
  (∀ size pointer width memcmp left right,
      array2176EqualBits size pointer width memcmp left right =
      if size left = size right then
        memcmp (pointer left) (pointer right) (width * left.length) = 0 else false) ∧
  (∀ pointer width memcmp left right,
      array2193EqualBitVector pointer width memcmp left right =
      if left.length = right.length then
        memcmp (pointer left) (pointer right) (width * left.length) = 0 else false)

theorem arrayComparisonCorrect : ArrayComparisonCorrect := by
  simp [ArrayComparisonCorrect, array2155Empty, array2161CmpBytes,
    array2176EqualBits, array2193EqualBitVector]

def ArrayReverseRoutesCorrect : Prop :=
  (∀ route array dims, array2271ReverseDims route array dims = route array dims) ∧
  (∀ reverse first last array, array2272ReverseColon reverse first last array =
      reverse array (first array) (last array)) ∧
  (∀ route array dim, array2273ReverseTuple route array dim = route array dim) ∧
  (∀ throw colon array dim, array2274ReverseDim throw colon array dim = do
      if dim = 1 then pure () else throw dim
      colon array) ∧
  (∀ linear first last array index, array2281ReverseIndex linear first last array index =
      let indices := linear array
      first indices + last indices - index) ∧
  (∀ sub shift add low high, array2288Midpoint sub shift add low high =
      add low (shift (sub high low))) ∧
  (∀ promote midpoint low high, array2289MidpointPromoted promote midpoint low high =
      let values := promote low high
      midpoint values.1 values.2)

theorem arrayReverseRoutesCorrect : ArrayReverseRoutesCorrect := by
  simp [ArrayReverseRoutesCorrect, array2271ReverseDims, array2272ReverseColon,
    array2273ReverseTuple, array2274ReverseDim, array2281ReverseIndex,
    array2288Midpoint, array2289MidpointPromoted]

def ArrayConcatCorrect : Prop :=
  (∀ u, array2337VcatEmpty u = []) ∧
  (∀ u, array2338HcatEmpty u = []) ∧
  (∀ first rest, array2340Hcat (first :: rest) =
      if rest.any (fun vector => vector.length != first.length) then
        .error .dimensionMismatch
      else .ok (List.range first.length |>.map fun i =>
        (first :: rest).map fun vector => vector.getD i 0)) ∧
  (∀ cat vectors, array2349HcatGeneric cat vectors = cat vectors 2) ∧
  (∀ add allocate copy vectors, array2351Vcat add allocate copy vectors = do
      let length := array2351Total add vectors
      let output ← allocate length
      array2351CopyLoop copy output 1 vectors) ∧
  (∀ cat vectors, array2366VcatGeneric cat vectors = cat vectors 1) ∧
  (∀ reshape rank values, array2368CatIntegers reshape rank values =
      reshape values (List.replicate (rank - 1) (1 : Int) ++ [(values.length : Int)]))

theorem arrayConcatCorrect : ArrayConcatCorrect := by
  simp [ArrayConcatCorrect, array2337VcatEmpty, array2338HcatEmpty,
    array2340Hcat, array2349HcatGeneric, array2351Vcat,
    array2366VcatGeneric, array2368CatIntegers]

end JuliaLean.ArrayCov
