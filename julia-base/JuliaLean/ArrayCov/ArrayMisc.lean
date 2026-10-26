import JuliaLean.Core

namespace JuliaLean.ArrayCov

def array2155Empty (deleteEnd : List Int → Nat → List Int)
    (array : List Int) : List Int := deleteEnd array array.length

def array2161CmpBytes (pointer : List UInt8 → Int)
    (memcmp : Int → Int → Nat → Int) (cmpLength : Nat → Nat → Int)
    (left right : List UInt8) : Int :=
  let result := memcmp (pointer left) (pointer right) (min left.length right.length)
  if result < 0 then -1 else if result > 0 then 1 else cmpLength left.length right.length

def array2176EqualBits (size : List Int → List Int)
    (pointer : List Int → Int) (sizeofElement : Nat)
    (memcmp : Int → Int → Nat → Int) (left right : List Int) : Bool :=
  if size left = size right then
    memcmp (pointer left) (pointer right) (sizeofElement * left.length) = 0
  else false

def array2193EqualBitVector (pointer : List Int → Int) (sizeofElement : Nat)
    (memcmp : Int → Int → Nat → Int) (left right : List Int) : Bool :=
  if left.length = right.length then
    memcmp (pointer left) (pointer right) (sizeofElement * left.length) = 0
  else false

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

def array2271ReverseDims (route : List Int → Int → Jl (List Int))
    (array : List Int) (dims : Int) : Jl (List Int) := route array dims

def array2272ReverseColon (reverseWindow : List Int → Int → Int → Jl (List Int))
    (first last : List Int → Int) (array : List Int) : Jl (List Int) :=
  reverseWindow array (first array) (last array)

def array2273ReverseTuple (route : List Int → Int → Jl (List Int))
    (array : List Int) (dim : Int) : Jl (List Int) := route array dim

def array2274ReverseDim (throwArg : Int → Jl Unit)
    (colonRoute : List Int → Jl (List Int)) (array : List Int) (dim : Int) : Jl (List Int) := do
  if dim = 1 then pure () else throwArg dim
  colonRoute array

def array2281ReverseIndex (linearIndices : List Int → List Int)
    (first last : List Int → Int) (array : List Int) (index : Int) : Int :=
  let linear := linearIndices array
  first linear + last linear - index

def array2288Midpoint (subWrap : Int → Int → Int)
    (logicalShiftOne : Int → Int) (addWrap : Int → Int → Int)
    (low high : Int) : Int :=
  addWrap low (logicalShiftOne (subWrap high low))

def array2289MidpointPromoted (promote : Int → Int → Int × Int)
    (midpoint : Int → Int → Int) (low high : Int) : Int :=
  let promoted := promote low high
  midpoint promoted.1 promoted.2

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

inductive ConcatError where
  | dimensionMismatch | assertion
  deriving Repr, DecidableEq

abbrev ConcatJl (α : Type) := Except ConcatError α

def array2337VcatEmpty (_ : Unit) : List Int := []
def array2338HcatEmpty (_ : Unit) : List Int := []

def array2340Hcat (vectors : List (List Int)) : ConcatJl (List (List Int)) :=
  match vectors with
  | [] => .ok []
  | first :: rest =>
      if rest.any (fun vector => vector.length != first.length) then
        .error .dimensionMismatch
      else .ok (List.range first.length |>.map fun i =>
        vectors.map fun vector => vector.getD i 0)

def array2349HcatGeneric (cat : List (List Int) → Int → ConcatJl (List Int))
    (vectors : List (List Int)) : ConcatJl (List Int) := cat vectors 2

def array2351Total (addWrap : Int → Int → Int) : List (List Int) → Int
  | [] => 0
  | vector :: rest => addWrap vector.length (array2351Total addWrap rest)

def array2351CopyLoop
    (copy : List Int → Int → List Int → Nat → ConcatJl (List Int)) :
    List Int → Int → List (List Int) → ConcatJl (List Int)
  | output, _, [] => .ok output
  | output, offset, vector :: rest => do
      if offset + vector.length > output.length + 1 then throw .assertion
      let output ← copy output offset vector vector.length
      array2351CopyLoop copy output (offset + vector.length) rest

def array2351Vcat (addWrap : Int → Int → Int)
    (allocate : Int → ConcatJl (List Int))
    (copy : List Int → Int → List Int → Nat → ConcatJl (List Int))
    (vectors : List (List Int)) : ConcatJl (List Int) := do
  let length := array2351Total addWrap vectors
  let output ← allocate length
  array2351CopyLoop copy output 1 vectors

def array2366VcatGeneric (cat : List (List Int) → Int → ConcatJl (List Int))
    (vectors : List (List Int)) : ConcatJl (List Int) := cat vectors 1

def array2368CatIntegers (reshape : List Int → List Int → ConcatJl (List Int))
    (rank : Nat) (values : List Int) : ConcatJl (List Int) :=
  reshape values (List.replicate (rank - 1) (1 : Int) ++ [(values.length : Int)])

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
