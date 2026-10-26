import JuliaLean.Core

namespace JuliaLean.ArrayCov

def array2903FindIn (contains : Int → List Int → Bool)
    (array set : List Int) : List Nat :=
  ((List.range array.length).zip array).filterMap fun (index, value) =>
    if contains value set then some (index + 1) else none

def array2910FindInConvert (makeSet : List Int → List Int)
    (findin : List Int → List Int → List Nat) (array values : List Int) : List Nat :=
  findin array (makeSet values)

def array2915SortedFindLoop (isless : Int → Int → Bool) :
    Nat → List Int → List Int → Nat → Nat → List Nat → List Nat
  | 0, _, _, _, _, output => output.reverse
  | fuel + 1, left, right, i, j, output =>
      if i ≥ left.length || j ≥ right.length then output.reverse
      else
        let l := left.getD i 0
        let r := right.getD j 0
        if isless l r then array2915SortedFindLoop isless fuel left right (i + 1) j output
        else if isless r l then array2915SortedFindLoop isless fuel left right i (j + 1) output
        else array2915SortedFindLoop isless fuel left right (i + 1) j ((i + 1) :: output)

def array2915SortedFind (isless : Int → Int → Bool)
    (left right : List Int) : List Nat :=
  array2915SortedFindLoop isless (left.length + right.length + 1) left right 0 0 []

def array2957FindAllIn (issorted : List Int → Bool)
    (sortedFind findIn : List Int → List Int → List Nat)
    (array values : List Int) : List Nat :=
  if issorted array && issorted values then sortedFind array values else findIn array values

def ArrayFindInCorrect : Prop :=
  (∀ contains array set, array2903FindIn contains array set =
      ((List.range array.length).zip array).filterMap fun (index, value) =>
        if contains value set then some (index + 1) else none) ∧
  (∀ make find array values, array2910FindInConvert make find array values =
      find array (make values)) ∧
  (∀ isless left right, array2915SortedFind isless left right =
      array2915SortedFindLoop isless (left.length + right.length + 1) left right 0 0 []) ∧
  (∀ sorted merge find array values, array2957FindAllIn sorted merge find array values =
      if sorted array && sorted values then merge array values else find array values)

theorem arrayFindInCorrect : ArrayFindInCorrect := by
  simp [ArrayFindInCorrect, array2903FindIn, array2910FindInConvert,
    array2915SortedFind, array2957FindAllIn]

def array3020FilterLoop (setindex : List Int → Nat → Int → List Int)
    (predicate : Int → Bool) : List Int → List Int → Nat → List Int × Nat
  | [], output, index => (output, index)
  | value :: rest, output, index =>
      let output := setindex output index value
      let index := if predicate value then index + 1 else index
      array3020FilterLoop setindex predicate rest output index

def array3020FilterArray (allocate : Nat → List Int)
    (setindex : List Int → Nat → Int → List Int) (resize : List Int → Nat → List Int)
    (sizehint : List Int → Nat → List Int) (predicate : Int → Bool)
    (array : List Int) : List Int :=
  let result := array3020FilterLoop setindex predicate array (allocate array.length) 1
  let output := resize result.1 (result.2 - 1)
  sizehint output output.length

def array3032FilterAbstract (linear : Bool)
    (logicalIndex : List Int → List Bool → List Int)
    (integerIndex : List Int → List Int → List Int)
    (allocate : Nat → List Int) (setindex : List Int → Nat → Int → List Int)
    (resize : List Int → Nat → List Int) (empty : List Int → List Int)
    (sizehint : List Int → Nat → List Int)
    (predicate : Int → Bool) (array : List Int) : List Int :=
  if !linear then logicalIndex array (array.map predicate)
  else
    let result := array3020FilterLoop setindex predicate array (allocate array.length) 1
    let indices := resize result.1 (result.2 - 1)
    let output := integerIndex array indices
    let indices := empty indices
    let _ := sizehint indices 0
    output

def array3105FilterFix (filter : (Int → Bool) → List Int → List Int)
    (predicate : Int → Bool) : List Int → List Int :=
  fun array => filter predicate array

def ArrayFilterCorrect : Prop :=
  (∀ allocate set resize hint predicate array,
      array3020FilterArray allocate set resize hint predicate array =
      let result := array3020FilterLoop set predicate array (allocate array.length) 1
      let output := resize result.1 (result.2 - 1)
      hint output output.length) ∧
  (∀ linear logical integer allocate set resize empty hint predicate array,
      array3032FilterAbstract linear logical integer allocate set resize empty hint predicate array =
      if !linear then logical array (array.map predicate)
      else
        let result := array3020FilterLoop set predicate array (allocate array.length) 1
        let indices := resize result.1 (result.2 - 1)
        let output := integer array indices
        let indices := empty indices
        let _ := hint indices 0
        output) ∧
  (∀ filter predicate array, array3105FilterFix filter predicate array = filter predicate array)

theorem arrayFilterCorrect : ArrayFilterCorrect := by
  simp [ArrayFilterCorrect, array3020FilterArray, array3032FilterAbstract,
    array3105FilterFix]

def array3134KeepAt (keep : List Int → List Int → Jl (List Int))
    (array indices : List Int) : Jl (List Int) := keep array indices

def array3159KeepMask (keep : List Int → List Bool → Jl (List Int))
    (array : List Int) (mask : List Bool) : Jl (List Int) := keep array mask

def array3164UniqueFilter (predicate : Int → List Int → Bool)
    (update : List Int → Int → List Int) (state : List Int) :
    Int → Bool × List Int :=
  fun value => if predicate value state then (true, update state value) else (false, state)

def array3174GrowFilter
    (uniqueFilter : (Int → List Int → Bool) → (List Int → Int → List Int) →
      List Int → (Int → Bool × List Int))
    (notIn : Int → List Int → Bool) (push : List Int → Int → List Int)
    (seen : List Int) : Int → Bool × List Int := uniqueFilter notIn push seen

def array3175ShrinkFilter
    (uniqueFilter : (Int → List Int → Bool) → (List Int → Int → List Int) →
      List Int → (Int → Bool × List Int))
    (isIn : Int → List Int → Bool) (pop : List Int → Int → List Int)
    (keep : List Int) : Int → Bool × List Int := uniqueFilter isIn pop keep

def array3177Grow (filter : (Int → Bool × List Int) → List Int → List Int)
    (mapfilter : (Int → Bool × List Int) → List Int → List Int → List Int)
    (predicate : Int → Bool × List Int) (vector : List Int)
    (iterators : List (List Int)) : List Int :=
  iterators.foldl (fun result iterator => mapfilter predicate iterator result)
    (filter predicate vector)

def array3185Union (makeSeen : List Int → List Int)
    (growFilter : List Int → Int → Bool × List Int)
    (grow : (Int → Bool × List Int) → List Int → List (List Int) → List Int)
    (vector : List Int) (iterators : List (List Int)) : List Int :=
  grow (growFilter (makeSeen vector)) vector iterators

def array3188Symdiff := array3185Union

def array3191Shrink (unique : List Int → List Int)
    (shrinkSet : List Int → List (List Int) → List Int)
    (filterIn : List Int → List Int → List Int)
    (vector : List Int) (iterators : List (List Int)) : List Int :=
  let vector := unique vector
  let seen := shrinkSet vector iterators
  filterIn seen vector

def array3198Intersect (shrink : List Int → List (List Int) → List Int)
    (vector : List Int) (iterators : List (List Int)) : List Int := shrink vector iterators

def array3199Setdiff := array3198Intersect

def array3201VectorFilter (predicate : Int → Bool) (vector : List Int) : List Int :=
  vector.filter predicate

def array3203Intersect (promote : List Int → List (List Int) → Int)
    (setIntersect : Int → List Int → List (List Int) → List Int)
    (vectorFilter : Int → (Int → Bool) → List Int → List Int)
    (shrinkPredicate : List Int → Int → Bool)
    (iterator : List Int) (iterators : List (List Int)) : List Int :=
  let type := promote iterator iterators
  let keep := setIntersect type iterator iterators
  vectorFilter type (shrinkPredicate keep) iterator

def array3209Setdiff (setDiff : List Int → List (List Int) → List Int)
    (vectorFilter : (Int → Bool) → List Int → List Int)
    (shrinkPredicate : List Int → Int → Bool)
    (iterator : List Int) (iterators : List (List Int)) : List Int :=
  let keep := setDiff iterator iterators
  vectorFilter (shrinkPredicate keep) iterator

def array3215IntersectRange (contains : Int → List Int → Bool)
    (unique : List Int → List Int) (vector range : List Int) : List Int :=
  unique (vector.filter fun value => contains value range)

def array3221IntersectRangeReverse (intersect : List Int → List Int → List Int)
    (range vector : List Int) : List Int := intersect vector range

def ArraySetLikeCorrect : Prop :=
  (∀ keep array indices, array3134KeepAt keep array indices = keep array indices) ∧
  (∀ keep array mask, array3159KeepMask keep array mask = keep array mask) ∧
  (∀ pred update state value, array3164UniqueFilter pred update state value =
      if pred value state then (true, update state value) else (false, state)) ∧
  (∀ make notIn push seen value, array3174GrowFilter make notIn push seen value =
      make notIn push seen value) ∧
  (∀ make isIn pop keep value, array3175ShrinkFilter make isIn pop keep value =
      make isIn pop keep value) ∧
  (∀ filter map predicate vector iterators,
      array3177Grow filter map predicate vector iterators =
      iterators.foldl (fun result iterator => map predicate iterator result)
        (filter predicate vector)) ∧
  (∀ make filter grow vector iterators, array3185Union make filter grow vector iterators =
      grow (filter (make vector)) vector iterators) ∧
  (∀ make filter grow vector iterators, array3188Symdiff make filter grow vector iterators =
      grow (filter (make vector)) vector iterators) ∧
  (∀ unique shrink filter vector iterators,
      array3191Shrink unique shrink filter vector iterators =
      let vector := unique vector
      let seen := shrink vector iterators
      filter seen vector) ∧
  (∀ shrink vector iterators, array3198Intersect shrink vector iterators =
      shrink vector iterators) ∧
  (∀ shrink vector iterators, array3199Setdiff shrink vector iterators =
      shrink vector iterators) ∧
  (∀ predicate vector, array3201VectorFilter predicate vector = vector.filter predicate) ∧
  (∀ promote intersect filter shrink iterator iterators,
      array3203Intersect promote intersect filter shrink iterator iterators =
      let type := promote iterator iterators
      let keep := intersect type iterator iterators
      filter type (shrink keep) iterator) ∧
  (∀ diff filter shrink iterator iterators,
      array3209Setdiff diff filter shrink iterator iterators =
      let keep := diff iterator iterators
      filter (shrink keep) iterator) ∧
  (∀ contains unique vector range, array3215IntersectRange contains unique vector range =
      unique (vector.filter fun value => contains value range)) ∧
  (∀ intersect range vector, array3221IntersectRangeReverse intersect range vector =
      intersect vector range)

theorem arraySetLikeCorrect : ArraySetLikeCorrect := by
  simp [ArraySetLikeCorrect, array3134KeepAt, array3159KeepMask,
    array3164UniqueFilter, array3174GrowFilter, array3175ShrinkFilter,
    array3177Grow, array3185Union, array3188Symdiff, array3191Shrink,
    array3198Intersect, array3199Setdiff, array3201VectorFilter,
    array3203Intersect, array3209Setdiff, array3215IntersectRange,
    array3221IntersectRangeReverse]

end JuliaLean.ArrayCov
