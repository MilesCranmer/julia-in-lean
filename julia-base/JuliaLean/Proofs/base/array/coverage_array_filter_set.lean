import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

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
