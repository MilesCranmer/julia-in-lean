import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

theorem array2523FindFirstPairs_eq (pairs : List (Int × Int)) (predicate : Int → Bool) :
    array2523FindFirstPairs pairs predicate =
      (pairs.find? fun pair => predicate pair.2).map (·.1) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp [array2523FindFirstPairs, ih]
      split <;> simp_all

def ArrayFindRoutingCorrect : Prop :=
  (∀ identity find array start, array2404FindNext identity find array start =
      find identity array start) ∧
  (∀ identity find array, array2441FindFirst identity find array = find identity array) ∧
  (∀ keys first find array, array2444FindFirstArray keys first find array =
      find array (first (keys array))) ∧
  (∀ predicate pairs, array2523FindFirstPairs pairs predicate =
      (pairs.find? fun pair => predicate pair.2).map (·.1)) ∧
  (∀ keys first find predicate array,
      array2531FindFirstIndexed keys first find predicate array =
      find predicate array (first (keys array))) ∧
  (∀ identity find array start, array2591FindPrev identity find array start =
      find identity array start) ∧
  (∀ identity find array, array2629FindLast identity find array = find identity array) ∧
  (∀ keys last find array, array2632FindLastArray keys last find array =
      find array (last (keys array))) ∧
  (∀ pairs predicate, array2716FindLastPairs pairs predicate =
      (pairs.reverse.find? fun pair => predicate pair.2).map (·.1)) ∧
  (∀ keys last find predicate array, array2724FindLastIndexed keys last find predicate array =
      find predicate array (last (keys array))) ∧
  (∀ find predicate range, array2728FindLastUnit find predicate range = find predicate range) ∧
  (∀ find predicate range, array2733FindLastStep find predicate range = find predicate range)

theorem arrayFindRoutingCorrect : ArrayFindRoutingCorrect := by
  simp [ArrayFindRoutingCorrect, array2404FindNext, array2441FindFirst,
    array2444FindFirstArray, array2523FindFirstPairs_eq, array2531FindFirstIndexed,
    array2591FindPrev, array2629FindLast, array2632FindLastArray,
    array2716FindLastPairs, array2724FindLastIndexed, array2728FindLastUnit,
    array2733FindLastStep]

def ArrayRangeFindCorrect : Prop :=
  (∀ convert value stop, array2534FindOneTo convert value stop =
      if 1 ≤ value && value ≤ stop then (convert value).map some else .ok none) ∧
  (∀ u, array2537FindZeroOneTo u = none) ∧
  (∀ one type stop, array2538FindOneOneTo one type stop =
      if stop < 1 then none else some (one type)) ∧
  (∀ first last key convert value, array2540FindUnitRange first last key convert value =
      if !(first ≤ value && value ≤ last) then none
      else some (key + convert (value - first))) ∧
  (∀ first zero find range, array2554FindZeroRange first zero find range =
      find (zero (first range)) range) ∧
  (∀ first one find range, array2555FindOneRange first one find range =
      find (one (first range)) range)

theorem arrayRangeFindCorrect : ArrayRangeFindCorrect := by
  simp [ArrayRangeFindCorrect, array2534FindOneTo, array2537FindZeroOneTo,
    array2538FindOneOneTo, array2540FindUnitRange, array2554FindZeroRange,
    array2555FindOneRange]

def ArrayFindAllCorrect : Prop :=
  (∀ default type collectTyped collect predicate pairs,
      array2789FindAll default type collectTyped collect predicate pairs =
      let selected := (pairs.filter fun pair => predicate pair.2).map (·.1)
      match default selected with
      | none => collectTyped (type selected) selected
      | some _ => collect selected) ∧
  (∀ broadcast find predicate array, array2796FindAllBroadcast broadcast find predicate array =
      find (broadcast predicate array)) ∧
  (∀ pairs, array2838FindAll pairs = (pairs.filter fun pair => pair.2).map (·.1)) ∧
  (∀ count pairs, array2843FindAllBool count pairs =
      (array2843FindAllBoolLoop pairs).take (count (pairs.map (·.2)))) ∧
  (∀ value, array2856FindAllBoolScalar value = if value then [1] else []) ∧
  (∀ predicate value, array2857FindAllNumber predicate value =
      if predicate value then [1] else []) ∧
  (∀ contains value set, array2858FindAllInNumber contains value set =
      if contains value set then [1] else [])

theorem arrayFindAllCorrect : ArrayFindAllCorrect := by
  simp [ArrayFindAllCorrect, array2789FindAll, array2796FindAllBroadcast,
    array2838FindAll, array2843FindAllBool, array2856FindAllBoolScalar,
    array2857FindAllNumber, array2858FindAllInNumber]
  intros
  rfl

end JuliaLean.ArrayCov
