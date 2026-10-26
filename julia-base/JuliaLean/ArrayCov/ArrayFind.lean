import JuliaLean.Core

namespace JuliaLean.ArrayCov

def array2404FindNext (identity : Int → Bool)
    (findnext : (Int → Bool) → List Int → Int → Option Int)
    (array : List Int) (start : Int) : Option Int :=
  findnext identity array start

def array2441FindFirst (identity : Int → Bool)
    (findfirst : (Int → Bool) → List Int → Option Int)
    (array : List Int) : Option Int := findfirst identity array

def array2444FindFirstArray (keys : List Int → List Int)
    (first : List Int → Int)
    (findnext : List Int → Int → Option Int) (array : List Int) : Option Int :=
  findnext array (first (keys array))

def array2523FindFirstPairs : List (Int × Int) → (Int → Bool) → Option Int
  | [], _ => none
  | (index, value) :: rest, predicate =>
      if predicate value then some index else array2523FindFirstPairs rest predicate

theorem array2523FindFirstPairs_eq (pairs : List (Int × Int)) (predicate : Int → Bool) :
    array2523FindFirstPairs pairs predicate =
      (pairs.find? fun pair => predicate pair.2).map (·.1) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp [array2523FindFirstPairs, ih]
      split <;> simp_all

def array2531FindFirstIndexed (keys : List Int → List Int)
    (first : List Int → Int)
    (findnext : (Int → Bool) → List Int → Int → Option Int)
    (predicate : Int → Bool) (array : List Int) : Option Int :=
  findnext predicate array (first (keys array))

def array2591FindPrev (identity : Int → Bool)
    (findprev : (Int → Bool) → List Int → Int → Option Int)
    (array : List Int) (start : Int) : Option Int :=
  findprev identity array start

def array2629FindLast (identity : Int → Bool)
    (findlast : (Int → Bool) → List Int → Option Int)
    (array : List Int) : Option Int := findlast identity array

def array2632FindLastArray (keys : List Int → List Int)
    (last : List Int → Int)
    (findprev : List Int → Int → Option Int) (array : List Int) : Option Int :=
  findprev array (last (keys array))

def array2716FindLastPairs (pairs : List (Int × Int))
    (predicate : Int → Bool) : Option Int :=
  array2523FindFirstPairs pairs.reverse predicate

def array2724FindLastIndexed (keys : List Int → List Int)
    (last : List Int → Int)
    (findprev : (Int → Bool) → List Int → Int → Option Int)
    (predicate : Int → Bool) (array : List Int) : Option Int :=
  findprev predicate array (last (keys array))

def array2728FindLastUnit (findfirst : (Int → Bool) → List Int → Option Int)
    (predicate : Int → Bool) (range : List Int) : Option Int :=
  findfirst predicate range

def array2733FindLastStep := array2728FindLastUnit

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

def array2534FindOneTo (convert : Int → Jl Int) (value stop : Int) : Jl (Option Int) :=
  if 1 ≤ value && value ≤ stop then (convert value).map some else .ok none

def array2537FindZeroOneTo (_ : Unit) : Option Int := none

def array2538FindOneOneTo (oneunit : Int → Int) (keyType stop : Int) : Option Int :=
  if stop < 1 then none else some (oneunit keyType)

def array2540FindUnitRange (first last firstKey : Int)
    (convertOffset : Int → Int) (value : Int) : Option Int :=
  if !(first ≤ value && value ≤ last) then none
  else some (firstKey + convertOffset (value - first))

def array2546FindStep (minimum maximum first step : JInt64)
    (convert : JInt64 → Jl Int) (value : JInt64) : Jl (Option Int) := do
  if maximum < minimum then return none
  if value < minimum || maximum < value then return none
  let difference := value - first
  let remainder ← JInt.remInt difference step
  if remainder.val != 0 then return none
  let quotient ← JInt.div difference step
  (convert (quotient + JInt.lit .i64 1)).map some

def array2554FindZeroRange (first : List Int → Int) (zero : Int → Int)
    (findfirst : Int → List Int → Option Int) (range : List Int) : Option Int :=
  findfirst (zero (first range)) range

def array2555FindOneRange (first : List Int → Int) (one : Int → Int)
    (findfirst : Int → List Int → Option Int) (range : List Int) : Option Int :=
  findfirst (one (first range)) range

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

def array2789FindAll (defaultEltype : List Int → Option Int)
    (defaultKeyType : List Int → Int)
    (collectTyped : Int → List Int → List Int)
    (collect : List Int → List Int)
    (predicate : Int → Bool) (pairs : List (Int × Int)) : List Int :=
  let selected := (pairs.filter fun pair => predicate pair.2).map (·.1)
  match defaultEltype selected with
  | none => collectTyped (defaultKeyType selected) selected
  | some _ => collect selected

def array2796FindAllBroadcast (broadcast : (Int → Bool) → List Int → List Bool)
    (findall : List Bool → List Int) (predicate : Int → Bool)
    (array : List Int) : List Int := findall (broadcast predicate array)

def array2838FindAll (pairs : List (Int × Bool)) : List Int :=
  (pairs.filter fun pair => pair.2).map (·.1)

def array2843FindAllBoolLoop : List (Int × Bool) → List Int
  | [] => []
  | (index, value) :: rest =>
      if value then index :: array2843FindAllBoolLoop rest else array2843FindAllBoolLoop rest

def array2843FindAllBool (count : List Bool → Nat)
    (pairs : List (Int × Bool)) : List Int :=
  (array2843FindAllBoolLoop pairs).take (count (pairs.map (·.2)))

def array2856FindAllBoolScalar (value : Bool) : List Int := if value then [1] else []
def array2857FindAllNumber (predicate : Int → Bool) (value : Int) : List Int :=
  if predicate value then [1] else []
def array2858FindAllInNumber (contains : Int → List Int → Bool)
    (value : Int) (set : List Int) : List Int := if contains value set then [1] else []

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

end JuliaLean.ArrayCov
