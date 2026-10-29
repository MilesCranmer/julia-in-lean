import JuliaLean.base.set
import JuliaLean.base.int
import JuliaLean.base.dict
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.set

open JuliaLean
open JuliaLean.base.set
open JuliaLean.Registry

/-! ## Specification vocabulary -/

def resultBool : Result Bool → Bool
  | .ok value => value
  | .error _ => false

def stableNubBy {α : Type} (equal : α → α → Bool) (values : List α) : List α :=
  values.foldl (fun out x => if out.any (equal x) then out else out ++ [x]) []

def stableMapNubBy {A K : Type} (equal : K → K → Bool) (f : A → K)
    (values : List A) : List A :=
  values.foldl (fun out x => if out.any (fun y => equal (f x) (f y)) then out else out ++ [x]) []

def listAllDistinctBy {α : Type} (equal : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !equal x y) && listAllDistinctBy equal xs

def listAllEqualBy {α : Type} (equal : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (equal x)

def groupHeadsBy {α : Type} (equal : α → α → Bool) (values : List α) : List α :=
  ((values.foldl (fun (previous, heads) x =>
    match previous with
    | none => (some x, [x])
    | some y => (some x, if equal x y then heads else heads ++ [x]))
    (none, [])).2)

def changedCountBy {α : Type} (same : α → α → Bool) (left right : List α) : Nat :=
  ((left.zip right).filter (fun pair => !same pair.1 pair.2)).length

def hasConvertedKey {Q K : Type} (ops : DictRuntime K)
    (convert : Q → DictResult K) (values : List Q) (key : K) : Bool :=
  values.any fun x => match convert x with
    | .ok converted => ops.equal key converted
    | .error _ => false

def DictRuntimeLawful {K : Type} (ops : DictRuntime K) : Prop :=
  (∀ x, ops.equal x x = true) ∧
  (∀ x y, ops.equal x y = ops.equal y x) ∧
  (∀ x y z, ops.equal x y = true → ops.equal y z = true → ops.equal x z = true) ∧
  (∀ x y, ops.equal x y = true → ops.hash x = ops.hash y)

def DictRuntimeCopyLawful {K : Type} (ops : DictRuntime K) : Prop :=
  (∀ n slots i, ops.copySlots n slots i = slots i) ∧
  (∀ n keys i, ops.copyKeys n keys i = keys i) ∧
  (∀ n values i, ops.copyValues n values i = values i)

def TypeOpsPreserveMembership {K : Type} (ops : DictRuntime K) (types : TypeOps K) : Prop :=
  ∀ tag s s', types.convertSet tag s = .ok s' →
    ∀ x, setInMethod ops x s' = setInMethod ops x s

def VectorOperationsLawful {α : Type} (empty : Nat → VectorModel α)
    (singleton : Nat → α → VectorModel α)
    (push : VectorModel α → α → Result (VectorModel α)) : Prop :=
  (∀ tag, (empty tag).values = [] ∧ (empty tag).eltype = tag) ∧
  (∀ tag x, (singleton tag x).values = [x] ∧ (singleton tag x).eltype = tag) ∧
  (∀ vector x result, push vector x = .ok result → result.values = vector.values ++ [x])

/-! ## Construction -/

def SetConstructionSpec : Prop :=
  (∀ (K : Type) tag, (setConstructorEmpty (K := K) tag).dict.count = 0) ∧
  (setConstructorAny.dict.count = 0) ∧
  (∀ (K : Type) (ops : DictRuntime K) (s : SetModel K) (x : K), DictRuntimeCopyLawful ops →
    setInMethod ops x (setConstructorCopy ops s) = setInMethod ops x s) ∧
  (∀ (K : Type) (ops : DictRuntime K) (s : KeySetModel K) (x : K), DictRuntimeCopyLawful ops →
    setInMethod ops x (setConstructorKeySet ops s) = setInMethod ops x (fromDict s.dict)) ∧
  (∀ (S K : Type) (s : S) (tag : Nat) (ops : DictRuntime K) (x : K),
    setInMethod ops x (setEmptyMethod s tag) = .ok false ∧
    setInMethod ops x (setEmptymutableMethod s) = .ok false ∧
    setInMethod ops x (setSimilarForMethod s tag) = .ok false)

def SetIteratorConstructionSpec : Prop :=
  ∀ (K Q : Type) (ops : DictRuntime K) (convert : Q → DictResult K)
    (unionBang : SetModel K → List Q → Result (SetModel K)) (values : List Q),
    (∀ out key, unionBang emptySet values = .ok out →
      setInMethod ops key out = .ok (hasConvertedKey ops convert values key)) →
    match setConstructorIterator unionBang values with
    | .error _ => False
    | .ok out => ∀ key, setInMethod ops key out = .ok (hasConvertedKey ops convert values key)

/-! ## Mutable Set behavior -/

def SetShowSpec : Prop :=
  ∀ (K : Type) (s : SetModel K) (log : List String),
    setShowMethod (fun xs text => xs ++ [text])
      (fun xs _ => xs ++ ["type"])
      (fun xs _ => xs ++ ["members"])
      (fun _ => 0) (fun _ _ => true) log s =
      if setIsEmptyMethod s then log ++ ["Set()"] else log ++ ["Set(", "members", ")"]

def SetMutationSpec : Prop :=
  ∀ (K Q : Type) (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv Q K)
    (s s' : SetModel K) (x : Q) (key y : K) (wasPresent : Bool)
    (newsize : JInt .i64),
    DictRuntimeLawful ops → DictRuntimeCopyLawful ops →
    keyConv.convert x = .ok key →
    (setPushMethod ops keyConv x s = .ok s' → setInMethod ops key s' = .ok true) ∧
    (setInBangMethod ops keyConv.convert x s = .ok (wasPresent, s') →
      setInMethod ops key s = .ok wasPresent ∧ setInMethod ops key s' = .ok true) ∧
    (setDeleteMethod ops key s = .ok s' → setInMethod ops key s' = .ok false) ∧
    (∀ y, setInMethod ops y (setCopyMethod ops s) = setInMethod ops y s) ∧
    (setRehashMethod ops s = .ok s' → ∀ y, setInMethod ops y s' = setInMethod ops y s) ∧
    (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true s newsize = .ok s' →
      ∀ y, setInMethod ops y s' = setInMethod ops y s) ∧
    (setInMethod ops y (setEmptyBangMethod ops s) = .ok false) ∧
    setLengthMethod s = JInt.wrap .i64 (Int.ofNat s.dict.count) ∧
    (∀ state next, setIterateMethod s state = .ok (some (y, next)) →
      setInMethod ops y s = .ok true)

def SetPopBehavior : Prop :=
  ∀ (K : Type) (ops : DictRuntime K) (s s' : SetModel K) (x default key : K),
    (setInMethod ops x s = .ok true →
      setPopKeyMethod ops x s = .ok (key, s') →
        ops.equal key x = true ∧ setInMethod ops key s' = .ok false) ∧
    (setInMethod ops x s = .ok false →
      setPopKeyMethod ops x s = .error (.dictionary .keyError)) ∧
    (setInMethod ops x s = .ok false →
      setPopDefaultMethod ops x default s = .ok (default, s)) ∧
    (setIsEmptyMethod s = true →
      setPopAnyMethod setIsEmptyMethod ops s = .error (.julia (.argumentError "set must be non-empty")))

def InBangEquiv : Prop :=
  (∀ (K S : Type) (contains : K → S → Result Bool) (push : S → K → Result S)
    (s s' : S) (x : K) (present : Bool),
    contains x s = .ok present →
    setInBangAbstractMethod contains push x s = .ok (present, s') →
      (present = true → s' = s) ∧ (present = false → push s x = .ok s')) ∧
  (∀ (K Q : Type) (ops : DictRuntime K) (convert : Q → DictResult K)
    (s s' : SetModel K) (x : Q) (key : K) (present : Bool),
    convert x = .ok key → setInMethod ops key s = .ok present →
    setInBangMethod ops convert x s = .ok (present, s') →
      setInMethod ops key s' = .ok true ∧
      ∀ y, setInMethod ops y s = .ok true → setInMethod ops y s' = .ok true)

/-! ## Set algebra -/

def SetSetdiffAgrees : Prop :=
  ∀ (K : Type) (ops : DictRuntime K) (s t out : SetModel K) (x : K),
    setdiffMethod setIterateMethod (setInMethod ops) (setDeleteMethod ops) s t = .ok out →
    setInMethod ops x s = .ok true →
    (setInMethod ops x t = .ok false → setInMethod ops x out = .ok true) ∧
    (setInMethod ops x t = .ok true → setInMethod ops x out = .ok false)

/-! ## Unique values -/

def UniqueSpec : Prop :=
  ∀ (α : Type) (ops : DictRuntime α) (keyConv : JuliaLean.base.dict.KeyConv α α)
    (types : TypeOps α) (trace : FiniteTrace α)
    (vectorEmpty : Nat → VectorModel α) (vectorSingleton : Nat → α → VectorModel α)
    (pushVector : VectorModel α → α → Result (VectorModel α)),
    DictRuntimeLawful ops → TypeOpsPreserveMembership ops types →
    (∀ x, keyConv.convert x = .ok x) →
    VectorOperationsLawful vectorEmpty vectorSingleton pushVector →
    trace.values.length ≤ ops.maxValues →
    match uniqueMethod trace types vectorEmpty vectorSingleton setConstructorEmpty
      (setPushMethod ops keyConv) (setInBangMethod ops keyConv.convert) pushVector
      (uniqueFromDispatch (uniqueFromMethod types (setInBangMethod ops keyConv.convert) pushVector)) with
    | .error _ => False
    | .ok result => result.values = stableNubBy ops.equal trace.values

def UniqueMappedSpec : Prop :=
  ∀ (A K : Type) (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv K K)
    (types : TypeOps K) (f : A → K) (values : List A)
    (vectorEmpty : Nat → VectorModel A) (pushVector : VectorModel A → A → Result (VectorModel A)),
    DictRuntimeLawful ops → TypeOpsPreserveMembership ops types →
    (∀ x, keyConv.convert x = .ok x) →
    VectorOperationsLawful vectorEmpty (fun tag x => ⟨tag, 1, [x]⟩) pushVector →
    values.length ≤ ops.maxValues →
    match uniqueMapMethod f values none vectorEmpty 0 setConstructorEmpty types.typeof
      (setPushMethod ops keyConv) (setInBangMethod ops keyConv.convert) pushVector
      (uniqueMapTail types (setInMethod ops) (setPushMethod ops keyConv) pushVector) with
    | .error _ => False
    | .ok result => result.values = stableMapNubBy ops.equal f values

def UniqueBangSpec : Prop :=
  ∀ (A K : Type) (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv K K)
    (types : TypeOps K) (f : A → K) (vector : VectorModel A),
    DictRuntimeLawful ops → TypeOpsPreserveMembership ops types →
    (∀ x, keyConv.convert x = .ok x) → vector.firstIndex = 1 →
    vector.values.length ≤ ops.maxValues →
    match uniqueBangMethod f vector none types.typeof setConstructorEmpty
      (setPushMethod ops keyConv)
      (uniqueBangCompactMethod (setInMethod ops) (setPushMethod ops keyConv)
        (fun y tag => types.subtype (types.typeof y) tag)
        types.typeof types.typejoin types.convertSet) with
    | .error _ => False
    | .ok result => result.values = stableMapNubBy ops.equal f vector.values

def GroupedUniqueSpec : Prop :=
  ∀ (α : Type) (equal : α → α → Bool) (vector : VectorModel α),
    vector.firstIndex = 1 →
    (groupedUniqueMethod equal vector).values = groupHeadsBy equal vector.values

def SetUniqueSpec : Prop := UniqueMappedSpec ∧ UniqueBangSpec

def OrderedEqualityLawful {α : Type} (equal less : α → α → Bool) : Prop :=
  (∀ x, less x x = false) ∧
  (∀ x y, less x y = true → equal x y = false) ∧
  (∀ x y, equal x y = true → less x y = false ∧ less y x = false) ∧
  (∀ x y, equal x y = false → less x y = true ∨ less y x = true) ∧
  (∀ x y z, less x y = true → less y z = true → less x z = true)

def ArrayUniqueSpec : Prop :=
  UniqueSpec ∧
  (∀ (α : Type) (ops : DictRuntime α) (keyConv : JuliaLean.base.dict.KeyConv α α)
    (equal less : α → α → Bool) (trace : FiniteTrace α),
    DictRuntimeLawful ops → OrderedEqualityLawful equal less →
    (∀ x, keyConv.convert x = .ok x) →
    alluniqueStridedMethod trace true equal less (indexedAlluniqueMethod equal)
      (hashedAlluniqueMethod setConstructorEmpty (setInBangMethod ops keyConv.convert)
        (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true)) =
      .ok (listAllDistinctBy equal trace.values)) ∧
  (∀ (α : Type) (equal : α → α → Bool) (trace : FiniteTrace α),
    allequalGeneric equal trace = .ok (listAllEqualBy equal trace.values))

/-! ## allunique and allequal -/

def AlluniqueSetSpec : Prop :=
  ∀ (S K : Type) (elements : S → List K) (equal : K → K → Bool) (s : S),
    alluniqueSetMethod s = listAllDistinctBy equal (elements s) ∧
    allequalSetMethod (fun value => (elements value).length) s =
      listAllEqualBy equal (elements s)

def RangeUniqueSpec : Prop :=
  ∀ (R K : Type) (step : R → R) (stepIsZero : R → Bool) (length : R → Nat)
    (elements : R → List K) (equal : K → K → Bool)
    (ofType : R → R → R) (singletonRange : R → R) (r first : R),
    alluniqueRangeMethod stepIsZero step length r =
      listAllDistinctBy equal (elements r) ∧
    allequalRangeMethod stepIsZero step length r =
      listAllEqualBy equal (elements r) ∧
    uniqueRangeMethod (alluniqueRangeMethod stepIsZero step length)
      ofType singletonRange r first =
        if listAllDistinctBy equal (elements r) then r else ofType r (singletonRange first)

def AlluniqueGenericSpec : Prop :=
  ∀ (K : Type) (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv K K)
    (trace : FiniteTrace K) (collect : FiniteTrace K → Result (FiniteTrace K)),
    DictRuntimeLawful ops → (∀ x, keyConv.convert x = .ok x) →
    (∀ input, collect input = .ok input) →
    alluniqueGeneric (fun input => input.hasLength) (fun input => input.length) collect
      (indexedAlluniqueMethod ops.equal)
      (hashedAlluniqueMethod setConstructorEmpty (setInBangMethod ops keyConv.convert)
        (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true)) trace =
      .ok (listAllDistinctBy ops.equal trace.values)

def AlluniqueMappedSpec : Prop :=
  ∀ (A K : Type) (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv K K)
    (input : FiniteTrace A) (output : FiniteTrace K) (f : A → K)
    (generator : (A → K) → FiniteTrace A → FiniteTrace K)
    (collect : FiniteTrace K → Result (FiniteTrace K)),
    DictRuntimeLawful ops → (∀ x, keyConv.convert x = .ok x) →
    generator f input = output → output.values = input.values.map f →
    (∀ trace, collect trace = .ok trace) →
    alluniqueMapMethod generator
      (alluniqueGeneric (fun trace => trace.hasLength) (fun trace => trace.length) collect
        (indexedAlluniqueMethod ops.equal)
        (hashedAlluniqueMethod setConstructorEmpty (setInBangMethod ops keyConv.convert)
          (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true)) )
      f input = .ok (listAllDistinctBy ops.equal output.values)

def SetPredicateSpec : Prop :=
  ∀ (K : Type) (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv K K)
    (trace : FiniteTrace K) (less : K → K → Bool),
    DictRuntimeLawful ops → (∀ x, keyConv.convert x = .ok x) →
    alluniqueStringMethod (fun value => value.values.length)
      (indexedAlluniqueMethod ops.equal)
      (hashedAlluniqueMethod setConstructorEmpty (setInBangMethod ops keyConv.convert)
        (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true)) trace =
      .ok (listAllDistinctBy ops.equal trace.values) ∧
    alluniqueStridedMethod trace false ops.equal less (indexedAlluniqueMethod ops.equal)
      (hashedAlluniqueMethod setConstructorEmpty (setInBangMethod ops keyConv.convert)
        (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true)) =
      .ok (listAllDistinctBy ops.equal trace.values) ∧
    alluniqueTupleMethod ops.equal
      (hashedAlluniqueMethod setConstructorEmpty (setInBangMethod ops keyConv.convert)
        (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true)) trace =
      .ok (listAllDistinctBy ops.equal trace.values) ∧
    alluniqueMapTuple id ops.equal
      (hashedAlluniqueMethod setConstructorEmpty (setInBangMethod ops keyConv.convert)
        (setSizehintMethod ops (JuliaLean.base.int.convert .i64) true)) trace =
      .ok (listAllDistinctBy ops.equal trace.values) ∧ alluniqueEmptyTuple = true

def AllequalTupleSpec : Prop :=
  ∀ (A K : Type) (f : A → Jl K) (equal : K → K → Bool)
    (values : List A) (mapped : A → K),
    (∀ x, f x = .ok (mapped x)) →
    allequalTupleMethod f equal true values (allequalLoopMethod f equal) =
      .ok (listAllEqualBy equal (values.map mapped)) ∧
    (allequalEmptyTuple = true)

def AllequalMapSpec : Prop :=
  ∀ (A K : Type) (equal : K → K → Bool) (values : FiniteTrace A)
    (generator : (A → K) → FiniteTrace A → FiniteTrace K) (f : A → K),
    allequalMapMethod generator (allequalGeneric equal) f values =
      .ok (listAllEqualBy equal ((generator f values).values))

/-! ## Hash and replacement helpers -/

def SetHashOrderIndependent : Prop :=
  ∀ (K : Type) (hashKey : K → JInt .u64)
    (combine : JInt .u64 → JInt .u64 → JInt .u64)
    (s : SetModel K) (seed : JInt .u64) (xs ys : List K), xs.Perm ys →
      setHashMethod hashKey combine (fun _ => .ok xs) s seed =
      setHashMethod hashKey combine (fun _ => .ok ys) s seed

def CheckCountSpec : Prop :=
  ∀ count : Int,
    if count < 0 then
      checkCountMethod count = .error (.domainError
        ("`count` must not be negative (got " ++ toString count ++ ")"))
    else
      checkCountMethod count = .ok (JInt.wrap .i64 (min count (IntTy.max .i64)))

def SetHashCheckCountSpec : Prop := SetHashOrderIndependent ∧ CheckCountSpec

def firstReplacement {α : Type} (equal : α → α → Bool) : List (α × α) → α → α
  | [], x => x
  | (old, new) :: rest, x => if equal old x then new else firstReplacement equal rest x

def SetReplaceSpec : Prop :=
  (∀ (α : Type) (equal : α → α → Bool) (pairs : List (α × α)) (x : α),
    replacePairsNewMethod equal pairs x = firstReplacement equal pairs x) ∧
  (∀ (α : Type) (new : α → Result α) (same : α → α → Bool)
    (sameVector : VectorModel α → VectorModel α → Bool)
    (result source out : VectorModel α) (count : Nat),
    result.values.length = source.values.length →
    replaceArrayMethod new same sameVector result source count = .ok out →
    out.values.length = source.values.length ∧ changedCountBy same source.values out.values ≤ count) ∧
  (∀ (α : Type) (new : α → Result α) (same : α → α → Bool)
    (values out : List α) (count : Nat),
    replaceTupleMethod new same values count = .ok out → out.length = values.length) ∧
  (∀ (α : Type) (equal same : α → α → Bool) (values out : List α)
    (count : Nat) (pairs : List (α × α)),
    replaceTuplePairsMethod equal same values count pairs = .ok out → out.length = values.length) ∧
  replaceAmbiguousBangOne = .error (.methodError "replace!") ∧
  replaceAmbiguousBangTwo = .error (.methodError "replace!") ∧
  replaceAmbiguousOne = .error (.methodError "replace") ∧
  replaceAmbiguousTwo = .error (.methodError "replace")

def SetReplaceWrappersSpec : Prop :=
  (∀ (A α : Type) (pairs : List (α × α)) (count : Int)
    (replacePairs : A → A → JInt .i64 → List (α × α) → Result A) (a : A),
    count < 0 →
    replacePairsBangWrapper pairs count checkCountMethod replacePairs a =
      .error (.julia (.domainError
        ("`count` must not be negative (got " ++ toString count ++ ")")))) ∧
  (∀ (A α : Type) (new : α → Result α) (a : A) (count : Int)
    (replaceInPlace : (α → Result α) → A → A → JInt .i64 → Result A),
    count < 0 →
    replaceCallableBangWrapper new a count checkCountMethod replaceInPlace =
      .error (.julia (.domainError
        ("`count` must not be negative (got " ++ toString count ++ ")")))) ∧
  (∀ (A B α : Type) (new : α → Result α) (a : A) (count : Int)
    (similarOrCopy : A → Result B)
    (replaceInPlace : (α → Result α) → B → A → JInt .i64 → Result B) (copy : B),
    count < 0 → similarOrCopy a = .ok copy →
    replaceCallableCopyWrapper new a similarOrCopy count checkCountMethod replaceInPlace =
      .error (.julia (.domainError
        ("`count` must not be negative (got " ++ toString count ++ ")")))) ∧
  (∀ (A B P : Type) (pairs : List P) (count : Int)
    (elementType : A → Nat) (promoteValues : List P → Nat)
    (subtractSingletons : Nat → List P → Nat) (promote : Nat → Nat → Nat)
    (similarOrCopy : A → Nat → Result B)
    (replacePairs : B → A → JInt .i64 → List P → Result B) (a : A) (copy : B),
    count < 0 → similarOrCopy a (promote (elementType a) (promoteValues pairs)) = .ok copy →
    replacePairsCopyMethod pairs (some count) elementType promoteValues subtractSingletons
      promote similarOrCopy checkCountMethod replacePairs a =
      .error (.julia (.domainError
        ("`count` must not be negative (got " ++ toString count ++ ")")))) ∧
  (∀ (α : Type) (f : α → Result α) (same : α → α → Bool)
    (values : List α) (count : Int),
    count < 0 →
    replaceTupleCallableMethod f same values count checkCountMethod =
      .error (.julia (.domainError
        ("`count` must not be negative (got " ++ toString count ++ ")")))) ∧
  (∀ (α : Type) (equal same : α → α → Bool) (values : List α)
    (pairs : List (α × α)) (count : Int),
    count < 0 →
    replaceTuplePairsWrapper equal same values pairs count checkCountMethod =
      .error (.julia (.domainError
        ("`count` must not be negative (got " ++ toString count ++ ")"))))

def ReplaceKeepsReplacements : Prop :=
  (∀ (K V A : Type) (ops : DictReplaceRuntime K V) (t t' : DictState K V)
    (new : (K × V) → DictResult (K × V)) (same : (K × V) → (K × V) → Bool)
    (source : A) (count : Nat) (original : List (K × V)),
    replaceDictMethod ops new same source t count = .ok t' →
    (∀ pair, pair ∈ original → JuliaLean.base.dict.haskey ops.hash ops.equal t pair.1 = .ok true →
      ∀ replacement, new pair = .ok replacement →
        JuliaLean.base.dict.haskey ops.hash ops.equal t' replacement.1 = .ok true)) ∧
  (∀ (K : Type) (ops : DictReplaceRuntime K Unit) (t t' : SetModel K)
    (new : K → DictResult K) (same : K → K → Bool) (count : Nat) (original : List K),
    replaceSetMethod ops new same t count = .ok t' →
    (∀ key, key ∈ original → JuliaLean.base.dict.haskey ops.hash ops.equal t.dict key = .ok true →
      ∀ replacement, new key = .ok replacement →
        JuliaLean.base.dict.haskey ops.hash ops.equal t'.dict replacement = .ok true))

def ReplaceGenericSetSpec : Prop :=
  ∀ (K : Type) (ops : DictRuntime K) (keyConv : JuliaLean.base.dict.KeyConv K K)
    (isDict isSet : SetModel K → Bool) (same : SetModel K → SetModel K → Bool)
    (elements : SetModel K → Result (List K)) (new : K → Result K)
    (identical : K → K → Bool) (s out : SetModel K) (values : List K) (f : K → K),
    isDict s = false → isSet s = true → same s s = true → elements s = .ok values →
    (∀ x, new x = .ok (f x)) → (∀ x, keyConv.convert x = .ok x) →
    (∀ x y, identical x y = true → ops.equal x y = true) →
    replaceAbstractCollectionsMethod isDict isSet same elements new identical asKeySet
      (setPopKeyMethod ops) (setPushMethod ops keyConv) s s values.length = .ok out →
    ∀ x, setInMethod ops x out = .ok (values.any fun y => ops.equal x (f y))

/-! ## Registry entries -/
def entries : List Entry := [
  { id := "bitsetscov-set-basic", juliaFile := "base/set.jl",
    juliaFns := ["Set{T}()", "Set{T}(s::Set{T})", "Set()", "Set{T}(s::KeySet)", "empty", "emptymutable", "_similar_for"],
    statement := "Set constructors preserve copied members, produce empty typed results, and initialize from iterator members with duplicate keys collapsed.",
    source := "Set constructors and source-body invariants; base/set.jl:42-73", status := .todo,
    prop := ``SetConstructionSpec },
  { id := "set-iterator-constructor-membership", juliaFile := "base/set.jl",
    juliaFns := ["Set{T}(itr)"],
    statement := "Constructing a Set from a finite iterator stores exactly its converted keys, with duplicates collapsed under isequal.",
    source := "Set constructor docstring and base/set.jl:47-65", status := .todo,
    prop := ``SetIteratorConstructionSpec },
  { id := "bitsetscov-set-mutable", juliaFile := "base/set.jl",
    juliaFns := ["show(::IO,::Set)"],
    statement := "show renders an empty Set as Set() and surrounds non-empty members with Set(...).",
    source := "base/set.jl:75-88", status := .todo, prop := ``SetShowSpec },
  { id := "set-mutation-membership", juliaFile := "base/set.jl",
    juliaFns := ["push!", "in!", "delete!", "copy", "sizehint!", "empty!", "rehash!", "length", "iterate"],
    statement := "Successful Set mutations add or remove the requested key, preserve unrelated membership, and keep length and iteration consistent with stored keys.",
    source := "Set mutation docstrings and backing Dict invariants; base/set.jl:90-176", status := .todo,
    prop := ``SetMutationSpec },
  { id := "set-pop-contract", juliaFile := "base/set.jl",
    juliaFns := ["pop!(::Set, key, default)", "pop!(::Set, key)", "pop!(::Set)"],
    statement := "Keyed pop removes and returns a stored key, returns the default when absent, and throws the documented errors for missing and empty sets.",
    source := "base/set.jl:139-162", status := .todo, prop := ``SetPopBehavior },
  { id := "dicts-set-in-bang-convert", juliaFile := "base/set.jl",
    juliaFns := ["in!(x, s::Set)"],
    statement := "in! returns whether the converted key was already present and leaves the converted key present without removing previous members.",
    source := "in! docstring base/set.jl:94-100", status := .todo, prop := ``InBangEquiv },
  { id := "dicts-set-setdiff", juliaFile := "base/set.jl",
    juliaFns := ["setdiff!(s::Set, t::Set)"],
    statement := "After setdiff!(s,t), a member is present exactly when it was in s and absent from t, in both size branches.",
    source := "setdiff! docstring base/abstractset.jl:225-243; base/set.jl:187-198", status := .todo,
    prop := ``SetSetdiffAgrees },
  { id := "arrayops-unique", juliaFile := "base/set.jl",
    juliaFns := ["unique(itr)", "_unique_from", "unique_from", "allunique(A::StridedArray)", "_indexed_allunique", "_hashed_allunique", "allequal(itr)"],
    statement := "unique retains the first value of each isequal class in order; allunique and allequal agree with pairwise isequal over the iterated values, including the strided-array fast path.",
    source := "unique, allunique and allequal docstrings; base/set.jl:200-260, 553-592, 648-656", status := .todo,
    prop := ``ArrayUniqueSpec },
  { id := "bitsetscov-set-unique", juliaFile := "base/set.jl",
    juliaFns := ["unique(f, C)", "_unique!(f, out::AbstractVector, C, seen, i)", "unique!(f, A::AbstractVector)", "_unique!(f, A::AbstractVector, seen, current, i)"],
    statement := "Mapped unique and unique! retain the first source value for each mapped isequal class in source order.",
    source := "unique and unique! docstrings; base/set.jl:301-434", status := .todo,
    prop := ``SetUniqueSpec },
  { id := "set-grouped-unique", juliaFile := "base/set.jl",
    juliaFns := ["_groupedunique!(A::AbstractVector)"],
    statement := "Grouped unique! retains exactly the first value from each adjacent equal run, in order.",
    source := "base/set.jl:417-434", status := .todo, prop := ``GroupedUniqueSpec },
  { id := "dicts-range-allunique-subulp", juliaFile := "base/set.jl",
    juliaFns := ["unique(::AbstractRange)", "allunique(::AbstractRange)", "allequal(::AbstractRange)"],
    statement := "For finite ranges, allunique and allequal agree with isequal over the elements, and unique returns the original range or its first-element singleton.",
    source := "allunique, allequal and unique range methods; base/set.jl:262,546,660", status := .todo,
    prop := ``RangeUniqueSpec },
  { id := "bitsetscov-set-predicates", juliaFile := "base/set.jl",
    juliaFns := ["allunique(s::AbstractString)", "allunique(A::StridedArray)", "allunique(t::Tuple)", "allunique(f::F,t::Tuple)"],
    statement := "String, strided-array, and tuple allunique specializations agree with isequal-based distinctness, including their fast-path cutoffs.",
    source := "allunique string, strided-array, and tuple methods; base/set.jl:549-607", status := .todo,
    prop := ``SetPredicateSpec },
  { id := "set-allunique-generic", juliaFile := "base/set.jl",
    juliaFns := ["allunique(C)", "_hashed_allunique(C)", "_indexed_allunique(A)"],
    statement := "Generic allunique returns true exactly when no two iterated values are isequal, regardless of the length-based algorithm branch.",
    source := "allunique docstring and base/set.jl:515-542,579-592", status := .todo,
    prop := ``AlluniqueGenericSpec },
  { id := "set-allunique-mapped", juliaFile := "base/set.jl",
    juliaFns := ["allunique(f, xs)"],
    statement := "Mapped allunique tests the generated values for pairwise isequal distinctness.",
    source := "allunique docstring and base/set.jl:523", status := .todo,
    prop := ``AlluniqueMappedSpec },
  { id := "set-allequal-tuple", juliaFile := "base/set.jl",
    juliaFns := ["_allequal_loop", "allequal(f, xs::Tuple)", "allequal(f, ::Tuple{})"],
    statement := "Tuple allequal returns true exactly when all successful mapped elements are isequal to the first, including the empty tuple.",
    source := "allequal docstring and base/set.jl:664-690,692", status := .todo,
    prop := ``AllequalTupleSpec },
  { id := "set-allequal-mapped", juliaFile := "base/set.jl",
    juliaFns := ["allequal(f, xs)"],
    statement := "Mapped allequal applies the function before checking that every generated value equals the first under isequal.",
    source := "allequal docstring and base/set.jl:662", status := .todo,
    prop := ``AllequalMapSpec },
  { id := "bitsetscov-allunique-idset", juliaFile := "base/set.jl",
    juliaFns := ["allunique(::Union{AbstractSet,AbstractDict})", "allequal(::Union{AbstractSet,AbstractDict})"],
    statement := "Set and dictionary predicate specializations agree with isequal-based distinctness and equality of their iterated values, including identity collections.",
    source := "allunique and allequal docstrings; base/set.jl:544,658", status := .todo,
    prop := ``AlluniqueSetSpec },
  { id := "bitsetscov-set-helpers", juliaFile := "base/set.jl",
    juliaFns := ["hash(::AbstractSet, ::UInt)", "check_count(::Integer)"],
    statement := "Set hashing is independent of iteration order, and replacement count validation rejects negative values and clamps nonnegative values to typemax(Int).",
    source := "base/set.jl:698-715", status := .todo, prop := ``SetHashCheckCountSpec },
  { id := "bitsetscov-set-replace", juliaFile := "base/set.jl",
    juliaFns := ["new", "_replace!(::Callable, ::AbstractArray, ::AbstractArray)", "_replace(f::Callable, t::Tuple, count::Int)", "_replace(t::Tuple, count::Int, old_new::Tuple{Vararg{Pair}})", "replace! and replace Pair/callable ambiguities"],
    statement := "Pair replacement uses the first matching pair, array and tuple replacement respect count and preserve shape, and ambiguous Pair/callable forms raise MethodError.",
    source := "replace and replace! docstrings; base/set.jl:762-1046", status := .todo,
    prop := ``SetReplaceSpec },
  { id := "set-replace-wrappers", juliaFile := "base/set.jl",
    juliaFns := ["replace!(A, old_new::Pair...)", "replace!(new, A)", "replace(A, old_new::Pair...)", "replace(new, A)", "replace(f::Callable, t::Tuple)", "replace(t::Tuple, old_new::Pair...)"],
    statement := "Negative replacement counts raise the documented DomainError through the public array, collection, and tuple wrappers.",
    source := "check_count docstring and base/set.jl:762-763,804-805,842-851,895-896,1032-1033,1045-1046", status := .todo,
    prop := ``SetReplaceWrappersSpec },
  { id := "dicts-replace-lossy-key", juliaFile := "base/set.jl",
    juliaFns := ["replace!(::Function, ::Dict)", "replace!(::Function, ::Set)"],
    statement := "When dictionary or Set replacement returns, every requested replacement key remains present in the resulting collection.",
    source := "replace! docstring base/set.jl:778; Dict key contract base/dict.jl:347-357", status := .todo,
    prop := ``ReplaceKeepsReplacements },
  { id := "bitsetscov-replace-generic-set", juliaFile := "base/set.jl",
    juliaFns := ["replace(::Callable, ::AbstractSet)", "_replace!(::Callable, ::AbstractSet, ::AbstractSet, ::Int)"],
    statement := "Replacing every original member of an AbstractSet with f(x) yields the set of mapped original members, with duplicates collapsed by isequal.",
    source := "replace docstring; base/set.jl:895-896,909-943", status := .todo,
    prop := ``ReplaceGenericSetSpec }
]

/-! Nothing to promise:
- `_Set@42`: wraps the supplied Dict value; copied and constructed membership is covered by Set properties.
- `Set(itr)@58`: selects the iterator-eltype constructor; the typed and unknown-eltype constructors cover members.
- `_Set(itr, ::HasEltype)@59`: selects the declared-eltype constructor; iterator construction covers its members.
- `_Set(itr, ::EltypeUnknown)@61`: selects growth or typed construction from eltype metadata; iterator construction covers its members.
- `Iterators.only(s::Set)@178`: forwards to the iterator library's `only` implementation.
- `_unique_from@243`: dispatches to `unique_from`, whose stable-first result is covered.
- `_unique!(A::AbstractVector)@411`: forwards identity mapping to mapped unique!.
- `unique!(itr)@470`: selects the grouped or general uniqueness algorithm covered by the uniqueness properties.
- `allequal(xs::Tuple)@693`: forwards to tuple allequal with identity mapping.
- `filter!(f, s::Set)@695`: forwards to the AbstractSet filter implementation.
- `convert(::Type{T}, s::T)@706`: returns the original set unchanged.
- `convert(::Type{T}, s::AbstractSet)@707`: delegates conversion to the requested set constructor.
- `_copy_oftype(x, ::Type{T})@718`: delegates allocation and copying to similar and copyto!.
- `_copy_oftype(x::AbstractDict, ::Type{Pair{K,V}})@720`: delegates to empty and merge!.
- `_copy_oftype(x::AbstractSet, ::Type{T})@721`: delegates to empty and union!.
- `_copy_oftype(x::AbstractArray{T}, ::Type{T})@723`: returns the same-type copy.
- `_copy_oftype(x::AbstractDict, ::Type{T})@724`: returns the same-type copy.
- `_copy_oftype(x::AbstractSet, ::Type{T})@725`: returns the same-type copy.
- `_similar_or_copy(x::Any)@727`: delegates allocation to similar.
- `_similar_or_copy(x::Any, ::Type{T})@728`: delegates typed allocation to similar.
- `_similar_or_copy(x::Union{AbstractDict,AbstractSet})@730`: delegates to copy.
- `_similar_or_copy(x::Union{AbstractDict,AbstractSet}, ::Type{T})@731`: delegates to `_copy_oftype`.
- `replace_pairs!(res,A,count,pairs)@765`: adapts the first-match callback to the selected container replacement method.
- `promote_valuetype(x::Pair)@853`: returns the Pair value type.
- `promote_valuetype(x::Pair, y::Pair...)@854`: delegates value-type promotion to promote_type.
- `subtract_singletontype(::Type{T}, x::Pair)@858`: selects the type split for a singleton key.
- `subtract_singletontype(::Type{T}, x::Pair, y::Pair...)@865`: applies singleton subtraction across Pair keys.
- `askey(k, ::AbstractDict)@906`: extracts the dictionary key from a Pair.
- `askey(k, ::AbstractSet)@907`: returns the set key unchanged.
-/

/-! Method -> property table:
_Set@42 -> Nothing to promise
Set{T}@45 -> bitsetscov-set-basic
Set{T}@46 -> bitsetscov-set-basic
Set{T}@47 -> set-iterator-constructor-membership
Set@48 -> bitsetscov-set-basic
Set{T}@50 -> bitsetscov-set-basic
Set@58 -> Nothing to promise
_Set@59 -> Nothing to promise
_Set@61 -> Nothing to promise
empty@67 -> bitsetscov-set-basic
emptymutable@71 -> bitsetscov-set-basic
_similar_for@73 -> bitsetscov-set-basic
show@75 -> bitsetscov-set-mutable
isempty@90 -> set-mutation-membership
length@91 -> set-mutation-membership
in@92 -> set-mutation-membership
in!@125 -> dicts-set-in-bang-convert
in!@129 -> dicts-set-in-bang-convert
push!@137 -> set-mutation-membership
pop!@139 -> set-pop-contract
pop!@151 -> set-pop-contract
pop!@159 -> set-pop-contract
delete!@164 -> set-mutation-membership
copy@166 -> set-mutation-membership
copymutable@168 -> set-mutation-membership
copymutable@170 -> set-mutation-membership
sizehint!@172 -> set-mutation-membership
empty!@173 -> set-mutation-membership
rehash!@174 -> set-mutation-membership
iterate@176 -> set-mutation-membership
Iterators.only@178 -> Nothing to promise
setdiff!@187 -> dicts-set-setdiff
unique@224 -> arrayops-unique
_unique_from@243 -> Nothing to promise
unique_from@244 -> arrayops-unique
unique@262 -> dicts-range-allunique-subulp
unique@301 -> bitsetscov-set-unique
_unique!@323 -> bitsetscov-set-unique
unique!@373 -> bitsetscov-set-unique
_unique!@388 -> bitsetscov-set-unique
_unique!@411 -> Nothing to promise
_groupedunique!@417 -> set-grouped-unique
unique!@470 -> Nothing to promise
allunique@515 -> set-allunique-generic
allunique@523 -> set-allunique-mapped
_hashed_allunique@525 -> set-allunique-generic
allunique@544 -> bitsetscov-allunique-idset
allunique@546 -> dicts-range-allunique-subulp
allunique@549 -> bitsetscov-set-predicates
allunique@553 -> bitsetscov-set-predicates
_indexed_allunique@579 -> set-allunique-generic
allunique@594 -> bitsetscov-set-predicates
allunique@601 -> bitsetscov-set-predicates
allunique@603 -> bitsetscov-set-predicates
allequal@648 -> arrayops-unique
allequal@658 -> bitsetscov-allunique-idset
allequal@660 -> dicts-range-allunique-subulp
allequal@662 -> set-allequal-mapped
_allequal_loop@664 -> set-allequal-tuple
allequal@672 -> set-allequal-tuple
allequal@692 -> set-allequal-tuple
allequal@693 -> Nothing to promise
filter!@695 -> Nothing to promise
hash@698 -> bitsetscov-set-helpers
convert@706 -> Nothing to promise
convert@707 -> Nothing to promise
check_count@712 -> bitsetscov-set-helpers
_copy_oftype@718 -> Nothing to promise
_copy_oftype@720 -> Nothing to promise
_copy_oftype@721 -> Nothing to promise
_copy_oftype@723 -> Nothing to promise
_copy_oftype@724 -> Nothing to promise
_copy_oftype@725 -> Nothing to promise
_similar_or_copy@727 -> Nothing to promise
_similar_or_copy@728 -> Nothing to promise
_similar_or_copy@730 -> Nothing to promise
_similar_or_copy@731 -> Nothing to promise
replace!@762 -> set-replace-wrappers
replace_pairs!@765 -> Nothing to promise
new@766 -> bitsetscov-set-replace
replace!@804 -> set-replace-wrappers
replace@842 -> set-replace-wrappers
promote_valuetype@853 -> Nothing to promise
promote_valuetype@854 -> Nothing to promise
subtract_singletontype@858 -> Nothing to promise
subtract_singletontype@865 -> Nothing to promise
replace@895 -> set-replace-wrappers
replace!@899 -> bitsetscov-set-replace
replace!@900 -> bitsetscov-set-replace
replace@901 -> bitsetscov-set-replace
replace@902 -> bitsetscov-set-replace
askey@906 -> Nothing to promise
askey@907 -> Nothing to promise
_replace!@909 -> bitsetscov-set-replace
_replace!@947 -> bitsetscov-set-replace
_replace!@980 -> dicts-replace-lossy-key
_replace!@1012 -> dicts-replace-lossy-key
_replace@1023 -> bitsetscov-set-replace
replace@1032 -> set-replace-wrappers
_replace@1035 -> bitsetscov-set-replace
replace@1045 -> set-replace-wrappers

-/

end JuliaLean.Proofs.base.set
