import JuliaLean.Proofs.base.set.collection_bugs
import JuliaLean.Proofs.base.set.collection_rows
import JuliaLean.base.set
import JuliaLean.base.int
import JuliaLean.base.dict
import JuliaLean.base.abstractarray
import JuliaLean.base.operators
import JuliaLean.base.bool
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

namespace Round2

open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- Independent occupied-slot observation: each slot is a byte, whose high bit marks
an occupied slot (base/dict.jl:65-75). This observes storage, not `only` or iteration. -/
def OnlyOccupiedSlots {K : Type} (s : SetModel K) : List Nat :=
  ((List.range s.dict.size).map (fun i => i + 1)).filter
    (fun i => decide (128 ≤ s.dict.slots i))

def OnlyStoredKeys {K : Type} (s : SetModel K) : List K :=
  (OnlyOccupiedSlots s).filterMap s.dict.keys

/-- Representation invariants of a live Set's backing Dict. The length and floor
fit Julia Int; count counts occupied slots; occupied slots have initialized keys;
idxfloor is a lower bound on occupied indices. No call or result is assumed.
Julia source: base/dict.jl:65-90,135-136,328-342,689-704
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def OnlyStorageValid {K : Type} (s : SetModel K) : Prop :=
  s.dict.size < 2 ^ 63 ∧
  0 < s.dict.idxfloor ∧ s.dict.idxfloor < 2 ^ 63 ∧
  s.dict.count = (OnlyOccupiedSlots s).length ∧
  (∀ i, 1 ≤ i → i ≤ s.dict.size → s.dict.slots i < 256) ∧
  (∀ i ∈ OnlyOccupiedSlots s,
    s.dict.idxfloor ≤ i ∧ ∃ key, s.dict.keys i = some key)

/-- Bridge the existing Set iteration and generic `first` mirrors. Iteration's
Dict error is preserved before entering `firstIterator`; after a successful
iteration its callback returns that observed result, so `firstIterator` can
produce only a value or its own Julia ArgumentError. The other ArrayError
constructors are unreachable in this composition. -/
def OnlyFirstBound {K : Type} (s : SetModel K) : Result K := do
  let next ← dictResult (setIterateMethod s none)
  match JuliaLean.base.abstractarray.firstIterator
      (fun (_ : SetModel K) => .ok next) s with
  | .ok key => .ok key
  | .error (.julia error) => .error (.julia error)
  | .error _ => .error (.assertion "unreachable firstIterator error")

/-- Concrete composition of the existing public Set-only mirror with the
existing `_only(...,first)`, length, integer inequality, and first/iterate models.
No callback or expected outcome is supplied by the property caller. -/
def OnlyBound {K : Type} (s : SetModel K) : Result K :=
  setOnlyMethod
    (fun receiver first =>
      JuliaLean.base.iterators.sourceMethod1673
        (fun x => .ok (setLengthMethod x))
        (fun n => .ok (JuliaLean.base.operators.notEqual
          JuliaLean.base.int.eqSame JuliaLean.base.bool.notBool n (JInt.lit .i64 1)))
        (fun b => .ok b)
        first (fun message => .error (.julia (.argumentError message))) receiver)
    OnlyFirstBound s

/-- `only` returns the unique stored Set key and throws ArgumentError for every
empty or multiple-element Set, independently of the backing table layout.
Julia source: base/set.jl:178; base/iterators.jl:1673-1678;
base/abstractarray.jl:474-478; base/dict.jl:717-723
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/iterators.jl:1630-1633; doc/src/base/iterators.md:24
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def OnlyStoredElement : Prop :=
  ∀ (K : Type) (s : SetModel K), OnlyStorageValid s →
    match OnlyStoredKeys s with
    | [key] => OnlyBound s = .ok key
    | _ => ∃ message, OnlyBound s = .error (.julia (.argumentError message))

end Round2

end JuliaLean.Proofs.base.set

/-! Completed targets and reusable partial lemmas for batch 4, group 14. -/


/-! ## SetEarly -/

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

theorem setKeyindexLoopCongr {K : Type} (eqKey : K → K → Bool) (query : K)
    (d e : JuliaLean.base.dict.DictState K Unit) (sh remaining index : Nat)
    (hs : d.size = e.size) (ht : d.slots = e.slots) (hk : d.keys = e.keys) :
    JuliaLean.base.dict.keyindexLoop eqKey query d sh remaining index =
      JuliaLean.base.dict.keyindexLoop eqKey query e sh remaining index := by
  induction remaining generalizing index with
  | zero => rfl
  | succ remaining ih =>
    simp only [JuliaLean.base.dict.keyindexLoop, JuliaLean.base.dict.isslotempty,
      hs, ht, hk, ih]
    rfl

theorem setLookupCongr {K : Type} (ops : DictRuntime K) (query : K)
    (d e : JuliaLean.base.dict.DictState K Unit)
    (hs : d.size = e.size) (ht : d.slots = e.slots) (hk : d.keys = e.keys)
    (hc : d.count = e.count) (hp : d.maxprobe = e.maxprobe) :
    setInMethod ops query (fromDict d) = setInMethod ops query (fromDict e) := by
  unfold setInMethod setIn dictResult JuliaLean.base.dict.haskey
  have hh : JuliaLean.base.dict.htKeyindex ops.hash ops.equal d query =
      JuliaLean.base.dict.htKeyindex ops.hash ops.equal e query := by
    simp only [JuliaLean.base.dict.htKeyindex, JuliaLean.base.dict.isempty, hs, hc, hp]
    split
    · rfl
    · split
      · rfl
      · congr 1
        funext pair
        exact setKeyindexLoopCongr ops.equal query d e pair.2 (e.maxprobe + 1) pair.1 hs ht hk
  simp only [fromDict, hh]

theorem setCopyEquals {K : Type} (ops : DictRuntime K) (s : SetModel K)
    (h : DictRuntimeCopyLawful ops) : setTypedCopy ops s = s := by
  rcases h with ⟨hslots, hkeys, hvals⟩
  have hs : ops.copySlots s.dict.size s.dict.slots = s.dict.slots := funext (hslots _ _)
  have hk : ops.copyKeys s.dict.size s.dict.keys = s.dict.keys := funext (hkeys _ _)
  have hv : ops.copyValues s.dict.size s.dict.vals = s.dict.vals := funext (hvals _ _)
  cases s with
  | mk d =>
    simp only [setTypedCopy, JuliaLean.base.dict.dictCopy, hs, hk, hv, fromDict]

theorem setEmptyMembership {K : Type} (ops : DictRuntime K) (x : K) :
    setInMethod ops x emptySet = .ok false := by
  rfl

theorem BitsetscovSetBasic_proven : JuliaLean.Proofs.base.set.SetConstructionSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · rfl
  · intro K ops s x hc
    change setInMethod ops x (setTypedCopy ops s) = _
    rw [setCopyEquals ops s hc]
  · intro K ops s x hc
    unfold setConstructorKeySet
    apply setLookupCongr ops x
    · rfl
    · exact funext (hc.1 _ _)
    · exact funext (hc.2.1 _ _)
    · rfl
    · rfl
  · intro S K s tag ops x
    exact ⟨setEmptyMembership ops x, setEmptyMembership ops x, setEmptyMembership ops x⟩

theorem BitsetscovSetMutable_proven : JuliaLean.Proofs.base.set.SetShowSpec := by
  intro K s log
  unfold setShowMethod setIsEmptyMethod
  cases setIsEmpty s <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, List.append_assoc] <;> rfl

/-- A successful iterator constructor inherits the supplied membership contract. -/
theorem setIteratorMembershipOnSuccess {K Q : Type} (ops : DictRuntime K)
    (convert : Q → DictResult K)
    (unionBang : SetModel K → List Q → Result (SetModel K)) (values : List Q)
    (out : SetModel K)
    (h : ∀ result key, unionBang emptySet values = .ok result →
      setInMethod ops key result = .ok (hasConvertedKey ops convert values key))
    (hs : setConstructorIterator unionBang values = .ok out) :
    ∀ key, setInMethod ops key out = .ok (hasConvertedKey ops convert values key) := by
  intro key
  exact h out key hs

/-- The abstract in! wrapper preserves the two branches specified by its contract. -/
theorem setAbstractInBangBranches {K S : Type} (contains : K → S → Result Bool)
    (push : S → K → Result S) (s s' : S) (x : K) (present : Bool)
    (hc : contains x s = .ok present)
    (hr : setInBangAbstractMethod contains push x s = .ok (present, s')) :
    (present = true → s' = s) ∧ (present = false → push s x = .ok s') := by
  cases present with
  | true =>
    simp only [setInBangAbstractMethod, hc, bind, Except.bind] at hr
    cases hr
    exact ⟨fun _ => rfl, Bool.noConfusion⟩
  | false =>
    simp only [setInBangAbstractMethod, hc, bind, Except.bind] at hr
    cases hp : push s x with
    | error e => simp only [hp] at hr; cases hr
    | ok out =>
      simp only [hp] at hr
      cases hr
      exact ⟨Bool.noConfusion, fun _ => rfl⟩


/-- The mutation contract's copy, empty, and length components hold without table layout assumptions. -/
theorem setMutationStructuralParts {K : Type} (ops : DictRuntime K) (s : SetModel K)
    (hc : DictRuntimeCopyLawful ops) :
    (∀ y, setInMethod ops y (setCopyMethod ops s) = setInMethod ops y s) ∧
    (∀ y, setInMethod ops y (setEmptyBangMethod ops s) = .ok false) ∧
    setLengthMethod s = JInt.wrap .i64 (Int.ofNat s.dict.count) := by
  refine ⟨?_, ?_, rfl⟩
  · intro y
    change setInMethod ops y (setTypedCopy ops s) = _
    rw [setCopyEquals ops s hc]
  · intro y
    rfl

/-- An absent lookup must have returned the negative index sentinel. -/
theorem setLookupNegativeOfNotMember {K : Type} (ops : DictRuntime K)
    (s : SetModel K) (x : K) (h : setInMethod ops x s = .ok false) :
    ∃ i : Int, JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict x = .ok i ∧ i < 0 := by
  unfold setInMethod setIn dictResult JuliaLean.base.dict.haskey at h
  cases hi : JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict x with
  | error e =>
    simp only [hi, bind, Except.bind, Except.mapError] at h
    cases h
  | ok i =>
    simp only [hi, bind, Except.bind, Except.mapError] at h
    have hf : decide (i ≥ 0) = false := Except.ok.inj h
    have hn := of_decide_eq_false hf
    exact ⟨i, rfl, by omega⟩

/-- All three absence/empty components of the pop contract. -/
theorem setPopAbsentAndEmpty {K : Type} (ops : DictRuntime K)
    (s : SetModel K) (x default : K) :
    (setInMethod ops x s = .ok false →
      setPopKeyMethod ops x s = .error (.dictionary .keyError)) ∧
    (setInMethod ops x s = .ok false →
      setPopDefaultMethod ops x default s = .ok (default, s)) ∧
    (setIsEmptyMethod s = true →
      setPopAnyMethod setIsEmptyMethod ops s =
        .error (.julia (.argumentError "set must be non-empty"))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨i, hi, hn⟩ := setLookupNegativeOfNotMember ops s x h
    have hl : i < 1 := by omega
    simp only [setPopKeyMethod, setPopKeyModel, hi, dictResult, Except.mapError,
      bind, Except.bind, hl, ite_true]
  · intro h
    obtain ⟨i, hi, hn⟩ := setLookupNegativeOfNotMember ops s x h
    have hl : ¬ i > 0 := by omega
    simp only [setPopDefaultMethod, setPopDefaultModel, hi, dictResult, Except.mapError,
      bind, Except.bind, hl, ite_false]
  · intro h
    simp only [setPopAnyMethod, setPopAnyModel, h, ite_true]

end JuliaLean.ChatGPT.Batch4.Group14


/-! ## SetMembershipWork -/

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- A successful nonnegative probing result identifies a matching stored key. -/
theorem setProbeFoundKey {K : Type} (eqKey : K → K → Bool) (query : K)
    (d : JuliaLean.base.dict.DictState K Unit) (sh remaining index : Nat) (i : Int)
    (h : JuliaLean.base.dict.keyindexLoop eqKey query d sh remaining index = .ok i)
    (hi : 0 ≤ i) :
    ∃ key, d.keys i.toNat = some key ∧ eqKey query key = true := by
  induction remaining generalizing index with
  | zero =>
    have he : (-1 : Int) = i := Except.ok.inj h
    omega
  | succ n ih =>
    simp only [JuliaLean.base.dict.keyindexLoop] at h
    split at h
    · have he : (-1 : Int) = i := Except.ok.inj h
      omega
    · split at h
      · cases hk : d.keys index with
        | none =>
          simp only [hk] at h
          cases h
        | some key =>
          simp only [hk] at h
          split at h
          next heq =>
            have he : (index : Int) = i := Except.ok.inj h
            subst i
            exact ⟨key, hk, heq⟩
          next heq => exact ih _ h
      · exact ih _ h

/-- Hash lookup preserves the witness supplied by the successful probing path. -/
theorem setLookupFoundKey {K : Type} (ops : DictRuntime K) (s : SetModel K)
    (query : K) (i : Int)
    (h : JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict query = .ok i)
    (hi : 0 ≤ i) :
    ∃ key, s.dict.keys i.toNat = some key ∧ ops.equal query key = true := by
  unfold JuliaLean.base.dict.htKeyindex at h
  split at h
  · have he : (-1 : Int) = i := Except.ok.inj h
    omega
  · dsimp only at h
    split at h
    · cases h
    · cases hh : JuliaLean.base.dict.hashindex ops.hash query
          (JInt.lit .i64 (Int.ofNat s.dict.size)) with
      | error e =>
        simp only [hh, bind, Except.bind] at h
        cases h
      | ok pair =>
        simp only [hh, bind, Except.bind] at h
        exact setProbeFoundKey ops.equal query s.dict pair.2 (s.dict.maxprobe + 1) pair.1 i h hi

/-- A successful keyed pop returns a key matching its query; symmetry gives the contract's direction. -/
theorem setPopReturnedMatches {K : Type} (ops : DictRuntime K) (s s' : SetModel K)
    (x key : K) (hs : ∀ a b, ops.equal a b = ops.equal b a)
    (hp : setPopKeyMethod ops x s = .ok (key, s')) : ops.equal key x = true := by
  unfold setPopKeyMethod setPopKeyModel at hp
  cases hh : JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict x with
  | error e =>
    simp only [hh, dictResult, Except.mapError, bind, Except.bind] at hp
    cases hp
  | ok i =>
    simp only [hh, dictResult, Except.mapError, bind, Except.bind] at hp
    split at hp
    · cases hp
    next hn =>
      have hi : 0 ≤ i := by omega
      obtain ⟨stored, hk, he⟩ := setLookupFoundKey ops s x i hh hi
      simp only [JuliaLean.base.dict.keyAt, hk] at hp
      have hp' := Except.ok.inj hp
      have hkey : stored = key := congrArg Prod.fst hp'
      subst key
      rw [hs]
      exact he

end JuliaLean.ChatGPT.Batch4.Group14


/-! ## SetDiffWork -/

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- The deletion loop preserves the exact membership effect of its individual deletions. -/
theorem setDeleteManyMembership {K : Type} (equal : K → K → Bool)
    (member : K → SetModel K → Bool)
    (delete : K → SetModel K → Result (SetModel K))
    (hdelete : ∀ key state result, delete key state = .ok result →
      ∀ query, member query result = (member query state && !equal query key))
    (keys : List K) (state result : SetModel K)
    (hr : setDeleteMany delete keys state = .ok result) (query : K) :
    member query result = (member query state && !(keys.any (equal query))) := by
  induction keys generalizing state with
  | nil =>
    cases hr
    simp only [List.any_nil, Bool.not_false, Bool.and_true]
  | cons key rest ih =>
    cases hd : delete key state with
    | error e =>
      simp only [setDeleteMany, hd, bind, Except.bind] at hr
      cases hr
    | ok next =>
      simp only [setDeleteMany, hd, bind, Except.bind] at hr
      rw [ih next hr, hdelete key state next hd query]
      simp only [List.any_cons]
      cases member query state <;> cases equal query key <;>
        cases rest.any (equal query) <;> rfl

/-- The filtering branch deletes exactly the scanned keys that belong to its second set. -/
theorem setDiffFilterMembership {K : Type} (equal : K → K → Bool)
    (member : K → SetModel K → Bool) (other : K → Bool)
    (contains : K → SetModel K → Result Bool)
    (delete : K → SetModel K → Result (SetModel K))
    (second : SetModel K)
    (hcontains : ∀ key, contains key second = .ok (other key))
    (hdelete : ∀ key state result, delete key state = .ok result →
      ∀ query, member query result = (member query state && !equal query key))
    (keys : List K) (state result : SetModel K)
    (hr : setDiffFilterLoop contains delete second keys state = .ok result) (query : K) :
    member query result =
      (member query state && !(keys.any (fun key => other key && equal query key))) := by
  induction keys generalizing state with
  | nil =>
    cases hr
    simp only [List.any_nil, Bool.not_false, Bool.and_true]
  | cons key rest ih =>
    cases hc : other key with
    | false =>
      simp only [setDiffFilterLoop, hcontains, hc, bind, Except.bind,
        Bool.false_eq_true, ite_false] at hr
      rw [ih state hr]
      simp only [List.any_cons, hc, Bool.false_and, Bool.false_or]
    | true =>
      simp only [setDiffFilterLoop, hcontains, hc, bind, Except.bind, ite_true] at hr
      cases hd : delete key state with
      | error e =>
        simp only [hd, bind, Except.bind] at hr
        cases hr
      | ok next =>
        simp only [hd, bind, Except.bind] at hr
        rw [ih next hr, hdelete key state next hd query]
        simp only [List.any_cons, hc, Bool.true_and]
        cases member query state <;> cases equal query key <;>
          cases rest.any (fun key => other key && equal query key) <;> rfl

end JuliaLean.ChatGPT.Batch4.Group14


/-! ## SetLater -/

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- The observed values of two distinct identity keys can be equal. -/
theorem BitsetscovAlluniqueIdset_refuted : ¬ JuliaLean.Proofs.base.set.AlluniqueSetSpec := by
  intro claim
  have h := (claim (List (List Nat)) (List Nat) id (fun x y => x == y) [[1], [1]]).1
  have bad : alluniqueSetMethod ([[1], [1]] : List (List Nat)) ≠
      listAllDistinctBy (fun (x y : List Nat) => x == y) [[1], [1]] := by decide
  exact bad h

/-- Observations of a two-element range at one quarter of the ULP at 1.0. -/
theorem DictsRangeAlluniqueSubulp_refuted : ¬ JuliaLean.Proofs.base.set.RangeUniqueSpec := by
  intro claim
  have h := (claim Unit Nat (fun _ => ()) (fun _ => false) (fun _ => 2)
    (fun _ => [1, 1]) (fun x y => x == y) (fun _ x => x) (fun _ => ()) () ()).1
  have bad : alluniqueRangeMethod (fun (_ : Unit) => false) (fun _ => ())
      (fun _ => 2) () ≠ listAllDistinctBy (fun (x y : Nat) => x == y) [1, 1] := by decide
  exact bad h

/-- The indexed branch implements the independent pairwise specification. -/
theorem indexedAlluniqueCorrect {K : Type} (equal : K → K → Bool)
    (trace : FiniteTrace K) :
    indexedAlluniqueMethod equal trace = .ok (listAllDistinctBy equal trace.values) := by
  unfold indexedAlluniqueMethod
  have h : ∀ xs : List K, indexedAlluniqueMethod.loop equal xs = listAllDistinctBy equal xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [indexedAlluniqueMethod.loop, listAllDistinctBy, ih]
  rw [h]

/-- Length metadata suffices to justify the generic equality shortcut. -/
theorem allequalGenericCorrect {K : Type} (equal : K → K → Bool)
    (trace : FiniteTrace K) (hLength : trace.hasLength = true → trace.length = trace.values.length) :
    allequalGeneric equal trace = .ok (listAllEqualBy equal trace.values) := by
  unfold allequalGeneric
  split
  next h =>
    have ht : trace.hasLength = true := (Bool.and_eq_true_iff.mp h).1
    have hl : trace.length ≤ 1 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    have hm := hLength ht
    cases hv : trace.values with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys => simp only [hv, List.length_cons] at hm; omega
  next h =>
    cases trace.values <;> rfl

/-- With coherent generated length metadata, mapped equality is correct. -/
theorem allequalMapCorrect {A K : Type} (equal : K → K → Bool) (values : FiniteTrace A)
    (generator : (A → K) → FiniteTrace A → FiniteTrace K) (f : A → K)
    (hLength : (generator f values).hasLength = true →
      (generator f values).length = (generator f values).values.length) :
    allequalMapMethod generator (allequalGeneric equal) f values =
      .ok (listAllEqualBy equal ((generator f values).values)) := by
  exact allequalGenericCorrect equal (generator f values) hLength

/-- The generated and loop tuple paths share the same total map semantics. -/
theorem tupleLoopChecksCorrect {A K : Type} (f : A → Jl K) (equal : K → K → Bool)
    (mapped : A → K) (hf : ∀ x, f x = .ok (mapped x)) (first : K) (xs : List A) :
    allequalLoopMethod.loop f equal first xs = .ok ((xs.map mapped).all (equal first)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [allequalLoopMethod.loop, hf, bind, Except.bind, List.map_cons, List.all_cons]
    cases equal first (mapped x) <;> simp only [Bool.false_eq_true, ite_false,
      Bool.false_and, ite_true, Bool.true_and, ih]

theorem tupleGeneratedChecksCorrect {A K : Type} (f : A → Jl K) (equal : K → K → Bool)
    (mapped : A → K) (hf : ∀ x, f x = .ok (mapped x)) (first : K) (xs : List A) :
    allequalTupleMethod.checks f equal first xs = .ok ((xs.map mapped).all (equal first)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [allequalTupleMethod.checks, hf, bind, Except.bind, List.map_cons, List.all_cons]
    cases equal first (mapped x) <;> simp only [Bool.false_eq_true, ite_false,
      Bool.false_and, ite_true, Bool.true_and, ih]

theorem SetAllequalTuple_proven : JuliaLean.Proofs.base.set.AllequalTupleSpec := by
  intro A K f equal values mapped hf
  constructor
  · unfold allequalTupleMethod
    simp only [ite_true]
    split
    · split
      · cases values with
        | nil => rfl
        | cons x xs =>
          cases xs with
          | nil => rfl
          | cons y ys => simp only [List.length_cons] at *; omega
      · cases values with
        | nil => rfl
        | cons x xs =>
          simp only [hf, bind, Except.bind]
          exact tupleGeneratedChecksCorrect f equal mapped hf (mapped x) xs
    · cases values with
      | nil => simp only [List.length_nil] at *; omega
      | cons x xs =>
        simp only [allequalLoopMethod, hf, bind, Except.bind]
        exact tupleLoopChecksCorrect f equal mapped hf (mapped x) xs
  · rfl

/-- Count validation clips positive counts to the signed-machine upper bound. -/
theorem checkCountCorrect : CheckCountSpec := by
  intro count
  unfold checkCountMethod checkCount
  split
  · rfl
  next h =>
    have hr : IntTy.min .i64 ≤ min count (IntTy.max .i64) ∧
        min count (IntTy.max .i64) ≤ IntTy.max .i64 := by
      change -9223372036854775808 ≤ min count 9223372036854775807 ∧
        min count 9223372036854775807 ≤ 9223372036854775807
      omega
    simp only [JInt.convert, dite_eq_left hr, JInt.wrap, wrapInt_of_inRange .i64 _ hr]

theorem SetReplaceWrappers_proven : JuliaLean.Proofs.base.set.SetReplaceWrappersSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A α pairs count replacePairs a hc
    simp only [replacePairsBangWrapper, checkCountMethod, checkCount, ite_eq_left hc,
      Except.mapError, bind, Except.bind]
  · intro A α new a count replaceInPlace hc
    simp only [replaceCallableBangWrapper, checkCountMethod, checkCount, ite_eq_left hc,
      Except.mapError, bind, Except.bind]
  · intro A B α new a count similarOrCopy replaceInPlace copy hc hcopy
    simp only [replaceCallableCopyWrapper, hcopy, checkCountMethod, checkCount, ite_eq_left hc,
      Except.mapError, bind, Except.bind]
  · intro A B P pairs count elementType promoteValues subtractSingletons promote
      similarOrCopy replacePairs a copy hc hcopy
    simp only [replacePairsCopyMethod, hcopy, checkCountMethod, checkCount, ite_eq_left hc,
      Except.mapError, bind, Except.bind]
  · intro α f same values count hc
    simp only [replaceTupleCallableMethod, checkCountMethod, checkCount, ite_eq_left hc,
      Except.mapError, bind, Except.bind]
  · intro α equal same values pairs count hc
    simp only [replaceTuplePairsWrapper, checkCountMethod, checkCount, ite_eq_left hc,
      Except.mapError, bind, Except.bind]

/-- Pair replacement chooses the first matching pair. -/
theorem pairReplacementCorrect {α : Type} (equal : α → α → Bool)
    (pairs : List (α × α)) (x : α) :
    replacePairsNewMethod equal pairs x = firstReplacement equal pairs x := by
  unfold replacePairsNewMethod
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    cases p
    simp only [replacePairsValue, firstReplacement, ih]

/-- Tuple replacement always preserves its length. -/
theorem tupleReplacementLength {α : Type} (new : α → Result α)
    (same : α → α → Bool) (values out : List α) (count : Nat)
    (h : replaceTupleMethod new same values count = .ok out) : out.length = values.length := by
  unfold replaceTupleMethod at h
  induction values generalizing out count with
  | nil =>
    simp only [replaceTupleMethod.loop] at h
    cases h
    rfl
  | cons x xs ih =>
    cases count with
    | zero =>
      simp only [replaceTupleMethod.loop] at h
      cases h
      rfl
    | succ n =>
      simp only [replaceTupleMethod.loop] at h
      cases hf : new x with
      | error e => simp only [hf, bind, Except.bind] at h; cases h
      | ok y =>
        simp only [hf, bind, Except.bind] at h
        cases ht : replaceTupleMethod.loop new same xs (n - if same y x then 0 else 1) with
        | error e => simp only [ht] at h; cases h
        | ok tail =>
          simp only [ht, pure, Except.pure] at h
          cases h
          simp only [List.length_cons, ih tail _ ht]


/-- The unsigned intrinsic conversion preserves all 64 bits. -/
theorem setU64ToValue (word : BitVec IntTy.u64.bits) :
    (JuliaLean.C.toJInt .u64 word).val = (word.toNat : Int) := by
  change wrapInt .u64 (word.toNat : Int) = (word.toNat : Int)
  apply wrapInt_of_inRange
  have h := word.isLt
  change word.toNat < 18446744073709551616 at h
  change 0 ≤ (word.toNat : Int) ∧ (word.toNat : Int) ≤ 18446744073709551615
  omega

theorem setU64FromValue (word : JInt .u64) :
    (JuliaLean.C.fromJInt word).toNat = word.val.toNat := by
  rw [JuliaLean.C.fromJInt, BitVec.toNat_ofInt]
  change (word.val % 18446744073709551616).toNat = word.val.toNat
  have h := word.property
  change 0 ≤ word.val ∧ word.val ≤ 18446744073709551615 at h
  rw [Int.emod_eq_of_lt h.1 (by omega)]

theorem setU64Roundtrip (word : BitVec IntTy.u64.bits) :
    JuliaLean.C.fromJInt (JuliaLean.C.toJInt .u64 word) = word := by
  apply BitVec.eq_of_toNat_eq
  rw [setU64FromValue, setU64ToValue, Int.toNat_natCast]

theorem setXorRightComm (a b c : JInt .u64) :
    JuliaLean.base.int.xor_int (JuliaLean.base.int.xor_int a b) c =
      JuliaLean.base.int.xor_int (JuliaLean.base.int.xor_int a c) b := by
  unfold JuliaLean.base.int.xor_int
  rw [setU64Roundtrip, setU64Roundtrip]
  unfold JuliaLean.C.jlXorInt
  rw [BitVec.xor_assoc, BitVec.xor_assoc, BitVec.xor_comm (JuliaLean.C.fromJInt b)]

theorem hashForInFold {K : Type} (hashKey : K → JInt .u64)
    (xs : List K) (acc : JInt .u64) :
    (forIn xs acc (fun x hv => pure (ForInStep.yield
      (JuliaLean.base.int.xor_int hv (hashKey x)))) : Result (JInt .u64)) =
        .ok (xs.foldl (fun hv x => JuliaLean.base.int.xor_int hv (hashKey x)) acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, pure, Except.pure, bind, Except.bind, List.foldl_cons]
    exact ih _

theorem setHashOrderCorrect : SetHashOrderIndependent := by
  intro K hashKey combine s seed xs ys hp
  unfold setHashMethod
  simp only [bind, Except.bind, hashForInFold]
  have hfold := hp.foldl_eq'
    (f := fun (hv : JInt .u64) (x : K) => JuliaLean.base.int.xor_int hv (hashKey x))
    (fun x _ y _ hv => setXorRightComm hv (hashKey x) (hashKey y))
    (JInt.lit .u64 0x852ada37cfe8e0ce)
  rw [hfold]

theorem BitsetscovSetHelpers_proven : JuliaLean.Proofs.base.set.SetHashCheckCountSpec :=
  ⟨setHashOrderCorrect, checkCountCorrect⟩


/-- The generic dispatcher is correct once length metadata and its hashed branch are justified. -/
theorem genericAlluniqueCorrect {K : Type} (equal : K → K → Bool)
    (trace : FiniteTrace K) (collect : FiniteTrace K → Result (FiniteTrace K))
    (hashed : FiniteTrace K → Result Bool)
    (hLength : trace.hasLength = true → trace.length = trace.values.length)
    (hCollect : collect trace = .ok trace)
    (hHash : hashed trace = .ok (listAllDistinctBy equal trace.values)) :
    alluniqueGeneric (fun t => t.hasLength) (fun t => t.length) collect
      (indexedAlluniqueMethod equal) hashed trace = .ok (listAllDistinctBy equal trace.values) := by
  unfold alluniqueGeneric
  split
  next h =>
    have hlen := hLength h
    split
    next hlt =>
      change trace.length < 2 at hlt
      cases hv : trace.values with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons y ys => simp only [hv, List.length_cons] at hlen; omega
    next hn =>
      split
      · simp only [hCollect, bind, Except.bind, indexedAlluniqueCorrect]
      · exact hHash
  next h => exact hHash

/-- Every direct tuple comparison, including short-circuit combinations, is correct. -/
theorem alluniqueTupleLoopCorrect {K : Type} (equal : K → K → Bool) (xs : List K) :
    alluniqueTupleMethod.loop equal xs = .ok (listAllDistinctBy equal xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [alluniqueTupleMethod.loop, ih, bind, Except.bind, listAllDistinctBy]

theorem alluniqueTupleCorrect {K : Type} (equal : K → K → Bool)
    (hashed : FiniteTrace K → Result Bool) (trace : FiniteTrace K)
    (hHash : hashed trace = .ok (listAllDistinctBy equal trace.values)) :
    alluniqueTupleMethod equal hashed trace = .ok (listAllDistinctBy equal trace.values) := by
  unfold alluniqueTupleMethod
  split
  · exact hHash
  · exact alluniqueTupleLoopCorrect equal trace.values

theorem alluniqueStringCorrect {K : Type} (equal : K → K → Bool)
    (hashed : FiniteTrace K → Result Bool) (trace : FiniteTrace K)
    (hHash : hashed trace = .ok (listAllDistinctBy equal trace.values)) :
    alluniqueStringMethod (fun t => t.values.length)
      (indexedAlluniqueMethod equal) hashed trace = .ok (listAllDistinctBy equal trace.values) := by
  unfold alluniqueStringMethod
  split
  · exact indexedAlluniqueCorrect equal trace
  · exact hHash

theorem alluniqueUnorderedStridedCorrect {K : Type} (equal less : K → K → Bool)
    (hashed : FiniteTrace K → Result Bool) (trace : FiniteTrace K)
    (hHash : hashed trace = .ok (listAllDistinctBy equal trace.values)) :
    alluniqueStridedMethod trace false equal less
      (indexedAlluniqueMethod equal) hashed = .ok (listAllDistinctBy equal trace.values) := by
  unfold alluniqueStridedMethod
  split
  · exact indexedAlluniqueCorrect equal trace
  · exact hHash

/-- Pair-based tuple replacement inherits the general length invariant. -/
theorem tuplePairReplacementLength {K : Type} (equal same : K → K → Bool)
    (values out : List K) (count : Nat) (pairs : List (K × K))
    (h : replaceTuplePairsMethod equal same values count pairs = .ok out) :
    out.length = values.length :=
  tupleReplacementLength (fun x => .ok (replacePairsValue equal pairs x))
    same values out count h

end JuliaLean.ChatGPT.Batch4.Group14


/-! ## SetOnly -/

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set
open JuliaLean.Proofs.base.set.Round2

/-- The independent occupied-slot description identifies exactly the byte's high bit. -/
theorem onlyOccupiedMem {K : Type} (s : SetModel K) (i : Nat) :
    i ∈ OnlyOccupiedSlots s ↔ 1 ≤ i ∧ i ≤ s.dict.size ∧ 128 ≤ s.dict.slots i := by
  simp only [OnlyOccupiedSlots, List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j, hj, heq⟩, hslot⟩
    omega
  · rintro ⟨hi, hn, hs⟩
    refine ⟨⟨i - 1, ?_, ?_⟩, hs⟩ <;> omega

set_option maxRecDepth 1000 in
theorem onlyByteHighBit (b : Nat) (hb : b < 256) :
    (Nat.land b 128 != 0) = decide (128 ≤ b) := by
  have h : ∀ x : Fin 256, (Nat.land x.val 128 != 0) = decide (128 ≤ x.val) := by decide
  exact h ⟨b, hb⟩

theorem onlySlotFilled {K : Type} (s : SetModel K) (hs : OnlyStorageValid s)
    (i : Nat) (hi : 1 ≤ i) (hn : i ≤ s.dict.size) :
    JuliaLean.base.dict.isslotfilled s.dict i = decide (128 ≤ s.dict.slots i) := by
  exact onlyByteHighBit _ (hs.2.2.2.2.1 i hi hn)

/-- The scanner reaches the first occupied slot in the given finite interval. -/
theorem onlyScanFirst {K V : Type} (d : JuliaLean.base.dict.DictState K V)
    (remaining start target : Nat)
    (hle : start ≤ target) (hlt : target < start + remaining)
    (hyes : JuliaLean.base.dict.isslotfilled d target = true)
    (hno : ∀ i, start ≤ i → i < target → JuliaLean.base.dict.isslotfilled d i = false) :
    JuliaLean.base.dict.skipDeleted.loop d remaining start = target := by
  induction remaining generalizing start with
  | zero => omega
  | succ n ih =>
    by_cases he : start = target
    · subst start
      simp only [JuliaLean.base.dict.skipDeleted.loop, hyes, ite_true]
    · have hlt' : start < target := by omega
      simp only [JuliaLean.base.dict.skipDeleted.loop, hno start (by omega) hlt',
        Bool.false_eq_true, ite_false]
      exact ih (start + 1) (by omega) (by omega) (fun i hi ht => hno i (by omega) ht)

/-- Initialized occupied keys preserve the slot count when observed as a list. -/
theorem onlyFilterMapLength {A B : Type} (f : A → Option B) (xs : List A)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : (xs.filterMap f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp only [List.mem_cons, true_or])
    simp only [List.filterMap_cons, hy, List.length_cons]
    exact congrArg Nat.succ (ih (fun a ha => h a (by simp only [List.mem_cons]; exact Or.inr ha)))

theorem onlyKeysLength {K : Type} (s : SetModel K) (hs : OnlyStorageValid s) :
    (OnlyStoredKeys s).length = s.dict.count := by
  rw [hs.2.2.2.1]
  exact onlyFilterMapLength s.dict.keys (OnlyOccupiedSlots s)
    (fun i hi => (hs.2.2.2.2.2 i hi).2)

theorem onlyCountBound {K : Type} (s : SetModel K) (hs : OnlyStorageValid s) :
    s.dict.count < 2 ^ 63 := by
  have hle : (OnlyOccupiedSlots s).length ≤ s.dict.size := by
    unfold OnlyOccupiedSlots
    calc
      _ ≤ ((List.range s.dict.size).map (fun i => i + 1)).length := List.length_filter_le _ _
      _ = s.dict.size := by simp only [List.length_map, List.length_range]
  rw [← hs.2.2.2.1] at hle
  exact Nat.lt_of_le_of_lt hle hs.1

theorem onlyLengthValue {K : Type} (s : SetModel K) (hn : s.dict.count < 2 ^ 63) :
    (setLengthMethod s).val = (s.dict.count : Int) := by
  change wrapInt .i64 (s.dict.count : Int) = (s.dict.count : Int)
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (s.dict.count : Int) ∧
    (s.dict.count : Int) ≤ 9223372036854775807
  omega

theorem onlyLengthEqOne {K : Type} (s : SetModel K) (hn : s.dict.count < 2 ^ 63) :
    JuliaLean.base.int.eqSame (setLengthMethod s) (JInt.lit .i64 1) =
      decide (s.dict.count = 1) := by
  unfold JuliaLean.base.int.eqSame JuliaLean.base.int.eq_int JuliaLean.C.jlEqInt
    JuliaLean.C.fromJInt
  rw [onlyLengthValue s hn]
  change ((BitVec.ofInt 64 (s.dict.count : Int)) == BitVec.ofInt 64 1) = decide (s.dict.count = 1)
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofInt] at he'
    have hc : (s.dict.count : Int) % 18446744073709551616 = (s.dict.count : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    change ((s.dict.count : Int) % 18446744073709551616).toNat = 1 at he'
    rw [hc, Int.toNat_natCast] at he'
    exact he'
  · intro he
    rw [he]
    rfl

theorem onlyBoolChoice {A : Type} (b : Bool) (yes no : Result A) :
    (if JuliaLean.base.bool.notBool b then no else yes) =
      if b then yes else no := by
  cases b <;> rfl

theorem onlyDispatch {I A : Type} (length : I → JInt .i64)
    (first : I → Result A) (receiver : I) :
    JuliaLean.base.iterators.sourceMethod1673
      (fun x => .ok (length x))
      (fun n => .ok (JuliaLean.base.operators.notEqual
        JuliaLean.base.int.eqSame JuliaLean.base.bool.notBool n (JInt.lit .i64 1)))
      (fun b => .ok b) first
      (fun message => .error (.julia (.argumentError message))) receiver =
    if JuliaLean.base.int.eqSame (length receiver) (JInt.lit .i64 1) then first receiver else
      .error (.julia (.argumentError "Collection must contain exactly 1 element")) := by
  simp only [JuliaLean.base.iterators.sourceMethod1673, bind, Except.bind,
    ite_true, JuliaLean.base.operators.notEqual]
  exact onlyBoolChoice _ _ _

theorem onlyBoundReduction {K : Type} (s : SetModel K) (hn : s.dict.count < 2 ^ 63) :
    OnlyBound s = if s.dict.count = 1 then OnlyFirstBound s else
      .error (.julia (.argumentError "Collection must contain exactly 1 element")) := by
  dsimp only [OnlyBound, setOnlyMethod]
  rw [onlyDispatch, onlyLengthEqOne s hn]
  simp only [decide_eq_true_eq]

/-- Every valid non-singleton is rejected without inspecting a key. -/
theorem onlyNonSingleton {K : Type} (s : SetModel K) (hs : OnlyStorageValid s)
    (hn : s.dict.count ≠ 1) :
    OnlyBound s = .error (.julia (.argumentError "Collection must contain exactly 1 element")) := by
  rw [onlyBoundReduction s (onlyCountBound s hs), ite_eq_right hn]

theorem onlySingleton {K : Type} (s : SetModel K) (hs : OnlyStorageValid s)
    (key : K) (hkeys : OnlyStoredKeys s = [key]) : OnlyBound s = .ok key := by
  have hcount : s.dict.count = 1 := by
    rw [← onlyKeysLength s hs, hkeys]
    rfl
  have hlength : (OnlyOccupiedSlots s).length = 1 := hs.2.2.2.1.symm.trans hcount
  obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hlength
  have hmem : i ∈ OnlyOccupiedSlots s := by
    rw [hi]
    exact List.mem_cons_self
  obtain ⟨hfloor, stored, hstored⟩ := hs.2.2.2.2.2 i hmem
  have hkey : s.dict.keys i = some key := by
    unfold OnlyStoredKeys at hkeys
    rw [hi, List.filterMap_cons, hstored, List.filterMap_nil] at hkeys
    have he : stored = key := (List.cons.inj hkeys).1
    rw [hstored, he]
  obtain ⟨hi0, hin, hhigh⟩ := (onlyOccupiedMem s i).mp hmem
  have hyes : JuliaLean.base.dict.isslotfilled s.dict i = true := by
    rw [onlySlotFilled s hs i hi0 hin]
    exact decide_eq_true hhigh
  have hno : ∀ j, s.dict.idxfloor ≤ j → j < i →
      JuliaLean.base.dict.isslotfilled s.dict j = false := by
    intro j hj hji
    apply Bool.eq_false_iff.mpr
    intro hjyes
    have hj0 : 1 ≤ j := by have hf := hs.2.1; omega
    have hjn : j ≤ s.dict.size := by omega
    rw [onlySlotFilled s hs j hj0 hjn, decide_eq_true_eq] at hjyes
    have hjmem := (onlyOccupiedMem s j).mpr ⟨hj0, hjn, hjyes⟩
    rw [hi, List.mem_singleton] at hjmem
    omega
  have hskip : JuliaLean.base.dict.skipDeleted s.dict s.dict.idxfloor = i := by
    unfold JuliaLean.base.dict.skipDeleted
    rw [ite_eq_right (show ¬s.dict.idxfloor > s.dict.size by omega)]
    exact onlyScanFirst s.dict (s.dict.size - s.dict.idxfloor + 1)
      s.dict.idxfloor i hfloor (by omega) hyes hno
  have hfzero : (s.dict.idxfloor == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    have hf := hs.2.1
    omega
  have hizero : (i == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    omega
  have hit : setIterateMethod s none =
      .ok (some (key, if i == 2 ^ 63 - 1 then 0 else i + 1)) := by
    simp only [setIterateMethod, setIterate, Option.getD_none,
      JuliaLean.base.dict.iteratePart, hfzero, hskip, hizero,
      Bool.false_eq_true, ite_false, JuliaLean.base.dict.partAt,
      JuliaLean.base.dict.keyAt, hkey, bind, Except.bind]
    rfl
  rw [onlyBoundReduction s (onlyCountBound s hs), ite_eq_left hcount]
  simp only [OnlyFirstBound, hit, dictResult, Except.mapError, bind, Except.bind,
    JuliaLean.base.abstractarray.firstIterator, pure, Except.pure]

/-- set-only-stored-element. -/
theorem SetOnlyStoredElement_proven : JuliaLean.Proofs.base.set.Round2.OnlyStoredElement := by
  intro K s hs
  have hlength := onlyKeysLength s hs
  cases hkeys : OnlyStoredKeys s with
  | nil =>
    refine ⟨"Collection must contain exactly 1 element", onlyNonSingleton s hs ?_⟩
    rw [hkeys] at hlength
    simp only [List.length_nil] at hlength
    omega
  | cons key rest =>
    cases rest with
    | nil => exact onlySingleton s hs key hkeys
    | cons next rest =>
      refine ⟨"Collection must contain exactly 1 element", onlyNonSingleton s hs ?_⟩
      rw [hkeys] at hlength
      simp only [List.length_cons] at hlength
      omega

end JuliaLean.ChatGPT.Batch4.Group14

namespace JuliaLean.Proofs.base.set

open JuliaLean.Registry

/-! ## Registry entries -/
def entries : List Entry := [
  { id := "bitsetscov-set-basic", juliaFile := "base/set.jl",
    juliaFns := ["Set{T}()", "Set{T}(s::Set{T})", "Set()", "Set{T}(s::KeySet)", "empty", "emptymutable", "_similar_for"],
    statement := "Set constructors preserve copied members, produce empty typed results, and initialize from iterator members with duplicate keys collapsed.",
    source := "Set constructors and source-body invariants; base/set.jl:42-73", status := .proven,
    prop := ``SetConstructionSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.BitsetscovSetBasic_proven },
  { id := "set-iterator-constructor-membership", juliaFile := "base/set.jl",
    juliaFns := ["Set{T}(itr)"],
    statement := "Constructing a Set from a finite iterator stores exactly its converted keys, with duplicates collapsed under isequal.",
    source := "Set constructor docstring and base/set.jl:47-65", status := .todo,
    prop := ``SetIteratorConstructionSpec, notes := "Frozen successful-construction conclusion lacks a callback-success premise." },
  { id := "bitsetscov-set-mutable", juliaFile := "base/set.jl",
    juliaFns := ["show(::IO,::Set)"],
    statement := "show renders an empty Set as Set() and surrounds non-empty members with Set(...).",
    source := "base/set.jl:75-88", status := .proven, prop := ``SetShowSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.BitsetscovSetMutable_proven },
  { id := "set-mutation-membership", juliaFile := "base/set.jl",
    juliaFns := ["push!", "in!", "delete!", "copy", "sizehint!", "empty!", "rehash!", "length", "iterate"],
    statement := "Successful Set mutations add or remove the requested key, preserve unrelated membership, and keep length and iteration consistent with stored keys.",
    source := "Set mutation docstrings and backing Dict invariants; base/set.jl:90-176", status := .todo,
    prop := ``SetMutationSpec, notes := "Frozen arbitrary storage and callbacks lack the invariants needed for the stated membership promises." },
  { id := "set-pop-contract", juliaFile := "base/set.jl",
    juliaFns := ["pop!(::Set, key, default)", "pop!(::Set, key)", "pop!(::Set)"],
    statement := "Keyed pop removes and returns a stored key, returns the default when absent, and throws the documented errors for missing and empty sets.",
    source := "base/set.jl:139-162", status := .todo, prop := ``SetPopBehavior, notes := "Frozen arbitrary storage lacks the invariant connecting count, occupancy and successful pop effects." },
  { id := "dicts-set-in-bang-convert", juliaFile := "base/set.jl",
    juliaFns := ["in!(x, s::Set)"],
    statement := "in! returns whether the converted key was already present and leaves the converted key present without removing previous members.",
    source := "in! docstring base/set.jl:94-100", status := .todo, prop := ``InBangEquiv, notes := "Frozen arbitrary storage and callbacks lack membership-preserving insertion laws." },
  { id := "dicts-set-setdiff", juliaFile := "base/set.jl",
    juliaFns := ["setdiff!(s::Set, t::Set)"],
    statement := "After setdiff!(s,t), a member is present exactly when it was in s and absent from t, in both size branches.",
    source := "setdiff! docstring base/abstractset.jl:225-243; base/set.jl:187-198", status := .todo,
    prop := ``SetSetdiffAgrees, notes := "Frozen arbitrary storage and callbacks lack the membership laws needed by both setdiff branches." },
  { id := "arrayops-unique", juliaFile := "base/set.jl",
    juliaFns := ["unique(itr)", "_unique_from", "unique_from", "allunique(A::StridedArray)", "_indexed_allunique", "_hashed_allunique", "allequal(itr)"],
    statement := "unique retains the first value of each isequal class in order; allunique and allequal agree with pairwise isequal over the iterated values, including the strided-array fast path.",
    source := "unique, allunique and allequal docstrings; base/set.jl:200-260, 553-592, 648-656", status := .todo,
    prop := ``ArrayUniqueSpec, notes := "Frozen widening appends a present key and leaves ordered-scan equality unrelated to backend equality." },
  { id := "bitsetscov-set-unique", juliaFile := "base/set.jl",
    juliaFns := ["unique(f, C)", "_unique!(f, out::AbstractVector, C, seen, i)", "unique!(f, A::AbstractVector)", "_unique!(f, A::AbstractVector, seen, current, i)"],
    statement := "Mapped unique and unique! retain the first source value for each mapped isequal class in source order.",
    source := "unique and unique! docstrings; base/set.jl:301-434", status := .todo,
    prop := ``SetUniqueSpec, notes := "Frozen mapped wrapper resumes an already-consumed tail at state one; retained helpers only prove the tail with its actual state." },
  { id := "dicts-range-allunique-subulp", juliaFile := "base/set.jl",
    juliaFns := ["unique(::AbstractRange)", "allunique(::AbstractRange)", "allequal(::AbstractRange)"],
    statement := "For finite ranges, allunique and allequal agree with isequal over the elements, and unique returns the original range or its first-element singleton.",
    source := "allunique, allequal and unique range methods; base/set.jl:262,546,660", status := .refuted,
    prop := ``RangeUniqueSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.DictsRangeAlluniqueSubulp_refuted,
    issue := "related JuliaLang/julia#36849 (closed), #36850 (merged); no exact duplicate found" },
  { id := "bitsetscov-set-predicates", juliaFile := "base/set.jl",
    juliaFns := ["allunique(s::AbstractString)", "allunique(A::StridedArray)", "allunique(t::Tuple)", "allunique(f::F,t::Tuple)"],
    statement := "String, strided-array, and tuple allunique specializations agree with isequal-based distinctness, including their fast-path cutoffs.",
    source := "allunique string, strided-array, and tuple methods; base/set.jl:549-607", status := .todo,
    prop := ``SetPredicateSpec, notes := "Frozen dictionary callbacks lack the storage/insertion invariants required for set predicate correctness." },
  { id := "set-allunique-generic", juliaFile := "base/set.jl",
    juliaFns := ["allunique(C)", "_hashed_allunique(C)", "_indexed_allunique(A)"],
    statement := "Generic allunique returns true exactly when no two iterated values are isequal, regardless of the length-based algorithm branch.",
    source := "allunique docstring and base/set.jl:515-542,579-592", status := .todo,
    prop := ``AlluniqueGenericSpec, notes := "Frozen metadata and runtime premises do not establish honest length shortcuts or dictionary insertion invariants." },
  { id := "set-allunique-mapped", juliaFile := "base/set.jl",
    juliaFns := ["allunique(f, xs)"],
    statement := "Mapped allunique tests the generated values for pairwise isequal distinctness.",
    source := "allunique docstring and base/set.jl:523", status := .todo,
    prop := ``AlluniqueMappedSpec, notes := "Frozen mapped-value fidelity does not imply insertion, resize, collection and length laws." },
  { id := "set-allequal-tuple", juliaFile := "base/set.jl",
    juliaFns := ["_allequal_loop", "allequal(f, xs::Tuple)", "allequal(f, ::Tuple{})"],
    statement := "Tuple allequal returns true exactly when all successful mapped elements are isequal to the first, including the empty tuple.",
    source := "allequal docstring and base/set.jl:664-690,692", status := .proven,
    prop := ``AllequalTupleSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.SetAllequalTuple_proven },
  { id := "set-allequal-mapped", juliaFile := "base/set.jl",
    juliaFns := ["allequal(f, xs)"],
    statement := "Mapped allequal applies the function before checking that every generated value equals the first under isequal.",
    source := "allequal docstring and base/set.jl:662", status := .todo,
    prop := ``AllequalMapSpec, notes := "Frozen generator metadata is not constrained by the length shortcut condition required for correctness." },
  { id := "bitsetscov-allunique-idset", juliaFile := "base/set.jl",
    juliaFns := ["allunique(::Union{AbstractSet,AbstractDict})", "allequal(::Union{AbstractSet,AbstractDict})"],
    statement := "Set and dictionary predicate specializations agree with isequal-based distinctness and equality of their iterated values, including identity collections.",
    source := "allunique and allequal docstrings; base/set.jl:544,658", status := .refuted,
    prop := ``AlluniqueSetSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.BitsetscovAlluniqueIdset_refuted,
    issue := "fixed upstream by JuliaLang/julia#64432 (merged); related #61893 (open)" },
  { id := "bitsetscov-set-helpers", juliaFile := "base/set.jl",
    juliaFns := ["hash(::AbstractSet, ::UInt)", "check_count(::Integer)"],
    statement := "Set hashing is independent of iteration order, and replacement count validation rejects negative values and clamps nonnegative values to typemax(Int).",
    source := "base/set.jl:698-715", status := .proven, prop := ``SetHashCheckCountSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.BitsetscovSetHelpers_proven },
  { id := "bitsetscov-set-replace", juliaFile := "base/set.jl",
    juliaFns := ["new", "_replace!(::Callable, ::AbstractArray, ::AbstractArray)", "_replace(f::Callable, t::Tuple, count::Int)", "_replace(t::Tuple, count::Int, old_new::Tuple{Vararg{Pair}})", "replace! and replace Pair/callable ambiguities"],
    statement := "Pair replacement uses the first matching pair, array and tuple replacement respect count and preserve shape, and ambiguous Pair/callable forms raise MethodError.",
    source := "replace and replace! docstrings; base/set.jl:762-1046", status := .todo,
    prop := ``SetReplaceSpec, notes := "Frozen traversal lacks equal source/destination origins and reflexive identity required for its change budget." },
  { id := "set-replace-wrappers", juliaFile := "base/set.jl",
    juliaFns := ["replace!(A, old_new::Pair...)", "replace!(new, A)", "replace(A, old_new::Pair...)", "replace(new, A)", "replace(f::Callable, t::Tuple)", "replace(t::Tuple, old_new::Pair...)"],
    statement := "Negative replacement counts raise the documented DomainError through the public array, collection, and tuple wrappers.",
    source := "check_count docstring and base/set.jl:762-763,804-805,842-851,895-896,1032-1033,1045-1046", status := .proven,
    prop := ``SetReplaceWrappersSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.SetReplaceWrappers_proven },
  { id := "dicts-replace-lossy-key", juliaFile := "base/set.jl",
    juliaFns := ["replace!(::Function, ::Dict)", "replace!(::Function, ::Set)"],
    statement := "When dictionary or Set replacement returns, every requested replacement key remains present in the resulting collection.",
    source := "replace! docstring base/set.jl:778; Dict key contract base/dict.jl:347-357", status := .todo,
    prop := ``ReplaceKeepsReplacements, notes := "Frozen homogeneous callback target demands the full replacement image even when the processing budget is zero." },
  { id := "bitsetscov-replace-generic-set", juliaFile := "base/set.jl",
    juliaFns := ["replace(::Callable, ::AbstractSet)", "_replace!(::Callable, ::AbstractSet, ::AbstractSet, ::Int)"],
    statement := "Replacing every original member of an AbstractSet with f(x) yields the set of mapped original members, with duplicates collapsed by isequal.",
    source := "replace docstring; base/set.jl:895-896,909-943", status := .todo,
    prop := ``ReplaceGenericSetSpec, notes := "Frozen callbacks lack faithful snapshots and membership-preserving pop/push laws." },
  { id := "set-only-stored-element", juliaFile := "base/set.jl",
    juliaFns := ["only(::Set)"],
    statement := "only returns the sole stored key of a Set and throws ArgumentError for an empty or multi-element Set, independently of the backing table layout.",
    source := "base/set.jl:178; base/iterators.jl:1673-1678; base/abstractarray.jl:474-478; base/dict.jl:717-723", status := .proven,
    prop := ``Round2.OnlyStoredElement, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.SetOnlyStoredElement_proven }
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

namespace JuliaLean.ChatGPT.Batch8.Group1
open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- The constructor's missing obligation is exactly successful termination of its callback. -/
theorem setIteratorContractIffSuccess {K Q : Type} (ops : DictRuntime K)
    (convert : Q → DictResult K)
    (unionBang : SetModel K → List Q → Result (SetModel K)) (values : List Q)
    (hm : ∀ out key, unionBang emptySet values = .ok out →
      setInMethod ops key out = .ok (hasConvertedKey ops convert values key)) :
    (match setConstructorIterator unionBang values with
    | .error _ => False
    | .ok out => ∀ key, setInMethod ops key out = .ok (hasConvertedKey ops convert values key)) ↔
      ∃ out, unionBang emptySet values = .ok out := by
  unfold setConstructorIterator
  cases h : unionBang emptySet values with
  | error error =>
    constructor
    · intro hf
      exact False.elim hf
    · rintro ⟨out, ho⟩
      cases ho
  | ok out =>
    constructor
    · intro _
      exact ⟨out, rfl⟩
    · intro _ key
      exact hm out key h

/-- Failure of conversion is returned unchanged by concrete in!. -/
theorem setInBangConversionError {K Q : Type} (ops : DictRuntime K)
    (convert : Q → DictResult K) (x : Q) (s : SetModel K) (error : DictError)
    (h : convert x = .error error) :
    setInBangMethod ops convert x s = .error (.dictionary error) := by
  simp only [setInBangMethod, setInBang, h, dictResult, Except.mapError, bind, Except.bind]

/-- A zero stored count makes lookup empty independently of the backing callbacks. -/
theorem setZeroCountMembership {K : Type} (ops : DictRuntime K) (s : SetModel K)
    (hc : s.dict.count = 0) (query : K) : setInMethod ops query s = .ok false := by
  simp only [setInMethod, setIn, dictResult, JuliaLean.base.dict.haskey,
    JuliaLean.base.dict.htKeyindex, JuliaLean.base.dict.isempty, hc,
    Except.mapError, bind, Except.bind]
  rfl

/-- Deleting an absent key preserves the entire modeled set, not just membership. -/
theorem setDeleteAbsentIdentity {K : Type} (ops : DictRuntime K) (s : SetModel K)
    (query : K) (h : setInMethod ops query s = .ok false) :
    setDeleteMethod ops query s = .ok s := by
  obtain ⟨i, hi, hn⟩ := JuliaLean.ChatGPT.Batch4.Group14.setLookupNegativeOfNotMember ops s query h
  have hnot : ¬ i > 0 := by omega
  simp only [setDeleteMethod, setDelete, JuliaLean.base.dict.deleteKey, hi, hnot,
    ite_false, dictResult, Except.mapError, bind, Except.bind, Functor.map, Except.map]
  cases s
  rfl

/-- Successful keyed pop exposes the exact stored slot and deletion effect. -/
theorem setPopKeyExactEffect {K : Type} (ops : DictRuntime K) (s out : SetModel K)
    (query key : K) (h : setPopKeyMethod ops query s = .ok (key, out)) :
    ∃ i : Int,
      JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict query = .ok i ∧
      0 < i ∧ s.dict.keys i.toNat = some key ∧ ops.equal query key = true ∧
      out = fromDict (JuliaLean.base.dict.deleteAt ops.unsetKey ops.unsetValue s.dict i.toNat) := by
  unfold setPopKeyMethod setPopKeyModel at h
  cases hi : JuliaLean.base.dict.htKeyindex ops.hash ops.equal s.dict query with
  | error error =>
    simp only [hi, dictResult, Except.mapError, bind, Except.bind] at h
    cases h
  | ok i =>
    simp only [hi, dictResult, Except.mapError, bind, Except.bind] at h
    split at h
    · cases h
    next hp =>
      have hpos : 0 < i := by omega
      obtain ⟨stored, hk, heq⟩ := JuliaLean.ChatGPT.Batch4.Group14.setLookupFoundKey ops s query i hi (by omega)
      simp only [JuliaLean.base.dict.keyAt, hk] at h
      have hout := Except.ok.inj h
      have hkey : stored = key := congrArg Prod.fst hout
      subst key
      refine ⟨i, rfl, hpos, hk, heq, ?_⟩
      exact (congrArg Prod.snd hout).symm

/-- Successful keyed pop always decrements the modeled count by one. -/
theorem setPopKeyCount {K : Type} (ops : DictRuntime K) (s out : SetModel K)
    (query key : K) (h : setPopKeyMethod ops query s = .ok (key, out)) :
    out.dict.count = s.dict.count - 1 := by
  obtain ⟨i, _, _, _, _, he⟩ := setPopKeyExactEffect ops s out query key h
  rw [he]
  rfl

/-- For a singleton count, successful pop leaves every membership query false. -/
theorem setPopSingletonEmpty {K : Type} (ops : DictRuntime K) (s out : SetModel K)
    (query key : K) (hc : s.dict.count = 1)
    (h : setPopKeyMethod ops query s = .ok (key, out)) :
    ops.equal query key = true ∧ ∀ y, setInMethod ops y out = .ok false := by
  obtain ⟨i, _, _, _, heq, _⟩ := setPopKeyExactEffect ops s out query key h
  refine ⟨heq, ?_⟩
  have hout : out.dict.count = 0 := by rw [setPopKeyCount ops s out query key h, hc]
  exact setZeroCountMembership ops out hout


/-- Pop cannot return a key from a zero-count table. -/
theorem setPopKeyPositiveCount {K : Type} (ops : DictRuntime K) (s out : SetModel K)
    (query key : K) (h : setPopKeyMethod ops query s = .ok (key, out)) :
    0 < s.dict.count := by
  obtain ⟨i, hi, hpos, _, _, _⟩ := setPopKeyExactEffect ops s out query key h
  by_cases hc : s.dict.count = 0
  · have hempty : JuliaLean.base.dict.isempty s.dict = true := by
      simp only [JuliaLean.base.dict.isempty, hc]
      rfl
    simp only [JuliaLean.base.dict.htKeyindex, hempty, ite_true] at hi
    have he : (-1 : Int) = i := Except.ok.inj hi
    omega
  · omega

/-- All four pop clauses hold when the starting count is at most one and comparison is symmetric. -/
theorem setPopSmallCountContract {K : Type} (ops : DictRuntime K) (s out : SetModel K)
    (query default key : K) (hc : s.dict.count ≤ 1)
    (hsym : ∀ a b, ops.equal a b = ops.equal b a) :
    (setInMethod ops query s = .ok true →
      setPopKeyMethod ops query s = .ok (key, out) →
        ops.equal key query = true ∧ setInMethod ops key out = .ok false) ∧
    (setInMethod ops query s = .ok false →
      setPopKeyMethod ops query s = .error (.dictionary .keyError)) ∧
    (setInMethod ops query s = .ok false →
      setPopDefaultMethod ops query default s = .ok (default, s)) ∧
    (setIsEmptyMethod s = true →
      setPopAnyMethod setIsEmptyMethod ops s =
        .error (.julia (.argumentError "set must be non-empty"))) := by
  refine ⟨?_, JuliaLean.ChatGPT.Batch4.Group14.setPopAbsentAndEmpty ops s query default⟩
  intro _ hp
  have hpos := setPopKeyPositiveCount ops s out query key hp
  have hone : s.dict.count = 1 := by omega
  obtain ⟨heq, hmem⟩ := setPopSingletonEmpty ops s out query key hone hp
  rw [hsym] at heq
  exact ⟨heq, hmem key⟩

end JuliaLean.ChatGPT.Batch8.Group1

namespace JuliaLean.ChatGPT.Batch8.Group2.UniqueSupport

open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- The retained source values describe the keys currently represented by a set. -/
def MappedSeen {A K : Type} (equal : K → K → Bool) (f : A → K)
    (contains : K → SetModel K → Result Bool) (seen : SetModel K)
    (kept : List A) : Prop :=
  ∀ key, contains key seen = .ok (kept.any (fun x => equal key (f x)))

def mappedStep {A K : Type} (equal : K → K → Bool) (f : A → K)
    (kept : List A) (x : A) : List A :=
  if kept.any (fun y => equal (f x) (f y)) then kept else kept ++ [x]

/-- A direct invariant for the source-mirrored mapped tail, including type widening.
No correctness of the complete tail is assumed. -/
theorem mappedTailLoopFromStorage {A K : Type} (equal : K → K → Bool)
    (f : A → K) (types : TypeOps K)
    (contains : K → SetModel K → Result Bool)
    (insert : K → SetModel K → Result (SetModel K))
    (push : VectorModel A → A → Result (VectorModel A))
    (hpush : ∀ out x, ∃ out', push out x = .ok out' ∧ out'.values = out.values ++ [x])
    (hinsert : ∀ seen kept x, MappedSeen equal f contains seen kept →
      kept.any (fun y => equal (f x) (f y)) = false →
      ∃ seen', insert (f x) seen = .ok seen' ∧
        MappedSeen equal f contains seen' (kept ++ [x]))
    (hconvert : ∀ tag seen kept, MappedSeen equal f contains seen kept →
      ∃ seen', types.convertSet tag seen = .ok seen' ∧
        MappedSeen equal f contains seen' kept)
    (xs : List A) (out : VectorModel A) (seen : SetModel K) (tag : Nat)
    (hseen : MappedSeen equal f contains seen out.values) :
    ∃ result,
      uniqueMapTail.loop types contains insert push f xs out seen tag = .ok result ∧
      result.values = xs.foldl (mappedStep equal f) out.values := by
  induction xs generalizing out seen tag with
  | nil => exact ⟨out, rfl, rfl⟩
  | cons x xs ih =>
    have hc := hseen (f x)
    cases hp : out.values.any (fun y => equal (f x) (f y)) with
    | true =>
      obtain ⟨result, hr, hv⟩ := ih out seen tag hseen
      refine ⟨result, ?_, ?_⟩
      · simp only [uniqueMapTail.loop, hc, hp, bind, Except.bind, ite_true, hr]
      · simpa only [List.foldl_cons, mappedStep, hp, ite_true] using hv
    | false =>
      obtain ⟨out', ho, hov⟩ := hpush out x
      cases ht : types.subtype (types.typeof (f x)) tag with
      | true =>
        obtain ⟨seen', hs, hsr⟩ := hinsert seen out.values x hseen hp
        have hsr' : MappedSeen equal f contains seen' out'.values := by
          simpa only [hov] using hsr
        obtain ⟨result, hr, hv⟩ := ih out' seen' tag hsr'
        refine ⟨result, ?_, ?_⟩
        · simp only [uniqueMapTail.loop, hc, hp, ho, ht, hs, bind, Except.bind,
            Bool.false_eq_true, ite_false, ite_true, hr]
        · simpa only [List.foldl_cons, mappedStep, hp, Bool.false_eq_true,
            ite_false, hov] using hv
      | false =>
        obtain ⟨converted, hconv, hcr⟩ :=
          hconvert (types.typejoin (types.typeof (f x)) tag) seen out.values hseen
        obtain ⟨seen', hs, hsr⟩ := hinsert converted out.values x hcr hp
        have hsr' : MappedSeen equal f contains seen' out'.values := by
          simpa only [hov] using hsr
        obtain ⟨result, hr, hv⟩ :=
          ih out' seen' (types.typejoin (types.typeof (f x)) tag) hsr'
        refine ⟨result, ?_, ?_⟩
        · simp only [uniqueMapTail.loop, hc, hp, ho, ht, hconv, hs, bind, Except.bind,
            Bool.false_eq_true, ite_false, hr]
        · simpa only [List.foldl_cons, mappedStep, hp, Bool.false_eq_true,
            ite_false, hov] using hv

/-- The state argument counts consumed elements in the original list. -/
theorem mappedTailFromStorage {A K : Type} (equal : K → K → Bool)
    (f : A → K) (types : TypeOps K)
    (contains : K → SetModel K → Result Bool)
    (insert : K → SetModel K → Result (SetModel K))
    (push : VectorModel A → A → Result (VectorModel A))
    (hpush : ∀ out x, ∃ out', push out x = .ok out' ∧ out'.values = out.values ++ [x])
    (hinsert : ∀ seen kept x, MappedSeen equal f contains seen kept →
      kept.any (fun y => equal (f x) (f y)) = false →
      ∃ seen', insert (f x) seen = .ok seen' ∧
        MappedSeen equal f contains seen' (kept ++ [x]))
    (hconvert : ∀ tag seen kept, MappedSeen equal f contains seen kept →
      ∃ seen', types.convertSet tag seen = .ok seen' ∧
        MappedSeen equal f contains seen' kept)
    (values : List A) (state : Nat) (out : VectorModel A) (seen : SetModel K) (tag : Nat)
    (hseen : MappedSeen equal f contains seen out.values) :
    ∃ result, uniqueMapTail types contains insert push f out values seen state tag = .ok result ∧
      result.values = (values.drop state).foldl (mappedStep equal f) out.values := by
  exact mappedTailLoopFromStorage equal f types contains insert push hpush hinsert hconvert
    (values.drop state) out seen tag hseen


/-- The ordinary unique loop needs a total insertion step, not just equality/hash laws. -/
theorem uniqueListFromStepContract {A : Type} (equal : A → A → Bool)
    (inBang : A → SetModel A → Result (Bool × SetModel A))
    (push : VectorModel A → A → Result (VectorModel A))
    (Rep : SetModel A → List A → Prop)
    (hstep : ∀ seen kept x, Rep seen kept → ∃ seen',
      inBang x seen = .ok (kept.any (equal x), seen') ∧
      Rep seen' (if kept.any (equal x) then kept else kept ++ [x]))
    (hpush : ∀ out x, ∃ out', push out x = .ok out' ∧ out'.values = out.values ++ [x])
    (values : List A) (out : VectorModel A) (seen : SetModel A)
    (hrep : Rep seen out.values) :
    ∃ result, uniqueListLoop inBang push values out seen = .ok result ∧
      result.values = values.foldl
        (fun kept x => if kept.any (equal x) then kept else kept ++ [x]) out.values := by
  induction values generalizing out seen with
  | nil => exact ⟨out, rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨seen', hs, hsr⟩ := hstep seen out.values x hrep
    cases hp : out.values.any (equal x) with
    | true =>
      have hsr' : Rep seen' out.values := by simpa only [hp, ite_true] using hsr
      obtain ⟨result, hr, hv⟩ := ih out seen' hsr'
      refine ⟨result, ?_, ?_⟩
      · simp only [uniqueListLoop, hs, hp, bind, Except.bind, ite_true, hr]
      · simpa only [List.foldl_cons, hp, ite_true] using hv
    | false =>
      obtain ⟨out', ho, hov⟩ := hpush out x
      have hsr' : Rep seen' out'.values := by
        simpa only [hp, Bool.false_eq_true, ite_false, hov] using hsr
      obtain ⟨result, hr, hv⟩ := ih out' seen' hsr'
      refine ⟨result, ?_, ?_⟩
      · simp only [uniqueListLoop, hs, hp, ho, bind, Except.bind,
          Bool.false_eq_true, ite_false, hr]
      · simpa only [List.foldl_cons, hp, Bool.false_eq_true, ite_false, hov] using hv

/-- The complete known-element-type branch follows from the individual loop contracts. -/
theorem uniqueKnownEltypeFromStorage {A : Type} (equal : A → A → Bool)
    (types : TypeOps A) (trace : FiniteTrace A)
    (empty : Nat → VectorModel A) (singleton : Nat → A → VectorModel A)
    (newSet : Nat → SetModel A)
    (insert : A → SetModel A → Result (SetModel A))
    (inBang : A → SetModel A → Result (Bool × SetModel A))
    (push : VectorModel A → A → Result (VectorModel A))
    (resume : FiniteTrace A → VectorModel A → SetModel A → Nat → Result (VectorModel A))
    (Rep : SetModel A → List A → Prop)
    (hstep : ∀ seen kept x, Rep seen kept → ∃ seen',
      inBang x seen = .ok (kept.any (equal x), seen') ∧
      Rep seen' (if kept.any (equal x) then kept else kept ++ [x]))
    (hpush : ∀ out x, ∃ out', push out x = .ok out' ∧ out'.values = out.values ++ [x])
    (hempty : (empty trace.eltype).values = [])
    (hset : Rep (newSet trace.eltype) []) (htype : trace.hasEltype = true) :
    ∃ result, uniqueMethod trace types empty singleton newSet insert inBang push resume =
      .ok result ∧ result.values = stableNubBy equal trace.values := by
  have hrep : Rep (newSet trace.eltype) (empty trace.eltype).values := by
    simpa only [hempty] using hset
  obtain ⟨result, hr, hv⟩ := uniqueListFromStepContract equal inBang push Rep hstep hpush
    trace.values (empty trace.eltype) (newSet trace.eltype) hrep
  refine ⟨result, ?_, ?_⟩
  · simpa only [uniqueMethod, htype, ite_true] using hr
  · simpa only [stableNubBy, hempty] using hv

end JuliaLean.ChatGPT.Batch8.Group2.UniqueSupport

namespace JuliaLean.ChatGPT.Batch8.Group2.Predicates

open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- Exactly the assumption needed for the generic equality shortcut. -/
theorem allequalExactShortcutLaw {K : Type} (equal : K → K → Bool)
    (trace : FiniteTrace K) :
    allequalGeneric equal trace = .ok (listAllEqualBy equal trace.values) ↔
      (trace.hasLength = true → trace.length ≤ 1 →
        listAllEqualBy equal trace.values = true) := by
  constructor
  · intro h ht hl
    simp only [allequalGeneric, ht, hl, decide_true, Bool.true_and, ite_true] at h
    exact (Except.ok.inj h).symm
  · intro h
    unfold allequalGeneric
    split
    next hGate =>
      have ht := (Bool.and_eq_true_iff.mp hGate).1
      have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp hGate).2
      rw [h ht hl]
    next hGate => cases trace.values <;> rfl

/-- Exact mapped shortcut requirement; a full length equation is stronger than needed. -/
theorem mappedAllequalExactShortcutLaw {A K : Type} (equal : K → K → Bool)
    (values : FiniteTrace A)
    (generator : (A → K) → FiniteTrace A → FiniteTrace K) (f : A → K) :
    allequalMapMethod generator (allequalGeneric equal) f values =
      .ok (listAllEqualBy equal ((generator f values).values)) ↔
      ((generator f values).hasLength = true → (generator f values).length ≤ 1 →
        listAllEqualBy equal ((generator f values).values) = true) := by
  exact allequalExactShortcutLaw equal (generator f values)

/-- No earlier key may equal a remaining value, and the remaining values are distinct. -/
def remainingDistinct {K : Type} (equal : K → K → Bool)
    (seen values : List K) : Bool :=
  values.all (fun x => !(seen.any (equal x))) && listAllDistinctBy equal values

theorem freshCons {K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x) (x : K) (seen values : List K) :
    values.all (fun y => !((x :: seen).any (equal y))) =
      (values.all (fun y => !equal x y) && values.all (fun y => !(seen.any (equal y)))) := by
  induction values with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.all_cons, ih]
    simp only [List.any_cons]
    rw [hsym y x]
    cases equal x y <;> cases seen.any (equal y) <;>
      cases ys.all (fun z => !equal x z) <;>
      cases ys.all (fun z => !(seen.any (equal z))) <;> rfl

theorem remainingDistinctCons {K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x) (x : K) (seen values : List K) :
    remainingDistinct equal seen (x :: values) =
      (!(seen.any (equal x)) && remainingDistinct equal (x :: seen) values) := by
  simp only [remainingDistinct, List.all_cons, listAllDistinctBy, freshCons equal hsym]
  cases seen.any (equal x) <;>
    cases values.all (fun y => !(seen.any (equal y))) <;>
    cases values.all (fun y => !equal x y) <;>
    cases listAllDistinctBy equal values <;> rfl

theorem remainingDistinctEmpty {K : Type} (equal : K → K → Bool) (values : List K) :
    remainingDistinct equal [] values = listAllDistinctBy equal values := by
  have h : values.all (fun _ => true) = true := List.all_eq_true.mpr (by intros; rfl)
  simp only [remainingDistinct, List.any_nil, Bool.not_false, h, Bool.true_and]

/-- One-step insertion law up to a finite scan limit. This records precisely
which absent dictionary invariants a future model proof must establish. -/
def InsertHistoryLaw {K : Type} (equal : K → K → Bool)
    (Stored : SetModel K → List K → Prop)
    (inBang : K → SetModel K → Result (Bool × SetModel K)) (limit : Nat) : Prop :=
  ∀ key state history, history.length < limit → Stored state history →
    ∃ next, inBang key state = .ok (history.any (equal key), next) ∧
      Stored next (key :: history)

/-- The insertion loop is total and correct under a finite one-step history law.
Its final representation is required only on the no-duplicate path. -/
theorem insertLoopCorrect {K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (Stored : SetModel K → List K → Prop)
    (inBang : K → SetModel K → Result (Bool × SetModel K))
    (limit : Nat)
    (hInsert : InsertHistoryLaw equal Stored inBang limit)
    (values : List K) (state : SetModel K) (history : List K)
    (hStored : Stored state history)
    (hBound : history.length + values.length ≤ limit) :
    ∃ result out, alluniqueInsertLoop inBang values state = .ok (result, out) ∧
      result = remainingDistinct equal history values ∧
      (result = true → Stored out (values.reverse ++ history)) := by
  induction values generalizing state history with
  | nil =>
    exact ⟨true, state, rfl, rfl, fun _ => hStored⟩
  | cons key values ih =>
    have hRoom : history.length < limit := by
      simp only [List.length_cons] at hBound
      omega
    have hRestBound : (key :: history).length + values.length ≤ limit := by
      simp only [List.length_cons] at hBound ⊢
      omega
    obtain ⟨next, hStep, hNext⟩ := hInsert key state history hRoom hStored
    cases hp : history.any (equal key) with
    | true =>
      refine ⟨false, next, ?_, ?_, ?_⟩
      · simp only [alluniqueInsertLoop, hStep, hp, bind, Except.bind, ite_true]
      · rw [remainingDistinctCons equal hsym, hp]; rfl
      · intro h; cases h
    | false =>
      obtain ⟨result, out, hLoop, hResult, hOut⟩ := ih next (key :: history) hNext hRestBound
      refine ⟨result, out, ?_, ?_, ?_⟩
      · simp only [alluniqueInsertLoop, hStep, hp, bind, Except.bind,
          Bool.false_eq_true, ite_false, hLoop]
      · rw [remainingDistinctCons equal hsym, hp, Bool.not_false, Bool.true_and]
        exact hResult
      · intro hr
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hOut hr

theorem remainingDistinctAppend {K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x) (history front rest : List K) :
    remainingDistinct equal history (front ++ rest) =
      (remainingDistinct equal history front &&
        remainingDistinct equal (front.reverse ++ history) rest) := by
  induction front generalizing history with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, remainingDistinctCons equal hsym, ih,
      List.reverse_cons, List.append_assoc, List.nil_append, Bool.and_assoc]

/-- Correctness of a scan split by an arbitrary representation-preserving resize. -/
theorem splitScanCorrect {K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (Stored : SetModel K → List K → Prop)
    (inBang : K → SetModel K → Result (Bool × SetModel K))
    (limit : Nat)
    (hInsert : InsertHistoryLaw equal Stored inBang limit)
    (state : SetModel K) (hEmpty : Stored state [])
    (resize : SetModel K → Result (SetModel K))
    (hResize : ∀ current history, Stored current history →
      ∃ next, resize current = .ok next ∧ Stored next history)
    (front rest : List K) (hBound : front.length + rest.length ≤ limit) :
    (do
      let (prefixUnique, current) ← alluniqueInsertLoop inBang front state
      if !prefixUnique then .ok false
      else
        let next ← resize current
        (alluniqueInsertLoop inBang rest next).map Prod.fst) =
      .ok (listAllDistinctBy equal (front ++ rest)) := by
  have hFrontBound : ([] : List K).length + front.length ≤ limit := by
    simp only [List.length_nil, Nat.zero_add]
    omega
  have hRestBound : (front.reverse ++ []).length + rest.length ≤ limit := by
    simpa only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero] using hBound
  obtain ⟨prefixUnique, current, hPrefix, hPrefixBool, hCurrent⟩ :=
    insertLoopCorrect equal hsym Stored inBang limit hInsert front state [] hEmpty hFrontBound
  have hJoin : listAllDistinctBy equal (front ++ rest) =
      (prefixUnique && remainingDistinct equal (front.reverse ++ []) rest) := by
    rw [← remainingDistinctEmpty equal (front ++ rest),
      remainingDistinctAppend equal hsym, ← hPrefixBool]
  cases hp : prefixUnique with
  | false =>
    simp only [hPrefix, hp, bind, Except.bind, Bool.not_false, ite_true,
      hJoin, Bool.false_and]
  | true =>
    obtain ⟨next, hNext, hStored⟩ := hResize current (front.reverse ++ []) (hCurrent hp)
    obtain ⟨result, out, hLoop, hResult, _⟩ :=
      insertLoopCorrect equal hsym Stored inBang limit hInsert rest next (front.reverse ++ []) hStored hRestBound
    simp only [hPrefix, hp, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
      ite_false, hNext, hLoop, Except.map, hJoin, Bool.true_and, hResult]

/-- Full hashed predicate, including the 1000-element prefix and resizing, derived
from insertion and resizing laws rather than an assumed hashed-predicate result. -/
theorem hashedCorrectFromHistory {K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (Stored : SetModel K → List K → Prop)
    (newSet : Nat → SetModel K)
    (inBang : K → SetModel K → Result (Bool × SetModel K))
    (sizehint : SetModel K → JInt .i64 → Result (SetModel K))
    (hEmpty : Stored (newSet 0) [])
    (limit : Nat)
    (hInsert : InsertHistoryLaw equal Stored inBang limit)
    (trace : FiniteTrace K) (hBound : trace.values.length ≤ limit)
    (hSizehint : ∀ current history, Stored current history →
      ∃ next, sizehint current (JInt.wrap .i64 (Int.ofNat trace.length)) = .ok next ∧
        Stored next history) :
    hashedAlluniqueMethod newSet inBang sizehint trace =
      .ok (listAllDistinctBy equal trace.values) := by
  unfold hashedAlluniqueMethod
  by_cases hg : (trace.hasLength && decide (trace.length > 1000)) = true
  · simp only [hg, ite_true]
    have h := splitScanCorrect equal hsym Stored inBang limit hInsert (newSet 0) hEmpty
      (fun current => sizehint current (JInt.wrap .i64 (Int.ofNat trace.length)))
      hSizehint (trace.values.take 1000) (trace.values.drop 1000) (by
        rw [← List.length_append, List.take_append_drop]
        exact hBound)
    simpa only [List.take_append_drop] using h
  · simp only [hg]
    have hResize : ∀ (current : SetModel K) history, Stored current history →
        ∃ next, (Except.ok current : Result (SetModel K)) = .ok next ∧ Stored next history := by
      intro current history hs
      exact ⟨current, rfl, hs⟩
    exact splitScanCorrect equal hsym Stored inBang limit hInsert (newSet 0) hEmpty
      (fun current => .ok current) hResize [] trace.values
      (by simpa only [List.length_nil, Nat.zero_add] using hBound)

/-- The generic predicate needs length coherence only for its early true branch.
The larger branches are established by the loop theorem above and the existing
indexed proof imported by the frozen target file. -/
theorem genericCorrectFromHistory {K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (Stored : SetModel K → List K → Prop)
    (newSet : Nat → SetModel K)
    (inBang : K → SetModel K → Result (Bool × SetModel K))
    (sizehint : SetModel K → JInt .i64 → Result (SetModel K))
    (hEmpty : Stored (newSet 0) [])
    (limit : Nat)
    (hInsert : InsertHistoryLaw equal Stored inBang limit)
    (trace : FiniteTrace K) (hBound : trace.values.length ≤ limit)
    (collect : FiniteTrace K → Result (FiniteTrace K))
    (hCollect : collect trace = .ok trace)
    (hShort : trace.hasLength = true → trace.length < 2 → trace.values.length < 2)
    (hSizehint : ∀ current history, Stored current history →
      ∃ next, sizehint current (JInt.wrap .i64 (Int.ofNat trace.length)) = .ok next ∧
        Stored next history) :
    alluniqueGeneric (fun t => t.hasLength) (fun t => t.length) collect
      (indexedAlluniqueMethod equal) (hashedAlluniqueMethod newSet inBang sizehint) trace =
      .ok (listAllDistinctBy equal trace.values) := by
  have hHash := hashedCorrectFromHistory equal hsym Stored newSet inBang sizehint
    hEmpty limit hInsert trace hBound hSizehint
  unfold alluniqueGeneric
  split
  next hLength =>
    split
    next hSmall =>
      have hvSmall := hShort hLength hSmall
      cases hv : trace.values with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons y ys => simp only [hv, List.length_cons] at hvSmall; omega
    next hNotSmall =>
      split
      · simp only [hCollect, bind, Except.bind,
          JuliaLean.ChatGPT.Batch4.Group14.indexedAlluniqueCorrect]
      · exact hHash
  next hLength => exact hHash

/-- Mapped generic correctness under the same local storage and shortcut laws. -/
theorem mappedGenericCorrectFromHistory {A K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (Stored : SetModel K → List K → Prop)
    (newSet : Nat → SetModel K)
    (inBang : K → SetModel K → Result (Bool × SetModel K))
    (sizehint : SetModel K → JInt .i64 → Result (SetModel K))
    (hEmpty : Stored (newSet 0) [])
    (limit : Nat)
    (hInsert : InsertHistoryLaw equal Stored inBang limit)
    (input : FiniteTrace A) (output : FiniteTrace K) (hBound : output.values.length ≤ limit) (f : A → K)
    (generator : (A → K) → FiniteTrace A → FiniteTrace K)
    (hGenerator : generator f input = output)
    (collect : FiniteTrace K → Result (FiniteTrace K))
    (hCollect : collect output = .ok output)
    (hShort : output.hasLength = true → output.length < 2 → output.values.length < 2)
    (hSizehint : ∀ current history, Stored current history →
      ∃ next, sizehint current (JInt.wrap .i64 (Int.ofNat output.length)) = .ok next ∧
        Stored next history) :
    alluniqueMapMethod generator
      (alluniqueGeneric (fun t => t.hasLength) (fun t => t.length) collect
        (indexedAlluniqueMethod equal) (hashedAlluniqueMethod newSet inBang sizehint))
      f input = .ok (listAllDistinctBy equal output.values) := by
  unfold alluniqueMapMethod
  rw [hGenerator]
  exact genericCorrectFromHistory equal hsym Stored newSet inBang sizehint hEmpty limit hInsert
    output hBound collect hCollect hShort hSizehint

/-- Mapped tuples, including both cutoffs, follow from finite insertion/resize laws. -/
theorem mappedTupleCorrectFromHistory {A K : Type} (equal : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (Stored : SetModel K → List K → Prop)
    (newSet : Nat → SetModel K)
    (inBang : K → SetModel K → Result (Bool × SetModel K))
    (sizehint : SetModel K → JInt .i64 → Result (SetModel K))
    (hEmpty : Stored (newSet 0) []) (limit : Nat)
    (hInsert : InsertHistoryLaw equal Stored inBang limit)
    (f : A → K) (trace : FiniteTrace A) (hBound : trace.values.length ≤ limit)
    (hSizehint : ∀ current history, Stored current history →
      ∃ next, sizehint current (JInt.wrap .i64 (Int.ofNat trace.values.length)) = .ok next ∧
        Stored next history) :
    alluniqueMapTuple f equal (hashedAlluniqueMethod newSet inBang sizehint) trace =
      .ok (listAllDistinctBy equal (trace.values.map f)) := by
  have hHash : ∀ (t : FiniteTrace K), t.length = trace.values.length →
      t.values.length ≤ limit → hashedAlluniqueMethod newSet inBang sizehint t =
      .ok (listAllDistinctBy equal t.values) := by
    intro t ht hb
    apply hashedCorrectFromHistory equal hsym Stored newSet inBang sizehint
      hEmpty limit hInsert t hb
    intro current history hs
    simpa only [ht] using hSizehint current history hs
  unfold alluniqueMapTuple
  split
  next hSmall =>
    cases hv : trace.values with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys => simp only [hv, List.length_cons] at hSmall; omega
  next hNotSmall =>
    dsimp only
    split
    · exact hHash _ rfl (by simpa only [List.length_map] using hBound)
    · exact JuliaLean.ChatGPT.Batch4.Group14.alluniqueTupleCorrect equal
        (hashedAlluniqueMethod newSet inBang sizehint) _
        (hHash _ rfl (by simpa only [List.length_map] using hBound))

/-- Every conjunct of the specialized predicate target follows from explicit
finite one-step backend laws; no full hashed-predicate conclusion is assumed. -/
theorem specializationsCorrectFromHistory {K : Type} (equal less : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (Stored : SetModel K → List K → Prop)
    (newSet : Nat → SetModel K)
    (inBang : K → SetModel K → Result (Bool × SetModel K))
    (sizehint : SetModel K → JInt .i64 → Result (SetModel K))
    (hEmpty : Stored (newSet 0) []) (limit : Nat)
    (hInsert : InsertHistoryLaw equal Stored inBang limit)
    (trace : FiniteTrace K) (hBound : trace.values.length ≤ limit)
    (hOriginalSizehint : ∀ current history, Stored current history →
      ∃ next, sizehint current (JInt.wrap .i64 (Int.ofNat trace.length)) = .ok next ∧
        Stored next history)
    (hMappedSizehint : ∀ current history, Stored current history →
      ∃ next, sizehint current (JInt.wrap .i64 (Int.ofNat trace.values.length)) = .ok next ∧
        Stored next history) :
    alluniqueStringMethod (fun t => t.values.length)
      (indexedAlluniqueMethod equal) (hashedAlluniqueMethod newSet inBang sizehint) trace =
        .ok (listAllDistinctBy equal trace.values) ∧
    alluniqueStridedMethod trace false equal less (indexedAlluniqueMethod equal)
      (hashedAlluniqueMethod newSet inBang sizehint) =
        .ok (listAllDistinctBy equal trace.values) ∧
    alluniqueTupleMethod equal (hashedAlluniqueMethod newSet inBang sizehint) trace =
        .ok (listAllDistinctBy equal trace.values) ∧
    alluniqueMapTuple id equal (hashedAlluniqueMethod newSet inBang sizehint) trace =
        .ok (listAllDistinctBy equal trace.values) ∧ alluniqueEmptyTuple = true := by
  have hHash := hashedCorrectFromHistory equal hsym Stored newSet inBang sizehint
    hEmpty limit hInsert trace hBound hOriginalSizehint
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · exact JuliaLean.ChatGPT.Batch4.Group14.alluniqueStringCorrect equal
      (hashedAlluniqueMethod newSet inBang sizehint) trace hHash
  · exact JuliaLean.ChatGPT.Batch4.Group14.alluniqueUnorderedStridedCorrect equal less
      (hashedAlluniqueMethod newSet inBang sizehint) trace hHash
  · exact JuliaLean.ChatGPT.Batch4.Group14.alluniqueTupleCorrect equal
      (hashedAlluniqueMethod newSet inBang sizehint) trace hHash
  · simpa only [List.map_id] using
      mappedTupleCorrectFromHistory equal hsym Stored newSet inBang sizehint
        hEmpty limit hInsert id trace hBound hMappedSizehint

end JuliaLean.ChatGPT.Batch8.Group2.Predicates

namespace JuliaLean.ChatGPT.Batch8.Group2.OrderedStrided

open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- The comparison scan's successful monotone prefix can safely gain its endpoint. -/
theorem pairwiseSnoc {α : Type} (compare : α → α → Bool)
    (before : List α) (current : α)
    (hbefore : before.Pairwise (fun x y => compare x y = true))
    (hbound : ∀ x, x ∈ before → compare x current = true) :
    (before ++ [current]).Pairwise (fun x y => compare x y = true) := by
  apply List.pairwise_append.mpr
  refine ⟨hbefore, List.pairwise_singleton _ _, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst y
  exact hbound x hx

/-- Strict pairwise comparison implies the Boolean distinctness specification. -/
theorem distinctOfPairwise {α : Type} (equal compare : α → α → Bool)
    (hdifferent : ∀ x y, compare x y = true → equal x y = false)
    (values : List α) (hvalues : values.Pairwise (fun x y => compare x y = true)) :
    listAllDistinctBy equal values = true := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hvalues
    have hall : xs.all (fun y => !equal x y) = true := by
      apply List.all_eq_true.mpr
      intro y hy
      rw [hdifferent x y (hhead y hy)]
      rfl
    simp only [listAllDistinctBy, hall, ih htail, Bool.true_and]

/-- An adjacent repeated value disproves full-list distinctness regardless of
how many values have already been scanned. -/
theorem adjacentEqualNotDistinct {α : Type} (equal : α → α → Bool)
    (before : List α) (current next : α) (rest : List α)
    (heq : equal current next = true) :
    listAllDistinctBy equal (before ++ current :: next :: rest) = false := by
  induction before with
  | nil =>
    simp only [List.nil_append, listAllDistinctBy, List.all_cons, heq, Bool.not,
      Bool.false_and]
  | cons x xs ih =>
    simp only [List.cons_append, listAllDistinctBy, ih, Bool.and_false]

/-- The loop invariant records the complete input and the pairwise monotone
prefix. Hash fallback checks the complete input; an adjacent equal value is a
concrete duplicate; exhausting the loop certifies the entire monotone chain. -/
theorem scanCorrect {α : Type} (trace : FiniteTrace α)
    (equal compare : α → α → Bool) (hashed : FiniteTrace α → Result Bool)
    (htrans : ∀ x y z, compare x y = true → compare y z = true → compare x z = true)
    (hdifferent : ∀ x y, compare x y = true → equal x y = false)
    (hhash : hashed trace = .ok (listAllDistinctBy equal trace.values))
    (remaining before : List α) (current : α)
    (hwhole : trace.values = before ++ current :: remaining)
    (hbefore : before.Pairwise (fun x y => compare x y = true))
    (hbound : ∀ x, x ∈ before → compare x current = true) :
    alluniqueStridedMethod.scan trace equal hashed compare current remaining =
      .ok (listAllDistinctBy equal trace.values) := by
  induction remaining generalizing before current with
  | nil =>
    have hd := distinctOfPairwise equal compare hdifferent
      (before ++ [current]) (pairwiseSnoc compare before current hbefore hbound)
    simp only [alluniqueStridedMethod.scan, hwhole, hd]
  | cons next rest ih =>
    simp only [alluniqueStridedMethod.scan]
    split
    next hstep =>
      apply ih (before ++ [current]) next
      · simpa only [List.append_assoc, List.singleton_append] using hwhole
      · exact pairwiseSnoc compare before current hbefore hbound
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact htrans x current next (hbound x hx) hstep
        · simp only [List.mem_singleton] at hx
          subst x
          exact hstep
    next hnstep =>
      split
      next heq =>
        rw [hwhole, adjacentEqualNotDistinct equal before current next rest heq]
      next hneq => exact hhash

/-- Reverse strict comparison is also incompatible with forward equality. -/
theorem reverseDifferent {α : Type} (equal less : α → α → Bool)
    (hlaw : OrderedEqualityLawful equal less) (x y : α) (h : less y x = true) :
    equal x y = false := by
  cases heq : equal x y with
  | false => rfl
  | true =>
    have hfalse := (hlaw.2.2.1 x y heq).2
    rw [h] at hfalse
    contradiction

/-- Correctness of the ordered StridedArray specialization, including the
ascending scan, descending scan, adjacent-duplicate exit, and full-input fallback.
The backend hypothesis explicitly uses the same equality as the fast path. -/
theorem orderedStridedCorrect {α : Type} (equal less : α → α → Bool)
    (trace : FiniteTrace α) (hashed : FiniteTrace α → Result Bool)
    (hlaw : OrderedEqualityLawful equal less)
    (hhash : hashed trace = .ok (listAllDistinctBy equal trace.values)) :
    alluniqueStridedMethod trace true equal less (indexedAlluniqueMethod equal) hashed =
      .ok (listAllDistinctBy equal trace.values) := by
  unfold alluniqueStridedMethod
  split
  · exact JuliaLean.ChatGPT.Batch4.Group14.indexedAlluniqueCorrect equal trace
  · simp only [ite_true]
    cases hvalues : trace.values with
    | nil => simpa only [hvalues] using hhash
    | cons first tail =>
      cases tail with
      | nil => simpa only [hvalues] using hhash
      | cons second rest =>
        change (if equal first second then .ok false else
          alluniqueStridedMethod.scan trace equal hashed
            (if less first second then less else fun a b => less b a) second rest) =
          .ok (listAllDistinctBy equal (first :: second :: rest))
        by_cases hequal : equal first second = true
        · simp only [hequal, ite_true, listAllDistinctBy, List.all_cons,
            Bool.not, Bool.false_and]
        · simp only [hequal, Bool.false_eq_true, ite_false]
          have hneq : equal first second = false := by
            cases h : equal first second
            · rfl
            · exact False.elim (hequal h)
          by_cases hforward : less first second = true
          · simp only [hforward, ite_true]
            have hbound : ∀ x, x ∈ [first] → less x second = true := by
              intro x hx
              simp only [List.mem_singleton] at hx
              subst x
              exact hforward
            have hscan := scanCorrect trace equal less hashed
              hlaw.2.2.2.2 hlaw.2.1 hhash rest [first] second hvalues
              (List.pairwise_singleton _ _) hbound
            simpa only [hvalues] using hscan
          · simp only [hforward, Bool.false_eq_true, ite_false]
            have hreverse : less second first = true := by
              rcases hlaw.2.2.2.1 first second hneq with h | h
              · exact False.elim (hforward h)
              · exact h
            have hbound : ∀ x, x ∈ [first] → less second x = true := by
              intro x hx
              simp only [List.mem_singleton] at hx
              subst x
              exact hreverse
            have hscan := scanCorrect trace equal (fun x y => less y x) hashed
              (fun x y z hxy hyz => hlaw.2.2.2.2 z y x hyz hxy)
              (reverseDifferent equal less hlaw) hhash rest [first] second hvalues
              (List.pairwise_singleton _ _) hbound
            simpa only [hvalues] using hscan

end JuliaLean.ChatGPT.Batch8.Group2.OrderedStrided

namespace JuliaLean.ChatGPT.Batch8.Group2.Replacement
open JuliaLean JuliaLean.base.set JuliaLean.Proofs.base.set

/-- The array's element-level traversal, extracted independently from its writes. -/
def arrayValues {α : Type} (new : α → Result α) (same : α → α → Bool)
    (replaceAll : Bool) (limit changed : Nat) : List α → Result (List α)
  | [] => .ok []
  | x :: xs => do
    if !replaceAll && changed >= limit then
      return x :: (← arrayValues new same false limit changed xs)
    else
      let y ← new x
      return y :: (← arrayValues new same replaceAll limit
        (changed + if same x y then 0 else 1) xs)


theorem takePrefix {α : Type} (pref suffix : List α) :
    (pref ++ suffix).take pref.length = pref := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, List.take_succ_cons, ih]

theorem dropPrefixOne {α : Type} (pref : List α) (x : α) (xs : List α) :
    (pref ++ x :: xs).drop (pref.length + 1) = xs := by
  induction pref with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
    exact ih

/-- A valid indexed write changes exactly the selected element. -/
theorem writeAtPrefix {α : Type} (tag : Nat) (first : Int)
    (pref : List α) (old value : α) (suffix : List α) :
    vectorWriteAt ⟨tag, first, pref ++ old :: suffix⟩
      (first + (pref.length : Int)) value =
      (⟨tag, first, pref ++ value :: suffix⟩ : VectorModel α) := by
  have hoff : (first + (pref.length : Int) - first).toNat = pref.length := by omega
  simp only [vectorWriteAt, hoff, takePrefix, dropPrefixOne, List.append_assoc,
    List.singleton_append]

/-- The array loop overwrites the remaining region in source order. -/
theorem arrayLoopPrefix {α : Type} (new : α → Result α) (same : α → α → Bool)
    (source suffix pref : List α) (tag : Nat) (first : Int)
    (replaceAll : Bool) (limit changed : Nat)
    (hlen : suffix.length = source.length) :
    replaceArrayLoop new same source (first + (pref.length : Int)) first
      ⟨tag, first, pref ++ suffix⟩ replaceAll limit changed =
    (arrayValues new same replaceAll limit changed source).map
      (fun values => ⟨tag, first, pref ++ values⟩) := by
  induction source generalizing suffix pref replaceAll changed with
  | nil =>
    have hnil : suffix = [] := List.eq_nil_of_length_eq_zero hlen
    subst suffix
    rfl
  | cons x xs ih =>
    cases suffix with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons old suffix =>
      have htail : suffix.length = xs.length := by
        simp only [List.length_cons] at hlen
        omega
      have hindex : ¬ first + (pref.length : Int) < first := by omega
      have hnext (value : α) :
          first + (pref.length : Int) + 1 = first + ((pref ++ [value]).length : Int) := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      simp only [replaceArrayLoop, hindex, ite_false, arrayValues]
      split
      next hstop =>
        rw [writeAtPrefix, hnext x]
        have heq : pref ++ x :: suffix = (pref ++ [x]) ++ suffix := by
          simp only [List.append_assoc, List.singleton_append]
        rw [heq, ih suffix (pref ++ [x]) false changed htail]
        cases hrec : arrayValues new same false limit changed xs <;>
          simp only [hrec, Except.map, bind, Except.bind, pure, Except.pure,
            List.append_assoc, List.singleton_append]
      next hcontinue =>
        cases hnew : new x with
        | error e => simp only [hnew, bind, Except.bind, Except.map]
        | ok y =>
          simp only [hnew, bind, Except.bind]
          rw [writeAtPrefix, hnext y]
          have heq : pref ++ y :: suffix = (pref ++ [y]) ++ suffix := by
            simp only [List.append_assoc, List.singleton_append]
          rw [heq, ih suffix (pref ++ [y]) replaceAll
            (changed + if same x y then 0 else 1) htail]
          cases hrec : arrayValues new same replaceAll limit
            (changed + if same x y then 0 else 1) xs <;>
            simp only [hrec, Except.map, bind, Except.bind, pure, Except.pure,
              List.append_assoc, List.singleton_append]

/-- Successful element-level array traversal preserves length. -/
theorem arrayValuesLength {α : Type} (new : α → Result α) (same : α → α → Bool)
    (values out : List α) (replaceAll : Bool) (limit changed : Nat)
    (h : arrayValues new same replaceAll limit changed values = .ok out) :
    out.length = values.length := by
  induction values generalizing out replaceAll changed with
  | nil => cases h; rfl
  | cons x xs ih =>
    simp only [arrayValues] at h
    split at h
    · cases ht : arrayValues new same false limit changed xs with
      | error e => simp only [ht, bind, Except.bind] at h; cases h
      | ok ys =>
        simp only [ht, bind, Except.bind, pure, Except.pure] at h
        cases h
        simp only [List.length_cons, ih ys false changed ht]
    · cases hn : new x with
      | error e => simp only [hn, bind, Except.bind] at h; cases h
      | ok y =>
        simp only [hn, bind, Except.bind] at h
        cases ht : arrayValues new same replaceAll limit
            (changed + if same x y then 0 else 1) xs with
        | error e => simp only [ht, bind, Except.bind] at h; cases h
        | ok ys =>
          simp only [ht, bind, Except.bind, pure, Except.pure] at h
          cases h
          simp only [List.length_cons, ih ys replaceAll _ ht]

/-- Changes are counted in lockstep with the model's identity test. -/
theorem changedCons {α : Type} (same : α → α → Bool) (x y : α) (xs ys : List α) :
    changedCountBy same (x :: xs) (y :: ys) =
      (if same x y then 0 else 1) + changedCountBy same xs ys := by
  simp only [changedCountBy, List.zip_cons_cons, List.filter_cons]
  cases hs : same x y <;>
    simp only [hs, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      List.length_cons, Nat.zero_add, Nat.add_comm]

/-- Comparing a list to itself records no changes for a reflexive identity test. -/
theorem changedSelf {α : Type} (same : α → α → Bool) (hsame : ∀ x, same x x = true)
    (xs : List α) : changedCountBy same xs xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [changedCons, hsame, ih]; rfl

/-- Once the budget is exhausted, the remaining values are copied verbatim. -/
theorem arrayValuesExhausted {α : Type} (new : α → Result α) (same : α → α → Bool)
    (xs : List α) (limit changed : Nat) (hlimit : limit ≤ changed) :
    arrayValues new same false limit changed xs = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [arrayValues, Bool.not_false, Bool.true_and, decide_eq_true hlimit,
      ite_true, ih, bind, Except.bind, pure, Except.pure]

/-- The bounded array traversal consumes at most its remaining budget. -/
theorem arrayValuesBudget {α : Type} (new : α → Result α) (same : α → α → Bool)
    (hsame : ∀ x, same x x = true) (xs ys : List α) (limit changed : Nat)
    (h : arrayValues new same false limit changed xs = .ok ys) :
    changedCountBy same xs ys ≤ limit - changed := by
  induction xs generalizing ys changed with
  | nil => cases h; simp only [changedCountBy, List.zip_nil_left,
      List.filter_nil, List.length_nil, Nat.zero_le]
  | cons x xs ih =>
    by_cases hstop : limit ≤ changed
    · rw [arrayValuesExhausted new same (x :: xs) limit changed hstop] at h
      cases h
      rw [changedSelf same hsame]
      exact Nat.zero_le _
    · have hcontinue : changed < limit := by omega
      simp only [arrayValues, Bool.not_false, Bool.true_and,
        decide_eq_false hstop, Bool.false_eq_true, ite_false] at h
      cases hn : new x with
      | error e => simp only [hn, bind, Except.bind] at h; cases h
      | ok y =>
        simp only [hn, bind, Except.bind] at h
        cases ht : arrayValues new same false limit
            (changed + if same x y then 0 else 1) xs with
        | error e => simp only [ht, bind, Except.bind] at h; cases h
        | ok tail =>
          simp only [ht, bind, Except.bind, pure, Except.pure] at h
          cases h
          rw [changedCons]
          have htail := ih tail _ ht
          cases hs : same x y <;>
            simp only [hs, ite_true, Bool.false_eq_true, ite_false] at * <;> omega

/-- No list comparison can count more changes than there are source values. -/
theorem changedBound {α : Type} (same : α → α → Bool) (xs ys : List α) :
    changedCountBy same xs ys ≤ xs.length := by
  unfold changedCountBy
  exact Nat.le_trans (List.length_filter_le _ _) (by
    rw [List.length_zip]
    exact Nat.min_le_left _ _)

/-- Existing array replacement is correct under matching index origins and
reflexive element identity. No law for the collection-identity callback is needed. -/
theorem arrayContract {α : Type} (new : α → Result α) (same : α → α → Bool)
    (sameVector : VectorModel α → VectorModel α → Bool)
    (result source out : VectorModel α) (count : Nat)
    (hlen : result.values.length = source.values.length)
    (hfirst : result.firstIndex = source.firstIndex)
    (hidentity : ∀ x, same x x = true)
    (h : replaceArrayMethod new same sameVector result source count = .ok out) :
    out.values.length = source.values.length ∧
      changedCountBy same source.values out.values ≤ count := by
  have hresult : result = ⟨result.eltype, source.firstIndex, [] ++ result.values⟩ := by
    cases result
    simp only [List.nil_append] at *
    cases hfirst
    rfl
  have hloop (all : Bool) :
      replaceArrayLoop new same source.values source.firstIndex source.firstIndex result all count 0 =
      (arrayValues new same all count 0 source.values).map
        (fun values => ⟨result.eltype, source.firstIndex, values⟩) := by
    conv => lhs; rw [hresult]
    simpa only [List.nil_append, List.length_nil, Int.natCast_zero, Int.add_zero] using
      arrayLoopPrefix new same source.values result.values [] result.eltype source.firstIndex all count 0 hlen
  unfold replaceArrayMethod at h
  split at h
  next hlarge =>
    have hbranch :
        replaceArrayLoop new same source.values source.firstIndex source.firstIndex result true count 0 =
          .ok out := by
      split at h <;> exact h
    rw [hloop true] at hbranch
    cases hr : arrayValues new same true count 0 source.values with
    | error e => simp only [hr, Except.map] at hbranch; cases hbranch
    | ok ys =>
      simp only [hr, Except.map] at hbranch
      cases hbranch
      exact ⟨arrayValuesLength new same source.values ys true count 0 hr,
        Nat.le_trans (changedBound same source.values ys) hlarge⟩
  next hsmall =>
    rw [hloop false] at h
    cases hr : arrayValues new same false count 0 source.values with
    | error e => simp only [hr, Except.map] at h; cases h
    | ok ys =>
      simp only [hr, Except.map] at h
      cases h
      exact ⟨arrayValuesLength new same source.values ys false count 0 hr,
        by simpa only [Nat.sub_zero] using arrayValuesBudget new same hidentity source.values ys count 0 hr⟩



/-- Each deletion preserves validity and removes precisely its selected key,
under the pop operation's local contract for valid states. -/
theorem popPairsEffect {C K : Type} (equal : K → K → Bool)
    (valid : C → Prop) (member : K → C → Bool) (pop : K → C → Result (K × C))
    (hpop : ∀ key before returned after, valid before →
      pop key before = .ok (returned, after) → valid after ∧
      ∀ query, member query after = (member query before && !equal query key))
    (pairs : List (K × K)) (before after : C) (hvalid : valid before)
    (h : pairs.foldlM (fun r pair => (pop pair.1 r).map Prod.snd) before = .ok after) :
    valid after ∧ ∀ query, member query after =
      (member query before && !(pairs.any (fun pair => equal query pair.1))) := by
  induction pairs generalizing before with
  | nil =>
    cases h
    refine ⟨hvalid, ?_⟩
    intro query
    simp only [List.any_nil, Bool.not_false, Bool.and_true]
  | cons pair pairs ih =>
    simp only [List.foldlM_cons] at h
    cases hp : pop pair.1 before with
    | error e => simp only [hp, Except.map, bind, Except.bind] at h; cases h
    | ok result =>
      rcases result with ⟨returned, next⟩
      simp only [hp, Except.map, bind, Except.bind] at h
      obtain ⟨hnext, heffect⟩ := hpop pair.1 before returned next hvalid hp
      obtain ⟨hafter, htail⟩ := ih next hnext h
      refine ⟨hafter, ?_⟩
      intro query
      rw [htail query, heffect query]
      simp only [List.any_cons]
      cases member query before <;> cases equal query pair.1 <;>
        cases pairs.any (fun pair => equal query pair.1) <;> rfl

/-- Each insertion preserves validity and adds precisely its replacement key,
under the push operation's local contract for valid states. -/
theorem pushPairsEffect {C K : Type} (equal : K → K → Bool)
    (valid : C → Prop) (member : K → C → Bool) (push : K → C → Result C)
    (hpush : ∀ key before after, valid before → push key before = .ok after →
      valid after ∧ ∀ query, member query after = (member query before || equal query key))
    (pairs : List (K × K)) (before after : C) (hvalid : valid before)
    (h : pairs.foldlM (fun r pair => push pair.2 r) before = .ok after) :
    valid after ∧ ∀ query, member query after =
      (member query before || pairs.any (fun pair => equal query pair.2)) := by
  induction pairs generalizing before with
  | nil =>
    cases h
    refine ⟨hvalid, ?_⟩
    intro query
    simp only [List.any_nil, Bool.or_false]
  | cons pair pairs ih =>
    simp only [List.foldlM_cons] at h
    cases hp : push pair.2 before with
    | error e => simp only [hp, bind, Except.bind] at h; cases h
    | ok next =>
      simp only [hp, bind, Except.bind] at h
      obtain ⟨hnext, heffect⟩ := hpush pair.2 before next hvalid hp
      obtain ⟨hafter, htail⟩ := ih next hnext h
      refine ⟨hafter, ?_⟩
      intro query
      rw [htail query, heffect query]
      simp only [List.any_cons, Bool.or_assoc]

/-- The two-stage mutation preserves validity and has an exact remove-then-add
membership effect. The dictionary backend obligations remain explicit and local. -/
theorem stagedPairsEffect {C K : Type} (equal : K → K → Bool)
    (valid : C → Prop) (member : K → C → Bool) (pop : K → C → Result (K × C))
    (push : K → C → Result C)
    (hpop : ∀ key before returned after, valid before →
      pop key before = .ok (returned, after) → valid after ∧
      ∀ query, member query after = (member query before && !equal query key))
    (hpush : ∀ key before after, valid before → push key before = .ok after →
      valid after ∧ ∀ query, member query after = (member query before || equal query key))
    (pairs : List (K × K)) (before after : C) (hvalid : valid before)
    (h : ((do
      let middle ← pairs.foldlM (fun (r : C) (pair : K × K) => (pop pair.1 r).map Prod.snd) before
      pairs.foldlM (fun (r : C) (pair : K × K) => push pair.2 r) middle) : Result C) = .ok after) :
    valid after ∧ ∀ query, member query after =
      ((member query before && !(pairs.any (fun pair => equal query pair.1))) ||
        pairs.any (fun pair => equal query pair.2)) := by
  cases hp : pairs.foldlM (fun r pair => (pop pair.1 r).map Prod.snd) before with
  | error e => simp only [hp, bind, Except.bind] at h; cases h
  | ok middle =>
    simp only [hp, bind, Except.bind] at h
    obtain ⟨hmiddle, hpopEffect⟩ := popPairsEffect equal valid member pop hpop
      pairs before middle hvalid hp
    obtain ⟨hafter, hpushEffect⟩ := pushPairsEffect equal valid member push hpush
      pairs middle after hmiddle h
    refine ⟨hafter, ?_⟩
    intro query
    rw [hpushEffect query, hpopEffect query]

/-- The source method plans exactly those replacements whose identity changes. -/
def plannedPairs {K : Type} (f : K → K) (identical : K → K → Bool) :
    List K → List (K × K)
  | [] => []
  | x :: xs => if identical x (f x) then plannedPairs f identical xs
      else (x, f x) :: plannedPairs f identical xs

/-- Membership in the planned list records an original value and its changed image. -/
theorem plannedPairMem {K : Type} (f : K → K) (identical : K → K → Bool)
    (xs : List K) (pair : K × K) :
    pair ∈ plannedPairs f identical xs ↔
      ∃ x, x ∈ xs ∧ identical x (f x) = false ∧ pair = (x, f x) := by
  induction xs with
  | nil => simp only [plannedPairs, List.not_mem_nil, false_and, exists_false]
  | cons x xs ih =>
    simp only [plannedPairs]
    cases hi : identical x (f x) with
    | true =>
      simp only [hi, ite_true, ih, List.mem_cons]
      constructor
      · rintro ⟨y, hy, hf, hp⟩
        exact ⟨y, Or.inr hy, hf, hp⟩
      · rintro ⟨y, hy, hf, hp⟩
        rcases hy with hsame | hmem
        · subst y
          rw [hi] at hf
          cases hf
        · exact ⟨y, hmem, hf, hp⟩
    | false =>
      simp only [hi, Bool.false_eq_true, ite_false, List.mem_cons, ih]
      constructor
      · intro hp
        rcases hp with heq | ⟨y, hy, hf, hp⟩
        · exact ⟨x, Or.inl rfl, hi, heq⟩
        · exact ⟨y, Or.inr hy, hf, hp⟩
      · rintro ⟨y, hy, hf, hp⟩
        rcases hy with heq | hmem
        · subst y
          exact Or.inl hp
        · exact Or.inr ⟨y, hmem, hf, hp⟩

/-- A matching query identifies at most one original representative. This and
unchanged-value congruence are enough to simplify remove-then-add to mapped membership. -/
theorem plannedPairsImage {K : Type} (equal identical : K → K → Bool)
    (f : K → K) (xs : List K) (query : K)
    (hunique : ∀ x, x ∈ xs → ∀ y, y ∈ xs →
      equal query x = true → equal query y = true → x = y)
    (hunchanged : ∀ x, x ∈ xs → identical x (f x) = true →
      equal query (f x) = equal query x) :
    ((xs.any (equal query) && !(plannedPairs f identical xs).any
      (fun pair => equal query pair.1)) ||
        (plannedPairs f identical xs).any (fun pair => equal query pair.2)) =
      xs.any (fun x => equal query (f x)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true]
  constructor
  · intro h
    rcases h with ⟨⟨x, hx, hqx⟩, hno⟩ | ⟨pair, hp, hqp⟩
    · cases hi : identical x (f x) with
      | false =>
        have hpair : (x, f x) ∈ plannedPairs f identical xs :=
          (plannedPairMem f identical xs (x, f x)).mpr ⟨x, hx, hi, rfl⟩
        have hyes : (plannedPairs f identical xs).any (fun pair => equal query pair.1) = true :=
          List.any_eq_true.mpr ⟨(x, f x), hpair, hqx⟩
        rw [hyes] at hno
        cases hno
      | true =>
        exact ⟨x, hx, (hunchanged x hx hi).trans hqx⟩
    · obtain ⟨x, hx, hi, heq⟩ := (plannedPairMem f identical xs pair).mp hp
      subst pair
      exact ⟨x, hx, hqp⟩
  · rintro ⟨x, hx, hqfx⟩
    cases hi : identical x (f x) with
    | false =>
      exact Or.inr ⟨(x, f x), (plannedPairMem f identical xs (x, f x)).mpr
        ⟨x, hx, hi, rfl⟩, hqfx⟩
    | true =>
      have hqx : equal query x = true := by rw [← hunchanged x hx hi]; exact hqfx
      refine Or.inl ⟨⟨x, hx, hqx⟩, ?_⟩
      apply List.any_eq_false.mpr
      intro pair hp hqp
      obtain ⟨y, hy, hyi, heq⟩ := (plannedPairMem f identical xs pair).mp hp
      subst pair
      have he : x = y := hunique x hx y hy hqx hqp
      subst y
      rw [hi] at hyi
      cases hyi

/-- The actual collection loop visits the whole snapshot when its remaining
budget bounds the number of unvisited originals. -/
theorem collectAllPairs {K : Type} (new : K → Result K)
    (identical : K → K → Bool) (f : K → K) (hf : ∀ x, new x = .ok (f x))
    (xs : List K) (count changed : Nat) (acc : List (K × K))
    (hbudget : changed + xs.length ≤ count) :
    replaceAbstractCollectionsMethod.replacements new identical count xs changed acc =
      .ok (acc ++ plannedPairs f identical xs) := by
  induction xs generalizing changed acc with
  | nil => simp only [replaceAbstractCollectionsMethod.replacements, plannedPairs, List.append_nil]
  | cons x xs ih =>
    simp only [replaceAbstractCollectionsMethod.replacements, hf, bind, Except.bind, plannedPairs]
    cases hi : identical x (f x) with
    | true =>
      simp only [hi, ite_true]
      exact ih changed acc (by simp only [List.length_cons] at hbudget; omega)
    | false =>
      simp only [hi, Bool.false_eq_true, ite_false]
      split
      next hdone =>
        have hcount : changed + 1 = count := by simpa only [beq_iff_eq] using hdone
        have hempty : xs.length = 0 := by simp only [List.length_cons] at hbudget; omega
        have hnil : xs = [] := List.eq_nil_of_length_eq_zero hempty
        subst xs
        rfl
      next hmore =>
        rw [ih (changed + 1) (acc ++ [(x, f x)])
          (by simp only [List.length_cons] at hbudget; omega)]
        simp only [List.append_assoc, List.singleton_append]

/-- Full correctness of the source's staged generic-set replacement, conditional
only on the initial snapshot and the local pop/push membership laws. -/
theorem genericSetImage {C K : Type} (isDict isSet : C → Bool)
    (sameCollection : C → C → Bool) (elements : C → Result (List K))
    (new : K → Result K) (identical equal : K → K → Bool) (f : K → K)
    (valid : C → Prop) (member : K → C → Bool) (pop : K → C → Result (K × C))
    (push : K → C → Result C) (source out : C) (xs : List K)
    (hdict : isDict source = false) (hset : isSet source = true)
    (hsame : sameCollection source source = true)
    (helements : elements source = .ok xs) (hvalid : valid source)
    (hf : ∀ x, new x = .ok (f x))
    (hpop : ∀ key before returned after, valid before →
      pop key before = .ok (returned, after) → valid after ∧
      ∀ query, member query after = (member query before && !equal query key))
    (hpush : ∀ key before after, valid before → push key before = .ok after →
      valid after ∧ ∀ query, member query after = (member query before || equal query key))
    (hsource : ∀ query, member query source = xs.any (equal query))
    (hunique : ∀ query x, x ∈ xs → ∀ y, y ∈ xs →
      equal query x = true → equal query y = true → x = y)
    (hunchanged : ∀ query x, x ∈ xs → identical x (f x) = true →
      equal query (f x) = equal query x)
    (hresult : replaceAbstractCollectionsMethod isDict isSet sameCollection elements
      new identical asKeySet pop push source source xs.length = .ok out) :
    valid out ∧ ∀ query, member query out = xs.any (fun x => equal query (f x)) := by
  cases xs with
  | nil =>
    simp only [replaceAbstractCollectionsMethod, hdict, hset, Bool.false_and,
      Bool.true_and, Bool.false_or, Bool.not_true, Bool.false_eq_true,
      ite_false, List.length_nil, beq_self_eq_true, ite_true] at hresult
    cases hresult
    exact ⟨hvalid, fun query => hsource query⟩
  | cons x xs =>
    have hcount : ((x :: xs).length == 0) = false := by
      simp only [beq_eq_false_iff_ne, List.length_cons]
      omega
    have hcollect := collectAllPairs new identical f hf (x :: xs) (x :: xs).length 0 [] (by omega)
    simp only [List.nil_append] at hcollect
    simp only [replaceAbstractCollectionsMethod, hdict, hset, Bool.false_and,
      Bool.true_and, Bool.false_or, Bool.not_true, Bool.false_eq_true,
      ite_false, hcount, hsame, ite_true, helements, bind, Except.bind,
      hcollect, asKeySet] at hresult
    have heffect := stagedPairsEffect equal valid member pop push hpop hpush
      (plannedPairs f identical (x :: xs)) source out hvalid hresult
    refine ⟨heffect.1, ?_⟩
    intro query
    have hquery := heffect.2 query
    rw [hsource] at hquery
    exact hquery.trans (plannedPairsImage equal identical f (x :: xs) query
      (hunique query) (hunchanged query))

/-- Equality symmetry and transitivity transport a query across an unchanged value. -/
theorem unchangedCongruence {K : Type} (equal identical : K → K → Bool)
    (hsym : ∀ x y, equal x y = equal y x)
    (htrans : ∀ x y z, equal x y = true → equal y z = true → equal x z = true)
    (hid : ∀ x y, identical x y = true → equal x y = true)
    (x y query : K) (hxy : identical x y = true) : equal query y = equal query x := by
  have heq := hid x y hxy
  have heq' : equal y x = true := (hsym y x).trans heq
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hqy
    exact htrans query y x hqy heq'
  · intro hqx
    exact htrans query x y hqx heq

/-- Equality laws and a distinct snapshot discharge query uniqueness. -/
theorem snapshotQueryUnique {K : Type} (equal : K → K → Bool) (xs : List K)
    (hsym : ∀ x y, equal x y = equal y x)
    (htrans : ∀ x y z, equal x y = true → equal y z = true → equal x z = true)
    (hdistinct : ∀ x, x ∈ xs → ∀ y, y ∈ xs → equal x y = true → x = y)
    (query x : K) (hx : x ∈ xs) (y : K) (hy : y ∈ xs)
    (hqx : equal query x = true) (hqy : equal query y = true) : x = y := by
  have hxq : equal x query = true := (hsym x query).trans hqx
  exact hdistinct x hx y hy (htrans x query y hxq hqy)


/-- Instantiation at the frozen Dict-backed Set operations. The concrete backend
obligations are validity-guarded lookup, pop, and push laws, not assumed correctness
of the whole replacement method. -/
theorem concreteGenericSetImage {K : Type} (ops : DictRuntime K)
    (keyConv : JuliaLean.base.dict.KeyConv K K)
    (isDict isSet : SetModel K → Bool) (same : SetModel K → SetModel K → Bool)
    (elements : SetModel K → Result (List K)) (new : K → Result K)
    (identical : K → K → Bool) (s out : SetModel K) (values : List K) (f : K → K)
    (valid : SetModel K → Prop) (member : K → SetModel K → Bool)
    (hlaw : DictRuntimeLawful ops)
    (hdict : isDict s = false) (hset : isSet s = true) (hsame : same s s = true)
    (helements : elements s = .ok values) (hvalid : valid s)
    (hf : ∀ x, new x = .ok (f x))
    (hid : ∀ x y, identical x y = true → ops.equal x y = true)
    (hlookup : ∀ state, valid state → ∀ query,
      setInMethod ops query state = .ok (member query state))
    (hpop : ∀ key before returned after, valid before →
      setPopKeyMethod ops key before = .ok (returned, after) → valid after ∧
      ∀ query, member query after = (member query before && !ops.equal query key))
    (hpush : ∀ key before after, valid before →
      setPushMethod ops keyConv key before = .ok after → valid after ∧
      ∀ query, member query after = (member query before || ops.equal query key))
    (hsnapshot : ∀ query, member query s = values.any (ops.equal query))
    (hdistinct : ∀ x, x ∈ values → ∀ y, y ∈ values → ops.equal x y = true → x = y)
    (hresult : replaceAbstractCollectionsMethod isDict isSet same elements new identical asKeySet
      (setPopKeyMethod ops) (setPushMethod ops keyConv) s s values.length = .ok out) :
    ∀ query, setInMethod ops query out = .ok (values.any fun y => ops.equal query (f y)) := by
  have hunique : ∀ query x, x ∈ values → ∀ y, y ∈ values →
      ops.equal query x = true → ops.equal query y = true → x = y := by
    intro query x hx y hy hqx hqy
    exact snapshotQueryUnique ops.equal values hlaw.2.1 hlaw.2.2.1 hdistinct
      query x hx y hy hqx hqy
  have hunchanged : ∀ query x, x ∈ values → identical x (f x) = true →
      ops.equal query (f x) = ops.equal query x := by
    intro query x _ hi
    exact unchangedCongruence ops.equal identical hlaw.2.1 hlaw.2.2.1 hid x (f x) query hi
  obtain ⟨houtValid, hmembers⟩ := genericSetImage isDict isSet same elements new identical
    ops.equal f valid member (setPopKeyMethod ops) (setPushMethod ops keyConv) s out values
    hdict hset hsame helements hvalid hf hpop hpush hsnapshot hunique hunchanged hresult
  intro query
  rw [hlookup out houtValid query, hmembers query]

end JuliaLean.ChatGPT.Batch8.Group2.Replacement
