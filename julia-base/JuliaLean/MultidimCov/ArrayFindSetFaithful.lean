import JuliaLean.MultidimCov.ArrayVectorFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayFindSetFaithful

open JuliaLean.Registry
open ArrayFaithfulCore
open ArrayBasicsFaithful

def m2337 : ArrayState α := typedLiteral "Any" []
def P2337 : Prop := ∀ {α : Type} (_ : α), (m2337 : ArrayState α).values = []
theorem p2337 : P2337 := by simp [P2337, m2337, typedLiteral]
def m2338 := @m2337
def P2338 : Prop := ∀ {α : Type} (_value : α), (m2338 : ArrayState α).values = []
theorem p2338 : P2338 := by simp [P2338, m2338, m2337, typedLiteral]

def concatVectors (elementType : String) (vectors : List (List α)) : ArrayState α :=
  typedLiteral elementType vectors.flatten
def m2340 := @concatVectors
def P2340 : Prop := ∀ {α : Type} elementType (vectors : List (List α)),
  (m2340 elementType vectors).values = vectors.flatten.map some
theorem p2340 : P2340 := by simp [P2340, m2340, concatVectors, typedLiteral]
def m2349 := @concatVectors
def P2349 : Prop := ∀ {α : Type} elementType (vectors : List (List α)),
  (m2349 elementType vectors).values = vectors.flatten.map some
theorem p2349 : P2349 := by simp [P2349, m2349, concatVectors, typedLiteral]
def m2351 := @concatVectors
def P2351 : Prop := ∀ {α : Type} elementType (vectors : List (List α)),
  (m2351 elementType vectors).values = vectors.flatten.map some
theorem p2351 : P2351 := by simp [P2351, m2351, concatVectors, typedLiteral]
def m2366 := @concatVectors
def P2366 : Prop := ∀ {α : Type} elementType (vectors : List (List α)),
  (m2366 elementType vectors).values = vectors.flatten.map some
theorem p2366 : P2366 := by simp [P2366, m2366, concatVectors, typedLiteral]
def m2368 (dimension : Int) (values : List Int) : ArrayState Int :=
  if dimension = 1 then typedLiteral "Int" values else typedLiteral "Int" []
def P2368 : Prop := ∀ dimension values,
  (m2368 dimension values).values = if dimension = 1 then values.map some else []
theorem p2368 : P2368 := by
  unfold P2368
  intro dimension values
  by_cases h : dimension = 1 <;> simp [m2368, typedLiteral, h]

structure Collection (κ α : Type) where
  entries : List (κ × α)
  deriving Repr, DecidableEq

def findNext (predicate : α → Result Bool) (collection : Collection κ α)
    (startAllowed : κ → Bool) : Result (Option κ) :=
  let rec go : List (κ × α) → Result (Option κ)
    | [] => .ok none
    | pair :: rest => if !startAllowed pair.1 then go rest else do
        if ← predicate pair.2 then .ok (some pair.1) else go rest
  go collection.entries

def identityPredicate (truth : α → Result Bool) := truth
def m2404 (truth : α → Result Bool) (collection : Collection κ α) (startAllowed : κ → Bool) :=
  findNext (identityPredicate truth) collection startAllowed
def P2404 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α) (startAllowed : κ → Bool),
  m2404 truth collection startAllowed = findNext (identityPredicate truth) collection startAllowed
theorem p2404 : P2404 := by simp [P2404, m2404]

def m2441 (truth : α → Result Bool) (collection : Collection κ α) :=
  findNext truth collection (fun _ => true)
def P2441 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α),
  m2441 truth collection = findNext truth collection (fun _ => true)
theorem p2441 : P2441 := by simp [P2441, m2441]
def m2444 := @m2441
def P2444 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α), m2444 truth collection = m2441 truth collection
theorem p2444 : P2444 := by simp [P2444, m2444]
def m2475 := @findNext
def P2475 : Prop := ∀ {κ α : Type} (predicate : α → Result Bool)
    (collection : Collection κ α) (startAllowed : κ → Bool),
  m2475 predicate collection startAllowed = findNext predicate collection startAllowed
theorem p2475 : P2475 := by simp [P2475, m2475]
def m2523 := @m2441
def P2523 : Prop := ∀ {κ α : Type} (predicate : α → Result Bool)
    (collection : Collection κ α), m2523 predicate collection = m2441 predicate collection
theorem p2523 : P2523 := by simp [P2523, m2523]
def m2531 := @m2441
def P2531 : Prop := ∀ {κ α : Type} (predicate : α → Result Bool)
    (collection : Collection κ α), m2531 predicate collection = m2441 predicate collection
theorem p2531 : P2531 := by simp [P2531, m2531]

def m2534 (target : Int) (range : List Int) : Option Int :=
  match range.findIdx? (fun value => value = target) with | some index => some (Int.ofNat index + 1) | none => none
def P2534 : Prop := ∀ target range, m2534 target range =
  match range.findIdx? (fun value => value = target) with | some index => some (Int.ofNat index + 1) | none => none
theorem p2534 : P2534 := by simp [P2534, m2534]
def m2538 (range : List Int) := m2534 1 range
def P2538 : Prop := ∀ range, m2538 range = m2534 1 range
theorem p2538 : P2538 := by simp [P2538, m2538]
def m2540 := m2534
def P2540 : Prop := ∀ target range, m2540 target range = m2534 target range
theorem p2540 : P2540 := by simp [P2540, m2540]

def findFirstList (predicate : α → Result Bool) : Nat → List α → Result (Option Nat)
  | _, [] => .ok none
  | index, head :: tail => do
      if ← predicate head then .ok (some index) else findFirstList predicate (index + 1) tail

def m2546 (equal : α → α → Result Bool) (target : α) (range : List α) : Result (Option Nat) :=
  findFirstList (equal target) 1 range
def P2546 : Prop := ∀ {α : Type} (equal : α → α → Result Bool) target range,
  m2546 equal target range = findFirstList (equal target) 1 range
theorem p2546 : P2546 := by simp [P2546, m2546]
def m2554 (range : List α) (iszero : α → Result Bool) := findFirstList iszero 1 range
def P2554 : Prop := ∀ {α : Type} range (iszero : α → Result Bool),
  m2554 range iszero = findFirstList iszero 1 range
theorem p2554 : P2554 := by simp [P2554, m2554]
def m2555 (range : List α) (isone : α → Result Bool) := findFirstList isone 1 range
def P2555 : Prop := ∀ {α : Type} range (isone : α → Result Bool),
  m2555 range isone = findFirstList isone 1 range
theorem p2555 : P2555 := by simp [P2555, m2555]

def findPrev (predicate : α → Result Bool) (collection : Collection κ α)
    (allowed : κ → Bool) : Result (Option κ) :=
  let rec go : List (κ × α) → Option κ → Result (Option κ)
    | [], found => .ok found
    | pair :: rest, found => if !allowed pair.1 then go rest found else do
        go rest (if ← predicate pair.2 then some pair.1 else found)
  go collection.entries none
def m2591 := @findPrev
def P2591 : Prop := ∀ {κ α : Type} (predicate : α → Result Bool)
    (collection : Collection κ α) (allowed : κ → Bool),
  m2591 predicate collection allowed = findPrev predicate collection allowed
theorem p2591 : P2591 := by simp [P2591, m2591]
def m2629 (truth : α → Result Bool) (collection : Collection κ α) := findPrev truth collection (fun _ => true)
def P2629 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α), m2629 truth collection = findPrev truth collection (fun _ => true)
theorem p2629 : P2629 := by simp [P2629, m2629]
def m2632 := @m2629
def P2632 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α), m2632 truth collection = m2629 truth collection
theorem p2632 : P2632 := by simp [P2632, m2632]
def m2671 := @findPrev
def P2671 : Prop := ∀ {κ α : Type} (predicate : α → Result Bool)
    (collection : Collection κ α) (allowed : κ → Bool),
  m2671 predicate collection allowed = findPrev predicate collection allowed
theorem p2671 : P2671 := by simp [P2671, m2671]
def m2716 := @m2629
def P2716 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α), m2716 truth collection = m2629 truth collection
theorem p2716 : P2716 := by simp [P2716, m2716]
def m2724 := @m2629
def P2724 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α), m2724 truth collection = m2629 truth collection
theorem p2724 : P2724 := by simp [P2724, m2724]
def m2728 (predicate : Int → Result Bool) (range : List Int) : Result (Option Nat) :=
  findFirstList predicate 1 range
def P2728 : Prop := ∀ predicate range, m2728 predicate range = findFirstList predicate 1 range
theorem p2728 : P2728 := by simp [P2728, m2728]
def m2733 := @m2728
def P2733 : Prop := ∀ predicate range, m2733 predicate range = m2728 predicate range
theorem p2733 : P2733 := by simp [P2733, m2733]

def findAll (predicate : α → Result Bool) (collection : Collection κ α) : Result (List κ) :=
  let rec go : List (κ × α) → Result (List κ)
    | [] => .ok []
    | pair :: rest => do
        let tail ← go rest
        pure (if ← predicate pair.2 then pair.1 :: tail else tail)
  go collection.entries
def m2789 := @findAll
def P2789 : Prop := ∀ {κ α : Type} (predicate : α → Result Bool)
    (collection : Collection κ α), m2789 predicate collection = findAll predicate collection
theorem p2789 : P2789 := by simp [P2789, m2789]
def m2796 := @findAll
def P2796 : Prop := ∀ {κ α : Type} (predicate : α → Result Bool)
    (collection : Collection κ α), m2796 predicate collection = findAll predicate collection
theorem p2796 : P2796 := by simp [P2796, m2796]
def m2838 (truth : α → Result Bool) (collection : Collection κ α) := findAll truth collection
def P2838 : Prop := ∀ {κ α : Type} (truth : α → Result Bool)
    (collection : Collection κ α), m2838 truth collection = findAll truth collection
theorem p2838 : P2838 := by simp [P2838, m2838]
def m2843 (collection : Collection κ Bool) := findAll (fun value => .ok value) collection
def P2843 : Prop := ∀ {κ : Type} (collection : Collection κ Bool),
  m2843 collection = findAll (fun value => .ok value) collection
theorem p2843 : P2843 := by simp [P2843, m2843]
def m2856 (value : Bool) : List Unit := if value then [()] else []
def P2856 : Prop := ∀ value, m2856 value = if value then [()] else []
theorem p2856 : P2856 := by simp [P2856, m2856]
def m2857 (predicate : α → Result Bool) (value : α) : Result (List Unit) := do
  pure (if ← predicate value then [()] else [])
def P2857 : Prop := ∀ {α : Type} (predicate : α → Result Bool) (value : α), m2857 predicate value = do
  pure (if ← predicate value then [()] else [])
theorem p2857 : P2857 := by simp [P2857, m2857]
def m2858 := @m2857
def P2858 : Prop := ∀ {α : Type} (predicate : α → Result Bool) (value : α),
  m2858 predicate value = m2857 predicate value
theorem p2858 : P2858 := by simp [P2858, m2858]

def indexIn (isequal : α → α → Bool) (queries values : List α) : List (Option Nat) :=
  queries.map fun query => (values.findIdx? (isequal query)).map (fun index => index + 1)
def m2892 := @indexIn
def P2892 : Prop := ∀ {α : Type} (isequal : α → α → Bool)
    (queries values : List α), m2892 isequal queries values = indexIn isequal queries values
theorem p2892 : P2892 := by simp [P2892, m2892]
def m2903 (membership : α → Bool) (entries : List (κ × α)) : List κ :=
  entries.filterMap fun pair => if membership pair.2 then some pair.1 else none
def P2903 : Prop := ∀ {κ α : Type} (membership : α → Bool) (entries : List (κ × α)),
  m2903 membership entries =
  entries.filterMap fun pair => if membership pair.2 then some pair.1 else none
theorem p2903 : P2903 := by simp [P2903, m2903]
def m2910 := @m2903
def P2910 : Prop := ∀ {κ α : Type} (membership : α → Bool) (entries : List (κ × α)),
  m2910 membership entries = m2903 membership entries
theorem p2910 : P2910 := by simp [P2910, m2910]
def m2915 := @indexIn
def P2915 : Prop := ∀ {α : Type} (isequal : α → α → Bool) (queries values : List α),
  m2915 isequal queries values = indexIn isequal queries values
theorem p2915 : P2915 := by simp [P2915, m2915]
def m2957 := @m2903
def P2957 : Prop := ∀ {κ α : Type} (membership : α → Bool) (entries : List (κ × α)),
  m2957 membership entries = m2903 membership entries
theorem p2957 : P2957 := by simp [P2957, m2957]
def m2966 := @m2903
def P2966 : Prop := ∀ {κ α : Type} (membership : α → Bool) (entries : List (κ × α)),
  m2966 membership entries = m2903 membership entries
theorem p2966 : P2966 := by simp [P2966, m2966]
def m2967 := @m2903
def P2967 : Prop := ∀ {κ α : Type} (membership : α → Bool) (entries : List (κ × α)),
  m2967 membership entries = m2903 membership entries
theorem p2967 : P2967 := by simp [P2967, m2967]

def m2970 (findin : List Int → List (Option Nat)) (sizes : List Nat) (indices : List Int) : List Nat :=
  let first := findin indices
  let second := findin indices
  List.zipWith (fun size pair => if pair.1.isSome && pair.2.isSome then size else 0) sizes (List.zip first second)
def P2970 : Prop := ∀ findin sizes indices,
  m2970 findin sizes indices =
    let first := findin indices; let second := findin indices
    List.zipWith (fun size pair => if pair.1.isSome && pair.2.isSome then size else 0) sizes (List.zip first second)
theorem p2970 : P2970 := by simp [P2970, m2970]
def m2981 := m2970
def P2981 : Prop := ∀ findin sizes indices, m2981 findin sizes indices = m2970 findin sizes indices
theorem p2981 : P2981 := by simp [P2981, m2981]

def filterArray (predicate : α → Result Bool) (array : ArrayState α) : Result (ArrayState α) := do
  let values ← assignedValues array
  let rec select : List α → Result (List α)
    | [] => .ok []
    | head :: tail => do
        let rest ← select tail
        pure (if ← predicate head then head :: rest else rest)
  pure (typedLiteral array.elementType (← select values))
def m3020 := @filterArray
def P3020 : Prop := ∀ {α : Type} (predicate : α → Result Bool) (array : ArrayState α),
  m3020 predicate array = filterArray predicate array
theorem p3020 : P3020 := by simp [P3020, m3020]
def m3066 (predicate : α → Result Bool) (array : ArrayState α) : Result (ArrayState α) := do
  let filtered ← filterArray predicate array
  pure { array with axes := filtered.axes, values := filtered.values }
def P3066 : Prop := ∀ {α : Type} (predicate : α → Result Bool) (array : ArrayState α),
  m3066 predicate array = do
  let filtered ← filterArray predicate array
  pure { array with axes := filtered.axes, values := filtered.values }
theorem p3066 : P3066 := by simp [P3066, m3066]
def m3105 (predicate : α → Result Bool) : List α → Result (List α) := fun values => do
  let filtered ← filterArray predicate (typedLiteral "Any" values)
  assignedValues filtered
def P3105 : Prop := ∀ {α : Type} (predicate : α → Result Bool) (values : List α),
  m3105 predicate values = do let filtered ← filterArray predicate (typedLiteral "Any" values); assignedValues filtered
theorem p3105 : P3105 := by simp [P3105, m3105]

def keepIndices (array : ArrayState α) (indices : List Int) : Result (ArrayState α) := do
  let values ← indices.mapM (fun (index : Int) =>
    if index < 1 || array.values.length < index then .error .bounds else .ok (array.values[(index - 1).toNat]?.getD none))
  pure { array with axes := oneToAxes [values.length], values }
def m3134 := @keepIndices
def P3134 : Prop := ∀ {α : Type} (array : ArrayState α) indices,
  m3134 array indices = keepIndices array indices
theorem p3134 : P3134 := by simp [P3134, m3134]
def m3159 (array : ArrayState α) (mask : List Bool) : Result (ArrayState α) :=
  if mask.length ≠ array.values.length then .error .bounds else
  let values := (array.values.zip mask).filterMap fun pair => if pair.2 then some pair.1 else none
  .ok { array with axes := oneToAxes [values.length], values := values }
def P3159 : Prop := ∀ {α : Type} (array : ArrayState α) mask, m3159 array mask =
  if mask.length ≠ array.values.length then .error .bounds else
  let values := (array.values.zip mask).filterMap fun pair => if pair.2 then some pair.1 else none
  .ok { array with axes := oneToAxes [values.length], values := values }
theorem p3159 : P3159 := by simp [P3159, m3159]

def uniqueFilter (predicate : α → σ → Bool) (update : α → σ → σ)
    (state : σ) (values : List α) : List α × σ :=
  values.foldl (fun pair value =>
    if predicate value pair.2 then (pair.1 ++ [value], update value pair.2) else pair) ([], state)
def m3164 := @uniqueFilter
def P3164 : Prop := ∀ {α σ : Type} (predicate : α → σ → Bool)
    (update : α → σ → σ) (state : σ) (values : List α),
  m3164 predicate update state values = uniqueFilter predicate update state values
theorem p3164 : P3164 := by simp [P3164, m3164]
def m3174 (contains : α → Bool) (value : α) := !contains value
def P3174 : Prop := ∀ {α : Type} contains (value : α), m3174 contains value = !contains value
theorem p3174 : P3174 := by simp [P3174, m3174]
def m3175 (keep : α → Bool) (value : α) := keep value
def P3175 : Prop := ∀ {α : Type} keep (value : α), m3175 keep value = keep value
theorem p3175 : P3175 := by simp [P3175, m3175]
def m3177 (predicate : α → σ → Bool) (update : α → σ → σ)
    (state : σ) (vector : List α) (iterables : List (List α)) :=
  uniqueFilter predicate update state (vector ++ iterables.flatten)
def P3177 : Prop := ∀ {α σ : Type} (predicate : α → σ → Bool)
    (update : α → σ → σ) (state : σ) (vector : List α)
    (iterables : List (List α)),
  m3177 predicate update state vector iterables = uniqueFilter predicate update state (vector ++ iterables.flatten)
theorem p3177 : P3177 := by simp [P3177, m3177]
def m3185 := @m3177
def P3185 : Prop := ∀ {α σ : Type} (predicate : α → σ → Bool)
    (update : α → σ → σ) (state : σ) (vector : List α)
    (iterables : List (List α)),
  m3185 predicate update state vector iterables = m3177 predicate update state vector iterables
theorem p3185 : P3185 := by simp [P3185, m3185]
def m3188 := @m3177
def P3188 : Prop := ∀ {α σ : Type} (predicate : α → σ → Bool)
    (update : α → σ → σ) (state : σ) (vector : List α)
    (iterables : List (List α)),
  m3188 predicate update state vector iterables = m3177 predicate update state vector iterables
theorem p3188 : P3188 := by simp [P3188, m3188]
def m3191 (keep : α → Bool) (vector : List α) := vector.filter keep
def P3191 : Prop := ∀ {α : Type} keep (vector : List α), m3191 keep vector = vector.filter keep
theorem p3191 : P3191 := by
  unfold P3191
  intros
  rfl
def m3198 := @m3191
def P3198 : Prop := ∀ {α : Type} keep (vector : List α), m3198 keep vector = vector.filter keep
theorem p3198 : P3198 := by
  unfold P3198
  intros
  rfl
def m3199 := @m3191
def P3199 : Prop := ∀ {α : Type} keep (vector : List α), m3199 keep vector = vector.filter keep
theorem p3199 : P3199 := by
  unfold P3199
  intros
  rfl

def vectorFilter (convert : α → Result β) (predicate : α → Result Bool) :
    List α → Result (List β)
  | [] => .ok []
  | head :: tail => do
      let rest ← vectorFilter convert predicate tail
      if ← predicate head then pure ((← convert head) :: rest) else pure rest
def m3201 := @vectorFilter
def P3201 : Prop :=
  (∀ {α β : Type} (convert : α → Result β) predicate,
    m3201 convert predicate [] = .ok []) ∧
  (∀ {α β : Type} (convert : α → Result β) predicate head tail,
    m3201 convert predicate (head :: tail) = do
      let rest ← m3201 convert predicate tail
      if ← predicate head then pure ((← convert head) :: rest) else pure rest)
theorem p3201 : P3201 := by simp [P3201, m3201, vectorFilter]
def stableUnique (equal : α → α → Bool) (values : List α) : List α :=
  values.foldl (fun output value => if output.any (equal value) then output else output ++ [value]) []

def m3203 (equal : α → α → Bool) (first : List α) (rest : List (List α)) : List α :=
  stableUnique equal (first.filter fun value => rest.all fun values => values.any (equal value))
def P3203 : Prop := ∀ {α : Type} (equal : α → α → Bool)
    (first : List α) (rest : List (List α)),
  m3203 equal first rest = stableUnique equal (first.filter fun value => rest.all fun values => values.any (equal value))
theorem p3203 : P3203 := by simp [P3203, m3203]
def m3209 (equal : α → α → Bool) (first : List α) (rest : List (List α)) : List α :=
  first.filter fun value => rest.all fun values => !values.any (equal value)
def P3209 : Prop := ∀ {α : Type} (equal : α → α → Bool)
    (first : List α) (rest : List (List α)),
  m3209 equal first rest = first.filter fun value => rest.all fun values => !values.any (equal value)
theorem p3209 : P3209 := by simp [P3209, m3209]
def m3215 (equal : α → α → Bool) (vector range : List α) : List α :=
  stableUnique equal (vector.filter fun value => range.any (equal value))
def P3215 : Prop := ∀ {α : Type} (equal : α → α → Bool)
    (vector range : List α),
  m3215 equal vector range = stableUnique equal (vector.filter fun value => range.any (equal value))
theorem p3215 : P3215 := by simp [P3215, m3215]
def m3221 := @m3215
def P3221 : Prop := ∀ {α : Type} (equal : α → α → Bool)
    (vector range : List α), m3221 equal vector range = m3215 equal vector range
theorem p3221 : P3221 := by simp [P3221, m3221]

structure IntegerValue where value : Int deriving Repr, DecidableEq

def m3224 [Inhabited α] (values : List α) (convert : IntegerValue → Result Int)
    (index : IntegerValue) : Result α := do
  let converted ← convert index
  if converted < 1 || values.length < converted then .error .bounds else .ok (values.getD (converted - 1).toNat values.head!)
def P3224 : Prop := ∀ {α : Type} [Inhabited α] (values : List α)
    (convert : IntegerValue → Result Int) index,
  m3224 values convert index = do
    let converted ← convert index
    if converted < 1 || values.length < converted then .error .bounds else .ok (values.getD (converted - 1).toNat values.head!)
theorem p3224 : P3224 := by simp [P3224, m3224]

structure MemoryState (α : Type) where
  values : List α
  offset : Nat
  id : Nat
  deriving Repr, DecidableEq
def m3241 (memory : MemoryState α) (dims : List Int) : Result (ArrayState α) :=
  let product := dims.foldl (fun n dim => n * dim) 1
  if dims.any (fun dim => dim < 0) || product.toNat + memory.offset > memory.values.length then .error .bounds
  else
    let values := ((memory.values.drop memory.offset).take product.toNat).map some
    .ok { elementType := "T", axes := oneToAxes (dims.map Int.toNat), values, id := memory.id }
def P3241 : Prop := ∀ {α : Type} (memory : MemoryState α) dims,
  m3241 memory dims =
    let product := dims.foldl (fun n dim => n * dim) 1
    if dims.any (fun dim => dim < 0) || product.toNat + memory.offset > memory.values.length then .error .bounds
    else let values := ((memory.values.drop memory.offset).take product.toNat).map some
      .ok { elementType := "T", axes := oneToAxes (dims.map Int.toNat), values, id := memory.id }
theorem p3241 : P3241 := by simp [P3241, m3241]
def m3249 (length : Nat) (dims : List Int) (product : Int) : String :=
  "invalid Array dimensions " ++ toString dims ++ " for memory length " ++ toString length ++ " product " ++ toString product
def P3249 : Prop := ∀ length dims product, m3249 length dims product =
  "invalid Array dimensions " ++ toString dims ++ " for memory length " ++ toString length ++ " product " ++ toString product
theorem p3249 : P3249 := by simp [P3249, m3249]
def m3254 := @m3241
def P3254 : Prop := ∀ {α : Type} (memory : MemoryState α) dims,
  m3254 memory dims = m3241 memory dims
theorem p3254 : P3254 := by simp [P3254, m3254]
def m3260 (memory : MemoryState α) dims := m3241 { memory with offset := 0 } dims
def P3260 : Prop := ∀ {α : Type} (memory : MemoryState α) dims,
  m3260 memory dims = m3241 { memory with offset := 0 } dims
theorem p3260 : P3260 := by simp [P3260, m3260]
def m3265 (memory : MemoryState α) (convert : IntegerValue → Result Int) length := do
  m3241 memory [← convert length]
def P3265 : Prop := ∀ {α : Type} (memory : MemoryState α)
    (convert : IntegerValue → Result Int) (length : IntegerValue), m3265 memory convert length = do
  m3241 memory [← convert length]
theorem p3265 : P3265 := by simp [P3265, m3265]
def m3270 (memory : MemoryState α) (length : IntegerValue) : Result (ArrayState α) :=
  if length.value < 0 || memory.values.length < length.value then .error .typeError else
  m3241 { memory with offset := 0 } [length.value]
def P3270 : Prop := ∀ {α : Type} (memory : MemoryState α) (length : IntegerValue), m3270 memory length =
  if length.value < 0 || memory.values.length < length.value then .error .typeError else
  m3241 { memory with offset := 0 } [length.value]
theorem p3270 : P3270 := by simp [P3270, m3270]
def m3275 (memory : MemoryState α) := m3241 { memory with offset := 0 } [Int.ofNat memory.values.length]
def P3275 : Prop := ∀ {α : Type} (memory : MemoryState α),
  m3275 memory = m3241 { memory with offset := 0 } [Int.ofNat memory.values.length]
theorem p3275 : P3275 := by simp [P3275, m3275]

private def entry (id : String) (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := [name],
    statement, source := s!"base/array.jl:{line}; search, filtering, set, and wrapping source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.ArrayFindSetFaithful
