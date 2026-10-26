import JuliaLean.Core

namespace JuliaLean.ArrayCov

inductive CollectSize where
  | unknown | length | shape
  deriving Repr, DecidableEq

def array771Collect (iteratorEltype : List Int → Int)
    (iteratorSize : List Int → CollectSize)
    (collect : Int → List Int → Int → CollectSize → Jl (List Int))
    (iterator : List Int) : Jl (List Int) :=
  collect 1 iterator (iteratorEltype iterator) (iteratorSize iterator)

def array773CollectArray (axes : List Int → List Int)
    (collectIndices : List Int → List Int → Jl (List Int))
    (array : List Int) : Jl (List Int) := collectIndices (axes array) array

def array775CollectSimilar (iteratorEltype : List Int → Int)
    (iteratorSize : List Int → CollectSize)
    (collect : Int → List Int → Int → CollectSize → Jl (List Int))
    (container : Int) (iterator : List Int) : Jl (List Int) :=
  collect container iterator (iteratorEltype iterator) (iteratorSize iterator)

def array777CollectSized (eltype : List Int → Int)
    (similarShape : List Int → CollectSize → Int)
    (similarFor : Int → Int → List Int → CollectSize → Int → Jl (List Int))
    (copyto : List Int → List Int → Jl (List Int))
    (container : Int) (iterator : List Int) (size : CollectSize) : Jl (List Int) := do
  let dest ← similarFor container (eltype iterator) iterator size (similarShape iterator size)
  copyto dest iterator

def array780CollectUnknown (eltype : List Int → Int)
    (similarFor : Int → Int → List Int → Jl (List Int))
    (push : List Int → Int → Jl (List Int))
    (container : Int) (iterator : List Int) : Jl (List Int) := do
  let dest ← similarFor container (eltype iterator) iterator
  iterator.foldlM push dest

def array788CollectZero (eltype : List Int → Int) (allocate : Int → Jl (List Int))
    (copy : List Int → List Int → Jl (List Int)) (array : List Int) : Jl (List Int) := do
  let dest ← allocate (eltype array)
  if array.isEmpty then return dest
  copy dest array

def array793CollectOneTo (eltype : List Int → Int)
    (lengths : List Int → List Int) (allocate : Int → List Int → Jl (List Int))
    (copy : List Int → List Int → Jl (List Int))
    (indices array : List Int) : Jl (List Int) := do
  let dest ← allocate (eltype array) (lengths indices)
  if array.isEmpty then return dest
  copy dest array

def array798CollectIndices (eltype : List Int → Int)
    (lengths : List Int → List Int) (allocate : Int → List Int → Jl (List Int))
    (axes cartesian : List Int → List Int)
    (copy : List Int → List Int → List Int → List Int → Jl (List Int))
    (indices array : List Int) : Jl (List Int) := do
  let dest ← allocate (eltype array) (lengths indices)
  copy dest (cartesian (axes dest)) array (cartesian indices)

def ArrayCollectRoutesCorrect : Prop :=
  (∀ et size collect iter, array771Collect et size collect iter =
      collect 1 iter (et iter) (size iter)) ∧
  (∀ axes collect array, array773CollectArray axes collect array = collect (axes array) array) ∧
  (∀ et size collect container iter, array775CollectSimilar et size collect container iter =
      collect container iter (et iter) (size iter)) ∧
  (∀ et shape similar copy container iter size,
      array777CollectSized et shape similar copy container iter size = do
      let dest ← similar container (et iter) iter size (shape iter size)
      copy dest iter) ∧
  (∀ et similar push container iter,
      array780CollectUnknown et similar push container iter = do
      let dest ← similar container (et iter) iter
      iter.foldlM push dest) ∧
  (∀ et allocate copy array, array788CollectZero et allocate copy array = do
      let dest ← allocate (et array)
      if array.isEmpty then return dest
      copy dest array) ∧
  (∀ et lengths allocate copy indices array,
      array793CollectOneTo et lengths allocate copy indices array = do
      let dest ← allocate (et array) (lengths indices)
      if array.isEmpty then return dest
      copy dest array) ∧
  (∀ et lengths allocate axes cart copy indices array,
      array798CollectIndices et lengths allocate axes cart copy indices array = do
      let dest ← allocate (et array) (lengths indices)
      copy dest (cart (axes dest)) array (cart indices))

theorem arrayCollectRoutesCorrect : ArrayCollectRoutesCorrect := by
  simp [ArrayCollectRoutesCorrect, array771Collect, array773CollectArray,
    array775CollectSimilar, array777CollectSized, array780CollectUnknown,
    array788CollectZero, array793CollectOneTo, array798CollectIndices]

def array805IteratorUpperLoop (iterateNext : Int → Option (Int × Int))
    (barrier : Unit → Bool) : Nat → Option (Int × Int) → Except Unit Int
  | 0, _ => .error ()
  | _ + 1, none => .error ()
  | fuel + 1, some (value, state) =>
      if barrier () then .ok value
      else array805IteratorUpperLoop iterateNext barrier fuel (iterateNext state)

def array805IteratorUpper (iterateFirst : Unit → Option (Int × Int))
    (iterateNext : Int → Option (Int × Int)) (barrier : Unit → Bool)
    (fuel : Nat) : Except Unit Int :=
  array805IteratorUpperLoop iterateNext barrier fuel (iterateFirst ())

def array821DefaultEltype (isGenerator : Int → Bool) (functionIsType : Int → Bool)
    (generatorFunction : Int → Int) (returnType : Int → Int)
    (promoteUnion : Int → Int) (iterator : Int) : Int :=
  let type := if isGenerator iterator && functionIsType iterator then
    generatorFunction iterator else returnType iterator
  promoteUnion type

def ArrayIteratorTypeCorrect : Prop :=
  (∀ first next barrier fuel, array805IteratorUpper first next barrier fuel =
      array805IteratorUpperLoop next barrier fuel (first ())) ∧
  (∀ generator isType fn ret promote iterator,
      array821DefaultEltype generator isType fn ret promote iterator =
      promote (if generator iterator && isType iterator then fn iterator else ret iterator))

theorem arrayIteratorTypeCorrect : ArrayIteratorTypeCorrect := by
  simp [ArrayIteratorTypeCorrect, array805IteratorUpper, array821DefaultEltype]

def array833CollectGenerator (iteratorSize : Int → CollectSize)
    (defaultEltype : Int → Int) (grow : Int → Int → Jl Int)
    (similarShape : Int → CollectSize → Int)
    (iterate : Int → Option (Int × Int))
    (arrayFor : Int → CollectSize → Int → Jl Int)
    (collectFirst : Int → Int → Int → Int → Jl Int)
    (iterator : Int) : Jl Int := do
  let size := iteratorSize iterator
  let elementType := defaultEltype iterator
  if size = .unknown then return ← grow elementType iterator
  let shape := similarShape iterator size
  match iterate iterator with
  | none => arrayFor elementType size shape
  | some (first, state) => do
      let dest ← arrayFor first size shape
      collectFirst dest first iterator state

def array855CollectUnknownEltype (defaultEltype : Int → Int)
    (similar : Int → Int → Int → Jl Int) (grow : Int → Int → Jl Int)
    (container iterator : Int) : Jl Int := do
  let dest ← similar container (defaultEltype iterator) iterator
  grow dest iterator

def array858CollectKnownSize (defaultEltype : Int → Int)
    (similarShape : Int → CollectSize → Int)
    (iterate : Int → Option (Int × Int))
    (similar : Int → Int → Int → CollectSize → Int → Jl Int)
    (collectFirst : Int → Int → Int → Int → Jl Int)
    (container iterator : Int) (size : CollectSize) : Jl Int := do
  let elementType := defaultEltype iterator
  let shape := similarShape iterator size
  match iterate iterator with
  | none => similar container elementType iterator size shape
  | some (first, state) => do
      let dest ← similar container first iterator size shape
      collectFirst dest first iterator state

def ArrayGeneratorCollectCorrect : Prop :=
  (∀ size et grow shape iterate allocate collect iterator,
      array833CollectGenerator size et grow shape iterate allocate collect iterator = do
      let isz := size iterator
      let elementType := et iterator
      if isz = .unknown then return ← grow elementType iterator
      let shp := shape iterator isz
      match iterate iterator with
      | none => allocate elementType isz shp
      | some (first, state) => do
          let dest ← allocate first isz shp
          collect dest first iterator state) ∧
  (∀ et similar grow container iterator,
      array855CollectUnknownEltype et similar grow container iterator = do
      let dest ← similar container (et iterator) iterator
      grow dest iterator) ∧
  (∀ et shape iterate similar collect container iterator size,
      array858CollectKnownSize et shape iterate similar collect container iterator size = do
      let elementType := et iterator
      let shp := shape iterator size
      match iterate iterator with
      | none => similar container elementType iterator size shp
      | some (first, state) => do
          let dest ← similar container first iterator size shp
          collect dest first iterator state)

theorem arrayGeneratorCollectCorrect : ArrayGeneratorCollectCorrect := by
  simp [ArrayGeneratorCollectCorrect, array833CollectGenerator,
    array855CollectUnknownEltype, array858CollectKnownSize]

def array875CollectFirstArray (firstLinear : Int → Int)
    (setindex : Int → Int → Int → Int) (collectTo : Int → Int → Int → Int → Int)
    (dest first iterator state : Int) : Int :=
  let index := firstLinear dest
  collectTo (setindex dest index first) iterator (index + 1) state

def array881CollectFirstGeneric (push : Int → Int → Int)
    (grow : Int → Int → Int → Int) (dest first iterator state : Int) : Int :=
  grow (push dest first) iterator state

def array886Widen (promote : Int → Int → Int) (similar : Int → Int → Int)
    (firstLinear : Int → Int) (copy : Int → Int → Int → Int → Int → Int)
    (setindex : Int → Int → Int → Int) (dest element : Int) (index : Int) : Int :=
  let new := similar dest (promote dest element)
  let first := firstLinear dest
  let new := copy new (firstLinear new) dest first (index - first)
  setindex new index element

def ArrayCollectFirstWidenCorrect : Prop :=
  (∀ first set collect dest value iterator state,
      array875CollectFirstArray first set collect dest value iterator state =
      let index := first dest
      collect (set dest index value) iterator (index + 1) state) ∧
  (∀ push grow dest value iterator state,
      array881CollectFirstGeneric push grow dest value iterator state =
      grow (push dest value) iterator state) ∧
  (∀ promote similar first copy set dest element index,
      array886Widen promote similar first copy set dest element index =
      let new := similar dest (promote dest element)
      let start := first dest
      let new := copy new (first new) dest start (index - start)
      set new index element)

theorem arrayCollectFirstWidenCorrect : ArrayCollectFirstWidenCorrect := by
  simp [ArrayCollectFirstWidenCorrect, array875CollectFirstArray,
    array881CollectFirstGeneric, array886Widen]

def array895CollectToLoop (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Bool) (setindex : Int → Int → Int → Int)
    (widen : Int → Int → Int → Int) (recurse : Int → Int → Int → Int → Int) :
    Int → Int → Int → Int → Nat → Int
  | dest, _iterator, _index, _state, 0 => dest
  | dest, iterator, index, state, fuel + 1 =>
      match iterate iterator state with
      | none => dest
      | some (element, nextState) =>
          if isType element then
            array895CollectToLoop iterate isType setindex widen recurse
              (setindex dest index element) iterator (index + 1) nextState fuel
          else recurse (widen dest element index) iterator (index + 1) nextState

def array895CollectTo (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Bool) (setindex : Int → Int → Int → Int)
    (widen : Int → Int → Int → Int) (recurse : Int → Int → Int → Int → Int)
    (dest iterator offset state : Int) (fuel : Nat) : Int :=
  array895CollectToLoop iterate isType setindex widen recurse dest iterator offset state fuel

def array914GrowFirst (iterate : Int → Option (Int × Int))
    (empty : Int → Int → Int) (push : Int → Int → Int)
    (grow : Int → Int → Int → Int) (dest iterator : Int) : Int :=
  match iterate iterator with
  | none => dest
  | some (first, state) => grow (push (empty dest first) first) iterator state

def array922PushWiden (promote : Int → Int → Int) (empty : Int → Int → Int)
    (sizehint : Int → Int → Int) (isSet : Int → Bool)
    (union append : Int → Int → Int) (push : Int → Int → Int)
    (eltype length : Int → Int) (dest element : Int) : Int :=
  let new := sizehint (empty dest (promote (eltype dest) element)) (length dest)
  let new := if isSet new then union new dest else append new dest
  push new element

def array935GrowLoop (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Bool) (push : Int → Int → Int)
    (widen : Int → Int → Int) (recurse : Int → Int → Int → Int) :
    Int → Int → Int → Nat → Int
  | dest, _iterator, _state, 0 => dest
  | dest, iterator, state, fuel + 1 =>
      match iterate iterator state with
      | none => dest
      | some (element, nextState) =>
          if isType element then
            array935GrowLoop iterate isType push widen recurse
              (push dest element) iterator nextState fuel
          else recurse (widen dest element) iterator nextState

def array935GrowTo (iterate : Int → Int → Option (Int × Int))
    (isType : Int → Bool) (push : Int → Int → Int)
    (widen : Int → Int → Int) (recurse : Int → Int → Int → Int)
    (dest iterator state : Int) (fuel : Nat) : Int :=
  array935GrowLoop iterate isType push widen recurse dest iterator state fuel

def ArrayCollectLoopsCorrect : Prop :=
  (∀ iterate type set widen recurse dest iterator offset state fuel,
      array895CollectTo iterate type set widen recurse dest iterator offset state fuel =
      array895CollectToLoop iterate type set widen recurse dest iterator offset state fuel) ∧
  (∀ iterate empty push grow dest iterator, array914GrowFirst iterate empty push grow dest iterator =
      match iterate iterator with
      | none => dest
      | some (first, state) => grow (push (empty dest first) first) iterator state) ∧
  (∀ promote empty hint isSet union append push eltype length dest element,
      array922PushWiden promote empty hint isSet union append push eltype length dest element =
      let new := hint (empty dest (promote (eltype dest) element)) (length dest)
      let new := if isSet new then union new dest else append new dest
      push new element) ∧
  (∀ iterate type push widen recurse dest iterator state fuel,
      array935GrowTo iterate type push widen recurse dest iterator state fuel =
      array935GrowLoop iterate type push widen recurse dest iterator state fuel)

theorem arrayCollectLoopsCorrect : ArrayCollectLoopsCorrect := by
  simp [ArrayCollectLoopsCorrect, array895CollectTo, array914GrowFirst,
    array922PushWiden, array935GrowTo]

end JuliaLean.ArrayCov
