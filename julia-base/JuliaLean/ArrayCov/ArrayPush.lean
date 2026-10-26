import JuliaLean.Core

namespace JuliaLean.ArrayCov

def array1114NewMemory (allocateLike : List Int → Int → Jl (List Int))
    (memory : List Int) (newLength : Int) : Jl (List Int) :=
  allocateLike memory newLength

def array1358Push (sameType : Int → Bool) (convert : Int → Jl Int)
    (pushTyped : List Int → Int → Jl (List Int))
    (array : List Int) (item : Int) : Jl (List Int) := do
  let item ← if sameType item then pure item else convert item
  pushTyped array item

def array1366PushTyped (growEnd : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array : List Int) (item : Int) : Jl (List Int) := do
  let array ← growEnd array 1
  pure (safeSet array array.length item)

def array1373PushAny := array1366PushTyped

def array1378PushAnyLoop (safeSet : List Int → Nat → Int → List Int) :
    List Int → Nat → List Int → List Int
  | array, _, [] => array
  | array, index, item :: rest =>
      array1378PushAnyLoop safeSet (safeSet array index item) (index + 1) rest

def array1378PushAnyMany (growEnd : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array items : List Int) : Jl (List Int) := do
  let oldLength := array.length
  let array ← growEnd array items.length
  pure (array1378PushAnyLoop safeSet array (oldLength + 1) items)

def ArrayPushCorrect : Prop :=
  (∀ allocate memory length, array1114NewMemory allocate memory length = allocate memory length) ∧
  (∀ same convert push array item, array1358Push same convert push array item = do
      let item ← if same item then pure item else convert item
      push array item) ∧
  (∀ grow set array item, array1366PushTyped grow set array item = do
      let array ← grow array 1
      pure (set array array.length item)) ∧
  (∀ grow set array item, array1373PushAny grow set array item = do
      let array ← grow array 1
      pure (set array array.length item)) ∧
  (∀ grow set array items, array1378PushAnyMany grow set array items = do
      let oldLength := array.length
      let array ← grow array items.length
      pure (array1378PushAnyLoop set array (oldLength + 1) items))

theorem arrayPushCorrect : ArrayPushCorrect := by
  simp [ArrayPushCorrect, array1114NewMemory, array1358Push, array1366PushTyped,
    array1373PushAny, array1378PushAnyMany]

def array1427Append (isTuple sameObject : Bool) (convertAll : List Int → Jl (List Int))
    (convertLength : Nat → Jl Int) (growEnd : List Int → Int → Jl (List Int))
    (copyto : List Int → Int → List Int → Int → Int → Jl (List Int))
    (array items : List Int) : Jl (List Int) := do
  let items ← if isTuple then convertAll items else pure items
  let count ← convertLength items.length
  let array ← growEnd array count
  let source := if sameObject && !isTuple then array else items
  copyto array (array.length - count + 1) source 1 count

def array1435AppendIterator (iteratorSize : List Int → Int)
    (appendInner : List Int → Int → List Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) :=
  appendInner array (iteratorSize iterator) iterator

def array1436PushMany (append : List Int → List Int → Jl (List Int))
    (array items : List Int) : Jl (List Int) := append array items

def array1437AppendManyLoop (append : List Int → List Int → Jl (List Int)) :
    List Int → List (List Int) → Jl (List Int)
  | array, [] => .ok array
  | array, items :: rest => do
      let array ← append array items
      array1437AppendManyLoop append array rest

def array1439AppendSized (convertLength : Nat → Jl Int)
    (sizehint : List Int → Int → Bool → Jl (List Int))
    (push : List Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := do
  let count ← convertLength iterator.length
  let array ← sizehint array (array.length + count) false
  iterator.foldlM push array

def array1447AppendUnknown (push : List Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := iterator.foldlM push array

def ArrayAppendCorrect : Prop :=
  (∀ tuple same convert convLen grow copy array items,
      array1427Append tuple same convert convLen grow copy array items = do
      let items ← if tuple then convert items else pure items
      let count ← convLen items.length
      let array ← grow array count
      let source := if same && !tuple then array else items
      copy array (array.length - count + 1) source 1 count) ∧
  (∀ size inner array iter, array1435AppendIterator size inner array iter =
      inner array (size iter) iter) ∧
  (∀ append array items, array1436PushMany append array items = append array items) ∧
  (∀ append array collections, array1437AppendManyLoop append array collections =
      collections.foldlM append array) ∧
  (∀ conv hint push array iter, array1439AppendSized conv hint push array iter = do
      let count ← conv iter.length
      let array ← hint array (array.length + count) false
      iter.foldlM push array) ∧
  (∀ push array iter, array1447AppendUnknown push array iter = iter.foldlM push array)

theorem arrayAppendCorrect : ArrayAppendCorrect := by
  simp [ArrayAppendCorrect, array1427Append, array1435AppendIterator,
    array1436PushMany, array1439AppendSized, array1447AppendUnknown]
  intro append array collections
  induction collections generalizing array with
  | nil => rfl
  | cons items rest ih => simp [array1437AppendManyLoop, List.foldlM, ih]

def array1485Prepend (isTuple sameObject : Bool)
    (convertAll : List Int → Jl (List Int))
    (unalias : List Int → List Int → List Int)
    (growBegin : List Int → Nat → Jl (List Int))
    (copyto : List Int → Int → List Int → Int → Nat → Jl (List Int))
    (array items : List Int) : Jl (List Int) := do
  let items ← if isTuple then convertAll items
    else pure (if sameObject then items else unalias array items)
  let count := items.length
  let array ← growBegin array count
  let source := if sameObject && !isTuple then array else items
  copyto array 1 source (source.length - count + 1) count

def array1500PrependIterator (iteratorSize : List Int → Int)
    (prependInner : List Int → Int → List Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) :=
  prependInner array (iteratorSize iterator) iterator

def array1501PushFirstMany (prepend : List Int → List Int → Jl (List Int))
    (array items : List Int) : Jl (List Int) := prepend array items

def array1502PrependForward (prepend : List Int → List Int → Jl (List Int)) :
    List Int → List (List Int) → Jl (List Int)
  | array, [] => .ok array
  | array, items :: rest => do
      let array ← prepend array items
      array1502PrependForward prepend array rest

def array1502PrependManyLoop (prepend : List Int → List Int → Jl (List Int))
    (array : List Int) (collections : List (List Int)) : Jl (List Int) :=
  array1502PrependForward prepend array collections.reverse

def array1504PrependSized (oneBased : List Int → Jl Unit)
    (convertLength : Nat → Jl Int)
    (sizehint : List Int → Int → Bool → Bool → Jl (List Int))
    (pushFirst : List Int → Int → Jl (List Int))
    (reverse : List Int → Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := do
  oneBased array
  let count ← convertLength iterator.length
  let array ← sizehint array (array.length + count) true false
  let (array, inserted) ← iterator.foldlM (fun (state : List Int × Int) item => do
    let array ← pushFirst state.1 item
    pure (array, state.2 + 1)) (array, 0)
  reverse array 1 inserted

def array1517PrependUnknown (pushFirst : List Int → Int → Jl (List Int))
    (reverse : List Int → Int → Int → Jl (List Int))
    (array iterator : List Int) : Jl (List Int) := do
  let (array, inserted) ← iterator.foldlM (fun (state : List Int × Int) item => do
    let array ← pushFirst state.1 item
    pure (array, state.2 + 1)) (array, 0)
  reverse array 1 inserted

def ArrayPrependCorrect : Prop :=
  (∀ tuple same convert unalias grow copy array items,
      array1485Prepend tuple same convert unalias grow copy array items = do
      let items ← if tuple then convert items else pure (if same then items else unalias array items)
      let count := items.length
      let array ← grow array count
      let source := if same && !tuple then array else items
      copy array 1 source (source.length - count + 1) count) ∧
  (∀ size inner array iter, array1500PrependIterator size inner array iter =
      inner array (size iter) iter) ∧
  (∀ prepend array items, array1501PushFirstMany prepend array items = prepend array items) ∧
  (∀ prepend array collections, array1502PrependManyLoop prepend array collections =
      array1502PrependForward prepend array collections.reverse) ∧
  (∀ oneBased conv hint push reverse array iter,
      array1504PrependSized oneBased conv hint push reverse array iter = do
      oneBased array
      let count ← conv iter.length
      let array ← hint array (array.length + count) true false
      let (array, inserted) ← iter.foldlM (fun (state : List Int × Int) item => do
        let array ← push state.1 item
        pure (array, state.2 + 1)) (array, 0)
      reverse array 1 inserted) ∧
  (∀ push reverse array iter, array1517PrependUnknown push reverse array iter = do
      let (array, inserted) ← iter.foldlM (fun (state : List Int × Int) item => do
        let array ← push state.1 item
        pure (array, state.2 + 1)) (array, 0)
      reverse array 1 inserted)

theorem arrayPrependCorrect : ArrayPrependCorrect := by
  simp [ArrayPrependCorrect, array1485Prepend, array1500PrependIterator,
    array1501PushFirstMany, array1502PrependManyLoop,
    array1504PrependSized, array1517PrependUnknown]

def array1777PushFirst (sameType : Int → Bool) (convert : Int → Jl Int)
    (pushTyped : List Int → Int → Jl (List Int))
    (array : List Int) (item : Int) : Jl (List Int) := do
  let item ← if sameType item then pure item else convert item
  pushTyped array item

def array1782PushFirstTyped (growBegin : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array : List Int) (item : Int) : Jl (List Int) := do
  let array ← growBegin array 1
  pure (safeSet array 1 item)

def array1789PushFirstAny := array1782PushFirstTyped

def array1794PushFirstMany (growBegin : List Int → Nat → Jl (List Int))
    (safeSet : List Int → Nat → Int → List Int)
    (array items : List Int) : Jl (List Int) := do
  let array ← growBegin array items.length
  pure (array1378PushAnyLoop safeSet array 1 items)

def array1866Insert (sameType : Int → Bool) (convert : Int → Jl Int)
    (insertTyped : List Int → Int → Int → Jl (List Int))
    (array : List Int) (index item : Int) : Jl (List Int) := do
  let item ← if sameType item then pure item else convert item
  insertTyped array index item

def array1871InsertTyped (growAt : List Int → Int → Nat → Jl (List Int))
    (setindex : List Int → Int → Int → List Int)
    (array : List Int) (index item : Int) : Jl (List Int) := do
  let array ← growAt array index 1
  pure (setindex array index item)

def ArrayPushFirstInsertCorrect : Prop :=
  (∀ same convert push array item, array1777PushFirst same convert push array item = do
      let item ← if same item then pure item else convert item
      push array item) ∧
  (∀ grow set array item, array1782PushFirstTyped grow set array item = do
      let array ← grow array 1; pure (set array 1 item)) ∧
  (∀ grow set array item, array1789PushFirstAny grow set array item = do
      let array ← grow array 1; pure (set array 1 item)) ∧
  (∀ grow set array items, array1794PushFirstMany grow set array items = do
      let array ← grow array items.length
      pure (array1378PushAnyLoop set array 1 items)) ∧
  (∀ same convert insert array index item, array1866Insert same convert insert array index item = do
      let item ← if same item then pure item else convert item
      insert array index item) ∧
  (∀ grow set array index item, array1871InsertTyped grow set array index item = do
      let array ← grow array index 1
      pure (set array index item))

theorem arrayPushFirstInsertCorrect : ArrayPushFirstInsertCorrect := by
  simp [ArrayPushFirstInsertCorrect, array1777PushFirst, array1782PushFirstTyped,
    array1789PushFirstAny, array1794PushFirstMany, array1866Insert,
    array1871InsertTyped]

end JuliaLean.ArrayCov
