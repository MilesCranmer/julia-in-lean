import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

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
