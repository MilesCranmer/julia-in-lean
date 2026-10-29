import JuliaLean.MultidimCov.ArrayCollectIndexFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayVectorFaithful

open JuliaLean.Registry
open ArrayFaithfulCore

def resizeValues (values : List (Option α)) (length : Nat) (first : Bool) : List (Option α) :=
  if length ≤ values.length then if first then values.drop (values.length - length) else values.take length
  else if first then List.replicate (length - values.length) none ++ values
  else values ++ List.replicate (length - values.length) none

def m1102 (maxsize : Int) (wordBits : Nat) : Int :=
  let maxint := Int.ofNat (2 ^ (wordBits - 1) - 1)
  min maxint (maxsize + maxsize / 8 + 4)
def P1102 : Prop := ∀ maxsize wordBits, m1102 maxsize wordBits =
  let maxint := Int.ofNat (2 ^ (wordBits - 1) - 1); min maxint (maxsize + maxsize / 8 + 4)
theorem p1102 : P1102 := by simp [P1102, m1102]

def m1114 (array : ArrayState α) (newLength : Nat) : ArrayState α :=
  { array with axes := oneToAxes [newLength], values := resizeValues array.values newLength false }
def P1114 : Prop := ∀ {α : Type} (array : ArrayState α) newLength,
  (m1114 array newLength).values = resizeValues array.values newLength false
theorem p1114 : P1114 := by simp [P1114, m1114]

def m1116 (array : ArrayState α) (delta length : Nat) : ArrayState α :=
  { array with axes := oneToAxes [length + delta], values := List.replicate delta none ++ array.values.take length }
def P1116 : Prop := ∀ {α : Type} (array : ArrayState α) delta length,
  (m1116 array delta length).values = List.replicate delta none ++ array.values.take length
theorem p1116 : P1116 := by simp [P1116, m1116]

def m1151 (array : ArrayState α) (delta : Int) : Result (ArrayState α) :=
  if delta < 0 then .error .argument else .ok (m1116 array delta.toNat array.values.length)
def P1151 : Prop := ∀ {α : Type} (array : ArrayState α) delta,
  m1151 array delta = if delta < 0 then .error .argument else .ok (m1116 array delta.toNat array.values.length)
theorem p1151 : P1151 := by simp [P1151, m1151]

def m1171 (array : ArrayState α) (delta length : Nat) : ArrayState α :=
  { array with axes := oneToAxes [length + delta], values := array.values.take length ++ List.replicate delta none }
def P1171 : Prop := ∀ {α : Type} (array : ArrayState α) delta length,
  (m1171 array delta length).values = array.values.take length ++ List.replicate delta none
theorem p1171 : P1171 := by simp [P1171, m1171]

def m1212 (array : ArrayState α) (delta : Int) : Result (ArrayState α) :=
  if delta < 0 then .error .argument else .ok (m1171 array delta.toNat array.values.length)
def P1212 : Prop := ∀ {α : Type} (array : ArrayState α) delta,
  m1212 array delta = if delta < 0 then .error .argument else .ok (m1171 array delta.toNat array.values.length)
theorem p1212 : P1212 := by simp [P1212, m1212]

def m1230 (array : ArrayState α) (index delta : Int) : Result (ArrayState α) :=
  if index < 1 || array.values.length + 1 < index || delta < 0 then .error .bounds else
  let position := (index - 1).toNat
  let values := array.values.take position ++ List.replicate delta.toNat none ++ array.values.drop position
  .ok { array with axes := oneToAxes [array.values.length + delta.toNat], values := values }
def P1230 : Prop := ∀ {α : Type} (array : ArrayState α) index delta, m1230 array index delta =
  if index < 1 || array.values.length + 1 < index || delta < 0 then .error .bounds else
  let position := (index - 1).toNat
  let values := array.values.take position ++ List.replicate delta.toNat none ++ array.values.drop position
  .ok { array with axes := oneToAxes [array.values.length + delta.toNat], values := values }
theorem p1230 : P1230 := by simp [P1230, m1230]

def m1278 (array : ArrayState α) (delta : Int) : Result (ArrayState α) :=
  if delta < 0 || array.values.length < delta then .error .bounds else
  .ok { array with axes := oneToAxes [array.values.length - delta.toNat], values := array.values.drop delta.toNat }
def P1278 : Prop := ∀ {α : Type} (array : ArrayState α) delta, m1278 array delta =
  if delta < 0 || array.values.length < delta then .error .bounds else
  .ok { array with axes := oneToAxes [array.values.length - delta.toNat], values := array.values.drop delta.toNat }
theorem p1278 : P1278 := by simp [P1278, m1278]

def m1296 (array : ArrayState α) (delta : Int) : Result (ArrayState α) :=
  if delta < 0 || array.values.length < delta then .error .bounds else
  .ok { array with axes := oneToAxes [array.values.length - delta.toNat], values := array.values.take (array.values.length - delta.toNat) }
def P1296 : Prop := ∀ {α : Type} (array : ArrayState α) delta, m1296 array delta =
  if delta < 0 || array.values.length < delta then .error .bounds else
  .ok { array with axes := oneToAxes [array.values.length - delta.toNat], values := array.values.take (array.values.length - delta.toNat) }
theorem p1296 : P1296 := by simp [P1296, m1296]

def m1312 (array : ArrayState α) (index delta : Int) : Result (ArrayState α) :=
  if index < 1 || delta < 0 || array.values.length < index + delta - 1 then .error .bounds else
  let position := (index - 1).toNat
  let values := array.values.take position ++ array.values.drop (position + delta.toNat)
  .ok { array with axes := oneToAxes [array.values.length - delta.toNat], values := values }
def P1312 : Prop := ∀ {α : Type} (array : ArrayState α) index delta, m1312 array index delta =
  if index < 1 || delta < 0 || array.values.length < index + delta - 1 then .error .bounds else
  let position := (index - 1).toNat
  let values := array.values.take position ++ array.values.drop (position + delta.toNat)
  .ok { array with axes := oneToAxes [array.values.length - delta.toNat], values := values }
theorem p1312 : P1312 := by simp [P1312, m1312]

def appendConverted (convert : α → Result β) (array : ArrayState β) (values : List α) : Result (ArrayState β) := do
  match convertAll convert values with
  | .error error => .error error
  | .ok converted =>
      let output := array.values ++ converted.map some
      .ok { array with axes := oneToAxes [output.length], values := output }

theorem convertAll_identity (values : List α) :
    convertAll (fun value : α => .ok value) values = .ok values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [convertAll, ih]

def m1358 (convert : α → Result β) (array : ArrayState β) (item : α) := appendConverted convert array [item]
def P1358 : Prop := ∀ {α β : Type} (convert : α → Result β)
    (array : ArrayState β) (item : α), m1358 convert array item = appendConverted convert array [item]
theorem p1358 : P1358 := by simp [P1358, m1358]
def m1366 (array : ArrayState α) (item : α) := appendConverted (fun value => .ok value) array [item]
def P1366 : Prop := ∀ {α : Type} (array : ArrayState α) item, m1366 array item = appendConverted (fun value => .ok value) array [item]
theorem p1366 : P1366 := by simp [P1366, m1366]
def m1373 := @m1366
def P1373 : Prop := ∀ {α : Type} (array : ArrayState α) item, m1373 array item = m1366 array item
theorem p1373 : P1373 := by simp [P1373, m1373]
def m1378 (array : ArrayState α) (items : List α) := appendConverted (fun value => .ok value) array items
def P1378 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1378 array items = appendConverted (fun value => .ok value) array items
theorem p1378 : P1378 := by simp [P1378, m1378]

def m1427 (array : ArrayState α) (items : List α) := appendConverted (fun value => .ok value) array items
def P1427 : Prop := ∀ {α : Type} (array : ArrayState α) items,
  (m1427 array items).map (fun result => result.values) = .ok (array.values ++ items.map some)
theorem p1427 : P1427 := by simp [P1427, m1427, appendConverted, convertAll_identity, Except.map]
def m1435 := @m1427
def P1435 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1435 array items = m1427 array items
theorem p1435 : P1435 := by simp [P1435, m1435]
def m1436 := @m1378
def P1436 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1436 array items = m1378 array items
theorem p1436 : P1436 := by simp [P1436, m1436]
def m1437 := @m1427
def P1437 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1437 array items = m1427 array items
theorem p1437 : P1437 := by simp [P1437, m1437]
def m1439 := @m1427
def P1439 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1439 array items = m1427 array items
theorem p1439 : P1439 := by simp [P1439, m1439]
def m1447 := @m1427
def P1447 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1447 array items = m1427 array items
theorem p1447 : P1447 := by simp [P1447, m1447]

def prependConverted (convert : α → Result β) (array : ArrayState β) (values : List α) : Result (ArrayState β) := do
  match convertAll convert values with
  | .error error => .error error
  | .ok converted =>
      let output := converted.map some ++ array.values
      .ok { array with axes := oneToAxes [output.length], values := output }
def m1485 (array : ArrayState α) (items : List α) := prependConverted (fun value => .ok value) array items
def P1485 : Prop := ∀ {α : Type} (array : ArrayState α) items,
  (m1485 array items).map (fun result => result.values) = .ok (items.map some ++ array.values)
theorem p1485 : P1485 := by simp [P1485, m1485, prependConverted, convertAll_identity, Except.map]
def m1500 := @m1485
def P1500 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1500 array items = m1485 array items
theorem p1500 : P1500 := by simp [P1500, m1500]
def m1501 (array : ArrayState α) (items : List α) := prependConverted (fun value => .ok value) array items
def P1501 : Prop := ∀ {α : Type} (array : ArrayState α) items,
  (m1501 array items).map (fun result => result.values) = .ok (items.map some ++ array.values)
theorem p1501 : P1501 := by simp [P1501, m1501, prependConverted, convertAll_identity, Except.map]
def m1502 := @m1485
def P1502 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1502 array items = m1485 array items
theorem p1502 : P1502 := by simp [P1502, m1502]
def m1504 := @m1485
def P1504 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1504 array items = m1485 array items
theorem p1504 : P1504 := by simp [P1504, m1504]
def m1517 := @m1485
def P1517 : Prop := ∀ {α : Type} (array : ArrayState α) items, m1517 array items = m1485 array items
theorem p1517 : P1517 := by simp [P1517, m1517]

def m1564 (array : ArrayState α) (newLength : Int) (first : Bool) : Result (ArrayState α) :=
  if newLength < 0 then .error .argument else
  .ok { array with axes := oneToAxes [newLength.toNat], values := resizeValues array.values newLength.toNat first }
def P1564 : Prop := ∀ {α : Type} (array : ArrayState α) newLength first,
  m1564 array newLength first = if newLength < 0 then .error .argument else
    .ok { array with axes := oneToAxes [newLength.toNat], values := resizeValues array.values newLength.toNat first }
theorem p1564 : P1564 := by simp [P1564, m1564]

def m1617 (array : ArrayState α) (size : Int) (first shrink : Bool) : Result (ArrayState α) :=
  if size < 0 then .error .argument
  else if shrink && size.toNat < array.values.length then m1564 array size first
  else .ok array
def P1617 : Prop := ∀ {α : Type} (array : ArrayState α) size first shrink,
  m1617 array size first shrink = if size < 0 then .error .argument
    else if shrink && size.toNat < array.values.length then m1564 array size first else .ok array
theorem p1617 : P1617 := by simp [P1617, m1617]

def m1652 (allowed : List String) (provided : List String) (call : Result α) : Result α :=
  if provided.all allowed.contains then call else .error .argument
def P1652 : Prop := ∀ {α : Type} allowed provided (call : Result α),
  m1652 allowed provided call = if provided.all allowed.contains then call else .error .argument
theorem p1652 : P1652 := by simp [P1652, m1652]

def removeAt (values : List (Option α)) (index : Int) : Result (Option α × List (Option α)) :=
  if index < 1 || values.length < index then .error .bounds else
  match values[(index - 1).toNat]? with
  | none => .error .bounds
  | some value => .ok (value, values.take (index - 1).toNat ++ values.drop index.toNat)

def m1700 (array : ArrayState α) : Result (α × ArrayState α) := do
  let removed ← removeAt array.values array.values.length
  match removed.1 with
  | none => .error .unassigned
  | some value => .ok (value, { array with axes := oneToAxes [removed.2.length], values := removed.2 })
def P1700 : Prop := ∀ {α : Type} (array : ArrayState α), m1700 array = do
  let removed ← removeAt array.values array.values.length
  match removed.1 with
  | none => .error .unassigned
  | some value => .ok (value, { array with axes := oneToAxes [removed.2.length], values := removed.2 })
theorem p1700 : P1700 := by simp [P1700, m1700]

def m1741 (array : ArrayState α) (index : Int) : Result (α × ArrayState α) := do
  let removed ← removeAt array.values index
  match removed.1 with
  | none => .error .unassigned
  | some value => .ok (value, { array with axes := oneToAxes [removed.2.length], values := removed.2 })
def P1741 : Prop := ∀ {α : Type} (array : ArrayState α) index, m1741 array index = do
  let removed ← removeAt array.values index
  match removed.1 with
  | none => .error .unassigned
  | some value => .ok (value, { array with axes := oneToAxes [removed.2.length], values := removed.2 })
theorem p1741 : P1741 := by simp [P1741, m1741]

def m1748 (array : ArrayState α) (index : Int) (default : α) : α × ArrayState α :=
  match m1741 array index with | .ok result => result | .error _ => (default, array)
def P1748 : Prop := ∀ {α : Type} (array : ArrayState α) index default,
  m1748 array index default = match m1741 array index with | .ok result => result | .error _ => (default, array)
theorem p1748 : P1748 := by simp [P1748, m1748]

def m1777 (convert : α → Result β) (array : ArrayState β) item := prependConverted convert array [item]
def P1777 : Prop := ∀ {α β : Type} (convert : α → Result β)
    (array : ArrayState β) (item : α),
  (m1777 convert array item).map (fun result => result.values) =
    (convert item).map (fun value => some value :: array.values)
theorem p1777 : P1777 := by
  unfold P1777
  intro α β convert array item
  cases h : convert item <;> simp [m1777, prependConverted, convertAll, h, Except.map]
def m1782 (array : ArrayState α) item := prependConverted (fun value => .ok value) array [item]
def P1782 : Prop := ∀ {α : Type} (array : ArrayState α) item,
  (m1782 array item).map (fun result => result.values) = .ok (some item :: array.values)
theorem p1782 : P1782 := by simp [P1782, m1782, prependConverted, convertAll_identity, Except.map]
def m1789 := @m1782
def P1789 : Prop := ∀ {α : Type} (array : ArrayState α) item, m1789 array item = m1782 array item
theorem p1789 : P1789 := by simp [P1789, m1789]
def m1794 (array : ArrayState α) items := prependConverted (fun value => .ok value) array items
def P1794 : Prop := ∀ {α : Type} (array : ArrayState α) items,
  (m1794 array items).map (fun result => result.values) = .ok (items.map some ++ array.values)
theorem p1794 : P1794 := by simp [P1794, m1794, prependConverted, convertAll_identity, Except.map]

def m1836 (array : ArrayState α) : Result (α × ArrayState α) := m1741 array 1
def P1836 : Prop := ∀ {α : Type} (array : ArrayState α), m1836 array = m1741 array 1
theorem p1836 : P1836 := by simp [P1836, m1836]

def m1866 (convert : α → Result β) (array : ArrayState β) (index : Int) (item : α) : Result (ArrayState β) := do
  let grown ← m1230 array index 1
  setLinear grown index (← convert item)
def P1866 : Prop := ∀ {α β : Type} (convert : α → Result β)
    (array : ArrayState β) index (item : α), m1866 convert array index item = do
  let grown ← m1230 array index 1
  setLinear grown index (← convert item)
theorem p1866 : P1866 := by simp [P1866, m1866]
def m1871 (array : ArrayState α) (index : Int) (item : α) : Result (ArrayState α) := do
  let grown ← m1230 array index 1
  setLinear grown index item
def P1871 : Prop := ∀ {α : Type} (array : ArrayState α) index item, m1871 array index item = do
  let grown ← m1230 array index 1
  setLinear grown index item
theorem p1871 : P1871 := by simp [P1871, m1871]

def deleteIndices (array : ArrayState α) (indices : List Int) : Result (ArrayState α) :=
  if indices ≠ indices.mergeSort || indices.eraseDups.length ≠ indices.length ||
      indices.any (fun index => index < 1 || array.values.length < index) then .error .bounds
  else
    let values := (array.values.zipIdx).filterMap fun pair =>
      if indices.contains (Int.ofNat pair.2 + 1) then none else some pair.1
    .ok { array with axes := oneToAxes [values.length], values := values }

def m1899 (array : ArrayState α) (index : Int) := deleteIndices array [index]
def P1899 : Prop := ∀ {α : Type} (array : ArrayState α) index, m1899 array index = deleteIndices array [index]
theorem p1899 : P1899 := by simp [P1899, m1899]
def m1905 (array : ArrayState α) (indices : List Int) := deleteIndices array indices
def P1905 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m1905 array indices = deleteIndices array indices
theorem p1905 : P1905 := by simp [P1905, m1905]
def m1945 := @deleteIndices
def P1945 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m1945 array indices = deleteIndices array indices
theorem p1945 : P1945 := by simp [P1945, m1945]
def m1946 := @deleteIndices
def P1946 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m1946 array indices = deleteIndices array indices
theorem p1946 : P1946 := by simp [P1946, m1946]

def m1949 {T : Type} (_value : T) : Unit := ()
def P1949 : Prop := ∀ {T : Type} (value : T), m1949 value = ()
theorem p1949 : P1949 := by simp [P1949, m1949]
def m1950 {T : Type} (_value : T) : Unit := ()
def P1950 : Prop := ∀ {T : Type} (value : T), m1950 value = ()
theorem p1950 : P1950 := by simp [P1950, m1950]
def m1952 {D : Type} (push : D → Option α → D) (deleted : D)
    (array : ArrayState α) (index : Int) : Result D :=
  if index < 1 || array.values.length < index then .error .bounds else
  .ok (push deleted (array.values[(index - 1).toNat]?.getD none))
def P1952 : Prop := ∀ {D α : Type} (push : D → Option α → D) deleted
    (array : ArrayState α) (index : Int),
  m1952 push deleted array index = if index < 1 || array.values.length < index then .error .bounds else
    .ok (push deleted (array.values[(index - 1).toNat]?.getD none))
theorem p1952 : P1952 := by
  unfold P1952
  intro D α push deleted array index
  by_cases h : index < 1 || array.values.length < index <;> simp [m1952, h]
def m1961 (array : ArrayState α) (sourceIndex targetIndex : Int) : Result (ArrayState α) :=
  if sourceIndex < 1 || array.values.length < sourceIndex || targetIndex < 1 || array.values.length < targetIndex
  then .error .bounds
  else
    let slot := array.values[(sourceIndex - 1).toNat]?.getD none
    .ok { array with values := array.values.set (targetIndex - 1).toNat slot }
def P1961 : Prop := ∀ {α : Type} (array : ArrayState α) sourceIndex targetIndex,
  m1961 array sourceIndex targetIndex =
  if sourceIndex < 1 || array.values.length < sourceIndex || targetIndex < 1 || array.values.length < targetIndex
  then .error .bounds
  else
    let slot := array.values[(sourceIndex - 1).toNat]?.getD none
    .ok { array with values := array.values.set (targetIndex - 1).toNat slot }
theorem p1961 : P1961 := by simp [P1961, m1961]
def m1970 := @deleteIndices
def P1970 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m1970 array indices = deleteIndices array indices
theorem p1970 : P1970 := by simp [P1970, m1970]
def m2005 (array : ArrayState α) (mask : List Bool) : Result (ArrayState α) :=
  if mask.length ≠ array.values.length then .error .bounds else
  let values := (array.values.zip mask).filterMap fun pair => if pair.2 then none else some pair.1
  .ok { array with axes := oneToAxes [values.length], values := values }
def P2005 : Prop := ∀ {α : Type} (array : ArrayState α) mask, m2005 array mask =
  if mask.length ≠ array.values.length then .error .bounds else
  let values := (array.values.zip mask).filterMap fun pair => if pair.2 then none else some pair.1
  .ok { array with axes := oneToAxes [values.length], values := values }
theorem p2005 : P2005 := by simp [P2005, m2005]

def spliceAt (array : ArrayState α) (start count : Int) (inserted : List α) : Result (List (Option α) × ArrayState α) :=
  if start < 1 || count < 0 || array.values.length < start + count - 1 then .error .bounds else
  let position := (start - 1).toNat
  let removed := (array.values.drop position).take count.toNat
  let values := array.values.take position ++ inserted.map some ++ array.values.drop (position + count.toNat)
  .ok (removed, { array with axes := oneToAxes [values.length], values })
def m2070 (array : ArrayState α) index inserted := spliceAt array index 1 inserted
def P2070 : Prop := ∀ {α : Type} (array : ArrayState α) index inserted, m2070 array index inserted = spliceAt array index 1 inserted
theorem p2070 : P2070 := by simp [P2070, m2070]
def m2125 (array : ArrayState α) start stop inserted := spliceAt array start (stop - start + 1) inserted
def P2125 : Prop := ∀ {α : Type} (array : ArrayState α) start stop inserted,
  m2125 array start stop inserted = spliceAt array start (stop - start + 1) inserted
theorem p2125 : P2125 := by simp [P2125, m2125]
def m2153 := @deleteIndices
def P2153 : Prop := ∀ {α : Type} (array : ArrayState α) indices, m2153 array indices = deleteIndices array indices
theorem p2153 : P2153 := by simp [P2153, m2153]
def m2155 (array : ArrayState α) : ArrayState α := { array with axes := oneToAxes [0], values := [] }
def P2155 : Prop := ∀ {α : Type} (array : ArrayState α), (m2155 array).values = []
theorem p2155 : P2155 := by simp [P2155, m2155]

def m2161 (left right : List UInt8) : Ordering := compare left right
def P2161 : Prop := ∀ left right, m2161 left right = compare left right
theorem p2161 : P2161 := by simp [P2161, m2161]
def m2176 [DecidableEq α] (left right : ArrayState α) : Bool :=
  decide (left.axes = right.axes) && decide (left.values = right.values)
def P2176 : Prop := ∀ {α : Type} [DecidableEq α] (left right : ArrayState α),
  m2176 left right = (decide (left.axes = right.axes) && decide (left.values = right.values))
theorem p2176 : P2176 := by simp [P2176, m2176]
def m2193 [DecidableEq α] (left right : List α) : Bool := decide (left = right)
def P2193 : Prop := ∀ {α : Type} [DecidableEq α] (left right : List α),
  m2193 left right = decide (left = right)
theorem p2193 : P2193 := by simp [P2193, m2193]

def reverseWindow (values : List (Option α)) (start stop : Int) : Result (List (Option α)) :=
  if start < 1 || stop < start || values.length < stop then .error .bounds else
  let left := (start - 1).toNat
  .ok (values.take left ++ ((values.drop left).take (stop - start + 1).toNat).reverse ++ values.drop stop.toNat)
def m2253 (array : ArrayState α) (start stop : Int) : Result (ArrayState α) := do
  pure { array with values := ← reverseWindow array.values start stop, id := array.id + 1 }
def P2253 : Prop := ∀ {α : Type} (array : ArrayState α) start stop, m2253 array start stop = do
  pure { array with values := ← reverseWindow array.values start stop, id := array.id + 1 }
theorem p2253 : P2253 := by simp [P2253, m2253]

def m2271 {A D R : Type} (route : A → D → R) array dims := route array dims
def P2271 : Prop := ∀ {A D R : Type} (route : A → D → R) array dims, m2271 route array dims = route array dims
theorem p2271 : P2271 := by simp [P2271, m2271]
def m2272 (array : ArrayState α) := m2253 array 1 array.values.length
def P2272 : Prop := ∀ {α : Type} (array : ArrayState α), m2272 array = m2253 array 1 array.values.length
theorem p2272 : P2272 := by simp [P2272, m2272]
def m2273 (array : ArrayState α) (dimension : Int) := if dimension = 1 then m2272 array else .error .argument
def P2273 : Prop := ∀ {α : Type} (array : ArrayState α) dimension,
  m2273 array dimension = if dimension = 1 then m2272 array else .error .argument
theorem p2273 : P2273 := by simp [P2273, m2273]
def m2274 := @m2273
def P2274 : Prop := ∀ {α : Type} (array : ArrayState α) dimension, m2274 array dimension = m2273 array dimension
theorem p2274 : P2274 := by simp [P2274, m2274]
def m2281 (length index : Int) : Int := length - index + 1
def P2281 : Prop := ∀ length index, m2281 length index = length - index + 1
theorem p2281 : P2281 := by simp [P2281, m2281]
def m2288 (low high : Int) : Int := low + (high - low) / 2
def P2288 : Prop := ∀ low high, m2288 low high = low + (high - low) / 2
theorem p2288 : P2288 := by simp [P2288, m2288]
def m2289 := m2288
def P2289 : Prop := ∀ low high, m2289 low high = low + (high - low) / 2
theorem p2289 : P2289 := by simp [P2289, m2289, m2288]
def m2317 (array : ArrayState α) (start stop : Int) : Result (ArrayState α) := do
  pure { array with values := ← reverseWindow array.values start stop }
def P2317 : Prop := ∀ {α : Type} (array : ArrayState α) start stop, m2317 array start stop = do
  pure { array with values := ← reverseWindow array.values start stop }
theorem p2317 : P2317 := by simp [P2317, m2317]

private def entry (id : String) (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := [name],
    statement, source := s!"base/array.jl:{line}; vector mutation source equation", status := .proven,
    prop, thm := some thm }

def entries : List Entry := [
  entry "multidimcov-array-faithful-1427" 1427 "append!(Vector,vector or tuple)" "Append uses the source first index and appends every item in source order." ``P1427 ``p1427,
  entry "multidimcov-array-faithful-1485" 1485 "prepend!(Vector,vector or tuple)" "Prepend respects arbitrary source indexing and places all items before existing values in order." ``P1485 ``p1485,
  entry "multidimcov-array-faithful-1501" 1501 "pushfirst!(AbstractVector,items...)" "Variadic pushfirst places every item at the front in supplied order." ``P1501 ``p1501,
  entry "multidimcov-array-faithful-1794" 1794 "pushfirst!(Vector{Any},items...)" "Variadic Any pushfirst inserts all items at the front in supplied order." ``P1794 ``p1794
]

end JuliaLean.MultidimCov.ArrayVectorFaithful
