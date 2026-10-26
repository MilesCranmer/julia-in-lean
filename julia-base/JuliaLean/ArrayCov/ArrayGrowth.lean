import JuliaLean.Core

namespace JuliaLean.ArrayCov

structure GrowthState where
  length : Int
  memoryLength : Int
  offset : Int
  deriving Repr, DecidableEq

inductive GrowthError where
  | argument | bounds | concurrency | overflow | keyword
  deriving Repr, DecidableEq

abbrev GrowthJl (α : Type) := Except GrowthError α

def array1102Overallocation (ctlz shiftOne : Int → Int)
    (mulWrap addWrap subWrap divInt : Int → Int → Int)
    (maxInt maxSize : Int) : Int :=
  let exponent := 64 - ctlz maxSize
  let extra := addWrap (mulWrap (shiftOne (divInt (mulWrap exponent 7) 8)) 3)
    (divInt maxSize 8)
  if maxSize > subWrap maxInt extra then maxInt else addWrap maxSize extra

def array1116GrowBeginInternal
    (checkedAdd checkedMul : Int → Int → GrowthJl Int)
    (overallocation : Int → Int)
    (reuseMove allocateMove : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (delta len : Int) : GrowthJl GrowthState := do
  let newLength ← checkedAdd len delta
  let _ ← (if state.offset < 1 || state.offset - 1 > state.memoryLength ||
      len > state.memoryLength - (state.offset - 1) then throw .concurrency else pure ())
  let twice ← checkedMul 2 delta
  let exact ← checkedAdd len twice >>= fun value => checkedAdd value 1
  let newMemoryLength := max (overallocation len) exact
  let newOffset := (newMemoryLength - newLength) / 2 + 1
  if newLength < state.memoryLength && newOffset < state.memoryLength - newLength then
    reuseMove state delta newLength
  else allocateMove { state with memoryLength := newMemoryLength, offset := newOffset } delta newLength

def array1151GrowBegin (convert : Int → GrowthJl Int)
    (checkedAdd : Int → Int → GrowthJl Int)
    (moveRef : GrowthState → Int → GrowthState)
    (internal : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta = 0 then return state
  if delta < 0 then throw .argument
  let newLength ← checkedAdd state.length delta
  let state ← if delta ≤ state.offset - 1 then
    pure (moveRef state (1 - delta))
  else internal state delta state.length
  pure { state with length := newLength }

def array1171GrowEndInternal
    (checkedAdd : Int → Int → GrowthJl Int) (overallocation : Int → Int)
    (reuseMove allocateMove : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (delta len : Int) : GrowthJl GrowthState := do
  let newLength ← checkedAdd len delta
  let _ ← (if state.offset < 1 || state.offset - 1 > state.memoryLength ||
      len > state.memoryLength - (state.offset - 1) then throw .concurrency else pure ())
  let needed ← checkedAdd (state.offset - 1) newLength
  if state.offset - 1 > newLength && state.offset - 1 - newLength > newLength / 4 then
    return ← reuseMove state newLength (newLength / 8 + 1)
  else
    return ← (allocateMove { state with memoryLength := max (overallocation state.memoryLength) needed }
      newLength state.offset)

def array1212GrowEnd (convert : Int → GrowthJl Int)
    (checkedAdd : Int → Int → GrowthJl Int)
    (internal : GrowthState → Int → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta < 0 then throw .argument
  let newLength ← checkedAdd state.length delta
  let needed ← checkedAdd (state.offset - 1) newLength
  let state ← if state.memoryLength < needed then internal state delta state.length else pure state
  pure { state with length := newLength }

def array1230GrowAt (convert : Int → GrowthJl Int)
    (growBegin growEnd : GrowthState → Int → GrowthJl GrowthState)
    (checkedAdd : Int → Int → GrowthJl Int)
    (frontMove backMove allocateMove : GrowthState → Int → Int → GrowthJl GrowthState)
    (maxInt : Int) (state : GrowthState) (rawIndex rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  let index ← convert rawIndex
  if index = 1 then return ← growBegin state delta
  if state.length < maxInt && index = state.length + 1 then return ← growEnd state delta
  if delta < 0 then throw .argument
  if !(1 < index && index ≤ state.length) then throw .bounds
  let newLength ← checkedAdd state.length delta
  let preferStart := index ≤ state.length / 2
  if preferStart && delta ≤ state.offset - 1 then
    frontMove { state with length := newLength, offset := state.offset - delta } index delta
  else if !preferStart && state.memoryLength ≥ state.offset - 1 + newLength then
    backMove { state with length := newLength } index delta
  else allocateMove { state with length := newLength } index delta

def ArrayGrowthCorrect : Prop :=
  (∀ ctlz shift mul add sub div maxInt size,
      array1102Overallocation ctlz shift mul add sub div maxInt size =
      let exponent := 64 - ctlz size
      let extra := add (mul (shift (div (mul exponent 7) 8)) 3) (div size 8)
      if size > sub maxInt extra then maxInt else add size extra) ∧
  (∀ add mul overall reuse allocate state delta len,
      array1116GrowBeginInternal add mul overall reuse allocate state delta len = do
      let newLength ← add len delta
      let _ ← (if state.offset < 1 || state.offset - 1 > state.memoryLength ||
          len > state.memoryLength - (state.offset - 1) then throw .concurrency else pure ())
      let twice ← mul 2 delta
      let exact ← add len twice >>= fun value => add value 1
      let memoryLength := max (overall len) exact
      let offset := (memoryLength - newLength) / 2 + 1
      if newLength < state.memoryLength && offset < state.memoryLength - newLength then
        reuse state delta newLength
      else allocate { state with memoryLength := memoryLength, offset := offset } delta newLength) ∧
  (∀ convert add move internal state delta,
      array1151GrowBegin convert add move internal state delta = do
      let delta ← convert delta
      if delta = 0 then return state
      if delta < 0 then throw .argument
      let newLength ← add state.length delta
      let state ← if delta ≤ state.offset - 1 then pure (move state (1 - delta))
        else internal state delta state.length
      pure { state with length := newLength }) ∧
  (∀ add overall reuse allocate state delta len,
      array1171GrowEndInternal add overall reuse allocate state delta len = do
      let newLength ← add len delta
      let _ ← (if state.offset < 1 || state.offset - 1 > state.memoryLength ||
          len > state.memoryLength - (state.offset - 1) then throw .concurrency else pure ())
      let needed ← add (state.offset - 1) newLength
      if state.offset - 1 > newLength && state.offset - 1 - newLength > newLength / 4 then
        return ← reuse state newLength (newLength / 8 + 1)
      else return ← (allocate { state with memoryLength := max (overall state.memoryLength) needed }
        newLength state.offset)) ∧
  (∀ convert add internal state delta, array1212GrowEnd convert add internal state delta = do
      let delta ← convert delta
      if delta < 0 then throw .argument
      let newLength ← add state.length delta
      let needed ← add (state.offset - 1) newLength
      let state ← if state.memoryLength < needed then internal state delta state.length else pure state
      pure { state with length := newLength }) ∧
  (∀ convert begin finish add front back allocate maxInt state index delta,
      array1230GrowAt convert begin finish add front back allocate maxInt state index delta = do
      let delta ← convert delta
      let index ← convert index
      if index = 1 then return ← begin state delta
      if state.length < maxInt && index = state.length + 1 then return ← finish state delta
      if delta < 0 then throw .argument
      if !(1 < index && index ≤ state.length) then throw .bounds
      let newLength ← add state.length delta
      let preferStart := index ≤ state.length / 2
      if preferStart && delta ≤ state.offset - 1 then
        front { state with length := newLength, offset := state.offset - delta } index delta
      else if !preferStart && state.memoryLength ≥ state.offset - 1 + newLength then
        back { state with length := newLength } index delta
      else allocate { state with length := newLength } index delta)

theorem arrayGrowthCorrect : ArrayGrowthCorrect := by
  simp [ArrayGrowthCorrect, array1102Overallocation, array1116GrowBeginInternal,
    array1151GrowBegin, array1171GrowEndInternal, array1212GrowEnd, array1230GrowAt]

def array1278DeleteBegin (convert : Int → GrowthJl Int)
    (unsetRange : GrowthState → Int → Int → GrowthState)
    (moveRef : GrowthState → Int → GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta < 0 || state.length < delta then throw .argument
  let state := unsetRange state 1 delta
  let newLength := state.length - delta
  let state := { state with length := newLength }
  if newLength = 0 then return state
  pure (moveRef state (delta + 1))

def array1296DeleteEnd (convert : Int → GrowthJl Int)
    (unsetRange : GrowthState → Int → Int → GrowthState)
    (state : GrowthState) (rawDelta : Int) : GrowthJl GrowthState := do
  let delta ← convert rawDelta
  if delta < 0 || state.length < delta then throw .argument
  let newLength := state.length - delta
  pure { (unsetRange state (newLength + 1) state.length) with length := newLength }

def array1312DeleteAt (copy : GrowthState → Int → Int → Int → GrowthJl GrowthState)
    (deleteBegin deleteEnd : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (index delta : Int) : GrowthJl GrowthState := do
  if delta < 0 then throw .argument
  if !(1 ≤ index && index ≤ state.length) then throw .bounds
  if index + delta > state.length + 1 then throw .bounds
  if 2 * index + delta ≤ state.length then
    let state ← copy state (1 + delta) 1 (index - 1)
    deleteBegin state delta
  else
    let state ← copy state index (index + delta) (state.length + 1 - delta - index)
    deleteEnd state delta

def array1564Resize (convert : Int → GrowthJl Int)
    (growBegin growEnd deleteBegin deleteEnd : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawLength : Int) (first : Bool) : GrowthJl GrowthState := do
  let newLength ← convert rawLength
  if state.length < newLength then
    if first then growBegin state (newLength - state.length)
    else growEnd state (newLength - state.length)
  else if newLength != state.length then
    if newLength < 0 then throw .argument
    if first then deleteBegin state (state.length - newLength)
    else deleteEnd state (state.length - newLength)
  else pure state

def ArrayDeleteResizeCorrect : Prop :=
  (∀ convert unset move state delta, array1278DeleteBegin convert unset move state delta = do
      let delta ← convert delta
      if delta < 0 || state.length < delta then throw .argument
      let state := unset state 1 delta
      let length := state.length - delta
      let state := { state with length := length }
      if length = 0 then return state
      pure (move state (delta + 1))) ∧
  (∀ convert unset state delta, array1296DeleteEnd convert unset state delta = do
      let delta ← convert delta
      if delta < 0 || state.length < delta then throw .argument
      let length := state.length - delta
      pure { (unset state (length + 1) state.length) with length := length }) ∧
  (∀ copy begin finish state index delta, array1312DeleteAt copy begin finish state index delta = do
      if delta < 0 then throw .argument
      if !(1 ≤ index && index ≤ state.length) then throw .bounds
      if index + delta > state.length + 1 then throw .bounds
      if 2 * index + delta ≤ state.length then
        let state ← copy state (1 + delta) 1 (index - 1)
        begin state delta
      else
        let state ← copy state index (index + delta) (state.length + 1 - delta - index)
        finish state delta) ∧
  (∀ convert begin finish deleteBegin deleteEnd state length first,
      array1564Resize convert begin finish deleteBegin deleteEnd state length first = do
      let length ← convert length
      if state.length < length then
        if first then begin state (length - state.length) else finish state (length - state.length)
      else if length != state.length then
        if length < 0 then throw .argument
        if first then deleteBegin state (state.length - length)
        else deleteEnd state (state.length - length)
      else pure state)

theorem arrayDeleteResizeCorrect : ArrayDeleteResizeCorrect := by
  simp [ArrayDeleteResizeCorrect, array1278DeleteBegin, array1296DeleteEnd,
    array1312DeleteAt, array1564Resize]

def array1617Sizehint
    (convert : Int → GrowthJl Int)
    (reallocateCopy : GrowthState → Int → Bool → GrowthJl GrowthState)
    (growBegin growEnd : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (rawSize : Int) (first shrink : Bool) : GrowthJl GrowthState := do
  let requested ← convert rawSize
  let size := max requested state.length
  let increment := size - state.length
  if size ≤ state.memoryLength then
    if !shrink || state.memoryLength - size ≤ state.memoryLength / 8 then return state
    reallocateCopy state size first
  else if first then do
    let grown ← growBegin state increment
    pure { grown with length := state.length }
  else do
    let grown ← growEnd state increment
    pure { grown with length := state.length }

def array1652Kwcall (getBool : Int → Bool → GrowthJl Bool)
    (extraEmpty : Bool) (kwerr : GrowthJl GrowthState)
    (sizehint : GrowthState → Int → GrowthJl GrowthState)
    (state : GrowthState) (size : Int) : GrowthJl GrowthState := do
  let _first ← getBool 0 false
  let _shrink ← getBool 1 true
  if !extraEmpty then kwerr else sizehint state size

def ArraySizehintCorrect : Prop :=
  (∀ convert realloc begin finish state size first shrink,
      array1617Sizehint convert realloc begin finish state size first shrink = do
      let requested ← convert size
      let size := max requested state.length
      let increment := size - state.length
      if size ≤ state.memoryLength then
        if !shrink || state.memoryLength - size ≤ state.memoryLength / 8 then return state
        realloc state size first
      else if first then do
        let grown ← begin state increment
        pure { grown with length := state.length }
      else do
        let grown ← finish state increment
        pure { grown with length := state.length }) ∧
  (∀ get extra kwerr hint state size, array1652Kwcall get extra kwerr hint state size = do
      let _first ← get 0 false
      let _shrink ← get 1 true
      if !extra then kwerr else hint state size)

theorem arraySizehintCorrect : ArraySizehintCorrect := by
  simp [ArraySizehintCorrect, array1617Sizehint, array1652Kwcall]

end JuliaLean.ArrayCov
