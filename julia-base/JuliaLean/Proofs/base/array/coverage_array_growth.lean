import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

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
