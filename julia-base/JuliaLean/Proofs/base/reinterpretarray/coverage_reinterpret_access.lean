import JuliaLean.base.reinterpretarray
import JuliaLean.Core
import JuliaLean.base.reinterpretarray

namespace JuliaLean.ArrayCov

def ReinterpretGetRoutesCorrect : Prop :=
  (∀ readable ptr getPtr getRa array indices,
      reinterpret433Get readable ptr getPtr getRa array indices = do
      readable array
      if ptr array then return ← getPtr array indices
      getRa array (indices.getD 0 (JInt.lit .i64 1)) indices.tail) ∧
  (∀ readable ptr getPtr linear subs first getRa array index,
      reinterpret439GetLinear readable ptr getPtr linear subs first getRa array index = do
      readable array
      if ptr array then return ← getPtr array index
      if linear array then return ← getRa array index []
      let indices := subs array index
      if indices.isEmpty then getRa array (first array) []
      else getRa array (indices.getD 0 (JInt.lit .i64 1)) indices.tail) ∧
  (∀ readable parent extract array index,
      reinterpret451GetCartesian readable parent extract array index = do
      readable array
      let value ← parent array.parent index.j
      extract value index.i) ∧
  (∀ bounds linear first elsize convert load array indices,
      reinterpret458GetPtr bounds linear first elsize convert load array indices = do
      if bounds array indices then pure () else throw .bounds
      let pointer := convert array + elsize array * (linear array indices - first array)
      load pointer) ∧
  (∀ singleton primitive target source, reinterpret466ScalarApplicable singleton primitive target source =
      (singleton target || (primitive target && target = source))) ∧
  (∀ bounds singleton singletonValue scalar scalarGet larger equal smaller target source ts ss array first tail,
      reinterpret524GetRaReshaped bounds singleton singletonValue scalar scalarGet larger equal smaller
        target source ts ss array first tail = do
      if singleton target then
        bounds array first tail
        return singletonValue target
      if scalar target source then return ← scalarGet array first tail
      bounds array first tail
      if ss < ts then larger array first tail
      else if ts = ss then equal array first tail
      else smaller array first tail)

theorem reinterpretGetRoutesCorrect : ReinterpretGetRoutesCorrect := by
  simp [ReinterpretGetRoutesCorrect, reinterpret433Get, reinterpret439GetLinear,
    reinterpret451GetCartesian, reinterpret458GetPtr, reinterpret466ScalarApplicable,
    reinterpret524GetRaReshaped]

def ReinterpretSetRoutesCorrect : Prop :=
  (∀ scalar convert reinterpret parentSet first set target source array value,
      reinterpret569SetZero scalar convert reinterpret parentSet first set
        target source array value =
      if scalar target source then do
        let value ← convert value
        let parent ← parentSet array.parent (reinterpret source value)
        pure ⟨parent⟩
      else set array value (first array)) ∧
  (∀ writable ptr setPtr setRa array value indices,
      reinterpret579Set writable ptr setPtr setRa array value indices = do
      writable array
      if ptr array then return ← setPtr array value indices
      setRa array value (indices.getD 0 (JInt.lit .i64 1)) indices.tail) ∧
  (∀ writable ptr setPtr linear subs first setRa array value index,
      reinterpret585SetLinear writable ptr setPtr linear subs first setRa array value index = do
      writable array
      if ptr array then return ← setPtr array value index
      if linear array then return ← setRa array value index []
      let indices := subs array index
      if indices.isEmpty then setRa array value (first array) []
      else setRa array value (indices.getD 0 (JInt.lit .i64 1)) indices.tail) ∧
  (∀ writable convert get overwrite set array value index,
      reinterpret595SetCartesian writable convert get overwrite set array value index = do
      writable array
      let value ← convert value
      let parentValue ← get array.parent index.j
      let parent ← set array.parent index.j (overwrite parentValue value index.i)
      pure ⟨parent⟩) ∧
  (∀ bounds linear first elsize convert store array value indices,
      reinterpret607SetPtr bounds linear first elsize convert store array value indices = do
      if bounds array indices then pure () else throw .bounds
      let pointer := convert array + elsize array * (linear array indices - first array)
      store pointer value
      pure array) ∧
  (∀ convert bounds singleton scalar scalarSet larger equal smaller target source ts ss array value first tail,
      reinterpret685SetRaReshaped convert bounds singleton scalar scalarSet larger equal smaller
        target source ts ss array value first tail = do
      let value ← convert value
      if singleton target then
        bounds array first tail
        return array
      if scalar target source then return ← scalarSet array value first tail
      bounds array first tail
      if ss < ts then larger array value first tail
      else if ts = ss then equal array value first tail
      else smaller array value first tail)

theorem reinterpretSetRoutesCorrect : ReinterpretSetRoutesCorrect := by
  simp [ReinterpretSetRoutesCorrect, reinterpret569SetZero, reinterpret579Set,
    reinterpret585SetLinear, reinterpret595SetCartesian, reinterpret607SetPtr,
    reinterpret685SetRaReshaped]

end JuliaLean.ArrayCov
