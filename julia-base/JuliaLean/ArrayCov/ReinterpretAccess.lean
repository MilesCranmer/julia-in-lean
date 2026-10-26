import JuliaLean.Core
import JuliaLean.ArrayCov.ReinterpretSimple

namespace JuliaLean.ArrayCov

inductive ReinterpretAccessError where
  | bounds | unreadable | unwritable | conversion
  deriving Repr, DecidableEq

abbrev ReinterpretAccessJl (α : Type) := Except ReinterpretAccessError α

def reinterpret433Get (checkReadable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (getPtr : ReinterpretValue → List JInt64 → ReinterpretAccessJl Int)
    (getRa : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (indices : List JInt64) : ReinterpretAccessJl Int := do
  checkReadable array
  if ptrIndexable array then return ← getPtr array indices
  getRa array (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret439GetLinear (checkReadable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (getPtr : ReinterpretValue → JInt64 → ReinterpretAccessJl Int)
    (linearStyle : ReinterpretValue → Bool)
    (toSubscripts : ReinterpretValue → JInt64 → List JInt64)
    (firstIndex : ReinterpretValue → JInt64)
    (getRa : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (index : JInt64) : ReinterpretAccessJl Int := do
  checkReadable array
  if ptrIndexable array then return ← getPtr array index
  if linearStyle array then return ← getRa array index []
  let indices := toSubscripts array index
  if indices.isEmpty then getRa array (firstIndex array) []
  else getRa array (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret451GetCartesian (checkReadable : ReinterpretValue → ReinterpretAccessJl Unit)
    (parentGet : List Int → JInt64 → ReinterpretAccessJl Int)
    (extract : Int → JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (index : SCartesianIndexModel) : ReinterpretAccessJl Int := do
  checkReadable array
  let parentValue ← parentGet array.parent index.j
  extract parentValue index.i

def reinterpret458GetPtr (checkbounds : ReinterpretValue → List JInt64 → Bool)
    (linearIndex : ReinterpretValue → List JInt64 → JInt64)
    (firstIndex : ReinterpretValue → JInt64) (elsize : ReinterpretValue → JInt64)
    (cconvert : ReinterpretValue → JInt64)
    (load : JInt64 → ReinterpretAccessJl Int)
    (array : ReinterpretValue) (indices : List JInt64) : ReinterpretAccessJl Int := do
  if checkbounds array indices then pure () else throw .bounds
  let linear := linearIndex array indices
  let pointer := cconvert array + elsize array * (linear - firstIndex array)
  load pointer

def reinterpret466ScalarApplicable (singleton primitive : Int → Bool)
    (target source : Int) : Bool :=
  singleton target || (primitive target && target = source)

def reinterpret524GetRaReshaped
    (checkbounds : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Unit)
    (singleton : Int → Bool) (singletonValue : Int → Int)
    (scalarApplicable : Int → Int → Bool)
    (scalarGet : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (assembleLarger : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (assembleEqual : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (extractSmaller : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Int)
    (target source : Int) (targetSize sourceSize : JInt64)
    (array : ReinterpretValue) (first : JInt64) (tail : List JInt64) :
    ReinterpretAccessJl Int := do
  if singleton target then
    checkbounds array first tail
    return singletonValue target
  if scalarApplicable target source then return ← scalarGet array first tail
  checkbounds array first tail
  if sourceSize < targetSize then assembleLarger array first tail
  else if targetSize = sourceSize then assembleEqual array first tail
  else extractSmaller array first tail

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

def reinterpret569SetZero (scalarApplicable : Int → Int → Bool)
    (convert : Int → ReinterpretAccessJl Int)
    (reinterpretScalar : Int → Int → Int)
    (parentSet : List Int → Int → ReinterpretAccessJl (List Int))
    (firstIndex : ReinterpretValue → JInt64)
    (setindex : ReinterpretValue → Int → JInt64 → ReinterpretAccessJl ReinterpretValue)
    (target source : Int) (array : ReinterpretValue) (value : Int) :
    ReinterpretAccessJl ReinterpretValue :=
  if scalarApplicable target source then do
    let value ← convert value
    let parent ← parentSet array.parent (reinterpretScalar source value)
    pure ⟨parent⟩
  else setindex array value (firstIndex array)

def reinterpret579Set (checkWritable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (setPtr : ReinterpretValue → Int → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (setRa : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) (indices : List JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  checkWritable array
  if ptrIndexable array then return ← setPtr array value indices
  setRa array value (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret585SetLinear (checkWritable : ReinterpretValue → ReinterpretAccessJl Unit)
    (ptrIndexable : ReinterpretValue → Bool)
    (setPtr : ReinterpretValue → Int → JInt64 → ReinterpretAccessJl ReinterpretValue)
    (linearStyle : ReinterpretValue → Bool)
    (toSubscripts : ReinterpretValue → JInt64 → List JInt64)
    (firstIndex : ReinterpretValue → JInt64)
    (setRa : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) (index : JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  checkWritable array
  if ptrIndexable array then return ← setPtr array value index
  if linearStyle array then return ← setRa array value index []
  let indices := toSubscripts array index
  if indices.isEmpty then setRa array value (firstIndex array) []
  else setRa array value (indices.getD 0 (JInt.lit .i64 1)) indices.tail

def reinterpret595SetCartesian (checkWritable : ReinterpretValue → ReinterpretAccessJl Unit)
    (convert : Int → ReinterpretAccessJl Int)
    (parentGet : List Int → JInt64 → ReinterpretAccessJl Int)
    (overwrite : Int → Int → JInt64 → Int)
    (parentSet : List Int → JInt64 → Int → ReinterpretAccessJl (List Int))
    (array : ReinterpretValue) (value : Int) (index : SCartesianIndexModel) :
    ReinterpretAccessJl ReinterpretValue := do
  checkWritable array
  let value ← convert value
  let parentValue ← parentGet array.parent index.j
  let parent ← parentSet array.parent index.j (overwrite parentValue value index.i)
  pure ⟨parent⟩

def reinterpret607SetPtr (checkbounds : ReinterpretValue → List JInt64 → Bool)
    (linearIndex : ReinterpretValue → List JInt64 → JInt64)
    (firstIndex : ReinterpretValue → JInt64) (elsize : ReinterpretValue → JInt64)
    (cconvert : ReinterpretValue → JInt64)
    (store : JInt64 → Int → ReinterpretAccessJl Unit)
    (array : ReinterpretValue) (value : Int) (indices : List JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  if checkbounds array indices then pure () else throw .bounds
  let pointer := cconvert array + elsize array * (linearIndex array indices - firstIndex array)
  store pointer value
  pure array

def reinterpret685SetRaReshaped
    (convert : Int → ReinterpretAccessJl Int)
    (checkbounds : ReinterpretValue → JInt64 → List JInt64 → ReinterpretAccessJl Unit)
    (singleton : Int → Bool) (scalarApplicable : Int → Int → Bool)
    (scalarSet : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (writeLarger : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (writeEqual : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (writeSmaller : ReinterpretValue → Int → JInt64 → List JInt64 → ReinterpretAccessJl ReinterpretValue)
    (target source : Int) (targetSize sourceSize : JInt64)
    (array : ReinterpretValue) (value : Int) (first : JInt64) (tail : List JInt64) :
    ReinterpretAccessJl ReinterpretValue := do
  let value ← convert value
  if singleton target then
    checkbounds array first tail
    return array
  if scalarApplicable target source then return ← scalarSet array value first tail
  checkbounds array first tail
  if sourceSize < targetSize then writeLarger array value first tail
  else if targetSize = sourceSize then writeEqual array value first tail
  else writeSmaller array value first tail

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
