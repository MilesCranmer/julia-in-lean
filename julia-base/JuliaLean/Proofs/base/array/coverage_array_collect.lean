import JuliaLean.base.array
import JuliaLean.Core
import JuliaLean.base.range

namespace JuliaLean.ArrayCov

open JuliaLean.base.range (JlX)

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

def ArrayIteratorTypeCorrect : Prop :=
  (∀ first next barrier fuel, array805IteratorUpper first next barrier fuel =
      array805IteratorUpperLoop next barrier fuel (first ())) ∧
  (∀ generator isType fn ret promote iterator,
      array821DefaultEltype generator isType fn ret promote iterator =
      promote (if generator iterator && isType iterator then fn iterator else ret iterator))

theorem arrayIteratorTypeCorrect : ArrayIteratorTypeCorrect := by
  simp [ArrayIteratorTypeCorrect, array805IteratorUpper, array821DefaultEltype]

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
  (repeat' (apply And.intro)) <;> intros <;> rfl

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


def ArrayCollectLoopsCorrect : Prop :=
  (∀ iterate type set widen dest iterator offset state fuel,
      array895CollectTo iterate type set widen dest iterator offset state fuel =
      array895CollectToLoop iterate type set widen dest iterator offset state fuel) ∧
  (∀ iterate empty push grow dest iterator, array914GrowFirst iterate empty push grow dest iterator =
      match iterate iterator with
      | none => .ok dest
      | some (first, state) => grow (push (empty dest first) first) iterator state) ∧
  (∀ promote empty hint isSet union append push eltype length dest element,
      array922PushWiden promote empty hint isSet union append push eltype length dest element =
      let new := hint (empty dest (promote (eltype dest) element)) (length dest)
      let new := if isSet new then union new dest else append new dest
      push new element) ∧
  (∀ iterate type push widen dest iterator state fuel,
      array935GrowTo iterate type push widen dest iterator state fuel =
      array935GrowLoop iterate type push widen dest iterator state fuel)

theorem arrayCollectLoopsCorrect : ArrayCollectLoopsCorrect := by
  simp [ArrayCollectLoopsCorrect, array895CollectTo, array914GrowFirst,
    array922PushWiden, array935GrowTo]
  intros
  rfl

end JuliaLean.ArrayCov
