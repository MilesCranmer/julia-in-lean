import JuliaLean.base.array
import JuliaLean.Core
import JuliaLean.Proofs.base.array.coverage_simple

namespace JuliaLean.ArrayCov

def ArrayFillConstructorsCorrect : Prop :=
  (∀ d, array482ToDimInteger d = d) ∧
  (∀ last, array483ToDimOneTo last = last) ∧
  (∀ call value dims, array583FillVarargs call value dims = call value dims) ∧
  (∀ call value dims, array584FillMapped call value dims =
      call value (dims.map dimArgValue)) ∧
  (∀ allocate fill value type dims, array585FillInteger allocate fill value type dims = do
      let array ← allocate type dims; fill array value) ∧
  (∀ similar fill value type dims, array586FillDimArgs similar fill value type dims = do
      let array ← similar type dims; fill array value) ∧
  (∀ allocate fill value type, array587FillZero allocate fill value type = do
      let array ← allocate type []; fill array value) ∧
  (∀ call dims, array633FilledVarargs call dims = call dims) ∧
  (∀ call type dims, array634FilledTypedVarargs call type dims = call type dims) ∧
  (∀ call float64 dims, array635FilledDefaultTuple call float64 dims = call float64 dims) ∧
  (∀ call type dims, array636FilledMapped call type dims =
      call type (dims.map dimArgValue)) ∧
  (∀ allocate fill felt type dims, array637FilledInteger allocate fill felt type dims = do
      let array ← allocate type dims; fill array (felt type)) ∧
  (∀ allocate fill felt type, array642FilledZero allocate fill felt type = do
      let array ← allocate type []; fill array (felt type)) ∧
  (∀ similar fill felt type dims, array647FilledDimArgs similar fill felt type dims = do
      let array ← similar type dims; fill array (felt type))

theorem arrayFillConstructorsCorrect : ArrayFillConstructorsCorrect := by
  simp [ArrayFillConstructorsCorrect, array482ToDimInteger, array483ToDimOneTo,
    array583FillVarargs, array584FillMapped, array585FillInteger, array586FillDimArgs,
    array587FillZero, array633FilledVarargs, array634FilledTypedVarargs,
    array635FilledDefaultTuple, array636FilledMapped, array637FilledInteger,
    array642FilledZero, array647FilledDimArgs]


def ArrayConversionConstructorsCorrect : Prop :=
  (∀ isType construct array, array657Convert isType construct array =
      if isType array then .ok array else construct array) ∧
  (∀ promote same left right a b, array659PromoteRule promote same left right a b =
      same (promote left right) a b) ∧
  (∀ size allocate copy source, array664ArrayConstructor size allocate copy source = do
      let dest ← allocate (size source); copy dest source) ∧
  (∀ similar copy source, array665AbstractConstructor similar copy source = do
      let dest ← similar source; copy dest source)

theorem arrayConversionConstructorsCorrect : ArrayConversionConstructorsCorrect := by
  simp [ArrayConversionConstructorsCorrect, array657Convert, array659PromoteRule,
    array664ArrayConstructor, array665AbstractConstructor]

def ArrayTypedCollectCorrect : Prop :=
  (∀ size collect iterator, array684Collect size collect iterator =
      collect iterator (size iterator)) ∧
  (∀ shape allocate copy iterator size, array686CollectSized shape allocate copy iterator size = do
      let dest ← allocate size (shape iterator size); copy dest iterator) ∧
  (∀ push iterator, array688CollectUnknown push iterator = array688PushAll push [] iterator) ∧
  (∀ similar container type, array697SimilarFor similar container type =
      similar container type) ∧
  (∀ iterator, array699SimilarShapeUnknown iterator = none) ∧
  (∀ iterator, array700SimilarShapeLength iterator = iterator.length) ∧
  (∀ axes iterator, array701SimilarShapeAxes axes iterator = axes iterator) ∧
  (∀ similar container type, array703SimilarForUnknown similar container type =
      similar container type 0) ∧
  (∀ similar container type length, array705SimilarForLength similar container type length =
      similar container type length) ∧
  (∀ similar container type axes, array707SimilarForShape similar container type axes =
      similar container type axes) ∧
  (∀ allocate type, array711ArrayForUnknown allocate type = allocate type 0) ∧
  (∀ allocate type length, array712ArrayForLength allocate type length = allocate type length) ∧
  (∀ similar type axes, array713ArrayForShape similar type axes = similar type axes) ∧
  (∀ shape allocate iterator size, array716ArrayFor shape allocate iterator size =
      allocate size (shape iterator size))

theorem arrayTypedCollectCorrect : ArrayTypedCollectCorrect := by
  simp [ArrayTypedCollectCorrect, array684Collect, array686CollectSized,
    array688CollectUnknown, array697SimilarFor, array699SimilarShapeUnknown,
    array700SimilarShapeLength, array701SimilarShapeAxes, array703SimilarForUnknown,
    array705SimilarForLength, array707SimilarForShape, array711ArrayForUnknown,
    array712ArrayForLength, array713ArrayForShape, array716ArrayFor]

end JuliaLean.ArrayCov
