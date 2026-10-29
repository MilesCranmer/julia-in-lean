import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Reviewed exact mirrors from base/multidimensional.jl. -/

def L88Identity : Prop := ∀ p : CartesianInput,
  runCartesian .constructIdentity p = .coords p.a
theorem l88Identity : L88Identity := by intro; rfl

def L90FlattenEmpty : Prop := ∀ p : CartesianInput,
  runCartesian .flattenEmpty p = .coords []
theorem l90FlattenEmpty : L90FlattenEmpty := by intro; rfl

def L101LengthValue : Prop := ∀ p : CartesianInput,
  runCartesian .length p = .natural p.a.length
theorem l101LengthValue : L101LengthValue := by intro; rfl

def L102LengthType : Prop := ∀ p : CartesianInput,
  runCartesian .length p = .natural p.a.length
theorem l102LengthType : L102LengthType := by intro; rfl

def L106Firstindex : Prop := ∀ p : CartesianInput,
  runCartesian .firstindex p = .scalar (JInt.lit .i64 1)
theorem l106Firstindex : L106Firstindex := by intro; rfl

def L107Lastindex : Prop := ∀ p : CartesianInput,
  runCartesian .lastindex p = .scalar (JInt.wrap .i64 p.a.length)
theorem l107Lastindex : L107Lastindex := by intro; rfl

def L112Tuple : Prop := ∀ p : CartesianInput,
  runCartesian .tuple p = .coords p.a
theorem l112Tuple : L112Tuple := by intro; rfl

def L117CartesianEq : Prop := ∀ p : CartesianInput,
  runCartesian .equality p = .boolean (p.a = p.b)
theorem l117CartesianEq : L117CartesianEq := by intro; rfl

def L126UnaryPlus : Prop := ∀ p : CartesianInput,
  runCartesian .unaryPlus p = .coords p.a
theorem l126UnaryPlus : L126UnaryPlus := by intro; rfl

def L127UnaryMinus : Prop := ∀ p : CartesianInput,
  runCartesian .neg p = .coords (p.a.map (- ·))
theorem l127UnaryMinus : L127UnaryMinus := by intro; rfl

def L129CartesianAdd : Prop := ∀ p : CartesianInput,
  runCartesian .add p = .coords (List.zipWith (· + ·) p.a p.b)
theorem l129CartesianAdd : L129CartesianAdd := by intro; rfl

def L131CartesianSub : Prop := ∀ p : CartesianInput,
  runCartesian .sub p = .coords (List.zipWith (· - ·) p.a p.b)
theorem l131CartesianSub : L131CartesianSub := by intro; rfl

def L133CartesianMin : Prop := ∀ p : CartesianInput,
  runCartesian .min p = .coords (cartesianMin p.a p.b)
theorem l133CartesianMin : L133CartesianMin := by intro; rfl

def L135CartesianMax : Prop := ∀ p : CartesianInput,
  runCartesian .max p = .coords (cartesianMax p.a p.b)
theorem l135CartesianMax : L135CartesianMax := by intro; rfl

def L138ScaleLeft : Prop := ∀ p : CartesianInput,
  runCartesian .scaleLeft p = .coords (p.a.map (p.value * ·))
theorem l138ScaleLeft : L138ScaleLeft := by intro; rfl

def L172Ind2sub : Prop := ∀ p : CartesianInput,
  runCartesian .ind2sub p = .coords p.a
theorem l172Ind2sub : L172Ind2sub := by intro; rfl

def L192DisabledIn : Prop := ∀ p : CartesianInput,
  runCartesian .inDisabled p = .boolean false
theorem l192DisabledIn : L192DisabledIn := by intro; rfl

def L298CartesianIndicesEmpty : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .empty p = .axes []
theorem l298CartesianIndicesEmpty : L298CartesianIndicesEmpty := by intro; rfl

def L387CartesianAxes : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .axes p = .axes (p.axes.map fun a => oneToAxis (JInt.wrap .i64 a.len))
theorem l387CartesianAxes : L387CartesianAxes := by intro; rfl

def L397GetindexZero : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .getZero p = .coords []
theorem l397GetindexZero : L397GetindexZero := by intro; rfl

def L491CartesianStep : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .step p = .coords (p.axes.map (·.step))
theorem l491CartesianStep : L491CartesianStep := by intro; rfl

def L493CartesianFirst : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .first p = .coords (p.axes.map (·.first))
theorem l493CartesianFirst : L493CartesianFirst := by intro; rfl

def L505ContainsWrongRank : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .containsWrongRank p = .boolean false
theorem l505ContainsWrongRank : L505ContainsWrongRank := by intro; rfl

def L506Contains : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .contains p = .boolean
    (p.coords.length = p.axes.length && (p.axes.zip p.coords).all fun (a, x) => (axisValues a).contains x)
theorem l506Contains : L506Contains := by intro; rfl

def L508Copy : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .copy p = .axes p.axes
theorem l508Copy : L508Copy := by intro; rfl

def L510SimdOuterZero : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .simdOuterZero p = .axes p.axes
theorem l510SimdOuterZero : L510SimdOuterZero := by intro; rfl

def L511SimdOuter : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .simdOuter p = .axes p.axes.tail
theorem l511SimdOuter : L511SimdOuter := by intro; rfl

def L515SimdInnerZero : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .simdInnerZero p = .natural 1
theorem l515SimdInnerZero : L515SimdInnerZero := by intro; rfl

def L516SimdInner : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .simdInner p = .natural (p.axes.head?.map (·.len) |>.getD 0)
theorem l516SimdInner : L516SimdInner := by intro; rfl

def L518SimdIndexZero : Prop := ∀ p : CartesianIndicesInput,
  runCartesianIndices .simdIndexZero p = .coords []
theorem l518SimdIndexZero : L518SimdIndexZero := by intro; rfl

def L793IndexNdimsCartesian : Prop := ∀ n rest,
  indexNdims (.cartesian n :: rest) = n + indexNdims rest
theorem l793IndexNdimsCartesian : L793IndexNdimsCartesian := by
  unfold L793IndexNdimsCartesian
  intros
  rfl

def L796IndexNdimsArray : Prop := ∀ n dims rest,
  indexNdims (.cartesianArray n dims :: rest) = n + indexNdims rest
theorem l796IndexNdimsArray : L796IndexNdimsArray := by
  unfold L796IndexNdimsArray
  intros
  rfl

def L799IndexNdimsEmpty : Prop := ∀ (_ : Unit), indexNdims [] = 0
theorem l799IndexNdimsEmpty : L799IndexNdimsEmpty := by
  unfold L799IndexNdimsEmpty
  intros
  rfl

def L803IndexDimsumScalar : Prop := ∀ rest,
  indexDims (.scalar :: rest) = indexDims rest
theorem l803IndexDimsumScalar : L803IndexDimsumScalar := by
  unfold L803IndexDimsumScalar
  intros
  rfl

def L804IndexDimsumColon : Prop := ∀ n rest,
  indexDims (.colon n :: rest) = true :: indexDims rest
theorem l804IndexDimsumColon : L804IndexDimsumColon := by
  unfold L804IndexDimsumColon
  intros
  rfl

def L805IndexDimsumBool : Prop := ∀ n dims rest,
  indexDims (.boolArray n dims :: rest) = true :: indexDims rest
theorem l805IndexDimsumBool : L805IndexDimsumBool := by
  unfold L805IndexDimsumBool
  intros
  rfl

def L806IndexDimsumArray : Prop := ∀ dims rest,
  indexDims (.array dims :: rest) = List.replicate dims.length true ++ indexDims rest
theorem l806IndexDimsumArray : L806IndexDimsumArray := by
  unfold L806IndexDimsumArray
  intros
  rfl

def L809IndexDimsumEmpty : Prop := ∀ (_ : Unit), indexDims [] = []
theorem l809IndexDimsumEmpty : L809IndexDimsumEmpty := by
  unfold L809IndexDimsumEmpty
  intros
  rfl

def L812IndexLengthsEmpty : Prop := ∀ (_ : Unit), indexLengths [] = []
theorem l812IndexLengthsEmpty : L812IndexLengthsEmpty := by
  unfold L812IndexLengthsEmpty
  intros
  rfl

def L813IndexLengthsScalar : Prop := ∀ rest,
  indexLengths (.scalar :: rest) = 1 :: indexLengths rest
theorem l813IndexLengthsScalar : L813IndexLengthsScalar := by
  unfold L813IndexLengthsScalar
  intros
  rfl

def L814IndexLengthsArray : Prop := ∀ dims rest,
  indexLengths (.array dims :: rest) = dims.foldl (· * ·) 1 :: indexLengths rest
theorem l814IndexLengthsArray : L814IndexLengthsArray := by
  unfold L814IndexLengthsArray
  intros
  rfl

def L818IndexShapeEmpty : Prop := ∀ (_ : Unit), indexShape [] = []
theorem l818IndexShapeEmpty : L818IndexShapeEmpty := by
  unfold L818IndexShapeEmpty
  intros
  rfl

def L819IndexShapeScalar : Prop := ∀ rest,
  indexShape (.scalar :: rest) = indexShape rest
theorem l819IndexShapeScalar : L819IndexShapeScalar := by
  unfold L819IndexShapeScalar
  intros
  rfl

def L822IndexSizesEmpty : Prop := ∀ (_ : Unit), indexShape [] = []
theorem l822IndexSizesEmpty : L822IndexSizesEmpty := by
  unfold L822IndexSizesEmpty
  intros
  rfl

def L823IndexSizesScalar : Prop := ∀ rest,
  indexShape (.scalar :: rest) = indexShape rest
theorem l823IndexSizesScalar : L823IndexSizesScalar := by
  unfold L823IndexSizesScalar
  intros
  rfl

def L824IndexSizesArray : Prop := ∀ dims rest,
  indexShape (.array dims :: rest) = dims ++ indexShape rest
theorem l824IndexSizesArray : L824IndexSizesArray := by
  unfold L824IndexSizesArray
  intros
  rfl

/-! Reviewed exact mirrors from base/subarray.jl. -/

def S133TrimmedScalar : Prop := ∀ x rest,
  trimmedShape (.scalar x :: rest) = 1 :: trimmedShape rest
theorem s133TrimmedScalar : S133TrimmedScalar := by
  unfold S133TrimmedScalar
  intros
  rfl

def S135TrimmedRange : Prop := ∀ a rest,
  trimmedShape (.range a :: rest) = a.len :: trimmedShape rest
theorem s135TrimmedRange : S135TrimmedRange := by
  unfold S135TrimmedRange
  intros
  rfl

def S136TrimmedArray : Prop := ∀ axes values rest,
  trimmedShape (.array axes values :: rest) = values.length :: trimmedShape rest
theorem s136TrimmedArray : S136TrimmedArray := by
  unfold S136TrimmedArray
  intros
  rfl

def S139TrimmedEmpty : Prop := ∀ (_ : Unit), trimmedShape [] = []
theorem s139TrimmedEmpty : S139TrimmedEmpty := by
  unfold S139TrimmedEmpty
  intros
  rfl

def S327ReindexLinear : Prop := ∀ view i,
  view.linear = true → reindexLinear view i = view.offset + view.stride * i
theorem s327ReindexLinear : S327ReindexLinear := by
  intro view i h
  simp [reindexLinear, h]

def S439SubstridesEmpty : Prop := ∀ (_ : Unit), subStrides [] [] = .ok []
theorem s439SubstridesEmpty : S439SubstridesEmpty := by
  unfold S439SubstridesEmpty
  intros
  rfl

private def rowEntry (id file fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := file
    juliaFns := [fn]
    statement
    source := "method body and obvious return-value invariant at the cited source line"
    status := .proven
    prop
    thm := some theoremName }

def reviewedEntries : List Entry := []

end JuliaLean.MultidimCov
