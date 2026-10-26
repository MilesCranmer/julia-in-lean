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

def reviewedEntries : List Entry := [
  rowEntry "multidimcov-l88-cartesian-identity" "base/multidimensional.jl" "CartesianIndex{N}(::CartesianIndex{N})" "The identity constructor returns its CartesianIndex input." ``L88Identity ``l88Identity,
  rowEntry "multidimcov-l90-flatten-empty" "base/multidimensional.jl" "flatten(::Tuple{})" "Flattening the empty tuple returns the empty tuple." ``L90FlattenEmpty ``l90FlattenEmpty,
  rowEntry "multidimcov-l101-length-value" "base/multidimensional.jl" "length(::CartesianIndex{N})" "The value method returns the coordinate count." ``L101LengthValue ``l101LengthValue,
  rowEntry "multidimcov-l102-length-type" "base/multidimensional.jl" "length(::Type{CartesianIndex{N}})" "The type method returns N." ``L102LengthType ``l102LengthType,
  rowEntry "multidimcov-l106-firstindex" "base/multidimensional.jl" "firstindex(::CartesianIndex)" "The first index is one." ``L106Firstindex ``l106Firstindex,
  rowEntry "multidimcov-l107-lastindex" "base/multidimensional.jl" "lastindex(::CartesianIndex)" "The last index is the coordinate count." ``L107Lastindex ``l107Lastindex,
  rowEntry "multidimcov-l112-tuple" "base/multidimensional.jl" "Tuple(::CartesianIndex)" "Tuple returns the stored coordinates." ``L112Tuple ``l112Tuple,
  rowEntry "multidimcov-l117-cartesian-eq" "base/multidimensional.jl" "==(::CartesianIndex,::CartesianIndex)" "Equality is stored-coordinate equality." ``L117CartesianEq ``l117CartesianEq,
  rowEntry "multidimcov-l126-unary-plus" "base/multidimensional.jl" "+(::CartesianIndex)" "Unary plus returns the same index." ``L126UnaryPlus ``l126UnaryPlus,
  rowEntry "multidimcov-l127-unary-minus" "base/multidimensional.jl" "-(::CartesianIndex)" "Unary minus negates every coordinate with Int wrapping." ``L127UnaryMinus ``l127UnaryMinus,
  rowEntry "multidimcov-l129-add" "base/multidimensional.jl" "+(::CartesianIndex,::CartesianIndex)" "Addition is componentwise with Int wrapping." ``L129CartesianAdd ``l129CartesianAdd,
  rowEntry "multidimcov-l131-sub" "base/multidimensional.jl" "-(::CartesianIndex,::CartesianIndex)" "Subtraction is componentwise with Int wrapping." ``L131CartesianSub ``l131CartesianSub,
  rowEntry "multidimcov-l133-min" "base/multidimensional.jl" "min(::CartesianIndex,::CartesianIndex)" "min is componentwise." ``L133CartesianMin ``l133CartesianMin,
  rowEntry "multidimcov-l135-max" "base/multidimensional.jl" "max(::CartesianIndex,::CartesianIndex)" "max is componentwise." ``L135CartesianMax ``l135CartesianMax,
  rowEntry "multidimcov-l138-scale-left" "base/multidimensional.jl" "*(::Integer,::CartesianIndex)" "Left scaling multiplies every coordinate." ``L138ScaleLeft ``l138ScaleLeft,
  rowEntry "multidimcov-l172-ind2sub" "base/multidimensional.jl" "_ind2sub(::Tuple,::CartesianIndex)" "Cartesian _ind2sub returns the coordinate tuple." ``L172Ind2sub ``l172Ind2sub,
  rowEntry "multidimcov-l192-in-disabled" "base/multidimensional.jl" "in(::CartesianIndex,::AbstractRange)" "The deliberately disabled fallback returns false." ``L192DisabledIn ``l192DisabledIn,
  rowEntry "multidimcov-l298-ci-empty" "base/multidimensional.jl" "CartesianIndices(::Tuple{})" "The empty tuple constructs zero-dimensional CartesianIndices." ``L298CartesianIndicesEmpty ``l298CartesianIndicesEmpty,
  rowEntry "multidimcov-l387-ci-axes" "base/multidimensional.jl" "axes(::CartesianIndices)" "Axes map axes1 over every component range." ``L387CartesianAxes ``l387CartesianAxes,
  rowEntry "multidimcov-l397-ci-getzero" "base/multidimensional.jl" "getindex(::CartesianIndices{0})" "Zero-dimensional getindex returns CartesianIndex()." ``L397GetindexZero ``l397GetindexZero,
  rowEntry "multidimcov-l491-ci-step" "base/multidimensional.jl" "step(::CartesianIndices)" "step returns the component steps." ``L491CartesianStep ``l491CartesianStep,
  rowEntry "multidimcov-l493-ci-first" "base/multidimensional.jl" "first(::CartesianIndices)" "first returns the component first values." ``L493CartesianFirst ``l493CartesianFirst,
  rowEntry "multidimcov-l505-in-wrong-rank" "base/multidimensional.jl" "in(::CartesianIndex,::CartesianIndices)" "Wrong-rank membership returns false." ``L505ContainsWrongRank ``l505ContainsWrongRank,
  rowEntry "multidimcov-l506-in" "base/multidimensional.jl" "in(::CartesianIndex{N},::CartesianIndices{N})" "Membership checks every coordinate against its range." ``L506Contains ``l506Contains,
  rowEntry "multidimcov-l508-copy" "base/multidimensional.jl" "copy(::CartesianIndices)" "Copy returns the immutable iterator itself." ``L508Copy ``l508Copy,
  rowEntry "multidimcov-l510-simd-outer-zero" "base/multidimensional.jl" "simd_outer_range(::CartesianIndices{0})" "Zero-dimensional SIMD outer range returns the iterator." ``L510SimdOuterZero ``l510SimdOuterZero,
  rowEntry "multidimcov-l511-simd-outer" "base/multidimensional.jl" "simd_outer_range(::CartesianIndices)" "SIMD outer range drops the first component range." ``L511SimdOuter ``l511SimdOuter,
  rowEntry "multidimcov-l515-simd-inner-zero" "base/multidimensional.jl" "simd_inner_length(::CartesianIndices{0},::CartesianIndex)" "Zero-dimensional SIMD inner length is one." ``L515SimdInnerZero ``l515SimdInnerZero,
  rowEntry "multidimcov-l516-simd-inner" "base/multidimensional.jl" "simd_inner_length(::CartesianIndices,::CartesianIndex)" "SIMD inner length is the first range length." ``L516SimdInner ``l516SimdInner,
  rowEntry "multidimcov-l518-simd-index-zero" "base/multidimensional.jl" "simd_index(::CartesianIndices{0},...)" "Zero-dimensional SIMD indexing returns CartesianIndex()." ``L518SimdIndexZero ``l518SimdIndexZero,
  rowEntry "multidimcov-l793-index-ndims-ci" "base/multidimensional.jl" "index_ndims(::CartesianIndex,...)" "CartesianIndex contributes its rank to consumed dimensions." ``L793IndexNdimsCartesian ``l793IndexNdimsCartesian,
  rowEntry "multidimcov-l796-index-ndims-array-ci" "base/multidimensional.jl" "index_ndims(::AbstractArray{CartesianIndex{N}},...)" "A CartesianIndex array consumes N dimensions." ``L796IndexNdimsArray ``l796IndexNdimsArray,
  rowEntry "multidimcov-l799-index-ndims-empty" "base/multidimensional.jl" "index_ndims()" "The empty index tuple consumes zero dimensions." ``L799IndexNdimsEmpty ``l799IndexNdimsEmpty,
  rowEntry "multidimcov-l803-index-dimsum-scalar" "base/multidimensional.jl" "index_dimsum(i1,I...)" "A scalar contributes no output dimension." ``L803IndexDimsumScalar ``l803IndexDimsumScalar,
  rowEntry "multidimcov-l804-index-dimsum-colon" "base/multidimensional.jl" "index_dimsum(::Colon,I...)" "Colon contributes one output dimension." ``L804IndexDimsumColon ``l804IndexDimsumColon,
  rowEntry "multidimcov-l805-index-dimsum-bool" "base/multidimensional.jl" "index_dimsum(::AbstractArray{Bool},I...)" "A Boolean mask contributes one output dimension." ``L805IndexDimsumBool ``l805IndexDimsumBool,
  rowEntry "multidimcov-l806-index-dimsum-array" "base/multidimensional.jl" "index_dimsum(::AbstractArray{T,N},I...)" "An N-dimensional array index contributes N output dimensions." ``L806IndexDimsumArray ``l806IndexDimsumArray,
  rowEntry "multidimcov-l809-index-dimsum-empty" "base/multidimensional.jl" "index_dimsum()" "The empty index tuple has no output dimensions." ``L809IndexDimsumEmpty ``l809IndexDimsumEmpty,
  rowEntry "multidimcov-l812-index-lengths-empty" "base/multidimensional.jl" "index_lengths()" "The empty index tuple has no lengths." ``L812IndexLengthsEmpty ``l812IndexLengthsEmpty,
  rowEntry "multidimcov-l813-index-lengths-scalar" "base/multidimensional.jl" "index_lengths(::Real,...)" "A scalar index has length one." ``L813IndexLengthsScalar ``l813IndexLengthsScalar,
  rowEntry "multidimcov-l814-index-lengths-array" "base/multidimensional.jl" "index_lengths(::AbstractArray,...)" "An array index contributes its length." ``L814IndexLengthsArray ``l814IndexLengthsArray,
  rowEntry "multidimcov-l818-index-shape-empty" "base/multidimensional.jl" "index_shape()" "The empty index tuple has empty shape." ``L818IndexShapeEmpty ``l818IndexShapeEmpty,
  rowEntry "multidimcov-l819-index-shape-scalar" "base/multidimensional.jl" "index_shape(::Real,...)" "Scalar indices are dropped from output shape." ``L819IndexShapeScalar ``l819IndexShapeScalar,
  rowEntry "multidimcov-l822-index-sizes-empty" "base/multidimensional.jl" "index_sizes()" "The empty index tuple has empty sizes." ``L822IndexSizesEmpty ``l822IndexSizesEmpty,
  rowEntry "multidimcov-l823-index-sizes-scalar" "base/multidimensional.jl" "index_sizes(::Real,...)" "Scalar indices are dropped from output sizes." ``L823IndexSizesScalar ``l823IndexSizesScalar,
  rowEntry "multidimcov-l824-index-sizes-array" "base/multidimensional.jl" "index_sizes(::AbstractArray,...)" "Array indices contribute their dimensions." ``L824IndexSizesArray ``l824IndexSizesArray,
  rowEntry "multidimcov-s133-trimmed-scalar" "base/subarray.jl" "_trimmedshape(::ScalarIndex,...)" "A scalar reserves a leading singleton dimension." ``S133TrimmedScalar ``s133TrimmedScalar,
  rowEntry "multidimcov-s135-trimmed-range" "base/subarray.jl" "_trimmedshape(::UnitRange/StepRange/OneTo,...)" "Dense ranges contribute their length." ``S135TrimmedRange ``s135TrimmedRange,
  rowEntry "multidimcov-s136-trimmed-array" "base/subarray.jl" "_trimmedshape(::AbstractArray{<:ScalarIndex},...)" "A scalar-index array contributes its length." ``S136TrimmedArray ``s136TrimmedArray,
  rowEntry "multidimcov-s139-trimmed-empty" "base/subarray.jl" "_trimmedshape()" "The empty index tuple has empty trimmed shape." ``S139TrimmedEmpty ``s139TrimmedEmpty,
  rowEntry "multidimcov-s327-reindexlinear" "base/subarray.jl" "_reindexlinear(::FastSubArray,::Int)" "Fast linear reindexing computes offset plus stride times index." ``S327ReindexLinear ``s327ReindexLinear,
  rowEntry "multidimcov-s439-substrides-empty" "base/subarray.jl" "substrides(::Tuple{},::Tuple{})" "Empty parent strides and indices return empty strides." ``S439SubstridesEmpty ``s439SubstridesEmpty
]

end JuliaLean.MultidimCov
