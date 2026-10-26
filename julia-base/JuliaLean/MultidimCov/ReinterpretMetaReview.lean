import JuliaLean.ArrayCov.ReinterpretSimple
import JuliaLean.ArrayCov.ReinterpretShape
import JuliaLean.ArrayCov.ReinterpretCartesian
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry
open JuliaLean.ArrayCov

def RA190191Property : Prop :=
  (∀ call type array, reinterpret190Nested call type array = call type array.parent) ∧
  (∀ call type array, reinterpret191NestedReshape call type array = call true type array.parent)
theorem ra190191Property : RA190191Property := by
  simp [RA190191Property, reinterpret190Nested, reinterpret191NestedReshape]

def RA204232Property : Prop :=
  (∀ size strides array, reinterpret204Strides size strides array =
    strides (JInt.lit .i64 1) (size array)) ∧
  (∀ ndims strides length get array k, reinterpret205Stride ndims strides length get array k =
    if k ≤ ndims array then get (strides array) k else length array) ∧
  (∀ contiguous make size strides elsize target source reshaped array,
    reinterpret208Strides contiguous make size strides elsize target source reshaped array = do
      if contiguous array then return make (JInt.lit .i64 1) (size array)
      let parentStrides := strides array
      if target = source then return parentStrides
      let byteStrides := parentStrides.map (· * elsize array)
      if reshaped && target < source then
        return JInt.lit .i64 1 :: (← reinterpret222CheckedStrides byteStrides target)
      if byteStrides.getD 0 (JInt.lit .i64 0) != source then throw .noncontiguous
      let tail ← reinterpret222CheckedStrides byteStrides.tail target
      if reshaped then return tail else return JInt.lit .i64 1 :: tail) ∧
  (∀ elementSize, reinterpret222CheckedStrides [] elementSize = .ok []) ∧
  (∀ stride rest elementSize, reinterpret222CheckedStrides (stride :: rest) elementSize = do
    let quotient ← JInt.div stride elementSize |>.mapError fun _ => .arithmetic
    let remainder ← JInt.remInt stride elementSize |>.mapError fun _ => .arithmetic
    if remainder.val != 0 then throw .nonIntegralStride
    let tail ← reinterpret222CheckedStrides rest elementSize
    pure (quotient :: tail)) ∧
  (∀ contiguous array, reinterpret229Contiguous contiguous array = contiguous array.parent) ∧
  (∀ similar array type dims, reinterpret231Similar similar array type dims =
    similar array.parent type dims) ∧
  (∀ similar parentType dims, reinterpret232SimilarType similar parentType dims =
    similar parentType dims)
theorem ra204232Property : RA204232Property := by
  simp [RA204232Property, reinterpret204Strides, reinterpret205Stride,
    reinterpret208Strides, reinterpret222CheckedStrides, reinterpret229Contiguous,
    reinterpret231Similar, reinterpret232SimilarType]

def RA234241Property : Prop :=
  (∀ sub source target readable, reinterpret234CheckReadable sub source target readable =
    if !readable && !sub target source then .error .padding else .ok ()) ∧
  (∀ sub source target writable, reinterpret241CheckWritable sub source target writable =
    if !writable && !sub source target then .error .padding else .ok ())
theorem ra234241Property : RA234241Property := by
  simp [RA234241Property, reinterpret234CheckReadable, reinterpret241CheckWritable]

def RA260270Property : Prop :=
  (∀ style parent, reinterpret260IndexStyle style parent =
    if style parent = .linear then .linear else .cartesian) ∧
  (∀ style parent target source, reinterpret263IndexStyleReshaped style parent target source = do
    if target < source then
      if style parent = .linear then
        let k ← JInt.div source target |>.mapError fun _ => .arithmetic
        return .staticCartesian k
      return .cartesian
    return style parent) ∧
  (∀ k, reinterpret270CombineStyle k = k)
theorem ra260270Property : RA260270Property := by
  simp [RA260270Property, reinterpret260IndexStyle, reinterpret263IndexStyleReshaped,
    reinterpret270CombineStyle]

def RA276279Property : Prop :=
  (∀ index, reinterpret276ToIndex index = index) ∧
  (∀ k index, reinterpret277NextIndex k index =
    if index.i < k then ⟨index.i + JInt.lit .i64 1, index.j⟩
    else ⟨JInt.lit .i64 1, index.j + JInt.lit .i64 1⟩) ∧
  (∀ k index, reinterpret279PrevIndex k index =
    if JInt.lit .i64 1 < index.i then ⟨index.i - JInt.lit .i64 1, index.j⟩
    else ⟨k, index.j - JInt.lit .i64 1⟩)
theorem ra276279Property : RA276279Property := by
  simp [RA276279Property, reinterpret276ToIndex, reinterpret277NextIndex,
    reinterpret279PrevIndex]

def RA285326Property : Prop :=
  (∀ k indices, reinterpret285IndicesConstructor k indices =
    if JInt.lit .i64 1 < k then .ok ⟨k, indices⟩ else .error .assertionError) ∧
  (∀ each construct k array, reinterpret287EachIndex each construct k array =
    construct k (each 1 array.parent)) ∧
  (∀ each axes mismatch style first rest, reinterpret288EachIndex each axes mismatch style first rest =
    let iter := each style first
    let other := rest.map (each style)
    if other.all (· == iter) then .ok iter else mismatch (axes first) (rest.map axes)) ∧
  (∀ iter, reinterpret295IndicesSize iter = (iter.k, JInt.lit .i64 iter.indices2.length)) ∧
  (∀ oneto iter, reinterpret296IndicesAxes oneto iter = (oneto iter.k, iter.indices2)) ∧
  (∀ first iter, reinterpret298IndicesFirst first iter = ⟨JInt.lit .i64 1, first iter.indices2⟩) ∧
  (∀ last iter, reinterpret299IndicesLast last iter = ⟨iter.k, last iter.indices2⟩) ∧
  (∀ bounds get iter i j, reinterpret301GetIndex bounds get iter i j = do
    if bounds iter i j then pure () else throw .bounds
    let item ← get iter.indices2 j
    pure ⟨i, item⟩) ∧
  (∀ iterate iter, reinterpret306Iterate iterate iter =
    match iterate iter.indices2 with
    | none => none
    | some (item, state) =>
      some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))) ∧
  (∀ iterate iter state1 item2 state2,
    reinterpret313IterateState iterate iter state1 item2 state2 =
    if state1 < iter.k then
      let item1 := state1 + JInt.lit .i64 1
      some (⟨item1, item2⟩, (item1, item2, state2))
    else match iterate iter.indices2 state2 with
      | none => none
      | some (item, state) =>
        some (⟨JInt.lit .i64 1, item⟩, (JInt.lit .i64 1, item, state))) ∧
  (∀ iter, reinterpret324SimdOuter iter = iter.indices2) ∧
  (∀ iter outer, reinterpret325SimdLength iter outer = iter.k) ∧
  (∀ k last i1, reinterpret326SimdIndex k last i1 = ⟨i1 + JInt.lit .i64 1, last⟩)
theorem ra285326Property : RA285326Property := by
  simp [RA285326Property, reinterpret285IndicesConstructor, reinterpret287EachIndex,
    reinterpret288EachIndex, reinterpret295IndicesSize, reinterpret296IndicesAxes,
    reinterpret298IndicesFirst, reinterpret299IndicesLast, reinterpret301GetIndex,
    reinterpret306Iterate, reinterpret313IterateState, reinterpret324SimdOuter,
    reinterpret325SimdLength, reinterpret326SimdIndex]
  constructor <;> intros <;> rfl

def RA330362Property : Prop :=
  (∀ fallback array indices, reinterpret330MaybeReshapeFallback fallback array indices =
    fallback 0 array indices) ∧
  (∀ array indices, reinterpret331MaybeReshapeIdentity array indices = array) ∧
  (∀ get array indices, reinterpret334GetFallback get array indices = get array indices) ∧
  (∀ set array value indices, reinterpret338SetFallback set array value indices =
    set array value indices) ∧
  (∀ first trailing get style array index,
    reinterpret344GetCartesian first trailing get style array index =
    get array ((first array + index.i - JInt.lit .i64 1) :: trailing style array index)) ∧
  (∀ first trailing set style array value index,
    reinterpret349SetCartesian first trailing set style array value index =
    set array value ((first array + index.i - JInt.lit .i64 1) :: trailing style array index)) ∧
  (∀ each axes first cart style array index,
    reinterpret356Trailing each axes first cart style array index =
    let k := index.j - first (each style array)
    let tailAxes := (axes array).tail
    match tailAxes with
    | [axis] => [first axis + k]
    | _ => cart tailAxes (k + JInt.lit .i64 1)) ∧
  (∀ each style parent array, reinterpret362EachIndex each style parent array =
    each style (parent array))
theorem ra330362Property : RA330362Property := by
  simp [RA330362Property, reinterpret330MaybeReshapeFallback,
    reinterpret331MaybeReshapeIdentity, reinterpret334GetFallback,
    reinterpret338SetFallback, reinterpret344GetCartesian, reinterpret349SetCartesian,
    reinterpret356Trailing, reinterpret362EachIndex]
  intros
  rfl

def RA366369Property : Prop :=
  (∀ array, reinterpret366Parent array = array.parent) ∧
  (∀ ids array, reinterpret367DataIds ids array = ids array.parent) ∧
  (∀ copy call type array, reinterpret368Unalias copy call type array =
    call type (copy array.parent)) ∧
  (∀ copy call type array, reinterpret369UnaliasReshape copy call type array =
    call true type (copy array.parent))
theorem ra366369Property : RA366369Property := by
  simp [RA366369Property, reinterpret366Parent, reinterpret367DataIds,
    reinterpret368Unalias, reinterpret369UnaliasReshape]

def RA371410Property : Prop :=
  (∀ size singleton source target array, reinterpret371Size size singleton source target array = do
    let parentSize := size array
    let first := parentSize.getD 0 (JInt.lit .i64 0)
    let size1 ← if singleton then pure first else
      JInt.div (first * source) target |>.mapError fun _ => .arithmetic
    pure (size1 :: parentSize.tail)) ∧
  (∀ size source target array, reinterpret376SizeReshaped size source target array = do
    let parentSize := size array
    if target < source then
      let ratio ← JInt.div source target |>.mapError fun _ => .arithmetic
      return ratio :: parentSize
    if source < target then return parentSize.tail
    return parentSize) ∧
  (∀ array, reinterpret382SizeZero array = []) ∧
  (∀ axes singleton source target array, reinterpret384Axes axes singleton source target array = do
    let parentAxes := axes array
    let axis := parentAxes.getD 0 ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩
    let size1 ← if singleton then pure axis.length else
      JInt.div (axis.length * source) target |>.mapError fun _ => .arithmetic
    pure (⟨axis.first, size1⟩ :: parentAxes.tail)) ∧
  (∀ axes source target array, reinterpret390AxesReshaped axes source target array = do
    let parentAxes := axes array
    if target < source then
      let ratio ← JInt.div source target |>.mapError fun _ => .arithmetic
      return ⟨JInt.lit .i64 1, ratio⟩ :: parentAxes
    if source < target then return parentAxes.tail
    return parentAxes) ∧
  (∀ array, reinterpret396AxesZero array = []) ∧
  (∀ offset array, reinterpret398HasOffset offset array = offset array.parent) ∧
  (∀ parent target source, reinterpret400Elsize parent target source =
    if target = source then parent else target) ∧
  (∀ convert source array, reinterpret407Cconvert convert source array =
    convert source array.parent) ∧
  (∀ convert source target array, reinterpret408UnsafeConvert convert source target array =
    ⟨target, convert source array.parent⟩) ∧
  (∀ scalar reinterpret parentGet first get source target array,
    reinterpret410GetZero scalar reinterpret parentGet first get source target array =
    if scalar target source then reinterpret target (parentGet array)
    else get array (first array))
theorem ra371410Property : RA371410Property := by
  simp [RA371410Property, reinterpret371Size, reinterpret376SizeReshaped,
    reinterpret382SizeZero, reinterpret384Axes, reinterpret390AxesReshaped,
    reinterpret396AxesZero, reinterpret398HasOffset, reinterpret400Elsize,
    reinterpret407Cconvert, reinterpret408UnsafeConvert, reinterpret410GetZero]

def RA418431Property : Prop :=
  (∀ check parent target source array, reinterpret418CheckPtr check parent target source array =
    if target = source then false else check (parent array)) ∧
  (∀ check parent array, reinterpret422CheckPtrReshaped check parent array =
    check (parent array)) ∧
  (∀ check parent array, reinterpret423CheckPtrSubarray check parent array =
    check (parent array)) ∧
  (∀ array, reinterpret424CheckPtrDense array = true) ∧
  (∀ array, reinterpret425CheckPtrAbstract array = false) ∧
  (∀ first get array, reinterpret427GetZero first get array = get array (first array)) ∧
  (∀ bounds ptr assigned array indices, reinterpret429IsAssigned bounds ptr assigned array indices =
    (bounds array indices && (ptr array || assigned array indices))) ∧
  (∀ assigned array index, reinterpret430IsAssignedCartesian assigned array index =
    assigned array.parent index.j) ∧
  (∀ array indices, reinterpret431AssignedRa array indices = true)
theorem ra418431Property : RA418431Property := by
  simp [RA418431Property, reinterpret418CheckPtr, reinterpret422CheckPtrReshaped,
    reinterpret423CheckPtrSubarray, reinterpret424CheckPtrDense,
    reinterpret425CheckPtrAbstract, reinterpret427GetZero, reinterpret429IsAssigned,
    reinterpret430IsAssignedCartesian, reinterpret431AssignedRa]

private def raMetaEntry (id fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/reinterpretarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def reinterpretMetaReviewEntries : List Entry := [
  raMetaEntry "multidimcov-reinterpretarray-nested" "reinterpret nested wrappers" "Nested reinterpret methods unwrap parent and preserve reshape dispatch." "base/reinterpretarray.jl:190-191" ``RA190191Property ``ra190191Property,
  raMetaEntry "multidimcov-reinterpretarray-strides" "strides, stride, _checked_strides, similar, _checkcontiguous" "Stride and allocation methods preserve source branch order, exact division checks, and parent delegation." "base/reinterpretarray.jl:204-232" ``RA204232Property ``ra204232Property,
  raMetaEntry "multidimcov-reinterpretarray-padding-checks" "check_readable, check_writable" "Read and write checks use the cached flag and recomputed padding relation in source order." "base/reinterpretarray.jl:234-251" ``RA234241Property ``ra234241Property,
  raMetaEntry "multidimcov-reinterpretarray-index-style" "IndexStyle methods" "Index styles preserve parent linearity and select static Cartesian style only for channel expansion." "base/reinterpretarray.jl:260-270" ``RA260270Property ``ra260270Property,
  raMetaEntry "multidimcov-reinterpretarray-scartesian-step" "to_index, nextind, prevind" "SCartesian index conversion and stepping preserve both components and wrap the static inner coordinate." "base/reinterpretarray.jl:276-280" ``RA276279Property ``ra276279Property,
  raMetaEntry "multidimcov-reinterpretarray-scartesian-iterate" "SCartesianIndices2 interface and iteration" "The static Cartesian iterator validates K, checks shared indices, exposes axes, and advances inner then outer state." "base/reinterpretarray.jl:285-328" ``RA285326Property ``ra285326Property,
  raMetaEntry "multidimcov-reinterpretarray-scartesian-routing" "_maybe_reshape, _getindex, _setindex!, _scartesian2_trailing, eachindex" "Cartesian routing delegates fallbacks and converts the trailing linear coordinate through array axes." "base/reinterpretarray.jl:330-362" ``RA330362Property ``ra330362Property,
  raMetaEntry "multidimcov-reinterpretarray-parent-copy" "parent, dataids, unaliascopy" "Parent metadata and both unaliascopy variants preserve exact unwrap, copy, and reconstruction order." "base/reinterpretarray.jl:366-369" ``RA366369Property ``ra366369Property,
  raMetaEntry "multidimcov-reinterpretarray-shape" "size, axes, has_offset_axes, elsize, pointer conversion, scalar getindex" "Shape and pointer methods preserve element-size branches, axes, wrapping arithmetic, parent calls, and scalar dispatch." "base/reinterpretarray.jl:371-416" ``RA371410Property ``ra371410Property,
  raMetaEntry "multidimcov-reinterpretarray-pointer-assigned" "check_ptr_indexable, zero-dimensional getindex, isassigned" "Pointer eligibility and assignment queries preserve parent recursion, bounds short-circuiting, and static Cartesian delegation." "base/reinterpretarray.jl:418-431" ``RA418431Property ``ra418431Property
]

end JuliaLean.MultidimCov
