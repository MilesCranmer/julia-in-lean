import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReshapedFaithfulB

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

def m255 (parent : V → P) (similar : P → T → D → JResult R)
    (view : V) (elementType : T) (dims : D) : JResult R := similar (parent view) elementType dims
def P255 : Prop := ∀ {V P T D R : Type} (parent : V → P)
    (similar : P → T → D → JResult R) view elementType dims,
  m255 parent similar view elementType dims = similar (parent view) elementType dims
theorem p255 : P255 := by unfold P255; intros; rfl

def m256 (parentType : TA → P) (similar : P → D → JResult R) (type : TA) (dims : D) : JResult R :=
  similar (parentType type) dims
def P256 : Prop := ∀ {TA P D R : Type} (parentType : TA → P)
    (similar : P → D → JResult R) type dims,
  m256 parentType similar type dims = similar (parentType type) dims
theorem p256 : P256 := by unfold P256; intros; rfl

def m262 (typeOf : V → Ty) (parent : V → P) (dims : V → D) (mi : V → MI)
    (unalias : P → JResult P2) (construct : Ty → P2 → D → MI → JResult R) (view : V) : JResult R := do
  let copied ← unalias (parent view)
  construct (typeOf view) copied (dims view) (mi view)
def P262 : Prop := ∀ {V Ty P D MI P2 R : Type} (typeOf : V → Ty) (parent : V → P)
    (dims : V → D) (mi : V → MI) (unalias : P → JResult P2)
    (construct : Ty → P2 → D → MI → JResult R) view,
  m262 typeOf parent dims mi unalias construct view = do
    let copied ← unalias (parent view)
    construct (typeOf view) copied (dims view) (mi view)
theorem p262 : P262 := by unfold P262; intros; rfl

def m272 (lastAxis : AX → JResult A) (first : A → JResult I)
    (add : I → N → JResult I) (axes : AX) (index : N) : JResult (List I) := do
  let axis ← lastAxis axes
  let origin ← first axis
  let value ← add origin index
  .ok [value]
def P272 : Prop := ∀ {AX A I N : Type} (lastAxis : AX → JResult A)
    (first : A → JResult I) (add : I → N → JResult I) axes index,
  m272 lastAxis first add axes index = do
    let axis ← lastAxis axes
    let origin ← first axis
    let value ← add origin index
    .ok [value]
theorem p272 : P272 := by unfold P272; intros; rfl

def m273 (firstSize : S → JResult N) (divrem : I → N → JResult (I × I))
    (firstAxis : AX → JResult A) (first : A → JResult I) (add : I → I → JResult I)
    (tailAxes : AX → JResult AX) (tailSizes : S → JResult S)
    (recurse : AX → S → I → JResult (List I)) (axes : AX) (sizes : S) (index : I) : JResult (List I) := do
  let size ← firstSize sizes
  let (quotient, remainder) ← divrem index size
  let axis ← firstAxis axes
  let origin ← first axis
  let head ← add remainder origin
  let remainingAxes ← tailAxes axes
  let remainingSizes ← tailSizes sizes
  let tail ← recurse remainingAxes remainingSizes quotient
  .ok (head :: tail)
def P273 : Prop := ∀ {S N I AX A : Type} (firstSize : S → JResult N)
    (divrem : I → N → JResult (I × I)) (firstAxis : AX → JResult A)
    (first : A → JResult I) (add : I → I → JResult I)
    (tailAxes : AX → JResult AX) (tailSizes : S → JResult S)
    (recurse : AX → S → I → JResult (List I)) axes sizes index,
  m273 firstSize divrem firstAxis first add tailAxes tailSizes recurse axes sizes index = do
    let size ← firstSize sizes
    let (quotient, remainder) ← divrem index size
    let axis ← firstAxis axes
    let origin ← first axis
    let head ← add remainder origin
    let remainingAxes ← tailAxes axes
    let remainingSizes ← tailSizes sizes
    let tail ← recurse remainingAxes remainingSizes quotient
    .ok (head :: tail)
theorem p273 : P273 := by unfold P273; intros; rfl

def m294 (checkbounds : V → Int → JResult Unit) (firstView : V → JResult Int)
    (parent : V → P) (firstParent : P → JResult Int) (subtract add : Int → Int → JResult Int)
    (getindex : P → Int → JResult T) (view : V) (index : Int) : JResult T := do
  checkbounds view index
  let viewOrigin ← firstView view
  let delta ← subtract index viewOrigin
  let p := parent view
  let parentOrigin ← firstParent p
  let parentIndex ← add delta parentOrigin
  getindex p parentIndex
def P294 : Prop := ∀ {V P T : Type} (checkbounds : V → Int → JResult Unit)
    (firstView : V → JResult Int) (parent : V → P) (firstParent : P → JResult Int)
    (subtract add : Int → Int → JResult Int) (getindex : P → Int → JResult T) view index,
  m294 checkbounds firstView parent firstParent subtract add getindex view index = do
    checkbounds view index
    let viewOrigin ← firstView view
    let delta ← subtract index viewOrigin
    let p := parent view
    let parentOrigin ← firstParent p
    let parentIndex ← add delta parentOrigin
    getindex p parentIndex
theorem p294 : P294 := by unfold P294; intros; rfl

def m300 (checkbounds : V → I → JResult Unit) (unsafeGet : V → I → JResult T)
    (view : V) (indices : I) : JResult T := do checkbounds view indices; unsafeGet view indices
def P300 : Prop := ∀ {V I T : Type} (checkbounds : V → I → JResult Unit)
    (unsafeGet : V → I → JResult T) view indices,
  m300 checkbounds unsafeGet view indices = do checkbounds view indices; unsafeGet view indices
theorem p300 : P300 := by unfold P300; intros; rfl

def m304 (parent : V → P) (parentIndex : RI → I) (checkbounds : P → I → JResult Unit)
    (getindex : P → I → JResult T) (view : V) (index : RI) : JResult T := do
  let p := parent view
  let i := parentIndex index
  checkbounds p i
  getindex p i
def P304 : Prop := ∀ {V P RI I T : Type} (parent : V → P) (parentIndex : RI → I)
    (checkbounds : P → I → JResult Unit) (getindex : P → I → JResult T) view index,
  m304 parent parentIndex checkbounds getindex view index = do
    let p := parent view
    let i := parentIndex index
    checkbounds p i
    getindex p i
theorem p304 : P304 := by unfold P304; intros; rfl

def m310 (parent : V → P) (axes : P → JResult AX) (size : V → JResult S)
    (sub2ind : S → I → JResult L) (offset : L → AX → JResult L)
    (mi : V → MI) (ind2sub : AX → MI → L → JResult PI)
    (read : P → PI → JResult T) (view : V) (indices : I) : JResult T := do
  let p := parent view
  let parentAxes ← axes p
  let shape ← size view
  let linear ← sub2ind shape indices
  let adjusted ← offset linear parentAxes
  let parentIndices ← ind2sub parentAxes (mi view) adjusted
  read p parentIndices
def P310 : Prop := ∀ {V P AX S I L MI PI T : Type} (parent : V → P)
    (axes : P → JResult AX) (size : V → JResult S) (sub2ind : S → I → JResult L)
    (offset : L → AX → JResult L) (mi : V → MI) (ind2sub : AX → MI → L → JResult PI)
    (read : P → PI → JResult T) view indices,
  m310 parent axes size sub2ind offset mi ind2sub read view indices = do
    let p := parent view
    let parentAxes ← axes p
    let shape ← size view
    let linear ← sub2ind shape indices
    let adjusted ← offset linear parentAxes
    let parentIndices ← ind2sub parentAxes (mi view) adjusted
    read p parentIndices
theorem p310 : P310 := by unfold P310; intros; rfl

def m316 (read : A → I → JResult T) (array : A) (index : I) : JResult T := read array index
def P316 : Prop := ∀ {A I T : Type} (read : A → I → JResult T) array index,
  m316 read array index = read array index
theorem p316 : P316 := by unfold P316; intros; rfl
def m317 (read : A → I → JResult T) (array : A) (indices : I) : JResult T := read array indices
def P317 : Prop := ∀ {A I T : Type} (read : A → I → JResult T) array indices,
  m317 read array indices = read array indices
theorem p317 : P317 := by unfold P317; intros; rfl

def m319 (checkbounds : V → Int → JResult Unit) (firstView : V → JResult Int)
    (parent : V → P) (firstParent : P → JResult Int) (subtract add : Int → Int → JResult Int)
    (convert : X → JResult T) (write : P → T → Int → JResult P)
    (view : V) (value : X) (index : Int) : JResult X := do
  checkbounds view index
  let vo ← firstView view
  let delta ← subtract index vo
  let p := parent view
  let po ← firstParent p
  let pi ← add delta po
  let converted ← convert value
  let _ ← write p converted pi
  .ok value
def P319 : Prop := ∀ {V P X T : Type} (checkbounds : V → Int → JResult Unit)
    (firstView : V → JResult Int) (parent : V → P) (firstParent : P → JResult Int)
    (subtract add : Int → Int → JResult Int) (convert : X → JResult T)
    (write : P → T → Int → JResult P) view value index,
  m319 checkbounds firstView parent firstParent subtract add convert write view value index = do
    checkbounds view index
    let vo ← firstView view
    let delta ← subtract index vo
    let p := parent view
    let po ← firstParent p
    let pi ← add delta po
    let converted ← convert value
    let _ ← write p converted pi
    .ok value
theorem p319 : P319 := by unfold P319; intros; rfl

def m325 (checkbounds : V → I → JResult Unit) (unsafeSet : V → X → I → JResult X)
    (view : V) (value : X) (indices : I) : JResult X := do
  checkbounds view indices
  unsafeSet view value indices
def P325 : Prop := ∀ {V I X : Type} (checkbounds : V → I → JResult Unit)
    (unsafeSet : V → X → I → JResult X) view value indices,
  m325 checkbounds unsafeSet view value indices = do checkbounds view indices; unsafeSet view value indices
theorem p325 : P325 := by unfold P325; intros; rfl

def m329 (parent : V → P) (parentIndex : RI → I) (checkbounds : P → I → JResult Unit)
    (convert : X → JResult T) (write : P → T → I → JResult P)
    (view : V) (value : X) (index : RI) : JResult X := do
  let p := parent view
  let i := parentIndex index
  checkbounds p i
  let converted ← convert value
  let _ ← write p converted i
  .ok value
def P329 : Prop := ∀ {V P RI I X T : Type} (parent : V → P) (parentIndex : RI → I)
    (checkbounds : P → I → JResult Unit) (convert : X → JResult T)
    (write : P → T → I → JResult P) view value index,
  m329 parent parentIndex checkbounds convert write view value index = do
    let p := parent view
    let i := parentIndex index
    checkbounds p i
    let converted ← convert value
    let _ ← write p converted i
    .ok value
theorem p329 : P329 := by unfold P329; intros; rfl

def m335 (parent : V → P) (axes : P → JResult AX) (size : V → JResult S)
    (sub2ind : S → I → JResult L) (offset : L → AX → JResult L)
    (mi : V → MI) (ind2sub : AX → MI → L → JResult PI) (convert : X → JResult T)
    (write : P → T → PI → JResult P) (view : V) (value : X) (indices : I) : JResult X := do
  let p := parent view
  let firstAxes ← axes p
  let shape ← size view
  let linear ← sub2ind shape indices
  let adjusted ← offset linear firstAxes
  let secondAxes ← axes p
  let parentIndices ← ind2sub secondAxes (mi view) adjusted
  let converted ← convert value
  let _ ← write p converted parentIndices
  .ok value
def P335 : Prop := ∀ {V P AX S I L MI PI X T : Type} (parent : V → P)
    (axes : P → JResult AX) (size : V → JResult S) (sub2ind : S → I → JResult L)
    (offset : L → AX → JResult L) (mi : V → MI) (ind2sub : AX → MI → L → JResult PI)
    (convert : X → JResult T) (write : P → T → PI → JResult P) view value indices,
  m335 parent axes size sub2ind offset mi ind2sub convert write view value indices = do
    let p := parent view
    let firstAxes ← axes p
    let shape ← size view
    let linear ← sub2ind shape indices
    let adjusted ← offset linear firstAxes
    let secondAxes ← axes p
    let parentIndices ← ind2sub secondAxes (mi view) adjusted
    let converted ← convert value
    let _ ← write p converted parentIndices
    .ok value
theorem p335 : P335 := by unfold P335; intros; rfl

def m348 : JResult α := .error (.callback 348)
def P348 : Prop := ∀ {α : Type}, m348 (α := α) = .error (.callback 348)
theorem p348 : P348 := by unfold P348; intros; rfl

def pointerDelegate (convert : PT → P → JResult R) (pointerType : PT) (parent : V → P)
    (view : V) : JResult R := convert pointerType (parent view)
def P350 : Prop := ∀ {PT P R V : Type} (convert : PT → P → JResult R)
    pointerType (parent : V → P) view,
  pointerDelegate convert pointerType parent view = convert pointerType (parent view)
theorem p350 : P350 := by unfold P350 pointerDelegate; intros; rfl
def P351 : Prop := P350
theorem p351 : P351 := p350

def m357 (firstIndex : I → JResult R) (parent : R → P) (step : P → JResult X)
    (toInt : X → JResult Int) (multiply : S → Int → JResult S)
    (stride : S) (indices : I) : JResult S := do
  let range ← firstIndex indices
  let rawStep ← step (parent range)
  let integerStep ← toInt rawStep
  multiply stride integerStep
def P357 : Prop := ∀ {I R P X S : Type} (firstIndex : I → JResult R)
    (parent : R → P) (step : P → JResult X) (toInt : X → JResult Int)
    (multiply : S → Int → JResult S) stride indices,
  m357 firstIndex parent step toInt multiply stride indices = do
    let range ← firstIndex indices
    let rawStep ← step (parent range)
    let integerStep ← toInt rawStep
    multiply stride integerStep
theorem p357 : P357 := by unfold P357; intros; rfl

def m360 (firstStride : Str → JResult Int) (firstIndex : I → JResult R)
    (parent : R → P) (step : P → JResult X) (toInt : X → JResult Int)
    (multiply : Int → Int → JResult Int) (size : R → JResult SZ)
    (sizeToStrides : Int → SZ → JResult (List Int)) (tailStrides : Str → JResult Str)
    (tailIndices : I → JResult I) (recurse : Str → I → JResult (List Int))
    (strides : Str) (indices : I) : JResult (List Int) := do
  let base ← firstStride strides
  let range ← firstIndex indices
  let rawStep ← step (parent range)
  let integerStep ← toInt rawStep
  let initial ← multiply base integerStep
  let shape ← size range
  let own ← sizeToStrides initial shape
  let remainingStrides ← tailStrides strides
  let remainingIndices ← tailIndices indices
  let rest ← recurse remainingStrides remainingIndices
  .ok (own ++ rest)
def P360 : Prop := ∀ {Str I R P X SZ : Type} (firstStride : Str → JResult Int)
    (firstIndex : I → JResult R) (parent : R → P) (step : P → JResult X)
    (toInt : X → JResult Int) (multiply : Int → Int → JResult Int)
    (size : R → JResult SZ) (sizeToStrides : Int → SZ → JResult (List Int))
    (tailStrides : Str → JResult Str) (tailIndices : I → JResult I)
    (recurse : Str → I → JResult (List Int)) strides indices,
  m360 firstStride firstIndex parent step toInt multiply size sizeToStrides tailStrides tailIndices recurse strides indices = do
    let base ← firstStride strides
    let range ← firstIndex indices
    let rawStep ← step (parent range)
    let integerStep ← toInt rawStep
    let initial ← multiply base integerStep
    let shape ← size range
    let own ← sizeToStrides initial shape
    let remainingStrides ← tailStrides strides
    let remainingIndices ← tailIndices indices
    let rest ← recurse remainingStrides remainingIndices
    .ok (own ++ rest)
theorem p360 : P360 := by unfold P360; intros; rfl

def m368 (parent : V → P) (contiguous : P → JResult Bool) (firstIndex : V → JResult Int)
    (firstParent : P → JResult Int) (elsize : P → JResult Int)
    (offsetArithmetic : Int → Int → Int → JResult Int) (indices : V → I)
    (firsts : I → JResult FI) (memoryOffset : P → FI → JResult M) (toInt : M → JResult Int)
    (unsafeConvert : PT → P → JResult Ptr) (addPointer : Ptr → Int → JResult Ptr)
    (castPointer : OutPT → Ptr → JResult Out) (inputType : PT) (outputType : OutPT)
    (view : V) : JResult Out := do
  let p := parent view
  let linear ← contiguous p
  let delta ← if linear then do
    let first ← firstIndex view
    let origin ← firstParent p
    let bytes ← elsize p
    offsetArithmetic first origin bytes
  else do let fs ← firsts (indices view); let raw ← memoryOffset p fs; toInt raw
  let pointer ← unsafeConvert inputType p
  let shifted ← addPointer pointer delta
  castPointer outputType shifted
def P368 : Prop := ∀ {V P I FI M PT Ptr OutPT Out : Type} (parent : V → P)
    (contiguous : P → JResult Bool) (firstIndex : V → JResult Int)
    (firstParent : P → JResult Int) (elsize : P → JResult Int)
    (offsetArithmetic : Int → Int → Int → JResult Int) (indices : V → I)
    (firsts : I → JResult FI) (memoryOffset : P → FI → JResult M) (toInt : M → JResult Int)
    (unsafeConvert : PT → P → JResult Ptr) (addPointer : Ptr → Int → JResult Ptr)
    (castPointer : OutPT → Ptr → JResult Out) inputType outputType view,
  m368 parent contiguous firstIndex firstParent elsize offsetArithmetic indices firsts memoryOffset
    toInt unsafeConvert addPointer castPointer inputType outputType view = do
      let p := parent view
      let linear ← contiguous p
      let delta ← if linear then do
        let first ← firstIndex view
        let origin ← firstParent p
        let bytes ← elsize p
        offsetArithmetic first origin bytes
      else do let fs ← firsts (indices view); let raw ← memoryOffset p fs; toInt raw
      let pointer ← unsafeConvert inputType p
      let shifted ← addPointer pointer delta
      castPointer outputType shifted
theorem p368 : P368 := by unfold P368; intros; rfl

def m398 (unsafeConvert : PT → C → JResult Ptr) (addPointer : Ptr → Int → JResult Ptr)
    (castPointer : OutPT → Ptr → JResult Out) (parentType : PT) (outputType : OutPT)
    (parent : C → C) (offset : C → Int) (conversion : C) : JResult Out := do
  let pointer ← unsafeConvert parentType (parent conversion)
  let shifted ← addPointer pointer (offset conversion)
  castPointer outputType shifted
def P398 : Prop := ∀ {PT C Ptr OutPT Out : Type} (unsafeConvert : PT → C → JResult Ptr)
    (addPointer : Ptr → Int → JResult Ptr) (castPointer : OutPT → Ptr → JResult Out)
    parentType outputType (parent : C → C) offset conversion,
  m398 unsafeConvert addPointer castPointer parentType outputType parent offset conversion = do
    let pointer ← unsafeConvert parentType (parent conversion)
    let shifted ← addPointer pointer (offset conversion)
    castPointer outputType shifted
theorem p398 : P398 := by unfold P398; intros; rfl

def m402 (parent : V → P) (cconvert : PT → P → JResult C) (contiguous : P → JResult Bool)
    (fastOffset : V → P → JResult M) (indices : V → I) (firsts : I → JResult FI)
    (memoryOffset : P → FI → JResult M) (toInt : M → JResult Int)
    (offsetConvert : PT → Int → C → JResult R) (pointerType : PT) (view : V) : JResult R := do
  let p := parent view
  let converted ← cconvert pointerType p
  let linear ← contiguous p
  let rawOffset ← if linear then fastOffset view p
    else do let fs ← firsts (indices view); memoryOffset p fs
  let byteOffset ← toInt rawOffset
  offsetConvert pointerType byteOffset converted
def P402 : Prop := ∀ {V P PT C M I FI R : Type} (parent : V → P)
    (cconvert : PT → P → JResult C) (contiguous : P → JResult Bool)
    (fastOffset : V → P → JResult M) (indices : V → I) (firsts : I → JResult FI)
    (memoryOffset : P → FI → JResult M) (toInt : M → JResult Int)
    (offsetConvert : PT → Int → C → JResult R) pointerType view,
  m402 parent cconvert contiguous fastOffset indices firsts memoryOffset toInt offsetConvert pointerType view = do
    let p := parent view
    let converted ← cconvert pointerType p
    let linear ← contiguous p
    let rawOffset ← if linear then fastOffset view p
      else do let fs ← firsts (indices view); memoryOffset p fs
    let byteOffset ← toInt rawOffset
    offsetConvert pointerType byteOffset converted
theorem p402 : P402 := by unfold P402; intros; rfl

def m424 (contiguous : V → JResult Bool) (sizeView : V → JResult D)
    (sizeToStrides : Int → D → JResult R) (parent : V → P) (sizeParent stridesParent : P → JResult D)
    (merge : D → D → JResult (Int × Int × Nat)) (ndims : P → JResult Nat)
    (reshaped : D → Int → Int → Int → Nat → D → D → JResult R) (view : V) : JResult R := do
  let simple ← contiguous view
  if simple then do let shape ← sizeView view; sizeToStrides 1 shape
  else do
    let p := parent view
    let psize ← sizeParent p
    let pstride ← stridesParent p
    let (mergedSize, mergedStride, n) ← merge psize pstride
    let rank ← ndims p
    let shape ← sizeView view
    if n = rank then sizeToStrides mergedStride shape
    else reshaped shape 1 mergedSize mergedStride n psize pstride
def P424 : Prop := ∀ {V D R P : Type} (contiguous : V → JResult Bool)
    (sizeView : V → JResult D) (sizeToStrides : Int → D → JResult R) (parent : V → P)
    (sizeParent stridesParent : P → JResult D) (merge : D → D → JResult (Int × Int × Nat))
    (ndims : P → JResult Nat) (reshaped : D → Int → Int → Int → Nat → D → D → JResult R) view,
  m424 contiguous sizeView sizeToStrides parent sizeParent stridesParent merge ndims reshaped view = do
    let simple ← contiguous view
    if simple then do let shape ← sizeView view; sizeToStrides 1 shape
    else do
      let p := parent view
      let psize ← sizeParent p
      let pstride ← stridesParent p
      let (mergedSize, mergedStride, n) ← merge psize pstride
      let rank ← ndims p
      let shape ← sizeView view
      if n = rank then sizeToStrides mergedStride shape
      else reshaped shape 1 mergedSize mergedStride n psize pstride
theorem p424 : P424 := by unfold P424; intros; rfl

def mergeLoop (sizeAt strideAt : Nat → JResult Int) (multiply : Int → Int → JResult Int) :
    Nat → Nat → Int → Int → JResult (Int × Int × Nat)
  | index, 0, size, stride => .ok (size, stride, index)
  | index, remaining + 1, size, stride => do
      let nextSize ← sizeAt (index + 1)
      let nextStride ← strideAt (index + 1)
      if size = 1 then mergeLoop sizeAt strideAt multiply (index + 1) remaining nextSize nextStride
      else do
        let packed ← multiply stride size
        if nextStride = packed || nextSize = 1 then do
          let merged ← multiply size nextSize
          mergeLoop sizeAt strideAt multiply (index + 1) remaining merged stride
        else .ok (size, stride, index)

def m450 (sizeAt strideAt : Nat → JResult Int) (multiply : Int → Int → JResult Int)
    (rank start : Nat) : JResult (Int × Int × Nat) := do
  let size ← sizeAt start
  let stride ← strideAt start
  if start < rank then mergeLoop sizeAt strideAt multiply start (rank - start) size stride
  else .ok (size, stride, start)
def P450 : Prop := ∀ (sizeAt strideAt : Nat → JResult Int)
    (multiply : Int → Int → JResult Int) rank start,
  m450 sizeAt strideAt multiply rank start = do
    let size ← sizeAt start
    let stride ← strideAt start
    if start < rank then mergeLoop sizeAt strideAt multiply start (rank - start) size stride
    else .ok (size, stride, start)
theorem p450 : P450 := by unfold P450; intros; rfl

def m466 (parent : V → P) (map : F → P → JResult M) (size : V → JResult D)
    (reshape : M → D → JResult R) (function : F) (view : V) : JResult R := do
  let mapped ← map function (parent view)
  let shape ← size view
  reshape mapped shape
def P466 : Prop := ∀ {V P F M D R : Type} (parent : V → P) (map : F → P → JResult M)
    (size : V → JResult D) (reshape : M → D → JResult R) function view,
  m466 parent map size reshape function view = do
    let mapped ← map function (parent view)
    let shape ← size view
    reshape mapped shape
theorem p466 : P466 := by unfold P466; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-reshapedarray-faithful-{line}", juliaFile := "base/reshapedarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.ReshapedFaithfulB
