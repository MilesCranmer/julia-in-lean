import JuliaLean.MultidimCov.SubarrayV2Core

/-!
Line-by-line models of the `base/subarray.jl` methods (master `bbfa0ce4150`)
that construct a `SubArray`, compute its linear layout and access it.
Every definition cites the lines it mirrors. Multiple methods of one Julia
function are one Lean function whose branches follow Julia's dispatch
(most specific method first).
-/

namespace JuliaLean.MultidimCov.SubarrayV2

/-! ## Index classification -/

/-- `index_ndims(I...)` (`base/multidimensional.jl:793-799`): one `true` per
parent dimension an index consumes (`N` for a `CartesianIndex{N}` array). -/
def indexNdims (I : List Idx) : List Bool := I.flatMap (fun i => List.replicate (idxConsumes i) true)

/-- `index_dimsum(I...)` (`base/multidimensional.jl:803-809`): one `true` per
output dimension (none for a scalar, `ndims(i)` for an array). -/
def indexDimsum (I : List Idx) : List Bool := I.flatMap (fun i => List.replicate (idxRank i) true)

/-- `viewindexing(I)`, `base/subarray.jl:52-67`. -/
def viewindexing : List Idx → Style
  | [] => .linear                                                     -- 52
  | .int _ :: rest => viewindexing rest                               -- 54
  | .slice _ :: rest =>
      match rest with
      | .slice _ :: rest' =>
          if allScalar rest' then .linear                             -- 59
          else viewindexing rest                                      -- 56
      | u :: rest' =>
          if u.isUnitRange && allScalar rest' then .linear            -- 58
          else if allScalar rest then .linear                         -- 63
          else .cartesian                                             -- 67
      | [] => .linear                                                 -- 63
  | i :: rest =>
      if i.isRange && allScalar rest then .linear                     -- 63
      else .cartesian                                                 -- 65, 67

/-! ## Rank check, `base/subarray.jl:46-49` -/

/-- A value used as a `SubArray` parent: an `AbstractArray` of some rank, a
number (`ndims(::Number) == 0`), or another object (`ndims` has no method). -/
inductive PObj where
  | arr (nd : Nat)
  | num
  | other
  deriving Repr, DecidableEq

/-- `ndims(parent)`. -/
def ndimsObj : PObj → SR Nat
  | .arr n => .ok n
  | .num => .ok 0
  | .other => .error .method

/-- `check_parent_index_match(parent::AbstractArray{T,N}, ::NTuple{N,Bool}) = nothing`, line 47. -/
def checkMatch47 : SR Unit := .ok ()

/-- `check_parent_index_match(parent, ::NTuple{N,Bool})`, lines 48-49. -/
def checkMatch48 (parent : PObj) (n : Nat) : SR Unit := do
  let nd ← ndimsObj parent
  .error (.argument s!"number of indices ({n}) must match the parent dimensionality ({nd})")

/-- Dispatch between lines 47 and 48 on `(parent, shape::NTuple{N,Bool})`. -/
def checkMatchShape (parent : PObj) (shape : List Bool) : SR Unit :=
  match parent with
  | .arr nd => if nd = shape.length then checkMatch47 else checkMatch48 parent shape.length
  | _ => checkMatch48 parent shape.length

/-- `check_parent_index_match(parent, indices)`, line 46. -/
def checkParentIndexMatch (parent : PObj) (I : List Idx) : SR Unit :=
  checkMatchShape parent (indexNdims I)

/-! ## Construction, `base/subarray.jl:19-44` -/

/-- A `SubArray{T,N,P,I,L}` value: type parameters and the four fields. -/
structure Sub (α : Type) where
  T : String
  N : Nat
  P : PType
  L : Bool
  parent : Par α
  indices : List Idx
  offset1 : Int
  stride1 : Int

/-- `typeof(parent)`. -/
def typeOf (p : Par α) : PType := p.ty

/-- Inner constructor `SubArray{T,N,P,I,L}(parent, indices, offset1, stride1)`, lines 19-23. -/
def subInner (T : String) (N : Nat) (P : PType) (L : Bool) (parent : Par α) (indices : List Idx)
    (offset1 stride1 : Int) : SR (Sub α) := do
  checkParentIndexMatch (.arr parent.axes.length) indices
  pure ⟨T, N, P, L, parent, indices, offset1, stride1⟩

/-- `fill_to_length(t, val, Val(N))`, `base/ntuple.jl:74-85` (and `base/tuple.jl:442-445`). -/
def fillToLength (t : List Ax) (val : Ax) (n : Nat) : SR (List Ax) :=
  if t.length > n then .error (.argument s!"input tuple of length {t.length}, requested {n}")
  else .ok (t ++ List.replicate (n - t.length) val)

/-- `compute_stride1(s, inds, I)`, lines 450-456. -/
def computeStride1Rec (s : Int) : List Ax → List Idx → SR Int
  | _, [] => .ok s                                                    -- 450
  | inds, i :: rest =>
      if allScalar (i :: rest) then .ok s                             -- 451
      else match i with
        | .int _ =>                                                   -- 452-453
            match inds with
            | a :: inds' => computeStride1Rec (imul s a.len) inds' rest
            | [] => .error .bounds
        | .slice _ => .ok s                                           -- 455
        | _ =>
            if i.isRange then .ok (imul s (idxStep i))                -- 454
            else .error (.argument s!"invalid strided index type {idxTypeName i}")  -- 456

/-- `compute_stride1(parent, I)`, lines 448-449. -/
def computeStride1 (p : Par α) (I : List Idx) : SR Int := do
  let inds ← fillToLength p.axes (oneAx 1) I.length
  computeStride1Rec 1 inds I

/-- `Int(first(LinearIndices(parent)))`. -/
def firstLinear (axs : List Ax) : Int :=
  match axs with
  | [a] => a.lo
  | _ => 1

/-- `IP[1]` of a tuple of axes. -/
def axHead : List Ax → SR Ax
  | a :: _ => .ok a
  | [] => .error .bounds

/-- `compute_linindex(f, s, IP, I)`, lines 491-501: both the two-or-more-index
method (491-495) and the one-index method (496-500) start with
`Δi = Int(first(I[1])) - Int(first(IP[1]))`. -/
def computeLinindexRec (f s : Int) : List Ax → List Idx → SR Int
  | _, [] => .ok f                                                    -- 501
  | ip, i :: tl => do
      let fi ← idxFirst i
      let a ← axHead ip
      let di := isub fi a.lo
      match tl with
      | [] => .ok (iadd f (imul di s))                                -- 496-500
      | _ :: _ => computeLinindexRec (iadd f (imul di s)) (imul s a.len) ip.tail tl  -- 491-495

/-- `compute_linindex(parent, I)`, lines 486-490. -/
def computeLinindex (p : Par α) (I : List Idx) : SR Int := do
  let IP ← fillToLength p.axes (oneAx 1) I.length
  computeLinindexRec (firstLinear p.axes) 1 IP I

/-- `find_extended_dims(dim, I...)`, lines 503-505. -/
def findExtendedDims (dim : Int) : List Idx → List Int
  | [] => []
  | .int _ :: rest => findExtendedDims (dim + 1) rest
  | _ :: rest => dim :: findExtendedDims (dim + 1) rest

/-- `find_extended_inds(I...)`, lines 506-508. -/
def findExtendedInds : List Idx → List Idx
  | [] => []
  | .int _ :: rest => findExtendedInds rest
  | i :: rest => i :: findExtendedInds rest

/-- `axes1(i)` of an index object (its first axis). -/
def axes1Idx (i : Idx) : Ax := (idxAxes i).headD (oneAx 1)

/-- `axes(parent, d)`: `OneTo(1)` beyond the last dimension. -/
def axisAt (axs : List Ax) (d : Int) : Ax := axs.getD (d - 1).toNat (oneAx 1)

/-- `compute_offset1(parent, stride1, dims, inds, I)`, lines 480-485. -/
def computeOffset1Dims (p : Par α) (stride1 : Int) (dims : List Int) (inds : List Idx)
    (I : List Idx) : SR Int :=
  match dims, inds with
  | [d], [.slice _] => do                                             -- 480-481
      let li ← computeLinindex p I
      .ok (isub li (imul stride1 (axisAt p.axes d).lo))
  | _, [r] =>
      if r.isRange then do                                            -- 482-483
        let li ← computeLinindex p I
        .ok (isub li (imul stride1 (axes1Idx r).lo))
      else do                                                         -- 484-485
        let li ← computeLinindex p I
        .ok (isub li stride1)
  | _, _ => do                                                        -- 484-485
      let li ← computeLinindex p I
      .ok (isub li stride1)

/-- `compute_offset1(parent, stride1, I)`, lines 471-479. -/
def computeOffset1 (p : Par α) (stride1 : Int) (I : List Idx) : SR Int :=
  match p.axes, I with
  | [_], [r] =>
      if r.isRange then do                                            -- 471-472
        let f ← idxFirst r
        .ok (isub f (imul stride1 (axes1Idx r).lo))
      else computeOffset1Dims p stride1 (findExtendedDims 1 I) (findExtendedInds I) I
  | _, _ => computeOffset1Dims p stride1 (findExtendedDims 1 I) (findExtendedInds I) I  -- 478-479

/-- `_compute_linear_layout(parent, indices)`, lines 40-44 (`Int(x)` of an `Int` is `x`). -/
def computeLinearLayout (p : Par α) (I : List Idx) : SR (Int × Int) := do
  let stride1 ← computeStride1 p I
  let offset1 ← computeOffset1 p stride1 I
  pure (offset1, stride1)

/-- `SubArray(::IndexCartesian, parent::P, indices::I, ::NTuple{N,Any})`, lines 30-33. -/
def subCartesian (p : Par α) (I : List Idx) (dims : List Bool) : SR (Sub α) :=
  let P := typeOf p
  subInner (eltypeOf P) dims.length P false p I 0 0

/-- `SubArray(::IndexLinear, parent::P, indices::I, ::NTuple{N,Any})`, lines 34-38. -/
def subLinear (p : Par α) (I : List Idx) (dims : List Bool) : SR (Sub α) := do
  let (offset1, stride1) ← computeLinearLayout p I
  let P := typeOf p
  subInner (eltypeOf P) dims.length P true p I offset1 stride1

/-- `ensure_indexable(I)` (`base/multidimensional.jl:922-925`): the identity on these index objects. -/
def ensureIndexable (I : List Idx) : List Idx := I

/-- `SubArray(parent::AbstractArray, indices::Tuple)`, lines 26-29. -/
def subArray (p : Par α) (I : List Idx) : SR (Sub α) :=
  match Style.combine (viewindexing I) p.style with
  | .cartesian => subCartesian p (ensureIndexable I) (indexDimsum I)
  | .linear => subLinear p (ensureIndexable I) (indexDimsum I)

/-! ## Axes, `base/subarray.jl:525-541` -/

/-- `axes(i)` of an index object, from each type's `axes` method: `Slice` and
`IdentityUnitRange` (`base/indices.jl:343,370`), `OneTo` and the other
ranges (`axes(r::AbstractRange) = (oneto(length(r)),)`), `LogicalIndex`
(`(OneTo(L.sum),)`), and arrays (`map(oneto, size(A))`). -/
def axesOf : Idx → List Ax
  | .int _ => []
  | .slice a => [a]
  | .ident a => [a]
  | .oneto n => [oneAx n]
  | .unit a => [oneAx a.len]
  | .step _ _ n => [oneAx n]
  | .arr dims _ => dims.map (fun (d : Nat) => oneAx (d : Int))
  | .mask bs => [oneAx (countTrue bs)]
  | .carr _ dims _ => dims.map (fun (d : Nat) => oneAx (d : Int))

/-- `_indices_sub(I...)`, lines 526-531. -/
def indicesSub : List Idx → List Ax
  | [] => []                                                          -- 527
  | .int _ :: rest => indicesSub rest                                 -- 526
  | i :: rest => axesOf i ++ indicesSub rest                          -- 528-531

/-- `axes(S::SubArray)`, line 525. -/
def subAxes (V : Sub α) : List Ax := indicesSub V.indices

/-- `_axes1_sub(I...)`, lines 535-541 (`none` is the empty tuple of line 535). -/
def axes1SubRec : List Idx → Option Ax
  | [] => none                                                        -- 535
  | .int _ :: rest => axes1SubRec rest                                -- 536
  | i :: rest =>
      if idxRank i = 0 then axes1SubRec rest                          -- 537
      else some ((axesOf i).headD (oneAx 1))                          -- 538-541

/-- `axes1(::SubArray{<:Any,0}) = OneTo(1)` (line 533) and `axes1(S::SubArray)` (line 534). -/
def axes1Sub (V : Sub α) : Option Ax :=
  if V.N = 0 then some (oneAx 1) else axes1SubRec V.indices

/-! ## Scalar access -/

/-- `idxs[1][subidxs...]` for `Int` subscripts under `@inbounds`, as parent
coordinates (a `CartesianIndex` value is splatted by the parent's `to_indices`):
`getindex(::Slice, ::Int)` and `getindex(::IdentityUnitRange, ::Integer)` return
the subscript (`base/indices.jl:350,378`), `OneTo` converts it, `UnitRange`
and `StepRange` compute `first + (i-1)*step` with `Int` wrapping
(`base/range.jl:950-980`), arrays read their element. -/
def idxGetInt (i : Idx) (js : List Int) : SR (List Int) :=
  match i, js with
  | .slice _, [j] => .ok [j]
  | .ident _, [j] => .ok [j]
  | .oneto _, [j] => .ok [j]
  | .unit a, [j] => .ok [iadd a.lo (isub j 1)]
  | .step s st _, [j] => .ok [iadd s (imul (isub j 1) st)]
  | .arr dims xs, js =>
      match (cmOff dims js).bind (fun k => xs[k]?) with
      | some v => .ok [v]
      | none => .error .bounds
  | .mask bs, [j] =>
      match (truePos bs)[(j - 1).toNat]? with
      | some v => if 1 ≤ j then .ok [v] else .error .bounds
      | none => .error .bounds
  | .carr _ dims xs, js =>
      match (cmOff dims js).bind (fun k => xs[k]?) with
      | some v => .ok v
      | none => .error .bounds
  | _, _ => .error .bounds

/-- `reindex(idxs, subidxs)` with `Int` subindices, lines 292-312. -/
def reindexS : List Idx → List Int → SR (List Int)
  | [], [] => .ok []                                                  -- 292
  | [], _ :: _ => .error .method
  | .int n :: ps, js => do                                            -- 295-296
      let r ← reindexS ps js
      pure (n :: r)
  | .slice _ :: ps, j :: js => do                                     -- 299-300
      let r ← reindexS ps js
      pure (j :: r)
  | p :: ps, js =>
      let d := idxRank p
      if d = 1 then
        match js with
        | j :: js' => do                                              -- 303-304
            let v ← idxGetInt p [j]
            let r ← reindexS ps js'
            pure (v ++ r)
        | [] => .error .bounds                                        -- 311 with subidxs[1:1] of ()
      else if d = 2 then
        match js with
        | j1 :: j2 :: js' => do                                       -- 307-308
            let v ← idxGetInt p [j1, j2]
            let r ← reindexS ps js'
            pure (v ++ r)
        | _ => .error .bounds                                         -- 311 with too few subindices
      else if js.length < d then .error .bounds                       -- 311, subidxs[1:N]
      else do                                                         -- 311-312
        let v ← idxGetInt p (js.take d)
        let r ← reindexS ps (js.drop d)
        pure (v ++ r)

/-- `checkbounds(V, I...)` with one subscript per dimension. -/
def checkboundsCart (V : Sub α) (J : List Int) : SR Unit :=
  if inAxesB (subAxes V) J then .ok () else .error .bounds

/-- `getindex(V::SubArray{T,N}, I::Vararg{Int,N})`, lines 316-321. -/
def getindexSlow (V : Sub α) (J : List Int) : SR α := do
  checkboundsCart V J
  let pos ← reindexS V.indices J
  readElt (V.parent.atPos pos)

/-- `FastContiguousSubArray` (lines 348-349): the first index is an
`AbstractUnitRange`, or every index is a scalar. -/
def contiguous (I : List Idx) : Bool :=
  match I with
  | i :: _ => i.isUnitRange || allScalar I
  | [] => true

/-- `_reindexlinear(V, i::Int)`: `V.offset1 + V.stride1*i` (line 327) or
`V.offset1 + i` for a `FastContiguousSubArray` (line 351). -/
def reindexLinear (V : Sub α) (i : Int) : Int :=
  if contiguous V.indices then iadd V.offset1 i else iadd V.offset1 (imul V.stride1 i)

/-- `checkbounds(V, i)` for one linear subscript. -/
def checkboundsLin (V : Sub α) (i : Int) : SR Unit :=
  if (linearAxis (subAxes V)).mem i then .ok () else .error .bounds

/-- Linear read of a parent under `@inbounds` (`IndexLinear` storage). -/
def Par.atLin (p : Par α) (k : Int) : Option α := p.lin k

/-- `getindex(V::FastSubArray, i::Int)`, lines 330-335. -/
def getindexFast (V : Sub α) (i : Int) : SR α := do
  checkboundsLin V i
  readElt (V.parent.atLin (reindexLinear V i))

/-- `getindex(V::FastSubArray{<:Any,1}, i::Int)`, lines 339-344. -/
def getindexFastVec (V : Sub α) (i : Int) : SR α := do
  checkboundsLin V i
  readElt (V.parent.atLin (reindexLinear V i))

/-- `getindex(V, i::Int)` on a fast view: lines 339-344 for a vector, else 330-335. -/
def getindexFastDispatch (V : Sub α) (i : Int) : SR α :=
  if V.N = 1 then getindexFastVec V i else getindexFast V i

/-- Parent linear write `A[k] = x` under `@inbounds`: the element whose linear
index is `k` changes, seen through both accesses. -/
def Par.setLin (p : Par α) (k : Int) (x : α) : Par α :=
  { p with lin := fun k' => if k' = k then some x else p.lin k',
           cart := fun pos => if linearIndex p.axes pos = k then some x else p.cart pos }

/-- `setindex!(V::FastSubArray, x, i::Int)`, lines 392-397. -/
def setindexFast (V : Sub α) (x : α) (i : Int) : SR (Sub α) := do
  checkboundsLin V i
  pure { V with parent := V.parent.setLin (reindexLinear V i) x }

/-- `setindex!(V::FastSubArray{<:Any,1}, x, i::Int)`, lines 398-403. -/
def setindexFastVec (V : Sub α) (x : α) (i : Int) : SR (Sub α) := do
  checkboundsLin V i
  pure { V with parent := V.parent.setLin (reindexLinear V i) x }

/-- `isassigned(parent, k)` under `@inbounds`. -/
def Par.assignedLin (p : Par α) (k : Int) : Bool := (p.lin k).isSome

/-- `isassigned(V::FastSubArray, i::Int)`, lines 420-425. -/
def isassignedFast (V : Sub α) (i : Int) : Bool :=
  if (linearAxis (subAxes V)).mem i then V.parent.assignedLin (reindexLinear V i) else false

/-- `isassigned(V::FastSubArray{<:Any,1}, i::Int)`, lines 426-431. -/
def isassignedFastVec (V : Sub α) (i : Int) : Bool :=
  if (linearAxis (subAxes V)).mem i then V.parent.assignedLin (reindexLinear V i) else false

/-- `pointer(V::FastSubArray, i::Int)`, line 510; `pptr k` is `pointer(V.parent, k)`. -/
def pointerFast (pptr : Int → Int) (V : Sub α) (i : Int) : Int :=
  pptr (iadd V.offset1 (imul V.stride1 i))

/-- `pointer(V::FastContiguousSubArray, i::Int)`, line 511. -/
def pointerFastContig (pptr : Int → Int) (V : Sub α) (i : Int) : Int :=
  pptr (iadd V.offset1 i)

/-- Dispatch of `pointer(V, i::Int)` between lines 510 and 511. -/
def pointerDispatch (pptr : Int → Int) (V : Sub α) (i : Int) : Int :=
  if contiguous V.indices then pointerFastContig pptr V i else pointerFast pptr V i

/-! ## Strides, `base/subarray.jl:437-444` -/

/-- `substrides(strds, I)`, lines 439-444. -/
def substrides : List Int → List Idx → SR (List Int)
  | [], [] => .ok []                                                  -- 439
  | strds, i :: rest =>
      match i with
      | .int _ =>                                                     -- 440
          match strds with
          | _ :: st => substrides st rest
          | [] => .error (.argument "Cannot call tail on an empty tuple.")
      | .slice _ =>                                                   -- 441
          match strds with
          | s :: st => do
              let r ← substrides st rest
              pure (s :: r)
          | [] => .error .bounds
      | _ =>
          if i.isRange then                                           -- 442
            match strds with
            | s :: st => do
                let r ← substrides st rest
                pure (imul s (idxStep i) :: r)
            | [] => .error .bounds
          else .error (.argument                                      -- 443-444
            s!"strides is invalid for SubArrays with indices of type {idxTypeName i}")
  | _ :: _, [] => .error .method

/-- `strides(::Array)`: `(1, size(A,1), size(A,1)*size(A,2), ...)`. -/
def arrayStrides : List Ax → List Int
  | [] => []
  | a :: as => 1 :: (arrayStrides as).map (fun s => a.len * s)

/-- `strides(V::SubArray)` for an `Array` parent, line 437. -/
def subStrides (V : Sub α) : SR (List Int) := substrides (arrayStrides V.parent.axes) V.indices

end JuliaLean.MultidimCov.SubarrayV2
