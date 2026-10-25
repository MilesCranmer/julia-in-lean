import JuliaLean.BroadcastViews.Shape

/-!
Fast linear indexing of `SubArray`s, `base/subarray.jl` at master `bbfa0ce4150`: `viewindexing`
(lines 51-67), `compute_stride1` (448-456), `compute_offset1`/`compute_linindex` (478-508) and
`getindex(V::FastSubArray, i::Int) = V.parent[V.offset1 + V.stride1*i]` (327, 330-344).

The parent is an `Array` (`IndexLinear`, one-based axes `OneTo(n)`) with one index per dimension
(`view` reshapes the parent otherwise, line 226). An index is an `Int`, a `Slice(OneTo(n))`
(from `:`), an `AbstractUnitRange{Int}` `lo:lo+len-1`, or a `StepRange{Int,Int}`.
-/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- A parent index of a view, after `to_indices`. -/
inductive LIdx where
  | scalar (c : I64)
  | slice
  | urange (lo len : I64)
  | srange (start step len : I64)
  deriving DecidableEq, Repr

def LIdx.isScalar : LIdx → Bool
  | .scalar _ => true
  | _ => false

/-- `viewindexing(I)` is `IndexLinear()`, `base/subarray.jl:52-67`: leading scalars are skipped
(54), `Slice`s may be followed by more `Slice`s (56) and then by one `AbstractUnitRange` and
scalars (58) or only scalars (59, 63); a single range followed by scalars is linear (63); all other
tuples are `IndexCartesian()` (65, 67). -/
def viewLinear : List LIdx → Bool
  | [] => true
  | .scalar _ :: is => viewLinear is
  | .slice :: .slice :: is => viewLinear (.slice :: is)
  | .slice :: .urange _ _ :: is => is.all LIdx.isScalar
  | .slice :: is => is.all LIdx.isScalar
  | .urange _ _ :: is => is.all LIdx.isScalar
  | .srange _ _ _ :: is => is.all LIdx.isScalar

/-- `compute_stride1(s, inds, I)`, `base/subarray.jl:450-456`: all-scalar tuples return `s`
(451), a leading scalar multiplies `s` by the length of its parent axis (452-453), a `Slice`
returns `s` (455), another range returns `s * Int(step(I[1]))` (454). -/
def computeStride1 (s : I64) : List I64 → List LIdx → I64
  | _, [] => s
  | ns, i :: is =>
    if (i :: is).all LIdx.isScalar then s
    else match i, ns with
      | .scalar _, n :: ns' => computeStride1 (s * n) ns' is
      | .scalar _, [] => computeStride1 (s * i64 1) [] is
      | .slice, _ => s
      | .urange _ _, _ => s * i64 1
      | .srange _ st _, _ => s * st

/-- `first(I[d])` for an index. -/
def LIdx.first : LIdx → I64
  | .scalar c => c
  | .slice => i64 1
  | .urange lo _ => lo
  | .srange st _ _ => st

/-- `compute_linindex(f, s, IP, I)`, `base/subarray.jl:491-501`, with one-based parent axes:
`Δi = first(I[1]) - first(IP[1])`, `f + Δi*s`, next stride `s*length(IP[1])`. -/
def computeLinindex (f s : I64) : List I64 → List LIdx → I64
  | _, [] => f
  | _, [i] => f + (i.first - i64 1) * s
  | ns, i :: is => computeLinindex (f + (i.first - i64 1) * s) (s * ns.headD (i64 1)) ns.tail is

/-- `compute_offset1(parent, stride1, I)`, `base/subarray.jl:478-485`: with exactly one non-scalar
index, `compute_linindex(parent, I) - stride1*first(axes(...))` where that first axis element is 1
(480-483); otherwise `compute_linindex(parent, I) - stride1` (484-485). -/
def computeOffset1 (ns : List I64) (stride1 : I64) (I : List LIdx) : I64 :=
  let L := computeLinindex (i64 1) (i64 1) ns I
  if (I.filter (fun i => !i.isScalar)).length = 1 then L - stride1 * i64 1 else L - stride1

/-- The parent linear index read by `V[i]` for a fast linear view: `V.offset1 + V.stride1*i`
(`_reindexlinear`, line 327; `FastContiguousSubArray` uses `V.offset1 + i`, line 351, with
`stride1 == 1`). -/
def fastParentIndex (ns : List I64) (I : List LIdx) (i : I64) : I64 :=
  let stride1 := computeStride1 (i64 1) ns I
  computeOffset1 ns stride1 I + stride1 * i

/-! ## Reference: Cartesian indexing -/

/-- The length of the view axis of a non-scalar index on a parent axis of length `n`. -/
def LIdx.vlen (n : Int) : LIdx → Int
  | .scalar _ => 1
  | .slice => n
  | .urange _ len => len.val
  | .srange _ _ len => len.val

/-- The parent subscript selected by view subscript `j` (one-based). -/
def LIdx.sub (j : Int) : LIdx → Int
  | .scalar c => c.val
  | .slice => j
  | .urange lo _ => lo.val + (j - 1)
  | .srange st step _ => st.val + (j - 1) * step.val

/-- The parent subscripts `reindex(V.indices, js)` (`base/subarray.jl:316-321`) for view
subscripts `js`, one per non-scalar index. -/
def parentSubs : List LIdx → List Int → List Int
  | [], _ => []
  | .scalar c :: is, js => c.val :: parentSubs is js
  | i :: is, j :: js => i.sub j :: parentSubs is js
  | i :: is, [] => i.sub 1 :: parentSubs is []

/-- The view's dimensions: one per non-scalar index. -/
def viewDims : List Int → List LIdx → List Int
  | _, [] => []
  | ns, .scalar _ :: is => viewDims ns.tail is
  | ns, i :: is => i.vlen (ns.headD 1) :: viewDims ns.tail is

/-- `(s-1)*P` summed column-major: `LinearIndices(dims)[subs...] - 1` when `P = 1`. -/
def colMajor (P : Int) : List Int → List Int → Int
  | n :: ns, s :: ss => (s - 1) * P + colMajor (P * n) ns ss
  | _, _ => 0

end JuliaLean.BroadcastViews
