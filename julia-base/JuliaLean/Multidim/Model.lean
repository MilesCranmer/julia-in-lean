import JuliaLean.Core

/-!
Model of `CartesianIndex`/`CartesianIndices`, `copyto!` on `CartesianIndices`,
`circshift!`, `circcopy!`, `findnext` on arrays, `selectdim`, `cat`/`hvcat`, `repeat`
and `diff` (`base/multidimensional.jl`, `base/abstractarraymath.jl`,
`base/abstractarray.jl`, `base/array.jl`) at master `bbfa0ce4150`.

* A `CartesianIndex{N}` is a `List I64` of length `N`.
* An `OrdinalRange{Int,Int}` component of a `CartesianIndices` is `Rng`: first element,
  step and length. Julia stores the normalised `stop`, which is `Rng.last`.
* An array is described by its axes `List (Int × Int)` (`lo:hi` per dimension; `(1, n)`
  for an `Array`) and its contents, a function from multi-indices to values.
* Exceptions are `Err`; message texts are not modelled.
-/

namespace JuliaLean.Multidim

/-- Julia exception types thrown by the modelled functions. -/
inductive Err where
  | argumentError
  | boundsError
  | dimensionMismatch
  | divideError
  | overflowError
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call that may throw. -/
abbrev R (α : Type) := Except Err α

deriving instance DecidableEq for Except

/-- Exception type of an outcome, or `none` when the call returns. -/
def errKind {α : Type} : R α → Option Err
  | .ok _ => none
  | .error e => some e

/-- Julia `Int`. -/
abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

/-! ## Ranges and `CartesianIndices` -/

/-- An `OrdinalRange{Int,Int}`: `start`, `step` and `length`. -/
structure Rng where
  start : I64
  step : I64
  len : Nat
  deriving DecidableEq, Repr

/-- The exact value of the `j`-th element (0-based). -/
def Rng.elem (r : Rng) (j : Int) : Int := r.start.val + j * r.step.val

/-- `last(r)`: the normalised `stop` field, `start + (len-1)*step` (for an empty range
`start - step`, as `steprange_last_empty` produces), `base/range.jl`. -/
def Rng.last (r : Rng) : I64 := JInt.wrap .i64 (r.elem ((r.len : Int) - 1))

/-- The elements of `r`, in iteration order. -/
def Rng.elems (r : Rng) : List I64 :=
  (List.range r.len).map fun (j : Nat) => JInt.wrap .i64 (r.elem j)

/-- A range that Julia can construct: nonzero step and every element representable. -/
def Rng.WF (r : Rng) : Prop :=
  r.step.val ≠ 0 ∧ ∀ j : Nat, j < r.len → IntTy.min .i64 ≤ r.elem j ∧ r.elem j ≤ IntTy.max .i64

instance (r : Rng) : Decidable r.WF := by
  unfold Rng.WF; exact inferInstance

/-- `in(x, r)` for an integer range: `x` is one of its elements. -/
def Rng.contains (r : Rng) (x : I64) : Bool := r.elems.contains x

/-- 0-based position of the exact integer `x` in `r`, if it is an element. -/
def Rng.pos (r : Rng) (x : Int) : Option Nat :=
  if r.step.val ≠ 0 ∧ (x - r.start.val) % r.step.val = 0 ∧ 0 ≤ (x - r.start.val) / r.step.val ∧
      (x - r.start.val) / r.step.val < r.len
  then some ((x - r.start.val) / r.step.val).toNat else none

/-- The unit range `lo:hi` (`UnitRange{Int}`), converted for a `CartesianIndices`. -/
def unitRng (lo hi : Int) : Rng := ⟨i64 lo, i64 1, (hi - lo + 1).toNat⟩

/-- Column-major product of the component ranges: the elements of a `CartesianIndices`
in the order of the nested loops of its docstring (`base/multidimensional.jl:216-225`). -/
def elems : List Rng → List (List I64)
  | [] => [[]]
  | r :: rs => (elems rs).flatMap fun t => r.elems.map fun x => x :: t

/-- `__inc(state, indices)`, `base/multidimensional.jl:468-483`. The one-dimensional
method adds with `+%`, the multidimensional one with `+`; both wrap. -/
def inc : List I64 → List Rng → Bool × List I64
  | [], [] => (false, [])
  | [s], [r] => (decide (s ≠ r.last), [s + r.step])
  | s :: s' :: ss, r :: r' :: rs =>
    if s ≠ r.last then (true, (s + r.step) :: s' :: ss)
    else
      let p := inc (s' :: ss) (r' :: rs)
      (p.1, r.start :: p.2)
  | _, _ => (false, [])

/-- `iterate(iter::CartesianIndices)`, `base/multidimensional.jl:445-451` (and the
0-dimensional special case, line 486, which this reproduces for `R = []`). -/
def iterFirst (R : List Rng) : Option (List I64) :=
  if R.all (fun r => r.contains r.start) then some (R.map (·.start)) else none

/-- `iterate(iter::CartesianIndices, state)`, `base/multidimensional.jl:452-456`. -/
def iterNext (R : List Rng) (s : List I64) : Option (List I64) :=
  let p := inc s R
  if p.1 then some p.2 else none

/-- `__dec(state, indices)`, `base/multidimensional.jl:592-607`. -/
def dec : List I64 → List Rng → Bool × List I64
  | [], [] => (false, [])
  | [s], [r] => (decide (s ≠ r.start), [s - r.step])
  | s :: s' :: ss, r :: r' :: rs =>
    if s ≠ r.start then (true, (s - r.step) :: s' :: ss)
    else
      let p := dec (s' :: ss) (r' :: rs)
      (p.1, r.last :: p.2)
  | _, _ => (false, [])

/-- `iterate(r::Reverse{<:CartesianIndices})`, `base/multidimensional.jl:572-578`. -/
def revFirst (R : List Rng) : Option (List I64) :=
  if R.all (fun r => r.contains r.last) then some (R.map (·.last)) else none

/-- `iterate(r::Reverse{<:CartesianIndices}, state)`, `base/multidimensional.jl:579-583`. -/
def revNext (R : List Rng) (s : List I64) : Option (List I64) :=
  let p := dec s R
  if p.1 then some p.2 else none

/-- `==(a::CartesianIndices{N}, b::CartesianIndices{N})`,
`base/multidimensional.jl:382-383`: componentwise range equality, where integer
ranges are equal iff they have the same elements. -/
def ciEq (R S : List Rng) : Bool :=
  R.length == S.length && (R.zip S).all fun (r, s) => r.elems == s.elems

/-- `length(t::AbstractArray) = prod(size(t))` (`base/essentials.jl:13`) with
`size(iter::CartesianIndices) = map(length, iter.indices)` (`base/multidimensional.jl:488`):
a product in wrapping `Int` arithmetic. -/
def ciLength (R : List Rng) : I64 := R.foldl (fun p r => p * i64 r.len) (i64 1)

/-- `isempty(a::AbstractArray) = (length(a) == 0)`, `base/abstractarray.jl:1262`. -/
def ciIsEmpty (R : List Rng) : Bool := (ciLength R).val == 0

/-- `isless(t1::Tuple, t2::Tuple)`, `base/tuple.jl`: `isless(a, b) || (isequal(a, b) &&
isless(tail(t1), tail(t2)))`. -/
def tupleLess : List I64 → List I64 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a.val < b.val) || (decide (a.val = b.val) && tupleLess as bs)

/-- `isless(I1::CartesianIndex, I2::CartesianIndex) = isless(reverse(I1.I), reverse(I2.I))`,
`base/multidimensional.jl:142`. -/
def ciLess (a b : List I64) : Bool := tupleLess a.reverse b.reverse

/-! ## `reverse(::CartesianIndices; dims)` -/

/-- Validity check of `_reverse(iter::CartesianIndices, dims::Tuple)`,
`base/multidimensional.jl:558-562`: `dimrev[i] = sum(==(i), dims) == 1` and
`length(dims) == sum(dimrev)`, else `ArgumentError`. -/
def reverseDimsOk (N : Nat) (dims : List Int) : Bool :=
  let dimrev := (List.range N).map fun (i : Nat) => decide (dims.count ((i : Int) + 1) = 1)
  dims.length == dimrev.count true

/-! ## Arrays -/

/-- Axes of a 1-based `Array` of size `sz`. -/
def oneAxes (sz : List Nat) : List (Int × Int) := sz.map fun (n : Nat) => ((1 : Int), (n : Int))

/-- `checkbounds(Bool, A, I)` for a `CartesianIndex` `I` and an array with axes `ax`. -/
def inAxes (ax : List (Int × Int)) (J : List Int) : Bool :=
  J.length == ax.length && (ax.zip J).all fun ((lo, hi), j) => decide (lo ≤ j ∧ j ≤ hi)

/-- `copyto!(dest, Rdest::CartesianIndices, src, Rsrc::CartesianIndices)`,
`base/multidimensional.jl:1190-1216`, on arrays with axes `axd`, `axs`. -/
def copytoCI {α : Type} (axd : List (Int × Int)) (dest : List Int → Option α) (Rd : List Rng)
    (axs : List (Int × Int)) (src : List Int → α) (Rs : List Rng) : R (List Int → Option α) :=
  if Rd.any (·.len == 0) then .ok dest                                -- isempty(Rdest)
  else if Rd.map (·.len) ≠ Rs.map (·.len) then .error .argumentError  -- size check
  else if !(inAxes axd (Rd.map (·.start.val)) && inAxes axd (Rd.map (·.last.val)) &&
            inAxes axs (Rs.map (·.start.val)) && inAxes axs (Rs.map (·.last.val)))
  then .error .boundsError
  else .ok fun J =>
    match (Rd.zip J).mapM (fun (r, j) => r.pos j) with
    | some ks => if J.length = Rd.length then some (src ((Rs.zip ks).map fun (r, k) => r.elem k))
                 else dest J
    | none => dest J

/-! ## `circshift!` and `circcopy!` -/

/-- `fill_to_length(t, 0, Val(N))`: pads with zeros; a longer tuple is an
`ArgumentError` ("input tuple of length ..., requested ..."). -/
def fillToLength (t : List Int) (N : Nat) : R (List Int) :=
  if t.length > N then .error .argumentError else .ok (t ++ List.replicate (N - t.length) 0)

/-- The `copyto!` blocks of `_circshift!`, `base/multidimensional.jl:1284-1299`, for the
axes `1:n` of each dimension, in call order (destination block, source block). The
shift amounts are exact integers: `mod(d, n)` of any `Integer` by a positive `Int` is
exact and lies in `[0, n)`, so the sums `first(ind1) + s` and `last(ind1) - s` do not
wrap. -/
def circBlocks : List Nat → List Int → List (List (Int × Int) × List (Int × Int))
  | n :: ns, d :: ds =>
    let s := d % (n : Int)
    let sf := 1 + s
    let sl := (n : Int) - s
    let r1 := ((1 : Int), sf - 1)
    let r2 := (sf, (n : Int))
    let r3 := ((1 : Int), sl)
    let r4 := (sl + 1, (n : Int))
    let rest := circBlocks ns ds
    rest.map (fun b => (r1 :: b.1, r4 :: b.2)) ++ rest.map (fun b => (r2 :: b.1, r3 :: b.2))
  | _, _ => [([], [])]

/-- Run the `copyto!` calls of a block list. -/
def runBlocks {α : Type} (axd axs : List (Int × Int)) (src : List Int → α) :
    List (List (Int × Int) × List (Int × Int)) → (List Int → Option α) → R (List Int → Option α)
  | [], dest => .ok dest
  | (bd, bs) :: rest, dest => do
    let dest' ← copytoCI axd dest (bd.map fun p => unitRng p.1 p.2) axs src
      (bs.map fun p => unitRng p.1 p.2)
    runBlocks axd axs src rest dest'

/-- `circshift(A, shifts) = circshift!(similar(A), A, shifts)` for an `Array` of size
`sz` (`base/abstractarraymath.jl:335-338, 411-413`, `base/multidimensional.jl:1257-1263`).
`similar` leaves the destination uninitialised (`none`). -/
def circshift {α : Type} (sz : List Nat) (src : List Int → α) (shifts : List Int) :
    R (List Int → Option α) :=
  if sz.any (· == 0) then .ok fun _ => none          -- isempty(src) && return dest
  else do
    let sh ← fillToLength shifts sz.length
    runBlocks (oneAxes sz) (oneAxes sz) src (circBlocks sz sh) fun _ => none

/-- The `copyto!` blocks of `_circcopy!`, `base/multidimensional.jl:1349-1366`, for
destination and source axes `indd`, `inds` of equal lengths. `mod(_, 0)` is a
`DivideError`. -/
def circcopyBlocks : List (Int × Int) → List (Int × Int) →
    R (List (List (Int × Int) × List (Int × Int)))
  | (fd, ld) :: tds, (fs, ls) :: tss => do
    let l := ld - fd + 1
    if l = 0 then throw .divideError
    let s := (fs - fd) % l
    let sdf := fd + s
    let rd1 := (fd, sdf - 1)
    let rd2 := (sdf, ld)
    let ssf := ls - s
    let rs1 := (fs, ssf)
    let rs2 := (ssf + 1, ls)
    let rest ← circcopyBlocks tds tss
    pure (rest.map (fun b => (rd1 :: b.1, rs2 :: b.2)) ++ rest.map (fun b => (rd2 :: b.1, rs1 :: b.2)))
  | _, _ => pure [([], [])]

/-- `circcopy!(dest, src)`, `base/multidimensional.jl:1337-1346`, for arrays with
nonempty-or-empty axes `axd`, `axs` (`lo:hi`, `hi = lo - 1` when empty). -/
def circcopy {α : Type} (axd : List (Int × Int)) (dest : List Int → Option α)
    (axs : List (Int × Int)) (src : List Int → α) : R (List Int → Option α) := do
  if axs.map (fun p => p.2 - p.1 + 1) ≠ axd.map (fun p => p.2 - p.1 + 1) then
    throw .dimensionMismatch
  if (axs.zip axd).all (fun (s, d) => s.1 - d.1 = 0) then
    -- copyto!(dest, src): same sizes, so it copies elementwise in iteration order
    return fun J => if inAxes axd J then
      some (src ((J.zip (axs.zip axd)).map fun (j, s, d) => j - d.1 + s.1)) else dest J
  let blocks ← circcopyBlocks axd axs
  runBlocks axd axs src blocks dest

/-! ## `findnext`/`findfirst` on arrays -/

/-- The loop of the generic `findnext(testf, A, start)`, `base/array.jl:2475-2486`,
with `keys(A) = CartesianIndices(axes(A))` for an `Array` of size `sz`; `A[i]` throws
`BoundsError` outside the array and `nextind(A, i)` is `inc(i.I, iter.indices)`
(`base/multidimensional.jl:159-164`). `fuel` bounds the number of iterations. -/
def findLoop (sz : List Nat) (A : List Int → Bool) : Nat → List I64 → R (Option (List I64))
  | 0, _ => .ok none
  | fuel + 1, i =>
    if !inAxes (oneAxes sz) (i.map (·.val)) then .error .boundsError
    else if A (i.map (·.val)) then .ok (some i)
    else if i = sz.map (fun (n : Nat) => i64 n) then .ok none
    else findLoop sz A fuel (inc i (sz.map fun (n : Nat) => (⟨i64 1, i64 1, n⟩ : Rng))).2

/-- `findnext(testf, A, start)`, `base/array.jl:2475-2486`: `l = last(keys(A))`,
`i > l && return nothing`, then the loop. -/
def findnext (sz : List Nat) (A : List Int → Bool) (start : List I64) : R (Option (List I64)) :=
  let l := sz.map fun (n : Nat) => i64 n
  if ciLess l start then .ok none
  else findLoop sz A (sz.foldl (· * ·) 1 + 1) start

/-- `findfirst(testf, A::AbstractArray) = findnext(testf, A, first(keys(A)))`,
`base/array.jl:2444, 2531-2532`. -/
def findfirst (sz : List Nat) (A : List Int → Bool) : R (Option (List I64)) :=
  findnext sz A (sz.map fun _ => i64 1)

/-- The first index of `A` (column-major order) holding `true`. -/
def firstTrue (sz : List Nat) (A : List Int → Bool) : Option (List I64) :=
  (elems (sz.map fun (n : Nat) => (⟨i64 1, i64 1, n⟩ : Rng))).find? fun I => A (I.map (·.val))

/-! ## `selectdim` and `view` -/

/-- An index argument. `urange lo hi` is `lo:hi` (it also stands for a `Vector{Int}` with
those values); `slice n` is `Base.Slice(OneTo(n))`; `cart vs` is `CartesianIndex(vs...)`. -/
inductive Idx where
  | int (v : Int)
  | bool (b : Bool)
  | urange (lo hi : Int)
  | colon
  | slice (n : Nat)
  | cart (vs : List Int)
  deriving DecidableEq, Repr

/-- Number of array dimensions an index consumes (`index_ndims`). -/
def Idx.ndims : Idx → Nat
  | .cart vs => vs.length
  | _ => 1

/-- `i == 1` in `_selectdim` (`Int`, `Bool`: numeric equality; ranges, `Colon`,
`CartesianIndex`: `false`). -/
def Idx.eqOne : Idx → Bool
  | .int v => v == 1
  | .bool b => b
  | _ => false

/-- Axis lengths seen by `k` consumed dimensions of an array of size `sz`: trailing
dimensions beyond `ndims` have length 1; with fewer indices than dimensions the last
index spans the remaining dimensions (linear indexing). -/
def axesFor (sz : List Nat) (k : Nat) : List Nat :=
  if sz.length ≤ k then sz ++ List.replicate (k - sz.length) 1
  else sz.take (k - 1) ++ [(sz.drop (k - 1)).foldl (· * ·) 1]

/-- Split the axis lengths among the indices. -/
def splitAxes : List Idx → List Nat → List (Idx × List Nat)
  | [], _ => []
  | i :: is, ax => (i, ax.take i.ndims) :: splitAxes is (ax.drop i.ndims)

/-- `checkindex(Bool, inds, i)` for one index and the axes it covers
(`base/abstractarray.jl:719-760`; a `Slice` is accepted unchecked, line 755). -/
def checkIdx : Idx → List Nat → Bool
  | .int v, [n] => decide (1 ≤ v ∧ v ≤ n)
  | .urange lo hi, [n] => decide (hi < lo ∨ (1 ≤ lo ∧ hi ≤ n))
  | .colon, _ => true
  | .slice _, _ => true
  | .cart vs, ns => vs.length == ns.length && (vs.zip ns).all fun (v, n) => decide (1 ≤ v ∧ v ≤ n)
  | _, _ => false

/-- Length of the view dimension an index produces (`none`: dropped, scalar). -/
def idxLen : Idx → List Nat → Option Nat
  | .urange lo hi, _ => some (hi - lo + 1).toNat
  | .colon, ns => some (ns.foldl (· * ·) 1)
  | .slice n, _ => some n
  | _, _ => none

/-- `view(A, I...)` for an `Array` of size `sz` (`base/subarray.jl`): `to_indices`
rejects `Bool` scalars with `ArgumentError` (`to_index(::Bool)`), then `checkbounds`
throws `BoundsError`. Returns the size of the view. -/
def view (sz : List Nat) (I : List Idx) : R (List Nat) :=
  let parts := splitAxes I (axesFor sz (I.foldl (fun k i => k + i.ndims) 0))
  if I.any (fun i => match i with | .bool _ => true | _ => false) then .error .argumentError
  else if !(parts.all fun (i, ns) => checkIdx i ns) then .error .boundsError
  else .ok (parts.filterMap fun (i, ns) => idxLen i ns)

/-- Every array position a view can address lies inside the array: each index stays
within the true length of each dimension it covers (dimensions beyond `ndims(A)` have
length 1), whether or not `checkbounds` looked at it. -/
def viewInBounds (sz : List Nat) (I : List Idx) : Bool :=
  let parts := splitAxes I (axesFor sz (I.foldl (fun k i => k + i.ndims) 0))
  parts.all fun (i, ns) => match i, ns with
    | .slice n, [m] => decide (n ≤ m)
    | i, ns => checkIdx i ns

/-- Index tuple built by `selectdim(A, d, i)`, `base/abstractarraymath.jl:327`:
`_setindex(i, d, map(Slice, axes(A))...)` replaces slot `d` of the `ndims(A)` slices
(and leaves them unchanged when `d > ndims(A)`). -/
def selectdimIdxs (sz : List Nat) (d : Nat) (i : Idx) : List Idx :=
  (List.range sz.length).map fun (j : Nat) => if j + 1 = d then i else .slice (sz.getD j 0)

/-- `selectdim(A, d, i)`, `base/abstractarraymath.jl:327-333`: the index tuple of the
returned view, after `_selectdim`'s checks and `view`'s. -/
def selectdim (sz : List Nat) (d : Int) (i : Idx) : R (List Idx) := do
  if ¬ (d ≥ 1) then throw .argumentError
  if d > sz.length ∧ !i.eqOne then throw .boundsError
  let I := selectdimIdxs sz d.toNat i
  let _ ← view sz I
  pure I

/-! ## `cat` -/

/-- A `cat` argument: a scalar (`cat_size = (1,)`) or an `Array` of the given size. -/
inductive CatArg where
  | scalar
  | array (sz : List Nat)
  deriving DecidableEq, Repr

/-- `cat_size(A)`, `base/abstractarray.jl:1836-1837`. -/
def CatArg.size : CatArg → List Nat
  | .scalar => [1]
  | .array sz => sz

/-- `cat_size(A, d)` (0-based `d`): `size(A, d+1)`, 1 beyond `ndims`; 1 for scalars. -/
def CatArg.sizeAt (x : CatArg) (d : Nat) : Nat :=
  match x with
  | .scalar => 1
  | .array sz => sz.getD d 1

/-- `_cs(d, a, b)`, `base/abstractarray.jl:1894-1895`. -/
def cs (a b : Nat) : R Nat := if a = b then .ok a else .error .dimensionMismatch

/-- `_cshp(ndim, (), shape, nshape)`, `base/abstractarray.jl:1872-1873, 1879-1886` (the
methods for an exhausted `dims`; `ndim` only appears in error messages). -/
def cshpNoDims : List Nat → List Nat → R (List Nat)
  | [], nshape => .ok nshape
  | a :: as, [] => do
    let _ ← cs a 1
    let rest ← cshpNoDims as []
    pure (1 :: rest)
  | a :: as, b :: bs => do
    let next ← cs a b
    let rest ← cshpNoDims as bs
    pure (next :: rest)

/-- `_cshp(ndim, dims, shape, nshape)`, `base/abstractarray.jl:1872-1892` (eight methods;
the empty/nonempty pattern of the arguments selects the most specific one). -/
def cshp : List Bool → List Nat → List Nat → R (List Nat)
  | [], shape, nshape => cshpNoDims shape nshape
  | dims, [], [] => .ok (dims.map fun _ => 1)
  | d :: ds, a :: as, [] => do
    let rest ← cshp ds as []
    pure ((a + if d then 1 else 0) :: rest)
  | _ :: ds, [], b :: bs => do
    let rest ← cshp ds [] bs
    pure (b :: rest)
  | d :: ds, a :: as, b :: bs => do
    let next ← if d then pure (a + b) else cs a b
    let rest ← cshp ds as bs
    pure (next :: rest)

/-- `cat_size_shape(dims, X...)`, `base/abstractarray.jl:1867-1870`. -/
def catSizeShape (dims : List Bool) : List CatArg → R (List Nat)
  | [] => .ok (dims.map fun _ => 0)
  | x :: xs => do
    let s0 ← cshp dims [] x.size
    xs.foldlM (fun s y => cshp dims s y.size) s0

/-- `dims2cat(dims)`, `base/abstractarray.jl:1898-1903`. -/
def dims2cat (dims : List Int) : R (List Bool) :=
  if dims.any (· ≤ 0) then .error .argumentError
  else match dims.max? with
    | none => .error .argumentError     -- maximum(()) throws
    | some m => .ok ((List.range m.toNat).map fun (i : Nat) => dims.contains ((i : Int) + 1))

/-- `setindex_shape_check(X, shape)` (`base/indices.jl:216-225`) for an `Array` `X`. -/
def setindexShapeCheck (sz shape : List Nat) : Bool :=
  if sz.length = 1 ∨ shape.length = 1 then sz.foldl (· * ·) 1 == shape.foldl (· * ·) 1
  else
    let rec go : List Nat → List Nat → Bool
      | [], [] => true
      | a, [] => a.all (· == 1)
      | [], b => b.all (· == 1)
      | a :: as, b :: bs => a == b && go as bs
    go sz shape

/-- `cat(X...; dims)` = `_cat_t(dims, T, X...)`, `base/abstractarray.jl:1907-1942`:
the result size, after `__cat_offset1!` stores each argument (`fill!` of the block for a
scalar, `A[inds...] = x` with its shape check for an array). -/
def cat (dims : List Int) (xs : List CatArg) : R (List Nat) := do
  let catdims ← dims2cat dims
  let shape ← catSizeShape catdims xs
  for x in xs do
    match x with
    | .scalar => pure ()
    | .array sz =>
      let blk := (List.range shape.length).map fun (i : Nat) =>
        if catdims.getD i false then x.sizeAt i else shape.getD i 0
      if !setindexShapeCheck sz blk then throw .dimensionMismatch
  pure shape

/-! ## `hvcat` -/

/-- `hvcat(rows, xs::T...) where T<:Number`, `base/abstractarray.jl:2253-2272`, with `n`
values. -/
def hvcatSame (rows : List Nat) (n : Nat) : R (Nat × Nat) :=
  match rows with
  | [] => .error .boundsError                         -- rows[1]
  | nc :: _ =>
    let nr := rows.length
    if nr * nc ≠ n then .error .argumentError
    else if rows.any (· ≠ nc) then .error .dimensionMismatch
    else .ok (nr, nc)

/-- `typed_hvcat(T, rows, xs::Number...)`, `base/abstractarray.jl:2279-2290`, with the
count check of `hvncat_fill!` (lines 2556-2566). -/
def hvcatTyped (rows : List Nat) (n : Nat) : R (Nat × Nat) :=
  match rows with
  | [] => .error .boundsError
  | nc :: rest =>
    if rest.any (· ≠ nc) then .error .dimensionMismatch
    else if rows.length * nc ≠ n then .error .argumentError
    else .ok (rows.length, nc)

/-- `hvcat(nbc::Int, as...)`, `base/abstractarray.jl:2197-2204`, with `n` values of one
`Number` type; `hvcat(())` with no values returns `[]`. -/
def hvcatCols (nbc : I64) (n : Nat) : R (Nat × Nat) := do
  let nI := i64 n
  let m ← (JInt.mod nI nbc).mapError fun _ => Err.divideError
  if m.val ≠ 0 then throw .argumentError
  let nbr ← (JInt.div nI nbc).mapError fun _ => Err.divideError
  if nbr.val < 0 then throw .argumentError         -- ntuple with a negative length
  if nbr.val = 0 then return (0, 0)                -- hvcat(()) = []
  hvcatSame (List.replicate nbr.val.toNat nbc.val.toNat) n

/-! ## `repeat` and `diff` -/

/-- `Base.checked_mul` on `Int`. -/
def checkedMul (a b : Int) : R Int :=
  if IntTy.min .i64 ≤ a * b ∧ a * b ≤ IntTy.max .i64 then .ok (a * b) else .error .overflowError

/-- `_RepeatInnerOuter.check`, `base/abstractarraymath.jl:526-552`, for integer counts. -/
def repeatCheck (N : Nat) (inner outer : Option (List Int)) : R Unit := do
  if let some i := inner then
    if i.any (· < 0) then throw .argumentError
    if i.length < N then throw .argumentError
  if let some o := outer then
    if o.any (· < 0) then throw .argumentError
    if o.length < N ∧ inner.isSome then throw .argumentError

/-- Pad with ones to length `N` (`fill_to_length(a, 1, Val(N))`). -/
def padOnes (a : List Int) (N : Nat) : List Int := a ++ List.replicate (N - a.length) 1

/-- Size of `repeat(A; inner, outer)` for an array of size `sz`
(`base/abstractarraymath.jl:488-612`): `check`, `resolve` (padding to a common length)
and the `checked_mul` size computations of `repeat_inner`/`repeat_outer`. -/
def repeatSize (sz : List Int) (inner outer : Option (List Int)) : R (List Int) := do
  repeatCheck sz.length inner outer
  let N := max sz.length (max ((inner.map List.length).getD 0) ((outer.map List.length).getD 0))
  let s := padOnes sz N
  let s ← match inner with
    | none => pure s
    | some i => (s.zip (padOnes i N)).mapM fun (a, b) => checkedMul a b
  match outer with
    | none => pure s
    | some o => (s.zip (padOnes o N)).mapM fun (a, b) => checkedMul a b

/-- `diff(a::AbstractArray; dims)`, `base/multidimensional.jl:1113-1122`: size of
`view(a, r1...) .- view(a, r0...)`, where `r0 = UnitRange(1, n-1)` and
`r1 = UnitRange(2, n)` along `dims`; broadcasting views of different sizes throws
`DimensionMismatch`. -/
def diffSize (sz : List Nat) (dims : Int) : R (List Nat) := do
  if ¬ (1 ≤ dims ∧ dims ≤ sz.length) then throw .argumentError
  let r0 := (List.range sz.length).map fun (i : Nat) =>
    if (i : Int) + 1 = dims then ((sz.getD i 0 : Int) - 1 - 1 + 1).toNat else sz.getD i 0
  let r1 := (List.range sz.length).map fun (i : Nat) =>
    if (i : Int) + 1 = dims then ((sz.getD i 0 : Int) - 2 + 1).toNat else sz.getD i 0
  if r0 ≠ r1 then throw .dimensionMismatch
  pure r1

end JuliaLean.Multidim
