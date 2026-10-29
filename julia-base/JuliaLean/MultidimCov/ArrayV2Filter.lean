import JuliaLean.MultidimCov.ArrayV2DeleteProps

/-!
`filter` and `filter!` (master `base/array.jl:3020-3107`).

A predicate `f` returns `some b` for a `Bool` result `b`, `none` for a result of any other
type (which the `f(ai)::Bool` assertions reject), or throws. An `AbstractArray` that is not
an `Array` is `AbsArr`: its elements in linear (column-major) order and whether its
`IndexStyle` is `IndexLinear()`.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- `f(ai)::Bool`. -/
def predBool (f : α → R (Option Bool)) (x : α) : R Bool := do
  let r ← f x
  match r with
  | some b => pure b
  | none => .error .typeError

/-- The loop of base/array.jl:3022-3025 over `a`'s slots `i, i+1, …` (`for ai in a` reads each
slot, `UndefRefError` for `#undef`): `@inbounds b[j] = ai; j = ifelse(f(ai)::Bool, j+1, j)`. -/
def filterLoop (f : α → R (Option Bool)) (a : Arr α) : Arr α → Nat → Int → Int → R (Arr α × Int)
  | b, 0, _, j => pure (b, j)
  | b, k + 1, i, j => do
    let ai ← getU a i
    let b := setU b j (some ai)
    let keep ← predBool f ai
    filterLoop f a b k (i + 1) (if keep then j + 1 else j)

/-- base/array.jl:3020 `filter(f, a::Array{T, N})`: `b = Vector{T}(undef, length(a))`, the
loop, `resize!(b, j-1)`, `sizehint!(b, length(b))`. -/
def m3020 (f : α → R (Option Bool)) (a : Arr α) : R (Arr α) := do
  let b ← newArray [length a]
  let (b, j) ← filterLoop f a b (length a).toNat 1 1
  let b ← m1564 b (j - 1) false
  m1617 b (length b) false true

/-- An `AbstractArray` given by its elements in linear order and its index style. -/
structure AbsArr (α : Type) where
  elems : List α
  linear : Bool

/-- `@inbounds a[idx]` for an index of `eachindex(a)`. -/
def absGet (a : AbsArr α) (idx : Int) : R α :=
  match a.elems[(idx - 1).toNat]? with
  | some x => .ok x
  | none => .error .bounds

/-- Historical map-all-then-assert model of the earlier Cartesian branch. -/
def mapBoolMask (f : α → R (Option Bool)) (inferBool : Bool) (xs : List α) : R (List Bool) := do
  let rs ← xs.mapM f
  let isBool := if rs.isEmpty then inferBool else rs.all Option.isSome
  if isBool then pure (rs.map fun r => r.getD false) else .error .typeError

/-- Target `map!(x -> f(x)::Bool, similar(a, Bool), a)` predicate loop. -/
def mapBoolMaskTarget (f : α → R (Option Bool)) (xs : List α) : R (List Bool) :=
  xs.mapM (predBool f)

/-- Calls made by the target loop, including the first call that fails. -/
def mapBoolMaskTrace (f : α → R (Option Bool)) : List α → List α × R (List Bool)
  | [] => ([], .ok [])
  | x :: xs =>
    match predBool f x with
    | .error e => ([x], .error e)
    | .ok b =>
      let (calls, result) := mapBoolMaskTrace f xs
      (x :: calls, result.map (b :: ·))

/-- `a[mask]` (logical indexing): `BoundsError` for a mask of another length, else the
elements where `mask` is true. -/
def absMask (a : AbsArr α) (mask : List Bool) : R (List α) :=
  if mask.length ≠ a.elems.length then .error .bounds else (maskIdx mask true).mapM (absGet a)

/-- The loop of base/array.jl:3037-3042: `@inbounds idxs[j] = idx; ai = @inbounds a[idx];
j = ifelse(f(ai)::Bool, j+1, j)`. -/
def idxLoop (f : α → R (Option Bool)) (a : AbsArr α) : Arr Int → Nat → Int → Int → R (Arr Int × Int)
  | idxs, 0, _, j => pure (idxs, j)
  | idxs, k + 1, idx, j => do
    let idxs := setU idxs j (some idx)
    let ai ← absGet a idx
    let keep ← predBool f ai
    idxLoop f a idxs k (idx + 1) (if keep then j + 1 else j)

/-- Reading an assigned `Vector{Int}`. -/
def intSlots (xs : List (Option Int)) : R (List Int) :=
  xs.mapM fun s => match s with
    | some i => .ok i
    | none => .error .undefRef

/-- Historical `filter(f, a::AbstractArray)` model from the previous source. -/
def m3032Historical (f : α → R (Option Bool)) (inferBool : Bool) (a : AbsArr α) : R (List α) :=
  if ¬ a.linear then do
    let mask ← mapBoolMask f inferBool a.elems
    absMask a mask
  else do
    let n := (a.elems.length : Int)
    let idxs ← newArray [n]
    let (idxs, j) ← idxLoop f a idxs n.toNat 1 1
    let idxs ← m1564 idxs (j - 1) false
    let sel ← intSlots (contents idxs)
    let res ← sel.mapM (absGet a)
    let idxs ← m2155 idxs
    let _ ← m1617 idxs 0 false true
    pure res

/-- Cartesian operations whose behavior depends on the concrete array type.
`allocate` represents `similar(a, Bool)` and `index` represents `a[mask]`. -/
structure CartesianOps (α : Type) where
  allocate : AbsArr α → R Unit
  index : AbsArr α → List Bool → R (List α)

/-- Cartesian target with allocation and logical indexing left explicit. -/
def filterCartesianTarget (ops : CartesianOps α) (f : α → R (Option Bool))
    (a : AbsArr α) : R (List α) := do
  let _ ← ops.allocate a
  let mask ← mapBoolMaskTarget f a.elems
  ops.index a mask

/-- An abstract Cartesian array's axes, iteration indices, and indexed reads.
Each index is a tuple of coordinates, including offset coordinates. -/
structure IndexedAbsArr (α : Type) where
  axes : List (List Int)
  eachindex : List (List Int)
  get : List Int → R α

/-- The allocated Boolean destination and the methods supplied by its array type. -/
structure MaskDestination (σ : Type) where
  axes : List (List Int)
  eachindex : List (List Int)
  initial : σ
  set : σ → List Int → Bool → R σ

/-- The Julia operations that depend on the concrete array and mask types. -/
structure IndexedCartesianOps (α σ : Type) where
  similar : IndexedAbsArr α → R (MaskDestination σ)
  logicalIndex : IndexedAbsArr α → MaskDestination σ → σ → R (List α)

/-- `map!` zips destination and source iteration indices. Each read, predicate
assertion and write completes before the next pair is visited. -/
def indexedMaskLoop (f : α → R (Option Bool)) (a : IndexedAbsArr α)
    (dest : MaskDestination σ) : List (List Int) → List (List Int) → σ → R σ
  | i :: is, j :: js, state => do
    let x ← a.get j
    let b ← predBool f x
    let state ← dest.set state i b
    indexedMaskLoop f a dest is js state
  | _, _, state => .ok state

/-- The Cartesian source branch, including allocation, paired `eachindex`
iteration, destination writes, and logical indexing. -/
def indexedFilterCartesian (ops : IndexedCartesianOps α σ)
    (f : α → R (Option Bool)) (a : IndexedAbsArr α) : R (List α) := do
  let dest ← ops.similar a
  let mask ← indexedMaskLoop f a dest dest.eachindex a.eachindex dest.initial
  ops.logicalIndex a dest mask

/-- Column-major Cartesian indices, with the first coordinate varying fastest. -/
def cartesianIndices (axes : List (List Int)) : List (List Int) :=
  axes.foldl (fun indices axis => axis.flatMap fun x => indices.map fun idx => idx ++ [x]) [[]]

/-- Necessary representation conditions for an ordinary finite Julia array.
Additional laws for custom `getindex`, `setindex!`, `similar`, and logical
indexing remain explicit at their respective interfaces. -/
def IndexedAbsArr.WellFormed (a : IndexedAbsArr α) : Prop :=
  (a.eachindex.length : Int) ≤ typemaxInt ∧
  a.eachindex = cartesianIndices a.axes ∧
  (∀ axis ∈ a.axes, axis.Nodup ∧ ∀ x ∈ axis, typeminInt ≤ x ∧ x ≤ typemaxInt)

/-- Linear-indexed arrays may have offset vector axes. -/
structure IndexedLinearArr (α : Type) where
  axes : List (List Int)
  length : Int
  eachindex : List Int
  get : Int → R α

/-- Julia's linear iteration uses a vector's axis and otherwise `1:length(a)`. -/
def IndexedLinearArr.WellFormed (a : IndexedLinearArr α) : Prop :=
  0 ≤ a.length ∧ a.length ≤ typemaxInt ∧
  a.length = (a.axes.foldl (fun n axis => n * axis.length) 1 : Nat) ∧
  (∀ axis ∈ a.axes, axis.Nodup ∧ ∀ x ∈ axis, typeminInt ≤ x ∧ x ≤ typemaxInt) ∧
  a.eachindex = match a.axes with
    | [axis] => axis
    | _ => (List.range a.length.toNat).map (fun (k : Nat) => (k : Int) + 1)

/-- The source branch's vector allocation, writes, resizing, indexing and cleanup. -/
structure IndexedLinearOps (α σ : Type) where
  allocate : Int → R σ
  set : σ → Int → Int → R σ
  resize : σ → Int → R σ
  index : IndexedLinearArr α → σ → R (List α)
  empty : σ → R σ
  sizehint : σ → R σ

/-- The concrete `Vector{Int}` operations used by the linear branch. The
source array's vector-indexing dispatch remains an explicit callback. -/
def linearVectorOps (index : IndexedLinearArr α → Arr Int → R (List α)) :
    IndexedLinearOps α (Arr Int) where
  allocate n := newArray [n]
  set state j idx := .ok (setU state j (some idx))
  resize state n := m1564 state n false
  index := index
  empty := m2155
  sizehint state := m1617 state 0 false true

/-- The linear filter loop writes each index before reading and testing its value. -/
def indexedLinearLoop (ops : IndexedLinearOps α σ) (f : α → R (Option Bool))
    (a : IndexedLinearArr α) : List Int → σ → Int → R (σ × Int)
  | [], state, j => .ok (state, j)
  | idx :: rest, state, j => do
    let state ← ops.set state j idx
    let x ← a.get idx
    let keep ← predBool f x
    indexedLinearLoop ops f a rest state (if keep then wrap64 (j + 1) else j)

/-- The target linear branch, with allocation and array methods explicit. -/
def indexedFilterLinear (ops : IndexedLinearOps α σ) (f : α → R (Option Bool))
    (a : IndexedLinearArr α) : R (List α) := do
  let idxs ← ops.allocate a.length
  let (idxs, j) ← indexedLinearLoop ops f a a.eachindex idxs 1
  let idxs ← ops.resize idxs (wrap64 (j - 1))
  let result ← ops.index a idxs
  let idxs ← ops.empty idxs
  let _ ← ops.sizehint idxs
  pure result

/-- The two `IndexStyle` branches and their type-specific array operations. -/
inductive IndexedFilterInput (α : Type) where
  | cartesian (array : IndexedAbsArr α)
  | linear (array : IndexedLinearArr α)

def indexedFilterTarget (cartOps : IndexedCartesianOps α σ)
    (linearOps : IndexedLinearOps α τ) (f : α → R (Option Bool)) :
    IndexedFilterInput α → R (List α)
  | .cartesian a => indexedFilterCartesian cartOps f a
  | .linear a => indexedFilterLinear linearOps f a

/-- List-backed approximation of `base/array.jl:3027`. It does not model
offset axes or custom allocation and indexing; use `indexedFilterTarget` for those. -/
def m3032 (f : α → R (Option Bool)) (_inferBool : Bool) (a : AbsArr α) : R (List α) :=
  if ¬ a.linear then do
    let mask ← mapBoolMaskTarget f a.elems
    absMask a mask
  else do
    let n := (a.elems.length : Int)
    let idxs ← newArray [n]
    let (idxs, j) ← idxLoop f a idxs n.toNat 1 1
    let idxs ← m1564 idxs (j - 1) false
    let sel ← intSlots (contents idxs)
    let res ← sel.mapM (absGet a)
    let idxs ← m2155 idxs
    let _ ← m1617 idxs 0 false true
    pure res

/-- The loop of base/array.jl:3068-3071 over the vector being filtered:
`@inbounds a[j] = ai; j = ifelse(f(ai)::Bool, nextind(a, j), j)`. -/
def filterBangLoop (f : α → R (Option Bool)) : Arr α → Nat → Int → Int → R (Arr α × Int)
  | a, 0, _, j => pure (a, j)
  | a, k + 1, i, j => do
    let ai ← getU a i
    let a := setU a j (some ai)
    let keep ← predBool f ai
    filterBangLoop f a k (i + 1) (if keep then j + 1 else j)

/-- base/array.jl:3066 `filter!(f, a::AbstractVector)`: the loop; `a` when every element is
kept; otherwise `resize!(a, j-1)` and `sizehint!(a, j-1)` for a `Vector`, and
`deleteat!(a, j:lastindex(a))` (`delRange`) for any other vector type. -/
def m3066 (f : α → R (Option Bool)) (isVector : Bool) (delRange : Arr α → Int → Int → R (Arr α))
    (a : Arr α) : R (Arr α) := do
  let (a, j) ← filterBangLoop f a (length a).toNat 1 1
  if j > length a then pure a else
  if isVector then do
    let a ← m1564 a (j - 1) false
    m1617 a (j - 1) false true
  else delRange a j (length a)

/-- `Base.Fix1(f, x)` = `Fix{1}` (`base/operators.jl:1202`), called as `(f::Fix{1})(arg) = f.f(f.x, arg)`
(`base/operators.jl:1223`). -/
structure Fix1 (F X Y : Type) where
  f : F → X → Y
  x : F

def Fix1.call (g : Fix1 F X Y) (y : X) : Y := g.f g.x y

/-- base/array.jl:3105 `filter(f) = Fix1(filter, f)`, with `filter` called on an `Array`
(the method `m3020` it dispatches to). -/
def m3105 (f : α → R (Option Bool)) : Fix1 (α → R (Option Bool)) (Arr α) (R (Arr α)) := ⟨m3020, f⟩

end JuliaLean.MultidimCov.ArrayV2
