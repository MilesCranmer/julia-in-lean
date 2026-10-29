import JuliaLean.MultidimCov.ArrayV2Range

/-!
Deletion by index collections, `splice!` and `keepat!` on `Vector` (master
`base/array.jl:1945-2153`, `3134`, `3159`; `_keepat!` at `base/abstractarray.jl:3699-3729`).

An index iterator is its elements in iteration order (`List Int`). The `dltd` argument
of `_deleteat!` is `none` for `Nowhere()` (whose `push!` and `_growend!` do nothing)
and `some l` for the vector `eltype(a)[]` that `splice!(a, inds)` passes: `push!`
appends the read value, `_growend!(dltd, 1)` appends an unassigned slot.

The helpers `_push_deleted!` and `_copy_item!` are called under `@inbounds` with
indices in `1:length(a)` at every call site, so eliding the bounds check inside
`isassigned` does not change their result.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- `push!(dltd, x)`: nothing for `Nowhere()`, append for a vector. -/
def dltdPush : Option (List (Option α)) → Option α → Option (List (Option α))
  | none, _ => none
  | some l, x => some (l ++ [x])

/-- base/array.jl:1952 `_push_deleted!(dltd, a, ind)`: `push!(dltd, a[ind])` when
`isassigned(a, ind)`, else `_growend!(dltd, 1)` (an unassigned slot). -/
def m1952 (dltd : Option (List (Option α))) (a : Arr α) (ind : Int) : R (Option (List (Option α))) :=
  if m239 a ind then do
    let x ← getU a ind
    pure (dltdPush dltd (some x))
  else pure (dltdPush dltd none)

/-- base/array.jl:1961 `_copy_item!(a, p, q)`: `a[p] = a[q]` when `isassigned(a, q)`,
else `unsetindex!(a, p)` (both writes unchecked under `@inbounds`). -/
def m1961 (a : Arr α) (p q : Int) : R (Arr α) :=
  if m239 a q then do
    let x ← getU a q
    pure (setU a p (some x))
  else pure (setU a p none)

/-- `while q < i; @inbounds _copy_item!(a, p, q); p += 1; q += 1; end`. -/
def copyWhile (a : Arr α) (p q i : Int) : R (Arr α × Int × Int) :=
  if q < i then do
    let a ← m1961 a p q
    copyWhile a (p + 1) (q + 1) i
  else pure (a, p, q)
termination_by (i - q).toNat
decreasing_by omega

/-- The `while true` loop of base/array.jl:1978-1993 over the remaining indices. -/
def delLoop (n : Int) (a : Arr α) (dltd : Option (List (Option α))) (p q : Int) :
    List Int → R (Arr α × Option (List (Option α)) × Int × Int)
  | [] => pure (a, dltd, p, q)
  | i :: rest =>
    if ¬ (q ≤ i ∧ i ≤ n) then
      (if i < q then m321 "indices must be unique and sorted" else .error .bounds)
    else do
      let (a, p, _) ← copyWhile a p q i
      let dltd ← m1952 dltd a i
      delLoop n a dltd p (i + 1) rest

/-- base/array.jl:1970 `_deleteat!(a::Vector, inds, dltd=Nowhere())`. -/
def m1970 (a : Arr α) (inds : List Int) (dltd : Option (List (Option α))) :
    R (Arr α × Option (List (Option α))) :=
  let n := length a
  match inds with
  | [] => pure (a, dltd)
  | p :: rest =>
    if ¬ inBounds a p then .error .bounds else do
    let dltd ← m1952 dltd a p
    let (a, dltd, p, q) ← delLoop n a dltd p (p + 1) rest
    let (a, p, _) ← copyWhile a p q (n + 1)
    let a ← m1296 a (n - p + 1)
    pure (a, dltd)

/-- base/array.jl:1945 `deleteat!(a::Vector, inds) = _deleteat!(a, inds)`. -/
def m1945 (a : Arr α) (inds : List Int) : R (Arr α) := do
  let (a, _) ← m1970 a inds none
  pure a

/-- `to_indices(a, (inds,))[1]` for an index vector that is not `AbstractVector{Bool}`
(`base/indices.jl:311, 322, 261`): `to_index(A, I::AbstractArray) = I`. -/
def toIndicesVec (inds : List Int) : List Int := inds

/-- base/array.jl:1946 `deleteat!(a::Vector, inds::AbstractVector) =
_deleteat!(a, to_indices(a, (inds,))[1])`. -/
def m1946 (a : Arr α) (inds : List Int) : R (Arr α) := do
  let (a, _) ← m1970 a (toIndicesVec inds) none
  pure a

/-- `for (q, i) in enumerate(inds); @inbounds _copy_item!(a, p, q); p += !i; end`. -/
def maskLoop (a : Arr α) (p q : Int) : List Bool → R (Arr α × Int)
  | [] => pure (a, p)
  | i :: rest => do
    let a ← m1961 a p q
    maskLoop a (if i then p else p + 1) (q + 1) rest

/-- base/array.jl:2005 `deleteat!(a::Vector, inds::AbstractVector{Bool})`. -/
def m2005 (a : Arr α) (inds : List Bool) : R (Arr α) :=
  let n := length a
  if (inds.length : Int) ≠ n then .error .bounds else do
  let (a, p) ← maskLoop a 1 1 inds
  m1296 a (n - p + 1)

/-- `for x in ins; a[start+k-1] = x; k += 1; end` (checked `setindex!` with conversion). -/
def writeFrom (conv : β → R α) (a : Arr α) (start : Int) : List β → R (Arr α)
  | [] => pure a
  | x :: xs => do
    let a ← m1031 conv a x start
    writeFrom conv a (start + 1) xs

/-- base/array.jl:2070 `splice!(a::Vector, i::Integer, ins=_default_splice)`: `v = a[i]`,
then by `m = length(ins)`: `_deleteat!(a, i, 1)` for `m == 0`, `a[i] = only(ins)` for
`m == 1`, else `_growat!(a, i, m-1)` and `a[i+k-1] = x` for each `x` in `ins`. -/
def m2070 (conv : β → R α) (a : Arr α) (i : Int) (ins : List β) : R (α × Arr α) := do
  let v ← getL a i
  match ins with
  | [] => do
    let a ← m1312 a i 1
    pure (v, a)
  | [x] => do
    let a ← m1031 conv a x i
    pure (v, a)
  | _ => do
    let a ← m1230 a i ((ins.length : Int) - 1)
    let a ← writeFrom conv a i ins
    pure (v, a)

/-- The `if m < d … elseif m > d … end` block of base/array.jl:2141-2146 (`n = length(a)`,
`d = length(r)`, `m = length(ins)`): delete `d - m` slots or grow `m - d` slots at the end
of `r` nearer to an end of `a`. -/
def spliceResize (a : Arr α) (f l m d : Int) : R (Arr α) :=
  let n := length a
  if m < d then m1312 a (if f - 1 < n - l then f else l - (d - m) + 1) (d - m)
  else if m > d then m1230 a (if f - 1 < n - l then f else l + 1) (m - d)
  else pure a

/-- base/array.jl:2125 `splice!(a::Vector, r::AbstractUnitRange{<:Integer}, ins=_default_splice)`
for `r = f:l` (`length(r)` wraps, `base/range.jl:794`): `v = a[r]`; `deleteat!(a, r)` when
`ins` is empty; otherwise the size change, then `a[f+k-1] = x` for each `x` in `ins`. -/
def m2125 (conv : β → R α) (a : Arr α) (f l : Int) (ins : List β) : R (Arr α × Arr α) := do
  let v ← m981 a f (wrap64 (1 + (l - f)))
  let m := (ins.length : Int)
  if m = 0 then do
    let a ← m1905 pure a f l false
    pure (v, a)
  else
  let a ← spliceResize a f l m (wrap64 (1 + (l - f)))
  let a ← writeFrom conv a f ins
  pure (v, a)

/-- base/array.jl:2153 `splice!(a::Vector, inds) = (dltds = eltype(a)[]; _deleteat!(a, inds, dltds); dltds)`:
the removed slots and the modified vector. -/
def m2153 (a : Arr α) (inds : List Int) : R (List (Option α) × Arr α) := do
  let (a, dltds) ← m1970 a inds (some [])
  pure (dltds.getD [], a)

/-- The `for k in inds` loop of base/abstractarray.jl:3702-3712 (`_keepat!(a, inds)`):
check `prev < k`, read `ak = a[k]` (checked), write `@inbounds a[i] = ak` when `i != k`. -/
def keepLoop (a : Arr α) (prev : Option Int) (i : Int) : List Int → R (Arr α × Int)
  | [] => pure (a, i)
  | k :: rest => do
    match prev with
    | some pv => if pv < k then pure () else .error .argument
    | none => pure ()
    let ak ← getL a k
    let a := if i ≠ k then setU a i (some ak) else a
    keepLoop a (some k) (i + 1) rest

/-- base/abstractarray.jl:3699 `_keepat!(a::AbstractVector, inds)` for a `Vector`: the loop,
then `deleteat!(a, i:lastindex(a))`. -/
def keepatIdx (a : Arr α) (inds : List Int) : R (Arr α) := do
  let (a, i) ← keepLoop a none 1 inds
  m1905 pure a i (length a) false

/-- base/array.jl:3134 `keepat!(a::Vector, inds) = _keepat!(a, inds)`. -/
def m3134 (a : Arr α) (inds : List Int) : R (Arr α) := keepatIdx a inds

/-- The `for i in eachindex(a, m)` loop of base/abstractarray.jl:3720-3727
(`_keepat!(a, m::AbstractVector{Bool})`): for `m[i]`, `i == j || (a[j] = a[i])` (both
unchecked) and `j = nextind(a, j)`. -/
def keepMaskLoop (a : Arr α) (j i : Int) : List Bool → R (Arr α × Int)
  | [] => pure (a, j)
  | b :: rest =>
    if b then do
      let a ← if i = j then pure a else do
        let x ← getU a i
        pure (setU a j (some x))
      keepMaskLoop a (j + 1) (i + 1) rest
    else keepMaskLoop a j (i + 1) rest

/-- base/abstractarray.jl:3717 `_keepat!(a::AbstractVector, m::AbstractVector{Bool})` for a
`Vector`: `BoundsError` unless `length(m) == length(a)`, the loop, then
`deleteat!(a, j:lastindex(a))`. -/
def keepatMask (a : Arr α) (m : List Bool) : R (Arr α) :=
  if (m.length : Int) ≠ length a then .error .bounds else do
  let (a, j) ← keepMaskLoop a 1 1 m
  m1905 pure a j (length a) false

/-- base/array.jl:3159 `keepat!(a::Vector, m::AbstractVector{Bool}) = _keepat!(a, m)`. -/
def m3159 (a : Arr α) (m : List Bool) : R (Arr α) := keepatMask a m

end JuliaLean.MultidimCov.ArrayV2
