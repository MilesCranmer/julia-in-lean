import JuliaLean.MultidimCov.ArrayV2Reverse

/-!
`push!`, `append!`, `prepend!`, `pushfirst!`, `resize!`, `sizehint!`, `pop!`,
`popat!`, `popfirst!`, `insert!`, scalar and range `deleteat!` and `empty!` on
`Vector` (master `base/array.jl:1358-1910`, `2155`).

A source collection passed to `append!`/`prepend!` is `Src`: the target vector
itself (`items === a`), another `Array`, a `Tuple` (converted element-wise), or a
general iterator given by its elements and whether it `HasLength`.
-/

namespace JuliaLean.MultidimCov.ArrayV2

inductive Src (α β : Type) where
  | self
  | vec (b : Arr α)
  | tuple (xs : List β)
  | iter (xs : List β) (sized : Bool)

/-- `map(x -> convert(T, x), items)` over a tuple: left to right, first failure propagates. -/
def convList (conv : β → R α) : List β → R (List α)
  | [] => .ok []
  | x :: xs => do
    let y ← conv x
    let ys ← convList conv xs
    pure (y :: ys)

/-- `for i = 1:nx; @_safeindex a[start+i-1] = x[i]; end`. -/
def safeWrites (a : Arr α) (start : Int) : List α → Arr α
  | [] => a
  | x :: xs => safeWrites (m1055 a x start) (start + 1) xs

/-- `copyto!(dest::AbstractArray, dstart, src, sstart, n)` for an iterable `src`
(`base/abstractarray.jl:1003`), writing with `@inbounds dest[i] = val`. -/
def copyIter (dest : Arr α) (dstart : Int) (src : List α) (sstart n : Int) : R (Arr α) :=
  if n < 0 then .error .argument else
  if n = 0 then .ok dest else
  if sstart < 1 then .error .argument else
  if ¬ (inBounds dest dstart ∧ n ≤ length dest - dstart + 1) then .error .bounds else
  match src.drop (sstart - 1).toNat with
  | [] => .error .argument
  | rest =>
    let vals := rest.take n.toNat
    let dest := safeWrites dest dstart vals
    if dstart + vals.length - 1 < dstart + n - 1 then .error .bounds else .ok dest

/-- base/array.jl:1366 `_push!(a::Vector{T}, item::T)`. -/
def m1366 (a : Arr α) (item : α) : R (Arr α) := do
  let a ← m1212 a 1
  pure (m1057 a item (length a))

/-- base/array.jl:1358 `push!(a::Vector{T}, item)`: convert first, then `_push!`. -/
def m1358 (conv : β → R α) (a : Arr α) (item : β) : R (Arr α) := do
  let item ← conv item
  m1366 a item

/-- base/array.jl:1373 `push!(a::Vector{Any}, x)`. -/
def m1373 (a : Arr α) (x : α) : R (Arr α) := do
  let a ← m1212 a 1
  pure (m1055 a x (length a))

/-- base/array.jl:1378 `push!(a::Vector{Any}, x...)`. -/
def m1378 (a : Arr α) (xs : List α) : R (Arr α) := do
  let na := length a
  let nx : Int := xs.length
  let a ← m1212 a nx
  pure (safeWrites a (na + 1) xs)

/-- base/array.jl:1782 `_pushfirst!(a::Vector{T}, item::T)`. -/
def m1782 (a : Arr α) (item : α) : R (Arr α) := do
  let a ← m1151 a 1
  pure (m1057 a item 1)

/-- base/array.jl:1777 `pushfirst!(a::Vector{T}, item)` (used by `_prepend!`). -/
def pushfirstConv (conv : β → R α) (a : Arr α) (item : β) : R (Arr α) := do
  let item ← conv item
  m1782 a item

/-- base/array.jl:1789 `pushfirst!(a::Vector{Any}, x)`. -/
def m1789 (a : Arr α) (x : α) : R (Arr α) := do
  let a ← m1151 a 1
  pure (m1055 a x 1)

/-- base/array.jl:1794 `pushfirst!(a::Vector{Any}, x...)`. -/
def m1794 (a : Arr α) (xs : List α) : R (Arr α) := do
  let nx : Int := xs.length
  let a ← m1151 a nx
  pure (safeWrites a 1 xs)

/-- base/array.jl:1617 `sizehint!(a::Vector, sz; first=false, shrink=true)`. -/
def m1617 (a : Arr α) (sz0 : Int) (first shrink : Bool) : R (Arr α) := do
  let len := length a
  let mem := a.mem
  let memlen := mem.len
  let sz ← toInt sz0
  let sz := max sz len
  let inc := sz - len
  if sz ≤ memlen then
    if ¬ shrink ∨ memlen - sz ≤ Int.tdiv memlen 8 then .ok a else do
    let newmem := m1114 mem sz
    let newref ← if first && len != 0 then memref newmem (inc + 1) else .ok 1
    let newmem ← refCopy newmem newref mem a.off len
    pure { a with mem := newmem, off := newref }
  else if first then do
    let a ← m1151 a inc
    let newref ← refIndex a.mem a.off (inc + 1)
    let a := { a with dims := [len] }
    pure { a with off := newref }
  else do
    let a ← m1212 a inc
    pure { a with dims := [len] }

/-- base/array.jl:1427 `append!(a::Vector{T}, items::Union{AbstractVector{<:T},Tuple})`. -/
def m1427 (conv : β → R α) (a : Arr α) : Src α β → R (Arr α)
  | .tuple xs => do
    let ys ← convList conv xs
    let n ← toInt ys.length
    let a ← m1212 a n
    copyIter a (length a - n + 1) ys 1 n
  | .vec b => do
    let n ← toInt (length b)
    let a ← m1212 a n
    m288 a (length a - n + 1) b 1 n
  | .self => do
    let n ← toInt (length a)
    let a ← m1212 a n
    m288 a (length a - n + 1) a 1 n
  | .iter _ _ => .error .method

/-- `for item in iter; push!(a, item); end`. -/
def pushEach (conv : β → R α) (a : Arr α) : List β → R (Arr α)
  | [] => .ok a
  | x :: xs => do
    let a ← m1358 conv a x
    pushEach conv a xs

/-- base/array.jl:1439 `_append!(a, ::Union{HasLength,HasShape}, iter)`. -/
def m1439 (conv : β → R α) (a : Arr α) (iter : List β) : R (Arr α) := do
  let n ← toInt iter.length
  let a ← m1617 a (length a + n) false false
  pushEach conv a iter

/-- base/array.jl:1447 `_append!(a, ::IteratorSize, iter)`. -/
def m1447 (conv : β → R α) (a : Arr α) (iter : List β) : R (Arr α) := pushEach conv a iter

/-- base/array.jl:1435 `append!(a::AbstractVector, iter) = _append!(a, IteratorSize(iter), iter)`. -/
def m1435 (conv : β → R α) (a : Arr α) (iter : List β) (sized : Bool) : R (Arr α) :=
  if sized then m1439 conv a iter else m1447 conv a iter

/-- `append!(a, v)` dispatch for one argument. -/
def appendOne (conv : β → R α) (a : Arr α) : Src α β → R (Arr α)
  | .iter xs sized => m1435 conv a xs sized
  | s => m1427 conv a s

/-- base/array.jl:1436 `push!(a::AbstractVector, iter...) = append!(a, iter)` (a `Tuple`). -/
def m1436 (conv : β → R α) (a : Arr α) (xs : List β) : R (Arr α) := m1427 conv a (.tuple xs)

/-- base/array.jl:1437 `append!(a::AbstractVector, iter...) = (foreach(v -> append!(a, v), iter); a)`. -/
def m1437 (conv : β → R α) (a : Arr α) : List (Src α β) → R (Arr α)
  | [] => .ok a
  | v :: vs => do
    let a ← appendOne conv a v
    m1437 conv a vs

/-- base/array.jl:1485 `prepend!(a::Vector{T}, items::Union{AbstractVector{<:T},Tuple})`;
a distinct `Array` source does not share memory with `a`, so `unalias` returns it. -/
def m1485 (conv : β → R α) (a : Arr α) : Src α β → R (Arr α)
  | .tuple xs => do
    let ys ← convList conv xs
    let n : Int := ys.length
    let a ← m1151 a n
    copyIter a 1 ys (ys.length - n + 1) n
  | .vec b => do
    let n := length b
    let a ← m1151 a n
    m288 a 1 b (length b - n + 1) n
  | .self => do
    let n := length a
    let a ← m1151 a n
    m288 a 1 a (length a - n + 1) n
  | .iter _ _ => .error .method

/-- `n = 0; for item in iter; n += 1; pushfirst!(a, item); end`. -/
def pushfirstEach (conv : β → R α) (a : Arr α) (n : Int) : List β → R (Arr α × Int)
  | [] => .ok (a, n)
  | x :: xs => do
    let a ← pushfirstConv conv a x
    pushfirstEach conv a (n + 1) xs

/-- base/array.jl:1504 `_prepend!(a::Vector, ::Union{HasLength,HasShape}, iter)`. -/
def m1504 (conv : β → R α) (a : Arr α) (iter : List β) : R (Arr α) := do
  let n ← toInt iter.length
  let a ← m1617 a (length a + n) true false
  let (a, n) ← pushfirstEach conv a 0 iter
  m2317 a 1 n

/-- base/array.jl:1517 `_prepend!(a::Vector, ::IteratorSize, iter)`. -/
def m1517 (conv : β → R α) (a : Arr α) (iter : List β) : R (Arr α) := do
  let (a, n) ← pushfirstEach conv a 0 iter
  m2317 a 1 n

/-- base/array.jl:1500 `prepend!(a::AbstractVector, iter) = _prepend!(a, IteratorSize(iter), iter)`. -/
def m1500 (conv : β → R α) (a : Arr α) (iter : List β) (sized : Bool) : R (Arr α) :=
  if sized then m1504 conv a iter else m1517 conv a iter

def prependOne (conv : β → R α) (a : Arr α) : Src α β → R (Arr α)
  | .iter xs sized => m1500 conv a xs sized
  | s => m1485 conv a s

/-- base/array.jl:1501 `pushfirst!(a::AbstractVector, iter...) = prepend!(a, iter)`. -/
def m1501 (conv : β → R α) (a : Arr α) (xs : List β) : R (Arr α) := m1485 conv a (.tuple xs)

/-- base/array.jl:1502 `prepend!(a, iter...) = (for v = reverse(iter); prepend!(a, v); end; a)`. -/
def m1502 (conv : β → R α) (a : Arr α) (vs : List (Src α β)) : R (Arr α) :=
  vs.reverse.foldlM (fun a v => prependOne conv a v) a

/-- base/array.jl:1564 `resize!(a::Vector, nl::Integer; first=false)`. -/
def m1564 (a : Arr α) (nl0 : Int) (first : Bool) : R (Arr α) := do
  let nl ← toInt nl0
  let l := length a
  if nl > l then
    if first then m1151 a ((nl - l) % 2 ^ 63) else m1212 a ((nl - l) % 2 ^ 63)
  else if nl ≠ l then
    if nl < 0 then m321 "new length must be ≥ 0" else
    if first then m1278 a (l - nl) else m1296 a (l - nl)
  else .ok a

/-- base/array.jl:1700 `pop!(a::Vector)`. -/
def m1700 (a : Arr α) : R (α × Arr α) :=
  if length a = 0 then m321 "array must be non-empty" else do
  let item ← getL a (length a)
  let a ← m1296 a 1
  pure (item, a)

/-- base/array.jl:1836 `popfirst!(a::Vector)`. -/
def m1836 (a : Arr α) : R (α × Arr α) :=
  if length a = 0 then m321 "array must be non-empty" else do
  let item ← getL a 1
  let a ← m1278 a 1
  pure (item, a)

/-- base/array.jl:1741 `popat!(a::Vector, i::Integer)`. -/
def m1741 (a : Arr α) (i : Int) : R (α × Arr α) := do
  let x ← getL a i
  let a ← m1312 a i 1
  pure (x, a)

/-- base/array.jl:1748 `popat!(a::Vector, i::Integer, default)`. -/
def m1748 (a : Arr α) (i : Int) (default : γ) : R (Sum α γ × Arr α) :=
  if 1 ≤ i ∧ i ≤ length a then do
    let x ← getU a i
    let a ← m1312 a i 1
    pure (.inl x, a)
  else .ok (.inr default, a)

/-- base/array.jl:1871 `_insert!(a::Vector{T}, i::Integer, item::T)`. -/
def m1871 (a : Arr α) (i : Int) (item : α) : R (Arr α) := do
  let a ← m1230 a i 1
  pure (setU a i (some item))

/-- base/array.jl:1866 `insert!(a::Vector{T}, i::Integer, item)`: convert first. -/
def m1866 (conv : β → R α) (a : Arr α) (i : Int) (item : β) : R (Arr α) := do
  let item ← conv item
  m1871 a i item

/-- base/array.jl:1899 `deleteat!(a::Vector, i::Integer)` (a `Bool` only adds a deprecation warning). -/
def m1899 (a : Arr α) (i : Int) (_isBool : Bool) : R (Arr α) := m1312 a i 1

/-- base/array.jl:1905 `deleteat!(a::Vector, r::AbstractUnitRange{<:Integer})` for an
`Int` range `lo:hi` (`length(r)` wraps, `base/range.jl:794`); a `Bool` range is
the logical mask `mask` (handled by the `AbstractVector{Bool}` method). -/
def m1905 (maskMethod : Arr α → R (Arr α)) (a : Arr α) (lo hi : Int) (boolRange : Bool) : R (Arr α) :=
  if boolRange then maskMethod a else
  if lo > hi then .ok a else m1312 a lo (wrap64 (1 + (hi - lo)))

/-- base/array.jl:2155 `empty!(a::Vector)`. -/
def m2155 (a : Arr α) : R (Arr α) := m1296 a (length a)

end JuliaLean.MultidimCov.ArrayV2
