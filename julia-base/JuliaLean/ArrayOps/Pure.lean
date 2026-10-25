import JuliaLean.ArrayOps.Vec
import JuliaLean.Float.Basic

/-!
Vector operations that read or rearrange a fully assigned vector, and the 1-D
index machinery (master `bbfa0ce4150`): `reverse!`/`reverse` with a window,
`circshift!`/`circshift`, `repeat`, `fill`, the `Array` method of
`copyto!(dest, doffs, src, soffs, n)`, the generic `findnext`/`findprev`,
`findmax`/`findmin`/`argmax`/`argmin` on `Float64`, `sum`/`prod` of integer
vectors, `accumulate`/`cumsum`, `diff`, `vcat` of unit ranges, scalar indexing
with every `BitInteger` index type, and 1-D `LinearIndices`/`CartesianIndices`.

Vectors are lists (all elements assigned). Positions are 1-based Julia indices.
-/

namespace JuliaLean.ArrayOps

open JuliaLean

section
variable {α : Type}

/-! ### Scalar indexing -/

/-- `getindex(A::Array, i::Int)` (`base/essentials.jl:1063-1067`): bounds check. -/
def getAt (a : List α) (i : JInt64) : Jl α :=
  if h : 1 ≤ i.val ∧ i.val ≤ a.length then
    .ok (a[(i.val - 1).toNat]'(by omega))
  else .error .boundsError

/-- `to_index(A::Array, i)` for a `BitInteger` index, `base/indices.jl:247, 258`:
`UInt` is reinterpreted as `Int`, every other type is converted with
`convert(Int, i)` (`InexactError` when not representable). -/
def toIndexArray {t : IntTy} (i : JInt t) : Jl JInt64 :=
  if t = .u64 then .ok (JInt.wrap .i64 i.val) else toInt i

/-- `to_index(A, i)` for any other array (`base/indices.jl:243, 258`): `convert(Int, i)`. -/
def toIndexGeneric {t : IntTy} (i : JInt t) : Jl JInt64 := toInt i

/-- `v[i]` for a `Vector`: `getindex(A::Array, i1::Integer)` → `to_indices`
(`base/abstractarray.jl:1369`), then the `Int` method. -/
def getindex {t : IntTy} (a : List α) (i : JInt t) : Jl α := do
  getAt a (← toIndexArray i)

/-- `checkbounds(Bool, v, i)` for an integer index: `checkindex(Bool, OneTo(n), i::Real)`
(`base/abstractarray.jl:751`), `(first(inds) <= i) & (i <= last(inds))`, compared
exactly across integer types. -/
def checkboundsInt {t : IntTy} (a : List α) (i : JInt t) : Bool :=
  decide (1 ≤ i.val ∧ i.val ≤ a.length)

/-- `LinearIndices(v)[i]` for a vector, `base/indices.jl:509-513`:
`to_index` (generic, `convert(Int, i)`), bounds check, then `i` itself. -/
def linearGet {t : IntTy} (n : Nat) (i : JInt t) : Jl JInt64 := do
  let i ← toIndexGeneric i
  if 1 ≤ i.val ∧ i.val ≤ n then pure i else throw .boundsError

/-- `CartesianIndices(v)[i]` for a vector (`base/multidimensional.jl`, linear
`getindex` of `CartesianIndices{1}`): `to_index`, bounds check, `CartesianIndex(i)`;
the `CartesianIndex{1}` is represented by its single coordinate. -/
def cartesianGet {t : IntTy} (n : Nat) (i : JInt t) : Jl JInt64 := do
  let i ← toIndexGeneric i
  if 1 ≤ i.val ∧ i.val ≤ n then pure i else throw .boundsError

/-- `LinearIndices(v)[CartesianIndex(i)]` (`base/indices.jl:509` after
`to_indices` splats the `CartesianIndex`): bounds check, then `i`. -/
def linearOfCartesian (n : Nat) (i : JInt64) : Jl JInt64 :=
  if 1 ≤ i.val ∧ i.val ≤ n then pure i else throw .boundsError

/-! ### `reverse!` and `reverse` with a window -/

/-- `midpoint(lo, hi) = lo +% ((hi -% lo) >>> 0x01)`, `base/array.jl:2288`, for `lo ≤ hi`
(the only use, where the result is exact). -/
def midpoint (lo hi : Int) : Int := lo + (hi - lo) / 2

/-- The swap loop `for i in s:midpoint(s, n-1); v[i], v[r] = v[r], v[i]; r -= 1; end`
(`k` iterations left). -/
def swapLoop [Inhabited α] (v : List α) (i r : Int) : Nat → List α
  | 0 => v
  | k + 1 =>
    let vi := v[(i - 1).toNat]!
    let vr := v[(r - 1).toNat]!
    swapLoop ((v.set (i - 1).toNat vr).set (r - 1).toNat vi) (i + 1) (r - 1) k

/-- `reverse!(v, start, stop)`, `base/array.jl:2317-2333`. -/
def reverseBang [Inhabited α] {s t : IntTy} (v : List α) (start : JInt s) (stop : JInt t) :
    Jl (List α) := do
  let s ← toInt start
  let n ← toInt stop
  if n.val > s.val then
    if ¬ (1 ≤ s.val ∧ s.val ≤ v.length) then throw .boundsError
    else if ¬ (1 ≤ n.val ∧ n.val ≤ v.length) then throw .boundsError
    else pure (swapLoop v s.val n.val (midpoint s.val (n.val - 1) - s.val + 1).toNat)
  else pure v

/-- `for i = lo:hi; body(i); end` for `Int` bounds, stopping at the first exception. -/
def forRange {σ : Type} (body : Int → σ → Jl σ) : Int → Nat → σ → Jl σ
  | _, 0, st => .ok st
  | i, k + 1, st => do forRange body (i + 1) k (← body i st)

/-- `B[i] = A[j]` for `B = similar(A)` held as slots: read `A[j]`, then store. -/
def copySlot (A : List α) (i j : Int) (B : Vec α) : Jl (Vec α) := do
  let x ← getAt A (JInt.wrap .i64 j)
  if 1 ≤ i ∧ i ≤ B.length then pure (B.set (i - 1).toNat (some x)) else throw .boundsError

/-- Number of iterations of `lo:hi` for `Int` bounds (`hi` already wrapped). -/
def iterCount (lo hi : Int) : Nat := (hi - lo + 1).toNat

/-- `reverse(A, start, stop)`, `base/array.jl:2253-2266`: three copy loops into
`B = similar(A)`. The bounds `s-1` and `n+1` are computed in `Int`, wrapping. -/
def reverseCopy {s t : IntTy} (A : List α) (start : JInt s) (stop : JInt t) :
    Jl (List (Option α)) := do
  let s ← toInt start
  let n ← toInt stop
  let len : Int := A.length
  let B : Vec α := List.replicate A.length none
  let sm1 := (s - JInt.lit .i64 1).val
  let np1 := (n + JInt.lit .i64 1).val
  let B ← forRange (fun i B => copySlot A i i B) 1 (iterCount 1 sm1) B
  let B ← forRange (fun i B => copySlot A i (n.val + s.val - i) B) s.val (iterCount s.val n.val) B
  forRange (fun i B => copySlot A i i B) np1 (iterCount np1 len) B

/-! ### `circshift!` and `circshift` -/

/-- `mod(shift, n)` for a shift of any integer type and `n::Int > 0`
(`base/int.jl:331-351`: same-type `mod` after promotion, or the mixed
`mod(x::Unsigned, y::Signed)`/`mod(x::BitSigned, y::Unsigned)` methods). For
`n > 0` every one of them returns the floored remainder exactly. -/
def modShift {t : IntTy} (shift : JInt t) (n : Nat) : Int := shift.val % (n : Int)

/-- `circshift!(a::AbstractVector, shift::Integer)`, `base/abstractarray.jl:3756-3766`:
three `reverse!`s. -/
def circshiftBang [Inhabited α] {t : IntTy} (a : List α) (shift : JInt t) : Jl (List α) := do
  let n := a.length
  if n = 0 then return a
  let s := modShift shift n
  if s = 0 then return a
  let l : JInt64 := JInt.wrap .i64 n
  let a ← reverseBang a (JInt.lit .i64 1) (JInt.wrap .i64 (l.val - s))
  let a ← reverseBang a (JInt.wrap .i64 (l.val - s + 1)) l
  reverseBang a (JInt.lit .i64 1) l

/-- `circshift(a, shift)` for a vector, `base/abstractarraymath.jl:335-337` →
`circshift!(dest, src, (shift,))`, `base/multidimensional.jl:1257-1299`:
`s = mod(shift, n)`; `dest[1:s] = src[n-s+1:n]`, `dest[s+1:n] = src[1:n-s]`. -/
def circshift {t : IntTy} (a : List α) (shift : JInt t) : List α :=
  if a.isEmpty then a
  else
    let s := (modShift shift a.length).toNat
    let sl := a.length - s
    a.drop sl ++ a.take sl

/-! ### `repeat` and `fill` -/

/-- `checked_mul` on `Int`, `base/checked.jl`: `OverflowError` outside `Int64`. -/
def checkedMul64 (a b : JInt64) : Jl JInt64 :=
  if IntTy.i64.min ≤ a.val * b.val ∧ a.val * b.val ≤ IntTy.i64.max then
    .ok (JInt.wrap .i64 (a.val * b.val))
  else .error (.overflowError "checked_mul")

/-- `repeat(v::AbstractVector; inner, outer)` with `Int` counts (`none` = `nothing`),
`base/abstractarraymath.jl:482-614`: `check`, then `repeat_inner` (each entry `inner`
times, size `checked_mul(length, inner)`), then `repeat_outer`
(`checked_mul(length, outer)` copies of the whole vector). -/
def repeatVec (v : List α) (inner outer : Option JInt64) : Jl (List α) := do
  if (match inner with | some k => decide (k.val < 0) | none => false) then
    throw (.argumentError "no inner repetition count may be negative")
  if (match outer with | some k => decide (k.val < 0) | none => false) then
    throw (.argumentError "no outer repetition count may be negative")
  let w ← match inner with
    | none => pure v
    | some k => do
      let _ ← checkedMul64 (JInt.wrap .i64 v.length) k
      pure (v.flatMap fun x => List.replicate k.val.toNat x)
  match outer with
  | none => pure w
  | some m => do
    let _ ← checkedMul64 (JInt.wrap .i64 w.length) m
    pure (List.flatten (List.replicate m.val.toNat w))

/-- `fill(x, n)`, `base/array.jl:583-585` → `Array{T}(undef, n)`: `Int(n)`
(`InexactError`), then the allocation rejects a negative length (`ArgumentError`). -/
def fill {t : IntTy} (x : α) (n : JInt t) : Jl (List α) := do
  let n ← toInt n
  if n.val < 0 then throw (.argumentError "invalid GenericMemory size")
  pure (List.replicate n.val.toNat x)

/-! ### `copyto!(dest, doffs, src, soffs, n)` -/

/-- `_copyto_impl!(dest, doffs, src, soffs, n)`, `base/array.jl:299-316`, for
`dest::Array` and `src::Array`; `src = none` stands for `src === dest`. `length(dest) - doffs + 1`
is computed in the promoted type (it cannot wrap once `checkbounds(dest, doffs)`
holds). The copy is a `memmove`: the source block is read before any store. -/
def copyto {s t u : IntTy} (dest : List α) (doffs : JInt s) (src : Option (List α)) (soffs : JInt t)
    (n : JInt u) : Jl (List α) :=
  let srcv := src.getD dest
  if n.val = 0 then .ok dest
  else if ¬ n.val > 0 then .error (.argumentError "Number of elements to copy must be non-negative.")
  else if ¬ (1 ≤ doffs.val ∧ doffs.val ≤ dest.length) then .error .boundsError
  else if ¬ n.val ≤ dest.length - doffs.val + 1 then .error .boundsError
  else if ¬ (1 ≤ soffs.val ∧ soffs.val ≤ srcv.length) then .error .boundsError
  else if ¬ n.val ≤ srcv.length - soffs.val + 1 then .error .boundsError
  else
    let d := (doffs.val - 1).toNat
    let block := (srcv.drop (soffs.val - 1).toNat).take n.val.toNat
    .ok (dest.take d ++ block ++ dest.drop (d + n.val.toNat))

/-! ### `findnext` and `findprev` -/

/-- The loop of `findnext(testf, A, start)` from `i` (`k` iterations bound). -/
def findnextLoop (f : α → Bool) (a : List α) (l : Int) : Int → Nat → Jl (Option JInt64)
  | _, 0 => .ok none
  | i, k + 1 => do
    let x ← getAt a (JInt.wrap .i64 i)
    if f x then return some (JInt.wrap .i64 i)
    if i = l then return none
    findnextLoop f a l (i + 1) k

/-- `findnext(testf::Function, A, start)`, `base/array.jl:2475-2486`, for a vector:
`i = oftype(first(keys(A)), start)`, `l = last(keys(A))`. -/
def findnext {t : IntTy} (f : α → Bool) (a : List α) (start : JInt t) : Jl (Option JInt64) := do
  let i ← toInt start
  let l : Int := a.length
  if i.val > l then return none
  findnextLoop f a l i.val (l - i.val + 1).toNat

/-- The loop of `findprev(testf, A, start)` from `i` down to `f = 1`. -/
def findprevLoop (f : α → Bool) (a : List α) : Int → Nat → Jl (Option JInt64)
  | _, 0 => .ok none
  | i, k + 1 => do
    let x ← getAt a (JInt.wrap .i64 i)
    if f x then return some (JInt.wrap .i64 i)
    if i = 1 then return none
    findprevLoop f a (i - 1) k

/-- `findprev(testf::Function, A, start)`, `base/array.jl:2671-2682`, for a vector. -/
def findprev {t : IntTy} (f : α → Bool) (a : List α) (start : JInt t) : Jl (Option JInt64) := do
  let i ← toInt start
  if i.val < 1 then return none
  findprevLoop f a i.val i.val.toNat

end

/-! ### `findmax`, `findmin`, `argmax`, `argmin` on `Float64` -/

open JuliaLean.Float

/-- `isgreater(x, y)`, `base/operators.jl:295`, with `isunordered = isnan` for floats. -/
def isgreater (x y : F64) : Bool :=
  if F64.isnan x || F64.isnan y then F64.isless x y else F64.isless y x

/-- `mapfoldl` of `_rf_findmax`/`_rf_findmin` over `pairs(v)`, `base/reduce.jl:852-853,
918-919`: the accumulator `(fm, im)` is replaced by `(fx, ix)` when `better fm fx`. -/
def findFold (better : F64 → F64 → Bool) (acc : F64 × Nat) : List F64 → Nat → F64 × Nat
  | [], _ => acc
  | x :: rest, i => findFold better (if better acc.1 x then (x, i) else acc) rest (i + 1)

/-- `findmax(v)`, `base/reduce.jl:880-881, 851-853`: empty collections throw. -/
def findmax (v : List F64) : Jl (F64 × Nat) :=
  match v with
  | [] => .error (.argumentError "reducing over an empty collection is not allowed")
  | x :: rest => .ok (findFold F64.isless (x, 1) rest 2)

/-- `findmin(v)`, `base/reduce.jl:946-947, 917-919`. -/
def findmin (v : List F64) : Jl (F64 × Nat) :=
  match v with
  | [] => .error (.argumentError "reducing over an empty collection is not allowed")
  | x :: rest => .ok (findFold isgreater (x, 1) rest 2)

/-! ### `sum`, `prod` of integer vectors -/

/-- Result type of `add_sum`/`mul_prod` on `T` (`base/reduce.jl:16-30, 351-356, 413-418`):
`Int` for signed types narrower than `Int`, `UInt` for narrower unsigned types. -/
def sumTy : IntTy → IntTy
  | .i8 | .i16 | .i32 => .i64
  | .u8 | .u16 | .u32 => .u64
  | t => t

/-- `mapreduce_impl(f, op, A, ifirst, ilast, blksize)`, `base/reduce.jl:252-273`,
over the widened values (`f` composed with `reduce_first`'s widening); `op` wraps in
the widened type. Indices are 0-based positions into `xs`; Julia calls it with
`ifirst ≤ ilast`, so the first test `ifirst == ilast` is written `ilast ≤ ifirst`. -/
def mapreduceImpl {t : IntTy} (op : JInt t → JInt t → JInt t) (xs : List (JInt t))
    (blksize : Nat) (ifirst ilast : Nat) : JInt t :=
  let z : JInt t := JInt.lit t 0
  if ilast ≤ ifirst then xs.getD ifirst z
  else if ilast - ifirst < blksize then
    ((List.range (ilast + 1 - (ifirst + 2))).map (· + (ifirst + 2))).foldl
      (fun v i => op v (xs.getD i z)) (op (xs.getD ifirst z) (xs.getD (ifirst + 1) z))
  else
    let imid := ifirst + (ilast - ifirst) / 2
    op (mapreduceImpl op xs blksize ifirst imid) (mapreduceImpl op xs blksize (imid + 1) ilast)
termination_by ilast - ifirst
decreasing_by all_goals omega

/-- `_mapreduce(f, op, IndexLinear(), A)`, `base/reduce.jl:436-457`, with
`pairwise_blocksize = 1024` (`base/reduce.jl:311`); `empty` is `reduce_empty`. -/
def mapreduceLinear {t : IntTy} (op : JInt t → JInt t → JInt t) (empty : JInt t)
    (xs : List (JInt t)) : JInt t :=
  let n := xs.length
  let z : JInt t := JInt.lit t 0
  if n = 0 then empty
  else if n = 1 then xs.getD 0 z
  else if n < 16 then (xs.drop 2).foldl op (op (xs.getD 0 z) (xs.getD 1 z))
  else mapreduceImpl op xs 1024 0 (n - 1)

/-- Widening of `reduce_first(add_sum, x)`/`add_sum(x, y)` for small types. -/
def widen {t : IntTy} (x : JInt t) : JInt (sumTy t) := JInt.wrap _ x.val

/-- `sum(v)` for `v::Vector{T}`, `T` a `BitInteger`: `mapreduce(identity, add_sum, v)`. -/
def sum {t : IntTy} (v : List (JInt t)) : JInt (sumTy t) :=
  mapreduceLinear (· + ·) (JInt.lit _ 0) (v.map widen)

/-- `prod(v)`: `mapreduce(identity, mul_prod, v)`. -/
def prod {t : IntTy} (v : List (JInt t)) : JInt (sumTy t) :=
  mapreduceLinear (· * ·) (JInt.lit _ 1) (v.map widen)

/-! ### `accumulate`, `cumsum`, `diff` -/

section
variable {α β : Type}

/-- `_accumulate1!` loop, `base/accumulate.jl:436-453`: `cur_val = op(cur_val, A[i])`. -/
def accumulateLoop (op : β → α → β) (cur : β) : List α → List β
  | [] => []
  | x :: rest => let c := op cur x; c :: accumulateLoop op c rest

/-- `accumulate(op, v; init)` for a vector, `base/accumulate.jl:281-293, 368-372`:
`v1 = op(init, first(A))`, then the loop. Without `init` (`base/accumulate.jl:362-366`)
`v1 = reduce_first(op, first(A))`, given here as `first`. -/
def accumulate (op : β → α → β) (init : Option β) (first : α → β) (v : List α) : List β :=
  match v with
  | [] => []
  | x :: rest =>
    let v1 := match init with | some i => op i x | none => first x
    v1 :: accumulateLoop op v1 rest

/-- `cumsum(v::AbstractVector{T})` for a `BitInteger` `T`, `base/accumulate.jl:116-149, 64-66`:
`accumulate!(add_sum, out, v)` into `Vector{sumTy T}`. -/
def cumsum {t : IntTy} (v : List (JInt t)) : List (JInt (sumTy t)) :=
  accumulate (fun c x => c + widen x) none widen v

/-- `diff(a::AbstractVector)`, `base/multidimensional.jl:1081, 1113-1121` (`diff(a; dims=1)`:
`view(a, 2:n) .- view(a, 1:n-1)`), elementwise wrapping subtraction in `T`. -/
def diff {t : IntTy} (v : List (JInt t)) : List (JInt t) :=
  List.zipWith (fun x y => x - y) v.tail v

end

/-! ### `vcat` of unit ranges -/

/-- The elements of `lo:hi` (`UnitRange{Int}`, `hi ≥ lo - 1`). -/
def unitElems (lo hi : JInt64) : List JInt64 :=
  (List.range (hi.val - lo.val + 1).toNat).map fun (k : Nat) => JInt.wrap .i64 (lo.val + (k : Int))

/-- `checked_add` on `Int`. -/
def checkedAdd64 (a b : JInt64) : Jl JInt64 :=
  if IntTy.i64.min ≤ a.val + b.val ∧ a.val + b.val ≤ IntTy.i64.max then
    .ok (JInt.wrap .i64 (a.val + b.val))
  else .error (.overflowError "checked_add")

/-- `vcat(rs::AbstractRange{T}...)` for unit ranges of `Int`, `base/range.jl:1405-1417`:
`n = checked_add(n, length(ra))` over the ranges (`length` wraps, `base/range.jl:794-804`),
then every element is stored. Elements are only stored while `i ≤ n`; the model reports
`BoundsError` if an element would land past `n` (Julia stores it with `@inbounds`). -/
def vcatRanges (rs : List (JInt64 × JInt64)) : Jl (List JInt64) := do
  let n ← rs.foldlM (fun n r => checkedAdd64 n (JInt.wrap .i64 (r.2.val - r.1.val + 1)))
    (JInt.lit .i64 0)
  let elems := rs.flatMap fun r => unitElems r.1 r.2
  if elems.length ≤ n.val then pure elems else throw .boundsError

end JuliaLean.ArrayOps
