import JuliaLean.Reduce.Val

/-!
Whole-collection reductions of a vector of `Val`s (`dims = :`), `base/reduce.jl`,
`base/anyall.jl`, `base/reducedim.jl:333-346`.
-/

namespace JuliaLean.Reduce

open JuliaLean.Float

namespace Vec

/-- `reduce_empty(add_sum, T)`, `base/reduce.jl:342-353`: `Int`/`UInt` zero for small
integer types and `Bool`, `zero(T)` otherwise. -/
def emptyAddSum : Ty → R Val
  | .int t =>
    if Val.smallSigned t then .ok (Val.i64 0)
    else if Val.smallUnsigned t then .ok (.int .u64 (JInt.lit .u64 0))
    else .ok (.int t (JInt.lit t 0))
  | .bool => .ok (Val.i64 0)
  | t => match t.zero with
    | some z => .ok z
    | none => .error .argumentError

/-- `reduce_empty(mul_prod, T)`, `base/reduce.jl:344, 354-356`: `Int`/`UInt` one for small
integer types, `one(T)` otherwise. -/
def emptyMulProd : Ty → R Val
  | .int t =>
    if Val.smallSigned t then .ok (Val.i64 1)
    else if Val.smallUnsigned t then .ok (.int .u64 (JInt.lit .u64 1))
    else .ok (.int t (JInt.lit t 1))
  | t => match t.one with
    | some o => .ok o
    | none => .error .argumentError

/-- `reduce_empty(+, T)`, `base/reduce.jl:342-343`: `zero(T)`, `zero(Int)` for `Bool`. -/
def emptyPlus : Ty → R Val
  | .bool => .ok (Val.i64 0)
  | t => match t.zero with
    | some z => .ok z
    | none => .error .argumentError

/-- `sum(v)` for `v::Vector{T}`: `mapreduce(identity, add_sum, v)` → `_mapreduce`. -/
def sum (eltype : Ty) (v : List Val) : R Val :=
  mapreduceArr id Val.addSum Val.firstAddSum (emptyAddSum eltype) 1024 v

/-- `sum(v; init)`: `_mapreduce_dim(identity, add_sum, init, v, :)`, a left fold. -/
def sumInit (init : Val) (v : List Val) : Val := mapreduceInit id Val.addSum init v

/-- `prod(v)`. -/
def prod (eltype : Ty) (v : List Val) : R Val :=
  mapreduceArr id Val.mulProd Val.firstMulProd (emptyMulProd eltype) 1024 v

/-- `prod(v; init)`. -/
def prodInit (init : Val) (v : List Val) : Val := mapreduceInit id Val.mulProd init v

/-- `maximum(v)`: `mapreduce(identity, max, v)`; `reduce_empty(max, T)` throws. -/
def maximum (v : List Val) : R Val := mapreduceArr id Val.vmax id (.error .argumentError) 1024 v

/-- `minimum(v)`. -/
def minimum (v : List Val) : R Val := mapreduceArr id Val.vmin id (.error .argumentError) 1024 v

/-- `maximum(v; init)`: a left fold of `max` from `init`. -/
def maximumInit (init : Val) (v : List Val) : Val := mapreduceInit id Val.vmax init v

/-- `extrema(v)`: `mapreduce(ExtremaMap(identity), _extrema_rf, v)`,
`base/reduce.jl:806-816`; `reduce_first` of a tuple is the tuple. -/
def extrema (v : List Val) : R (Val × Val) :=
  mapreduceArr (fun x => (x, x)) (fun a b => (Val.vmin a.1 b.1, Val.vmax a.2 b.2))
    (fun x => (x, x)) (.error .argumentError) 1024 v

/-- `maximum(abs, v)`: `mapreduce(abs, max, v)`; `mapreduce_empty(abs, max, T) = abs(zero(T))`
(`base/reduce.jl:374`). -/
def maxAbs (eltype : Ty) (v : List Val) : R Val :=
  mapreduceArr Val.vabs Val.vmax Val.vabs
    (match eltype.zero with | some z => .ok (Val.vabs z) | none => .error .argumentError) 1024 v

/-- `isgreater(x, y)`, `base/operators.jl:295`. -/
def isgreater (x y : Val) : Bool :=
  if x.isunordered || y.isunordered then Val.visless x y else Val.visless y x

/-- `findmax(v)`: `mapfoldl(((k, v),) -> (v, k), _rf_findmax, pairs(v))`,
`base/reduce.jl:851-853, 880-881`; indices are 1-based. -/
def findmax (v : List Val) : R (Val × Nat) :=
  mapfoldlNoInit id (fun (a b : Val × Nat) => if Val.visless a.1 b.1 then b else a) id
    (.error .argumentError) (v.zipIdx 1)

/-- `findmin(v)`: `_rf_findmin` with `isgreater`, `base/reduce.jl:917-919, 946-947`. -/
def findmin (v : List Val) : R (Val × Nat) :=
  mapfoldlNoInit id (fun (a b : Val × Nat) => if isgreater a.1 b.1 then b else a) id
    (.error .argumentError) (v.zipIdx 1)

/-- `any(f, itr)`, `base/anyall.jl:115-130`: short-circuits on the first `true`; a
non-`Bool`, non-`missing` value of `f` throws `TypeError` in `v && return true`. -/
def any (f : Val → Val) : List Val → R Val
  | [] => .ok (.bool false)
  | x :: rest =>
    match f x with
    | .missing => (any f rest).map fun r => if r = .bool false then .missing else r
    | .bool true => .ok (.bool true)
    | .bool false => any f rest
    | _ => .error .typeError

/-- `all(f, itr)`, `base/anyall.jl:202-217`. -/
def all (f : Val → Val) : List Val → R Val
  | [] => .ok (.bool true)
  | x :: rest =>
    match f x with
    | .missing => (all f rest).map fun r => if r = .bool true then .missing else r
    | .bool false => .ok (.bool false)
    | .bool true => all f rest
    | _ => .error .typeError

/-- `count(identity, x::Array{Bool}; init)`: `_simple_count`, `base/reduce.jl:1097-1113`.
`v0 = add_sum(init, false)`, `T = typeof(v0)`; each chunk and each remaining element is
added with `n = (n + c) % T`, which exists only for integer `T` (a `Float64` `init` hits
`rem(::Float64, ::Type{Float64})`, a `MethodError`). The sum of the chunk counts is the
number of `true` elements, so for integer `T` the result is that count added to `v0`
modulo `T`. -/
def countBoolArray (init : Val) (xs : List Bool) : R Val :=
  let v0 := Val.addSum init (.bool false)
  match xs, v0 with
  | [], _ => .ok v0
  | _, .int t n => .ok (.int t (JInt.wrap t (n.val + (xs.filter id).length)))
  | _, _ => .error .methodError

/-- `count(identity, itr; init)` for an iterator that is not an array (e.g. a tuple):
`sum(_bool(identity), itr; init)` → `mapfoldl` from `init` (`base/reduce.jl:1093-1095`). -/
def countIter (init : Val) (xs : List Bool) : Val :=
  mapfoldlInit Val.bool Val.addSum init xs

/-- An element type of the outer iterator, here a vector type. -/
inductive OuterEltype where
  | vector (element : Ty)

/-- `eltype(Vector{T})`, used by `reduce_empty` on `FlatteningRF`. -/
def OuterEltype.eltype : OuterEltype → Ty
  | .vector element => element

/-- `foldl(op, itr)` over `Iterators.flatten(vs)` without `init`: `FlatteningRF(BottomRF(op))`,
`base/reduce.jl:83-84, 118-125, 161-164, 361`. The empty reduction delegates to the
wrapped reducer with `eltype(T)`, where `T` is the outer iterator's element type. -/
def foldlFlatten (op : Val → Val → Val) (first : Val → Val) (empty : Ty → R Val)
    (outerEltype : OuterEltype) (vs : List (List Val)) : R Val :=
  let step : Option Val → Val → Option Val := fun acc x =>
    match acc with
    | none => some (first x)
    | some a => some (op a x)
  match vs.foldl (fun acc v => v.foldl step acc) none with
  | none => empty outerEltype.eltype
  | some r => .ok r

/-- `foldl(op, Iterators.flatten(vs); init)`: the same nested fold started from `init`. -/
def foldlFlattenInit (op : Val → Val → Val) (init : Val) (vs : List (List Val)) : Val :=
  vs.foldl (fun acc v => v.foldl op acc) init

/-- `foldr(op, v)`: `reduce_first(FlipArgs(op), x)` delegates to
`reduce_first(op, x)`; an empty `v` uses `reduce_empty(op, T)`
(`base/reduce.jl:361, 420`). -/
def foldr (op : Val → Val → Val) (first : Val → Val) (empty : R Val) (v : List Val) : R Val :=
  mapfoldrNoInit id op first empty v

/-- `foldl(op, v)` with `reduce_first(op, x)` given as `first`. -/
def foldl (op : Val → Val → Val) (first : Val → Val) (v : List Val) : R Val :=
  mapfoldlNoInit id op first (.error .argumentError) v

end Vec

/-! ### `reduce(vcat, vs)`, `reduce(hcat, vs)` -/

namespace Cat
variable {α : Type}

/-- `reduce(vcat, A::AbstractVector{<:AbstractVector})`, `base/abstractarray.jl:1741-1753,
1827-1828`: `_typed_vcat!` copies each `V[k]` into `a[pos:p1]`; an empty `A` throws from
`mapreduce(eltype, promote_type, A)`. -/
def reduceVcat (vs : List (List α)) : R (List α) :=
  if vs = [] then .error .argumentError
  else .ok (vs.foldl (fun a v => a ++ v) [])

/-- `reduce(hcat, A::AbstractVector{<:AbstractVector})`, `base/abstractarray.jl:1768-1803,
1830-1831`: every column must have `size(A[1], 1)` rows (`DimensionMismatch`); dense
columns are copied in order. Returns `(nrows, ncols, column-major data)`. -/
def reduceHcat (vs : List (List α)) : R (Nat × Nat × List α) :=
  match vs with
  | [] => .error .argumentError
  | v1 :: _ =>
    if vs.all (fun v => v.length = v1.length) then
      .ok (v1.length, vs.length, vs.foldl (fun a v => a ++ v) [])
    else .error .dimensionMismatch

end Cat

end JuliaLean.Reduce
