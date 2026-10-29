import JuliaLean.Reduce.Val

/-!
Reductions and accumulations over a dimension of a matrix, `base/reducedim.jl` and
`base/accumulate.jl`.

A matrix is `Mat α`: `m` rows, `n` columns, entries in column-major order
(`data.length = m * n`), entry `(i, j)` (0-based) at position `i + m * j`. A
vector is the `m × 1` case where Julia's code is the same. `dims = d` is a
single positive integer; `d ≥ 3` reduces over a trailing singleton dimension.
Result arrays are `Arr`: an element type, a shape and column-major entries.
Every `setindex!` into a result converts to its element type (`Ty.convert`).
-/

open JuliaLean.Float
namespace JuliaLean.Reduce

/-- A column-major `m × n` matrix. -/
structure Mat (α : Type) where
  m : Nat
  n : Nat
  data : List α
  deriving DecidableEq

/-- A result array: element type, shape, column-major entries. -/
structure Arr where
  ty : Ty
  m : Nat
  n : Nat
  data : List Val
  deriving DecidableEq

namespace Mat
variable {α : Type}

/-- Column `j` (0-based). -/
def col (A : Mat α) (j : Nat) : List α := (A.data.drop (A.m * j)).take A.m

/-- Row `i` (0-based). -/
def row [Inhabited α] (A : Mat α) (i : Nat) : List α :=
  (List.range A.n).map fun j => A.data.getD (i + A.m * j) default

/-- Well-formed: `length(data) == m * n`. -/
def WF (A : Mat α) : Prop := A.data.length = A.m * A.n

end Mat

/-- `size(reduced_indices(A, d))`, `base/reducedim.jl:20-23`: dimension `d` becomes 1. -/
def reducedShape (m n d : Nat) : Nat × Nat :=
  if d = 1 then (1, n) else if d = 2 then (m, 1) else (m, n)

/-- `size(reduced_indices0(A, d))`, `base/reducedim.jl:25-28`: dimension `d` becomes 1
unless it is empty. -/
def reducedShape0 (m n d : Nat) : Nat × Nat :=
  if d = 1 then (if m = 0 then 0 else 1, n) else if d = 2 then (m, if n = 0 then 0 else 1)
  else (m, n)

/-- `check_reducedims(R, A)`, `base/reducedim.jl:205-234`, for `R` of `reducedShape m n d`:
the length of the leading reduced block, or 0 when a non-reduced dimension precedes a
reduced one. -/
def lsiz (m n d : Nat) : Nat :=
  if d = 1 then (if m > 1 then m else 1)
  else if d = 2 then (if m = 1 then (if n > 1 then n else 1) else if n > 1 then 0 else 1)
  else 1

/-- `reducedim_initarray(A, region, init, R)`, `base/reducedim.jl:52-53`: `fill!` of an
array of element type `ty` and the reduced shape; `fill!` converts `init` once. -/
def initArray (ty : Ty) (m n d : Nat) (init : Val) : R Arr := do
  let v ← ty.convert init
  let (rm, rn) := reducedShape m n d
  pure { ty, m := rm, n := rn, data := List.replicate (rm * rn) v }

/-- `R[k] = v` (linear index `k`, 0-based), converting to the element type. -/
def Arr.store (Rr : Arr) (k : Nat) (v : Val) : R Arr := do
  let w ← Rr.ty.convert v
  pure { Rr with data := Rr.data.set k w }

/-- `R[k]`. -/
def Arr.get (Rr : Arr) (k : Nat) : Val := Rr.data.getD k .missing

/-- Lift of a throwing `op` to thrown-or-returned arguments, evaluating left first. -/
def liftOp (op : Val → Val → R Val) (a b : R Val) : R Val := do
  let x ← a
  let y ← b
  op x y

/-- `_mapreducedim!(f, op, R, A)`, `base/reducedim.jl:256-293`. `blk` is
`pairwise_blocksize(f, op)`. -/
def mapreducedim (f : Val → R Val) (op : Val → Val → R Val) (blk : Nat) (Rr : Arr)
    (A : Mat Val) (d : Nat) : R Arr :=
  if A.m * A.n = 0 then .ok Rr
  else
    let ls := lsiz A.m A.n d
    if ls > 16 then
      (List.range Rr.data.length).foldlM (fun Rr k => do
        let blockv ← match A.data.drop (k * ls) with
          | [] => f .missing
          | a :: rest => mrImpl f (liftOp op) f blk a (rest.take (ls - 1))
        let r ← op (Rr.get k) blockv
        Rr.store k r) Rr
    else if Rr.m = 1 then
      (List.range A.n).foldlM (fun Rr j => do
        let jr := if Rr.n = 1 then 0 else j
        let r ← (A.col j).foldlM (fun r a => do op r (← f a)) (Rr.get jr)
        Rr.store jr r) Rr
    else
      (List.range A.n).foldlM (fun Rr j => do
        let jr := if Rr.n = 1 then 0 else j
        (List.range A.m).foldlM (fun Rr i => do
          let k := i + Rr.m * jr
          let a := A.data.getD (i + A.m * j) .missing
          let v ← op (Rr.get k) (← f a)
          Rr.store k v) Rr) Rr

/-- `view(A, ri...)` for the reduced indices `ri`, `base/reducedim.jl:98`: the first row
(`d = 1`), the first column (`d = 2`), or the whole array. -/
def firstSlice (A : Mat Val) (d : Nat) : List Val :=
  if d = 1 then (if A.m = 0 then [] else A.row 0)
  else if d = 2 then (if A.n = 0 then [] else A.col 0)
  else A.data

/-- `mapreduce(f, op, A1)` on the view `A1`, which has `IndexCartesian` and so is a
`mapfoldl` (`base/reduce.jl:461`), with `reduce_first(op, x) = x` for `max`/`min`. -/
def foldView (f : Val → R Val) (op : Val → Val → Val) : List Val → R Val
  | [] => .error .argumentError
  | a :: rest => do
    let v ← f a
    rest.foldlM (fun v x => do pure (op v (← f x))) v

/-- `reducedim_init(f, op::typeof(min|max), A, region)`, `base/reducedim.jl:88-129`.
`isMax` selects `max` (`f2 = min`, `initval = -Inf`, `typemin`); `eltype` is
`eltype(A)` and `realty` is `_realtype(f, promote_union(eltype(A)))`. An empty first slice
returns `map(f, A1)`, an empty array whose inferred element type is recorded as `eltype`
(Julia infers `Real` for `Union{Int, Float64}`, which `Ty` does not represent). -/
def initMinMax (f : Val → R Val) (isMax : Bool) (eltype realty : Ty) (A : Mat Val) (d : Nat) :
    R Arr := do
  let (rm, rn) := reducedShape A.m A.n d
  if (d = 1 ∧ A.m = 0) ∨ (d = 2 ∧ A.n = 0) then .error .argumentError
  else
    let A1 := firstSlice A d
    if A1 = [] then pure { ty := eltype, m := rm, n := rn, data := [] }
    else
      let f2 := if isMax then Val.vmin else Val.vmax
      let v0 ← foldView f f2 A1
      let tr := if realty.isa v0 then realty else v0.typeOf
      let v0 ← if v0.isnan then
          pure (Val.f64 (F64.inf isMax))
        else if v0.isunordered then
          let tnm := tr.nonmissing
          if tnm.bitIntFloat then (if isMax then tnm.typemin else tnm.typemax)
          else if !(A1.all Val.isunordered) then foldView f f2 (A1.filter fun x => !x.isunordered)
          else pure v0
        else pure v0
      let tr := if realty.isa v0 then realty else v0.typeOf
      initArray tr A.m A.n d v0

/-- `zero(x)` of a value. -/
def zeroOf : Val → Val
  | .int t _ => .int t (JInt.lit t 0)
  | .f64 _ => .f64 F64.zero
  | .bool _ => .bool false
  | .missing => .missing

/-- `one(x)` of a value. -/
def oneOf : Val → Val
  | .int t _ => .int t (JInt.lit t 1)
  | .f64 _ => .f64 F64.one
  | .bool _ => .bool true
  | .missing => .missing

/-- `reducedim_init(f, op::Union{typeof(+), typeof(add_sum)}, A, region)` and the `*`/
`mul_prod` analogue, `base/reducedim.jl:68-85, 184-198`. For an array with a concrete
`BitInteger` or `Float64` element type `T` the specialised method computes
`z = fv(f(fv(T)))` and fills with `op(z, z)` of its own type; otherwise
`_reducedim_init` uses `T = promote_union(eltype(A))`, `x = f(zero(T))`,
`z = op(fv(x), fv(x))` and the element type `z isa T ? T : typeof(z)`. `fv` is `zero`
(sum) or `one` (prod) of a value. The branch for element types without `zero(T)`
(`z = fv(fop(f, A))`) is not modelled and returns `methodError`. -/
def initSumProd (f : Val → R Val) (op : Val → Val → Val) (fv : Val → Val) (eltype : Ty)
    (A : Mat Val) (d : Nat) : R Arr :=
  match eltype with
  | .int _ | .f64 =>
    match Ty.zero eltype with
    | some z0 => do
      let x ← f (fv z0)
      let z := fv x
      let v := op z z
      initArray v.typeOf A.m A.n d v
    | none => .error .methodError
  | _ =>
    let T := eltype.promoteUnion
    match T.zero with
    | some z0 => do
      let x ← f z0
      let z := op (fv x) (fv x)
      let tr := if T.isa z then T else z.typeOf
      initArray tr A.m A.n d z
    | none => .error .methodError

/-- `sum(f, A; dims = d)`: `mapreduce(f, add_sum, A; dims)` with `reducedim_init`,
`base/reducedim.jl:351-352, 1024-1025`. -/
def sumDims (f : Val → R Val) (eltype : Ty) (A : Mat Val) (d : Nat) : R Arr := do
  let Rr ← initSumProd f Val.addSum zeroOf eltype A d
  mapreducedim f (fun x y => .ok (Val.addSum x y)) 1024 Rr A d

/-- `prod(f, A; dims = d)`. -/
def prodDims (f : Val → R Val) (eltype : Ty) (A : Mat Val) (d : Nat) : R Arr := do
  let Rr ← initSumProd f Val.mulProd oneOf eltype A d
  mapreducedim f (fun x y => .ok (Val.mulProd x y)) 1024 Rr A d

/-- `mapreduce(f, op, A; dims = d, init)`, `base/reducedim.jl:348-349`: the result array
has element type `typeof(init)`. -/
def mapreduceDimsInit (f : Val → R Val) (op : Val → Val → R Val) (blk : Nat) (init : Val)
    (A : Mat Val) (d : Nat) : R Arr := do
  let Rr ← initArray init.typeOf A.m A.n d init
  mapreducedim f op blk Rr A d

/-- `maximum(f, A; dims = d)` (`isMax`) or `minimum(f, A; dims = d)`. -/
def maxminDims (f : Val → R Val) (isMax : Bool) (eltype : Ty) (A : Mat Val) (d : Nat) :
    R Arr := do
  let Rr ← initMinMax f isMax eltype eltype.promoteUnion A d
  let op := if isMax then Val.vmax else Val.vmin
  mapreducedim f (fun x y => .ok (op x y)) 1024 Rr A d

/-- `maximum(abs, A; dims = d)`: `reducedim_init(f::Union{typeof(abs),typeof(abs2)},
op::typeof(max), A::AbstractArray{T}, region)`, `base/reducedim.jl:172-173`, fills with
`zero(f(zero(T)))` of element type `_realtype(f, T) = T` for real `T`. -/
def maxAbsDims (eltype : Ty) (A : Mat Val) (d : Nat) : R Arr := do
  let z ← match eltype.zero with
    | some z0 => pure (zeroOf (Val.vabs z0))
    | none => .error .methodError
  let Rr ← initArray eltype A.m A.n d z
  mapreducedim (fun x => .ok (Val.vabs x)) (fun x y => .ok (Val.vmax x y)) 1024 Rr A d

/-- `_bool(f)`, `base/reduce.jl:1064`: `f(x)::Bool`. -/
def boolf (f : Val → Val) (x : Val) : R Val :=
  match f x with
  | .bool b => .ok (.bool b)
  | _ => .error .typeError

/-- `any(f, A; dims = d)`: `mapreduce(f, or_any, A; dims)` with `reducedim_init` filling
`false` into a `Bool` array, `base/reducedim.jl:176, 1008, 1025`. -/
def anyDims (f : Val → Val) (A : Mat Val) (d : Nat) : R Arr := do
  let Rr ← initArray .bool A.m A.n d (.bool false)
  mapreducedim (fun x => .ok (f x)) Val.orAny 1024 Rr A d

/-- `all(f, A; dims = d)`, with `and_all` and `true`. -/
def allDims (f : Val → Val) (A : Mat Val) (d : Nat) : R Arr := do
  let Rr ← initArray .bool A.m A.n d (.bool true)
  mapreducedim (fun x => .ok (f x)) Val.andAll 1024 Rr A d

/-- `count(f, A; dims = d, init)`, `base/reducedim.jl:426-429`:
`mapreduce(_bool(f), add_sum, A; dims, init)`. -/
def countDims (f : Val → Val) (init : Val) (A : Mat Val) (d : Nat) : R Arr :=
  mapreduceDimsInit (boolf f) (fun x y => .ok (Val.addSum x y)) 1024 init A d

/-! ### `findmax`, `findmin` with `dims` -/

/-- A `findmax` result: the value array and the `CartesianIndex` array (1-based
`(row, column)`, `(0, 0)` for `zero(CartesianIndex{2})`). -/
structure FindRes where
  vals : Arr
  idx : List (Nat × Nat)
  deriving DecidableEq

/-- `findminmax!(f, op, Rval, Rind, A)`, `base/reducedim.jl:1032-1080`; `op` is `isless`
(findmax) or `isgreater` (findmin). -/
def findminmax (f : Val → Val) (op : Val → Val → Bool) (Rv : Arr) (Ri : List (Nat × Nat))
    (A : Mat Val) : R FindRes :=
  if Rv.data.length = 0 ∨ A.m * A.n = 0 then .ok ⟨Rv, Ri⟩
  else if Rv.m = 1 then
    (List.range A.n).foldlM (fun (st : FindRes) j => do
      let jr := if st.vals.n = 1 then 0 else j
      let (tv, ti) := (List.range A.m).foldl (fun (acc : Val × (Nat × Nat)) i =>
          let av := f (A.data.getD (i + A.m * j) .missing)
          if acc.2 = (0, 0) ∨ op acc.1 av then (av, (i + 1, j + 1)) else acc)
        (st.vals.get jr, st.idx.getD jr (0, 0))
      let vals ← st.vals.store jr tv
      pure ⟨vals, st.idx.set jr ti⟩) ⟨Rv, Ri⟩
  else
    (List.range A.n).foldlM (fun (st : FindRes) j => do
      let jr := if st.vals.n = 1 then 0 else j
      (List.range A.m).foldlM (fun (st : FindRes) i => do
        let k := i + st.vals.m * jr
        let av := f (A.data.getD (i + A.m * j) .missing)
        if st.idx.getD k (0, 0) = (0, 0) ∨ op (st.vals.get k) av then
          let vals ← st.vals.store k av
          pure ⟨vals, st.idx.set k (i + 1, j + 1)⟩
        else pure st) st) ⟨Rv, Ri⟩

/-- `_findminmax_inittype(f, A)`, `base/reducedim.jl:1228-1236`. -/
def findInitType (eltype : Ty) (v0 : Val) : Ty :=
  let T := eltype.promoteUnion
  if T.isa v0 then T
  else if Ty.isa .missing eltype then .union v0.typeOf .missing else v0.typeOf

/-- `_findmax(f, A, region)` (`isMax`, op `isless`) and `_findmin` (op `isgreater`),
`base/reducedim.jl:1141-1153, 1214-1226`. -/
def findDims (f : Val → Val) (isMax : Bool) (eltype : Ty) (A : Mat Val) (d : Nat) :
    R FindRes :=
  let (r0m, r0n) := reducedShape0 A.m A.n d
  if A.m * A.n = 0 then
    let (rm, rn) := reducedShape A.m A.n d
    if rm * rn ≠ 0 then .error .argumentError
    else .ok ⟨{ ty := eltype, m := r0m, n := r0n, data := [] }, []⟩
  else do
    let fA := f (A.data.getD 0 .missing)
    let Rv ← initArrayShape (findInitType eltype fA) r0m r0n fA
    let op : Val → Val → Bool := if isMax then Val.visless
      else fun x y => if x.isunordered || y.isunordered then Val.visless x y else Val.visless y x
    findminmax f op Rv (List.replicate (r0m * r0n) (0, 0)) A
where
  /-- `fill!(similar(A, T, ri), v)`. -/
  initArrayShape (ty : Ty) (rm rn : Nat) (v : Val) : R Arr := do
    let w ← ty.convert v
    pure { ty, m := rm, n := rn, data := List.replicate (rm * rn) w }

/-! ### `accumulate` with `dims` -/

section
variable {α β : Type}

/-- `_accumulate!(op, B, A, dims::Integer, init)` for a matrix, `base/accumulate.jl:374-434`:
`dims ≤ 0` throws, `dims > 2` treats each element as a singleton scan,
`dims = 1` scans each column, `dims = 2` scans each row (`_accumulaten!`). Entries are
returned in column-major order. -/
def accumulateDims [Inhabited α] [Inhabited β] (op : β → α → β) (first : α → β)
    (_copy : α → β) (init : Option β) (A : Mat α) (d : Int) : R (Mat β) :=
  if d ≤ 0 then .error .argumentError
  else if d > 2 then .ok ⟨A.m, A.n, A.data.map (fun x => match init with | none => first x | some i => op i x)⟩
  else if (d = 1 ∧ A.m = 0) ∨ (d = 2 ∧ A.n = 0) then .ok ⟨A.m, A.n, []⟩
  else if d = 1 then
    .ok ⟨A.m, A.n, ((List.range A.n).map fun j => accumulateVec op first init (A.col j)).flatten⟩
  else
    let rows := (List.range A.m).map fun i => accumulateVec op first init (A.row i)
    .ok ⟨A.m, A.n, ((List.range A.n).map fun j => rows.map fun r => r.getD j default).flatten⟩

/-- `accumulate(op, v; dims = d, init)` for a vector: `_accumulate!` with an integer `dims`
(`base/accumulate.jl:374-402`); the `dims == 1` branch is the column scan. -/
def accumulateVecDims (op : β → α → β) (first : α → β) (_copy : α → β) (init : Option β)
    (v : List α) (d : Int) : R (List β) :=
  if d ≤ 0 then .error .argumentError
  else if d > 1 then .ok (v.map (fun x => match init with | none => first x | some i => op i x))
  else .ok (accumulateVec op first init v)

/-- `cumsum(v::AbstractVector; dims)` for an integer vector: `cumsum!(out, v; dims)` →
`_cumsum!(out, v, dims, ArithmeticWraps())`, `base/accumulate.jl:54-67, 116-119`:
`dims == 1 ? accumulate!(add_sum, out, v) : copyto!(out, v)`. -/
def cumsumVecDims (first : α → β) (op : β → α → β) (copy : α → β) (v : List α) (d : Int) :
    R (List β) :=
  if d = 1 then .ok (accumulateVec op first none v) else .ok (v.map copy)

end

end JuliaLean.Reduce
