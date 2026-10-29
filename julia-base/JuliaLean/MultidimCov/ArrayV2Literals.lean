import JuliaLean.MultidimCov.ArrayV2IterProps
import JuliaLean.Promotion.PromoteType

/-!
Array literals, `vect`, `fill`, `zeros`/`ones`, `asize_from`, `_cat` of
integers, `convert` to `Array` and the `Array`/`AbstractArray` copy constructors
(master `base/array.jl:14-229`, `445-461`, `482-665`, `2337-2338`, `2368`).

Numbers are `NV`: a value `v` of a primitive number type `ty` (`Bool`, the ten
`BitInteger`s, the three `IEEEFloat`s); float values are integers, and
`convert(T, x)` (`nconv`) is exact (`InexactError` when the value does not fit an
integer or `Bool` type); float rounding is not modelled.
-/

namespace JuliaLean.MultidimCov.ArrayV2

open JuliaLean (IntTy)
open JuliaLean.Promotion (NumTy promoteType expectedPromotion promoteTypeTable_proven)

/-! ### `DimensionMismatch()` -/

/-- `struct DimensionMismatch <: Exception; msg::AbstractString; end`. -/
structure DimMismatch where
  msg : String
  deriving DecidableEq

/-- base/array.jl:14 `DimensionMismatch() = DimensionMismatch("")`. -/
def m14 : DimMismatch := ⟨""⟩

/-- The optional `msg` of `DimensionMismatch([msg])` (docstring base/array.jl:5-9)
defaults to the empty string. -/
def P14 : Prop := m14 = { msg := "" } ∧ m14.msg.length = 0

theorem p14 : P14 := ⟨rfl, rfl⟩

/-! ### Numbers -/

/-- A number: its type and (integral) value. -/
structure NV where
  ty : NumTy
  v : Int
  deriving DecidableEq

/-- `convert(T, x)` between primitive number types (`InexactError` when `x` does not
fit `Bool` or a `BitInteger` type). Values are integers; a float target is modelled
only for values of magnitude at most `2^11`, which every `IEEEFloat` holds exactly
(larger ones round, or become `Inf` in `Float16`, and are outside the model). -/
def nconv (T : NumTy) (x : NV) : R NV :=
  match T with
  | .bool => if x.v = 0 ∨ x.v = 1 then .ok ⟨.bool, x.v⟩ else .error .inexact
  | .int t => if t.min ≤ x.v ∧ x.v ≤ t.max then .ok ⟨.int t, x.v⟩ else .error .inexact
  | .flt F => .ok ⟨.flt F, x.v⟩

/-- `zero(T)` and `one(T)` (`felt` of the `zeros`/`ones` loop: `one = true` for `ones`). -/
def felt (one : Bool) (T : NumTy) : NV := ⟨T, if one then 1 else 0⟩

/-- `promote_typeof(x, xs...) = promote_type(typeof(x), promote_typeof(xs...))`
(`base/promotion.jl`); `none` would be a non-concrete join, which never occurs for
two primitive number types (`promoteTypeTable_proven`). -/
def promoteTypeof : List NV → Option NumTy
  | [] => none
  | [x] => some x.ty
  | x :: xs => match promoteTypeof xs with
    | some t => promoteType x.ty t
    | none => none

/-- The documented promotion of the argument types (manual promotion table). -/
def promotedTy : NV → List NV → NumTy
  | x, [] => x.ty
  | x, y :: ys => expectedPromotion x.ty (promotedTy y ys)

/-- An `Array` of numbers with its element type. -/
structure TArr where
  ty : NumTy
  a : Arr NV

/-! ### `vect` and typed literals -/

/-- base/array.jl:159 `vect(X::T...)`: `Vector{T}(undef, length(X))`, then
`@_safeindex vec[i] = X[i]` (`__safe_setindex!`, no conversion needed). -/
def m159 (xs : List α) : R (Arr α) := do
  let v ← newArray [xs.length]
  pure (safeWrites v 1 xs)

/-- `for i in 1:length(vals); a[i] = vals[i]; end` through the write `w`. -/
def convWrites (w : Arr α → β → Int → R (Arr α)) (a : Arr α) (i : Int) : List β → R (Arr α)
  | [] => .ok a
  | x :: xs => do
    let a ← w a x i
    convWrites w a (i + 1) xs

/-- base/array.jl:445 `getindex(::Type{T}, vals...)`: `Vector{T}(undef, length(vals))`;
for an `NTuple` (`homog`) `@_safeindex a[i] = vals[i]` (`__safe_setindex!`, converting),
otherwise `afoldl` with `@inbounds a[i] = v` (`setindex!`, converting). -/
def m445 (conv : β → R α) (homog : Bool) (vals : List β) : R (Arr α) := do
  let a ← newArray [vals.length]
  if homog then convWrites (m1059 conv) a 1 vals else convWrites (m1031 conv) a 1 vals

/-- base/array.jl:183 `vect(X...)`: `T = promote_typeof(X...); T[X...]` (one or more arguments). -/
def m183 (xs : List NV) : R TArr :=
  match promoteTypeof xs with
  | none => .error .typeError
  | some T => do
    let a ← m445 (nconv T) (xs.all fun x => x.ty == (xs.headD ⟨T, 0⟩).ty) xs
    pure ⟨T, a⟩

/-- base/array.jl:2337 `vcat() = Vector{Any}()`; an element type `none` is `Any`. -/
def m2337 : R (Option NumTy × Arr NV) := do
  let a ← newArray [0]
  pure (none, a)

/-- base/array.jl:2338 `hcat() = Vector{Any}()`. -/
def m2338 : R (Option NumTy × Arr NV) := do
  let a ← newArray [0]
  pure (none, a)

/-! ### `to_dim`, `fill`, `zeros`, `ones` -/

/-- A `DimOrInd` argument: an integer, `OneTo(n)` (`n ≥ 0`), or another
`AbstractUnitRange` `f:l`. -/
inductive DimArg where
  | int (d : Int)
  | oneTo (n : Int)
  | other (f l : Int)

/-- base/array.jl:482 `to_dim(d::Integer) = d`. -/
def m482 (d : Int) : Int := d

/-- base/array.jl:483 `to_dim(d::OneTo) = last(d)`. -/
def m483 (n : Int) : Int := n

def DimArg.isInt : DimArg → Bool
  | .int _ => true
  | _ => false

def DimArg.isIntOrOneTo : DimArg → Bool
  | .other _ _ => false
  | _ => true

/-- `map(to_dim, dims)` for `Integer`/`OneTo` entries. -/
def DimArg.toDim : DimArg → Int
  | .int d => m482 d
  | .oneTo n => m483 n
  | .other _ l => l

/-- `similar(Array{T,N}, dims::Tuple{Vararg{DimOrInd}})` (base/abstractarray.jl):
`to_shape` keeps a non-`OneTo` range, for which `Array` has no `similar` method. -/
def similarShape (dims : List DimArg) : R (Arr α) :=
  if dims.all DimArg.isIntOrOneTo then newArray (dims.map DimArg.toDim) else .error .method

/-- base/array.jl:585 `fill(v, dims::NTuple{N,Integer})`: `Array{typeof(v),N}(undef, dims); fill!(a, v)`. -/
def m585 (v : α) (dims : List Int) : R (Arr α) := do
  let a ← newArray dims
  m368 (fun x => .ok x) a v

/-- base/array.jl:584 `fill(v, dims::NTuple{N,Union{Integer,OneTo}}) = fill(v, map(to_dim, dims))`. -/
def m584 (v : α) (dims : List DimArg) : R (Arr α) := m585 v (dims.map DimArg.toDim)

/-- base/array.jl:586 `fill(v, dims::NTuple{N,DimOrInd})`: `similar(Array{typeof(v),N}, dims); fill!(a, v)`. -/
def m586 (v : α) (dims : List DimArg) : R (Arr α) := do
  let a ← similarShape dims
  m368 (fun x => .ok x) a v

/-- `fill(v, dims::Tuple)` dispatch (all `Integer`: 585; `Integer`/`OneTo`: 584; else 586). -/
def fillTuple (v : α) (dims : List DimArg) : R (Arr α) :=
  if dims.all DimArg.isInt then m585 v (dims.map DimArg.toDim)
  else if dims.all DimArg.isIntOrOneTo then m584 v dims
  else m586 v dims

/-- base/array.jl:583 `fill(v, dims::DimOrInd...) = fill(v, dims)`. -/
def m583 (v : α) (dims : List DimArg) : R (Arr α) := fillTuple v dims

/-- base/array.jl:637 `$fname(::Type{T}, dims::NTuple{N,Integer})`:
`Array{T,N}(undef, dims); fill!(a, $felt(T))`. -/
def m637 (one : Bool) (T : NumTy) (dims : List Int) : R TArr := do
  let a ← newArray dims
  let a ← m368 (nconv T) a (felt one T)
  pure ⟨T, a⟩

/-- base/array.jl:642 `$fname(::Type{T}, dims::Tuple{})`: `Array{T}(undef); fill!(a, $felt(T))`. -/
def m642 (one : Bool) (T : NumTy) : R TArr := do
  let a ← newArray []
  let a ← m368 (nconv T) a (felt one T)
  pure ⟨T, a⟩

/-- base/array.jl:636 `$fname(::Type{T}, dims::NTuple{N,Union{Integer,OneTo}}) = $fname(T, map(to_dim, dims))`. -/
def m636 (one : Bool) (T : NumTy) (dims : List DimArg) : R TArr := m637 one T (dims.map DimArg.toDim)

/-- base/array.jl:647 `$fname(::Type{T}, dims::NTuple{N,DimOrInd})`:
`similar(Array{T,N}, dims); fill!(a, $felt(T))`. -/
def m647 (one : Bool) (T : NumTy) (dims : List DimArg) : R TArr := do
  let a ← similarShape dims
  let a ← m368 (nconv T) a (felt one T)
  pure ⟨T, a⟩

/-- `$fname(T, dims::Tuple)` dispatch: `()` 642, all `Integer` 637, `Integer`/`OneTo` 636, else 647. -/
def zerosT (one : Bool) (T : NumTy) (dims : List DimArg) : R TArr :=
  if dims = [] then m642 one T
  else if dims.all DimArg.isInt then m637 one T (dims.map DimArg.toDim)
  else if dims.all DimArg.isIntOrOneTo then m636 one T dims
  else m647 one T dims

/-- base/array.jl:634 `$fname(::Type{T}, dims::DimOrInd...) = $fname(T, dims)`. -/
def m634 (one : Bool) (T : NumTy) (dims : List DimArg) : R TArr := zerosT one T dims

/-- base/array.jl:635 `$fname(dims::Tuple{Vararg{DimOrInd}}) = $fname(Float64, dims)`. -/
def m635 (one : Bool) (dims : List DimArg) : R TArr := zerosT one (.flt .f64) dims

/-- base/array.jl:633 `$fname(dims::DimOrInd...) = $fname(dims)`. -/
def m633 (one : Bool) (dims : List DimArg) : R TArr := m635 one dims

/-! ### `asize_from`, `_cat` -/

/-- `size(t::AbstractArray, dim)` (`base/abstractarray.jl:42-46`): `d = Int(dim)`, then `s[d]`
(tuple indexing, `BoundsError` for `d < 1`) when `d <= length(s)`, else `1`. -/
def sizeDim (a : Arr α) (dim : Int) : R Int := do
  let d ← toInt dim
  if d ≤ a.dims.length then
    (if 1 ≤ d then .ok (a.dims.getD (d - 1).toNat 1) else .error .bounds)
  else .ok 1

/-- base/array.jl:188 `asize_from(a::Array, n) = n > ndims(a) ? () : (size(a,n), asize_from(a, n+1)...)`. -/
def m188 (a : Arr α) (n : Int) : R (List Int) :=
  if n > a.dims.length then .ok [] else do
    let s ← sizeDim a n
    let rest ← m188 a (n + 1)
    pure (s :: rest)
termination_by (a.dims.length + 1 - n).toNat

/-- `reshape(a::Array, dims)`: the same data with size `dims`; `DimensionMismatch`
unless `prod(dims) == length(a)`. -/
def reshapeArr (a : Arr α) (dims : List Int) : R (Arr α) :=
  if dims.foldr (· * ·) 1 = length a then .ok { a with dims := dims } else .error .dimensionMismatch

/-- base/array.jl:2368 `_cat(n::Integer, x::Integer...) =
reshape([x...], (ntuple(Returns(1), n-1)..., length(x)))`; `[x...]` is `vect(x...)`
(`Vector{Any}()` for no arguments) and `ntuple` rejects a negative length with `ArgumentError`. -/
def m2368 (n : Int) (xs : List NV) : R (Option NumTy × Arr NV) := do
  let v ← match xs with
    | [] => m2337
    | _ => do let t ← m183 xs; pure (some t.ty, t.a)
  if n - 1 < 0 then .error .argument else do
  let a ← reshapeArr v.2 (List.replicate (n - 1).toNat 1 ++ [(xs.length : Int)])
  pure (v.1, a)

/-! ### `convert` and the copy constructors -/

/-- A source `AbstractArray`: its axes `f:l` (one per dimension) and its elements
in column-major order (`none` for `#undef`). -/
structure SrcArr (β : Type) where
  axs : List (Int × Int)
  elems : List (Option β)

/-- `axd == axs` for `OneTo(n)` against `f:l`: equal ranges (both empty, or `1:n`). -/
def axEq (n : Int) (ax : Int × Int) : Bool :=
  (n == 0 && decide (ax.2 < ax.1)) || (ax.1 == 1 && ax.2 == n)

/-- `size(x)` of a source. -/
def SrcArr.size (x : SrcArr β) : List Int := x.axs.map fun ax => max 0 (ax.2 - ax.1 + 1)

/-- `dest[i] = src[i]`: read the source element (`UndefRefError` when unset), then the
converting `setindex!`. -/
def readWrite (conv : β → R α) (dest : Arr α) (x : Option β) (i : Int) : R (Arr α) :=
  match x with
  | none => .error .undefRef
  | some x => m1031 conv dest x i

/-- `copyto_axcheck!(dest, src)` (base/abstractarray.jl:1184-1189): `_checkaxs`
(`DimensionMismatch` unless the axes agree), then `copyto!(dest, src)`, which
does `dest[i] = src[i]` in linear order. -/
def copytoAxcheck (conv : β → R α) (dest : Arr α) (x : SrcArr β) : R (Arr α) :=
  if (dest.dims.length == x.axs.length) && (List.zip dest.dims x.axs).all (fun p => axEq p.1 p.2) then
    convWrites (readWrite conv) dest 1 x.elems
  else .error .dimensionMismatch

/-- base/array.jl:664 `Array{T,N}(x::AbstractArray{S,N}) = copyto_axcheck!(Array{T,N}(undef, size(x)), x)`. -/
def m664 (conv : β → R α) (x : SrcArr β) : R (Arr α) := do
  let dest ← newArray x.size
  copytoAxcheck conv dest x

/-- base/array.jl:665 `AbstractArray{T,N}(A) = copyto_axcheck!(similar(A, T), A)` for an
`Array` `A` (`similar(A, T)` keeps `size(A)`). -/
def m665 (conv : β → R α) (A : Arr β) : R (Arr α) := do
  let dest ← m419 A A.dims
  copytoAxcheck conv dest ⟨A.dims.map fun d => (1, d), contents A⟩

/-- base/array.jl:657 `convert(::Type{T}, a::AbstractArray) where {T<:Array} = a isa T ? a : T(a)::T`
for numeric arrays: `a isa T` when the element types agree. -/
def m657 (T : NumTy) (x : TArr) : R TArr :=
  if x.ty = T then .ok x else do
  let a ← m664 (nconv T) ⟨x.a.dims.map fun d => (1, d), contents x.a⟩
  pure ⟨T, a⟩

end JuliaLean.MultidimCov.ArrayV2
