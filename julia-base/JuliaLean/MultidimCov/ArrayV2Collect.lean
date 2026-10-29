import JuliaLean.MultidimCov.ArrayV2Push
import JuliaLean.MultidimCov.ArrayV2Literals

/-!
`collect` and comprehensions, `hcat`/`vcat` of vectors (master `base/array.jl:684-949`,
`2340-2366`).

Element types matter here, so values carry their Julia type. The universe is
`Int`, `Float64`, `String`, `Union{Int,Float64}`, `Real` and `Any`, with the
subtype relation, `typejoin` (`base/promotion.jl:18-110`; `promote_typejoin` equals
`typejoin` without `Nothing`/`Missing`), `promote_typejoin_union`
(`Union{Int,Float64}` becomes `Real`), `promote_type` (`Int` and `Float64` promote to
`Float64`, every other pair to its `typejoin`) and `convert` (`Int` and `Float64` convert
into each other for the integral values used here; a `String` does not convert to a
number nor back, `MethodError`).

An iterator is its elements in iteration order, its `IteratorSize` and
`IteratorEltype`, the bound `Base._return_type(_iterator_upper_bound, …)` that
inference computes for its elements, and, for a `Generator` whose function is a
type `F`, that `F`.
-/

namespace JuliaLean.MultidimCov.ArrayV2

inductive VT where
  | int
  | f64
  | str
  | intOrF64
  | real
  | any
  deriving DecidableEq, Repr

inductive JV where
  | int (n : Int)
  | f64 (n : Int)
  | str (s : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- `typeof(x)`. -/
def typeofV : JV → VT
  | .int _ => .int
  | .f64 _ => .f64
  | .str _ => .str

/-- `a <: b`. -/
def subT (a b : VT) : Bool :=
  a == b || b == .any || (b == .real && (a == .int || a == .f64 || a == .intOrF64)) ||
    (b == .intOrF64 && (a == .int || a == .f64))

/-- `x isa T`. -/
def isaV (x : JV) (T : VT) : Bool := subT (typeofV x) T

/-- `typejoin(a, b)` (`a <: b && return b`, `b <: a && return a`, then the nearest common
supertype). -/
def typejoinT (a b : VT) : VT :=
  if subT a b then b else if subT b a then a else if subT a .real && subT b .real then .real else .any

/-- `promote_typejoin_union(T)` (`base/promotion.jl`). -/
def ptjUnion : VT → VT
  | .intOrF64 => .real
  | t => t

/-- `isconcretetype(T)`. -/
def isConcreteT : VT → Bool
  | .int => true
  | .f64 => true
  | .str => true
  | _ => false

/-- `promote_type(a, b)`. -/
def promoteT (a b : VT) : VT :=
  if a = b then a else if (a = .int ∧ b = .f64) ∨ (a = .f64 ∧ b = .int) then .f64 else typejoinT a b

/-- `convert(T, x)`. -/
def convertV (T : VT) (x : JV) : R JV :=
  if isaV x T then .ok x else
  match T, x with
  | .f64, .int n => .ok (.f64 n)
  | .int, .f64 n => .ok (.int n)
  | _, _ => .error .method

/-- An `Array{T}` value: its element type and its storage. -/
structure TA where
  et : VT
  a : Arr JV

inductive ISize where
  | unknown
  | len (n : Int)
  | shape (dims : List Int)

structure Iter where
  xs : List JV
  size : ISize
  eltype : Option VT
  inferred : VT
  fType : Option VT

/-- The result of `_similar_shape(itr, isz)`: `nothing`, `length(itr)` or `axes(itr)`. -/
inductive Shp where
  | none
  | len (n : Int)
  | axes (dims : List Int)

/-! ### Allocation -/

/-- base/array.jl:699-701 `_similar_shape(itr, ::SizeUnknown/HasLength/HasShape)`. -/
def m700 (it : Iter) : Shp :=
  match it.size with
  | .unknown => .none
  | .len n => .len n
  | .shape d => .axes d

/-- base/array.jl:711 `_array_for_inner(T, ::SizeUnknown, ::Nothing) = Vector{T}(undef, 0)`. -/
def m711 (T : VT) : R TA := do
  let a ← newArray [0]
  pure ⟨T, a⟩

/-- base/array.jl:712 `_array_for_inner(T, ::HasLength, len) = Vector{T}(undef, Int(len))`. -/
def m712 (T : VT) (len : Int) : R TA := do
  let n ← toInt len
  let a ← newArray [n]
  pure ⟨T, a⟩

/-- base/array.jl:713 `_array_for_inner(T, ::HasShape{N}, axs) = similar(Array{T,N}, axs)`
(for `OneTo` axes, `Array{T,N}(undef, length.(axs))`). -/
def m713 (T : VT) (dims : List Int) : R TA := do
  let a ← newArray dims
  pure ⟨T, a⟩

def arrayForInner (T : VT) : Shp → R TA
  | .none => m711 T
  | .len n => m712 T n
  | .axes d => m713 T d

/-- base/array.jl:716 `_array_for(T, itr, isz) = _array_for_inner(T, isz, _similar_shape(itr, isz))`. -/
def m716 (T : VT) (it : Iter) : R TA := arrayForInner T (m700 it)

/-- base/array.jl:703 `_similar_for(c::AbstractArray, T, itr, ::SizeUnknown, ::Nothing) = similar(c, T, 0)`. -/
def m703 (T : VT) : R TA := do
  let a ← newArray [0]
  pure ⟨T, a⟩

/-- base/array.jl:705 `_similar_for(c::AbstractArray, T, itr, ::HasLength, len) = similar(c, T, len)`
(`to_shape(len) = Int(len)`). -/
def m705 (T : VT) (len : Int) : R TA := do
  let n ← toInt len
  let a ← newArray [n]
  pure ⟨T, a⟩

/-- base/array.jl:707 `_similar_for(c::AbstractArray, T, itr, ::HasShape, axs) = similar(c, T, axs)`. -/
def m707 (T : VT) (dims : List Int) : R TA := do
  let a ← newArray dims
  pure ⟨T, a⟩

def similarFor (T : VT) : Shp → R TA
  | .none => m703 T
  | .len n => m705 T n
  | .axes d => m707 T d

/-- base/array.jl:697 `_similar_for(c, T, itr, isz, shp) = similar(c, T)`, for a container
`c` of size `cdims`. -/
def m697 (T : VT) (cdims : List Int) : R TA := do
  let a ← newArray cdims
  pure ⟨T, a⟩

/-! ### `collect(T, itr)` and `collect` with a known element type -/

/-- `copyto!(dest::AbstractArray, src)` for an iterator (base/abstractarray.jl:1048-1058):
walk `eachindex(dest)` alongside `src`, `ArgumentError` when `dest` runs out. -/
def copytoIter (conv : β → R α) (a : Arr α) : Int → List β → R (Arr α)
  | _, [] => .ok a
  | i, x :: xs => if length a < i then .error .argument else do
    let a ← m1031 conv a x i
    copytoIter conv a (i + 1) xs

/-- base/array.jl:686 `_collect(T, itr, isz::Union{HasLength,HasShape})`. -/
def m686 (T : VT) (it : Iter) : R TA := do
  let d ← arrayForInner T (m700 it)
  let a ← copytoIter (convertV T) d.a 1 it.xs
  pure ⟨T, a⟩

/-- base/array.jl:688 `_collect(T, itr, ::SizeUnknown)`: `Vector{T}()` and `push!`. -/
def m688 (T : VT) (it : Iter) : R TA := do
  let a ← newArray [0]
  let a ← pushEach (convertV T) a it.xs
  pure ⟨T, a⟩

/-- base/array.jl:684 `collect(::Type{T}, itr) = _collect(T, itr, IteratorSize(itr))`. -/
def m684 (T : VT) (it : Iter) : R TA :=
  match it.size with
  | .unknown => m688 T it
  | _ => m686 T it

/-- base/array.jl:777 `_collect(cont, itr, ::HasEltype, isz::Union{HasLength,HasShape})`. -/
def m777 (T : VT) (it : Iter) : R TA := do
  let d ← similarFor T (m700 it)
  let a ← copytoIter (convertV T) d.a 1 it.xs
  pure ⟨T, a⟩

/-- base/array.jl:780 `_collect(cont, itr, ::HasEltype, ::SizeUnknown)`. -/
def m780 (T : VT) (it : Iter) : R TA := do
  let d ← similarFor T .none
  let a ← pushEach (convertV T) d.a it.xs
  pure ⟨T, a⟩

/-! ### Widening collection -/

/-- base/array.jl:821 `@default_eltype(itr)`: the function of a `Generator` when it is a
type, else the inferred bound, then `promote_typejoin_union`. -/
def m821 (it : Iter) : VT :=
  ptjUnion (match it.fType with
    | some F => F
    | none => it.inferred)

/-- base/array.jl:805 `_iterator_upper_bound(itr)`: iterates to the end, then `throw(nothing)`. -/
def m805 (_it : Iter) : R JV := .error .thrownNothing

/-- base/array.jl:886 `setindex_widen_up_to(dest, el, i)`: `similar(dest, promote_typejoin(T, typeof(el)))`,
copy `dest[1:i-1]`, then `new[i] = el`. -/
def m886 (d : TA) (el : JV) (i : Int) : R TA := do
  let new ← newArray d.a.dims
  let new ← m288 new 1 d.a 1 (i - 1)
  pure ⟨typejoinT d.et (typeofV el), setU new i (some el)⟩

/-- base/array.jl:895 `collect_to!(dest, itr, offs, st)` over the remaining elements:
`@inbounds dest[i] = el` while `el isa T`, else widen and continue. -/
def m895 : TA → List JV → Int → R TA
  | d, [], _ => .ok d
  | d, el :: rest, i =>
    if isaV el d.et then m895 ⟨d.et, setU d.a i (some el)⟩ rest (i + 1)
    else do
      let new ← m886 d el i
      m895 new rest (i + 1)

/-- base/array.jl:875 `collect_to_with_first!(dest::AbstractArray, v1, itr, st)`:
`dest[first(LinearIndices(dest))] = v1`, then `collect_to!(dest, itr, i1+1, st)`. -/
def m875 (d : TA) (v1 : JV) (rest : List JV) : R TA := do
  let a ← m1031 (convertV d.et) d.a v1 1
  m895 ⟨d.et, a⟩ rest 2

/-- base/array.jl:922 `push_widen(dest, el)`: a new vector of type
`promote_typejoin(eltype(dest), typeof(el))`, `sizehint!` to `length(dest)`,
`append!(new, dest)`, `push!(new, el)`. -/
def m922 (d : TA) (el : JV) : R TA := do
  let S := typejoinT d.et (typeofV el)
  let new ← newArray [0]
  let new ← m1617 new (length d.a) false true
  let new ← m1427 (convertV S) new (.vec d.a)
  let new ← m1358 (convertV S) new el
  pure ⟨S, new⟩

/-- base/array.jl:935 `grow_to!(dest, itr, st)`: `push!` while `el isa T`, else `push_widen`. -/
def m935 : TA → List JV → R TA
  | d, [] => .ok d
  | d, el :: rest =>
    if isaV el d.et then do
      let a ← m1358 (convertV d.et) d.a el
      m935 ⟨d.et, a⟩ rest
    else do
      let new ← m922 d el
      m935 new rest

/-- base/array.jl:881 `collect_to_with_first!(dest, v1, itr, st)` for a non-array
destination (a vector-like container that is not an `AbstractArray`): `push!`, then
`grow_to!`. -/
def m881 (d : TA) (v1 : JV) (rest : List JV) : R TA := do
  let a ← m1358 (convertV d.et) d.a v1
  m935 ⟨d.et, a⟩ rest

/-- base/array.jl:914 `grow_to!(dest, itr)`: the first element decides the initial
element type (`empty(dest, typeof(y[1]))`). -/
def m914 (_d : TA) : List JV → R TA
  | [] => .ok _d
  | y :: rest => do
    let d2 ← newArray [0]
    let a ← m1358 (convertV (typeofV y)) d2 y
    m935 ⟨typeofV y, a⟩ rest

/-- The type assertion `::RT` after `collect_to_with_first!`: `AbstractArray{et′,N}` when
`et′` is concrete, else `AbstractArray{<:et′,N}`. -/
def rtCheck (et : VT) (d : TA) : R TA :=
  if isConcreteT et then (if d.et = et then .ok d else .error .typeError)
  else if subT d.et et then .ok d else .error .typeError

/-- The shared body of base/array.jl:833 and :858 for a known size: empty iterators get
`alloc(et, shp)`, others `alloc(typeof(v1), shp)` filled by `collect_to_with_first!`. -/
def collectSized (alloc : VT → Shp → R TA) (et : VT) (it : Iter) : R TA :=
  match it.xs with
  | [] => alloc et (m700 it)
  | v1 :: rest => do
    let dest ← alloc (typeofV v1) (m700 it)
    let r ← m875 dest v1 rest
    rtCheck et r

/-- base/array.jl:833 `collect(itr::Generator)`. -/
def m833 (it : Iter) : R TA :=
  let et := m821 it
  match it.size with
  | .unknown => do
    let d ← newArray [0]
    m914 ⟨et, d⟩ it.xs
  | _ => collectSized arrayForInner et it

/-- base/array.jl:855 `_collect(c, itr, ::EltypeUnknown, ::SizeUnknown)`. -/
def m855 (it : Iter) : R TA := do
  let d ← similarFor (m821 it) .none
  m914 d it.xs

/-- base/array.jl:858 `_collect(c, itr, ::EltypeUnknown, isz::Union{HasLength,HasShape})`. -/
def m858 (it : Iter) : R TA := collectSized similarFor (m821 it) it

/-- base/array.jl:771 `collect(itr) = _collect(1:1, itr, IteratorEltype(itr), IteratorSize(itr))`
(also base/array.jl:775 `collect_similar(cont, itr)` for an array `cont`). -/
def m771 (it : Iter) : R TA :=
  match it.eltype, it.size with
  | some T, .unknown => m780 T it
  | some T, _ => m777 T it
  | none, .unknown => m855 it
  | none, _ => m858 it

/-! ### `collect(A::AbstractArray)` -/

/-- An `AbstractArray` source with element type `et` (axes `f:l`, column-major elements). -/
structure SrcA where
  et : VT
  src : SrcArr JV

/-- `copyto_unaliased!`/`copyto!` of every element of `A` into `dest` in linear order
(`dest[i] = A[i]`; an `#undef` element throws `UndefRefError`). -/
def copyAll (et : VT) (dest : Arr JV) (A : SrcArr JV) : R (Arr JV) :=
  convWrites (readWrite (convertV et)) dest 1 A.elems

/-- base/array.jl:788 `_collect_indices(::Tuple{}, A)`: a zero-dimensional array. -/
def m788 (A : SrcA) : R TA := do
  let dest ← newArray []
  if A.src.elems = [] then pure ⟨A.et, dest⟩ else do
  let a ← copyAll A.et dest A.src
  pure ⟨A.et, a⟩

/-- base/array.jl:793 `_collect_indices(indsA::Tuple{Vararg{OneTo}}, A)`. -/
def m793 (A : SrcA) : R TA := do
  let dest ← newArray A.src.size
  if A.src.elems = [] then pure ⟨A.et, dest⟩ else do
  let a ← copyAll A.et dest A.src
  pure ⟨A.et, a⟩

/-- base/array.jl:798 `_collect_indices(indsA, A)`: `copyto!(B, CartesianIndices(axes(B)), A,
CartesianIndices(indsA))`, the same elements in the same order. -/
def m798 (A : SrcA) : R TA := do
  let B ← newArray A.src.size
  let a ← copyAll A.et B A.src
  pure ⟨A.et, a⟩

/-- base/array.jl:773 `collect(A::AbstractArray) = _collect_indices(axes(A), A)`. -/
def m773 (A : SrcA) : R TA :=
  if A.src.axs = [] then m788 A
  else if A.src.axs.all (fun ax => ax.1 == 1) then m793 A
  else m798 A

/-! ### `hcat` and `vcat` of vectors -/

/-- The elements of a vector, read in order (`UndefRefError` at the first `#undef`). -/
def readVec (a : Arr JV) : R (List JV) :=
  ((List.range (length a).toNat).map fun (k : Nat) => ((k : Int) + 1)).mapM (getL a)

/-- base/array.jl:2340 `hcat(V::Vector{T}...)` (one or more vectors): `DimensionMismatch`
unless all lengths equal `length(V[1])`, then the comprehension
`[V[j][i]::T for i=1:length(V[1]), j=1:length(V)]`, a `Generator` over a `HasShape{2}`
product whose element type inference bounds by `T`. -/
def m2340 (T : VT) (v1 : Arr JV) (vs : List (Arr JV)) : R TA :=
  let height := length v1
  if vs.any (fun v => length v != height) then .error .dimensionMismatch else do
  let cols ← (v1 :: vs).mapM readVec
  m833 ⟨cols.flatten, .shape [height, (vs.length + 1 : Nat)], none, T, none⟩

/-- `promote_eltype(A...)`: `promote_type` of the element types. -/
def promoteEltypes : List VT → VT
  | [] => .any
  | [t] => t
  | t :: ts => promoteT t (promoteEltypes ts)

/-- `cat(A...; dims=2)` of vectors (base/abstractarray.jl `_cat_t`): element type
`promote_eltype(A...)`, `DimensionMismatch` unless the lengths agree, the elements
converted column by column into a `length(A[1]) × length(A)` matrix. -/
def catCols (v1 : TA) (vs : List TA) : R TA :=
  let T := promoteEltypes ((v1 :: vs).map TA.et)
  let h := length v1.a
  if vs.any (fun v => length v.a != h) then .error .dimensionMismatch else do
  let cols ← (v1 :: vs).mapM fun v => readVec v.a
  let ys ← convList (convertV T) cols.flatten
  let a ← newArray [h, (vs.length + 1 : Nat)]
  pure ⟨T, safeWrites a 1 ys⟩

/-- `cat(A...; dims=1)` of vectors: element type `promote_eltype(A...)`, the elements
converted one vector after another. -/
def catRows (v1 : TA) (vs : List TA) : R TA :=
  let T := promoteEltypes ((v1 :: vs).map TA.et)
  do
  let cols ← (v1 :: vs).mapM fun v => readVec v.a
  let ys ← convList (convertV T) cols.flatten
  let a ← newArray [(ys.length : Int)]
  pure ⟨T, safeWrites a 1 ys⟩

/-- base/array.jl:2349 `hcat(A::Vector...) = cat(A...; dims=Val(2))`. -/
def m2349 (v1 : TA) (vs : List TA) : R TA := catCols v1 vs

/-- base/array.jl:2366 `vcat(A::Vector...) = cat(A...; dims=Val(1))`. -/
def m2366 (v1 : TA) (vs : List TA) : R TA := catRows v1 vs

/-- The copy loop of base/array.jl:2358-2363: `@assert nd + na <= 1 + length(arr)`, then
`unsafe_copyto!(arr, nd, a, 1, na)`. -/
def vcatCopy (arr : Arr JV) : Int → List (Arr JV) → R (Arr JV)
  | _, [] => .ok arr
  | nd, a :: as =>
    let na := length a
    if ¬ nd + na ≤ 1 + length arr then .error .assertion else do
    let arr ← m276 arr nd a 1 na
    vcatCopy arr (nd + na) as

/-- base/array.jl:2351 `vcat(arrays::Vector{T}...)`: `n = sum of lengths` (wrapping `+=`),
`Vector{T}(undef, n)`, then the copies. -/
def m2351 (T : VT) (arrays : List (Arr JV)) : R TA := do
  let n := arrays.foldl (fun n a => wrap64 (n + length a)) 0
  let arr ← newArray [n]
  let arr ← vcatCopy arr 1 arrays
  pure ⟨T, arr⟩

end JuliaLean.MultidimCov.ArrayV2
