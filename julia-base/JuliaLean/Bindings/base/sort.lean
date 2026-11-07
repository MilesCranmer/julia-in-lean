import JuliaLean.base.sort
import JuliaLean.base.abstractdict
import JuliaLean.base.gmp
import JuliaLean.base.missing
import JuliaLean.base.mpfr
import JuliaLean.base.rational
import JuliaLean.base.complex
import JuliaLean.base.indices
import JuliaLean.Proofs.base.range

/-!
# Callee bindings for `base/sort.jl`

Bindings of the public methods of `base/sort.jl` that the installed models leave as callbacks
(Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`): the keyword ordering `ord(lt, by, rev, order)`,
`defalg`, `sort!` on an `AbstractVector`, the legacy `sort!(v, lo, hi, a, o)`, `Vector`
storage on the installed heap, `partialsort!`/`partialsort`/`PartialQuickSort` targets and
`sort(x::NTuple)`. They are compiled against the changed `JuliaLean/base/sort.lean`
(`VectorStorage.firstindex`, axes-based `storageCheckBounds`, `Algorithm.user`,
`ArraySortKeywords.legacyEntry/names`, `UserAlgorithmMethods`, `PartialResult`, the `_sort!`
fallback branch of `sourceSortLoop`, and the one-based windows moved to `firstindex`/`lastindex`).

`JuliaLean.Proofs.base.range` is imported only for the `JInt` range instances.
-/

namespace JuliaLean.Bindings.base.sort

open JuliaLean JuliaLean.base JuliaLean.base.sort

/-! ## 0. Errors -/

/-- The public methods throw an `ordering.jl` error (`ord`), a Julia error of the installed
algorithms and array methods (`JlError`), a `range.jl` error of a target's `first`/`last`/`length`,
an error of the mutable heap (`array.Error`), a `to_index` error (`indices.IndexError`), or another
exception of the installed algorithms (`sort.SortException`). -/
inductive SortError where
  | ordering (e : ordering.OrderingError)
  | julia (e : JlError)
  | range (e : range.Exc)
  | heap (e : array.Error)
  | index (e : indices.IndexError)
  | sort (error : JuliaLean.base.sort.SortException)

universe u

abbrev SortResult (β : Type u) := Except SortError β

def liftJlR {β : Type} (x : Jl β) : SortResult β := x.mapError .julia

def liftSortR {β : Type} (x : JuliaLean.base.sort.SortResult β) : SortResult β :=
  x.mapError fun
    | .jl error => .julia error
    | .ordering error => .ordering error
    | error => .sort error

def liftRangeR {β : Type} (x : range.JlX β) : SortResult β := x.mapError .range

/-! ## 1. `ord(lt, by, rev, order)` (ordering.jl:155-160)

The keyword ordering is the installed `ordering.ordBool` (`rev::Bool`) or `ordering.ordNothing`
(`rev === nothing`). Ordering construction and each comparison preserve their exception through
`SortError.ordering`, including exceptions thrown by a user `lt` or `by` function. -/

def resolveOrd {A K : Type}
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg A K) (rev : Option Bool) (order : ordering.OrderArg K) :
    SortResult (ordering.OrdResult A K) :=
  (match rev with
   | some r => ordering.ordBool lt keyArg r order
   | none => ordering.ordNothing lt keyArg () order).mapError .ordering

/-- The installed comparison preserves its ordering error in the sorting error carrier. -/
def ordLess {A K : Type} (o : ordering.OrdResult A K) (a b : A) :
    JuliaLean.base.sort.SortResult Bool :=
  (ordering.ordCompare o a b).mapError .ordering

/-! ## 2. `defalg` (sort.jl:1620-1624)

`defalg(v::AbstractArray{<:Union{Number,Missing}})`, `AbstractArray{Missing}` and
`AbstractArray{Union{}}` are `DEFAULT_UNSTABLE`, other arrays and non-arrays `DEFAULT_STABLE`.
The choice is Julia's dispatch on the element type `T`. `SortEltype α` records
`T <: Union{Number, Missing}` for the Lean type `α` that models `T`; the instances below are
the installed value types, the same payloads as the `JVal` numeric constructors of the
jval-numeric proposal (`.float`, `.fixedInt`/`.int`/`.uint8`, `.bool`, `.complex`, `.bigInt`):
`JInt t` (`BitInteger <: Integer`), `float.FV T` (`IEEEFloat <: AbstractFloat`), `Bool <: Integer`,
`gmp.BigInt <: Signed`, `mpfr.BigFloat <: AbstractFloat`, `rational.Rational T <: Real`,
`complex.Complex T <: Number` (each `Number`); `Union{Missing, T}` (`Option α`) exactly when `T` is;
`String` is not. A program's own element type declares its supertype in its `struct`, and its
instance states that declaration. A program's own `defalg` method takes precedence
(`Base.Sort.defalg` "can be specialized", doc/src/base/sort.md). -/

/-- The `defalg` method an element type selects (sort.jl:1620-1623): `T <: Union{Number,
Missing}`, `T == Missing`, `T == Union{}`, or any other `T`. -/
inductive DefalgKind where
  | numberOrMissing
  | missing
  | bottom
  | other
  deriving DecidableEq

class SortEltype (α : Type) where
  kind : DefalgKind

/-- `T <: Union{Number, Missing}`. -/
def SortEltype.numberOrMissing (α : Type) [SortEltype α] : Bool :=
  SortEltype.kind α != .other

instance {t : IntTy} : SortEltype (JInt t) := ⟨.numberOrMissing⟩
instance {T : JuliaLean.base.float.FTy} : SortEltype (JuliaLean.base.float.FV T) := ⟨.numberOrMissing⟩
instance : SortEltype Bool := ⟨.numberOrMissing⟩
instance : SortEltype JuliaLean.base.gmp.BigInt := ⟨.numberOrMissing⟩
instance : SortEltype JuliaLean.base.mpfr.BigFloat := ⟨.numberOrMissing⟩
instance {T : Type} : SortEltype (JuliaLean.base.rational.Rational T) := ⟨.numberOrMissing⟩
instance {T : Type} : SortEltype (JuliaLean.base.complex.Complex T) := ⟨.numberOrMissing⟩
/-- `Missing` (installed `missing.MissingValue`): `defalg(v::AbstractArray{Missing})`. -/
instance : SortEltype JuliaLean.base.missing.MissingValue := ⟨.missing⟩
/-- `Union{}` (Lean `Empty`, no values): `defalg(v::AbstractArray{Union{}})`. -/
instance : SortEltype Empty := ⟨.bottom⟩
/-- `Union{Missing, T}`: a subtype of `Union{Number, Missing}` exactly when `T` is. -/
instance {α : Type} [SortEltype α] : SortEltype (Option α) :=
  ⟨if SortEltype.numberOrMissing α then .numberOrMissing else .other⟩
/-- `String`. -/
instance : SortEltype JuliaLean.Strings.JStr := ⟨.other⟩

theorem sortEltype_f64 : SortEltype.numberOrMissing (JuliaLean.base.sort.F64) = true := rfl

/-- `defalg(v)` of an `AbstractArray{T}`: a program method `userDefalg` if defined, otherwise
the installed `defalgNumberOrMissing` / `defalgArray` selected by `T`. -/
def defalgArrayDispatch {V α : Type} [SortEltype α]
    (userDefalg : Option (V → Algorithm (BracketSortTarget Int) Int)) (v : V) :
    Algorithm (BracketSortTarget Int) Int :=
  match userDefalg with
  | some method => method v
  | none => match SortEltype.kind α with
    | .numberOrMissing => defalgNumberOrMissing v
    | .missing => defalgMissing v
    | .bottom => defalgBottom v
    | .other => defalgArray v

/-! ## 3. `sort!` on an `AbstractVector` (sort.jl:1732-1741, 2570-2595)

A program's methods for its own `Algorithm` types take the `Ordering` object Julia passes:
`_sort!(v, ::TheirAlg, o::Ordering, kw)` and the old-style `sort!(v, lo, hi, ::TheirAlg, o)`.
They are generic in the ordering, so their argument is the resolved `ordering.OrdResult α K` of
any key type. In the generic `_sort!` dispatch of the installed `sourceSortLoop` (element types
without a `Missing`, `Bool`, `IEEEFloat` or `UIntMappable` method) every wrapper passes `o`
unchanged to its inner algorithm (sort.jl:570-572, 776-800, 878-990, 1277-1378), so the object a
nested user algorithm receives is the `o` resolved by the public entry. `withOrder` binds that
object into the patch's `UserAlgorithmMethods` record. -/

structure UserSortMethods (V α : Type) : Type 1 where
  sortBang : Nat → Option ({K : Type} → V → ordering.OrdResult α K → ArraySortKeywords α →
    JuliaLean.base.sort.SortResult (V × Option (Array α)))
  legacySortBang : Nat → Option ({K : Type} → V → Int → Int → ordering.OrdResult α K → JuliaLean.base.sort.SortResult V)

/-- A program that defines no sorting methods for its algorithms. -/
def UserSortMethods.none {V α : Type} : UserSortMethods V α :=
  ⟨fun _ => Option.none, fun _ => Option.none⟩

/-- The program's methods called with the resolved ordering object `o`. -/
def UserSortMethods.withOrder {V α K : Type} (m : UserSortMethods V α)
    (o : ordering.OrdResult α K) : UserAlgorithmMethods V α :=
  ⟨fun tag => (m.sortBang tag).map fun f v _ kw => f v o kw,
   fun tag => (m.legacySortBang tag).map fun f v lo hi _ => f v lo hi o⟩

/-- The vector storage with the program's methods bound to `o`. -/
def storageWithOrder {V α K : Type} (S : VectorStorage V α) (m : UserSortMethods V α)
    (o : ordering.OrdResult α K) : VectorStorage V α :=
  { S with userAlgorithms := m.withOrder o }

/-- The printed `typeof` names of the fallback `ArgumentError` (show.jl type printing). -/
abbrev Names := SortSignatureNames

/-- `sort!(v::AbstractVector{T}; alg=defalg(v), lt, by, rev, order, scratch)` (sort.jl:1732-1741):
`_sort!(v, maybe_apply_initial_optimizations(alg), ord(lt,by,rev,order), (;scratch))` on the
whole axis `firstindex(v):lastindex(v)`, with the resolved ordering object kept for the
program's algorithm methods. -/
def sortBang {V α K : Type} [Inhabited α] [SortEltype α] (S : VectorStorage V α)
    (methods : UserSortMethods V α)
    (pivot : Int → Int → Int)
    (userDefalg : Option (V → Algorithm (BracketSortTarget Int) Int)) (v : V)
    (alg : Option (Algorithm (BracketSortTarget Int) Int))
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) (names : Names) : SortResult V :=
  let alg := alg.getD (defalgArrayDispatch (α := α) userDefalg v)
  match hr : resolveOrd lt keyArg rev order with
  | .error e => .error e
  | .ok o => liftSortR (sourceSortBang (storageWithOrder S methods o) defaultBracketNumerics pivot v
      (sourceApplyInitialOptimizations alg) (ordLess o)
      { lo := S.firstindex v, hi := S.lastindex v, scratch, names })

/-- `legacy_dispatch_entry=a` of Base's old-style entry point (sort.jl:2575-2582): the fallback
`_sort!` compares it with the algorithm it receives, which only matters for a program's algorithm. -/
def legacyEntryOf : Algorithm (BracketSortTarget Int) Int → Option Nat
  | .user tag => some tag
  | _ => none

/-- `sort!(v, lo::Integer, hi::Integer, a, o)` and `sort!(v, lo, hi, a, o, scratch::Vector)`.
A program's own `sort!(v, lo, hi, ::TheirAlg, o)` method is more specific than Base's and runs
directly. Otherwise Base's method (sort.jl:2572-2582) checks `checkbounds(v, lo:hi)` against
`axes(v, 1)` and calls `_sort!(v, a, o, (; lo, hi, [scratch,] legacy_dispatch_entry=a))`. The
6-argument method with a non-`Vector` last argument drops it (`scratch = none`). -/
def legacySortBang {V α K : Type} [Inhabited α] (S : VectorStorage V α)
    (methods : UserSortMethods V α)
    (pivot : Int → Int → Int) (v : V) (lo hi : Int)
    (a : Algorithm (BracketSortTarget Int) Int) (o : ordering.OrdResult α K)
    (scratch : Option (Array α)) (names : Names) : SortResult V :=
  let base : SortResult V := do
    liftJlR (storageCheckBounds S v lo hi)
    liftSortR (sourceSortBang (storageWithOrder S methods o) defaultBracketNumerics pivot v a (ordLess o)
      { lo, hi, scratch, legacyEntry := legacyEntryOf a, names })
  match a with
  | .user tag =>
    match methods.legacySortBang tag with
    | some method => liftSortR (method v lo hi o)
    | none => base
  | _ => base

/-- `sort!(v, a, o) = sort!(v, firstindex(v), lastindex(v), a, o)` (sort.jl:2571). -/
def legacySortBangWhole {V α K : Type} [Inhabited α] (S : VectorStorage V α)
    (methods : UserSortMethods V α)
    (pivot : Int → Int → Int) (v : V)
    (a : Algorithm (BracketSortTarget Int) Int) (o : ordering.OrdResult α K)
    (names : Names) : SortResult V :=
  legacySortBang S methods pivot v (S.firstindex v) (S.lastindex v) a o none names

/-! ## 4. `Vector` on the installed heap (sort.jl:1780-1783)

`v` is a handle of the installed `array.MutableMemory α`; reads and writes are the installed
`getindex`/`setindex!` (`array.mutableGet`/`mutableSet`), `similar`/`copyto!` the installed
`similar414`/`copyto325`, and the sort is `sortBang` on `arrayStorage` with the program's
algorithm methods. `sort(v)` copies with `copymutable(v) = copyto!(similar(v), v)`
(abstractarray.jl:1211-1214), bound here only for `Vector`: no installed model gives `similar` and
`copyto!` for an arbitrary `AbstractVector`, so the copying methods `sort(v)` and
`partialsort(v, k)` are restricted to `Vector` (named gap G8). -/

abbrev SortM (α : Type) := ExceptT SortError (StateM (array.MutableMemory α))

def liftHeap {α β : Type} (x : array.MutationM α β) : SortM α β :=
  ExceptT.mk (do let r ← x.run; pure (r.mapError .heap))

def liftResult {α β : Type} (x : SortResult β) : SortM α β := ExceptT.mk (pure x)

/-- `v[1], ..., v[length(v)]`. -/
def heapElements {α : Type} (v : Nat) : array.MutationM α (Array α) := do
  let n ← array.mutableLength v
  let xs ← (arrayIndexRange 1 n.val).mapM fun i => array.mutableGet v (JInt.wrap .i64 i)
  pure xs.toArray

/-- `v[i] = xs[i]` for `i ∈ 1:length(xs)`. -/
def heapWriteBack {α : Type} (v : Nat) (xs : Array α) : array.MutationM α Unit := do
  for (x, i) in xs.toList.zipIdx 1 do
    array.mutableSet v x (JInt.wrap .i64 (Int.ofNat i))

/-- `sort!(v::Vector{T}; ...)`: the installed algorithm runs on `v`'s elements and the result is
written back. An unassigned slot throws `UndefRefError` before any write (named gap G2). -/
def heapSortBang {α K : Type} [Inhabited α] [SortEltype α]
    (methods : UserSortMethods (Array α) α)
    (pivot : Int → Int → Int) (userDefalg : Option (Array α → Algorithm (BracketSortTarget Int) Int))
    (v : Nat) (alg : Option (Algorithm (BracketSortTarget Int) Int))
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) (names : Names) : SortM α Nat := do
  let xs ← liftHeap (heapElements v)
  let sorted ← liftResult (sortBang arrayStorage methods pivot userDefalg xs alg lt
    keyArg rev order scratch names)
  liftHeap (heapWriteBack v sorted)
  pure v

/-- `copymutable(a) = copyto!(similar(a), a)` (abstractarray.jl:1211-1214) on a `Vector`. -/
def heapCopymutable {α : Type} (layout : Option array.MemoryLayout) (a : Nat) :
    array.MutationM α Nat :=
  abstractarray.copyMutableArray
    (array.similar414 (fun a _ => array.mutableLength a) (array.mutableAllocate layout a))
    (array.copyto325 (fun _ => pure array.one) (fun _ => pure array.one) array.mutableLength
      (fun d doffs s soffs n => do array.mutableCopyto d doffs s soffs n; pure d))
    a

/-- `sort(v::AbstractVector; kws...) = sort!(copymutable(v); kws...)` (sort.jl:1780) on a
`Vector`: a fresh handle is sorted; `v` is only read. -/
def heapSort {α K : Type} [Inhabited α] [SortEltype α] (layout : Option array.MemoryLayout)
    (methods : UserSortMethods (Array α) α)
    (pivot : Int → Int → Int) (userDefalg : Option (Array α → Algorithm (BracketSortTarget Int) Int))
    (v : Nat) (alg : Option (Algorithm (BracketSortTarget Int) Int))
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) (names : Names) : SortM α Nat := do
  let copied ← liftHeap (heapCopymutable layout v)
  heapSortBang methods pivot userDefalg copied alg lt keyArg rev order scratch names

/-- `collect(itr)` of a `HasLength` iterator into a fresh `Vector` (array.jl:686-687, installed
`collectSized`): `length(itr)` slots filled in iteration order. -/
def heapCollectList {α : Type} (layout : Option array.MemoryLayout) (elements : List α) :
    array.MutationM α Nat :=
  array.collectSized
    (fun (itr : List α) (_ : Unit) => pure (JInt.wrap .i64 (Int.ofNat itr.length)))
    (fun (_ : Unit) (_ : Unit) (n : array.I) => array.mutableAllocate layout 0 n)
    (fun dest (itr : List α) => do
      for (x, i) in itr.zipIdx 1 do array.mutableSet dest x (JInt.wrap .i64 (Int.ofNat i))
      pure dest)
    () elements ()

/-- The `KeySet`/`ValueIterator` of `sort(v::COLLECT_ON_SORT_TYPES)` (sort.jl:1782). -/
inductive Collected (K D : Type) where
  | keys (v : abstractdict.KeySet K D)
  | values (v : abstractdict.ValueIterator D)

/-- `sort(v::Union{KeySet,ValueIterator}; kws...) = sort!(collect(v); kws...)` (sort.jl:1783):
the iteration is the installed `iterate(v::Union{KeySet,ValueIterator})` (abstractdict.jl:65-69,
`abstractdict.iterPartAll`) over the dictionary type's own methods (`abstractdict.DictOps`). -/
def heapSortKeys {T D K V0 Kk : Type} [Inhabited K] [SortEltype K]
    (dictOps : abstractdict.DictOps T D K V0) (layout : Option array.MemoryLayout)
    (methods : UserSortMethods (Array K) K)
    (pivot : Int → Int → Int) (userDefalg : Option (Array K → Algorithm (BracketSortTarget Int) Int))
    (v : abstractdict.KeySet K D) (alg : Option (Algorithm (BracketSortTarget Int) Int))
    (lt : Sum (Kk → Kk → ordering.OrderingResult Bool) (Kk → Kk → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg K Kk) (rev : Option Bool) (order : ordering.OrderArg Kk)
    (scratch : Option (Array K)) (names : Names) : SortM K Nat := do
  let collected ← liftHeap (heapCollectList layout (abstractdict.iterPartAll dictOps .keys v.dict))
  heapSortBang methods pivot userDefalg collected alg lt keyArg rev order scratch names

def heapSortValues {T D K V0 Kk : Type} [Inhabited V0] [SortEltype V0]
    (dictOps : abstractdict.DictOps T D K V0) (layout : Option array.MemoryLayout)
    (methods : UserSortMethods (Array V0) V0)
    (pivot : Int → Int → Int)
    (userDefalg : Option (Array V0 → Algorithm (BracketSortTarget Int) Int))
    (v : abstractdict.ValueIterator D) (alg : Option (Algorithm (BracketSortTarget Int) Int))
    (lt : Sum (Kk → Kk → ordering.OrderingResult Bool) (Kk → Kk → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg V0 Kk) (rev : Option Bool) (order : ordering.OrderArg Kk)
    (scratch : Option (Array V0)) (names : Names) : SortM V0 Nat := do
  let collected ← liftHeap (heapCollectList layout (abstractdict.iterPartAll dictOps .vals v.dict))
  heapSortBang methods pivot userDefalg collected alg lt keyArg rev order scratch names

/-! ## 5. `partialsort!`, `partialsort` and `PartialQuickSort` targets (sort.jl:97-108, 166-177, 2356-2358)

`k::Union{Integer,OrdinalRange}`. Integers: every `BitInteger` (`JInt t`), `Bool` and `BigInt`.
Ordinal ranges, as the installed `range.jl` records with their constructor-normalized fields
(`first(r) = r.start`, `last(r) = r.stop`, `step(r) = r.step`; `first(::OneTo) = 1`):
`Base.OneTo{T}`, `UnitRange{T}` and `StepRange{T,S}` of `BitInteger` values (any `BitInteger`
step type), `UnitRange{BigInt}`, `StepRange{BigInt,BigInt}`, `StepRange{BigInt,S}` for a
`BitInteger` step type `S` (the type of `big(1):2:big(9)` and `big(9):-2:big(1)`; probed) and
`StepRange{T,BigInt}` for a `BitInteger` `T` (the type of `StepRange(1, big(2), 9)`; the colon
`1:big(2):9` makes a `StepRange{BigInt,BigInt}`; probed).

Unsupported targets (named gap G10, no binding; `SortTarget` has no constructor for them):
`Base.OneTo{BigInt}` (`Base.OneTo(big(3))`), every range whose element or step type is `Bool`
(`UnitRange{Bool}` from `false:true`, `StepRange{Bool,Bool}`, `StepRange{T,Bool}`),
`Base.IdentityUnitRange` and `Base.Slice` (wrappers of another range), a program's own
`OrdinalRange` subtypes, and a program's own `Integer` subtypes as `k` (a user `struct MyInt <:
Integer` satisfies the signature `k::Union{Integer,OrdinalRange}`, sort.jl:97,166, and `minimum`,
`floor(Int, ...)` and `to_index` then run the program's methods; not probed). Julia runs
`partialsort!` for the others (`partialsort!(v, Base.Slice(2:3))` etc.; probe `gap targets` in
`probe.jl`), so a statement over "every `Integer` or `OrdinalRange` target" cannot use this binding.

Two phases raise target errors, in this order:

1. Before any element moves, when `length(v) >= 260` and the element type is not `Bool`
   (`BracketedSort`, sort.jl:1264-1286; for a shorter vector `ln < 260 && return _sort!(...)` skips
   all scalar math). `BracketedSort`
   evaluates `minimum(target)` and `maximum(target)` (`ArgumentError` for an empty target) and then
   `floor(Int, (tar - lo) * k2ln + lo + off)` for the minimum and the maximum, each of which throws
   `InexactError` when the value is not an `Int`. The installed `sortBracketed` does these steps in
   the same order, before the first `ops.swap` (`targetMinimum`, `targetMaximum`, then `floorIndex`
   twice); `defaultBracketNumerics` binds its `floorIndex` field to `floor(Int, x) =
   convert(Int, floor(x))` of the installed `float.lean`. So at length 260 or more,
   `partialsort!(v, big(2)^70)` and `partialsort!(v, big(1):big(2)^70)` throw `InexactError` with `v`
   unchanged. A target whose signpost values are all `Int`s but which lies outside the vector gets
   past this phase and fails in phase 2. A `Vector{Bool}` never reaches `BracketedSort`:
   `partialsort!` runs `BoolOptimization(Small{12}(BracketedSort(k)))` (sort.jl:102-105) and
   `BoolOptimization` sorts a `Bool` vector by counting (sort.jl:746-758, installed `sortBoolVector`,
   routed by `boolSortRoute`), so every target error of a `Bool` vector comes from phase 2, after the
   vector is fully sorted, at any length (probe `bool len260` cases).
2. After the sort, `maybeview(v, k)` (sort.jl:110-111) indexes the sorted vector:
   - an integer `k` is `v[k]`: `to_index(A, k)` first (the parameter `toIndex`: for an `Array` the
     installed `indices.to_index_Array`, where a `UInt` is reinterpreted and other `BitInteger`s
     are converted with `InexactError` outside `Int`; for any other `AbstractVector` the generic
     `indices.to_index`, which converts a `UInt` above `typemax(Int)` with `InexactError`; for
     `Bool`, `indices.to_index_Bool` throws `ArgumentError` in both; a `BigInt` is converted with
     `gmp.convertSigned .i64`), then the bounds check;
   - a range is `view(v, k)` (subarray.jl:221-227): `checkbounds(v, k)` on the range's own values
     (`BoundsError` when it is nonempty and its first or last term lies outside
     `firstindex(v):lastindex(v)`), then `unsafe_view` builds the `SubArray` with `Int` indices,
     converting `first`, `step` and `last` (`InexactError` outside `Int`, for an empty range too).

Everything else about `k` in the installed algorithms (`first`, `last`, comparisons with `Int`
positions, `target .- count_below`, the `Int` indices) is integer arithmetic on its values, so the
installed `BracketSortTarget Int` holds the exact values (Lean `Int`), whatever the integer type:
`bracketTarget` below is total. `length(k)` is the exact number of terms.

Not faithful (named gap G9): the signpost arithmetic of phase 1 for length 260 or more. Julia
computes `tar - lo` in the promoted type of the target's element type and `lo::Int` (wrapping
`Int64`/`UInt64` subtraction, `Int128`, `UInt128`) and, for a `BigInt` target, the whole
expression in `BigFloat`; the installed `storageBracketOps.differenceToFloat` is
`Float.ofInt (a - b)` on exact integers. The two agree whenever the difference needs no wraparound
and no `BigFloat` rounding, and differ otherwise (for example `typemin(Int)` or `UInt64(0)` as
target with `lo = 1`; the signposts, and with them the state `v` is left in after the final
`BoundsError`, differ). A statement over all targets and lengths of 260 or more is therefore not
stateable with this binding.

Probed on both Julia versions. -/

inductive SortTarget where
  | integer {t : IntTy} (k : JInt t)
  | bool (k : Bool)
  | bigInt (k : JuliaLean.base.gmp.BigInt)
  | oneTo {t : IntTy} (r : range.OneTo (JInt t))
  | unitRange {t : IntTy} (r : range.UnitRange (JInt t))
  | stepRange {t s : IntTy} (r : range.StepRange (JInt t) (JInt s))
  | bigUnitRange (r : range.UnitRange JuliaLean.base.gmp.BigInt)
  | bigStepRange (r : range.StepRange JuliaLean.base.gmp.BigInt JuliaLean.base.gmp.BigInt)
  /-- `StepRange{BigInt,S}` for a `BitInteger` step type `S`: the type of `big(1):2:big(9)`. -/
  | bigStartStepRange {s : IntTy} (r : range.StepRange JuliaLean.base.gmp.BigInt (JInt s))
  /-- `StepRange{T,BigInt}` for a `BitInteger` `T`: the type of `StepRange(1, big(2), 9)`. -/
  | bigStepOfBitRange {t : IntTy} (r : range.StepRange (JInt t) JuliaLean.base.gmp.BigInt)

def liftIndexR {β : Type} (x : indices.IndexResult β) : SortResult β := x.mapError .index

/-- The number of terms of `start:step:stop` (`length(r)` of a constructor-normalized range). -/
def termCount (start step stop : Int) : Nat :=
  if step = 0 then 0 else
  let n := (stop - start) / step + 1
  if n ≤ 0 then 0 else n.toNat

/-- `k` as the installed algorithms use it: its exact values. -/
def bracketTarget : SortTarget → BracketSortTarget Int
  | .integer k => .index k.val
  | .bool k => .index (if k then 1 else 0)
  | .bigInt k => .index k.val
  | .oneTo r => .range 1 r.stop.val
  | .unitRange r => .range r.start.val r.stop.val
  | .stepRange r => .ordinal r.start.val r.step.val r.stop.val
      (termCount r.start.val r.step.val r.stop.val)
  | .bigUnitRange r => .range r.start.val r.stop.val
  | .bigStepRange r => .ordinal r.start.val r.step.val r.stop.val
      (termCount r.start.val r.step.val r.stop.val)
  | .bigStartStepRange r => .ordinal r.start.val r.step.val r.stop.val
      (termCount r.start.val r.step.val r.stop.val)
  | .bigStepOfBitRange r => .ordinal r.start.val r.step.val r.stop.val
      (termCount r.start.val r.step.val r.stop.val)

/-- `PartialQuickSort(k)` (sort.jl:2356-2358): the algorithm keeps `k`; the installed
`.partialQuickSort` reads `first(a.k)` and `last(a.k)`. -/
def partialQuickSortOf (k : SortTarget) : Algorithm (BracketSortTarget Int) Int :=
  .partialQuickSort (bracketTarget k)

/-- `to_index(A, i)` of an integer index (`indices.jl:244-259`), the method Julia selects for the
vector's type: for an `Array` the installed `indices.to_index_Array` (a `UInt` is reinterpreted,
`to_index(A::Array, i::UInt) = reinterpret(Int, i)`), for every other `AbstractVector` the generic
`to_index(A, i) = to_index(i)` (`indices.to_index`: `convert(Int, i)`, `InexactError` for a `UInt`
above `typemax(Int)`). -/
abbrev ToIndex := (t : IntTy) → JInt t → indices.IndexResult indices.I64

/-- `Array` vectors. -/
def toIndexArray : ToIndex := fun t i => indices.to_index_Array t () i

/-- Every other `AbstractVector`. -/
def toIndexGeneric : ToIndex := fun _ i => indices.to_index i

/-- `to_index(A, k)` of an integer target. -/
def targetIndex (toIndex : ToIndex) : SortTarget → SortResult Int
  | .integer (t := t) k => do pure (← liftIndexR (toIndex t k)).val
  | .bool k => do pure (← liftIndexR (indices.to_index_Bool k)).val
  | .bigInt k => do pure (← liftJlR (JuliaLean.base.gmp.convertSigned .i64 k)).val
  | _ => .error (.julia (.methodError "to_index"))

/-- `convert(Int, x)` of a range field in `unsafe_view`. -/
def rangeFieldInt : SortTarget → SortResult (List Int)
  | .oneTo r => do pure [1, (← liftJlR (JuliaLean.base.int.convert .i64 r.stop)).val]
  | .unitRange r => do
    pure [(← liftJlR (JuliaLean.base.int.convert .i64 r.start)).val,
      (← liftJlR (JuliaLean.base.int.convert .i64 r.stop)).val]
  | .stepRange r => do
    pure [(← liftJlR (JuliaLean.base.int.convert .i64 r.start)).val,
      (← liftJlR (JuliaLean.base.int.convert .i64 r.step)).val,
      (← liftJlR (JuliaLean.base.int.convert .i64 r.stop)).val]
  | .bigUnitRange r => do
    pure [(← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.start)).val,
      (← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.stop)).val]
  | .bigStepRange r => do
    pure [(← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.start)).val,
      (← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.step)).val,
      (← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.stop)).val]
  | .bigStartStepRange r => do
    pure [(← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.start)).val,
      (← liftJlR (JuliaLean.base.int.convert .i64 r.step)).val,
      (← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.stop)).val]
  | .bigStepOfBitRange r => do
    pure [(← liftJlR (JuliaLean.base.int.convert .i64 r.start)).val,
      (← liftJlR (JuliaLean.base.gmp.convertSigned .i64 r.step)).val,
      (← liftJlR (JuliaLean.base.int.convert .i64 r.stop)).val]
  | _ => pure []

/-- `maybeview(v, k)` on the sorted vector (sort.jl:110-111): `v[k]` for an integer, `view(v, k)`
for a range (bounds on the range's values, then the `Int` conversion of `unsafe_view`). -/
def maybeviewTarget {V α : Type} (toIndex : ToIndex) (S : VectorStorage V α) (values : V)
    (k : SortTarget) :
    SortResult (PartialResult α) :=
  let target := bracketTarget k
  let lo := S.firstindex values
  let hi := S.lastindex values
  match target with
  | .index _ => do
    let i ← targetIndex toIndex k
    pure (.element (← liftJlR (maybeviewInteger S.getindex values i)))
  | _ => do
    let ixs := bracketTargetIndices target
    match ixs.head?, ixs.getLast? with
    | some f, some l =>
      if f < lo ∨ hi < f ∨ l < lo ∨ hi < l then .error (.julia .boundsError) else pure ()
    | _, _ => pure ()
    let _ ← rangeFieldInt k
    pure (.elements (← liftJlR (maybeviewRange (fun current selection =>
      (bracketTargetIndices selection).mapM (S.getindex current)) values target)))


/-- `_sort!(v::AbstractVector{Bool}, ::BoolOptimization, o, kw)` (sort.jl:746-758), the installed
`sortBoolVector` on the whole axis: `partialsort!` runs `BoolOptimization(Small{12}(BracketedSort(k)))`
(sort.jl:102-105), so a `Bool` vector is sorted by counting and `BracketedSort` never runs. The
generic `sourceSortLoop` takes the `AbstractVector` method of `BoolOptimization` for every element
type (installed `sortBoolOther`); the element type `Bool` supplies this route. -/
def boolSortRoute {V : Type} (S : VectorStorage V Bool) :
    V → (Bool → Bool → JuliaLean.base.sort.SortResult Bool) → JuliaLean.base.sort.SortResult V :=
  fun v o => sortBoolVector (storageBoolSortOps S) v o (S.firstindex v, S.lastindex v)

/-- The installed `partialSortBang` (sort.jl:97-108) with the installed `storagePartialSortOps`
(whole axis `firstindex(v):lastindex(v)`, `defaultBracketNumerics`) and this target's
`maybeview` (`toIndex` selects the `to_index(A, i)` method of the vector's type; `boolSort` is
`some (boolSortRoute S)` exactly when the element type is `Bool`, `none` otherwise). -/
def partialSortOpsFor {V α : Type} [Inhabited α] (toIndex : ToIndex) (S : VectorStorage V α)
    (boolSort : Option (V → (α → α → JuliaLean.base.sort.SortResult Bool) → JuliaLean.base.sort.SortResult V))
    (pivot : Int → Int → Int) (k : SortTarget) :
    PartialSortOps V (BracketSortTarget Int) Int (α → α → JuliaLean.base.sort.SortResult Bool) (Option (Array α))
      (ArraySortKeywords α) (PartialResult α) SortError :=
  let ops := storagePartialSortOps S defaultBracketNumerics pivot
  { targetOps := ops.targetOps
    sort := fun v a o kw => match boolSort, a with
      | some route, .boolOptimization _ => liftSortR (route v o)
      | _, _ => liftSortR (ops.sort v a o kw)
    maybeView := fun v _ => maybeviewTarget toIndex S v k
    withScratch := ops.withScratch
    scratchOfKeywords := ops.scratchOfKeywords }

/-- `partialsort!(v, k; lt, by, rev, order, scratch) = partialsort!(v, k, ord(lt,by,rev,order);
scratch)` (sort.jl:166-168): `ord(...)` is resolved first (its `OrderingError` comes before any
sorting), then `partialsort!(v, k, o; scratch)` (sort.jl:97-108), the installed
`partialSortBang`. -/
def partialsortBang {V α K : Type} [Inhabited α] (toIndex : ToIndex) (S : VectorStorage V α)
    (boolSort : Option (V → (α → α → JuliaLean.base.sort.SortResult Bool) → JuliaLean.base.sort.SortResult V))
    (pivot : Int → Int → Int) (v : V) (k : SortTarget)
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) : SortResult (PartialResult α) :=
  match hr : resolveOrd lt keyArg rev order with
  | .error e => .error e
  | .ok o => partialSortBang (partialSortOpsFor toIndex S boolSort pivot k) v (bracketTarget k)
      (ordLess o) scratch

/-- `partialsort!(v::Vector, k; ...)` on the installed heap: `ord(...)` first, then the sort,
whose result is written back to `v`, then `maybeview`, whose error leaves `v` sorted (the two
phases of the installed `partialSortBang`, theorem `partialSortBang_phases`). -/
def heapPartialsortBang {α K : Type} [Inhabited α]
    (boolSort : Option (Array α → (α → α → JuliaLean.base.sort.SortResult Bool) → JuliaLean.base.sort.SortResult (Array α)))
    (pivot : Int → Int → Int) (v : Nat) (k : SortTarget)
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) : SortM α (PartialResult α) :=
  match hr : resolveOrd lt keyArg rev order with
  | .error e => liftResult (.error e)
  | .ok o => do
    let ops := partialSortOpsFor toIndexArray arrayStorage boolSort pivot k
    let xs ← liftHeap (heapElements v)
    let sorted ← liftResult (ops.sort xs
      (.boolOptimization (smallDefault 12 (bracketedSort ops.targetOps (bracketTarget k))))
      (ordLess o) (ops.withScratch scratch))
    liftHeap (heapWriteBack v sorted)
    liftResult (ops.maybeView sorted (bracketTarget k))

theorem partialSortBang_phases {V K Index O Scratch Kws R E : Type}
    (ops : PartialSortOps V K Index O Scratch Kws R E) (v : V) (k : K) (o : O) (s : Scratch) :
    partialSortBang ops v k o s =
      (do let sorted ← ops.sort v (.boolOptimization (smallDefault 12
            (bracketedSort ops.targetOps k))) o (ops.withScratch s)
          ops.maybeView sorted k) := rfl

/-- An `ord(lt, by, rev, order)` error is the result of `partialsort!` whatever the target and
length: it is raised before the target is looked at (sort.jl:166-168). -/
theorem partialsortBang_ordering_error {V α K : Type} [Inhabited α] (toIndex : ToIndex)
    (S : VectorStorage V α) (boolSort : Option (V → (α → α → JuliaLean.base.sort.SortResult Bool) → JuliaLean.base.sort.SortResult V))
    (pivot : Int → Int → Int) (v : V)
    (k : SortTarget)
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) (e : SortError)
    (h : resolveOrd lt keyArg rev order = .error e) :
    partialsortBang toIndex S boolSort pivot v k lt keyArg rev order scratch = .error e := by
  unfold partialsortBang
  split
  · next e' hr => rw [h] at hr; cases hr; rfl
  · next o hr => rw [h] at hr; cases hr

/-- On the heap the same error leaves memory untouched. -/
theorem heapPartialsortBang_ordering_error {α K : Type} [Inhabited α]
    (boolSort : Option (Array α → (α → α → JuliaLean.base.sort.SortResult Bool) → JuliaLean.base.sort.SortResult (Array α)))
    (pivot : Int → Int → Int) (v : Nat) (k : SortTarget)
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) (e : SortError) (mem : array.MutableMemory α)
    (h : resolveOrd lt keyArg rev order = .error e) :
    (heapPartialsortBang boolSort pivot v k lt keyArg rev order scratch).run mem =
      (.error e, mem) := by
  unfold heapPartialsortBang
  split
  · next e' hr => rw [h] at hr; cases hr; rfl
  · next o hr => rw [h] at hr; cases hr

/-- `partialsort(v, k; kws...) = partialsort!(copymutable(v), k; kws...)` (sort.jl:176-177) on a
`Vector`: `copymutable` is `heapCopymutable`; `v` is only read. -/
def heapPartialsort {α K : Type} [Inhabited α] (layout : Option array.MemoryLayout)
    (boolSort : Option (Array α → (α → α → JuliaLean.base.sort.SortResult Bool) → JuliaLean.base.sort.SortResult (Array α)))
    (pivot : Int → Int → Int) (v : Nat) (k : SortTarget)
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (Array α)) : SortM α (PartialResult α) := do
  let copied ← liftHeap (heapCopymutable layout v)
  heapPartialsortBang boolSort pivot copied k lt keyArg rev order scratch

/-! ## 6. `sort(x::NTuple; alg, ...)` (sort.jl:1785-1808)

The tuple scratch may be a `Vector` of any element type; `eltype(x) == eltype(scratch)` or
`ArgumentError`. `_sort` is dispatched on the algorithm and the element type: a program's own
`_sort(x::NTuple, ::TheirAlg, o)` or more specific
`_sort(x::NTuple{N,TheirType}, ::DefaultStable, o)` method (`userTupleSort`, comment at
sort.jl:1796-1797) takes precedence; otherwise Base's method for `DefaultStable`/`DefaultUnstable`
(installed `sortTupleCore`), and a `MethodError` for any other algorithm. -/

inductive TupleScratch (α : Type) where
  | sameEltype (v : Array α)
  | otherEltype

def sortTuple {α K : Type} [Inhabited α] (n : Nat) (pivot : Int → Int → Int)
    (userTupleSort : Algorithm (BracketSortTarget Int) Int →
      Option (NTuple n α → ordering.OrdResult α K → SortResult (NTuple n α)))
    (x : NTuple n α) (alg : Option (Algorithm (BracketSortTarget Int) Int))
    (lt : Sum (K → K → ordering.OrderingResult Bool) (K → K → ordering.OrderingResult Bool))
    (keyArg : ordering.KeyArg α K) (rev : Option Bool) (order : ordering.OrderArg K)
    (scratch : Option (TupleScratch α)) : SortResult (NTuple n α) := do
  -- `defalg(x)` for a tuple is `defalg(v) = DEFAULT_STABLE` (sort.jl:1624).
  let alg := alg.getD .defaultStable
  let scratch ← match scratch with
    | none => pure none
    | some (.sameEltype v) => pure (some v)
    | some .otherEltype => throw (.julia (.argumentError "scratch has the wrong eltype"))
  match hr : resolveOrd lt keyArg rev order with
  | .error e => .error e
  | .ok o =>
    match userTupleSort alg with
    | some method => method x o
    | none => match alg with
      | .defaultStable | .defaultUnstable =>
        liftSortR (sortTupleCore (nTupleCoreOps n pivot) x alg (ordLess o) scratch)
      | _ => .error (.julia (.methodError "_sort"))

end JuliaLean.Bindings.base.sort
