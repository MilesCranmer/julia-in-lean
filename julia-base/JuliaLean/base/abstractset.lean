import JuliaLean.Core
import JuliaLean.base.int

/-!
# Model of `base/abstractset.jl`

Typed models of the AbstractSet methods in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform. Collection protocol calls are typed parameters; `elements` records the
finite iteration trace, while operations that can fail return `Except` so failures propagate in
source order. Overload dispatch is represented by the static type tags and set-kind facts supplied
by the caller.
-/

namespace JuliaLean.base.abstractset

open JuliaLean JuliaLean.base.int

abbrev I64 := JInt .i64

def int (n : Int) : I64 := JInt.lit .i64 n

/-- The type token inspected by `max_values`. -/
inductive JuliaType where
  | other
  | bitInteger (t : IntTy)
  | bool
  | nothing
  | union (a b : JuliaType)
  deriving Repr, DecidableEq

/-- Interface calls made by methods in `abstractset.jl`. -/
structure Calls (α : Type) where
  C : Type
  Error : Type
  elements : C → List α
  equal : α → α → Bool
  hasLength : C → Bool
  length : C → Except Error I64
  hasFastIn : C → Bool
  isAbstractSet : C → Bool
  isIntegerRange : C → Bool
  isEmptyRange : C → Bool
  member : C → α → Except Error Bool
  makeSet : C → Except Error C
  empty : C → Except Error C
  emptyMutable : C → JuliaType → Except Error C
  emptyMutableDefault : C → Except Error C
  copy : C → Except Error C
  copyMutable : C → Except Error C
  sizehint : C → I64 → Bool → Except Error C
  push : C → α → Except Error C
  delete : C → α → Except Error C
  filterBang : (α → Except Error Bool) → C → Except Error C
  promoteEltype : C → List C → Except Error JuliaType
  elementType : C → JuliaType
  subtype : JuliaType → JuliaType → Bool
  sameType : JuliaType → JuliaType → Bool
  intLength : I64 → Except Error I64
  findminLength : List C → Except Error (I64 × Nat)
  setindex : List C → C → Nat → Except Error (List C)
  getindex : List C → Nat → Except Error C
  extrema : C → Except Error (α × α)
  step : C → Except Error α
  minimum : C → Except Error α
  abs : α → Except Error α
  lessThan : α → α → Except Error Bool
  mod : α → α → Except Error α
  addWithOverflow : I64 → I64 → I64 × Bool

/-- `Fix2(f, y)`, a function with its second argument fixed. -/
structure Fix2 (A B R : Type) where
  function : A → B → R
  fixed : B

def Fix2.apply {A B R : Type} (f : Fix2 A B R) (x : A) : R := f.function x f.fixed

/--
Julia source: base/abstractset.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:AbstractSet{T}}) where {T} = @isdefined(T) ? T : Any
```
-/
def eltypeAbstractSet {T : Type 1} (parameter : Option T) (anyType : T) : T :=
  parameter.getD anyType

/--
Julia source: base/abstractset.jl:4-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizehint!(s::AbstractSet, n) = s
```
-/
def sizehintAbstractSet {C : Type} (s : C) (_n : Nat) : C := s

/--
Julia source: base/abstractset.jl:92-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max_values(::Type) = typemax(Int)
```
-/
def maxValuesType (_T : JuliaType) : I64 := int (IntTy.max .i64)

/--
Julia source: base/abstractset.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max_values(T::Union{map(X -> Type{X}, BitIntegerSmall_types)...}) = 1 << (8*sizeof(T))
```
-/
def maxValuesBitIntegerSmall (T : IntTy) : I64 :=
  shl_int (int 1) (int (Int.ofNat (8 * sizeofT T)))

/--
Julia source: base/abstractset.jl:95-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function max_values(T::Union)
    a = max_values(T.a)::Int
    b = max_values(T.b)::Int
    r, o = add_with_overflow(a, b)
    o && return typemax(Int)
    return r
end
```
-/
def maxValuesUnion (addWithOverflow : I64 → I64 → I64 × Bool) (a b : I64) : I64 :=
  let (r, overflow) := addWithOverflow a b
  if overflow then int (IntTy.max .i64) else r

/--
Julia source: base/abstractset.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max_values(::Type{Bool}) = 2
```
-/
def maxValuesBool : I64 := int 2

/--
Julia source: base/abstractset.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max_values(::Type{Nothing}) = 1
```
-/
def maxValuesNothing : I64 := int 1

def maxValuesDispatch (addWithOverflow : I64 → I64 → I64 × Bool) : JuliaType → I64
  | .other => maxValuesType .other
  | .bitInteger t =>
      if BitIntegerSmall t then maxValuesBitIntegerSmall t else maxValuesType (.bitInteger t)
  | .bool => maxValuesBool
  | .nothing => maxValuesNothing
  | .union a b =>
      maxValuesUnion addWithOverflow
        (maxValuesDispatch addWithOverflow a) (maxValuesDispatch addWithOverflow b)

def unionBangIteratorLoop {α : Type} (o : Calls α) (T : JuliaType) (itr : o.C)
    (xs : List α) (s : o.C) : Except o.Error o.C :=
  match xs with
  | [] => pure s
  | x :: rest => do
      let s ← o.push s x
      if o.subtype (o.elementType itr) T then
        if (← o.length s) == maxValuesDispatch o.addWithOverflow T then
          pure s
        else
          unionBangIteratorLoop o T itr rest s
      else
        unionBangIteratorLoop o T itr rest s

/--
Julia source: base/abstractset.jl:105-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function union!(s::AbstractSet{T}, itr) where T
    haslength(itr) && sizehint!(s, length(s) + Int(length(itr))::Int; shrink = false)
    for x in itr
        push!(s, x)
        eltype(itr) <: T && length(s) == max_values(T) && break
    end
    return s
end
```
-/
def unionBangAbstractSetIterator {α : Type} (o : Calls α) (T : JuliaType)
    (s itr : o.C) : Except o.Error o.C := do
  let s ← if o.hasLength itr then do
    let slen ← o.length s
    let ilen ← o.length itr
    let ilen ← o.intLength ilen
    o.sizehint s (slen + ilen) false
  else
    pure s
  unionBangIteratorLoop o T itr (o.elements itr) s

def unionBangManyLoop {α : Type} (o : Calls α) (s : o.C) (sets : List o.C) :
    Except o.Error o.C :=
  match sets with
  | [] => pure s
  | itr :: itrs => do
      let s ← unionBangAbstractSetIterator o (o.elementType s) s itr
      unionBangManyLoop o s itrs

/--
Julia source: base/abstractset.jl:85-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function union!(s::AbstractSet, sets...)
    for x in sets
        union!(s, x)
    end
    return s
end
```
-/
def unionBangAbstractSetMany {α : Type} (o : Calls α) (s : o.C) (sets : List o.C) :
    Except o.Error o.C :=
  unionBangManyLoop o s sets

/--
Julia source: base/abstractset.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
union(s::AbstractSet) = copy(s)
```
-/
def unionAbstractSetUnary {α : Type} (o : Calls α) (s : o.C) : Except o.Error o.C :=
  o.copy s

/--
Julia source: base/abstractset.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
union(s, sets...) = union!(emptymutable(s, promote_eltype(s, sets...)), s, sets...)
```
-/
def unionGeneric {α : Type} (o : Calls α)
    (unionBang : o.C → List o.C → Except o.Error o.C)
    (s : o.C) (sets : List o.C) : Except o.Error o.C := do
  let ty ← o.promoteEltype s sets
  let out ← o.emptyMutable s ty
  unionBang out (s :: sets)

def unionDispatch {α : Type} (o : Calls α)
    (unionBang : o.C → List o.C → Except o.Error o.C) (s : o.C) :
    Except o.Error o.C :=
  if o.isAbstractSet s then unionAbstractSetUnary o s
  else unionGeneric o unionBang s []
/--
Julia source: base/abstractset.jl:6-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy!(dst::AbstractSet, src::AbstractSet)
    dst === src && return dst
    union!(empty!(dst), src)
end
```
-/
def copyBangAbstractSet {α : Type} (o : Calls α) (same : Bool) (dst src : o.C) : Except o.Error o.C :=
  if same then pure dst else do
    unionBangAbstractSetMany o (← o.empty dst) [src]

def mapfilterLoop {α : Type} (o : Calls α) (pred : α → Except o.Error Bool)
    (f : o.C → α → Except o.Error o.C) (xs : List α) (res : o.C) :
    Except o.Error o.C :=
  match xs with
  | [] => pure res
  | x :: rest => do
      if ← pred x then
        let res ← f res x
        mapfilterLoop o pred f rest res
      else
        mapfilterLoop o pred f rest res

/--
Julia source: base/abstractset.jl:636-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function mapfilter(pred, f, itr, res)
    for x in itr
        pred(x) && f(res, x)
    end
    res
end
```
-/
def mapfilter {α : Type} (o : Calls α) (pred : α → Except o.Error Bool)
    (f : o.C → α → Except o.Error o.C) (itr res : o.C) : Except o.Error o.C :=
  mapfilterLoop o pred f (o.elements itr) res

/--
Julia source: base/abstractset.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect!(s::AbstractSet, s2::AbstractSet) = filter!(in(s2), s)
```
-/
def intersectBangAbstractSetSet {α : Type} (o : Calls α) (s s2 : o.C) : Except o.Error o.C :=
  o.filterBang (fun x => o.member s2 x) s

/--
Julia source: base/abstractset.jl:199-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect!(s::AbstractSet, itr) =
    intersect!(s, union!(emptymutable(s, eltype(itr)), itr))
```
-/
def intersectBangAbstractSetIterator {α : Type} (o : Calls α) (s itr : o.C) :
    Except o.Error o.C := do
  let out ← o.emptyMutable s (o.elementType itr)
  let out ← unionBangAbstractSetIterator o (o.elementType itr) out itr
  intersectBangAbstractSetSet o s out

def intersectBangDispatch {α : Type} (o : Calls α) (s itr : o.C) : Except o.Error o.C :=
  if o.isAbstractSet itr then intersectBangAbstractSetSet o s itr
  else intersectBangAbstractSetIterator o s itr

def intersectBangManyLoop {α : Type} (o : Calls α) (s : o.C) (itrs : List o.C) :
    Except o.Error o.C :=
  match itrs with
  | [] => pure s
  | itr :: rest => do
      let s ← intersectBangDispatch o s itr
      intersectBangManyLoop o s rest

/--
Julia source: base/abstractset.jl:192-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect!(s::AbstractSet, itrs...)
    for x in itrs
        intersect!(s, x)
    end
    return s
end
```
-/
def intersectBangAbstractSetMany {α : Type} (o : Calls α) (s : o.C) (itrs : List o.C) :
    Except o.Error o.C :=
  intersectBangManyLoop o s itrs

/--
Julia source: base/abstractset.jl:174-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(s::AbstractSet, itr)
    if haslength(itr) && hasfastin(itr) && length(s) < length(itr)
        return mapfilter(in(itr), push!, s, emptymutable(s, promote_eltype(s, itr)))
    else
        return mapfilter(in(s), push!, itr, emptymutable(s, promote_eltype(s, itr)))
    end
end
```
-/
def intersectAbstractSetTwo {α : Type} (o : Calls α) (s itr : o.C) : Except o.Error o.C := do
  if o.hasLength itr && o.hasFastIn itr && (← o.length s) < (← o.length itr) then
    mapfilter o (fun x => o.member itr x) o.push s
      (← o.emptyMutable s (← o.promoteEltype s [itr]))
  else
    mapfilter o (fun x => o.member s x) o.push itr
      (← o.emptyMutable s (← o.promoteEltype s [itr]))

def intersectAbstractSetTail {α : Type} (o : Calls α) (s itr : o.C) (itrs : List o.C) :
    Except o.Error o.C := do
  let T ← o.promoteEltype s (itr :: itrs)
  let out ← if o.sameType T (← o.promoteEltype s [itr]) then
    intersectAbstractSetTwo o s itr
  else do
    let out ← o.emptyMutable s T
    let out ← unionBangAbstractSetMany o out [s]
    intersectBangAbstractSetIterator o out itr
  intersectBangAbstractSetMany o out itrs

/--
Julia source: base/abstractset.jl:155-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function intersect(s::AbstractSet, itr, itrs...)
    # heuristics to try to `intersect` with the shortest Set on the left
    if length(s)>50 && haslength(itr) && all(haslength, itrs)
        min_length, min_idx = findmin(length, itrs)
        if length(itr) > min_length
            new_itrs = setindex(itrs, itr, min_idx)
            return intersect(s, itrs[min_idx], new_itrs...)
        end
    end
    T = promote_eltype(s, itr, itrs...)
    if T == promote_eltype(s, itr)
        out = intersect(s, itr)
    else
        out = union!(emptymutable(s, T), s)
        intersect!(out, itr)
    end
    return intersect!(out, itrs...)
end
```
-/
def intersectAbstractSetMany {α : Type} (o : Calls α) (s itr : o.C) (itrs : List o.C)
    (fuel : Nat := itrs.length + 1) : Except o.Error o.C := do
  match fuel with
  | 0 => intersectAbstractSetTail o s itr itrs
  | fuel + 1 =>
      if (← o.length s) > int 50 && o.hasLength itr && itrs.all o.hasLength then
        let (minLength, minIndex) ← o.findminLength itrs
        if (← o.length itr) > minLength then
          let newItrs ← o.setindex itrs itr minIndex
          let first ← o.getindex itrs minIndex
          return ← intersectAbstractSetMany o s first newItrs fuel
      intersectAbstractSetTail o s itr itrs

/--
Julia source: base/abstractset.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(s) = union(s)
```
-/
def intersectUnary {α : Type} (o : Calls α)
    (unionBang : o.C → List o.C → Except o.Error o.C) (s : o.C) : Except o.Error o.C :=
  unionDispatch o unionBang s

def setdiffBangIteratorLoop {α : Type} (o : Calls α) (s : o.C) (xs : List α) :
    Except o.Error o.C :=
  match xs with
  | [] => pure s
  | x :: rest => do
      let s ← o.delete s x
      setdiffBangIteratorLoop o s rest

/--
Julia source: base/abstractset.jl:250-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setdiff!(s::AbstractSet, itr)
    for x in itr
        delete!(s, x)
    end
    return s
end
```
-/
def setdiffBangAbstractSetIterator {α : Type} (o : Calls α) (s itr : o.C) :
    Except o.Error o.C :=
  setdiffBangIteratorLoop o s (o.elements itr)

def setdiffBangManyLoop {α : Type} (o : Calls α) (s : o.C) (itrs : List o.C) :
    Except o.Error o.C :=
  match itrs with
  | [] => pure s
  | itr :: rest => do
      let s ← setdiffBangAbstractSetIterator o s itr
      setdiffBangManyLoop o s rest

/--
Julia source: base/abstractset.jl:244-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setdiff!(s::AbstractSet, itrs...)
    for x in itrs
        setdiff!(s, x)
    end
    return s
end
```
-/
def setdiffBangAbstractSetMany {α : Type} (o : Calls α) (s : o.C) (itrs : List o.C) :
    Except o.Error o.C :=
  setdiffBangManyLoop o s itrs

/--
Julia source: base/abstractset.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setdiff(s::AbstractSet, itrs...) = setdiff!(copymutable(s), itrs...)
```
-/
def setdiffAbstractSetMany {α : Type} (o : Calls α) (s : o.C) (itrs : List o.C) :
    Except o.Error o.C := do
  setdiffBangAbstractSetMany o (← o.copyMutable s) itrs

/--
Julia source: base/abstractset.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setdiff(s) = union(s)
```
-/
def setdiffUnary {α : Type} (o : Calls α)
    (unionBang : o.C → List o.C → Except o.Error o.C) (s : o.C) : Except o.Error o.C :=
  unionDispatch o unionBang s

def symdiffBangSetLoop {α : Type} (o : Calls α) (s : o.C) (xs : List α) :
    Except o.Error o.C :=
  match xs with
  | [] => pure s
  | x :: rest => do
      if ← o.member s x then
        let s ← o.delete s x
        symdiffBangSetLoop o s rest
      else
        let s ← o.push s x
        symdiffBangSetLoop o s rest

/--
Julia source: base/abstractset.jl:299-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function symdiff!(s::AbstractSet, itr::AbstractSet)
    for x in itr
        x in s ? delete!(s, x) : push!(s, x)
    end
    return s
end
```
-/
def symdiffBangAbstractSetSet {α : Type} (o : Calls α) (s itr : o.C) :
    Except o.Error o.C :=
  symdiffBangSetLoop o s (o.elements itr)

/--
Julia source: base/abstractset.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
symdiff!(s::AbstractSet, itr) = symdiff!(s::AbstractSet, Set(itr))
```
-/
def symdiffBangAbstractSetIterator {α : Type} (o : Calls α) (s itr : o.C) :
    Except o.Error o.C := do
  symdiffBangAbstractSetSet o s (← o.makeSet itr)

def symdiffBangDispatch {α : Type} (o : Calls α) (s itr : o.C) : Except o.Error o.C :=
  if o.isAbstractSet itr then symdiffBangAbstractSetSet o s itr
  else symdiffBangAbstractSetIterator o s itr

def symdiffBangManyLoop {α : Type} (o : Calls α) (s : o.C) (itrs : List o.C) :
    Except o.Error o.C :=
  match itrs with
  | [] => pure s
  | itr :: rest => do
      let s ← symdiffBangDispatch o s itr
      symdiffBangManyLoop o s rest

/--
Julia source: base/abstractset.jl:290-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function symdiff!(s::AbstractSet, itrs...)
    for x in itrs
        symdiff!(s, x)
    end
    return s
end
```
-/
def symdiffBangAbstractSetMany {α : Type} (o : Calls α) (s : o.C) (itrs : List o.C) :
    Except o.Error o.C :=
  symdiffBangManyLoop o s itrs

/--
Julia source: base/abstractset.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
symdiff(s, sets...) = symdiff!(emptymutable(s, promote_eltype(s, sets...)), s, sets...)
```
-/
def symdiffGeneric {α : Type} (o : Calls α)
    (symdiffBang : o.C → List o.C → Except o.Error o.C)
    (s : o.C) (sets : List o.C) : Except o.Error o.C := do
  let ty ← o.promoteEltype s sets
  let out ← o.emptyMutable s ty
  symdiffBang out (s :: sets)

/--
Julia source: base/abstractset.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
symdiff(s) = symdiff!(copy(s))
```
-/
def symdiffAbstractSetUnary {α : Type} (o : Calls α)
    (symdiffBang : o.C → List o.C → Except o.Error o.C) (s : o.C) : Except o.Error o.C := do
  symdiffBang (← o.copy s) []

def issubsetElements {α : Type} (o : Calls α) (b : o.C) (xs : List α) :
    Except o.Error Bool :=
  match xs with
  | [] => pure true
  | x :: rest => do
      if ← o.member b x then issubsetElements o b rest else pure false

/--
Julia source: base/abstractset.jl:335-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issubset(a, b)
    if haslength(b) && (isa(a, AbstractSet) || !hasfastin(b))
        blen = length(b) # conditions above make this length computed only when needed
        # check a for too many unique elements
        if isa(a, AbstractSet) && length(a) > blen
            return false
        end
        # when `in` would be too slow and b is big enough, convert it to a Set
        # this threshold was empirically determined (cf. #26198)
        if !hasfastin(b) && blen > FASTIN_SET_THRESHOLD
            return issubset(a, Set(b))
        end
    end
    for elt in a
        elt in b || return false
    end
    return true
end
```
-/
def issubsetSetRight {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  if o.hasLength b && (o.isAbstractSet a || !o.hasFastIn b) then
    let blen ← o.length b
    if o.isAbstractSet a && (← o.length a) > blen then return false
  issubsetElements o b (o.elements a)

def issubset {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  if o.hasLength b && (o.isAbstractSet a || !o.hasFastIn b) then
    let blen ← o.length b
    if o.isAbstractSet a && (← o.length a) > blen then
      return false
    if !o.hasFastIn b && blen > int 70 then
      return ← issubsetSetRight o a (← o.makeSet b)
  issubsetElements o b (o.elements a)

/--
Julia source: base/abstractset.jl:367-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasfastin(::Type) = false
```
-/
def hasFastinTypeDefault (_t : Type) : Bool := false

/--
Julia source: base/abstractset.jl:368-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasfastin(::Union{Type{<:AbstractSet},Type{<:AbstractDict},Type{<:AbstractRange}}) = true
```
-/
def hasFastinSetDictRange (_t : Type) : Bool := true

/--
Julia source: base/abstractset.jl:369-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hasfastin(x) = hasfastin(typeof(x))
```
-/
def hasFastinValue {C T : Type} (hasFastinType : T → Bool) (typeof : C → T) (x : C) : Bool :=
  hasFastinType (typeof x)

/--
Julia source: base/abstractset.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊇(a, b) = b ⊆ a
```
-/
def superset {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool :=
  issubset o b a

/--
Julia source: base/abstractset.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issubset(a) = Fix2(issubset, a)
```
-/
def issubsetFix2 {α : Type} (o : Calls α) (a : o.C) : Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => issubset o x y, a⟩

/--
Julia source: base/abstractset.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊇(a) = Fix2(⊇, a)
```
-/
def supersetFix2 {α : Type} (o : Calls α) (a : o.C) : Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => superset o x y, a⟩

/--
Julia source: base/abstractset.jl:421-421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊊(a::AbstractSet, b::AbstractSet) = length(a) < length(b) && a ⊆ b
```
-/
def properSubsetAbstractSetSet {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  if (← o.length a) < (← o.length b) then issubset o a b else pure false

/--
Julia source: base/abstractset.jl:422-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊊(a::AbstractSet, b) = a ⊊ Set(b)
```
-/
def properSubsetAbstractSetOther {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  properSubsetAbstractSetSet o a (← o.makeSet b)

/--
Julia source: base/abstractset.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊊(a, b::AbstractSet) = Set(a) ⊊ b
```
-/
def properSubsetOtherAbstractSet {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  properSubsetAbstractSetSet o (← o.makeSet a) b

/--
Julia source: base/abstractset.jl:424-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊊(a, b) = Set(a) ⊊ Set(b)
```
-/
def properSubsetOtherOther {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  properSubsetAbstractSetSet o (← o.makeSet a) (← o.makeSet b)

def properSubsetDispatch {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool :=
  if o.isAbstractSet a then
    if o.isAbstractSet b then properSubsetAbstractSetSet o a b
    else properSubsetAbstractSetOther o a b
  else if o.isAbstractSet b then properSubsetOtherAbstractSet o a b
  else properSubsetOtherOther o a b

/--
Julia source: base/abstractset.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊋(a, b) = b ⊊ a
```
-/
def properSuperset {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool :=
  properSubsetDispatch o b a

/--
Julia source: base/abstractset.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊋(a) = Fix2(⊋, a)
```
-/
def properSupersetFix2 {α : Type} (o : Calls α) (a : o.C) :
    Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => properSuperset o x y, a⟩

/--
Julia source: base/abstractset.jl:450-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊊(a) = Fix2(⊊, a)
```
-/
def properSubsetFix2 {α : Type} (o : Calls α) (a : o.C) :
    Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => properSubsetDispatch o x y, a⟩

/--
Julia source: base/abstractset.jl:473-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊈(a, b) = !⊆(a, b)
```
-/
def notSubset {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  return !(← issubset o a b)

/--
Julia source: base/abstractset.jl:474-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊉(a, b) = b ⊈ a
```
-/
def notSuperset {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool :=
  notSubset o b a

/--
Julia source: base/abstractset.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊉(a) = Fix2(⊉, a)
```
-/
def notSupersetFix2 {α : Type} (o : Calls α) (a : o.C) :
    Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => notSuperset o x y, a⟩

/--
Julia source: base/abstractset.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊈(a) = Fix2(⊈, a)
```
-/
def notSubsetFix2 {α : Type} (o : Calls α) (a : o.C) :
    Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => notSubset o x y, a⟩

/--
Julia source: base/abstractset.jl:622-622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::AbstractSet, b::AbstractSet) = length(a) == length(b) && a ⊆ b
```
-/
def setEqualAbstractSet {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  if (← o.length a) == (← o.length b) then issubset o a b else pure false

/--
Julia source: base/abstractset.jl:521-521 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issetequal(a::AbstractSet, b::AbstractSet) = a == b
```
-/
def issetequalAbstractSetSet {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool :=
  setEqualAbstractSet o a b

/--
Julia source: base/abstractset.jl:522-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issetequal(a::AbstractSet, b) = issetequal(a, Set(b))
```
-/
def issetequalAbstractSetOther {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  issetequalAbstractSetSet o a (← o.makeSet b)

/--
Julia source: base/abstractset.jl:524-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issetequal(a, b::AbstractSet)
    if haslength(a)
        # check b for too many unique elements
        length(a) < length(b) && return false
    end
    return issetequal(Set(a), b)
end
```
-/
def issetequalOtherAbstractSet {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  if o.hasLength a && (← o.length a) < (← o.length b) then
    return false
  issetequalAbstractSetSet o (← o.makeSet a) b

/--
Julia source: base/abstractset.jl:532-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issetequal(a, b)
    haslength(a) && return issetequal(a, Set(b))
    haslength(b) && return issetequal(b, Set(a))
    return issetequal(Set(a), Set(b))
end
```
-/
def issetequalOtherOther {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  if o.hasLength a then
    return ← issetequalOtherAbstractSet o a (← o.makeSet b)
  if o.hasLength b then
    return ← issetequalOtherAbstractSet o b (← o.makeSet a)
  issetequalAbstractSetSet o (← o.makeSet a) (← o.makeSet b)

def issetequalDispatch {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool :=
  if o.isAbstractSet a then
    if o.isAbstractSet b then issetequalAbstractSetSet o a b
    else issetequalAbstractSetOther o a b
  else if o.isAbstractSet b then issetequalOtherAbstractSet o a b
  else issetequalOtherOther o a b

/--
Julia source: base/abstractset.jl:549-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issetequal(a) = Fix2(issetequal, a)
```
-/
def issetequalFix2 {α : Type} (o : Calls α) (a : o.C) :
    Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => issetequalDispatch o x y, a⟩

def anyMember {α : Type} (o : Calls α) (b : o.C) (xs : List α) : Except o.Error Bool :=
  match xs with
  | [] => pure false
  | x :: rest => do
      if ← o.member b x then pure true else anyMember o b rest

/--
Julia source: base/abstractset.jl:573-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _isdisjoint(a, b)
        hasfastin(b) && return !any(in(b), a)
        hasfastin(a) && return !any(in(a), b)
        haslength(b) && length(b) < FASTIN_SET_THRESHOLD &&
            return !any(in(b), a)
        return !any(in(Set(b)), a)
    end
```
-/
def isdisjointInner {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  if o.hasFastIn b then return !(← anyMember o b (o.elements a))
  if o.hasFastIn a then return !(← anyMember o a (o.elements b))
  if o.hasLength b && (← o.length b) < int 70 then
    return !(← anyMember o b (o.elements a))
  let setB ← o.makeSet b
  return !(← anyMember o setB (o.elements a))

/--
Julia source: base/abstractset.jl:572-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isdisjoint(a, b)
    function _isdisjoint(a, b)
        hasfastin(b) && return !any(in(b), a)
        hasfastin(a) && return !any(in(a), b)
        haslength(b) && length(b) < FASTIN_SET_THRESHOLD &&
            return !any(in(b), a)
        return !any(in(Set(b)), a)
    end
    if haslength(a) && haslength(b) && length(b) < length(a)
        return _isdisjoint(b, a)
    end
    _isdisjoint(a, b)
end
```
-/
def isdisjoint {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  if o.hasLength a && o.hasLength b && (← o.length b) < (← o.length a) then
    isdisjointInner o b a
  else
    isdisjointInner o a b

/--
Julia source: base/abstractset.jl:610-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_overlapping_range_isdisjoint(a::AbstractRange{T}, b::AbstractRange{T}) where T = invoke(isdisjoint, Tuple{Any,Any}, a, b)
```
-/
def overlappingRangeGeneric {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool :=
  isdisjoint o a b

/--
Julia source: base/abstractset.jl:612-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _overlapping_range_isdisjoint(a::AbstractRange{T}, b::AbstractRange{T}) where T<:Integer
    if abs(step(a)) == abs(step(b))
        return mod(minimum(a), step(a)) != mod(minimum(b), step(a))
    else
        return invoke(isdisjoint, Tuple{Any,Any}, a, b)
    end
end
```
-/
def overlappingRangeInteger {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool := do
  let stepA ← o.step a
  let stepB ← o.step b
  let absA ← o.abs stepA
  let absB ← o.abs stepB
  if o.equal absA absB then
    let minA ← o.minimum a
    let minB ← o.minimum b
    let residueA ← o.mod minA stepA
    let residueB ← o.mod minB stepA
    return !o.equal residueA residueB
  else
    isdisjoint o a b

def overlappingRangeDispatch {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool :=
  if o.isIntegerRange a then overlappingRangeInteger o a b
  else overlappingRangeGeneric o a b

/--
Julia source: base/abstractset.jl:586-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isdisjoint(a::AbstractRange{T}, b::AbstractRange{T}) where T
    (isempty(a) || isempty(b)) && return true
    fa, la = extrema(a)
    fb, lb = extrema(b)
    if (la < fb) | (lb < fa)
        return true
    else
        return _overlapping_range_isdisjoint(a, b)
    end
end
```
-/
def isdisjointRange {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  if o.isEmptyRange a || o.isEmptyRange b then return true
  let (fa, la) ← o.extrema a
  let (fb, lb) ← o.extrema b
  let leftBefore ← o.lessThan la fb
  let rightBefore ← o.lessThan lb fa
  if leftBefore || rightBefore then
    return true
  overlappingRangeDispatch o a b

/--
Julia source: base/abstractset.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdisjoint(a) = Fix2(isdisjoint, a)
```
-/
def isdisjointFix2 {α : Type} (o : Calls α) (a : o.C) :
    Fix2 o.C o.C (Except o.Error Bool) :=
  ⟨fun x y => isdisjoint o x y, a⟩

/--
Julia source: base/abstractset.jl:625-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( a::AbstractSet, b::AbstractSet) = a ⊊ b
```
-/
def lessThanAbstractSet {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool :=
  properSubsetDispatch o a b

/--
Julia source: base/abstractset.jl:626-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(a::AbstractSet, b::AbstractSet) = a ⊆ b
```
-/
def lessEqualAbstractSet {α : Type} (o : Calls α) (a b : o.C) :
    Except o.Error Bool :=
  issubset o a b

/--
Julia source: base/abstractset.jl:630-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter(pred, s::AbstractSet) = mapfilter(pred, push!, s, emptymutable(s))
```
-/
def filterAbstractSet {α : Type} (o : Calls α) (pred : α → Except o.Error Bool) (s : o.C) :
    Except o.Error o.C := do
  mapfilter o pred o.push s (← o.emptyMutableDefault s)

/--
Julia source: base/abstractset.jl:633-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_filter!(pred, s::AbstractSet) = mapfilter(!pred, delete!, s, s)
```
-/
def unsafeFilterAbstractSet {α : Type} (o : Calls α) (pred : α → Except o.Error Bool)
    (s : o.C) : Except o.Error o.C :=
  mapfilter o (fun x => do return !(← pred x)) o.delete s s

end JuliaLean.base.abstractset
