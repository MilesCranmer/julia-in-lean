import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.hashing
import JuliaLean.Runtime.Collections
import JuliaLean.base.set

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
    let empty ← o.empty dst
    unionBangAbstractSetIterator o (o.elementType empty) empty src

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
  if ← (pure (o.hasLength itr && o.hasFastIn itr) <&&>
      do pure ((← o.length s) < (← o.length itr))) then
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
    let out ← unionBangAbstractSetIterator o (o.elementType out) out s
    intersectBangDispatch o out itr
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
    if ← (pure (o.isAbstractSet a) <&&> do pure ((← o.length a) > blen)) then return false
  issubsetElements o b (o.elements a)

def issubset {α : Type} (o : Calls α) (a b : o.C) : Except o.Error Bool := do
  if o.hasLength b && (o.isAbstractSet a || !o.hasFastIn b) then
    let blen ← o.length b
    if ← (pure (o.isAbstractSet a) <&&> do pure ((← o.length a) > blen)) then
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
  if ← (pure (o.hasLength a) <&&> do pure ((← o.length a) < (← o.length b))) then
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
  if ← (pure (o.hasLength b) <&&> do pure ((← o.length b) < int 70)) then
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
  if ← (pure (o.hasLength a && o.hasLength b) <&&>
      do pure ((← o.length b) < (← o.length a))) then
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
  let absA ← o.abs (← o.step a)
  let absB ← o.abs (← o.step b)
  if o.equal absA absB then
    let residueA ← o.mod (← o.minimum a) (← o.step a)
    let residueB ← o.mod (← o.minimum b) (← o.step a)
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

namespace JuliaLean.HashOps

def setHash (values : List Nat) (h : Nat) : Nat :=
  mixNat (values.foldl (fun acc x => Nat.xor acc (mixNat x 0)) 0x852ada37cfe8e0ce) h

end JuliaLean.HashOps

namespace JuliaLean.BitSetsCov.Bugs

inductive RangeOutcome where
  | value (disjoint : Bool)
  | divideError
  deriving DecidableEq

/-- Integer `_overlapping_range_isdisjoint`, `base/abstractset.jl:612-618`:
equal absolute steps compare the minima modulo `step(a)`. -/
def overlappingRangeIsdisjoint (minimumA stepA minimumB stepB : Int) : RangeOutcome :=
  if Int.natAbs stepA = Int.natAbs stepB then
    if stepA = 0 then .divideError
    else .value (decide (minimumA % stepA ≠ minimumB % stepA))
  else .value false

inductive EqValue where
  | positiveZero
  | negativeZero
  | one
  deriving DecidableEq

/-- Julia `==` identifies signed zeros. -/
def valueEq : EqValue → EqValue → Bool
  | .positiveZero, .negativeZero | .negativeZero, .positiveZero => true
  | x, y => decide (x = y)

/-- Julia `isequal` distinguishes signed zeros. -/
def valueIsequal (x y : EqValue) : Bool := decide (x = y)

def anyEqual (eq : EqValue → EqValue → Bool) (a b : List EqValue) : Bool :=
  a.any (fun x => b.any (eq x))

/-- The generic `isdisjoint` path, `base/abstractset.jl:572-584`: short
vectors scan with `in` (`==`); vectors of at least 70 elements are converted
to `Set` and use `isequal`. -/
def isdisjointThreshold (a b : List EqValue) : Bool :=
  if b.length < 70 then !anyEqual valueEq a b else !anyEqual valueIsequal a b

end JuliaLean.BitSetsCov.Bugs

/-!
# `Set`, `AbstractSet`, and `IdSet` source models

The models use natural numbers as equality classes for ordinary `isequal`
sets. `IdValue.identity` is the `===` key used by `IdSet`; its separate
`value` field lets documented value-based operations be stated independently.
Every definition cites the master source path implemented by its branches and
loops.
-/

namespace JuliaLean.BitSetsCov

namespace Coll

open Bugs

def unionOne (s : SetState) (xs : List Nat) : SetState := xs.foldl insert s

def unionMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl unionOne s

def intersectOne (s xs : List Nat) : SetState := s.filter (fun x => decide (x ∈ xs))

def intersectMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl intersectOne s

def setdiffOne (s xs : List Nat) : SetState := xs.foldl erase s

def setdiffMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl setdiffOne s

def symdiffOne (s xs : List Nat) : SetState :=
  (ofList xs).foldl (fun r x => if x ∈ r then erase r x else insert r x) s

def symdiffMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl symdiffOne s

def subset (a b : List Nat) : Bool := a.all (fun x => decide (x ∈ b))

def setequal (a b : List Nat) : Bool := subset a b && subset b a

def properSubset (a b : List Nat) : Bool := decide (a.length < b.length) && subset a b

def disjointEq (eq : Nat → Nat → Bool) (a b : List Nat) : Bool :=
  !a.any (fun x => b.any (eq x))

/-! ## `base/abstractset.jl` -/

/-- Lines 3-4. -/
def abstractEltype (defined : Bool) (declared : Nat) : Nat := if defined then declared else 0
def abstractSizehint (s : SetState) (_n : Int) : SetState := s

/-- Lines 6-9. -/
def abstractCopyBang (same : Bool) (dst src : SetState) : SetState :=
  if same then dst else unionOne [] src

/-- Lines 55-58 and 105-112. -/
def abstractUnion (s : SetState) (sets : List (List Nat)) : SetState :=
  unionMany [] (s :: sets)
def abstractUnionUnary (s : SetState) : SetState := s
def abstractUnionBangMany (s : SetState) (sets : List (List Nat)) : SetState := unionMany s sets
def abstractUnionBangOne (s : SetState) (itr : SetState) (maxValues : Nat)
    (eltypeSubtype : Bool) : SetState :=
  match itr with
  | [] => s
  | x :: xs =>
    let next := insert s x
    if eltypeSubtype && next.length == maxValues then next
    else abstractUnionBangOne next xs maxValues eltypeSubtype

/-- `union!` with fallible element conversion; a failed insertion leaves the
previously inserted elements in the destination. -/
def abstractUnionConvert (convert : Nat → Except JlError Nat) (maxValues : Nat)
    (eltypeSubtype : Bool) (s : SetState) : List Nat → SetState × Option JlError
  | [] => (s, none)
  | x :: xs =>
    match convert x with
    | .error e => (s, some e)
    | .ok y =>
      let next := insert s y
      if eltypeSubtype && next.length == maxValues then (next, none)
      else abstractUnionConvert convert maxValues eltypeSubtype next xs

/-- Lines 92-103. -/
def maxValuesGeneric : Nat := 9223372036854775807
def maxValuesSmall (bytes : Nat) : Nat := 2 ^ (8 * bytes)
def maxValuesUnion (a b : Nat) : Nat :=
  if maxValuesGeneric - a < b then maxValuesGeneric else a + b
def maxValuesBool : Nat := 2
def maxValuesNothing : Nat := 1

/-- Lines 155-180. The first branch models the shortest-set rotation; both
branches then call the two-argument body and fold `intersect!` over `itrs`. -/
def abstractIntersect (s itr : SetState) (itrs : List SetState) : SetState :=
  let candidates := itr :: itrs
  let first := candidates.foldl (fun best x => if x.length < best.length then x else best) itr
  intersectMany (intersectOne s first) (candidates.erase first)
def abstractIntersectUnary (s : SetState) : SetState := abstractUnionUnary s
def abstractIntersectTwo (s itr : SetState) : SetState :=
  if s.length < itr.length then intersectOne s itr else intersectOne itr s
def abstractIntersectBangMany (s : SetState) (itrs : List SetState) : SetState := intersectMany s itrs
def abstractIntersectBangSet (s s2 : SetState) : SetState := intersectOne s s2
def abstractIntersectBangItr (s itr : SetState) : SetState := intersectOne s (ofList itr)

/-- Lines 222-255. -/
def abstractSetdiff (s : SetState) (itrs : List SetState) : SetState := setdiffMany s itrs
def abstractSetdiffUnary (s : SetState) : SetState := abstractUnionUnary s
def abstractSetdiffBangMany (s : SetState) (itrs : List SetState) : SetState := setdiffMany s itrs
def abstractSetdiffBangItr (s itr : SetState) : SetState := setdiffOne s itr

/-- Lines 278-304. -/
def abstractSymdiff (s : SetState) (sets : List SetState) : SetState := symdiffMany [] (s :: sets)
def abstractSymdiffUnary (s : SetState) : SetState := symdiffOne s []
def abstractSymdiffBangMany (s : SetState) (itrs : List SetState) : SetState := symdiffMany s itrs
def abstractSymdiffBangItr (s itr : SetState) : SetState := symdiffOne s (ofList itr)
def abstractSymdiffBangSet (s itr : SetState) : SetState := symdiffOne s itr

/-- Lines 335-369. `fastB` and `setA` are the two source traits. -/
def abstractIssubset (setA fastB : Bool) (a b : SetState) : Bool :=
  if !fastB && b.length > 70 then subset a (ofList b)
  else if setA && a.length > b.length then false
  else subset a b
def hasfastinType (isSetOrDictOrRange : Bool) : Bool := isSetOrDictOrRange
def hasfastinValue (isSetOrDictOrRange : Bool) : Bool := hasfastinType isSetOrDictOrRange

/-- The operator wrappers and curried `Fix2` methods, lines 309-500. -/
def superset (a b : SetState) : Bool := subset b a
def subsetFix (a y : SetState) : Bool := subset y a
def supersetFix (a y : SetState) : Bool := superset y a
def properSuperset (a b : SetState) : Bool := properSubset b a
def properSubsetConverted (a b : List Nat) : Bool := properSubset (ofList a) (ofList b)
def properSupersetFix (a y : SetState) : Bool := properSuperset y a
def properSubsetFix (a y : SetState) : Bool := properSubset y a
def notSubset (a b : SetState) : Bool := !subset a b
def notSuperset (a b : SetState) : Bool := notSubset b a
def notSupersetFix (a y : SetState) : Bool := notSuperset y a
def notSubsetFix (a y : SetState) : Bool := notSubset y a

/-- Lines 521-549. -/
def abstractSetequalSet (a b : SetState) : Bool := setequal a b
def abstractSetequalLeft (a b : List Nat) : Bool := abstractSetequalSet a (ofList b)
def abstractSetequalRight (a b : List Nat) : Bool :=
  if a.length < (ofList b).length then false else abstractSetequalSet (ofList a) b
def abstractSetequalGeneric (a b : List Nat) : Bool := abstractSetequalSet (ofList a) (ofList b)
def abstractSetequalFix (a y : List Nat) : Bool := abstractSetequalGeneric y a

/-- Lines 572-610. This is the ordinary-value analogue of the signed-zero
model in `CollectionBugs`. -/
def abstractIsdisjoint (a b : List Nat) : Bool :=
  if b.length < a.length then disjointEq (fun x y => decide (x = y)) b a
  else if b.length < 70 then disjointEq (fun x y => decide (x = y)) a b
  else disjointEq (fun x y => decide (x = y)) a (ofList b)
def abstractIsdisjointFix (a y : List Nat) : Bool := abstractIsdisjoint y a

structure IntRange where
  first : Int
  step : Int
  len : Nat
  deriving DecidableEq

def rangeValues (r : IntRange) : List Int :=
  (List.range r.len).map (fun (i : Nat) => r.first + r.step * (i : Int))

def rangeDisjoint (a b : IntRange) : RangeOutcome :=
  if a.len = 0 || b.len = 0 then .value true
  else
    let av := rangeValues a
    let bv := rangeValues b
    let amin := av.foldl min a.first
    let bmin := bv.foldl min b.first
    overlappingRangeIsdisjoint amin a.step bmin b.step

def overlappingRangeGeneric (a b : IntRange) : Bool :=
  disjointEq (fun x y => decide (x = y)) ((rangeValues a).map Int.natAbs) ((rangeValues b).map Int.natAbs)

/-- Lines 625-641. -/
def abstractLt (a b : SetState) : Bool := properSubset a b
def abstractLe (a b : SetState) : Bool := subset a b
def mapfilter (pred : Nat → Bool) (f : SetState → Nat → SetState)
    (itr res : SetState) : SetState :=
  itr.foldl (fun out x => if pred x then f out x else out) res
def abstractFilter (pred : Nat → Bool) (s : SetState) : SetState := mapfilter pred insert s []
def abstractUnsafeFilter (pred : Nat → Bool) (s : SetState) : SetState :=
  mapfilter (fun x => !pred x) erase s s

end Coll

end JuliaLean.BitSetsCov

namespace JuliaLean.Dicts

variable {K Q E : Type}

/-- The loop of `union!(s::AbstractSet{T}, itr)`, `base/abstractset.jl:107-110`. -/
def unionLoop (o : KeyOps K) (c : Conv Q K) : SetT K → List Q → DR (SetT K)
  | s, [] => pure s
  | s, x :: xs => do
    let s ← pushConv o c s x
    if c.eltypeSubtype && (s.count : Int) == o.maxValues.val then pure s else unionLoop o c s xs

/-- Historical loop before the iterator element-type check. -/
def unionLoopHistorical (o : KeyOps K) (c : Conv Q K) : SetT K → List Q → DR (SetT K)
  | s, [] => pure s
  | s, x :: xs => do
    let s ← pushConv o c s x
    if (s.count : Int) == o.maxValues.val then pure s else unionLoopHistorical o c s xs

/-- `union!(s::AbstractSet{T}, itr)`, `base/abstractset.jl:105-112`, for an
iterator with a length (a vector or a set, listed in iteration order). -/
def unionBang (o : KeyOps K) (c : Conv Q K) (s : SetT K) (itr : List Q) : DR (SetT K) := do
  let s ← sizehint o s (JInt.lit .i64 (s.count + itr.length)) false
  unionLoop o c s itr

/-- `for x in s; (!keep(x)) && delete!(s, x); end`: the iteration of
`mapfilter(!pred, delete!, s, s)` (`base/abstractset.jl:633-641`) over a set
that is mutated inside the loop. The iteration state is the slot index,
`base/dict.jl:717-723`; `left` bounds the steps (each strictly increases it). -/
def filterLoop (o : KeyOps K) (keep : K → DR Bool) : Nat → SetT K → Nat → DR (SetT K)
  | 0, s, _ => pure s
  | left + 1, s, i =>
    let j := skipDeleted s i
    if j == 0 then pure s else
    match s.keys j with
    | none => throw .undefRef
    | some x => do
      let k ← keep x
      let s ← if !k then setDelete o s x else pure s
      filterLoop o keep left s (j + 1)

/-- `intersect!(s::AbstractSet, s2::AbstractSet) = filter!(in(s2), s)`, `base/abstractset.jl:198`. -/
def intersectBang (o : KeyOps K) (s t : SetT K) : DR (SetT K) :=
  setFilterBang filterLoop o (fun x => setIn o t x) s

/-- `symdiff!(s::AbstractSet, itr::AbstractSet)`, `base/abstractset.jl:299-304`. -/
def symdiffBang (o : KeyOps K) (s t : SetT K) : DR (SetT K) := do
  (← elems t).foldlM (fun s x => do
    if ← setIn o s x then setDelete o s x else push o s x) s

/-- The loop `for elt in a; elt in b || return false; end`, `base/abstractset.jl:348-351`. -/
def allIn (o : KeyOps K) (b : SetT K) : List K → DR Bool
  | [] => pure true
  | x :: xs => do
    if ← setIn o b x then allIn o b xs else pure false

/-- `issubset(a::Set, b::Set)`, `base/abstractset.jl:335-352`: `b` has a length
and `a` is an `AbstractSet`, so `length(a) > length(b)` returns early;
`hasfastin(b)` holds, so `b` is not converted. -/
def issubsetSet (o : KeyOps K) (a b : SetT K) : DR Bool := do
  if a.count > b.count then return false
  allIn o b (← elems a)

/-- `==(a::AbstractSet, b::AbstractSet)`, `base/abstractset.jl:622`. -/
def setEq (o : KeyOps K) (a b : SetT K) : DR Bool := do
  if a.count == b.count then issubsetSet o a b else pure false

/-- `issubset(a::Vector, b::Vector)`, `base/abstractset.jl:335-352`. A vector has
a length and no fast `in` (`hasfastin(::Type{<:Vector}) = false`,
`base/abstractset.jl:367`), so for `length(b) > FASTIN_SET_THRESHOLD = 70` the
call becomes `issubset(a, Set(b))`; otherwise each `elt in b` is
`any(y -> y == elt, b)` with the element `==` (`eqeq`). -/
def issubsetVec (o : KeyOps E) (eqeq : E → E → Bool) (a b : List E) : DR Bool := do
  if b.length > 70 then
    let sb ← setOf unionBang o (Conv.self o) b
    -- issubset(a, Set(b)): hasfastin(Set) holds, so straight to the loop
    allIn o sb a
  else
    pure (a.all fun x => b.any fun y => eqeq y x)

end JuliaLean.Dicts

namespace JuliaLean.IdDicts

/-- `max_values(T)`, base/abstractset.jl:92-103: `typemax(Int)` except
`Nothing` (1); none of the other types of the universe is a small bits type. -/
def maxValues : JTy → Nat
  | .nothing => 1
  | _ => 2 ^ 63 - 1

/-- `union!(s::AbstractSet{T}, itr)`, `base/abstractset.jl:105-112`. The
Boolean records whether the iterator's declared element type is a subtype of `T`.
The `sizehint!` call is a no-op for `IdSet` (`base/idset.jl:85-97`). -/
def IdSet.unionTyped (s : IdSet) (eltypeSubtype : Bool) : List JVal → Out IdSet Unit
  | [] => (s, .ok ())
  | x :: xs =>
    let r := s.push x
    match r.2 with
    | .error e => (r.1, .error e)
    | .ok () =>
      if eltypeSubtype && r.1.length == maxValues s.T then (r.1, .ok ())
      else r.1.unionTyped eltypeSubtype xs

/-- Union with an iterator whose declared element type is `Any`. -/
def IdSet.union (s : IdSet) : List JVal → Out IdSet Unit
  | [] => (s, .ok ())
  | x :: xs =>
    let r := s.push x
    match r.2 with
    | .error e => (r.1, .error e)
    | .ok () =>
      if (s.T == .any) && r.1.length == maxValues s.T then (r.1, .ok ()) else r.1.union xs

/-- `setdiff!(s, itr)`, base/abstractset.jl:250-255. -/
def IdSet.setdiff (s : IdSet) (xs : List JVal) : IdSet := xs.foldl IdSet.delete s

/-- The collections handed to the generic set functions. -/
inductive Coll where
  /-- a `Vector{Any}`: `haslength`, no fast `in`, `in` uses `==` -/
  | vec (xs : List JVal)
  /-- a `Set{Any}` with these (pairwise non-`isequal`) elements -/
  | set (xs : List JVal)
  /-- an `IdSet{Any}` -/
  | ids (s : IdSet)

def Coll.isSet : Coll → Bool
  | .vec _ => false
  | _ => true

/-- `hasfastin`, base/abstractset.jl:367-368 -/
def Coll.hasfastin : Coll → Bool := Coll.isSet

def Coll.length : Coll → Nat
  | .vec xs | .set xs => xs.length
  | .ids s => s.length

/-- Iteration (for an `IdSet{Any}` the `::Any` cast never throws). -/
def Coll.elems : Coll → List JVal
  | .vec xs | .set xs => xs
  | .ids s => s.elems

def Coll.mem : Coll → JVal → Bool
  | .vec xs, x => xs.any (isequal x)
  | .set xs, x => xs.any (isequal x)
  | .ids s, x => s.mem x

/-- The body of `issubset(a, b)`, base/abstractset.jl:335-350, once `b` is
known to have fast `in` (a `Set` or `IdSet`). -/
def issubsetFast (a b : Coll) : Bool :=
  if a.isSet && a.length > b.length then false else a.elems.all b.mem

/-- `issubset(a, b)`, base/abstractset.jl:335-350: a vector `b` longer than
`FASTIN_SET_THRESHOLD = 70` is replaced by `Set(b)` and the call repeated. -/
def issubset (a b : Coll) : Bool :=
  if b.hasfastin then issubsetFast a b
  else if a.isSet && a.length > b.length then false
  else if b.length > 70 then issubsetFast a (.set (jsetOf b.elems))
  else a.elems.all b.mem

/-- `==(a::AbstractSet, b::AbstractSet)`, base/abstractset.jl:622. -/
def setEq (a b : Coll) : Bool := a.length == b.length && issubset a b

/-- `issetequal(a, b)`, base/abstractset.jl:521-536. -/
def issetequal (a b : Coll) : Bool :=
  match a.isSet, b.isSet with
  | true, true => setEq a b
  | true, false => setEq a (.set (jsetOf b.elems))
  | false, true => if a.length < b.length then false else setEq (.set (jsetOf a.elems)) b
  | false, false => setEq (.set (jsetOf a.elems)) (.set (jsetOf b.elems))

/-- `symdiff!(s::AbstractSet, itr::AbstractSet)`, base/abstractset.jl:299-304. -/
def IdSet.symdiffSet (s : IdSet) : List JVal → IdSet
  | [] => s
  | x :: xs => (if s.mem x then s.delete x else (s.push x).1).symdiffSet xs

/-- `symdiff!(s, itr)` for a vector `itr`: `symdiff!(s, Set(itr))`,
base/abstractset.jl:297. -/
def IdSet.symdiffVec (s : IdSet) (xs : List JVal) : IdSet := s.symdiffSet (jsetOf xs)

end JuliaLean.IdDicts
