import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.div
import JuliaLean.base.rounding
import JuliaLean.base.math
import JuliaLean.base.promotion
import JuliaLean.base.operators
import JuliaLean.base.ordering
import JuliaLean.base.number
import JuliaLean.base.range
import JuliaLean.base.abstractarray
import JuliaLean.base.array
import JuliaLean.base.broadcast

import JuliaLean.base.special.cbrt
import JuliaLean.base.hashing
import JuliaLean.base.reinterpretarray
import JuliaLean.base.special.log
/-!
# Source-mirrored model of `base/sort.jl`

Julia revision `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform. Abstract-vector
reads, ordering operations, and finite-iterator operations are typed parameters for interfaces
provided by other Base files. Integer search locals retain Julia's BitInteger widths and promotion.

Recursive loop bounds are model resources. A zero bound can return normally only
when the corresponding Julia loop condition is false; otherwise the installed
operations return `.errorException "fuel"`, a model-exhaustion marker.
-/

namespace JuliaLean.base.sort

open JuliaLean JuliaLean.base
universe u

inductive Error where
  | array (error : array.Error)
  | range (error : range.Exc)
  | tuple (error : tuple.TupleError)
  | broadcast (error : broadcast.Material.Error)
  | style (error : broadcast.Style.StyleError)
  | constructor (error : broadcast.Lazy.Error)
  | julia (error : JlError)
  deriving Repr, DecidableEq

inductive SortException where
  | jl (error : JlError)
  | ordering (error : ordering.OrderingError)
  | errorException (message : String)
  | assertionError (message : String)
  | typeError (message : String)
  | native (error : Error)
  | invalidAccess (index : Int)
  deriving Repr, DecidableEq

abbrev SortResult (α : Type) := Except SortException α

def liftSortJl (result : Jl α) : SortResult α := result.mapError .jl

structure IteratorOps (I A St E : Type) where
  first : I → Except E (Option (A × St))
  next : I → St → Except E (Option (A × St))

def issortedLoop {I A St E : Type} {O : Type u} (iter : IteratorOps I A St E)
    (lt : O → A → A → Except E Bool) (order : O) (itr : I)
    (previous : A) (current : Option (A × St)) : Option (Except E Bool) :=
  match current with
  | none => some (.ok true)
  | some (this, state) =>
    match lt order this previous with
    | .error error => some (.error error)
    | .ok true => some (.ok false)
    | .ok false =>
      match iter.next itr state with
      | .error error => some (.error error)
      | .ok next => issortedLoop iter lt order itr this next
partial_fixpoint
/--
Julia source: base/sort.jl:48-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issorted(itr, order::Ordering)
    y = iterate(itr)
    y === nothing && return true
    prev, state = y
    y = iterate(itr, state)
    while y !== nothing
        this, state = y
        lt(order, this, prev) && return false
        prev = this
        y = iterate(itr, state)
    end
    return true
end
```
-/
def issorted {I A St E : Type} {O : Type u} (iter : IteratorOps I A St E)
    (lt : O → A → A → Except E Bool) (order : O) (itr : I) : Option (Except E Bool) :=
  match iter.first itr with
  | .error error => some (.error error)
  | .ok none => some (.ok true)
  | .ok (some (previous, state)) =>
    match iter.next itr state with
    | .error error => some (.error error)
    | .ok current => issortedLoop iter lt order itr previous current

def iteratorWithOrderingErrors {I A St E : Type} (iter : IteratorOps I A St E) :
    IteratorOps I A St (Sum E ordering.OrderingError) where
  first := fun itr => (iter.first itr).mapError Sum.inl
  next := fun itr state => (iter.next itr state).mapError Sum.inl
/--
Julia source: base/sort.jl:86-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issorted(itr;
        lt=isless, by=identity, rev::Union{Bool,Nothing}=nothing, order::Ordering=Forward)
    # Explicit branching because the compiler can't optimize away the
    # type instability of the `ord` call with Bool `rev` parameter.
    if rev === true
        issorted(itr, ord(lt, by, true, order))
    else
        issorted(itr, ord(lt, by, nothing, order))
    end
end
```
-/
def issortedKeywords {I A K St E : Type} (iter : IteratorOps I A St E)
    (itr : I)
    (less : Sum (K → K → ordering.OrderingResult Bool)
      (K → K → ordering.OrderingResult Bool))
    (byArg : ordering.KeyArg A K) (rev : Option Bool) (order : ordering.OrderArg K) :
    Option (Except (Sum E ordering.OrderingError) Bool) :=
  let resolved := if rev = some true then ordering.ordBool less byArg true order
    else ordering.ordNothing less byArg () order
  match resolved with
  | .error error => some (.error (.inr error))
  | .ok resolved => issorted (iteratorWithOrderingErrors iter)
      (fun o a b => (ordering.ordCompare o a b).mapError Sum.inr) resolved itr

structure SearchIndex where
  ty : IntTy
  word : JInt ty

def searchIndex (ty : IntTy) (value : Int) : SearchIndex :=
  ⟨ty, JInt.wrap ty value⟩

def SearchIndex.val (index : SearchIndex) : Int := index.word.val

def indexAdd (x y : SearchIndex) : SearchIndex :=
  searchIndex (IntTy.promote x.ty y.ty) (x.val + y.val)

def indexSub (x y : SearchIndex) : SearchIndex :=
  searchIndex (IntTy.promote x.ty y.ty) (x.val - y.val)

def indexHalf (x : SearchIndex) : SearchIndex :=
  searchIndex x.ty ((x.val % (2 ^ x.ty.bits)) / 2)

def indexMidpoint (lo hi : SearchIndex) : SearchIndex :=
  indexAdd lo (indexHalf (indexSub hi lo))

inductive SearchResult (α : Type) where
  | returned (value : α)
  | invalidAccess (index : Int)
  | exhausted
  | error (error : SortException)
  deriving Repr, DecidableEq

structure VectorOps (V α : Type) where
  read : V → Int → SortResult α

def arrayVectorOps : VectorOps (Array α) α where
  read := fun v i =>
    if 1 ≤ i ∧ i ≤ v.size then
      match v[i.toNat - 1]? with
      | some value => .ok value
      | none => .error (.invalidAccess i)
    else .error (.invalidAccess i)
def arrayFirstIndex {α : Type} (_v : Array α) : JInt .i64 := JInt.wrap .i64 1

def arrayLastIndex {α : Type} (v : Array α) : JInt .i64 := JInt.wrap .i64 v.size

def firstSearchLoop {V α O : Type} (ops : VectorOps V α)
    (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α) :
    Nat → SearchIndex → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _, _ => .exhausted
  | fuel + 1, lo, hi, len =>
    if len.val = 0 then .returned lo.val else
    let half := indexHalf len
    let m := indexAdd lo half
    match ops.read v m.val with
    | .error (.invalidAccess i) => .invalidAccess i
    | .error error => .error error
    | .ok value =>
      match lt order value x with
      | .error error => .error error
      | .ok true => firstSearchLoop ops lt order v x fuel
          (indexAdd m (searchIndex .i64 1)) hi
          (indexSub len (indexAdd half (searchIndex .i64 1)))
      | .ok false => firstSearchLoop ops lt order v x fuel lo m half

def lastSearchLoop {V α O : Type} (ops : VectorOps V α)
    (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then .returned lo.val else
    let m := indexMidpoint lo hi
    match ops.read v m.val with
    | .error (.invalidAccess i) => .invalidAccess i
    | .error error => .error error
    | .ok value =>
      match lt order x value with
      | .error error => .error error
      | .ok true => lastSearchLoop ops lt order v x u fuel lo m
      | .ok false => lastSearchLoop ops lt order v x u fuel m hi

def equalSearchLoop {V α O : Type} (ops : VectorOps V α)
    (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult (Int × Int)
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then
      .returned ((indexAdd lo (searchIndex .i64 1)).val,
        (indexSub hi (searchIndex .i64 1)).val)
    else
      let m := indexMidpoint lo hi
      match ops.read v m.val with
      | .error (.invalidAccess i) => .invalidAccess i
      | .error error => .error error
      | .ok value =>
        match lt order value x with
        | .error error => .error error
        | .ok true => equalSearchLoop ops lt order v x u fuel m hi
        | .ok false =>
          match lt order x value with
          | .error error => .error error
          | .ok true => equalSearchLoop ops lt order v x u fuel lo m
          | .ok false =>
            let start := indexAdd lo u
            let firstHi := indexAdd m (searchIndex m.ty 1)
            let firstLen := indexSub firstHi start
            match firstSearchLoop ops lt order v x (firstLen.val.toNat + 2) start firstHi firstLen with
            | .error error => .error error
            | .invalidAccess i => .invalidAccess i
            | .exhausted => .exhausted
            | .returned first =>
              let lastLo := indexSub m (searchIndex m.ty 1)
              let lastHi := indexAdd (indexSub hi u) (searchIndex m.ty 1)
              match lastSearchLoop ops lt order v x (searchIndex m.ty 1)
                  ((indexSub lastHi lastLo).val.toNat + 2) lastLo lastHi with
              | .error error => .error error
              | .returned last => .returned (first, last)
              | .invalidAccess i => .invalidAccess i
              | .exhausted => .exhausted

/--
Julia source: base/sort.jl:184-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function searchsortedfirst(v::AbstractVector, x, lo::T, hi::T, o::Ordering)::keytype(v) where T<:Integer
    hi = hi + T(1)
    len = hi - lo
    while len != 0
        half_len = len >>> 0x01
        m = lo + half_len
        if lt(o, @inbounds(v[m]), x)
            lo = m + 1
            len -= half_len + 1
        else
            hi = m
            len = half_len
        end
    end
    return lo
end
```
-/
def searchsortedfirstBounds {V α O : Type} {t : IntTy} (ops : VectorOps V α)
    (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α)
    (lo hi : JInt t) : SearchResult Int :=
  let l : SearchIndex := ⟨t, lo⟩
  let h := indexAdd ⟨t, hi⟩ (searchIndex t 1)
  let len := indexSub h l
  firstSearchLoop ops lt order v x (len.val.toNat + 2) l h len

/--
Julia source: base/sort.jl:203-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function searchsortedlast(v::AbstractVector, x, lo::T, hi::T, o::Ordering)::keytype(v) where T<:Integer
    u = T(1)
    lo = lo - u
    hi = hi + u
    while lo != hi - u
        m = midpoint(lo, hi)
        if lt(o, x, @inbounds(v[m]))
            hi = m
        else
            lo = m
        end
    end
    return lo
end
```
-/
def searchsortedlastBounds {V α O : Type} {t : IntTy} (ops : VectorOps V α)
    (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α)
    (lo hi : JInt t) : SearchResult Int :=
  let u := searchIndex t 1
  let l := indexSub ⟨t, lo⟩ u
  let h := indexAdd ⟨t, hi⟩ u
  lastSearchLoop ops lt order v x u ((indexSub h l).val.toNat + 2) l h

/--
Julia source: base/sort.jl:221-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function searchsorted(v::AbstractVector, x, ilo::T, ihi::T, o::Ordering)::UnitRange{keytype(v)} where T<:Integer
    u = T(1)
    lo = ilo - u
    hi = ihi + u
    while lo != hi - u
        m = midpoint(lo, hi)
        if lt(o, @inbounds(v[m]), x)
            lo = m
        elseif lt(o, x, @inbounds(v[m]))
            hi = m
        else
            a = searchsortedfirst(v, x, lo+u, m, o)
            b = searchsortedlast(v, x, m, hi-u, o)
            return a : b
        end
    end
    return (lo + 1) : (hi - 1)
end
```
-/
def searchsortedBounds {V α O : Type} {t : IntTy} (ops : VectorOps V α)
    (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α)
    (ilo ihi : JInt t) : SearchResult (Int × Int) :=
  let u := searchIndex t 1
  let l := indexSub ⟨t, ilo⟩ u
  let h := indexAdd ⟨t, ihi⟩ u
  equalSearchLoop ops lt order v x u ((indexSub h l).val.toNat + 2) l h


structure RealRangeOps (A R X Q K O E : Type) where
  requireOneBased : A → Except E Unit
  first : A → R
  step : A → R
  last : A → R
  length : A → K
  zeroIndex : K
  oneIndex : K
  increment : K → K
  decrement : K → K
  isZero : R → Bool
  subtract : X → R → Q
  divide : Q → R → Q
  addOne : Q → Q
  roundInteger : Q → Except E K
  get : A → K → Except E R
  finiteSearch : A → X → Prop

structure IntegerRangeOps (A R X Q K O E : Type) where
  requireOneBased : A → Except E Unit
  first : A → R
  step : A → R
  last : A → R
  length : A → K
  zeroIndex : K
  oneIndex : K
  increment : K → K
  isZero : R → Bool
  floorInteger : X → Except E R
  ceilInteger : X → Except E R
  subtract : R → R → R
  fld : R → R → Except E R
  cld : R → R → Except E R
  addOne : R → Q
  toKey : Q → Except E K
  get : A → K → Except E R
  values : A → List R
  indexAsInt : K → Int
  safeDifference : A → X → Prop
  isReverse : O → Bool

/--
Julia source: base/sort.jl:243-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function searchsortedlast(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)::keytype(a)
    require_one_based_indexing(a)
    f, h, l = first(a), step(a), last(a)
    if lt(o, x, f)
        0
    elseif h == 0 || !lt(o, x, l)
        length(a)
    else
        n = round(Integer, (x - f) / h + 1)
        lt(o, x, a[n]) ? n - 1 : n
    end
end
```
-/
def searchsortedlastRealRange {A R X Q K O E : Type}
    (ops : RealRangeOps A R X Q K O E) (lt : O → X → R → Except E Bool)
    (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if ← lt order x f then
    pure ops.zeroIndex
  else if ops.isZero h then
    pure (ops.length a)
  else if !(← lt order x l) then
    pure (ops.length a)
  else
    let quotient := ops.divide (ops.subtract x f) h
    let n ← ops.roundInteger (ops.addOne quotient)
    if ← lt order x (← ops.get a n) then pure (ops.decrement n) else pure n

/--
Julia source: base/sort.jl:256-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function searchsortedfirst(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)::keytype(a)
    require_one_based_indexing(a)
    f, h, l = first(a), step(a), last(a)
    if !lt(o, f, x)
        1
    elseif h == 0 || lt(o, l, x)
        length(a) + 1
    else
        n = round(Integer, (x - f) / h + 1)
        lt(o, a[n], x) ? n + 1 : n
    end
end
```
-/
def searchsortedfirstRealRange {A R X Q K O E : Type}
    (ops : RealRangeOps A R X Q K O E)
    (ltRange : O → R → X → Except E Bool) (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if !(← ltRange order f x) then
    pure ops.oneIndex
  else if ops.isZero h then
    pure (ops.increment (ops.length a))
  else if ← ltRange order l x then
    pure (ops.increment (ops.length a))
  else
    let quotient := ops.divide (ops.subtract x f) h
    let n ← ops.roundInteger (ops.addOne quotient)
    if ← ltRange order (← ops.get a n) x then pure (ops.increment n) else pure n

/--
Julia source: base/sort.jl:269-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function searchsortedlast(a::AbstractRange{<:Integer}, x::Real, o::FastRangeOrderings)::keytype(a)
    require_one_based_indexing(a)
    f, h, l = first(a), step(a), last(a)
    if lt(o, x, f)
        0
    elseif h == 0 || !lt(o, x, l)
        length(a)
    else
        if !(o isa ReverseOrdering)
            fld(floor(Integer, x) - f, h) + 1
        else
            fld(ceil(Integer, x) - f, h) + 1
        end
    end
end
```
-/
def searchsortedlastIntegerRange {A R X Q K O E : Type}
    (ops : IntegerRangeOps A R X Q K O E) (lt : O → X → R → Except E Bool)
    (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if ← lt order x f then
    pure ops.zeroIndex
  else if ops.isZero h then
    pure (ops.length a)
  else if !(← lt order x l) then
    pure (ops.length a)
  else
    let rounded ← if ops.isReverse order then ops.ceilInteger x else ops.floorInteger x
    let quotient ← ops.fld (ops.subtract rounded f) h
    ops.toKey (ops.addOne quotient)

/--
Julia source: base/sort.jl:285-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function searchsortedfirst(a::AbstractRange{<:Integer}, x::Real, o::FastRangeOrderings)::keytype(a)
    require_one_based_indexing(a)
    f, h, l = first(a), step(a), last(a)
    if !lt(o, f, x)
        1
    elseif h == 0 || lt(o, l, x)
        length(a) + 1
    else
        if !(o isa ReverseOrdering)
            cld(ceil(Integer, x) - f, h) + 1
        else
            cld(floor(Integer, x) - f, h) + 1
        end
    end
end
```
-/
def searchsortedfirstIntegerRange {A R X Q K O E : Type}
    (ops : IntegerRangeOps A R X Q K O E)
    (ltRange : O → R → X → Except E Bool) (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if !(← ltRange order f x) then
    pure ops.oneIndex
  else if ops.isZero h then
    pure (ops.increment (ops.length a))
  else if ← ltRange order l x then
    pure (ops.increment (ops.length a))
  else
    let rounded ← if ops.isReverse order then ops.floorInteger x else ops.ceilInteger x
    let quotient ← ops.cld (ops.subtract rounded f) h
    ops.toKey (ops.addOne quotient)

/--
Julia source: base/sort.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
searchsorted(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings) =
    searchsortedfirst(a, x, o) : searchsortedlast(a, x, o)
```
-/
def searchsortedRealRange {A R X Q K O E U : Type}
    (ops : RealRangeOps A R X Q K O E) (lt : O → X → R → Except E Bool)
    (ltRange : O → R → X → Except E Bool) (order : O) (a : A)
    (x : X) (unitRange : K → K → U) : Except E U := do
  let first ← searchsortedfirstRealRange ops ltRange order a x
  let last ← searchsortedlastRealRange ops lt order a x
  pure (unitRange first last)

/--
Julia source: base/sort.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
searchsorted(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings) =
    searchsortedfirst(a, x, o) : searchsortedlast(a, x, o)
```
-/
def searchsortedIntegerRange {A R X Q K O E U : Type}
    (ops : IntegerRangeOps A R X Q K O E) (lt : O → X → R → Except E Bool)
    (ltRange : O → R → X → Except E Bool) (order : O) (a : A)
    (x : X) (unitRange : K → K → U) : Except E U := do
  let first ← searchsortedfirstIntegerRange ops ltRange order a x
  let last ← searchsortedlastIntegerRange ops lt order a x
  pure (unitRange first last)

/--
Julia source: base/sort.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $s(v::AbstractVector, x, o::Ordering) = $s(v,x,firstindex(v),lastindex(v),o)
```
-/
def searchsortedfirstOrdering {V α O : Type} {t : IntTy} (ops : VectorOps V α)
    (firstIndex lastIndex : V → JInt t) (lt : O → α → α → SortResult Bool)
    (v : V) (x : α) (order : O) : SearchResult Int :=
  searchsortedfirstBounds ops lt order v x (firstIndex v) (lastIndex v)

/--
Julia source: base/sort.jl:307-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $s(v::AbstractVector, x;
           lt=isless, by=identity, rev::Union{Bool,Nothing}=nothing, order::Ordering=Forward) =
            $s(v,x,ord(lt,by,rev,order))
```
-/
def searchsortedfirstKeywords {V α L B O : Type} {t : IntTy} (ops : VectorOps V α)
    (firstIndex lastIndex : V → JInt t)
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → SortResult Bool)
    (v : V) (x : α) (less : L) (byFn : B) (rev : Option Bool) (order : O) :
    SearchResult Int :=
  searchsortedfirstOrdering ops firstIndex lastIndex lt v x (orderOf less byFn rev order)

/--
Julia source: base/sort.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $s(v::AbstractVector, x, o::Ordering) = $s(v,x,firstindex(v),lastindex(v),o)
```
-/
def searchsortedlastOrdering {V α O : Type} {t : IntTy} (ops : VectorOps V α)
    (firstIndex lastIndex : V → JInt t) (lt : O → α → α → SortResult Bool)
    (v : V) (x : α) (order : O) : SearchResult Int :=
  searchsortedlastBounds ops lt order v x (firstIndex v) (lastIndex v)

/--
Julia source: base/sort.jl:307-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $s(v::AbstractVector, x;
           lt=isless, by=identity, rev::Union{Bool,Nothing}=nothing, order::Ordering=Forward) =
            $s(v,x,ord(lt,by,rev,order))
```
-/
def searchsortedlastKeywords {V α L B O : Type} {t : IntTy} (ops : VectorOps V α)
    (firstIndex lastIndex : V → JInt t)
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → SortResult Bool)
    (v : V) (x : α) (less : L) (byFn : B) (rev : Option Bool) (order : O) :
    SearchResult Int :=
  searchsortedlastOrdering ops firstIndex lastIndex lt v x (orderOf less byFn rev order)

/--
Julia source: base/sort.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $s(v::AbstractVector, x, o::Ordering) = $s(v,x,firstindex(v),lastindex(v),o)
```
-/
def searchsortedOrdering {V α O : Type} {t : IntTy} (ops : VectorOps V α)
    (firstIndex lastIndex : V → JInt t) (lt : O → α → α → SortResult Bool)
    (v : V) (x : α) (order : O) : SearchResult (Int × Int) :=
  searchsortedBounds ops lt order v x (firstIndex v) (lastIndex v)

/--
Julia source: base/sort.jl:307-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $s(v::AbstractVector, x;
           lt=isless, by=identity, rev::Union{Bool,Nothing}=nothing, order::Ordering=Forward) =
            $s(v,x,ord(lt,by,rev,order))
```
-/
def searchsortedKeywords {V α L B O : Type} {t : IntTy} (ops : VectorOps V α)
    (firstIndex lastIndex : V → JInt t)
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → SortResult Bool)
    (v : V) (x : α) (less : L) (byFn : B) (rev : Option Bool) (order : O) :
    SearchResult (Int × Int) :=
  searchsortedOrdering ops firstIndex lastIndex lt v x (orderOf less byFn rev order)

/--
Julia source: base/sort.jl:465-465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
insorted(x, v::AbstractVector; kw...) = !isempty(searchsorted(v, x; kw...))
```
-/
def insortedVector {V α L B O : Type} {t : IntTy} (ops : VectorOps V α)
    (firstIndex lastIndex : V → JInt t)
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → SortResult Bool)
    (v : V) (x : α) (less : L) (byFn : B) (rev : Option Bool) (order : O) :
    SearchResult Bool :=
  match searchsortedKeywords ops firstIndex lastIndex orderOf lt v x less byFn rev order with
  | .returned (first, last) => .returned (first ≤ last)
  | .invalidAccess index => .invalidAccess index
  | .error error => .error error
  | .exhausted => .exhausted

/--
Julia source: base/sort.jl:466-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
insorted(x, r::AbstractRange) = in(x, r)
```
-/
def insortedRange {R X : Type} (contains : X → R → SortResult Bool) (x : X) (range : R) : SortResult Bool :=
  contains x range


structure ScratchOps (V W E : Type) where
  allocate : Nat → Except E V
  length : V → Nat
  resize : V → Nat → Except E V
  sizeofBacking : Nat
  multiply : Nat → Nat → Nat
  divide : Nat → Nat → Except E Nat
  reinterpret : Nat → V → Except E W
  viewLength : W → Nat
  allocateLength : ∀ n v, allocate n = .ok v → length v = n
  resizeLength : ∀ v n v', resize v n = .ok v' → length v' = max (length v) n
  reinterpretBytes : ∀ targetBytes v w, reinterpret targetBytes v = .ok w →
    targetBytes * viewLength w = length v * sizeofBacking
  multiplyEq : ∀ a b, multiply a b = a * b
  divideEq : ∀ a b q, divide a b = .ok q → 0 < b ∧ q = a / b

/--
Julia source: base/sort.jl:503-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_scratch(scratch::Nothing, T::Type, len::Integer)
    s = Vector{T}(undef, len)
    s, s
end
```
-/
def makeScratchNothing {V W E : Type} (ops : ScratchOps V W E) (len : Nat) :
    Except E (V × V) := do
  let scratch ← ops.allocate len
  pure (scratch, scratch)

/--
Julia source: base/sort.jl:507-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_scratch(scratch::Vector{T}, ::Type{T}, len::Integer) where T
    len > length(scratch) && resize!(scratch, len)
    scratch, scratch
end
```
-/
def makeScratchSame {V W E : Type} (ops : ScratchOps V W E)
    (scratch : V) (len : Nat) : Except E (V × V) := do
  let scratch ← if len > ops.length scratch then ops.resize scratch len else pure scratch
  pure (scratch, scratch)

/--
Julia source: base/sort.jl:511-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_scratch(scratch::Vector, T::Type, len::Integer)
    len_bytes = len * sizeof(T)
    len_scratch = div(len_bytes, sizeof(eltype(scratch)))
    len_scratch > length(scratch) && resize!(scratch, len_scratch)
    scratch, reinterpret(T, scratch)
end
```
-/
def makeScratchOther {V W E : Type} (ops : ScratchOps V W E)
    (scratch : V) (targetBytes len : Nat) : Except E (V × W) := do
  let lenBytes := ops.multiply len targetBytes
  let lenScratch ← ops.divide lenBytes ops.sizeofBacking
  let scratch ← if lenScratch > ops.length scratch then ops.resize scratch lenScratch else pure scratch
  let view ← ops.reinterpret targetBytes scratch
  pure (scratch, view)

structure SendToEndOps (m : Type → Type) (V α K : Type) where
  get : V → K → m α
  set : V → α → K → m Unit
  firstIndex : V → K
  lastIndex : V → K
  lessEq : K → K → Bool
  next : K → K
  previous : K → K
  distance : K → K → Nat
  reverseView : V → K → K → m V
  add : K → K → K
  subtract : K → K → K
  modelExhausted : {β : Type} → m β

def sendToEndFirstScan [Monad m] (ops : SendToEndOps m V α K)
    (predicate : α → m Bool) (v : V) (hi : K) : Nat → K → m K
  | 0, i => if ops.lessEq i hi then ops.modelExhausted else pure i
  | fuel + 1, i =>
    if ops.lessEq i hi then do
      let value ← ops.get v i
      let sent ← predicate value
      if sent then pure i
      else sendToEndFirstScan ops predicate v hi fuel (ops.next i)
    else pure i

def sendToEndSecondScan [Monad m] (ops : SendToEndOps m V α K)
    (predicate : α → m Bool) (v : V) (hi : K) : Nat → K → K → m K
  | 0, i, j => if ops.lessEq j hi then ops.modelExhausted else pure i
  | fuel + 1, i, j =>
    if ops.lessEq j hi then do
      let value ← ops.get v j
      let sent ← predicate value
      if sent then
        sendToEndSecondScan ops predicate v hi fuel i (ops.next j)
      else
        let current ← ops.get v j
        let previous ← ops.get v i
        ops.set v current i
        ops.set v previous j
        sendToEndSecondScan ops predicate v hi fuel (ops.next i) (ops.next j)
    else pure i

/--
Julia source: base/sort.jl:620-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function send_to_end!(f::F, v::AbstractVector; lo=firstindex(v), hi=lastindex(v)) where F <: Function
    i = lo
    @inbounds while i <= hi && !f(v[i])
        i += 1
    end
    j = i + 1
    @inbounds while j <= hi
        if !f(v[j])
            v[i], v[j] = v[j], v[i]
            i += 1
        end
        j += 1
    end
    i - 1
end
```
-/
def sendToEndBang [Monad m] (ops : SendToEndOps m V α K)
    (predicate : α → m Bool) (v : V) (lo? hi? : Option K := none) : m K := do
  let lo := match lo? with
    | none => ops.firstIndex v
    | some index => index
  let hi := match hi? with
    | none => ops.lastIndex v
    | some index => index
  let i ← sendToEndFirstScan ops predicate v hi (ops.distance lo hi + 1) lo
  let j := ops.next i
  let i ← sendToEndSecondScan ops predicate v hi (ops.distance j hi + 1) i j
  pure (ops.previous i)

/--
Julia source: base/sort.jl:645-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline send_to_end!(f::F, v::AbstractVector, ::ForwardOrdering, end_stable=false; lo, hi) where F <: Function =
    end_stable ? (lo, hi-send_to_end!(!f, view(v, hi:-1:lo))) : (lo, send_to_end!(f, v; lo, hi))
```
-/
def sendToEndForwardOrdering [Monad m] (ops : SendToEndOps m V α K)
    (predicate : α → m Bool) (v : V) (endStable : Bool) (lo hi : K) : m (K × K) := do
  if endStable then
    let view ← ops.reverseView v hi lo
    let endIndex ← sendToEndBang ops (fun x => do pure (!(← predicate x))) view
    pure (lo, ops.subtract hi endIndex)
  else
    let endIndex ← sendToEndBang ops predicate v (some lo) (some hi)
    pure (lo, endIndex)

/--
Julia source: base/sort.jl:647-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline send_to_end!(f::F, v::AbstractVector, ::ReverseOrdering, end_stable=false; lo, hi) where F <: Function =
    end_stable ? (send_to_end!(!f, v; lo, hi)+1, hi) : (hi-send_to_end!(f, view(v, hi:-1:lo))+1, hi)
```
-/
def sendToEndReverseOrdering [Monad m] (ops : SendToEndOps m V α K)
    (predicate : α → m Bool) (v : V) (endStable : Bool) (lo hi : K) : m (K × K) := do
  if endStable then
    let startIndex ← sendToEndBang ops (fun x => do pure (!(← predicate x))) v (some lo) (some hi)
    pure (ops.next startIndex, hi)
  else
    let view ← ops.reverseView v hi lo
    let endIndex ← sendToEndBang ops predicate view
    pure (ops.next (ops.subtract hi endIndex), hi)

structure WithoutMissingVector (α V : Type) where
  data : V

inductive KeywordValue (A : Type) where
  | valid (value : A)
  | missing
  | wrongType

inductive SortError (E : Type) where
  | callee (error : E)
  | julia (error : JlError)
  | typeError (keyword : String)
  | assertionError (message : String)
  deriving Repr

abbrev Result (E A : Type) := Except (SortError E) A

/--
Julia source: base/sort.jl:591-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function WithoutMissingVector(data; unsafe=false)
        if !unsafe && any(ismissing, data)
            throw(ArgumentError("data must not contain missing values"))
        end
        new{nonmissingtype(eltype(data)), typeof(data)}(data)
    end
```
-/
def withoutMissingVector {V A E : Type} (anyMissing : V → Result E Bool)
    (data : V) (unsafeMode : Bool := false) :
    Result E (WithoutMissingVector A V) := do
  if !unsafeMode then
    if ← anyMissing data then
      throw (.julia (.argumentError "data must not contain missing values"))
  pure ⟨data⟩

/--
Julia source: base/sort.jl:598-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function Base.getindex(v::WithoutMissingVector, i::Integer)
    out = v.data[i]
    @assert !(out isa Missing) "encountered `missing` in WithoutMissingVector"
    out::eltype(v)
end
```
-/
def withoutMissingGet {V α I E : Type} (get : V → I → Except E (Option α))
    (assertionError : String → E) (v : WithoutMissingVector α V) (i : I) :
    Except E α := do
  let out ← get v.data i
  match out with
  | none => .error (assertionError "encountered `missing` in WithoutMissingVector")
  | some value => pure value

/--
Julia source: base/sort.jl:603-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function Base.setindex!(v::WithoutMissingVector, x, i::Integer)
    v.data[i] = x
    v
end
```
-/
def withoutMissingSet {V α X I E : Type} (set : V → X → I → Except E V)
    (v : WithoutMissingVector α V) (x : X) (i : I) : Except E (WithoutMissingVector α V) := do
  let data ← set v.data x i
  pure ⟨data⟩

/--
Julia source: base/sort.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.size(v::WithoutMissingVector) = size(v.data)
```
-/
def withoutMissingSize {V S : Type} (size : V → S) (v : WithoutMissingVector α V) : S :=
  size v.data

/--
Julia source: base/sort.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.axes(v::WithoutMissingVector) = axes(v.data)
```
-/
def withoutMissingAxes {V A : Type} (axes : V → A) (v : WithoutMissingVector α V) : A :=
  axes v.data

inductive KwExpr where
  | name (value : String)
  | call (function : String) (arguments : List KwExpr)
  | tuple (values : List KwExpr)
  | assign (left right : KwExpr)
  | escape (body : KwExpr)
  | block (body : List KwExpr)
  deriving Repr

/--
Julia source: base/sort.jl:470-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro getkw(syms...)
    getters = (getproperty(Sort, Symbol(:_, sym)) for sym in syms)
    Expr(:block, (:($(esc(:((kw, $sym) = $getter(v, o, kw))))) for (sym, getter) in zip(syms, getters))...)
end
```
-/
def getkw (symbols : List String) : KwExpr :=
  .block (symbols.map fun symbol =>
    .escape (.assign (.tuple [.name "kw", .name symbol])
      (.call ("_" ++ symbol) [.name "v", .name "o", .name "kw"])))

structure SortKeywords (K A Backing Alg Tail : Type) where
  lo : Option (KeywordValue K) := none
  hi : Option (KeywordValue K) := none
  mn : Option (KeywordValue A) := none
  mx : Option (KeywordValue A) := none
  scratch : Option (KeywordValue (Option Backing)) := none
  legacyDispatchEntry : Option (KeywordValue (Option Alg)) := none
  tail : Tail

def assertKeyword {E A : Type} (name : String) : KeywordValue A → Result E A
  | .valid value => .ok value
  | .wrongType => .error (.typeError name)
  | .missing => .error (.typeError name)

def lookupKeyword {A : Type} : Option (KeywordValue A) → Option (KeywordValue A)
  | none => none
  | some .missing => none
  | some value => some value

/--
Julia source: base/sort.jl:483-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function $usym(v, o, kw)
        # using missing instead of nothing because scratch could === nothing.
        res = get(kw, $(Expr(:quote, sym)), missing)
        res !== missing && return kw, res::$type
        $sym = $exp
        (;kw..., $sym), $sym::$type
    end
```
-/
def generatedKeywordGetter {W Input Output V E : Type} {O : Type u}
    (lookup : W → Option Input) (append : W → Input → W)
    (default : V → O → Result E Input) (assertType : Input → Result E Output)
    (keywords : W) (v : V) (order : O) : Result E (W × Output) := do
  match lookup keywords with
  | some value =>
    let typed ← assertType value
    pure (keywords, typed)
  | none =>
    let value ← default v order
    let appended := append keywords value
    let typed ← assertType value
    pure (appended, typed)

/--
Julia source: base/sort.jl:475-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (sym, exp, type) in [
        (:lo, :(firstindex(v)), Integer),
        (:hi, :(lastindex(v)),  Integer),
        (:mn, :(throw(ArgumentError("mn is needed but has not been computed"))), :(eltype(v))),
        (:mx, :(throw(ArgumentError("mx is needed but has not been computed"))), :(eltype(v))),
        (:scratch, nothing, :(Union{Nothing, Vector})), # could have different eltype
        (:legacy_dispatch_entry, nothing, Union{Nothing, Algorithm})]
    usym = Symbol(:_, sym)
    @eval function $usym(v, o, kw)
        # using missing instead of nothing because scratch could === nothing.
        res = get(kw, $(Expr(:quote, sym)), missing)
        res !== missing && return kw, res::$type
        $sym = $exp
        (;kw..., $sym), $sym::$type
    end
end
```
-/
def getLo {V K A Backing Alg Tail E : Type} {O : Type u}
    (firstindex : V → Result E K)
    (v : V) (order : O) (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × K) :=
  generatedKeywordGetter (fun kw => lookupKeyword kw.lo) (fun kw value => { kw with lo := some value })
    (fun v _ => return .valid (← firstindex v)) (assertKeyword "lo") kw v order

/--
Julia source: base/sort.jl:475-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (sym, exp, type) in [
        (:lo, :(firstindex(v)), Integer),
        (:hi, :(lastindex(v)),  Integer),
        (:mn, :(throw(ArgumentError("mn is needed but has not been computed"))), :(eltype(v))),
        (:mx, :(throw(ArgumentError("mx is needed but has not been computed"))), :(eltype(v))),
        (:scratch, nothing, :(Union{Nothing, Vector})), # could have different eltype
        (:legacy_dispatch_entry, nothing, Union{Nothing, Algorithm})]
    usym = Symbol(:_, sym)
    @eval function $usym(v, o, kw)
        # using missing instead of nothing because scratch could === nothing.
        res = get(kw, $(Expr(:quote, sym)), missing)
        res !== missing && return kw, res::$type
        $sym = $exp
        (;kw..., $sym), $sym::$type
    end
end
```
-/
def getHi {V K A Backing Alg Tail E : Type} {O : Type u}
    (lastindex : V → Result E K)
    (v : V) (order : O) (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × K) :=
  generatedKeywordGetter (fun kw => lookupKeyword kw.hi) (fun kw value => { kw with hi := some value })
    (fun v _ => return .valid (← lastindex v)) (assertKeyword "hi") kw v order

/--
Julia source: base/sort.jl:475-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (sym, exp, type) in [
        (:lo, :(firstindex(v)), Integer),
        (:hi, :(lastindex(v)),  Integer),
        (:mn, :(throw(ArgumentError("mn is needed but has not been computed"))), :(eltype(v))),
        (:mx, :(throw(ArgumentError("mx is needed but has not been computed"))), :(eltype(v))),
        (:scratch, nothing, :(Union{Nothing, Vector})), # could have different eltype
        (:legacy_dispatch_entry, nothing, Union{Nothing, Algorithm})]
    usym = Symbol(:_, sym)
    @eval function $usym(v, o, kw)
        # using missing instead of nothing because scratch could === nothing.
        res = get(kw, $(Expr(:quote, sym)), missing)
        res !== missing && return kw, res::$type
        $sym = $exp
        (;kw..., $sym), $sym::$type
    end
end
```
-/
def getMn {V K A Backing Alg Tail E : Type} {O : Type u}
    (v : V) (order : O) (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × A) :=
  generatedKeywordGetter (fun kw => lookupKeyword kw.mn) (fun kw value => { kw with mn := some value })
    (fun _ _ => .error (.julia (.argumentError "mn is needed but has not been computed"))) (assertKeyword "mn") kw v order

/--
Julia source: base/sort.jl:475-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (sym, exp, type) in [
        (:lo, :(firstindex(v)), Integer),
        (:hi, :(lastindex(v)),  Integer),
        (:mn, :(throw(ArgumentError("mn is needed but has not been computed"))), :(eltype(v))),
        (:mx, :(throw(ArgumentError("mx is needed but has not been computed"))), :(eltype(v))),
        (:scratch, nothing, :(Union{Nothing, Vector})), # could have different eltype
        (:legacy_dispatch_entry, nothing, Union{Nothing, Algorithm})]
    usym = Symbol(:_, sym)
    @eval function $usym(v, o, kw)
        # using missing instead of nothing because scratch could === nothing.
        res = get(kw, $(Expr(:quote, sym)), missing)
        res !== missing && return kw, res::$type
        $sym = $exp
        (;kw..., $sym), $sym::$type
    end
end
```
-/
def getMx {V K A Backing Alg Tail E : Type} {O : Type u}
    (v : V) (order : O) (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × A) :=
  generatedKeywordGetter (fun kw => lookupKeyword kw.mx) (fun kw value => { kw with mx := some value })
    (fun _ _ => .error (.julia (.argumentError "mx is needed but has not been computed"))) (assertKeyword "mx") kw v order

/--
Julia source: base/sort.jl:475-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (sym, exp, type) in [
        (:lo, :(firstindex(v)), Integer),
        (:hi, :(lastindex(v)),  Integer),
        (:mn, :(throw(ArgumentError("mn is needed but has not been computed"))), :(eltype(v))),
        (:mx, :(throw(ArgumentError("mx is needed but has not been computed"))), :(eltype(v))),
        (:scratch, nothing, :(Union{Nothing, Vector})), # could have different eltype
        (:legacy_dispatch_entry, nothing, Union{Nothing, Algorithm})]
    usym = Symbol(:_, sym)
    @eval function $usym(v, o, kw)
        # using missing instead of nothing because scratch could === nothing.
        res = get(kw, $(Expr(:quote, sym)), missing)
        res !== missing && return kw, res::$type
        $sym = $exp
        (;kw..., $sym), $sym::$type
    end
end
```
-/
def getScratch {V K A Backing Alg Tail E : Type} {O : Type u}
    (v : V) (order : O) (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × (Option Backing)) :=
  generatedKeywordGetter (fun kw => lookupKeyword kw.scratch) (fun kw value => { kw with scratch := some value })
    (fun _ _ => .ok (.valid none)) (assertKeyword "scratch") kw v order

/--
Julia source: base/sort.jl:475-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (sym, exp, type) in [
        (:lo, :(firstindex(v)), Integer),
        (:hi, :(lastindex(v)),  Integer),
        (:mn, :(throw(ArgumentError("mn is needed but has not been computed"))), :(eltype(v))),
        (:mx, :(throw(ArgumentError("mx is needed but has not been computed"))), :(eltype(v))),
        (:scratch, nothing, :(Union{Nothing, Vector})), # could have different eltype
        (:legacy_dispatch_entry, nothing, Union{Nothing, Algorithm})]
    usym = Symbol(:_, sym)
    @eval function $usym(v, o, kw)
        # using missing instead of nothing because scratch could === nothing.
        res = get(kw, $(Expr(:quote, sym)), missing)
        res !== missing && return kw, res::$type
        $sym = $exp
        (;kw..., $sym), $sym::$type
    end
end
```
-/
def getLegacyDispatchEntry {V K A Backing Alg Tail E : Type} {O : Type u}
    (v : V) (order : O) (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × (Option Alg)) :=
  generatedKeywordGetter (fun kw => lookupKeyword kw.legacyDispatchEntry)
    (fun kw value => { kw with legacyDispatchEntry := some value })
    (fun _ _ => .ok (.valid none)) (assertKeyword "legacy_dispatch_entry") kw v order

def getBounds {V K A Backing Alg Tail E : Type} {O : Type u}
    (firstindex lastindex : V → Result E K) (v : V) (order : O)
    (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × K × K) := do
  let (kw, lo) ← getLo firstindex v order kw
  let (kw, hi) ← getHi lastindex v order kw
  pure (kw, lo, hi)

def getBoundsAndScratch {V K A Backing Alg Tail E : Type} {O : Type u}
    (firstindex lastindex : V → Result E K) (v : V) (order : O)
    (kw : SortKeywords K A Backing Alg Tail) :
    Result E (SortKeywords K A Backing Alg Tail × K × K × Option Backing) := do
  let (kw, lo, hi) ← getBounds firstindex lastindex v order kw
  let (kw, scratch) ← getScratch v order kw
  pure (kw, lo, hi, scratch)

def appendBounds {K A Backing Alg Tail : Type} (kw : SortKeywords K A Backing Alg Tail)
    (lo hi : K) : SortKeywords K A Backing Alg Tail :=
  { kw with lo := some (.valid lo), hi := some (.valid hi) }

def appendExtrema {K A Backing Alg Tail : Type} (kw : SortKeywords K A Backing Alg Tail)
    (mn mx : A) : SortKeywords K A Backing Alg Tail :=
  { kw with mn := some (.valid mn), mx := some (.valid mx) }

structure IntegerIndexOps (K : Type) where
  addOne : K → K
  previous : K → K
  range : K → K → List K
  less : K → K → Bool

abbrev Run (E A : Type) := ExceptT E Option A

def liftExcept {E A : Type} (result : Except E A) : Run E A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

structure WindowOps (V L H Start Bounds Window Index State Previous A E : Type) where
  bounds : L → H → Run E Bounds
  checkBounds : V → Bounds → Run E Unit
  addOne : L → Start
  window : Start → H → Run E Window
  first : Window → Run E (Option (Index × State))
  next : Window → State → Run E (Option (Index × State))
  getCurrent : V → Index → Run E A
  previous : Index → Previous
  getPrevious : V → Previous → Run E A

def issortedWindowLoop {V L H Start Bounds Window Index State Previous A E Key : Type}
    (ops : WindowOps V L H Start Bounds Window Index State Previous A E)
    (v : V) (window : Window) (order : ordering.OrdResult A Key)
    (current : Option (Index × State)) : Option (Except (Sum E ordering.OrderingError) Bool) :=
  match current with
  | none => some (.ok true)
  | some (i, state) =>
    match (ops.getCurrent v i).run with
    | none => none
    | some (.error error) => some (.error (.inl error))
    | some (.ok this) =>
      match (ops.getPrevious v (ops.previous i)).run with
      | none => none
      | some (.error error) => some (.error (.inl error))
      | some (.ok previous) =>
        match ordering.ordCompare order this previous with
        | .error error => some (.error (.inr error))
        | .ok true => some (.ok false)
        | .ok false =>
          match (ops.next window state).run with
          | none => none
          | some (.error error) => some (.error (.inl error))
          | some (.ok next) => issortedWindowLoop ops v window order next
partial_fixpoint

/--
Julia source: base/sort.jl:1445-1451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _issorted(v::AbstractVector, lo::Integer, hi::Integer, o::Ordering)
    @boundscheck checkbounds(v, lo:hi)
    @inbounds for i in (lo+1):hi
        lt(o, v[i], v[i-1]) && return false
    end
    true
end
```
-/
def issortedWindow {V L H Start Bounds Window Index State Previous A E Key : Type}
    (ops : WindowOps V L H Start Bounds Window Index State Previous A E)
    (v : V) (lo : L) (hi : H) (order : ordering.OrdResult A Key) :
    Option (Except (Sum E ordering.OrderingError) Bool) :=
  match (ops.bounds lo hi).run with
  | none => none
  | some (.error error) => some (.error (.inl error))
  | some (.ok bounds) =>
    match (ops.checkBounds v bounds).run with
    | none => none
    | some (.error error) => some (.error (.inl error))
    | some (.ok ()) =>
      match (ops.window (ops.addOne lo) hi).run with
      | none => none
      | some (.error error) => some (.error (.inl error))
      | some (.ok window) =>
        match (ops.first window).run with
        | none => none
        | some (.error error) => some (.error (.inl error))
        | some (.ok current) => issortedWindowLoop ops v window order current

/-- The bound increment uses the source Int64 literal, so narrow bounds promote. -/
def nativeAddOne {t : IntTy} (x : JInt t) : JInt (t.promote .i64) :=
  int.binop int.add x (int.lit .i64 1)

def nativePrevious {t : IntTy} (x : JInt t) : JInt (t.promote .i64) :=
  int.binop int.sub x (int.lit .i64 1)

def oneunitResult (t : IntTy) : Jl (JInt t) :=
  number.oneunitType
    (fun (_ : Unit) => number.oneType
      (fun (_ : Unit) n => int.convert t (int.lit .i64 n)) ())
    (fun x => .ok (int.widenTo t x)) ()

def oneunitNative (t : IntTy) : JInt t :=
  int.okOf (oneunitResult t) (by cases t <;> intro e h <;> cases h)

section NativeWindow
local instance nativeLe (t : IntTy) : range.JLe (JInt t) (JInt t) := ⟨int.le⟩
local instance nativeLt (t : IntTy) : range.JLt (JInt t) (JInt t) := ⟨int.lt⟩
local instance nativeEq (t : IntTy) : range.JEq (JInt t) (JInt t) := ⟨int.eq⟩
local instance nativeOne (t : IntTy) : range.JOneunit (JInt t) := ⟨oneunitNative t⟩
local instance nativeZero (t : IntTy) : range.JZero (JInt t) := ⟨int.zero (int.lit t 0)⟩
local instance nativeAdd (t : IntTy) : HAdd (JInt t) (JInt t) (JInt t) := ⟨int.add⟩
local instance nativeSub (t : IntTy) : HSub (JInt t) (JInt t) (JInt t) := ⟨int.sub⟩
local instance nativeWrappingSub (t : IntTy) : range.JWrappingSub (JInt t) (JInt t) (JInt t) := ⟨int.subWrap⟩
local instance nativeRangeSub (t : IntTy) : range.JRangeWrappingSub (JInt t) (JInt t) (JInt t) :=
  ⟨range._range_wrapping_sub_BitInteger⟩
local instance nativeConvert (t : IntTy) : range.JConvert (JInt t) (JInt t) :=
  ⟨fun x => .ok (int.widenTo t x)⟩
local instance nativeEltype (t : IntTy) : range.JEltype (range.UnitRange (JInt t)) (JInt t) := ⟨⟩
local instance nativeStart (t : IntTy) : range.JFieldStart (range.UnitRange (JInt t)) (JInt t) := ⟨fun r => r.start⟩
local instance nativeStop (t : IntTy) : range.JFieldStop (range.UnitRange (JInt t)) (JInt t) := ⟨fun r => r.stop⟩
local instance nativeFirst (t : IntTy) : range.JFirst (range.UnitRange (JInt t)) (JInt t) := ⟨range.first_OrdinalRange⟩
local instance nativeLast (t : IntTy) : range.JLast (range.UnitRange (JInt t)) (JInt t) := ⟨range.last_OrdinalRange⟩
local instance nativeEmpty (t : IntTy) : range.JIsempty (range.UnitRange (JInt t)) := ⟨range.isempty_AbstractUnitRange⟩
local instance nativeStep (t : IntTy) : range.JStep (range.UnitRange (JInt t)) (JInt t) :=
  ⟨fun r => .ok (range.step_AbstractUnitRange r)⟩
local instance nativeRangeLast (t : IntTy) : range.JUnitrangeLast (JInt t) (JInt t) :=
  ⟨range.unitrange_last_Integer⟩
local instance nativeUnitRange (t : IntTy) : range.JUnitRangeT (JInt t) (JInt t) (JInt t) :=
  ⟨range.UnitRange_T_new⟩

private theorem promoteSelf (t : IntTy) : t.promote t = t := by cases t <;> rfl

private def castSameAxis {t u : IntTy} (same : t = u) (axis : range.UnitRange (JInt t)) :
    range.UnitRange (JInt (t.promote u)) := by
  subst u
  simpa only [promoteSelf] using axis

private def liftPromotion {A : Type} (result : promotion.JlPartial A) : Run range.Exc A := do
  let result ← ExceptT.lift result.run
  match result with
  | .ok value => pure value
  | .error error => throw (.jl error)

private def promoteNative {t u : IntTy} (_different : t ≠ u) (x : JInt t) (y : JInt u) :
    promotion.JlPartial (JInt (t.promote u) × JInt (t.promote u)) :=
  promotion.promoteTwoValues
    (fun a b => promotion.promotePairValues
      (promotion.promoteTypeofTwo
        (fun _ => promotion.primitivePType (.int t))
        (fun _ => promotion.primitivePType (.int u))
        (promotion.promoteTypeValue promotion.primitivePromoteRule))
      (fun _ a => do
        match int.convert (t.promote u) a with
        | .ok value => pure value
        | .error error => throw error)
      (fun _ b => do
        match int.convert (t.promote u) b with
        | .ok value => pure value
        | .error error => throw error) a b)
    promotion.notSameTypeDifferent x y

def nativeColon {t u : IntTy} (lo : JInt t) (hi : JInt u) :
    Run range.Exc (range.UnitRange (JInt (t.promote u))) := do
  if same : t = u then
    let hiSame : JInt t := same.symm ▸ hi
    let axis ← liftExcept (range.colon_T_T_Real lo hiSame)
    pure (castSameAxis same axis)
  else
    let promoted ← liftPromotion (promoteNative same lo hi)
    letI : range.JPromote2 (JInt t) (JInt u) (JInt (t.promote u)) :=
      ⟨fun _ _ => .ok promoted⟩
    letI : range.JColon2 (JInt (t.promote u)) (JInt (t.promote u))
        (range.UnitRange (JInt (t.promote u))) := ⟨range.colon_T_T_Real⟩
    liftExcept (range.colon_Real_Real lo hi)

/-- This binding preserves the vector's own axis/checkindex dispatch, including
OneTo, IdentityUnitRange and external axis types. -/
def checkBoundsFromAxis {V Axis Bounds : Type}
    (eachindexLinear : V → abstractarray.Result Axis)
    (checkindex : Axis → Bounds → abstractarray.Result Bool) (v : V) (bounds : Bounds) :
    abstractarray.Result Unit := do
  let valid ← abstractarray.checkboundsOne eachindexLinear checkindex v bounds
  if valid then pure () else throw (.julia .boundsError)

inductive NativeError where
  | array (error : abstractarray.ArrayError)
  | range (error : range.Exc)
  deriving Repr

private def nativeLiftRange {A : Type} (result : Run range.Exc A) : Run NativeError A := do
  let result ← ExceptT.lift result.run
  match result with
  | .ok value => pure value
  | .error error => throw (.range error)

def nativeWindowOps {V A : Type} (t u : IntTy)
    (getindex : {k : IntTy} → V → JInt k → abstractarray.Result A)
    (checkbounds : V → range.UnitRange (JInt (t.promote u)) → abstractarray.Result Unit) :
    WindowOps V (JInt t) (JInt u) (JInt (t.promote .i64))
      (range.UnitRange (JInt (t.promote u)))
      (range.UnitRange (JInt ((t.promote .i64).promote u)))
      (JInt ((t.promote .i64).promote u)) (JInt ((t.promote .i64).promote u))
      (JInt (((t.promote .i64).promote u).promote .i64)) A NativeError where
  bounds := fun lo hi => nativeLiftRange (nativeColon lo hi)
  checkBounds := fun v bounds => liftExcept ((checkbounds v bounds).mapError NativeError.array)
  addOne := nativeAddOne
  window := fun lo hi => nativeLiftRange (nativeColon lo hi)
  first := fun window => liftExcept ((range.iterate_OrdinalRange window).mapError NativeError.range)
  next := fun window state => liftExcept
    ((range.iterate_OrdinalRange_state window state).mapError NativeError.range)
  getCurrent := fun v index => liftExcept ((getindex v index).mapError NativeError.array)
  previous := nativePrevious
  getPrevious := fun v index => liftExcept ((getindex v index).mapError NativeError.array)

end NativeWindow

def storageIssortedWindow {V α K O E : Type} (indices : IntegerIndexOps K)
    (checkBounds : V → K → K → Except E Unit) (get : V → K → Except E α)
    (lt : O → α → α → Except E Bool) (v : V) (lo hi : K) (order : O) : Except E Bool := do
  checkBounds v lo hi
  for i in indices.range (indices.addOne lo) hi do
    let current ← get v i
    let previous ← get v (indices.previous i)
    if ← lt order current previous then return false
  pure true

/--
Julia source: base/sort.jl:703-703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
after_zero(::ForwardOrdering, x) = !signbit(x)
```
-/
def afterZeroForward {α : Type} (signbit : α → Bool) (x : α) : Bool :=
  !signbit x

/--
Julia source: base/sort.jl:704-704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
after_zero(::ReverseOrdering, x) = signbit(x)
```
-/
def afterZeroReverse {α : Type} (signbit : α → Bool) (x : α) : Bool :=
  signbit x

/--
Julia source: base/sort.jl:705-705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_concrete_IEEEFloat(T::Type) = T <: Base.IEEEFloat && isconcretetype(T)
```
-/
def isConcreteIEEEFloat (isIEEEFloat isConcrete : Type → Bool) (T : Type) : Bool :=
  isIEEEFloat T && isConcrete T

/--
Julia source: base/sort.jl:946-946 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_reverse(o::ForwardOrdering, x) = x
```
-/
def maybeReverseForward {α : Type} (x : α) : α := x

/--
Julia source: base/sort.jl:947-947 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_reverse(o::ReverseOrdering, x) = reverse(x)
```
-/
def maybeReverseReverse {α : Type} (reverse : α → α) (x : α) : α :=
  reverse x

/--
Julia source: base/sort.jl:1443-1443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_unsigned(x::Integer) = x # this is necessary to avoid calling unsigned on BigInt
```
-/
def maybeUnsignedInteger {α : Type} (x : α) : α := x

/--
Julia source: base/sort.jl:1444-1444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_unsigned(x::BitSigned) = unsigned(x)
```
-/
def maybeUnsignedBitSigned {S U : Type} (unsigned : S → U) (x : S) : U :=
  unsigned x

/--
Julia source: base/sort.jl:2224-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_value(::Val{x}) where x = x
```
-/
def getValue {α : Type} (value : α) : α := value

/--
Julia source: base/sort.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybeview(v, k) = view(v, k)
```
-/
def maybeviewRange {V K W : Type} (view : V → K → W) (v : V) (k : K) : W :=
  view v k

/--
Julia source: base/sort.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybeview(v, k::Integer) = v[k]
```
-/
def maybeviewInteger {V K α E : Type} (get : V → K → Except E α)
    (v : V) (k : K) : Except E α :=
  get v k

/--
Julia source: base/sort.jl:2237-2237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UIntMappable(T::Type, order::Ordering) = nothing
```
-/
def uintMappableFallback {O : Type} (_type : Type) (_order : O) : Option Type := none

/--
Julia source: base/sort.jl:2267-2267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_map(x::Unsigned, ::ForwardOrdering) = x
```
-/
def uintMapUnsigned {U : Type} (x : U) : U := x

/--
Julia source: base/sort.jl:2268-2268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_unmap(::Type{T}, u::T, ::ForwardOrdering) where T <: Unsigned = u
```
-/
def uintUnmapUnsigned (T : Type) (u : T) : T := u

/--
Julia source: base/sort.jl:2270-2271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_map(x::Signed, ::ForwardOrdering) =
    unsigned(xor(x, typemin(x)))
```
-/
def uintMapSigned {S U : Type} (xor : S → S → S)
    (typemin : S → S) (unsigned : S → U) (x : S) : U :=
  unsigned (xor x (typemin x))

/--
Julia source: base/sort.jl:2272-2273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_unmap(::Type{T}, u::Unsigned, ::ForwardOrdering) where T <: Signed =
    xor(signed(u), typemin(T))
```
-/
def uintUnmapSigned {U : Type} (T : Type) (signed : U → T) (xor : T → T → T)
    (minimum : T) (u : U) : T :=
  xor (signed u) minimum

/--
Julia source: base/sort.jl:2275-2275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UIntMappable(T::BitIntegerType, ::ForwardOrdering) = unsigned(T)
```
-/
def uintMappableBitInteger (unsignedType : Type → Type) (T : Type) : Option Type :=
  some (unsignedType T)

/--
Julia source: base/sort.jl:2282-2282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_map(x::Char, ::ForwardOrdering) = reinterpret(UInt32, x)
```
-/
def uintMapChar {C U : Type} (reinterpret : C → U) (x : C) : U :=
  reinterpret x

/--
Julia source: base/sort.jl:2283-2283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_unmap(::Type{Char}, u::UInt32, ::ForwardOrdering) = reinterpret(Char, u)
```
-/
def uintUnmapChar {C U : Type} (reinterpret : U → C) (u : U) : C :=
  reinterpret u

/--
Julia source: base/sort.jl:2284-2284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UIntMappable(::Type{Char}, ::ForwardOrdering) = UInt32
```
-/
def uintMappableChar (uint32Type : Type) : Option Type := some uint32Type

inductive Algorithm (Target Index : Type) where
  | insertion
  | quick
  | merge
  | subArray (next : Algorithm Target Index)
  | missing (next : Algorithm Target Index)
  | boolOptimization (next : Algorithm Target Index)
  | ieeeFloat (next : Algorithm Target Index)
  | small (threshold : Nat) (small big : Algorithm Target Index)
  | checkSorted (next : Algorithm Target Index)
  | computeExtrema (next : Algorithm Target Index)
  | considerCounting (counting next : Algorithm Target Index)
  | counting
  | considerRadix (radix next : Algorithm Target Index)
  | radix
  | isUIntMappable (yes no : Algorithm Target Index)
  | scratchQuickSort (lo hi : Option Index) (next : Algorithm Target Index)
  | bracketedSort (target : Target) (getNext : Target → Algorithm Target Index)
  | stableCheckSorted (next : Algorithm Target Index)
  | partialQuickSort (target : Target)
  | defaultStable
  | defaultUnstable
  /-- A user `struct TheirAlg <: Algorithm`, identified by a tag; its methods are in the vector
  storage's `userAlgorithms` table. -/
  | user (tag : Nat)

/-- Nesting depth of an algorithm value; it bounds how many `_sort!` dispatches pass through
its wrappers before a leaf algorithm runs. -/
def Algorithm.depth {Target Index : Type} : Algorithm Target Index → Nat
  | .subArray next | .missing next | .boolOptimization next | .ieeeFloat next
  | .checkSorted next | .computeExtrema next | .stableCheckSorted next
  | .scratchQuickSort _ _ next => next.depth + 1
  | .small _ first second | .considerCounting first second
  | .considerRadix first second | .isUIntMappable first second =>
    max first.depth second.depth + 1
  | .bracketedSort target getNext => (getNext target).depth + 1
  | _ => 1

structure SortTargetOps (Target Index : Type) where
  first : Target → Index
  last : Target → Index

def smallAlgorithm {Target Index : Type} : Algorithm Target Index := .insertion

/--
Julia source: base/sort.jl:793-793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Small{N}(small, big) where N = Small{N, typeof(small), typeof(big)}(small, big)
```
-/
def smallExplicit {Target Index : Type} (threshold : Nat)
    (small big : Algorithm Target Index) : Algorithm Target Index :=
  .small threshold small big

/--
Julia source: base/sort.jl:794-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Small{N}(big) where N = Small{N}(SMALL_ALGORITHM, big)
```
-/
def smallDefault {Target Index : Type} (threshold : Nat)
    (big : Algorithm Target Index) : Algorithm Target Index :=
  .small threshold smallAlgorithm big

/--
Julia source: base/sort.jl:922-922 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ConsiderCountingSort(next) = ConsiderCountingSort(CountingSort(), next)
```
-/
def considerCountingSort {Target Index : Type} (next : Algorithm Target Index) :
    Algorithm Target Index :=
  .considerCounting .counting next

/--
Julia source: base/sort.jl:982-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ConsiderRadixSort(next) = ConsiderRadixSort(RadixSort(), next)
```
-/
def considerRadixSort {Target Index : Type} (next : Algorithm Target Index) :
    Algorithm Target Index :=
  .considerRadix .radix next

/--
Julia source: base/sort.jl:1079-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ScratchQuickSort(next::Algorithm=SMALL_ALGORITHM) = ScratchQuickSort(missing, missing, next)
```
-/
def scratchQuickDefault {Target Index : Type}
    (next : Algorithm Target Index := smallAlgorithm) : Algorithm Target Index :=
  .scratchQuickSort none none next

/--
Julia source: base/sort.jl:1080-1080 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ScratchQuickSort(lo::Union{Integer, Missing}, hi::Union{Integer, Missing}) = ScratchQuickSort(lo, hi, SMALL_ALGORITHM)
```
-/
def scratchQuickBounds {Target Index : Type} (lo hi : Option Index) :
    Algorithm Target Index :=
  .scratchQuickSort lo hi smallAlgorithm

/--
Julia source: base/sort.jl:1081-1081 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ScratchQuickSort(lo::Union{Integer, Missing}, next::Algorithm=SMALL_ALGORITHM) = ScratchQuickSort(lo, lo, next)
```
-/
def scratchQuickSingle {Target Index : Type} (lo : Option Index)
    (next : Algorithm Target Index := smallAlgorithm) : Algorithm Target Index :=
  .scratchQuickSort lo lo next

/--
Julia source: base/sort.jl:1082-1082 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ScratchQuickSort(r::OrdinalRange, next::Algorithm=SMALL_ALGORITHM) = ScratchQuickSort(first(r), last(r), next)
```
-/
def scratchQuickRange {Target Index : Type} (targetOps : SortTargetOps Target Index)
    (range : Target) (next : Algorithm Target Index := smallAlgorithm) :
    Algorithm Target Index :=
  .scratchQuickSort (some (targetOps.first range)) (some (targetOps.last range)) next

/--
Julia source: base/sort.jl:1224-1224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BracketedSort(k) = BracketedSort(k, k -> InitialOptimizations(ScratchQuickSort(k)))
```
-/
def bracketedSort {Target Index : Type} (targetOps : SortTargetOps Target Index)
    (target : Target) : Algorithm Target Index :=
  .bracketedSort target
    (fun nextTarget =>
      .subArray (.missing (.boolOptimization
        (.small 10 .insertion (.ieeeFloat (scratchQuickRange targetOps nextTarget)))))
    )

/--
Julia source: base/sort.jl:1473-1478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
InitialOptimizations(next) = SubArrayOptimization(
    MissingOptimization(
        BoolOptimization(
            Small{10}(
                IEEEFloatOptimization(
                    next)))))
```
-/
def initialOptimizations {Target Index : Type}
    (next : Algorithm Target Index) : Algorithm Target Index :=
  .subArray (.missing (.boolOptimization (.small 10 .insertion (.ieeeFloat next))))

/--
Julia source: base/sort.jl:2396-2396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_apply_initial_optimizations(alg::Algorithm) = alg
```
-/
def maybeApplyInitialGeneric {Target Index : Type}
    (algorithm : Algorithm Target Index) : Algorithm Target Index :=
  algorithm

/--
Julia source: base/sort.jl:2397-2397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_apply_initial_optimizations(alg::QuickSortAlg) = InitialOptimizations(alg)
```
-/
def maybeApplyInitialQuick {Target Index : Type} : Algorithm Target Index :=
  initialOptimizations .quick

/--
Julia source: base/sort.jl:2398-2398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_apply_initial_optimizations(alg::MergeSortAlg) = InitialOptimizations(alg)
```
-/
def maybeApplyInitialMerge {Target Index : Type} : Algorithm Target Index :=
  initialOptimizations .merge

/--
Julia source: base/sort.jl:2399-2399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maybe_apply_initial_optimizations(alg::InsertionSortAlg) = InitialOptimizations(alg)
```
-/
def maybeApplyInitialInsertion {Target Index : Type} : Algorithm Target Index :=
  initialOptimizations .insertion
/--
Julia source: base/sort.jl:1620-1620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
defalg(v::AbstractArray) = DEFAULT_STABLE
```
-/
def defalgArray {Target Index V : Type} (_v : V) : Algorithm Target Index :=
  .defaultStable

/--
Julia source: base/sort.jl:1621-1621 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
defalg(v::AbstractArray{<:Union{Number, Missing}}) = DEFAULT_UNSTABLE
```
-/
def defalgNumberOrMissing {Target Index V : Type} (_v : V) : Algorithm Target Index :=
  .defaultUnstable

/--
Julia source: base/sort.jl:1622-1622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
defalg(v::AbstractArray{Missing}) = DEFAULT_UNSTABLE # for method disambiguation
```
-/
def defalgMissing {Target Index V : Type} (_v : V) : Algorithm Target Index :=
  .defaultUnstable

/--
Julia source: base/sort.jl:1623-1623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
defalg(v::AbstractArray{Union{}}) = DEFAULT_UNSTABLE # for method disambiguation
```
-/
def defalgBottom {Target Index V : Type} (_v : V) : Algorithm Target Index :=
  .defaultUnstable

/--
Julia source: base/sort.jl:1624-1624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
defalg(v) = DEFAULT_STABLE
```
-/
def defalgOther {Target Index V : Type} (_v : V) : Algorithm Target Index :=
  .defaultStable

/--
Julia source: base/sort.jl:2206-2206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        get_view(idx) = view(A, ntuple(i -> i == get_value(d) ? Colon() : idx[i], ndims(A))...)
```
-/
def getView {A D Idx K V E : Type} (view : A → List (Option K) → Except E V)
    (dimensionValue : D → Nat) (dimensionCount : A → Nat)
    (getIndex : Idx → Nat → K) (array : A) (dimension : D) (index : Idx) :
    Except E V :=
  let selected := dimensionValue dimension
  let selectors := (List.range (dimensionCount array)).map fun offset =>
    if offset + 1 = selected then none else some (getIndex index (offset + 1))
  view array selectors
abbrev I := JInt .i64
abbrev U := JInt .u64
abbrev Vec := array.HeapArray IntTy
abbrev Axis := List (Int × Nat)

structure Heap where
  integers : array.VectorHeap I
  unsigned : array.VectorHeap U

abbrev M := StateT Heap (Except Error)

/-- Lift the installed array primitive, retaining its original error and shared handles. -/
def integerAction (action : array.VectorM I A) : M A := fun heap =>
  match action heap.integers with
  | .error error => .error (.array error)
  | .ok (value, integers) => .ok (value, { heap with integers })

def unsignedAction (action : array.VectorM U A) : M A := fun heap =>
  match action heap.unsigned with
  | .error error => .error (.array error)
  | .ok (value, unsigned) => .ok (value, { heap with unsigned })

def checkedRange (result : range.JlX A) : Except Error A :=
  result.mapError Error.range

section NativeRangeBridge
local instance : range.JLe I I := nativeLe .i64
local instance : range.JLt I I := nativeLt .i64
local instance : range.JEq I I := nativeEq .i64
local instance : range.JOneunit I := nativeOne .i64
local instance : range.JZero I := nativeZero .i64
local instance : HAdd I I I := nativeAdd .i64
local instance : HSub I I I := nativeSub .i64
local instance : range.JWrappingSub I I I := nativeWrappingSub .i64
local instance : range.JRangeWrappingSub I I I := nativeRangeSub .i64
local instance : range.JConvert I I := nativeConvert .i64
local instance : range.JEltype (range.UnitRange I) I := nativeEltype .i64
local instance : range.JFieldStart (range.UnitRange I) I := nativeStart .i64
local instance : range.JFieldStop (range.UnitRange I) I := nativeStop .i64
local instance : range.JFirst (range.UnitRange I) I := nativeFirst .i64
local instance : range.JLast (range.UnitRange I) I := nativeLast .i64
local instance : range.JIsempty (range.UnitRange I) := nativeEmpty .i64
local instance : range.JStep (range.UnitRange I) I := nativeStep .i64
local instance : range.JUnitrangeLast I I := nativeRangeLast .i64
local instance : range.JUnitRangeT I I I := nativeUnitRange .i64

local instance : range.JEltype (range.OneTo I) I := ⟨⟩
local instance : range.JFieldStop (range.OneTo I) I := ⟨fun r => r.stop⟩
local instance : range.JFirst (range.OneTo I) I := ⟨fun r => .ok (range.first_OneTo r)⟩
local instance : range.JLast (range.OneTo I) I := ⟨range.last_OrdinalRange⟩
local instance : range.JIsempty (range.OneTo I) := ⟨range.isempty_AbstractUnitRange⟩
local instance : range.JStep (range.OneTo I) I := ⟨fun r => .ok (range.step_AbstractUnitRange r)⟩

/-- A finite native UnitRange bridge. Its loop count is the exact mathematical
cardinality of the constructed native range, not user-supplied fuel. All yielded
indices and the final next call come from the installed range iteration methods. -/
def unitRangeItems (r : range.UnitRange I) : Except Error (List I) := do
  let mut current ← checkedRange (range.iterate_OrdinalRange r)
  let mut reversed := []
  for _ in List.range (r.stop.val - r.start.val + 1).toNat do
    match current with
    | none => pure ()
    | some (index, state) =>
      reversed := index :: reversed
      current ← checkedRange (range.iterate_OrdinalRange_state r state)
  pure reversed.reverse

def nativeRange (lo hi : I) : Except Error (List I) := do
  unitRangeItems (← checkedRange (range.colon_T_T_Real lo hi))

def oneToItems (r : range.OneTo I) : Except Error (List I) := do
  let mut current ← checkedRange (range.iterate_OrdinalRange r)
  let mut reversed := []
  for _ in List.range r.stop.val.toNat do
    match current with
    | none => pure ()
    | some (index, state) =>
      reversed := index :: reversed
      current ← checkedRange (range.iterate_OrdinalRange_state r state)
  pure reversed.reverse

/-- eachindex(::Array) follows the installed DenseArray method and the unchecked
OneTo constructor, retaining the OneTo axis before its finite iteration bridge. -/
def integerIndices (v : Vec) : M (List I) := do
  let axis ← abstractarray.eachindexDense
    (fun v : Vec => integerAction (array.heapLength v.handle)) range.unchecked_oneto v
  liftM (oneToItems axis)
end NativeRangeBridge

def integerRead (v : Vec) (i : I) : M I := integerAction (array.heapGet v.handle i)
def integerWrite (v : Vec) (x : I) (i : I) : M Unit :=
  integerAction (array.heapSet v.handle x i)
def unsignedRead (v : Vec) (i : I) : M U := unsignedAction (array.heapGet v.handle i)
def unsignedWrite (v : Vec) (x : U) (i : I) : M Unit :=
  unsignedAction (array.heapSet v.handle x i)

def intTyLayout (t : IntTy) : Option array.MemoryLayout :=
  some ⟨t.bits / 8, false, false⟩

def integerAllocate (dimensions : List I) : M Vec :=
  integerAction (array.heapAllocateIntDims intTyLayout .i64 dimensions)

def fillInteger (v : Vec) (value : I) : M Vec :=
  array.fillBang (fun _ => true) id pure
    (array.fillTyped integerIndices integerWrite) v value

def allocateCounts (length : I) : M Vec :=
  array.fill585 integerAllocate fillInteger (int.lit .i64 0) [length]

structure SortpermRangeOps (m : Type → Type) (V C P : Type) where
  length : V → m I
  read : V → I → m I
  range : I → I → m (List I)
  allocateCounts : I → m C
  countLength : C → m I
  getCount : C → I → m I
  setCount : C → I → I → m Unit
  allocatePermutation : I → m P
  setPermutation : P → I → I → m Unit
/--
Julia source: base/sort.jl:2058-2081 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sortperm_int_range(x::Vector{<:Integer}, rangelen, minval)
    offs = 1 -% minval
    n = length(x)

    counts = fill(0, rangelen+1)
    counts[1] = 1
    @inbounds for i = 1:n
        counts[x[i] +% offs +% 1] += 1
    end

    #cumsum!(counts, counts)
    @inbounds for i = 2:length(counts)
        counts[i] += counts[i-1]
    end

    P = Vector{Int}(undef, n)
    @inbounds for i = 1:n
        label = x[i] +% offs
        P[counts[label]] = i
        counts[label] += 1
    end

    return P
end
```
-/
def sortpermIntRange [Monad m] (ops : SortpermRangeOps m V C P)
    (x : V) (rangeLength minValue : I) : m P := do
  let offsets := int.subWrap (int.lit .i64 1) minValue
  let n ← ops.length x
  let counts ← ops.allocateCounts (int.add rangeLength (int.lit .i64 1))
  ops.setCount counts (int.lit .i64 1) (int.lit .i64 1)
  for i in (← ops.range (int.lit .i64 1) n) do
    let value ← ops.read x i
    let bucket := int.addWrap (int.addWrap value offsets) (int.lit .i64 1)
    let count ← ops.getCount counts bucket
    ops.setCount counts bucket (int.add count (int.lit .i64 1))
  for i in (← ops.range (int.lit .i64 2) (← ops.countLength counts)) do
    let count ← ops.getCount counts i
    let previous ← ops.getCount counts (int.sub i (int.lit .i64 1))
    ops.setCount counts i (int.add count previous)
  let permutation ← ops.allocatePermutation n
  for i in (← ops.range (int.lit .i64 1) n) do
    let value ← ops.read x i
    let label := int.addWrap value offsets
    let target ← ops.getCount counts label
    ops.setPermutation permutation target i
    let count ← ops.getCount counts label
    ops.setCount counts label (int.add count (int.lit .i64 1))
  pure permutation

def arrayRead {α : Type} (values : Array α) (index : Int) : Jl α :=
  if 1 ≤ index then
    match values[(index - 1).toNat]? with
    | some value => .ok value
    | none => .error .boundsError
  else .error .boundsError

def arrayWrite {α : Type} (values : Array α) (index : Int) (value : α) : Jl (Array α) :=
  if 1 ≤ index ∧ index ≤ values.size then
    .ok (values.set! (index - 1).toNat value)
  else .error .boundsError

def arrayIndexRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun offset => lo + Int.ofNat offset

def nativeSortpermOps : SortpermRangeOps M Vec Vec Vec where
  length := fun v => integerAction (array.heapLength v.handle)
  read := integerRead
  range := fun lo hi => liftM (nativeRange lo hi)
  allocateCounts := allocateCounts
  countLength := fun v => integerAction (array.heapLength v.handle)
  getCount := integerRead
  setCount := fun v i x => integerWrite v x i
  allocatePermutation := fun n =>
    integerAction (array.heapVectorAllocate intTyLayout .i64 n)
  setPermutation := fun v i x => integerWrite v x i

def arraySortpermRangeOps :
    SortpermRangeOps (StateT (Array Int × Array Int) Jl) (Array Int) Unit Unit where
  length := fun x => pure (int.lit .i64 x.size)
  read := fun x i => do
    let v ← liftM (arrayRead x i.val)
    pure (int.lit .i64 v)
  range := fun lo hi => pure ((arrayIndexRange lo.val hi.val).map (int.lit .i64))
  allocateCounts := fun n => fun (_, p) =>
    if 0 ≤ n.val then .ok ((), (Array.replicate n.val.toNat 0, p)) else .error .boundsError
  countLength := fun _ => fun (c, p) => .ok (int.lit .i64 c.size, (c, p))
  getCount := fun _ i => fun (c, p) => do
    let v ← arrayRead c i.val
    .ok (int.lit .i64 v, (c, p))
  setCount := fun _ i v => fun (c, p) => do
    let c' ← arrayWrite c i.val v.val
    .ok ((), (c', p))
  allocatePermutation := fun n => fun (c, _) =>
    if 0 ≤ n.val then .ok ((), (c, Array.replicate n.val.toNat 0)) else .error .boundsError
  setPermutation := fun _ i v => fun (c, p) => do
    let p' ← arrayWrite p i.val v.val
    .ok ((), (c, p'))
structure VectorMutationOps (m : Type → Type) (V α K : Type) where
  get : V → K → m α
  set : V → α → K → m Unit
  indices : IntegerIndexOps K
  distance : K → K → Nat
  modelExhausted : {β : Type} → m β

def insertionShift [Monad m] (ops : VectorMutationOps m V α K)
    (lt : O → α → α → m Bool) (order : O) (v : V) (lo : K) (value : α) :
    Nat → K → m K
  | 0, j => if ops.indices.less lo j then ops.modelExhausted else pure j
  | fuel + 1, j =>
    if ops.indices.less lo j then do
      let previous := ops.indices.previous j
      let other ← ops.get v previous
      if ← lt order value other then do
        ops.set v other j
        insertionShift ops lt order v lo value fuel previous
      else pure j
    else pure j

/--
Julia source: base/sort.jl:835-852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, ::InsertionSortAlg, o::Ordering, kw)
    @getkw lo hi scratch
    lo_plus_1 = (lo + 1)::Integer
    @inbounds for i = lo_plus_1:hi
        j = i
        x = v[i]
        while j > lo
            y = v[j-1]
            if !(lt(o, x, y)::Bool)
                break
            end
            v[j] = y
            j -= 1
        end
        v[j] = x
    end
    scratch
end
```
-/
def insertionSort [Monad m] {V α K O S : Type} (ops : VectorMutationOps m V α K)
    (lt : O → α → α → m Bool) (order : O) (v : V) (lo hi : K) (scratch : S) : m S := do
  for i in ops.indices.range (ops.indices.addOne lo) hi do
    let value ← ops.get v i
    let j ← insertionShift ops lt order v lo value (ops.distance lo i + 1) i
    ops.set v value j
  pure scratch

structure PartialSortOps (V K Index O Scratch Kws R E : Type) where
  targetOps : SortTargetOps K Index
  sort : V → Algorithm K Index → O → Kws → Except E V
  maybeView : V → K → Except E R
  withScratch : Scratch → Kws
  scratchOfKeywords : Kws → Scratch

/--
Julia source: base/sort.jl:97-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function partialsort!(v::AbstractVector, k::Union{Integer,OrdinalRange}, o::Ordering; scratch::Union{Nothing, Vector} = nothing)
    # TODO move k from `alg` to `kw`
    # Don't perform InitialOptimizations before Bracketing. The optimizations take O(n)
    # time and so does the whole sort. But do perform them before recursive calls because
    # that can cause significant speedups when the target range is large so the runtime is
    # dominated by k log k and the optimizations runs in O(k) time.
    _sort!(v, BoolOptimization(
        Small{12}( # Very small inputs should go straight to insertion sort
            BracketedSort(k))),
        o, (; scratch))
    maybeview(v, k)
end
```
-/
def partialSortBang {V K Index O Scratch Kws R E : Type}
    (ops : PartialSortOps V K Index O Scratch Kws R E)
    (v : V) (k : K) (order : O) (scratch : Scratch) : Except E R := do
  let sorted ← ops.sort v (.boolOptimization (smallDefault 12 (bracketedSort ops.targetOps k))) order
    (ops.withScratch scratch)
  ops.maybeView sorted k

/--
Julia source: base/sort.jl:166-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
partialsort!(v::AbstractVector, k::Union{Integer,OrdinalRange};
             lt=isless, by=identity, rev::Union{Bool,Nothing}=nothing, order::Ordering=Forward, kws...) =
    partialsort!(v, k, ord(lt,by,rev,order); kws...)
```
-/
def partialSortBangKeywords {V K Index L B O Scratch Kws R E : Type}
    (ops : PartialSortOps V K Index O Scratch Kws R E)
    (orderOf : L → B → Option Bool → O → O) (v : V) (k : K)
    (less : L) (byFn : B) (rev : Option Bool) (order : O) (kws : Kws) :
    Except E R := do
  let resolvedOrder := orderOf less byFn rev order
  partialSortBang ops v k resolvedOrder (ops.scratchOfKeywords kws)

/--
Julia source: base/sort.jl:176-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
partialsort(v::AbstractVector, k::Union{Integer,OrdinalRange}; kws...) =
    partialsort!(copymutable(v), k; kws...)
```
-/
def partialSort {V K Index L B O Scratch Kws R E : Type}
    (ops : PartialSortOps V K Index O Scratch Kws R E)
    (copyMutable : V → Except E V)
    (orderOf : L → B → Option Bool → O → O) (v : V) (k : K)
    (less : L) (byFn : B) (rev : Option Bool) (order : O) (kws : Kws) :
    Except E R := do
  let copied ← copyMutable v
  partialSortBangKeywords ops orderOf copied k less byFn rev order kws

structure SortVectorOps (V Alg L B O Scratch Kws E : Type) where
  applyInitialOptimizations : Alg → Alg
  ordering : L → B → Option Bool → O → O
  runSort : V → Alg → O → Kws → Except E V
  withScratch : Scratch → Kws

/--
Julia source: base/sort.jl:1732-1741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort!(v::AbstractVector{T};
               alg::Algorithm=defalg(v),
               lt=isless,
               by=identity,
               rev::Union{Bool,Nothing}=nothing,
               order::Ordering=Forward,
               scratch::Union{Vector{T}, Nothing}=nothing) where T
    _sort!(v, maybe_apply_initial_optimizations(alg), ord(lt,by,rev,order), (;scratch))
    v
end
```
-/
def sortVectorBang {V Alg L B O Scratch Kws E : Type}
    (ops : SortVectorOps V Alg L B O Scratch Kws E) (v : V) (alg : Alg)
    (less : L) (byFn : B) (rev : Option Bool) (order : O) (scratch : Scratch) :
    Except E V := do
  let sorted ← ops.runSort v (ops.applyInitialOptimizations alg)
    (ops.ordering less byFn rev order) (ops.withScratch scratch)
  pure sorted

structure SortCopyOps (V E Kws : Type) where
  copyMutable : V → Except E V
  sortBang : V → Kws → Except E V

/--
Julia source: base/sort.jl:1780-1780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort(v::AbstractVector; kws...) = sort!(copymutable(v); kws...)
```
-/
def sortVector {V E Kws : Type} (ops : SortCopyOps V E Kws)
    (v : V) (keywords : Kws) : Except E V := do
  let copied ← ops.copyMutable v
  ops.sortBang copied keywords

structure SortCollectOps (C V E Kws : Type) where
  collect : C → Except E V
  sortBang : V → Kws → Except E V

/--
Julia source: base/sort.jl:1783-1783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort(v::COLLECT_ON_SORT_TYPES; kws...) = sort!(collect(v); kws...)
```
-/
def sortCollected {C V E Kws : Type} (ops : SortCollectOps C V E Kws)
    (v : C) (keywords : Kws) : Except E V := do
  let collected ← ops.collect v
  ops.sortBang collected keywords
structure PartialSortpermOps
    (IX V K Axis Idx Alg L B O PO Kws R E : Type) where
  makeIndexVector : V → K → Except E IX
  axesIndex : IX → Axis
  axesVector : V → Axis
  axesEqual : Axis → Axis → Bool
  axesError : Axis → Axis → E
  eachIndex : IX → List Idx
  writeIndex : IX → Idx → Idx → Except E IX
  scratchQuickSort : K → Alg
  initialOptimizations : Alg → Alg
  ordering : L → B → Option Bool → O → O
  permutationOrder : O → V → PO
  emptyKeywords : Kws
  sort : IX → Alg → PO → Kws → Except E IX
  maybeView : IX → K → Except E R

/--
Julia source: base/sort.jl:1896-1915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function partialsortperm!(ix::AbstractVector{<:Integer}, v::AbstractVector,
                          k::Union{Integer, OrdinalRange};
                          lt::Function=isless,
                          by::Function=identity,
                          rev::Union{Bool,Nothing}=nothing,
                          order::Ordering=Forward,
                          initialized::Bool=false)
    if axes(ix,1) != axes(v,1)
        throw(ArgumentError("The index vector is used as scratch space and must have the " *
                            "same length/indices as the source vector, $(axes(ix,1)) != $(axes(v,1))"))
    end
    @inbounds for i in eachindex(ix)
        ix[i] = i
    end

    # do partial quicksort
    _sort!(ix, InitialOptimizations(ScratchQuickSort(k)), Perm(ord(lt, by, rev, order), v), (;))

    maybeview(ix, k)
end
```
-/
def partialSortpermBang {IX V K Axis Idx Alg L B O PO Kws R E : Type}
    (ops : PartialSortpermOps IX V K Axis Idx Alg L B O PO Kws R E)
    (ix : IX) (v : V) (k : K) (less : L) (byFn : B) (rev : Option Bool)
    (order : O) (_initialized : Bool := false) : Except E R := do
  let indexAxes := ops.axesIndex ix
  let vectorAxes := ops.axesVector v
  if !ops.axesEqual indexAxes vectorAxes then
    throw (ops.axesError indexAxes vectorAxes)
  let mut ix := ix
  for index in ops.eachIndex ix do
    ix ← ops.writeIndex ix index index
  let resolvedOrder := ops.ordering less byFn rev order
  let algorithm := ops.initialOptimizations (ops.scratchQuickSort k)
  ix ← ops.sort ix algorithm (ops.permutationOrder resolvedOrder v) ops.emptyKeywords
  ops.maybeView ix k

/--
Julia source: base/sort.jl:1853-1854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
partialsortperm(v::AbstractVector, k::Union{Integer,OrdinalRange}; kwargs...) =
    partialsortperm!(similar(Vector{eltype(k)}, axes(v,1)), v, k; kwargs...)
```
-/
def partialSortperm {IX V K Axis Idx Alg L B O PO Kws R E : Type}
    (ops : PartialSortpermOps IX V K Axis Idx Alg L B O PO Kws R E)
    (v : V) (k : K) (less : L) (byFn : B) (rev : Option Bool) (order : O)
    (initialized : Bool := false) : Except E R := do
  let ix ← ops.makeIndexVector v k
  partialSortpermBang ops ix v k less byFn rev order initialized

structure SortpermTopOps (A Alg L B O Scratch Dims P E : Type) where
  ordering : L → B → Option Bool → O → O
  sortperm : A → Alg → O → Scratch → Dims → Except E P

/--
Julia source: base/sort.jl:1966-1979 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sortperm(A::AbstractArray;
                  alg::Algorithm=DEFAULT_UNSTABLE,
                  lt=isless,
                  by=identity,
                  rev::Union{Bool,Nothing}=nothing,
                  order::Ordering=Forward,
                  scratch::Union{Vector{<:Integer}, Nothing}=nothing,
                  dims...) #to optionally specify dims argument
    if rev === true
        _sortperm(A; alg, order=ord(lt, by, true, order), scratch, dims...)
    else
        _sortperm(A; alg, order=ord(lt, by, nothing, order), scratch, dims...)
    end
end
```
-/
def sortpermTop {A Alg L B O Scratch Dims P E : Type}
    (ops : SortpermTopOps A Alg L B O Scratch Dims P E)
    (array : A) (algorithm : Alg) (less : L) (byFn : B)
    (rev : Option Bool) (order : O) (scratch : Scratch) (dims : Dims) :
    Except E P :=
  if rev = some true then
    ops.sortperm array algorithm (ops.ordering less byFn (some true) order) scratch dims
  else
    ops.sortperm array algorithm (ops.ordering less byFn none order) scratch dims

structure SortpermCoreOps
    (A V Ix Alg O PO Scratch Dims P T E : Type) where
  isForward : O → Bool
  isVector : A → Bool
  hasIntegerElements : A → Bool
  length : A → Nat
  extrema : A → Except E (T × T)
  subtractWithOverflow : T → T → T × Bool
  addWithOverflow : T → T → T × Bool
  oneUnit : T
  rangeLessThanHalf : T → Nat → Bool
  sortpermIntRange : A → T → T → Except E P
  copyLinearIndices : A → Except E Ix
  vectorize : A → V
  permutationOrder : O → V → PO
  sortIndices : Ix → Alg → PO → Scratch → Dims → Except E P

/--
Julia source: base/sort.jl:1980-1994 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sortperm(A::AbstractArray; alg, order, scratch, dims...)
    if order === Forward && isa(A,Vector) && eltype(A)<:Integer
        n = length(A)
        if n > 1
            min, max = extrema(A)
            (diff, o1) = sub_with_overflow(max, min)
            (rangelen, o2) = add_with_overflow(diff, oneunit(diff))
            if !(o1 || o2)::Bool && rangelen < div(n,2)
                return sortperm_int_range(A, rangelen, min)
            end
        end
    end
    ix = copymutable(LinearIndices(A))
    sort!(ix; alg, order = Perm(order, vec(A)), scratch, dims...)
end
```
-/
def sortpermCore {A V Ix Alg O PO Scratch Dims P T E : Type}
    (ops : SortpermCoreOps A V Ix Alg O PO Scratch Dims P T E)
    (array : A) (algorithm : Alg) (order : O) (scratch : Scratch)
    (dims : Dims) : Except E P := do
  if ops.isForward order && ops.isVector array && ops.hasIntegerElements array then
    let n := ops.length array
    if n > 1 then
      let (minimum, maximum) ← ops.extrema array
      let (difference, subtractOverflow) := ops.subtractWithOverflow maximum minimum
      let (rangeLength, addOverflow) := ops.addWithOverflow difference ops.oneUnit
      if !(subtractOverflow || addOverflow) && ops.rangeLessThanHalf rangeLength (n / 2) then
        return ← ops.sortpermIntRange array rangeLength minimum
  let indices ← ops.copyLinearIndices array
  ops.sortIndices indices algorithm (ops.permutationOrder order (ops.vectorize array))
    scratch dims

structure SortpermBangOps
    (Ix A V Alg L B O PO Scratch Dims Axis E : Type) where
  isVector : A → Bool
  hasDims : Dims → Bool
  axesIndex : Ix → Axis
  axesArray : A → Axis
  axesEqual : Axis → Axis → Bool
  dimensionError : A → E
  axesError : Axis → Axis → E
  initializeLinearIndices : Ix → A → Except E Ix
  ordering : L → B → Option Bool → O → O
  vectorize : A → V
  permutationOrder : O → V → PO
  sortBang : Ix → Alg → PO → Scratch → Dims → Except E Ix

/--
Julia source: base/sort.jl:2037-2055 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function sortperm!(ix::AbstractArray{T}, A::AbstractArray;
                   alg::Algorithm=DEFAULT_UNSTABLE,
                   lt=isless,
                   by=identity,
                   rev::Union{Bool,Nothing}=nothing,
                   order::Ordering=Forward,
                   initialized::Bool=false,
                   scratch::Union{Vector{T}, Nothing}=nothing,
                   dims...) where T <: Integer #to optionally specify dims argument
    (typeof(A) <: AbstractVector) == (:dims in keys(dims)) && throw(ArgumentError("Dims argument incorrect for type $(typeof(A))"))
    axes(ix) == axes(A) || throw(ArgumentError("index array must have the same size/axes as the source array, $(axes(ix)) != $(axes(A))"))

    ix .= LinearIndices(A)
    if rev === true
        sort!(ix; alg, order=Perm(ord(lt, by, true, order), vec(A)), scratch, dims...)
    else
        sort!(ix; alg, order=Perm(ord(lt, by, nothing, order), vec(A)), scratch, dims...)
    end
end
```
-/
def sortpermBang {Ix A V Alg L B O PO Scratch Dims Axis E : Type}
    (ops : SortpermBangOps Ix A V Alg L B O PO Scratch Dims Axis E)
    (indices : Ix) (array : A) (algorithm : Alg)
    (less : L) (byFn : B) (rev : Option Bool) (order : O)
    (scratch : Scratch) (dims : Dims) (_initialized : Bool := false) :
    Except E Ix := do
  if ops.isVector array == ops.hasDims dims then
    throw (ops.dimensionError array)
  let indexAxes := ops.axesIndex indices
  let arrayAxes := ops.axesArray array
  if !ops.axesEqual indexAxes arrayAxes then
    throw (ops.axesError indexAxes arrayAxes)
  let indices ← ops.initializeLinearIndices indices array
  let resolvedOrder := if rev = some true then
    ops.ordering less byFn (some true) order else ops.ordering less byFn none order
  ops.sortBang indices algorithm (ops.permutationOrder resolvedOrder (ops.vectorize array))
    scratch dims

structure MultidimensionalSortOps
    (A V Alg L B O Scratch E : Type) where
  dimensionLength : A → Nat → Nat
  dimensions : A → List Nat
  dimensionOne : Nat
  ordering : L → B → Option Bool → O → O
  applyInitialOptimizations : Alg → Alg
  permuteDimensions : A → List Nat → Except E A
  vectorize : A → Except E V
  copyLinear : A → Except E V
  sortChunks : V → Nat → Alg → O → Scratch → Except E V
  inversePermutation : List Nat → List Nat
  restorePermuted : A → V → List Nat → Except E A
  reshapeOriginalAxes : A → V → Except E A

/--
Julia source: base/sort.jl:2112-2134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort(A::AbstractArray{T};
              dims::Integer,
              alg::Algorithm=defalg(A),
              lt=isless,
              by=identity,
              rev::Union{Bool,Nothing}=nothing,
              order::Ordering=Forward,
              scratch::Union{Vector{T}, Nothing}=nothing) where T
    dim = dims
    order = ord(lt,by,rev,order)
    n = length(axes(A, dim))
    if dim != 1
        pdims = (dim, setdiff(1:ndims(A), dim)...)  # put the selected dimension first
        Ap = permutedims(A, pdims)
        Av = vec(Ap)
        sort_chunks!(Av, n, maybe_apply_initial_optimizations(alg), order, scratch)
        permutedims(Ap, invperm(pdims))
    else
        Av = A[:]
        sort_chunks!(Av, n, maybe_apply_initial_optimizations(alg), order, scratch)
        reshape(Av, axes(A))
    end
end
```
-/
def sortArrayDimension {A V Alg L B O Scratch E : Type}
    (ops : MultidimensionalSortOps A V Alg L B O Scratch E)
    (array : A) (dimension : Nat) (algorithm : Alg)
    (less : L) (byFn : B) (rev : Option Bool) (order : O)
    (scratch : Scratch) : Except E A := do
  let selectedOrder := ops.ordering less byFn rev order
  let n := ops.dimensionLength array dimension
  let selectedAlgorithm := ops.applyInitialOptimizations algorithm
  if dimension != ops.dimensionOne then
    let otherDimensions := (ops.dimensions array).filter fun dim => dim != dimension
    let permutedDimensions := dimension :: otherDimensions
    let permuted ← ops.permuteDimensions array permutedDimensions
    let vector ← ops.vectorize permuted
    let sorted ← ops.sortChunks vector n selectedAlgorithm selectedOrder scratch
    ops.restorePermuted permuted sorted (ops.inversePermutation permutedDimensions)
  else
    let vector ← ops.copyLinear array
    let sorted ← ops.sortChunks vector n selectedAlgorithm selectedOrder scratch
    ops.reshapeOriginalAxes array sorted

structure SortChunksDispatchOps (V Bound N Alg O Scratch E : Type) where
  linearBounds : V → Except E (Bound × Bound)
  sortChunksBounded : V → N → Alg → O → Scratch → Bound → Bound → Except E V

/--
Julia source: base/sort.jl:2136-2139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function sort_chunks!(Av, n, alg, order, scratch)
    inds = LinearIndices(Av)
    sort_chunks!(Av, n, alg, order, scratch, first(inds), last(inds))
end
```
-/
def sortChunksDispatch {V Bound N Alg O Scratch E : Type}
    (ops : SortChunksDispatchOps V Bound N Alg O Scratch E)
    (vector : V) (n : N) (algorithm : Alg) (order : O) (scratch : Scratch) :
    Except E V := do
  let (first, last) ← ops.linearBounds vector
  ops.sortChunksBounded vector n algorithm order scratch first last

structure SortBangDimensionsOps
    (A V D Index Alg L B O Scratch E : Type) where
  dimensionCount : A → Nat
  dimensionError : E
  applyInitialOptimizations : Alg → Alg
  ordering : L → B → Option Bool → O → O
  dimensionValues : Nat → List D
  dimensionValue : D → Nat
  cartesianIndices : A → D → Except E (List Index)
  firstIndex : List Index → Except E Index
  getView : A → D → Index → Except E V
  setView : A → D → Index → V → Except E A
  size : A → Nat → Nat
  similar : V → Except E V
  copyInto : V → V → Except E V
  copyFrom : A → D → Index → V → Except E A
  sortBang : V → Alg → O → Scratch → Except E V
  defaultScratch : A → Int → Except E Scratch := fun _ _ => throw dimensionError

/--
Julia source: base/sort.jl:2187-2223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort!(A::AbstractArray{T};
               dims::Integer,
               alg::Algorithm=defalg(A),
               lt=isless,
               by=identity,
               rev::Union{Bool,Nothing}=nothing,
               order::Ordering=Forward, # TODO stop eagerly over-allocating.
               scratch::Union{Vector{T}, Nothing}=size(A, dims) < 10 ? nothing : Vector{T}(undef, size(A, dims))) where T
    nd = ndims(A)
    1 <= dims <= nd || throw(ArgumentError("dimension out of range"))
    alg2 = maybe_apply_initial_optimizations(alg)
    order2 = ord(lt, by, rev, order)
    foreach(ntuple(Val, nd)) do d
        get_value(d) == dims || return
        # We assume that an Integer between 1 and nd must be equal to one of the
        # values 1:nd. If this assumption is false, then what's an integer? and
        # also sort! will silently do nothing.

        idxs = CartesianIndices(ntuple(i -> i == get_value(d) ? 1 : axes(A, i), ndims(A)))
        get_view(idx) = view(A, ntuple(i -> i == get_value(d) ? Colon() : idx[i], ndims(A))...)
        if d == Val(1) || size(A, get_value(d)) < 30
            for idx in idxs
                sort!(get_view(idx); alg=alg2, order=order2, scratch)
            end
        else
            v = similar(get_view(first(idxs)))
            for idx in idxs
                vw = get_view(idx)
                v .= vw
                sort!(v; alg=alg2, order=order2, scratch)
                vw .= v
            end
        end
        A
    end
    A
end
```
-/
def sortBangDimensions {A V D Index Alg L B O Scratch E : Type}
    (ops : SortBangDimensionsOps A V D Index Alg L B O Scratch E)
    (array : A) (dimension : Int) (algorithm : Alg)
    (less : L) (byFn : B) (rev : Option Bool) (order : O)
    (scratch : Scratch) (useDefaultScratch : Bool := false) : Except E A := do
  let scratch ← if useDefaultScratch then ops.defaultScratch array dimension else pure scratch
  let nd := ops.dimensionCount array
  if !(1 ≤ dimension && dimension ≤ Int.ofNat nd) then
    throw ops.dimensionError
  let algorithm2 := ops.applyInitialOptimizations algorithm
  let order2 := ops.ordering less byFn rev order
  let mut result := array
  for d in ops.dimensionValues nd do
    if Int.ofNat (ops.dimensionValue d) == dimension then
      let indices ← ops.cartesianIndices result d
      if ops.dimensionValue d == 1 || ops.size result (ops.dimensionValue d) < 30 then
        for index in indices do
          let view ← ops.getView result d index
          let sorted ← ops.sortBang view algorithm2 order2 scratch
          result ← ops.setView result d index sorted
      else
        let first ← ops.firstIndex indices
        let firstView ← ops.getView result d first
        let mut temporary ← ops.similar firstView
        for index in indices do
          let view ← ops.getView result d index
          temporary ← ops.copyInto temporary view
          temporary ← ops.sortBang temporary algorithm2 order2 scratch
          result ← ops.copyFrom result d index temporary
  pure result
structure SortChunksLoopOps (V K N Alg O Scratch E : Type) where
  starts : K → N → K → Except E (List K)
  chunkEnd : K → N → K
  nextChunk : K → N → K
  sortWithoutScratch : V → Alg → O → K → K → Except E (V × Option Scratch)
  sortWithScratch : V → Alg → O → K → K → Scratch → Except E V

/--
Julia source: base/sort.jl:2149-2154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function sort_chunks!(Av, n, alg, order, scratch::AbstractVector, fst, lst)
    for lo = fst:n:lst
        _sort!(Av, alg, order, (; lo, hi=lo+n-1, scratch))
    end
    Av
end
```
-/
def sortChunksWithScratch {V K N Alg O Scratch E : Type}
    (ops : SortChunksLoopOps V K N Alg O Scratch E)
    (vector : V) (n : N) (algorithm : Alg) (order : O)
    (scratch : Scratch) (first last : K) : Except E V := do
  let mut vector := vector
  let starts ← ops.starts first n last
  for lo in starts do
    vector ← ops.sortWithScratch vector algorithm order lo (ops.chunkEnd lo n) scratch
  pure vector

/--
Julia source: base/sort.jl:2141-2147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function sort_chunks!(Av, n, alg, order, scratch::Nothing, fst, lst)
    for lo = fst:n:lst
        s = _sort!(Av, alg, order, (; lo, hi=lo+n-1, scratch))
        s !== nothing && return sort_chunks!(Av, n, alg, order, s, lo+n, lst)
    end
    Av
end
```
-/
def sortChunksNoScratch {V K N Alg O Scratch E : Type}
    (ops : SortChunksLoopOps V K N Alg O Scratch E)
    (vector : V) (n : N) (algorithm : Alg) (order : O) (first last : K) :
    Except E V := do
  let rec loop (vector : V) : List K → Except E V
    | [] => .ok vector
    | lo :: rest => do
      let (vector, scratch) ← ops.sortWithoutScratch vector algorithm order
        lo (ops.chunkEnd lo n)
      match scratch with
      | some scratch =>
        sortChunksWithScratch ops vector n algorithm order scratch
          (ops.nextChunk lo n) last
      | none => loop vector rest
  let starts ← ops.starts first n last
  loop vector starts
structure ReverseUIntMappingOps (T U O R : Type) where
  bitwiseNot : U → U
  forwardOrdering : R → O
  mapForward : T → O → U
  unmapForward : Type → U → O → T
  mappableForward : Type → O → Option Type

/--
Julia source: base/sort.jl:2287-2287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_map(x, rev::ReverseOrdering) = ~uint_map(x, rev.fwd)
```
-/
def uintMapReverse {T U O R : Type} (ops : ReverseUIntMappingOps T U O R)
    (value : T) (reverseOrder : R) : U :=
  ops.bitwiseNot (ops.mapForward value (ops.forwardOrdering reverseOrder))

/--
Julia source: base/sort.jl:2288-2288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uint_unmap(T::Type, u::Unsigned, rev::ReverseOrdering) = uint_unmap(T, ~u, rev.fwd)
```
-/
def uintUnmapReverse {T U O R : Type} (ops : ReverseUIntMappingOps T U O R)
    (valueType : Type) (value : U) (reverseOrder : R) : T :=
  ops.unmapForward valueType (ops.bitwiseNot value) (ops.forwardOrdering reverseOrder)

/--
Julia source: base/sort.jl:2289-2289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
UIntMappable(T::Type, order::ReverseOrdering) = UIntMappable(T, order.fwd)
```
-/
def uintMappableReverse {T U O R : Type} (ops : ReverseUIntMappingOps T U O R)
    (valueType : Type) (reverseOrder : R) : Option Type :=
  ops.mappableForward valueType (ops.forwardOrdering reverseOrder)

structure UIntMapVectorOps (V UV U K α O E : Type) where
  elementType : V → Type
  uintMappable : Type → O → Option Type
  reinterpret : Option Type → V → Except E UV
  range : K → K → List K
  read : V → K → Except E α
  uintMap : α → O → Except E U
  writeUnsigned : UV → K → U → Except E UV

/--
Julia source: base/sort.jl:2295-2301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uint_map!(v::AbstractVector, lo::Integer, hi::Integer, order::Ordering)
    u = reinterpret(UIntMappable(eltype(v), order), v)
    @inbounds for i in lo:hi
        u[i] = uint_map(v[i], order)
    end
    u
end
```
-/
def uintMapVectorBang {V UV U K α O E : Type}
    (ops : UIntMapVectorOps V UV U K α O E)
    (vector : V) (lo hi : K) (order : O) : Except E UV := do
  let unsignedType := ops.uintMappable (ops.elementType vector) order
  let mut unsignedVector ← ops.reinterpret unsignedType vector
  for index in ops.range lo hi do
    let value ← ops.read vector index
    let mapped ← ops.uintMap value order
    unsignedVector ← ops.writeUnsigned unsignedVector index mapped
  pure unsignedVector

structure UIntUnmapVectorOps (V UV U K α O E : Type) where
  range : K → K → List K
  addIndex : K → K → K
  readUnsigned : UV → K → Except E U
  zeroUnsigned : U
  zeroIndex : K
  addUnsigned : U → U → U
  elementType : V → Type
  uintUnmap : Type → U → O → Except E α
  write : V → K → α → Except E V

/--
Julia source: base/sort.jl:2303-2310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uint_unmap!(v::AbstractVector, u::AbstractVector{U}, lo::Integer, hi::Integer,
                     order::Ordering, offset::U=zero(U),
                     index_offset::Integer=0) where U <: Unsigned
    @inbounds for i in lo:hi
        v[i] = uint_unmap(eltype(v), u[i+index_offset]+offset, order)
    end
    v
end
```
-/
def uintUnmapVectorBang {V UV U K α O E : Type}
    (ops : UIntUnmapVectorOps V UV U K α O E)
    (vector : V) (unsignedVector : UV) (lo hi : K) (order : O)
    (offsetArg : Option U := none) (indexOffsetArg : Option K := none) :
    Except E V := do
  let offset := offsetArg.getD ops.zeroUnsigned
  let indexOffset := indexOffsetArg.getD ops.zeroIndex
  let mut vector := vector
  for index in ops.range lo hi do
    let unsigned := ← ops.readUnsigned unsignedVector (ops.addIndex index indexOffset)
    let value ← ops.uintUnmap (ops.elementType vector) (ops.addUnsigned unsigned offset) order
    vector ← ops.write vector index value
  pure vector
abbrev F64 := float.FV .f64

/-- Heterogeneous native-integer/Float64 promotion follows the installed
`promote_typeof` and `promote_type` dispatch, including its partial result. -/
def promoteIntFloat {t : IntTy} (x : JInt t) (y : F64) :
    promotion.JlPartial (F64 × F64) :=
  promotion.promoteTwoValues
    (fun a b => promotion.promotePairValues
      (promotion.promoteTypeofTwo
        (fun _ => promotion.primitivePType (.int t))
        (fun _ => promotion.primitivePType (.float .f64))
        (promotion.promoteTypeValue promotion.primitivePromoteRule))
      (fun _ a => pure (float.floatOfInt .f64 a))
      (fun _ b => pure (float.convertFloat .f64 b)) a b)
    promotion.notSameTypeDifferent x y

def liftJl {α : Type} (result : Jl α) : promotion.JlPartial α :=
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- `minNumber` has one input type parameter; the sum only accommodates its
heterogeneous arguments. Its only invocation here has an integer on the left
and a Float64 on the right. `minIEEE` reads only the overwritten `minFloat` field. -/
def minimumIntFloat (ieee : math.IEEEOps .f64) (x : JInt .i64) (y : F64) : promotion.JlPartial F64 :=
  promotion.minNumber
    (fun a b : Sum (JInt .i64) F64 =>
      let convert := fun value => match value with
        | .inl integer => float.floatOfInt .f64 integer
        | .inr real => float.convertFloat .f64 real
      match a, b with
      | .inl integer, .inr real => promoteIntFloat integer real
      | _, _ => pure (convert a, convert b))
    (fun a b => pure (math.minIEEE { ieee with minFloat := JuliaLean.C.jlMinFloat } a b))
    (.inl x) (.inr y)

def floatMod (x y : F64) : F64 :=
  float.mod_generic float.isinf_IEEEFloat float.isfinite_IEEEFloat float.rem_IEEEFloat
    float.iszero_float float.copysign_float
    (fun z => operators.greaterThan float.lt_IEEEFloat z (float.zero_float .f64))
    float.add_IEEEFloat x y

def floatRemUp (x y : F64) : F64 :=
  int.okOf (div.rem_Up (fun a b => .ok (floatMod a b)) float.neg_IEEEFloat x y)
    (by intro e h; cases h)

def floatDivUp (x y : F64) (_mode : float.RoundingMode) : Jl F64 :=
  .ok (div.div_AbstractFloat float.div_IEEEFloat (fun a b _ => floatRemUp a b)
    float.sub_IEEEFloat
    (fun x => rounding.roundKeyword (fun z _ (_ : Unit) => float.round_Nearest_llvm z) x ())
    x y .Up)

def mixedCld {u : IntTy} (bits : JInt u) (denominator : F64) :
    promotion.JlPartial F64 := do
  let promoted ← promoteIntFloat bits denominator
  liftJl (div.cld_Real_Real (fun _ _ => promoted) floatDivUp bits denominator)

def maybeUnsigned : (t : IntTy) → JInt t → JInt t.toUnsigned
  | .i8, x => maybeUnsignedBitSigned int.unsigned x
  | .i16, x => maybeUnsignedBitSigned int.unsigned x
  | .i32, x => maybeUnsignedBitSigned int.unsigned x
  | .i64, x => maybeUnsignedBitSigned int.unsigned x
  | .i128, x => maybeUnsignedBitSigned int.unsigned x
  | .u8, x => maybeUnsignedInteger x
  | .u16, x => maybeUnsignedInteger x
  | .u32, x => maybeUnsignedInteger x
  | .u64, x => maybeUnsignedInteger x
  | .u128, x => maybeUnsignedInteger x

/--
Julia source: base/sort.jl:1430-1441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function radix_chunk_size_heuristic(lo::Integer, hi::Integer, bits::Unsigned)
    # chunk_size is the number of bits to radix over at once.
    # We need to allocate an array of size 2^chunk size, and on the other hand the higher
    # the chunk size the fewer passes we need. Theoretically, chunk size should be based on
    # the Lambert W function applied to length. Empirically, we use this heuristic:
    guess = min(10, log(maybe_unsigned(hi-lo))*3/4+3)
    # TODO the maximum chunk size should be based on architecture cache size.

    # We need iterations * chunk size ≥ bits, and these cld's
    # make an effort to get iterations * chunk size ≈ bits
    UInt8(cld(bits, cld(bits, guess)))
end
```
-/
def radixChunkSizeHeuristic {s t u : IntTy} (ieee : math.IEEEOps .f64)
    (log : JInt (t.promote s).toUnsigned → Jl F64)
    (lo : JInt s) (hi : JInt t) (bits : JInt u) : promotion.JlPartial (JInt .u8) := do
  let difference := int.binop int.sub hi lo
  let logarithm ← liftJl (log (maybeUnsigned _ difference))
  let three := float.floatOfInt .f64 (int.lit .i64 3)
  let four := float.floatOfInt .f64 (int.lit .i64 4)
  let guess ← minimumIntFloat ieee (int.lit .i64 10)
    (float.add_IEEEFloat
      (float.div_IEEEFloat (float.mul_IEEEFloat logarithm three) four) three)
  let inner ← mixedCld bits guess
  liftJl (float.intOfFloat .u8 (← mixedCld bits inner))

abbrev BC := broadcast.Material.MaterializedExpr broadcast.Style.Style Unit (List I) Axis
abbrev CopyExpr := broadcast.Material.Expr (Option broadcast.Style.Style) Unit (List I) Axis

def scalarStyle (x : I) : Except broadcast.Style.StyleError broadcast.Style.Style :=
  broadcast.Style.m432
    (fun _ : I => broadcast.Style.m103
      (fun _ : Unit => pure (.fixed (number.ndimsType ()).val.toNat)) ()) x

def makeScalarBroadcast (f : Unit) (args : List I) (axes : Axis) : M BC := do
  let style ← liftM ((broadcast.Style.combineStyles scalarStyle
    (broadcast.Style.m459 (fun a b => decide (a = b))) args).mapError Error.style)
  let bc ← liftM ((broadcast.Lazy.m181 (fun _ => .style style) f args axes).mapError Error.constructor)
  pure ⟨bc.style, bc.f, bc.args, bc.axes⟩

def maxRank : broadcast.Style.Rank → broadcast.Style.Rank → Except broadcast.Style.StyleError broadcast.Style.Rank
  | .fixed a, .fixed b =>
    let maximum := int.okOf
      (promotion.maxSameType (fun x y : I => .ok (int.lt x y))
        (int.lit .i64 a) (int.lit .i64 b))
      (by intro error h; change Except.ok _ = Except.error error at h; cases h)
    .ok (.fixed maximum.val.toNat)
  | .any, _ | _, .any => .ok .any

def combinedStyle (dest : Vec) (bc : BC) : M broadcast.Style.Style :=
  broadcast.Style.m437
    (fun value : Sum Vec BC => match value with
      | .inl v => pure (broadcast.Style.m102 (.fixed v.dimensions.length))
      | .inr e => liftM ((broadcast.Style.m433 (.assigned e.style)).mapError Error.julia))
    (fun a b => do
      let (style, _) ← liftM ((broadcast.Style.m463
        (fun a b state => do
          let style ← broadcast.Style.m149 maxRank broadcast.Style.rebuildRank a a.rank b.rank
          pure (style, state)) a b ()).mapError Error.style)
      pure style)
    (.inl dest) (.inr bc)

/-- The unresolved throwdm primitive keeps its own exception interface.
Scalar unalias is bound directly to the installed abstractarray model. -/
structure ScalarPrimitives where
  throwdm : Axis → Axis → M Vec

/-- Only the unavailable throwdm callee has an interface law. -/
def ScalarPrimitiveLaws (p : ScalarPrimitives) : Prop :=
  ∀ a b heap, p.throwdm a b heap = .error (.broadcast .dimensionMismatch)

def scalarArgument (args : List I) : M I := do
  let x ← liftM ((tuple.getindexInt args (int.lit .i64 1)).mapError Error.tuple)
  pure (number.getindex0 x)

def scalarBroadcastUnalias (dest : Vec) (x : I) : I :=
  (broadcast.Material.m1001 (fun (_ _ : Vec × I) => false)
    (fun _ pair => (pair.1, abstractarray.unaliasOther pair.1 pair.2)) (dest, x) (dest, x)).2

def scalarPreprocess (dest : Vec) (bc : CopyExpr) : CopyExpr :=
  broadcast.Material.m1007 (m := Id)
    (fun dest args => args.map
      (broadcast.Material.m1008 (m := Id) scalarBroadcastUnalias broadcast.Index.m672 dest)) dest bc

def scalarCopyto (p : ScalarPrimitives) (dest : Vec) (bc : CopyExpr) : M Vec :=
  broadcast.Material.m1015
    (fun d : Vec => pure d.axes) (fun e : CopyExpr => pure e.axes)
    (fun a b => decide (a = b)) (fun _ : Unit => true)
    (fun _ : List I => none) p.throwdm
    (fun d s => do
      let _ ← integerAction (array.heapWholeCopy pure d.handle s.handle)
      pure d)
    (fun d e => pure (scalarPreprocess d e))
    (fun _ => integerIndices dest)
    (fun e _ => scalarArgument e.args)
    (fun d i x => integerWrite d x i) dest bc

def scalarCopytoSpecial (p : ScalarPrimitives) (dest : Vec) (bc : CopyExpr) : M Vec :=
  broadcast.Material.m983
    (fun _ : Unit => true) (fun args : List I => decide (args.length = 1))
    (fun e => broadcast.Flatten.isFlatArgs
      (S := Option broadcast.Style.Style) (X := Axis) (e.args.map broadcast.Flatten.Tree.leaf))
    id scalarArgument fillInteger (fun e => { e with style := none }) (scalarCopyto p) dest bc

def zeroCounts (p : ScalarPrimitives) (dest : Vec) : M Vec :=
  broadcast.Material.m924 (fun d : Vec => pure d.axes)
    makeScalarBroadcast () (int.lit .i64 0)
    (fun bc => pure (broadcast.Lazy.m319 bc))
    (fun d bc =>
      broadcast.Material.m928 combinedStyle
        (fun styleAction d e => do
          let style ← styleAction
          broadcast.Material.m932 (fun d : Vec => pure d.axes)
            (fun e => pure (broadcast.Lazy.m319 e))
            (fun d e => scalarCopytoSpecial p d ⟨some e.style, e.f, e.args, e.axes⟩) style d e)
        d bc) dest

structure RadixSortPassOps (m : Type → Type) (V C : Type) where
  zeroCounts : C → m C
  read : V → I → m U
  write : V → U → I → m Unit
  range : I → I → m (List I)
  readCount : C → U → m I
  writeCount : C → U → I → m Unit
  setFirstTarget : C → I → m Unit
  cumsum : C → C → m C
/--
Julia source: base/sort.jl:1402-1429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function radix_sort_pass!(t, lo, hi, offset, counts, v, shift, chunk_size)
    mask = UInt(1) << chunk_size - 1  # mask is defined in pass so that the compiler
    @inbounds begin                   #  ↳ knows it's shape
        # counts[2:mask+2] will store the number of elements that fall into each bucket.
        # if chunk_size = 8, counts[2] is bucket 0x00 and counts[257] is bucket 0xff.
        counts .= 0
        for k in lo:hi
            x = v[k]                  # lookup the element
            i = (x >> shift)&mask + 2 # compute its bucket's index for this pass
            counts[i] += 1            # increment that bucket's count
        end

        counts[1] = lo + offset       # set target index for the first bucket
        cumsum!(counts, counts)       # set target indices for subsequent buckets
        # counts[1:mask+1] now stores indices where the first member of each bucket
        # belongs, not the number of elements in each bucket. We will put the first element
        # of bucket 0x00 in t[counts[1]], the next element of bucket 0x00 in t[counts[1]+1],
        # and the last element of bucket 0x00 in t[counts[2]-1].

        for k in lo:hi
            x = v[k]                  # lookup the element
            i = (x >> shift)&mask + 1 # compute its bucket's index for this pass
            j = counts[i]             # lookup the target index
            t[j] = x                  # put the element where it belongs
            counts[i] = j + 1         # increment the target index for the next
        end                           #  ↳ element in this bucket
    end
end
```
-/
def radixSortPass [Monad m] (ops : RadixSortPassOps m V C)
    (target : V) (lo hi offset : I) (counts : C) (source : V)
    (shift : I) (chunk : JInt .u8) : m Unit := do
  let mask := int.sub (int.shl_BitInteger_BitUnsigned (int.lit .u64 1) chunk)
    (int.lit .u64 1)
  let counts ← ops.zeroCounts counts
  for index in (← ops.range lo hi) do
    let value ← ops.read source index
    let bucket := int.add (int.band (int.shr_Int value shift) mask) (int.lit .u64 2)
    let count ← ops.readCount counts bucket
    ops.writeCount counts bucket (int.add count (int.lit .i64 1))
  ops.setFirstTarget counts (int.add lo offset)
  let counts ← ops.cumsum counts counts
  for index in (← ops.range lo hi) do
    let value ← ops.read source index
    let bucket := int.add (int.band (int.shr_Int value shift) mask) (int.lit .u64 1)
    let targetIndex ← ops.readCount counts bucket
    ops.write target value targetIndex
    ops.writeCount counts bucket (int.add targetIndex (int.lit .i64 1))

def unsignedIndex (index : U) : M I :=
  liftM ((array.indexConvert index).mapError Error.array)

def nativeRadixPassOps (p : ScalarPrimitives) (cumsum : Vec → Vec → M Vec) :
    RadixSortPassOps M Vec Vec where
  zeroCounts := zeroCounts p
  read := unsignedRead
  write := unsignedWrite
  range := fun lo hi => liftM (nativeRange lo hi)
  readCount := fun v i => do integerRead v (← unsignedIndex i)
  writeCount := fun v i x => do integerWrite v x (← unsignedIndex i)
  setFirstTarget := fun v first => integerWrite v first (int.lit .i64 1)
  cumsum := cumsum

structure RadixSortOps where
  pass : RadixSortPassOps M Vec Vec
  heuristic : I → I → U → promotion.JlPartial (JInt .u8)
  allocateCounts : I → M Vec

/-- Exact source while-loop, threading the shared heaps after each complete pass.
none is nonreturning, never a successful fuel-exhaustion result. -/
def radixSortLoop (ops : RadixSortOps) (vector scratch : Vec)
    (lo hi offset : I) (bits : U) (chunk : JInt .u8) (counts : Vec) (shift : I)
    (heap : Heap) : Option (Except Error (Bool × Heap)) :=
  match radixSortPass ops.pass scratch lo hi offset counts vector shift chunk heap with
  | .error error => some (.error error)
  | .ok (_, heap) =>
    let shift := int.add shift (int.widenTo .i64 chunk)
    if !(int.lt shift bits) then some (.ok (false, heap))
    else
      match radixSortPass ops.pass vector (int.add lo offset) (int.add hi offset)
          (int.neg offset) counts scratch shift chunk heap with
      | .error error => some (.error error)
      | .ok (_, heap) =>
        let shift := int.add shift (int.widenTo .i64 chunk)
        if !(int.lt shift bits) then some (.ok (true, heap))
        else radixSortLoop ops vector scratch lo hi offset bits chunk counts shift heap
partial_fixpoint

/--
Julia source: base/sort.jl:1384-1401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function radix_sort!(v::AbstractVector{U}, lo::Integer, hi::Integer, bits::Unsigned,
                     t::AbstractVector{U}, offset::Integer,
                     chunk_size=radix_chunk_size_heuristic(lo, hi, bits)) where U <: Unsigned
    # bits is unsigned for performance reasons.
    counts = Vector{Int}(undef, 1 << chunk_size + 1) # TODO use scratch for this

    shift = 0
    while true
        @noinline radix_sort_pass!(t, lo, hi, offset, counts, v, shift, chunk_size)
        # the latest data resides in t
        shift += chunk_size
        shift < bits || return false
        @noinline radix_sort_pass!(v, lo+offset, hi+offset, -offset, counts, t, shift, chunk_size)
        # the latest data resides in v
        shift += chunk_size
        shift < bits || return true
    end
end
```
-/
def radixSortBang (ops : RadixSortOps) (vector scratch : Vec) (lo hi offset : I)
    (bits : U) (chunk : Option (JInt .u8)) (heap : Heap) :
    Option (Except Error (Bool × Heap)) :=
  let resolved : Option (Jl (JInt .u8)) := match chunk with
    | some chunk => some (.ok chunk)
    | none => (ops.heuristic lo hi bits).run
  match resolved with
  | none => none
  | some (.error error) => some (.error (.julia error))
  | some (.ok chunk) =>
    let size := int.add (int.shl_BitInteger_BitUnsigned (int.lit .i64 1) chunk)
      (int.lit .i64 1)
    match ops.allocateCounts size heap with
    | .error error => some (.error error)
    | .ok (counts, heap) =>
      radixSortLoop ops vector scratch lo hi offset bits chunk counts (int.lit .i64 0) heap

def nativeRadixOps (p : ScalarPrimitives) (cumsum : Vec → Vec → M Vec)
    (ieee : math.IEEEOps .f64) (log : U → Jl F64) : RadixSortOps where
  pass := nativeRadixPassOps p cumsum
  heuristic := radixChunkSizeHeuristic ieee log
  allocateCounts := fun n =>
    integerAction (array.heapVectorAllocate intTyLayout .i64 n)

def CumsumLaws (cumsum : Vec → Vec → M Vec) : Prop :=
  ∀ dest source heap, dest = source →
    (∃ xs : List I, heap.integers[source.handle]? = some (xs.map some)) →
    ∃ output after,
      cumsum dest source heap = .ok (output, after) ∧ output = dest ∧
      after.unsigned = heap.unsigned ∧
      (∀ handle, handle ≠ dest.handle → after.integers[handle]? = heap.integers[handle]?) ∧
      ∀ xs : List I, heap.integers[source.handle]? = some (xs.map some) →
        after.integers[dest.handle]? =
          some ((xs.scanl int.add (int.lit .i64 0)).tail.map some)

structure SubArraySortOps (View Parent ParentVector K Alg O Kws R E : Type) where
  range : Kws → Except E (K × K)
  parent : View → Parent
  parentIsArray : Parent → Bool
  parentIsVector : Parent → Bool
  spanLessThan100 : K → K → Bool
  offsetIsZero : View → Bool
  vectorizeParent : Parent → Except E ParentVector
  nextAlgorithm : Alg → Alg
  sortView : View → Alg → O → Kws → Except E R
  sortParent : ParentVector → Alg → O → Kws → Except E R

/--
Julia source: base/sort.jl:559-559 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sort!(v::AbstractVector, a::SubArrayOptimization, o::Ordering, kw) = _sort!(v, a.next, o, kw)
```
-/
def sortSubArrayFallback {V Alg O Kws R E : Type}
    (sort : V → Alg → O → Kws → Except E R) (getNext : Alg → Alg)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E R :=
  sort vector (getNext algorithm) order keywords

/--
Julia source: base/sort.jl:560-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::UnwrappableSubArray, a::SubArrayOptimization, o::Ordering, kw)
    @getkw lo hi
    # @assert v.stride1 == 1
    parent = v.parent
    if parent isa Array && !(parent isa Vector) && hi - lo < 100 || !iszero(v.offset1)
        # vec(::Array{T, ≠1}) allocates and is therefore somewhat expensive.
        # We don't want that for small inputs.

        # Additionally, if offset1 is non-zero, then this optimization is incompatible with
        # algorithms that track absolute first and last indices (e.g. ScratchQuickSort)
        _sort!(v, a.next, o, kw)
    else
        _sort!(vec(parent), a.next, o, kw)
    end
end
```
-/
def sortSubArrayUnwrappable {View Parent ParentVector K Alg O Kws R E : Type}
    (ops : SubArraySortOps View Parent ParentVector K Alg O Kws R E)
    (view : View) (nextAlgorithm : Alg) (order : O) (keywords : Kws) :
    Except E R := do
  let (lo, hi) ← ops.range keywords
  let parent := ops.parent view
  if (ops.parentIsArray parent && !ops.parentIsVector parent &&
      ops.spanLessThan100 lo hi) || !ops.offsetIsZero view then
    ops.sortView view (ops.nextAlgorithm nextAlgorithm) order keywords
  else
    let vector ← ops.vectorizeParent parent
    ops.sortParent vector (ops.nextAlgorithm nextAlgorithm) order keywords

structure UIntMappableSortOps (V Alg O Kws R E : Type) where
  elementType : V → Type
  uintMappable : Type → O → Option Type
  yesAlgorithm : Alg → Alg
  noAlgorithm : Alg → Alg
  sort : V → Alg → O → Kws → Except E R

/--
Julia source: base/sort.jl:774-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::IsUIntMappable, o::Ordering, kw)
    if UIntMappable(eltype(v), o) !== nothing
        _sort!(v, a.yes, o, kw)
    else
        _sort!(v, a.no, o, kw)
    end
end
```
-/
def sortIsUIntMappable {V Alg O Kws R E : Type}
    (ops : UIntMappableSortOps V Alg O Kws R E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E R := do
  match ops.uintMappable (ops.elementType vector) order with
  | some _ => ops.sort vector (ops.yesAlgorithm algorithm) order keywords
  | none => ops.sort vector (ops.noAlgorithm algorithm) order keywords

structure SmallSortOps (V Alg O K Kws R E : Type) where
  range : Kws → Except E (K × K)
  spanLessThan : K → K → Nat → Bool
  smallAlgorithm : Alg → Alg
  bigAlgorithm : Alg → Alg
  sort : V → Alg → O → Kws → Except E R

/--
Julia source: base/sort.jl:795-802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::Small{N}, o::Ordering, kw) where N
    @getkw lo hi
    if (hi-lo) < N
        _sort!(v, a.small, o, kw)
    else
        _sort!(v, a.big, o, kw)
    end
end
```
-/
def sortSmall {V Alg O K Kws R E : Type}
    (ops : SmallSortOps V Alg O K Kws R E) (vector : V) (algorithm : Alg)
    (threshold : Nat) (order : O) (keywords : Kws) : Except E R := do
  let (lo, hi) ← ops.range keywords
  let selected := if ops.spanLessThan lo hi threshold
    then ops.smallAlgorithm algorithm else ops.bigAlgorithm algorithm
  ops.sort vector selected order keywords

/--
Julia source: base/sort.jl:933-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sort!(v::AbstractVector, a::ConsiderCountingSort, o::Ordering, kw) = _sort!(v, a.next, o, kw)
```
-/
def sortConsiderCountingOther {V Alg O Kws R E : Type}
    (sort : V → Alg → O → Kws → Except E R) (getNext : Alg → Alg)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E R :=
  sort vector (getNext algorithm) order keywords

structure ConsiderRadixSortOps (V A K U Alg O Kws R E : Type) where
  rangeAndExtrema : Kws → Except E (K × K × A × A)
  uintMap : A → O → U
  subtractUnsigned : U → U → U
  topSetBit : U → U
  unsignedToNat : U → Nat
  elementSize : V → Nat
  logarithmOfSpan : K → K → Float
  floatOfNat : Nat → Float
  multiplyFloat : Float → Float → Float
  addFloat : Float → Float → Float
  lessFloat : Float → Float → Bool
  radixAlgorithm : Alg → Alg
  nextAlgorithm : Alg → Alg
  sort : V → Alg → O → Kws → Except E R

/--
Julia source: base/sort.jl:983-992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::ConsiderRadixSort, o::DirectOrdering, kw)
    @getkw lo hi mn mx
    urange = uint_map(mx, o)-uint_map(mn, o)
    bits = unsigned(top_set_bit(urange))
    if sizeof(eltype(v)) <= 8 && bits+70 < 22log(hi-lo)
        _sort!(v, a.radix, o, kw)
    else
        _sort!(v, a.next, o, kw)
    end
end
```
-/
def sortConsiderRadix {V A K U Alg O Kws R E : Type}
    (ops : ConsiderRadixSortOps V A K U Alg O Kws R E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E R := do
  let (lo, hi, minimum, maximum) ← ops.rangeAndExtrema keywords
  let unsignedRange := ops.subtractUnsigned
    (ops.uintMap maximum order) (ops.uintMap minimum order)
  let bits := ops.unsignedToNat (ops.topSetBit unsignedRange)
  let lhs := ops.floatOfNat (bits + 70)
  let rhs := ops.multiplyFloat (ops.floatOfNat 22) (ops.logarithmOfSpan lo hi)
  let selected := if ops.elementSize vector ≤ 8 && ops.lessFloat lhs rhs
    then ops.radixAlgorithm algorithm else ops.nextAlgorithm algorithm
  ops.sort vector selected order keywords

/--
Julia source: base/sort.jl:1580-1590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _DEFAULT_ALGORITHMS_FOR_VECTORS = InitialOptimizations(
    IsUIntMappable(
        Small{40}(
            CheckSorted(
                ComputeExtrema(
                    ConsiderCountingSort(
                        ConsiderRadixSort(
                            Small{80}(
                                ScratchQuickSort())))))),
        StableCheckSorted(
            ScratchQuickSort())))
```
-/
def defaultVectorAlgorithms {Target Index : Type} : Algorithm Target Index :=
  initialOptimizations (.isUIntMappable
    (.small 40 .insertion (.checkSorted (.computeExtrema
      (considerCountingSort (considerRadixSort (.small 80 .insertion scratchQuickDefault))))))
    (.stableCheckSorted scratchQuickDefault))

/--
Julia source: base/sort.jl:1592-1593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sort!(v::AbstractVector, ::Union{DefaultStable, DefaultUnstable}, o::Ordering, kw) =
    _sort!(v, _DEFAULT_ALGORITHMS_FOR_VECTORS, o, kw)
```
-/
def sortDefaultAlgorithm {V Target Index O Kws R E : Type}
    (sort : V → Algorithm Target Index → O → Kws → Except E R)
    (vector : V) (order : O) (keywords : Kws) : Except E R :=
  sort vector defaultVectorAlgorithms order keywords

structure CheckSortedOps (V Alg O K Kws Scratch E : Type) where
  rangeAndScratch : Kws → Except E (K × K × Scratch)
  difference : K → K → Int
  isSorted : V → K → K → O → Except E Bool
  reverseOrder : O → O
  reverse : V → K → K → Except E V
  nextAlgorithm : Alg → Alg
  sort : V → Alg → O → Kws → Except E (V × Scratch)

/--
Julia source: base/sort.jl:864-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::CheckSorted, o::Ordering, kw)
    @getkw lo hi scratch

    # For most arrays, a presorted check is cheap (overhead < 5%) and for most large
    # arrays it is essentially free (<1%).
    _issorted(v, lo, hi, o) && return scratch

    # For most large arrays, a reverse-sorted check is essentially free (overhead < 1%)
    if hi-lo >= 500 && _issorted(v, lo, hi, ReverseOrdering(o))
        # If reversing is valid, do so. This violates stability.
        reverse!(v, lo, hi)
        return scratch
    end

    _sort!(v, a.next, o, kw)
end
```
-/
def sortCheckSorted {V Alg O K Kws Scratch E : Type}
    (ops : CheckSortedOps V Alg O K Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E (V × Scratch) := do
  let (lo, hi, scratch) ← ops.rangeAndScratch keywords
  let sorted ← ops.isSorted vector lo hi order
  if sorted then
    pure (vector, scratch)
  else if ops.difference hi lo ≥ 500 then
    let reverseSorted ← ops.isSorted vector lo hi (ops.reverseOrder order)
    if reverseSorted then
      let reversed ← ops.reverse vector lo hi
      pure (reversed, scratch)
    else
      ops.sort vector (ops.nextAlgorithm algorithm) order keywords
  else
    ops.sort vector (ops.nextAlgorithm algorithm) order keywords

/-- A source local can initially have the keyword bound's type and then acquire
its promoted type after arithmetic with the Int64 literal one. -/
inductive PromotingIndex (Initial Promoted : Type) where
  | initial (value : Initial)
  | promoted (value : Promoted)

def PromotingIndex.unwrap {T : Type} : PromotingIndex T T → T
  | .initial value => value
  | .promoted value => value

structure IndexStep (Initial Promoted : Type) where
  initialStep : Initial → Promoted
  promotedStep : Promoted → Promoted

def stepIndex {Initial Promoted : Type} (ops : IndexStep Initial Promoted) :
    PromotingIndex Initial Promoted → PromotingIndex Initial Promoted
  | .initial value => .promoted (ops.initialStep value)
  | .promoted value => .promoted (ops.promotedStep value)

def nativeSubtractOne {t : IntTy} (value : JInt t) : JInt (t.promote .i64) :=
  int.binop int.sub value (int.lit .i64 1)

private theorem repeatedPromotion (t : IntTy) :
    (t.promote .i64).promote .i64 = t.promote .i64 := by cases t <;> rfl

private def castRepeatedPromotion {t : IntTy}
    (value : JInt ((t.promote .i64).promote .i64)) : JInt (t.promote .i64) :=
  cast (congrArg JInt (repeatedPromotion t)) value

def nativeIncrement (t : IntTy) : IndexStep (JInt t) (JInt (t.promote .i64)) where
  initialStep := nativeAddOne
  promotedStep := fun value => castRepeatedPromotion (t := t) (nativeAddOne value)

def nativeDecrement (t : IntTy) : IndexStep (JInt t) (JInt (t.promote .i64)) where
  initialStep := nativeSubtractOne
  promotedStep := fun value => castRepeatedPromotion (t := t) (nativeSubtractOne value)

structure ComputeExtremaOps (V Alg Lo Hi Start Index A Kws Scratch E : Type)
    (O : Type u) where
  rangeAndScratch : V → O → Kws → Except E (Kws × Lo × Hi × Scratch)
  nextIndex : Lo → Start
  range : Start → Hi → List Index
  readFirst : V → Lo → Except E A
  read : V → Index → Except E A
  less : O → A → A → Except E Bool
  appendExtrema : Kws → A → A → Kws
  nextAlgorithm : Alg → Alg
  sort : V → Alg → O → Kws → Except E Scratch

/--
Julia source: base/sort.jl:893-905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::ComputeExtrema, o::Ordering, kw)
    @getkw lo hi scratch
    mn = mx = v[lo]
    @inbounds for i in (lo+1):hi
        vi = v[i]
        lt(o, vi, mn) && (mn = vi)
        lt(o, mx, vi) && (mx = vi)
    end

    lt(o, mn, mx) || return scratch # all same

    _sort!(v, a.next, o, (;kw..., mn, mx))
end
```
-/
def sortComputeExtrema {V Alg Lo Hi Start Index A Kws Scratch E : Type} {O : Type u}
    (ops : ComputeExtremaOps V Alg Lo Hi Start Index A Kws Scratch E O)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) : Except E Scratch := do
  let (keywords, lo, hi, scratch) ← ops.rangeAndScratch vector order keywords
  let first ← ops.readFirst vector lo
  let mut minimum := first
  let mut maximum := first
  for index in ops.range (ops.nextIndex lo) hi do
    let value ← ops.read vector index
    if ← ops.less order value minimum then minimum := value
    if ← ops.less order maximum value then maximum := value
  if !(← ops.less order minimum maximum) then
    pure scratch
  else
    ops.sort vector (ops.nextAlgorithm algorithm) order
      (ops.appendExtrema keywords minimum maximum)
structure BoolSortOps (V K O Kws Scratch R E : Type) where
  less : O → Bool → Bool → Except E Bool
  rangeAndScratch : Kws → Except E (K × K × Scratch)
  range : K → K → List K
  read : V → K → Except E Bool
  firstSegmentEnd : K → Nat → K
  secondSegmentStart : K → Nat → K
  setSegment : V → K → K → Bool → Except E V
  returnVector : V → R
  returnScratch : V → Scratch → R

/--
Julia source: base/sort.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sort!(v::AbstractVector, a::BoolOptimization, o::Ordering, kw) = _sort!(v, a.next, o, kw)
```
-/
def sortBoolOther {V Alg O Kws R E : Type}
    (sort : V → Alg → O → Kws → Except E R) (getNext : Alg → Alg)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E R :=
  sort vector (getNext algorithm) order keywords

/--
Julia source: base/sort.jl:746-758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector{Bool}, ::BoolOptimization, o::Ordering, kw)
    first = lt(o, false, true) ? false : lt(o, true, false) ? true : return v
    @getkw lo hi scratch
    count = 0
    @inbounds for i in lo:hi
        if v[i] == first
            count += 1
        end
    end
    @inbounds v[lo:lo+count-1] .= first
    @inbounds v[lo+count:hi] .= !first
    scratch
end
```
-/
def sortBoolVector {V K O Kws Scratch R E : Type}
    (ops : BoolSortOps V K O Kws Scratch R E)
    (vector : V) (order : O) (keywords : Kws) : Except E R := do
  let first ← do
    if ← ops.less order false true then pure (some false)
    else if ← ops.less order true false then pure (some true)
    else pure none
  match first with
  | none => pure (ops.returnVector vector)
  | some first =>
    let (lo, hi, scratch) ← ops.rangeAndScratch keywords
    let mut count := 0
    for index in ops.range lo hi do
      if (← ops.read vector index) == first then
        count := count + 1
    let firstFilled ← ops.setSegment vector lo (ops.firstSegmentEnd lo count) first
    let secondFilled ← ops.setSegment firstFilled (ops.secondSegmentStart lo count) hi (!first)
    pure (ops.returnScratch secondFilled scratch)
structure MissingSortOps
    (V Data WrappedV WrappedData Lo Hi PromotedLo PromotedHi DirectLo DirectHi
      LoopIndex DataIndex A Alg Kws DirectKws PermKws Scratch E CV : Type)
    (O PermOrder WrappedPermOrder : Type u) where
  range : V → O → Kws → Except E (Kws × Lo × Hi)
  elementType : V → Type
  dataElementType : Data → Type
  hasMissingSupertype : Type → Bool
  nonMissingType : Type → Type
  sameType : Type → Type → Bool
  isIntegerType : Type → Bool
  isDirectOrdering : O → Bool
  permutationDetails : O → Option (PermOrder × Data)
  isDirectPermutationOrder : PermOrder → Bool
  isReversePermutationOrder : PermOrder → Bool
  allIdentityIndices : V → Data → Except E Bool
  sendMissingToEnd : V → O → Lo → Hi → Except E (V × DirectLo × DirectHi)
  wrapVectorWithoutMissing : V → Except E WrappedV
  wrapDataWithoutMissing : Data → Except E WrappedData
  indexRange : Lo → Hi → List LoopIndex
  eachDataIndex : Data → Except E CV
  dataIndexAt : CV → LoopIndex → Except E DataIndex
  readData : Data → DataIndex → Except E A
  isMissing : A → Except E Bool
  writeLowIndex : V → PromotingIndex Lo PromotedLo → LoopIndex → Except E V
  writeHighIndex : V → PromotingIndex Hi PromotedHi → LoopIndex → Except E V
  incrementLow : IndexStep Lo PromotedLo
  decrementHigh : IndexStep Hi PromotedHi
  reverse : V → PromotingIndex Lo PromotedLo → Hi → Except E V
  permutationOrder : PermOrder → WrappedData → WrappedPermOrder
  nextAlgorithm : Alg → Alg
  appendDirectBounds : Kws → DirectLo → DirectHi → DirectKws
  appendPermutationBounds : Kws → PromotingIndex Lo PromotedLo →
    PromotingIndex Hi PromotedHi → PermKws
  sortWrapped : WrappedV → Alg → O → DirectKws → Except E Scratch
  sortVector : V → Alg → O → Kws → Except E Scratch
  sortPermutation : V → Alg → WrappedPermOrder → PermKws → Except E Scratch

/--
Julia source: base/sort.jl:651-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::MissingOptimization, o::Ordering, kw)
    @getkw lo hi
    if o isa DirectOrdering && eltype(v) >: Missing && nonmissingtype(eltype(v)) != eltype(v)
        lo, hi = send_to_end!(ismissing, v, o; lo, hi)
        _sort!(WithoutMissingVector(v, unsafe=true), a.next, o, (;kw..., lo, hi))
    elseif o isa Perm && o.order isa DirectOrdering && eltype(v) <: Integer &&
                eltype(o.data) >: Missing && nonmissingtype(eltype(o.data)) != eltype(o.data) &&
                all(i === j for (i,j) in zip(v, eachindex(o.data)))
        # TODO make this branch known at compile time
        # This uses a custom function because we need to ensure stability of both sides and
        # we can assume v is equal to eachindex(o.data) which allows a copying partition
        # without allocations.
        lo_i, hi_i = lo, hi
        cv = eachindex(o.data) # equal to copy(v)
        for i in lo:hi
            x = o.data[cv[i]]
            if ismissing(x) == (o.order == Reverse) # should x go at the beginning/end?
                v[lo_i] = i
                lo_i += 1
            else
                v[hi_i] = i
                hi_i -= 1
            end
        end
        reverse!(v, lo_i, hi)
        if o.order == Reverse
            lo = lo_i
        else
            hi = hi_i
        end

        _sort!(v, a.next, Perm(o.order, WithoutMissingVector(o.data, unsafe=true)), (;kw..., lo, hi))
    else
        _sort!(v, a.next, o, kw)
    end
end
```
-/
def sortMissingOptimization
    {V Data WrappedV WrappedData Lo Hi PromotedLo PromotedHi DirectLo DirectHi
      LoopIndex DataIndex A Alg Kws DirectKws PermKws Scratch E CV : Type}
    {O PermOrder WrappedPermOrder : Type u}
    (ops : MissingSortOps V Data WrappedV WrappedData Lo Hi PromotedLo PromotedHi
      DirectLo DirectHi LoopIndex DataIndex A Alg Kws DirectKws PermKws Scratch E CV
      O PermOrder WrappedPermOrder)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) : Except E Scratch := do
  let (keywords, lo, hi) ← ops.range vector order keywords
  let vectorType := ops.elementType vector
  if ops.isDirectOrdering order && ops.hasMissingSupertype vectorType &&
      !ops.sameType (ops.nonMissingType vectorType) vectorType then
    let (vector, lo, hi) ← ops.sendMissingToEnd vector order lo hi
    let withoutMissing ← ops.wrapVectorWithoutMissing vector
    ops.sortWrapped withoutMissing (ops.nextAlgorithm algorithm) order
      (ops.appendDirectBounds keywords lo hi)
  else
    match ops.permutationDetails order with
    | some (permutationOrder, data) =>
      let dataType := ops.dataElementType data
      if ops.isDirectPermutationOrder permutationOrder && ops.isIntegerType vectorType &&
          ops.hasMissingSupertype dataType && !ops.sameType (ops.nonMissingType dataType) dataType then
        let identity ← ops.allIdentityIndices vector data
        if identity then
          let mut loIndex : PromotingIndex Lo PromotedLo := .initial lo
          let mut hiIndex : PromotingIndex Hi PromotedHi := .initial hi
          let indices ← ops.eachDataIndex data
          let mut vector := vector
          for i in ops.indexRange lo hi do
            let dataIndex ← ops.dataIndexAt indices i
            let value ← ops.readData data dataIndex
            let missing ← ops.isMissing value
            if missing == ops.isReversePermutationOrder permutationOrder then
              vector ← ops.writeLowIndex vector loIndex i
              loIndex := stepIndex ops.incrementLow loIndex
            else
              vector ← ops.writeHighIndex vector hiIndex i
              hiIndex := stepIndex ops.decrementHigh hiIndex
          vector ← ops.reverse vector loIndex hi
          let (lo, hi) := if ops.isReversePermutationOrder permutationOrder then
            (loIndex, PromotingIndex.initial hi)
            else (PromotingIndex.initial lo, hiIndex)
          let withoutMissing ← ops.wrapDataWithoutMissing data
          ops.sortPermutation vector (ops.nextAlgorithm algorithm)
            (ops.permutationOrder permutationOrder withoutMissing)
            (ops.appendPermutationBounds keywords lo hi)
        else ops.sortVector vector (ops.nextAlgorithm algorithm) order keywords
      else ops.sortVector vector (ops.nextAlgorithm algorithm) order keywords
    | none => ops.sortVector vector (ops.nextAlgorithm algorithm) order keywords
structure IEEEFloatSortOps
    (V Data UnsignedVector K Alg O PermOrder NextOrder Kws Scratch E : Type) where
  range : Kws → Except E (K × K)
  elementType : V → Type
  dataElementType : Data → Type
  isConcreteIEEEFloat : Type → Bool
  isDirectOrdering : O → Bool
  isIntegerVector : V → Bool
  permutationDetails : O → Option (PermOrder × Data)
  isDirectPermutationOrder : PermOrder → Bool
  reverseOrdering : O → O
  forwardOrdering : O → O
  sendNaNs : V → O → K → K → Except E (V × K × K)
  sendAfterZero : V → O → K → K → Except E (V × K)
  reinterpretVector : V → Except E UnsignedVector
  syncUnsignedAlias : V → UnsignedVector → Except E UnsignedVector
  restoreVectorAlias : V → UnsignedVector → Except E V
  nextIndex : K → K
  sortUnsigned : UnsignedVector → Alg → O → Kws →
    Except E (UnsignedVector × Option Scratch)
  sendPermutationNaNs : V → Data → PermOrder → K → K → Except E (V × K × K)
  reinterpretData : Data → Except E UnsignedVector
  sendPermutationAfterZero : V → Data → PermOrder → K → K → Except E (V × K)
  reversePermutationOrder : PermOrder → PermOrder
  forwardPermutationOrder : PermOrder → PermOrder
  makePermutationOrder : PermOrder → UnsignedVector → NextOrder
  sortPermutation : V → Alg → NextOrder → Kws → Except E (V × Option Scratch)
  nextAlgorithm : Alg → Alg
  keywordsWithBounds : Kws → K → K → Kws
  keywordsWithBoundsAndScratch : Kws → K → K → Option Scratch → Kws
  sortFallback : V → Alg → O → Kws → Except E (V × Option Scratch)

/--
Julia source: base/sort.jl:706-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::IEEEFloatOptimization, o::Ordering, kw)
    @getkw lo hi
    if is_concrete_IEEEFloat(eltype(v)) && o isa DirectOrdering
        lo, hi = send_to_end!(isnan, v, o, true; lo, hi)
        iv = reinterpret(uinttype(eltype(v)), v)
        j = send_to_end!(x -> after_zero(o, x), v; lo, hi)
        scratch = _sort!(iv, a.next, Reverse, (;kw..., lo, hi=j))
        if scratch === nothing # Union split
            _sort!(iv, a.next, Forward, (;kw..., lo=j+1, hi, scratch))
        else
            _sort!(iv, a.next, Forward, (;kw..., lo=j+1, hi, scratch))
        end
    elseif eltype(v) <: Integer && o isa Perm && o.order isa DirectOrdering && is_concrete_IEEEFloat(eltype(o.data))
        lo, hi = send_to_end!(i -> isnan(@inbounds o.data[i]), v, o.order, true; lo, hi)
        ip = reinterpret(uinttype(eltype(o.data)), o.data)
        j = send_to_end!(i -> after_zero(o.order, @inbounds o.data[i]), v; lo, hi)
        scratch = _sort!(v, a.next, Perm(Reverse, ip), (;kw..., lo, hi=j))
        if scratch === nothing # Union split
            _sort!(v, a.next, Perm(Forward, ip), (;kw..., lo=j+1, hi, scratch))
        else
            _sort!(v, a.next, Perm(Forward, ip), (;kw..., lo=j+1, hi, scratch))
        end
    else
        _sort!(v, a.next, o, kw)
    end
end
```
-/
def sortIEEEFloatOptimization
    {V Data UnsignedVector K Alg O PermOrder NextOrder Kws Scratch E : Type}
    (ops : IEEEFloatSortOps V Data UnsignedVector K Alg O PermOrder NextOrder Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E (V × Option Scratch) := do
  let (lo, hi) ← ops.range keywords
  if ops.isConcreteIEEEFloat (ops.elementType vector) && ops.isDirectOrdering order then
    let (vector, lo, hi) ← ops.sendNaNs vector order lo hi
    let unsignedView ← ops.reinterpretVector vector
    let (vector, split) ← ops.sendAfterZero vector order lo hi
    let unsignedVector ← ops.syncUnsignedAlias vector unsignedView
    let (unsignedVector, scratch) ← ops.sortUnsigned unsignedVector (ops.nextAlgorithm algorithm)
      (ops.reverseOrdering order) (ops.keywordsWithBounds keywords lo split)
    let (sortedBits, scratch) ← match scratch with
      | none =>
        ops.sortUnsigned unsignedVector (ops.nextAlgorithm algorithm)
          (ops.forwardOrdering order)
          (ops.keywordsWithBoundsAndScratch keywords (ops.nextIndex split) hi scratch)
      | some _ =>
        ops.sortUnsigned unsignedVector (ops.nextAlgorithm algorithm)
          (ops.forwardOrdering order)
          (ops.keywordsWithBoundsAndScratch keywords (ops.nextIndex split) hi scratch)
    let result ← ops.restoreVectorAlias vector sortedBits
    pure (result, scratch)
  else if ops.isIntegerVector vector then
    match ops.permutationDetails order with
    | some (permutationOrder, data) =>
      if ops.isDirectPermutationOrder permutationOrder &&
          ops.isConcreteIEEEFloat (ops.dataElementType data) then
        let (vector, lo, hi) ← ops.sendPermutationNaNs vector data permutationOrder lo hi
        let unsignedData ← ops.reinterpretData data
        let (vector, split) ← ops.sendPermutationAfterZero vector data permutationOrder lo hi
        let reverseOrder := ops.makePermutationOrder
          (ops.reversePermutationOrder permutationOrder) unsignedData
        let (vector, scratch) ← ops.sortPermutation vector (ops.nextAlgorithm algorithm) reverseOrder
          (ops.keywordsWithBounds keywords lo split)
        let forwardOrder := ops.makePermutationOrder
          (ops.forwardPermutationOrder permutationOrder) unsignedData
        match scratch with
        | none =>
          ops.sortPermutation vector (ops.nextAlgorithm algorithm) forwardOrder
            (ops.keywordsWithBoundsAndScratch keywords (ops.nextIndex split) hi scratch)
        | some _ =>
          ops.sortPermutation vector (ops.nextAlgorithm algorithm) forwardOrder
            (ops.keywordsWithBoundsAndScratch keywords (ops.nextIndex split) hi scratch)
      else
        ops.sortFallback vector (ops.nextAlgorithm algorithm) order keywords
    | none => ops.sortFallback vector (ops.nextAlgorithm algorithm) order keywords
  else
    ops.sortFallback vector (ops.nextAlgorithm algorithm) order keywords
structure ConsiderCountingOps (V T U K Alg O Kws R E : Type) where
  rangeAndExtrema : Kws → Except E (K × K × T × T)
  isReverse : O → Bool
  wrapSubtract : T → T → T
  maybeUnsigned : T → U
  span : K → K → Int
  elementSize : V → Nat
  rangeLessThan : U → Int → Bool
  countingAlgorithm : Alg → Alg
  nextAlgorithm : Alg → Alg
  sort : V → Alg → O → Kws → Except E R

/--
Julia source: base/sort.jl:923-932 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector{<:Integer}, a::ConsiderCountingSort, o::DirectOrdering, kw)
    @getkw lo hi mn mx
    range = maybe_unsigned(o === Reverse ? mn -% mx : mx -% mn)

    if range < (sizeof(eltype(v)) > 8 ? 5(hi-lo)-100 : div(hi-lo, 2))
        _sort!(v, a.counting, o, kw)
    else
        _sort!(v, a.next, o, kw)
    end
end
```
-/
def sortConsiderCountingInteger {V T U K Alg O Kws R E : Type}
    (ops : ConsiderCountingOps V T U K Alg O Kws R E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E R := do
  let (lo, hi, minimum, maximum) ← ops.rangeAndExtrema keywords
  let range := ops.maybeUnsigned
    (if ops.isReverse order then ops.wrapSubtract minimum maximum
      else ops.wrapSubtract maximum minimum)
  let length := ops.span hi lo
  let threshold := if ops.elementSize vector > 8 then 5 * length - 100 else length / 2
  let selected := if ops.rangeLessThan range threshold
    then ops.countingAlgorithm algorithm else ops.nextAlgorithm algorithm
  ops.sort vector selected order keywords

structure CountingSortOps
    (V K T U C O Kws Scratch E : Type) where
  rangeAndScratch : Kws → Except E (K × K × T × T × Scratch)
  isReverse : O → Bool
  wrapSubtract : T → T → T
  one : T
  maybeUnsigned : T → U
  countLength : U → Nat
  allocateCounts : Nat → Except E C
  range : K → K → List K
  read : V → K → Except E T
  write : V → K → T → Except E V
  bucketForValue : T → T → Nat
  countRead : C → Nat → Except E Nat
  countWrite : C → Nat → Nat → Except E C
  bucketValues : U → List U
  bucketIndex : U → Nat
  bucketValue : U → T
  lastBucketIndex : K → Nat → K
  nextAfterBucket : K → K
  valueNeedsSignedConversion : V → T → Bool
  toSigned : T → T

/--
Julia source: base/sort.jl:948-969 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector{<:Integer}, ::CountingSort, o::DirectOrdering, kw)
    @getkw lo hi mn mx scratch
    range = maybe_unsigned(o === Reverse ? mn -% mx : mx -% mn)
    offs = 1 -% (o === Reverse ? mx : mn)

    counts = fill(0, range+1) # TODO use scratch (but be aware of type stability)
    @inbounds for i = lo:hi
        counts[v[i] +% offs] += 1
    end

    idx = lo
    @inbounds for i = maybe_reverse(o, 1:range+1)
        lastidx = idx + counts[i] - 1
        val = i -% offs
        for j = idx:lastidx
            v[j] = val isa Unsigned && eltype(v) <: Signed ? signed(val) : val
        end
        idx = lastidx + 1
    end

    scratch
end
```
-/
def sortCounting {V K T U C O Kws Scratch E : Type}
    (ops : CountingSortOps V K T U C O Kws Scratch E)
    (vector : V) (order : O) (keywords : Kws) : Except E (V × Scratch) := do
  let (lo, hi, minimum, maximum, scratch) ← ops.rangeAndScratch keywords
  let reverseOrder := ops.isReverse order
  let range := ops.maybeUnsigned
    (if reverseOrder then ops.wrapSubtract minimum maximum
      else ops.wrapSubtract maximum minimum)
  let offset := ops.wrapSubtract ops.one (if reverseOrder then maximum else minimum)
  let mut counts ← ops.allocateCounts (ops.countLength range)
  for index in ops.range lo hi do
    let value ← ops.read vector index
    let bucket := ops.bucketForValue value offset
    let count ← ops.countRead counts bucket
    counts ← ops.countWrite counts bucket (count + 1)
  let rawBuckets := ops.bucketValues range
  let orderedBuckets := if reverseOrder then
    maybeReverseReverse List.reverse rawBuckets
    else maybeReverseForward rawBuckets
  let mut index := lo
  let mut vector := vector
  for bucket in orderedBuckets do
    let count ← ops.countRead counts (ops.bucketIndex bucket)
    let lastIndex := ops.lastBucketIndex index count
    let value := ops.wrapSubtract (ops.bucketValue bucket) offset
    let value := if ops.valueNeedsSignedConversion vector value then ops.toSigned value else value
    for target in ops.range index lastIndex do
      vector ← ops.write vector target value
    index := ops.nextAfterBucket lastIndex
  pure (vector, scratch)
structure RadixSortWrapperOps
    (V α UV U K C Backing O Kws E Result : Type) where
  rangeAndExtrema : Kws → Except E (K × K × α × α × Option Backing)
  uintMapOps : UIntMapVectorOps V UV U K α O E
  subtractUnsigned : U → U → U
  topSetBit : U → JInt .u64
  range : K → K → List K
  windowLength : K → K → Nat
  oneMinus : K → K
  readUnsigned : UV → K → Except E U
  writeUnsigned : UV → K → U → Except E UV
  radixOps : RadixSortOps
  runRadixSort : RadixSortOps → UV → K → K → JInt .u64 → UV → K → Option (Except E (UV × UV × Bool))
  makeScratch : Option Backing → V → Nat → Except E (Backing × Backing)
  reinterpretScratch : Option Type → Backing → Except E UV
  unmapOps : UIntUnmapVectorOps V UV U K α O E
  finish : V → Backing → Result

/--
Julia source: base/sort.jl:1017-1047 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::RadixSort, o::DirectOrdering, kw)
    @getkw lo hi mn mx scratch
    umn = uint_map(mn, o)
    urange = uint_map(mx, o)-umn
    bits = unsigned(top_set_bit(urange))

    # At this point, we are committed to radix sort.
    u = uint_map!(v, lo, hi, o)

    # we subtract umn to avoid radixing over unnecessary bits. For example,
    # Int32[3, -1, 2] uint_maps to UInt32[0x80000003, 0x7fffffff, 0x80000002]
    # which uses all 32 bits, but once we subtract umn = 0x7fffffff, we are left with
    # UInt32[0x00000004, 0x00000000, 0x00000003] which uses only 3 bits, and
    # Float32[2.012, 400.0, 12.345] uint_maps to UInt32[0x3fff3b63, 0x3c37ffff, 0x414570a4]
    # which is reduced to UInt32[0x03c73b64, 0x00000000, 0x050d70a5] using only 26 bits.
    # the overhead for this subtraction is small enough that it is worthwhile in many cases.

    # this is faster than u[lo:hi] .-= umn as of v1.9.0-DEV.100
    @inbounds for i in lo:hi
        u[i] -= umn
    end

    scratch, t = make_scratch(scratch, eltype(v), hi-lo+1)
    tu = reinterpret(eltype(u), t)
    if radix_sort!(u, lo, hi, bits, tu, 1-lo)
        uint_unmap!(v, u, lo, hi, o, umn)
    else
        uint_unmap!(v, tu, lo, hi, o, umn, 1-lo)
    end
    scratch
end
```
-/
def sortRadixAlgorithm {V α UV U K C Backing O Kws E Result : Type}
    (ops : RadixSortWrapperOps V α UV U K C Backing O Kws E Result)
    (vector : V) (order : O) (keywords : Kws) : Option (Except E Result) :=
  match (do
    let (lo, hi, minimum, maximum, scratchArg) ← ops.rangeAndExtrema keywords
    let minimumUnsigned ← ops.uintMapOps.uintMap minimum order
    let maximumUnsigned ← ops.uintMapOps.uintMap maximum order
    let range := ops.subtractUnsigned maximumUnsigned minimumUnsigned
    let bits := ops.topSetBit range
    let mut unsignedVector ← uintMapVectorBang ops.uintMapOps vector lo hi order
    for index in ops.range lo hi do
      let value ← ops.readUnsigned unsignedVector index
      unsignedVector ← ops.writeUnsigned unsignedVector index
        (ops.subtractUnsigned value minimumUnsigned)
    let (scratch, scratchView) ←
      ops.makeScratch scratchArg vector (ops.windowLength lo hi)
    let unsignedType := ops.uintMapOps.uintMappable
      (ops.uintMapOps.elementType vector) order
    let unsignedScratch ← ops.reinterpretScratch unsignedType scratchView
    let indexOffset := ops.oneMinus lo
    pure (lo, hi, minimumUnsigned, unsignedVector, scratch, unsignedScratch, indexOffset, bits)) with
  | .error error => some (.error error)
  | .ok (lo, hi, minimumUnsigned, unsignedVector, scratch, unsignedScratch, indexOffset, bits) =>
    match ops.runRadixSort ops.radixOps unsignedVector lo hi bits unsignedScratch indexOffset with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (unsignedResult, unsignedScratchResult, dataInVector)) =>
      some do
        let resultVector ← if dataInVector then
          uintUnmapVectorBang ops.unmapOps vector unsignedResult lo hi order
            (some minimumUnsigned) none
        else
          uintUnmapVectorBang ops.unmapOps vector unsignedScratchResult lo hi order
            (some minimumUnsigned) (some indexOffset)
        pure (ops.finish resultVector scratch)
structure AlgorithmDisplayOps (IO Alg Name Arg E : Type) where
  print : IO → String → Except E IO
  println : IO → String → Except E IO
  showTypeName : IO → Name → Except E IO
  algorithmTypeName : Alg → Name
  fieldNames : Alg → List Name
  getField : Alg → Name → Arg
  isAlgorithm : Arg → Bool
  toAlgorithm : Arg → Alg
  printArgument : IO → Arg → Except E IO
  showType : IO → Alg → Except E IO
  algorithmDepth : Alg → Nat
  childDepthLess : ∀ algorithm name, name ∈ fieldNames algorithm →
    isAlgorithm (getField algorithm name) = true →
    algorithmDepth (toAlgorithm (getField algorithm name)) < algorithmDepth algorithm

/--
Julia source: base/sort.jl:1617-1617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_type(io::IO, alg::Algorithm) = Base.show_type_name(io, typeof(alg).name)
```
-/
def showAlgorithmType {IO Alg Name Arg E : Type}
    (ops : AlgorithmDisplayOps IO Alg Name Arg E)
    (io : IO) (algorithm : Alg) : Except E IO :=
  ops.showTypeName io (ops.algorithmTypeName algorithm)

/--
Julia source: base/sort.jl:1618-1618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_type(io::IO, alg::Small{N}) where N = print(io, "Base.Sort.Small{$N}")
```
-/
def showSmallAlgorithmType {IO Alg Name Arg E : Type}
    (ops : AlgorithmDisplayOps IO Alg Name Arg E)
    (io : IO) (threshold : Nat) : Except E IO :=
  ops.print io ("Base.Sort.Small{" ++ toString threshold ++ "}")

/--
Julia source: base/sort.jl:1600-1616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_tree(io::IO, alg::Algorithm, cols::Int)
    print(io, "    "^cols)
    show_type(io, alg)
    print(io, '(')
    for (i, name) in enumerate(fieldnames(typeof(alg)))
        arg = getproperty(alg, name)
        i > 1 && print(io, ',')
        if arg isa Algorithm
            println(io)
            print_tree(io, arg, cols+1)
        else
            i > 1 && print(io, ' ')
            print(io, arg)
        end
    end
    print(io, ')')
end
```
-/
def printAlgorithmTree {IO Alg Name Arg E : Type}
    (ops : AlgorithmDisplayOps IO Alg Name Arg E)
    (io : IO) (algorithm : Alg) (columns : Nat) : Except E IO := do
  let indentation := String.ofList (List.replicate (4 * columns) ' ')
  let io ← ops.print io indentation
  let io ← ops.showType io algorithm
  let io ← ops.print io "("
  let names := ops.fieldNames algorithm
  let mut io := io
  let mut index := 0
  for name in names do
    let argument := ops.getField algorithm name
    if index > 0 then
      io ← ops.print io ","
    if ops.isAlgorithm argument then
      io ← ops.println io ""
      io ← printAlgorithmTree ops io (ops.toAlgorithm argument) (columns + 1)
    else
      if index > 0 then
        io ← ops.print io " "
      io ← ops.printArgument io argument
    index := index + 1
  ops.print io ")"
termination_by ops.algorithmDepth algorithm
decreasing_by
  apply ops.childDepthLess algorithm name
  · assumption
  · assumption

/--
Julia source: base/sort.jl:1597-1599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, alg::Algorithm)
    print_tree(io, alg, 0)
end
```
-/
def showAlgorithm {IO Alg E : Type}
    (printTree : IO → Alg → Nat → Except E IO)
    (io : IO) (algorithm : Alg) : Except E IO :=
  printTree io algorithm 0
structure TupleMergeOps (Tuple O E : Type) where
  length : Tuple → Nat
  split : Tuple → Nat → Tuple × Tuple
  splitSmaller : ∀ tuple, 1 < length tuple →
    length (split tuple (length tuple / 2)).1 < length tuple ∧
    length (split tuple (length tuple / 2)).2 < length tuple
  merge : Tuple → Tuple → O → Except E Tuple

/--
Julia source: base/sort.jl:1809-1809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mergesort(x::Union{NTuple{0}, NTuple{1}}, o::Ordering) = x
```
-/
def mergeSortTupleBase {Tuple O : Type} (tuple : Tuple) (_order : O) : Tuple :=
  tuple

/--
Julia source: base/sort.jl:1810-1813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mergesort(x::NTuple, o::Ordering)
    a, b = Base.IteratorsMD.split(x, Val(length(x)>>1))
    merge(_mergesort(a, o), _mergesort(b, o), o)
end
```
-/
def mergeSortTupleRecursive {Tuple O E : Type}
    (ops : TupleMergeOps Tuple O E) (tuple : Tuple) (order : O) :
    Except E Tuple := do
  if small : ops.length tuple ≤ 1 then
    pure (mergeSortTupleBase tuple order)
  else
    let midpoint := ops.length tuple / 2
    let split := ops.split tuple midpoint
    let sortedLeft ← mergeSortTupleRecursive ops split.1 order
    let sortedRight ← mergeSortTupleRecursive ops split.2 order
    ops.merge sortedLeft sortedRight order
termination_by ops.length tuple
decreasing_by
  · simpa [split, midpoint] using (ops.splitSmaller tuple (by omega)).1
  · simpa [split, midpoint] using (ops.splitSmaller tuple (by omega)).2

/--
Julia source: base/sort.jl:1814-1814 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(x::NTuple, y::NTuple{0}, o::Ordering) = x
```
-/
def mergeTupleRightEmpty {Tuple O : Type} (left _right : Tuple) (_order : O) : Tuple :=
  left

/--
Julia source: base/sort.jl:1815-1815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(x::NTuple{0}, y::NTuple, o::Ordering) = y
```
-/
def mergeTupleLeftEmpty {Tuple O : Type} (_left right : Tuple) (_order : O) : Tuple :=
  right

/--
Julia source: base/sort.jl:1816-1816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(x::NTuple{0}, y::NTuple{0}, o::Ordering) = x # Method ambiguity
```
-/
def mergeTupleBothEmpty {Tuple O : Type} (left _right : Tuple) (_order : O) : Tuple :=
  left

structure TupleMergeStepOps (Tuple α O E : Type) where
  head : Tuple → α
  tail : Tuple → Tuple
  prepend : α → Tuple → Tuple
  less : O → α → α → Except E Bool
  merge : Tuple → Tuple → O → Except E Tuple

/--
Julia source: base/sort.jl:1817-1818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
merge(x::NTuple, y::NTuple, o::Ordering) =
    (lt(o, y[1], x[1]) ? (y[1], merge(x, tail(y), o)...) : (x[1], merge(tail(x), y, o)...))
```
-/
def mergeTupleNonempty {Tuple α O E : Type}
    (ops : TupleMergeStepOps Tuple α O E)
    (left right : Tuple) (order : O) : Except E Tuple := do
  let leftHead := ops.head left
  let rightHead := ops.head right
  if ← ops.less order rightHead leftHead then
    let rest ← ops.merge left (ops.tail right) order
    pure (ops.prepend rightHead rest)
  else
    let rest ← ops.merge (ops.tail left) right order
    pure (ops.prepend leftHead rest)

structure TupleSortCoreOps (Tuple Mutable Alg O Kws E : Type) where
  length : Tuple → Nat
  copyMutable : Tuple → Except E Mutable
  sortMutable : Mutable → Alg → O → Kws → Except E Mutable
  constructLike : Tuple → Mutable → Except E Tuple
  mergeSort : Tuple → O → Except E Tuple

/--
Julia source: base/sort.jl:1798-1808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort(x::NTuple, a::Union{DefaultStable, DefaultUnstable}, o::Ordering, kw)
    # The unrolled tuple sort is prohibitively slow to compile for length > 9.
    # See https://github.com/JuliaLang/julia/pull/46104#issuecomment-1435688502 for benchmarks
    if length(x) > 9
        v = copymutable(x)
        _sort!(v, a, o, kw)
        typeof(x)(v)
    else
        _mergesort(x, o)
    end
end
```
-/
def sortTupleCore {Tuple Mutable Alg O Kws E : Type}
    (ops : TupleSortCoreOps Tuple Mutable Alg O Kws E)
    (tuple : Tuple) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E Tuple := do
  if ops.length tuple > 9 then
    let vector ← ops.copyMutable tuple
    let sorted ← ops.sortMutable vector algorithm order keywords
    ops.constructLike tuple sorted
  else
    ops.mergeSort tuple order

structure TuplePublicSortOps (Tuple Alg L B O Scratch Kws E : Type) where
  scratchMatches : Tuple → Option Scratch → Bool
  argumentError : String → E
  ordering : L → B → Option Bool → O → O
  keywords : Option Scratch → Kws
  sortTuple : Tuple → Alg → O → Kws → Except E Tuple
  assertSameType : Tuple → Tuple → Except E Tuple

/--
Julia source: base/sort.jl:1785-1795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort(x::NTuple;
              alg::Algorithm=defalg(x),
              lt=isless,
              by=identity,
              rev::Union{Bool,Nothing}=nothing,
              order::Ordering=Forward,
              scratch::Union{Vector, Nothing}=nothing)
    # Can't do this check with type parameters because of https://github.com/JuliaLang/julia/issues/56698
    scratch === nothing || eltype(x) == eltype(scratch) || throw(ArgumentError("scratch has the wrong eltype"))
    _sort(x, alg, ord(lt,by,rev,order), (;scratch))::typeof(x)
end
```
-/
def sortTupleTop {Tuple Alg L B O Scratch Kws E : Type}
    (ops : TuplePublicSortOps Tuple Alg L B O Scratch Kws E)
    (tuple : Tuple) (algorithm : Alg) (less : L) (byFn : B)
    (rev : Option Bool) (order : O) (scratch : Option Scratch) :
    Except E Tuple := do
  if !ops.scratchMatches tuple scratch then
    throw (ops.argumentError "scratch has the wrong eltype")
  let sorted ← ops.sortTuple tuple algorithm (ops.ordering less byFn rev order)
    (ops.keywords scratch)
  ops.assertSameType tuple sorted
structure StableCheckSortedOps (V Alg O K Kws Scratch E : Type) where
  rangeAndScratch : Kws → Except E (K × K × Scratch)
  isSorted : V → K → K → O → Except E Bool
  stableReverseOrdering : O → O
  reverse : V → K → K → Except E V
  nextAlgorithm : Alg → Alg
  sort : V → Alg → O → Kws → Except E (V × Scratch)

/--
Julia source: base/sort.jl:1368-1379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::StableCheckSorted, o::Ordering, kw)
    @getkw lo hi scratch
    if _issorted(v, lo, hi, o)
        return scratch
    elseif _issorted(v, lo, hi, Lt((x, y) -> !lt(o, x, y)))
        # Reverse only if necessary. Using issorted(..., Reverse(o)) would violate stability.
        reverse!(v, lo, hi)
        return scratch
    end

    _sort!(v, a.next, o, kw)
end
```
-/
def sortStableCheck {V Alg O K Kws Scratch E : Type}
    (ops : StableCheckSortedOps V Alg O K Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E (V × Scratch) := do
  let (lo, hi, scratch) ← ops.rangeAndScratch keywords
  if ← ops.isSorted vector lo hi order then
    pure (vector, scratch)
  else if ← ops.isSorted vector lo hi (ops.stableReverseOrdering order) then
    let reversed ← ops.reverse vector lo hi
    pure (reversed, scratch)
  else
    ops.sort vector (ops.nextAlgorithm algorithm) order keywords
structure LegacyQuickSortOps (V α K Alg O E : Type) where
  modelExhausted : E
  midpoint : K → K → K
  lessValue : O → α → α → Except E Bool
  read : V → K → Except E α
  write : V → K → α → Except E V
  nextIndex : K → K
  previousIndex : K → K
  lessIndex : K → K → Bool
  distance : K → K → Nat
  checkBounds : V → K → K → Except E Unit
  smallAlgorithm : Alg
  smallThreshold : Nat
  smallSort : V → Alg → O → K → K → Except E V

/--
Julia source: base/sort.jl:2409-2429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function selectpivot!(v::AbstractVector, lo::Integer, hi::Integer, o::Ordering)
    @inbounds begin
        mi = midpoint(lo, hi)

        # sort v[mi] <= v[lo] <= v[hi] such that the pivot is immediately in place
        if lt(o, v[lo], v[mi])
            v[mi], v[lo] = v[lo], v[mi]
        end

        if lt(o, v[hi], v[lo])
            if lt(o, v[hi], v[mi])
                v[hi], v[lo], v[mi] = v[lo], v[mi], v[hi]
            else
                v[hi], v[lo] = v[lo], v[hi]
            end
        end

        # return the pivot
        return v[lo]
    end
end
```
-/
def selectPivot {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (vector : V) (lo hi : K) (order : O) : Except E (V × α) := do
  let middle := ops.midpoint lo hi
  let loValue ← ops.read vector lo
  let middleValue ← ops.read vector middle
  let vector ← if ← ops.lessValue order loValue middleValue then do
    let vector ← ops.write vector lo middleValue
    ops.write vector middle loValue
  else
    pure vector
  let hiValue ← ops.read vector hi
  let loValue ← ops.read vector lo
  let vector ← if ← ops.lessValue order hiValue loValue then do
    let middleValue ← ops.read vector middle
    if ← ops.lessValue order hiValue middleValue then do
      let vector ← ops.write vector hi loValue
      let vector ← ops.write vector lo middleValue
      ops.write vector middle hiValue
    else
      let vector ← ops.write vector hi loValue
      ops.write vector lo hiValue
  else
    pure vector
  let pivot ← ops.read vector lo
  pure (vector, pivot)

/--
Julia source: base/sort.jl:2435-2452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function partition!(v::AbstractVector, lo::Integer, hi::Integer, o::Ordering)
    pivot = selectpivot!(v, lo, hi, o)
    # pivot == v[lo], v[hi] > pivot
    i, j = lo, hi
    @inbounds while true
        i += 1; j -= 1
        while lt(o, v[i], pivot); i += 1; end;
        while lt(o, pivot, v[j]); j -= 1; end;
        i >= j && break
        v[i], v[j] = v[j], v[i]
    end
    v[j], v[lo] = pivot, v[j]

    # v[j] == pivot
    # v[k] >= pivot for k > j
    # v[i] <= pivot for i < j
    return j
end
```
-/
def partitionScanLeft {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (vector : V) (pivot : α) (order : O) : Nat → K → α → Except E (K × α)
  | 0, i, leftValue => do
    if ← ops.lessValue order leftValue pivot then .error ops.modelExhausted
    else pure (i, leftValue)
  | fuel + 1, i, leftValue => do
    if ← ops.lessValue order leftValue pivot then do
      let i := ops.nextIndex i
      let leftValue ← ops.read vector i
      partitionScanLeft ops vector pivot order fuel i leftValue
    else
      pure (i, leftValue)

def partitionScanRight {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (vector : V) (pivot : α) (order : O) : Nat → K → α → Except E (K × α)
  | 0, j, rightValue => do
    if ← ops.lessValue order pivot rightValue then .error ops.modelExhausted
    else pure (j, rightValue)
  | fuel + 1, j, rightValue => do
    if ← ops.lessValue order pivot rightValue then do
      let j := ops.previousIndex j
      let rightValue ← ops.read vector j
      partitionScanRight ops vector pivot order fuel j rightValue
    else
      pure (j, rightValue)

def partitionVectorLoop {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (lo hi : K) (pivot : α) (order : O) : Nat → V → K → K → Except E (V × K)
  | 0, _, _, _ => .error ops.modelExhausted
  | fuel + 1, vector, i, j => do
    let i := ops.nextIndex i
    let j := ops.previousIndex j
    let leftValue0 ← ops.read vector i
    let (i, leftValue) ← partitionScanLeft ops vector pivot order (ops.distance i hi + 2) i leftValue0
    let rightValue0 ← ops.read vector j
    let (j, rightValue) ← partitionScanRight ops vector pivot order (ops.distance lo j + 2) j rightValue0
    if !ops.lessIndex i j then
      pure (vector, j)
    else
      let vector ← ops.write vector i rightValue
      let vector ← ops.write vector j leftValue
      partitionVectorLoop ops lo hi pivot order fuel vector i j

def partitionVector {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (vector : V) (lo hi : K) (order : O) : Except E (V × K) := do
  let (vectorAfterPivot, pivot) ← selectPivot ops vector lo hi order
  let (vector, j) ← partitionVectorLoop ops lo hi pivot order (ops.distance lo hi + 2) vectorAfterPivot lo hi
  let rightValue ← ops.read vector j
  let vector ← ops.write vector j pivot
  let vector ← ops.write vector lo rightValue
  pure (vector, j)

/--
Julia source: base/sort.jl:2459-2478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _quicksort!(v::AbstractVector, lo::Integer, hi::Integer, a::QuickSortAlg, o::Ordering)
    @inbounds while lo < hi
        if hi-lo <= SMALL_THRESHOLD
            _sort!(v, SMALL_ALGORITHM, o, (; lo, hi, scratch=nothing))
            return v
        end
        j = partition!(v, lo, hi, o)
        if j-lo < hi-j
            # recurse on the smaller chunk
            # this is necessary to preserve O(log(n))
            # stack space in the worst case (rather than O(n))
            lo < (j-1) && _quicksort!(v, lo, j-1, a, o)
            lo = j+1
        else
            j+1 < hi && _quicksort!(v, j+1, hi, a, o)
            hi = j-1
        end
    end
    return v
end
```
-/
def quickSortRangeLoop {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E) (order : O) :
    Nat → V → K → K → Except E V
  | 0, vector, lo, hi =>
    if ops.lessIndex lo hi then .error ops.modelExhausted else pure vector
  | fuel + 1, vector, lo, hi => do
    if ops.lessIndex lo hi then
      if ops.distance lo hi ≤ ops.smallThreshold then
        ops.smallSort vector ops.smallAlgorithm order lo hi
      else
        let (vector, pivotIndex) ← partitionVector ops vector lo hi order
        if ops.distance lo pivotIndex < ops.distance pivotIndex hi then
          let leftHi := ops.previousIndex pivotIndex
          let vector ← if ops.lessIndex lo leftHi then
            quickSortRangeLoop ops order fuel vector lo leftHi
          else pure vector
          quickSortRangeLoop ops order fuel vector (ops.nextIndex pivotIndex) hi
        else
          let rightLo := ops.nextIndex pivotIndex
          let vector ← if ops.lessIndex rightLo hi then
            quickSortRangeLoop ops order fuel vector rightLo hi
          else pure vector
          quickSortRangeLoop ops order fuel vector lo (ops.previousIndex pivotIndex)
    else
      pure vector

def quickSortRange {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (vector : V) (lo hi : K) (order : O) : Except E V :=
  quickSortRangeLoop ops order (ops.distance lo hi + 2) vector lo hi

/--
Julia source: base/sort.jl:2454-2457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort!(v::AbstractVector, lo::Integer, hi::Integer, a::QuickSortAlg, o::Ordering)
    checkbounds(v, lo:hi)
    _quicksort!(v, lo, hi, a, o)
end
```
-/
def legacyQuickSortBang {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (vector : V) (lo hi : K) (order : O) : Except E V := do
  ops.checkBounds vector lo hi
  quickSortRange ops vector lo hi order

structure BracketKernelOps (V α K O E : Type) where
  checkBounds : V → K → K → Except E Unit
  range : K → K → List K
  read : V → K → Except E α
  less : O → α → α → Except E Bool
  swap : V → K → K → Except E V
  scaleByBool : Int → Bool → Int
  addIndexOffset : K → Int → K
  addInt : Int → Int → Int
  boolMinusOne : Bool → Int

/--
Julia source: base/sort.jl:1226-1246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bracket_kernel!(v::AbstractVector, lo, hi, lo_signpost, hi_signpost, o)
    i = 0
    count_below = 0
    checkbounds(v, lo:hi)
    for j in lo:hi
        x = @inbounds v[j]
        a = lo_signpost !== nothing && lt(o, x, lo_signpost)
        b = hi_signpost === nothing || !lt(o, hi_signpost, x)
        count_below += a
        # if a != b # This branch is almost never taken, so making it branchless is bad.
        #     @inbounds v[i], v[j] = v[j], v[i]
        #     i += 1
        # end
        c = a != b # JK, this is faster.
        k = i * c + j
        # Invariant: @assert firstindex(v) ≤ lo ≤ i + j ≤ k ≤ j ≤ hi ≤ lastindex(v)
        @inbounds v[j], v[k] = v[k], v[j]
        i += c - 1
    end
    count_below, i+hi
end
```
-/
def bracketKernel {V α K O E : Type}
    (ops : BracketKernelOps V α K O E)
    (vector : V) (lo hi : K) (loSignpost hiSignpost : Option α) (order : O) :
    Except E (V × Nat × K) := do
  ops.checkBounds vector lo hi
  let mut vector := vector
  let mut offset := 0
  let mut countBelow := 0
  for index in ops.range lo hi do
    let value ← ops.read vector index
    let below ← match loSignpost with
      | none => pure false
      | some signpost => ops.less order value signpost
    let notAbove ← match hiSignpost with
      | none => pure true
      | some signpost => do pure (!(← ops.less order signpost value))
    countBelow := countBelow + if below then 1 else 0
    let swapNeeded := below != notAbove
    let target := ops.addIndexOffset index (ops.scaleByBool offset swapNeeded)
    vector ← ops.swap vector index target
    offset := ops.addInt offset (ops.boolMinusOne swapNeeded)
  pure (vector, countBelow, ops.addIndexOffset hi offset)

structure MoveVectorOps (V Range K E : Type) where
  length : Range → Nat
  disjoint : Range → Range → Bool
  indices : Range → List K
  minimum : Range → Except E K
  maximum : Range → Except E K
  lessEq : K → K → Bool
  lengthMismatch : E
  rangeMismatch : E
  swap : V → K → K → Except E V
  reverse : V → K → K → Except E V

/--
Julia source: base/sort.jl:1248-1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function move!(v, target, source)
    # This function never dominates runtime—only add `@inbounds` if you can demonstrate a
    # performance improvement. And if you do, also double check behavior when `target`
    # is out of bounds.
    @assert length(target) == length(source) "length mismatch"
    if length(target) == 1 || isdisjoint(target, source)
        for (i, j) in zip(target, source)
            v[i], v[j] = v[j], v[i]
        end
    else
        @assert minimum(source) <= minimum(target) "range mismatch"
        reverse!(v, minimum(source), maximum(target))
        reverse!(v, minimum(target), maximum(target))
    end
end
```
-/
def moveVector {V Range K E : Type} (ops : MoveVectorOps V Range K E)
    (vector : V) (target source : Range) : Except E V := do
  if ops.length target != ops.length source then
    throw ops.lengthMismatch
  if ops.length target == 1 || ops.disjoint target source then
    let mut vector := vector
    for (targetIndex, sourceIndex) in (ops.indices target).zip (ops.indices source) do
      vector ← ops.swap vector targetIndex sourceIndex
    pure vector
  else
    if !ops.lessEq (← ops.minimum source) (← ops.minimum target) then
      throw ops.rangeMismatch
    let vector ← ops.reverse vector (← ops.minimum source) (← ops.maximum target)
    ops.reverse vector (← ops.minimum target) (← ops.maximum target)
inductive BracketSortTarget (K : Type) where
  | index (value : K)
  | range (first last : K)
  | ordinal (first step last : K) (length : Nat)
  deriving Repr

structure BracketedSortOps
    (V α K Alg Next O Kws Scratch E Result : Type) where
  rangeAndScratch : Kws → Except E (K × K × Scratch)
  rangeLength : K → K → Nat
  lessIndex : K → K → Bool
  lessEqIndex : K → K → Bool
  advance : K → Nat → K
  range : K → K → List K
  target : Alg → BracketSortTarget K
  targetMinimum : BracketSortTarget K → Except E K
  targetMaximum : BracketSortTarget K → Except E K
  shiftTarget : BracketSortTarget K → Nat → BracketSortTarget K
  nextAlgorithm : Alg → BracketSortTarget K → Next
  cbrt : Nat → Float
  square : Float → Float
  roundInt : Float → Except E Int
  floatOfNat : Nat → Float
  floatOfIndex : K → Float
  differenceToFloat : K → K → Float
  topSetBitFloat : Nat → Float
  multiplyFloat : Float → Float → Float
  divideFloat : Float → Float → Float
  addFloat : Float → Float → Float
  subtractFloat : Float → Float → Float
  negateFloat : Float → Float
  lessEqFloat : Float → Float → Bool
  floorIndex : Float → Except E K
  minimumIndex : K → K → K
  maximumIndex : K → K → K
  inclusiveSpan : K → K → Float
  seedForLength : Nat → Nat
  hashAttempt : Nat → Nat → Nat
  hashIndex : Nat → K → K → Except E K
  swap : V → K → K → Except E V
  read : V → K → Except E α
  checkFailure : E
  kernelOps : BracketKernelOps V α K O E
  moveOps : MoveVectorOps V (BracketSortTarget K) K E
  sortSegment : V → Next → O → Kws → Except E (V × Scratch)
  keywordsWithHi : Kws → K → Kws
  finish : V → Scratch → Result

/--
Julia source: base/sort.jl:1264-1353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::BracketedSort, o::Ordering, kw)
    @getkw lo hi scratch
    # TODO for further optimization: reuse scratch between trials better, from signpost
    # selection to recursive calls, and from the fallback (but be aware of type stability,
    # especially when sorting IEEE floats.

    # We don't need to bounds check target because that is done higher up in the stack
    # However, we cannot assume the target is inbounds.
    lo < hi || return scratch
    ln = hi - lo + 1

    # This is simply a precomputed short-circuit to avoid doing scalar math for small inputs.
    # It does not change dispatch at all.
    ln < 260 && return _sort!(v, a.get_next(a.target), o, kw)

    target = a.target
    k = cbrt(ln)
    k2 = round(Int, k^2)
    k2ln = k2/ln
    offset = .15k*top_set_bit(k2) # TODO for further optimization: tune this
    lo_signpost_i, hi_signpost_i =
        (floor(Int, (tar - lo) * k2ln + lo + off) for (tar, off) in
            ((minimum(target), -offset), (maximum(target), offset)))
    lastindex_sample = lo+k2-1
    expected_middle_ln = (min(lastindex_sample, hi_signpost_i) - max(lo, lo_signpost_i) + 1) / k2ln
    # This heuristic is complicated because it fairly accurately reflects the runtime of
    # this algorithm which is necessary to get good dispatch when both the target is large
    # and the input are large.
    # expected_middle_ln is a float and k2 is significantly below typemax(Int), so this will
    # not overflow:
    # TODO move target from alg to kw to avoid this ickyness:
    ln <= 130 + 2k2 + 2expected_middle_ln && return _sort!(v, a.get_next(a.target), o, kw)

    # We store the random sample in
    #     sample = view(v, lo:lo+k2)
    # but views are not quite as fast as using the input array directly,
    # so we don't actually construct this view at runtime.

    # TODO for further optimization: handle lots of duplicates better.
    # Right now lots of duplicates rounds up when it could use some super fast optimizations
    # in some cases.
    # e.g.
    #
    # Target:                      |----|
    # Sorted input: 000000000000000000011111112222223333333333
    #
    # Will filter all zeros and ones to the front when it could just take the first few
    # it encounters. This optimization would be especially potent when `allequal(ans)` and
    # equal elements are egal.

    # 3 random trials should typically give us 0.99999 reliability; we can assume
    # the input is pathological and abort to fallback if we fail three trials.
    seed = hash(ln, Int === Int64 ? 0x85eb830e0216012d : 0xae6c4e15)
    for attempt in 1:3
        seed = hash(attempt, seed)
        for i in lo:lo+k2-1
            j = mod(hash(i, seed), i:hi) # TODO for further optimization: be sneaky and remove this division
            v[i], v[j] = v[j], v[i]
        end
        count_below, lastindex_middle = if lo_signpost_i <= lo && lastindex_sample <= hi_signpost_i
            # The heuristics higher up in this function that dispatch to the `next`
            # algorithm should prevent this from happening.
            # Specifically, this means that expected_middle_ln == ln, so
            # ln <= ... + 2.0expected_middle_ln && return ...
            # will trigger.
            @assert false "this should never happen"
            # But if it does happen, the kernel reduces to
            0, hi
        elseif lo_signpost_i <= lo
            _sort!(v, a.get_next(hi_signpost_i), o, (;kw..., hi=lastindex_sample))
            bracket_kernel!(v, lo, hi, nothing, v[hi_signpost_i], o)
        elseif lastindex_sample <= hi_signpost_i
            _sort!(v, a.get_next(lo_signpost_i), o, (;kw..., hi=lastindex_sample))
            bracket_kernel!(v, lo, hi, v[lo_signpost_i], nothing, o)
        else
            # TODO for further optimization: don't sort the middle elements
            _sort!(v, a.get_next(lo_signpost_i:hi_signpost_i), o, (;kw..., hi=lastindex_sample))
            bracket_kernel!(v, lo, hi, v[lo_signpost_i], v[hi_signpost_i], o)
        end
        target_in_middle = target .- count_below
        if lo <= minimum(target_in_middle) && maximum(target_in_middle) <= lastindex_middle
            scratch = _sort!(v, a.get_next(target_in_middle), o, (;kw..., hi=lastindex_middle))
            move!(v, target, target_in_middle)
            return scratch
        end
        # This line almost never runs.
    end
    # This line only runs on pathological inputs. Make sure it's covered by tests :)
    _sort!(v, a.get_next(target), o, kw)
end
```
-/
def sortBracketed {V α K Alg Next O Kws Scratch E Result : Type}
    (ops : BracketedSortOps V α K Alg Next O Kws Scratch E Result)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E Result := do
  let (lo, hi, scratch) ← ops.rangeAndScratch keywords
  if !ops.lessIndex lo hi then
    return ops.finish vector scratch
  let inputLength := ops.rangeLength lo hi
  let target := ops.target algorithm
  let sortNext := ops.nextAlgorithm algorithm target
  if inputLength < 260 then
    let (sorted, sortedScratch) ← ops.sortSegment vector sortNext order keywords
    return ops.finish sorted sortedScratch
  let k := ops.cbrt inputLength
  let sampleCount ← ops.roundInt (ops.square k)
  let k2 := sampleCount.toNat
  let k2ln := ops.divideFloat (ops.floatOfNat k2) (ops.floatOfNat inputLength)
  let offset := ops.multiplyFloat
    (ops.multiplyFloat (ops.divideFloat (ops.floatOfNat 15) (ops.floatOfNat 100)) k)
    (ops.topSetBitFloat k2)
  let lowerTarget ← ops.targetMinimum target
  let upperTarget ← ops.targetMaximum target
  let lowerSignpost ← ops.floorIndex
    (ops.addFloat
      (ops.addFloat (ops.multiplyFloat (ops.differenceToFloat lowerTarget lo) k2ln)
        (ops.floatOfIndex lo))
      (ops.negateFloat offset))
  let upperSignpost ← ops.floorIndex
    (ops.addFloat
      (ops.addFloat (ops.multiplyFloat (ops.differenceToFloat upperTarget lo) k2ln)
        (ops.floatOfIndex lo))
      offset)
  let lastSample := ops.advance lo (k2 - 1)
  let middleLo := ops.maximumIndex lo lowerSignpost
  let middleHi := ops.minimumIndex lastSample upperSignpost
  let expectedMiddle := ops.divideFloat (ops.inclusiveSpan middleLo middleHi) k2ln
  let dispatchLimit := ops.addFloat
    (ops.addFloat (ops.floatOfNat 130) (ops.multiplyFloat (ops.floatOfNat 2) (ops.floatOfNat k2)))
    (ops.multiplyFloat (ops.floatOfNat 2) expectedMiddle)
  if ops.lessEqFloat (ops.floatOfNat inputLength) dispatchLimit then
    let (sorted, sortedScratch) ← ops.sortSegment vector sortNext order keywords
    return ops.finish sorted sortedScratch
  let mut seed := ops.seedForLength inputLength
  let mut vector := vector
  let mut finalResult : Option Result := none
  for attempt in [1, 2, 3] do
    seed := ops.hashAttempt attempt seed
    for index in ops.range lo lastSample do
      let pivot ← ops.hashIndex seed index hi
      vector ← ops.swap vector index pivot
    let (countBelow, lastMiddle) ←
      if ops.lessEqIndex lowerSignpost lo && ops.lessEqIndex lastSample upperSignpost then
        throw ops.checkFailure
      else if ops.lessEqIndex lowerSignpost lo then do
        let segmentAlgorithm := ops.nextAlgorithm algorithm (.index upperSignpost)
        let (sorted, _) ← ops.sortSegment vector segmentAlgorithm order
          (ops.keywordsWithHi keywords lastSample)
        vector := sorted
        let highValue ← ops.read vector upperSignpost
        let (partitioned, count, middle) ← bracketKernel ops.kernelOps vector lo hi none
          (some highValue) order
        vector := partitioned
        pure (count, middle)
      else if ops.lessEqIndex lastSample upperSignpost then do
        let segmentAlgorithm := ops.nextAlgorithm algorithm (.index lowerSignpost)
        let (sorted, _) ← ops.sortSegment vector segmentAlgorithm order
          (ops.keywordsWithHi keywords lastSample)
        vector := sorted
        let lowValue ← ops.read vector lowerSignpost
        let (partitioned, count, middle) ← bracketKernel ops.kernelOps vector lo hi
          (some lowValue) none order
        vector := partitioned
        pure (count, middle)
      else do
        let segmentAlgorithm := ops.nextAlgorithm algorithm
          (.range lowerSignpost upperSignpost)
        let (sorted, _) ← ops.sortSegment vector segmentAlgorithm order
          (ops.keywordsWithHi keywords lastSample)
        vector := sorted
        let lowValue ← ops.read vector lowerSignpost
        let highValue ← ops.read vector upperSignpost
        let (partitioned, count, middle) ← bracketKernel ops.kernelOps vector lo hi
          (some lowValue) (some highValue) order
        vector := partitioned
        pure (count, middle)
    let targetInMiddle := ops.shiftTarget target countBelow
    let shiftedMinimum ← ops.targetMinimum targetInMiddle
    let shiftedMaximum ← ops.targetMaximum targetInMiddle
    if ops.lessEqIndex lo shiftedMinimum && ops.lessEqIndex shiftedMaximum lastMiddle then
      let segmentAlgorithm := ops.nextAlgorithm algorithm targetInMiddle
      let (sorted, sortedScratch) ← ops.sortSegment vector segmentAlgorithm order
        (ops.keywordsWithHi keywords lastMiddle)
      let moved ← moveVector ops.moveOps sorted target targetInMiddle
      finalResult := some (ops.finish moved sortedScratch)
      break
  match finalResult with
  | some result => pure result
  | none =>
    let (sorted, sortedScratch) ← ops.sortSegment vector
      (ops.nextAlgorithm algorithm target) order keywords
    pure (ops.finish sorted sortedScratch)
structure ScratchPartitionOps (Target Source PivotDest K α O E : Type) where
  modelExhausted : E
  pivotIndex : K → K → Except E K
  readSource : Source → K → Except E α
  writeTarget : Target → K → α → Except E Target
  writePivot : Target → PivotDest → K → α → Except E (Target × PivotDest)
  lessValue : O → α → α → Except E Bool
  lessIndex : K → K → Bool
  nextIndex : K → K
  subtractIndex : K → K → K
  addBoolToIndex : K → Bool → K
  addPivotOffset : K → K → K
  distance : K → K → Nat

/--
Julia source: base/sort.jl:1088-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function partition!(t::AbstractVector, lo::Integer, hi::Integer, offset::Integer, o::Ordering,
        v::AbstractVector, rev::Bool, pivot_dest::AbstractVector, pivot_index_offset::Integer)
    # Ideally we would use `pivot_index = rand(lo:hi)`, but that requires Random.jl
    # and would mutate the global RNG in sorting.
    pivot_index = mod(hash(lo), lo:hi)
    @inbounds begin
        pivot = v[pivot_index]
        while lo < pivot_index
            x = v[lo]
            fx = rev ? !lt(o, x, pivot) : lt(o, pivot, x)
            t[(fx ? hi : lo) - offset] = x
            offset += fx
            lo += 1
        end
        while lo < hi
            x = v[lo+1]
            fx = rev ? lt(o, pivot, x) : !lt(o, x, pivot)
            t[(fx ? hi : lo) - offset] = x
            offset += fx
            lo += 1
        end
        pivot_index = lo-offset + pivot_index_offset
        pivot_dest[pivot_index] = pivot
    end

    # t_pivot_index = lo-offset (i.e. without pivot_index_offset)
    # t[t_pivot_index] is whatever it was before unless t is the pivot_dest
    # t[<t_pivot_index] <* pivot, stable
    # t[>t_pivot_index] >* pivot, reverse stable

    pivot_index
end
```
-/
def partitionScratchBeforeLoop {Target Source PivotDest K α O E : Type}
    (ops : ScratchPartitionOps Target Source PivotDest K α O E)
    (pivotIndex hi : K) (order : O) (source : Source) (reverse : Bool) (pivot : α) :
    Nat → Target → K → K → Except E (Target × K × K)
  | 0, target, lo, offset =>
    if ops.lessIndex lo pivotIndex then .error ops.modelExhausted
    else pure (target, lo, offset)
  | fuel + 1, target, lo, offset =>
    if ops.lessIndex lo pivotIndex then do
      let value ← ops.readSource source lo
      let sendRight ← if reverse then do pure (!(← ops.lessValue order value pivot))
        else ops.lessValue order pivot value
      let destination := ops.subtractIndex (if sendRight then hi else lo) offset
      let target ← ops.writeTarget target destination value
      let offset := ops.addBoolToIndex offset sendRight
      let lo := ops.nextIndex lo
      partitionScratchBeforeLoop ops pivotIndex hi order source reverse pivot fuel target lo offset
    else
      pure (target, lo, offset)

def partitionScratchAfterLoop {Target Source PivotDest K α O E : Type}
    (ops : ScratchPartitionOps Target Source PivotDest K α O E)
    (hi : K) (order : O) (source : Source) (reverse : Bool) (pivot : α) :
    Nat → Target → K → K → Except E (Target × K × K)
  | 0, target, lo, offset =>
    if ops.lessIndex lo hi then .error ops.modelExhausted
    else pure (target, lo, offset)
  | fuel + 1, target, lo, offset =>
    if ops.lessIndex lo hi then do
      let value ← ops.readSource source (ops.nextIndex lo)
      let sendRight ← if reverse then ops.lessValue order pivot value
        else do pure (!(← ops.lessValue order value pivot))
      let destination := ops.subtractIndex (if sendRight then hi else lo) offset
      let target ← ops.writeTarget target destination value
      let offset := ops.addBoolToIndex offset sendRight
      let lo := ops.nextIndex lo
      partitionScratchAfterLoop ops hi order source reverse pivot fuel target lo offset
    else
      pure (target, lo, offset)

def partitionScratch {Target Source PivotDest K α O E : Type}
    (ops : ScratchPartitionOps Target Source PivotDest K α O E)
    (target : Target) (lo hi offset : K) (order : O) (source : Source)
    (reverse : Bool) (pivotDestination : PivotDest) (pivotIndexOffset : K) :
    Except E (Target × PivotDest × K) := do
  let pivotIndex ← ops.pivotIndex lo hi
  let pivot ← ops.readSource source pivotIndex
  let (target, lo, offset) ← partitionScratchBeforeLoop ops pivotIndex hi order source
    reverse pivot (ops.distance lo pivotIndex + 1) target lo offset
  let (target, lo, offset) ← partitionScratchAfterLoop ops hi order source
    reverse pivot (ops.distance lo hi + 1) target lo offset
  let pivotIndex := ops.addPivotOffset (ops.subtractIndex lo offset) pivotIndexOffset
  let (finalTarget, finalPivotDestination) ←
    ops.writePivot target pivotDestination pivotIndex pivot
  pure (finalTarget, finalPivotDestination, pivotIndex)
structure ScratchQuickSortOps
    (V T α K Alg O Kws Scratch E : Type) where
  rangeAndScratch : Kws → Except E (K × K × Option Scratch)
  makeScratch : Option Scratch → V → Nat → Except E (Scratch × T)
  requireOffset : Option K → Except E K
  oneMinus : K → K
  zeroIndex : K
  negateIndex : K → K
  windowLength : K → K → Nat
  lessIndex : K → K → Bool
  lessEq : K → K → Bool
  distance : K → K → Nat
  addIndex : K → K → K
  nextIndex : K → K
  previousIndex : K → K
  lowBound : Alg → Option K
  highBound : Alg → Option K
  smallThreshold : Nat
  partitionInVector : ScratchPartitionOps V T V K α O E
  partitionInScratch : ScratchPartitionOps T V V K α O E
  copyTo : V → K → T → K → Nat → Except E V
  reverse : V → K → K → Except E V
  withScratch : Kws → Scratch → Kws
  withBounds : Kws → K → K → Kws
  nextAlgorithm : Alg → Alg
  sortNext : V → Alg → O → Kws → Except E (V × Option Scratch)

/--
Julia source: base/sort.jl:1121-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::ScratchQuickSort, o::Ordering, kw;
                t=nothing, offset=nothing, swap=false, rev=false)
    @getkw lo hi scratch

    if t === nothing
        scratch, t = make_scratch(scratch, eltype(v), hi-lo+1)
        offset = 1-lo
        kw = (;kw..., scratch)
    end

    while lo < hi && hi - lo > SMALL_THRESHOLD
        j = if swap
            partition!(v, lo+offset, hi+offset, offset, o, t, rev, v, 0)
        else
            partition!(t, lo, hi, -offset, o, v, rev, v, -offset)
        end
        swap = !swap

        # For ScratchQuickSort(), a.lo === a.hi === missing, so the first two branches get skipped
        if !ismissing(a.lo) && j <= a.lo # Skip sorting the lower part
            swap && copyto!(v, lo, t, lo+offset, j-lo)
            rev && reverse!(v, lo, j-1)
            lo = j+1
            rev = !rev
        elseif !ismissing(a.hi) && a.hi <= j # Skip sorting the upper part
            swap && copyto!(v, j+1, t, j+1+offset, hi-j)
            rev || reverse!(v, j+1, hi)
            hi = j-1
        elseif j-lo < hi-j
            # Sort the lower part recursively because it is smaller. Recursing on the
            # smaller part guarantees O(log(n)) stack space even on pathological inputs.
            _sort!(v, a, o, (;kw..., lo, hi=j-1); t, offset, swap, rev)
            lo = j+1
            rev = !rev
        else # Sort the higher part recursively
            _sort!(v, a, o, (;kw..., lo=j+1, hi); t, offset, swap, rev=!rev)
            hi = j-1
        end
    end
    hi < lo && return scratch
    swap && copyto!(v, lo, t, lo+offset, hi-lo+1)
    rev && reverse!(v, lo, hi)
    _sort!(v, a.next, o, (;kw..., lo, hi))
end
```
-/
def sortScratchQuickLoop {V T α K Alg O Kws Scratch E : Type}
    (ops : ScratchQuickSortOps V T α K Alg O Kws Scratch E)
    (algorithm : Alg) (order : O) :
    Nat → V → T → K → K → K → Kws → Option Scratch → Bool → Bool →
      Except E (V × T × Option Scratch)
  | 0, _, _, _, _, _, _, _, _, _ => .error ops.partitionInVector.modelExhausted
  | fuel + 1, vector, temporary, lo, hi, offset, keywords, scratch, swap, reverse => do
    if ops.lessIndex lo hi && ops.distance lo hi > ops.smallThreshold then
      let (pivotVector, pivotTemporary, pivotIndex) ← if swap then do
        let (_, pivotDestination, pivotIndex) ← partitionScratch ops.partitionInVector
          vector (ops.addIndex lo offset) (ops.addIndex hi offset) offset order temporary
          reverse vector ops.zeroIndex
        pure (pivotDestination, temporary, pivotIndex)
      else do
        let (nextTemporary, pivotDestination, pivotIndex) ←
          partitionScratch ops.partitionInScratch temporary lo hi
            (ops.negateIndex offset) order vector reverse vector (ops.negateIndex offset)
        pure (pivotDestination, nextTemporary, pivotIndex)
      let vector := pivotVector
      let temporary := pivotTemporary
      let swap := !swap
      let skipLower := match ops.lowBound algorithm with
        | none => false
        | some bound => ops.lessEq pivotIndex bound
      let skipUpper := match ops.highBound algorithm with
        | none => false
        | some bound => ops.lessEq bound pivotIndex
      if skipLower then
        let vector ← if swap then
          ops.copyTo vector lo temporary (ops.addIndex lo offset)
            (ops.distance lo pivotIndex)
        else pure vector
        let vector ← if reverse then
          ops.reverse vector lo (ops.previousIndex pivotIndex)
        else pure vector
        sortScratchQuickLoop ops algorithm order fuel vector temporary
          (ops.nextIndex pivotIndex) hi offset keywords scratch swap (!reverse)
      else if skipUpper then
        let vector ← if swap then
          let start := ops.nextIndex pivotIndex
          ops.copyTo vector start temporary (ops.addIndex start offset)
            (ops.distance pivotIndex hi)
        else pure vector
        let vector ← if !reverse then
          ops.reverse vector (ops.nextIndex pivotIndex) hi
        else pure vector
        sortScratchQuickLoop ops algorithm order fuel vector temporary
          lo (ops.previousIndex pivotIndex) offset keywords scratch swap reverse
      else if ops.distance lo pivotIndex < ops.distance pivotIndex hi then
        let (sorted, temporary, _) ← sortScratchQuickLoop ops algorithm order fuel
          vector temporary lo (ops.previousIndex pivotIndex) offset
          (ops.withBounds keywords lo (ops.previousIndex pivotIndex)) scratch swap reverse
        sortScratchQuickLoop ops algorithm order fuel sorted temporary
          (ops.nextIndex pivotIndex) hi offset keywords scratch swap (!reverse)
      else
        let (sorted, temporary, _) ← sortScratchQuickLoop ops algorithm order fuel
          vector temporary (ops.nextIndex pivotIndex) hi offset
          (ops.withBounds keywords (ops.nextIndex pivotIndex) hi) scratch swap (!reverse)
        sortScratchQuickLoop ops algorithm order fuel sorted temporary
          lo (ops.previousIndex pivotIndex) offset keywords scratch swap reverse
    else
      if ops.lessIndex hi lo then
        pure (vector, temporary, scratch)
      else
        let vector ← if swap then
          ops.copyTo vector lo temporary (ops.addIndex lo offset)
            (ops.windowLength lo hi)
        else pure vector
        let vector ← if reverse then
          ops.reverse vector lo hi
        else pure vector
        let (sorted, nextScratch) ← ops.sortNext vector (ops.nextAlgorithm algorithm) order
          (ops.withBounds keywords lo hi)
        pure (sorted, temporary, nextScratch)

def sortScratchQuick {V T α K Alg O Kws Scratch E : Type}
    (ops : ScratchQuickSortOps V T α K Alg O Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws)
    (temporary? : Option T := none) (offset? : Option K := none)
    (swapInitially : Bool := false) (reverseInitially : Bool := false) :
    Except E (V × Option Scratch) := do
  let (lo0, hi0, scratch0) ← ops.rangeAndScratch keywords
  let (scratch, temporary, offset, keywords) ← match temporary? with
    | none => do
      let (newScratch, newTemporary) ←
        ops.makeScratch scratch0 vector (ops.windowLength lo0 hi0)
      pure (some newScratch, newTemporary, ops.oneMinus lo0,
        ops.withScratch keywords newScratch)
    | some temporary =>
      let offset ← ops.requireOffset offset?
      pure (scratch0, temporary, offset, keywords)
  let (sorted, _, finalScratch) ← sortScratchQuickLoop ops algorithm order
    (ops.windowLength lo0 hi0 + 2) vector temporary lo0 hi0 offset keywords
    scratch swapInitially reverseInitially
  pure (sorted, finalScratch)
structure LegacyMergeSortOps (V Temp α K Alg O E : Type) where
  quick : LegacyQuickSortOps V α K Alg O E
  oneIndex : K
  lessEqIndex : K → K → Bool
  similar : V → Nat → Except E Temp
  temporaryLength : Temp → Nat
  resizeTemporary : Temp → Nat → Except E Temp
  requireOneBased : Temp → Except E Unit
  readTemporary : Temp → K → Except E α
  writeTemporary : Temp → K → α → Except E Temp

/--
Julia source: base/sort.jl:2488-2531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mergesort!(v::AbstractVector{T}, lo::Integer, hi::Integer, a::MergeSortAlg, o::Ordering,
        t0::Union{AbstractVector{T}, Nothing}) where T
    @inbounds if lo < hi
        if hi-lo <= SMALL_THRESHOLD
            _sort!(v, SMALL_ALGORITHM, o, (; lo, hi, scratch=nothing))
            return v
        end

        m = midpoint(lo, hi)

        t = t0 === nothing ? similar(v, m-lo+1) : t0
        length(t) < m-lo+1 && resize!(t, m-lo+1)
        Base.require_one_based_indexing(t)

        _mergesort!(v, lo,  m,  a, o, t)
        _mergesort!(v, m+1, hi, a, o, t)

        i, j = 1, lo
        while j <= m
            t[i] = v[j]
            i += 1
            j += 1
        end

        i, k = 1, lo
        while k < j <= hi
            if lt(o, v[j], t[i])
                v[k] = v[j]
                j += 1
            else
                v[k] = t[i]
                i += 1
            end
            k += 1
        end
        while k < j
            v[k] = t[i]
            k += 1
            i += 1
        end
    end

    return v
end
```
-/
def mergeCopyTempLoop {V Temp α K Alg O E : Type}
    (ops : LegacyMergeSortOps V Temp α K Alg O E)
    (vector : V) (middle : K) : Nat → Temp → K → K → Except E (Temp × K)
  | 0, temporary, _, j =>
    if ops.lessEqIndex j middle then .error ops.quick.modelExhausted
    else pure (temporary, j)
  | fuel + 1, temporary, i, j =>
    if ops.lessEqIndex j middle then do
      let value ← ops.quick.read vector j
      let temporary ← ops.writeTemporary temporary i value
      mergeCopyTempLoop ops vector middle fuel temporary
        (ops.quick.nextIndex i) (ops.quick.nextIndex j)
    else
      pure (temporary, j)

def mergeBothLoop {V Temp α K Alg O E : Type}
    (ops : LegacyMergeSortOps V Temp α K Alg O E)
    (temporary : Temp) (hi : K) (order : O) :
    Nat → V → K → K → K → Except E (V × K × K × K)
  | 0, vector, i, j, k =>
    if ops.quick.lessIndex k j && ops.lessEqIndex j hi then .error ops.quick.modelExhausted
    else pure (vector, i, j, k)
  | fuel + 1, vector, i, j, k =>
    if ops.quick.lessIndex k j && ops.lessEqIndex j hi then do
      let right ← ops.quick.read vector j
      let left ← ops.readTemporary temporary i
      if ← ops.quick.lessValue order right left then
        let vector ← ops.quick.write vector k right
        mergeBothLoop ops temporary hi order fuel vector
          i (ops.quick.nextIndex j) (ops.quick.nextIndex k)
      else
        let vector ← ops.quick.write vector k left
        mergeBothLoop ops temporary hi order fuel vector
          (ops.quick.nextIndex i) j (ops.quick.nextIndex k)
    else
      pure (vector, i, j, k)

def mergeLeftLoop {V Temp α K Alg O E : Type}
    (ops : LegacyMergeSortOps V Temp α K Alg O E)
    (temporary : Temp) (j : K) : Nat → V → K → K → Except E V
  | 0, vector, _, k =>
    if ops.quick.lessIndex k j then .error ops.quick.modelExhausted else pure vector
  | fuel + 1, vector, i, k =>
    if ops.quick.lessIndex k j then do
      let value ← ops.readTemporary temporary i
      let vector ← ops.quick.write vector k value
      mergeLeftLoop ops temporary j fuel vector
        (ops.quick.nextIndex i) (ops.quick.nextIndex k)
    else
      pure vector

def legacyMergeSortKernelLoop {V Temp α K Alg O E : Type}
    (ops : LegacyMergeSortOps V Temp α K Alg O E)
    (algorithm : Alg) (order : O) :
    Nat → V → K → K → Option Temp → Except E V
  | 0, vector, lo, hi, _ =>
    if ops.quick.lessIndex lo hi then .error ops.quick.modelExhausted else pure vector
  | fuel + 1, vector, lo, hi, temporary => do
    if ops.quick.lessIndex lo hi then
      if ops.quick.distance lo hi ≤ ops.quick.smallThreshold then
        ops.quick.smallSort vector ops.quick.smallAlgorithm order lo hi
      else
        let middle := ops.quick.midpoint lo hi
        let temporaryLength := ops.quick.distance lo middle + 1
        let temporary0 ← match temporary with
          | none => ops.similar vector temporaryLength
          | some existing => pure existing
        let temporary ← if ops.temporaryLength temporary0 < temporaryLength then
          ops.resizeTemporary temporary0 temporaryLength
        else pure temporary0
        ops.requireOneBased temporary
        let vector ← legacyMergeSortKernelLoop ops algorithm order fuel
          vector lo middle (some temporary)
        let vector ← legacyMergeSortKernelLoop ops algorithm order fuel
          vector (ops.quick.nextIndex middle) hi (some temporary)
        let (temporary, j) ← mergeCopyTempLoop ops vector middle
          (ops.quick.distance lo middle + 2) temporary ops.oneIndex lo
        let (vector, i, j, k) ← mergeBothLoop ops temporary hi order
          (ops.quick.distance lo hi + 2) vector ops.oneIndex j lo
        mergeLeftLoop ops temporary j (ops.quick.distance lo hi + 2) vector i k
    else
      pure vector

def legacyMergeSortKernel {V Temp α K Alg O E : Type}
    (ops : LegacyMergeSortOps V Temp α K Alg O E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O)
    (temporary : Option Temp) : Except E V :=
  legacyMergeSortKernelLoop ops algorithm order (ops.quick.distance lo hi + 2)
    vector lo hi temporary

/--
Julia source: base/sort.jl:2482-2486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort!(v::AbstractVector{T}, lo::Integer, hi::Integer, a::MergeSortAlg, o::Ordering,
        t0::Union{AbstractVector{T}, Nothing}=nothing) where T
    checkbounds(v, lo:hi)
    _mergesort!(v, lo, hi, a, o, t0)
end
```
-/
def legacyMergeSortBang {V Temp α K Alg O E : Type}
    (ops : LegacyMergeSortOps V Temp α K Alg O E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O)
    (temporary : Option Temp := none) : Except E V := do
  ops.quick.checkBounds vector lo hi
  legacyMergeSortKernel ops vector lo hi algorithm order temporary

/--
Julia source: base/sort.jl:2480-2481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort!(v::AbstractVector{T}, lo::Integer, hi::Integer, a::MergeSortAlg, o::Ordering, t0::Vector{T}) where T =
    invoke(sort!, Tuple{typeof.((v, lo, hi, a, o))..., AbstractVector{T}}, v, lo, hi, a, o, t0) # For disambiguation
```
-/
def legacyMergeSortVectorScratch {V Temp α K Alg O E : Type}
    (ops : LegacyMergeSortOps V Temp α K Alg O E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O) (temporary : Temp) :
    Except E V :=
  legacyMergeSortBang ops vector lo hi algorithm order (some temporary)

structure LegacyPartialQuickSortOps (V α K Alg O E : Type) where
  quick : LegacyQuickSortOps V α K Alg O E
  firstTarget : Alg → K
  lastTarget : Alg → K
  lessEqIndex : K → K → Bool

/--
Julia source: base/sort.jl:2539-2566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _partialquicksort!(v::AbstractVector, lo::Integer, hi::Integer, a::PartialQuickSort,
                            o::Ordering)
    @inbounds while lo < hi
        if hi-lo <= SMALL_THRESHOLD
            _sort!(v, SMALL_ALGORITHM, o, (; lo, hi, scratch=nothing))
            return v
        end
        j = partition!(v, lo, hi, o)

        if j <= first(a.k)
            lo = j+1
        elseif j >= last(a.k)
            hi = j-1
        else
            # recurse on the smaller chunk
            # this is necessary to preserve O(log(n))
            # stack space in the worst case (rather than O(n))
            if j-lo < hi-j
                lo < (j-1) && _partialquicksort!(v, lo, j-1, a, o)
                lo = j+1
            else
                hi > (j+1) && _partialquicksort!(v, j+1, hi, a, o)
                hi = j-1
            end
        end
    end
    return v
end
```
-/
def legacyPartialQuickSortKernelLoop {V α K Alg O E : Type}
    (ops : LegacyPartialQuickSortOps V α K Alg O E)
    (algorithm : Alg) (order : O) :
    Nat → V → K → K → Except E V
  | 0, vector, lo, hi =>
    if ops.quick.lessIndex lo hi then .error ops.quick.modelExhausted else pure vector
  | fuel + 1, vector, lo, hi => do
    if ops.quick.lessIndex lo hi then
      if ops.quick.distance lo hi ≤ ops.quick.smallThreshold then
        ops.quick.smallSort vector ops.quick.smallAlgorithm order lo hi
      else
        let (vector, pivotIndex) ← partitionVector ops.quick vector lo hi order
        if ops.lessEqIndex pivotIndex (ops.firstTarget algorithm) then
          legacyPartialQuickSortKernelLoop ops algorithm order fuel
            vector (ops.quick.nextIndex pivotIndex) hi
        else if ops.lessEqIndex (ops.lastTarget algorithm) pivotIndex then
          legacyPartialQuickSortKernelLoop ops algorithm order fuel
            vector lo (ops.quick.previousIndex pivotIndex)
        else if ops.quick.distance lo pivotIndex < ops.quick.distance pivotIndex hi then
          let leftHi := ops.quick.previousIndex pivotIndex
          let vector ← if ops.quick.lessIndex lo leftHi then
            legacyPartialQuickSortKernelLoop ops algorithm order fuel vector lo leftHi
          else pure vector
          legacyPartialQuickSortKernelLoop ops algorithm order fuel
            vector (ops.quick.nextIndex pivotIndex) hi
        else
          let rightLo := ops.quick.nextIndex pivotIndex
          let vector ← if ops.quick.lessIndex rightLo hi then
            legacyPartialQuickSortKernelLoop ops algorithm order fuel vector rightLo hi
          else pure vector
          legacyPartialQuickSortKernelLoop ops algorithm order fuel
            vector lo (ops.quick.previousIndex pivotIndex)
    else
      pure vector

def legacyPartialQuickSortKernel {V α K Alg O E : Type}
    (ops : LegacyPartialQuickSortOps V α K Alg O E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O) : Except E V :=
  legacyPartialQuickSortKernelLoop ops algorithm order (ops.quick.distance lo hi + 2)
    vector lo hi

/--
Julia source: base/sort.jl:2533-2537 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort!(v::AbstractVector, lo::Integer, hi::Integer, a::PartialQuickSort,
               o::Ordering)
    checkbounds(v, lo:hi)
    _partialquicksort!(v, lo, hi, a, o)
end
```
-/
def legacyPartialQuickSortBang {V α K Alg O E : Type}
    (ops : LegacyPartialQuickSortOps V α K Alg O E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O) : Except E V := do
  ops.quick.checkBounds vector lo hi
  legacyPartialQuickSortKernel ops vector lo hi algorithm order

structure LegacySortOps (V K Alg O Kws Scratch E : Type) where
  firstIndex : V → K
  lastIndex : V → K
  checkBounds : V → K → K → Except E Unit
  keywords : K → K → Alg → Kws
  keywordsWithScratch : K → K → Alg → Scratch → Kws
  runSort : V → Alg → O → Kws → Except E V

/--
Julia source: base/sort.jl:2572-2576 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort!(v::AbstractVector, lo::Integer, hi::Integer, a::Algorithm, o::Ordering)
    checkbounds(v, lo:hi)
    _sort!(v, a, o, (; lo, hi, legacy_dispatch_entry=a))
    v
end
```
-/
def legacySortBounds {V K Alg O Kws Scratch E : Type}
    (ops : LegacySortOps V K Alg O Kws Scratch E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O) : Except E V := do
  ops.checkBounds vector lo hi
  let sorted ← ops.runSort vector algorithm order (ops.keywords lo hi algorithm)
  pure sorted

/--
Julia source: base/sort.jl:2571-2571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort!(v::AbstractVector, a::Algorithm, o::Ordering) = sort!(v, firstindex(v), lastindex(v), a, o)
```
-/
def legacySortWhole {V K Alg O Kws Scratch E : Type}
    (ops : LegacySortOps V K Alg O Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) : Except E V :=
  legacySortBounds ops vector (ops.firstIndex vector) (ops.lastIndex vector) algorithm order

/--
Julia source: base/sort.jl:2577-2577 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sort!(v::AbstractVector, lo::Integer, hi::Integer, a::Algorithm, o::Ordering, _) = sort!(v, lo, hi, a, o)
```
-/
def legacySortIgnoredScratch {V K Alg O Kws Scratch Ignored E : Type}
    (ops : LegacySortOps V K Alg O Kws Scratch E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O) (_ignored : Ignored) :
    Except E V :=
  legacySortBounds ops vector lo hi algorithm order

/--
Julia source: base/sort.jl:2578-2582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sort!(v::AbstractVector, lo::Integer, hi::Integer, a::Algorithm, o::Ordering, scratch::Vector)
    checkbounds(v, lo:hi)
    _sort!(v, a, o, (; lo, hi, scratch, legacy_dispatch_entry=a))
    v
end
```
-/
def legacySortWithScratch {V K Alg O Kws Scratch E : Type}
    (ops : LegacySortOps V K Alg O Kws Scratch E)
    (vector : V) (lo hi : K) (algorithm : Alg) (order : O) (scratch : Scratch) :
    Except E V := do
  ops.checkBounds vector lo hi
  let sorted ← ops.runSort vector algorithm order
    (ops.keywordsWithScratch lo hi algorithm scratch)
  pure sorted

structure LegacyDispatchOps (V K Alg O Kws Scratch E : Type) where
  getKeywords : Kws → Except E (K × K × Scratch × Option Alg)
  sameAlgorithm : Alg → Alg → Bool
  undefinedAlgorithm : V → Alg → O → E
  legacySort : V → K → K → Alg → O → Except E V

/--
Julia source: base/sort.jl:2586-2595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sort!(v::AbstractVector, a::Algorithm, o::Ordering, kw)
    @getkw lo hi scratch legacy_dispatch_entry
    if legacy_dispatch_entry === a
        # This error prevents infinite recursion for unknown algorithms
        throw(ArgumentError(LazyString("Base.Sort._sort!(::", typeof(v), ", ::", typeof(a), ", ::", typeof(o), ", ::Any) is not defined")))
    else
        sort!(v, lo, hi, a, o)
        scratch
    end
end
```
-/
def legacySortDispatch {V K Alg O Kws Scratch E : Type}
    (ops : LegacyDispatchOps V K Alg O Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E (V × Scratch) := do
  let (lo, hi, scratch, legacyEntry) ← ops.getKeywords keywords
  if legacyEntry.any (fun entry => ops.sameAlgorithm entry algorithm) then
    throw (ops.undefinedAlgorithm vector algorithm order)
  let sorted ← ops.legacySort vector lo hi algorithm order
  pure (sorted, scratch)

def arrayCheckBounds {α : Type} (values : Array α) (lo hi : Int) : Jl Unit :=
  if hi < lo then .ok ()
  else if 1 ≤ lo ∧ hi ≤ values.size then .ok ()
  else .error .boundsError

/-- The printed `typeof(v)`, `typeof(a)` and `typeof(o)` of the `ArgumentError` raised by the
`_sort!` fallback (sort.jl:2590); type printing is `show.jl`'s, so the caller supplies them. -/
structure SortSignatureNames where
  vector : String := ""
  algorithm : String := ""
  ordering : String := ""
  deriving Repr

/-- The keyword tuple `kw` of `_sort!(v, a, o, kw)`: `lo`, `hi`, `scratch` and
`legacy_dispatch_entry` (sort.jl:2578-2595). -/
structure ArraySortKeywords (α : Type) where
  lo : Int
  hi : Int
  scratch : Option (Array α) := none
  legacyEntry : Option Nat := none
  names : SortSignatureNames := {}

/-- The methods a program defines for its own `Algorithm` subtypes (no laws): `_sort!(v, ::TheirAlg,
o, kw)` and the old-style `sort!(v, lo, hi, ::TheirAlg, o)`, each optional. -/
structure UserAlgorithmMethods (V α : Type) where
  sortBang : Nat → Option (V → (α → α → SortResult Bool) → ArraySortKeywords α → SortResult (V × Option (Array α)))
  legacySortBang : Nat → Option (V → Int → Int → (α → α → SortResult Bool) → SortResult V)

/-- A program that defines no sorting methods for user algorithms. -/
def UserAlgorithmMethods.none {V α : Type} : UserAlgorithmMethods V α :=
  ⟨fun _ => Option.none, fun _ => Option.none⟩

/-- `AbstractVector` storage read and written by the sorting methods: the first index of
`axes(v, 1)`, `length(v)`, `v[i]` (`getindex`), `v[i] = x` (`setindex!`) at Julia indices, and the
program's `_sort!`/`sort!` methods for user algorithms on this vector type. `Array` is
`arrayStorageWith`. -/
structure VectorStorage (V α : Type) where
  firstindex : V → Int
  length : V → Nat
  getindex : V → Int → Jl α
  setindex : V → Int → α → Jl V
  userAlgorithms : UserAlgorithmMethods V α := UserAlgorithmMethods.none

/-- `lastindex(v) = last(axes(v, 1))`. -/
def VectorStorage.lastindex {V α : Type} (S : VectorStorage V α) (v : V) : Int :=
  S.firstindex v + Int.ofNat (S.length v) - 1

/-- `Array`: axes `OneTo(length(v))`, with the program's user-algorithm methods on `Vector`. -/
def arrayStorageWith {α : Type} (methods : UserAlgorithmMethods (Array α) α) :
    VectorStorage (Array α) α where
  firstindex := fun _ => 1
  length := Array.size
  getindex := arrayRead
  setindex := arrayWrite
  userAlgorithms := methods

/-- `Array` in a program with no user-algorithm sorting methods. -/
def arrayStorage {α : Type} : VectorStorage (Array α) α := arrayStorageWith UserAlgorithmMethods.none

/-- `checkbounds(Bool, v, lo:hi)`: `checkbounds(Bool, A, i) =
checkindex(Bool, eachindex(IndexLinear(), A), i)` (abstractarray.jl:690-693, installed
`checkboundsOne`), where `eachindex(IndexLinear(), v) = axes(v, 1)`;
`checkindex(Bool, inds, r::AbstractRange) = isempty(r) | (checkindex(Bool, inds, first(r)) &
checkindex(Bool, inds, last(r)))` (abstractarray.jl:757-758, installed `checkindexRange`) and
`checkindex(Bool, inds::AbstractUnitRange, i::Real) = (first(inds) <= i) & (i <= last(inds))`
(abstractarray.jl:751, installed `checkindexReal`). -/
def storageCheckBoundsBool {V α : Type} (S : VectorStorage V α) (values : V) (lo hi : Int) :
    abstractarray.Result Bool :=
  abstractarray.checkboundsOne (fun w : V => .ok ((S.firstindex w, S.lastindex w) : Int × Int))
    (abstractarray.checkindexRange
      (fun r : Int × Int => .ok (decide (r.2 < r.1)))
      (fun r => .ok r.1) (fun r => .ok r.2)
      (abstractarray.checkindexReal (fun a : Int × Int => .ok a.1) (fun a : Int × Int => .ok a.2)
        (fun l i => .ok (decide (l ≤ i))) (fun i l => .ok (decide (i ≤ l)))))
    values (lo, hi)

/-- `checkbounds(v, lo:hi)`: `checkbounds(Bool, v, lo:hi) || throw_boundserror(v, (lo:hi,))`
(abstractarray.jl:697-700). The `Bool` methods above throw nothing. -/
def storageCheckBounds {V α : Type} (S : VectorStorage V α) (values : V) (lo hi : Int) :
    Jl Unit :=
  match storageCheckBoundsBool S values lo hi with
  | .ok true => .ok ()
  | _ => .error .boundsError

def arrayIndices : IntegerIndexOps Int where
  addOne := fun i => i + 1
  previous := fun i => i - 1
  range := arrayIndexRange
  less := fun a b => decide (a < b)

def storageMutationOps {V α : Type} (S : VectorStorage V α) :
    VectorMutationOps (StateT V (Except SortException)) Unit α Int where
  get := fun _ index => fun values => do
    let value ← liftSortJl (S.getindex values index)
    pure (value, values)
  set := fun _ value index => fun values => do
    let updated ← liftSortJl (S.setindex values index value)
    pure ((), updated)
  indices := arrayIndices
  distance := fun lo hi => (hi - lo).toNat
  modelExhausted := fun {_} _ => .error (.errorException "fuel")

def storageInsertion {V α : Type} (S : VectorStorage V α) (lt : α → α → SortResult Bool)
    (values : V) (lo hi : Int) : SortResult V := do
  let (_, sorted) ←
    (insertionSort (storageMutationOps S) (fun (_ : Unit) a b => liftM (lt a b)) () () lo hi ()).run values
  pure sorted

def storageSwap {V α : Type} (S : VectorStorage V α) (values : V) (left right : Int) :
    SortResult V := do
  let leftValue ← liftSortJl (S.getindex values left)
  let rightValue ← liftSortJl (S.getindex values right)
  let updated ← liftSortJl (S.setindex values left rightValue)
  liftSortJl (S.setindex updated right leftValue)

def storageReverse {V α : Type} (S : VectorStorage V α) (values : V) (lo hi : Int) :
    SortResult V := do
  let mut values := values
  for offset in List.range ((hi - lo + 1).toNat / 2) do
    values ← storageSwap S values (lo + Int.ofNat offset) (hi - Int.ofNat offset)
  pure values

def storageCopyFromArray {V α : Type} (S : VectorStorage V α) (destination : V) (first : Int)
    (source : Array α) (sourceFirst : Int) (length : Nat) : SortResult V := do
  let mut destination := destination
  for offset in List.range length do
    let value ← liftSortJl (arrayRead source (sourceFirst + Int.ofNat offset))
    destination ← liftSortJl (S.setindex destination (first + Int.ofNat offset) value)
  pure destination

def storageQuickOps {V α : Type} (S : VectorStorage V α) (lt : α → α → SortResult Bool) :
    LegacyQuickSortOps V α Int Unit Unit SortException where
  midpoint := fun lo hi => lo + (hi - lo) / 2
  lessValue := fun _ => lt
  read := fun values index => liftSortJl (S.getindex values index)
  write := fun values index value => liftSortJl (S.setindex values index value)
  nextIndex := fun i => i + 1
  previousIndex := fun i => i - 1
  lessIndex := fun lo hi => decide (lo < hi)
  distance := fun lo hi => (hi - lo).toNat
  checkBounds := fun values lo hi => liftSortJl (storageCheckBounds S values lo hi)
  smallAlgorithm := ()
  smallThreshold := 20
  smallSort := fun values _ _ lo hi => storageInsertion S lt values lo hi
  modelExhausted := .errorException "fuel"

def storageMergeOps {V α : Type} [Inhabited α] (S : VectorStorage V α) (lt : α → α → SortResult Bool) :
    LegacyMergeSortOps V (Array α) α Int Unit Unit SortException where
  quick := storageQuickOps S lt
  oneIndex := 1
  lessEqIndex := fun lo hi => decide (lo ≤ hi)
  similar := fun _ length => .ok (Array.replicate length default)
  temporaryLength := Array.size
  resizeTemporary := fun values length =>
    .ok (values ++ Array.replicate (length - values.size) default)
  requireOneBased := fun _ => .ok ()
  readTemporary := fun values index => liftSortJl (arrayRead values index)
  writeTemporary := fun values index value => liftSortJl (arrayWrite values index value)

def storagePartialQuickOps {V α : Type} (S : VectorStorage V α) (lt : α → α → SortResult Bool) :
    LegacyPartialQuickSortOps V α Int (Int × Int) Unit SortException where
  quick := { storageQuickOps S lt with
    smallAlgorithm := (0, 0)
    smallSort := fun values _ _ lo hi => storageInsertion S lt values lo hi }
  firstTarget := Prod.fst
  lastTarget := Prod.snd
  lessEqIndex := fun lo hi => decide (lo ≤ hi)

def arrayScratchOps {α : Type} [Inhabited α] : ScratchOps (Array α) (Array α) JlError where
  allocate := fun length => .ok (Array.replicate length default)
  length := Array.size
  resize := fun values length => .ok (values ++ Array.replicate (length - values.size) default)
  sizeofBacking := 1
  multiply := Nat.mul
  divide := fun bytes size =>
    if size = 0 then .error .divideError else .ok (bytes / size)
  reinterpret := fun bytes values =>
    if bytes = 1 then .ok values else .error (.argumentError "incompatible element size")
  viewLength := Array.size
  allocateLength := by
    intro length values h
    cases h
    simp
  resizeLength := by
    intro values length result h
    cases h
    simp
    omega
  reinterpretBytes := by
    intro bytes values view h
    split at h <;> simp_all
  multiplyEq := fun _ _ => rfl
  divideEq := by
    intro a b q h
    split at h <;> simp_all
    omega

/-- The same scratch operations, reporting each error through `wrap`. -/
def ScratchOps.mapError {V W E E' : Type} (wrap : E → E') (ops : ScratchOps V W E) :
    ScratchOps V W E' where
  allocate := fun length => (ops.allocate length).mapError wrap
  length := ops.length
  resize := fun values length => (ops.resize values length).mapError wrap
  sizeofBacking := ops.sizeofBacking
  multiply := ops.multiply
  divide := fun bytes size => (ops.divide bytes size).mapError wrap
  reinterpret := fun bytes values => (ops.reinterpret bytes values).mapError wrap
  viewLength := ops.viewLength
  allocateLength := by
    intro length values h
    cases hr : ops.allocate length with
    | error e => rw [hr] at h; cases h
    | ok allocated => rw [hr] at h; cases h; exact ops.allocateLength length _ hr
  resizeLength := by
    intro values length result h
    cases hr : ops.resize values length with
    | error e => rw [hr] at h; cases h
    | ok resized => rw [hr] at h; cases h; exact ops.resizeLength values length _ hr
  reinterpretBytes := by
    intro bytes values view h
    cases hr : ops.reinterpret bytes values with
    | error e => rw [hr] at h; cases h
    | ok w => rw [hr] at h; cases h; exact ops.reinterpretBytes bytes values _ hr
  multiplyEq := ops.multiplyEq
  divideEq := by
    intro a b q h
    cases hr : ops.divide a b with
    | error e => rw [hr] at h; cases h
    | ok quotient => rw [hr] at h; cases h; exact ops.divideEq a b _ hr


/-- `partition!` writing into the vector from the scratch array (`swap == true`); the pivot
destination is the vector itself. -/
def vectorTargetPartitionOps {V α : Type} (S : VectorStorage V α)
    (pivot : Int → Int → Int) :
    ScratchPartitionOps V (Array α) V Int α (α → α → SortResult Bool) SortException where
  modelExhausted := .errorException "fuel"
  pivotIndex := fun lo hi => .ok (pivot lo hi)
  readSource := fun values index => liftSortJl (arrayRead values index)
  writeTarget := fun values index value => liftSortJl (S.setindex values index value)
  writePivot := fun target _ index value => do
    let updated ← liftSortJl (S.setindex target index value)
    pure (updated, updated)
  lessValue := fun order => order
  lessIndex := fun lo hi => decide (lo < hi)
  nextIndex := fun i => i + 1
  subtractIndex := Int.sub
  addBoolToIndex := fun i yes => i + if yes then 1 else 0
  addPivotOffset := Int.add
  distance := fun lo hi => (hi - lo).toNat

/-- `partition!` writing into the scratch array from the vector (`swap == false`); the pivot
destination is the vector. -/
def scratchTargetPartitionOps {V α : Type} (S : VectorStorage V α)
    (pivot : Int → Int → Int) :
    ScratchPartitionOps (Array α) V V Int α (α → α → SortResult Bool) SortException where
  modelExhausted := .errorException "fuel"
  pivotIndex := fun lo hi => .ok (pivot lo hi)
  readSource := fun values index => liftSortJl (S.getindex values index)
  writeTarget := fun values index value => liftSortJl (arrayWrite values index value)
  writePivot := fun target destination index value => do
    let updated ← liftSortJl (S.setindex destination index value)
    pure (target, updated)
  lessValue := fun order => order
  lessIndex := fun lo hi => decide (lo < hi)
  nextIndex := fun i => i + 1
  subtractIndex := Int.sub
  addBoolToIndex := fun i yes => i + if yes then 1 else 0
  addPivotOffset := Int.add
  distance := fun lo hi => (hi - lo).toNat

def storageScratchQuickOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (pivot : Int → Int → Int)
    (sortNext : V → Algorithm (BracketSortTarget Int) Int → (α → α → SortResult Bool) →
      ArraySortKeywords α → SortResult (V × Option (Array α))) :
    ScratchQuickSortOps V (Array α) α Int (Algorithm (BracketSortTarget Int) Int)
      (α → α → SortResult Bool) (ArraySortKeywords α) (Array α) SortException where
  rangeAndScratch := fun keywords => .ok (keywords.lo, keywords.hi, keywords.scratch)
  makeScratch := fun existing _ length =>
    match existing with
    | none => liftSortJl (makeScratchNothing arrayScratchOps length)
    | some backing => liftSortJl (makeScratchSame arrayScratchOps backing length)
  requireOffset := fun offset => match offset with
    | none => .error (.jl (.methodError "+"))
    | some value => .ok value
  oneMinus := fun i => 1 - i
  zeroIndex := 0
  negateIndex := Int.neg
  windowLength := fun lo hi => (hi - lo + 1).toNat
  lessIndex := fun lo hi => decide (lo < hi)
  lessEq := fun lo hi => decide (lo ≤ hi)
  distance := fun lo hi => (hi - lo).toNat
  addIndex := Int.add
  nextIndex := fun i => i + 1
  previousIndex := fun i => i - 1
  lowBound := fun alg => match alg with | .scratchQuickSort lo _ _ => lo | _ => none
  highBound := fun alg => match alg with | .scratchQuickSort _ hi _ => hi | _ => none
  smallThreshold := 20
  partitionInVector := vectorTargetPartitionOps S pivot
  partitionInScratch := scratchTargetPartitionOps S pivot
  copyTo := storageCopyFromArray S
  reverse := storageReverse S
  withScratch := fun keywords scratch => { keywords with scratch := some scratch }
  withBounds := fun keywords lo hi => { keywords with lo, hi }
  nextAlgorithm := fun alg => match alg with | .scratchQuickSort _ _ next => next | _ => .insertion
  sortNext := sortNext

def storageStableCheckOps {V α Alg : Type} (S : VectorStorage V α)
    (nextAlgorithm : Alg → Alg)
    (sortNext : V → Alg → (α → α → SortResult Bool) → ArraySortKeywords α →
      SortResult (V × Option (Array α))) :
    StableCheckSortedOps V Alg (α → α → SortResult Bool) Int
      (ArraySortKeywords α) (Option (Array α)) SortException where
  rangeAndScratch := fun keywords => .ok (keywords.lo, keywords.hi, keywords.scratch)
  isSorted := fun values lo hi order =>
    storageIssortedWindow arrayIndices (fun v lo hi => liftSortJl (storageCheckBounds S v lo hi))
      (fun v i => liftSortJl (S.getindex v i))
      (fun order => order) values lo hi order
  stableReverseOrdering := fun order a b => do pure (!(← order a b))
  reverse := storageReverse S
  nextAlgorithm := nextAlgorithm
  sort := sortNext

def storageCheckSortedOps {V α Alg : Type} (S : VectorStorage V α)
    (nextAlgorithm : Alg → Alg)
    (sortNext : V → Alg → (α → α → SortResult Bool) → ArraySortKeywords α →
      SortResult (V × Option (Array α))) :
    CheckSortedOps V Alg (α → α → SortResult Bool) Int
      (ArraySortKeywords α) (Option (Array α)) SortException where
  rangeAndScratch := fun kw => .ok (kw.lo, kw.hi, kw.scratch)
  difference := Int.sub
  isSorted := fun values lo hi order =>
    storageIssortedWindow arrayIndices (fun v lo hi => liftSortJl (storageCheckBounds S v lo hi))
      (fun v i => liftSortJl (S.getindex v i)) (fun order => order)
      values lo hi order
  reverseOrder := fun order a b => order b a
  reverse := storageReverse S
  nextAlgorithm := nextAlgorithm
  sort := sortNext

structure CountingKeywords (t : IntTy) where
  lo : Int
  hi : Int
  minimum : JInt t
  maximum : JInt t

def unsignedIntegerType : IntTy → IntTy
  | .i8 | .u8 => .u8
  | .i16 | .u16 => .u16
  | .i32 | .u32 => .u32
  | .i64 | .u64 => .u64
  | .i128 | .u128 => .u128

def signedIntegerType : IntTy → IntTy
  | .i8 | .u8 => .i8
  | .i16 | .u16 => .i16
  | .i32 | .u32 => .i32
  | .i64 | .u64 => .i64
  | .i128 | .u128 => .i128

def arrayCountingOps (t : IntTy) :
    CountingSortOps (Array (JInt t)) Int SearchIndex SearchIndex (Array Nat) Bool
      (CountingKeywords t) Unit SortException where
  rangeAndScratch := fun kw =>
    .ok (kw.lo, kw.hi, ⟨t, kw.minimum⟩, ⟨t, kw.maximum⟩, ())
  isReverse := id
  wrapSubtract := indexSub
  one := searchIndex .i64 1
  maybeUnsigned := fun value => searchIndex (unsignedIntegerType value.ty) value.val
  countLength := fun range => (indexAdd range (searchIndex .i64 1)).val.toNat
  allocateCounts := fun length => .ok (Array.replicate length 0)
  range := arrayIndexRange
  read := fun values index => do
    let value ← liftSortJl (arrayRead values index)
    pure ⟨t, value⟩
  write := fun values index value => do
    let converted ← liftSortJl (JInt.convert (t.name) t value.val)
    liftSortJl (arrayWrite values index converted)
  bucketForValue := fun value offset => (indexAdd value offset).val.toNat
  countRead := fun counts bucket =>
    match counts[bucket - 1]? with
    | some count => if bucket = 0 then .error (.jl .boundsError) else .ok count
    | none => .error (.jl .boundsError)
  countWrite := fun counts bucket value =>
    if 1 ≤ bucket ∧ bucket ≤ counts.size then .ok (counts.set! (bucket - 1) value)
    else .error (.jl .boundsError)
  bucketValues := fun range =>
    let last := indexAdd range (searchIndex .i64 1)
    (List.range last.val.toNat).map fun index => searchIndex last.ty (Int.ofNat index + 1)
  bucketIndex := fun value => value.val.toNat
  bucketValue := id
  lastBucketIndex := fun index count => index + Int.ofNat count - 1
  nextAfterBucket := fun index => index + 1
  valueNeedsSignedConversion := fun _ value => !value.ty.signed && t.signed
  toSigned := fun value => searchIndex (signedIntegerType value.ty) value.val

local instance (t : IntTy) : Inhabited (JInt t) := ⟨JInt.wrap t 0⟩

inductive LegacyArrayAlgorithm where
  | insertion
  | quick
  | merge
  | partialQuick (first last : Int)
  deriving BEq, DecidableEq

structure LegacyArrayKeywords (α : Type) where
  lo : Int
  hi : Int
  scratch : Option (Array α)
  entry : Option LegacyArrayAlgorithm

def storageLegacyFive {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (lt : α → α → SortResult Bool) (values : V) (lo hi : Int) (algorithm : LegacyArrayAlgorithm) :
    SortResult V := do
  match algorithm with
  | .insertion =>
    liftSortJl (storageCheckBounds S values lo hi)
    storageInsertion S lt values lo hi
  | .quick => legacyQuickSortBang (storageQuickOps S lt) values lo hi ()
  | .merge => legacyMergeSortBang (storageMergeOps S lt) values lo hi () ()
  | .partialQuick first last =>
    legacyPartialQuickSortBang (storagePartialQuickOps S lt) values lo hi (first, last) ()

def storageLegacyRun {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (lt : α → α → SortResult Bool) (values : V) (algorithm : LegacyArrayAlgorithm)
    (keywords : LegacyArrayKeywords α) : SortResult V := do
  match algorithm with
  | .insertion => storageInsertion S lt values keywords.lo keywords.hi
  | _ =>
    let ops : LegacyDispatchOps V Int LegacyArrayAlgorithm Unit
        (LegacyArrayKeywords α) (Option (Array α)) SortException := {
      getKeywords := fun kw => .ok (kw.lo, kw.hi, kw.scratch, kw.entry)
      sameAlgorithm := BEq.beq
      undefinedAlgorithm := fun _ _ _ =>
        .jl (.argumentError "Base.Sort._sort! is not defined for this algorithm")
      legacySort := fun current lo hi alg _ => storageLegacyFive S lt current lo hi alg
    }
    let (sorted, _) ← legacySortDispatch ops values algorithm () keywords
    pure sorted

def storageLegacyOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (lt : α → α → SortResult Bool) :
    LegacySortOps V Int LegacyArrayAlgorithm Unit
      (LegacyArrayKeywords α) (Array α) SortException where
  firstIndex := S.firstindex
  lastIndex := S.lastindex
  checkBounds := fun values lo hi => liftSortJl (storageCheckBounds S values lo hi)
  keywords := fun lo hi algorithm => ⟨lo, hi, none, some algorithm⟩
  keywordsWithScratch := fun lo hi algorithm scratch => ⟨lo, hi, some scratch, some algorithm⟩
  runSort := fun values algorithm _ keywords => storageLegacyRun S lt values algorithm keywords

def bracketTargetIndices : BracketSortTarget Int → List Int
  | .index value => [value]
  | .range first last => arrayIndexRange first last
  | .ordinal first step _ length =>
    (List.range length).map fun index => first + Int.ofNat index * step

def bracketTargetEndpoints : SortTargetOps (BracketSortTarget Int) Int where
  first := fun target => match target with
    | .index value => value
    | .range first _ | .ordinal first _ _ _ => first
  last := fun target => match target with
    | .index value => value
    | .range _ last | .ordinal _ _ last _ => last

def minimumIntList : List Int → Option Int
  | [] => none
  | first :: rest => some (rest.foldl min first)

def maximumIntList : List Int → Option Int
  | [] => none
  | first :: rest => some (rest.foldl max first)

def bracketTargetMinimum (target : BracketSortTarget Int) : Jl Int :=
  match minimumIntList (bracketTargetIndices target) with
  | some value => .ok value
  | none => .error (.argumentError "reducing over an empty collection")

def bracketTargetMaximum (target : BracketSortTarget Int) : Jl Int :=
  match maximumIntList (bracketTargetIndices target) with
  | some value => .ok value
  | none => .error (.argumentError "reducing over an empty collection")

def shiftBracketTarget : BracketSortTarget Int → Nat → BracketSortTarget Int
  | .index value, count => .index (value - Int.ofNat count)
  | .range first last, count => .range (first - Int.ofNat count) (last - Int.ofNat count)
  | .ordinal first step last length, count =>
    .ordinal (first - Int.ofNat count) step (last - Int.ofNat count) length

structure BracketNumerics where
  cbrt : Nat → Float
  roundInt : Float → Jl Int
  floorInt : Float → Jl Int
  topSetBit : Nat → Nat
  hashLength : Nat → Nat
  hashAttempt : Nat → Nat → Nat
  sampleIndex : Nat → Int → Int → Jl Int

/-- `base/special/cbrt.jl:144-150`: the installed binary64 cube-root model. -/
def bracketCbrt (n : Nat) : Float :=
  let x := float.floatOfInt .f64 (int.lit .i64 (Int.ofNat n))
  let root := match special.cbrt.cbrt (.f64 x) with
    | .f64 value => value
    | .f32 value => float.convertFloat .f64 (S := .f32) value
  Float.ofBits (UInt64.ofNat root.toBits)

/-- `base/rounding.jl:485-486`, `base/float.jl:458-461,888-919`:
round in binary64, then use the installed checked Int64 conversion. -/
def bracketRoundInt (x : Float) : Jl Int := do
  let value : float.FV .f64 := JuliaLean.Promotion.Fl.ofBits x.toBits.toNat
  let result ← float.intOfFloat .i64 (float.round_Nearest_llvm value)
  pure result.val

/-- `base/rounding.jl:486`, `base/float.jl:459,921-932`: checked Int64 floor. -/
def bracketFloorInt (x : Float) : Jl Int := do
  let value : float.FV .f64 := JuliaLean.Promotion.Fl.ofBits x.toBits.toNat
  let result ← float.intOfFloat .i64 (float.round_Down_llvm value)
  pure result.val

/-- `base/sort.jl:1320`, `base/hashing.jl:75-76`:
the sample index is the seeded integer hash reduced into the remaining interval.
The UInt64 subtraction retains Julia's mixed signed/unsigned wrapping. -/
def sourceHashSample (seed : Nat) (lo hi : Int) : Jl Int := do
  let hash := hashing.hashInt64 (int.lit .i64 lo) (int.lit .u64 (Int.ofNat seed))
  let difference := int.lit .u64 (hash.val - lo)
  let length := int.lit .i64 (hi - lo + 1)
  let remainder ← div.modMixedUnsignedSigned difference length
  pure (int.add remainder (int.lit .i64 lo)).val

/-- `base/sort.jl:1280-1320`: installed numeric callees, including Julia's
deterministic hash-based sample selection. -/
def defaultBracketNumerics : BracketNumerics where
  cbrt := bracketCbrt
  roundInt := bracketRoundInt
  floorInt := bracketFloorInt
  topSetBit := fun n => if n = 0 then 0 else Nat.log2 n + 1
  hashLength := fun n =>
    (hashing.hashInt64 (int.lit .i64 (Int.ofNat n))
      (int.lit .u64 0x85eb830e0216012d)).val.toNat
  hashAttempt := fun attempt seed =>
    (hashing.hashInt64 (int.lit .i64 (Int.ofNat attempt))
      (int.lit .u64 (Int.ofNat seed))).val.toNat
  sampleIndex := sourceHashSample

def sourceApplyInitialOptimizations {Target Index : Type} :
    Algorithm Target Index → Algorithm Target Index
  | .quick => maybeApplyInitialQuick
  | .merge => maybeApplyInitialMerge
  | .insertion => maybeApplyInitialInsertion
  | algorithm => maybeApplyInitialGeneric algorithm

def storageBracketKernelOps {V α : Type} (S : VectorStorage V α) (lt : α → α → SortResult Bool) :
    BracketKernelOps V α Int Unit SortException where
  checkBounds := fun values lo hi => liftSortJl (storageCheckBounds S values lo hi)
  range := arrayIndexRange
  read := fun values index => liftSortJl (S.getindex values index)
  less := fun _ => lt
  swap := storageSwap S
  scaleByBool := fun i yes => if yes then i else 0
  addIndexOffset := Int.add
  addInt := Int.add
  boolMinusOne := fun yes => if yes then 0 else -1

def storageMoveOps {V α : Type} (S : VectorStorage V α) :
    MoveVectorOps V (BracketSortTarget Int) Int SortException where
  length := fun target => (bracketTargetIndices target).length
  disjoint := fun left right =>
    !(bracketTargetIndices left).any fun value => (bracketTargetIndices right).contains value
  indices := bracketTargetIndices
  minimum := fun target => liftSortJl (bracketTargetMinimum target)
  maximum := fun target => liftSortJl (bracketTargetMaximum target)
  lessEq := fun a b => decide (a ≤ b)
  lengthMismatch := .assertionError "length mismatch"
  rangeMismatch := .assertionError "range mismatch"
  swap := storageSwap S
  reverse := storageReverse S

abbrev ArrayBracketAlgorithm :=
  BracketSortTarget Int ×
    (BracketSortTarget Int → Algorithm (BracketSortTarget Int) Int)

def storageBracketOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics)
    (sortSegment : V → Algorithm (BracketSortTarget Int) Int →
      (α → α → SortResult Bool) → ArraySortKeywords α → SortResult (V × Option (Array α))) :
    BracketedSortOps V α Int ArrayBracketAlgorithm
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool) (ArraySortKeywords α)
      (Option (Array α)) SortException (V × Option (Array α)) where
  rangeAndScratch := fun kw => .ok (kw.lo, kw.hi, kw.scratch)
  rangeLength := fun lo hi => (hi - lo + 1).toNat
  lessIndex := fun a b => decide (a < b)
  lessEqIndex := fun a b => decide (a ≤ b)
  advance := fun i amount => i + Int.ofNat amount
  range := arrayIndexRange
  target := Prod.fst
  targetMinimum := fun target => liftSortJl (bracketTargetMinimum target)
  targetMaximum := fun target => liftSortJl (bracketTargetMaximum target)
  shiftTarget := shiftBracketTarget
  nextAlgorithm := fun algorithm target => algorithm.2 target
  cbrt := numeric.cbrt
  square := fun value => value * value
  roundInt := fun value => liftSortJl (numeric.roundInt value)
  floatOfNat := Float.ofNat
  floatOfIndex := Float.ofInt
  differenceToFloat := fun a b => Float.ofInt (a - b)
  topSetBitFloat := fun value => Float.ofNat (numeric.topSetBit value)
  multiplyFloat := Float.mul
  divideFloat := Float.div
  addFloat := Float.add
  subtractFloat := Float.sub
  negateFloat := Float.neg
  lessEqFloat := fun a b => a ≤ b
  floorIndex := fun value => liftSortJl (numeric.floorInt value)
  minimumIndex := min
  maximumIndex := max
  inclusiveSpan := fun lo hi => Float.ofInt (hi - lo + 1)
  seedForLength := numeric.hashLength
  hashAttempt := numeric.hashAttempt
  hashIndex := fun seed lo hi => liftSortJl (numeric.sampleIndex seed lo hi)
  swap := storageSwap S
  read := fun values index => liftSortJl (S.getindex values index)
  checkFailure := .assertionError "this should never happen"
  kernelOps := {
    checkBounds := fun values lo hi => liftSortJl (storageCheckBounds S values lo hi)
    range := arrayIndexRange
    read := fun values index => liftSortJl (S.getindex values index)
    less := fun order => order
    swap := storageSwap S
    scaleByBool := fun i yes => if yes then i else 0
    addIndexOffset := Int.add
    addInt := Int.add
    boolMinusOne := fun yes => if yes then 0 else -1
  }
  moveOps := storageMoveOps S
  sortSegment := sortSegment
  keywordsWithHi := fun kw hi => { kw with hi }
  finish := fun values scratch => (values, scratch)

/-- `base/sort.jl:683-684`: the generic-element branch of MissingOptimization.
Only the continuation is needed when neither specialized Missing branch applies. -/
def sortMissingFallback {V Alg O Kws R E : Type}
    (sort : V → Alg → O → Kws → Except E R)
    (vector : V) (next : Alg) (order : O) (keywords : Kws) : Except E R :=
  sort vector next order keywords

/-- `base/sort.jl:728-729`: the generic-element branch of IEEEFloatOptimization.
The reinterpretation and partition capabilities belong to the specialized model. -/
def sortIEEEFloatFallback {V Alg O Kws R E : Type}
    (sort : V → Alg → O → Kws → Except E R)
    (vector : V) (next : Alg) (order : O) (keywords : Kws) : Except E R :=
  sort vector next order keywords

/-- `_sort!` dispatch on the algorithm for an `AbstractVector` whose element type has no
specialised `Missing`, `Bool`, `IEEEFloat` or `UIntMappable` method. The fuel only bounds the
nesting of algorithm wrappers; `sourceSortWindow` supplies the algorithm's depth. -/
def sourceSortLoop {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) :
    Nat → V → Algorithm (BracketSortTarget Int) Int → (α → α → SortResult Bool) →
      ArraySortKeywords α → SortResult (V × Option (Array α))
  | 0, _, _, _, _ => .error (.errorException "fuel")
  | fuel + 1, values, algorithm, order, keywords =>
    let step := sourceSortLoop S numeric pivot fuel
    match algorithm with
    | .defaultStable | .defaultUnstable =>
      sortDefaultAlgorithm step values order keywords
    | .subArray _ =>
      sortSubArrayFallback step
        (fun alg => match alg with | .subArray next => next | _ => alg)
        values algorithm order keywords
    | .missing next =>
      sortMissingFallback step values next order keywords
    | .boolOptimization _ =>
      sortBoolOther step
        (fun alg => match alg with | .boolOptimization next => next | _ => alg)
        values algorithm order keywords
    | .small threshold _ _ =>
      let ops : SmallSortOps V (Algorithm (BracketSortTarget Int) Int)
          (α → α → SortResult Bool) Int (ArraySortKeywords α) (V × Option (Array α)) SortException := {
        range := fun kw => .ok (kw.lo, kw.hi)
        spanLessThan := fun lo hi limit => decide (hi - lo < Int.ofNat limit)
        smallAlgorithm := fun alg => match alg with | .small _ small _ => small | _ => alg
        bigAlgorithm := fun alg => match alg with | .small _ _ big => big | _ => alg
        sort := step
      }
      sortSmall ops values algorithm threshold order keywords
    | .ieeeFloat next =>
      sortIEEEFloatFallback step values next order keywords
    | .isUIntMappable _ _ =>
      let ops : UIntMappableSortOps V (Algorithm (BracketSortTarget Int) Int)
          (α → α → SortResult Bool) (ArraySortKeywords α) (V × Option (Array α)) SortException := {
        elementType := fun _ => α
        uintMappable := uintMappableFallback
        yesAlgorithm := fun alg => match alg with | .isUIntMappable yes _ => yes | _ => alg
        noAlgorithm := fun alg => match alg with | .isUIntMappable _ no => no | _ => alg
        sort := step
      }
      sortIsUIntMappable ops values algorithm order keywords
    | .checkSorted _ =>
      sortCheckSorted
        (storageCheckSortedOps S
          (fun alg => match alg with | .checkSorted next => next | _ => alg) step)
        values algorithm order keywords
    | .stableCheckSorted _ =>
      sortStableCheck
        (storageStableCheckOps S
          (fun alg => match alg with | .stableCheckSorted next => next | _ => alg) step)
        values algorithm order keywords
    | .scratchQuickSort _ _ _ =>
      sortScratchQuick (storageScratchQuickOps S pivot step)
        values algorithm order keywords
    | .bracketedSort target getNext =>
      sortBracketed (storageBracketOps S numeric step)
        values (target, getNext) order keywords
    | .insertion => do
      let sorted ← storageInsertion S order values keywords.lo keywords.hi
      pure (sorted, keywords.scratch)
    | .quick => do
      let sorted ← legacyQuickSortBang (storageQuickOps S order) values keywords.lo keywords.hi ()
      pure (sorted, keywords.scratch)
    | .merge => do
      let sorted ← legacyMergeSortBang (storageMergeOps S order) values keywords.lo keywords.hi () ()
      pure (sorted, keywords.scratch)
    | .partialQuickSort target => do
      let sorted ← legacyPartialQuickSortBang (storagePartialQuickOps S order) values
        keywords.lo keywords.hi
        (bracketTargetEndpoints.first target, bracketTargetEndpoints.last target) ()
      pure (sorted, keywords.scratch)
    | .considerCounting _ _ =>
      sortConsiderCountingOther step
        (fun alg => match alg with | .considerCounting _ next => next | _ => alg)
        values algorithm order keywords
    | .computeExtrema _ | .counting | .considerRadix _ _ | .radix =>
      .error (.jl (.methodError "algorithm requires a direct integer ordering"))
    | .user tag =>
      match S.userAlgorithms.sortBang tag with
      | some method => method values order keywords
      | none =>
        -- `_sort!(v::AbstractVector, a::Algorithm, o::Ordering, kw)` (sort.jl:2586-2595)
        if keywords.legacyEntry = some tag then
          .error (.jl (.argumentError ("Base.Sort._sort!(::" ++ keywords.names.vector ++ ", ::" ++
            keywords.names.algorithm ++ ", ::" ++ keywords.names.ordering ++ ", ::Any) is not defined")))
        else do
          match S.userAlgorithms.legacySortBang tag with
          | some method =>
            let sorted ← method values keywords.lo keywords.hi order
            pure (sorted, keywords.scratch)
          | none =>
            -- `sort!(v, lo, hi, a, o)` (sort.jl:2572-2576): `checkbounds(v, lo:hi)`, then
            -- `_sort!(v, a, o, (; lo, hi, legacy_dispatch_entry=a))`.
            liftSortJl (storageCheckBounds S values keywords.lo keywords.hi)
            let (sorted, _) ← step values algorithm order
              { lo := keywords.lo, hi := keywords.hi, legacyEntry := some tag,
                names := keywords.names }
            pure (sorted, keywords.scratch)

def sourceSortWindow {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int)
    (values : V) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (order : α → α → SortResult Bool) (keywords : ArraySortKeywords α) : SortResult (V × Option (Array α)) :=
  sourceSortLoop S numeric pivot (algorithm.depth + 16) values algorithm order keywords

def sourceSortBang {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int)
    (values : V) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (order : α → α → SortResult Bool) (keywords : ArraySortKeywords α) : SortResult V := do
  let (sorted, _) ← sourceSortWindow S numeric pivot values algorithm order keywords
  pure sorted

def sourceVectorSortOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) :
    SortVectorOps V (Algorithm (BracketSortTarget Int) Int)
      (α → α → SortResult Bool) Unit (α → α → SortResult Bool)
      (Option (Array α)) (ArraySortKeywords α) SortException where
  applyInitialOptimizations := sourceApplyInitialOptimizations
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  runSort := fun values algorithm order keywords =>
    sourceSortBang S numeric pivot values algorithm order
      { keywords with lo := S.firstindex values, hi := S.lastindex values }
  withScratch := fun scratch => { lo := 1, hi := 0, scratch }

/-- The value of `maybeview(v, k)` (sort.jl:110-111): `v[k]` for an integer `k`, the selected
elements of the view `view(v, k)` for a range `k`. -/
inductive PartialResult (α : Type) where
  | element (value : α)
  | elements (values : List α)

def storagePartialSortOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) :
    PartialSortOps V (BracketSortTarget Int) Int (α → α → SortResult Bool)
      (Option (Array α)) (ArraySortKeywords α) (PartialResult α) SortException where
  targetOps := bracketTargetEndpoints
  sort := fun values algorithm order keywords =>
    sourceSortBang S numeric pivot values algorithm order
      { keywords with lo := S.firstindex values, hi := S.lastindex values }
  maybeView := fun values target => match target with
    | .index index => do
      pure (.element (← liftSortJl (maybeviewInteger S.getindex values index)))
    | _ => do
      pure (.elements (← liftSortJl (maybeviewRange
        (fun current selection => (bracketTargetIndices selection).mapM (S.getindex current))
        values target)))
  withScratch := fun scratch => { lo := 1, hi := 0, scratch }
  scratchOfKeywords := ArraySortKeywords.scratch

def storagePartialSortpermOps {V α : Type} [Inhabited α] (S : VectorStorage V α) (t : IntTy)
    (pivot : Int → Int → Int) :
    PartialSortpermOps (Array (JInt t)) V (BracketSortTarget Int) Nat Int
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool) Unit
      (α → α → SortResult Bool) (JInt t → JInt t → SortResult Bool) (ArraySortKeywords (JInt t))
      (List (JInt t)) SortException where
  makeIndexVector := fun values _ => .ok (Array.replicate (S.length values) (JInt.wrap t 0))
  axesIndex := Array.size
  axesVector := S.length
  axesEqual := fun a b => decide (a = b)
  axesError := fun _ _ => .jl (.argumentError "index vector must share the source axes")
  eachIndex := fun indices => arrayIndexRange 1 indices.size
  writeIndex := fun indices target value => do
    let converted ← liftSortJl (JInt.convert (t.name) t value)
    liftSortJl (arrayWrite indices target converted)
  scratchQuickSort := fun target => scratchQuickRange bracketTargetEndpoints target
  initialOptimizations := initialOptimizations
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  permutationOrder := fun less values a b => do
    let left ← liftSortJl (S.getindex values a.val)
    let right ← liftSortJl (S.getindex values b.val)
    let ab ← less left right
    let ba ← less right left
    pure (ab || (!ba && decide (a.val < b.val)))
  emptyKeywords := { lo := 1, hi := 0, scratch := none }
  sort := fun indices algorithm order kw =>
    sourceSortBang arrayStorage defaultBracketNumerics pivot indices algorithm order
      { kw with lo := 1, hi := Int.ofNat indices.size }
  maybeView := fun indices target => liftSortJl ((bracketTargetIndices target).mapM (arrayRead indices))

structure ArrayWindow where
  first : Int
  stride : Int
  length : Nat

def arrayWindowIndex (window : ArrayWindow) (index : Int) : Int :=
  window.first + (index - 1) * window.stride

def storageSendToEndOps {V α : Type} (S : VectorStorage V α) :
    SendToEndOps (StateT V (Except SortException)) ArrayWindow α Int where
  get := fun window index => fun values => do
    let value ← liftSortJl (S.getindex values (arrayWindowIndex window index))
    pure (value, values)
  set := fun window value index => fun values => do
    let updated ← liftSortJl (S.setindex values (arrayWindowIndex window index) value)
    pure ((), updated)
  firstIndex := fun _ => 1
  lastIndex := fun window => window.length
  lessEq := fun a b => decide (a ≤ b)
  next := fun i => i + 1
  previous := fun i => i - 1
  distance := fun lo hi => (hi - lo).toNat
  reverseView := fun window hi lo => pure {
    first := arrayWindowIndex window hi
    stride := -window.stride
    length := (hi - lo + 1).toNat
  }
  add := Int.add
  subtract := Int.sub
  modelExhausted := fun {_} _ => .error (.errorException "fuel")

def storageBoolSortOps {V : Type} (S : VectorStorage V Bool) :
    BoolSortOps V Int (Bool → Bool → SortResult Bool) (Int × Int) Unit V SortException where
  less := fun order => order
  rangeAndScratch := fun (lo, hi) => .ok (lo, hi, ())
  range := arrayIndexRange
  read := fun values index => liftSortJl (S.getindex values index)
  firstSegmentEnd := fun lo count => lo + Int.ofNat count - 1
  secondSegmentStart := fun lo count => lo + Int.ofNat count
  setSegment := fun values lo hi value => do
    let mut values := values
    for index in arrayIndexRange lo hi do
      values ← liftSortJl (S.setindex values index value)
    pure values
  returnVector := id
  returnScratch := fun values _ => values

def defaultScalarPrimitives : ScalarPrimitives where
  throwdm := fun _ _ _ => .error (.broadcast .dimensionMismatch)

/-- `base/accumulate.jl:362-367,436-453`, specialized to one-based Int64 vectors:
read the first value, check linear indices, then accumulate through installed heap accesses. -/
def nativeCumsum (dest source : Vec) : M Vec := do
  let length ← integerAction (array.heapLength source.handle)
  if length.val = 0 then return dest
  let mut current ← integerRead source (int.lit .i64 1)
  let destLength ← integerAction (array.heapLength dest.handle)
  if destLength.val ≠ length.val then
    throw (.broadcast .dimensionMismatch)
  integerWrite dest current (int.lit .i64 1)
  for index in ← liftM (nativeRange (int.lit .i64 2) length) do
    current := int.add current (← integerRead source index)
    integerWrite dest current index
  pure dest

def arrayRadixOps (heuristic : Int → Int → JInt .u64 → Jl UInt8) : RadixSortOps where
  pass := nativeRadixPassOps defaultScalarPrimitives nativeCumsum
  heuristic := fun lo hi bits =>
    some (do
      let c ← heuristic lo.val hi.val bits
      pure (int.lit .u8 c.toNat))
  allocateCounts := fun n =>
    integerAction (array.heapVectorAllocate intTyLayout .i64 n)

def runArrayRadixSort (ops : RadixSortOps) (vector : Array Nat) (lo hi : Int)
    (bits : JInt .u64) (scratch : Array Nat) (offset : Int)
    (chunkSize? : Option UInt8 := none) :
    Option (SortResult (Array Nat × Array Nat × Bool)) :=
  let vVec : Vec := ⟨0, .u64, [vector.size], [(1, vector.size)]⟩
  let sVec : Vec := ⟨1, .u64, [scratch.size], [(1, scratch.size)]⟩
  let vSlots : List (Option U) := vector.toList.map (fun v : Nat => some (int.lit .u64 (Int.ofNat v)))
  let sSlots : List (Option U) := scratch.toList.map (fun v : Nat => some (int.lit .u64 (Int.ofNat v)))
  let heap : Heap := { integers := [], unsigned := [vSlots, sSlots] }
  match radixSortBang ops vVec sVec (int.lit .i64 lo) (int.lit .i64 hi) (int.lit .i64 offset)
      bits (chunkSize?.map (fun c => int.lit .u8 c.toNat)) heap with
  | none => none
  | some (.error err) => some (.error (.native err))
  | some (.ok (inVector, heap')) => some (do
    let decode (slots : Option (List (Option U))) : SortResult (Array Nat) := do
      let slots ← match slots with
        | none => .error (.native (.array .bounds))
        | some slots => pure slots
      let values ← slots.mapM fun slot => match slot with
        | none => .error (.native (.array .undefinedReference))
        | some value => pure value.val.toNat
      pure values.toArray
    let outV ← decode heap'.unsigned[0]?
    let outS ← decode heap'.unsigned[1]?
    pure (outV, outS, inVector))

abbrev NTuple (n : Nat) (α : Type) := { xs : List α // xs.length = n }
abbrev AnyNTuple (α : Type) := Sigma fun n : Nat => NTuple n α

def mergeAnyNTupleLoop {α : Type} [Inhabited α] (lt : α → α → SortResult Bool) :
    Nat → AnyNTuple α → AnyNTuple α → SortResult (AnyNTuple α)
  | 0, _, _ => .error (.errorException "fuel")
  | fuel + 1, left, right =>
    match left.2.val, right.2.val with
    | [], [] => pure (mergeTupleBothEmpty left right ())
    | [], _ :: _ => pure (mergeTupleLeftEmpty left right ())
    | _ :: _, [] => pure (mergeTupleRightEmpty left right ())
    | _ :: _, _ :: _ =>
      mergeTupleNonempty {
        head := fun values => values.2.val.headD default
        tail := fun ⟨n, ⟨xs, h⟩⟩ => ⟨n - 1, ⟨xs.tail, by simp [h]⟩⟩
        prepend := fun x ⟨n, ⟨xs, h⟩⟩ => ⟨n + 1, ⟨x :: xs, by simp [h]⟩⟩
        less := fun (_ : Unit) => lt
        merge := fun a b _ => mergeAnyNTupleLoop lt fuel a b
      } left right ()

def mergeNTuple {α : Type} [Inhabited α] (lt : α → α → SortResult Bool)
    {m n : Nat} (left : NTuple m α) (right : NTuple n α) : SortResult (NTuple (m + n) α) := do
  let merged ← mergeAnyNTupleLoop lt (m + n + 1) ⟨m, left⟩ ⟨n, right⟩
  if h : merged.2.val.length = m + n then
    pure ⟨merged.2.val, h⟩
  else
    .error (.jl (.methodError "tuple merge length mismatch"))

def anyNTupleMergeOps {α : Type} [Inhabited α] (lt : α → α → SortResult Bool) :
    TupleMergeOps (AnyNTuple α) Unit SortException where
  length := fun t => t.2.val.length
  split := fun ⟨_, ⟨xs, _⟩⟩ index =>
    (⟨(xs.take index).length, ⟨xs.take index, rfl⟩⟩,
     ⟨(xs.drop index).length, ⟨xs.drop index, rfl⟩⟩)
  splitSmaller := by
    rintro ⟨_, ⟨xs, _⟩⟩ h
    change 1 < xs.length at h
    show (xs.take (xs.length / 2)).length < xs.length ∧
      (xs.drop (xs.length / 2)).length < xs.length
    simp only [List.length_take, List.length_drop]
    omega
  merge := fun left right _ =>
    mergeAnyNTupleLoop lt (left.2.val.length + right.2.val.length + 1) left right

def mergeSortNTuple {α : Type} [Inhabited α] (lt : α → α → SortResult Bool)
    {n : Nat} (tuple : NTuple n α) : SortResult (NTuple n α) := do
  let sorted ← mergeSortTupleRecursive (anyNTupleMergeOps lt) ⟨n, tuple⟩ ()
  if h : sorted.2.val.length = n then
    pure ⟨sorted.2.val, h⟩
  else
    .error (.jl (.methodError "tuple length changed"))

def nTupleCoreOps {α : Type} [Inhabited α] (n : Nat) (pivot : Int → Int → Int) :
    TupleSortCoreOps (NTuple n α) (Array α) (Algorithm (BracketSortTarget Int) Int)
      (α → α → SortResult Bool) (Option (Array α)) SortException where
  length := fun _ => n
  copyMutable := fun values => .ok values.val.toArray
  sortMutable := fun values algorithm order scratch =>
    sourceSortBang arrayStorage defaultBracketNumerics pivot values algorithm order
      { lo := 1, hi := Int.ofNat values.size, scratch }
  constructLike := fun _ values =>
    if h : values.toList.length = n then .ok ⟨values.toList, h⟩
    else .error (.jl (.methodError "tuple length changed"))
  mergeSort := fun values order => mergeSortNTuple order values

def nTuplePublicOps {α : Type} [Inhabited α] (n : Nat) (pivot : Int → Int → Int) :
    TuplePublicSortOps (NTuple n α) (Algorithm (BracketSortTarget Int) Int)
      (α → α → SortResult Bool) Unit (α → α → SortResult Bool) (Array α) (Option (Array α)) SortException where
  scratchMatches := fun _ _ => true
  argumentError := fun message => .jl (.argumentError message)
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  keywords := id
  sortTuple := fun values algorithm order keywords =>
    match algorithm with
    | .defaultStable | .defaultUnstable =>
      sortTupleCore (nTupleCoreOps n pivot) values algorithm order keywords
    | _ => .error (.jl (.methodError "Base.Sort._sort"))
  assertSameType := fun _ result => .ok result

def arrayPermutationOrder {α : Type} [Inhabited α]
    (order : α → α → SortResult Bool) (values : Array α) (left right : Int) : SortResult Bool := do
  let a ← liftSortJl (arrayRead values left)
  let b ← liftSortJl (arrayRead values right)
  let ab ← order a b
  let ba ← order b a
  pure (ab || (!ba && decide (left < right)))

def arrayIntegerExtrema (values : Array Int) : Jl (Int × Int) :=
  match values.toList with
  | [] => .error (.argumentError "reducing over an empty collection")
  | first :: rest => .ok (rest.foldl min first, rest.foldl max first)

def arraySortpermCoreOps {α : Type} [Inhabited α] (pivot : Int → Int → Int)
    (integerView : Array α → SortResult (Array Int)) (hasIntegerElements : Array α → Bool)
    (isForward : (α → α → SortResult Bool) → Bool := fun _ => false) :
    SortpermCoreOps (Array α) (Array α) (Array Int)
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool)
      (Int → Int → SortResult Bool) (Option (Array Int)) Unit (Array Int) Int SortException where
  isForward := isForward
  isVector := fun _ => true
  hasIntegerElements := hasIntegerElements
  length := Array.size
  extrema := fun values => do
    let integerValues ← integerView values
    liftSortJl (arrayIntegerExtrema integerValues)
  subtractWithOverflow := fun a b =>
    let exact := a - b
    ((JInt.wrap .i64 exact).val, decide (exact < IntTy.min .i64 ∨ IntTy.max .i64 < exact))
  addWithOverflow := fun a b =>
    let exact := a + b
    ((JInt.wrap .i64 exact).val, decide (exact < IntTy.min .i64 ∨ IntTy.max .i64 < exact))
  oneUnit := 1
  rangeLessThanHalf := fun value half => decide (value < Int.ofNat half)
  sortpermIntRange := fun values length minimum => do
    let integers ← integerView values
    let (_, (_, perm)) ←
      liftSortJl ((sortpermIntRange arraySortpermRangeOps integers (int.lit .i64 length) (int.lit .i64 minimum)).run (#[], #[]))
    pure perm
  copyLinearIndices := fun values => .ok (arrayIndexRange 1 values.size).toArray
  vectorize := id
  permutationOrder := arrayPermutationOrder
  sortIndices := fun indices algorithm order scratch _ =>
    sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
      indices algorithm order () none order scratch

def arraySortpermTopOps {α : Type} [Inhabited α] (pivot : Int → Int → Int)
    (integerView : Array α → SortResult (Array Int)) (hasIntegerElements : Array α → Bool)
    (isForward : (α → α → SortResult Bool) → Bool := fun _ => false) :
    SortpermTopOps (Array α) (Algorithm (BracketSortTarget Int) Int)
      (α → α → SortResult Bool) Unit (α → α → SortResult Bool)
      (Option (Array Int)) Unit (Array Int) SortException where
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  sortperm := fun values algorithm order scratch dims =>
    sortpermCore (arraySortpermCoreOps pivot integerView hasIntegerElements isForward)
      values algorithm order scratch dims

def arraySortpermBangOps {α : Type} [Inhabited α] (pivot : Int → Int → Int) :
    SortpermBangOps (Array Int) (Array α) (Array α)
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool)
      Unit (α → α → SortResult Bool) (Int → Int → SortResult Bool) (Option (Array Int))
      (Option Int) Nat SortException where
  isVector := fun _ => true
  hasDims := Option.isSome
  axesIndex := Array.size
  axesArray := Array.size
  axesEqual := fun a b => decide (a = b)
  dimensionError := fun _ => .jl (.argumentError "Dims argument incorrect for vector")
  axesError := fun _ _ => .jl (.argumentError "index array must have the same axes")
  initializeLinearIndices := fun _ values => .ok (arrayIndexRange 1 values.size).toArray
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  vectorize := id
  permutationOrder := arrayPermutationOrder
  sortBang := fun indices algorithm order scratch _ =>
    sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
      indices algorithm order () none order scratch
def optionIntegerLess (reverse : Bool) (left right : Option Int) : Bool :=
  let forward := match left, right with
    | some a, some b => decide (a < b)
    | some _, none => true
    | none, _ => false
  let backward := match right, left with
    | some a, some b => decide (a < b)
    | some _, none => true
    | none, _ => false
  if reverse then backward else forward


def partitionMissingArray {α : Type} (values : Array (Option α)) (reverse : Bool) (lo hi : Int) :
    SortResult (Array (Option α) × Int × Int) := do
  let window : ArrayWindow := ⟨1, 1, values.size⟩
  if reverse then
    let ((first, last), result) ←
      (sendToEndReverseOrdering (storageSendToEndOps arrayStorage) (fun x => pure x.isNone)
        window false lo hi).run values
    pure (result, first, last)
  else
    let ((first, last), result) ←
      (sendToEndForwardOrdering (storageSendToEndOps arrayStorage) (fun x => pure x.isNone)
        window false lo hi).run values
    pure (result, first, last)

def arrayMissingDirectOpsWithNext {Alg : Type}
    (nextAlgorithm : Alg → Alg)
    (sortWrapped : WithoutMissingVector Int (Array (Option Int)) → Alg → Bool →
      (Int × Int) → SortResult (Array (Option Int)))
    (sortVector : Array (Option Int) → Alg → Bool →
      (Int × Int) → SortResult (Array (Option Int))) :
    MissingSortOps (Array (Option Int)) (Array (Option Int))
      (WithoutMissingVector Int (Array (Option Int)))
      (WithoutMissingVector Int (Array (Option Int)))
      Int Int Int Int Int Int Int Int (Option Int)
      Alg (Int × Int) (Int × Int) (Int × Int) (Array (Option Int)) SortException (List Int)
      Bool Empty Bool where
  range := fun _ _ bounds => .ok (bounds, bounds.1, bounds.2)
  elementType := fun _ => Option Int
  dataElementType := fun _ => Option Int
  hasMissingSupertype := fun _ => true
  nonMissingType := fun _ => Int
  sameType := fun _ _ => false
  isIntegerType := fun _ => false
  isDirectOrdering := fun _ => true
  permutationDetails := fun _ => none
  isDirectPermutationOrder := Empty.elim
  isReversePermutationOrder := Empty.elim
  allIdentityIndices := fun values data =>
    .ok (values.toList == (arrayIndexRange 1 data.size).map some)
  sendMissingToEnd := partitionMissingArray
  wrapVectorWithoutMissing := fun values =>
    match withoutMissingVector (E := Empty) (fun data => .ok (data.any Option.isNone)) values true with
    | .ok w => .ok w
    | .error (.julia e) => .error (.jl e)
    | .error (.callee e) => nomatch e
    | .error (.typeError msg) => .error (.typeError msg)
    | .error (.assertionError msg) => .error (.assertionError msg)
  wrapDataWithoutMissing := fun values =>
    match withoutMissingVector (E := Empty) (fun data => .ok (data.any Option.isNone)) values true with
    | .ok w => .ok w
    | .error (.julia e) => .error (.jl e)
    | .error (.callee e) => nomatch e
    | .error (.typeError msg) => .error (.typeError msg)
    | .error (.assertionError msg) => .error (.assertionError msg)
  indexRange := arrayIndexRange
  eachDataIndex := fun values => .ok (arrayIndexRange 1 values.size)
  dataIndexAt := fun indices index => liftSortJl (arrayRead indices.toArray index)
  readData := fun values index => liftSortJl (arrayRead values index)
  isMissing := fun x => .ok (Option.isNone x)
  writeLowIndex := fun values index value => liftSortJl (arrayWrite values index.unwrap (some value))
  writeHighIndex := fun values index value => liftSortJl (arrayWrite values index.unwrap (some value))
  incrementLow := ⟨(· + 1), (· + 1)⟩
  decrementHigh := ⟨(· - 1), (· - 1)⟩
  reverse := fun v lo hi => storageReverse arrayStorage v lo.unwrap hi
  permutationOrder := fun impossible _ => Empty.elim impossible
  nextAlgorithm := nextAlgorithm
  appendDirectBounds := fun _ lo hi => (lo, hi)
  appendPermutationBounds := fun _ lo hi => (lo.unwrap, hi.unwrap)
  sortWrapped := sortWrapped
  sortVector := sortVector
  sortPermutation := sortVector

def arrayMissingPermutationOpsWithNext {Alg : Type} (data : Array (Option Int))
    (nextAlgorithm : Alg → Alg)
    (sortWrapped : WithoutMissingVector Int (Array (Option Int)) → Alg → Bool →
      (Int × Int) → SortResult (Array Int))
    (sortVector : Array Int → Alg → Bool → (Int × Int) → SortResult (Array Int)) :
    MissingSortOps (Array Int) (Array (Option Int))
      (WithoutMissingVector Int (Array (Option Int)))
      (WithoutMissingVector Int (Array (Option Int)))
      Int Int Int Int Int Int Int Int (Option Int)
      Alg (Int × Int) (Int × Int) (Int × Int) (Array Int) SortException (List Int)
      Bool Bool Bool where
  range := fun _ _ bounds => .ok (bounds, bounds.1, bounds.2)
  elementType := fun _ => Int
  dataElementType := fun _ => Option Int
  hasMissingSupertype := fun _ => true
  nonMissingType := fun _ => Int
  sameType := fun _ _ => false
  isIntegerType := fun _ => true
  isDirectOrdering := fun _ => false
  permutationDetails := fun reverse => some (reverse, data)
  isDirectPermutationOrder := fun _ => true
  isReversePermutationOrder := id
  allIdentityIndices := fun values source => .ok (values.toList == arrayIndexRange 1 source.size)
  sendMissingToEnd := fun values reverse lo hi => do
    let window : ArrayWindow := ⟨1, 1, values.size⟩
    let ((first, last), result) ←
      (sendToEndForwardOrdering (storageSendToEndOps arrayStorage) (fun (_ : Int) => pure false)
        window reverse lo hi).run values
    pure (result, first, last)
  wrapVectorWithoutMissing := fun values =>
    match withoutMissingVector (E := Empty) (fun source => .ok (source.any Option.isNone))
        (values.map some) true with
    | .ok w => .ok w
    | .error (.julia e) => .error (.jl e)
    | .error (.callee e) => nomatch e
    | .error (.typeError msg) => .error (.typeError msg)
    | .error (.assertionError msg) => .error (.assertionError msg)
  wrapDataWithoutMissing := fun values =>
    match withoutMissingVector (E := Empty) (fun source => .ok (source.any Option.isNone))
        values true with
    | .ok w => .ok w
    | .error (.julia e) => .error (.jl e)
    | .error (.callee e) => nomatch e
    | .error (.typeError msg) => .error (.typeError msg)
    | .error (.assertionError msg) => .error (.assertionError msg)
  indexRange := arrayIndexRange
  eachDataIndex := fun values => .ok (arrayIndexRange 1 values.size)
  dataIndexAt := fun indices index => liftSortJl (arrayRead indices.toArray index)
  readData := fun values index => liftSortJl (arrayRead values index)
  isMissing := fun x => .ok (Option.isNone x)
  writeLowIndex := fun values index value => liftSortJl (arrayWrite values index.unwrap value)
  writeHighIndex := fun values index value => liftSortJl (arrayWrite values index.unwrap value)
  incrementLow := ⟨(· + 1), (· + 1)⟩
  decrementHigh := ⟨(· - 1), (· - 1)⟩
  reverse := fun v lo hi => storageReverse arrayStorage v lo.unwrap hi
  permutationOrder := fun reverse _ => reverse
  nextAlgorithm := nextAlgorithm
  appendDirectBounds := fun _ lo hi => (lo, hi)
  appendPermutationBounds := fun _ lo hi => (lo.unwrap, hi.unwrap)
  sortWrapped := sortWrapped
  sortVector := sortVector
  sortPermutation := sortVector

structure IEEECodec (α : Type) where
  encode : α → Nat
  decode : Nat → Jl α
  isNaN : α → Bool
  signbit : α → Bool
  less : α → α → SortResult Bool
  isIEEEFloat : Type → Bool
  isConcrete : Type → Bool

def partitionArrayOrdered {α : Type} (predicate : α → Bool) (values : Array α)
    (reverse endStable : Bool) (lo hi : Int) : SortResult (Array α × Int × Int) := do
  let window : ArrayWindow := ⟨1, 1, values.size⟩
  if reverse then
    let ((first, last), result) ←
      (sendToEndReverseOrdering (storageSendToEndOps arrayStorage) (fun x => pure (predicate x))
        window endStable lo hi).run values
    pure (result, first, last)
  else
    let ((first, last), result) ←
      (sendToEndForwardOrdering (storageSendToEndOps arrayStorage) (fun x => pure (predicate x))
        window endStable lo hi).run values
    pure (result, first, last)

def arrayIEEEDirectOps {α : Type} (codec : IEEECodec α) :
    IEEEFloatSortOps (Array α) (Array α) (Array Nat) Int Unit Bool Empty Bool
      (ArraySortKeywords Nat) (Array Nat) SortException where
  range := fun kw => .ok (kw.lo, kw.hi)
  elementType := fun _ => α
  dataElementType := fun _ => α
  isConcreteIEEEFloat := isConcreteIEEEFloat codec.isIEEEFloat codec.isConcrete
  isDirectOrdering := fun _ => true
  isIntegerVector := fun _ => false
  permutationDetails := fun _ => none
  isDirectPermutationOrder := Empty.elim
  reverseOrdering := fun _ => true
  forwardOrdering := fun _ => false
  sendNaNs := fun values reverse lo hi =>
    partitionArrayOrdered codec.isNaN values reverse true lo hi
  sendAfterZero := fun values reverse lo hi => do
    let predicate := if reverse then afterZeroReverse codec.signbit
      else afterZeroForward codec.signbit
    let (last, result) ←
      (sendToEndBang (storageSendToEndOps arrayStorage) (fun x => pure (predicate x))
        ⟨1, 1, values.size⟩
        (some lo) (some hi)).run values
    pure (result, last)
  reinterpretVector := fun values => .ok (values.map codec.encode)
  syncUnsignedAlias := fun values _ => .ok (values.map codec.encode)
  restoreVectorAlias := fun _ bits => liftSortJl (bits.mapM codec.decode)
  nextIndex := fun index => index + 1
  sortUnsigned := fun values _ reverse kw => do
    let compare := fun a b : Nat => pure (if reverse then decide (b < a) else decide (a < b))
    let sorted ← storageInsertion arrayStorage compare values kw.lo kw.hi
    pure (sorted, kw.scratch)
  sendPermutationNaNs := fun _ _ impossible => Empty.elim impossible
  reinterpretData := fun values => .ok (values.map codec.encode)
  sendPermutationAfterZero := fun _ _ impossible => Empty.elim impossible
  reversePermutationOrder := Empty.elim
  forwardPermutationOrder := Empty.elim
  makePermutationOrder := fun impossible _ => Empty.elim impossible
  sortPermutation := fun values _ reverse kw => do
    let compare := if reverse then fun a b => codec.less b a else codec.less
    let sorted ← storageInsertion arrayStorage compare values kw.lo kw.hi
    pure (sorted, kw.scratch)
  nextAlgorithm := id
  keywordsWithBounds := fun kw lo hi => { kw with lo, hi }
  keywordsWithBoundsAndScratch := fun kw lo hi scratch => { kw with lo, hi, scratch }
  sortFallback := fun values _ reverse kw => do
    let compare := if reverse then fun a b => codec.less b a else codec.less
    let sorted ← storageInsertion arrayStorage compare values kw.lo kw.hi
    pure (sorted, kw.scratch)

structure ExtremaKeywords (t : IntTy) where
  lo : Int
  hi : Int
  minimum : Option (JInt t) := none
  maximum : Option (JInt t) := none

def arrayExtremaCountingOps (t : IntTy) (initial : Array (JInt t)) :
    ComputeExtremaOps (Array (JInt t)) Unit Int Int Int Int (JInt t) (ExtremaKeywords t)
      (Array (JInt t)) SortException Bool where
  rangeAndScratch := fun _ _ kw => .ok (kw, kw.lo, kw.hi, initial)
  nextIndex := fun index => index + 1
  range := arrayIndexRange
  readFirst := fun values index => liftSortJl (arrayRead values index)
  read := fun values index => liftSortJl (arrayRead values index)
  less := fun reverse a b => .ok (if reverse then decide (b.val < a.val) else decide (a.val < b.val))
  appendExtrema := fun kw minimum maximum => { kw with minimum := some minimum, maximum := some maximum }
  nextAlgorithm := id
  sort := fun values _ reverse kw => do
    match kw.minimum, kw.maximum with
    | some minimum, some maximum =>
      let (result, _) ← sortCounting (arrayCountingOps t) values reverse
        { lo := kw.lo, hi := kw.hi, minimum, maximum }
      pure result
    | _, _ => .error (.jl (.argumentError "extrema have not been computed"))

def mapUnsigned {t : IntTy} (x : JInt t) : JInt t := uintMapUnsigned x

def mapSigned {t : IntTy} (x : JInt t) : JInt t.toUnsigned :=
  uintMapSigned int.bxor (fun _ => int.typemin t) int.unsigned x

def unmapSigned {u : IntTy} (x : JInt u) : JInt u.toSigned :=
  uintUnmapSigned (JInt u.toSigned) int.signed int.bxor (int.typemin u.toSigned) x

def forwardIntegerCode : (t : IntTy) → JInt t → JInt t.toUnsigned
  | .i8, x => mapSigned x
  | .i16, x => mapSigned x
  | .i32, x => mapSigned x
  | .i64, x => mapSigned x
  | .i128, x => mapSigned x
  | .u8, x => mapUnsigned x
  | .u16, x => mapUnsigned x
  | .u32, x => mapUnsigned x
  | .u64, x => mapUnsigned x
  | .u128, x => mapUnsigned x

def forwardIntegerDecode : (t : IntTy) → JInt t.toUnsigned → JInt t
  | .i8, x => unmapSigned x
  | .i16, x => unmapSigned x
  | .i32, x => unmapSigned x
  | .i64, x => unmapSigned x
  | .i128, x => unmapSigned x
  | .u8, x => uintUnmapUnsigned (JInt .u8) x
  | .u16, x => uintUnmapUnsigned (JInt .u16) x
  | .u32, x => uintUnmapUnsigned (JInt .u32) x
  | .u64, x => uintUnmapUnsigned (JInt .u64) x
  | .u128, x => uintUnmapUnsigned (JInt .u128) x

def integerReverseMappingOps (t : IntTy) :
    ReverseUIntMappingOps (JInt t) (JInt t.toUnsigned) Unit Unit where
  bitwiseNot := int.bnot
  forwardOrdering := id
  mapForward := fun x _ => forwardIntegerCode t x
  unmapForward := fun _ x _ => forwardIntegerDecode t x
  mappableForward := fun T _ => uintMappableBitInteger (fun _ => JInt t.toUnsigned) T

def integerCode (t : IntTy) (reverse : Bool) (x : JInt t) : JInt t.toUnsigned :=
  if reverse then uintMapReverse (integerReverseMappingOps t) x ()
  else forwardIntegerCode t x

def integerDecode (t : IntTy) (reverse : Bool) (x : JInt t.toUnsigned) : JInt t :=
  if reverse then uintUnmapReverse (integerReverseMappingOps t) (JInt t) x ()
  else forwardIntegerDecode t x

def arrayIntegerMapOps (t : IntTy) :
    UIntMapVectorOps (Array (JInt t)) (Array Nat) Nat Int (JInt t) Bool SortException where
  elementType := fun _ => JInt t
  uintMappable := fun valueType reverse =>
    if reverse then uintMappableReverse (integerReverseMappingOps t) valueType ()
    else uintMappableBitInteger (fun _ => JInt (unsignedIntegerType t)) valueType
  reinterpret := fun unsignedType values =>
    match unsignedType with
    | none => .error (.jl (.argumentError "element type has no unsigned mapping"))
    | some _ => .ok (values.map fun value => (value.val % (2 ^ t.bits)).toNat)
  range := arrayIndexRange
  read := fun values index => liftSortJl (arrayRead values index)
  uintMap := fun value reverse => .ok (integerCode t reverse value).val.toNat
  writeUnsigned := fun values index value => liftSortJl (arrayWrite values index value)

def arrayIntegerUnmapOps (t : IntTy) :
    UIntUnmapVectorOps (Array (JInt t)) (Array Nat) Nat Int (JInt t) Bool SortException where
  range := arrayIndexRange
  addIndex := Int.add
  readUnsigned := fun values index => liftSortJl (arrayRead values index)
  zeroUnsigned := 0
  zeroIndex := 0
  addUnsigned := fun a b => (a + b) % 2 ^ t.bits
  elementType := fun _ => JInt t
  uintUnmap := fun _ code reverse => .ok (integerDecode t reverse (int.lit t.toUnsigned (Int.ofNat code)))
  write := fun values index value => liftSortJl (arrayWrite values index value)

def unsignedArrayScratchOps : ScratchOps (Array Nat) (Array Nat) SortException :=
  arrayScratchOps.mapError .jl

structure RadixKeywords (t : IntTy) where
  lo : Int
  hi : Int
  minimum : JInt t
  maximum : JInt t
  scratch : Option (Array Nat) := none

def arrayRadixWrapperOps (t : IntTy)
    (heuristic : Int → Int → JInt .u64 → Jl UInt8) :
    RadixSortWrapperOps (Array (JInt t)) (JInt t) (Array Nat) Nat Int (Array Int)
      (Array Nat) Bool (RadixKeywords t) SortException (Array (JInt t) × Array Nat) where
  rangeAndExtrema := fun kw => .ok (kw.lo, kw.hi, kw.minimum, kw.maximum, kw.scratch)
  uintMapOps := arrayIntegerMapOps t
  subtractUnsigned := fun a b => (a + 2 ^ t.bits - b) % 2 ^ t.bits
  topSetBit := fun code => int.lit .u64 (if code = 0 then 0 else Nat.log2 code + 1)
  range := arrayIndexRange
  windowLength := fun lo hi => (hi - lo + 1).toNat
  oneMinus := fun index => 1 - index
  readUnsigned := fun values index => liftSortJl (arrayRead values index)
  writeUnsigned := fun values index value => liftSortJl (arrayWrite values index value)
  radixOps := arrayRadixOps heuristic
  runRadixSort := fun ops v lo hi bits s off => runArrayRadixSort ops v lo hi bits s off none
  makeScratch := fun existing _ length =>
    match existing with
    | none => makeScratchNothing unsignedArrayScratchOps length
    | some backing => makeScratchSame unsignedArrayScratchOps backing length
  reinterpretScratch := fun unsignedType backing =>
    match unsignedType with
    | none => .error (.jl (.argumentError "element type has no unsigned mapping"))
    | some _ => .ok backing
  unmapOps := arrayIntegerUnmapOps t
  finish := fun values scratch => (values, scratch)

structure CharacterCode where
  bits : BitVec 32
  deriving Repr, DecidableEq

def arrayChunkLoopOps {α : Type} [Inhabited α] (pivot : Int → Int → Int) :
    SortChunksLoopOps (Array α) Int Nat
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool) (Array α) SortException where
  starts := fun first step last =>
    if step = 0 then .error (.jl (.argumentError "step cannot be zero"))
    else if last < first then .ok []
    else .ok ((List.range ((last - first) / Int.ofNat step + 1).toNat).map
      fun i => first + Int.ofNat (i * step))
  chunkEnd := fun lo n => lo + Int.ofNat n - 1
  nextChunk := fun lo n => lo + Int.ofNat n
  sortWithoutScratch := fun values algorithm order lo hi =>
    sourceSortWindow arrayStorage defaultBracketNumerics pivot values algorithm order
      { lo, hi, scratch := none }
  sortWithScratch := fun values algorithm order lo hi scratch =>
    sourceSortBang arrayStorage defaultBracketNumerics pivot values algorithm order
      { lo, hi, scratch := some scratch }

def arrayChunkDispatchOps {α : Type} [Inhabited α] (pivot : Int → Int → Int) :
    SortChunksDispatchOps (Array α) Int Nat
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool)
      (Option (Array α)) SortException where
  linearBounds := fun values => .ok (1, Int.ofNat values.size)
  sortChunksBounded := fun values n algorithm order scratch first last =>
    match scratch with
    | none => sortChunksNoScratch (arrayChunkLoopOps pivot)
      values n algorithm order first last
    | some scratch => sortChunksWithScratch (arrayChunkLoopOps pivot)
      values n algorithm order scratch first last

structure DimensionArrayLayout (A α Axes : Type) where
  ndims : A → Nat
  axisLength : A → Nat → Nat
  permute : A → List Nat → Jl A
  vectorize : A → Jl (Array α)
  copyLinear : A → Jl (Array α)
  inversePermutation : List Nat → List Nat
  restorePermuted : A → Array α → List Nat → Jl A
  reshapeOriginalAxes : A → Array α → Jl A
  axes : A → Axes
  slices : A → Nat → List (List α)

def dimensionArrayOps {A α Axes : Type} [Inhabited α]
    (layout : DimensionArrayLayout A α Axes) (pivot : Int → Int → Int) :
    MultidimensionalSortOps A (Array α)
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool) Unit
      (α → α → SortResult Bool) (Option (Array α)) SortException where
  dimensionLength := layout.axisLength
  dimensions := fun array => (List.range (layout.ndims array)).map Nat.succ
  dimensionOne := 1
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  permuteDimensions := fun array dimensions => liftSortJl (layout.permute array dimensions)
  vectorize := fun array => liftSortJl (layout.vectorize array)
  applyInitialOptimizations := sourceApplyInitialOptimizations
  sortChunks := fun values n algorithm order scratch =>
    sortChunksDispatch (arrayChunkDispatchOps pivot) values n algorithm order scratch
  inversePermutation := layout.inversePermutation
  restorePermuted := fun array values permutation => liftSortJl (layout.restorePermuted array values permutation)
  copyLinear := fun array => liftSortJl (layout.copyLinear array)
  reshapeOriginalAxes := fun array values => liftSortJl (layout.reshapeOriginalAxes array values)
structure SliceArrayLayout (A α Axes Index K : Type) where
  ndims : A → Nat
  axisLength : A → Nat → Nat
  cartesianIndices : A → Nat → Jl (List Index)
  coordinate : Index → Nat → K
  view : A → List (Option K) → Jl (Array α)
  writeView : A → List (Option K) → Array α → Jl A
  axes : A → Axes
  slices : A → Nat → List (List α)

def sliceSelectors {A α Axes Index K : Type} (layout : SliceArrayLayout A α Axes Index K)
    (array : A) (dimension : Nat) (index : Index) : List (Option K) :=
  (List.range (layout.ndims array)).map fun offset =>
    if offset + 1 = getValue dimension then none
    else some (layout.coordinate index (offset + 1))

def sliceArrayOps {A α Axes Index K : Type} [Inhabited α]
    (layout : SliceArrayLayout A α Axes Index K) (pivot : Int → Int → Int) :
    SortBangDimensionsOps A (Array α) Nat Index
      (Algorithm (BracketSortTarget Int) Int) (α → α → SortResult Bool) Unit
      (α → α → SortResult Bool) (Option (Array α)) SortException where
  dimensionCount := layout.ndims
  dimensionError := .jl (.argumentError "dimension out of range")
  applyInitialOptimizations := sourceApplyInitialOptimizations
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  dimensionValues := fun count => (List.range count).map Nat.succ
  dimensionValue := getValue
  cartesianIndices := fun array dimension => liftSortJl (layout.cartesianIndices array dimension)
  size := layout.axisLength
  getView := fun array dimension index =>
    liftSortJl (getView layout.view getValue layout.ndims layout.coordinate array dimension index)
  setView := fun array dimension index values =>
    liftSortJl (layout.writeView array (sliceSelectors layout array dimension index) values)
  sortBang := fun values algorithm order scratch =>
    sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
      values algorithm order () none order scratch
  defaultScratch := fun array dimension =>
    if dimension < 1 then .error (.jl .boundsError)
    else
      let len := if dimension ≤ Int.ofNat (layout.ndims array) then
        layout.axisLength array dimension.toNat
      else 1
      if len < 10 then .ok none else .ok (some (Array.replicate len default))
  firstIndex := fun indices =>
    match indices with
    | [] => .error (.jl .boundsError)
    | first :: _ => .ok first
  similar := fun values => .ok (Array.replicate values.size default)
  copyInto := fun temporary values =>
    if temporary.size = values.size then .ok values
    else .error (.jl (.argumentError "length mismatch"))
  copyFrom := fun array dimension index values =>
    liftSortJl (layout.writeView array (sliceSelectors layout array dimension index) values)
structure FlatSortParent (α : Type) where
  storage : Array α
  dimensions : Nat

structure FlatSortView (α : Type) where
  parent : FlatSortParent α
  offset : Int
  length : Nat

def flatSortViewValues {α : Type} (view : FlatSortView α) : Jl (Array α) := do
  let values ← (arrayIndexRange 1 view.length).mapM
    fun index => arrayRead view.parent.storage (view.offset + index)
  pure values.toArray

def partitionPermutationOrdered {α : Type} (predicate : α → Bool)
    (data : Array α) (indices : Array Int) (reverse endStable : Bool) (lo hi : Int) :
    SortResult (Array Int × Int × Int) := do
  let window : ArrayWindow := ⟨1, 1, indices.size⟩
  let test : Int → StateT (Array Int) (Except SortException) Bool := fun index state => do
    let value ← liftM (liftSortJl (arrayRead data index))
    pure (predicate value, state)
  if reverse then
    let ((first, last), result) ←
      (sendToEndReverseOrdering (storageSendToEndOps arrayStorage) test window endStable lo hi).run
        indices
    pure (result, first, last)
  else
    let ((first, last), result) ←
      (sendToEndForwardOrdering (storageSendToEndOps arrayStorage) test window endStable lo hi).run
        indices
    pure (result, first, last)

def arrayIEEEPermutationOps {α : Type} [Inhabited α] (codec : IEEECodec α) :
    IEEEFloatSortOps (Array Int) (Array α) (Array Nat) Int Unit (Bool × Array α)
      Bool (Bool × Array Nat) (ArraySortKeywords Nat) (Array Nat) SortException where
  range := fun kw => .ok (kw.lo, kw.hi)
  elementType := fun _ => Int
  dataElementType := fun _ => α
  isConcreteIEEEFloat := isConcreteIEEEFloat codec.isIEEEFloat codec.isConcrete
  isDirectOrdering := fun _ => false
  isIntegerVector := fun _ => true
  permutationDetails := fun order => some order
  isDirectPermutationOrder := fun _ => true
  reverseOrdering := fun order => (true, order.2)
  forwardOrdering := fun order => (false, order.2)
  sendNaNs := fun values order lo hi =>
    partitionPermutationOrdered codec.isNaN order.2 values order.1 true lo hi
  sendAfterZero := fun values order lo hi => do
    let predicate := if order.1 then afterZeroReverse codec.signbit
      else afterZeroForward codec.signbit
    let (result, _, last) ←
      partitionPermutationOrdered predicate order.2 values false false lo hi
    pure (result, last)
  reinterpretVector := fun values =>
    .ok (values.map fun value => (JInt.wrap .u64 value).val.toNat)
  syncUnsignedAlias := fun values _ =>
    .ok (values.map fun value => (JInt.wrap .u64 value).val.toNat)
  restoreVectorAlias := fun _ values =>
    .ok (values.map fun value => (JInt.wrap .i64 (Int.ofNat value)).val)
  nextIndex := fun index => index + 1
  sortUnsigned := fun values _ order kw => do
    let compare := fun a b : Nat => pure (if order.1 then decide (b < a) else decide (a < b))
    let result ← storageInsertion arrayStorage compare values kw.lo kw.hi
    pure (result, kw.scratch)
  sendPermutationNaNs := fun values data reverse lo hi =>
    partitionPermutationOrdered codec.isNaN data values reverse true lo hi
  reinterpretData := fun values => .ok (values.map codec.encode)
  sendPermutationAfterZero := fun values data reverse lo hi => do
    let predicate := if reverse then afterZeroReverse codec.signbit
      else afterZeroForward codec.signbit
    let (result, _, last) ←
      partitionPermutationOrdered predicate data values false false lo hi
    pure (result, last)
  reversePermutationOrder := fun _ => true
  forwardPermutationOrder := fun _ => false
  makePermutationOrder := fun reverse data => (reverse, data)
  sortPermutation := fun values _ order kw => do
    let compare := fun a b : Nat => pure (if order.1 then decide (b < a) else decide (a < b))
    let result ← storageInsertion arrayStorage (arrayPermutationOrder compare order.2) values
      kw.lo kw.hi
    pure (result, kw.scratch)
  nextAlgorithm := id
  keywordsWithBounds := fun kw lo hi => { kw with lo, hi }
  keywordsWithBoundsAndScratch := fun kw lo hi scratch => { kw with lo, hi, scratch }
  sortFallback := fun values _ order kw => do
    let compare := if order.1 then fun a b => codec.less b a else codec.less
    let result ← storageInsertion arrayStorage (arrayPermutationOrder compare order.2) values
      kw.lo kw.hi
    pure (result, kw.scratch)

/-- `base/hashing.jl:40,75-76`: installed one-argument Int64 hashing. -/
def juliaHashInt (x : Int) : Nat :=
  (hashing.hashInt64 (int.lit .i64 x) hashing.hashSeed).val.toNat

/-- `base/sort.jl:1092`: deterministic hash pivot on a nonempty Int64 window.
The subtraction is UInt64 even when the lower bound is negative. -/
def juliaPivot (lo hi : Int) : Int :=
  let difference := int.lit .u64 (Int.ofNat (juliaHashInt lo) - lo)
  lo + (difference.val.toNat % (hi - lo + 1).toNat : Nat)

def rangeLt {t : IntTy} (rev : Bool) (a b : JInt t) : Bool :=
  if rev then decide (b.val < a.val) else decide (a.val < b.val)

def addOneInt {t : IntTy} (y : JInt t) : Int :=
  wrapInt (IntTy.promote t .i64) (y.val + 1)

def toKeytype (y : Int) : Jl JInt64 := JInt.convert (IntTy.i64.name) .i64 y

def rangeElem {t : IntTy} (f h : JInt t) (i : Int) : Int := f.val + (i - 1) * h.val

def bitIntegerRangeOps (t : IntTy) :
    IntegerRangeOps (JInt t × JInt t × JInt t × JInt64) (JInt t) (JInt t) Int JInt64 Bool JlError where
  requireOneBased := fun _ => .ok ()
  first := fun (f, _, _, _) => f
  step := fun (_, h, _, _) => h
  last := fun (_, _, l, _) => l
  length := fun (_, _, _, len) => len
  zeroIndex := JInt.lit .i64 0
  oneIndex := JInt.lit .i64 1
  increment := fun k => k + JInt.lit .i64 1
  isZero := fun h => decide (h.val = 0)
  floorInteger := fun x => .ok x
  ceilInteger := fun x => .ok x
  subtract := fun a b => a - b
  fld := JInt.fld
  cld := JInt.cld
  addOne := addOneInt
  toKey := toKeytype
  get := fun (f, h, _, len) i =>
    if 1 ≤ i.val ∧ i.val ≤ len.val then
      JInt.convert (t.name) t (rangeElem f h i.val)
    else .error .boundsError
  values := fun (f, h, _, len) =>
    (List.range len.val.toNat).map fun k => JInt.wrap t (f.val + Int.ofNat k * h.val)
  indexAsInt := fun k => k.val
  safeDifference := fun (f, _, _, _) x =>
    t.min + (if t.signed then 1 else 0) ≤ x.val - f.val ∧ x.val - f.val ≤ t.max
  isReverse := id


structure RealRangeQuery where
  floor : Int
  ceil : Int
  deriving DecidableEq, Repr

def realQueryLtRange {t : IntTy} (rev : Bool) (a : JInt t) (x : RealRangeQuery) : Bool :=
  if rev then decide (x.floor < a.val) else decide (a.val < x.ceil)

def realQueryLt {t : IntTy} (rev : Bool) (x : RealRangeQuery) (a : JInt t) : Bool :=
  if rev then decide (a.val < x.ceil) else decide (x.floor < a.val)

def bitIntegerRealRangeOps (t : IntTy) :
    IntegerRangeOps (JInt t × JInt t × JInt t × JInt64) (JInt t) RealRangeQuery Int JInt64 Bool JlError where
  requireOneBased := fun _ => .ok ()
  first := fun (f, _, _, _) => f
  step := fun (_, h, _, _) => h
  last := fun (_, _, l, _) => l
  length := fun (_, _, _, len) => len
  zeroIndex := JInt.lit .i64 0
  oneIndex := JInt.lit .i64 1
  increment := fun k => k + JInt.lit .i64 1
  isZero := fun h => decide (h.val = 0)
  floorInteger := fun x => JInt.convert (t.name) t x.floor
  ceilInteger := fun x => JInt.convert (t.name) t x.ceil
  subtract := fun a b => a - b
  fld := JInt.fld
  cld := JInt.cld
  addOne := addOneInt
  toKey := toKeytype
  get := fun (f, h, _, len) i =>
    if 1 ≤ i.val ∧ i.val ≤ len.val then
      JInt.convert (t.name) t (rangeElem f h i.val)
    else .error .boundsError
  values := fun (f, h, _, len) =>
    (List.range len.val.toNat).map fun k => JInt.wrap t (f.val + Int.ofNat k * h.val)
  indexAsInt := fun k => k.val
  safeDifference := fun (f, _, _, _) x =>
    t.min ≤ x.floor ∧ x.ceil ≤ t.max ∧
    t.min + (if t.signed then 1 else 0) ≤ x.floor - f.val ∧
    t.min + (if t.signed then 1 else 0) ≤ x.ceil - f.val ∧
    x.floor - f.val ≤ t.max ∧ x.ceil - f.val ≤ t.max
  isReverse := id

def arrayIEEEDirectOpsWithNext {α Alg : Type} (codec : IEEECodec α)
    (nextAlgorithm : Alg → Alg)
    (sortUnsigned : Array Nat → Alg → Bool → ArraySortKeywords Nat →
      SortResult (Array Nat × Option (Array Nat)))
    (sortFallback : Array α → Alg → Bool → ArraySortKeywords Nat →
      SortResult (Array α × Option (Array Nat))) :
    IEEEFloatSortOps (Array α) (Array α) (Array Nat) Int Alg Bool Empty Bool
      (ArraySortKeywords Nat) (Array Nat) SortException :=
  { arrayIEEEDirectOps codec with
    nextAlgorithm := nextAlgorithm
    sortUnsigned := sortUnsigned
    sortPermutation := sortFallback
    sortFallback := sortFallback }

def arrayIEEEPermutationOpsWithNext {α Alg : Type} [Inhabited α] (codec : IEEECodec α)
    (nextAlgorithm : Alg → Alg)
    (sortPermutation : Array Int → Alg → (Bool × Array Nat) → ArraySortKeywords Nat →
      SortResult (Array Int × Option (Array Nat)))
    (sortFallback : Array Int → Alg → (Bool × Array α) → ArraySortKeywords Nat →
      SortResult (Array Int × Option (Array Nat))) :
    IEEEFloatSortOps (Array Int) (Array α) (Array Nat) Int Alg (Bool × Array α)
      Bool (Bool × Array Nat) (ArraySortKeywords Nat) (Array Nat) SortException :=
  { arrayIEEEPermutationOps codec with
    nextAlgorithm := nextAlgorithm
    sortUnsigned := fun values _ order kw =>
      (arrayIEEEPermutationOps codec).sortUnsigned values () order kw
    sortPermutation := sortPermutation
    sortFallback := sortFallback }

def flatSubArraySortOpsWithNext {α Alg : Type} [Inhabited α]
    (original : FlatSortView α)
    (nextAlgorithm : Alg → Alg)
    (sortSlice : Array α → Alg → (α → α → SortResult Bool) → ArraySortKeywords α →
      SortResult (Array α × Option (Array α))) :
    SubArraySortOps (FlatSortView α) (FlatSortParent α) (Array α) Int Alg
      (α → α → SortResult Bool) (ArraySortKeywords α) (FlatSortView α) SortException where
  range := fun kw => .ok (kw.lo, kw.hi)
  parent := FlatSortView.parent
  parentIsArray := fun _ => true
  parentIsVector := fun parent => decide (parent.dimensions = 1)
  spanLessThan100 := fun lo hi => decide (hi - lo < 100)
  offsetIsZero := fun view => decide (view.offset = 0)
  vectorizeParent := fun parent => .ok parent.storage
  nextAlgorithm := nextAlgorithm
  sortView := fun view alg order kw => do
    let values ← liftSortJl (flatSortViewValues view)
    let (sorted, _) ← sortSlice values alg order kw
    let mut parent := view.parent.storage
    for index in arrayIndexRange kw.lo kw.hi do
      let value ← liftSortJl (arrayRead sorted index)
      parent ← liftSortJl (arrayWrite parent (view.offset + index) value)
    pure { view with parent := { view.parent with storage := parent } }
  sortParent := fun values alg order kw => do
    let (sorted, _) ← sortSlice values alg order kw
    pure { original with parent := { original.parent with storage := sorted } }

def isFullSortAlgorithm {Target Index : Type} : Algorithm Target Index → Bool
  | .insertion | .quick | .merge | .defaultStable | .defaultUnstable => true
  | .subArray next | .missing next | .boolOptimization next | .ieeeFloat next
  | .checkSorted next | .stableCheckSorted next =>
    isFullSortAlgorithm next
  | .small _ small big => isFullSortAlgorithm small && isFullSortAlgorithm big
  | .considerCounting _ next => isFullSortAlgorithm next
  | .isUIntMappable _ no => isFullSortAlgorithm no
  | .scratchQuickSort lo hi next => lo.isNone && hi.isNone && isFullSortAlgorithm next
  | .computeExtrema _ | .counting | .considerRadix _ _ | .radix
  | .bracketedSort _ _ | .partialQuickSort _ | .user _ => false


/-! ## Native Int32/Missing default dispatch and typed scratch storage -/

abbrev Int32Values := Array (Option (JInt .i32))
abbrev Int32WithoutMissing := WithoutMissingVector (JInt .i32) Int32Values

/-- The scratch vector retains its declared element type, including Union{Missing,Int32}.
`none` in an integer buffer is uninitialized storage, not a zero-valued element. -/
structure Int32Scratch where
  missingEltype : Bool
  data : Int32Values

/-- Native datatype metadata used by reinterpret (reinterpretarray.jl:73-103).
Union{Missing,Int32} has four-byte elements but is not an isbits type. -/
def int32ScratchLayout (missingEltype : Bool) : reinterpretarray.TypeLayout :=
  .mk ⟨if missingEltype then 2 else 1, 32, int.lit .i64 4,
    !missingEltype, !missingEltype, missingEltype, false, false⟩ [] []

def int32ScratchInput (s : Int32Scratch) : reinterpretarray.ArrayInput Int32Values :=
  ⟨s.data, 1, [int.lit .i64 s.data.size], [⟨int.lit .i64 1, int.lit .i64 s.data.size⟩]⟩

/-- reinterpretarray.jl:73-103, called by make_scratch(sort.jl:515).
Validation runs on the actual declared scratch element type before a view is returned. -/
def reinterpretInt32Scratch (s : Int32Scratch) : SortResult Int32Scratch := do
  match reinterpretarray.m73_reinterpret (T := JInt .i32) (S := Option (JInt .i32))
      (int32ScratchLayout false) (int32ScratchLayout s.missingEltype) (int32ScratchInput s) with
  | .error _ => .error (.jl (.argumentError "cannot reinterpret a non-bits scratch element type"))
  | .ok _ => pure { s with missingEltype := false }

/-- sort.jl:2295-2301,1040 and reinterpretarray.jl:73-103: validate the UInt32
view of Int32-typed storage before exposing its bit patterns. -/
def reinterpretInt32Unsigned (s : Int32Scratch) : SortResult (Array (Option Nat)) := do
  let target : reinterpretarray.TypeLayout :=
    .mk ⟨3, 32, int.lit .i64 4, true, true, false, false, false⟩ [] []
  match reinterpretarray.m73_reinterpret (T := JInt .u32) (S := Option (JInt .i32))
      target (int32ScratchLayout s.missingEltype) (int32ScratchInput s) with
  | .error _ => .error (.jl (.argumentError "cannot reinterpret a non-bits scratch element type"))
  | .ok _ => pure (s.data.map (Option.map fun x => (x.val % 2 ^ 32).toNat))


/-- Vector allocation/resize with the signed Int length checks (array.jl:193-199,1288-1293). -/
def resizeInt32Scratch (s : Int32Scratch) (length : JInt .i64) : SortResult Int32Scratch :=
  if length.val < 0 then .error (.jl (.argumentError "invalid Array size")) else
    .ok { s with data := if length.val.toNat ≤ s.data.size then s.data.extract 0 length.val.toNat
      else s.data ++ Array.replicate (length.val.toNat - s.data.size) none }

/-- sort.jl:503-516: Nothing allocates a Vector{Int32}; matching eltypes resize directly;
otherwise compute wrapped byte counts, resize the original scratch, then reinterpret it. -/
def makeInt32Scratch (existing : Option Int32Scratch) (length : JInt .i64) :
    SortResult (Int32Scratch × Int32Scratch) := do
  match existing with
  | none =>
    let s ← resizeInt32Scratch ⟨false, #[]⟩ length
    pure (s, s)
  | some s =>
    if !s.missingEltype then
      let s ← if length.val > s.data.size then resizeInt32Scratch s length else pure s
      pure (s, s)
    else
      let lenBytes := int.mul length (int.lit .i64 4)
      let lenScratch ← liftSortJl (JInt.div lenBytes (int.lit .i64 4))
      let s ← if lenScratch.val > s.data.size then resizeInt32Scratch s lenScratch else pure s
      let view ← reinterpretInt32Scratch s
      pure (s, view)

/-- sort.jl:598-602: WithoutMissingVector's getindex first asserts that the value is not Missing. -/
def int32NonmissingRead (v : Int32WithoutMissing) (index : Int) : SortResult (JInt .i32) :=
  withoutMissingGet (fun values index => liftSortJl (arrayRead values index))
    SortException.assertionError v index

def int32NonmissingWrite (v : Int32WithoutMissing) (index : Int) (value : JInt .i32) :
    SortResult Int32WithoutMissing :=
  withoutMissingSet (fun data value index => liftSortJl (arrayWrite data index (some value))) v value index

def int32ScratchRead (v : Int32Scratch) (index : Int) : SortResult (JInt .i32) := do
  let value ← liftSortJl (arrayRead v.data index)
  match value with
  | some value => pure value
  | none => .error (.native (.array .undefinedReference))

def int32ScratchWrite (v : Int32Scratch) (index : Int) (value : JInt .i32) :
    SortResult Int32Scratch := do
  let data ← liftSortJl (arrayWrite v.data index (some value))
  pure { v with data }


def int32DirectLess (reverse : Bool) (a b : JInt .i32) : SortResult Bool :=
  .ok (if reverse then decide (b.val < a.val) else decide (a.val < b.val))

/-- sort.jl: insertion-sort element accesses use WithoutMissingVector's type assertion. -/
def int32Insertion (reverse : Bool) (values : Int32WithoutMissing) (lo hi : Int) :
    SortResult Int32WithoutMissing := do
  let operations : VectorMutationOps (StateT Int32WithoutMissing (Except SortException))
      Unit (JInt .i32) Int := {
    get := fun _ index => fun v => do pure (← int32NonmissingRead v index, v)
    set := fun _ value index => fun v => do pure ((), ← int32NonmissingWrite v index value)
    indices := arrayIndices
    distance := fun lo hi => (hi - lo).toNat
    modelExhausted := fun {_} _ => .error (.errorException "fuel")
  }
  let (_, result) ← (insertionSort operations
    (fun (_ : Unit) a b => liftM (int32DirectLess reverse a b)) () () lo hi ()).run values
  pure result

/-- array.jl reverse!: exchange the symmetric elements of the active window. -/
def int32Reverse (values : Int32WithoutMissing) (lo hi : Int) : SortResult Int32WithoutMissing := do
  let mut values := values
  for offset in List.range ((hi - lo + 1).toNat / 2) do
    let left := lo + offset
    let right := hi - offset
    let a ← int32NonmissingRead values left
    let b ← int32NonmissingRead values right
    values ← int32NonmissingWrite values left b
    values ← int32NonmissingWrite values right a
  pure values

structure Int32SortKeywords where
  lo : Int
  hi : Int
  minimum : JInt .i32
  maximum : JInt .i32
  scratch : Option Int32Scratch

/-- The UInt32 reinterpret view retains missing/uninitialized slots outside the active window;
reading one raises an error, while writing replaces it with a defined UInt32 value. -/
def int32UnsignedRead (values : Array (Option Nat)) (index : Int) : SortResult Nat := do
  let value ← liftSortJl (arrayRead values index)
  match value with
  | some value => pure value
  | none => .error (.native (.array .undefinedReference))

def int32MapOps : UIntMapVectorOps Int32WithoutMissing (Array (Option Nat)) Nat Int
    (JInt .i32) Bool SortException where
  elementType := fun _ => JInt .i32
  uintMappable := (arrayIntegerMapOps .i32).uintMappable
  reinterpret := fun _ v => reinterpretInt32Unsigned ⟨false, v.data⟩
  range := arrayIndexRange
  read := int32NonmissingRead
  uintMap := fun value reverse => pure (integerCode .i32 reverse value).val.toNat
  writeUnsigned := fun values index value => liftSortJl (arrayWrite values index (some value))

def int32UnmapOps : UIntUnmapVectorOps Int32WithoutMissing (Array (Option Nat)) Nat Int
    (JInt .i32) Bool SortException where
  range := arrayIndexRange
  addIndex := Int.add
  readUnsigned := int32UnsignedRead
  zeroUnsigned := 0
  zeroIndex := 0
  addUnsigned := fun a b => (a + b) % 2 ^ 32
  elementType := fun _ => JInt .i32
  uintUnmap := fun _ value reverse => pure (integerDecode .i32 reverse (int.lit .u32 value))
  write := int32NonmissingWrite

/-- The source radix machine with undefined slots retained in its memory state.
Only active reads demand defined elements (sort.jl:1361-1427). -/
def runInt32Radix (ops : RadixSortOps) (vector scratch : Array (Option Nat))
    (lo hi : Int) (bits : JInt .u64) (offset : Int) :
    Option (SortResult (Array (Option Nat) × Array (Option Nat) × Bool)) :=
  let vVec : Vec := ⟨0, .u64, [vector.size], [(1, vector.size)]⟩
  let sVec : Vec := ⟨1, .u64, [scratch.size], [(1, scratch.size)]⟩
  let encode := fun values : Array (Option Nat) =>
    values.toList.map (Option.map fun value => int.lit .u64 (Int.ofNat value))
  let heap : Heap := { integers := [], unsigned := [encode vector, encode scratch] }
  match radixSortBang ops vVec sVec (int.lit .i64 lo) (int.lit .i64 hi)
      (int.lit .i64 offset) bits none heap with
  | none => none
  | some (.error error) => some (.error (.native error))
  | some (.ok (inVector, heap')) => some do
    let get (index : Nat) := match heap'.unsigned[index]? with
      | none => .error (.native (.array .bounds))
      | some values => .ok ((values.map (Option.map fun value => value.val.toNat)).toArray)
    pure (← get 0, ← get 1, inVector)

/-- sort.jl:1430-1441, with the installed Float64 logarithm and native integer/IEEE
arithmetic. The default radix passes use the source memory machine and cumulative sum. -/
def int32DefaultRadixOps : RadixSortOps where
  pass := nativeRadixPassOps defaultScalarPrimitives nativeCumsum
  heuristic := fun lo hi bits => do
    let difference := int.sub hi lo
    let logarithm ← liftJl (special.log.log_64 (float.floatOfInt .f64 difference))
    let three := float.floatOfInt .f64 (int.lit .i64 3)
    let four := float.floatOfInt .f64 (int.lit .i64 4)
    let ten := float.floatOfInt .f64 (int.lit .i64 10)
    let guess := JuliaLean.C.jlMinFloat ten (float.add_IEEEFloat
      (float.div_IEEEFloat (float.mul_IEEEFloat logarithm three) four) three)
    let inner ← mixedCld bits guess
    liftJl (float.intOfFloat .u8 (← mixedCld bits inner))
  allocateCounts := fun n => integerAction (array.heapVectorAllocate intTyLayout .i64 n)

/-- sort.jl:1017-1047: the native Int32 radix specialization uses the original typed scratch. -/
def int32RadixWrapperOps (radix : RadixSortOps) :
    RadixSortWrapperOps Int32WithoutMissing (JInt .i32) (Array (Option Nat)) Nat Int (Array Int)
      Int32Scratch Bool Int32SortKeywords SortException (Int32WithoutMissing × Int32Scratch) where
  rangeAndExtrema := fun kw => pure (kw.lo, kw.hi, kw.minimum, kw.maximum, kw.scratch)
  uintMapOps := int32MapOps
  subtractUnsigned := fun a b => (a + 2 ^ 32 - b) % 2 ^ 32
  topSetBit := fun code => int.lit .u64 (if code = 0 then 0 else Nat.log2 code + 1)
  range := arrayIndexRange
  windowLength := fun lo hi => (hi - lo + 1).toNat
  oneMinus := fun lo => 1 - lo
  readUnsigned := int32UnsignedRead
  writeUnsigned := fun values index value => liftSortJl (arrayWrite values index (some value))
  radixOps := radix
  runRadixSort := fun ops values lo hi bits scratch offset =>
    runInt32Radix ops values scratch lo hi bits offset
  makeScratch := fun existing _ length => makeInt32Scratch existing (int.lit .i64 length)
  reinterpretScratch := fun _ => reinterpretInt32Unsigned
  unmapOps := int32UnmapOps
  finish := Prod.mk

/-- sort.jl:948-969, using WithoutMissingVector indexing and preserving kw.scratch. -/
def int32CountingOps : CountingSortOps Int32WithoutMissing Int SearchIndex SearchIndex
    (Array Nat) Bool Int32SortKeywords (Option Int32Scratch) SortException where
  rangeAndScratch := fun kw => pure (kw.lo, kw.hi, ⟨.i32, kw.minimum⟩, ⟨.i32, kw.maximum⟩, kw.scratch)
  isReverse := id
  wrapSubtract := indexSub
  one := searchIndex .i64 1
  maybeUnsigned := fun value => searchIndex (unsignedIntegerType value.ty) value.val
  countLength := (arrayCountingOps .i32).countLength
  allocateCounts := (arrayCountingOps .i32).allocateCounts
  range := arrayIndexRange
  read := fun v i => do pure ⟨.i32, ← int32NonmissingRead v i⟩
  write := fun v i value => do
    let value ← liftSortJl (JInt.convert "Int32" .i32 value.val)
    int32NonmissingWrite v i value
  bucketForValue := (arrayCountingOps .i32).bucketForValue
  countRead := (arrayCountingOps .i32).countRead
  countWrite := (arrayCountingOps .i32).countWrite
  bucketValues := (arrayCountingOps .i32).bucketValues
  bucketIndex := (arrayCountingOps .i32).bucketIndex
  bucketValue := id
  lastBucketIndex := (arrayCountingOps .i32).lastBucketIndex
  nextAfterBucket := (arrayCountingOps .i32).nextAfterBucket
  valueNeedsSignedConversion := fun _ value => !value.ty.signed
  toSigned := (arrayCountingOps .i32).toSigned

/-- sort.jl:1252-1287, scratch/vector partition with checked abstract storage methods. -/
def int32PartitionVector (pivot : Int → Int → Int) :
    ScratchPartitionOps Int32WithoutMissing Int32Scratch Int32WithoutMissing Int
      (JInt .i32) Bool SortException where
  modelExhausted := .errorException "fuel"
  pivotIndex := fun lo hi => pure (pivot lo hi)
  readSource := int32ScratchRead
  writeTarget := int32NonmissingWrite
  writePivot := fun target _ index value => do
    let updated ← int32NonmissingWrite target index value
    pure (updated, updated)
  lessValue := int32DirectLess
  lessIndex := fun a b => decide (a < b)
  nextIndex := (· + 1)
  subtractIndex := Int.sub
  addBoolToIndex := fun i yes => i + if yes then 1 else 0
  addPivotOffset := Int.add
  distance := fun a b => (b - a).toNat

def int32PartitionScratch (pivot : Int → Int → Int) :
    ScratchPartitionOps Int32Scratch Int32WithoutMissing Int32WithoutMissing Int
      (JInt .i32) Bool SortException where
  modelExhausted := .errorException "fuel"
  pivotIndex := fun lo hi => pure (pivot lo hi)
  readSource := int32NonmissingRead
  writeTarget := int32ScratchWrite
  writePivot := fun target destination index value => do
    let destination ← int32NonmissingWrite destination index value
    pure (target, destination)
  lessValue := int32DirectLess
  lessIndex := fun a b => decide (a < b)
  nextIndex := (· + 1)
  subtractIndex := Int.sub
  addBoolToIndex := fun i yes => i + if yes then 1 else 0
  addPivotOffset := Int.add
  distance := fun a b => (b - a).toNat

/-- The ScratchQuickSort fallback in DEFAULT_UNSTABLE has SMALL_ALGORITHM as its next
algorithm (sort.jl:1079,1121-1164,1568-1601). Scratch is allocated at the source allocation site. -/
def int32ScratchQuickOps (pivot : Int → Int → Int) :
    ScratchQuickSortOps Int32WithoutMissing Int32Scratch (JInt .i32) Int Unit Bool
      Int32SortKeywords Int32Scratch SortException where
  rangeAndScratch := fun kw => pure (kw.lo, kw.hi, kw.scratch)
  makeScratch := fun scratch _ length => makeInt32Scratch scratch (int.lit .i64 length)
  requireOffset := fun offset => match offset with
    | some value => pure value
    | none => .error (.jl (.methodError "+"))
  oneMinus := fun lo => 1 - lo
  zeroIndex := 0
  negateIndex := Int.neg
  windowLength := fun lo hi => (hi - lo + 1).toNat
  lessIndex := fun a b => decide (a < b)
  lessEq := fun a b => decide (a ≤ b)
  distance := fun a b => (b - a).toNat
  addIndex := Int.add
  nextIndex := (· + 1)
  previousIndex := (· - 1)
  lowBound := fun _ => none
  highBound := fun _ => none
  smallThreshold := 20
  partitionInVector := int32PartitionVector pivot
  partitionInScratch := int32PartitionScratch pivot
  copyTo := fun v destination source start length => do
    let mut v := v
    for offset in List.range length do
      let value ← int32ScratchRead source (start + offset)
      v ← int32NonmissingWrite v (destination + offset) value
    pure v
  reverse := int32Reverse
  withScratch := fun kw scratch => { kw with scratch := some scratch }
  withBounds := fun kw lo hi => { kw with lo, hi }
  nextAlgorithm := id
  sortNext := fun v _ reverse kw => do
    let v ← int32Insertion reverse v kw.lo kw.hi
    pure (v, kw.scratch)

/-- The integer half of the fixed DEFAULT_UNSTABLE tree, sort.jl:1568-1601.
The native eltype is UIntMappable; Small{40}, CheckSorted, ComputeExtrema,
ConsiderCountingSort, ConsiderRadixSort and Small{80}/ScratchQuickSort retain source order. -/
def sortInt32Default (radix : RadixSortOps)
    (pivot : Int → Int → Int) (v : Int32WithoutMissing) (reverse : Bool)
    (lo hi : Int) (scratch : Option Int32Scratch) :
    Option (SortResult (Int32WithoutMissing × Option Int32Scratch)) :=
  (do
    if hi - lo < 40 then
      let v ← liftExcept (int32Insertion reverse v lo hi)
      return (v, scratch)
    let sorted ← liftExcept (storageIssortedWindow arrayIndices
      (fun v lo hi => liftSortJl (storageCheckBounds arrayStorage v.data lo hi))
      int32NonmissingRead (fun reverse => int32DirectLess reverse) v lo hi reverse)
    if sorted then return (v, scratch)
    if hi - lo ≥ 500 then
      let revSorted ← liftExcept (storageIssortedWindow arrayIndices
        (fun v lo hi => liftSortJl (storageCheckBounds arrayStorage v.data lo hi))
        int32NonmissingRead (fun reverse => int32DirectLess reverse) v lo hi (!reverse))
      if revSorted then
        return (← liftExcept (int32Reverse v lo hi), scratch)
    let first ← liftExcept (int32NonmissingRead v lo)
    let mut minimum := first
    let mut maximum := first
    for index in arrayIndexRange (lo + 1) hi do
      let value ← liftExcept (int32NonmissingRead v index)
      if ← liftExcept (int32DirectLess reverse value minimum) then minimum := value
      if ← liftExcept (int32DirectLess reverse maximum value) then maximum := value
    if !(← liftExcept (int32DirectLess reverse minimum maximum)) then return (v, scratch)
    let kw : Int32SortKeywords := ⟨lo, hi, minimum, maximum, scratch⟩
    let range := (maybeUnsigned .i32
      (if reverse then int.sub minimum maximum else int.sub maximum minimum)).val
    if range < (hi - lo) / 2 then
      return ← liftExcept (sortCounting int32CountingOps v reverse kw)
    let urange := ((integerCode .i32 reverse maximum).val -
      (integerCode .i32 reverse minimum).val) % 2 ^ 32
    let bits := if urange = 0 then 0 else Nat.log2 urange.toNat + 1
    let logarithm ← liftExcept (liftSortJl (special.log.log_64
      (float.floatOfInt .f64 (int.lit .i64 (hi - lo)))))
    let lhs := float.floatOfInt .f64 (int.lit .i64 (bits + 70))
    let rhs := float.mul_IEEEFloat (float.floatOfInt .f64 (int.lit .i64 22)) logarithm
    if float.lt_IEEEFloat lhs rhs then
      let result ← (ExceptT.mk (sortRadixAlgorithm (int32RadixWrapperOps radix) v reverse kw) :
        Run SortException (Int32WithoutMissing × Int32Scratch))
      return (result.1, some result.2)
    if hi - lo < 80 then
      return (← liftExcept (int32Insertion reverse v lo hi), scratch)
    return ← liftExcept (sortScratchQuick (int32ScratchQuickOps pivot) v () reverse kw)
      : Run SortException (Int32WithoutMissing × Option Int32Scratch)).run

/-- sort.jl:1732-1741,1568-1601,651-655,794-811: public default sorting of a native
Union{Missing,Int32} vector. MissingOptimization forwards the original scratch while
WithoutMissingVector changes the working eltype to Int32. Bool/IEEE specializations do not
apply to Int32; Small{10} precedes the UIntMappable integer subtree. -/
def sortMissingInt32Default
    (pivot : Int → Int → Int) (values : Int32Values) (reverse : Bool)
    (scratch : Option Int32Values) : Option (SortResult Int32Values) :=
  (do
    let (values, lo, hi) ← liftExcept (partitionMissingArray values reverse 1 values.size)
    let wrapped : Int32WithoutMissing := ⟨values⟩
    let scratch := scratch.map (Int32Scratch.mk true)
    if hi - lo < 10 then
      return (← liftExcept (int32Insertion reverse
        wrapped lo hi)).data
    let (result, _) ← (ExceptT.mk (sortInt32Default int32DefaultRadixOps pivot wrapped reverse lo hi scratch) :
      Run SortException (Int32WithoutMissing × Option Int32Scratch))
    return result.data : Run SortException Int32Values).run
end JuliaLean.base.sort


/-!
The comparison-based sorting kernels of `base/sort.jl` (master `bbfa0ce4150`)
reached by `sort!`, `partialsort!` and `partialsortperm!` for orderings that
are not `UIntMappable` (any `by`/`lt`, and `Perm`), and their entry points.

Vectors are one-based `Array α`; `lt` is `lt(o, ·, ·)` for the ordering `o`.
Index reads and writes mirror Julia's `@inbounds` accesses: the model is only
claimed faithful on executions whose accesses are in bounds (every property
below holds on such executions only). `fuel` bounds recursion and is a model
artifact; the entry points supply enough for every input.
-/

namespace JuliaLean.Sort

open JuliaLean

section
variable {α : Type} [Inhabited α]

/-- `v[i]` (one-based). -/
def rd (v : Array α) (i : Int) : α := if 1 ≤ i then v.getD (i - 1).toNat default else default

/-- `v[i] = x` (one-based). -/
def wr (v : Array α) (i : Int) (x : α) : Array α :=
  if 1 ≤ i then v.modify (i - 1).toNat (fun _ => x) else v

/-- `copyto!(dest, d, src, s, n)` for `n ≥ 0`, `base/array.jl`. -/
def copyTo (dest : Array α) (d : Int) (src : Array α) (s : Int) (n : Int) : Array α :=
  (List.range n.toNat).foldl (fun w (k : Nat) => wr w (d + k) (rd src (s + k))) dest

/-- `reverse!(v, lo, hi)`, `base/array.jl` (swaps `v[lo+k]` and `v[hi-k]`). -/
def reverseRange (v : Array α) (lo hi : Int) : Array α :=
  (List.range ((hi - lo + 1) / 2).toNat).foldl
    (fun w (k : Nat) => let a := rd w (lo + k); let b := rd w (hi - k); wr (wr w (lo + k) b) (hi - k) a) v

/-- Inner loop of `InsertionSort`, `base/sort.jl:841-849`: `k = j - lo` steps remain. -/
def insertLoop (lt : α → α → Bool) (lo : Int) (x : α) : Nat → Array α → Int → Array α
  | 0, v, j => wr v j x
  | k + 1, v, j =>
    let y := rd v (j - 1)
    if !(lt x y) then wr v j x
    else insertLoop lt lo x k (wr v j y) (j - 1)

/-- `_sort!(v, InsertionSortAlg(), o, (; lo, hi))`, `base/sort.jl:835-852`. -/
def insertionSort (lt : α → α → Bool) (v : Array α) (lo hi : Int) : Array α :=
  (List.range (hi - lo).toNat).foldl
    (fun w (k : Nat) => let i := lo + 1 + k; insertLoop lt lo (rd w i) (i - lo).toNat w i) v

/-- `partition!(t, lo, hi, offset, o, v, rev, pivot_dest, pivot_index_offset)`,
`base/sort.jl:1088-1119`, with source `src` (Julia's `v`) and destination `dst`
(Julia's `t`). `pivotToSrc` says whether `pivot_dest` is the source array
(the first call site, sort.jl:1135) or the destination (sort.jl:1133).
`piv lo hi` is `mod(hash(lo), lo:hi)` (sort.jl:1092). Returns the updated
source, destination and the pivot index. -/
def partition (piv : Int → Int → Int) (lt : α → α → Bool) (src dst : Array α)
    (lo hi offset : Int) (rev pivotToSrc : Bool) (pio : Int) : Array α × Array α × Int :=
  let p := piv lo hi
  let pivot := rd src p
  -- sort.jl:1095-1101
  let r1 := (List.range (p - lo).toNat).foldl (fun (st : Array α × Int) (k : Nat) =>
      let l := lo + k
      let x := rd src l
      let fx := if rev then !(lt x pivot) else lt pivot x
      (wr st.1 ((if fx then hi else l) - st.2) x, st.2 + (if fx then 1 else 0))) (dst, offset)
  -- sort.jl:1102-1108
  let r2 := (List.range (hi - p).toNat).foldl (fun (st : Array α × Int) (k : Nat) =>
      let l := p + k
      let x := rd src (l + 1)
      let fx := if rev then lt pivot x else !(lt x pivot)
      (wr st.1 ((if fx then hi else l) - st.2) x, st.2 + (if fx then 1 else 0))) r1
  -- sort.jl:1109-1110 (the loops end with `lo == hi`)
  let j := hi - r2.2 + pio
  if pivotToSrc then (wr src j pivot, r2.1, j) else (src, wr r2.1 j pivot, j)

/-- The `lo`/`hi` targets of `ScratchQuickSort` (`missing` is `none`), sort.jl:1074-1082. -/
structure Target where
  lo : Option Int
  hi : Option Int

/-- `SMALL_THRESHOLD`, `base/sort.jl:1595`. -/
def smallThreshold : Int := 20

/-- `_sort!(v, a::ScratchQuickSort, o, kw; t, offset, swap, rev)`,
`base/sort.jl:1121-1164`, on the pair `(v, t)`; `a.next` is `InsertionSort`. -/
def scratchQuickSortLoop (piv : Int → Int → Int) (lt : α → α → Bool) (a : Target) :
    Nat → Array α → Array α → Int → Int → Int → Bool → Bool → Array α × Array α
  | 0, v, t, _, _, _, _, _ => (v, t)
  | fuel + 1, v, t, lo, hi, offset, swap, rev =>
    if lo < hi ∧ hi - lo > smallThreshold then
      -- sort.jl:1132-1137
      let r : Array α × Array α × Int :=
        if swap then
          let (s, d, j) := partition piv lt t v (lo + offset) (hi + offset) offset rev false 0
          (d, s, j)
        else partition piv lt v t lo hi (-offset) rev true (-offset)
      let v := r.1
      let t := r.2.1
      let j := r.2.2
      let swap := !swap
      if a.lo.isSome ∧ j ≤ a.lo.getD 0 then
        -- sort.jl:1140-1144: skip sorting the lower part
        let v := if swap then copyTo v lo t (lo + offset) (j - lo) else v
        let v := if rev then reverseRange v lo (j - 1) else v
        scratchQuickSortLoop piv lt a fuel v t (j + 1) hi offset swap (!rev)
      else if a.hi.isSome ∧ a.hi.getD 0 ≤ j then
        -- sort.jl:1145-1148: skip sorting the upper part
        let v := if swap then copyTo v (j + 1) t (j + 1 + offset) (hi - j) else v
        let v := if rev then v else reverseRange v (j + 1) hi
        scratchQuickSortLoop piv lt a fuel v t lo (j - 1) offset swap rev
      else if j - lo < hi - j then
        -- sort.jl:1149-1154
        let r := scratchQuickSortLoop piv lt a fuel v t lo (j - 1) offset swap rev
        scratchQuickSortLoop piv lt a fuel r.1 r.2 (j + 1) hi offset swap (!rev)
      else
        -- sort.jl:1155-1157
        let r := scratchQuickSortLoop piv lt a fuel v t (j + 1) hi offset swap (!rev)
        scratchQuickSortLoop piv lt a fuel r.1 r.2 lo (j - 1) offset swap rev
    else
      -- sort.jl:1160-1163
      if hi < lo then (v, t)
      else
        let v := if swap then copyTo v lo t (lo + offset) (hi - lo + 1) else v
        let v := if rev then reverseRange v lo hi else v
        (insertionSort lt v lo hi, t)

/-- Entry of `ScratchQuickSort` without a caller scratch vector, sort.jl:1125-1129:
`t` is a fresh vector of length `hi-lo+1` and `offset = 1-lo`. -/
def scratchQuickSort (piv : Int → Int → Int) (lt : α → α → Bool) (a : Target)
    (v : Array α) (lo hi : Int) : Array α :=
  (scratchQuickSortLoop piv lt a ((hi - lo + 2).toNat) v
    (Array.replicate (hi - lo + 1).toNat default) lo hi (1 - lo) false false).1

/-- `InitialOptimizations(next)` (sort.jl:1473-1478) for element types that are
neither `Missing`-unions, `Bool` nor IEEE floats, on a plain vector: only
`Small{10}` acts, sending `hi - lo < 10` to `InsertionSort` (sort.jl:795-802). -/
def initialOptimizations (lt : α → α → Bool) (next : Array α → Array α)
    (v : Array α) (lo hi : Int) : Array α :=
  if hi - lo < 10 then insertionSort lt v lo hi else next v

/-- `_issorted(v, lo, hi, o)`, `base/sort.jl:1445-1451`. -/
def isSortedRange (lt : α → α → Bool) (v : Array α) (lo hi : Int) : Bool :=
  (List.range (hi - lo).toNat).all fun (k : Nat) => !(lt (rd v (lo + 1 + k)) (rd v (lo + k)))

/-- `StableCheckSorted(ScratchQuickSort())`, `base/sort.jl:1368-1379`. The
reverse check uses `Lt((x, y) -> !lt(o, x, y))`. -/
def stableCheckSorted (piv : Int → Int → Int) (lt : α → α → Bool) (v : Array α)
    (lo hi : Int) : Array α :=
  if isSortedRange lt v lo hi then v
  else if isSortedRange (fun x y => !(lt x y)) v lo hi then reverseRange v lo hi
  else scratchQuickSort piv lt ⟨none, none⟩ v lo hi

/-- `sort!(v; alg=DEFAULT_STABLE or DEFAULT_UNSTABLE, order)` for an ordering
that is not `UIntMappable` (sort.jl:1580-1593, 1732-1741): the `IsUIntMappable`
test (sort.jl:774-780) takes the `StableCheckSorted(ScratchQuickSort())` branch. -/
def sortGeneric (piv : Int → Int → Int) (lt : α → α → Bool) (v : Array α) : Array α :=
  initialOptimizations lt (fun w => stableCheckSorted piv lt w 1 w.size) v 1 v.size

/-- The pivot rule `mod(hash(lo), lo:hi)` (sort.jl:1092) on 64-bit Julia, for
`1 ≤ lo ≤ hi`: `hash(x::Int64) = hash_finalizer(3 * HASH_SEED - x)` with
wrapping `UInt64` arithmetic (`base/hashing.jl:3,40,55-63,75-76`), and
`mod(i, lo:hi) = mod(i - lo, hi - lo + 1) + lo` (`base/range.jl:1549`) in `UInt64`. -/
def juliaHashInt (x : Int) : Nat :=
  let m : Nat := 2 ^ 64
  let z : Nat := (((3 * 0xbdd89aa982704029 + m * m : Nat) : Int) - x).toNat % m
  let z : Nat := z ^^^ (z >>> 32)
  let z : Nat := (z * 0x63652a4cd374b267) % m
  z ^^^ (z >>> 33)

def juliaPivot (lo hi : Int) : Int :=
  lo + (((juliaHashInt lo + 2 ^ 64 - lo.toNat) % 2 ^ 64) % (hi - lo + 1).toNat : Nat)

end

end JuliaLean.Sort


/-!
Binary searches on vectors, `base/sort.jl:184-238` (master `bbfa0ce4150`),
and `issorted(itr, order)`, `base/sort.jl:48-60`.

The searches take the window `lo::T`, `hi::T` of an arbitrary integer type `T`.
Their locals change type as the source runs: `m + 1` and `half_len + 1` add
the `Int` literal `1` and so are computed in `promote_type(T, Int)`, while
`midpoint`, `T(1)` and the sentinels stay in `T`. `SearchIndex` records the
current Julia type of each local. The keyword methods (`sort.jl:304-311`) call
these with `lo = firstindex(v) = 1` and `hi = lastindex(v)`, both `Int`.
-/

namespace JuliaLean.Sort

open JuliaLean

/-- An integer local together with its current Julia type. -/
structure SearchIndex where
  ty : IntTy
  word : JInt ty

def searchIndex (t : IntTy) (x : Int) : SearchIndex := ⟨t, JInt.wrap t x⟩

def SearchIndex.val (x : SearchIndex) : Int := x.word.val

/-- `x + y` and `x - y` after promotion (`base/int.jl`), wrapping in the promoted type. -/
def indexAdd (x y : SearchIndex) : SearchIndex :=
  searchIndex (IntTy.promote x.ty y.ty) (x.val + y.val)

def indexSub (x y : SearchIndex) : SearchIndex :=
  searchIndex (IntTy.promote x.ty y.ty) (x.val - y.val)

/-- `x >>> 0x01` (logical shift of the bit pattern), `base/sort.jl:188`. -/
def indexHalf (x : SearchIndex) : SearchIndex :=
  searchIndex x.ty ((x.val % (2 ^ x.ty.bits)) / 2)

/-- `midpoint(lo::T, hi::T) = lo +% ((hi -% lo) >>> 0x01)`, `base/array.jl:2288`. -/
def indexMidpoint (lo hi : SearchIndex) : SearchIndex :=
  indexAdd lo (indexHalf (indexSub hi lo))

/-- Outcome of a search. `invalidAccess i` is an `@inbounds` read of `v[i]`
outside the vector (undefined behaviour in Julia: it reads arbitrary memory);
`exhausted` is the model's fuel running out, never a Julia outcome. -/
inductive SearchResult (α : Type) where
  | returned (value : α)
  | invalidAccess (index : Int)
  | exhausted
  deriving DecidableEq

/-- One-based read `v[i]`; `none` outside the vector. -/
def vectorRead (v : Array α) (i : Int) : Option α :=
  if 1 ≤ i then v[i.toNat - 1]? else none

/-- Loop of `searchsortedfirst`, `base/sort.jl:187-197`. `hi = m` is dead
(the loop reads only `lo` and `len`) and is omitted. -/
def firstSearchLoop (lt : α → α → Bool) (v : Array α) (x : α) :
    Nat → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _ => .exhausted
  | fuel + 1, lo, len =>
    if len.val = 0 then .returned lo.val else
    let half := indexHalf len
    let m := indexAdd lo half
    match vectorRead v m.val with
    | none => .invalidAccess m.val
    | some a =>
      if lt a x then
        firstSearchLoop lt v x fuel (indexAdd m (searchIndex .i64 1))
          (indexSub len (indexAdd half (searchIndex .i64 1)))
      else firstSearchLoop lt v x fuel lo half

/-- `searchsortedfirst(v, x, lo::T, hi::T, o)`, `base/sort.jl:184-199`. -/
def searchsortedfirst (lt : α → α → Bool) (v : Array α) (x : α) {t : IntTy}
    (lo hi : JInt t) (fuel : Nat := v.size + 2) : SearchResult Int :=
  let l : SearchIndex := ⟨t, lo⟩
  let h := indexAdd ⟨t, hi⟩ (searchIndex t 1)
  firstSearchLoop lt v x fuel l (indexSub h l)

/-- Loop of `searchsortedlast`, `base/sort.jl:207-214`. -/
def lastSearchLoop (lt : α → α → Bool) (v : Array α) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then .returned lo.val else
    let m := indexMidpoint lo hi
    match vectorRead v m.val with
    | none => .invalidAccess m.val
    | some a =>
      if lt x a then lastSearchLoop lt v x u fuel lo m
      else lastSearchLoop lt v x u fuel m hi

/-- `searchsortedlast(v, x, lo::T, hi::T, o)`, `base/sort.jl:203-216`. -/
def searchsortedlast (lt : α → α → Bool) (v : Array α) (x : α) {t : IntTy}
    (lo hi : JInt t) (fuel : Nat := v.size + 2) : SearchResult Int :=
  let u := searchIndex t 1
  lastSearchLoop lt v x u fuel (indexSub ⟨t, lo⟩ u) (indexAdd ⟨t, hi⟩ u)

/-- Loop of `searchsorted`, `base/sort.jl:225-237`: `v[m] < x` is tested before
`x < v[m]`; on a match the first and last searches run on `lo+u:m` and `m:hi-u`. -/
def equalSearchLoop (lt : α → α → Bool) (v : Array α) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult (Int × Int)
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then
      .returned ((indexAdd lo (searchIndex .i64 1)).val, (indexSub hi (searchIndex .i64 1)).val)
    else
      let m := indexMidpoint lo hi
      match vectorRead v m.val with
      | none => .invalidAccess m.val
      | some a =>
        if lt a x then equalSearchLoop lt v x u fuel m hi
        else if lt x a then equalSearchLoop lt v x u fuel lo m
        else
          let start := indexAdd lo u
          match firstSearchLoop lt v x (v.size + 2) start
              (indexSub (indexAdd m (searchIndex m.ty 1)) start) with
          | .invalidAccess i => .invalidAccess i
          | .exhausted => .exhausted
          | .returned a =>
            match lastSearchLoop lt v x (searchIndex m.ty 1) (v.size + 2)
                (indexSub m (searchIndex m.ty 1)) (indexAdd (indexSub hi u) (searchIndex m.ty 1)) with
            | .returned b => .returned (a, b)
            | .invalidAccess i => .invalidAccess i
            | .exhausted => .exhausted

/-- `searchsorted(v, x, ilo::T, ihi::T, o)`, `base/sort.jl:221-238`. -/
def searchsorted (lt : α → α → Bool) (v : Array α) (x : α) {t : IntTy}
    (lo hi : JInt t) (fuel : Nat := v.size + 2) : SearchResult (Int × Int) :=
  let u := searchIndex t 1
  equalSearchLoop lt v x u fuel (indexSub ⟨t, lo⟩ u) (indexAdd ⟨t, hi⟩ u)

/-- `issorted(itr, order)`, `base/sort.jl:48-60`, on a finite list. -/
def issorted (lt : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => if lt b a then false else issorted lt (b :: rest)

/-- `v[i]` is ordered before `x`. -/
def before (lt : α → α → Bool) (v : Array α) (x : α) (i : Int) : Bool :=
  match vectorRead v i with
  | some a => lt a x
  | none => false

/-- `v[i]` is not ordered after `x`. -/
def notAfter (lt : α → α → Bool) (v : Array α) (x : α) (i : Int) : Bool :=
  match vectorRead v i with
  | some a => !(lt x a)
  | none => false

/-! ### Proofs for `Int` windows -/

abbrev I (x : Int) : SearchIndex := searchIndex .i64 x

end JuliaLean.Sort


/-!
`searchsortedfirst`/`searchsortedlast`/`searchsorted` on integer ranges,
`base/sort.jl:269-302` (master `bbfa0ce4150`).

Scope: ranges whose `first`, `step` and `last` share the element type `T`
(`UnitRange{T}`, and `StepRange{T,T}` for signed `T`), searched for a value
`x::T` of the same type. On `Int64` ranges this is the default case
`searchsortedfirst(r, x::Int)`. The four `FastRangeOrderings`
(`Forward`, `Reverse`, `Lt(<)`, `ReverseOrdering(Lt(<))`) compare
`BitInteger`s identically to `<` (`isless` on integers is `<`), so the ordering
is the Boolean `rev` (`ReverseOrdering`).
-/

namespace JuliaLean.Sort

open JuliaLean JuliaLean.Registry

/-- `lt(o, a, b)` for a `FastRangeOrderings` value on integers,
`base/ordering.jl:118-121`: `rev` is `o isa ReverseOrdering`. -/
def rangeLt {t : IntTy} (rev : Bool) (a b : JInt t) : Bool :=
  if rev then decide (b.val < a.val) else decide (a.val < b.val)

/-- `y + 1` with the `Int` literal `1`: the sum is computed in
`promote_type(T, Int64)` (`base/int.jl`), wrapping there. -/
def addOneInt {t : IntTy} (y : JInt t) : Int :=
  wrapInt (IntTy.promote t .i64) (y.val + 1)

/-- The `::keytype(a)` return annotation converts the result to `Int`. -/
def toKeytype (y : Int) : Jl JInt64 := JInt.convert (IntTy.i64.name) .i64 y

/-- `searchsortedlast(a::AbstractRange{<:Integer}, x::Real, o::FastRangeOrderings)`,
`base/sort.jl:269-283`. `floor(Integer, x)` and `ceil(Integer, x)` are `x`
for an integer `x`. `len` is `length(a)`. -/
def rangeSearchLast {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t)
    (rev : Bool) : Jl JInt64 :=
  if rangeLt rev x f then pure (JInt.lit .i64 0)                 -- sort.jl:272-273
  else if h.val = 0 ∨ !(rangeLt rev x l) then pure len            -- sort.jl:274-275
  else do
    -- sort.jl:277-281: both branches are `fld(x - f, h) + 1` for integer x
    let q ← JInt.fld (x - f) h
    toKeytype (addOneInt q)

/-- `searchsortedfirst(a::AbstractRange{<:Integer}, x::Real, o::FastRangeOrderings)`,
`base/sort.jl:285-299`. `length(a) + 1` is `Int` arithmetic. -/
def rangeSearchFirst {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t)
    (rev : Bool) : Jl JInt64 :=
  if !(rangeLt rev f x) then pure (JInt.lit .i64 1)               -- sort.jl:288-289
  else if h.val = 0 ∨ rangeLt rev l x then pure (len + JInt.lit .i64 1)  -- sort.jl:290-291
  else do
    -- sort.jl:293-297: both branches are `cld(x - f, h) + 1` for integer x
    let q ← JInt.cld (x - f) h
    toKeytype (addOneInt q)

/-- `searchsorted(a::AbstractRange{<:Real}, x::Real, o)`, `base/sort.jl:301-302`:
the pair of endpoints of `searchsortedfirst(a,x,o):searchsortedlast(a,x,o)`. -/
def rangeSearchsorted {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t)
    (rev : Bool) : Jl (JInt64 × JInt64) := do
  let a ← rangeSearchFirst f h l len x rev
  let b ← rangeSearchLast f h l len x rev
  pure (a, b)

/-- The `i`-th element (1-based) of the arithmetic progression, as a mathematical integer. -/
def rangeElem {t : IntTy} (f h : JInt t) (i : Int) : Int := f.val + (i - 1) * h.val

/-- `lt(o, a, b)` on the mathematical element values. -/
def elemLt (rev : Bool) (a b : Int) : Bool :=
  if rev then decide (b < a) else decide (a < b)

end JuliaLean.Sort


/-!
`partialsort!`/`partialsort` and `partialsortperm!`/`partialsortperm`,
`base/sort.jl:97-177, 1853-1915` (master `bbfa0ce4150`), for element types
that are not `Bool` (so `BoolOptimization` passes through).
-/

namespace JuliaLean.Sort

open JuliaLean

/-- `k::Union{Integer,OrdinalRange}`. A range is stored as Julia stores it:
`first`, `step`, `last` and its length; its elements are `first + i*step`, `i < len`. -/
inductive KSel where
  | int (k : Int)
  | range (first step last : Int) (len : Nat)

/-- The indices `k` selects (`maybeview`, sort.jl:110-111). -/
def KSel.indices : KSel → List Int
  | .int k => [k]
  | .range f s _ n => (List.range n).map fun (i : Nat) => f + (i : Int) * s

/-- `ScratchQuickSort(k)`, sort.jl:1081-1082: `(k, k)` or `(first(k), last(k))`. -/
def KSel.target : KSel → Target
  | .int k => ⟨some k, some k⟩
  | .range f _ l _ => ⟨some f, some l⟩

def KSel.isEmpty : KSel → Bool
  | .int _ => false
  | .range _ _ _ n => n == 0

/-- Result of `partialsort!` in the model. `sampling` marks inputs that reach the
randomized sampling phase of `BracketedSort` (sort.jl:1287 onward: `length(v) ≥ 260`
and a nonempty target), which is outside this model. -/
inductive PartialOutcome (α : Type) where
  | done (v : Array α) (result : List α)
  | thrown (e : JlError)
  | sampling

section
variable {α : Type} [Inhabited α]

/-- `maybeview(v, k)` with the bounds check of `getindex`/`view`. -/
def maybeview (v : Array α) (k : KSel) : Jl (List α) :=
  if k.indices.all (fun i => decide (1 ≤ i ∧ i ≤ v.size)) then .ok (k.indices.map (rd v))
  else .error .boundsError

/-- `partialsort!(v, k, o)`, sort.jl:97-108:
`BoolOptimization(Small{12}(BracketedSort(k)))`. `BracketedSort` (sort.jl:1264-1286)
returns at once for `lo ≥ hi`, delegates to `InitialOptimizations(ScratchQuickSort(k))`
when `ln < 260`, and otherwise evaluates `minimum(target)` (sort.jl:1286), which
throws `ArgumentError` for an empty range. -/
def partialsort (piv : Int → Int → Int) (lt : α → α → Bool) (v : Array α) (k : KSel) :
    PartialOutcome α :=
  let n : Int := v.size
  let finish (w : Array α) : PartialOutcome α :=
    match maybeview w k with
    | .ok r => .done w r
    | .error e => .thrown e
  if n - 1 < 12 then finish (insertionSort lt v 1 n)                       -- sort.jl:797
  else if n < 260 then                                                    -- sort.jl:1277
    finish (initialOptimizations lt (fun w => scratchQuickSort piv lt k.target w 1 n) v 1 n)
  else if k.isEmpty then .thrown (.argumentError "range must be non-empty") -- sort.jl:1286
  else .sampling

end

/-! ### `partialsortperm` -/

instance sortInhabitedJInt {t : IntTy} : Inhabited (JInt t) := ⟨JInt.lit t 0⟩

/-- `partialsortperm(v, k)` for `k` of integer type `t` (sort.jl:1853-1854) and
`partialsortperm!` (sort.jl:1896-1915): `ix = similar(Vector{eltype(k)}, axes(v,1))`,
`ix[i] = i` converts each index to `t` (`InexactError` when it does not fit),
then `InitialOptimizations(ScratchQuickSort(k))` sorts `ix` under
`Perm(ord(lt, by, rev, order), v)` (`base/ordering.jl:123-127`). -/
def partialsortperm (t : IntTy) (piv : Int → Int → Int) (lt : Int → Int → Bool)
    (v : Array Int) (k : KSel) : Jl (List (JInt t)) := do
  let ix ← (List.range v.size).mapM fun (i : Nat) => JInt.convert (t.name) t ((i : Int) + 1)
  let ix := ix.toArray
  let n : Int := v.size
  let plt (a b : JInt t) : Bool :=
    lt (rd v a.val) (rd v b.val) || (!(lt (rd v b.val) (rd v a.val)) && decide (a.val < b.val))
  let ix := initialOptimizations plt (fun w => scratchQuickSort piv plt k.target w 1 n) ix 1 n
  maybeview ix k

end JuliaLean.Sort


/-!
Executable control-flow models for the `base/sort.jl` findings catalogued by
the `SortTuplesCov` area. The public Julia reproducers exercise the complete methods.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean

/-! ### `insorted` equivalence -/

inductive SortValue where
  | negZero | posZero | one | missing
  deriving DecidableEq

/-- Julia `==` for the values used by the reproducer (`none` is `missing`). -/
def SortValue.eq : SortValue → SortValue → Option Bool
  | .missing, _ | _, .missing => none
  | .negZero, .posZero | .posZero, .negZero => some true
  | a, b => some (a = b)

/-- Julia `isless`: signed zeroes are ordered and `missing` sorts last. -/
def SortValue.lt : SortValue → SortValue → Bool
  | .negZero, .posZero | .negZero, .one | .negZero, .missing => true
  | .posZero, .one | .posZero, .missing => true
  | .one, .missing => true
  | _, _ => false

def orMissing : Option Bool → Option Bool → Option Bool
  | some true, _ | _, some true => some true
  | none, _ | _, none => none
  | _, _ => some false

/-- `in(x, r)` used by `insorted(x, r::AbstractRange)`, `base/sort.jl:466`. -/
def insortedRange (x : SortValue) (r : List SortValue) : Option Bool :=
  r.foldl (fun acc y => orMissing acc (SortValue.eq x y)) (some false)

/-- `!isempty(searchsorted(v, x))`, `base/sort.jl:465`: membership under the
sort-order equivalence `!lt(x,y) && !lt(y,x)`. -/
def insortedVector (x : SortValue) (v : List SortValue) : Bool :=
  v.any fun y => !SortValue.lt x y && !SortValue.lt y x

/-! ### Legacy six-argument sort -/

inductive LegacyAlg where
  | quick | merge | partialQuick | custom
  deriving DecidableEq

/-- `_sort!(v, a::Algorithm, o, kw)`, `base/sort.jl:2586-2595`. -/
def legacySortFallback (a legacyEntry : LegacyAlg) : Jl Unit :=
  if legacyEntry = a then
    .error (.argumentError "Base.Sort._sort! is not defined")
  else .ok ()

/-- The six-argument `sort!(..., scratch::Vector)`, `base/sort.jl:2578-2582`:
after a bounds check it enters `_sort!` with `legacy_dispatch_entry=a`. -/
def legacySortWithScratch (length lo hi : Int) (a : LegacyAlg) : Jl Unit :=
  if 1 ≤ lo ∧ hi ≤ length then legacySortFallback a a else .error .boundsError

/-- Supported old five-argument methods, `base/sort.jl:2454-2457,2482-2486,
2533-2537`. -/
def legacySortWithoutScratch (length lo hi : Int) (a : LegacyAlg) : Jl Unit :=
  if 1 ≤ lo ∧ hi ≤ length then
    match a with
    | .quick | .merge | .partialQuick => .ok ()
    | .custom => legacySortFallback a a
  else .error .boundsError

/-! ### Descending `PartialQuickSort` target -/

inductive PartialAction where
  | skipLower | skipUpper | recurseLower | recurseUpper
  deriving DecidableEq

/-- The branch after `partition!` in `_partialquicksort!`,
`base/sort.jl:2546-2562`. -/
def partialQuickAction (lo hi firstTarget lastTarget pivot : Int) : PartialAction :=
  if pivot ≤ firstTarget then .skipLower
  else if pivot ≥ lastTarget then .skipUpper
  else if pivot - lo < hi - pivot then .recurseLower
  else .recurseUpper

def targetIndices (first step : Int) (length : Nat) : List Int :=
  (List.range length).map fun (i : Nat) => first + (i : Int) * step

/-! ### Tuple algorithm dispatch -/

inductive TupleAlg where
  | defaultStable | defaultUnstable | insertion | quick | merge | partialQuick
  deriving DecidableEq

/-- `_sort(x::NTuple, a, o, kw)`, `base/sort.jl:1798-1808`: only the two
default algorithm tags have a method. -/
def sortTupleDispatch (a : TupleAlg) : Jl Unit :=
  match a with
  | .defaultStable | .defaultUnstable => .ok ()
  | _ => .error (.methodError "Base.Sort._sort")

/-! ### `dims` default evaluation order -/

/-- `size(A, dims)` for a two-dimensional array, including its exception at
dimension zero. -/
def matrixSize (dims : Int) : Jl Nat :=
  if dims < 1 then .error .boundsError
  else if dims ≤ 2 then .ok 2 else .ok 1

/-- `sort!(A; dims, scratch=<default>)`, `base/sort.jl:2187-2223`.  Julia
evaluates the scratch default's `size(A,dims)` before the body's explicit
dimension check. -/
def sortDimsDefault (nd dims : Int) : Jl Unit := do
  let n ← matrixSize dims
  let _scratchAllocated := !(n < 10)
  if 1 ≤ dims ∧ dims ≤ nd then .ok ()
  else .error (.argumentError "dimension out of range")

/-! ### Missing values and caller-provided scratch -/

inductive ScratchEltype where
  | int32 | missingOrInt32
  deriving DecidableEq

/-- `make_scratch(scratch::Vector, T, len)`, `base/sort.jl:511-516`: a scratch
whose element type differs from `T` is reinterpreted, which requires both
element types to be bitstypes. -/
def makeScratch (scratchType targetType : ScratchEltype) : Jl Unit :=
  if scratchType = targetType then .ok ()
  else match scratchType, targetType with
    | .int32, .int32 => .ok ()
    | _, _ => .error (.argumentError "cannot reinterpret")

/-- `MissingOptimization` keeps the caller scratch while changing the view's
element type to the non-missing type, and `RadixSort` passes both to
`make_scratch`, `base/sort.jl:651-655,1017-1046`. -/
def sortMissingWithScratch (scratchType : ScratchEltype) : Jl Unit :=
  makeScratch scratchType .int32

end JuliaLean.SortTuplesCov


/-! Keyword wrappers and scratch-space methods from `base/sort.jl`
(master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

inductive RevChoice where
  | nothing | false_ | true_
  deriving DecidableEq

def reverseRequested : RevChoice → Bool
  | .true_ => true
  | _ => false

/-- Keyword `issorted`, `base/sort.jl:86-95`. -/
def issortedKeyword {I O R : Type} (ord : Bool → O) (core : I → O → R)
    (itr : I) (rev : RevChoice) : R :=
  if reverseRequested rev then core itr (ord true) else core itr (ord false)

/-- Keyword `partialsort!`, `base/sort.jl:166-168`. -/
def partialsortKeyword {V K O R : Type} (ord : RevChoice → O)
    (core : V → K → O → R) (v : V) (k : K) (rev : RevChoice) : R :=
  core v k (ord rev)

/-- Generated positional search wrappers, `base/sort.jl:304-310`. -/
def searchOrderWrapper {V X O R : Type} (first last : V → Int)
    (core : V → X → Int → Int → O → R) (v : V) (x : X) (o : O) : R :=
  core v x (first v) (last v) o

/-- Generated keyword search wrappers, `base/sort.jl:304-310`. -/
def searchKeywordWrapper {V X O R : Type} (ord : RevChoice → O)
    (core : V → X → O → R) (v : V) (x : X) (rev : RevChoice) : R :=
  core v x (ord rev)

/-! ### Alternative keyword management -/

inductive KwValue where
  | missing
  | nothing
  | value (n : Int)
  deriving DecidableEq

abbrev KwState := List (String × KwValue)

def kwLookup (kw : KwState) (name : String) : Option KwValue :=
  (kw.find? fun p => p.1 = name).map Prod.snd

/-- The body generated for `_lo`, `_hi`, `_mn`, `_mx`, `_scratch`, and
`_legacy_dispatch_entry`, `base/sort.jl:475-489`. -/
def generatedKeywordGetter (kw : KwState) (name : String) (default : KwValue) : KwState × KwValue :=
  match kwLookup kw name with
  | some v => if v = .missing then (kw ++ [(name, default)], default) else (kw, v)
  | none => (kw ++ [(name, default)], default)

/-- `@getkw syms...`, `base/sort.jl:470-473`, expands each symbol to its
generated getter name in the same order. -/
def getkwExpansion (syms : List String) : List String := syms.map ("_" ++ ·)

/-! ### Scratch space -/

structure ScratchType where
  name : String
  bytes : Nat
  bits : Bool

structure ScratchVector where
  type : ScratchType
  length : Nat

structure ScratchResult where
  backing : ScratchVector
  viewType : ScratchType
  viewLength : Nat

/-- `make_scratch(nothing, T, len)`, `base/sort.jl:503-506`. -/
def makeScratchNothing (target : ScratchType) (length : Nat) : ScratchResult :=
  let v := ⟨target, length⟩
  ⟨v, target, length⟩

/-- `make_scratch(scratch::Vector{T}, T, len)`, `base/sort.jl:507-510`. -/
def makeScratchSame (scratch : ScratchVector) (length : Nat) : ScratchResult :=
  let backing := { scratch with length := max scratch.length length }
  ⟨backing, scratch.type, backing.length⟩

/-- `make_scratch(scratch::Vector, T, len)`, `base/sort.jl:511-516`: compute
the backing length in bytes, resize, then reinterpret. -/
def makeScratchOther (scratch : ScratchVector) (target : ScratchType) (length : Nat) : Jl ScratchResult :=
  let bytesNeeded := length * target.bytes
  let backingLength := bytesNeeded / scratch.type.bytes
  let backing := { scratch with length := max scratch.length backingLength }
  if scratch.type.bits && target.bits && target.bytes > 0 &&
      (backing.length * scratch.type.bytes) % target.bytes = 0 then
    .ok ⟨backing, target, backing.length * scratch.type.bytes / target.bytes⟩
  else .error (.argumentError "cannot reinterpret")

end JuliaLean.SortTuplesCov


/-! Executable branch and mutation models for the optimization pipeline in
`base/sort.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

/-! ### SubArray optimization -/

inductive SubarrayRoute where
  | view | parentVector
  deriving DecidableEq

/-- Generic `SubArrayOptimization`, `base/sort.jl:559`. -/
def subarrayOptimization {R : Type} (next : R) : R := next

/-- Unwrappable SubArray method, `base/sort.jl:560-574`. -/
def unwrappableSubarrayOptimization (parentIsArray parentIsVector : Bool)
    (hi lo offset : Int) : SubarrayRoute :=
  if (parentIsArray && !parentIsVector && hi - lo < 100) || offset ≠ 0 then .view
  else .parentVector

/-! ### WithoutMissingVector -/

/-- Constructor, `base/sort.jl:591-596`. `none` represents `missing`. -/
def withoutMissingVector {V : Type} (data : Array (Option V)) (unsafeFlag : Bool := false) :
    Jl (Array (Option V)) :=
  if !unsafeFlag && data.any (fun x => x.isNone) then
    .error (.argumentError "data must not contain missing values")
  else .ok data

/-- `getindex`, `base/sort.jl:598-602`, including its assertion. -/
def withoutMissingGet {V : Type} (data : Array (Option V)) (i : Int) : Jl V :=
  match JuliaLean.Sort.rd data i with
  | some x => .ok x
  | none => .error (.argumentError "encountered missing in WithoutMissingVector")

/-- `setindex!`, `size`, and `axes`, `base/sort.jl:603-608`. -/
def withoutMissingSet {V : Type} (data : Array (Option V)) (x : V) (i : Int) : Array (Option V) :=
  JuliaLean.Sort.wr data i (some x)
def withoutMissingSize {V : Type} (data : Array (Option V)) : Nat := data.size
def withoutMissingAxes {V : Type} (data : Array (Option V)) : Nat × Nat := (1, data.size)

/-! ### send_to_end! -/

section SendToEnd

variable {V : Type} [Inhabited V]

def sendScan (f : V → Bool) (hi : Int) : Nat → Array V → Int → Array V × Int
  | 0, v, i => (v, i)
  | fuel + 1, v, i =>
    if i ≤ hi && !f (JuliaLean.Sort.rd v i) then sendScan f hi fuel v (i + 1) else (v, i)

def sendLoop (f : V → Bool) (hi : Int) : Nat → Array V → Int → Int → Array V × Int
  | 0, v, i, _ => (v, i)
  | fuel + 1, v, i, j =>
    if j ≤ hi then
      if !f (JuliaLean.Sort.rd v j) then
        let a := JuliaLean.Sort.rd v i
        let b := JuliaLean.Sort.rd v j
        sendLoop f hi fuel (JuliaLean.Sort.wr (JuliaLean.Sort.wr v i b) j a) (i + 1) (j + 1)
      else sendLoop f hi fuel v i (j + 1)
    else (v, i)

/-- `send_to_end!(f, v; lo, hi)`, `base/sort.jl:620-634`. -/
def sendToEnd (f : V → Bool) (v : Array V) (lo hi : Int) : Array V × Int :=
  let first := sendScan f hi (hi - lo + 2).toNat v lo
  let out := sendLoop f hi (hi - first.2 + 1).toNat first.1 first.2 (first.2 + 1)
  (out.1, out.2 - 1)

/-- Direct-order wrappers, `base/sort.jl:645-648`, recorded as the exact
choice of direction, predicate complement, and stability flag. -/
inductive SendRoute where
  | forward (complement reverseView : Bool)
  | reverse (complement reverseView : Bool)
  deriving DecidableEq

def sendToEndRoute (reverseOrder endStable : Bool) : SendRoute :=
  if !reverseOrder then
    if endStable then .forward true true else .forward false false
  else if endStable then .reverse true false else .reverse false true

end SendToEnd

/-! ### Missing and IEEE dispatch -/

inductive MissingRoute where
  | direct | permutation | pass
  deriving DecidableEq

/-- Branch conditions of `MissingOptimization`, `base/sort.jl:651-686`. -/
def missingOptimizationRoute (direct hasMissingEltype perm permDirect integerIndices
    dataHasMissing identityIndices : Bool) : MissingRoute :=
  if direct && hasMissingEltype then .direct
  else if perm && permDirect && integerIndices && dataHasMissing && identityIndices then .permutation
  else .pass

def afterZero (reverse signbit : Bool) : Bool := if reverse then signbit else !signbit
def isConcreteIEEEFloat (isIEEE concrete : Bool) : Bool := isIEEE && concrete

inductive IEEERoute where
  | values | permutation | pass
  deriving DecidableEq

/-- The three branches of `IEEEFloatOptimization`, `base/sort.jl:706-731`. -/
def ieeeOptimizationRoute (valueIEEE direct integerIndices perm permDirect dataIEEE : Bool) : IEEERoute :=
  if valueIEEE && direct then .values
  else if integerIndices && perm && permDirect && dataIEEE then .permutation
  else .pass

/-! ### Bool optimization -/

def fillBoolRange (v : Array Bool) (lo hi : Int) (x : Bool) : Array Bool :=
  (List.range (hi - lo + 1).toNat).foldl
    (fun out (k : Nat) => JuliaLean.Sort.wr out (lo + (k : Int)) x) v

/-- Specialized Bool sort, `base/sort.jl:746-758`. -/
def boolOptimization (lt : Bool → Bool → Bool) (v : Array Bool) (lo hi : Int) : Array Bool :=
  let first := if lt false true then some false else if lt true false then some true else none
  match first with
  | none => v
  | some x =>
    let count := (List.range (hi - lo + 1).toNat).foldl
      (fun n (k : Nat) => if JuliaLean.Sort.rd v (lo + (k : Int)) = x then n + 1 else n) 0
    fillBoolRange (fillBoolRange v lo (lo + count - 1) x) (lo + count) hi (!x)

def boolOptimizationGeneric {R : Type} (next : R) : R := next

end JuliaLean.SortTuplesCov


/-! Algorithm-selection methods from `base/sort.jl` (master
`bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

/-! ### Generic dispatch components -/

def isUIntMappableDispatch {R : Type} (mappable : Bool) (yes no : R) : R :=
  if mappable then yes else no

structure SmallAlgorithm (R : Type) where
  threshold : Int
  small : R
  big : R

/-- `Small{N}(small,big)` and `Small{N}(big)`, `base/sort.jl:793-794`. -/
def smallExplicit {R : Type} (n : Int) (small big : R) : SmallAlgorithm R := ⟨n, small, big⟩
def smallDefault {R : Type} (n : Int) (defaultSmall big : R) : SmallAlgorithm R :=
  smallExplicit n defaultSmall big

/-- `_sort!(..., a::Small{N}, ...)`, `base/sort.jl:795-802`. -/
def smallDispatch {R : Type} (a : SmallAlgorithm R) (lo hi : Int) : R :=
  if hi - lo < a.threshold then a.small else a.big

inductive CheckSortedRoute where
  | alreadySorted | reversed | next
  deriving DecidableEq

/-- `CheckSorted`, `base/sort.jl:864-879`. -/
def checkSortedDispatch (sorted reverseSorted : Bool) (lo hi : Int) : CheckSortedRoute :=
  if sorted then .alreadySorted
  else if hi - lo ≥ 500 && reverseSorted then .reversed
  else .next

inductive StableCheckRoute where
  | alreadySorted | strictlyReversed | next
  deriving DecidableEq

/-- `StableCheckSorted`, `base/sort.jl:1368-1379`. -/
def stableCheckDispatch (sorted strictlyReverseSorted : Bool) : StableCheckRoute :=
  if sorted then .alreadySorted else if strictlyReverseSorted then .strictlyReversed else .next

structure Extrema (V : Type) where
  min : V
  max : V

/-- The loop of `ComputeExtrema`, `base/sort.jl:893-905`. -/
def computeExtremaLoop {V : Type} (lt : V → V → Bool) (v : Array V) :
    Nat → Nat → Extrema V → Extrema V
  | _, 0, e => e
  | i, fuel + 1, e =>
    match v[i]? with
    | none => e
    | some x => computeExtremaLoop lt v (i + 1) fuel
        ⟨if lt x e.min then x else e.min, if lt e.max x then x else e.max⟩

def computeExtrema {V : Type} (lt : V → V → Bool) (v : Array V) : Option (Extrema V) :=
  match v[0]? with
  | none => none
  | some x => some (computeExtremaLoop lt v 1 (v.size - 1) ⟨x, x⟩)

inductive ExtremaRoute where
  | allEquivalent | next
  deriving DecidableEq

def computeExtremaRoute {V : Type} (lt : V → V → Bool) (e : Extrema V) : ExtremaRoute :=
  if lt e.min e.max then .next else .allEquivalent

structure CountingChoice where
  useCounting : Bool
  threshold : Int

/-- `ConsiderCountingSort`, `base/sort.jl:923-933`, after the source's
wrapping range computation. -/
def considerCounting (elementBytes : Nat) (range span : Int) : CountingChoice :=
  let threshold := if elementBytes > 8 then 5 * span - 100 else span / 2
  ⟨range < threshold, threshold⟩

/-- `maybe_reverse`, `base/sort.jl:946-947`. -/
def maybeReverse {V : Type} (reverse : Bool) (xs : List V) : List V :=
  if reverse then xs.reverse else xs

structure RadixChoice where
  useRadix : Bool

/-- `ConsiderRadixSort`, `base/sort.jl:983-992`, with `scaledLog` equal to
the already evaluated source expression `22log(hi-lo)`. -/
def considerRadix (elementBytes bits scaledLog : Nat) : RadixChoice :=
  ⟨elementBytes ≤ 8 && bits + 70 < scaledLog⟩

/-! ### Pipeline construction and defaults -/

inductive PipelineStage where
  | subarray | missing | bool_ | small (n : Int) | ieee | uintMappable
  | checkSorted | computeExtrema | considerCounting | considerRadix
  | stableCheckSorted | insertion | scratchQuick
  deriving Repr, DecidableEq

/-- `InitialOptimizations(next)`, `base/sort.jl:1473-1478`. -/
def initialOptimizationStages (next : List PipelineStage) : List PipelineStage :=
  [.subarray, .missing, .bool_, .small 10, .ieee] ++ next

/-- `_DEFAULT_ALGORITHMS_FOR_VECTORS` and the default `_sort!` method,
`base/sort.jl:1580-1593`. -/
def defaultVectorStages : List PipelineStage :=
  initialOptimizationStages [.uintMappable, .small 40, .checkSorted, .computeExtrema,
    .considerCounting, .considerRadix, .small 80, .scratchQuick, .stableCheckSorted,
    .scratchQuick]

def defaultSortDispatch (_stable : Bool) : List PipelineStage := defaultVectorStages

inductive DefaultAlgorithm where
  | stable | unstable
  deriving DecidableEq

inductive ValueClass where
  | numericArray | missingArray | bottomArray | otherArray | other
  deriving DecidableEq

/-- `defalg`, `base/sort.jl:1620-1624`. -/
def defalg : ValueClass → DefaultAlgorithm
  | .numericArray | .missingArray | .bottomArray => .unstable
  | .otherArray | .other => .stable

/-! ### Algorithm display -/

structure AlgorithmNode where
  typeName : String
  fields : List (String × Option AlgorithmNode)
  depth : Nat

inductive PrintToken where
  | indent (columns : Nat) | typeName (name : String) | openParen | closeParen
  | comma | newline | value (text : String)
  deriving Repr, DecidableEq

/-- `print_tree`, `base/sort.jl:1600-1616`.  Fuel is a structural model
parameter; callers supply more than the nesting depth. -/
def printAlgorithmTree : Nat → AlgorithmNode → Nat → List PrintToken
  | 0, _, _ => []
  | fuel + 1, alg, columns =>
    [.indent columns, .typeName alg.typeName, .openParen] ++
      (alg.fields.zipIdx.flatMap fun (field, i) =>
        (if i > 0 then [.comma] else []) ++
        match field.2 with
        | some child => [.newline] ++ printAlgorithmTree fuel child (columns + 1)
        | none => (if i > 0 then [.value " "] else []) ++ [.value field.1]) ++
      [.closeParen]

/-- `show` calls `print_tree(io, alg, 0)`, `base/sort.jl:1597-1599`. -/
def showAlgorithm (alg : AlgorithmNode) : List PrintToken := printAlgorithmTree (alg.depth + 1) alg 0

/-- `show_type`, `base/sort.jl:1617-1618`. -/
def showAlgorithmType (smallN : Option Int) (name : String) : String :=
  match smallN with
  | none => name
  | some n => "Base.Sort.Small{" ++ toString n ++ "}"

end JuliaLean.SortTuplesCov


/-! Counting-sort and radix-sort kernels from `base/sort.jl` (master
`bbfa0ce4150`).  Values are represented after the source's reversible unsigned
mapping, so the kernels operate on nonnegative bucket offsets. -/

namespace JuliaLean.SortTuplesCov

/-- The count loop of `CountingSort`, `base/sort.jl:948-969`. -/
def countingBuckets (range : Nat) (xs : List Nat) : List Nat :=
  (List.range (range + 1)).map fun bucket => xs.count bucket

/-- Repopulation loop of `CountingSort`. -/
def countingOutput (reverse : Bool) (counts : List Nat) : List Nat :=
  let buckets := (List.range counts.length).flatMap fun i => List.replicate (counts.getD i 0) i
  if reverse then buckets.reverse else buckets

def countingSortMapped (range : Nat) (reverse : Bool) (xs : List Nat) : List Nat :=
  countingOutput reverse (countingBuckets range xs)

/-- A stable radix pass, the observable result of the two loops in
`radix_sort_pass!`, `base/sort.jl:1402-1429`. -/
def radixPass (xs : List Nat) (shift chunkSize : Nat) : List Nat :=
  let bucketCount := 2 ^ chunkSize
  (List.range bucketCount).flatMap fun bucket =>
    xs.filter fun x => ((x >>> shift) % bucketCount) = bucket

structure RadixState where
  inWorking : Bool
  data : List Nat

/-- Alternating passes of `radix_sort!`, `base/sort.jl:1384-1401`.
Fuel exhaustion is a model error. Julia accepts a zero chunk and does not
terminate when `bits > 0`; it still executes one pass when `bits = 0`. -/
def radixSortLoop (bits chunkSize : Nat) :
    Nat → Nat → Bool → List Nat → base.range.JlX RadixState
  | 0, _, _, _ => .error (.errorException "fuel")
  | fuel + 1, shift, inWorking, xs =>
    let ys := radixPass xs shift chunkSize
    let nextShift := shift + chunkSize
    if nextShift ≥ bits then .ok ⟨!inWorking, ys⟩
    else radixSortLoop bits chunkSize fuel nextShift (!inWorking) ys

def radixSort (xs : List Nat) (bits chunkSize : Nat) : base.range.JlX RadixState :=
  radixSortLoop bits chunkSize (bits + 1) 0 true xs

/-- `radix_chunk_size_heuristic`, `base/sort.jl:1430-1441`.  `guess` is the
source expression `min(10, log(hi-lo)*3/4+3)` after evaluation. -/
def radixChunkSizeHeuristic (bits guess : Nat) : Nat :=
  if bits = 0 then 0 else (bits + ((bits + guess - 1) / guess) - 1) / ((bits + guess - 1) / guess)

/-- The two `maybe_unsigned` methods, `base/sort.jl:1443-1444`. -/
def maybeUnsignedInteger (x : Int) : Int := x
def maybeUnsignedBitSigned (bits : Nat) (x : Int) : Int :=
  x % (2 ^ bits : Nat)

end JuliaLean.SortTuplesCov


/-! Public sorting wrappers, tuple merge sort, permutation wrappers, and
multidimensional routing from `base/sort.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

/-! ### Vector and tuple sort wrappers -/

/-- `sort!(v; ...)`, `base/sort.jl:1732-1741`, after `ord` and
`maybe_apply_initial_optimizations` have been evaluated. -/
def sortVectorBang {V : Type} (core : List V → List V) (v : List V) : List V := core v

/-- `sort(v::AbstractVector; kws...)`, `base/sort.jl:1780`.  The pair records
that the source is unchanged and the copied result is sorted. -/
def sortVectorCopy {V : Type} (core : List V → List V) (v : List V) : List V × List V :=
  (v, core v)

/-- `sort` on KeySet and ValueIterator, `base/sort.jl:1782-1783`. -/
def sortCollected {V : Type} (collect : List V) (core : List V → List V) : List V := core collect

/-- Tuple `merge`, `base/sort.jl:1814-1818`. -/
def mergeSorted {V : Type} (lt : V → V → Bool) : List V → List V → List V
  | xs, [] => xs
  | [], ys => ys
  | x :: xs, y :: ys =>
    if lt y x then y :: mergeSorted lt (x :: xs) ys
    else x :: mergeSorted lt xs (y :: ys)
termination_by xs ys => xs.length + ys.length

/-- `_mergesort(x::NTuple, o)`, `base/sort.jl:1809-1813`, with fuel equal to
the tuple length. -/
def tupleMergeSort {V : Type} (lt : V → V → Bool) : Nat → List V → List V
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, xs =>
    let n := xs.length / 2
    mergeSorted lt (tupleMergeSort lt fuel (xs.take n)) (tupleMergeSort lt fuel (xs.drop n))

/-- Default tuple `_sort`, `base/sort.jl:1798-1808`. -/
def sortTupleDefault {V : Type} (vectorCore : List V → List V)
    (lt : V → V → Bool) (xs : List V) : List V :=
  if xs.length > 9 then vectorCore xs else tupleMergeSort lt (xs.length + 1) xs

/-! ### Permutation wrappers -/

inductive SortpermRoute where
  | integerRangeFastPath | generic
  deriving DecidableEq

/-- `sortperm`, `base/sort.jl:1966-1979`: explicit branching on `rev`. -/
def sortpermOrderingChoice (rev : RevChoice) : Bool := reverseRequested rev

/-- `_sortperm`, `base/sort.jl:1980-1994`, after extrema and overflow checks. -/
def sortpermRoute (forward vector integerElements moreThanOne noOverflow shortRange : Bool) :
    SortpermRoute :=
  if forward && vector && integerElements && moreThanOne && noOverflow && shortRange then
    .integerRangeFastPath
  else .generic

/-- `sortperm!`, `base/sort.jl:2037-2055`, recording validation and the
initialized linear indices. -/
def sortpermBang (axesMatch vectorDimsConflict : Bool) (length : Nat) : Except String (List Nat) :=
  if vectorDimsConflict then .error "Dims argument incorrect for type"
  else if !axesMatch then .error "index array must have the same axes"
  else .ok ((List.range length).map (.+1))

/-- `partialsortperm!`, `base/sort.jl:1896-1915`, including the axes check and
unconditional index initialization (`initialized` is accepted but unused). -/
def partialsortpermBang (axesMatch initialized : Bool) (length : Nat) : Except String (List Nat) :=
  if !axesMatch then .error "index vector must have the same axes"
  else
    let _ := initialized
    .ok ((List.range length).map (.+1))

/-! ### Multidimensional sorting -/

inductive ArraySortRoute where
  | firstDimension | permutedDimension
  deriving DecidableEq

/-- `sort(A; dims)`, `base/sort.jl:2112-2134`. -/
def arraySortRoute (dimension : Int) : ArraySortRoute :=
  if dimension = 1 then .firstDimension else .permutedDimension

inductive ChunkScratchRoute where
  | noScratch | acquiredScratch | reusedScratch
  deriving DecidableEq

/-- The three `sort_chunks!` methods, `base/sort.jl:2136-2154`. -/
def sortChunksRoute (scratchPresent nestedProducedScratch : Bool) : ChunkScratchRoute :=
  if scratchPresent then .reusedScratch
  else if nestedProducedScratch then .acquiredScratch else .noScratch

/-- Local `get_view` and `get_value`, `base/sort.jl:2205-2206,2224`. -/
def getViewIndices (selectedDimension : Nat) (idx : List Nat) (ndims : Nat) : List (Option Nat) :=
  (List.range ndims).map fun i => if i + 1 = selectedDimension then none else idx[i]?
def getValue (x : Nat) : Nat := x

end JuliaLean.SortTuplesCov


/-! Unsigned order-preserving mappings from `base/sort.jl:2227-2310`
(master `bbfa0ce4150`).  A bit integer is its fixed-width bit pattern. -/

namespace JuliaLean.SortTuplesCov

def wordMask (bits : Nat) : Nat := 2 ^ bits - 1
def signMask (bits : Nat) : Nat := 2 ^ (bits - 1)

/-- Unsigned Forward methods, `base/sort.jl:2267-2268`. -/
def uintMapUnsigned (word : Nat) : Nat := word
def uintUnmapUnsigned (word : Nat) : Nat := word

/-- Signed Forward methods, `base/sort.jl:2270-2273`. -/
def uintMapSigned (bits word : Nat) : Nat := word ^^^ signMask bits
def uintUnmapSigned (bits word : Nat) : Nat := word ^^^ signMask bits

/-- Char methods, `base/sort.jl:2282-2284`: reinterpret to and from UInt32. -/
def uintMapChar (code : UInt32) : UInt32 := code
def uintUnmapChar (word : UInt32) : UInt32 := word

/-- ReverseOrdering methods, `base/sort.jl:2287-2289`. -/
def uintMapReverse (bits : Nat) (forward : Nat → Nat) (word : Nat) : Nat :=
  wordMask bits ^^^ forward word
def uintUnmapReverse (bits : Nat) (forwardUnmap : Nat → Nat) (word : Nat) : Nat :=
  forwardUnmap (wordMask bits ^^^ word)

inductive UIntMapType where
  | bits (width : Nat) | char | unsupported
  deriving DecidableEq

/-- `UIntMappable`, including fallback, Forward bit integers and Char, and
ReverseOrdering forwarding, `base/sort.jl:2237,2275,2284,2289`. -/
def uintMappable : UIntMapType → Bool → Option Nat
  | .bits width, _ => some width
  | .char, _ => some 32
  | .unsupported, _ => none

/-! ### Vector mapping loops -/

def uintMapLoop (map : Nat → Nat) (lo : Int) : Nat → Array Nat → Array Nat
  | 0, v => v
  | fuel + 1, v =>
    let i := lo + fuel
    uintMapLoop map lo fuel (JuliaLean.Sort.wr v i (map (JuliaLean.Sort.rd v i)))

/-- `uint_map!`, `base/sort.jl:2295-2301`. -/
def uintMapBang (map : Nat → Nat) (v : Array Nat) (lo hi : Int) : Array Nat :=
  uintMapLoop map lo (hi - lo + 1).toNat v

def uintUnmapLoop (unmap : Nat → Nat) (offset : Nat) (lo indexOffset : Int) :
    Nat → Array Nat → Array Nat → Array Nat
  | 0, v, _ => v
  | fuel + 1, v, u =>
    let i := lo + fuel
    uintUnmapLoop unmap offset lo indexOffset fuel
      (JuliaLean.Sort.wr v i (unmap (JuliaLean.Sort.rd u (i + indexOffset) + offset))) u

/-- `uint_unmap!`, `base/sort.jl:2303-2310`. -/
def uintUnmapBang (unmap : Nat → Nat) (v u : Array Nat) (lo hi : Int)
    (offset : Nat := 0) (indexOffset : Int := 0) : Array Nat :=
  uintUnmapLoop unmap offset lo indexOffset (hi - lo + 1).toNat v u

/-! ### Legacy algorithm wrapping -/

inductive PublicAlg where
  | quick | merge | insertion | other
  deriving DecidableEq

/-- `maybe_apply_initial_optimizations`, `base/sort.jl:2396-2399`. -/
def maybeApplyInitialOptimizations : PublicAlg → Bool
  | .quick | .merge | .insertion => true
  | .other => false

end JuliaLean.SortTuplesCov


/-! Legacy QuickSort, MergeSort, and PartialQuickSort kernels from
`base/sort.jl:2401-2595` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

section

variable {V : Type} [Inhabited V]

def midpointInt (lo hi : Int) : Int := lo + (hi - lo) / 2

/-- `selectpivot!`, `base/sort.jl:2409-2429`. -/
def selectPivot (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V × V :=
  let mi := midpointInt lo hi
  let v := if lt (JuliaLean.Sort.rd v lo) (JuliaLean.Sort.rd v mi) then
    let a := JuliaLean.Sort.rd v lo
    let b := JuliaLean.Sort.rd v mi
    JuliaLean.Sort.wr (JuliaLean.Sort.wr v mi a) lo b else v
  let v := if lt (JuliaLean.Sort.rd v hi) (JuliaLean.Sort.rd v lo) then
    if lt (JuliaLean.Sort.rd v hi) (JuliaLean.Sort.rd v mi) then
      let a := JuliaLean.Sort.rd v hi
      let b := JuliaLean.Sort.rd v lo
      let c := JuliaLean.Sort.rd v mi
      JuliaLean.Sort.wr (JuliaLean.Sort.wr (JuliaLean.Sort.wr v hi b) lo c) mi a
    else
      let a := JuliaLean.Sort.rd v hi
      let b := JuliaLean.Sort.rd v lo
      JuliaLean.Sort.wr (JuliaLean.Sort.wr v hi b) lo a
    else v
  (v, JuliaLean.Sort.rd v lo)

def scanLess (lt : V → V → Bool) (pivot : V) : Nat → Array V → Int → Int
  | 0, _, i => i
  | fuel + 1, v, i => if lt (JuliaLean.Sort.rd v i) pivot then scanLess lt pivot fuel v (i + 1) else i

def scanGreater (lt : V → V → Bool) (pivot : V) : Nat → Array V → Int → Int
  | 0, _, j => j
  | fuel + 1, v, j => if lt pivot (JuliaLean.Sort.rd v j) then scanGreater lt pivot fuel v (j - 1) else j

def partitionLoop (lt : V → V → Bool) (pivot : V) (lo : Int) :
    Nat → Array V → Int → Int → Array V × Int
  | 0, v, _, j => (JuliaLean.Sort.wr (JuliaLean.Sort.wr v j pivot) lo (JuliaLean.Sort.rd v j), j)
  | fuel + 1, v, i, j =>
    let i := scanLess lt pivot fuel v (i + 1)
    let j := scanGreater lt pivot fuel v (j - 1)
    if i ≥ j then (JuliaLean.Sort.wr (JuliaLean.Sort.wr v j pivot) lo (JuliaLean.Sort.rd v j), j)
    else
      let a := JuliaLean.Sort.rd v i
      let b := JuliaLean.Sort.rd v j
      partitionLoop lt pivot lo fuel (JuliaLean.Sort.wr (JuliaLean.Sort.wr v i b) j a) i j

/-- Old `partition!`, `base/sort.jl:2435-2452`. -/
def legacyPartition (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V × Int :=
  let p := selectPivot lt v lo hi
  partitionLoop lt p.2 lo (hi - lo + 2).toNat p.1 lo hi

/-- `_quicksort!`, `base/sort.jl:2459-2478`. -/
def quickSortLoop (lt : V → V → Bool) : Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, lo, hi =>
    if lo < hi then
      if hi - lo ≤ 20 then JuliaLean.Sort.insertionSort lt v lo hi
      else
        let p := legacyPartition lt v lo hi
        let j := p.2
        if j - lo < hi - j then
          let w := if lo < j - 1 then quickSortLoop lt fuel p.1 lo (j - 1) else p.1
          quickSortLoop lt fuel w (j + 1) hi
        else
          let w := if j + 1 < hi then quickSortLoop lt fuel p.1 (j + 1) hi else p.1
          quickSortLoop lt fuel w lo (j - 1)
    else v

def quickSort (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V :=
  quickSortLoop lt (hi - lo + 2).toNat v lo hi

def copyLeftLoop (v : Array V) (lo : Int) : Nat → Array V → Array V
  | 0, t => t
  | fuel + 1, t => copyLeftLoop v lo fuel (JuliaLean.Sort.wr t (fuel + 1) (JuliaLean.Sort.rd v (lo + fuel)))

def mergeMainLoop (lt : V → V → Bool) (hi : Int) :
    Nat → Array V → Array V → Int → Int → Int → Array V × Int × Int × Int
  | 0, v, _, i, j, k => (v, i, j, k)
  | fuel + 1, v, t, i, j, k =>
    if k < j && j ≤ hi then
      if lt (JuliaLean.Sort.rd v j) (JuliaLean.Sort.rd t i) then
        mergeMainLoop lt hi fuel (JuliaLean.Sort.wr v k (JuliaLean.Sort.rd v j)) t i (j + 1) (k + 1)
      else
        mergeMainLoop lt hi fuel (JuliaLean.Sort.wr v k (JuliaLean.Sort.rd t i)) t (i + 1) j (k + 1)
    else (v, i, j, k)

def mergeRemainder (t : Array V) : Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, i, k => mergeRemainder t fuel (JuliaLean.Sort.wr v k (JuliaLean.Sort.rd t i)) (i + 1) (k + 1)

/-- `_mergesort!`, `base/sort.jl:2488-2531`. -/
def mergeSortLoop (lt : V → V → Bool) : Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, lo, hi =>
    if lo < hi then
      if hi - lo ≤ 20 then JuliaLean.Sort.insertionSort lt v lo hi
      else
        let m := midpointInt lo hi
        let v := mergeSortLoop lt fuel v lo m
        let v := mergeSortLoop lt fuel v (m + 1) hi
        let leftLength := (m - lo + 1).toNat
        let t := copyLeftLoop v lo leftLength (Array.replicate leftLength default)
        let r := mergeMainLoop lt hi (hi - lo + 1).toNat v t 1 (m + 1) lo
        mergeRemainder t (r.2.2.2 - r.2.1).toNat r.1 r.2.1 r.2.2.2
    else v

def mergeSort (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Array V :=
  mergeSortLoop lt (hi - lo + 2).toNat v lo hi

/-- `_partialquicksort!`, `base/sort.jl:2539-2566`. -/
def partialQuickSortLoop (lt : V → V → Bool) (firstTarget lastTarget : Int) :
    Nat → Array V → Int → Int → Array V
  | 0, v, _, _ => v
  | fuel + 1, v, lo, hi =>
    if lo < hi then
      if hi - lo ≤ 20 then JuliaLean.Sort.insertionSort lt v lo hi
      else
        let p := legacyPartition lt v lo hi
        let j := p.2
        if j ≤ firstTarget then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 (j + 1) hi
        else if j ≥ lastTarget then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 lo (j - 1)
        else if j - lo < hi - j then
          let w := if lo < j - 1 then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 lo (j - 1) else p.1
          partialQuickSortLoop lt firstTarget lastTarget fuel w (j + 1) hi
        else
          let w := if j + 1 < hi then partialQuickSortLoop lt firstTarget lastTarget fuel p.1 (j + 1) hi else p.1
          partialQuickSortLoop lt firstTarget lastTarget fuel w lo (j - 1)
    else v

def partialQuickSort (lt : V → V → Bool) (firstTarget lastTarget : Int)
    (v : Array V) (lo hi : Int) : Array V :=
  partialQuickSortLoop lt firstTarget lastTarget (hi - lo + 2).toNat v lo hi

end

end JuliaLean.SortTuplesCov


/-! Remaining behavioral methods in `base/sort.jl` (master `bbfa0ce4150`):
BracketedSort helpers, the RadixSort wrapper, the integer-range permutation
fast path, and the legacy entry-point wrappers. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

/-! ### BracketedSort -/

structure BracketKernelResult where
  countBelow : Nat
  lastMiddle : Nat
  selected : List Bool

/-- The predicates and counters of `bracket_kernel!`,
`base/sort.jl:1226-1246`. -/
def bracketKernel {V : Type} (lt : V → V → Bool) (xs : List V)
    (loSign hiSign : Option V) : BracketKernelResult :=
  let flags := xs.map fun x =>
    let below := loSign.any fun s => lt x s
    let atMostHigh := hiSign.elim true fun s => !lt s x
    below != atMostHigh
  ⟨(xs.filter fun x => loSign.any fun s => lt x s).length,
    flags.count true, flags⟩

/-- `move!`, `base/sort.jl:1248-1262`, represented by the exact route because
the method either swaps disjoint pairs or performs its two range reversals. -/
inductive MoveRoute where
  | pairSwaps | overlappingReversals | lengthError | rangeError
  deriving DecidableEq

def moveRoute (targetLength sourceLength : Nat) (single disjoint rangeOrdered : Bool) : MoveRoute :=
  if targetLength ≠ sourceLength then .lengthError
  else if single || disjoint then .pairSwaps
  else if rangeOrdered then .overlappingReversals else .rangeError

inductive BracketedRoute where
  | emptyWindow | smallFallback | heuristicFallback | successfulTrial | finalFallback
  deriving DecidableEq

/-- Control flow of `_sort!(..., a::BracketedSort, ...)`,
`base/sort.jl:1264-1353`, after its scalar estimates and three trials have been
evaluated. -/
def bracketedSortRoute (lo hi length : Int) (heuristicFallback trialSucceeded : Bool) :
    BracketedRoute :=
  if !(lo < hi) then .emptyWindow
  else if length < 260 then .smallFallback
  else if heuristicFallback then .heuristicFallback
  else if trialSucceeded then .successfulTrial
  else .finalFallback

/-! ### RadixSort wrapper -/

structure RadixWrapperTrace where
  mapped : Bool
  subtractedMinimum : Bool
  madeScratch : Bool
  radixPasses : Bool
  unmapped : Bool
  deriving DecidableEq

/-- `_sort!(v, a::RadixSort, o, kw)`, `base/sort.jl:1017-1047`. -/
def radixSortWrapper (_bits : Nat) : RadixWrapperTrace :=
  ⟨true, true, true, true, true⟩

/-! ### Integer-range sortperm fast path -/

/-- `sortperm_int_range`, `base/sort.jl:2058-2081`: stable bucket order for
the labels `x[i] - minval`. -/
def sortpermIntRange (x : List Int) (rangeLength : Nat) (minValue : Int) : List Nat :=
  (List.range rangeLength).flatMap fun label =>
    ((List.range x.length).zip x).filterMap fun (i, value) =>
      if value - minValue = (label : Int) then some (i + 1) else none

/-! ### Legacy entry wrappers -/

def checkedLegacyEntry {V : Type} (boundsOK : Bool) (result : Array V) : Jl (Array V) :=
  if boundsOK then .ok result else .error .boundsError

/-- QuickSort five-argument entry, `base/sort.jl:2454-2457`. -/
def quickSortEntry {V : Type} [Inhabited V] (boundsOK : Bool) (lt : V → V → Bool)
    (v : Array V) (lo hi : Int) : Jl (Array V) :=
  checkedLegacyEntry boundsOK (quickSort lt v lo hi)

/-- MergeSort vector disambiguation and main entry, `base/sort.jl:2480-2486`. -/
def mergeSortEntry {V : Type} [Inhabited V] (boundsOK : Bool) (lt : V → V → Bool)
    (v : Array V) (lo hi : Int) : Jl (Array V) :=
  checkedLegacyEntry boundsOK (mergeSort lt v lo hi)
def mergeSortVectorEntry {V : Type} [Inhabited V] (boundsOK : Bool)
    (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Jl (Array V) :=
  mergeSortEntry boundsOK lt v lo hi

/-- PartialQuickSort five-argument entry, `base/sort.jl:2533-2537`. -/
def partialQuickSortEntry {V : Type} [Inhabited V] (boundsOK : Bool)
    (lt : V → V → Bool) (firstTarget lastTarget : Int)
    (v : Array V) (lo hi : Int) : Jl (Array V) :=
  checkedLegacyEntry boundsOK (partialQuickSort lt firstTarget lastTarget v lo hi)

/-- Generic three-, five-, and ignored-sixth-argument entries,
`base/sort.jl:2571-2577`. -/
def legacyThreeArg {V A O : Type} (five : Array V → Int → Int → A → O → Jl (Array V))
    (v : Array V) (a : A) (o : O) : Jl (Array V) := five v 1 v.size a o
def legacyFiveArg {V A O : Type} (boundsOK : Bool)
    (newSort : Array V → A → O → Jl (Array V)) (v : Array V) (a : A) (o : O) :
    Jl (Array V) := if boundsOK then newSort v a o else .error .boundsError
def legacyIgnoredScratch {V A O S : Type}
    (five : Array V → Int → Int → A → O → Jl (Array V))
    (v : Array V) (lo hi : Int) (a : A) (o : O) (_ : S) : Jl (Array V) :=
  five v lo hi a o

end JuliaLean.SortTuplesCov
