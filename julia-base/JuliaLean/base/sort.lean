import JuliaLean.Core
import JuliaLean.Registry.Types

/-!
# Source-mirrored model of `base/sort.jl`

Julia revision `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform. Abstract-vector
reads, ordering operations, and finite-iterator operations are typed parameters for interfaces
provided by other Base files. Integer search locals retain Julia's BitInteger widths and promotion.
-/

namespace JuliaLean.base.sort

open JuliaLean

structure FiniteIterator (I α St : Type) where
  first : I → Option (α × St)
  next : I → St → Option (α × St)
  rank : I → St → Nat
  decreases : ∀ (itr : I) (state : St) (x : α) (state' : St),
    next itr state = some (x, state') → rank itr state' < rank itr state

def issortedLoop {I α St O : Type} (iter : FiniteIterator I α St)
    (lt : O → α → α → Bool) (order : O) (itr : I) :
    Nat → α → St → Bool
  | 0, _, _ => true
  | fuel + 1, prev, state =>
    match iter.next itr state with
    | none => true
    | some (this, nextState) =>
      if lt order this prev then false
      else issortedLoop iter lt order itr fuel this nextState

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
def issorted {I α St O : Type} (iter : FiniteIterator I α St)
    (lt : O → α → α → Bool) (order : O) (itr : I) : Bool :=
  let y := iter.first itr
  match y with
  | none => true
  | some (prev, state) =>
    let y := iter.next itr state
    match y with
    | none => true
    | some (this, nextState) =>
      if lt order this prev then false
      else issortedLoop iter lt order itr (iter.rank itr nextState) this nextState

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
def issortedKeywords {I α St L B O : Type} (iter : FiniteIterator I α St)
    (orderOf : L → B → Option Bool → O → O)
    (lt : O → α → α → Bool) (itr : I) (less : L) (byFn : B)
    (rev : Option Bool) (order : O) : Bool :=
  if rev = some true then
    issorted iter lt (orderOf less byFn (some true) order) itr
  else
    issorted iter lt (orderOf less byFn none order) itr

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
  deriving Repr, DecidableEq

structure VectorOps (V α : Type) where
  read : V → Int → Option α

def arrayVectorOps : VectorOps (Array α) α where
  read := fun v i =>
    if 1 ≤ i ∧ i ≤ v.size then v[i.toNat - 1]? else none
def arrayFirstIndex {α : Type} (_v : Array α) : JInt .i64 := JInt.wrap .i64 1

def arrayLastIndex {α : Type} (v : Array α) : JInt .i64 := JInt.wrap .i64 v.size

def firstSearchLoop {V α O : Type} (ops : VectorOps V α)
    (lt : O → α → α → Bool) (order : O) (v : V) (x : α) :
    Nat → SearchIndex → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _, _ => .exhausted
  | fuel + 1, lo, hi, len =>
    if len.val = 0 then .returned lo.val else
    let half := indexHalf len
    let m := indexAdd lo half
    match ops.read v m.val with
    | none => .invalidAccess m.val
    | some value =>
      if lt order value x then
        firstSearchLoop ops lt order v x fuel
          (indexAdd m (searchIndex .i64 1)) hi
          (indexSub len (indexAdd half (searchIndex .i64 1)))
      else firstSearchLoop ops lt order v x fuel lo m half

def lastSearchLoop {V α O : Type} (ops : VectorOps V α)
    (lt : O → α → α → Bool) (order : O) (v : V) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then .returned lo.val else
    let m := indexMidpoint lo hi
    match ops.read v m.val with
    | none => .invalidAccess m.val
    | some value =>
      if lt order x value then lastSearchLoop ops lt order v x u fuel lo m
      else lastSearchLoop ops lt order v x u fuel m hi

def equalSearchLoop {V α O : Type} (ops : VectorOps V α)
    (lt : O → α → α → Bool) (order : O) (v : V) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult (Int × Int)
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then
      .returned ((indexAdd lo (searchIndex .i64 1)).val,
        (indexSub hi (searchIndex .i64 1)).val)
    else
      let m := indexMidpoint lo hi
      match ops.read v m.val with
      | none => .invalidAccess m.val
      | some value =>
        if lt order value x then equalSearchLoop ops lt order v x u fuel m hi
        else if lt order x value then equalSearchLoop ops lt order v x u fuel lo m
        else
          let start := indexAdd lo u
          let firstHi := indexAdd m (searchIndex m.ty 1)
          let firstLen := indexSub firstHi start
          match firstSearchLoop ops lt order v x (firstLen.val.toNat + 2) start
              firstHi firstLen
          with
          | .invalidAccess i => .invalidAccess i
          | .exhausted => .exhausted
          | .returned first =>
            let lastLo := indexSub m (searchIndex m.ty 1)
            let lastHi := indexAdd (indexSub hi u) (searchIndex m.ty 1)
            match lastSearchLoop ops lt order v x (searchIndex m.ty 1)
                ((indexSub lastHi lastLo).val.toNat + 2) lastLo lastHi
            with
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
    (lt : O → α → α → Bool) (order : O) (v : V) (x : α)
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
    (lt : O → α → α → Bool) (order : O) (v : V) (x : α)
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
    (lt : O → α → α → Bool) (order : O) (v : V) (x : α)
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
    (ops : RealRangeOps A R X Q K O E) (lt : O → X → R → Bool)
    (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if lt order x f then
    pure ops.zeroIndex
  else if ops.isZero h || !(lt order x l) then
    pure (ops.length a)
  else
    let quotient := ops.divide (ops.subtract x f) h
    let n ← ops.roundInteger (ops.addOne quotient)
    if lt order x (← ops.get a n) then pure (ops.decrement n) else pure n

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
    (ltRange : O → R → X → Bool) (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if !(ltRange order f x) then
    pure ops.oneIndex
  else if ops.isZero h || ltRange order l x then
    pure (ops.increment (ops.length a))
  else
    let quotient := ops.divide (ops.subtract x f) h
    let n ← ops.roundInteger (ops.addOne quotient)
    if ltRange order (← ops.get a n) x then pure (ops.increment n) else pure n

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
    (ops : IntegerRangeOps A R X Q K O E) (lt : O → X → R → Bool)
    (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if lt order x f then
    pure ops.zeroIndex
  else if ops.isZero h || !(lt order x l) then
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
    (ltRange : O → R → X → Bool) (order : O) (a : A) (x : X) : Except E K := do
  ops.requireOneBased a
  let f := ops.first a
  let h := ops.step a
  let l := ops.last a
  if !(ltRange order f x) then
    pure ops.oneIndex
  else if ops.isZero h || ltRange order l x then
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
    (ops : RealRangeOps A R X Q K O E) (lt : O → X → R → Bool)
    (ltRange : O → R → X → Bool) (order : O) (a : A)
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
    (ops : IntegerRangeOps A R X Q K O E) (lt : O → X → R → Bool)
    (ltRange : O → R → X → Bool) (order : O) (a : A)
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
    (firstIndex lastIndex : V → JInt t) (lt : O → α → α → Bool)
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
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → Bool)
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
    (firstIndex lastIndex : V → JInt t) (lt : O → α → α → Bool)
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
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → Bool)
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
    (firstIndex lastIndex : V → JInt t) (lt : O → α → α → Bool)
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
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → Bool)
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
    (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → Bool)
    (v : V) (x : α) (less : L) (byFn : B) (rev : Option Bool) (order : O) :
    SearchResult Bool :=
  match searchsortedKeywords ops firstIndex lastIndex orderOf lt v x less byFn rev order with
  | .returned (first, last) => .returned (first ≤ last)
  | .invalidAccess index => .invalidAccess index
  | .exhausted => .exhausted

/--
Julia source: base/sort.jl:466-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
insorted(x, r::AbstractRange) = in(x, r)
```
-/
def insortedRange {R X : Type} (contains : X → R → Bool) (x : X) (range : R) : Bool :=
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

def sendToEndFirstScan [Monad m] (ops : SendToEndOps m V α K)
    (predicate : α → m Bool) (v : V) (hi : K) : Nat → K → m K
  | 0, i => pure i
  | fuel + 1, i =>
    if ops.lessEq i hi then do
      let value ← ops.get v i
      let sent ← predicate value
      if sent then pure i
      else sendToEndFirstScan ops predicate v hi fuel (ops.next i)
    else pure i

def sendToEndSecondScan [Monad m] (ops : SendToEndOps m V α K)
    (predicate : α → m Bool) (v : V) (hi : K) : Nat → K → K → m K
  | 0, i, _ => pure i
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
def withoutMissingVector {V α E : Type} (hasMissing : V → Bool)
    (argumentError : String → E) (data : V) (unsafeMode : Bool := false) :
    Except E (WithoutMissingVector α V) :=
  if !unsafeMode && hasMissing data then
    .error (argumentError "data must not contain missing values")
  else .ok ⟨data⟩

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
def generatedKeywordGetter {W A V O E : Type}
    (lookup : W → Option A) (append : W → A → W)
    (default : V → O → Except E A) (assertType : A → Except E A)
    (keywords : W) (v : V) (order : O) : Except E (W × A) := do
  match lookup keywords with
  | some value =>
    let typed ← assertType value
    pure (keywords, typed)
  | none =>
    let value ← default v order
    let typed ← assertType value
    pure (append keywords value, typed)

structure IntegerIndexOps (K : Type) where
  addOne : K → K
  previous : K → K
  range : K → K → List K
  less : K → K → Bool

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
def issortedWindow {V α K O E : Type} (indices : IntegerIndexOps K)
    (checkBounds : V → K → K → Except E Unit) (get : V → K → Except E α)
    (lt : O → α → α → Bool) (v : V) (lo hi : K) (order : O) : Except E Bool := do
  checkBounds v lo hi
  for i in indices.range (indices.addOne lo) hi do
    let current ← get v i
    let previous ← get v (indices.previous i)
    if lt order current previous then return false
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
structure SortpermRangeOps (V T C P E : Type) where
  length : V → Int
  read : V → Int → Except E T
  wrapAdd : T → T → T
  wrapSub : T → T → T
  one : T
  toIndex : T → Int
  allocateCounts : Int → Except E C
  countLength : C → Int
  getCount : C → Int → Except E Int
  setCount : C → Int → Int → Except E C
  allocatePermutation : Int → Except E P
  getPermutation : P → Int → Except E Int
  setPermutation : P → Int → Int → Except E P
  lessEqual : T → T → Bool
  equal : T → T → Bool
  range : Int → Int → List Int

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
def sortpermIntRange {V T C P E : Type} (ops : SortpermRangeOps V T C P E)
    (x : V) (rangeLength : Int) (minValue : T) : Except E P := do
  let offsets := ops.wrapSub ops.one minValue
  let n := ops.length x
  let mut counts ← ops.allocateCounts (rangeLength + 1)
  counts ← ops.setCount counts 1 1
  for i in ops.range 1 n do
    let value ← ops.read x i
    let bucket := ops.toIndex (ops.wrapAdd (ops.wrapAdd value offsets) ops.one)
    let count ← ops.getCount counts bucket
    counts ← ops.setCount counts bucket (count + 1)
  for i in ops.range 2 (ops.countLength counts) do
    let count ← ops.getCount counts i
    let previous ← ops.getCount counts (i - 1)
    counts ← ops.setCount counts i (count + previous)
  let mut permutation ← ops.allocatePermutation n
  for i in ops.range 1 n do
    let value ← ops.read x i
    let label := ops.toIndex (ops.wrapAdd value offsets)
    let target ← ops.getCount counts label
    permutation ← ops.setPermutation permutation target i
    let count ← ops.getCount counts label
    counts ← ops.setCount counts label (count + 1)
  pure permutation
private def wrapInt64 (value : Int) : Int :=
  (JInt.wrap .i64 value).val

private def readIntArray (array : Array Int) (index : Int) : Except JlError Int :=
  if 1 ≤ index ∧ index ≤ array.size then
    match array[index.toNat - 1]? with
    | some value => .ok value
    | none => .error .boundsError
  else .error .boundsError

private def writeIntArray (array : Array Int) (index value : Int) :
    Except JlError (Array Int) :=
  if 1 ≤ index ∧ index ≤ array.size then
    .ok (array.set! (index.toNat - 1) value)
  else .error .boundsError

def sortpermIntArrayOps : SortpermRangeOps (Array Int) Int (Array Int) (Array Int) JlError where
  length := fun x => x.size
  read := readIntArray
  wrapAdd := fun a b => wrapInt64 (a + b)
  wrapSub := fun a b => wrapInt64 (a - b)
  one := 1
  toIndex := id
  allocateCounts := fun n =>
    if 0 ≤ n then .ok (Array.replicate n.toNat 0) else .error .boundsError
  countLength := fun counts => counts.size
  getCount := readIntArray
  setCount := writeIntArray
  allocatePermutation := fun n =>
    if 0 ≤ n then .ok (Array.replicate n.toNat 0) else .error .boundsError
  getPermutation := readIntArray
  setPermutation := writeIntArray
  lessEqual := fun a b => decide (a ≤ b)
  equal := fun a b => decide (a = b)
  range := fun lo hi =>
    (List.range ((hi - lo + 1).toNat)).map fun offset => lo + Int.ofNat offset

structure VectorMutationOps (m : Type → Type) (V α K : Type) where
  get : V → K → m α
  set : V → α → K → m Unit
  indices : IntegerIndexOps K
  distance : K → K → Nat

def insertionShift [Monad m] (ops : VectorMutationOps m V α K)
    (lt : O → α → α → Bool) (order : O) (v : V) (lo : K) (value : α) :
    Nat → K → m K
  | 0, j => pure j
  | fuel + 1, j =>
    if ops.indices.less lo j then do
      let previous := ops.indices.previous j
      let other ← ops.get v previous
      if lt order value other then do
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
    (lt : O → α → α → Bool) (order : O) (v : V) (lo hi : K) (scratch : S) : m S := do
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
structure RadixChunkHeuristicOps (K U Bits E : Type) where
  subtract : K → K → K
  maybeUnsigned : K → U
  log : U → Float
  fromNat : Nat → Float
  min : Float → Float → Float
  multiply : Float → Float → Float
  divide : Float → Float → Float
  add : Float → Float → Float
  ceilingDiv : Nat → Float → Float
  bitsToNat : Bits → Nat
  toUInt8 : Float → Except E UInt8

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
def radixChunkSizeHeuristic {K U Bits E : Type}
    (ops : RadixChunkHeuristicOps K U Bits E) (lo hi : K) (bits : Bits) :
    Except E UInt8 := do
  let difference := ops.subtract hi lo
  let guess := ops.min (ops.fromNat 10)
    (ops.add (ops.divide (ops.multiply (ops.log (ops.maybeUnsigned difference))
      (ops.fromNat 3)) (ops.fromNat 4)) (ops.fromNat 3))
  let bitCount := ops.bitsToNat bits
  let inner := ops.ceilingDiv bitCount guess
  ops.toUInt8 (ops.ceilingDiv bitCount inner)

structure RadixSortPassOps (V C K U E : Type) where
  mask : UInt8 → U
  bucketIndex : U → Nat → U → Nat → Nat
  zeroCounts : C → Except E C
  read : V → K → Except E U
  write : V → K → U → Except E V
  range : K → K → List K
  readCount : C → Nat → Except E Int
  writeCount : C → Nat → Int → Except E C
  setFirstTarget : C → K → Except E C
  prefixSum : C → Except E C
  addIndex : K → K → K
  toIndex : Int → K

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
def radixSortPass {V C K U E : Type}
    (ops : RadixSortPassOps V C K U E)
    (target : V) (lo hi offset : K) (counts : C) (source : V)
    (shift : Nat) (chunkSize : UInt8) : Except E (V × C) := do
  let passMask := ops.mask chunkSize
  let mut counts ← ops.zeroCounts counts
  for index in ops.range lo hi do
    let value ← ops.read source index
    let bucket := ops.bucketIndex value shift passMask 2
    let count ← ops.readCount counts bucket
    counts ← ops.writeCount counts bucket (count + 1)
  counts ← ops.setFirstTarget counts (ops.addIndex lo offset)
  counts ← ops.prefixSum counts
  let mut target := target
  for index in ops.range lo hi do
    let value ← ops.read source index
    let bucket := ops.bucketIndex value shift passMask 1
    let targetIndex ← ops.readCount counts bucket
    target ← ops.write target (ops.toIndex targetIndex) value
    counts ← ops.writeCount counts bucket (targetIndex + 1)
  pure (target, counts)

structure RadixSortOps (V C K U Bits E : Type) where
  heuristic : RadixChunkHeuristicOps K U Bits E
  pass : RadixSortPassOps V C K U E
  allocateCounts : Nat → Except E C
  bucketCount : UInt8 → Nat
  bitsToNat : Bits → Nat
  chunkToNat : UInt8 → Nat
  addIndex : K → K → K
  negateIndex : K → K

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
def radixSortLoop {V C K U Bits E : Type}
    (ops : RadixSortOps V C K U Bits E)
    (lo hi offset : K) (bitCount step : Nat) (chunkSize : UInt8) :
    Nat → V → V → C → Nat → Except E (V × V × Bool)
  | 0, vector, scratch, _, _ => pure (vector, scratch, false)
  | fuel + 1, vector, scratch, counts, shift => do
    let (scratch, counts) ←
      radixSortPass ops.pass scratch lo hi offset counts vector shift chunkSize
    let shift := shift + step
    if !(shift < bitCount) then
      pure (vector, scratch, false)
    else
      let (vector, counts) ← radixSortPass ops.pass vector
        (ops.addIndex lo offset) (ops.addIndex hi offset) (ops.negateIndex offset)
        counts scratch shift chunkSize
      let shift := shift + step
      if !(shift < bitCount) then
        pure (vector, scratch, true)
      else
        radixSortLoop ops lo hi offset bitCount step chunkSize fuel vector scratch counts shift

def radixSortBang {V C K U Bits E : Type}
    (ops : RadixSortOps V C K U Bits E)
    (vector : V) (lo hi : K) (bits : Bits) (scratch : V) (offset : K)
    (chunkSize? : Option UInt8 := none) : Except E (V × V × Bool) := do
  let chunkSize ← match chunkSize? with
    | some size => pure size
    | none => radixChunkSizeHeuristic ops.heuristic lo hi bits
  let counts ← ops.allocateCounts (ops.bucketCount chunkSize)
  let bitCount := ops.bitsToNat bits
  let step := ops.chunkToNat chunkSize
  radixSortLoop ops lo hi offset bitCount step chunkSize (bitCount + 1) vector scratch counts 0

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

structure ComputeExtremaOps (V Alg O K α Kws Scratch E : Type) where
  rangeAndScratch : Kws → Except E (K × K × Scratch)
  nextIndex : K → K
  range : K → K → List K
  read : V → K → Except E α
  less : O → α → α → Bool
  appendExtrema : Kws → α → α → Kws
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
def sortComputeExtrema {V Alg O K α Kws Scratch E : Type}
    (ops : ComputeExtremaOps V Alg O K α Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E Scratch := do
  let (lo, hi, scratch) ← ops.rangeAndScratch keywords
  let first ← ops.read vector lo
  let mut minimum := first
  let mut maximum := first
  for index in ops.range (ops.nextIndex lo) hi do
    let value ← ops.read vector index
    if ops.less order value minimum then
      minimum := value
    if ops.less order maximum value then
      maximum := value
  if !(ops.less order minimum maximum) then
    pure scratch
  else
    ops.sort vector (ops.nextAlgorithm algorithm) order
      (ops.appendExtrema keywords minimum maximum)
structure BoolSortOps (V K O Kws Scratch R E : Type) where
  less : O → Bool → Bool → Bool
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
  let first :=
    if ops.less order false true then some false
    else if ops.less order true false then some true
    else none
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
    (V Data Wrapped K Index α Alg O PermOrder Kws Scratch E : Type) where
  range : Kws → Except E (K × K)
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
  allIdentityIndices : V → Data → Bool
  sendMissingToEnd : V → O → K → K → Except E (V × K × K)
  wrapVectorWithoutMissing : V → Except E Wrapped
  wrapDataWithoutMissing : Data → Except E Wrapped
  indexRange : K → K → List K
  eachDataIndex : Data → List Index
  dataIndexAt : List Index → K → Index
  readData : Data → Index → Except E α
  isMissing : α → Bool
  writeIndex : V → K → K → Except E V
  nextIndex : K → K
  previousIndex : K → K
  reverse : V → K → K → Except E V
  permutationOrder : PermOrder → Wrapped → O
  nextAlgorithm : Alg → Alg
  appendBounds : Kws → K → K → Kws
  sortWrapped : Wrapped → Alg → O → Kws → Except E Scratch
  sortVector : V → Alg → O → Kws → Except E Scratch

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
def sortMissingOptimization {V Data Wrapped K Index α Alg O PermOrder Kws Scratch E : Type}
    (ops : MissingSortOps V Data Wrapped K Index α Alg O PermOrder Kws Scratch E)
    (vector : V) (algorithm : Alg) (order : O) (keywords : Kws) :
    Except E Scratch := do
  let (lo, hi) ← ops.range keywords
  let vectorType := ops.elementType vector
  if ops.isDirectOrdering order && ops.hasMissingSupertype vectorType &&
      !ops.sameType (ops.nonMissingType vectorType) vectorType then
    let (vector, lo, hi) ← ops.sendMissingToEnd vector order lo hi
    let withoutMissing ← ops.wrapVectorWithoutMissing vector
    ops.sortWrapped withoutMissing (ops.nextAlgorithm algorithm) order
      (ops.appendBounds keywords lo hi)
  else
    match ops.permutationDetails order with
    | some (permutationOrder, data) =>
      let dataType := ops.dataElementType data
      if ops.isDirectPermutationOrder permutationOrder &&
          ops.isIntegerType vectorType && ops.hasMissingSupertype dataType &&
          !ops.sameType (ops.nonMissingType dataType) dataType &&
          ops.allIdentityIndices vector data then
        let mut loIndex := lo
        let mut hiIndex := hi
        let indices := ops.eachDataIndex data
        let mut vector := vector
        for i in ops.indexRange lo hi do
          let dataIndex := ops.dataIndexAt indices i
          let value ← ops.readData data dataIndex
          if ops.isMissing value == ops.isReversePermutationOrder permutationOrder then
            vector ← ops.writeIndex vector loIndex i
            loIndex := ops.nextIndex loIndex
          else
            vector ← ops.writeIndex vector hiIndex i
            hiIndex := ops.previousIndex hiIndex
        vector ← ops.reverse vector loIndex hi
        let (lo, hi) := if ops.isReversePermutationOrder permutationOrder then
          (loIndex, hi) else (lo, hiIndex)
        let withoutMissing ← ops.wrapDataWithoutMissing data
        ops.sortVector vector (ops.nextAlgorithm algorithm)
          (ops.permutationOrder permutationOrder withoutMissing)
          (ops.appendBounds keywords lo hi)
      else
        ops.sortVector vector (ops.nextAlgorithm algorithm) order keywords
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
    (V α UV U K Bits C Backing O Kws E Result : Type) where
  rangeAndExtrema : Kws → Except E (K × K × α × α × Option Backing)
  uintMapOps : UIntMapVectorOps V UV U K α O E
  subtractUnsigned : U → U → U
  topSetBit : U → Bits
  range : K → K → List K
  windowLength : K → K → Nat
  oneMinus : K → K
  radixOps : RadixSortOps UV C K U Bits E
  scratchOps : ScratchOps Backing Backing E
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
def sortRadixAlgorithm {V α UV U K Bits C Backing O Kws E Result : Type}
    (ops : RadixSortWrapperOps V α UV U K Bits C Backing O Kws E Result)
    (vector : V) (order : O) (keywords : Kws) : Except E Result := do
  let (lo, hi, minimum, maximum, scratchArg) ← ops.rangeAndExtrema keywords
  let minimumUnsigned ← ops.uintMapOps.uintMap minimum order
  let maximumUnsigned ← ops.uintMapOps.uintMap maximum order
  let range := ops.subtractUnsigned maximumUnsigned minimumUnsigned
  let bits := ops.topSetBit range
  let mut unsignedVector ← uintMapVectorBang ops.uintMapOps vector lo hi order
  for index in ops.range lo hi do
    let value ← ops.radixOps.pass.read unsignedVector index
    unsignedVector ← ops.radixOps.pass.write unsignedVector index
      (ops.subtractUnsigned value minimumUnsigned)
  let (scratch, scratchView) ←
    match scratchArg with
    | none => makeScratchNothing ops.scratchOps (ops.windowLength lo hi)
    | some existing => makeScratchSame ops.scratchOps existing (ops.windowLength lo hi)
  let unsignedType := ops.uintMapOps.uintMappable
    (ops.uintMapOps.elementType vector) order
  let unsignedScratch ← ops.reinterpretScratch unsignedType scratchView
  let indexOffset := ops.oneMinus lo
  let (unsignedResult, unsignedScratchResult, dataInVector) ←
    radixSortBang ops.radixOps unsignedVector lo hi bits unsignedScratch indexOffset
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
  less : O → α → α → Bool
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
  if ops.less order rightHead leftHead then
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
  midpoint : K → K → K
  lessValue : O → α → α → Bool
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
  let vector ← if ops.lessValue order loValue middleValue then do
    let vector ← ops.write vector lo middleValue
    ops.write vector middle loValue
  else
    pure vector
  let hiValue ← ops.read vector hi
  let loValue ← ops.read vector lo
  let vector ← if ops.lessValue order hiValue loValue then do
    let middleValue ← ops.read vector middle
    if ops.lessValue order hiValue middleValue then do
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
  | 0, i, leftValue => pure (i, leftValue)
  | fuel + 1, i, leftValue =>
    if ops.lessValue order leftValue pivot then do
      let i := ops.nextIndex i
      let leftValue ← ops.read vector i
      partitionScanLeft ops vector pivot order fuel i leftValue
    else
      pure (i, leftValue)

def partitionScanRight {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (vector : V) (pivot : α) (order : O) : Nat → K → α → Except E (K × α)
  | 0, j, rightValue => pure (j, rightValue)
  | fuel + 1, j, rightValue =>
    if ops.lessValue order pivot rightValue then do
      let j := ops.previousIndex j
      let rightValue ← ops.read vector j
      partitionScanRight ops vector pivot order fuel j rightValue
    else
      pure (j, rightValue)

def partitionVectorLoop {V α K Alg O E : Type}
    (ops : LegacyQuickSortOps V α K Alg O E)
    (lo hi : K) (pivot : α) (order : O) : Nat → V → K → K → Except E (V × K)
  | 0, vector, _, j => pure (vector, j)
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
  | 0, vector, _, _ => pure vector
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
  less : O → α → α → Bool
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
    let below := loSignpost.any fun signpost => ops.less order value signpost
    let notAbove := hiSignpost.all fun signpost => !ops.less order signpost value
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
  minimum : Range → K
  maximum : Range → K
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
    if !ops.lessEq (ops.minimum source) (ops.minimum target) then
      throw ops.rangeMismatch
    let vector ← ops.reverse vector (ops.minimum source) (ops.maximum target)
    ops.reverse vector (ops.minimum target) (ops.maximum target)
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
  roundInt : Float → Nat
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
  let k2 := ops.roundInt (ops.square k)
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
  pivotIndex : K → K → Except E K
  readSource : Source → K → Except E α
  writeTarget : Target → K → α → Except E Target
  writePivot : Target → PivotDest → K → α → Except E (Target × PivotDest)
  lessValue : O → α → α → Bool
  lessIndex : K → K → Bool
  nextIndex : K → K
  subtractIndex : K → K → K
  addBoolToIndex : K → Bool → K
  addPivotOffset : K → K → K
  distance : K → K → Nat := fun _ _ => 0

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
  | 0, target, lo, offset => pure (target, lo, offset)
  | fuel + 1, target, lo, offset =>
    if ops.lessIndex lo pivotIndex then do
      let value ← ops.readSource source lo
      let sendRight := if reverse then !(ops.lessValue order value pivot)
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
  | 0, target, lo, offset => pure (target, lo, offset)
  | fuel + 1, target, lo, offset =>
    if ops.lessIndex lo hi then do
      let value ← ops.readSource source (ops.nextIndex lo)
      let sendRight := if reverse then ops.lessValue order pivot value
        else !(ops.lessValue order value pivot)
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
  | 0, vector, temporary, _, _, _, _, scratch, _, _ =>
    pure (vector, temporary, scratch)
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
  | 0, temporary, _, j => pure (temporary, j)
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
  | 0, vector, i, j, k => pure (vector, i, j, k)
  | fuel + 1, vector, i, j, k =>
    if ops.quick.lessIndex k j && ops.lessEqIndex j hi then do
      let right ← ops.quick.read vector j
      let left ← ops.readTemporary temporary i
      if ops.quick.lessValue order right left then
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
  | 0, vector, _, _ => pure vector
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
  | 0, vector, _, _, _ => pure vector
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
  | 0, vector, _, _ => pure vector
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

def arrayCheckBounds {α : Type} (values : Array α) (lo hi : Int) : Jl Unit :=
  if hi < lo then .ok ()
  else if 1 ≤ lo ∧ hi ≤ values.size then .ok ()
  else .error .boundsError

/-- One-based `AbstractVector` storage read and written by the sorting methods: `length(v)`,
`v[i]` (`getindex`) and `v[i] = x` (`setindex!`). `Array` is one instance (`arrayStorage`). -/
structure VectorStorage (V α : Type) where
  length : V → Nat
  getindex : V → Int → Jl α
  setindex : V → Int → α → Jl V

def arrayStorage {α : Type} : VectorStorage (Array α) α where
  length := Array.size
  getindex := arrayRead
  setindex := arrayWrite

def storageCheckBounds {V α : Type} (S : VectorStorage V α) (values : V) (lo hi : Int) :
    Jl Unit :=
  if hi < lo then .ok ()
  else if 1 ≤ lo ∧ hi ≤ S.length values then .ok ()
  else .error .boundsError

def arrayIndexRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun offset => lo + Int.ofNat offset

def arrayIndices : IntegerIndexOps Int where
  addOne := fun i => i + 1
  previous := fun i => i - 1
  range := arrayIndexRange
  less := fun a b => decide (a < b)

def storageMutationOps {V α : Type} (S : VectorStorage V α) :
    VectorMutationOps (StateT V (Except JlError)) Unit α Int where
  get := fun _ index => fun values => do
    let value ← S.getindex values index
    pure (value, values)
  set := fun _ value index => fun values => do
    let updated ← S.setindex values index value
    pure ((), updated)
  indices := arrayIndices
  distance := fun lo hi => (hi - lo).toNat

def storageInsertion {V α : Type} (S : VectorStorage V α) (lt : α → α → Bool)
    (values : V) (lo hi : Int) : Jl V := do
  let (_, sorted) ←
    (insertionSort (storageMutationOps S) (fun (_ : Unit) => lt) () () lo hi ()).run values
  pure sorted

def storageSwap {V α : Type} (S : VectorStorage V α) (values : V) (left right : Int) :
    Jl V := do
  let leftValue ← S.getindex values left
  let rightValue ← S.getindex values right
  let updated ← S.setindex values left rightValue
  S.setindex updated right leftValue

def storageReverse {V α : Type} (S : VectorStorage V α) (values : V) (lo hi : Int) :
    Jl V := do
  let mut values := values
  for offset in List.range ((hi - lo + 1).toNat / 2) do
    values ← storageSwap S values (lo + Int.ofNat offset) (hi - Int.ofNat offset)
  pure values

def storageCopyFromArray {V α : Type} (S : VectorStorage V α) (destination : V) (first : Int)
    (source : Array α) (sourceFirst : Int) (length : Nat) : Jl V := do
  let mut destination := destination
  for offset in List.range length do
    let value ← arrayRead source (sourceFirst + Int.ofNat offset)
    destination ← S.setindex destination (first + Int.ofNat offset) value
  pure destination

def storageQuickOps {V α : Type} (S : VectorStorage V α) (lt : α → α → Bool) :
    LegacyQuickSortOps V α Int Unit Unit JlError where
  midpoint := fun lo hi => lo + (hi - lo) / 2
  lessValue := fun _ => lt
  read := S.getindex
  write := S.setindex
  nextIndex := fun i => i + 1
  previousIndex := fun i => i - 1
  lessIndex := fun lo hi => decide (lo < hi)
  distance := fun lo hi => (hi - lo).toNat
  checkBounds := storageCheckBounds S
  smallAlgorithm := ()
  smallThreshold := 20
  smallSort := fun values _ _ lo hi => storageInsertion S lt values lo hi

def storageMergeOps {V α : Type} [Inhabited α] (S : VectorStorage V α) (lt : α → α → Bool) :
    LegacyMergeSortOps V (Array α) α Int Unit Unit JlError where
  quick := storageQuickOps S lt
  oneIndex := 1
  lessEqIndex := fun lo hi => decide (lo ≤ hi)
  similar := fun _ length => .ok (Array.replicate length default)
  temporaryLength := Array.size
  resizeTemporary := fun values length =>
    .ok (values ++ Array.replicate (length - values.size) default)
  requireOneBased := fun _ => .ok ()
  readTemporary := arrayRead
  writeTemporary := arrayWrite

def storagePartialQuickOps {V α : Type} (S : VectorStorage V α) (lt : α → α → Bool) :
    LegacyPartialQuickSortOps V α Int (Int × Int) Unit JlError where
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

structure ArraySortKeywords (α : Type) where
  lo : Int
  hi : Int
  scratch : Option (Array α) := none

/-- `partition!` writing into the vector from the scratch array (`swap == true`); the pivot
destination is the vector itself. -/
def vectorTargetPartitionOps {V α : Type} (S : VectorStorage V α)
    (pivot : Int → Int → Int) :
    ScratchPartitionOps V (Array α) V Int α (α → α → Bool) JlError where
  pivotIndex := fun lo hi => .ok (pivot lo hi)
  readSource := arrayRead
  writeTarget := S.setindex
  writePivot := fun target _ index value => do
    let updated ← S.setindex target index value
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
    ScratchPartitionOps (Array α) V V Int α (α → α → Bool) JlError where
  pivotIndex := fun lo hi => .ok (pivot lo hi)
  readSource := S.getindex
  writeTarget := arrayWrite
  writePivot := fun target destination index value => do
    let updated ← S.setindex destination index value
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
    (sortNext : V → Algorithm (BracketSortTarget Int) Int → (α → α → Bool) →
      ArraySortKeywords α → Jl (V × Option (Array α))) :
    ScratchQuickSortOps V (Array α) α Int (Algorithm (BracketSortTarget Int) Int)
      (α → α → Bool) (ArraySortKeywords α) (Array α) JlError where
  rangeAndScratch := fun keywords => .ok (keywords.lo, keywords.hi, keywords.scratch)
  makeScratch := fun existing _ length =>
    match existing with
    | none => makeScratchNothing arrayScratchOps length
    | some backing => makeScratchSame arrayScratchOps backing length
  requireOffset := fun offset => match offset with
    | none => .error (.methodError "missing scratch offset")
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
    (sortNext : V → Alg → (α → α → Bool) → ArraySortKeywords α →
      Jl (V × Option (Array α))) :
    StableCheckSortedOps V Alg (α → α → Bool) Int
      (ArraySortKeywords α) (Option (Array α)) JlError where
  rangeAndScratch := fun keywords => .ok (keywords.lo, keywords.hi, keywords.scratch)
  isSorted := fun values lo hi order =>
    issortedWindow arrayIndices (storageCheckBounds S) S.getindex
      (fun order => order) values lo hi order
  stableReverseOrdering := fun order a b => !order a b
  reverse := storageReverse S
  nextAlgorithm := nextAlgorithm
  sort := sortNext

def storageCheckSortedOps {V α Alg : Type} (S : VectorStorage V α)
    (nextAlgorithm : Alg → Alg)
    (sortNext : V → Alg → (α → α → Bool) → ArraySortKeywords α →
      Jl (V × Option (Array α))) :
    CheckSortedOps V Alg (α → α → Bool) Int
      (ArraySortKeywords α) (Option (Array α)) JlError where
  rangeAndScratch := fun kw => .ok (kw.lo, kw.hi, kw.scratch)
  difference := Int.sub
  isSorted := fun values lo hi order =>
    issortedWindow arrayIndices (storageCheckBounds S) S.getindex (fun order => order)
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
      (CountingKeywords t) Unit JlError where
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
    let value ← arrayRead values index
    pure ⟨t, value⟩
  write := fun values index value => do
    let converted ← JInt.convert t value.val
    arrayWrite values index converted
  bucketForValue := fun value offset => (indexAdd value offset).val.toNat
  countRead := fun counts bucket =>
    match counts[bucket - 1]? with
    | some count => if bucket = 0 then .error .boundsError else .ok count
    | none => .error .boundsError
  countWrite := fun counts bucket value =>
    if 1 ≤ bucket ∧ bucket ≤ counts.size then .ok (counts.set! (bucket - 1) value)
    else .error .boundsError
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
    (lt : α → α → Bool) (values : V) (lo hi : Int) (algorithm : LegacyArrayAlgorithm) :
    Jl V := do
  match algorithm with
  | .insertion =>
    storageCheckBounds S values lo hi
    storageInsertion S lt values lo hi
  | .quick => legacyQuickSortBang (storageQuickOps S lt) values lo hi ()
  | .merge => legacyMergeSortBang (storageMergeOps S lt) values lo hi () ()
  | .partialQuick first last =>
    legacyPartialQuickSortBang (storagePartialQuickOps S lt) values lo hi (first, last) ()

def storageLegacyRun {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (lt : α → α → Bool) (values : V) (algorithm : LegacyArrayAlgorithm)
    (keywords : LegacyArrayKeywords α) : Jl V := do
  match algorithm with
  | .insertion => storageInsertion S lt values keywords.lo keywords.hi
  | _ =>
    let ops : LegacyDispatchOps V Int LegacyArrayAlgorithm Unit
        (LegacyArrayKeywords α) (Option (Array α)) JlError := {
      getKeywords := fun kw => .ok (kw.lo, kw.hi, kw.scratch, kw.entry)
      sameAlgorithm := BEq.beq
      undefinedAlgorithm := fun _ _ _ =>
        .argumentError "Base.Sort._sort! is not defined for this algorithm"
      legacySort := fun current lo hi alg _ => storageLegacyFive S lt current lo hi alg
    }
    let (sorted, _) ← legacySortDispatch ops values algorithm () keywords
    pure sorted

def storageLegacyOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (lt : α → α → Bool) :
    LegacySortOps V Int LegacyArrayAlgorithm Unit
      (LegacyArrayKeywords α) (Array α) JlError where
  firstIndex := fun _ => 1
  lastIndex := fun values => S.length values
  checkBounds := storageCheckBounds S
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
  roundInt : Float → Nat
  floorInt : Float → Jl Int
  topSetBit : Nat → Nat
  hashLength : Nat → Nat
  hashAttempt : Nat → Nat → Nat
  sampleIndex : Nat → Int → Int → Jl Int

def defaultBracketNumerics : BracketNumerics where
  cbrt := fun n => Float.ofNat n
  roundInt := fun _ => 1
  floorInt := fun _ => .ok 1
  topSetBit := fun n => if n = 0 then 0 else Nat.log2 n + 1
  hashLength := id
  hashAttempt := fun a b => a + b
  sampleIndex := fun _ lo _ => .ok lo

def sourceApplyInitialOptimizations {Target Index : Type} :
    Algorithm Target Index → Algorithm Target Index
  | .quick => maybeApplyInitialQuick
  | .merge => maybeApplyInitialMerge
  | .insertion => maybeApplyInitialInsertion
  | algorithm => maybeApplyInitialGeneric algorithm

def storageBracketKernelOps {V α : Type} (S : VectorStorage V α) (lt : α → α → Bool) :
    BracketKernelOps V α Int Unit JlError where
  checkBounds := storageCheckBounds S
  range := arrayIndexRange
  read := S.getindex
  less := fun _ => lt
  swap := storageSwap S
  scaleByBool := fun i yes => if yes then i else 0
  addIndexOffset := Int.add
  addInt := Int.add
  boolMinusOne := fun yes => if yes then 0 else -1

def storageMoveOps {V α : Type} (S : VectorStorage V α) :
    MoveVectorOps V (BracketSortTarget Int) Int JlError where
  length := fun target => (bracketTargetIndices target).length
  disjoint := fun left right =>
    !(bracketTargetIndices left).any fun value => (bracketTargetIndices right).contains value
  indices := bracketTargetIndices
  minimum := fun target => (minimumIntList (bracketTargetIndices target)).getD 0
  maximum := fun target => (maximumIntList (bracketTargetIndices target)).getD 0
  lessEq := fun a b => decide (a ≤ b)
  lengthMismatch := .argumentError "length mismatch"
  rangeMismatch := .argumentError "range mismatch"
  swap := storageSwap S
  reverse := storageReverse S

abbrev ArrayBracketAlgorithm :=
  BracketSortTarget Int ×
    (BracketSortTarget Int → Algorithm (BracketSortTarget Int) Int)

def storageBracketOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics)
    (sortSegment : V → Algorithm (BracketSortTarget Int) Int →
      (α → α → Bool) → ArraySortKeywords α → Jl (V × Option (Array α))) :
    BracketedSortOps V α Int ArrayBracketAlgorithm
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool) (ArraySortKeywords α)
      (Option (Array α)) JlError (V × Option (Array α)) where
  rangeAndScratch := fun kw => .ok (kw.lo, kw.hi, kw.scratch)
  rangeLength := fun lo hi => (hi - lo + 1).toNat
  lessIndex := fun a b => decide (a < b)
  lessEqIndex := fun a b => decide (a ≤ b)
  advance := fun i amount => i + Int.ofNat amount
  range := arrayIndexRange
  target := Prod.fst
  targetMinimum := bracketTargetMinimum
  targetMaximum := bracketTargetMaximum
  shiftTarget := shiftBracketTarget
  nextAlgorithm := fun algorithm target => algorithm.2 target
  cbrt := numeric.cbrt
  square := fun value => value * value
  roundInt := numeric.roundInt
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
  floorIndex := numeric.floorInt
  minimumIndex := min
  maximumIndex := max
  inclusiveSpan := fun lo hi => Float.ofInt (hi - lo + 1)
  seedForLength := numeric.hashLength
  hashAttempt := numeric.hashAttempt
  hashIndex := numeric.sampleIndex
  swap := storageSwap S
  read := S.getindex
  checkFailure := .argumentError "this should never happen"
  kernelOps := {
    checkBounds := storageCheckBounds S
    range := arrayIndexRange
    read := S.getindex
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

/-- `_sort!` dispatch on the algorithm for an `AbstractVector` whose element type has no
specialised `Missing`, `Bool`, `IEEEFloat` or `UIntMappable` method. The fuel only bounds the
nesting of algorithm wrappers; `sourceSortWindow` supplies the algorithm's depth. -/
def sourceSortLoop {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) :
    Nat → V → Algorithm (BracketSortTarget Int) Int → (α → α → Bool) →
      ArraySortKeywords α → Jl (V × Option (Array α))
  | 0, _, _, _, _ => .error (.methodError "algorithm nesting exceeds the dispatch depth")
  | fuel + 1, values, algorithm, order, keywords =>
    let step := sourceSortLoop S numeric pivot fuel
    match algorithm with
    | .defaultStable | .defaultUnstable =>
      sortDefaultAlgorithm step values order keywords
    | .subArray _ =>
      sortSubArrayFallback step
        (fun alg => match alg with | .subArray next => next | _ => alg)
        values algorithm order keywords
    | .missing _ =>
      let ops : MissingSortOps V V (WithoutMissingVector α V)
          Int Int α (Algorithm (BracketSortTarget Int) Int) (α → α → Bool)
          Empty (ArraySortKeywords α) (V × Option (Array α)) JlError := {
        range := fun kw => .ok (kw.lo, kw.hi)
        elementType := fun _ => α
        dataElementType := fun _ => α
        hasMissingSupertype := fun _ => false
        nonMissingType := id
        sameType := fun _ _ => true
        isIntegerType := fun _ => false
        isDirectOrdering := fun _ => false
        permutationDetails := fun _ => none
        isDirectPermutationOrder := Empty.elim
        isReversePermutationOrder := Empty.elim
        allIdentityIndices := fun _ _ => false
        sendMissingToEnd := fun v _ lo hi => .ok (v, lo, hi)
        wrapVectorWithoutMissing := fun v => .ok ⟨v⟩
        wrapDataWithoutMissing := fun v => .ok ⟨v⟩
        indexRange := arrayIndexRange
        eachDataIndex := fun v => arrayIndexRange 1 (S.length v)
        dataIndexAt := fun indices i => indices[(i - 1).toNat]?.getD 0
        readData := S.getindex
        isMissing := fun _ => false
        writeIndex := fun v _ _ => .ok v
        nextIndex := fun i => i + 1
        previousIndex := fun i => i - 1
        reverse := storageReverse S
        permutationOrder := fun impossible _ => Empty.elim impossible
        nextAlgorithm := fun alg => match alg with | .missing next => next | _ => alg
        appendBounds := fun kw lo hi => { kw with lo, hi }
        sortWrapped := fun wrapped next o kw => step wrapped.data next o kw
        sortVector := step
      }
      sortMissingOptimization ops values algorithm order keywords
    | .boolOptimization _ =>
      sortBoolOther step
        (fun alg => match alg with | .boolOptimization next => next | _ => alg)
        values algorithm order keywords
    | .small threshold _ _ =>
      let ops : SmallSortOps V (Algorithm (BracketSortTarget Int) Int)
          (α → α → Bool) Int (ArraySortKeywords α) (V × Option (Array α)) JlError := {
        range := fun kw => .ok (kw.lo, kw.hi)
        spanLessThan := fun lo hi limit => decide (hi - lo < Int.ofNat limit)
        smallAlgorithm := fun alg => match alg with | .small _ small _ => small | _ => alg
        bigAlgorithm := fun alg => match alg with | .small _ _ big => big | _ => alg
        sort := step
      }
      sortSmall ops values algorithm threshold order keywords
    | .ieeeFloat _ =>
      let ops : IEEEFloatSortOps V V (Array Nat) Int
          (Algorithm (BracketSortTarget Int) Int) (α → α → Bool) Empty (α → α → Bool)
          (ArraySortKeywords α) (Array α) JlError := {
        range := fun kw => .ok (kw.lo, kw.hi)
        elementType := fun _ => α
        dataElementType := fun _ => α
        isConcreteIEEEFloat := fun _ => false
        isDirectOrdering := fun _ => false
        isIntegerVector := fun _ => false
        permutationDetails := fun _ => none
        isDirectPermutationOrder := Empty.elim
        reverseOrdering := fun o a b => o b a
        forwardOrdering := id
        sendNaNs := fun v _ lo hi => .ok (v, lo, hi)
        sendAfterZero := fun v _ lo _ => .ok (v, lo)
        reinterpretVector := fun _ => .ok #[]
        syncUnsignedAlias := fun _ u => .ok u
        restoreVectorAlias := fun v _ => .ok v
        nextIndex := fun i => i + 1
        sortUnsigned := fun u _ _ kw => .ok (u, kw.scratch)
        sendPermutationNaNs := fun _ _ impossible => Empty.elim impossible
        reinterpretData := fun _ => .ok #[]
        sendPermutationAfterZero := fun _ _ impossible => Empty.elim impossible
        reversePermutationOrder := Empty.elim
        forwardPermutationOrder := Empty.elim
        makePermutationOrder := fun impossible _ => Empty.elim impossible
        sortPermutation := step
        nextAlgorithm := fun alg => match alg with | .ieeeFloat next => next | _ => alg
        keywordsWithBounds := fun kw lo hi => { kw with lo, hi }
        keywordsWithBoundsAndScratch := fun kw lo hi scratch => { kw with lo, hi, scratch }
        sortFallback := step
      }
      sortIEEEFloatOptimization ops values algorithm order keywords
    | .isUIntMappable _ _ =>
      let ops : UIntMappableSortOps V (Algorithm (BracketSortTarget Int) Int)
          (α → α → Bool) (ArraySortKeywords α) (V × Option (Array α)) JlError := {
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
    | .quick =>
      let ops : LegacyDispatchOps V Int (Algorithm (BracketSortTarget Int) Int)
          (α → α → Bool) (ArraySortKeywords α) (Option (Array α)) JlError := {
        getKeywords := fun kw => .ok (kw.lo, kw.hi, kw.scratch, none)
        sameAlgorithm := fun _ _ => false
        undefinedAlgorithm := fun _ _ _ =>
          .argumentError "Base.Sort._sort! is not defined for this algorithm"
        legacySort := fun current lo hi _ o =>
          legacyQuickSortBang (storageQuickOps S o) current lo hi ()
      }
      legacySortDispatch ops values algorithm order keywords
    | .merge =>
      let ops : LegacyDispatchOps V Int (Algorithm (BracketSortTarget Int) Int)
          (α → α → Bool) (ArraySortKeywords α) (Option (Array α)) JlError := {
        getKeywords := fun kw => .ok (kw.lo, kw.hi, kw.scratch, none)
        sameAlgorithm := fun _ _ => false
        undefinedAlgorithm := fun _ _ _ =>
          .argumentError "Base.Sort._sort! is not defined for this algorithm"
        legacySort := fun current lo hi _ o =>
          legacyMergeSortBang (storageMergeOps S o) current lo hi () ()
      }
      legacySortDispatch ops values algorithm order keywords
    | .partialQuickSort target =>
      let ops : LegacyDispatchOps V Int (Algorithm (BracketSortTarget Int) Int)
          (α → α → Bool) (ArraySortKeywords α) (Option (Array α)) JlError := {
        getKeywords := fun kw => .ok (kw.lo, kw.hi, kw.scratch, none)
        sameAlgorithm := fun _ _ => false
        undefinedAlgorithm := fun _ _ _ =>
          .argumentError "Base.Sort._sort! is not defined for this algorithm"
        legacySort := fun current lo hi _ o =>
          legacyPartialQuickSortBang (storagePartialQuickOps S o) current lo hi
            (bracketTargetEndpoints.first target, bracketTargetEndpoints.last target) ()
      }
      legacySortDispatch ops values algorithm order keywords
    | .considerCounting _ _ =>
      sortConsiderCountingOther step
        (fun alg => match alg with | .considerCounting _ next => next | _ => alg)
        values algorithm order keywords
    | .computeExtrema _ | .counting | .considerRadix _ _ | .radix =>
      .error (.methodError "algorithm requires a direct integer ordering")

def sourceSortWindow {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int)
    (values : V) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (order : α → α → Bool) (keywords : ArraySortKeywords α) : Jl (V × Option (Array α)) :=
  sourceSortLoop S numeric pivot (algorithm.depth + 16) values algorithm order keywords

def sourceSortBang {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int)
    (values : V) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (order : α → α → Bool) (keywords : ArraySortKeywords α) : Jl V := do
  let (sorted, _) ← sourceSortWindow S numeric pivot values algorithm order keywords
  pure sorted

def sourceVectorSortOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) :
    SortVectorOps V (Algorithm (BracketSortTarget Int) Int)
      (α → α → Bool) Unit (α → α → Bool)
      (Option (Array α)) (ArraySortKeywords α) JlError where
  applyInitialOptimizations := sourceApplyInitialOptimizations
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  runSort := fun values algorithm order keywords =>
    sourceSortBang S numeric pivot values algorithm order
      { keywords with lo := 1, hi := Int.ofNat (S.length values) }
  withScratch := fun scratch => { lo := 1, hi := 0, scratch }

def storagePartialSortOps {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) :
    PartialSortOps V (BracketSortTarget Int) Int (α → α → Bool)
      (Option (Array α)) (ArraySortKeywords α) (List α) JlError where
  targetOps := bracketTargetEndpoints
  sort := fun values algorithm order keywords =>
    sourceSortBang S numeric pivot values algorithm order
      { keywords with lo := 1, hi := Int.ofNat (S.length values) }
  maybeView := fun values target => match target with
    | .index index => do
      let value ← maybeviewInteger S.getindex values index
      pure [value]
    | _ => maybeviewRange
      (fun current selection => (bracketTargetIndices selection).mapM (S.getindex current))
      values target
  withScratch := fun scratch => { lo := 1, hi := 0, scratch }
  scratchOfKeywords := ArraySortKeywords.scratch

def storageElementOrDefault {V α : Type} [Inhabited α] (S : VectorStorage V α)
    (values : V) (index : Int) : α :=
  match S.getindex values index with
  | .ok value => value
  | .error _ => default

def storagePartialSortpermOps {V α : Type} [Inhabited α] (S : VectorStorage V α) (t : IntTy)
    (pivot : Int → Int → Int) :
    PartialSortpermOps (Array (JInt t)) V (BracketSortTarget Int) Nat Int
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool) Unit
      (α → α → Bool) (JInt t → JInt t → Bool) (ArraySortKeywords (JInt t))
      (List (JInt t)) JlError where
  makeIndexVector := fun values _ => .ok (Array.replicate (S.length values) (JInt.wrap t 0))
  axesIndex := Array.size
  axesVector := S.length
  axesEqual := fun a b => decide (a = b)
  axesError := fun _ _ => .argumentError "index vector must share the source axes"
  eachIndex := fun indices => arrayIndexRange 1 indices.size
  writeIndex := fun indices target value => do
    let converted ← JInt.convert t value
    arrayWrite indices target converted
  scratchQuickSort := fun target => scratchQuickRange bracketTargetEndpoints target
  initialOptimizations := initialOptimizations
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  permutationOrder := fun less values a b =>
    let left := storageElementOrDefault S values a.val
    let right := storageElementOrDefault S values b.val
    less left right || (!(less right left) && decide (a.val < b.val))
  emptyKeywords := { lo := 1, hi := 0, scratch := none }
  sort := fun indices algorithm order kw =>
    sourceSortBang arrayStorage defaultBracketNumerics pivot indices algorithm order
      { kw with lo := 1, hi := Int.ofNat indices.size }
  maybeView := fun indices target => (bracketTargetIndices target).mapM (arrayRead indices)

structure ArrayWindow where
  first : Int
  stride : Int
  length : Nat

def arrayWindowIndex (window : ArrayWindow) (index : Int) : Int :=
  window.first + (index - 1) * window.stride

def storageSendToEndOps {V α : Type} (S : VectorStorage V α) :
    SendToEndOps (StateT V (Except JlError)) ArrayWindow α Int where
  get := fun window index => fun values => do
    let value ← S.getindex values (arrayWindowIndex window index)
    pure (value, values)
  set := fun window value index => fun values => do
    let updated ← S.setindex values (arrayWindowIndex window index) value
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

def storageBoolSortOps {V : Type} (S : VectorStorage V Bool) :
    BoolSortOps V Int (Bool → Bool → Bool) (Int × Int) Unit V JlError where
  less := fun order => order
  rangeAndScratch := fun (lo, hi) => .ok (lo, hi, ())
  range := arrayIndexRange
  read := S.getindex
  firstSegmentEnd := fun lo count => lo + Int.ofNat count - 1
  secondSegmentStart := fun lo count => lo + Int.ofNat count
  setSegment := fun values lo hi value => do
    let mut values := values
    for index in arrayIndexRange lo hi do
      values ← S.setindex values index value
    pure values
  returnVector := id
  returnScratch := fun values _ => values

def arrayRadixPassOps :
    RadixSortPassOps (Array Nat) (Array Int) Int Nat JlError where
  mask := fun size => 2 ^ size.toNat - 1
  bucketIndex := fun value shift mask increment => ((value >>> shift) &&& mask) + increment
  zeroCounts := fun counts => .ok (Array.replicate counts.size 0)
  read := arrayRead
  write := arrayWrite
  range := arrayIndexRange
  readCount := fun counts index => arrayRead counts index
  writeCount := fun counts index value => arrayWrite counts index value
  setFirstTarget := fun counts first => arrayWrite counts 1 first
  prefixSum := fun counts => do
    let mut counts := counts
    for index in arrayIndexRange 2 counts.size do
      let value ← arrayRead counts index
      let previous ← arrayRead counts (index - 1)
      counts ← arrayWrite counts index ((JInt.wrap .i64 (value + previous)).val)
    pure counts
  addIndex := Int.add
  toIndex := id

def arrayRadixOps (heuristic : RadixChunkHeuristicOps Int Nat Nat JlError) :
    RadixSortOps (Array Nat) (Array Int) Int Nat Nat JlError where
  heuristic := heuristic
  pass := arrayRadixPassOps
  allocateCounts := fun size => .ok (Array.replicate size 0)
  bucketCount := fun size => 2 ^ size.toNat + 1
  bitsToNat := id
  chunkToNat := UInt8.toNat
  addIndex := Int.add
  negateIndex := Int.neg

abbrev NTuple (n : Nat) (α : Type) := { xs : List α // xs.length = n }
abbrev AnyNTuple (α : Type) := Sigma fun n : Nat => NTuple n α

def mergeAnyNTupleLoop {α : Type} [Inhabited α] (lt : α → α → Bool) :
    Nat → AnyNTuple α → AnyNTuple α → Jl (AnyNTuple α)
  | 0, left, _ => pure left
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

def mergeNTuple {α : Type} [Inhabited α] (lt : α → α → Bool)
    {m n : Nat} (left : NTuple m α) (right : NTuple n α) : Jl (NTuple (m + n) α) := do
  let merged ← mergeAnyNTupleLoop lt (m + n + 1) ⟨m, left⟩ ⟨n, right⟩
  if h : merged.2.val.length = m + n then
    pure ⟨merged.2.val, h⟩
  else
    .error (.methodError "tuple merge length mismatch")

def anyNTupleMergeOps {α : Type} [Inhabited α] (lt : α → α → Bool) :
    TupleMergeOps (AnyNTuple α) Unit JlError where
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

def mergeSortNTuple {α : Type} [Inhabited α] (lt : α → α → Bool)
    {n : Nat} (tuple : NTuple n α) : Jl (NTuple n α) := do
  let sorted ← mergeSortTupleRecursive (anyNTupleMergeOps lt) ⟨n, tuple⟩ ()
  if h : sorted.2.val.length = n then
    pure ⟨sorted.2.val, h⟩
  else
    .error (.methodError "tuple length changed")

def nTupleCoreOps {α : Type} [Inhabited α] (n : Nat) (pivot : Int → Int → Int) :
    TupleSortCoreOps (NTuple n α) (Array α) (Algorithm (BracketSortTarget Int) Int)
      (α → α → Bool) (Option (Array α)) JlError where
  length := fun _ => n
  copyMutable := fun values => .ok values.val.toArray
  sortMutable := fun values algorithm order scratch =>
    sourceSortBang arrayStorage defaultBracketNumerics pivot values algorithm order
      { lo := 1, hi := Int.ofNat values.size, scratch }
  constructLike := fun _ values =>
    if h : values.toList.length = n then .ok ⟨values.toList, h⟩
    else .error (.methodError "tuple length changed")
  mergeSort := fun values order => mergeSortNTuple order values

def nTuplePublicOps {α : Type} [Inhabited α] (n : Nat) (pivot : Int → Int → Int) :
    TuplePublicSortOps (NTuple n α) (Algorithm (BracketSortTarget Int) Int)
      (α → α → Bool) Unit (α → α → Bool) (Array α) (Option (Array α)) JlError where
  scratchMatches := fun _ _ => true
  argumentError := JlError.argumentError
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  keywords := id
  sortTuple := fun values algorithm order keywords =>
    match algorithm with
    | .defaultStable | .defaultUnstable =>
      sortTupleCore (nTupleCoreOps n pivot) values algorithm order keywords
    | _ => .error (.methodError "Base.Sort._sort")
  assertSameType := fun _ result => .ok result

def arrayPermutationOrder {α : Type} [Inhabited α]
    (order : α → α → Bool) (values : Array α) (left right : Int) : Bool :=
  let a := values[(left - 1).toNat]?.getD default
  let b := values[(right - 1).toNat]?.getD default
  order a b || (!(order b a) && decide (left < right))

def arrayIntegerExtrema (values : Array Int) : Jl (Int × Int) :=
  match values.toList with
  | [] => .error (.argumentError "reducing over an empty collection")
  | first :: rest => .ok (rest.foldl min first, rest.foldl max first)

def arraySortpermCoreOps {α : Type} [Inhabited α] (pivot : Int → Int → Int)
    (integerView : Array α → Jl (Array Int)) (hasIntegerElements : Array α → Bool)
    (isForward : (α → α → Bool) → Bool := fun _ => false) :
    SortpermCoreOps (Array α) (Array α) (Array Int)
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool)
      (Int → Int → Bool) (Option (Array Int)) Unit (Array Int) Int JlError where
  isForward := isForward
  isVector := fun _ => true
  hasIntegerElements := hasIntegerElements
  length := Array.size
  extrema := fun values => do
    let integerValues ← integerView values
    arrayIntegerExtrema integerValues
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
    sortpermIntRange sortpermIntArrayOps integers length minimum
  copyLinearIndices := fun values => .ok (arrayIndexRange 1 values.size).toArray
  vectorize := id
  permutationOrder := arrayPermutationOrder
  sortIndices := fun indices algorithm order scratch _ =>
    sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
      indices algorithm order () none order scratch

def arraySortpermTopOps {α : Type} [Inhabited α] (pivot : Int → Int → Int)
    (integerView : Array α → Jl (Array Int)) (hasIntegerElements : Array α → Bool)
    (isForward : (α → α → Bool) → Bool := fun _ => false) :
    SortpermTopOps (Array α) (Algorithm (BracketSortTarget Int) Int)
      (α → α → Bool) Unit (α → α → Bool)
      (Option (Array Int)) Unit (Array Int) JlError where
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  sortperm := fun values algorithm order scratch dims =>
    sortpermCore (arraySortpermCoreOps pivot integerView hasIntegerElements isForward)
      values algorithm order scratch dims

def arraySortpermBangOps {α : Type} [Inhabited α] (pivot : Int → Int → Int) :
    SortpermBangOps (Array Int) (Array α) (Array α)
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool)
      Unit (α → α → Bool) (Int → Int → Bool) (Option (Array Int))
      (Option Int) Nat JlError where
  isVector := fun _ => true
  hasDims := Option.isSome
  axesIndex := Array.size
  axesArray := Array.size
  axesEqual := fun a b => decide (a = b)
  dimensionError := fun _ => .argumentError "Dims argument incorrect for vector"
  axesError := fun _ _ => .argumentError "index array must have the same axes"
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

def arrayNonmissingInsertion (values : Array (Option Int)) (lo hi : Int)
    (reverse : Bool) : Jl (Array (Option Int)) := do
  let operations :
      VectorMutationOps (StateT (Array (Option Int)) (Except JlError)) Unit Int Int := {
    get := fun _ index => fun current => do
      let value ← withoutMissingGet arrayRead JlError.argumentError
        (⟨current⟩ : WithoutMissingVector Int (Array (Option Int))) index
      pure (value, current)
    set := fun _ value index => fun current => do
      let wrapped ← withoutMissingSet
        (fun storage value index => arrayWrite storage index (some value))
        (⟨current⟩ : WithoutMissingVector Int (Array (Option Int))) value index
      pure ((), wrapped.data)
    indices := arrayIndices
    distance := fun lo hi => (hi - lo).toNat
  }
  let compare := fun (_ : Unit) (a b : Int) => if reverse then decide (b < a) else decide (a < b)
  let (_, sorted) ← (insertionSort operations compare () () lo hi ()).run values
  pure sorted

def partitionMissingArray (values : Array (Option Int)) (reverse : Bool) (lo hi : Int) :
    Jl (Array (Option Int) × Int × Int) := do
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

def arrayMissingDirectOps :
    MissingSortOps (Array (Option Int)) (Array (Option Int))
      (WithoutMissingVector Int (Array (Option Int))) Int Int (Option Int)
      Unit Bool Empty (Int × Int) (Array (Option Int)) JlError where
  range := fun bounds => .ok bounds
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
    values.toList == (arrayIndexRange 1 data.size).map some
  sendMissingToEnd := partitionMissingArray
  wrapVectorWithoutMissing := fun values =>
    withoutMissingVector (fun data => data.any Option.isNone) JlError.argumentError values true
  wrapDataWithoutMissing := fun values =>
    withoutMissingVector (fun data => data.any Option.isNone) JlError.argumentError values true
  indexRange := arrayIndexRange
  eachDataIndex := fun values => arrayIndexRange 1 values.size
  dataIndexAt := fun indices index => indices[(index - 1).toNat]?.getD 0
  readData := arrayRead
  isMissing := Option.isNone
  writeIndex := fun values index value => arrayWrite values index (some value)
  nextIndex := fun index => index + 1
  previousIndex := fun index => index - 1
  reverse := storageReverse arrayStorage
  permutationOrder := fun impossible _ => Empty.elim impossible
  nextAlgorithm := id
  appendBounds := fun _ lo hi => (lo, hi)
  sortWrapped := fun wrapped _ reverse bounds =>
    arrayNonmissingInsertion wrapped.data bounds.1 bounds.2 reverse
  sortVector := fun values _ reverse bounds =>
    storageInsertion arrayStorage (optionIntegerLess reverse) values bounds.1 bounds.2

def arrayMissingPermutationOps (data : Array (Option Int)) :
    MissingSortOps (Array Int) (Array (Option Int))
      (WithoutMissingVector Int (Array (Option Int))) Int Int (Option Int)
      Unit Bool Bool (Int × Int) (Array Int) JlError where
  range := fun bounds => .ok bounds
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
  allIdentityIndices := fun values source => values.toList == arrayIndexRange 1 source.size
  sendMissingToEnd := fun values reverse lo hi => do
    let window : ArrayWindow := ⟨1, 1, values.size⟩
    let ((first, last), result) ←
      (sendToEndForwardOrdering (storageSendToEndOps arrayStorage) (fun (_ : Int) => pure false)
        window reverse lo hi).run values
    pure (result, first, last)
  wrapVectorWithoutMissing := fun values =>
    withoutMissingVector (fun source => source.any Option.isNone) JlError.argumentError
      (values.map some) true
  wrapDataWithoutMissing := fun values =>
    withoutMissingVector (fun source => source.any Option.isNone) JlError.argumentError values true
  indexRange := arrayIndexRange
  eachDataIndex := fun values => arrayIndexRange 1 values.size
  dataIndexAt := fun indices index => indices[(index - 1).toNat]?.getD 0
  readData := arrayRead
  isMissing := Option.isNone
  writeIndex := arrayWrite
  nextIndex := fun index => index + 1
  previousIndex := fun index => index - 1
  reverse := storageReverse arrayStorage
  permutationOrder := fun reverse _ => reverse
  nextAlgorithm := id
  appendBounds := fun _ lo hi => (lo, hi)
  sortWrapped := fun wrapped _ reverse bounds => do
    let sorted ← arrayNonmissingInsertion wrapped.data bounds.1 bounds.2 reverse
    sorted.mapM fun value => match value with
      | some integer => .ok integer
      | none => .error (.argumentError "encountered missing in nonmissing vector")
  sortVector := fun values _ reverse bounds =>
    storageInsertion arrayStorage (arrayPermutationOrder (optionIntegerLess reverse) data)
      values bounds.1 bounds.2

structure IEEECodec (α : Type) where
  encode : α → Nat
  decode : Nat → Jl α
  isNaN : α → Bool
  signbit : α → Bool
  less : α → α → Bool
  isIEEEFloat : Type → Bool
  isConcrete : Type → Bool

def partitionArrayOrdered {α : Type} (predicate : α → Bool) (values : Array α)
    (reverse endStable : Bool) (lo hi : Int) : Jl (Array α × Int × Int) := do
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
      (ArraySortKeywords Nat) (Array Nat) JlError where
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
  restoreVectorAlias := fun _ bits => bits.mapM codec.decode
  nextIndex := fun index => index + 1
  sortUnsigned := fun values _ reverse kw => do
    let compare := fun a b : Nat => if reverse then decide (b < a) else decide (a < b)
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
    ComputeExtremaOps (Array (JInt t)) Unit Bool Int (JInt t) (ExtremaKeywords t)
      (Array (JInt t)) JlError where
  rangeAndScratch := fun kw => .ok (kw.lo, kw.hi, initial)
  nextIndex := fun index => index + 1
  range := arrayIndexRange
  read := arrayRead
  less := fun reverse a b => if reverse then decide (b.val < a.val) else decide (a.val < b.val)
  appendExtrema := fun kw minimum maximum => { kw with minimum := some minimum, maximum := some maximum }
  nextAlgorithm := id
  sort := fun values _ reverse kw => do
    match kw.minimum, kw.maximum with
    | some minimum, some maximum =>
      let (result, _) ← sortCounting (arrayCountingOps t) values reverse
        { lo := kw.lo, hi := kw.hi, minimum, maximum }
      pure result
    | _, _ => .error (.argumentError "extrema have not been computed")

def xorIntegerWords {t : IntTy} (a b : JInt t) : JInt t :=
  JInt.wrap t (a.val + b.val)

def forwardIntegerCode (t : IntTy) (value : JInt t) : Nat :=
  if t.signed then
    uintMapSigned xorIntegerWords
      (fun _ => JInt.wrap t t.min)
      (fun word => ((word.val + 2 ^ t.bits) % (2 ^ t.bits)).toNat) value
  else
    (uintMapUnsigned value).val.toNat

def forwardIntegerDecode (t : IntTy) (code : Nat) : JInt t :=
  if t.signed then
    uintUnmapSigned (JInt t) (fun bits => JInt.wrap t (Int.ofNat bits))
      xorIntegerWords (JInt.wrap t t.min) code
  else
    JInt.wrap t (Int.ofNat (uintUnmapUnsigned Nat code))

def integerReverseMappingOps (t : IntTy) :
    ReverseUIntMappingOps (JInt t) Nat Unit Unit where
  bitwiseNot := fun code => (2 ^ t.bits - 1) - code
  forwardOrdering := id
  mapForward := fun value _ => forwardIntegerCode t value
  unmapForward := fun _ code _ => forwardIntegerDecode t code
  mappableForward := fun valueType _ =>
    uintMappableBitInteger (fun _ => JInt (unsignedIntegerType t)) valueType

def integerCode (t : IntTy) (reverse : Bool) (value : JInt t) : Nat :=
  if reverse then uintMapReverse (integerReverseMappingOps t) value ()
  else forwardIntegerCode t value

def integerDecode (t : IntTy) (reverse : Bool) (code : Nat) : JInt t :=
  if reverse then uintUnmapReverse (integerReverseMappingOps t) (JInt t) code ()
  else forwardIntegerDecode t code

def arrayIntegerMapOps (t : IntTy) :
    UIntMapVectorOps (Array (JInt t)) (Array Nat) Nat Int (JInt t) Bool JlError where
  elementType := fun _ => JInt t
  uintMappable := fun valueType reverse =>
    if reverse then uintMappableReverse (integerReverseMappingOps t) valueType ()
    else uintMappableBitInteger (fun _ => JInt (unsignedIntegerType t)) valueType
  reinterpret := fun unsignedType values =>
    match unsignedType with
    | none => .error (.argumentError "element type has no unsigned mapping")
    | some _ => .ok (values.map fun value => (value.val % (2 ^ t.bits)).toNat)
  range := arrayIndexRange
  read := arrayRead
  uintMap := fun value reverse => .ok (integerCode t reverse value)
  writeUnsigned := arrayWrite

def arrayIntegerUnmapOps (t : IntTy) :
    UIntUnmapVectorOps (Array (JInt t)) (Array Nat) Nat Int (JInt t) Bool JlError where
  range := arrayIndexRange
  addIndex := Int.add
  readUnsigned := arrayRead
  zeroUnsigned := 0
  zeroIndex := 0
  addUnsigned := fun a b => (a + b) % 2 ^ t.bits
  elementType := fun _ => JInt t
  uintUnmap := fun _ code reverse => .ok (integerDecode t reverse code)
  write := arrayWrite

def unsignedArrayScratchOps : ScratchOps (Array Nat) (Array Nat) JlError :=
  arrayScratchOps

structure RadixKeywords (t : IntTy) where
  lo : Int
  hi : Int
  minimum : JInt t
  maximum : JInt t
  scratch : Option (Array Nat) := none

def arrayRadixWrapperOps (t : IntTy)
    (heuristic : RadixChunkHeuristicOps Int Nat Nat JlError) :
    RadixSortWrapperOps (Array (JInt t)) (JInt t) (Array Nat) Nat Int Nat (Array Int)
      (Array Nat) Bool (RadixKeywords t) JlError (Array (JInt t) × Array Nat) where
  rangeAndExtrema := fun kw => .ok (kw.lo, kw.hi, kw.minimum, kw.maximum, kw.scratch)
  uintMapOps := arrayIntegerMapOps t
  subtractUnsigned := fun a b => (a + 2 ^ t.bits - b) % 2 ^ t.bits
  topSetBit := fun code => if code = 0 then 0 else Nat.log2 code + 1
  range := arrayIndexRange
  windowLength := fun lo hi => (hi - lo + 1).toNat
  oneMinus := fun index => 1 - index
  radixOps := arrayRadixOps heuristic
  scratchOps := unsignedArrayScratchOps
  reinterpretScratch := fun unsignedType backing =>
    match unsignedType with
    | none => .error (.argumentError "element type has no unsigned mapping")
    | some _ => .ok backing
  unmapOps := arrayIntegerUnmapOps t
  finish := fun values scratch => (values, scratch)

structure CharacterCode where
  bits : BitVec 32
  deriving Repr, DecidableEq

def arrayChunkLoopOps {α : Type} [Inhabited α] (pivot : Int → Int → Int) :
    SortChunksLoopOps (Array α) Int Nat
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool) (Array α) JlError where
  starts := fun first step last =>
    if step = 0 then .error (.argumentError "step cannot be zero")
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
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool)
      (Option (Array α)) JlError where
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
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool) Unit
      (α → α → Bool) (Option (Array α)) JlError where
  dimensionLength := layout.axisLength
  dimensions := fun array => (List.range (layout.ndims array)).map Nat.succ
  dimensionOne := 1
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  permuteDimensions := layout.permute
  vectorize := layout.vectorize
  applyInitialOptimizations := sourceApplyInitialOptimizations
  sortChunks := fun values n algorithm order scratch =>
    sortChunksDispatch (arrayChunkDispatchOps pivot) values n algorithm order scratch
  inversePermutation := layout.inversePermutation
  restorePermuted := layout.restorePermuted
  copyLinear := layout.copyLinear
  reshapeOriginalAxes := layout.reshapeOriginalAxes
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
      (Algorithm (BracketSortTarget Int) Int) (α → α → Bool) Unit
      (α → α → Bool) (Option (Array α)) JlError where
  dimensionCount := layout.ndims
  dimensionError := .argumentError "dimension out of range"
  applyInitialOptimizations := sourceApplyInitialOptimizations
  ordering := fun less _ reverse _ =>
    if reverse = some true then fun a b => less b a else less
  dimensionValues := fun count => (List.range count).map Nat.succ
  dimensionValue := getValue
  cartesianIndices := layout.cartesianIndices
  size := layout.axisLength
  getView := fun array dimension index =>
    getView layout.view getValue layout.ndims layout.coordinate array dimension index
  setView := fun array dimension index values =>
    layout.writeView array (sliceSelectors layout array dimension index) values
  sortBang := fun values algorithm order scratch =>
    sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
      values algorithm order () none order scratch
  defaultScratch := fun array dimension =>
    if dimension < 1 then .error .boundsError
    else
      let len := if dimension ≤ Int.ofNat (layout.ndims array) then
        layout.axisLength array dimension.toNat
      else 1
      if len < 10 then .ok none else .ok (some (Array.replicate len default))
  firstIndex := fun indices =>
    match indices with
    | [] => .error .boundsError
    | first :: _ => .ok first
  similar := fun values => .ok (Array.replicate values.size default)
  copyInto := fun temporary values =>
    if temporary.size = values.size then .ok values
    else .error (.argumentError "length mismatch")
  copyFrom := fun array dimension index values =>
    layout.writeView array (sliceSelectors layout array dimension index) values
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

def arrayRadixHeuristicOps : RadixChunkHeuristicOps Int Nat Nat JlError where
  subtract := fun a b => (JInt.wrap .i64 (a - b)).val
  maybeUnsigned := fun value =>
    maybeUnsignedBitSigned (fun word : Int => (JInt.wrap .u64 word).val.toNat) value
  log := fun value => (Float.ofNat value).log
  fromNat := Float.ofNat
  min := fun a b => if a ≤ b then a else b
  multiply := Float.mul
  divide := Float.div
  add := Float.add
  ceilingDiv := fun count denominator => (Float.ofNat count / denominator).ceil
  bitsToNat := id
  toUInt8 := fun value =>
    if 0 ≤ value && value ≤ 255 && value.floor == value then
      .ok (UInt8.ofNat value.toUInt64.toNat)
    else
      .error (.inexactError "UInt8")

def partitionPermutationOrdered {α : Type} (predicate : α → Bool)
    (data : Array α) (indices : Array Int) (reverse endStable : Bool) (lo hi : Int) :
    Jl (Array Int × Int × Int) := do
  let window : ArrayWindow := ⟨1, 1, indices.size⟩
  let test : Int → StateT (Array Int) (Except JlError) Bool := fun index state => do
    let value ← arrayRead data index
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
      Bool (Bool × Array Nat) (ArraySortKeywords Nat) (Array Nat) JlError where
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
    let compare := fun a b : Nat => if order.1 then decide (b < a) else decide (a < b)
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
    let compare := fun a b : Nat => if order.1 then decide (b < a) else decide (a < b)
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

def juliaHashInt (x : Int) : Nat :=
  let m : Nat := 2 ^ 64
  let z : Nat := (((3 * 0xbdd89aa982704029 + m * m : Nat) : Int) - x).toNat % m
  let z : Nat := z ^^^ (z >>> 32)
  let z : Nat := (z * 0x63652a4cd374b267) % m
  z ^^^ (z >>> 33)

def juliaPivot (lo hi : Int) : Int :=
  lo + (((juliaHashInt lo + 2 ^ 64 - lo.toNat) % 2 ^ 64) % (hi - lo + 1).toNat : Nat)

def rangeLt {t : IntTy} (rev : Bool) (a b : JInt t) : Bool :=
  if rev then decide (b.val < a.val) else decide (a.val < b.val)

def addOneInt {t : IntTy} (y : JInt t) : Int :=
  wrapInt (IntTy.promote t .i64) (y.val + 1)

def toKeytype (y : Int) : Jl JInt64 := JInt.convert .i64 y

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
      JInt.convert t (rangeElem f h i.val)
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
  floorInteger := fun x => JInt.convert t x.floor
  ceilInteger := fun x => JInt.convert t x.ceil
  subtract := fun a b => a - b
  fld := JInt.fld
  cld := JInt.cld
  addOne := addOneInt
  toKey := toKeytype
  get := fun (f, h, _, len) i =>
    if 1 ≤ i.val ∧ i.val ≤ len.val then
      JInt.convert t (rangeElem f h i.val)
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
def arrayMissingDirectOpsWithNext {Alg : Type}
    (nextAlgorithm : Alg → Alg)
    (sortWrapped : WithoutMissingVector Int (Array (Option Int)) → Alg → Bool →
      (Int × Int) → Jl (Array (Option Int)))
    (sortVector : Array (Option Int) → Alg → Bool →
      (Int × Int) → Jl (Array (Option Int))) :
    MissingSortOps (Array (Option Int)) (Array (Option Int))
      (WithoutMissingVector Int (Array (Option Int))) Int Int (Option Int)
      Alg Bool Empty (Int × Int) (Array (Option Int)) JlError :=
  { arrayMissingDirectOps with
    nextAlgorithm := nextAlgorithm
    sortWrapped := sortWrapped
    sortVector := sortVector }

def arrayMissingPermutationOpsWithNext {Alg : Type} (data : Array (Option Int))
    (nextAlgorithm : Alg → Alg)
    (sortWrapped : WithoutMissingVector Int (Array (Option Int)) → Alg → Bool →
      (Int × Int) → Jl (Array Int))
    (sortVector : Array Int → Alg → Bool → (Int × Int) → Jl (Array Int)) :
    MissingSortOps (Array Int) (Array (Option Int))
      (WithoutMissingVector Int (Array (Option Int))) Int Int (Option Int)
      Alg Bool Bool (Int × Int) (Array Int) JlError :=
  { arrayMissingPermutationOps data with
    nextAlgorithm := nextAlgorithm
    sortWrapped := sortWrapped
    sortVector := sortVector }

def arrayIEEEDirectOpsWithNext {α Alg : Type} (codec : IEEECodec α)
    (nextAlgorithm : Alg → Alg)
    (sortUnsigned : Array Nat → Alg → Bool → ArraySortKeywords Nat →
      Jl (Array Nat × Option (Array Nat)))
    (sortFallback : Array α → Alg → Bool → ArraySortKeywords Nat →
      Jl (Array α × Option (Array Nat))) :
    IEEEFloatSortOps (Array α) (Array α) (Array Nat) Int Alg Bool Empty Bool
      (ArraySortKeywords Nat) (Array Nat) JlError :=
  { arrayIEEEDirectOps codec with
    nextAlgorithm := nextAlgorithm
    sortUnsigned := sortUnsigned
    sortPermutation := sortFallback
    sortFallback := sortFallback }

def arrayIEEEPermutationOpsWithNext {α Alg : Type} [Inhabited α] (codec : IEEECodec α)
    (nextAlgorithm : Alg → Alg)
    (sortPermutation : Array Int → Alg → (Bool × Array Nat) → ArraySortKeywords Nat →
      Jl (Array Int × Option (Array Nat)))
    (sortFallback : Array Int → Alg → (Bool × Array α) → ArraySortKeywords Nat →
      Jl (Array Int × Option (Array Nat))) :
    IEEEFloatSortOps (Array Int) (Array α) (Array Nat) Int Alg (Bool × Array α)
      Bool (Bool × Array Nat) (ArraySortKeywords Nat) (Array Nat) JlError :=
  { arrayIEEEPermutationOps codec with
    nextAlgorithm := nextAlgorithm
    sortUnsigned := fun values _ order kw =>
      (arrayIEEEPermutationOps codec).sortUnsigned values () order kw
    sortPermutation := sortPermutation
    sortFallback := sortFallback }

def flatSubArraySortOpsWithNext {α Alg : Type} [Inhabited α]
    (original : FlatSortView α)
    (nextAlgorithm : Alg → Alg)
    (sortSlice : Array α → Alg → (α → α → Bool) → ArraySortKeywords α →
      Jl (Array α × Option (Array α))) :
    SubArraySortOps (FlatSortView α) (FlatSortParent α) (Array α) Int Alg
      (α → α → Bool) (ArraySortKeywords α) (FlatSortView α) JlError where
  range := fun kw => .ok (kw.lo, kw.hi)
  parent := FlatSortView.parent
  parentIsArray := fun _ => true
  parentIsVector := fun parent => decide (parent.dimensions = 1)
  spanLessThan100 := fun lo hi => decide (hi - lo < 100)
  offsetIsZero := fun view => decide (view.offset = 0)
  vectorizeParent := fun parent => .ok parent.storage
  nextAlgorithm := nextAlgorithm
  sortView := fun view alg order kw => do
    let values ← flatSortViewValues view
    let (sorted, _) ← sortSlice values alg order kw
    let mut parent := view.parent.storage
    for index in arrayIndexRange kw.lo kw.hi do
      let value ← arrayRead sorted index
      parent ← arrayWrite parent (view.offset + index) value
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
  | .bracketedSort _ _ | .partialQuickSort _ => false

end JuliaLean.base.sort
