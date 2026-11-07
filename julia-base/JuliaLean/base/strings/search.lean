import JuliaLean.base.regex
import JuliaLean.Core
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.string
import JuliaLean.base.strings.substring
import JuliaLean.base.operators
import JuliaLean.base.char
import JuliaLean.base.array
import JuliaLean.base.iterators
import JuliaLean.base.generator
import JuliaLean.base.gmp

/-!
# Model of `base/strings/search.jl`

The source revision is `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit
platform. Indices and integer arithmetic use `JInt64`; a `Char` is its stored
UInt32 UTF-8 representation, so malformed bytes are retained. String,
SubString and StringView implementations remain generic. The imported models
supply their storage types. Later-loaded, user-extensible, iterator and C
runtime operations are typed parameters.

Finite loops use one step per possible source byte or pattern element. The
interface laws in the properties file require advancing character indices,
correct byte-search positions and finite iterator lengths. No valid-UTF-8
precondition is imposed.
-/

namespace JuliaLean.base.strings.search

open JuliaLean

/--
Julia source: base/strings/search.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type AbstractPattern end
```
-/
class AbstractPattern (P : Type) : Prop where

abbrev Index := JuliaLean.base.strings.basic.Index
abbrev JChar := UInt32
abbrev Pointer := JInt .u64
abbrev JString := JuliaLean.base.strings.string.JString

def int (z : Int) : Index := JInt.lit .i64 z

def imin (a b : Index) : Index := if a.val < b.val then a else b
def imax (a b : Index) : Index := if a.val < b.val then b else a

structure MatchRange where
  first : Index
  last : Index
  deriving DecidableEq, Repr
inductive DenseSearchIndex (I : Type) where
  | sourceInteger (value : I)
  | juliaInt (value : Index)

def rangeEmpty (r : MatchRange) : Bool := r.last.val < r.first.val

structure IntegerOps (I E : Type) where
  value : I → Int
  toInt : I → Except E Index

structure SearchStringOps (S C E : Type) where
  ncodeunits : S → Index
  iterationBound : S → Nat
  lastindex : S → Except E Index
  nextind : S → Index → Except E Index
  prevind : S → Index → Except E Index
  isvalid : S → Index → Except E Bool
  getindex : S → Index → Except E C
  iterate : S → Index → Except E (Option (C × Index))
  boundsError : S → Int → E
  stringIndexError : S → Index → E
  somethingError : E

structure ByteOps (A B E : Type) where
  firstindex : A → Index
  lastindex : A → Index
  length : A → Index
  getindex : A → Index → Except E B
  value : B → Int
  zero : B
  boundsError : A → Int → E

/--
Julia source: base/strings/search.jl:45-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct FwCharPosIter{S}
    string::S # S is assumed to be either String, StringView or SubString of those
    char::Char
    # Char searchers search for the last UTF8 byte, because this byte tends to
    # have the most variety in real texts, so any individual value is rarer.
    # This allows more work to be done in the fast path using memchr.
    last_char_byte::UInt8
end
```
-/
structure FwCharPosIter (S : Type) where
  string : S
  char : JChar
  lastCharByte : UInt8

/--
Julia source: base/strings/search.jl:96-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct RvCharPosIter{S}
    string::S # S is assumed to be String, StringView or SubString of those
    char::Char
    last_char_byte::UInt8
end
```
-/
structure RvCharPosIter (S : Type) where
  string : S
  char : JChar
  lastCharByte : UInt8

inductive IteratorSizeValue where
  | sizeUnknown
  deriving DecidableEq

structure Fix2 (A B R : Type) where
  function : A → B → R
  fixed : B

def applyFix2 {A B R : Type} (f : Fix2 A B R) (a : A) : R :=
  f.function a f.fixed

/-- Exceptions `E`, and `none` for a search that does not terminate. -/
abbrev SearchM (E α : Type) := ExceptT E Option α

def liftE {E α : Type} (x : Except E α) : SearchM E α := ExceptT.mk (some x)

/-- Bridges the common AbstractString interface to the existing basic model. -/
def fromBasic {S R C CU CT E : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R C CU CT E) :
    SearchStringOps S C E where
  ncodeunits := ops.ncodeunits
  iterationBound := ops.iterationBound
  lastindex := ops.lastindex
  nextind s i := ops.nextind s i (int 1)
  prevind s i := ops.prevind s i (int 1)
  isvalid := ops.isvalid
  getindex := JuliaLean.base.strings.basic.getindexString ops
  iterate := ops.iterateAt
  boundsError s z := ops.boundsError s (int z)
  stringIndexError := ops.stringIndexError
  somethingError := ops.tupleTypeError

/--
Julia source: base/strings/search.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_standalone_byte(x::UInt8) = (x < 0x80) | (x > 0xf7)
```
-/
def isStandaloneByte (x : UInt8) : Bool := (x < 0x80) || (x > 0xf7)

/--
Julia source: base/strings/search.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(s::Type{<:Union{FwCharPosIter, RvCharPosIter}}) = SizeUnknown()
```
-/
def iteratorSize (_S : Type) : IteratorSizeValue := .sizeUnknown

/--
Julia source: base/strings/search.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:Union{FwCharPosIter, RvCharPosIter}}) = Int
```
-/
def iteratorEltype (_S : Type) : Type := Index

/--
Julia source: base/strings/search.jl:138-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function try_next(x, state)
    y = iterate(x, state)
    y === nothing ? nothing : first(y)
end
```
-/
def tryNext {A St B E : Type} (iterate : A → St → Except E (Option (B × St)))
    (x : A) (state : St) : Except E (Option B) := do
  let y ← iterate x state
  pure (y.map (·.1))

def indexOps {E : Type} : IntegerOps Index E where
  value i := i.val
  toInt i := .ok i

/-- `findnextPredicateLoop` (search.jl:349-352 `while i <= e`) for a predicate that
may throw or not terminate (R9-7's `in` over a user collection's `iterate`); R3-3's `whileLoop`
form needs a total step. -/
def findnextPredicateLoop {S C E : Type} (ops : SearchStringOps S C E)
    (testf : C → SearchM E Bool) (s : S) (e : Index) (i : Index) : SearchM E (Option Index) :=
  if i.val ≤ e.val then do
    let c ← liftE (ops.getindex s i)
    let hit ← testf c
    if hit then pure (some i)
    else do
      let next ← liftE (ops.nextind s i)
      findnextPredicateLoop ops testf s e next
  else pure none
partial_fixpoint

/-- `findprevPredicateLoop` (search.jl:674-677 `while i >= 1`). -/
def findprevPredicateLoop {S C E : Type} (ops : SearchStringOps S C E)
    (testf : C → SearchM E Bool) (s : S) (i : Index) : SearchM E (Option Index) :=
  if i.val ≥ 1 then do
    let c ← liftE (ops.getindex s i)
    let hit ← testf c
    if hit then pure (some i)
    else do
      let next ← liftE (ops.prevind s i)
      findprevPredicateLoop ops testf s next
  else pure none
partial_fixpoint

/--
Julia source: base/strings/search.jl:343-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(testf::Function, s::AbstractString, i::Integer)
    i = Int(i)
    z = ncodeunits(s) + 1
    1 ≤ i ≤ z || throw(BoundsError(s, i))
    @inbounds i == z || isvalid(s, i) || string_index_err(s, i)
    e = lastindex(s)
    while i <= e
        testf(@inbounds s[i]) && return i
        i = @inbounds nextind(s, i)
    end
    return nothing
end
```
-/
def findnextPredicate {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I) :
    SearchM E (Option Index) := do
  let i ← liftE (ix.toInt start)
  let z := ops.ncodeunits s + int 1
  if !(1 ≤ i.val && i.val ≤ z.val) then throw (ops.boundsError s i.val)
  if i != z then
    if !(← liftE (ops.isvalid s i)) then throw (ops.stringIndexError s i)
  let e ← liftE (ops.lastindex s)
  findnextPredicateLoop ops testf s e i

/--
Julia source: base/strings/search.jl:668-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(testf::Function, s::AbstractString, i::Integer)
    i = Int(i)
    z = ncodeunits(s) + 1
    0 ≤ i ≤ z || throw(BoundsError(s, i))
    i == z && return nothing
    @inbounds i == 0 || isvalid(s, i) || string_index_err(s, i)
    while i >= 1
        testf(@inbounds s[i]) && return i
        i = @inbounds prevind(s, i)
    end
    return nothing
end
```
-/
def findprevPredicate {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I) :
    SearchM E (Option Index) := do
  let i ← liftE (ix.toInt start)
  let z := ops.ncodeunits s + int 1
  if !(0 ≤ i.val && i.val ≤ z.val) then throw (ops.boundsError s i.val)
  if i == z then return none
  if i.val != 0 then
    if !(← liftE (ops.isvalid s i)) then throw (ops.stringIndexError s i)
  findprevPredicateLoop ops testf s i

/-- search.jl:380 `all(splat(==), zip(SubString(s, ii), a))` with `a = Iterators.Stateful(trest)`,
lazily. `look` is `a.nextvalstate`. Each `zip` step (iterators.jl:448-460) first asks every
component's `isdone`: the `SubString`'s is `missing` (essentials.jl:1601) and `a`'s is
`a.nextvalstate === nothing` (iterators.jl:1607), so an empty `a` ends `zip` with nothing
iterated. Otherwise it iterates the `SubString` (the `missing` pass), ending if that returns
`nothing`, then `a` (`popfirst!`, iterators.jl:1609-1618, which iterates `trest` once more,
`iterate(t, st)` by iterators.jl:732). `all` (anyall.jl:207-218) applies `==` to the pair: a
`missing` sets `anymissing` and iteration continues, a `false` stops it, and at the end the
result is `missing` if `anymissing`, else `true`. Returns `matched` and `a.nextvalstate`. -/
def zipAllForward {SubSt C D TSt E : Type}
    (iterateSub : Option SubSt → SearchM E (Option (C × SubSt)))
    (iterateRest : TSt → SearchM E (Option (D × TSt)))
    (equal : C → D → SearchM E operators.Truth) (anymissing : Bool)
    (subState : Option SubSt) (look : Option (D × TSt)) :
    SearchM E (operators.Truth × Option (D × TSt)) := do
  match look with
  | none => pure (if anymissing then .missing else .true, none)
  | some (v, tst) =>
      match ← iterateSub subState with
      | none => pure (if anymissing then .missing else .true, look)
      | some (c, sst) =>
          let look' ← iterateRest tst
          match ← equal c v with
          | .missing => zipAllForward iterateSub iterateRest equal true (some sst) look'
          | .true => zipAllForward iterateSub iterateRest equal anymissing (some sst) look'
          | .false => pure (.false, look')
partial_fixpoint

/-- search.jl:696 `all(splat(==), zip(a, (x[2] for x in b)))`, lazily: both `isdone`s are
known (`a`'s by iterators.jl:1607, the generator's is `b`'s by generator.jl:59), so a step ends
`zip` when either `Stateful` is empty and otherwise pops `a`, then `b` (iterators.jl:443-460,
the `false` pass in order), then applies `==`, with `all`'s `anymissing` (anyall.jl:207-218).
Returns `matched` and both lookaheads. -/
def zipAllReverse {D RSt C PSt E : Type}
    (iterateRest : RSt → SearchM E (Option (D × RSt)))
    (iteratePairs : PSt → SearchM E (Option ((Index × C) × PSt)))
    (equal : D → C → SearchM E operators.Truth) (anymissing : Bool) (lookA : Option (D × RSt))
    (lookB : Option ((Index × C) × PSt)) :
    SearchM E (operators.Truth × Option (D × RSt) × Option ((Index × C) × PSt)) := do
  match lookA, lookB with
  | some (d, ast), some ((_, c), bst) =>
      let lookA' ← iterateRest ast
      let lookB' ← iteratePairs bst
      match ← equal d c with
      | .missing => zipAllReverse iterateRest iteratePairs equal true lookA' lookB'
      | .true => zipAllReverse iterateRest iteratePairs equal anymissing lookA' lookB'
      | .false => pure (.false, lookA', lookB')
  | _, _ => pure (if anymissing then .missing else .true, lookA, lookB)
partial_fixpoint

/--
Julia source: base/strings/search.jl:386-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_searchindex(s::AbstractString, t::AbstractChar, i::Integer) = something(findnext(isequal(t), s, i), 0)
```
-/
def searchindexChar {S C I E : Type}
    (findnext : C → S → I → Except E (Option Index)) (s : S) (t : C) (i : I) : Except E Index := do
  pure ((← findnext t s i).getD (int 0))

/--
Julia source: base/strings/search.jl:388-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _search_bloom_mask(c)
    UInt64(1) << (c & 63)
end
```
-/
def searchBloomMask {C N R E : Type} (band : C → Index → Except E N)
    (shift : JInt .u64 → N → Except E R) (c : C) : Except E R := do
  shift (JInt.lit .u64 1) (← band c (int 63))

/--
Julia source: base/strings/search.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nthbyte(s::DenseUTF8String, i) = codeunit(s, i)
```
-/
def nthStringByte {S I B E : Type} (codeunit : S → I → Except E B)
    (s : S) (i : I) : Except E B := codeunit s i

/--
Julia source: base/strings/search.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nthbyte(t::AbstractVector, index) = t[index + (firstindex(t)-1)]
```
-/
def nthVectorByte {A I J K B E : Type} (firstindex : A → J)
    (subOne : J → Except E K) (add : I → K → Except E J)
    (getindex : A → J → Except E B) (t : A) (index : I) : Except E B := do
  getindex t (← add index (← subOne (firstindex t)))

def vectorNth {A B E : Type} (ops : ByteOps A B E) (a : A) (i : Index) : Except E B :=
  nthVectorByte ops.firstindex (fun j => .ok (j - int 1))
    (fun i j => .ok (i + j)) ops.getindex a i

def byteBloom {B E : Type} (value : B → Int) (b : B) : Except E UInt64 :=
  searchBloomMask
    (fun c n => .ok ((BitVec.ofInt 64 (value c) &&& BitVec.ofInt 64 n.val).toNat))
    (fun x n => .ok (UInt64.ofNat x.val.toNat <<< UInt64.ofNat n)) b

def forwardMask {A B E : Type} (ops : ByteOps A B E) (t : A) (n : Index) (tlast : B) :
    Except E (UInt64 × Index) :=
  (List.range n.val.toNat).foldlM (fun (acc : UInt64 × Index) j0 => do
    let j := int (Int.ofNat j0 + 1)
    let bloomMask := acc.1 ||| (← byteBloom ops.value (← vectorNth ops t j))
    let same := ops.value (← vectorNth ops t j) == ops.value tlast
    let skip := if same && j.val < n.val then n - j - int 1 else acc.2
    pure (bloomMask, skip)) (0, n - int 1)

def reverseMask {A B E : Type} (ops : ByteOps A B E) (t : A) (n : Index) (tfirst : B) :
    Except E (UInt64 × Index) :=
  (List.range n.val.toNat).reverse.foldlM (fun (acc : UInt64 × Index) j0 => do
    let j := int (Int.ofNat j0 + 1)
    let bloomMask := acc.1 ||| (← byteBloom ops.value (← vectorNth ops t j))
    let same := ops.value (← vectorNth ops t j) == ops.value tfirst
    let skip := if same && j.val > 1 then j - int 2 else acc.2
    pure (bloomMask, skip)) (0, n - int 1)

/-- search.jl:437-443 inner `while j < n - 1` comparison. -/
def forwardCompare {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (i n : Index) (j : Index) : SearchM E Index := do
  if j.val < (n - int 1).val then
    let left ← liftE (vectorNth sops s (i + j + int 1))
    let right ← liftE (vectorNth tops t (j + int 1))
    if sops.value left != tops.value right then pure j
    else forwardCompare sops tops s t i n (j + int 1)
  else pure j
partial_fixpoint

/-- search.jl:755-761 inner `while j < n` comparison. -/
def reverseCompare {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (i n : Index) (j : Index) : SearchM E Index := do
  if j.val < n.val then
    let left ← liftE (vectorNth sops s (i + j))
    let right ← liftE (vectorNth tops t (j + int 1))
    if sops.value left != tops.value right then pure j
    else reverseCompare sops tops s t i n (j + int 1)
  else pure j
partial_fixpoint

/-- search.jl:434-463 `while i <= w`. -/
def searchBytesLoop {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (n w : Index) (mask : UInt64) (skip : Index) (tlast : C)
    (sentinel : Index) (i : Index) : SearchM E Index := do
  if i.val > w.val then pure sentinel
  else
    let next ← (do
      if sops.value (← liftE (vectorNth sops s (i + n))) == tops.value tlast then
        let j ← forwardCompare sops tops s t i n (int 0)
        if j == n - int 1 then pure (Sum.inl (i + sops.firstindex s))
        else if i.val < w.val then
          let bit ← liftE (byteBloom sops.value (← liftE (vectorNth sops s (i + n + int 1))))
          pure (Sum.inr (if mask &&& bit == 0 then i + n else i + skip))
        else pure (Sum.inr (i + skip))
      else if i.val < w.val then
        let bit ← liftE (byteBloom sops.value (← liftE (vectorNth sops s (i + n + int 1))))
        pure (Sum.inr (if mask &&& bit == 0 then i + n else i))
      else pure (Sum.inr i) : SearchM E (Index ⊕ Index))
    match next with
    | .inl found => pure found
    | .inr i => searchBytesLoop sops tops s t n w mask skip tlast sentinel (i + int 1)
partial_fixpoint

/-- search.jl:752-780 `while i > 0`. -/
def rsearchBytesLoop {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (n : Index) (mask : UInt64) (skip : Index) (tfirst : C)
    (sentinel : Index) (i : Index) : SearchM E Index := do
  if i.val ≤ 0 then pure sentinel
  else
    let next ← (do
      if sops.value (← liftE (vectorNth sops s i)) == tops.value tfirst then
        let j ← reverseCompare sops tops s t i n (int 1)
        if j == n then pure (Sum.inl (i + sentinel))
        else if i.val > 1 then
          let bit ← liftE (byteBloom sops.value (← liftE (vectorNth sops s (i - int 1))))
          pure (Sum.inr (if mask &&& bit == 0 then i - n else i - skip))
        else pure (Sum.inr (i - skip))
      else if i.val > 1 then
        let bit ← liftE (byteBloom sops.value (← liftE (vectorNth sops s (i - int 1))))
        pure (Sum.inr (if mask &&& bit == 0 then i - n else i))
      else pure (Sum.inr i) : SearchM E (Index ⊕ Index))
    match next with
    | .inl found => pure found
    | .inr i => rsearchBytesLoop sops tops s t n mask skip tfirst sentinel (i - int 1)
partial_fixpoint

/--
Julia source: base/strings/search.jl:401-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _searchindex(s::AbstractVector{<:Union{Int8,UInt8}},
                      t::AbstractVector{<:Union{Int8,UInt8}},
                      _i::Integer)
    sentinel = firstindex(s) - 1
    n = length(t)
    m = length(s)
    i = Int(_i) - sentinel
    (i < 1 || i > m+1) && throw(BoundsError(s, _i))

    if n == 0
        return 1 <= i <= m+1 ? max(1, i) : sentinel
    elseif m == 0
        return sentinel
    elseif n == 1
        return something(findnext(isequal(_nthbyte(t,1)), s, i), sentinel)
    end

    w = m - n
    if w < 0 || i - 1 > w
        return sentinel
    end

    bloom_mask = UInt64(0)
    skip = n - 1
    tlast = _nthbyte(t,n)
    for j in 1:n
        bloom_mask |= _search_bloom_mask(_nthbyte(t,j))
        if _nthbyte(t,j) == tlast && j < n
            skip = n - j - 1
        end
    end

    i -= 1
    while i <= w
        if _nthbyte(s,i+n) == tlast
            # check candidate
            j = 0
            while j < n - 1
                if _nthbyte(s,i+j+1) != _nthbyte(t,j+1)
                    break
                end
                j += 1
            end

            # match found
            if j == n - 1
                # restore in case `s` is an OffsetArray
                return i+firstindex(s)
            end

            # no match, try to rule out the next character
            if i < w && bloom_mask & _search_bloom_mask(_nthbyte(s,i+n+1)) == 0
                i += n
            else
                i += skip
            end
        elseif i < w
            if bloom_mask & _search_bloom_mask(_nthbyte(s,i+n+1)) == 0
                i += n
            end
        end
        i += 1
    end

    sentinel
end
```
-/
def searchindexBytes {A T B C I E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (findnext : C → A → Index → Except E (Option Index)) (ix : IntegerOps I E)
    (s : A) (t : T) (start : I) : SearchM E Index := do
  let sentinel := sops.firstindex s - int 1
  let n := tops.length t
  let m := sops.length s
  let i := (← liftE (ix.toInt start)) - sentinel
  if i.val < 1 || i.val > (m + int 1).val then
    throw (sops.boundsError s (ix.value start))
  if n.val == 0 then
    return if 1 ≤ i.val && i.val ≤ (m + int 1).val then imax (int 1) i else sentinel
  else if m.val == 0 then return sentinel
  else if n.val == 1 then
    return (← liftE (do findnext (← vectorNth tops t (int 1)) s i)).getD sentinel
  let w := m - n
  if w.val < 0 || (i - int 1).val > w.val then return sentinel
  let tlast ← liftE (vectorNth tops t n)
  let (bloomMask, skip) ← liftE (forwardMask tops t n tlast)
  searchBytesLoop sops tops s t n w bloomMask skip tlast sentinel (i - int 1)

/--
Julia source: base/strings/search.jl:721-783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _rsearchindex(s::AbstractVector{<:Union{Int8,UInt8}}, t::AbstractVector{<:Union{Int8,UInt8}}, _k::Integer)
    sentinel = firstindex(s) - 1
    n = length(t)
    m = length(s)
    k = Int(_k) - sentinel
    k < 0 && throw(BoundsError(s, _k))

    if n == 0
        return 0 <= k <= m ? max(k, 1) : sentinel
    elseif m == 0
        return sentinel
    elseif n == 1
        return something(findprev(isequal(_nthbyte(t,1)), s, k), sentinel)
    end

    w = m - n
    if w < 0 || k <= 0
        return sentinel
    end

    bloom_mask = UInt64(0)
    skip = n - 1
    tfirst = _nthbyte(t,1)
    for j in n:-1:1
        bloom_mask |= _search_bloom_mask(_nthbyte(t,j))
        if _nthbyte(t,j) == tfirst && j > 1
            skip = j - 2
        end
    end

    i = min(k - n + 1, w + 1)
    while i > 0
        if _nthbyte(s,i) == tfirst
            # check candidate
            j = 1
            while j < n
                if _nthbyte(s,i+j) != _nthbyte(t,j+1)
                    break
                end
                j += 1
            end

            # match found, restore in case `s` is an OffsetArray
            if j == n
                return i + sentinel
            end

            # no match, try to rule out the next character
            if i > 1 && bloom_mask & _search_bloom_mask(_nthbyte(s,i-1)) == 0
                i -= n
            else
                i -= skip
            end
        elseif i > 1
            if bloom_mask & _search_bloom_mask(_nthbyte(s,i-1)) == 0
                i -= n
            end
        end
        i -= 1
    end

    sentinel
end
```
-/
def rsearchindexBytes {A T B C I E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (findprev : C → A → Index → Except E (Option Index)) (ix : IntegerOps I E)
    (s : A) (t : T) (start : I) : SearchM E Index := do
  let sentinel := sops.firstindex s - int 1
  let n := tops.length t
  let m := sops.length s
  let k := (← liftE (ix.toInt start)) - sentinel
  if k.val < 0 then throw (sops.boundsError s (ix.value start))
  if n.val == 0 then
    return if 0 ≤ k.val && k.val ≤ m.val then imax k (int 1) else sentinel
  else if m.val == 0 then return sentinel
  else if n.val == 1 then
    return (← liftE (do findprev (← vectorNth tops t (int 1)) s k)).getD sentinel
  let w := m - n
  if w.val < 0 || k.val ≤ 0 then return sentinel
  let tfirst ← liftE (vectorNth tops t (int 1))
  let (bloomMask, skip) ← liftE (reverseMask tops t n tfirst)
  rsearchBytesLoop sops tops s t n bloomMask skip tfirst sentinel (imin (k - n + int 1) (w + int 1))

/--
Julia source: base/strings/search.jl:468-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _search(s::Union{AbstractString,AbstractVector{<:Union{Int8,UInt8}}},
                 t::Union{AbstractString,AbstractChar,AbstractVector{<:Union{Int8,UInt8}}},
                 i::Integer)
    idx = _searchindex(s,t,i)
    if isempty(t)
        idx:idx-1
    elseif idx >= firstindex(s)
        idx:(idx + lastindex(t) - firstindex(t))
    else
        nothing
    end
end
```
-/
def searchRange {S T I E : Type} (searchindex : S → T → I → SearchM E Index)
    (isempty : T → Bool) (firstindexS : S → Except E Index)
    (firstindexT lastindexT : T → Except E Index)
    (s : S) (t : T) (i : I) : SearchM E (Option MatchRange) := do
  let idx ← searchindex s t i
  if isempty t then return some ⟨idx, idx - int 1⟩
  else if idx.val ≥ (← liftE (firstindexS s)).val then
    let last ← liftE (lastindexT t)
    let first ← liftE (firstindexT t)
    return some ⟨idx, idx + last - first⟩
  else return none

/--
Julia source: base/strings/search.jl:785-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _rsearch(s::Union{AbstractString,AbstractVector{<:Union{Int8,UInt8}}},
                  t::Union{AbstractString,AbstractChar,AbstractVector{<:Union{Int8,UInt8}}},
                  i::Integer)
    idx = _rsearchindex(s,t,i)
    if isempty(t)
        idx:idx-1
    elseif idx > firstindex(s) - 1
        idx:(idx + lastindex(t) - firstindex(t))
    else
        nothing
    end
end
```
-/
def rsearchRange {S T I E : Type} (rsearchindex : S → T → I → SearchM E Index)
    (isempty : T → Bool) (firstindexS : S → Except E Index)
    (firstindexT lastindexT : T → Except E Index)
    (s : S) (t : T) (i : I) : SearchM E (Option MatchRange) := do
  let idx ← rsearchindex s t i
  if isempty t then return some ⟨idx, idx - int 1⟩
  else if idx.val > ((← liftE (firstindexS s)) - int 1).val then
    let last ← liftE (lastindexT t)
    let first ← liftE (firstindexT t)
    return some ⟨idx, idx + last - first⟩
  else return none

/--
Julia source: base/strings/search.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(t::AbstractString, s::AbstractString, start::Integer) = _search(s, t, Int(start))
```
-/
def findnextString {S T I E : Type} (ix : IntegerOps I E)
    (search : S → T → Index → SearchM E (Option MatchRange))
    (t : T) (s : S) (start : I) : SearchM E (Option MatchRange) := do
  search s t (← liftE (ix.toInt start))

/--
Julia source: base/strings/search.jl:821-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(t::AbstractString, s::AbstractString, i::Integer) = _rsearch(s, t, Int(i))
```
-/
def findprevString {S T I E : Type} (ix : IntegerOps I E)
    (rsearch : S → T → Index → SearchM E (Option MatchRange))
    (t : T) (s : S) (start : I) : SearchM E (Option MatchRange) := do
  rsearch s t (← liftE (ix.toInt start))

/--
Julia source: base/strings/search.jl:526-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(ch::AbstractChar, string::AbstractString, start::Integer) =
    findnext(==(ch), string, start)
```
-/
def findnextCharWrapper {S C D I E : Type} (equal : D → C → Except E Bool)
    (findnext : (D → SearchM E Bool) → S → I → SearchM E (Option Index))
    (ch : C) (s : S) (start : I) : SearchM E (Option Index) :=
  findnext (fun c => liftE (equal c ch)) s start

/--
Julia source: base/strings/search.jl:840-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(ch::AbstractChar, string::AbstractString, start::Integer) =
    findprev(==(ch), string, start)
```
-/
def findprevCharWrapper {S C D I E : Type} (equal : D → C → Except E Bool)
    (findprev : (D → SearchM E Bool) → S → I → SearchM E (Option Index))
    (ch : C) (s : S) (start : I) : SearchM E (Option Index) :=
  findprev (fun c => liftE (equal c ch)) s start

/--
Julia source: base/strings/search.jl:548-551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(pattern::AbstractVector{<:Union{Int8,UInt8}},
         A::AbstractVector{<:Union{Int8,UInt8}},
         start::Integer) =
    _search(A, pattern, start)
```
-/
def findnextVector {A T I E : Type}
    (search : A → T → I → SearchM E (Option MatchRange))
    (pattern : T) (a : A) (start : I) : SearchM E (Option MatchRange) :=
  search a pattern start

/--
Julia source: base/strings/search.jl:859-862 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(pattern::AbstractVector{<:Union{Int8,UInt8}},
         A::AbstractVector{<:Union{Int8,UInt8}},
         start::Integer) =
    _rsearch(A, pattern, start)
```
-/
def findprevVector {A T I E : Type}
    (rsearch : A → T → I → SearchM E (Option MatchRange))
    (pattern : T) (a : A) (start : I) : SearchM E (Option MatchRange) :=
  rsearch a pattern start

/--
Julia source: base/strings/search.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(pattern::AbstractString, string::AbstractString) =
    findnext(pattern, string, firstindex(string))
```
-/
def findfirstString {S T E : Type} (firstindex : S → Index)
    (findnext : T → S → Index → SearchM E (Option MatchRange))
    (pattern : T) (s : S) : SearchM E (Option MatchRange) :=
  findnext pattern s (firstindex s)

/--
Julia source: base/strings/search.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(ch::AbstractChar, string::AbstractString) = findfirst(==(ch), string)
```
-/
def findfirstChar {S C D E : Type} (equal : D → C → Except E Bool)
    (findfirst : (D → Except E Bool) → S → Except E (Option Index))
    (ch : C) (s : S) : Except E (Option Index) :=
  findfirst (fun c => equal c ch) s

/--
Julia source: base/strings/search.jl:338-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(pattern::AbstractVector{<:Union{Int8,UInt8}},
          A::AbstractVector{<:Union{Int8,UInt8}}) =
    _search(A, pattern, firstindex(A))
```
-/
def findfirstVector {A T E : Type} (firstindex : A → Index)
    (search : A → T → Index → SearchM E (Option MatchRange))
    (pattern : T) (a : A) : SearchM E (Option MatchRange) :=
  search a pattern (firstindex a)

/--
Julia source: base/strings/search.jl:568-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(pattern::AbstractString, string::AbstractString) =
    findprev(pattern, string, lastindex(string))
```
-/
def findlastString {S T E : Type} (lastindex : S → Except E Index)
    (findprev : T → S → Index → SearchM E (Option MatchRange))
    (pattern : T) (s : S) : SearchM E (Option MatchRange) := do
  findprev pattern s (← liftE (lastindex s))

/--
Julia source: base/strings/search.jl:584-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(pattern::AbstractVector{<:Union{Int8,UInt8}},
         A::AbstractVector{<:Union{Int8,UInt8}}) =
    findprev(pattern, A, lastindex(A))
```
-/
def findlastVector {A T E : Type} (lastindex : A → Index)
    (findprev : T → A → Index → SearchM E (Option MatchRange))
    (pattern : T) (a : A) : SearchM E (Option MatchRange) :=
  findprev pattern a (lastindex a)

/--
Julia source: base/strings/search.jl:605-605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(ch::AbstractChar, string::AbstractString) = findlast(==(ch), string)
```
-/
def findlastChar {S C D E : Type} (equal : D → C → Except E Bool)
    (findlast : (D → Except E Bool) → S → Except E (Option Index))
    (ch : C) (s : S) : Except E (Option Index) :=
  findlast (fun c => equal c ch) s

def findallLoop {S T E : Type}
    (findnext : T → S → Index → SearchM E (Option MatchRange))
    (nextind : S → Index → Except E Index) (s : S) (t : T) (overlap : Bool) (e : Index) :
    Nat → Index → List MatchRange → SearchM E (List MatchRange)
  | 0, _, found => pure found
  | fuel + 1, i, found => do
      match ← findnext t s i with
      | none => pure found
      | some r =>
          let found := found ++ [r]
          let j := if overlap || rangeEmpty r then r.first else r.last
          if j.val > e.val then return found
          let i ← liftE (nextind s j)
          findallLoop findnext nextind s t overlap e fuel i found

/--
Julia source: base/strings/search.jl:886-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
occursin(needle::Union{AbstractString,AbstractChar}, haystack::AbstractString) =
    _searchindex(haystack, needle, firstindex(haystack)) != 0
```
-/
def occursin {S T E : Type} (firstindex : S → Index)
    (searchindex : S → T → Index → SearchM E Index) (needle : T) (haystack : S) : SearchM E Bool := do
  pure ((← searchindex haystack needle (firstindex haystack)).val != 0)

/--
Julia source: base/strings/search.jl:911-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
occursin(haystack) = Base.Fix2(occursin, haystack)
```
-/
def occursinFix {S T E : Type} (firstindex : S → Index)
    (searchindex : S → T → Index → SearchM E Index) (haystack : S) : Fix2 T S (SearchM E Bool) :=
  ⟨occursin firstindex searchindex, haystack⟩

/--
Julia source: base/strings/search.jl:913-913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(::AbstractString, ::AbstractString) = error("use occursin(needle, haystack) for string containment")
```
-/
def inString {S T E : Type} (error : String → E) (_needle : T) (_haystack : S) : Except E Bool :=
  .error (error "use occursin(needle, haystack) for string containment")

/-! ## Typed dispatch instantiations

These helpers select the source-mirrored methods above. They introduce no
alternative search algorithm.
-/

structure BytePatternSearch (A T B C E : Type) where
  source : ByteOps A B E
  pattern : ByteOps T C E
  findnext : C → A → Index → Except E (Option Index)
  findprev : C → A → Index → Except E (Option Index)

def vectorRange {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (a : A) (t : T) (i : I) : SearchM E (Option MatchRange) :=
  searchRange (searchindexBytes cfg.source cfg.pattern cfg.findnext ix)
    (fun t => (cfg.pattern.length t).val == 0)
    (fun a => .ok (cfg.source.firstindex a)) (fun t => .ok (cfg.pattern.firstindex t))
    (fun t => .ok (cfg.pattern.lastindex t)) a t i

def vectorRRange {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (a : A) (t : T) (i : I) : SearchM E (Option MatchRange) :=
  rsearchRange (rsearchindexBytes cfg.source cfg.pattern cfg.findprev ix)
    (fun t => (cfg.pattern.length t).val == 0)
    (fun a => .ok (cfg.source.firstindex a)) (fun t => .ok (cfg.pattern.firstindex t))
    (fun t => .ok (cfg.pattern.lastindex t)) a t i

def vectorNext {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (t : T) (a : A) (i : I) : SearchM E (Option MatchRange) :=
  findnextVector (vectorRange cfg ix) t a i

def vectorPrev {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (t : T) (a : A) (i : I) : SearchM E (Option MatchRange) :=
  findprevVector (vectorRRange cfg ix) t a i

def vectorFirst {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (t : T) (a : A) : SearchM E (Option MatchRange) :=
  findfirstVector cfg.source.firstindex (vectorRange cfg indexOps) t a

def vectorLast {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (t : T) (a : A) : SearchM E (Option MatchRange) :=
  findlastVector cfg.source.lastindex (vectorPrev cfg indexOps) t a

/-! ## Bound callees (search-bind2)

The declarations below bind the callees of the search methods to the installed string, character,
array, iterator and GMP models; only the runtime primitives are typed (see `DenseOps`). -/

section SearchBind
open JuliaLean
open JuliaLean.base.strings.search (Index JChar JString Pointer SearchStringOps IntegerOps ByteOps
  FwCharPosIter RvCharPosIter MatchRange SearchM liftE)
open JuliaLean.base.strings.basic (int)

abbrev SErr := JuliaLean.Strings.SErr
abbrev Sub := JuliaLean.base.strings.substring.SubString JString

/-! ## Exceptions

The bound search methods throw the exceptions of the string models (`SErr`: `BoundsError`,
`StringIndexError`, `ArgumentError`, ...); the `div` of `ncodeunits(::Char)` (char.jl:119-124)
throws an ordinary `JlError`, carried as `SErr.jl`; a failed `::T` assertion is a `TypeError`. -/
inductive NativeError where
  | string (e : SErr)
  | typeError (assertion : String)
  /-- A C library call outside its defined domain (undefined behaviour in C). -/
  | undefinedBehavior (call : String)

def liftS {α : Type} : JuliaLean.Strings.SJl α → Except NativeError α
  | .ok a => .ok a
  | .error e => .error (.string e)

def liftJ {α : Type} : Jl α → Except NativeError α
  | .ok a => .ok a
  | .error e => .error (.string (.jl e))

def boundsErrorN : NativeError := .string (.jl .boundsError)

/-- The decimal `string(::Int)` interpolated by basic.jl's `"n cannot be negative: $n"`. -/
def intString (n : Index) : String := toString n.val

/-- `checkbounds(s, i:j)` (basic.jl:676-678): an empty range, or `1 ≤ i` and `j ≤ ncodeunits(s)`,
else `BoundsError(s, i:j)`. -/
def checkboundsUnitRange (n i j : Index) : Except NativeError Unit :=
  if j.val < i.val || (1 ≤ i.val && j.val ≤ n.val) then .ok () else .error boundsErrorN

/-! ## `String` (base/strings/string.jl), from the installed source models -/

open JuliaLean.base.strings.string

/-- `lastindex(s::String)` (string.jl:249). -/
def stringLastindex (s : JString) : JuliaLean.Strings.SJl Index :=
  lastindexString stringNcodeunits stringBetweenIndex stringBetweenByte stringCodeunitAt s

/-- The runtime primitives behind `getindex(s::String, r::AbstractUnitRange{Int})`
(string.jl): `Csize_t` conversion, `_string_n` (`jl_alloc_string`, src/array.c), `GC.@preserve`
and `unsafe_copyto!` (`memmove`). -/
structure StringRuntime where
  toCsize : JInt .u64 → JuliaLean.Strings.SJl Nat
  allocateString : Nat → JuliaLean.Strings.SJl JString
  preserve : JString → JString → (Unit → JString) → JString
  unsafeCopyTo : Int → Int → Nat → JString → JString

/-- The `AbstractString` methods of `String`. `prevind`/`nextind` with a count are basic.jl's
generic methods, filled in by `stringBasic`. -/
def stringBasicPrimitive (rt : StringRuntime) :
    JuliaLean.base.strings.basic.StringOps JString JString JChar UInt8 Unit NativeError where
  ncodeunits := stringNcodeunits
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit s i := liftS (stringCodeunit s i)
  isvalid s i := .ok (stringIsvalidIndex s i)
  iterateFirst s := .ok (stringIterate s (int 1))
  iterateAt s i := .ok (stringIterate s i)
  iterationBound s := s.bytes.length + 1
  thisind s i := liftS (stringThisind s i)
  prevind _ _ _ := .error (.string (.jl (.methodError "prevind")))
  nextind _ _ _ := .error (.string (.jl (.methodError "nextind")))
  lastindex s := liftS (stringLastindex s)
  getindexSlice s i j := liftS (stringGetindexRange (fun a b => decide (b.val < a.val))
    (fun s i j => if j.val < i.val || (1 ≤ i.val && j.val ≤ (stringNcodeunits s).val) then .ok ()
      else .error (.jl .boundsError))
    rt.toCsize rt.allocateString (fun i => i.val) rt.preserve rt.unsafeCopyTo s i j)
  checkbounds s i := liftS (stringCheckbounds s i)
  checkboundsBool s i := .ok (stringCheckboundsBool s i)
  boundsError _ _ := boundsErrorN
  stringIndexError _ i := .string (.stringIndexError i.val)
  methodError f := .string (.jl (.methodError f))
  argumentError msg := .string (.jl (.argumentError msg))
  tupleTypeError := .typeError "Tuple{Char,Int}"
  isBoundsError
    | .string (.jl .boundsError) => true
    | _ => false
  characters s := JuliaLean.base.strings.basic.collectStringChars
    (fun s i => .ok (stringIterate s i)) s (s.bytes.length + 1) (stringIterate s (int 1))
  sameReference s t := s == t
  equalChar a b := a == b
  lessChar a b := a < b

/-- `prevind(s::AbstractString, i::Int, n::Int)` (basic.jl:505-514) and `nextind` (basic.jl)
over `String`'s own `thisind`/`isvalid`. -/
def stringBasic (rt : StringRuntime) :
    JuliaLean.base.strings.basic.StringOps JString JString JChar UInt8 Unit NativeError :=
  let prim := stringBasicPrimitive rt
  { prim with
    prevind := JuliaLean.base.strings.basic.previndInt prim intString
    nextind := JuliaLean.base.strings.basic.nextindInt prim intString }

/-- The search interface of `String`: `ncodeunits` (string.jl:107), `lastindex` (:249),
`nextind(s::String, i::Int)` (:273), `prevind(s::AbstractString, i::Int)` (basic.jl:503),
`isvalid` (:662), `getindex(s::String, i::Int)` and `iterate(s::String, i::Int)` (:508). -/
def stringSearch (rt : StringRuntime) : SearchStringOps JString JChar NativeError where
  ncodeunits := stringNcodeunits
  iterationBound s := s.bytes.length + 1
  lastindex s := liftS (stringLastindex s)
  nextind s i := liftS (stringNextind s i)
  prevind s i := JuliaLean.base.strings.basic.previndOne (stringBasic rt) s i
  isvalid s i := .ok (stringIsvalidIndex s i)
  getindex s i := liftS (stringGetindex s i)
  iterate s i := .ok (stringIterate s i)
  boundsError _ _ := boundsErrorN
  stringIndexError _ i := .string (.stringIndexError i.val)
  somethingError := .string (.jl (.argumentError "No value arguments present"))

/-! ## `SubString{String}` (base/strings/substring.jl), from the installed source models -/

open JuliaLean.base.strings.substring

/-- `checkbounds(Bool, s::SubString, i)` (basic.jl:206-207). -/
def subCheckboundsBool (s : Sub) (i : Index) : Bool :=
  JuliaLean.base.strings.basic.checkboundsScalar ncodeunitsSubString
    (fun i => decide (1 ≤ i.val)) (fun i n => decide (i.val ≤ n.val)) s i

def subCheckbounds (s : Sub) (i : Index) : Except NativeError Unit :=
  if subCheckboundsBool s i then .ok () else .error boundsErrorN

/-- `codeunit(s::SubString, i)` (substring.jl:144-147): `@boundscheck` honoured when
`boundsChecking`, then `@inbounds codeunit(s.string, s.offset + i)`. -/
def subCodeunitAt (boundsChecking : Bool) (s : Sub) (i : Index) : JuliaLean.Strings.SJl UInt8 :=
  codeunitSubStringAt
    (fun s i => if !boundsChecking || subCheckboundsBool s i then .ok ()
      else .error (.jl .boundsError))
    (fun offset i => .ok (offset + i)) (stringCodeunitAt false) s i

/-- `thisind(s::SubString{String}, i::Int) = _thisind_str(s, i)` (substring.jl:174). -/
def subThisind (s : Sub) (i : Index) : JuliaLean.Strings.SJl Index :=
  thisindSubString (thisindString ncodeunitsSubString stringBetweenIndex stringBetweenByte
    subCodeunitAt) s i

/-- `nextind(s::SubString{String}, i::Int) = _nextind_str(s, i)` (substring.jl:175). -/
def subNextind (s : Sub) (i : Index) : JuliaLean.Strings.SJl Index :=
  nextindSubString (nextindString ncodeunitsSubString stringBetweenIndex stringBetweenByte
    subCodeunitAt) s i

/-- `lastindex(s::SubString{String})` (substring.jl:178). -/
def subLastindex (s : Sub) : JuliaLean.Strings.SJl Index :=
  lastindexSubString subThisind s

/-- `isvalid(s::SubString, i::Integer)` (substring.jl:168-172). -/
def subIsvalid (s : Sub) (i : Index) : Except NativeError Bool :=
  isvalidSubStringAt (fun s i => .ok (subCheckboundsBool s i)) (fun offset i => .ok (offset + i))
    (fun s i => .ok (stringIsvalidIndex s i)) s i

/-- `iterate(s::SubString, i::Integer)` (substring.jl:151-158). -/
def subIterate (s : Sub) (i : Index) : Except NativeError (Option (JChar × Index)) :=
  iterateSubString (fun i z => i.val == z.val) subCheckbounds (fun offset i => .ok (offset + i))
    (fun s i => .ok (stringIterate s i)) s i

/-- `getindex(s::SubString, i::Integer)` (substring.jl:160-163). -/
def subGetindex (s : Sub) (i : Index) : Except NativeError JChar :=
  getindexSubString subCheckbounds (fun offset i => .ok (offset + i))
    (fun s i => liftS (stringGetindex s i)) s i

/-- The `SubString` constructors' callees on a `String` parent (substring.jl:40-115). -/
def stringSubStringOps : SubStringOps JString JChar Unit NativeError where
  ncodeunits := stringNcodeunits
  codeunitType _ := ()
  length s i j := liftS (stringLengthRange s i j)
  checkboundsRange s i j := checkboundsUnitRange (stringNcodeunits s) i j
  checkboundsViewRange s i j := checkboundsUnitRange s.ncodeunits i j
  isvalid s i := .ok (stringIsvalidIndex s i)
  stringIndexError _ i := .string (.stringIndexError i.val)
  boundsError _ _ _ := boundsErrorN
  viewBoundsError _ _ _ := boundsErrorN
  nextind s i := liftS (stringNextind s i)
  firstindex _ := int 1
  thisindParent s i := liftS (stringThisind s i)
  isasciiCodeunits units :=
    .ok (((units.s.string.bytes.drop units.s.offset.val.toNat).take
      units.s.ncodeunits.val.toNat).all (fun b => decide (b.toNat < 128)))
  sizeof := stringNcodeunits

/-- The `AbstractString` methods of `SubString{String}`; `getindex(s, r::AbstractUnitRange)`
is `SubString(s, r)` (substring.jl:322, 110, 112-115). -/
def subBasicPrimitive :
    JuliaLean.base.strings.basic.StringOps Sub Sub JChar UInt8 Unit NativeError where
  ncodeunits := ncodeunitsSubString
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit s i := liftS (subCodeunitAt true s i)
  isvalid := subIsvalid
  iterateFirst s := subIterate s (int 1)
  iterateAt := subIterate
  iterationBound s := s.ncodeunits.val.toNat + 1
  thisind s i := liftS (subThisind s i)
  prevind _ _ _ := .error (.string (.jl (.methodError "prevind")))
  nextind _ _ _ := .error (.string (.jl (.methodError "nextind")))
  lastindex s := liftS (subLastindex s)
  getindexSlice s i j := subStringNested stringSubStringOps s i j
  checkbounds := subCheckbounds
  checkboundsBool s i := .ok (subCheckboundsBool s i)
  boundsError _ _ := boundsErrorN
  stringIndexError _ i := .string (.stringIndexError i.val)
  methodError f := .string (.jl (.methodError f))
  argumentError msg := .string (.jl (.argumentError msg))
  tupleTypeError := .typeError "Tuple{AbstractChar,Int}"
  isBoundsError
    | .string (.jl .boundsError) => true
    | _ => false
  characters s := do
    JuliaLean.base.strings.basic.collectStringChars subIterate s (s.ncodeunits.val.toNat + 1)
      (← subIterate s (int 1))
  sameReference s t := s == t
  equalChar a b := a == b
  lessChar a b := a < b

def subBasic : JuliaLean.base.strings.basic.StringOps Sub Sub JChar UInt8 Unit NativeError :=
  { subBasicPrimitive with
    prevind := JuliaLean.base.strings.basic.previndInt subBasicPrimitive intString
    nextind := JuliaLean.base.strings.basic.nextindInt subBasicPrimitive intString }

def subSearch : SearchStringOps Sub JChar NativeError where
  ncodeunits := ncodeunitsSubString
  iterationBound s := s.ncodeunits.val.toNat + 1
  lastindex s := liftS (subLastindex s)
  nextind s i := liftS (subNextind s i)
  prevind s i := JuliaLean.base.strings.basic.previndOne subBasic s i
  isvalid := subIsvalid
  getindex := subGetindex
  iterate := subIterate
  boundsError _ _ := boundsErrorN
  stringIndexError _ i := .string (.stringIndexError i.val)
  somethingError := .string (.jl (.argumentError "No value arguments present"))

/-! ## `Char` (base/char.jl)

`CharOps.ncodeunits` is effectful: `ncodeunits(c::Char)` (char.jl:119-124) is the installed
`ncodeunits_Char`, whose `div` can throw. `Char(c)::Char` of a `Char` is the identity
constructor (char.jl:71-78, installed `constructor_Same_AbstractChar`). Every search declaration
below that calls `ncodeunits(::Char)` or `last_utf8_byte` takes this effectful form. -/
structure CharOps (C E : Type) where
  toChar : C → Except E JChar
  ncodeunits : JChar → Except E Index

/-- `ncodeunits(c::Char)` (char.jl:119-124) with `sizeof(UInt32) = 4` and `Int` `div`. -/
def charNcodeunits (c : JChar) : Except NativeError Index :=
  JuliaLean.base.char.ncodeunits_Char (JInt.lit .i64 4) (fun x y => liftJ (JInt.div x y))
    JuliaLean.base.char.charBitOps JuliaLean.base.char.iszeroUInt32 c

def charOps : CharOps JChar NativeError where
  toChar c := .ok (JuliaLean.base.char.constructor_Same_AbstractChar c)
  ncodeunits := charNcodeunits

/--
Julia source: base/strings/search.jl:34-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function last_utf8_byte(c::Char)
    u = reinterpret(UInt32, c)
    shift = ((4 - ncodeunits(c)) * 8) & 31
    (u >> shift) % UInt8
end
```
-/
def lastUtf8Byte {E : Type} (ncodeunits : JChar → Except E Index) (c : JChar) :
    Except E UInt8 := do
  let u := c
  let shift := (int 4 - (← ncodeunits c)) * int 8
  let shift := (BitVec.ofInt 64 shift.val &&& BitVec.ofNat 64 31).toNat
  pure (u >>> UInt32.ofNat shift).toUInt8

/--
Julia source: base/strings/search.jl:54-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function FwCharPosIter(s::UTF8String, c::AbstractChar)
    char = Char(c)::Char
    byte = last_utf8_byte(char)
    FwCharPosIter{typeof(s)}(s, char, byte)
end
```
-/
def fwCharPosIter {S C E : Type} (ops : CharOps C E) (s : S) (c : C) :
    Except E (FwCharPosIter S) := do
  let char ← ops.toChar c
  let byte ← lastUtf8Byte ops.ncodeunits char
  pure ⟨s, char, byte⟩

/--
Julia source: base/strings/search.jl:105-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function RvCharPosIter(s::UTF8String, c::AbstractChar)
    char = Char(c)::Char
    byte = last_utf8_byte(char)
    RvCharPosIter{typeof(s)}(s, char, byte)
end
```
-/
def rvCharPosIter {S C E : Type} (ops : CharOps C E) (s : S) (c : C) :
    Except E (RvCharPosIter S) := do
  let char ← ops.toChar c
  let byte ← lastUtf8Byte ops.ncodeunits char
  pure ⟨s, char, byte⟩

/-! ## `Int(i)::Int` of an `Integer` start

`BitInteger` sources (boot.jl:1032-1221 `toInt64`): signed and unsigned sources narrower than
64 bits are exact (`sext_int`/`zext_int`); `Int128` uses `checked_trunc_sint`
(`InexactError(:trunc, ...)`); `UInt64` uses `check_sign_bit` (`InexactError(:convert, ...)`);
`UInt128` checks the sign bit first (`:convert`) and then truncates (`:trunc`). -/
def toInt64Name : IntTy → Int → String
  | .u64, _ => "convert"
  | .u128, v => if v ≥ 2 ^ 127 then "convert" else "trunc"
  | _, _ => "trunc"

def intOps (t : IntTy) : IntegerOps (JInt t) NativeError where
  value x := x.val
  toInt x := liftJ (JInt.convert (toInt64Name t x.val) .i64 x.val)

/-- `Int(x::BigInt)` (gmp.jl:396-407, installed `gmp.convertSigned`): more than one limb, or a
sign change on truncation, is `InexactError(:Int64, Int64, x)`. -/
def bigIntOps : IntegerOps JuliaLean.base.gmp.BigInt NativeError where
  value x := x.val
  toInt x := liftJ (JuliaLean.base.gmp.convertSigned .i64 x)

/-- `Int(x::Bool)` (boot.jl `toInt64(x::Bool) = and_int(zext_int(Int64, x), Int64(1))`). -/
def boolOps : IntegerOps Bool NativeError where
  value b := if b then 1 else 0
  toInt b := .ok (int (if b then 1 else 0))

/-! ## Dense code units of a `String` (`codeunits(s)`, basic.jl:788-789)

`DenseOps.memchrCall`/`memrchrCall` receive the object `a` preserved by `GC.@preserve a`, so
the C call reads `a`'s own storage. `pointer(codeunits(s))` is `jl_string_data(s)`
(src/julia.h), the only runtime primitive. -/
structure DenseOps (A B E : Type) extends ByteOps A B E where
  pointer : A → Pointer
  memchrCall : A → Pointer → JInt .i32 → JInt .u64 → Except E Pointer
  memrchrCall : A → Pointer → JInt .i32 → JInt .u64 → Except E Pointer

/-- ISO C11 7.24.5.1 `memchr(p, c, n)` on an object whose `bytes` start at `base`: the address
of the first of the `n` bytes at `p` equal to `(unsigned char)c`, or `NULL`; a range outside
the object is undefined behaviour. -/
def cMemchr (base : Pointer) (bytes : List UInt8) (p : Pointer) (c : JInt .i32) (n : JInt .u64) :
    Except NativeError Pointer :=
  let off := p.val - base.val
  if off < 0 ∨ off + n.val > bytes.length then .error (.undefinedBehavior "memchr")
  else
    let window := (bytes.drop off.toNat).take n.val.toNat
    match window.findIdx? (fun b => b.toNat == c.val % 256) with
    | some k => .ok (JInt.wrap .u64 (p.val + k))
    | none => .ok (JInt.wrap .u64 0)

/-- glibc `memrchr(p, c, n)` (string/memrchr.c): the address of the last of the `n` bytes at
`p` equal to `(unsigned char)c`, or `NULL`. -/
def cMemrchr (base : Pointer) (bytes : List UInt8) (p : Pointer) (c : JInt .i32) (n : JInt .u64) :
    Except NativeError Pointer :=
  let off := p.val - base.val
  if off < 0 ∨ off + n.val > bytes.length then .error (.undefinedBehavior "memrchr")
  else
    let window := (bytes.drop off.toNat).take n.val.toNat
    match (window.reverse.findIdx? (fun b => b.toNat == c.val % 256)) with
    | some k => .ok (JInt.wrap .u64 (p.val + (window.length - 1 - k)))
    | none => .ok (JInt.wrap .u64 0)

def stringCodeUnits (dataPointer : JString → Pointer) : DenseOps JString UInt8 NativeError where
  firstindex _ := int 1
  lastindex := stringNcodeunits
  length := stringNcodeunits
  getindex s i := liftS (stringCodeunit s i)
  value b := b.toNat
  zero := 0
  boundsError _ _ := boundsErrorN
  pointer := dataPointer
  memchrCall s := cMemchr (dataPointer s) s.bytes
  memrchrCall s := cMemrchr (dataPointer s) s.bytes

/--
Julia source: base/strings/search.jl:182-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memchr(a::DenseUInt8, b::UInt8, i::Int)
    fst = Int(firstindex(a))::Int
    GC.@preserve a begin
        p = pointer(a)
        q = ccall(:memchr, Ptr{UInt8}, (Ptr{UInt8}, Int32, Csize_t), p+i-fst, b, lastindex(a) - i + 1)
    end
    return q == C_NULL ? nothing : (q-p+fst) % Int
end
```
-/
def memchrUInt8 {A E : Type} (ops : DenseOps A UInt8 E) (a : A) (b : UInt8)
    (i : Index) : Except E (Option Index) := do
  let fst := ops.firstindex a
  let p := ops.pointer a
  let q ← ops.memchrCall a (JInt.wrap .u64 (p.val + (i - fst).val))
    (JInt.wrap .i32 (Int.ofNat b.toNat)) (JInt.rem .u64 (ops.lastindex a - i + int 1))
  pure (if q.val = 0 then none else some (int (q.val - p.val + fst.val)))

/--
Julia source: base/strings/search.jl:191-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memchr(a::DenseInt8, b::Int8, i::Int)
    fst = Int(firstindex(a))::Int
    GC.@preserve a begin
        p = Ptr{UInt8}(pointer(a))
        q = ccall(:memchr, Ptr{UInt8}, (Ptr{UInt8}, Int32, Csize_t), p+i-fst, b, lastindex(a) - i + 1)
    end
    return q == C_NULL ? nothing : (q-p+fst) % Int
end
```
-/
def memchrInt8 {A E : Type} (ops : DenseOps A (JInt .i8) E) (a : A) (b : JInt .i8)
    (i : Index) : Except E (Option Index) := do
  let fst := ops.firstindex a
  let p := ops.pointer a
  let q ← ops.memchrCall a (JInt.wrap .u64 (p.val + (i - fst).val))
    (JInt.wrap .i32 b.val) (JInt.rem .u64 (ops.lastindex a - i + int 1))
  pure (if q.val = 0 then none else some (int (q.val - p.val + fst.val)))

/--
Julia source: base/strings/search.jl:246-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memrchr(a::DenseUInt8, b::UInt8, i::Int)
    fst = firstindex(a)
    GC.@preserve a begin
        p = pointer(a)
        q = ccall(:memrchr, Ptr{UInt8}, (Ptr{UInt8}, Int32, Csize_t), p, b, i-fst+1)
    end
    return q == C_NULL ? nothing : (q-p+fst) % Int
end
```
-/
def memrchrUInt8 {A E : Type} (ops : DenseOps A UInt8 E) (a : A) (b : UInt8)
    (i : Index) : Except E (Option Index) := do
  let fst := ops.firstindex a
  let p := ops.pointer a
  let q ← ops.memrchrCall a p (JInt.wrap .i32 (Int.ofNat b.toNat)) (JInt.rem .u64 (i - fst + int 1))
  pure (if q.val = 0 then none else some (int (q.val - p.val + fst.val)))

/--
Julia source: base/strings/search.jl:255-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memrchr(a::DenseInt8, b::Int8, i::Int)
    fst = firstindex(a)
    GC.@preserve a begin
        p = Ptr{UInt8}(pointer(a))
        q = ccall(:memrchr, Ptr{UInt8}, (Ptr{UInt8}, Int32, Csize_t), p, b, i-fst+1)
    end
    return q == C_NULL ? nothing : (q-p+fst) % Int
end
```
-/
def memrchrInt8 {A E : Type} (ops : DenseOps A (JInt .i8) E) (a : A) (b : JInt .i8)
    (i : Index) : Except E (Option Index) := do
  let fst := ops.firstindex a
  let p := ops.pointer a
  let q ← ops.memrchrCall a p (JInt.wrap .i32 b.val) (JInt.rem .u64 (i - fst + int 1))
  pure (if q.val = 0 then none else some (int (q.val - p.val + fst.val)))

/--
Julia source: base/strings/search.jl:175-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(pred::Fix2{<:Union{typeof(isequal),typeof(==)},UInt8}, a::DenseUInt8, i::Integer)
    i = Int(i)::Int
    @boundscheck i < Int(firstindex(a))::Int && throw(BoundsError(a, i))
    i > Int(lastindex(a))::Int && return nothing
    return memchr(a, pred.x, i)
end
```
-/
def findnextUInt8 {A I E : Type} (ops : DenseOps A UInt8 E) (ix : IntegerOps I E)
    (pred : UInt8) (a : A) (start : I) : Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val < (ops.firstindex a).val then throw (ops.boundsError a i.val)
  if i.val > (ops.lastindex a).val then return none
  memchrUInt8 ops a pred i

/--
Julia source: base/strings/search.jl:168-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(pred::Fix2{<:Union{typeof(isequal),typeof(==)},Int8}, a::DenseInt8, i::Integer)
    i = Int(i)::Int
    @boundscheck i < Int(firstindex(a))::Int && throw(BoundsError(a, i))
    i > Int(lastindex(a))::Int && return nothing
    return memchr(a, pred.x, i)
end
```
-/
def findnextInt8 {A I E : Type} (ops : DenseOps A (JInt .i8) E) (ix : IntegerOps I E)
    (pred : JInt .i8) (a : A) (start : I) : Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val < (ops.firstindex a).val then throw (ops.boundsError a i.val)
  if i.val > (ops.lastindex a).val then return none
  memchrInt8 ops a pred i

/--
Julia source: base/strings/search.jl:239-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(pred::Fix2{<:Union{typeof(isequal),typeof(==)},UInt8}, a::DenseUInt8, i::Integer)
    i = Int(i)::Int
    @boundscheck i > Int(lastindex(a))::Int && throw(BoundsError(a, i))
    i < Int(firstindex(a))::Int && return nothing
    memrchr(a, pred.x, i)
end
```
-/
def findprevUInt8 {A I E : Type} (ops : DenseOps A UInt8 E) (ix : IntegerOps I E)
    (pred : UInt8) (a : A) (start : I) : Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val > (ops.lastindex a).val then throw (ops.boundsError a i.val)
  if i.val < (ops.firstindex a).val then return none
  memrchrUInt8 ops a pred i

/--
Julia source: base/strings/search.jl:232-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(pred::Fix2{<:Union{typeof(isequal),typeof(==)},Int8}, a::DenseInt8, i::Integer)
    i = Int(i)::Int
    @boundscheck i > Int(lastindex(a))::Int && throw(BoundsError(a, i))
    i < Int(firstindex(a))::Int && return nothing
    memrchr(a, pred.x, i)
end
```
-/
def findprevInt8 {A I E : Type} (ops : DenseOps A (JInt .i8) E) (ix : IntegerOps I E)
    (pred : JInt .i8) (a : A) (start : I) : Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val > (ops.lastindex a).val then throw (ops.boundsError a i.val)
  if i.val < (ops.firstindex a).val then return none
  memrchrInt8 ops a pred i

/--
Julia source: base/strings/search.jl:915-915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(a::UInt8, b::DenseUInt8) = !isnothing(findfirst(==(a), b))
```
-/
def inUInt8 {A E : Type} (ops : DenseOps A UInt8 E) (a : UInt8) (b : A) : Except E Bool := do
  pure (← findnextUInt8 ops JuliaLean.base.strings.search.indexOps a b (ops.firstindex b)).isSome

/--
Julia source: base/strings/search.jl:916-916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(a::Int8, b::DenseInt8) = !isnothing(findfirst(==(a), b))
```
-/
def inInt8 {A E : Type} (ops : DenseOps A (JInt .i8) E) (a : JInt .i8) (b : A) : Except E Bool := do
  pure (← findnextInt8 ops JuliaLean.base.strings.search.indexOps a b (ops.firstindex b)).isSome

/-! ## Character search on a UTF-8 string (search.jl:34-166, 209-263)

The installed bodies, over the effectful `ncodeunits(::Char)` and the bound dense storage. -/

open JuliaLean.base.strings.search (indexOps isStandaloneByte tryNext imin)

def fwLoop {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A)
    (s : FwCharPosIter S) (scu ncu : Index) : Nat → Index → Except E (Option (Index × Index))
  | 0, _ => .ok none
  | fuel + 1, i => do
      if i.val > scu.val then return none
      let found ← findnextUInt8 bytes indexOps s.lastCharByte (codeunits s.string) i
      match found with
      | none => pure none
      | some found =>
          let i := found + int 1
          let index := i - ncu
          if !(← ops.isvalid s.string index) then
            fwLoop ops bytes codeunits s scu ncu fuel i
          else
            match ← ops.iterate s.string index with
            | none => throw ops.somethingError
            | some (char, _) =>
                if char == s.char then pure (some (index, i))
                else fwLoop ops bytes codeunits s scu ncu fuel i

def rvLoop {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A)
    (s : RvCharPosIter S) (ncu : Index) : Nat → Index → Except E (Option (Index × Index))
  | 0, _ => .ok none
  | fuel + 1, i => do
      if i.val < ncu.val then return none
      let found ← findprevUInt8 bytes indexOps s.lastCharByte (codeunits s.string) i
      match found with
      | none => pure none
      | some found =>
          let index := found - ncu + int 1
          let i := found - int 1
          if !(← ops.isvalid s.string index) then
            rvLoop ops bytes codeunits s ncu fuel i
          else
            match ← ops.iterate s.string index with
            | none => throw ops.somethingError
            | some (char, _) =>
                if char == s.char then pure (some (index, i))
                else rvLoop ops bytes codeunits s ncu fuel i

/--
Julia source: base/strings/search.jl:62-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.iterate(s::FwCharPosIter, i::Int=1)
    scu = ncodeunits(s.string)

    # By definition, if the last byte is a standalone byte, then the char
    # is a single-byte char where the byte can never be a subset of another char.
    # Hence, we can simply search for the occurrence of the byte itself.
    if is_standalone_byte(s.last_char_byte)
        i > scu && return nothing
        i = findnext(==(s.last_char_byte), codeunits(s.string), i)
        i === nothing ? nothing : (i, i + 1)
    else
        ncu = ncodeunits(s.char)
        while true
            i > scu && return nothing
            i = findnext(==(s.last_char_byte), codeunits(s.string), i)
            i === nothing && return nothing
            # Increment i before the continue to avoid infinite loop.
            # Since we search for the last byte in the char, the index has an offset.
            i += 1
            index = i - ncu
            # The byte may be part of a different char, in which case index
            # may be invalid.
            isvalid(s.string, index) || continue
            # Here, we use iterate instead of indexing, because indexing needlessly
            # re-validates the index which we have already done here.
            # This relies on the implementation detail that the iterator state for
            # iterating strings is the same as the byte index.
            char = first(something(iterate(s.string, index)))
            char == s.char && return (index, i)
        end
    end
end
```
-/
def fwIterate {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (ncodeunitsChar : JChar → Except E Index)
    (s : FwCharPosIter S) (i : Index := int 1) : Except E (Option (Index × Index)) := do
  let scu := ops.ncodeunits s.string
  if isStandaloneByte s.lastCharByte then
    if i.val > scu.val then return none
    let found ← findnextUInt8 bytes indexOps s.lastCharByte (codeunits s.string) i
    pure (found.map fun i => (i, i + int 1))
  else
    let ncu ← ncodeunitsChar s.char
    fwLoop ops bytes codeunits s scu ncu (scu.val.toNat + 2) i

/--
Julia source: base/strings/search.jl:117-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.iterate(s::RvCharPosIter, i::Int=ncodeunits(s.string))
    ncu = ncodeunits(s.char)
    if is_standalone_byte(s.last_char_byte)
        i < ncu && return nothing
        i = findprev(==(s.last_char_byte), codeunits(s.string), i)
        i === nothing ? nothing : (i, i - 1)
    else
        i = min(ncodeunits(s.string), i + ncu - 1)
        while true
            i < ncu && return nothing
            i = findprev(==(s.last_char_byte), codeunits(s.string), i)
            i === nothing && return nothing
            index = i - ncu + 1
            i -= 1
            isvalid(s.string, index) || continue
            char = first(something(iterate(s.string, index)))
            char == s.char && return (index, i)
        end
    end
end
```
-/
def rvIterate {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (ncodeunitsChar : JChar → Except E Index)
    (s : RvCharPosIter S) (start : Option Index := none) : Except E (Option (Index × Index)) := do
  let i := start.getD (ops.ncodeunits s.string)
  let ncu ← ncodeunitsChar s.char
  if isStandaloneByte s.lastCharByte then
    if i.val < ncu.val then return none
    let found ← findprevUInt8 bytes indexOps s.lastCharByte (codeunits s.string) i
    pure (found.map fun i => (i, i - int 1))
  else
    let i := imin (ops.ncodeunits s.string) (i + ncu - int 1)
    rvLoop ops bytes codeunits s ncu (i.val.toNat + 2) i

/--
Julia source: base/strings/search.jl:143-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(
    pred::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},
    s::UTF8String,
    i::Integer,
)
    # TODO: Redesign these strange rules for errors, see #54584
    scu = ncodeunits(s)
    i == scu + 1 && return nothing
    @boundscheck if i < 1 || i > scu + 1
        throw(BoundsError(s, i))
    end
    # The most common case is probably searching for an ASCII char.
    # We inline this critical path here to avoid instantiating a
    # FwCharPosIter in the common case.
    c = Char(pred.x)::Char
    u = (reinterpret(UInt32, c) >> 24) % UInt8
    i = Int(i)::Int
    isvalid(s, i) || string_index_err(s, i)
    return if is_standalone_byte(u)
        findnext(==(u), codeunits(s), i)
    else
        try_next(FwCharPosIter(s, c, last_utf8_byte(c)), i)
    end
end
```
-/
def findnextChar {S A C I E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (chars : CharOps C E)
    (ix : IntegerOps I E) (pred : C) (s : S) (start : I) : Except E (Option Index) := do
  let scu := ops.ncodeunits s
  if ix.value start = (scu + int 1).val then return none
  if ix.value start < 1 || ix.value start > (scu + int 1).val then
    throw (ops.boundsError s (ix.value start))
  let c ← chars.toChar pred
  let u := (c >>> 24).toUInt8
  let i ← ix.toInt start
  if !(← ops.isvalid s i) then throw (ops.stringIndexError s i)
  if isStandaloneByte u then
    findnextUInt8 bytes indexOps u (codeunits s) i
  else
    let byte ← lastUtf8Byte chars.ncodeunits c
    tryNext (fun iter state => fwIterate ops bytes codeunits chars.ncodeunits iter state)
      ⟨s, c, byte⟩ i

/--
Julia source: base/strings/search.jl:209-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(
    pred::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},
    s::UTF8String,
    i::Integer,
)
    # TODO: Redesign these strange rules for errors, see #54584
    if i == ncodeunits(s) + 1 || i == 0
        return nothing
    end
    @boundscheck if i < 1 || i > ncodeunits(s) + 1
        throw(BoundsError(s, i))
    end
    # Manually inline the fast path if c is ASCII, as we expect it to often be
    c = Char(pred.x)::Char
    u = (reinterpret(UInt32, c) >> 24) % UInt8
    i = Int(i)::Int
    return if is_standalone_byte(u)
        findprev(==(u), codeunits(s), i)
    else
        try_next(RvCharPosIter(s, c, last_utf8_byte(c)), i)
    end
end
```
-/
def findprevChar {S A C I E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (chars : CharOps C E)
    (ix : IntegerOps I E) (pred : C) (s : S) (start : I) : Except E (Option Index) := do
  if ix.value start = (ops.ncodeunits s + int 1).val || ix.value start = 0 then return none
  if ix.value start < 1 || ix.value start > (ops.ncodeunits s + int 1).val then
    throw (ops.boundsError s (ix.value start))
  let c ← chars.toChar pred
  let u := (c >>> 24).toUInt8
  let i ← ix.toInt start
  if isStandaloneByte u then
    findprevUInt8 bytes indexOps u (codeunits s) i
  else
    let byte ← lastUtf8Byte chars.ncodeunits c
    tryNext (fun iter state => rvIterate ops bytes codeunits chars.ncodeunits iter (some state))
      ⟨s, c, byte⟩ i

/-- `occursin(c::AbstractChar, s::UTF8String)` (search.jl:886-887): `_searchindex(s, c, 1) != 0`
(search.jl:386). -/
def charOccurrence {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (chars : CharOps JChar E)
    (c : JChar) (s : S) : SearchM E Bool :=
  JuliaLean.base.strings.search.occursin JuliaLean.base.strings.basic.firstindexString
    (fun s c i => liftE <| JuliaLean.base.strings.search.searchindexChar
      (findnextChar ops bytes codeunits chars indexOps) s c i) c s

/-! ## Dense string-in-string search (search.jl:395-399, 705-719) -/

structure DenseStringSearch (S T A D E : Type) where
  source : SearchStringOps S JChar E
  pattern : SearchStringOps T JChar E
  sourceBytes : DenseOps A UInt8 E
  patternBytes : ByteOps D UInt8 E
  codeunitsSource : S → A
  codeunitsPattern : T → D
  chars : CharOps JChar E
  /-- The `AbstractString` methods of the source; `sizeof(s)` is the installed
  `sizeofString` (`ncodeunits(s) * sizeof(codeunit(s))`, basic.jl:178). -/
  sourceBasic : JuliaLean.base.strings.basic.StringOps S S JChar UInt8 Unit E

/--
Julia source: base/strings/search.jl:395-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _searchindex(s::DenseUTF8String, t::DenseUTF8String, i::Integer)
    # Check for fast case of a single byte
    lastindex(t) == 1 && return something(findnext(isequal(t[1]), s, i), 0)
    _searchindex(codeunits(s), codeunits(t), i)
end
```
-/
def searchindexDense {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (s : S) (t : T) (i : I) : SearchM E Index := do
  if (← liftE (cfg.pattern.lastindex t)).val == 1 then
    let c ← liftE (cfg.pattern.getindex t (int 1))
    return (← liftE (findnextChar cfg.source cfg.sourceBytes cfg.codeunitsSource cfg.chars ix c s
      i)).getD (int 0)
  JuliaLean.base.strings.search.searchindexBytes cfg.sourceBytes.toByteOps cfg.patternBytes
    (fun b a i => findnextUInt8 cfg.sourceBytes indexOps b a i) ix (cfg.codeunitsSource s)
    (cfg.codeunitsPattern t) i

/--
Julia source: base/strings/search.jl:705-719 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _rsearchindex(s::DenseUTF8String, t::DenseUTF8String, i::Integer)
    # Check for fast case of a single byte
    if lastindex(t) == 1
        return something(findprev(isequal(t[1]), s, i), 0)
    elseif lastindex(t) != 0
        j = i ≤ ncodeunits(s) ? nextind(s, i)-1 : i
        return _rsearchindex(codeunits(s), codeunits(t), j)
    elseif i > sizeof(s)
        return 0
    elseif i == 0
        return 1
    else
        return i
    end
end
```
-/
def rsearchindexDense {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (s : S) (t : T) (start : I) :
    SearchM E (JuliaLean.base.strings.search.DenseSearchIndex I) := do
  if (← liftE (cfg.pattern.lastindex t)).val == 1 then
    let c ← liftE (cfg.pattern.getindex t (int 1))
    return .juliaInt ((← liftE (findprevChar cfg.source cfg.sourceBytes cfg.codeunitsSource
      cfg.chars ix c s start)).getD (int 0))
  else if (← liftE (cfg.pattern.lastindex t)).val != 0 then
    let i ← liftE (ix.toInt start)
    let j ← if ix.value start ≤ (cfg.source.ncodeunits s).val then do
      pure ((← liftE (cfg.source.nextind s i)) - int 1)
    else pure i
    return .juliaInt (← JuliaLean.base.strings.search.rsearchindexBytes cfg.sourceBytes.toByteOps
      cfg.patternBytes (fun b a i => findprevUInt8 cfg.sourceBytes indexOps b a i) indexOps
      (cfg.codeunitsSource s) (cfg.codeunitsPattern t) j)
  else if ix.value start > (JuliaLean.base.strings.basic.sizeofString cfg.sourceBasic s).val then return .juliaInt (int 0)
  else if ix.value start == 0 then return .juliaInt (int 1)
  else return .sourceInteger start

def denseIndex {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (s : S) (t : T) (i : I) : SearchM E Index :=
  searchindexDense cfg ix s t i

def denseRIndex {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (s : S) (t : T) (i : I) : SearchM E Index := do
  match ← rsearchindexDense cfg ix s t i with
  | .sourceInteger value => pure (int (ix.value value))
  | .juliaInt value => pure value

/-- `_search(s, t, i)` (search.jl:468-479). -/
def denseRange {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (s : S) (t : T) (i : Index) : SearchM E (Option MatchRange) :=
  JuliaLean.base.strings.search.searchRange (denseIndex cfg indexOps)
    (fun t => (cfg.pattern.ncodeunits t).val == 0)
    (fun _ => .ok (int 1)) (fun _ => .ok (int 1)) cfg.pattern.lastindex s t i

/-- `_rsearch(s, t, i)` (search.jl:785-796). -/
def denseRRange {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (s : S) (t : T) (i : Index) : SearchM E (Option MatchRange) :=
  JuliaLean.base.strings.search.rsearchRange (denseRIndex cfg indexOps)
    (fun t => (cfg.pattern.ncodeunits t).val == 0)
    (fun _ => .ok (int 1)) (fun _ => .ok (int 1)) cfg.pattern.lastindex s t i

/-- `findnext(t::AbstractString, s::AbstractString, start::Integer)` (search.jl:507). -/
def denseNext {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (t : T) (s : S) (i : I) : SearchM E (Option MatchRange) :=
  JuliaLean.base.strings.search.findnextString ix (denseRange cfg) t s i

/-- `findprev(t::AbstractString, s::AbstractString, i::Integer)` (search.jl:821). -/
def densePrev {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (t : T) (s : S) (i : I) : SearchM E (Option MatchRange) :=
  JuliaLean.base.strings.search.findprevString ix (denseRRange cfg) t s i

/-- `findfirst(pattern::AbstractString, string::AbstractString)` (search.jl:301-302). -/
def denseFirst {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (t : T) (s : S) : SearchM E (Option MatchRange) :=
  JuliaLean.base.strings.search.findfirstString JuliaLean.base.strings.basic.firstindexString
    (denseNext cfg indexOps) t s

/-- `findlast(pattern::AbstractString, string::AbstractString)` (search.jl:568-569). -/
def denseLast {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (t : T) (s : S) : SearchM E (Option MatchRange) :=
  JuliaLean.base.strings.search.findlastString cfg.source.lastindex (densePrev cfg indexOps) t s

/-- `occursin(needle::AbstractString, haystack::AbstractString)` (search.jl:886-887). -/
def denseOccursin {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (t : T) (s : S) : SearchM E Bool :=
  JuliaLean.base.strings.search.occursin JuliaLean.base.strings.basic.firstindexString
    (denseIndex cfg indexOps) t s

/-- `occursin(haystack)` (search.jl:911). -/
def denseOccursinFix {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (s : S) : JuliaLean.base.strings.search.Fix2 T S (SearchM E Bool) :=
  JuliaLean.base.strings.search.occursinFix JuliaLean.base.strings.basic.firstindexString
    (denseIndex cfg indexOps) s

/-! ## Byte-pattern search on a vector: `findnext(isequal(x), a, i)` (array.jl:2470-2481)

The installed array model, over a byte vector with an offset axis. -/
structure ByteVector (B : Type) where
  /-- `firstindex(a)`: an `OffsetArray`'s first axis value (1 for a `Vector`). -/
  first : Index
  data : List B

def byteVectorOps {B : Type} [Inhabited B] (value : B → Int) (zero : B) :
    ByteOps (ByteVector B) B NativeError where
  firstindex a := a.first
  lastindex a := a.first + int (Int.ofNat a.data.length) - int 1
  length a := int (Int.ofNat a.data.length)
  getindex a i :=
    let k := i.val - a.first.val
    if 0 ≤ k ∧ k < a.data.length then .ok (a.data.getD k.toNat default) else .error boundsErrorN
  value := value
  zero := zero
  boundsError _ _ := boundsErrorN

/-- `nextind(A, i) = i + 1` of an `Int` axis, as a step of decreasing `2^63 - i`; the loop exits
at `lastindex(A) ≤ typemax(Int)` before stepping past it. -/
def byteNextind (i : Index) : Except NativeError { j : Index // (2 ^ 63 - j.val).toNat < (2 ^ 63 - i.val).toNat } :=
  if h : i.val < 2 ^ 63 - 1 then
    .ok ⟨int (i.val + 1), by
      have hw : (int (i.val + 1)).val = i.val + 1 := by
        change JuliaLean.wrapInt .i64 (i.val + 1) = i.val + 1
        exact JuliaLean.wrapInt_of_inRange .i64 _ (by
          have := (JuliaLean.wrapInt_bounds .i64 i.val)
          have hi := i.property
          simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hi ⊢
          omega)
      rw [hw]; omega⟩
  else .error (.string (.jl (.overflowError "nextind")))

def byteFindnext {B : Type} [Inhabited B] [DecidableEq B] (ops : ByteOps (ByteVector B) B NativeError)
    (x : B) (a : ByteVector B) (start : Index) : Except NativeError (Option Index) :=
  JuliaLean.base.array.findnext (m := Except NativeError) (Start := Index)
    ops.firstindex ops.lastindex (fun _ s => .ok s) (fun i l => decide (l.val < i.val))
    ops.getindex (fun y => .ok (decide (y = x))) (fun i => (2 ^ 63 - i.val).toNat) byteNextind
    a start

/-- `prevind(A, i) = i - 1` of an `Int` axis, as a step of decreasing `i + 2^63`; the loop exits
at `firstindex(A) ≥ typemin(Int)` before stepping below it. -/
def bytePrevind (i : Index) : Except NativeError { j : Index // (j.val + 2 ^ 63).toNat < (i.val + 2 ^ 63).toNat } :=
  if h : -(2 ^ 63) < i.val then
    .ok ⟨int (i.val - 1), by
      have hw : (int (i.val - 1)).val = i.val - 1 := by
        change JuliaLean.wrapInt .i64 (i.val - 1) = i.val - 1
        exact JuliaLean.wrapInt_of_inRange .i64 _ (by
          have hi := i.property
          simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hi ⊢
          omega)
      rw [hw]; omega⟩
  else .error (.string (.jl (.overflowError "prevind")))

/-- `findprev(isequal(x), a, i)` (array.jl:2666-2677, installed `array.findprev`). -/
def byteFindprev {B : Type} [Inhabited B] [DecidableEq B] (ops : ByteOps (ByteVector B) B NativeError)
    (x : B) (a : ByteVector B) (start : Index) : Except NativeError (Option Index) :=
  JuliaLean.base.array.findprev (m := Except NativeError) (Start := Index)
    ops.firstindex (fun _ s => .ok s) (fun i f => decide (i.val < f.val))
    ops.getindex (fun y => .ok (decide (y = x))) (fun i => (i.val + 2 ^ 63).toNat) bytePrevind
    a start


/-! ## `SubString{S}` and the search interface of an arbitrary `AbstractString` `S`

A user string type contributes only its own methods (`basic.StringOps`: `ncodeunits`,
`codeunit`, `isvalid`, `iterate`, `thisind`, ...) and the exception constructors. Base's
generic methods over it are the installed ones: `SubString` construction (substring.jl:93-115),
`iterate`/`getindex`/`isvalid`/`codeunit` of a `SubString` (substring.jl:144-172),
`thisind`/`prevind`/`nextind`/`lastindex` of an `AbstractString` (basic.jl), `getindex`
(basic.jl:185-189), `isempty` (basic.jl:181), `Iterators.reverse` iteration (basic.jl:775) and
`pairs` (iterators.jl:1725). -/

open JuliaLean.base.strings.basic (StringOps)

/-- `BoundsError`/`StringIndexError` of a `SubString`, and `BoundsError(s, i:j)` of a parent. -/
structure SubErrors (S E : Type) where
  boundsError : SubString S → Index → E
  rangeBoundsError : S → Index → Index → E
  viewBoundsError : SubString S → Index → Index → E
  stringIndexError : SubString S → Index → E

/-- A user `AbstractString` type: its methods, the integer value of its code units, and its
exception constructors (`BoundsError(s, i)` with the caller's `Integer` value, and the
`ArgumentError` of `something(nothing)`). -/
structure StringType (S R C CU CT E : Type) where
  ops : StringOps S R C CU CT E
  codeunitValue : CU → Int
  subErrors : SubErrors S E
  boundsErrorInt : S → Int → E
  somethingError : E

/-- `checkbounds(Bool, s::SubString, i)` (basic.jl:206-207). -/
def subCheckboundsBoolG {S : Type} (s : SubString S) (i : Index) : Bool :=
  JuliaLean.base.strings.basic.checkboundsScalar ncodeunitsSubString
    (fun i => decide (1 ≤ i.val)) (fun i n => decide (i.val ≤ n.val)) s i

/-- `checkbounds(s::SubString, i)` (basic.jl:208-209). -/
def subCheckboundsG {S E : Type} (err : SubErrors S E) (s : SubString S) (i : Index) :
    Except E Unit :=
  if subCheckboundsBoolG s i then .ok () else .error (err.boundsError s i)

/-- The callees of the `SubString` constructors (substring.jl:93-115) on a parent `S`:
`length(s, i, j)` (basic.jl:398-408), `checkbounds(s, i:j)` (basic.jl:676-678), `isvalid`,
`nextind(s, i)` (basic.jl:562), `thisind`, `sizeof(s) = ncodeunits(s) * sizeof(codeunit(s))`
(basic.jl:178), and `isascii(codeunits(ss))` (basic.jl:645-653), which is ASCII exactly when
every code unit is below `0x80`. -/
def subStringOpsOf {S R C CU CT E : Type} (st : StringType S R C CU CT E) :
    SubStringOps S C CT E where
  ncodeunits := st.ops.ncodeunits
  codeunitType := st.ops.codeunitType
  length := JuliaLean.base.strings.basic.lengthInt st.ops
  checkboundsRange s i j :=
    if j.val < i.val || (1 ≤ i.val && j.val ≤ (st.ops.ncodeunits s).val) then .ok ()
    else .error (st.subErrors.rangeBoundsError s i j)
  checkboundsViewRange s i j :=
    if j.val < i.val || (1 ≤ i.val && j.val ≤ s.ncodeunits.val) then .ok ()
    else .error (st.subErrors.viewBoundsError s i j)
  isvalid := st.ops.isvalid
  stringIndexError := st.ops.stringIndexError
  boundsError := st.subErrors.rangeBoundsError
  viewBoundsError := st.subErrors.viewBoundsError
  nextind := JuliaLean.base.strings.basic.nextindOne st.ops
  firstindex _ := int 1
  thisindParent := st.ops.thisind
  isasciiCodeunits units := do
    let s := units.s
    let cus ← (List.range s.ncodeunits.val.toNat).mapM
      (fun k => st.ops.codeunit s.string (s.offset + int (Int.ofNat k + 1)))
    pure (cus.all (fun cu => decide (st.codeunitValue cu < 128)))
  sizeof s := st.ops.ncodeunits s * st.ops.codeunitSize (st.ops.codeunitType s)

/-- `iterate(s::SubString, i::Integer=firstindex(s))` (substring.jl:151-158). -/
def subIterateG {S R C CU CT E : Type} (st : StringType S R C CU CT E) (s : SubString S)
    (i : Index) : Except E (Option (C × Index)) :=
  iterateSubString (fun i z => i.val == z.val) (subCheckboundsG st.subErrors)
    (fun offset i => .ok (offset + i)) st.ops.iterateAt s i

/-- The methods of `SubString{S}` (substring.jl:140-172; `getindex(s, r)` is `SubString(s, r)`,
substring.jl:322). `thisind`, `prevind`, `nextind` and `lastindex` are basic.jl's
`AbstractString` methods, filled in by `subStringBasic`. -/
def subStringBasicPrimitive {S R C CU CT E : Type} (st : StringType S R C CU CT E) :
    StringOps (SubString S) (SubString S) C CU CT E where
  ncodeunits := ncodeunitsSubString
  codeunitType s := st.ops.codeunitType s.string
  codeunitSize := st.ops.codeunitSize
  codeunit := codeunitSubStringAt (subCheckboundsG st.subErrors) (fun offset i => .ok (offset + i))
    st.ops.codeunit
  isvalid := isvalidSubStringAt (fun s i => .ok (subCheckboundsBoolG s i))
    (fun offset i => .ok (offset + i)) st.ops.isvalid
  iterateFirst s := subIterateG st s (int 1)
  iterateAt := subIterateG st
  iterationBound s := s.ncodeunits.val.toNat + 1
  thisind _ _ := .error (st.ops.methodError "thisind")
  prevind _ _ _ := .error (st.ops.methodError "prevind")
  nextind _ _ _ := .error (st.ops.methodError "nextind")
  lastindex _ := .error (st.ops.methodError "lastindex")
  getindexSlice := subStringNested (subStringOpsOf st)
  checkbounds := subCheckboundsG st.subErrors
  checkboundsBool s i := .ok (subCheckboundsBoolG s i)
  boundsError := st.subErrors.boundsError
  stringIndexError := st.subErrors.stringIndexError
  methodError := st.ops.methodError
  argumentError := st.ops.argumentError
  tupleTypeError := st.ops.tupleTypeError
  isBoundsError := st.ops.isBoundsError
  characters s := do
    JuliaLean.base.strings.basic.collectStringChars (subIterateG st) s
      (s.ncodeunits.val.toNat + 1) (← subIterateG st s (int 1))
  sameReference a b := st.ops.sameReference a.string b.string && a.offset == b.offset &&
    a.ncodeunits == b.ncodeunits
  equalChar := st.ops.equalChar
  lessChar := st.ops.lessChar

/-- `thisind(s::AbstractString, i::Int)` (basic.jl), `lastindex(s) = thisind(s, ncodeunits(s))`
(basic.jl:180), `prevind`/`nextind` with a count (basic.jl:505-514, 564-573). -/
def subStringBasic {S R C CU CT E : Type} (st : StringType S R C CU CT E) :
    StringOps (SubString S) (SubString S) C CU CT E :=
  let p := subStringBasicPrimitive st
  let p := { p with thisind := JuliaLean.base.strings.basic.thisindInt p }
  { p with
    lastindex := JuliaLean.base.strings.basic.lastindexString p
    prevind := JuliaLean.base.strings.basic.previndInt p intString
    nextind := JuliaLean.base.strings.basic.nextindInt p intString }

/-- The search interface of a user string: `nextind(s, i)`/`prevind(s, i)` are basic.jl:562 and
:503, `s[i]` is `getindex(s::AbstractString, i::Integer)` (basic.jl:185-189). -/
def searchOpsOf {S R C CU CT E : Type} (st : StringType S R C CU CT E) : SearchStringOps S C E where
  ncodeunits := st.ops.ncodeunits
  iterationBound := st.ops.iterationBound
  lastindex := st.ops.lastindex
  nextind := JuliaLean.base.strings.basic.nextindOne st.ops
  prevind := JuliaLean.base.strings.basic.previndOne st.ops
  isvalid := st.ops.isvalid
  getindex := JuliaLean.base.strings.basic.getindexString st.ops
  iterate := st.ops.iterateAt
  boundsError := st.boundsErrorInt
  stringIndexError := st.ops.stringIndexError
  somethingError := st.somethingError

/-! ## Generic `AbstractString` search in the iterator model's monad

`search.jl:365-384` and `:681-703` call `Iterators.peel`, `rest`, `Iterators.Stateful`,
`zip`, `all`, `isempty` and `popfirst!`. Their installed models (`iterators.lean`) run in
`Exec E H`, which threads the heap holding each mutable `Stateful`; the generic searches move
there. The runtime allocation of a `Stateful` (`StatefulOps`) and the user types' own methods
(`iterate`, `==` of their characters, `Char(c)`) are the only typed callees. -/

open JuliaLean.base.iterators (Exec Rest StatefulOps DescriptorOps ZipCalls Zip TupleVals Reverse
  IterableStatePairs)
open JuliaLean.base.operators (Truth)

/-- `SearchM` and `Except` computations inside `Exec`: the heap is unchanged. -/
def liftSearch {E H α : Type} (x : SearchM E α) : Exec E H α :=
  fun h => match x.run with
  | none => none
  | some r => some (r, h)

def liftExcept {E H α : Type} (x : Except E α) : Exec E H α :=
  fun h => some (x, h)

private theorem exec_bind_apply {E H α β : Type} (x : Exec E H α) (f : α → Exec E H β) (w : H) :
    (x >>= f) w = ((x w) >>= fun p => match p with
      | (.error e, h) => some (.error e, h)
      | (.ok a, h) => f a h) := by
  show JuliaLean.base.iterators.bind x f w = _
  unfold JuliaLean.base.iterators.bind
  rcases x w with _ | ⟨_ | _, _⟩ <;> rfl

/-- Recursion through `Exec` (the `while true` loops below). -/
instance monoBindExec {E H : Type} : Lean.Order.MonoBind (Exec E H) where
  bind_mono_left h := by
    intro w
    rw [exec_bind_apply, exec_bind_apply]
    exact Lean.Order.MonoBind.bind_mono_left (m := Option) (h w)
  bind_mono_right h := by
    intro w
    rw [exec_bind_apply, exec_bind_apply]
    apply Lean.Order.MonoBind.bind_mono_right (m := Option)
    intro p
    rcases p with ⟨_ | a, h'⟩
    · exact Lean.Order.PartialOrder.rel_refl
    · exact h a h'

/-- `for x in itr` (the `iterate` protocol of Julia's `for` lowering): `iterate(itr)`, then
`iterate(itr, state)` until `nothing`. -/
def forInLoop {E H X St α β : Type} (run : X → Option St → Exec E H (Option (α × St))) (itr : X)
    (f : α → β → Exec E H (ForInStep β)) (b : β) (st : Option St) : Exec E H β := do
  match ← run itr st with
  | none => pure b
  | some (x, next) =>
      match ← f x b with
      | .done b => pure b
      | .yield b => forInLoop run itr f b (some next)
partial_fixpoint

/-- An iterable with its `iterate` method. -/
structure Iterated (E H X St α : Type) where
  itr : X
  run : X → Option St → Exec E H (Option (α × St))

instance {E H X St α : Type} : ForIn (Exec E H) (Iterated E H X St α) α where
  forIn x b f := forInLoop x.run x.itr f b none

/-- anyall.jl:207-220 `_all(f, itr, :)` (`ItrT = Any`), with `for x in itr` lowered to
`iterate`: a `missing` sets `anymissing`, a `false` returns `false`, and at the end the result
is `missing` if `anymissing`, else `true`. -/
def allIterate {E H A St : Type} (iterate : Option St → Exec E H (Option (A × St)))
    (f : A → Exec E H Truth) (anymissing : Bool) (state : Option St) : Exec E H Truth := do
  match ← iterate state with
  | none => pure (if anymissing then .missing else .true)
  | some (x, next) =>
      match ← f x with
      | .missing => allIterate iterate f true (some next)
      | .true => allIterate iterate f anymissing (some next)
      | .false => pure .false
partial_fixpoint

/-- The two components of a two-argument `zip`. -/
inductive Slot where
  | left
  | right

@[reducible] def SlotT (A B : Type) : Slot → Type
  | .left => A
  | .right => B

/-- `zip(x, y)`'s calls: each component's own `iterate` and `isdone`. -/
def pairZipCalls {E H IA IB VA VB SA SB : Type}
    (runA : IA → Option SA → Exec E H (Option (VA × SA)))
    (doneA : IA → Option SA → Exec E H (Option Bool))
    (runB : IB → Option SB → Exec E H (Option (VB × SB)))
    (doneB : IB → Option SB → Exec E H (Option Bool)) :
    ZipCalls (Exec E H) (SlotT IA IB) (SlotT VA VB) (SlotT SA SB) where
  run k := match k with
    | .left => runA
    | .right => runB
  done k := match k with
    | .left => doneA
    | .right => doneB

/-- `all(splat(==), zip(x, y))` over the installed `zip` model (iterators.jl:440-441). -/
def allZipEqual {E H IA IB VA VB SA SB : Type}
    (calls : ZipCalls (Exec E H) (SlotT IA IB) (SlotT VA VB) (SlotT SA SB))
    (x : IA) (y : IB) (equal : VA → VB → Exec E H Truth) : Exec E H Truth :=
  let z : Zip (TupleVals (SlotT IA IB) [Slot.left, Slot.right]) := ⟨.cons x (.cons y .nil)⟩
  allIterate
    (fun st => match st with
      | none => JuliaLean.base.iterators.zipStart calls z
      | some ss => JuliaLean.base.iterators.zipState calls z ss)
    (fun vs => match vs with
      | .cons a (.cons b .nil) => equal a b)
    false none

/-- `iterate(s)`/`iterate(s, i)` of a string, by its own methods. -/
def stringIterate {S R C CU CT E H : Type} (ops : StringOps S R C CU CT E) (s : S)
    (st : Option Index) : Exec E H (Option (C × Index)) :=
  liftExcept (match st with
    | none => ops.iterateFirst s
    | some i => ops.iterateAt s i)

/-- `iterate(r::Iterators.Reverse{<:AbstractString}, i=lastindex(r.itr))` (basic.jl:775). -/
def reverseStringIterate {S R C CU CT E H : Type} (ops : StringOps S R C CU CT E)
    (r : Reverse S) (st : Option Index) : Exec E H (Option (C × Index)) :=
  liftExcept (JuliaLean.base.strings.basic.reverseIterateString ops id
    (fun i f => .ok (decide (i.val < f.val))) (JuliaLean.base.strings.basic.getindexString ops)
    (JuliaLean.base.strings.basic.previndOne ops) ⟨r.itr⟩ st)

/-- iterators.jl:1717-1721 `iterate(x::IterableStatePairs{<:Iterators.Reverse},
state=last(keys(x.x.itr)))`, in any monad (proposed replacement of the installed `Jl`-only
`iterateReverseIterableStatePairs`, same body). -/
def iterateReverseStatePairs {m : Type → Type} [Monad m] {T Keys V S : Type}
    (keys : T → m Keys) (last : Keys → m S)
    (iterate : Reverse T → Option S → m (Option (V × S)))
    (x : IterableStatePairs (Reverse T)) (state : Option S) : m (Option ((S × V) × S)) := do
  let st ← match state with
    | none => do last (← keys x.x.itr)
    | some s => pure s
  match ← iterate x.x (some st) with
  | none => pure none
  | some (value, next) => pure (some ((st, value), next))

/-- `isequal(c, t1) = (c == t1)::Bool` (operators.jl:196): a `missing` is a failed `::Bool`
assertion (`TypeError`). -/
def isequalTest {C D E : Type} (equal : C → D → Except E Truth) (assertion : E) (t1 : D)
    (c : C) : SearchM E Bool := do
  match ← liftE (equal c t1) with
  | .true => pure true
  | .false => pure false
  | .missing => throw assertion

/-- The dense character search of a `UTF8String` source (`String`, `SubString{String}`). -/
structure Utf8Source (S A D E : Type) where
  search : SearchStringOps S JChar E
  bytes : DenseOps A UInt8 E
  codeunits : S → A
  chars : CharOps D E

/-- Julia's method choice for `findnext(isequal(c), s, i)`/`findprev`: the `UTF8String` methods
(search.jl:143-166, 209-230) or the `AbstractString` ones (search.jl:343-354, 668-679). -/
inductive SourceKind (S A D E : Type) where
  | utf8 (source : Utf8Source S A D E)
  | generic

def findnextIsequal {S A C D I E H : Type} (kind : SourceKind S A D E)
    (src : SearchStringOps S C E) (equal : C → D → Except E Truth) (assertion : E)
    (ix : IntegerOps I E) (t1 : D) (s : S) (i : I) : Exec E H (Option Index) :=
  match kind with
  | .utf8 u => liftExcept (findnextChar u.search u.bytes u.codeunits u.chars ix t1 s i)
  | .generic => liftSearch (JuliaLean.base.strings.search.findnextPredicate src ix
      (isequalTest equal assertion t1) s i)

def findprevIsequal {S A C D I E H : Type} (kind : SourceKind S A D E)
    (src : SearchStringOps S C E) (equal : C → D → Except E Truth) (assertion : E)
    (ix : IntegerOps I E) (t1 : D) (s : S) (i : I) : Exec E H (Option Index) :=
  match kind with
  | .utf8 u => liftExcept (findprevChar u.search u.bytes u.codeunits u.chars ix t1 s i)
  | .generic => liftSearch (JuliaLean.base.strings.search.findprevPredicate src ix
      (isequalTest equal assertion t1) s i)

/--
Julia source: base/strings/search.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(c::AbstractChar, s::AbstractString) = (findfirst(isequal(c),s)!==nothing)
```
-/
def inChar {S R C CU CT A D E H : Type} (st : StringType S R C CU CT E)
    (kind : SourceKind S A D E) (equal : C → D → Except E Truth) (assertion : E)
    (c : D) (s : S) : Exec E H Bool := do
  pure (← findnextIsequal kind (searchOpsOf st) equal assertion indexOps c s (int 1)).isSome

/-- The callees of the generic forward search (search.jl:365-384) that the source and pattern
types define: their methods, `==` of their characters, the `TypeError`s, and the runtime
allocation of the mutable `Stateful` (`StatefulOps`, `DescriptorOps`). -/
structure GenericForwardCalls (S R C CU CT T TR D TCU TCT A Handle Ty E H : Type) where
  source : StringType S R C CU CT E
  kind : SourceKind S A D E
  pattern : StringOps T TR D TCU TCT E
  equal : C → D → Except E Truth
  stateful : StatefulOps E H Handle (Rest T Index) (D × Index) Ty
  types : DescriptorOps Ty
  typeofRest : Rest T Index → Ty
  eof : E
  assertion : E
  nonBoolean : E

/-- `iterate(s::Stateful)` over a `Rest`: `iterate(trest, st) = iterate(t, st)`
(iterators.jl:732, 1624). -/
def statefulRestRun {E H T TSt D : Type} (iterateT : T → Option TSt → Exec E H (Option (D × TSt))) :
    Rest T TSt → TSt → Exec E H (Option (D × TSt)) :=
  fun r st => JuliaLean.base.iterators.iterateRest iterateT r (some st)

/-- search.jl:375-383 `while true` of `_searchindex`: `findnext(isequal(t1), s, i)`,
`ii = nextind(s, i)`, `a = Iterators.Stateful(trest)`,
`matched = all(splat(==), zip(SubString(s, ii), a))`,
`(isempty(a) && matched) && return i` (a `missing` `matched` after an empty `a` is a `TypeError`). -/
def searchindexGenericLoop {S R C CU CT T TR D TCU TCT A Handle Ty I E H : Type}
    (ops : GenericForwardCalls S R C CU CT T TR D TCU TCT A Handle Ty E H) (ix : IntegerOps I E)
    (s : S) (t1 : D) (trest : Rest T Index) (sentinel : Index) (start : I ⊕ Index) :
    Exec E H Index := do
  let src := searchOpsOf ops.source
  let found ← Sum.elim (findnextIsequal ops.kind src ops.equal ops.assertion ix t1 s)
    (findnextIsequal ops.kind src ops.equal ops.assertion indexOps t1 s) start
  match found with
  | none => pure sentinel
  | some i =>
      let ii ← liftExcept (src.nextind s i)
      let iterT := stringIterate (H := H) ops.pattern
      let a ← JuliaLean.base.iterators.stateful ops.stateful ops.types ops.typeofRest
        (fun r => JuliaLean.base.iterators.iterateRest iterT r none) trest
      let sub ← liftExcept (subStringIntegerDefault (subStringOpsOf ops.source) (fun i => .ok i)
        ops.source.ops.lastindex s ii)
      let runSub := fun (x : SubString S) (st : Option Index) =>
        liftExcept (H := H) (subIterateG ops.source x (st.getD (int 1)))
      let runA := fun (h : Handle) (_ : Option Unit) =>
        JuliaLean.base.iterators.iterateStateful ops.stateful (statefulRestRun iterT) ops.eof h
      let doneA := fun (h : Handle) (_ : Option Unit) => do
        pure (some (← JuliaLean.base.iterators.isdoneStateful ops.stateful h))
      let calls := pairZipCalls runSub (fun _ _ => pure none) runA doneA
      let matched ← allZipEqual calls sub a (fun c d => liftExcept (ops.equal c d))
      if ← JuliaLean.base.iterators.isempty doneA runA a then
        match matched with
        | .true => pure i
        | .false => searchindexGenericLoop ops ix s t1 trest sentinel (.inr ii)
        | .missing => JuliaLean.base.iterators.fail ops.nonBoolean
      else searchindexGenericLoop ops ix s t1 trest sentinel (.inr ii)
partial_fixpoint

/--
Julia source: base/strings/search.jl:365-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _searchindex(s::Union{AbstractString,DenseUInt8OrInt8},
                      t::Union{AbstractString,AbstractChar,Int8,UInt8},
                      i::Integer)
    sentinel = firstindex(s) - 1
    x = Iterators.peel(t)
    if isnothing(x)
        return firstindex(s) <= i <= nextind(s,lastindex(s))::Int ? i :
               throw(BoundsError(s, i))
    end
    t1, trest = x
    while true
        i = findnext(isequal(t1),s,i)
        if i === nothing return sentinel end
        ii = nextind(s, i)::Int
        a = Iterators.Stateful(trest)
        matched = all(splat(==), zip(SubString(s, ii), a))
        (isempty(a) && matched) && return i
        i = ii
    end
end
```
search.jl:365-384 `_searchindex` (generic): `Iterators.peel(t)` (iterators.jl:725-730) is
`iterate(t)`.
-/
def searchindexGeneric {S R C CU CT T TR D TCU TCT A Handle Ty I E H : Type}
    (ops : GenericForwardCalls S R C CU CT T TR D TCU TCT A Handle Ty E H) (ix : IntegerOps I E)
    (s : S) (t : T) (start : I) : Exec E H Index := do
  let src := searchOpsOf ops.source
  let sentinel := JuliaLean.base.strings.basic.firstindexString s - int 1
  match ← JuliaLean.base.iterators.peel (stringIterate (H := H) ops.pattern) t with
  | none =>
      if (JuliaLean.base.strings.basic.firstindexString s).val ≤ ix.value start then
        let z ← liftExcept (do src.nextind s (← src.lastindex s))
        if ix.value start ≤ z.val then liftExcept (ix.toInt start)
        else JuliaLean.base.iterators.fail (src.boundsError s (ix.value start))
      else JuliaLean.base.iterators.fail (src.boundsError s (ix.value start))
  | some (t1, trest) => searchindexGenericLoop ops ix s t1 trest sentinel (.inl start)

/-- search.jl:468-479 `_search(s, t, i)` over the generic `_searchindex`
(`firstindex(::AbstractString) = 1`, basic.jl:179). -/
def genericRange {S R C CU CT T TR D TCU TCT A Handle Ty E H : Type}
    (ops : GenericForwardCalls S R C CU CT T TR D TCU TCT A Handle Ty E H)
    (s : S) (t : T) (i : Index) : Exec E H (Option MatchRange) := do
  let idx ← searchindexGeneric ops indexOps s t i
  if JuliaLean.base.strings.basic.isemptyString ops.pattern t then pure (some ⟨idx, idx - int 1⟩)
  else if idx.val ≥ 1 then
    let last ← liftExcept (ops.pattern.lastindex t)
    pure (some ⟨idx, idx + last - int 1⟩)
  else pure none

/-- search.jl:507 `findnext(t::AbstractString, s::AbstractString, start::Integer) =
_search(s, t, Int(start))`. -/
def genericNext {S R C CU CT T TR D TCU TCT A Handle Ty I E H : Type}
    (ops : GenericForwardCalls S R C CU CT T TR D TCU TCT A Handle Ty E H) (ix : IntegerOps I E)
    (t : T) (s : S) (start : I) : Exec E H (Option MatchRange) := do
  genericRange ops s t (← liftExcept (ix.toInt start))

/-- The callees of the generic reverse search (search.jl:681-703): as forward, with `==` in
both argument orders (`isequal(c, t1)` and `splat(==)(x, y)` over `zip(a, ...)`) and the
allocation of both `Stateful`s. -/
structure GenericReverseCalls (S R C CU CT T TR D TCU TCT A HA HB Ty E H : Type) where
  source : StringType S R C CU CT E
  kind : SourceKind S A D E
  pattern : StringOps T TR D TCU TCT E
  equalCD : C → D → Except E Truth
  equalDC : D → C → Except E Truth
  statefulA : StatefulOps E H HA (Rest (Reverse T) Index) (D × Index) Ty
  statefulB : StatefulOps E H HB (IterableStatePairs (Reverse (SubString S)))
    ((Index × C) × Index) Ty
  types : DescriptorOps Ty
  typeofRest : Rest (Reverse T) Index → Ty
  typeofPairs : IterableStatePairs (Reverse (SubString S)) → Ty
  eof : E
  assertion : E
  typeError : E
  nonBoolean : E

/-- `iterate(Iterators.reverse(pairs(ss)), state)` for `ss::SubString{S}`: `pairs(s) =
IterableStatePairs(s)` (iterators.jl:1725), `reverse(x::IterableStatePairs) =
IterableStatePairs(Iterators.reverse(x.x))` (:1714), iterated by :1717-1721 with
`keys(s) = EachStringIndex(s)` (basic.jl:580) and `last(e) = lastindex(e.s)` (basic.jl:1212). -/
def iterateRevPairs {S R C CU CT E H : Type} (st : StringType S R C CU CT E)
    (p : IterableStatePairs (Reverse (SubString S))) (state : Option Index) :
    Exec E H (Option ((Index × C) × Index)) :=
  iterateReverseStatePairs (m := Exec E H)
    (fun x => pure (JuliaLean.base.strings.basic.keysString x))
    (fun e => liftExcept (JuliaLean.base.strings.basic.lastEachStringIndex (subStringBasic st) e))
    (reverseStringIterate (subStringBasic st)) p state

/-- search.jl:689-702 `while true` of `_rsearchindex`: `a = Stateful(trest)`,
`b = Stateful(reverse(pairs(SubString(s, 1, ii))))`, `all(splat(==), zip(a, (x[2] for x in b)))`
over the installed `Generator` model (generator.jl:44-50, isdone :59), then
`if matched && isempty(a)` (a `missing` `matched` is a `TypeError`),
`isempty(b) && return firstindex(s)`, `nextind(s, popfirst!(b)[1])`. -/
def rsearchindexGenericLoop {S R C CU CT T TR D TCU TCT A HA HB Ty I E H : Type}
    (ops : GenericReverseCalls S R C CU CT T TR D TCU TCT A HA HB Ty E H) (ix : IntegerOps I E)
    (s : S) (t1 : D) (trest : Rest (Reverse T) Index) (start : I ⊕ Index) : Exec E H Index := do
  let src := searchOpsOf ops.source
  let found ← Sum.elim (findprevIsequal ops.kind src ops.equalCD ops.assertion ix t1 s)
    (findprevIsequal ops.kind src ops.equalCD ops.assertion indexOps t1 s) start
  match found with
  | none => pure (int 0)
  | some i =>
      let ii ← liftExcept (src.prevind s i)
      let iterR := reverseStringIterate (H := H) ops.pattern
      let a ← JuliaLean.base.iterators.stateful ops.statefulA ops.types ops.typeofRest
        (fun r => JuliaLean.base.iterators.iterateRest iterR r none) trest
      let sub ← liftExcept (subStringInt (subStringOpsOf ops.source) s (int 1) ii)
      let pairs ← JuliaLean.base.iterators.reverseIterableStatePairs (m := Exec E H)
        (fun x => pure (Reverse.mk x)) (IterableStatePairs.mk sub)
      let b ← JuliaLean.base.iterators.stateful ops.statefulB ops.types ops.typeofPairs
        (fun p => iterateRevPairs ops.source p none) pairs
      let runA := fun (h : HA) (_ : Option Unit) =>
        JuliaLean.base.iterators.iterateStateful ops.statefulA (statefulRestRun iterR) ops.eof h
      let doneA := fun (h : HA) (_ : Option Unit) => do
        pure (some (← JuliaLean.base.iterators.isdoneStateful ops.statefulA h))
      let runPairs := fun (p : IterableStatePairs (Reverse (SubString S))) (st : Index) =>
        iterateRevPairs (H := H) ops.source p (some st)
      let runB := fun (h : HB) (_ : Option Unit) =>
        JuliaLean.base.iterators.iterateStateful ops.statefulB runPairs ops.eof h
      let doneB := fun (h : HB) (_ : Option Unit) => do
        pure (some (← JuliaLean.base.iterators.isdoneStateful ops.statefulB h))
      let gen : JuliaLean.base.generator.Generator HB Unit := ⟨(), b⟩
      let runGen := fun (g : JuliaLean.base.generator.Generator HB Unit) (st : Option Unit) =>
        JuliaLean.base.generator.iterateGenerator (fun _ (x : Index × C) => pure x.2) runB
          (fun y => pure y) g st
      let doneGen := fun (g : JuliaLean.base.generator.Generator HB Unit) (st : Option Unit) =>
        JuliaLean.base.generator.generatorIsdone doneB g st
      let calls := pairZipCalls runA doneA runGen doneGen
      let matched ← allZipEqual calls a gen (fun d c => liftExcept (ops.equalDC d c))
      match matched with
      | .missing => JuliaLean.base.iterators.fail ops.nonBoolean
      | .false => rsearchindexGenericLoop ops ix s t1 trest (.inr ii)
      | .true =>
          if ← JuliaLean.base.iterators.isempty doneA runA a then
            if ← JuliaLean.base.iterators.isempty doneB runB b then
              pure (JuliaLean.base.strings.basic.firstindexString s)
            else
              let pair ← JuliaLean.base.iterators.popfirstStateful ops.statefulB runPairs ops.eof b
              liftExcept (src.nextind s pair.1)
          else rsearchindexGenericLoop ops ix s t1 trest (.inr ii)
partial_fixpoint

/--
Julia source: base/strings/search.jl:681-703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _rsearchindex(s::AbstractString,
                       t::Union{AbstractString,AbstractChar,Int8,UInt8},
                       i::Integer)
    if isempty(t)
        return 1 <= i <= nextind(s, lastindex(s))::Int ? i :
               throw(BoundsError(s, i))
    end
    t1, trest = Iterators.peel(Iterators.reverse(t))::NTuple{2,Any}
    while true
        i = findprev(isequal(t1), s, i)
        i === nothing && return 0
        ii = prevind(s, i)::Int
        a = Iterators.Stateful(trest)
        b = Iterators.Stateful(Iterators.reverse(
            pairs(SubString(s, 1, ii))))
        matched = all(splat(==), zip(a, (x[2] for x in b)))
        if matched && isempty(a)
            isempty(b) && return firstindex(s)
            return nextind(s, popfirst!(b)[1])::Int
        end
        i = ii
    end
end
```
search.jl:681-703 `_rsearchindex` (generic): `peel(Iterators.reverse(t))` is the first
`iterate` of the reversed pattern, and its `::NTuple{2,Any}` throws on `nothing`.
-/
def rsearchindexGeneric {S R C CU CT T TR D TCU TCT A HA HB Ty I E H : Type}
    (ops : GenericReverseCalls S R C CU CT T TR D TCU TCT A HA HB Ty E H) (ix : IntegerOps I E)
    (s : S) (t : T) (start : I) : Exec E H Index := do
  let src := searchOpsOf ops.source
  if JuliaLean.base.strings.basic.isemptyString ops.pattern t then
    if 1 ≤ ix.value start then
      let z ← liftExcept (do src.nextind s (← src.lastindex s))
      if ix.value start ≤ z.val then liftExcept (ix.toInt start)
      else JuliaLean.base.iterators.fail (src.boundsError s (ix.value start))
    else JuliaLean.base.iterators.fail (src.boundsError s (ix.value start))
  else
    match ← JuliaLean.base.iterators.peel (reverseStringIterate (H := H) ops.pattern)
        (Reverse.mk t) with
    | none => JuliaLean.base.iterators.fail ops.typeError
    | some (t1, trest) => rsearchindexGenericLoop ops ix s t1 trest (.inl start)

/-- search.jl:785-796 `_rsearch(s, t, i)` over the generic `_rsearchindex`. -/
def genericRRange {S R C CU CT T TR D TCU TCT A HA HB Ty E H : Type}
    (ops : GenericReverseCalls S R C CU CT T TR D TCU TCT A HA HB Ty E H)
    (s : S) (t : T) (i : Index) : Exec E H (Option MatchRange) := do
  let idx ← rsearchindexGeneric ops indexOps s t i
  if JuliaLean.base.strings.basic.isemptyString ops.pattern t then pure (some ⟨idx, idx - int 1⟩)
  else if idx.val > 0 then
    let last ← liftExcept (ops.pattern.lastindex t)
    pure (some ⟨idx, idx + last - int 1⟩)
  else pure none

/-- search.jl:821 `findprev(t::AbstractString, s::AbstractString, i::Integer) =
_rsearch(s, t, Int(i))`. -/
def genericPrev {S R C CU CT T TR D TCU TCT A HA HB Ty I E H : Type}
    (ops : GenericReverseCalls S R C CU CT T TR D TCU TCT A HA HB Ty E H) (ix : IntegerOps I E)
    (t : T) (s : S) (start : I) : Exec E H (Option MatchRange) := do
  genericRRange ops s t (← liftExcept (ix.toInt start))

/-! ## `findall` results in a `Vector` (array.jl, boot.jl)

The result vectors live in the installed growable-vector store (`array.MutationM`), part of the
caller's heap `H`. `T[]` is `Vector{T}(undef, 0)` (boot.jl:821-824, installed
`mutableAllocate`); `push!(a, x)` of an already-typed item is array.jl:1353-1365 (installed
`array.push` over `push1361` with `_growend!`, `length` and `setindex!`). -/

open JuliaLean.base.array (MutationM MutableMemory MemoryLayoutMetadata)

structure VectorStore (α E H : Type) where
  layout : MemoryLayoutMetadata
  memory : H → MutableMemory α
  setMemory : H → MutableMemory α → H
  error : JuliaLean.base.array.Error → E

/-- A vector-store computation in `Exec`: its mutations persist on success and on error. -/
def liftMutation {α β E H : Type} (v : VectorStore α E H) (x : MutationM α β) : Exec E H β :=
  fun h =>
    let p := Id.run ((ExceptT.run x).run (v.memory h))
    match p.1 with
    | .ok b => some (.ok b, v.setMemory h p.2)
    | .error e => some (.error (v.error e), v.setMemory h p.2)


/-- `push!(a::Vector{T}, item::T)` (array.jl:1353-1365). -/
def vectorPush {α : Type} (layout : MemoryLayoutMetadata) (a : Nat) (x : α) : MutationM α Nat :=
  JuliaLean.base.array.push (fun _ => true) id (fun x => pure x)
    (JuliaLean.base.array.push1361
      (JuliaLean.base.array.growend (JuliaLean.base.array.mutableStorage layout) pure
        (JuliaLean.base.array.growendInternal (JuliaLean.base.array.mutableStorage layout)))
      JuliaLean.base.array.mutableLength JuliaLean.base.array.mutableSet) a x

/-- search.jl:651-665 `findall(t, s; overlap)`: `found = UnitRange{Int}[]`, then `findnext`
and `push!` until `nothing` or `j > lastindex(s)`. -/
def findallRangesLoop {S T E H : Type} (vec : VectorStore MatchRange E H)
    (findnext : T → S → Index → Exec E H (Option MatchRange))
    (nextind : S → Index → Exec E H Index) (overlap : Bool) (t : T) (s : S) (e : Index)
    (found : Nat) (i : Index) : Exec E H Nat := do
  match ← findnext t s i with
  | none => pure found
  | some r =>
      let found ← liftMutation vec (vectorPush vec.layout found r)
      let j := if overlap || r.last.val < r.first.val then r.first else r.last
      if e.val < j.val then pure found
      else findallRangesLoop vec findnext nextind overlap t s e found (← nextind s j)
partial_fixpoint

/--
Julia source: base/strings/search.jl:651-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(t::Union{AbstractString, AbstractPattern, AbstractVector{UInt8}},
                 s::Union{AbstractString, AbstractPattern, AbstractVector{UInt8}},
                 ; overlap::Bool=false)
    found = UnitRange{Int}[]
    i, e = firstindex(s), lastindex(s)
    while true
        r = findnext(t, s, i)
        isnothing(r) && break
        push!(found, r)
        j = overlap || isempty(r) ? first(r) : last(r)
        j > e && break
        @inbounds i = nextind(s, j)
    end
    return found
end
```
-/
def findallRanges {S T E H : Type} (vec : VectorStore MatchRange E H)
    (findnext : T → S → Index → Exec E H (Option MatchRange))
    (firstindex : S → Index) (lastindex : S → Exec E H Index) (nextind : S → Index → Exec E H Index)
    (overlap : Bool) (t : T) (s : S) : Exec E H Nat := do
  let found ← liftMutation vec (JuliaLean.base.array.mutableAllocate vec.layout.allocation 0 (int 0))
  let i := firstindex s
  let e ← lastindex s
  findallRangesLoop vec findnext nextind overlap t s e found i

/-- `findall(t, s::DenseUTF8String; overlap)` over the dense search (search.jl:651-665). -/
def denseAll {S T A D E H : Type} (cfg : DenseStringSearch S T A D E)
    (vec : VectorStore MatchRange E H) (t : T) (s : S) (overlap : Bool) : Exec E H Nat :=
  findallRanges vec (fun t s i => liftSearch (denseNext cfg indexOps t s i))
    JuliaLean.base.strings.basic.firstindexString (fun s => liftExcept (cfg.source.lastindex s)) (fun s i => liftExcept (cfg.source.nextind s i))
    overlap t s

/-- `findall(t, s::AbstractString; overlap)` over the generic search (search.jl:651-665). -/
def genericAll {S R C CU CT T TR D TCU TCT A Handle Ty E H : Type}
    (ops : GenericForwardCalls S R C CU CT T TR D TCU TCT A Handle Ty E H)
    (vec : VectorStore MatchRange E H) (t : T) (s : S) (overlap : Bool) : Exec E H Nat :=
  findallRanges vec (genericNext ops indexOps) JuliaLean.base.strings.basic.firstindexString
    (fun s => liftExcept ((searchOpsOf ops.source).lastindex s))
    (fun s i => liftExcept ((searchOpsOf ops.source).nextind s i)) overlap t s

/--
Julia source: base/strings/search.jl:272-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(
    pred::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},
    s::UTF8String,
)
    iter = FwCharPosIter(s, pred.x)
    return if is_standalone_byte(iter.last_char_byte)
        findall(==(iter.last_char_byte), codeunits(s))
    else
        # It is slightly wasteful that every iteration will check is_standalone_byte
        # again, but this should only be minor overhead in the non-fast path.
        collect(iter)
    end
end
```
-/
def findallChar {S A D E H : Type} (source : Utf8Source S A D E) (vec : VectorStore Index E H)
    (findallByte : UInt8 → A → Exec E H Nat) (pred : D) (s : S) : Exec E H Nat := do
  let iter ← liftExcept (fwCharPosIter source.chars s pred)
  if isStandaloneByte iter.lastCharByte then findallByte iter.lastCharByte (source.codeunits s)
  else
    JuliaLean.base.array.collectKnownUnknown (m := Exec E H)
      (X := Iterated E H (FwCharPosIter S) Index Index)
      (fun _ => ()) (fun _ _ => liftMutation vec (JuliaLean.base.array.mutableAllocate vec.layout.allocation 0 (int 0)))
      (fun a x => do let _ ← liftMutation vec (vectorPush vec.layout a x); pure ()) ()
      ⟨iter, fun it st => liftExcept (fwIterate source.search source.bytes source.codeunits
        source.chars.ncodeunits it (st.getD (int 1)))⟩

/--
Julia source: base/strings/search.jl:202-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(::typeof(iszero), a::DenseUInt8OrInt8, i::Integer)
    i = Int(i)::Int
    @boundscheck i < Int(firstindex(a))::Int && throw(BoundsError(a, i))
    i > Int(lastindex(a))::Int && return nothing
    return memchr(a, zero(eltype(a)), i)
end
```
-/
def findnextZero {A B I E : Type} (ops : DenseOps A B E) (ix : IntegerOps I E)
    (memchr : A → B → Index → Except E (Option Index)) (a : A) (start : I) :
    Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val < (ops.firstindex a).val then throw (ops.boundsError a i.val)
  if i.val > (ops.lastindex a).val then return none
  memchr a ops.zero i

/--
Julia source: base/strings/search.jl:265-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(::typeof(iszero), a::DenseUInt8OrInt8, i::Integer)
    i = Int(i)::Int
    @boundscheck i > Int(lastindex(a))::Int && throw(BoundsError(a, i))
    i < Int(firstindex(a))::Int && return nothing
    memrchr(a, zero(eltype(a)), i)
end
```
-/
def findprevZero {A B I E : Type} (ops : DenseOps A B E) (ix : IntegerOps I E)
    (memrchr : A → B → Index → Except E (Option Index)) (a : A) (start : I) :
    Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val > (ops.lastindex a).val then throw (ops.boundsError a i.val)
  if i.val < (ops.firstindex a).val then return none
  memrchr a ops.zero i

def denseFindnextUInt8 {A E : Type} (ops : DenseOps A UInt8 E)
    (b : UInt8) (a : A) (i : Index) : Except E (Option Index) :=
  findnextUInt8 ops indexOps b a i

def denseFindprevUInt8 {A E : Type} (ops : DenseOps A UInt8 E)
    (b : UInt8) (a : A) (i : Index) : Except E (Option Index) :=
  findprevUInt8 ops indexOps b a i

/--
Julia source: base/strings/search.jl:360-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow :foldable function in(c::Char, s::Union{String,SubString{String}})
    pos = @inline findnext(==(c), s, 1)
    return pos !== nothing
end
```
-/
def inCharDense {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (chars : CharOps JChar E)
    (c : JChar) (s : S) : Except E Bool := do
  let pos ← findnextChar ops bytes codeunits chars indexOps c s (int 1)
  pure pos.isSome

end SearchBind

end JuliaLean.base.strings.search


/-! Coverage models for `base/strings/search.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.Strings

/-- `memchr`-based `findnext(==(b), codeunits(s), i)`, `base/search.jl:175-189`:
the first index `k ≥ i` holding `b`. Bound: `n + 1 - i`. -/
def memchrFrom (bs : List UInt8) (b : UInt8) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, i => if bs.getD (i - 1) 0 == b then some i else memchrFrom bs b k (i + 1)

/-- `findnext(==(b), a::DenseUInt8, i)`, `base/strings/search.jl:175-180`. -/
def findnextByte (bs : List UInt8) (b : UInt8) (i : JInt64) : SJl (Option JInt64) :=
  if i.val < 1 then .error boundsErr
  else if i.val > bs.length then .ok none
  else .ok ((memchrFrom bs b (bs.length + 1 - i.val.toNat) i.val.toNat).map fun k => ix k)

/-- `memrchr`-based `findprev(==(b), a, i)`: the last index `k ≤ i` holding `b`. -/
def memrchrFrom (bs : List UInt8) (b : UInt8) : Nat → Option Nat
  | 0 => none
  | k + 1 => if bs.getD k 0 == b then some (k + 1) else memrchrFrom bs b k

/-- `findprev(==(b), a::DenseUInt8, i)`, `base/strings/search.jl:239-244`. -/
def findprevByte (bs : List UInt8) (b : UInt8) (i : JInt64) : SJl (Option JInt64) :=
  if i.val > bs.length then .error boundsErr
  else if i.val < 1 then .ok none
  else .ok ((memrchrFrom bs b i.val.toNat).map fun k => ix k)

/-- `last_utf8_byte(c)`, `base/strings/search.jl:34-38`. -/
def lastUtf8Byte (c : UInt32) : UInt8 :=
  let shift := ((4 - ncodeunitsChar c) * 8) % 32
  (c >>> shift.toUInt32).toUInt8

/-- `is_standalone_byte(x) = (x < 0x80) | (x > 0xf7)`, `base/strings/search.jl:42`. -/
def isStandalone (x : UInt8) : Bool := decide (x < 0x80) || decide (x > 0xf7)

/-- The loop of `iterate(s::FwCharPosIter, i)`, `base/strings/search.jl:73-91`.
Each pass increases `i`; bound `n + 1 - i`. -/
def fwLoop (s : JStr) (c : UInt32) (byte : UInt8) (ncu : Nat) : Nat → JInt64 → SJl (Option (JInt64 × JInt64))
  | 0, _ => .ok none
  | k + 1, i =>
    if i.val > (ncodeunits s).val then .ok none
    else
      match findnextByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) =>
        let i := i + ix 1
        let index := i - ix ncu
        if !isvalidAt s index then fwLoop s c byte ncu k i
        else
          match iterate s index with
          | none => .error .assertion
          | some (ch, _) => if ch == c then .ok (some (index, i)) else fwLoop s c byte ncu k i

/-- `iterate(s::FwCharPosIter, i)`, `base/strings/search.jl:62-93`. -/
def fwIterate (s : JStr) (c : UInt32) (i : JInt64) : SJl (Option (JInt64 × JInt64)) :=
  let byte := lastUtf8Byte c
  if isStandalone byte then
    if i.val > (ncodeunits s).val then .ok none
    else
      match findnextByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) => .ok (some (i, i + ix 1))
  else fwLoop s c byte (ncodeunitsChar c) (s.bytes.length + 2) i

/-- `findnext(==(c), s::String, i)` for `c::Char`, `base/strings/search.jl:143-166`. -/
def findnextChar (c : UInt32) (s : JStr) (i : JInt64) : SJl (Option JInt64) :=
  let scu := ncodeunits s
  if i.val = (scu + ix 1).val then .ok none
  else if decide (i.val < 1) || decide (i.val > (scu + ix 1).val) then .error boundsErr
  else
    let u := (c >>> 24).toUInt8
    if !isvalidAt s i then .error (.stringIndexError i.val)
    else if isStandalone u then findnextByte s.bytes u i
    else (fwIterate s c i).map (·.map (·.1))

/-- The loop of `iterate(s::RvCharPosIter, i)`, `base/strings/search.jl:125-134`.
Each pass decreases `i`; bound `i + 1`. -/
def rvLoop (s : JStr) (c : UInt32) (byte : UInt8) (ncu : Nat) : Nat → JInt64 → SJl (Option (JInt64 × JInt64))
  | 0, _ => .ok none
  | k + 1, i =>
    if i.val < ncu then .ok none
    else
      match findprevByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) =>
        let index := i - ix ncu + ix 1
        let i := i - ix 1
        if !isvalidAt s index then rvLoop s c byte ncu k i
        else
          match iterate s index with
          | none => .error .assertion
          | some (ch, _) => if ch == c then .ok (some (index, i)) else rvLoop s c byte ncu k i

/-- `iterate(s::RvCharPosIter, i)`, `base/strings/search.jl:117-136`. -/
def rvIterate (s : JStr) (c : UInt32) (i : JInt64) : SJl (Option (JInt64 × JInt64)) :=
  let ncu := ncodeunitsChar c
  let byte := lastUtf8Byte c
  if isStandalone byte then
    if i.val < ncu then .ok none
    else
      match findprevByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) => .ok (some (i, i - ix 1))
  else
    let i := imin (ncodeunits s) (i + ix ncu - ix 1)
    rvLoop s c byte ncu (s.bytes.length + 2) i

/-- `findprev(==(c), s::String, i)` for `c::Char`, `base/strings/search.jl:209-230`. -/
def findprevChar (c : UInt32) (s : JStr) (i : JInt64) : SJl (Option JInt64) :=
  if decide (i.val = (ncodeunits s + ix 1).val) || decide (i.val = 0) then .ok none
  else if decide (i.val < 1) || decide (i.val > (ncodeunits s + ix 1).val) then .error boundsErr
  else
    let u := (c >>> 24).toUInt8
    if isStandalone u then findprevByte s.bytes u i
    else (rvIterate s c i).map (·.map (·.1))

/-- `_search_bloom_mask(c) = UInt64(1) << (c & 63)`, `base/strings/search.jl:388-390`. -/
def bloomBit (b : UInt8) : UInt64 := (1 : UInt64) <<< (b &&& 63).toUInt64

/-- `_nthbyte`: one-based byte access. -/
abbrev nth (bs : List UInt8) (i : Int) : UInt8 := bs.getD (i - 1).toNat 0

/-- The inner comparison loop, `base/strings/search.jl:437-443`: the number of
leading bytes `t[1..j]` that match `s[i+1..i+j]`, up to `n - 1`. -/
def matchLen (s t : List UInt8) (i : Int) (n : Nat) : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j =>
    if j < n - 1 then
      if nth s (i + j + 1) != nth t (j + 1) then j else matchLen s t i n k (j + 1)
    else j

/-- The main loop of the byte `_searchindex`, `base/strings/search.jl:434-463`.
Every pass increases `i`; bound `w - i + 1`. -/
def searchLoop (s t : List UInt8) (n : Nat) (w : Int) (mask : UInt64) (skip : Int) (tlast : UInt8) :
    Nat → Int → Int
  | 0, _ => 0
  | k + 1, i =>
    if i ≤ w then
      if nth s (i + n) == tlast then
        let j := matchLen s t i n n 0
        if j = n - 1 then i + 1
        else
          let i := if i < w && (mask &&& bloomBit (nth s (i + n + 1))) == 0 then i + n else i + skip
          searchLoop s t n w mask skip tlast k (i + 1)
      else
        let i := if i < w && (mask &&& bloomBit (nth s (i + n + 1))) == 0 then i + n else i
        searchLoop s t n w mask skip tlast k (i + 1)
    else 0

/-- `_searchindex(s::AbstractVector{UInt8}, t::AbstractVector{UInt8}, _i)`,
`base/strings/search.jl:401-466`. Index arithmetic stays far inside Int. -/
def searchindexBytes (s t : List UInt8) (i0 : JInt64) : SJl Int := do
  let n := t.length
  let m := s.length
  let i : Int := i0.val
  if i < 1 ∨ i > m + 1 then throw boundsErr
  if n = 0 then return (if 1 ≤ i ∧ i ≤ m + 1 then max 1 i else 0)
  if m = 0 then return 0
  if n = 1 then
    let r ← findnextByte s (nth t 1) i0
    return (r.map (·.val)).getD 0
  let w : Int := (m : Int) - n
  if w < 0 ∨ i - 1 > w then return 0
  let tlast := nth t n
  let (mask, skip) := (List.range n).foldl (fun (acc : UInt64 × Int) j0 =>
    let j : Nat := j0 + 1
    let mask := acc.1 ||| bloomBit (nth t j)
    let skip := if nth t j == tlast && j < n then (n : Int) - j - 1 else acc.2
    (mask, skip)) ((0 : UInt64), (n : Int) - 1)
  return searchLoop s t n w mask skip tlast (m + 2) (i - 1)

/-- `_searchindex(s::DenseUTF8String, t::DenseUTF8String, i)`, `base/strings/search.jl:395-399`. -/
def searchindexStr (s t : JStr) (i : JInt64) : SJl Int :=
  if (lastindex t).val = 1 then
    match getindex t (ix 1) with
    | .error e => .error e
    | .ok c => (findnextChar c s i).map fun r => (r.map (·.val)).getD 0
  else searchindexBytes s.bytes t.bytes i

/-- `findnext(t::AbstractString, s::AbstractString, i)` = `_search(s, t, Int(i))`,
`base/strings/search.jl:468-479,507` for two Strings. -/
def findnextStr (t s : JStr) (i : JInt64) : SJl (Option (Int × Int)) := do
  let idx ← searchindexStr s t i
  if t.bytes.length = 0 then return some (idx, idx - 1)
  else if idx ≥ 1 then return some (idx, idx + (lastindex t).val - 1)
  else return none

/-- The main loop of the byte `_rsearchindex`, `base/strings/search.jl:752-780`.
Every pass decreases `i`; bound `i`. -/
def rsearchLoop (s t : List UInt8) (n : Nat) (mask : UInt64) (skip : Int) (tfirst : UInt8) :
    Nat → Int → Int
  | 0, _ => 0
  | k + 1, i =>
    if i > 0 then
      if nth s i == tfirst then
        let j := (matchLen s t (i - 1) (n + 1) n 1)
        if j = n then i
        else
          let i := if i > 1 && (mask &&& bloomBit (nth s (i - 1))) == 0 then i - n else i - skip
          rsearchLoop s t n mask skip tfirst k (i - 1)
      else
        let i := if i > 1 && (mask &&& bloomBit (nth s (i - 1))) == 0 then i - n else i
        rsearchLoop s t n mask skip tfirst k (i - 1)
    else 0

/-- `_rsearchindex(s::AbstractVector{UInt8}, t::AbstractVector{UInt8}, _k)`,
`base/strings/search.jl:721-783`. -/
def rsearchindexBytes (s t : List UInt8) (k0 : Int) : SJl Int := do
  let n := t.length
  let m := s.length
  let k := k0
  if k < 0 then throw boundsErr
  if n = 0 then return (if 0 ≤ k ∧ k ≤ m then max k 1 else 0)
  if m = 0 then return 0
  if n = 1 then
    let r ← findprevByte s (nth t 1) (ix k)
    return (r.map (·.val)).getD 0
  let w : Int := (m : Int) - n
  if w < 0 ∨ k ≤ 0 then return 0
  let tfirst := nth t 1
  let (mask, skip) := ((List.range n).reverse).foldl (fun (acc : UInt64 × Int) j0 =>
    let j : Nat := j0 + 1
    let mask := acc.1 ||| bloomBit (nth t j)
    let skip := if nth t j == tfirst && j > 1 then (j : Int) - 2 else acc.2
    (mask, skip)) ((0 : UInt64), (n : Int) - 1)
  return rsearchLoop s t n mask skip tfirst (m + 2) (min (k - n + 1) (w + 1))

/-- `_rsearchindex(s::DenseUTF8String, t::DenseUTF8String, i)`, `base/strings/search.jl:705-719`. -/
def rsearchindexStr (s t : JStr) (i : JInt64) : SJl Int :=
  let lt := lastindex t
  if lt.val = 1 then
    match getindex t (ix 1) with
    | .error e => .error e
    | .ok c => (findprevChar c s i).map fun r => (r.map (·.val)).getD 0
  else if lt.val ≠ 0 then
    if i.val ≤ (ncodeunits s).val then
      match nextind s i with
      | .error e => .error e
      | .ok j => rsearchindexBytes s.bytes t.bytes (j - ix 1).val
    else rsearchindexBytes s.bytes t.bytes i.val
  else if i.val > s.bytes.length then .ok 0
  else if i.val = 0 then .ok 1
  else .ok i.val

/-- `findprev(t::AbstractString, s::AbstractString, i)` = `_rsearch(s, t, Int(i))`,
`base/strings/search.jl:785-796,821` for two Strings. -/
def findprevStr (t s : JStr) (i : JInt64) : SJl (Option (Int × Int)) := do
  let idx ← rsearchindexStr s t i
  if t.bytes.length = 0 then return some (idx, idx - 1)
  else if idx > 0 then return some (idx, idx + (lastindex t).val - 1)
  else return none

end JuliaLean.Strings

namespace JuliaLean.StringsCovA.Search

open JuliaLean JuliaLean.Strings

def lastUtf8Byte (c : UInt32) := Strings.lastUtf8Byte c
def standalone (b : UInt8) := Strings.isStandalone b
def fwCtor (s : JStr) (c : UInt32) := (s, c, lastUtf8Byte c)
def fwIterate (s : JStr) (c : UInt32) (i : JInt64) := Strings.fwIterate s c i
def iteratorSize : String := "SizeUnknown"
def iteratorEltype : String := "Int"
def rvCtor (s : JStr) (c : UInt32) := (s, c, lastUtf8Byte c)
def rvIterate (s : JStr) (c : UInt32) (i : JInt64) := Strings.rvIterate s c i
def tryNext {α β : Type} (iterate : α → β → Option (γ × β)) (x : α) (state : β) : Option γ :=
  (iterate x state).map (·.1)
def findnextChar (c : UInt32) (s : JStr) (i : JInt64) := Strings.findnextChar c s i
def findnextByte (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findnextByte a b i
def memchr (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findnextByte a b i
def findnextZero (a : List UInt8) (i : JInt64) := Strings.findnextByte a 0 i
def findprevChar (c : UInt32) (s : JStr) (i : JInt64) := Strings.findprevChar c s i
def findprevByte (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findprevByte a b i
def memrchr (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findprevByte a b i
def findprevZero (a : List UInt8) (i : JInt64) := Strings.findprevByte a 0 i
def findallChar (c : UInt32) (s : JStr) : List Int :=
  (Strings.collectPairs s).filterMap (fun x => if x.1 == c then some x.2.val else none)

def findfirstChar (c : UInt32) (s : JStr) := Strings.findnextChar c s (ix 1)
def findfirstBytes (pattern bytes : List UInt8) := Strings.searchindexBytes bytes pattern (ix 1)
def findnextPredicate (test : UInt32 → Bool) (s : JStr) (i : JInt64) : Option Int :=
  ((Strings.collectPairs s).dropWhile (fun x => x.2.val < i.val || !test x.1)).head?.map (·.2.val)
def charIn (c : UInt32) (s : JStr) := (Strings.chars s).contains c
def searchindexGeneric (s t : JStr) (i : JInt64) := Strings.searchindexStr s t i
/-- `base/strings/search.jl:386`: only `nothing` becomes the zero sentinel. -/
def searchindexChar (c : UInt32) (s : JStr) (i : JInt64) :=
  (Strings.findnextChar c s i).map (fun found => (found.map fun index => index.val).getD 0)

def bloomMask (b : UInt8) := Strings.bloomBit b
def nthString (s : JStr) (i : Int) := Strings.nth s.bytes i
def nthVector (s : List UInt8) (i : Int) := Strings.nth s i
def searchindexDense (s t : JStr) (i : JInt64) := Strings.searchindexStr s t i
def searchindexBytes (s t : List UInt8) (i : JInt64) := Strings.searchindexBytes s t i
def searchRange (s t : JStr) (i : JInt64) := Strings.findnextStr t s i

def findnextCharWrapper (c : UInt32) (s : JStr) (i : JInt64) := Strings.findnextChar c s i
def findnextBytesWrapper (p s : List UInt8) (i : JInt64) := Strings.searchindexBytes s p i
def findlastString (t s : JStr) := Strings.findprevStr t s (Strings.lastindex s)
def findlastBytes (t s : List UInt8) := Strings.rsearchindexBytes s t (s.length : Int)
def findlastChar (c : UInt32) (s : JStr) := Strings.findprevChar c s (Strings.lastindex s)
def findallLoop (findnext : Int → Option (Int × Int)) (nextind : Int → Int)
    (overlap : Bool) (last : Int) : Nat → Int → List (Int × Int)
  | 0, _ => []
  | fuel + 1, i =>
      match findnext i with
      | none => []
      | some r =>
          let j := if overlap || r.2 < r.1 then r.1 else r.2
          r :: if j > last then [] else findallLoop findnext nextind overlap last fuel (nextind j)
def findallRanges (findnext : Int → Option (Int × Int)) (nextind : Int → Int)
    (overlap : Bool) (first last : Int) : List (Int × Int) :=
  findallLoop findnext nextind overlap last (last - first + 2).toNat first

def findprevPredicate (test : UInt32 → Bool) (s : JStr) (i : JInt64) : Option Int :=
  ((Strings.collectPairs s).filter (fun x => x.2.val ≤ i.val && test x.1)).getLast?.map (·.2.val)
def rsearchindexGeneric (s t : JStr) (i : JInt64) := Strings.rsearchindexStr s t i
def rsearchindexDense (s t : JStr) (i : JInt64) := Strings.rsearchindexStr s t i
def rsearchindexBytes (s t : List UInt8) (i : Int) := Strings.rsearchindexBytes s t i
def rsearchRange (s t : JStr) (i : JInt64) := Strings.findprevStr t s i

def findprevCharWrapper (c : UInt32) (s : JStr) (i : JInt64) := Strings.findprevChar c s i
def findprevBytesWrapper (p s : List UInt8) (i : Int) := Strings.rsearchindexBytes s p i
def occursin (searchindex : JStr → JStr → JInt64 → SJl Int) (t s : JStr) : Bool :=
  match searchindex s t (ix 1) with | .ok i => i != 0 | .error _ => false
def occursinFix (searchindex : JStr → JStr → JInt64 → SJl Int) (haystack needle : JStr) :=
  occursin searchindex needle haystack
def stringInError : Jl Unit := .error (.argumentError "use occursin")
def byteIn (a : UInt8) (b : List UInt8) := b.contains a

end JuliaLean.StringsCovA.Search


namespace JuliaLean.StringsCovA.SearchRebuilt
open JuliaLean JuliaLean.Strings

/-! Concrete scalar helpers, `base/strings/search.jl:34-42`. -/

def lastUtf8Byte (character : UInt32) : UInt8 :=
  let shift := ((4 - Strings.ncodeunitsChar character) * 8) % 32
  (character >>> shift.toUInt32).toUInt8

def isStandaloneByte (byte : UInt8) : Bool := byte < 0x80 || byte > 0xf7

structure IntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64

structure FwIter where
  string : JStr
  character : UInt32
  lastByte : UInt8

def fwCtor (string : JStr) (convertChar : SJl UInt32) : SJl FwIter := do
  let character ← convertChar
  return ⟨string, character, Strings.lastUtf8Byte character⟩

def fwIterate (iterator : FwIter) (index : JInt64) :=
  Strings.fwIterate iterator.string iterator.character index

structure RvIter where
  string : JStr
  character : UInt32
  lastByte : UInt8

def rvCtor (string : JStr) (convertChar : SJl UInt32) : SJl RvIter := do
  let character ← convertChar
  return ⟨string, character, Strings.lastUtf8Byte character⟩

def rvIterate (iterator : RvIter) (index : JInt64) :=
  Strings.rvIterate iterator.string iterator.character index

def tryNext (iteration : SJl (Option (A × State))) : SJl (Option A) := do
  let result ← iteration
  return result.map Prod.fst

def findnextChar (character : UInt32) (string : JStr) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  Strings.findnextChar character string converted

structure DenseBytes where
  bytes : List UInt8
  firstindex : JInt64

def findnextByte (array : DenseBytes) (byte : UInt8) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  if converted < array.firstindex then .error boundsErr
  else Strings.findnextByte array.bytes byte converted

def memchr (array : DenseBytes) (byte : UInt8) (index : JInt64) : Option JInt64 :=
  (array.bytes.drop (index.val - array.firstindex.val).toNat).findIdx? (fun value => value == byte) |>
    Option.map (fun offset => index + ix (Int.ofNat offset))

def findnextZero (array : DenseBytes) (index : IntegerInput I) : SJl (Option JInt64) :=
  findnextByte array 0 index

def findprevChar (character : UInt32) (string : JStr) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  Strings.findprevChar character string converted

def findprevByte (array : DenseBytes) (byte : UInt8) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  Strings.findprevByte array.bytes byte converted

def memrchr (array : DenseBytes) (byte : UInt8) (index : JInt64) : Option JInt64 :=
  Strings.findprevByte array.bytes byte index |>.toOption.join

def findprevZero (array : DenseBytes) (index : IntegerInput I) : SJl (Option JInt64) :=
  findprevByte array 0 index

def findallChar (character : UInt32) (string : JStr) : List Int :=
  (Strings.collectPairs string).filterMap
    (fun pair => if pair.1 == character then some pair.2.val else none)

/-! Wrapper and generic-search methods, `base/strings/search.jl:301-916`. -/

structure IndexedBytes where
  bytes : List UInt8
  firstindex : JInt64

def lastindexBytes (array : IndexedBytes) : JInt64 :=
  array.firstindex + ix (Int.ofNat array.bytes.length) - ix 1

def findfirstString (pattern string : S) (firstindex : S → SJl JInt64)
    (findnext : S → S → JInt64 → SJl R) : SJl R := do
  let start ← firstindex string
  findnext pattern string start

def findfirstChar (character : C) (string : S)
    (findfirstPredicate : C → S → SJl R) : SJl R :=
  findfirstPredicate character string

def findfirstVector (pattern array : A) (firstindex : A → SJl JInt64)
    (search : A → A → JInt64 → SJl R) : SJl R := do
  let start ← firstindex array
  search array pattern start

structure PredicateStep (C : Type) where
  index : JInt64
  character : C

def firstAccepted (test : C → SJl Bool) : List (PredicateStep C) → SJl (Option JInt64)
  | [] => .ok none
  | step :: rest => do
      let accepted ← test step.character
      if accepted then return some step.index
      firstAccepted test rest

def findnextPredicate (steps : List (PredicateStep C)) (test : C → SJl Bool) : SJl (Option JInt64) :=
  firstAccepted test steps

def charInAbstract (character : C) (string : S)
    (findfirst : C → S → SJl (Option JInt64)) : SJl Bool := do
  let result ← findfirst character string
  return result.isSome

def charInDense (character : C) (string : S)
    (findnext : C → S → JInt64 → SJl (Option JInt64)) : SJl Bool := do
  let result ← findnext character string (ix 1)
  return result.isSome

def searchindexChar (findnext : SJl (Option JInt64)) : SJl JInt64 := do
  let result ← findnext
  return result.getD (ix 0)

def searchBloomMask (value : UInt64) : UInt64 := (1 : UInt64) <<< (value &&& 63)

def nthStringByte (codeunit : JInt64 → SJl UInt8) (index : JInt64) : SJl UInt8 :=
  codeunit index

def nthVectorByte (array : IndexedBytes) (index : JInt64) : SJl UInt8 :=
  let physical := index + (array.firstindex - ix 1)
  let offset := physical - array.firstindex
  if offset.val < 0 || offset.val ≥ array.bytes.length then .error boundsErr
  else .ok (array.bytes.getD offset.val.toNat 0)

def normalizeIndex (array : IndexedBytes) (index : JInt64) : JInt64 :=
  index - (array.firstindex - ix 1)

def restoreIndex (array : IndexedBytes) (index : Int) : JInt64 :=
  if index = 0 then array.firstindex - ix 1
  else ix index + (array.firstindex - ix 1)

def searchindexBytes (source pattern : IndexedBytes) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  let found ← Strings.searchindexBytes source.bytes pattern.bytes (normalizeIndex source converted)
  return restoreIndex source found

def denseSearchindex (singleByte : Bool) (index : IntegerInput I)
    (singleByteSearch : JInt64 → SJl (Option JInt64))
    (byteVectorSearch : JInt64 → SJl Int) : SJl JInt64 := do
  let converted ← index.toInt
  if singleByte then
    let found ← singleByteSearch converted
    return found.getD (ix 0)
  let found ← byteVectorSearch converted
  return ix found

def searchRange (source pattern : IndexedBytes) (index : JInt64) : Option (JInt64 × JInt64) :=
  if pattern.bytes.isEmpty then some (index, index - ix 1)
  else if source.firstindex ≤ index then
    some (index, index + lastindexBytes pattern - pattern.firstindex)
  else none

/-- Prior master used the pattern's last index as if its first index were one. -/
def legacySearchRange (source pattern : IndexedBytes) (index : JInt64) :
    Option (JInt64 × JInt64) :=
  if pattern.bytes.isEmpty then some (index, index - ix 1)
  else if source.firstindex ≤ index then
    some (index, index + lastindexBytes pattern - ix 1)
  else none

def findnextString (pattern string : S) (start : IntegerInput I)
    (search : S → S → JInt64 → SJl R) : SJl R := do
  let converted ← start.toInt
  search string pattern converted

def findnextCharWrapper (character : C) (string : S) (start : I)
    (findnextPredicate : C → S → I → SJl R) : SJl R :=
  findnextPredicate character string start

def findnextVector (pattern array : A) (start : I)
    (search : A → A → I → SJl R) : SJl R := search array pattern start

def findlastString (pattern string : S) (lastindex : S → SJl I)
    (findprev : S → S → I → SJl R) : SJl R := do
  let start ← lastindex string
  findprev pattern string start

def findlastVector (pattern array : A) (lastindex : A → SJl I)
    (findprev : A → A → I → SJl R) : SJl R := do
  let start ← lastindex array
  findprev pattern array start

def findlastChar (character : C) (string : S)
    (findlastPredicate : C → S → SJl R) : SJl R :=
  findlastPredicate character string

structure MatchRange where
  first : JInt64
  last : JInt64
deriving DecidableEq

def findallResponses (overlap : Bool) (endIndex : JInt64)
    (nextind : JInt64 → SJl JInt64) : List (Option MatchRange) → SJl (List MatchRange)
  | [] => .ok []
  | none :: _ => .ok []
  | some range :: rest =>
      let pivot := if overlap = true ∨ range.last < range.first then range.first else range.last
      if endIndex < pivot then .ok [range]
      else do
        let _ ← nextind pivot
        let following ← findallResponses overlap endIndex nextind rest
        return range :: following

def findprevPredicate (steps : List (PredicateStep C)) (test : C → SJl Bool) : SJl (Option JInt64) :=
  firstAccepted test steps

structure GenericCandidate where
  index : JInt64
  suffixMatched : Bool

def firstMatchedCandidate : List GenericCandidate → Option JInt64
  | [] => none
  | candidate :: rest =>
      if candidate.suffixMatched then some candidate.index else firstMatchedCandidate rest

def lastMatchedCandidate : List GenericCandidate → Option JInt64
  | [] => none
  | candidate :: rest =>
      match lastMatchedCandidate rest with
      | some index => some index
      | none => if candidate.suffixMatched then some candidate.index else none

def searchindexGeneric (sourceFirst nextAfterLast start : JInt64)
    (patternEmpty : Bool) (candidates : List GenericCandidate) : SJl JInt64 :=
  let sentinel := sourceFirst - ix 1
  if patternEmpty then
    if sourceFirst ≤ start && start ≤ nextAfterLast then .ok start else .error boundsErr
  else .ok ((firstMatchedCandidate candidates).getD sentinel)

def rsearchindexGeneric (sourceFirst nextAfterLast start : JInt64)
    (patternEmpty : Bool) (candidates : List GenericCandidate) : SJl JInt64 :=
  if patternEmpty then
    if sourceFirst ≤ start && start ≤ nextAfterLast then .ok start else .error boundsErr
  else .ok ((lastMatchedCandidate candidates).getD (ix 0))

def rsearchindexBytes (source pattern : IndexedBytes) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  let normalized := normalizeIndex source converted
  let found ← Strings.rsearchindexBytes source.bytes pattern.bytes normalized.val
  return restoreIndex source found

def denseRsearchindex (index : IntegerInput I) (search : JInt64 → SJl Int) : SJl JInt64 := do
  let converted ← index.toInt
  let found ← search converted
  return ix found

def rsearchRange (source pattern : IndexedBytes) (index : JInt64) : Option (JInt64 × JInt64) :=
  if pattern.bytes.isEmpty then some (index, index - ix 1)
  else if source.firstindex - ix 1 < index then
    some (index, index + lastindexBytes pattern - pattern.firstindex)
  else none

def findprevString (pattern string : S) (start : IntegerInput I)
    (search : S → S → JInt64 → SJl R) : SJl R := do
  let converted ← start.toInt
  search string pattern converted

def findprevCharWrapper (character : C) (string : S) (start : I)
    (findprevPredicate : C → S → I → SJl R) : SJl R :=
  findprevPredicate character string start

def findprevVector (pattern array : A) (start : I)
    (search : A → A → I → SJl R) : SJl R := search array pattern start

def occursinSearch (needle haystack : S)
    (searchindex : S → S → JInt64 → SJl JInt64)
    (firstindex : S → SJl JInt64) : SJl Bool := do
  let start ← firstindex haystack
  let result ← searchindex haystack needle start
  return result.val ≠ 0

structure OccursinFix (S : Type) where
  haystack : S
  apply : S → S → SJl Bool

def makeOccursinFix (haystack : S) (occursin : S → S → SJl Bool) : OccursinFix S :=
  ⟨haystack, occursin⟩

inductive SearchError where
  | string (error : SErr)
  | errorException (message : String)
deriving Repr, DecidableEq

def stringIn : Except SearchError Unit :=
  .error (.errorException "use occursin(needle, haystack) for string containment")

def byteIn (byte : B) (array : A)
    (findfirst : B → A → SJl (Option I)) : SJl Bool := do
  let result ← findfirst byte array
  return !result.isNone

end JuliaLean.StringsCovA.SearchRebuilt

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- The loop of `findall(t, s; overlap)`, `base/strings/search.jl:651-665`, with
`find i = findnext(t, s, i)`; same bound as `countLoop`. -/
def findallLoop (find : JInt64 → RJl (Option (JInt64 × JInt64))) (s : JStr) (overlap : Bool)
    (e : JInt64) : Nat → JInt64 → List (JInt64 × JInt64) → RJl (List (JInt64 × JInt64))
  | 0, _, found => .ok found
  | f + 1, i, found =>
    match find i with
    | .error err => .error err
    | .ok none => .ok found
    | .ok (some r) =>
      let found := found ++ [r]
      let j := if overlap || decide (r.2.val < r.1.val) then r.1 else r.2
      if j.val > e.val then .ok found
      else
        match nextind s j with
        | .error err => .error (.str err)
        | .ok i => findallLoop find s overlap e f i found

/-- `findall(re, s; overlap)`, `base/strings/search.jl:651-665`. -/
def findall (re : Regex) (s : JStr) (overlap : Bool := false) : RJl (List (JInt64 × JInt64)) :=
  findallLoop (findnextRe re s) s overlap (lastindex s) (s.bytes.length + 2) (ix 1) []

end JuliaLean.RegexUnicode.Core
