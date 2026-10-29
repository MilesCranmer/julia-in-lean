import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.operators
import JuliaLean.base.anyall

/-!
# Model of `base/strings/basic.jl`

The model keeps Julia `Int` values as `JInt64`, preserves wrapping arithmetic, and takes the
implementations of later-loaded or user-extensible string operations as typed parameters. Character
and array iteration are represented by lazy step-by-step `IterSteps` traces; indexed byte access
retains the string's code-unit API and its errors.
-/

namespace JuliaLean.base.strings.basic

open JuliaLean

abbrev Index := JInt64
abbrev Char := UInt32

def int (n : Int) : Index := JInt.lit .i64 n
def boolInt (b : Bool) : Index := int (if b then 1 else 0)
def toUInt64 (n : Index) : JInt .u64 := JInt.rem .u64 n

/-- Runtime `i isa Int` check on a `BitInteger` value (`Int === Int64` on 64-bit platforms). -/
def isaInt {t : IntTy} (_ : JInt t) : Bool := t == .i64

def rangeSteps (first last : Index) : Nat :=
  if first.val ≤ last.val then (last.val - first.val + 1).toNat else 0

/-- A lazy, step-by-step iterator trace over a collection or string with element type `A`,
state type `St`, and error type `E`. Each constructor represents one call to `iterate`,
evaluated only if the loop reaches that step. -/
inductive IterSteps (A St E : Type) where
  | done : IterSteps A St E
  | fail (err : E) : IterSteps A St E
  | yield (elem : A) (state : St) (next : St → IterSteps A St E) : IterSteps A St E

def iterStepsOfList {A St E : Type} (defaultState : St) : List A → IterSteps A St E
  | [] => .done
  | x :: xs => .yield x defaultState (fun _ => iterStepsOfList defaultState xs)

def collectIterSteps {A St E : Type} : IterSteps A St E → Except E (List A)
  | .done => .ok []
  | .fail err => .error err
  | .yield x state next => do
      let rest ← collectIterSteps (next state)
      pure (x :: rest)

/-- Dispatch and primitive operations supplied by the selected `AbstractString` implementation. -/
structure StringOps (S R C CU CT E : Type) where
  ncodeunits : S → Index
  codeunitType : S → CT
  codeunitSize : CT → Index
  codeunit : S → Index → Except E CU
  isvalid : S → Index → Except E Bool
  iterateFirst : S → Except E (Option (C × Index))
  iterateAt : S → Index → Except E (Option (C × Index))
  iterationBound : S → Nat
  thisind : S → Index → Except E Index
  prevind : S → Index → Index → Except E Index
  nextind : S → Index → Index → Except E Index
  lastindex : S → Except E Index
  getindexSlice : S → Index → Index → Except E R
  checkbounds : S → Index → Except E Unit
  checkboundsBool : S → Index → Except E Bool
  boundsError : S → Index → E
  stringIndexError : S → Index → E
  methodError : String → E
  argumentError : String → E
  tupleTypeError : E
  isBoundsError : E → Bool
  characters : S → Except E (List C)
  sameReference : S → S → Bool
  equalChar : C → C → Bool
  lessChar : C → C → Bool

def collectStringChars {S C E : Type}
    (iterateAt : S → Index → Except E (Option (C × Index))) (s : S) :
    Nat → Option (C × Index) → Except E (List C)
  | 0, none => .ok []
  | 0, some (c, _) => .ok [c]
  | _ + 1, none => .ok []
  | fuel + 1, some (c, i) => do
      let next ← iterateAt s i
      let rest ← collectStringChars iterateAt s fuel next
      pure (c :: rest)

def iterStepsFromState {S C E : Type}
    (iterateAt : S → Index → Except E (Option (C × Index))) (s : S) :
    Nat → Option (C × Index) → IterSteps C Index E
  | 0, none => .done
  | 0, some (c, i) => .yield c i (fun _ => .done)
  | _ + 1, none => .done
  | fuel + 1, some (c, i) =>
      .yield c i (fun j =>
        match iterateAt s j with
        | .error err => .fail err
        | .ok next => iterStepsFromState iterateAt s fuel next)

def iterStepsOfOps {S R C CU CT E : Type} (ops : StringOps S R C CU CT E) (s : S) :
    IterSteps C Index E :=
  match ops.iterateFirst s with
  | .error err => .fail err
  | .ok first => iterStepsFromState ops.iterateAt s (ops.iterationBound s) first

structure IntegerRangeOps (R I E : Type) where
  isempty : R → Bool
  minimum : R → Except E I
  maximum : R → Except E I
  atLeastOne : I → Bool
  atMostN : I → Index → Bool

/-- Operations of an integer code-unit type `CU <: Integer` used by `_isascii`. -/
structure CodeUnitOps (CU : Type) where
  zero : CU
  bitor : CU → CU → CU
  toInt : CU → Int

def uint8CodeUnitOps : CodeUnitOps UInt8 where
  zero := 0
  bitor a b := a ||| b
  toInt a := Int.ofNat a.toNat

def jintCodeUnitOps (t : IntTy) : CodeUnitOps (JInt t) where
  zero := JInt.lit t 0
  bitor a b :=
    let bv := BitVec.ofInt t.bits a.val ||| BitVec.ofInt t.bits b.val
    JInt.wrap t (if t.signed then bv.toInt else Int.ofNat bv.toNat)
  toInt a := a.val

/-- Generic integer index operations for `AbstractVector{CU}` indexing in `_isascii`,
`_isascii_chunks`, and `isascii(::AbstractVector)`. -/
structure VectorIndexOps (Idx : Type) where
  toInt : Idx → Int
  ofInt : Int → Idx
  add : Idx → Idx → Idx
  sub : Idx → Idx → Idx

def indexVectorOps : VectorIndexOps Index where
  toInt i := i.val
  ofInt n := int n
  add a b := a + b
  sub a b := a - b

def jintVectorOps (t : IntTy) : VectorIndexOps (JInt t) where
  toInt i := i.val
  ofInt n := JInt.lit t n
  add a b := a + b
  sub a b := a - b

structure IndexedVector (Idx A : Type) where
  firstindex : Idx
  lastindex : Idx
  get : Idx → A

def genericRangeSteps {Idx : Type} (ix : VectorIndexOps Idx) (first last : Idx) : Nat :=
  if ix.toInt first ≤ ix.toInt last then (ix.toInt last - ix.toInt first + 1).toNat else 0

def lexCompare {C : Type} (equal less : C → C → Bool) :
    List C → List C → Index
  | [], [] => int 0
  | [], _ :: _ => int (-1)
  | _ :: _, [] => int 1
  | c :: cs, d :: ds =>
      if equal c d then lexCompare equal less cs ds
      else if less c d then int (-1) else int 1

def cmpLoop {S R C CU CT E : Type} (ops : StringOps S R C CU CT E) (a b : S) :
    Nat → Option (C × Index) → Option (C × Index) → Except E Index
  | 0, none, none => .ok (int 0)
  | 0, none, some _ => .ok (int (-1))
  | 0, some _, _ => .ok (int 1)
  | _ + 1, none, none => .ok (int 0)
  | _ + 1, none, some _ => .ok (int (-1))
  | _ + 1, some _, none => .ok (int 1)
  | fuel + 1, some (c, i), some (d, j) => do
      if !ops.equalChar c d then
        pure (JuliaLean.base.operators.ifelseValue (ops.lessChar c d) (int (-1)) (int 1))
      else
        let iv1 ← ops.iterateAt a i
        let iv2 ← ops.iterateAt b j
        cmpLoop ops a b fuel iv1 iv2
def lengthLoop {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (last : Index) : Nat → Index → Index → Except E Index
  | 0, _, count => .ok count
  | fuel + 1, k, count =>
      if k.val ≤ last.val then do
        let valid ← ops.isvalid s k
        lengthLoop ops s last fuel (k + int 1) (count + boolInt valid)
      else .ok count

def thisindLoop {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) : Nat → Index → Except E Index
  | 0, i => .ok i
  | fuel + 1, i =>
      if 1 < i.val then do
        if ← ops.isvalid s i then pure i
        else thisindLoop ops s fuel (i - int 1)
      else pure i

def previndLoop {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) : Nat → Index → Index → Except E Index
  | 0, i, n => .ok (i - n)
  | fuel + 1, i, n =>
      if 0 < n.val && 1 < i.val then do
        let i := i - int 1
        let valid ← ops.isvalid s i
        previndLoop ops s fuel i (n - boolInt valid)
      else .ok (i - n)

def nextindLoop {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (z : Index) : Nat → Index → Index → Except E Index
  | 0, i, n => .ok (i + n)
  | fuel + 1, i, n =>
      if 0 < n.val && i.val < z.val then do
        let i := i + int 1
        let valid ← ops.isvalid s i
        nextindLoop ops s z fuel i (n - boolInt valid)
      else .ok (i + n)

def asciiRangeLoop {Idx CU : Type} (ix : VectorIndexOps Idx) (cuOps : CodeUnitOps CU)
    (v : IndexedVector Idx CU) (last : Idx) : Nat → Idx → CU → CU
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      if ix.toInt n ≤ ix.toInt last then
        asciiRangeLoop ix cuOps v last fuel (ix.add n (ix.ofInt 1)) (cuOps.bitor acc (v.get n))
      else acc

def indexList : Index → Nat → List Index
  | _, 0 => []
  | i, fuel + 1 => i :: indexList (i + int 1) fuel

/-! ## AbstractString interface methods -/

/-!
Julia source: base/strings/basic.jl:1-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

import Core: Symbol

"""
The `AbstractString` type is the supertype of all string implementations in
Julia. Strings are encodings of sequences of [Unicode](https://unicode.org/)
code points as represented by the `AbstractChar` type. Julia makes a few assumptions
about strings:

* Strings are encoded in terms of fixed-size "code units"
  * Code units can be extracted with `codeunit(s, i)`
  * The first code unit has index `1`
  * The last code unit has index `ncodeunits(s)`
  * Any index `i` such that `1 ≤ i ≤ ncodeunits(s)` is in bounds
* String indexing is done in terms of these code units:
  * Characters are extracted by `s[i]` with a valid string index `i`
  * Each `AbstractChar` in a string is encoded by one or more code units
  * Only the index of the first code unit of an `AbstractChar` is a valid index
  * The encoding of an `AbstractChar` is independent of what precedes or follows it
  * String encodings are [self-synchronizing](https://en.wikipedia.org/wiki/Self-synchronizing_code) – i.e. `isvalid(s, i)` is O(1)

Some string functions that extract code units, characters or substrings from
strings error if you pass them out-of-bounds or invalid string indices. This
includes `codeunit(s, i)` and `s[i]`. Functions that do string
index arithmetic take a more relaxed approach to indexing and give you the
closest valid string index when in-bounds, or when out-of-bounds, behave as if
there were an infinite number of characters padding each side of the string.
Usually these imaginary padding characters have code unit length `1` but string
types may choose different "imaginary" character sizes as makes sense for their
implementations (e.g. substrings may pass index arithmetic through to the
underlying string they provide a view into). Relaxed indexing functions include
those intended for index arithmetic: `thisind`, `nextind` and `prevind`. This
model allows index arithmetic to work with out-of-bounds indices as
intermediate values so long as one never uses them to retrieve a character,
which often helps avoid needing to code around edge cases.

See also [`codeunit`](@ref), [`ncodeunits`](@ref), [`thisind`](@ref),
[`nextind`](@ref), [`prevind`](@ref).
"""
AbstractString
```
-/

/-- Error type preserving `MethodError(f, args)` with its exact argument tuple `args`,
alongside underlying exceptions `E`. -/
inductive MethodCallError (Args E : Type) where
  | methodError (fn : String) (args : Args)
  | base (err : E)
  deriving DecidableEq, Repr

/-- Code-unit type tags for `AbstractString` implementations (`UInt8`, `UInt16`, `UInt32`). -/
inductive CodeunitTag where
  | uint8
  | uint16
  | uint32
  deriving DecidableEq, Repr

namespace CodeunitTag
def toType : CodeunitTag → Type
  | .uint8 => UInt8
  | .uint16 => UInt16
  | .uint32 => UInt32

def byteSize : CodeunitTag → Index
  | .uint8 => int 1
  | .uint16 => int 2
  | .uint32 => int 4
end CodeunitTag

/-- Interface structure for `AbstractString` carrying the bodyless interface declarations
`ncodeunits(s::AbstractString)` and `codeunit(s::AbstractString)` together with their
documented interface laws:
- `codeunit(s)` is one of `UInt8`, `UInt16`, `UInt32`
- `codeunit(s, i)` is defined and returns a value of type `codeunit(s)` iff `1 ≤ i ≤ ncodeunits(s)`. -/
structure AbstractStringInterface (S E : Type) where
  ncodeunits : S → Index
  codeunit : S → CodeunitTag
  codeunitAt : (s : S) → Index → Except E (codeunit s).toType
  codeunit_mem : ∀ s : S, codeunit s ∈ [CodeunitTag.uint8, .uint16, .uint32]
  codeunitAt_inbounds : ∀ (s : S) (i : Index),
    (1 ≤ i.val ∧ i.val ≤ (ncodeunits s).val) ↔
      ∃ u : (codeunit s).toType, codeunitAt s i = .ok u
/--
Julia source: base/strings/basic.jl:45-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    ncodeunits(s::AbstractString)::Int

Return the number of code units in a string. Indices that are in bounds to
access this string must satisfy `1 ≤ i ≤ ncodeunits(s)`. Not all such indices
are valid – they may not be the start of a character, but they will return a
code unit value when calling `codeunit(s,i)`.

# Examples
```jldoctest
julia> ncodeunits("The Julia Language")
18

julia> ncodeunits("∫eˣ")
6

julia> ncodeunits('∫'), ncodeunits('e'), ncodeunits('ˣ')
(3, 1, 2)
```

See also [`codeunit`](@ref), [`checkbounds`](@ref), [`sizeof`](@ref),
[`length`](@ref), [`lastindex`](@ref).
"""
ncodeunits(s::AbstractString)
````
-/
def ncodeunits {S E : Type} (iface : AbstractStringInterface S E) (s : S) : Index :=
  iface.ncodeunits s

/--
Julia source: base/strings/basic.jl:70-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    codeunit(s::AbstractString)::Type{<:Union{UInt8, UInt16, UInt32}}

Return the code unit type of the given string object. For ASCII, Latin-1, or
UTF-8 encoded strings, this would be `UInt8`; for UCS-2 and UTF-16 it would be
`UInt16`; for UTF-32 it would be `UInt32`. The code unit type need not be
limited to these three types, but it's hard to think of widely used string
encodings that don't use one of these units. `codeunit(s)` is the same as
`typeof(codeunit(s,1))` when `s` is a non-empty string.

See also [`ncodeunits`](@ref).
"""
codeunit(s::AbstractString)
```
-/
def codeunit {S E : Type} (iface : AbstractStringInterface S E) (s : S) : CodeunitTag :=
  iface.codeunit s
/--
Julia source: base/strings/basic.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const CodeunitType = Union{Type{UInt8},Type{UInt16},Type{UInt32}}
```
-/
def CodeunitType : List CodeunitTag := [.uint8, .uint16, .uint32]

/--
Julia source: base/strings/basic.jl:86-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    codeunit(s::AbstractString, i::Integer)::Union{UInt8, UInt16, UInt32}

Return the code unit value in the string `s` at index `i`. Note that

    codeunit(s, i) :: codeunit(s)

I.e. the value returned by `codeunit(s, i)` is of the type returned by
`codeunit(s)`.

# Examples
```jldoctest
julia> a = codeunit("Hello", 2)
0x65

julia> typeof(a)
UInt8
```

See also [`ncodeunits`](@ref), [`checkbounds`](@ref).
"""
@propagate_inbounds codeunit(s::AbstractString, i::Integer) = i isa Int ?
    throw(MethodError(codeunit, (s, i))) : codeunit(s, Int(i)::Int)
````
-/
def codeunitInteger {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (isInt : I → Bool) (toInt : I → Except E Index) (s : S) (i : I) :
    Except (MethodCallError (S × I) E) CU :=
  if isInt i then
    .error (.methodError "codeunit" (s, i))
  else
    match do ops.codeunit s (← toInt i) with
    | .ok cu => .ok cu
    | .error err => .error (.base err)

/--
Julia source: base/strings/basic.jl:110-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isvalid(s::AbstractString, i::Integer)::Bool

Predicate indicating whether the given index is the start of the encoding of a
character in `s` or not. If `isvalid(s, i)` is true then `s[i]` will return the
character whose encoding starts at that index, if it's false, then `s[i]` will
raise an invalid index error or a bounds error depending on if `i` is in bounds.
In order for `isvalid(s, i)` to be an O(1) function, the encoding of `s` must be
[self-synchronizing](https://en.wikipedia.org/wiki/Self-synchronizing_code). This
is a basic assumption of Julia's generic string support.

See also [`getindex`](@ref), [`iterate`](@ref), [`thisind`](@ref),
[`nextind`](@ref), [`prevind`](@ref), [`length`](@ref).

# Examples
```jldoctest
julia> str = "αβγdef";

julia> isvalid(str, 1)
true

julia> str[1]
'α': Unicode U+03B1 (category Ll: Letter, lowercase)

julia> isvalid(str, 2)
false

julia> str[2]
ERROR: StringIndexError: invalid index [2], valid nearby indices [1]=>'α', [3]=>'β'
Stacktrace:
[...]
```
"""
@propagate_inbounds isvalid(s::AbstractString, i::Integer) = i isa Int ?
    throw(MethodError(isvalid, (s, i))) : isvalid(s, Int(i)::Int)
````
-/
def isvalidInteger {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (isInt : I → Bool) (toInt : I → Except E Index) (s : S) (i : I) :
    Except (MethodCallError (S × I) E) Bool :=
  if isInt i then
    .error (.methodError "isvalid" (s, i))
  else
    match do ops.isvalid s (← toInt i) with
    | .ok v => .ok v
    | .error err => .error (.base err)

/--
Julia source: base/strings/basic.jl:146-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    iterate(s::AbstractString, i::Integer)::Union{Tuple{<:AbstractChar, Int}, Nothing}

Return a tuple of the character in `s` at index `i` with the index of the start
of the following character in `s`. This is the key method that allows strings to
be iterated, yielding a sequences of characters. The `iterate` function, as part
of the iteration protocol may assume that `i` is the start of a character in `s`.

See also [`getindex`](@ref), [`checkbounds`](@ref).
"""
@propagate_inbounds iterate(s::AbstractString, i::Integer) = i isa Int ?
    throw(MethodError(iterate, (s, i))) : iterate(s, Int(i)::Int)
```
-/
def iterateInteger {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (isInt : I → Bool) (toInt : I → Except E Index) (s : S) (i : I) :
    Except (MethodCallError (S × I) E) (Option (C × Index)) :=
  if isInt i then
    .error (.methodError "iterate" (s, i))
  else
    match do ops.iterateAt s (← toInt i) with
    | .ok next => .ok next
    | .error err => .error (.base err)
/--
Julia source: base/strings/basic.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:AbstractString}) = Char # some string types may use another AbstractChar
```
-/
def eltypeString (_S : Type) : Type := Char

/--
Julia source: base/strings/basic.jl:163-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    sizeof(str::AbstractString)

Size, in bytes, of the string `str`. Equal to the number of code units in `str` multiplied by
the size, in bytes, of one code unit in `str`.

# Examples
```jldoctest
julia> sizeof("")
0

julia> sizeof("∀")
3
```
"""
sizeof(s::AbstractString) = ncodeunits(s)::Int * sizeof(codeunit(s)::CodeunitType)
````
-/
def sizeofString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E) (s : S) : Index :=
  ops.ncodeunits s * ops.codeunitSize (ops.codeunitType s)

/--
Julia source: base/strings/basic.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(s::AbstractString) = 1
```
-/
def firstindexString {S : Type} (_s : S) : Index := int 1

/--
Julia source: base/strings/basic.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(s::AbstractString) = thisind(s, ncodeunits(s)::Int)
```
-/
def lastindexString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) : Except E Index :=
  ops.thisind s (ops.ncodeunits s)

/--
Julia source: base/strings/basic.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(s::AbstractString) = iszero(ncodeunits(s)::Int)
```
-/
def isemptyString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E) (s : S) : Bool :=
  (ops.ncodeunits s).val == 0

/--
Julia source: base/strings/basic.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds first(s::AbstractString) = s[firstindex(s)]
```
-/
def firstString {S C E : Type} (getindex : S → Index → Except E C)
    (s : S) : Except E C :=
  getindex s (firstindexString s)

/--
Julia source: base/strings/basic.jl:185-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(s::AbstractString, i::Integer)
    @boundscheck checkbounds(s, i)
    @inbounds return isvalid(s, i) ? (iterate(s, i)::NTuple{2,Any})[1] : string_index_err(s, i)
end
```
-/
def getindexInteger {S C E I : Type} (checkbounds : S → I → Except E Unit)
    (isvalid : S → I → Except E Bool)
    (iterate : S → I → Except E (Option (C × Index)))
    (stringIndexError : S → I → E) (tupleTypeError : E)
    (s : S) (i : I) : Except E C := do
  checkbounds s i
  if ← isvalid s i then
    match ← iterate s i with
    | some (c, _) => pure c
    | none => throw tupleTypeError
  else throw (stringIndexError s i)

def getindexString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (i : Index) : Except E C :=
  getindexInteger ops.checkbounds ops.isvalid ops.iterateAt ops.stringIndexError
    ops.tupleTypeError s i

/--
Julia source: base/strings/basic.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(s::AbstractString, i::Colon) = s
```
-/
def getindexColon {S : Type} (s : S) : S := s

def getindexVectorLoop {S I St C E IO : Type}
    (checkbounds : S → I → Except E Unit)
    (isvalid : S → I → Except E Bool)
    (iterate : S → I → Except E (Option (C × Index)))
    (stringIndexError : S → I → E) (tupleTypeError : E)
    (write : IO → C → Except E IO)
    (s : S) : IterSteps I St E → IO → Except E IO
  | .done, io => .ok io
  | .fail err, _ => .error err
  | .yield i state next, io => do
      let c ← getindexInteger checkbounds isvalid iterate stringIndexError tupleTypeError s i
      let io ← write io c
      getindexVectorLoop checkbounds isvalid iterate stringIndexError tupleTypeError write
        s (next state) io

/--
Julia source: base/strings/basic.jl:193-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(s::AbstractString, v::AbstractVector{<:Integer}) =
    sprint(io->(for i in v; write(io, s[i]) end), sizehint=length(v))
```
-/
def getindexVector {S V I St C E IO O : Type}
    (checkbounds : S → I → Except E Unit)
    (isvalid : S → I → Except E Bool)
    (iterate : S → I → Except E (Option (C × Index)))
    (stringIndexError : S → I → E) (tupleTypeError : E)
    (lengthV : V → Except E Index)
    (iterateV : V → IterSteps I St E)
    (write : IO → C → Except E IO)
    (sprint : (IO → Except E IO) → Index → Except E O)
    (s : S) (v : V) : Except E O := do
  let hint ← lengthV v
  sprint
    (getindexVectorLoop checkbounds isvalid iterate stringIndexError tupleTypeError write
      s (iterateV v))
    hint

/--
Julia source: base/strings/basic.jl:195-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(s::AbstractString, v::AbstractVector{Bool}) =
    throw(ArgumentError("logical indexing not supported for strings"))
```
-/
def getindexBoolVector {S R C CU CT E V O : Type} (ops : StringOps S R C CU CT E)
    (_s : S) (_indices : V) : Except E O :=
  .error (ops.argumentError "logical indexing not supported for strings")

/--
Julia source: base/strings/basic.jl:198-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get(s::AbstractString, i::Integer, default)
    checkbounds(Bool, s, i) ? (@inbounds s[i]) : default
end
```
-/
def getString {S C D E I : Type} (checkbounds : S → I → Except E Bool)
    (getindex : S → I → Except E C) (s : S) (i : I) (default : D) : Except E (C ⊕ D) := do
  if ← checkbounds s i then pure (.inl (← getindex s i)) else pure (.inr default)
/--
Julia source: base/strings/basic.jl:202-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## bounds checking ##

checkbounds(::Type{Bool}, s::AbstractString, i::Integer) =
    1 ≤ i ≤ ncodeunits(s)::Int
```
-/
def checkboundsScalar {S I : Type} (ncodeunits : S → Index)
    (atLeastOne : I → Bool) (atMostN : I → Index → Bool) (s : S) (i : I) : Bool :=
  atLeastOne i && atMostN i (ncodeunits s)

/--
Julia source: base/strings/basic.jl:206-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(::Type{Bool}, s::AbstractString, r::AbstractRange{<:Integer}) =
    isempty(r) || (1 ≤ minimum(r) && maximum(r) ≤ ncodeunits(s)::Int)
```
-/
def checkboundsRange {S R C CU CT E X I : Type} (ops : StringOps S R C CU CT E)
    (rangeOps : IntegerRangeOps X I E) (s : S) (r : X) : Except E Bool := do
  if rangeOps.isempty r then pure true
  else
    let lo ← rangeOps.minimum r
    if !rangeOps.atLeastOne lo then pure false
    else
      let hi ← rangeOps.maximum r
      pure (rangeOps.atMostN hi (ops.ncodeunits s))
/--
Julia source: base/strings/basic.jl:208-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(::Type{Bool}, s::AbstractString, I::AbstractArray{<:Real}) =
    all(i -> checkbounds(Bool, s, i), I)
```
-/
def checkboundsRealArray {S Arr A E : Type}
    (items : Arr → List A)
    (checkbounds : S → A → Except E Bool)
    (s : S) (indices : Arr) :
    Except (JuliaLean.base.anyall.AnyAllError E) (Option Bool) :=
  JuliaLean.base.anyall.allPredicate JuliaLean.base.anyall.allAny items
    (fun i => do pure (.bool (← checkbounds s i))) indices

/--
Julia source: base/strings/basic.jl:210-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(::Type{Bool}, s::AbstractString, I::AbstractArray{<:Integer}) =
    all(i -> checkbounds(Bool, s, i), I)
```
-/
def checkboundsIntegerArray {S Arr I E : Type}
    (items : Arr → List I)
    (checkbounds : S → I → Except E Bool)
    (s : S) (indices : Arr) :
    Except (JuliaLean.base.anyall.AnyAllError E) (Option Bool) :=
  JuliaLean.base.anyall.allPredicate JuliaLean.base.anyall.allAny items
    (fun i => do pure (.bool (← checkbounds s i))) indices

/--
Julia source: base/strings/basic.jl:212-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(s::AbstractString, I::Union{Integer,AbstractArray}) =
    checkbounds(Bool, s, I) ? nothing : throw(BoundsError(s, I))
```
-/
def checkbounds {S I E : Type} (checkboundsBool : S → I → Except E Bool)
    (boundsError : S → I → E) (s : S) (indices : I) : Except E Unit := do
  if ← checkboundsBool s indices then pure () else throw (boundsError s indices)

/-! ## Construction and conversion -/

/--
Julia source: base/strings/basic.jl:217-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string() = ""
```
-/
def stringEmpty : String := ""

/--
Julia source: base/strings/basic.jl:218-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(s::AbstractString) = s
```
-/
def stringIdentity {S : Type} (s : S) : S := s

/--
Julia source: base/strings/basic.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Vector{UInt8}(s::AbstractString) = unsafe_wrap(Vector{UInt8}, String(s))
```
-/
def vectorUInt8 {S V E : Type} (toString : S → Except E String)
    (unsafeWrap : String → Except E V) (s : S) : Except E V := do
  unsafeWrap (← toString s)

/--
Julia source: base/strings/basic.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Array{UInt8}(s::AbstractString) = unsafe_wrap(Vector{UInt8}, String(s))
```
-/
def arrayUInt8 {S V E : Type} (toString : S → Except E String)
    (unsafeWrap : String → Except E V) (s : S) : Except E V := do
  unsafeWrap (← toString s)

/--
Julia source: base/strings/basic.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Vector{T}(s::AbstractString) where {T<:AbstractChar} = collect(T, s)
```
-/
def vectorChars {S V E : Type} (T : Type)
    (collect : Type → S → Except E V) (s : S) : Except E V :=
  collect T s

/--
Julia source: base/strings/basic.jl:224-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Symbol(s::AbstractString) = Symbol(String(s)::String)
```
-/
def symbolString {S Sym E : Type} (toString : S → Except E String)
    (makeSymbol : String → Except E Sym) (s : S) : Except E Sym := do
  makeSymbol (← toString s)

/--
Julia source: base/strings/basic.jl:225-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Symbol(x...) = Symbol(string(x...))
```
-/
def symbolArgs {Args Sym E : Type} (stringArgs : Args → Except E String)
    (makeSymbol : String → Except E Sym) (xs : Args) : Except E Sym := do
  makeSymbol (← stringArgs xs)

/--
Julia source: base/strings/basic.jl:227-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, s::T) where {T<:AbstractString} = s
```
-/
def convertIdentity {T : Type} (s : T) : T := s

/--
Julia source: base/strings/basic.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, s::AbstractString) where {T<:AbstractString} = T(s)::T
```
-/
def convertString {S T E : Type} (construct : S → Except E T) (s : S) : Except E T :=
  construct s

/-! ## Summary and concatenation -/

/--
Julia source: base/strings/basic.jl:232-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function summary(io::IO, s::AbstractString)
    prefix = isempty(s) ? "empty" : string(ncodeunits(s), "-codeunit")
    print(io, prefix, " ", typeof(s))
end
```
-/
def summary {S R C CU CT E IO : Type} (ops : StringOps S R C CU CT E)
    (intString : Index → String) (typeName : S → String)
    (print : IO → List String → Except E Unit) (io : IO) (s : S) : Except E Unit :=
  let prefixString := if isemptyString ops s then "empty"
    else intString (ops.ncodeunits s) ++ "-codeunit"
  print io [prefixString, " ", typeName s]

/-- Type lattice for `_isannotated(S::Type)`: represents `Union{}` (`bottom`), subtypes of
`AnnotatedString`, subtypes of `AnnotatedChar`, or any other type (`other`). -/
inductive AnnotType where
  | bottom
  | annotatedString (subId : Nat := 0)
  | annotatedChar (subId : Nat := 0)
  | other (typeId : Nat := 0)
  deriving DecidableEq, Repr

def isSubtypeAnnotatedString : AnnotType → Bool
  | .bottom => true
  | .annotatedString _ => true
  | _ => false

def isSubtypeAnnotatedChar : AnnotType → Bool
  | .bottom => true
  | .annotatedChar _ => true
  | _ => false

/-- A string or character value paired with its runtime Julia type `typeof(s)`. -/
structure TypedValue (V : Type) where
  val : V
  typeof : AnnotType
  deriving DecidableEq, Repr

/--
Julia source: base/strings/basic.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isannotated(S::Type) = S != Union{} && (S <: AnnotatedString || S <: AnnotatedChar)
```
-/
def isannotatedType (S : AnnotType) : Bool :=
  (S != .bottom) && (isSubtypeAnnotatedString S || isSubtypeAnnotatedChar S)

/--
Julia source: base/strings/basic.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isannotated(s) = _isannotated(typeof(s))
```
-/
def isannotatedValue {V : Type} (s : TypedValue V) : Bool :=
  isannotatedType s.typeof

/--
Julia source: base/strings/basic.jl:257-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (*)(s1::Union{AbstractChar, AbstractString}, ss::Union{AbstractChar, AbstractString}...)
    if _isannotated(s1) || any(_isannotated, ss)
        annotatedstring(s1, ss...)
    else
        string(s1, ss...)
    end
end
```
-/
def concat {V1 V O E : Type}
    (annotatedString string : TypedValue V1 → List (TypedValue V) → Except E O)
    (s1 : TypedValue V1) (ss : List (TypedValue V))
    (isNTuple : Bool := false) : Except E O :=
  let anySs :=
    match JuliaLean.base.anyall.anyTupleMethod
        JuliaLean.base.anyall.anyTupleLoop
        JuliaLean.base.anyall.anyTupleStep
        JuliaLean.base.anyall.anyTupleDone
        (fun x => (.ok (.bool (isannotatedValue x)) :
          Except E JuliaLean.base.anyall.PredicateValue))
        isNTuple ss with
    | .ok (some b) => b
    | _ => false
  if isannotatedValue s1 || anySs then
    annotatedString s1 ss
  else
    string s1 ss
/--
Julia source: base/strings/basic.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
one(::Union{T,Type{T}}) where {T<:AbstractString} = convert(T, "")
```
-/
def oneString {T E : Type} (construct : String → Except E T) (_x : T ⊕ Unit := .inr ()) : Except E T :=
  convertString construct ""

/--
Julia source: base/strings/basic.jl:308-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(a::AbstractString, b::AbstractString)
    a === b && return 0
    (iv1, iv2) = (iterate(a), iterate(b))
    while iv1 !== nothing && iv2 !== nothing
        (c, d) = (first(iv1)::AbstractChar, first(iv2)::AbstractChar)
        c ≠ d && return ifelse(c < d, -1, 1)
        (iv1, iv2) = (iterate(a, last(iv1)), iterate(b, last(iv2)))
    end
    return iv1 === nothing ? (iv2 === nothing ? 0 : -1) : 1
end
```
-/
def cmp {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) : Except E Index := do
  if ops.sameReference a b then return int 0
  let iv1 ← ops.iterateFirst a
  let iv2 ← ops.iterateFirst b
  cmpLoop ops a b (ops.iterationBound a + ops.iterationBound b + 1) iv1 iv2

/--
Julia source: base/strings/basic.jl:335-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::AbstractString, b::AbstractString) = cmp(a, b) == 0
```
-/
def eq {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) : Except E Bool := do
  pure ((← cmp ops a b).val == 0)

/--
Julia source: base/strings/basic.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::AbstractString, b::AbstractString) = cmp(a, b) < 0
```
-/
def isless {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) : Except E Bool := do
  pure ((← cmp ops a b).val < 0)

/--
Julia source: base/strings/basic.jl:359-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :total function cmp(a::Symbol, b::Symbol)
    Int(sign(ccall(:strcmp, Int32, (Cstring, Cstring), a, b)))
end
```
-/
def cmpSymbol {Sym : Type} (strcmp : Sym → Sym → JInt .i32) (a b : Sym) : Index :=
  int (Int.sign (strcmp a b).val)

/--
Julia source: base/strings/basic.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::Symbol, b::Symbol) = cmp(a, b) < 0
```
-/
def islessSymbol {Sym : Type} (strcmp : Sym → Sym → JInt .i32) (a b : Sym) : Bool :=
  (cmpSymbol strcmp a b).val < 0

/-! ## Character index arithmetic -/

/--
Julia source: base/strings/basic.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(s::AbstractString) = @inbounds return length(s, 1, ncodeunits(s)::Int)
```
-/
def lengthString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (lengthBetween : S → Index → Index → Except E Index) (s : S) : Except E Index :=
  lengthBetween s (int 1) (ops.ncodeunits s)

/--
Julia source: base/strings/basic.jl:398-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(s::AbstractString, i::Int, j::Int)
    @boundscheck begin
        0 < i ≤ ncodeunits(s)::Int+1 || throw(BoundsError(s, i))
        0 ≤ j < ncodeunits(s)::Int+1 || throw(BoundsError(s, j))
    end
    n = 0
    for k = i:j
        @inbounds n += isvalid(s, k)
    end
    return n
end
```
-/
def lengthInt {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (i j : Index) : Except E Index := do
  if !(0 < i.val) then throw (ops.boundsError s i)
  if !(i.val ≤ (ops.ncodeunits s + int 1).val) then throw (ops.boundsError s i)
  if !(0 ≤ j.val) then throw (ops.boundsError s j)
  if !(j.val < (ops.ncodeunits s + int 1).val) then throw (ops.boundsError s j)
  lengthLoop ops s j (rangeSteps i j) i (int 0)

/--
Julia source: base/strings/basic.jl:410-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds length(s::AbstractString, i::Integer, j::Integer) =
    length(s, Int(i)::Int, Int(j)::Int)
```
-/
def lengthInteger {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (toInt : I → Except E Index) (s : S) (i j : I) : Except E Index := do
  let i ← toInt i
  let j ← toInt j
  lengthInt ops s i j

/--
Julia source: base/strings/basic.jl:445-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
thisind(s::AbstractString, i::Integer) = thisind(s, Int(i)::Int)
```
-/
def thisindInteger {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (toInt : I → Except E Index) (s : S) (i : I) : Except E Index := do
  ops.thisind s (← toInt i)

/--
Julia source: base/strings/basic.jl:447-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function thisind(s::AbstractString, i::Int)
    z = ncodeunits(s)::Int + 1
    i == z && return i
    @boundscheck 0 ≤ i ≤ z || throw(BoundsError(s, i))
    @inbounds while 1 < i && !(isvalid(s, i)::Bool)
        i -= 1
    end
    return i
end
```
-/
def thisindInt {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (i : Index) : Except E Index := do
  let z := ops.ncodeunits s + int 1
  if i.val == z.val then pure i
  else if !(0 ≤ i.val && i.val ≤ z.val) then throw (ops.boundsError s i)
  else thisindLoop ops s (i.val.toNat + 1) i

/--
Julia source: base/strings/basic.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(s::AbstractString, i::Integer, n::Integer) = prevind(s, Int(i)::Int, Int(n)::Int)
```
-/
def previndIntegerN {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (toInt : I → Except E Index) (s : S) (i n : I) : Except E Index := do
  let i ← toInt i
  let n ← toInt n
  ops.prevind s i n

/--
Julia source: base/strings/basic.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(s::AbstractString, i::Int)                 = prevind(s, i, 1)
```
-/
def previndOne {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (i : Index) : Except E Index :=
  ops.prevind s i (int 1)

/--
Julia source: base/strings/basic.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prevind(s::AbstractString, i::Integer)             = prevind(s, Int(i)::Int)
```
-/
def previndInteger {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (toInt : I → Except E Index) (s : S) (i : I) : Except E Index := do
  previndOne ops s (← toInt i)

/--
Julia source: base/strings/basic.jl:505-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function prevind(s::AbstractString, i::Int, n::Int)
    n < 0 && throw(ArgumentError("n cannot be negative: $n"))
    z = ncodeunits(s)::Int + 1
    @boundscheck 0 < i ≤ z || throw(BoundsError(s, i))
    n == 0 && return thisind(s, i)::Int == i ? i : string_index_err(s, i)
    while n > 0 && 1 < i
        @inbounds n -= isvalid(s, i -= 1)::Bool
    end
    return i - n
end
```
-/
def previndInt {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (intString : Index → String) (s : S) (i n : Index) : Except E Index := do
  if n.val < 0 then throw (ops.argumentError ("n cannot be negative: " ++ intString n))
  let z := ops.ncodeunits s + int 1
  if !(0 < i.val && i.val ≤ z.val) then throw (ops.boundsError s i)
  if n.val == 0 then
    if (← ops.thisind s i).val == i.val then return i
    else throw (ops.stringIndexError s i)
  previndLoop ops s (i.val.toNat - 1) i n

/--
Julia source: base/strings/basic.jl:560-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(s::AbstractString, i::Integer, n::Integer) = nextind(s, Int(i)::Int, Int(n)::Int)
```
-/
def nextindIntegerN {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (toInt : I → Except E Index) (s : S) (i n : I) : Except E Index := do
  let i ← toInt i
  let n ← toInt n
  ops.nextind s i n

/--
Julia source: base/strings/basic.jl:561-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(s::AbstractString, i::Integer)             = nextind(s, Int(i)::Int, 1)
```
-/
def nextindInteger {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (toInt : I → Except E Index) (s : S) (i : I) : Except E Index := do
  ops.nextind s (← toInt i) (int 1)

/--
Julia source: base/strings/basic.jl:562-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nextind(s::AbstractString, i::Int)                 = nextind(s, i, 1)
```
-/
def nextindOne {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : S) (i : Index) : Except E Index :=
  ops.nextind s i (int 1)

/--
Julia source: base/strings/basic.jl:564-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nextind(s::AbstractString, i::Int, n::Int)
    n < 0 && throw(ArgumentError("n cannot be negative: $n"))
    z = ncodeunits(s)::Int
    @boundscheck 0 ≤ i ≤ z || throw(BoundsError(s, i))
    n == 0 && return thisind(s, i)::Int == i ? i : string_index_err(s, i)
    while n > 0 && i < z
        @inbounds n -= isvalid(s, i += 1)::Bool
    end
    return i + n
end
```
-/
def nextindInt {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (intString : Index → String) (s : S) (i n : Index) : Except E Index := do
  if n.val < 0 then throw (ops.argumentError ("n cannot be negative: " ++ intString n))
  let z := ops.ncodeunits s
  if !(0 ≤ i.val && i.val ≤ z.val) then throw (ops.boundsError s i)
  if n.val == 0 then
    if (← ops.thisind s i).val == i.val then return i
    else throw (ops.stringIndexError s i)
  nextindLoop ops s z (z.val - i.val).toNat i n
/-! ## String index iteration -/

/--
Julia source: base/strings/basic.jl:577-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct EachStringIndex{T<:AbstractString}
    s::T
end
```
-/
structure EachStringIndex (S : Type) where
  s : S

/--
Julia source: base/strings/basic.jl:580-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(s::AbstractString) = EachStringIndex(s)
```
-/
def keysString {S : Type} (s : S) : EachStringIndex S := ⟨s⟩

/--
Julia source: base/strings/basic.jl:582-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(e::EachStringIndex) = length(e.s)
```
-/
def lengthEachStringIndex {S E : Type} (e : EachStringIndex S)
    (length : S → Except E Index) : Except E Index :=
  length e.s

/--
Julia source: base/strings/basic.jl:583-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(::EachStringIndex) = 1
```
-/
def firstEachStringIndex {S : Type} (_e : EachStringIndex S) : Index := int 1

/--
Julia source: base/strings/basic.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(e::EachStringIndex) = lastindex(e.s)
```
-/
def lastEachStringIndex {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (e : EachStringIndex S) : Except E Index :=
  ops.lastindex e.s

/--
Julia source: base/strings/basic.jl:585-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(e::EachStringIndex, state=firstindex(e.s)) = state > ncodeunits(e.s) ? nothing : (state, nextind(e.s, state))
```
-/
def iterateEachStringIndex {S R C CU CT E St : Type} (ops : StringOps S R C CU CT E)
    (ofIndex : Index → St)
    (gt : St → Index → Except E Bool)
    (nextind : S → St → Except E Index)
    (e : EachStringIndex S) (state : Option St := none) :
    Except E (Option (St × Index)) := do
  let state := state.getD (ofIndex (firstindexString e.s))
  if ← gt state (ops.ncodeunits e.s) then pure none
  else do
    let next ← nextind e.s state
    pure (some (state, next))

/--
Julia source: base/strings/basic.jl:586-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:EachStringIndex}) = Int
```
-/
def eltypeEachStringIndex (_E : Type) : Type := Index

/-! ## ASCII tests -/

def bswap32 (x : UInt32) : UInt32 :=
  ((x &&& 0xff) <<< 24) ||| (((x >>> 8) &&& 0xff) <<< 16) |||
    (((x >>> 16) &&& 0xff) <<< 8) ||| (x >>> 24)

/--
Julia source: base/strings/basic.jl:618-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isascii(c::Char) = bswap(reinterpret(UInt32, c)) < 0x80
```
-/
def isasciiChar (c : UInt32) : Bool :=
  decide (bswap32 c < 0x80)

/--
Julia source: base/strings/basic.jl:619-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isascii(s::AbstractString) = all(isascii, s)
```
-/
def isasciiString {S C E : Type}
    (items : S → List C)
    (isAscii : C → Except E Bool)
    (s : S) :
    Except (JuliaLean.base.anyall.AnyAllError E) (Option Bool) :=
  JuliaLean.base.anyall.allPredicate JuliaLean.base.anyall.allAny items
    (fun c => do pure (.bool (← isAscii c))) s

/--
Julia source: base/strings/basic.jl:620-620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isascii(c::AbstractChar) = UInt32(c) < 0x80
```
-/
def isasciiAbstractChar {C : Type} (toUInt32 : C → UInt32) (c : C) : Bool :=
  decide (toUInt32 c < 0x80)

/--
Julia source: base/strings/basic.jl:622-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _isascii(code_units::AbstractVector{CU}, first, last) where {CU}
    r = zero(CU)
    for n = first:last
        @inbounds r |= code_units[n]
    end
    return 0 ≤ r < 0x80
end
```
-/
def isasciiRange {Idx CU : Type} (ix : VectorIndexOps Idx) (cuOps : CodeUnitOps CU)
    (v : IndexedVector Idx CU) (first last : Idx) : Bool :=
  let r := asciiRangeLoop ix cuOps v last (genericRangeSteps ix first last) first cuOps.zero
  decide (0 ≤ cuOps.toInt r ∧ cuOps.toInt r < 0x80)

def asciiChunksLoop {Idx CU : Type} (ix : VectorIndexOps Idx) (cuOps : CodeUnitOps CU)
    (v : IndexedVector Idx CU) (chunk last : Idx) : Nat → Idx → Bool
  | 0, _ => isasciiRange ix cuOps v (ix.add (ix.sub last chunk) (ix.ofInt 1)) last
  | fuel + 1, n =>
      if ix.toInt n ≤ ix.toInt (ix.sub last chunk) then
        if !isasciiRange ix cuOps v n (ix.sub (ix.add n chunk) (ix.ofInt 1)) then
          false
        else
          asciiChunksLoop ix cuOps v chunk last fuel (ix.add n chunk)
      else
        isasciiRange ix cuOps v (ix.add (ix.sub last chunk) (ix.ofInt 1)) last

/--
Julia source: base/strings/basic.jl:631-638 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function  _isascii_chunks(chunk_size,cu::AbstractVector{CU}, first,last) where {CU}
    n=first
    while n <= last - chunk_size
        _isascii(cu,n,n+chunk_size-1) || return false
        n += chunk_size
    end
    return  _isascii(cu,last-chunk_size+1,last)
end
```
-/
def isasciiChunks {Idx CU : Type} (ix : VectorIndexOps Idx) (cuOps : CodeUnitOps CU)
    (v : IndexedVector Idx CU) (chunk first last : Idx) : Bool :=
  asciiChunksLoop ix cuOps v chunk last
    (genericRangeSteps ix first (ix.sub last chunk)) first

/--
Julia source: base/strings/basic.jl:645-653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isascii(cu::AbstractVector{CU}) where {CU <: Integer}
    # Note that String and SubString{String} assume this is :nothrow :foldable
    chunk_size = 1024
    chunk_threshold =  chunk_size + (chunk_size ÷ 2)
    first = firstindex(cu);   last = lastindex(cu)
    l = last - first + 1
    l < chunk_threshold && return _isascii(cu,first,last)
    return _isascii_chunks(chunk_size,cu,first,last)
end
```
-/
def isasciiVector {Idx CU : Type} (ix : VectorIndexOps Idx) (cuOps : CodeUnitOps CU)
    (v : IndexedVector Idx CU) : Bool :=
  let chunkSize := ix.ofInt 1024
  let chunkThreshold := ix.ofInt (1024 + 1024 / 2)
  let first := v.firstindex
  let last := v.lastindex
  let len := ix.add (ix.sub last first) (ix.ofInt 1)
  if ix.toInt len < ix.toInt chunkThreshold then
    isasciiRange ix cuOps v first last
  else
    isasciiChunks ix cuOps v chunkSize first last

/-! ## String map and filter -/

structure StringBuilderOps (B A E O : Type) where
  newStringVector : Index → Except E B
  length : B → Index
  resize : B → JInt .u64 → Except E B
  isAbstractChar : A → Bool
  convertChar : A → Except E UInt32
  unsafeString : B → UInt32 → JInt .u64 → Except E (B × JInt .u64)
  sizehint : B → JInt .u64 → Except E Unit
  makeString : B → Except E O
  divide : Index → Index → Except E Index
structure StringBuffer where
  capacity : Index
  chars : List UInt32

def charListBuilder {E : Type} : StringBuilderOps StringBuffer UInt32 E (List UInt32) where
  newStringVector capacity := .ok ⟨capacity, []⟩
  length buffer := buffer.capacity
  resize buffer capacity := .ok { buffer with capacity := int capacity.val }
  isAbstractChar _ := true
  convertChar char := .ok char
  unsafeString buffer char _ := .ok ({ buffer with chars := buffer.chars ++ [char] }, JInt.lit .u64 1)
  sizehint _ _ := .ok ()
  makeString buffer := .ok buffer.chars
  divide a b := .ok (int (a.val.tdiv b.val))

structure Utf8StringBuffer where
  capacity : Index
  bytes : List UInt8
  chars : List UInt32

def utf8CharBytes (c : UInt32) : List UInt8 :=
  let u := c.toNat
  if u < 0x80 then
    [UInt8.ofNat u]
  else if u < 0x800 then
    [UInt8.ofNat (0xc0 + u / 64), UInt8.ofNat (0x80 + u % 64)]
  else if u < 0x10000 then
    [UInt8.ofNat (0xe0 + u / 4096), UInt8.ofNat (0x80 + (u / 64) % 64),
     UInt8.ofNat (0x80 + u % 64)]
  else
    [UInt8.ofNat (0xf0 + u / 262144), UInt8.ofNat (0x80 + (u / 4096) % 64),
     UInt8.ofNat (0x80 + (u / 64) % 64), UInt8.ofNat (0x80 + u % 64)]

def utf8StringBuilder {A E : Type} (isAbstractChar : A → Bool)
    (convertChar : A → Except E UInt32) :
    StringBuilderOps Utf8StringBuffer A E (List UInt8 × List UInt32) where
  newStringVector capacity := .ok ⟨capacity, [], []⟩
  length buffer := buffer.capacity
  resize buffer capacity := .ok { buffer with capacity := int capacity.val }
  isAbstractChar := isAbstractChar
  convertChar := convertChar
  unsafeString buffer char _ :=
    let enc := utf8CharBytes char
    .ok ({ buffer with bytes := buffer.bytes ++ enc, chars := buffer.chars ++ [char] },
         JInt.lit .u64 (Int.ofNat enc.length))
  sizehint _ _ := .ok ()
  makeString buffer := .ok (buffer.bytes, buffer.chars)
  divide a b := .ok (int (a.val.tdiv b.val))

def mapChars {C A B E : Type} (f : C → Except E A) (isAbstractChar : A → Bool)
    (convertChar : A → Except E UInt32) (length : B → Index)
    (resize : B → JInt .u64 → Except E B)
    (unsafeString : B → UInt32 → JInt .u64 → Except E (B × JInt .u64))
    (argumentError : String → E) : IterSteps C Index E → B → JInt .u64 → Except E (B × JInt .u64)
  | .done, out, index => .ok (out, index)
  | .fail err, _, _ => .error err
  | .yield c state next, out, index => do
      let mapped ← f c
      if !isAbstractChar mapped then
        throw (argumentError
          "map(f, s::AbstractString) requires f to return AbstractChar; try map(f, collect(s)) or a comprehension instead")
      let out ← if (index + JInt.lit .u64 3).val > (toUInt64 (length out)).val then
          resize out (toUInt64 (length out * int 2))
        else pure out
      let char ← convertChar mapped
      let (out, width) ← unsafeString out char index
      mapChars f isAbstractChar convertChar length resize unsafeString argumentError
        (next state) out (index + width)

/--
Julia source: base/strings/basic.jl:657-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function map(f, s::AbstractString)
    out = StringVector(max(4, sizeof(s)::Int÷sizeof(codeunit(s)::CodeunitType)))
    index = UInt(1)
    for c::AbstractChar in s
        c′ = f(c)
        isa(c′, AbstractChar) || throw(ArgumentError(
            "map(f, s::AbstractString) requires f to return AbstractChar; " *
            "try map(f, collect(s)) or a comprehension instead"))
        index + 3 > length(out) && resize!(out, unsigned(2 * length(out)))
        index += __unsafe_string!(out, convert(Char, c′), index)
    end
    resize!(out, index-1)
    sizehint!(out, index-1)
    return String(out)
end
```
-/
def mapString {S R C CU CT E A B O : Type} (ops : StringOps S R C CU CT E)
    (iterate : S → IterSteps C Index E)
    (builder : StringBuilderOps B A E O) (f : C → Except E A) (s : S) : Except E O := do
  let units ← builder.divide (sizeofString ops s) (ops.codeunitSize (ops.codeunitType s))
  let out ← builder.newStringVector
    (JuliaLean.base.operators.max
      (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
      JuliaLean.base.operators.ifelseValue (int 4) units)
  let (out, index) ← mapChars f builder.isAbstractChar builder.convertChar builder.length
    builder.resize builder.unsafeString ops.argumentError (iterate s) out (JInt.lit .u64 1)
  let finalLength := index - JInt.lit .u64 1
  let out ← builder.resize out finalLength
  let _ ← builder.sizehint out finalLength
  builder.makeString out

def ioBufferNew {C E : Type} (_sizehint : Index) : Except E (List C) := .ok []
def ioBufferWrite {C E : Type} (buf : List C) (c : C) : Except E (List C) := .ok (buf ++ [c])
def ioBufferTake {C E : Type} (buf : List C) : Except E (List C) := .ok buf

def filterChars {C B E : Type} (f : C → Except E Bool) (write : B → C → Except E B) :
    IterSteps C Index E → B → Except E B
  | .done, out => .ok out
  | .fail err, _ => .error err
  | .yield c state next, out => do
      let keep ← f c
      let out ← if keep then write out c else pure out
      filterChars f write (next state) out

/--
Julia source: base/strings/basic.jl:673-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f, s::AbstractString)
    out = IOBuffer(sizehint=sizeof(s))
    for c in s
        f(c) && write(out, c)
    end
    takestring!(out)
end
```
-/
def filterString {S R C CU CT E B O : Type} (ops : StringOps S R C CU CT E)
    (iterate : S → IterSteps C Index E)
    (newBuffer : Index → Except E B) (write : B → C → Except E B)
    (takeString : B → Except E O) (f : C → Except E Bool) (s : S) : Except E O := do
  let out ← newBuffer (sizeofString ops s)
  takeString (← filterChars f write (iterate s) out)
/-! ## First and last string portions -/

/--
Julia source: base/strings/basic.jl:700-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first(s::AbstractString, n::Integer) = @inbounds s[1:min(end, nextind(s, 0, n))]
```
-/
def firstN {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (nextind : S → Index → Index → Except E Index)
    (toInt : I → Except E Index) (s : S) (n : I) : Except E R := do
  let endIndex ← ops.lastindex s
  let n ← toInt n
  let next ← nextind s (int 0) n
  ops.getindexSlice s (int 1)
    (JuliaLean.base.operators.min
      (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
      JuliaLean.base.operators.ifelseValue endIndex next)

/--
Julia source: base/strings/basic.jl:719-719 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(s::AbstractString, n::Integer) = @inbounds s[max(1, prevind(s, ncodeunits(s)+1, n)):end]
```
-/
def lastN {S R C CU CT E I : Type} (ops : StringOps S R C CU CT E)
    (prevind : S → Index → Index → Except E Index)
    (toInt : I → Except E Index) (s : S) (n : I) : Except E R := do
  let endIndex := ops.ncodeunits s + int 1
  let n ← toInt n
  let start ← prevind s endIndex n
  let lastIndex ← ops.lastindex s
  ops.getindexSlice s
    (JuliaLean.base.operators.max
      (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt)
      JuliaLean.base.operators.ifelseValue (int 1) start)
    lastIndex

/--
Julia source: base/strings/basic.jl:742-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverseind(s::AbstractString, i::Integer) = thisind(s, ncodeunits(s)-i+1)
```
-/
def reverseindString {S R C CU CT E I J : Type} (ops : StringOps S R C CU CT E)
    (subIndex : Index → I → J) (addOne : J → J)
    (toInt : J → Except E Index) (s : S) (i : I) : Except E Index :=
  thisindInteger ops toInt s (addOne (subIndex (ops.ncodeunits s) i))

/--
Julia source: base/strings/basic.jl:757-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeat(s::AbstractString, r::Integer) = repeat(String(s)::String, r)
```
-/
def repeatString {S E R O : Type} (toString : S → Except E String)
    (repeatFn : String → R → Except E O) (s : S) (r : R) : Except E O := do
  repeatFn (← toString s) r

/--
Julia source: base/strings/basic.jl:772-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(^)(s::Union{AbstractString,AbstractChar}, r::Integer) = repeat(s, r)
```
-/
def powerString {A R E O : Type} (repeatFn : A → R → Except E O) (s : A) (r : R) :
    Except E O :=
  repeatFn s r

structure ReverseString (S : Type) where
  itr : S

/--
Julia source: base/strings/basic.jl:775-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Iterators.Reverse{<:AbstractString}, i=lastindex(r.itr)) = i < firstindex(r.itr) ? nothing : (r.itr[i], prevind(r.itr, i))
```
-/
def reverseIterateString {S R C CU CT E St : Type} (ops : StringOps S R C CU CT E)
    (ofIndex : Index → St)
    (lt : St → Index → Except E Bool)
    (getindex : S → St → Except E C)
    (prevind : S → St → Except E Index)
    (r : ReverseString S) (state : Option St := none) :
    Except E (Option (C × Index)) := do
  let i ← match state with
    | some i => pure i
    | none => ofIndex <$> ops.lastindex r.itr
  if ← lt i (firstindexString r.itr) then pure none
  else do
    let c ← getindex r.itr i
    let prev ← prevind r.itr i
    pure (some (c, prev))

/--
Julia source: base/strings/basic.jl:776-776 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Iterators.Reverse{<:EachStringIndex}, i=lastindex(r.itr.s)) = i < firstindex(r.itr.s) ? nothing : (i, prevind(r.itr.s, i))
```
-/
def reverseIterateIndices {S R C CU CT E St : Type} (ops : StringOps S R C CU CT E)
    (ofIndex : Index → St)
    (lt : St → Index → Except E Bool)
    (prevind : S → St → Except E Index)
    (r : ReverseString (EachStringIndex S)) (state : Option St := none) :
    Except E (Option (St × Index)) := do
  let i ← match state with
    | some i => pure i
    | none => ofIndex <$> ops.lastindex r.itr.s
  if ← lt i (firstindexString r.itr.s) then pure none
  else do
    let prev ← prevind r.itr.s i
    pure (some (i, prev))

/-! ## Code unit access -/

/--
Julia source: base/strings/basic.jl:786-787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct CodeUnits{T,S<:AbstractString} <: DenseVector{T}
    s::S
```
-/
structure CodeUnits (T S : Type) where
  s : S

/--
Julia source: base/strings/basic.jl:788-789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CodeUnits(s::S) where {S<:AbstractString} = new{codeunit(s),S}(s)
end
```
-/
def codeUnitsCtor {S : Type} (codeunitType : S → Type) (s : S) :
    CodeUnits (codeunitType s) S :=
  ⟨s⟩

/--
Julia source: base/strings/basic.jl:791-791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(s::CodeUnits{T}) where {T} = ncodeunits(s.s) * sizeof(T)
```
-/
def codeUnitsSizeof {T S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (sizeofType : Type → Index) (s : CodeUnits T S) : Index :=
  ops.ncodeunits s.s * sizeofType T

/--
Julia source: base/strings/basic.jl:792-792 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(s::CodeUnits) = (ncodeunits(s.s),)
```
-/
def codeUnitsSize {T S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : CodeUnits T S) : Index × Unit :=
  (ops.ncodeunits s.s, ())

/--
Julia source: base/strings/basic.jl:793-793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elsize(s::Type{<:CodeUnits{T}}) where {T} = sizeof(T)
```
-/
def codeUnitsElsize {T : Type} (sizeofType : Type → Index) : Index :=
  sizeofType T

/--
Julia source: base/strings/basic.jl:794-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds getindex(s::CodeUnits, i::Int) = codeunit(s.s, i)
```
-/
def codeUnitsGetindex {T S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : CodeUnits T S) (i : Index) : Except E CU :=
  ops.codeunit s.s i

inductive ArrayIndexStyle where
  | linear
  deriving Repr, DecidableEq

/--
Julia source: base/strings/basic.jl:795-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:CodeUnits}) = IndexLinear()
```
-/
def codeUnitsIndexStyle : ArrayIndexStyle := .linear

/--
Julia source: base/strings/basic.jl:796-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checkbounds(::Type{Bool}, s::CodeUnits, i::Integer) = checkbounds(Bool, s.s, i)
```
-/
def codeUnitsCheckbounds {T S I Out : Type}
    (checkboundsBool : S → I → Out)
    (s : CodeUnits T S) (i : I) : Out :=
  checkboundsBool s.s i

/--
Julia source: base/strings/basic.jl:798-798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(s::CodeUnits) = dataids(s.s)
```
-/
def codeUnitsDataids {T S A : Type} (dataids : S → A) (s : CodeUnits T S) : A :=
  dataids s.s

/--
Julia source: base/strings/basic.jl:801-801 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::IO, s::CodeUnits) = write(io, s.s)
```
-/
def codeUnitsWrite {T S IO A E : Type} (write : IO → S → Except E A)
    (io : IO) (s : CodeUnits T S) : Except E A :=
  write io s.s

/--
Julia source: base/strings/basic.jl:803-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{T}},    s::CodeUnits{T}) where {T} = cconvert(Ptr{T}, s.s)
```
-/
def codeUnitsCconvert {T S A E : Type} (cconvert : S → Except E A)
    (s : CodeUnits T S) : Except E A :=
  cconvert s.s

/--
Julia source: base/strings/basic.jl:804-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{Int8}}, s::CodeUnits{UInt8}) = cconvert(Ptr{Int8}, s.s)
```
-/
def codeUnitsCconvertInt8 {S A E : Type} (cconvert : S → Except E A)
    (s : CodeUnits UInt8 S) : Except E A :=
  cconvert s.s

/--
Julia source: base/strings/basic.jl:806-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(::Type{<:CodeUnits{T}}, dims::Dims) where {T} = similar(Array{T}, dims)
```
-/
def codeUnitsSimilar {T D A : Type} (similarArray : T → D → A) (t : T) (dims : D) : A :=
  similarArray t dims

/--
Julia source: base/strings/basic.jl:827-827 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunits(s::AbstractString) = CodeUnits(s)
```
-/
def codeunits {S : Type} (codeunitType : S → Type) (s : S) : CodeUnits (codeunitType s) S :=
  codeUnitsCtor codeunitType s

/--
Julia source: base/strings/basic.jl:829-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _split_rest(s::AbstractString, n::Int)
    lastind = lastindex(s)
    i = try
        prevind(s, lastind, n)
    catch e
        e isa BoundsError || rethrow()
        _check_length_split_rest(length(s), n)
    end
    last_n = SubString(s, nextind(s, i), lastind)
    front = s[begin:i]
    return front, last_n
end
```
-/
def splitRest {S R C CU CT E Sub : Type} (ops : StringOps S R C CU CT E)
    (prevind : S → Index → Index → Except E Index)
    (nextind : S → Index → Index → Except E Index)
    (length : S → Except E Index)
    (checkLengthSplitRest : Index → Index → Except E Index)
    (substring : S → Index → Index → Except E Sub)
    (s : S) (n : Index) : Except E (R × Sub) := do
  let lastind ← ops.lastindex s
  let i ← match prevind s lastind n with
    | .ok i => pure i
    | .error e =>
        if ops.isBoundsError e then checkLengthSplitRest (← length s) n
        else throw e
  let next ← nextind s i (int 1)
  let lastN ← substring s next lastind
  let front ← ops.getindexSlice s (int 1) i
  pure (front, lastN)

/-! ## Finite string data for model counterexamples -/

structure StringData where
  bytes : List UInt8
  starts : List Index
  chars : List UInt32
  deriving DecidableEq

structure StringDataSpan where
  first : Index
  after : Index
  char : UInt32

def StringData.empty : StringData := ⟨[], [], []⟩

private theorem and_decide_iff (a b : Prop) [Decidable a] [Decidable b] :
    (a ∧ b) ↔ (decide a && decide b) = true := by
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

private theorem inbounds_if_ok {α E : Type} (p : Bool) (val : α) (err : E) :
    p = true ↔ ∃ u : α, (if p then Except.ok val else Except.error err) = .ok u := by
  cases p <;> simp

def stringDataInterface : AbstractStringInterface StringData JlError where
  ncodeunits s := int (Int.ofNat s.bytes.length)
  codeunit _ := .uint8
  codeunitAt s i :=
    if 1 ≤ i.val && i.val ≤ (int (Int.ofNat s.bytes.length)).val then
      .ok (s.bytes.getD (i.val.toNat - 1) 0)
    else .error .boundsError
  codeunit_mem _ := .head _
  codeunitAt_inbounds s i :=
    (and_decide_iff (1 ≤ i.val) (i.val ≤ (int (Int.ofNat s.bytes.length)).val)).trans
      (inbounds_if_ok _ _ _)
def stringDataOfLeanString (s : String) : StringData :=
  let cs := s.toList.map (fun c => c.val)
  ⟨cs.map (fun c => UInt8.ofNat c.toNat),
   (List.range cs.length).map (fun k => int (Int.ofNat (k + 1))),
   cs⟩

def stringDataConcat (s1 : TypedValue StringData) (ss : List (TypedValue StringData)) :
    Except JlError StringData :=
  .ok (ss.foldl (fun acc x =>
    ⟨acc.bytes ++ x.val.bytes,
     acc.starts ++ x.val.starts.map (fun i => i + int (Int.ofNat acc.bytes.length)),
     acc.chars ++ x.val.chars⟩) s1.val)

def stringDataSpans (afterLast : Index) : List Index → List UInt32 → List StringDataSpan
  | [], _ => []
  | first :: rest, c :: cs =>
      let after := match rest with | next :: _ => next | [] => afterLast
      ⟨first, after, c⟩ :: stringDataSpans afterLast rest cs
  | _ :: _, [] => []

def stringDataIterateAt (s : StringData) (i : Index) : Option (UInt32 × Index) :=
  let spans := stringDataSpans (int (Int.ofNat s.bytes.length) + int 1) s.starts s.chars
  match spans.find? (fun span => span.first.val == i.val) with
  | some span => some (span.char, span.after)
  | none => none

/-- Wire a primitive `StringOps` instance with the generic `basic.jl` definitions of
`thisind`, `prevind`, `nextind`, `lastindex`, and scalar `checkbounds`. -/
def modelStringOps {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (intString : Index → String) : StringOps S R C CU CT E :=
  let thisindOps := { ops with thisind := thisindInt ops }
  { thisindOps with
    checkboundsBool := fun s i =>
      .ok (checkboundsScalar ops.ncodeunits (fun i => decide (1 ≤ i.val))
        (fun i n => decide (i.val ≤ n.val)) s i)
    checkbounds := checkbounds
      (fun s i => .ok (checkboundsScalar ops.ncodeunits (fun i => decide (1 ≤ i.val))
        (fun i n => decide (i.val ≤ n.val)) s i))
      ops.boundsError
    prevind := previndInt thisindOps intString
    nextind := nextindInt thisindOps intString
    lastindex := lastindexString thisindOps }
def stringDataSlice (s : StringData) (first last : Index) : StringData :=
  let spans := stringDataSpans (int (Int.ofNat s.bytes.length) + int 1) s.starts s.chars
  let selected := spans.filter (fun span =>
    first.val ≤ span.first.val && span.first.val ≤ last.val)
  match selected with
  | [] => StringData.empty
  | span :: _ =>
      let after := selected.foldl (fun _ item => item.after) span.after
      let starts := selected.map (fun item => item.first - span.first + int 1)
      let chars := selected.map (·.char)
      let bytes := (s.bytes.drop (span.first.val - 1).toNat).take (after.val - span.first.val).toNat
      ⟨bytes, starts, chars⟩

def stringDataPrimOps : StringOps StringData StringData UInt32 UInt8 Unit JlError where
  ncodeunits s := int (Int.ofNat s.bytes.length)
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit s i :=
    if 1 ≤ i.val && i.val ≤ Int.ofNat s.bytes.length then .ok (s.bytes.getD (i.val.toNat - 1) 0)
    else .error .boundsError
  isvalid s i := .ok (s.starts.any (fun j => j.val == i.val))
  iterateFirst s := .ok (stringDataIterateAt s (int 1))
  iterateAt s i := .ok (stringDataIterateAt s i)
  iterationBound s := s.chars.length + 1
  thisind _ _ := .error .boundsError
  prevind _ _ _ := .error .boundsError
  nextind _ _ _ := .error .boundsError
  lastindex _ := .error .boundsError
  getindexSlice s i j := .ok (stringDataSlice s i j)
  checkbounds _ _ := .error .boundsError
  checkboundsBool _ _ := .error .boundsError
  boundsError _ _ := .boundsError
  stringIndexError _ _ := .methodError "StringIndexError"
  methodError name := .methodError name
  argumentError message := .argumentError message
  tupleTypeError := .methodError "tuple assertion"
  isBoundsError
    | .boundsError => true
    | _ => false
  characters s := .ok s.chars
  sameReference _ _ := false
  equalChar a b := decide (a = b)
  lessChar a b := decide (a < b)

/-- A byte string with explicit character starts, wired with the generic `basic.jl`
index-arithmetic and bounds-checking methods. -/
def stringDataIterateSteps (s : StringData) : IterSteps UInt32 Index JlError :=
  iterStepsOfList (int 1) s.chars

def stringDataOps : StringOps StringData StringData UInt32 UInt8 Unit JlError :=
  modelStringOps stringDataPrimOps (fun _ => "")

def charListSlice {C : Type} (chars : List C) (first last : Index) : List C :=
  if first.val ≤ last.val then
    (chars.drop (first.val - 1).toNat).take (last.val - first.val + 1).toNat
  else
    []

def charListPrimOps {C : Type} (defaultChar : C) :
    StringOps (List C) (List C) C UInt8 Unit JlError where
  ncodeunits s := int (Int.ofNat s.length)
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit s i :=
    if 1 ≤ i.val && i.val ≤ Int.ofNat s.length then .ok 0
    else .error .boundsError
  isvalid s i := .ok (decide (1 ≤ i.val && i.val ≤ Int.ofNat s.length))
  iterateFirst s :=
    match s with
    | [] => .ok none
    | c :: _ => .ok (some (c, int 2))
  iterateAt s i :=
    if 1 ≤ i.val && i.val ≤ Int.ofNat s.length then
      .ok (some (s.getD (i.val.toNat - 1) defaultChar, i + int 1))
    else .ok none
  iterationBound s := s.length + 1
  thisind _ _ := .error .boundsError
  prevind _ _ _ := .error .boundsError
  nextind _ _ _ := .error .boundsError
  lastindex _ := .error .boundsError
  getindexSlice s i j := .ok (charListSlice s i j)
  checkbounds _ _ := .error .boundsError
  checkboundsBool _ _ := .error .boundsError
  boundsError _ _ := .boundsError
  stringIndexError _ _ := .methodError "StringIndexError"
  methodError name := .methodError name
  argumentError message := .argumentError message
  tupleTypeError := .methodError "tuple assertion"
  isBoundsError
    | .boundsError => true
    | _ => false
  characters s := .ok s
  sameReference _ _ := false
  equalChar _ _ := false
  lessChar _ _ := false

def charListStringOps {C : Type} (defaultChar : C) (intString : Index → String) :
    StringOps (List C) (List C) C UInt8 Unit JlError :=
  modelStringOps (charListPrimOps defaultChar) intString


/-- Extract the characters whose start indices lie in the 1-based code-unit slice `first .. last`
of a variable-width code-unit layout `units : List (Option C)`, where `some c` marks the first
code unit of character `c` and `none` marks a continuation code unit of a multi-code-unit
character. -/
def codeunitSliceChars {C : Type} (units : List (Option C)) (first last : Index) : List C :=
  if first.val ≤ last.val then
    ((units.drop (first.val - 1).toNat).take (last.val - first.val + 1).toNat).filterMap id
  else
    []

def varWidthPrimOps {C : Type} :
    StringOps (List (Option C)) (List C) C UInt8 Unit JlError where
  ncodeunits s := int (Int.ofNat s.length)
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit s i :=
    if 1 ≤ i.val && i.val ≤ Int.ofNat s.length then .ok 0
    else .error .boundsError
  isvalid s i :=
    .ok (decide (1 ≤ i.val && i.val ≤ Int.ofNat s.length) &&
      (s.getD (i.val.toNat - 1) none).isSome)
  iterateFirst s :=
    match s.filterMap id with
    | [] => .ok none
    | c :: _ => .ok (some (c, int 2))
  iterateAt _ _ := .ok none
  iterationBound s := s.length + 1
  thisind _ _ := .error .boundsError
  prevind _ _ _ := .error .boundsError
  nextind _ _ _ := .error .boundsError
  lastindex _ := .error .boundsError
  getindexSlice s i j := .ok (codeunitSliceChars s i j)
  checkbounds _ _ := .error .boundsError
  checkboundsBool _ _ := .error .boundsError
  boundsError _ _ := .boundsError
  stringIndexError _ _ := .methodError "StringIndexError"
  methodError name := .methodError name
  argumentError message := .argumentError message
  tupleTypeError := .methodError "tuple assertion"
  isBoundsError
    | .boundsError => true
    | _ => false
  characters s := .ok (s.filterMap id)
  sameReference _ _ := false
  equalChar _ _ := false
  lessChar _ _ := false

def varWidthStringOps {C : Type} (intString : Index → String) :
    StringOps (List (Option C)) (List C) C UInt8 Unit JlError :=
  modelStringOps varWidthPrimOps intString
def leanStringPrimOps : StringOps String String Char UInt8 Unit JlError where
  ncodeunits s := int (Int.ofNat s.length)
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit s i :=
    if 1 ≤ i.val && i.val ≤ Int.ofNat s.length then .ok 0
    else .error .boundsError
  isvalid s i := .ok (decide (1 ≤ i.val && i.val ≤ Int.ofNat s.length))
  iterateFirst s :=
    match s.toList with
    | [] => .ok none
    | c :: _ => .ok (some (c.val, int 2))
  iterateAt s i :=
    if 1 ≤ i.val && i.val ≤ Int.ofNat s.toList.length then
      .ok (some ((s.toList.getD (i.val.toNat - 1) default).val, i + int 1))
    else .ok none
  iterationBound s := s.toList.length + 1
  thisind _ _ := .error .boundsError
  prevind _ _ _ := .error .boundsError
  nextind _ _ _ := .error .boundsError
  lastindex _ := .error .boundsError
  getindexSlice s _ _ := .ok s
  checkbounds _ _ := .error .boundsError
  checkboundsBool _ _ := .error .boundsError
  boundsError _ _ := .boundsError
  stringIndexError _ _ := .methodError "StringIndexError"
  methodError name := .methodError name
  argumentError message := .argumentError message
  tupleTypeError := .methodError "tuple assertion"
  isBoundsError
    | .boundsError => true
    | _ => false
  characters s := .ok (s.toList.map (fun c => c.val))
  sameReference a b := a == b
  equalChar a b := decide (a = b)
  lessChar a b := decide (a < b)

def leanStringOps : StringOps String String Char UInt8 Unit JlError :=
  modelStringOps leanStringPrimOps (fun _ => "")

def leanStringIterateSteps (s : String) : IterSteps Char Index JlError :=
  iterStepsOfList (int 1) (s.toList.map (fun c => c.val))

def checkboundsThrow {E : Type} (checkboundsBool : Except E Bool) (boundsError : E) :
    Except E Unit := do
  if ← checkboundsBool then pure () else throw boundsError

def cmpString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) : Except E Index :=
  cmp ops a b

def eqString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) : Except E Bool :=
  eq ops a b

def islessString {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) : Except E Bool :=
  isless ops a b
end JuliaLean.base.strings.basic