import JuliaLean.base.char
import JuliaLean.base.expr
import JuliaLean.base.strings.string
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.operators
import JuliaLean.base.anyall


section

/-!
# The TOML lexer with comment capture (`base/toml/parser.jl`)

Model, at master `bbfa0ce4150`, of the parser state and the character-level utilities of
`base/toml/parser.jl` including line/column bookkeeping and comment capture
(`comments !== nothing`), which `JuliaLean.Toml` leaves out; the comment containers
`CommentBlock` and `Comments`; the `Parser` constructors, `startup` and `reinit!`; the
`@try` macro; and `ParserError` with its formatting (`format_error_message_for_err_type`,
`point_to_line`, `showerror`).

Strings are their bytes and characters their raw `UInt32` values, as in `JuliaLean.Toml`
(`Toml.iterate` decodes UTF-8 as `base/strings/string.jl`). The parsed document, needed by
`path_traverses_array`, is a tree of tables, arrays and leaves. Every `while` loop consumes
one unit of fuel per iteration (each iteration eats at least one byte).
-/

namespace JuliaLean.DocsSyntaxCov.TomlLex

open JuliaLean JuliaLean.DocsSyntaxCov

/-- `prevind(s, i)` (`prevind(s, i, 1)`, `base/strings/basic.jl`): the previous valid index, or
`0`; a `BoundsError` unless `0 < i ≤ ncodeunits(s) + 1`. -/
def prevind (s : List Nat) (i : Int) : DJ Int :=
  if !(0 < i && i ≤ s.length + 1) then .error .boundsError
  else go (i.toNat) i
where
  go : Nat → Int → DJ Int
    | 0, _ => pure 0
    | k + 1, i =>
      if 1 < i then do
        let j := i - 1
        if (← thisind s j) == j then pure j else go k j
      else pure (i - 1)

end JuliaLean.DocsSyntaxCov.TomlLex

end


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

import Core
: Symbol

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
-- Source: base/strings/basic.jl:794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def codeUnitsGetindexWith {T S CU E : Type} (codeunit : S → Index → Except E CU)
    (s : CodeUnits T S) (i : Index) : Except E CU :=
  codeunit s.s i

def codeUnitsGetindex {T S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (s : CodeUnits T S) (i : Index) : Except E CU :=
  codeUnitsGetindexWith ops.codeunit s i

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


/-! Coverage models for `base/strings/basic.jl` at Julia `bbfa0ce4150`. -/


/-!
# Strings as UTF-8 code units

Model of `String` from `base/strings/string.jl` and the generic index
functions of `base/strings/basic.jl` (master `bbfa0ce4150`).

* A `String` is its byte sequence (`JStr.bytes`), with no validity
  requirement: overlong forms, surrogates, truncated sequences and stray
  continuation bytes are all representable, exactly as in Julia
  (`base/strings/string.jl:80-90`).
* A `Char` is its 32-bit encoded bit pattern (`base/char.jl:39-52`): the
  UTF-8 bytes of the character, left-aligned, padded with zero bytes.
  Bit patterns are Lean `UInt8`/`UInt32`, whose operators are the
  fixed-width wrapping operators Julia uses on those types.
* Indices and counts are `Int` (`JInt64`) and use the wrapping `JInt`
  operators, so overflow happens exactly where Julia overflows.
* Julia's `while` loops are written as structural recursion on an explicit
  bound on the number of remaining iterations (for example `n - i` when `i`
  increases towards `n`). Each docstring states the bound; when it reaches
  zero the loop condition is false, so the bound never truncates a run.
-/

namespace JuliaLean.Strings

/-- The loop of `nextind(s, i, n)`, `base/strings/basic.jl:569-572`:
`while n > 0 && i < z; n -= isvalid(s, i += 1); end; return i + n`.
The first argument is `z - i`, so at `0` the condition `i < z` is false. -/
def nextindNLoop (s : JStr) (z : JInt64) : Nat → JInt64 → JInt64 → JInt64
  | 0, i, n => i + n
  | k + 1, i, n =>
    if decide (n.val > 0) && decide (i.val < z.val) then
      let i := i + ix 1
      nextindNLoop s z k i (n - bInt (isvalidAt s i))
    else i + n

/-- `nextind(s::AbstractString, i::Int, n::Int)`, `base/strings/basic.jl:564-573`. -/
def nextindN (s : JStr) (i n : JInt64) : SJl JInt64 :=
  if n.val < 0 then .error (.jl (.argumentError "n cannot be negative"))
  else
    let z := ncodeunits s
    if !betweenI i (ix 0) z then .error boundsErr
    else if n.val = 0 then
      match thisind s i with
      | .error e => .error e
      | .ok j => if j.val = i.val then .ok i else .error (.stringIndexError i.val)
    else .ok (nextindNLoop s z (z.val - i.val).toNat i n)

/-- The loop of `prevind(s, i, n)`, `base/strings/basic.jl:510-513`:
`while n > 0 && 1 < i; n -= isvalid(s, i -= 1); end; return i - n`.
The first argument is `i - 1`, so at `0` the condition `1 < i` is false. -/
def previndNLoop (s : JStr) : Nat → JInt64 → JInt64 → JInt64
  | 0, i, n => i - n
  | k + 1, i, n =>
    if decide (n.val > 0) && decide (1 < i.val) then
      let i := i - ix 1
      previndNLoop s k i (n - bInt (isvalidAt s i))
    else i - n

/-- `prevind(s::AbstractString, i::Int, n::Int)`, `base/strings/basic.jl:505-514`.
`prevind(s, i)` is `prevind(s, i, 1)` (`:503`). -/
def previndN (s : JStr) (i n : JInt64) : SJl JInt64 :=
  if n.val < 0 then .error (.jl (.argumentError "n cannot be negative"))
  else
    let z := ncodeunits s + ix 1
    if !(decide (0 < i.val) && decide (i.val ≤ z.val)) then .error boundsErr
    else if n.val = 0 then
      match thisind s i with
      | .error e => .error e
      | .ok j => if j.val = i.val then .ok i else .error (.stringIndexError i.val)
    else .ok (previndNLoop s (i.val - 1).toNat i n)

/-- `prevind(s, i) = prevind(s, i, 1)`, `base/strings/basic.jl:503`. -/
def prevind (s : JStr) (i : JInt64) : SJl JInt64 := previndN s i (ix 1)

/-- `firstindex(s::AbstractString) = 1`, `base/strings/basic.jl:179`. -/
def firstindex (_ : JStr) : JInt64 := ix 1

end JuliaLean.Strings

namespace JuliaLean.Strings

/-- `min(x, y)` on Int: `ifelse(y < x, y, x)`. -/
def imin (x y : JInt64) : JInt64 := if y.val < x.val then y else x
/-- `max(x, y)` on Int: `ifelse(y < x, x, y)`. -/
def imax (x y : JInt64) : JInt64 := if y.val < x.val then x else y

/-- `first(s::AbstractString, n::Integer) = @inbounds s[1:min(end, nextind(s, 0, n))]`,
`base/strings/basic.jl:700`. -/
def firstN (s : JStr) (n : JInt64) : SJl JStr :=
  match nextindN s (ix 0) n with
  | .error e => .error e
  | .ok k => getindexRange s (ix 1) (imin (lastindex s) k) false

/-- `last(s::AbstractString, n::Integer) = @inbounds s[max(1, prevind(s, ncodeunits(s)+1, n)):end]`,
`base/strings/basic.jl:719`. -/
def lastN (s : JStr) (n : JInt64) : SJl JStr :=
  match previndN s (ncodeunits s + ix 1) n with
  | .error e => .error e
  | .ok k => getindexRange s (imax (ix 1) k) (lastindex s) false

/-- The loop of the generic `cmp(a::AbstractString, b::AbstractString)`,
`base/strings/basic.jl:308-317`; Char `<` compares bit patterns (`base/char.jl:264`). -/
def cmpLoop (a b : JStr) : Nat → Option (UInt32 × JInt64) → Option (UInt32 × JInt64) → Int
  | k + 1, some (c, i), some (d, j) =>
    if c != d then (if c < d then -1 else 1) else cmpLoop a b k (iterate a i) (iterate b j)
  | _, none, none => 0
  | _, none, some _ => -1
  | _, some _, _ => 1

def cmpGeneric (a b : JStr) : Int :=
  if a = b then 0
  else cmpLoop a b (a.bytes.length + 1) (iterate a (ix 1)) (iterate b (ix 1))

end JuliaLean.Strings

namespace JuliaLean.Strings

/-- `_isascii(cu, first, last)`, `base/strings/basic.jl:622-628`: OR the bytes. -/
def isasciiRange (bs : List UInt8) (a b : Int) : Bool :=
  let r := ((bs.drop (a - 1).toNat).take (b - a + 1).toNat).foldl (· ||| ·) 0
  decide (r < 0x80)

/-- `_isascii_chunks`, `base/strings/basic.jl:631-638`. Bound: `(last - n) / cs + 1`. -/
def isasciiChunksLoop (cs : Int) (bs : List UInt8) (last : Int) : Nat → Int → Bool
  | 0, _ => isasciiRange bs (last - cs + 1) last
  | k + 1, n =>
    if n ≤ last - cs then
      if !isasciiRange bs n (n + cs - 1) then false else isasciiChunksLoop cs bs last k (n + cs)
    else isasciiRange bs (last - cs + 1) last

instance : AsciiCodeUnitOps where
  range := isasciiRange
  chunks := isasciiChunksLoop

end JuliaLean.Strings

namespace JuliaLean.StringsCovA.Basic

open JuliaLean JuliaLean.Strings

/-- Integer fallbacks at lines 107-108,143-144,156-157. -/
def integerFallback {α : Type} (isMachineInt : Bool) (dispatch : Int → SJl α) (i : Int) : SJl α :=
  if isMachineInt then .error (.jl (.methodError "missing Int method")) else dispatch i

/-- Generic scalar methods at lines 161,178-228. -/
def eltypeString : String := "Char"
def sizeof (ncu unitBytes : Int) : Int := ncu * unitBytes
def firstindex : Int := 1
def lastindex (this : Int → Int) (ncu : Int) : Int := this ncu
def isempty (ncu : Int) : Bool := ncu == 0
def first {α : Type} (get : Int → SJl α) := get firstindex
def getindex {α : Type} (inbounds valid : Int → Bool) (iter : Int → α) (i : Int) : SJl α :=
  if !inbounds i then .error (.jl .boundsError)
  else if valid i then .ok (iter i) else .error (.stringIndexError i)
def getindexColon {α : Type} (s : α) : α := s
def getindexVector {α : Type} (get : Int → α) (is : List Int) : List α := is.map get
def getindexBool : SJl Unit := .error (.jl (.argumentError "logical indexing not supported for strings"))
def getDefault {α : Type} (inbounds : Int → Bool) (get : Int → α) (i : Int) (default : α) : α :=
  if inbounds i then get i else default
def checkboundsIndex (ncu i : Int) : Bool := decide (1 ≤ i ∧ i ≤ ncu)
def checkboundsRange (ncu lo hi : Int) : Bool := hi < lo || decide (1 ≤ lo ∧ hi ≤ ncu)
def checkboundsAll (check : Int → Bool) (is : List Int) : Bool := is.all check
def checkboundsThrow (ok : Bool) : Jl Unit := if ok then .ok () else .error .boundsError
def stringEmpty : List UInt8 := []
def stringIdentity {α : Type} (s : α) : α := s
def vectorBytes (toString : α → List UInt8) (s : α) : List UInt8 := toString s
def vectorChars (collect : α → List β) (s : α) : List β := collect s
def symbolString (intern : List UInt8 → Nat) (toString : α → List UInt8) (s : α) := intern (toString s)
def symbolArgs (render : List α → List UInt8) (intern : List UInt8 → Nat) (xs : List α) := intern (render xs)
def convertIdentity {α : Type} (s : α) : α := s
def convertString (ctor : α → β) (s : α) : β := ctor s

/-- Summary, concatenation, annotation, and comparison methods; lines 232-363. -/
def summary (ncu : Nat) (typeName : String) : String :=
  (if ncu = 0 then "empty" else toString ncu ++ "-codeunit") ++ " " ++ typeName
def concat (annotated : Bool) (plain annotatedJoin : List α → β) (xs : List α) : β :=
  if annotated then annotatedJoin xs else plain xs
def oneString (empty : α) : α := empty
def isannotatedType (isBottom isAnnotatedString isAnnotatedChar : Bool) : Bool :=
  !isBottom && (isAnnotatedString || isAnnotatedChar)
def isannotatedValue (typeCheck : α → Bool) (s : α) : Bool := typeCheck s
def cmpString (a b : JStr) : Int := cmpGeneric a b
def eqString (a b : JStr) : Bool := cmpString a b == 0
def islessString (a b : JStr) : Bool := decide (cmpString a b < 0)
def cmpSymbol (strcmp : Nat → Nat → Int) (a b : Nat) : Int := Int.sign (strcmp a b)
def islessSymbol (strcmp : Nat → Nat → Int) (a b : Nat) : Bool := decide (cmpSymbol strcmp a b < 0)

/-- Generic length and index arithmetic; lines 396-573. -/
def lengthString (s : JStr) := Strings.length s
def lengthBetween (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def thisindInteger (s : JStr) (i : JInt64) := Strings.thisind s i
def previndInteger (s : JStr) (i n : JInt64) := Strings.previndN s i n
def previndOne (s : JStr) (i : JInt64) := Strings.prevind s i
def nextindInteger (s : JStr) (i n : JInt64) := Strings.nextindN s i n
def nextindOne (s : JStr) (i : JInt64) := Strings.nextind s i

structure EachStringIndex where s : JStr

def keys (s : JStr) : EachStringIndex := ⟨s⟩
def eachLength (e : EachStringIndex) := Strings.length e.s
def eachFirst (_e : EachStringIndex) := ix 1
def eachLast (e : EachStringIndex) := Strings.lastindex e.s
def eachIterate (e : EachStringIndex) (state : JInt64) : Option (JInt64 × JInt64) :=
  if state.val > (Strings.ncodeunits e.s).val then none
  else match Strings.nextind e.s state with | .ok n => some (state, n) | .error _ => none
def eachEltype : String := "Int"
def isasciiChar (c : UInt32) : Bool := decide (c < 0x80)
def isasciiString (s : JStr) : Bool := Strings.isascii s
def isasciiRange (bytes : List UInt8) (first last : Int) := Strings.isasciiRange bytes first last
def isasciiChunks (chunk : Int) (bytes : List UInt8) (first last : Int) :=
  Strings.isasciiChunksLoop chunk bytes last bytes.length first
def isasciiVector (bytes : List UInt8) : Bool := bytes.all (· < 0x80)

/-- Mapping, filtering, slicing, repetition, and reverse iteration; lines 657-776. -/
def mapString (f : UInt32 → UInt32) (s : JStr) : SJl JStr := stringOfChars ((Strings.chars s).map f)
def filterString (f : UInt32 → Bool) (s : JStr) : SJl JStr := stringOfChars ((Strings.chars s).filter f)
def firstN (s : JStr) (n : JInt64) := Strings.firstN s n
def lastN (s : JStr) (n : JInt64) := Strings.lastN s n
def reverseind (this : Int → Int) (ncu i : Int) : Int := this (ncu - i + 1)
def repeatString (toString : α → JStr) (s : α) (r : JInt64) := Strings.repeatStr (toString s) r
def powerString (repeatFn : α → Int → β) (s : α) (r : Int) : β := repeatFn s r
def reverseIterate {α : Type} (first get prev : Int → α) (i : Int) : Option (α × α) :=
  if i < 1 then none else some (get i, prev i)

structure CodeUnits where bytes : List UInt8

def codeUnitsCtor (bytes : List UInt8) : CodeUnits := ⟨bytes⟩
def cuSizeof (s : CodeUnits) : Nat := s.bytes.length
def cuSize (s : CodeUnits) : Nat × Unit := (s.bytes.length, ())
def cuElsize : Nat := 1
def cuGetindex (s : CodeUnits) (i : Nat) : UInt8 := s.bytes.getD (i - 1) 0
def cuIndexStyle : String := "IndexLinear"
def cuCheckbounds (s : CodeUnits) (i : Int) : Bool := decide (1 ≤ i ∧ i ≤ s.bytes.length)
def cuDataids (id : List UInt8 → List Nat) (s : CodeUnits) := id s.bytes
def cuWrite (write : List UInt8 → Nat) (s : CodeUnits) := write s.bytes
def cuCconvert (convert : List UInt8 → Nat) (s : CodeUnits) := convert s.bytes
def cuSimilar (make : Nat → List UInt8) (n : Nat) := make n
def codeunits (bytes : List UInt8) : CodeUnits := codeUnitsCtor bytes
def splitRest (split : JStr → Int → JStr × JSub) (s : JStr) (n : Int) := split s n

end JuliaLean.StringsCovA.Basic


/-!
Faithful per-method models for rows rejected by the fixed review of
`base/strings/basic.jl` at Julia `bbfa0ce4150`.

An `IntegerInput` or `AbstractStringInput` records the observable dispatches
provided by an arbitrary Julia value.  This keeps conversion failures and
custom `AbstractString` behavior explicit instead of assuming `String`.
-/

namespace JuliaLean.StringsCovA.BasicRebuilt

open JuliaLean JuliaLean.Strings

structure IntegerInput (I : Type) where
  value : I
  isMachineInt : Bool
  toInt : SJl Int

/-! Integer fallbacks, lines 107-108, 143-144, and 156-157. -/

def codeunitInteger (s : S) (i : IntegerInput I)
    (codeunitInt : S → Int → SJl C) : SJl C :=
  if i.isMachineInt then .error (.jl (.methodError "codeunit(::AbstractString, ::Int) missing"))
  else do
    let converted ← i.toInt
    codeunitInt s converted

def isvalidInteger (s : S) (i : IntegerInput I)
    (isvalidInt : S → Int → SJl Bool) : SJl Bool :=
  if i.isMachineInt then .error (.jl (.methodError "isvalid(::AbstractString, ::Int) missing"))
  else do
    let converted ← i.toInt
    isvalidInt s converted

def iterateInteger (s : S) (i : IntegerInput I)
    (iterateInt : S → Int → SJl (Option (C × Int))) : SJl (Option (C × Int)) :=
  if i.isMachineInt then .error (.jl (.methodError "iterate(::AbstractString, ::Int) missing"))
  else do
    let converted ← i.toInt
    iterateInt s converted

/-! Scalar calls and bounds checks, lines 178-213. -/

structure AbstractStringInput (S : Type) where
  value : S
  ncodeunits : SJl Int
  codeunitSize : SJl Int
  firstindex : SJl Int

def sizeofString (s : AbstractStringInput S) : SJl Int := do
  let count ← s.ncodeunits
  let unitSize ← s.codeunitSize
  return count * unitSize

def lastindexString (s : AbstractStringInput S)
    (thisind : S → Int → SJl Int) : SJl Int := do
  let count ← s.ncodeunits
  thisind s.value count

def isemptyString (s : AbstractStringInput S) : SJl Bool := do
  let count ← s.ncodeunits
  return count == 0

def firstString (s : AbstractStringInput S)
    (getindex : S → Int → SJl C) : SJl C := do
  let index ← s.firstindex
  getindex s.value index

structure ScalarIndexCalls (C : Type) where
  checkbounds : SJl Unit
  isvalid : SJl Bool
  iterate : SJl (C × Int)
  stringIndexError : SJl C

def getindexInteger (calls : ScalarIndexCalls C) : SJl C := do
  let _ ← calls.checkbounds
  let valid ← calls.isvalid
  if valid then
    let pair ← calls.iterate
    return pair.1
  else calls.stringIndexError

structure IndexVectorInput (I : Type) where
  length : SJl Nat
  values : SJl (List I)

def collectIndices (getindex : I → SJl C) : List I → SJl (List C)
  | [] => .ok []
  | index :: rest => do
      let character ← getindex index
      let characters ← collectIndices getindex rest
      return character :: characters

def getindexVector (v : IndexVectorInput I)
    (getindex : I → SJl C) : SJl (List C) := do
  let _sizehint ← v.length
  let indices ← v.values
  collectIndices getindex indices

structure GetCalls (A : Type) where
  checkbounds : SJl Bool
  getindex : SJl A

def getDefault (calls : GetCalls A) (default : A) : SJl A := do
  let inbounds ← calls.checkbounds
  if inbounds then calls.getindex else return default

structure BoundsIndex (I : Type) where
  value : I
  oneLe : SJl Bool
  leCodeunits : Int → SJl Bool

def checkboundsIndex (s : AbstractStringInput S) (i : BoundsIndex I) : SJl Bool := do
  let lower ← i.oneLe
  if !lower then return false
  let count ← s.ncodeunits
  i.leCodeunits count

structure BoundsRange (I : Type) where
  isempty : SJl Bool
  minimum : SJl (BoundsIndex I)
  maximum : SJl (BoundsIndex I)

def checkboundsRange (s : AbstractStringInput S) (r : BoundsRange I) : SJl Bool := do
  let empty ← r.isempty
  if empty then return true
  let lo ← r.minimum
  let lower ← lo.oneLe
  if !lower then return false
  let hi ← r.maximum
  let count ← s.ncodeunits
  hi.leCodeunits count

def checkboundsArrayLoop (check : I → SJl Bool) : List I → SJl Bool
  | [] => .ok true
  | index :: rest => do
      let inbounds ← check index
      if inbounds then checkboundsArrayLoop check rest else return false

def checkboundsArray (values : SJl (List I))
    (check : I → SJl Bool) : SJl Bool := do
  let indices ← values
  checkboundsArrayLoop check indices

def checkboundsThrow (s : S) (indices : I) (check : SJl Bool) : SJl Unit := do
  let inbounds ← check
  if inbounds then return () else .error (.jl .boundsError)

/-! Construction, conversion, summary, and concatenation, lines 220-271. -/

structure ByteConversionInput (S : Type) where
  value : S
  string : SJl JStr

def vectorUInt8 (s : ByteConversionInput S)
    (unsafeWrap : JStr → SJl (List UInt8)) : SJl (List UInt8) := do
  let concrete ← s.string
  unsafeWrap concrete

def arrayUInt8 (s : ByteConversionInput S)
    (unsafeWrap : JStr → SJl (List UInt8)) : SJl (List UInt8) := do
  let concrete ← s.string
  unsafeWrap concrete

def vectorAbstractChar (s : S) (collect : S → SJl (List C)) : SJl (List C) :=
  collect s

structure SymbolStringInput (S Sym : Type) where
  value : S
  string : SJl JStr
  intern : JStr → SJl Sym

def symbolAbstractString (s : SymbolStringInput S Sym) : SJl Sym := do
  let concrete ← s.string
  s.intern concrete

structure SymbolArgsInput (Args Sym : Type) where
  values : Args
  render : Args → SJl JStr
  intern : JStr → SJl Sym

def symbolArgs (args : SymbolArgsInput Args Sym) : SJl Sym := do
  let rendered ← args.render args.values
  args.intern rendered

structure ConvertInput (S T : Type) where
  value : S
  construct : S → SJl T
  typeAssert : T → SJl T

def convertAbstractString (input : ConvertInput S T) : SJl T := do
  let converted ← input.construct input.value
  input.typeAssert converted

structure SummaryInput (S : Type) where
  value : S
  isempty : SJl Bool
  ncodeunits : SJl Int
  typeName : String
  print : List String → SJl Unit

def summary (input : SummaryInput S) : SJl Unit := do
  let empty ← input.isempty
  let summaryPrefix ← (if empty then .ok "empty" else do
      let count ← input.ncodeunits
      return toString count ++ "-codeunit")
  input.print [summaryPrefix, " ", input.typeName]

def anyAnnotated : List (SJl Bool) → SJl Bool
  | [] => .ok false
  | result :: rest => do
      let annotated ← result
      if annotated then return true else anyAnnotated rest

structure ConcatInput (A R : Type) where
  first : A
  rest : List A
  firstAnnotated : SJl Bool
  restAnnotated : List (SJl Bool)
  annotatedstring : A → List A → SJl R
  string : A → List A → SJl R

def concat (input : ConcatInput A R) : SJl R := do
  let firstAnnotated ← input.firstAnnotated
  let annotated ← if firstAnnotated then .ok true else anyAnnotated input.restAnnotated
  if annotated then input.annotatedstring input.first input.rest
  else input.string input.first input.rest

def oneString (convert : SJl T) : SJl T := convert

inductive StringTypeKind where
  | bottom
  | annotatedString
  | annotatedChar
  | other
  deriving DecidableEq

def isannotatedType : StringTypeKind → Bool
  | .bottom => false
  | .annotatedString => true
  | .annotatedChar => true
  | .other => false

structure ValueTypeInput (V : Type) where
  value : V
  typeOf : V → StringTypeKind

def isannotatedValue (input : ValueTypeInput V) : Bool :=
  isannotatedType (input.typeOf input.value)

/-! Generic string and Symbol comparison, lines 308-363. -/

structure AbstractStringSequence (A : Type) where
  identity : Nat
  characters : List A

def cmpCharacters [DecidableEq A] (lt : A → A → Bool) : List A → List A → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a = b then cmpCharacters lt as bs else if lt a b then -1 else 1

def cmpString [DecidableEq A] (lt : A → A → Bool)
    (a b : AbstractStringSequence A) : Int :=
  if a.identity == b.identity then 0 else cmpCharacters lt a.characters b.characters

def eqString [DecidableEq A] (lt : A → A → Bool)
    (a b : AbstractStringSequence A) : Bool := cmpString lt a b == 0

def islessString [DecidableEq A] (lt : A → A → Bool)
    (a b : AbstractStringSequence A) : Bool := decide (cmpString lt a b < 0)

def lexBytes : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a = b then lexBytes as bs else if a < b then -1 else 1

def cmpSymbol (a b : List UInt8) : Int := Int.sign (lexBytes a b)

def islessSymbol (a b : List UInt8) : Bool := decide (cmpSymbol a b < 0)

/-! Generic length and index arithmetic, lines 396-585. -/

structure IndexStringInput (S : Type) where
  value : S
  ncodeunits : SJl JInt64
  firstindex : SJl JInt64
  lastindex : SJl JInt64

structure MachineIntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64

def lengthString (s : IndexStringInput S)
    (lengthBetween : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let last ← s.ncodeunits
  lengthBetween s.value (ix 1) last

def indexRange (first last : JInt64) : List JInt64 :=
  if last.val < first.val then []
  else (List.range (last.val - first.val + 1).toNat).map
    (fun (offset : Nat) => first + ix (Int.ofNat offset))

def countValid (isvalid : JInt64 → SJl Bool) : List JInt64 → SJl JInt64
  | [] => .ok (ix 0)
  | index :: rest => do
      let valid ← isvalid index
      let count ← countValid isvalid rest
      return count + bInt valid

structure LengthBetweenInput (S : Type) where
  string : S
  first : JInt64
  last : JInt64
  firstCodeunits : SJl JInt64
  lastCodeunits : SJl JInt64
  isvalid : S → JInt64 → SJl Bool

def lengthBetween (input : LengthBetweenInput S) : SJl JInt64 := do
  let firstCount ← input.firstCodeunits
  if !(ix 0 < input.first && input.first ≤ firstCount + ix 1) then
    .error (.jl .boundsError)
  else
    let lastCount ← input.lastCodeunits
    if !(ix 0 ≤ input.last && input.last < lastCount + ix 1) then
      .error (.jl .boundsError)
    else countValid (input.isvalid input.string) (indexRange input.first input.last)

def lengthInteger (s : S) (first : MachineIntegerInput I) (last : MachineIntegerInput J)
    (lengthInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← first.toInt
  let j ← last.toInt
  lengthInt s i j

def thisindInteger (s : S) (index : MachineIntegerInput I)
    (thisindInt : S → JInt64 → SJl JInt64) : SJl JInt64 := do
  let converted ← index.toInt
  thisindInt s converted

def thisindRewind (isvalid : JInt64 → SJl Bool) : Nat → JInt64 → SJl JInt64
  | 0, index => .ok index
  | fuel + 1, index =>
      if ix 1 < index then do
        let valid ← isvalid index
        if valid then return index else thisindRewind isvalid fuel (index - ix 1)
      else return index

structure ThisindInput (S : Type) where
  string : S
  index : JInt64
  ncodeunits : SJl JInt64
  isvalid : S → JInt64 → SJl Bool

def thisindInt (input : ThisindInput S) : SJl JInt64 := do
  let count ← input.ncodeunits
  let after := count + ix 1
  if input.index == after then return input.index
  if !(ix 0 ≤ input.index && input.index ≤ after) then .error (.jl .boundsError)
  else thisindRewind (input.isvalid input.string) input.index.val.toNat input.index

def previndIntegerN (s : S) (index : MachineIntegerInput I) (count : MachineIntegerInput N)
    (previndInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  let n ← count.toInt
  previndInt s i n

def previndIntegerOne (s : S) (index : MachineIntegerInput I)
    (previndInt : S → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  previndInt s i

def previndOne (s : S) (index : JInt64)
    (previndIntN : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 :=
  previndIntN s index (ix 1)

def previndLoop (isvalid : JInt64 → SJl Bool) : Nat → JInt64 → JInt64 → SJl JInt64
  | 0, index, count => .ok (index - count)
  | fuel + 1, index, count =>
      if ix 0 < count && ix 1 < index then do
        let nextIndex := index - ix 1
        let valid ← isvalid nextIndex
        previndLoop isvalid fuel nextIndex (count - bInt valid)
      else return index - count

structure PrevindInput (S : Type) where
  string : S
  index : JInt64
  count : JInt64
  ncodeunits : SJl JInt64
  thisind : S → JInt64 → SJl JInt64
  isvalid : S → JInt64 → SJl Bool
  stringIndexError : SJl JInt64

def previndIntN (input : PrevindInput S) : SJl JInt64 :=
  if input.count < ix 0 then .error (.jl (.argumentError "n cannot be negative"))
  else do
    let codeunits ← input.ncodeunits
    let after := codeunits + ix 1
    if !(ix 0 < input.index && input.index ≤ after) then .error (.jl .boundsError)
    else if input.count == ix 0 then do
      let current ← input.thisind input.string input.index
      if current == input.index then return input.index else input.stringIndexError
    else previndLoop (input.isvalid input.string) input.index.val.toNat input.index input.count

def nextindIntegerN (s : S) (index : MachineIntegerInput I) (count : MachineIntegerInput N)
    (nextindInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  let n ← count.toInt
  nextindInt s i n

def nextindIntegerOne (s : S) (index : MachineIntegerInput I)
    (nextindInt : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 := do
  let i ← index.toInt
  nextindInt s i (ix 1)

def nextindOne (s : S) (index : JInt64)
    (nextindIntN : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 :=
  nextindIntN s index (ix 1)

def nextindLoop (isvalid : JInt64 → SJl Bool) (last : JInt64) :
    Nat → JInt64 → JInt64 → SJl JInt64
  | 0, index, count => .ok (index + count)
  | fuel + 1, index, count =>
      if ix 0 < count && index < last then do
        let nextIndex := index + ix 1
        let valid ← isvalid nextIndex
        nextindLoop isvalid last fuel nextIndex (count - bInt valid)
      else return index + count

structure NextindInput (S : Type) where
  string : S
  index : JInt64
  count : JInt64
  ncodeunits : SJl JInt64
  thisind : S → JInt64 → SJl JInt64
  isvalid : S → JInt64 → SJl Bool
  stringIndexError : SJl JInt64

def nextindIntN (input : NextindInput S) : SJl JInt64 :=
  if input.count < ix 0 then .error (.jl (.argumentError "n cannot be negative"))
  else do
    let last ← input.ncodeunits
    if !(ix 0 ≤ input.index && input.index ≤ last) then .error (.jl .boundsError)
    else
      if input.count == ix 0 then do
        let current ← input.thisind input.string input.index
        if current == input.index then return input.index else input.stringIndexError
      else
        nextindLoop (input.isvalid input.string) last
          (last.val - input.index.val).toNat input.index input.count

structure EachStringIndex (S : Type) where
  string : S

def keys (s : S) : EachStringIndex S := ⟨s⟩

def eachLength (index : EachStringIndex S) (length : S → SJl JInt64) : SJl JInt64 :=
  length index.string

def eachLast (index : EachStringIndex S) (lastindex : S → SJl JInt64) : SJl JInt64 :=
  lastindex index.string

structure EachIterateInput (S : Type) where
  index : EachStringIndex S
  state : Option JInt64
  firstindex : S → SJl JInt64
  ncodeunits : S → SJl JInt64
  nextind : S → JInt64 → SJl JInt64

def eachIterate (input : EachIterateInput S) : SJl (Option (JInt64 × JInt64)) := do
  let state ← match input.state with
    | some state => .ok state
    | none => input.firstindex input.index.string
  let last ← input.ncodeunits input.index.string
  if last < state then return none
  let next ← input.nextind input.index.string state
  return some (state, next)

/-! ASCII classification, lines 619-653. -/

def allAscii (isascii : C → SJl Bool) : List C → SJl Bool
  | [] => .ok true
  | character :: rest => do
      let ascii ← isascii character
      if ascii then allAscii isascii rest else return false

structure AsciiStringInput (C : Type) where
  characters : SJl (List C)
  isascii : C → SJl Bool

def isasciiString (input : AsciiStringInput C) : SJl Bool := do
  let characters ← input.characters
  allAscii input.isascii characters

def isasciiAbstractChar (toUInt32 : SJl UInt32) : SJl Bool := do
  let value ← toUInt32
  return value < 0x80

structure CodeUnitOps (CU V : Type) where
  vector : V
  zero : CU
  or : CU → CU → CU
  nonnegative : CU → Bool
  below80 : CU → Bool
  getindex : V → JInt64 → SJl CU

def isasciiRangeLoop (ops : CodeUnitOps CU V) (last : JInt64) :
    Nat → JInt64 → CU → SJl CU
  | 0, _, aggregate => .ok aggregate
  | fuel + 1, index, aggregate =>
      if last < index then .ok aggregate
      else do
        let value ← ops.getindex ops.vector index
        isasciiRangeLoop ops last fuel (index + ix 1) (ops.or aggregate value)

def isasciiRange (ops : CodeUnitOps CU V) (first last : JInt64) : SJl Bool := do
  let aggregate ← isasciiRangeLoop ops last
    (last.val - first.val + 1).toNat first ops.zero
  return ops.nonnegative aggregate && ops.below80 aggregate

def isasciiChunksLoop (range : JInt64 → JInt64 → SJl Bool)
    (chunkSize last : JInt64) : Nat → JInt64 → SJl Bool
  | 0, _ => range (last - chunkSize + ix 1) last
  | fuel + 1, index =>
      if index ≤ last - chunkSize then do
        let ascii ← range index (index + chunkSize - ix 1)
        if ascii then isasciiChunksLoop range chunkSize last fuel (index + chunkSize)
        else return false
      else range (last - chunkSize + ix 1) last

def isasciiChunks (range : JInt64 → JInt64 → SJl Bool)
    (chunkSize first last : JInt64) : SJl Bool :=
  isasciiChunksLoop range chunkSize last
    ((last.val - first.val + 1).toNat + 1) first

structure AsciiVectorInput where
  firstindex : SJl JInt64
  lastindex : SJl JInt64
  range : JInt64 → JInt64 → SJl Bool
  chunks : JInt64 → JInt64 → JInt64 → SJl Bool

def isasciiVector (input : AsciiVectorInput) : SJl Bool := do
  let first ← input.firstindex
  let last ← input.lastindex
  let length := last - first + ix 1
  let chunkSize := ix 1024
  let threshold := ix 1536
  if length < threshold then input.range first last
  else input.chunks chunkSize first last

/-! Map, filter, slice, repeat, and reverse iteration, lines 657-776. -/

structure MapInput (S C M B : Type) where
  string : S
  sizeof : SJl JInt64
  codeunitSize : SJl JInt64
  characters : SJl (List C)
  apply : C → SJl M
  isAbstractChar : M → Bool
  convertChar : M → SJl UInt32
  allocate : JInt64 → SJl B
  length : B → SJl JInt64
  resize : B → JInt64 → SJl B
  writeChar : B → UInt32 → JInt64 → SJl (B × JInt64)
  sizehint : B → JInt64 → SJl B
  makeString : B → SJl JStr

def mapLoop (input : MapInput S C M B) : List C → B → JInt64 → SJl (B × JInt64)
  | [], buffer, index => .ok (buffer, index)
  | character :: rest, buffer, index => do
      let mapped ← input.apply character
      if !input.isAbstractChar mapped then
        .error (.jl (.argumentError "map requires AbstractChar results"))
      else
        let length ← input.length buffer
        let buffer ← if length < index + ix 3 then input.resize buffer (length * ix 2)
          else .ok buffer
        let converted ← input.convertChar mapped
        let written ← input.writeChar buffer converted index
        mapLoop input rest written.1 (index + written.2)

def divStringInt (left right : JInt64) : SJl JInt64 :=
  (JInt.div left right).mapError SErr.jl

def mapString (input : MapInput S C M B) : SJl JStr := do
  let bytes ← input.sizeof
  let unitSize ← input.codeunitSize
  let capacity ← divStringInt bytes unitSize
  let capacity := if capacity < ix 4 then ix 4 else capacity
  let buffer ← input.allocate capacity
  let characters ← input.characters
  let result ← mapLoop input characters buffer (ix 1)
  let resized ← input.resize result.1 (result.2 - ix 1)
  let hinted ← input.sizehint resized (result.2 - ix 1)
  input.makeString hinted

structure FilterInput (S C B : Type) where
  string : S
  sizeof : SJl JInt64
  makeBuffer : JInt64 → SJl B
  characters : SJl (List C)
  predicate : C → SJl Bool
  write : B → C → SJl B
  takestring : B → SJl JStr

def filterLoop (input : FilterInput S C B) : List C → B → SJl B
  | [], buffer => .ok buffer
  | character :: rest, buffer => do
      let keep ← input.predicate character
      let buffer ← if keep then input.write buffer character else .ok buffer
      filterLoop input rest buffer

def filterString (input : FilterInput S C B) : SJl JStr := do
  let size ← input.sizeof
  let buffer ← input.makeBuffer size
  let characters ← input.characters
  let result ← filterLoop input characters buffer
  input.takestring result

structure FirstNInput (S I R : Type) where
  string : S
  count : I
  nextind : S → JInt64 → I → SJl JInt64
  lastindex : S → SJl JInt64
  slice : S → JInt64 → JInt64 → SJl R

def firstN (input : FirstNInput S I R) : SJl R := do
  let advanced ← input.nextind input.string (ix 0) input.count
  let last ← input.lastindex input.string
  let stop := if advanced < last then advanced else last
  input.slice input.string (ix 1) stop

structure LastNInput (S I R : Type) where
  string : S
  count : I
  ncodeunits : S → SJl JInt64
  prevind : S → JInt64 → I → SJl JInt64
  slice : S → JInt64 → SJl R

def lastN (input : LastNInput S I R) : SJl R := do
  let count ← input.ncodeunits input.string
  let first ← input.prevind input.string (count + ix 1) input.count
  input.slice input.string (if first < ix 1 then ix 1 else first)

def reverseind (ncodeunits : SJl JInt64) (index : MachineIntegerInput I)
    (thisind : JInt64 → SJl JInt64) : SJl JInt64 := do
  let count ← ncodeunits
  let converted ← index.toInt
  thisind (count - converted + ix 1)

def repeatString (string : SJl JStr) (count : I)
    (repeatFn : JStr → I → SJl JStr) : SJl JStr := do
  let concrete ← string
  repeatFn concrete count

def powerString (value : A) (count : I) (repeatFn : A → I → SJl R) : SJl R :=
  repeatFn value count

structure ReverseIterateInput (S A : Type) where
  string : S
  state : Option JInt64
  lastindex : S → SJl JInt64
  firstindex : S → SJl JInt64
  getindex : S → JInt64 → SJl A
  prevind : S → JInt64 → SJl JInt64

def reverseIterate (input : ReverseIterateInput S A) : SJl (Option (A × JInt64)) := do
  let state ← match input.state with
    | some state => .ok state
    | none => input.lastindex input.string
  let first ← input.firstindex input.string
  if state < first then return none
  let value ← input.getindex input.string state
  let previous ← input.prevind input.string state
  return some (value, previous)

/-! CodeUnits and `_split_rest`, lines 788-840. -/

structure CodeUnits (S T : Type) where
  string : S

def codeUnitsCtor (s : S) : CodeUnits S T := ⟨s⟩

def cuSizeof (s : CodeUnits S T) (ncodeunits : S → SJl JInt64)
    (sizeofType : SJl JInt64) : SJl JInt64 := do
  let count ← ncodeunits s.string
  let unitSize ← sizeofType
  return count * unitSize

def cuSize (s : CodeUnits S T) (ncodeunits : S → SJl JInt64) : SJl (JInt64 × Unit) := do
  let count ← ncodeunits s.string
  return (count, ())

def cuElsize (sizeofType : SJl JInt64) : SJl JInt64 := sizeofType

def cuGetindex (s : CodeUnits S T) (index : JInt64)
    (codeunit : S → JInt64 → SJl T) : SJl T := codeunit s.string index

def cuCheckbounds (s : CodeUnits S T) (index : I)
    (checkbounds : S → I → SJl Bool) : SJl Bool := checkbounds s.string index

def cuDataids (s : CodeUnits S T) (dataids : S → SJl R) : SJl R := dataids s.string

def cuWrite (io : IOType) (s : CodeUnits S T)
    (write : IOType → S → SJl R) : SJl R := write io s.string

inductive PointerTarget (T : Type) where
  | typed
  | int8

def cuCconvert (target : PointerTarget T) (s : CodeUnits S T)
    (cconvert : PointerTarget T → S → SJl P) : SJl P := cconvert target s.string

def cuSimilar (dims : Dims) (similarArray : Dims → SJl A) : SJl A := similarArray dims

def codeunits (s : S) : CodeUnits S T := codeUnitsCtor s

structure SplitRestInput (S R : Type) where
  string : S
  count : JInt64
  lastindex : S → SJl JInt64
  prevind : S → JInt64 → JInt64 → SJl JInt64
  length : S → SJl JInt64
  checkLength : JInt64 → JInt64 → SJl JInt64
  nextind : S → JInt64 → SJl JInt64
  substring : S → JInt64 → JInt64 → SJl R
  front : S → JInt64 → SJl R

def splitRest (input : SplitRestInput S R) : SJl (R × R) := do
  let last ← input.lastindex input.string
  let split ← match input.prevind input.string last input.count with
    | .ok index => .ok index
    | .error (.jl .boundsError) => do
        let length ← input.length input.string
        input.checkLength length input.count
    | .error error => .error error
  let suffixStart ← input.nextind input.string split
  let suffix ← input.substring input.string suffixStart last
  let frontResult ← input.front input.string split
  return (frontResult, suffix)

end JuliaLean.StringsCovA.BasicRebuilt
