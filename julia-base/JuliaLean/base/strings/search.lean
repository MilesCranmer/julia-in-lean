import JuliaLean.Core
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.string
import JuliaLean.base.strings.substring

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

structure CharOps (C E : Type) where
  toChar : C → Except E JChar
  ncodeunits : JChar → Index

structure ByteOps (A B E : Type) where
  firstindex : A → Index
  lastindex : A → Index
  length : A → Index
  getindex : A → Index → Except E B
  value : B → Int
  zero : B
  boundsError : A → Int → E

structure DenseOps (A B E : Type) extends ByteOps A B E where
  pointer : A → Pointer
  preserve : A → (Unit → Except E (Pointer × Pointer)) → Except E (Pointer × Pointer)
  memchrCall : Pointer → JInt .i32 → JInt .u64 → Except E Pointer
  memrchrCall : Pointer → JInt .i32 → JInt .u64 → Except E Pointer

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

/-- Compare the zip in iteration order, retaining both Stateful remainders. -/
def zipAll {A B E : Type} (equal : A → B → Except E Bool) :
    List A → List B → Except E (Bool × List A × List B)
  | [], ys => .ok (true, [], ys)
  | xs, [] => .ok (true, xs, [])
  | x :: xs, y :: ys => do
      if ← equal x y then zipAll equal xs ys else pure (false, xs, ys)

/-- Iterator and SubString callees used by the generic forward search. Their
laws specify peel, the suffix's character sequence, and equality. -/
structure GenericForwardOps (S T C Sub E : Type) where
  string : SearchStringOps S C E
  firstindex : S → Index
  peel : T → Except E (Option (C × List C))
  substring : S → Index → Except E Sub
  characters : Sub → Except E (List C)
  equal : C → C → Except E Bool
  findnext : {I : Type} → IntegerOps I E → C → S → I → Except E (Option Index)

/-- The reverse and pairs callees are separate, preserving their source order. -/
structure GenericReverseOps (S T R C Sub E : Type) where
  string : SearchStringOps S C E
  isempty : T → Bool
  reverse : T → R
  peel : R → Except E (C × List C)
  substring : S → Index → Index → Except E Sub
  reversePairs : Sub → Except E (List (Index × C))
  equal : C → C → Except E Bool
  findprev : {I : Type} → IntegerOps I E → C → S → I → Except E (Option Index)

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
Julia source: base/strings/search.jl:34-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function last_utf8_byte(c::Char)
    u = reinterpret(UInt32, c)
    shift = ((4 - ncodeunits(c)) * 8) & 31
    (u >> shift) % UInt8
end
```
-/
def lastUtf8Byte (ncodeunits : JChar → Index) (c : JChar) : UInt8 :=
  let u := c
  let shift := (int 4 - ncodeunits c) * int 8
  let shift := (BitVec.ofInt 64 shift.val &&& BitVec.ofNat 64 31).toNat
  (u >>> UInt32.ofNat shift).toUInt8

/--
Julia source: base/strings/search.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_standalone_byte(x::UInt8) = (x < 0x80) | (x > 0xf7)
```
-/
def isStandaloneByte (x : UInt8) : Bool := (x < 0x80) || (x > 0xf7)

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
  let byte := lastUtf8Byte ops.ncodeunits char
  pure ⟨s, char, byte⟩

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
  let byte := lastUtf8Byte ops.ncodeunits char
  pure ⟨s, char, byte⟩

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
  let (p, q) ← ops.preserve a fun _ => do
    let p := ops.pointer a
    let q ← ops.memchrCall (JInt.wrap .u64 (p.val + (i - fst).val))
      (JInt.wrap .i32 (Int.ofNat b.toNat)) (JInt.rem .u64 (ops.lastindex a - i + int 1))
    pure (p, q)
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
def memchrInt8 {A E : Type} (ops : DenseOps A (JInt .i8) E) (a : A)
    (b : JInt .i8) (i : Index) : Except E (Option Index) := do
  let fst := ops.firstindex a
  let (p, q) ← ops.preserve a fun _ => do
    let p := ops.pointer a
    let q ← ops.memchrCall (JInt.wrap .u64 (p.val + (i - fst).val))
      (JInt.wrap .i32 b.val) (JInt.rem .u64 (ops.lastindex a - i + int 1))
    pure (p, q)
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
  let (p, q) ← ops.preserve a fun _ => do
    let p := ops.pointer a
    let q ← ops.memrchrCall p (JInt.wrap .i32 (Int.ofNat b.toNat)) (JInt.rem .u64 (i - fst + int 1))
    pure (p, q)
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
def memrchrInt8 {A E : Type} (ops : DenseOps A (JInt .i8) E) (a : A)
    (b : JInt .i8) (i : Index) : Except E (Option Index) := do
  let fst := ops.firstindex a
  let (p, q) ← ops.preserve a fun _ => do
    let p := ops.pointer a
    let q ← ops.memrchrCall p (JInt.wrap .i32 b.val) (JInt.rem .u64 (i - fst + int 1))
    pure (p, q)
  pure (if q.val = 0 then none else some (int (q.val - p.val + fst.val)))

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
def findnextUInt8 {A I E : Type} (ops : DenseOps A (UInt8) E) (ix : IntegerOps I E)
    (pred : UInt8) (a : A) (start : I) : Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val < (ops.firstindex a).val then throw (ops.boundsError a i.val)
  if i.val > (ops.lastindex a).val then return none
  memchrUInt8 ops a pred i

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
def findprevUInt8 {A I E : Type} (ops : DenseOps A (UInt8) E) (ix : IntegerOps I E)
    (pred : UInt8) (a : A) (start : I) : Except E (Option Index) := do
  let i ← ix.toInt start
  if i.val > (ops.lastindex a).val then throw (ops.boundsError a i.val)
  if i.val < (ops.firstindex a).val then return none
  memrchrUInt8 ops a pred i

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

def indexOps {E : Type} : IntegerOps Index E where
  value i := i.val
  toInt i := .ok i

/-- Loop state follows the byte index returned by memchr, then advances it. -/
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
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (ncodeunitsChar : JChar → Index)
    (s : FwCharPosIter S) (i : Index := int 1) : Except E (Option (Index × Index)) := do
  let scu := ops.ncodeunits s.string
  if isStandaloneByte s.lastCharByte then
    if i.val > scu.val then return none
    let found ← findnextUInt8 bytes indexOps s.lastCharByte (codeunits s.string) i
    pure (found.map fun i => (i, i + int 1))
  else
    let ncu := ncodeunitsChar s.char
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
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (ncodeunitsChar : JChar → Index)
    (s : RvCharPosIter S) (start : Option Index := none) : Except E (Option (Index × Index)) := do
  let i := start.getD (ops.ncodeunits s.string)
  let ncu := ncodeunitsChar s.char
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
    tryNext (fun iter state => fwIterate ops bytes codeunits chars.ncodeunits iter state)
      ⟨s, c, lastUtf8Byte chars.ncodeunits c⟩ i

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
    tryNext (fun iter state => rvIterate ops bytes codeunits chars.ncodeunits iter (some state))
      ⟨s, c, lastUtf8Byte chars.ncodeunits c⟩ i

def collectFw {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (ncodeunitsChar : JChar → Index)
    (iter : FwCharPosIter S) : Nat → Index → Except E (List Index)
  | 0, _ => .ok []
  | fuel + 1, state => do
      match ← fwIterate ops bytes codeunits ncodeunitsChar iter state with
      | none => pure []
      | some (i, state) =>
          let rest ← collectFw ops bytes codeunits ncodeunitsChar iter fuel state
          pure (i :: rest)

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
def findallChar {S A C E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (chars : CharOps C E)
    (findallBytes : UInt8 → A → Except E (List Index)) (pred : C) (s : S) :
    Except E (List Index) := do
  let iter ← fwCharPosIter chars s pred
  if isStandaloneByte iter.lastCharByte then findallBytes iter.lastCharByte (codeunits s)
  else collectFw ops bytes codeunits chars.ncodeunits iter (ops.iterationBound s + 2) (int 1)

def findnextPredicateLoop {S C E : Type} (ops : SearchStringOps S C E)
    (testf : C → Except E Bool) (s : S) (e : Index) : Nat → Index → Except E (Option Index)
  | 0, _ => .ok none
  | fuel + 1, i => do
      if i.val ≤ e.val then
        if ← testf (← ops.getindex s i) then return some i
        findnextPredicateLoop ops testf s e fuel (← ops.nextind s i)
      else pure none

def findprevPredicateLoop {S C E : Type} (ops : SearchStringOps S C E)
    (testf : C → Except E Bool) (s : S) : Nat → Index → Except E (Option Index)
  | 0, _ => .ok none
  | fuel + 1, i => do
      if i.val ≥ 1 then
        if ← testf (← ops.getindex s i) then return some i
        findprevPredicateLoop ops testf s fuel (← ops.prevind s i)
      else pure none

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
    (ix : IntegerOps I E) (testf : C → Except E Bool) (s : S) (start : I) :
    Except E (Option Index) := do
  let i ← ix.toInt start
  let z := ops.ncodeunits s + int 1
  if !(1 ≤ i.val && i.val ≤ z.val) then throw (ops.boundsError s i.val)
  if i != z then
    if !(← ops.isvalid s i) then throw (ops.stringIndexError s i)
  let e ← ops.lastindex s
  findnextPredicateLoop ops testf s e (ops.iterationBound s + 2) i

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
    (ix : IntegerOps I E) (testf : C → Except E Bool) (s : S) (start : I) :
    Except E (Option Index) := do
  let i ← ix.toInt start
  let z := ops.ncodeunits s + int 1
  if !(0 ≤ i.val && i.val ≤ z.val) then throw (ops.boundsError s i.val)
  if i == z then return none
  if i.val != 0 then
    if !(← ops.isvalid s i) then throw (ops.stringIndexError s i)
  findprevPredicateLoop ops testf s (ops.iterationBound s + 2) i

def searchindexGenericLoop {S T C Sub I E : Type} (ops : GenericForwardOps S T C Sub E)
    (ix : IntegerOps I E) (s : S) (t1 : C) (trest : List C) (sentinel : Index) :
    Nat → I ⊕ Index → Except E Index
  | 0, _ => .ok sentinel
  | fuel + 1, start => do
      let found ← match start with
        | .inl i => ops.findnext ix t1 s i
        | .inr i => ops.findnext indexOps t1 s i
      match found with
      | none => pure sentinel
      | some i =>
          let ii ← ops.string.nextind s i
          let a := trest
          let sub ← ops.substring s ii
          let (matched, _, a) ← zipAll ops.equal (← ops.characters sub) a
          if a.isEmpty && matched then return i
          searchindexGenericLoop ops ix s t1 trest sentinel fuel (.inr ii)

def rsearchindexGenericLoop {S T R C Sub I E : Type} (ops : GenericReverseOps S T R C Sub E)
    (ix : IntegerOps I E) (s : S) (t1 : C) (trest : List C) :
    Nat → I ⊕ Index → Except E Index
  | 0, _ => .ok (int 0)
  | fuel + 1, start => do
      let found ← match start with
        | .inl i => ops.findprev ix t1 s i
        | .inr i => ops.findprev indexOps t1 s i
      match found with
      | none => pure (int 0)
      | some i =>
          let ii ← ops.string.prevind s i
          let a := trest
          let sub ← ops.substring s (int 1) ii
          let b ← ops.reversePairs sub
          let (matched, a, b) ← zipAll (fun c pair => ops.equal c pair.2) a b
          if matched && a.isEmpty then
            match b with
            | [] => pure (JuliaLean.base.strings.basic.firstindexString s)
            | (j, _) :: _ => ops.string.nextind s j
          else rsearchindexGenericLoop ops ix s t1 trest fuel (.inr ii)

/-- String dispatch for the generic search uses the actual predicate method above. -/
def genericForwardStringOps {S T C Sub E : Type} (ops : GenericForwardOps S T C Sub E) :
    GenericForwardOps S T C Sub E :=
  { ops with findnext := fun {_I} ix target s i =>
      findnextPredicate ops.string ix (fun c => ops.equal c target) s i }

def genericReverseStringOps {S T R C Sub E : Type} (ops : GenericReverseOps S T R C Sub E) :
    GenericReverseOps S T R C Sub E :=
  { ops with findprev := fun {_I} ix target s i =>
      findprevPredicate ops.string ix (fun c => ops.equal c target) s i }

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
-/
def searchindexGeneric {S T C Sub I E : Type} (ops : GenericForwardOps S T C Sub E)
    (ix : IntegerOps I E) (s : S) (t : T) (start : I) : Except E Index := do
  let sentinel := ops.firstindex s - int 1
  let x ← ops.peel t
  match x with
  | none =>
      if (ops.firstindex s).val ≤ ix.value start then
        let z ← ops.string.nextind s (← ops.string.lastindex s)
        if ix.value start ≤ z.val then ix.toInt start
        else throw (ops.string.boundsError s (ix.value start))
      else throw (ops.string.boundsError s (ix.value start))
  | some (t1, trest) =>
      searchindexGenericLoop ops ix s t1 trest sentinel
        (ops.string.iterationBound s + 2) (.inl start)

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
-/
def rsearchindexGeneric {S T R C Sub I E : Type} (ops : GenericReverseOps S T R C Sub E)
    (ix : IntegerOps I E) (s : S) (t : T) (start : I) : Except E Index := do
  if ops.isempty t then
    if 1 ≤ ix.value start then
      let z ← ops.string.nextind s (← ops.string.lastindex s)
      if ix.value start ≤ z.val then ix.toInt start
      else throw (ops.string.boundsError s (ix.value start))
    else throw (ops.string.boundsError s (ix.value start))
  else
    let (t1, trest) ← ops.peel (ops.reverse t)
    rsearchindexGenericLoop ops ix s t1 trest (ops.string.iterationBound s + 2)
      (.inl start)

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

def forwardCompare {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (i n : Index) : Nat → Index → Except E Index
  | 0, j => .ok j
  | fuel + 1, j => do
      if j.val < (n - int 1).val then
        let left ← vectorNth sops s (i + j + int 1)
        let right ← vectorNth tops t (j + int 1)
        if sops.value left != tops.value right then return j
        forwardCompare sops tops s t i n fuel (j + int 1)
      else pure j

def reverseCompare {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (i n : Index) : Nat → Index → Except E Index
  | 0, j => .ok j
  | fuel + 1, j => do
      if j.val < n.val then
        let left ← vectorNth sops s (i + j)
        let right ← vectorNth tops t (j + int 1)
        if sops.value left != tops.value right then return j
        reverseCompare sops tops s t i n fuel (j + int 1)
      else pure j

def searchBytesLoop {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (n w : Index) (mask : UInt64) (skip : Index) (tlast : C)
    (sentinel : Index) : Nat → Index → Except E Index
  | 0, _ => .ok sentinel
  | fuel + 1, i => do
      if i.val > w.val then return sentinel
      let mut i := i
      if sops.value (← vectorNth sops s (i + n)) == tops.value tlast then
        let j ← forwardCompare sops tops s t i n (n.val.toNat + 1) (int 0)
        if j == n - int 1 then return i + sops.firstindex s
        if i.val < w.val then
          let bit ← byteBloom sops.value (← vectorNth sops s (i + n + int 1))
          if mask &&& bit == 0 then i := i + n else i := i + skip
        else i := i + skip
      else if i.val < w.val then
        let bit ← byteBloom sops.value (← vectorNth sops s (i + n + int 1))
        if mask &&& bit == 0 then i := i + n
      i := i + int 1
      searchBytesLoop sops tops s t n w mask skip tlast sentinel fuel i

def rsearchBytesLoop {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (s : A) (t : T) (n : Index) (mask : UInt64) (skip : Index) (tfirst : C)
    (sentinel : Index) : Nat → Index → Except E Index
  | 0, _ => .ok sentinel
  | fuel + 1, i => do
      if i.val ≤ 0 then return sentinel
      let mut i := i
      if sops.value (← vectorNth sops s i) == tops.value tfirst then
        let j ← reverseCompare sops tops s t i n (n.val.toNat + 1) (int 1)
        if j == n then return i + sentinel
        if i.val > 1 then
          let bit ← byteBloom sops.value (← vectorNth sops s (i - int 1))
          if mask &&& bit == 0 then i := i - n else i := i - skip
        else i := i - skip
      else if i.val > 1 then
        let bit ← byteBloom sops.value (← vectorNth sops s (i - int 1))
        if mask &&& bit == 0 then i := i - n
      i := i - int 1
      rsearchBytesLoop sops tops s t n mask skip tfirst sentinel fuel i

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
    (s : A) (t : T) (start : I) : Except E Index := do
  let sentinel := sops.firstindex s - int 1
  let n := tops.length t
  let m := sops.length s
  let i := (← ix.toInt start) - sentinel
  if i.val < 1 || i.val > (m + int 1).val then
    throw (sops.boundsError s (ix.value start))
  if n.val == 0 then
    return if 1 ≤ i.val && i.val ≤ (m + int 1).val then imax (int 1) i else sentinel
  else if m.val == 0 then return sentinel
  else if n.val == 1 then
    return (← findnext (← vectorNth tops t (int 1)) s i).getD sentinel
  let w := m - n
  if w.val < 0 || (i - int 1).val > w.val then return sentinel
  let tlast ← vectorNth tops t n
  let (bloomMask, skip) ← forwardMask tops t n tlast
  let i := i - int 1
  searchBytesLoop sops tops s t n w bloomMask skip tlast sentinel (m.val.toNat + 2) i

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
    (s : A) (t : T) (start : I) : Except E Index := do
  let sentinel := sops.firstindex s - int 1
  let n := tops.length t
  let m := sops.length s
  let k := (← ix.toInt start) - sentinel
  if k.val < 0 then throw (sops.boundsError s (ix.value start))
  if n.val == 0 then
    return if 0 ≤ k.val && k.val ≤ m.val then imax k (int 1) else sentinel
  else if m.val == 0 then return sentinel
  else if n.val == 1 then
    return (← findprev (← vectorNth tops t (int 1)) s k).getD sentinel
  let w := m - n
  if w.val < 0 || k.val ≤ 0 then return sentinel
  let tfirst ← vectorNth tops t (int 1)
  let (bloomMask, skip) ← reverseMask tops t n tfirst
  let i := imin (k - n + int 1) (w + int 1)
  rsearchBytesLoop sops tops s t n bloomMask skip tfirst sentinel (i.val.toNat + 2) i

def rawCharOps {E : Type} (ncodeunits : JChar → Index) : CharOps JChar E where
  toChar c := .ok c
  ncodeunits := ncodeunits

def denseFindnextUInt8 {A E : Type} (ops : DenseOps A UInt8 E)
    (b : UInt8) (a : A) (i : Index) : Except E (Option Index) :=
  findnextUInt8 ops indexOps b a i

def denseFindprevUInt8 {A E : Type} (ops : DenseOps A UInt8 E)
    (b : UInt8) (a : A) (i : Index) : Except E (Option Index) :=
  findprevUInt8 ops indexOps b a i

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
def searchindexDense {S T A D I E : Type} (sops : SearchStringOps S JChar E)
    (tops : SearchStringOps T JChar E) (sbytes : DenseOps A UInt8 E)
    (tbytes : ByteOps D UInt8 E) (codeunitsS : S → A) (codeunitsT : T → D)
    (ncodeunitsChar : JChar → Index) (ix : IntegerOps I E) (s : S) (t : T) (i : I) :
    Except E Index := do
  if (← tops.lastindex t).val == 1 then
    let c ← tops.getindex t (int 1)
    return (← findnextChar sops sbytes codeunitsS (rawCharOps ncodeunitsChar) ix c s i).getD (int 0)
  searchindexBytes sbytes.toByteOps tbytes (denseFindnextUInt8 sbytes) ix (codeunitsS s) (codeunitsT t) i

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
def rsearchindexDense {S T A D I E : Type} (sops : SearchStringOps S JChar E)
    (tops : SearchStringOps T JChar E) (sbytes : DenseOps A UInt8 E)
    (tbytes : ByteOps D UInt8 E) (codeunitsS : S → A) (codeunitsT : T → D)
    (sizeof : S → Index) (ncodeunitsChar : JChar → Index) (ix : IntegerOps I E)
    (s : S) (t : T) (start : I) : Except E (DenseSearchIndex I) := do
  if (← tops.lastindex t).val == 1 then
    let c ← tops.getindex t (int 1)
    return .juliaInt ((← findprevChar sops sbytes codeunitsS
      (rawCharOps ncodeunitsChar) ix c s start).getD (int 0))
  else if (← tops.lastindex t).val != 0 then
    let i ← ix.toInt start
    let j ← if ix.value start ≤ (sops.ncodeunits s).val then do
      pure ((← sops.nextind s i) - int 1)
    else pure i
    return .juliaInt (← rsearchindexBytes sbytes.toByteOps tbytes
      (denseFindprevUInt8 sbytes) indexOps (codeunitsS s) (codeunitsT t) j)
  else if ix.value start > (sizeof s).val then return .juliaInt (int 0)
  else if ix.value start == 0 then return .juliaInt (int 1)
  else return .sourceInteger start

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
def searchRange {S T I E : Type} (searchindex : S → T → I → Except E Index)
    (isempty : T → Bool) (firstindexS : S → Except E Index)
    (firstindexT lastindexT : T → Except E Index)
    (s : S) (t : T) (i : I) : Except E (Option MatchRange) := do
  let idx ← searchindex s t i
  if isempty t then return some ⟨idx, idx - int 1⟩
  else if idx.val ≥ (← firstindexS s).val then
    let last ← lastindexT t
    let first ← firstindexT t
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
def rsearchRange {S T I E : Type} (rsearchindex : S → T → I → Except E Index)
    (isempty : T → Bool) (firstindexS : S → Except E Index)
    (firstindexT lastindexT : T → Except E Index)
    (s : S) (t : T) (i : I) : Except E (Option MatchRange) := do
  let idx ← rsearchindex s t i
  if isempty t then return some ⟨idx, idx - int 1⟩
  else if idx.val > ((← firstindexS s) - int 1).val then
    let last ← lastindexT t
    let first ← firstindexT t
    return some ⟨idx, idx + last - first⟩
  else return none

/--
Julia source: base/strings/search.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(t::AbstractString, s::AbstractString, start::Integer) = _search(s, t, Int(start))
```
-/
def findnextString {S T I E : Type} (ix : IntegerOps I E)
    (search : S → T → Index → Except E (Option MatchRange))
    (t : T) (s : S) (start : I) : Except E (Option MatchRange) := do
  search s t (← ix.toInt start)

/--
Julia source: base/strings/search.jl:821-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(t::AbstractString, s::AbstractString, i::Integer) = _rsearch(s, t, Int(i))
```
-/
def findprevString {S T I E : Type} (ix : IntegerOps I E)
    (rsearch : S → T → Index → Except E (Option MatchRange))
    (t : T) (s : S) (start : I) : Except E (Option MatchRange) := do
  rsearch s t (← ix.toInt start)

/--
Julia source: base/strings/search.jl:526-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(ch::AbstractChar, string::AbstractString, start::Integer) =
    findnext(==(ch), string, start)
```
-/
def findnextCharWrapper {S C D I E : Type} (equal : D → C → Except E Bool)
    (findnext : (D → Except E Bool) → S → I → Except E (Option Index))
    (ch : C) (s : S) (start : I) : Except E (Option Index) :=
  findnext (fun c => equal c ch) s start

/--
Julia source: base/strings/search.jl:840-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(ch::AbstractChar, string::AbstractString, start::Integer) =
    findprev(==(ch), string, start)
```
-/
def findprevCharWrapper {S C D I E : Type} (equal : D → C → Except E Bool)
    (findprev : (D → Except E Bool) → S → I → Except E (Option Index))
    (ch : C) (s : S) (start : I) : Except E (Option Index) :=
  findprev (fun c => equal c ch) s start

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
    (search : A → T → I → Except E (Option MatchRange))
    (pattern : T) (a : A) (start : I) : Except E (Option MatchRange) :=
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
    (rsearch : A → T → I → Except E (Option MatchRange))
    (pattern : T) (a : A) (start : I) : Except E (Option MatchRange) :=
  rsearch a pattern start

/--
Julia source: base/strings/search.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirst(pattern::AbstractString, string::AbstractString) =
    findnext(pattern, string, firstindex(string))
```
-/
def findfirstString {S T E : Type} (firstindex : S → Index)
    (findnext : T → S → Index → Except E (Option MatchRange))
    (pattern : T) (s : S) : Except E (Option MatchRange) :=
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
    (search : A → T → Index → Except E (Option MatchRange))
    (pattern : T) (a : A) : Except E (Option MatchRange) :=
  search a pattern (firstindex a)

/--
Julia source: base/strings/search.jl:568-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(pattern::AbstractString, string::AbstractString) =
    findprev(pattern, string, lastindex(string))
```
-/
def findlastString {S T E : Type} (lastindex : S → Except E Index)
    (findprev : T → S → Index → Except E (Option MatchRange))
    (pattern : T) (s : S) : Except E (Option MatchRange) := do
  findprev pattern s (← lastindex s)

/--
Julia source: base/strings/search.jl:584-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlast(pattern::AbstractVector{<:Union{Int8,UInt8}},
         A::AbstractVector{<:Union{Int8,UInt8}}) =
    findprev(pattern, A, lastindex(A))
```
-/
def findlastVector {A T E : Type} (lastindex : A → Index)
    (findprev : T → A → Index → Except E (Option MatchRange))
    (pattern : T) (a : A) : Except E (Option MatchRange) :=
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
    (findnext : T → S → Index → Except E (Option MatchRange))
    (nextind : S → Index → Except E Index) (s : S) (t : T) (overlap : Bool) (e : Index) :
    Nat → Index → List MatchRange → Except E (List MatchRange)
  | 0, _, found => .ok found
  | fuel + 1, i, found => do
      match ← findnext t s i with
      | none => pure found
      | some r =>
          let found := found ++ [r]
          let j := if overlap || rangeEmpty r then r.first else r.last
          if j.val > e.val then return found
          let i ← nextind s j
          findallLoop findnext nextind s t overlap e fuel i found

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
def findallRanges {S T E : Type}
    (findnext : T → S → Index → Except E (Option MatchRange))
    (firstindex : S → Index) (lastindex : S → Except E Index)
    (nextind : S → Index → Except E Index) (iterationBound : S → Nat)
    (t : T) (s : S) (overlap : Bool := false) : Except E (List MatchRange) := do
  let found := []
  let i := firstindex s
  let e ← lastindex s
  findallLoop findnext nextind s t overlap e (iterationBound s + 2) i found

/--
Julia source: base/strings/search.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(c::AbstractChar, s::AbstractString) = (findfirst(isequal(c),s)!==nothing)
```
-/
def inChar {S C D E : Type} (isequal : D → C → Except E Bool)
    (findfirst : (D → Except E Bool) → S → Except E (Option Index))
    (c : C) (s : S) : Except E Bool := do
  pure (← findfirst (fun d => isequal d c) s).isSome

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
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (ncodeunitsChar : JChar → Index)
    (c : JChar) (s : S) : Except E Bool := do
  let pos ← findnextChar ops bytes codeunits (rawCharOps ncodeunitsChar) indexOps c s (int 1)
  pure pos.isSome

/--
Julia source: base/strings/search.jl:886-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
occursin(needle::Union{AbstractString,AbstractChar}, haystack::AbstractString) =
    _searchindex(haystack, needle, firstindex(haystack)) != 0
```
-/
def occursin {S T E : Type} (firstindex : S → Index)
    (searchindex : S → T → Index → Except E Index) (needle : T) (haystack : S) : Except E Bool := do
  pure ((← searchindex haystack needle (firstindex haystack)).val != 0)

/--
Julia source: base/strings/search.jl:911-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
occursin(haystack) = Base.Fix2(occursin, haystack)
```
-/
def occursinFix {S T E : Type} (firstindex : S → Index)
    (searchindex : S → T → Index → Except E Index) (haystack : S) : Fix2 T S (Except E Bool) :=
  ⟨occursin firstindex searchindex, haystack⟩

/--
Julia source: base/strings/search.jl:913-913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(::AbstractString, ::AbstractString) = error("use occursin(needle, haystack) for string containment")
```
-/
def inString {S T E : Type} (error : String → E) (_needle : T) (_haystack : S) : Except E Bool :=
  .error (error "use occursin(needle, haystack) for string containment")

/--
Julia source: base/strings/search.jl:915-915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(a::UInt8, b::DenseUInt8) = !isnothing(findfirst(==(a), b))
```
-/
def inUInt8 {A E : Type}
    (findfirst : UInt8 → A → Except E (Option Index)) (a : UInt8) (b : A) : Except E Bool := do
  pure (← findfirst a b).isSome

/--
Julia source: base/strings/search.jl:916-916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(a::Int8, b::DenseInt8) = !isnothing(findfirst(==(a), b))
```
-/
def inInt8 {A E : Type}
    (findfirst : JInt .i8 → A → Except E (Option Index)) (a : JInt .i8) (b : A) : Except E Bool := do
  pure (← findfirst a b).isSome

/-! ## Typed dispatch instantiations

These helpers select the source-mirrored methods above. They introduce no
alternative search algorithm.
-/

structure DenseStringSearch (S T A D E : Type) where
  source : SearchStringOps S JChar E
  pattern : SearchStringOps T JChar E
  sourceBytes : DenseOps A UInt8 E
  patternBytes : ByteOps D UInt8 E
  codeunitsSource : S → A
  codeunitsPattern : T → D
  ncodeunitsChar : JChar → Index
  sizeof : S → Index

def denseIndex {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (s : S) (t : T) (i : I) : Except E Index :=
  searchindexDense cfg.source cfg.pattern cfg.sourceBytes cfg.patternBytes
    cfg.codeunitsSource cfg.codeunitsPattern cfg.ncodeunitsChar ix s t i

def denseRIndex {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (s : S) (t : T) (i : I) : Except E Index := do
  match ← rsearchindexDense cfg.source cfg.pattern cfg.sourceBytes cfg.patternBytes
      cfg.codeunitsSource cfg.codeunitsPattern cfg.sizeof cfg.ncodeunitsChar ix s t i with
  | .sourceInteger value => pure (int (ix.value value))
  | .juliaInt value => pure value

def denseRange {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (s : S) (t : T) (i : Index) : Except E (Option MatchRange) :=
  searchRange (denseIndex cfg indexOps) (fun t => (cfg.pattern.ncodeunits t).val == 0)
    (fun _ => .ok (int 1)) (fun _ => .ok (int 1)) cfg.pattern.lastindex s t i

def denseRRange {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (s : S) (t : T) (i : Index) : Except E (Option MatchRange) :=
  rsearchRange (denseRIndex cfg indexOps) (fun t => (cfg.pattern.ncodeunits t).val == 0)
    (fun _ => .ok (int 1)) (fun _ => .ok (int 1)) cfg.pattern.lastindex s t i

def denseNext {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (t : T) (s : S) (i : I) : Except E (Option MatchRange) :=
  findnextString ix (denseRange cfg) t s i

def densePrev {S T A D I E : Type} (cfg : DenseStringSearch S T A D E)
    (ix : IntegerOps I E) (t : T) (s : S) (i : I) : Except E (Option MatchRange) :=
  findprevString ix (denseRRange cfg) t s i

def denseFirst {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (t : T) (s : S) : Except E (Option MatchRange) :=
  findfirstString JuliaLean.base.strings.basic.firstindexString (denseNext cfg indexOps) t s

def denseLast {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (t : T) (s : S) : Except E (Option MatchRange) :=
  findlastString cfg.source.lastindex (densePrev cfg indexOps) t s

def denseAll {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (t : T) (s : S) (overlap : Bool) : Except E (List MatchRange) :=
  findallRanges (denseNext cfg indexOps) JuliaLean.base.strings.basic.firstindexString
    cfg.source.lastindex cfg.source.nextind cfg.source.iterationBound t s overlap

def denseOccursin {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (t : T) (s : S) : Except E Bool :=
  occursin JuliaLean.base.strings.basic.firstindexString (denseIndex cfg indexOps) t s

def denseOccursinFix {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (s : S) : Fix2 T S (Except E Bool) :=
  occursinFix JuliaLean.base.strings.basic.firstindexString (denseIndex cfg indexOps) s

structure BytePatternSearch (A T B C E : Type) where
  source : ByteOps A B E
  pattern : ByteOps T C E
  findnext : C → A → Index → Except E (Option Index)
  findprev : C → A → Index → Except E (Option Index)

def vectorRange {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (a : A) (t : T) (i : I) : Except E (Option MatchRange) :=
  searchRange (searchindexBytes cfg.source cfg.pattern cfg.findnext ix)
    (fun t => (cfg.pattern.length t).val == 0)
    (fun a => .ok (cfg.source.firstindex a)) (fun t => .ok (cfg.pattern.firstindex t))
    (fun t => .ok (cfg.pattern.lastindex t)) a t i

def vectorRRange {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (a : A) (t : T) (i : I) : Except E (Option MatchRange) :=
  rsearchRange (rsearchindexBytes cfg.source cfg.pattern cfg.findprev ix)
    (fun t => (cfg.pattern.length t).val == 0)
    (fun a => .ok (cfg.source.firstindex a)) (fun t => .ok (cfg.pattern.firstindex t))
    (fun t => .ok (cfg.pattern.lastindex t)) a t i

def vectorNext {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (t : T) (a : A) (i : I) : Except E (Option MatchRange) :=
  findnextVector (vectorRange cfg ix) t a i

def vectorPrev {A T B C I E : Type} (cfg : BytePatternSearch A T B C E)
    (ix : IntegerOps I E) (t : T) (a : A) (i : I) : Except E (Option MatchRange) :=
  findprevVector (vectorRRange cfg ix) t a i

def vectorFirst {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (t : T) (a : A) : Except E (Option MatchRange) :=
  findfirstVector cfg.source.firstindex (vectorRange cfg indexOps) t a

def vectorLast {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (t : T) (a : A) : Except E (Option MatchRange) :=
  findlastVector cfg.source.lastindex (vectorPrev cfg indexOps) t a

def charOccurrence {S A E : Type} (ops : SearchStringOps S JChar E)
    (bytes : DenseOps A UInt8 E) (codeunits : S → A) (ncodeunitsChar : JChar → Index)
    (c : JChar) (s : S) : Except E Bool :=
  occursin JuliaLean.base.strings.basic.firstindexString
    (fun s c i => searchindexChar
      (findnextChar ops bytes codeunits (rawCharOps ncodeunitsChar) indexOps) s c i) c s

end JuliaLean.base.strings.search
