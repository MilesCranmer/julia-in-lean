import JuliaLean.Core
import JuliaLean.base.strings.basic

/-!
# Model of `base/strings/substring.jl`

Julia `Int` offsets use `JInt64`; operations supplied by generic string implementations,
allocators, pointer intrinsics, and later-loaded methods remain typed parameters.
-/

namespace JuliaLean.base.strings.substring

open _root_.JuliaLean

abbrev Index := _root_.JuliaLean.base.strings.basic.Index

def int (n : Int) : Index := _root_.JuliaLean.base.strings.basic.int n

def zero : Index := int 0

def one : Index := int 1

structure SubString (S : Type) where
  string : S
  offset : Index
  ncodeunits : Index
  deriving DecidableEq

structure IndexRange where
  first : Index
  last : Index

def rangeLength (r : IndexRange) : Index := r.last - r.first + one

structure SubStringOps (S C CT E : Type) where
  ncodeunits : S → Index
  codeunitType : S → CT
  length : S → Index → Index → Except E Index
  checkboundsRange : S → Index → Index → Except E Unit
  checkboundsViewRange : SubString S → Index → Index → Except E Unit
  isvalid : S → Index → Except E Bool
  stringIndexError : S → Index → E
  boundsError : S → Index → Index → E
  viewBoundsError : SubString S → Index → Index → E
  nextind : S → Index → Except E Index
  firstindex : SubString S → Index
  thisindParent : S → Index → Except E Index
  isasciiCodeunits : JuliaLean.base.strings.basic.CodeUnits UInt8 (SubString S) → Except E Bool
  sizeof : S → Index

structure RangeOps (R I : Type) where
  first : R → I
  last : R → I

/-! This generic-function declaration has no executable Julia method body. -/
/-!
Julia source: base/strings/substring.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function raw_substring end
```
-/
-- UNTRANSLATED: `raw_substring` is only declared here; its concrete method bodies follow.

/-!
Julia source: base/strings/substring.jl:71-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct SubString{T<:AbstractString} <: AbstractString
    string::T
    offset::Int
    ncodeunits::Int

    function SubString{T}(s::T, i::Int, j::Int) where T<:AbstractString
        i ≤ j || return new(s, 0, 0)
        @boundscheck begin
            checkbounds(s, i:j)
            @inbounds isvalid(s, i) || string_index_err(s, i)
            @inbounds isvalid(s, j) || string_index_err(s, j)
        end
        return new(s, i-1, nextind(s,j)-i)
    end

    global function raw_substring(s::T, first_index::Int, n_codeunits::Int) where {T <: AbstractString}
        @boundscheck if n_codeunits < 0 || first_index < 1 || (n_codeunits > ncodeunits(s) - first_index + 1)
            throw(BoundsError(s, first_index:(first_index+n_codeunits-1)))
        end
        new{T}(s, first_index - 1, n_codeunits)
    end

    global function raw_substring(s::SubString{T}, first_index::Int, n_codeunits::Int) where {T <: AbstractString}
        @boundscheck if n_codeunits < 0 || first_index < 1 || (n_codeunits > ncodeunits(s) - first_index + 1)
            throw(BoundsError(s, first_index:(first_index+n_codeunits-1)))
        end
        new{T}(s.string, first_index + s.offset - 1, n_codeunits)
    end

    # Unlike the un-parameterized SubString constructor, this function must allow creating
    # e.g. a SubString{SubString{String}}, as this type is what the user may have explicitly
    # requested.
    function SubString{T}(s::T) where {T <: AbstractString}
        new{T}(s, 0, ncodeunits(s))
    end
```
-/

/-!
Julia source: base/strings/substring.jl:76-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function SubString{T}(s::T, i::Int, j::Int) where T<:AbstractString
        i ≤ j || return new(s, 0, 0)
        @boundscheck begin
            checkbounds(s, i:j)
            @inbounds isvalid(s, i) || string_index_err(s, i)
            @inbounds isvalid(s, j) || string_index_err(s, j)
        end
        return new(s, i-1, nextind(s,j)-i)
    end
```
-/
def typedSubString {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : S) (i j : Index) : Except E (SubString S) := do
  if j.val < i.val then
    pure ⟨s, zero, zero⟩
  else
    ops.checkboundsRange s i j
    if !(← ops.isvalid s i) then throw (ops.stringIndexError s i)
    if !(← ops.isvalid s j) then throw (ops.stringIndexError s j)
    pure ⟨s, i - one, (← ops.nextind s j) - i⟩

/-!
Julia source: base/strings/substring.jl:86-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global function raw_substring(s::T, first_index::Int, n_codeunits::Int) where {T <: AbstractString}
        @boundscheck if n_codeunits < 0 || first_index < 1 || (n_codeunits > ncodeunits(s) - first_index + 1)
            throw(BoundsError(s, first_index:(first_index+n_codeunits-1)))
        end
        new{T}(s, first_index - 1, n_codeunits)
    end
```
-/
def rawSubstring {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : S) (firstIndex count : Index) : Except E (SubString S) := do
  if count.val < 0 || firstIndex.val < 1 ||
      count.val > (ops.ncodeunits s - firstIndex + one).val then
    throw (ops.boundsError s firstIndex (firstIndex + count - one))
  pure ⟨s, firstIndex - one, count⟩

/-!
Julia source: base/strings/substring.jl:93-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global function raw_substring(s::SubString{T}, first_index::Int, n_codeunits::Int) where {T <: AbstractString}
        @boundscheck if n_codeunits < 0 || first_index < 1 || (n_codeunits > ncodeunits(s) - first_index + 1)
            throw(BoundsError(s, first_index:(first_index+n_codeunits-1)))
        end
        new{T}(s.string, first_index + s.offset - 1, n_codeunits)
    end
```
-/
def rawSubstringView {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : SubString S) (firstIndex count : Index) : Except E (SubString S) := do
  if count.val < 0 || firstIndex.val < 1 ||
      count.val > (s.ncodeunits - firstIndex + one).val then
    throw (ops.viewBoundsError s firstIndex (firstIndex + count - one))
  pure ⟨s.string, firstIndex + s.offset - one, count⟩

/-!
Julia source: base/strings/substring.jl:103-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function SubString{T}(s::T) where {T <: AbstractString}
        new{T}(s, 0, ncodeunits(s))
    end
```
-/
def typedWholeSubString {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : S) : SubString S := ⟨s, zero, ops.ncodeunits s⟩

/-!
Julia source: base/strings/substring.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds SubString(s::T, i::Int, j::Int) where {T<:AbstractString} = SubString{T}(s, i, j)
```
-/
def subStringInt {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : S) (i j : Index) : Except E (SubString S) := do
  let result ← typedSubString ops s i j
  pure result

/-!
Julia source: base/strings/substring.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds SubString(s::AbstractString, i::Integer, j::Integer=lastindex(s)) = SubString(s, Int(i)::Int, Int(j)::Int)
```
-/
def subStringInteger {S C CT E I : Type} (ops : SubStringOps S C CT E)
    (toInt : I → Except E Index) (s : S) (i j : I) : Except E (SubString S) := do
  let i ← toInt i
  let j ← toInt j
  subStringInt ops s i j

/-!
Julia source: base/strings/substring.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds SubString(s::AbstractString, i::Integer, j::Integer=lastindex(s)) = SubString(s, Int(i)::Int, Int(j)::Int)
```
-/
def subStringIntegerDefault {S C CT E I : Type} (ops : SubStringOps S C CT E)
    (toInt : I → Except E Index) (lastindex : S → Except E Index) (s : S) (i : I) : Except E (SubString S) := do
  let j ← lastindex s
  subStringInt ops s (← toInt i) j

/-!
Julia source: base/strings/substring.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds SubString(s::AbstractString, r::AbstractUnitRange{<:Integer}) = SubString(s, first(r), last(r))
```
-/
def subStringRange {S C CT E R I : Type} (ops : SubStringOps S C CT E)
    (rangeOps : RangeOps R I) (toInt : I → Except E Index) (s : S) (r : R) :
    Except E (SubString S) := do
  let i := rangeOps.first r
  let j := rangeOps.last r
  subStringInteger ops toInt s i j

/-!
Julia source: base/strings/substring.jl:112-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function SubString(s::SubString, i::Int, j::Int)
    @boundscheck i ≤ j && checkbounds(s, i:j)
    SubString(s.string, s.offset+i, s.offset+j)
end
```
-/
def subStringNested {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : SubString S) (i j : Index) : Except E (SubString S) := do
  if i.val ≤ j.val then ops.checkboundsViewRange s i j
  subStringInt ops s.string (s.offset + i) (s.offset + j)

/-!
Julia source: base/strings/substring.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SubString(s::AbstractString) = @inbounds raw_substring(s, 1, Int(ncodeunits(s))::Int)
```
-/
def subStringWhole {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : S) : Except E (SubString S) := rawSubstring ops s one (ops.ncodeunits s)

/-!
Julia source: base/strings/substring.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SubString(s::SubString) = s
```
-/
def subStringWholeView {S E : Type} (s : SubString S) : Except E (SubString S) := pure s

/-!
Julia source: base/strings/substring.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds view(s::AbstractString, r::AbstractUnitRange{<:Integer}) = SubString(s, r)
```
-/
def viewString {S C CT E R I : Type} (ops : SubStringOps S C CT E)
    (rangeOps : RangeOps R I) (toInt : I → Except E Index) (s : S) (r : R) :
    Except E (SubString S) := do
  let result ← subStringRange ops rangeOps toInt s r
  pure result

/-!
Julia source: base/strings/substring.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds maybeview(s::AbstractString, r::AbstractUnitRange{<:Integer}) = view(s, r)
```
-/
def maybeviewRange {S C CT R I E : Type} (ops : SubStringOps S C CT E)
    (rangeOps : RangeOps R I) (toInt : I → Except E Index) (s : S) (r : R) :
    Except E (SubString S) := do
  let result ← viewString ops rangeOps toInt s r
  pure result

/-!
Julia source: base/strings/substring.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds maybeview(s::AbstractString, args...) = getindex(s, args...)
```
-/
def maybeviewArgs {S A V E : Type} (getindex : S → A → Except E V) (s : S) (args : A) : Except E V :=
  getindex s args

/-!
Julia source: base/strings/substring.jl:124-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{SubString{S}}, s::AbstractString) where {S<:AbstractString} =
    SubString(convert(S, s))::SubString{S}
```
-/
def convertSubString {A S R E : Type}
    (convert : A → Except E S) (construct : S → Except E R)
    (assertSubString : R → Except E (SubString S)) (s : A) : Except E (SubString S) := do
  let parent ← convert s
  let result ← construct parent
  assertSubString result

/-!
Julia source: base/strings/substring.jl:126-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, s::T) where {T<:SubString} = s
```
-/
def convertSubStringIdentity {S : Type} (s : SubString S) : SubString S := s

inductive RegexString (S : Type) where
  | string (value : S)
  | substring (value : SubString S)

/-!
Julia source: base/strings/substring.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Union{String, SubString{String}}}, s::String) = s
```
-/
def convertRegexString {S : Type} (s : S) : RegexString S := .string s

/-!
Julia source: base/strings/substring.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Union{String, SubString{String}}}, s::SubString{String}) = s
```
-/
def convertRegexSubString {S : Type} (s : SubString S) : RegexString S := .substring s

/-!
Julia source: base/strings/substring.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Union{String, SubString{String}}}, s::AbstractString) = convert(String, s)::String
```
-/
def convertRegexAbstract {A S E : Type} (convert : A → Except E S) (s : A) : Except E (RegexString S) := do
  pure (.string (← convert s))

structure CopyStringOps (S Out E : Type) where
  pointer : S → Index → Index
  /-- The first argument is a strong GC root retained throughout the unsafe copy. -/
  unsafeString : S → Index → Index → Except E Out

/-!
Julia source: base/strings/substring.jl:133-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function String(s::SubString{String})
    parent = s.string
    copy = GC.@preserve parent unsafe_string(pointer(parent, s.offset+1), s.ncodeunits)
    return copy
end
```
-/
def stringFromSubString {S Out E : Type} (ops : CopyStringOps S Out E)
    (s : SubString S) : Except E Out := do
  let parent := s.string
  let copy ← ops.unsafeString parent (ops.pointer parent (s.offset + one)) s.ncodeunits
  pure copy

/-!
Julia source: base/strings/substring.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(s::SubString) = s.ncodeunits
```
-/
def ncodeunitsSubString {S : Type} (s : SubString S) : Index := s.ncodeunits

/-!
Julia source: base/strings/substring.jl:140-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::SubString) = codeunit(s.string)::CodeunitType
```
-/
def codeunitTypeSubString {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : SubString S) : CT := ops.codeunitType s.string

/-!
Julia source: base/strings/substring.jl:141-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(s::SubString) = length(s.string, s.offset+1, s.offset+s.ncodeunits)
```
-/
def lengthSubString {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : SubString S) : Except E Index :=
  ops.length s.string (s.offset + one) (s.offset + s.ncodeunits)

/-!
Julia source: base/strings/substring.jl:144-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow length(s::SubString{String}) = length(s.string, s.offset+1, s.offset+s.ncodeunits)
```
-/
def lengthStringSubString {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : SubString S) : Except E Index :=
  ops.length s.string (s.offset + one) (s.offset + s.ncodeunits)

/-!
Julia source: base/strings/substring.jl:146-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function codeunit(s::SubString, i::Integer)
    @boundscheck checkbounds(s, i)
    @inbounds return codeunit(s.string, s.offset + i)
end
```
-/
def codeunitSubStringAt {S I P CU E : Type}
    (checkbounds : SubString S → I → Except E Unit)
    (parentIndex : Index → I → Except E P) (codeunit : S → P → Except E CU)
    (s : SubString S) (i : I) : Except E CU := do
  checkbounds s i
  codeunit s.string (← parentIndex s.offset i)

/-!
Julia source: base/strings/substring.jl:151-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(s::SubString, i::Integer=firstindex(s))
    i == ncodeunits(s)+1 && return nothing
    @boundscheck checkbounds(s, i)
    y = iterate(s.string, s.offset + i)
    y === nothing && return nothing
    c, i = y::Tuple{AbstractChar,Int}
    return c, i - s.offset
end
```
-/
def iterateSubString {S I P C E : Type}
    (isEnd : I → Index → Bool) (checkbounds : SubString S → I → Except E Unit)
    (parentIndex : Index → I → Except E P)
    (iterate : S → P → Except E (Option (C × Index)))
    (s : SubString S) (i : I) : Except E (Option (C × Index)) := do
  if isEnd i (s.ncodeunits + one) then pure none
  else
    checkbounds s i
    match ← iterate s.string (← parentIndex s.offset i) with
    | none => pure none
    | some (c, next) => pure (some (c, next - s.offset))

/-!
Julia source: base/strings/substring.jl:151-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(s::SubString, i::Integer=firstindex(s))
    i == ncodeunits(s)+1 && return nothing
    @boundscheck checkbounds(s, i)
    y = iterate(s.string, s.offset + i)
    y === nothing && return nothing
    c, i = y::Tuple{AbstractChar,Int}
    return c, i - s.offset
end
```
-/
def iterateSubStringFirst {S C CT E P : Type} (ops : SubStringOps S C CT E)
    (isEnd : Index → Index → Bool) (checkbounds : SubString S → Index → Except E Unit)
    (parentIndex : Index → Index → Except E P)
    (iterate : S → P → Except E (Option (C × Index))) (s : SubString S) :
    Except E (Option (C × Index)) := do
  let result ← iterateSubString isEnd checkbounds parentIndex iterate s (ops.firstindex s)
  pure result
def collectSubStringLoop {S C E : Type}
    (iterate : SubString S → Index → Except E (Option (C × Index)))
    (s : SubString S) : Nat → Index → Except E (List C)
  | 0, _ => pure []
  | fuel + 1, i => do
      match ← iterate s i with
      | none => pure []
      | some (c, next) =>
          pure (c :: (← collectSubStringLoop iterate s fuel next))

def collectSubString {S C E : Type}
    (iterate : SubString S → Index → Except E (Option (C × Index)))
    (firstindex : SubString S → Index) (s : SubString S) : Except E (List C) :=
  collectSubStringLoop iterate s (s.ncodeunits.val.toNat + 2) (firstindex s)

/-!
Julia source: base/strings/substring.jl:160-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(s::SubString, i::Integer)
    @boundscheck checkbounds(s, i)
    @inbounds return getindex(s.string, s.offset + i)
end
```
-/
def getindexSubString {S I P C E : Type}
    (checkbounds : SubString S → I → Except E Unit)
    (parentIndex : Index → I → Except E P) (getindex : S → P → Except E C)
    (s : SubString S) (i : I) : Except E C := do
  checkbounds s i
  getindex s.string (← parentIndex s.offset i)

/-!
Julia source: base/strings/substring.jl:165-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `isascii(::AbstractVector)` reduces to `@inbounds codeunit(::SubString{String}, ::Int)`, total.
isascii(ss::SubString{String}) = @assume_effects :nothrow :foldable isascii(codeunits(ss))
```
-/
def isasciiSubString {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : SubString S) : Except E Bool :=
  ops.isasciiCodeunits (JuliaLean.base.strings.basic.codeunits (fun _ => UInt8) s)

/-!
Julia source: base/strings/substring.jl:168-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isvalid(s::SubString, i::Integer)
    ib = true
    @boundscheck ib = checkbounds(Bool, s, i)
    @inbounds return ib && isvalid(s.string, s.offset + i)::Bool
end
```
-/
def isvalidSubStringAt {S I P E : Type}
    (checkbounds : SubString S → I → Except E Bool)
    (parentIndex : Index → I → Except E P) (isvalid : S → P → Except E Bool)
    (s : SubString S) (i : I) : Except E Bool := do
  let inBounds ← checkbounds s i
  if inBounds then isvalid s.string (← parentIndex s.offset i) else pure false

/-!
Julia source: base/strings/substring.jl:174-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds thisind(s::SubString{String}, i::Int) = _thisind_str(s, i)
```
-/
def thisindSubString {S E : Type} (thisindString : SubString S → Index → Except E Index)
    (s : SubString S) (i : Index) : Except E Index := thisindString s i

/-!
Julia source: base/strings/substring.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds nextind(s::SubString{String}, i::Int) = _nextind_str(s, i)
```
-/
def nextindSubString {S E : Type} (nextindString : SubString S → Index → Except E Index)
    (s : SubString S) (i : Index) : Except E Index := nextindString s i

/-!
Julia source: base/strings/substring.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow lastindex(s::SubString{String}) = thisind(s, ncodeunits(s)::Int)
```
-/
def lastindexSubString {S E : Type} (thisindString : SubString S → Index → Except E Index)
    (s : SubString S) : Except E Index := thisindSubString thisindString s s.ncodeunits

/-!
Julia source: base/strings/substring.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parent(s::SubString) = s.string
```
-/
def parentSubString {S : Type} (s : SubString S) : S := s.string

/-!
Julia source: base/strings/substring.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parentindices(s::SubString) = (s.offset + 1 : thisind(s.string, s.offset + s.ncodeunits),)
```
-/
def parentindicesSubString {S C CT E : Type} (ops : SubStringOps S C CT E)
    (s : SubString S) : Except E IndexRange := do
  let last ← ops.thisindParent s.string (s.offset + s.ncodeunits)
  pure ⟨s.offset + one, last⟩

/-!
Julia source: base/strings/substring.jl:183-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(a::Union{String, SubString{String}}, b::Union{String, SubString{String}})
    sizeof(a) == sizeof(b) && _memcmp(a, b) == 0
end
```
-/
def equalStringViews {A : Type} (sizeof : A → Index) (memcmp : A → A → Index)
    (a b : A) : Bool :=
  (sizeof a).val == (sizeof b).val && (memcmp a b).val == 0

/-!
Julia source: base/strings/substring.jl:187-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(a::SubString{String}, b::SubString{String})
    c = _memcmp(a, b)
    return c < 0 ? -1 : c > 0 ? +1 : cmp(sizeof(a), sizeof(b))
end
```
-/
def cmpSubString {S : Type} (memcmp : S → S → Index) (sizeof : S → Index)
    (cmpIndex : Index → Index → Index) (a b : S) : Index :=
  let c := memcmp a b
  if c.val < 0 then int (-1) else if c.val > 0 then int 1 else cmpIndex (sizeof a) (sizeof b)

structure PointerOps (S : Type) where
  Pointer : Type
  pointer : S → Pointer
  add : Pointer → Index → Pointer

/-!
Julia source: base/strings/substring.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{UInt8}}, s::SubString{String}) = s
```
-/
def cconvertUInt8 {S : Type} (s : SubString S) : SubString S := s

/-!
Julia source: base/strings/substring.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Ptr{Int8}}, s::SubString{String}) = s
```
-/
def cconvertInt8 {S : Type} (s : SubString S) : SubString S := s

/-!
Julia source: base/strings/substring.jl:196-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(::Type{Ptr{R}}, s::SubString{String}) where R<:Union{Int8, UInt8}
    convert(Ptr{R}, pointer(s.string)) + s.offset
end
```
-/
def unsafeConvertSubString {S P E : Type} (ops : PointerOps S)
    (convertPointer : ops.Pointer → Except E P) (add : P → Index → Except E P)
    (s : SubString S) : Except E P := do
  let p ← convertPointer (ops.pointer s.string)
  add p s.offset

/-!
Julia source: base/strings/substring.jl:200-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(x::SubString{String}) = pointer(x.string) + x.offset
```
-/
def pointerSubString {S : Type} (ops : PointerOps S) (x : SubString S) : ops.Pointer :=
  ops.add (ops.pointer x.string) x.offset

/-!
Julia source: base/strings/substring.jl:201-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(x::SubString{String}, i::Integer) = pointer(x.string) + x.offset + (i-1)
```
-/
def pointerSubStringAt {S I J : Type} (ops : PointerOps S)
    (subtractOne : I → J) (add : ops.Pointer → J → Except JlError ops.Pointer)
    (x : SubString S) (i : I) : Except JlError ops.Pointer := do
  let p := ops.add (ops.pointer x.string) x.offset
  add p (subtractOne i)

structure HashOps (S : Type) where
  Secret : Type
  pointerOps : PointerOps S
  sizeof : SubString S → Index
  secret : Secret
  /-- The first argument is a strong GC root retained throughout byte hashing. -/
  hashBytes : SubString S → pointerOps.Pointer → Index → JInt .u64 → Secret → JInt .u64

/-!
Julia source: base/strings/substring.jl:203-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(data::SubString{String}, h::UInt) =
    GC.@preserve data hash_bytes(pointer(data), sizeof(data), UInt64(h), HASH_SECRET) % UInt
```
-/
def hashSubString {S : Type} (ops : HashOps S) (h : JInt .u64) (data : SubString S) : JInt .u64 :=
  JInt.rem .u64 (ops.hashBytes data (pointerSubString ops.pointerOps data) (ops.sizeof data) h ops.secret)

/-!
Julia source: base/strings/substring.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isannotated(::SubString{T}) where {T} = _isannotated(T)
```
-/
def isannotatedSubString {S : Type} (isannotatedType : Type → Bool) (_s : SubString S) : Bool :=
  isannotatedType S

/-!
Julia source: base/strings/substring.jl:208-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(a::String)            = String(a)
```
-/
def stringString {S E : Type} (toString : S → Except E S) (a : S) : Except E S := toString a

/-!
Julia source: base/strings/substring.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(a::SubString{String}) = String(a)
```
-/
def stringSubString {S Out E : Type} (ops : CopyStringOps S Out E)
    (a : SubString S) : Except E Out := do
  let result ← stringFromSubString ops a
  pure result

/-!
Julia source: base/strings/substring.jl:211-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Symbol(s::SubString{String})
    return ccall(:jl_symbol_n, Ref{Symbol}, (Ptr{UInt8}, Int), s, sizeof(s))
end
```
-/
def symbolSubString {S Sym E : Type} (ops : PointerOps S)
    (convertPointer : ops.Pointer → Except E ops.Pointer)
    (add : ops.Pointer → Index → Except E ops.Pointer)
    (sizeof : SubString S → Index) (jlSymbol : SubString S → ops.Pointer → Index → Except E Sym)
    (s : SubString S) : Except E Sym := do
  let arg := cconvertUInt8 s
  let p ← unsafeConvertSubString ops convertPointer add arg
  jlSymbol arg p (sizeof s)

structure UnsafeStringOps (C S Sym Out Off E : Type) where
  charBits : C → Nat
  bswap : Nat → Nat
  charCodeunits : C → Index
  addOffset : Off → Index → Except E Off
  writeByte : Out → Off → Nat → Except E Out
  sizeofString : S → Index
  sizeofSubString : SubString S → Index
  sizeofSymbol : Sym → Index
  copyString : Out → S → Off → Index → Except E Out
  copySubString : Out → SubString S → Off → Index → Except E Out
  copySymbol : Out → Sym → Off → Index → Except E Out

/-!
Julia source: base/strings/substring.jl:215-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function __unsafe_string!(out, c::Char, offs::Integer) # out is a (new) String (or StringVector)
    x = bswap(reinterpret(UInt32, c))
    n = ncodeunits(c)
    GC.@preserve out begin
        unsafe_store!(pointer(out, offs), x % UInt8)
        n == 1 && return n
        x >>= 8
        unsafe_store!(pointer(out, offs+1), x % UInt8)
        n == 2 && return n
        x >>= 8
        unsafe_store!(pointer(out, offs+2), x % UInt8)
        n == 3 && return n
        x >>= 8
        unsafe_store!(pointer(out, offs+3), x % UInt8)
    end
    return n
end
```
-/
def unsafeStringChar {C S Sym Out Off E : Type} (ops : UnsafeStringOps C S Sym Out Off E)
    (out : Out) (c : C) (offset : Off) : Except E (Out × Index) := do
  let mut x := ops.bswap (ops.charBits c)
  let n := ops.charCodeunits c
  let out ← ops.writeByte out offset (x % 256)
  if n.val == 1 then return (out, n)
  x := x / 256
  let out ← ops.writeByte out (← ops.addOffset offset one) (x % 256)
  if n.val == 2 then return (out, n)
  x := x / 256
  let out ← ops.writeByte out (← ops.addOffset offset (int 2)) (x % 256)
  if n.val == 3 then return (out, n)
  x := x / 256
  let out ← ops.writeByte out (← ops.addOffset offset (int 3)) (x % 256)
  pure (out, n)

/-!
Julia source: base/strings/substring.jl:233-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow @inline function __unsafe_string!(out, s::String, offs::Integer)
    n = sizeof(s)
    GC.@preserve s out unsafe_copyto!(pointer(out, offs), pointer(s), n)
    return n
end
```
-/
def unsafeStringString {C S Sym Out Off E : Type} (ops : UnsafeStringOps C S Sym Out Off E)
    (out : Out) (s : S) (offset : Off) : Except E (Out × Index) := do
  let n := ops.sizeofString s
  let out ← ops.copyString out s offset n
  pure (out, n)

/-!
Julia source: base/strings/substring.jl:239-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function __unsafe_string!(out, s::SubString{String}, offs::Integer)
    n = sizeof(s)
    GC.@preserve s out unsafe_copyto!(pointer(out, offs), pointer(s), n)
    return n
end
```
-/
def unsafeStringSubString {C S Sym Out Off E : Type} (ops : UnsafeStringOps C S Sym Out Off E)
    (out : Out) (s : SubString S) (offset : Off) : Except E (Out × Index) := do
  let n := ops.sizeofSubString s
  let out ← ops.copySubString out s offset n
  pure (out, n)

/-!
Julia source: base/strings/substring.jl:245-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow @inline function __unsafe_string!(out, s::Symbol, offs::Integer)
    n = sizeof(s)
    GC.@preserve s out unsafe_copyto!(pointer(out, offs), unsafe_convert(Ptr{UInt8},s), n)
    return n
end
```
-/
def unsafeStringSymbol {C S Sym Out Off E : Type} (ops : UnsafeStringOps C S Sym Out Off E)
    (out : Out) (s : Sym) (offset : Off) : Except E (Out × Index) := do
  let n := ops.sizeofSymbol s
  let out ← ops.copySymbol out s offset n
  pure (out, n)

inductive StringArg (C S Sym : Type) where
  | char (value : C)
  | string (value : S)
  | substring (value : SubString S)
  | symbol (value : Sym)

inductive RestrictedStringArg (C S Sym : Type) where
  | char (value : C)
  | string (value : S)
  | symbol (value : Sym)

def liftRestrictedStringArg {C S Sym : Type} : RestrictedStringArg C S Sym → StringArg C S Sym
  | .char value => .char value
  | .string value => .string value
  | .symbol value => .symbol value

structure StringBuilderOps (C S Sym Out E : Type) where
  unsafeOps : UnsafeStringOps C S Sym Out Index E
  argumentBytes : StringArg C S Sym → List Nat
  outputSize : Out → Index
  outputBytes : Out → List Nat
  allocate : Index → Except E Out

def stringArgSize {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E) :
    StringArg C S Sym → Index
  | .char c => ops.unsafeOps.charCodeunits c
  | .string s => ops.unsafeOps.sizeofString s
  | .substring s => ops.unsafeOps.sizeofSubString s
  | .symbol s => ops.unsafeOps.sizeofSymbol s

def writeStringArg {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (out : Out) (offset : Index) : StringArg C S Sym → Except E (Out × Index)
  | .char c => unsafeStringChar ops.unsafeOps out c offset
  | .string s => unsafeStringString ops.unsafeOps out s offset
  | .substring s => unsafeStringSubString ops.unsafeOps out s offset
  | .symbol s => unsafeStringSymbol ops.unsafeOps out s offset

def writeStringArgs {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E) :
    List (StringArg C S Sym) → Out → Index → Except E (Out × Index)
  | [], out, offset => pure (out, offset)
  | arg :: args, out, offset => do
      let (out, n) ← writeStringArg ops out offset arg
      writeStringArgs ops args out (offset + n)


/-!
Julia source: base/strings/substring.jl:256-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _string(a::Union{Char, String, SubString{String}, Symbol}...)
    n = 0
    for v in a
        # 4 types is too many for automatic Union-splitting, so we split manually
        # and allow one specializable call site per concrete type
        if v isa Char
            n += ncodeunits(v)
        elseif v isa String
            n += sizeof(v)
        elseif v isa SubString{String}
            n += sizeof(v)
        else
            n += sizeof(v::Symbol)
        end
    end
    out = _string_n(n)
    offs = 1
    for v in a
        if v isa Char
            offs += __unsafe_string!(out, v, offs)
        elseif v isa String || v isa SubString{String}
            offs += __unsafe_string!(out, v, offs)
        else
            offs += __unsafe_string!(out, v::Symbol, offs)
        end
    end
    return out
end
```
-/
def buildString {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (args : List (StringArg C S Sym)) : Except E Out := do
  let n := args.foldl (fun total arg => total + stringArgSize ops arg) zero
  let out ← ops.allocate n
  let (out, _) ← writeStringArgs ops args out one
  pure out
/-!
Julia source: base/strings/substring.jl:252-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable :nothrow string(a::Union{Char, String, Symbol}...) = _string(a...)
```
-/
def stringRestricted {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (args : List (RestrictedStringArg C S Sym)) : Except E Out := do
  let result ← buildString ops (args.map liftRestrictedStringArg)
  pure result

/-!
Julia source: base/strings/substring.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(a::Union{Char, String, SubString{String}, Symbol}...) = _string(a...)
```
-/
def stringAny {C S Sym Out E : Type} (ops : StringBuilderOps C S Sym Out E)
    (args : List (StringArg C S Sym)) : Except E Out := do
  let result ← buildString ops args
  pure result

inductive RepeatInput (S : Type) where
  | string (value : S)
  | substring (value : SubString S)

structure RepeatOps (S Out E I : Type) where
  isNegative : I → Bool
  toUInt : I → Except E Nat
  showInteger : I → String
  uintMax : Nat
  sizeof : RepeatInput S → Nat
  outputSize : Out → Nat
  emptyString : Out
  stringFromString : S → Except E Out
  stringCopyOps : CopyStringOps S Out E
  allocateString : Nat → Except E Out
  codeunitOne : RepeatInput S → Except E Nat
  memset : Out → Nat → Nat → Except E Out
  copyBlock : Out → RepeatInput S → Nat → Nat → Except E Out
  argumentError : String → E
  outOfMemoryError : E

def repeatCopyBlocks {S Out E I : Type} (ops : RepeatOps S Out E I)
    (s : RepeatInput S) (sourceSize : Nat) : Nat → Nat → Out → Except E Out
  | 0, _, out => pure out
  | remaining + 1, i, out => do
      let out ← ops.copyBlock out s (i * sourceSize + 1) sourceSize
      repeatCopyBlocks ops s sourceSize remaining (i + 1) out



/-!
Julia source: base/strings/substring.jl:289-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat(s::Union{String, SubString{String}}, r::Integer)
    r < 0 && throw(ArgumentError("can't repeat a string $r times"))
    r = UInt(r)::UInt
    r == 0 && return ""
    r == 1 && return String(s)
    n = sizeof(s)
    n == 0 && return ""
    r > typemax(UInt) ÷ UInt(n) && throw(OutOfMemoryError())
    out = _string_n(n*r)
    if n == 1 # common case: repeating a single-byte string
        @inbounds b = codeunit(s, 1)
        memset(unsafe_convert(Ptr{UInt8}, out), b, r)
    else
        for i = 0:r-1
            GC.@preserve s out unsafe_copyto!(pointer(out, i*n+1), pointer(s), n)
        end
    end
    return out
end
```
-/
def repeatString {S Out E I : Type} (ops : RepeatOps S Out E I)
    (s : RepeatInput S) (r : I) : Except E Out := do
  if ops.isNegative r then throw (ops.argumentError ("can't repeat a string " ++ ops.showInteger r ++ " times"))
  let r ← ops.toUInt r
  if r == 0 then pure ops.emptyString
  else if r == 1 then
    match s with
    | .string value => ops.stringFromString value
    | .substring view => stringFromSubString ops.stringCopyOps view
  else
    let n := ops.sizeof s
    if n == 0 then pure ops.emptyString
    else if r > ops.uintMax / n then throw ops.outOfMemoryError
    else do
      let out ← ops.allocateString (n * r)
      if n == 1 then
        let b ← ops.codeunitOne s
        ops.memset out b r
      else
        repeatCopyBlocks ops s n r 0 out
/-!
Julia source: base/strings/substring.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable repeat(s::String, r::BitInteger) = @invoke repeat(s::String, r::Integer)
```
-/
def repeatBitInteger {S Out E I : Type} (ops : RepeatOps S Out E I)
    (s : S) (r : I) : Except E Out := do
  let result ← repeatString ops (.string s) r
  pure result

/-- A successful iteration consumes a nonempty portion of the remaining code units.
The suffix and size proof are termination witnesses, with no executable bounds check. -/
structure FilterNext (C : Type) (remaining : List UInt8) where
  char : C
  state : Index
  tail : List UInt8
  smaller : tail.length < remaining.length

structure FilterOps (S C Out E Result : Type) where
  unsafeOps : UnsafeStringOps C S Unit Out Index E
  sizeof : S → Index
  /-- Semantic observation used by specifications; filtering executes `iterate` instead. -/
  characters : S → Except E (List C)
  codeunits : S → List UInt8
  iterate : S → (remaining : List UInt8) → Index → Except E (Option (FilterNext C remaining))
  firstindex : S → Index
  allocate : Index → Except E Out
  predicate : C → Bool
  resize : Out → Index → Except E Out
  sizehint : Out → Index → Except E Out
  toString : Out → Except E Result
  outputCharacters : Result → Except E (List C)

def filterCharacters {S C Out E Result : Type} (ops : FilterOps S C Out E Result)
    (chars : List C) : Out → Index → Except E (Out × Index)
  | out, offset =>
      match chars with
      | [] => pure (out, offset)
      | c :: rest => do
          if ops.predicate c then
            let (out, n) ← unsafeStringChar ops.unsafeOps out c offset
            filterCharacters ops rest out (offset + n)
          else filterCharacters ops rest out offset

def filterIteration {S C Out E Result : Type} (ops : FilterOps S C Out E Result)
    (s : S) (remaining : List UInt8) (state : Index) (out : Out) (offset : Index) :
    Except E (Out × Index) := do
  match ← ops.iterate s remaining state with
  | none => pure (out, offset)
  | some next =>
    if ops.predicate next.char then
      let (out, n) ← unsafeStringChar ops.unsafeOps out next.char offset
      filterIteration ops s next.tail next.state out (offset + n)
    else
      filterIteration ops s next.tail next.state out offset
termination_by remaining.length
decreasing_by all_goals exact next.smaller

/-!
Julia source: base/strings/substring.jl:309-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f, s::Union{String, SubString{String}})
    out = StringVector(sizeof(s))
    offset = 1
    for c in s
        if f(c)
            offset += __unsafe_string!(out, c, offset)
        end
    end
    resize!(out, offset-1)
    sizehint!(out, offset-1)
    return String(out)
end
```
-/
def filterString {S C Out E Result : Type} (ops : FilterOps S C Out E Result) (s : S) : Except E Result := do
  let mut out ← ops.allocate (ops.sizeof s)
  let (next, offset) ← filterIteration ops s (ops.codeunits s) (ops.firstindex s) out one
  out := ← ops.resize next (offset - one)
  out := ← ops.sizehint out (offset - one)
  ops.toString out

/-!
Julia source: base/strings/substring.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(s::AbstractString, r::AbstractUnitRange{<:Integer}) = SubString(s, r)
```
-/
def getindexStringRange {S C CT E R I : Type} (ops : SubStringOps S C CT E)
    (rangeOps : RangeOps R I) (toInt : I → Except E Index) (s : S) (r : R) :
    Except E (SubString S) := do
  let result ← subStringRange ops rangeOps toInt s r
  pure result

end JuliaLean.base.strings.substring
