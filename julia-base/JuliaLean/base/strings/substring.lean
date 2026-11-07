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
    (s : S) (i j : Index) (boundscheck : Bool := true) : Except E (SubString S) := do
  if j.val < i.val then
    pure ⟨s, zero, zero⟩
  else
    if boundscheck then
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
    (s : S) (firstIndex count : Index) (boundscheck : Bool := true) : Except E (SubString S) := do
  if boundscheck && (count.val < 0 || firstIndex.val < 1 ||
      count.val > (ops.ncodeunits s - firstIndex + one).val) then
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
    (s : SubString S) (firstIndex count : Index) (boundscheck : Bool := true) : Except E (SubString S) := do
  if boundscheck && (count.val < 0 || firstIndex.val < 1 ||
      count.val > (s.ncodeunits - firstIndex + one).val) then
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
    (s : S) (i j : Index) (boundscheck : Bool := true) : Except E (SubString S) := do
  let result ← typedSubString ops s i j boundscheck
  pure result

/-!
Julia source: base/strings/substring.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds SubString(s::AbstractString, i::Integer, j::Integer=lastindex(s)) = SubString(s, Int(i)::Int, Int(j)::Int)
```
-/
def subStringInteger {S C CT E I : Type} (ops : SubStringOps S C CT E)
    (toInt : I → Except E Index) (s : S) (i j : I) (boundscheck : Bool := true) :
    Except E (SubString S) := do
  let i ← toInt i
  let j ← toInt j
  subStringInt ops s i j boundscheck

/-!
Julia source: base/strings/substring.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds SubString(s::AbstractString, i::Integer, j::Integer=lastindex(s)) = SubString(s, Int(i)::Int, Int(j)::Int)
```
-/
def subStringIntegerDefault {S C CT E I : Type} (ops : SubStringOps S C CT E)
    (toInt : I → Except E Index) (lastindex : S → Except E Index) (s : S) (i : I)
    (boundscheck : Bool := true) : Except E (SubString S) := do
  let j ← lastindex s
  subStringInt ops s (← toInt i) j boundscheck

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
    (s : S) : Except E (SubString S) := rawSubstring ops s one (ops.ncodeunits s) false

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


/-! Coverage models for `base/strings/substring.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.Strings

/-- The code units of a SubString: `codeunit(s::SubString, i) =
codeunit(s.string, s.offset + i)`, `base/strings/substring.jl:146-149`. -/
def JSub.view (ss : JSub) : JStr := ss.str.slice ss.offset.val.toNat ss.ncu.val.toNat

/-- `SubString{T}(s, i, j)`, `base/strings/substring.jl:76-84`. `checked = false`
models `@inbounds`. `checkbounds(s, i:j)` is `1 ≤ i && j ≤ ncodeunits(s)` for a
nonempty range (`base/strings/basic.jl:206-207`). -/
def substring (s : JStr) (i j : JInt64) (checked : Bool := true) : SJl JSub :=
  if !decide (i.val ≤ j.val) then .ok ⟨s, ix 0, ix 0⟩
  else
    let chk : SJl Unit :=
      if !checked then .ok ()
      else if !(decide (1 ≤ i.val) && decide (j.val ≤ (ncodeunits s).val)) then .error boundsErr
      else if !isvalidAt s i then .error (.stringIndexError i.val)
      else if !isvalidAt s j then .error (.stringIndexError j.val)
      else .ok ()
    match chk with
    | .error e => .error e
    | .ok () =>
      match nextind s j with
      | .error e => .error e
      | .ok j' => .ok ⟨s, i - ix 1, j' - i⟩

/-- `raw_substring(s, first_index, n_codeunits)`, `base/strings/substring.jl:86-91`. -/
def rawSubstring (s : JStr) (first n : JInt64) (checked : Bool := true) : SJl JSub :=
  if checked && (decide (n.val < 0) || decide (first.val < 1) ||
      decide (n.val > (ncodeunits s - first + ix 1).val)) then .error boundsErr
  else .ok ⟨s, first - ix 1, n⟩

/-- `SubString(s) = @inbounds raw_substring(s, 1, ncodeunits(s))`,
`base/strings/substring.jl:117`. -/
def wholeSub (s : JStr) : JSub := ⟨s, ix 0, ncodeunits s⟩

/-- `iterate(s::SubString, i)`, `base/strings/substring.jl:151-158`. -/
def subIterate (ss : JSub) (i : JInt64) : SJl (Option (UInt32 × JInt64)) :=
  if i.val = (ss.ncu + ix 1).val then .ok none
  else if !(decide (1 ≤ i.val) && decide (i.val ≤ ss.ncu.val)) then .error boundsErr
  else
    match iterate ss.str (ss.offset + i) with
    | none => .ok none
    | some (c, j) => .ok (some (c, j - ss.offset))

/-- `length(s::SubString{String})`, `base/strings/substring.jl:144`. -/
def subLength (ss : JSub) : SJl JInt64 :=
  lengthRange ss.str (ss.offset + ix 1) (ss.offset + ss.ncu)

/-- `isvalid(s::SubString, i)`, `base/strings/substring.jl:168-172`. -/
def subIsvalid (ss : JSub) (i : JInt64) : Bool :=
  decide (1 ≤ i.val ∧ i.val ≤ ss.ncu.val) && isvalidAt ss.str (ss.offset + i)

/-- `getindex(s::SubString, i)`, `base/strings/substring.jl:160-163`. -/
def subGetindex (ss : JSub) (i : JInt64) : SJl UInt32 :=
  if !(decide (1 ≤ i.val) && decide (i.val ≤ ss.ncu.val)) then .error boundsErr
  else getindex ss.str (ss.offset + i)

end JuliaLean.Strings

namespace JuliaLean.StringsCovA.Substring

open JuliaLean JuliaLean.Strings

def ctor (s : JStr) (i j : JInt64) := Strings.substring s i j
def rawCtor (s : JStr) (first n : JInt64) := Strings.rawSubstring s first n
def rawCtorSub (s : JSub) (first n : JInt64) :=
  Strings.rawSubstring s.str (s.offset + first) n
def whole (s : JStr) : JSub := Strings.wholeSub s
def ctorInts (s : JStr) (i j : JInt64) := ctor s i j
def ctorRange (s : JStr) (r : JInt64 × JInt64) := ctor s r.1 r.2
def ctorSub (s : JSub) (i j : JInt64) := ctor s.str (s.offset + i) (s.offset + j)
def identity (s : JSub) : JSub := s
def view (s : JStr) (i j : JInt64) := ctor s i j
def maybeviewRange (s : JStr) (i j : JInt64) := view s i j
def maybeviewArgs {α : Type} (get : JStr → α → β) (s : JStr) (args : α) := get s args
def convertSub (convert : α → JStr) (s : α) := whole (convert s)
def convertIdentity (s : JSub) := s
def convertUnionString (s : JStr) : Sum JStr JSub := Sum.inl s
def convertUnionSub (s : JSub) : Sum JStr JSub := Sum.inr s
def convertUnionAbstract (convert : α → JStr) (s : α) : Sum JStr JSub := Sum.inl (convert s)
def toString (s : JSub) : List UInt8 := s.view.bytes

def ncodeunits (s : JSub) := s.ncu
def codeunitType (_s : JSub) : Nat := 8
def length (s : JSub) := Strings.subLength s
def codeunit (s : JSub) (i : JInt64) : SJl UInt8 :=
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else Strings.codeunit s.str (s.offset + i)
def getindex (s : JSub) (i : JInt64) := Strings.subGetindex s i
def isascii (s : JSub) := Strings.isascii s.view
def isvalid (s : JSub) (i : JInt64) := Strings.subIsvalid s i
def thisind (s : JSub) (i : JInt64) := Strings.thisind s.view i
def nextind (s : JSub) (i : JInt64) := Strings.nextind s.view i
def lastindex (s : JSub) := Strings.lastindex s.view
def parent (s : JSub) := s.str
def parentindices (s : JSub) : Int × Int := (s.offset.val + 1, s.offset.val + s.ncu.val)
def eq (a b : JSub) := a.view.bytes == b.view.bytes
def cmp (a b : JSub) := Strings.cmp a.view b.view
def cconvert (s : JSub) := s
def unsafeConvert (base : Nat) (s : JSub) := base + s.offset.val.toNat
def pointer (base : Nat) (s : JSub) := unsafeConvert base s
def pointerAt (base : Nat) (s : JSub) (i : Int) := base + s.offset.val + i - 1
def hash (H : List UInt8 → UInt64 → UInt64) (s : JSub) (h : UInt64) := H s.view.bytes h
def isannotated (f : JStr → Bool) (s : JSub) := f s.str
def stringString (s : JStr) := s
def stringSub (s : JSub) := s.view
def symbol (intern : List UInt8 → Nat) (s : JSub) := intern s.view.bytes

inductive Piece where | char (bytes : List UInt8) | string (bytes : List UInt8) | symbol (bytes : List UInt8)

def pieceBytes : Piece → List UInt8
  | .char b | .string b | .symbol b => b
def unsafeWrite (out : List UInt8) (piece : Piece) (offset : Nat) : List UInt8 :=
  out.take (offset - 1) ++ pieceBytes piece ++ out.drop (offset - 1 + (pieceBytes piece).length)
def buildString (pieces : List Piece) : List UInt8 := (pieces.map pieceBytes).flatten
def stringPieces (pieces : List Piece) := buildString pieces

def repeatBitInteger (s : JStr) (r : JInt64) := Strings.repeatStr s r
def repeatInteger (s : JSub) (r : JInt64) := Strings.repeatStr s.view r
def filter (f : UInt32 → Bool) (s : JSub) := stringOfChars ((Strings.chars s.view).filter f)
def getindexRange (s : JStr) (i j : JInt64) := Strings.substring s i j

end JuliaLean.StringsCovA.Substring


namespace JuliaLean.StringsCovA.SubstringFaithfulAccess

open JuliaLean JuliaLean.Strings

def ncodeunitsM (s : JSub) := s.ncu

def codeunitType (codeunitParent : JStr → Nat) (s : JSub) := codeunitParent s.str

def lengthGeneric (lengthParent : JStr → JInt64 → JInt64 → SJl JInt64) (s : JSub) :=
  lengthParent s.str (s.offset + ix 1) (s.offset + s.ncu)

def lengthString (lengthParent : JStr → JInt64 → JInt64 → SJl JInt64) (s : JSub) :=
  lengthParent s.str (s.offset + ix 1) (s.offset + s.ncu)

def codeunitAt (codeunitParent : JStr → JInt64 → SJl UInt8) (s : JSub) (i : JInt64) : SJl UInt8 :=
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else codeunitParent s.str (s.offset + i)

def getindexAt (getParent : JStr → JInt64 → SJl UInt32) (s : JSub) (i : JInt64) : SJl UInt32 :=
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else getParent s.str (s.offset + i)

def isasciiM (asciiBytes : List UInt8 → Bool) (s : JSub) := asciiBytes s.view.bytes

def isvalidM (check : JSub → JInt64 → Bool) (parentValid : JStr → JInt64 → Bool) (s : JSub) (i : JInt64) :=
  check s i && parentValid s.str (s.offset + i)

def thisindM (helper : JSub → JInt64 → SJl JInt64) (s : JSub) (i : JInt64) := helper s i

def nextindM (helper : JSub → JInt64 → SJl JInt64) (s : JSub) (i : JInt64) := helper s i

def lastindexM (thisind : JSub → JInt64 → JInt64) (s : JSub) := thisind s s.ncu

def parentM (s : JSub) := s.str

def parentindicesM (thisind : JStr → JInt64 → JInt64) (s : JSub) :=
  (s.offset + ix 1, thisind s.str (s.offset + s.ncu))

def eqM (memcmp : JSub → JSub → Int) (a b : JSub) : Bool :=
  a.ncu.val == b.ncu.val && memcmp a b == 0

def cmpM (memcmp : JSub → JSub → Int) (a b : JSub) : Int :=
  let c := memcmp a b
  if c < 0 then -1 else if c > 0 then 1 else Int.sign (a.ncu.val - b.ncu.val)

def cconvertU8 (s : JSub) := s

def cconvertI8 (s : JSub) := s

def unsafeConvert (convert : Nat → Nat) (base : Nat) (s : JSub) := convert base + s.offset.val

def pointerM (base : Nat) (s : JSub) := base + s.offset.val.toNat

def pointerAtM (base : Int) (s : JSub) (i : Int) := base + s.offset.val + i - 1

def hashM (hashBytes : Nat → Nat → UInt64 → UInt64 → UInt64) (base : Nat)
    (s : JSub) (h secret : UInt64) := hashBytes (base + s.offset.val.toNat) s.ncu.val.toNat h secret

def isannotatedM (f : JStr → Bool) (s : JSub) := f s.str

def stringString (s : JStr) := s

def stringSub (toString : JSub → JStr) (s : JSub) := toString s

def symbolM (ccall : Nat → Nat → Nat) (base : Nat) (s : JSub) :=
  ccall (base + s.offset.val.toNat) s.ncu.val.toNat

end JuliaLean.StringsCovA.SubstringFaithfulAccess


namespace JuliaLean.StringsCovA.SubstringFaithfulCtor

open JuliaLean JuliaLean.Strings

def typedCtor (s : JStr) (i j : JInt64) : SJl JSub := Strings.substring s i j

def rawCtor (s : JStr) (first n : JInt64) : SJl JSub := Strings.rawSubstring s first n

def rawSubCtor (s : JSub) (first n : JInt64) : SJl JSub := Strings.rawSubstring s.str (s.offset + first) n

def typedWhole (s : JStr) : JSub := ⟨s, ix 0, ncodeunits s⟩

def ctorInt (s : JStr) (i j : JInt64) := typedCtor s i j

def ctorInteger (s : JStr) (i j : JInt64) := ctorInt s i j

def ctorRange (s : JStr) (r : JInt64 × JInt64) := ctorInteger s r.1 r.2

def ctorNested (s : JSub) (i j : JInt64) : SJl JSub :=
  if i.val ≤ j.val && !(1 ≤ i.val ∧ j.val ≤ s.ncu.val) then .error boundsErr
  else typedCtor s.str (s.offset + i) (s.offset + j)

def wholeAbstract (s : JStr) := rawCtor s (ix 1) (ncodeunits s)

def wholeSub (s : JSub) := s

def viewRange (s : JStr) (r : JInt64 × JInt64) := ctorRange s r

def maybeviewRange (s : JStr) (r : JInt64 × JInt64) := viewRange s r

def maybeviewArgs (getindex : JStr → α → β) (s : JStr) (args : α) := getindex s args

def convertSub (convertString : α → JStr) (s : α) := typedWhole (convertString s)

def convertIdentity (s : JSub) := s

def convertUnionString (s : JStr) : Sum JStr JSub := .inl s

def convertUnionSub (s : JSub) : Sum JStr JSub := .inr s

def convertUnionAbstract (convertString : α → JStr) (s : α) : Sum JStr JSub := .inl (convertString s)

def toString (s : JSub) : List UInt8 := s.view.bytes

end JuliaLean.StringsCovA.SubstringFaithfulCtor


namespace JuliaLean.StringsCovA.SubstringFaithfulFinal

open JuliaLean JuliaLean.Strings

def storeByte (out : List UInt8) (offs : Nat) (b : UInt8) : List UInt8 :=
  Strings.writeAt out (offs - 1) [b]

/-- `__unsafe_string!(out, c::Char, offs)` at `base/strings/substring.jl:215-231`. -/
def writeChar (out : List UInt8) (c : UInt32) (offs : Nat) : List UInt8 × Nat :=
  let x := bswap32 c
  let n := ncodeunitsChar c
  let out := storeByte out offs x.toUInt8
  if n = 1 then (out, n) else
  let x := x >>> (8 : UInt32)
  let out := storeByte out (offs + 1) x.toUInt8
  if n = 2 then (out, n) else
  let x := x >>> (8 : UInt32)
  let out := storeByte out (offs + 2) x.toUInt8
  if n = 3 then (out, n) else
  let x := x >>> (8 : UInt32)
  (storeByte out (offs + 3) x.toUInt8, n)

/-- String overload at lines 233-237. -/
def writeString (out source : List UInt8) (offs : Nat) : List UInt8 × Nat :=
  let n := source.length
  (Strings.writeAt out (offs - 1) source, n)

/-- SubString overload at lines 239-243. -/
def writeSubString (out : List UInt8) (source : JSub) (offs : Nat) : List UInt8 × Nat :=
  let bytes := source.view.bytes
  let n := bytes.length
  (Strings.writeAt out (offs - 1) bytes, n)

/-- Symbol overload at lines 245-249; symbols are represented by their bytes. -/
def writeSymbol (out source : List UInt8) (offs : Nat) : List UInt8 × Nat :=
  let n := source.length
  (Strings.writeAt out (offs - 1) source, n)

inductive Value where
  | char (bits : UInt32)
  | string (bytes : List UInt8)
  | substring (value : JSub)
  | symbol (bytes : List UInt8)

def valueSize : Value → Nat
  | .char c => ncodeunitsChar c
  | .string s => s.length
  | .substring s => s.view.bytes.length
  | .symbol s => s.length

def writeValue (out : List UInt8) (v : Value) (offs : Nat) : List UInt8 × Nat :=
  match v with
  | .char c => writeChar out c offs
  | .string s => writeString out s offs
  | .substring s => writeSubString out s offs
  | .symbol s => writeSymbol out s offs

def writeValues : List Value → List UInt8 → Nat → List UInt8
  | [], out, _ => out
  | v :: vs, out, offs =>
      let written := writeValue out v offs
      writeValues vs written.1 (offs + written.2)

/-- `_string(a...)` at lines 256-283, including its two type-dispatch loops. -/
def buildString (values : List Value) : SJl (List UInt8) :=
  let n := (values.map valueSize).sum
  if n < 2 ^ 62 then
    let out := List.replicate n 0
    .ok (writeValues values out 1)
  else .error .outOfMemory

/-- The restricted vararg wrapper at line 252. -/
def stringRestricted (values : List Value) := buildString values

/-- The four-type vararg wrapper at line 254. -/
def stringAll (values : List Value) := buildString values

/-- BitInteger forwarding overload at line 287. -/
def repeatBitInteger (s : JStr) (r : JInt64) := Strings.repeatStr s r

/-- General Integer repeat at lines 289-307, modelled by the shared line-faithful implementation. -/
def repeatInteger (s : JStr) (r : JInt64) := Strings.repeatStr s r

/-- `filter` at lines 309-320. -/
def filterString (f : UInt32 → Bool) (s : JStr) : SJl JStr :=
  stringOfChars ((Strings.chars s).filter f)

/-- Range indexing at line 322. -/
def getindexRange (s : JStr) (i j : JInt64) := Strings.substring s i j

end JuliaLean.StringsCovA.SubstringFaithfulFinal


namespace JuliaLean.StringsCovA.SubstringRebuilt

open JuliaLean JuliaLean.Strings

structure Sub (S : Type) where
  string : S
  offset : JInt64
  ncodeunits : JInt64

structure IntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64

structure TypedCtorInput (S : Type) where
  string : S
  first : JInt64
  last : JInt64
  checkbounds : S → JInt64 → JInt64 → SJl Unit
  isvalid : S → JInt64 → SJl Bool
  stringIndexError : S → JInt64 → SJl Unit
  nextind : S → JInt64 → SJl JInt64

def typedCtor (input : TypedCtorInput S) : SJl (Sub S) :=
  if input.last < input.first then .ok ⟨input.string, ix 0, ix 0⟩
  else do
    let _ ← input.checkbounds input.string input.first input.last
    let firstValid ← input.isvalid input.string input.first
    if !firstValid then
      let _ ← input.stringIndexError input.string input.first
      .error .assertion
    else
      let lastValid ← input.isvalid input.string input.last
      if !lastValid then
        let _ ← input.stringIndexError input.string input.last
        .error .assertion
      else
        let after ← input.nextind input.string input.last
        return ⟨input.string, input.first - ix 1, after - input.first⟩

def emptyOffsetInput : TypedCtorInput Unit where
  string := ()
  first := ix 4
  last := ix 3
  checkbounds := fun _ _ _ => .ok ()
  isvalid := fun _ _ => .error .assertion
  stringIndexError := fun _ _ => .error .assertion
  nextind := fun _ _ => .error .assertion

structure RawCtorInput (S : Type) where
  string : S
  first : JInt64
  count : JInt64
  ncodeunits : S → SJl JInt64

def rawCtor (input : RawCtorInput S) : SJl (Sub S) := do
  let total ← input.ncodeunits input.string
  if input.count < ix 0 || input.first < ix 1 || total - input.first + ix 1 < input.count then
    .error (.jl .boundsError)
  else .ok ⟨input.string, input.first - ix 1, input.count⟩

structure RawNestedInput (S : Type) where
  substring : Sub S
  first : JInt64
  count : JInt64

def rawNested (input : RawNestedInput S) : SJl (Sub S) :=
  if input.count < ix 0 || input.first < ix 1 ||
      input.substring.ncodeunits - input.first + ix 1 < input.count then
    .error (.jl .boundsError)
  else .ok ⟨input.substring.string,
    input.first + input.substring.offset - ix 1, input.count⟩

def typedWhole (s : S) (ncodeunits : S → SJl JInt64) : SJl (Sub S) := do
  let count ← ncodeunits s
  return ⟨s, ix 0, count⟩

def ctorInt (input : TypedCtorInput S) : SJl (Sub S) := typedCtor input

def ctorInteger (s : S) (first : IntegerInput I) (last : IntegerInput J)
    (ctor : S → JInt64 → JInt64 → SJl (Sub S)) : SJl (Sub S) := do
  let i ← first.toInt
  let j ← last.toInt
  ctor s i j

structure UnitRangeInput (I J : Type) where
  value : I
  first : I → SJl (IntegerInput J)
  last : I → SJl (IntegerInput J)

def ctorRange (s : S) (range : UnitRangeInput R I)
    (ctor : S → IntegerInput I → IntegerInput I → SJl (Sub S)) : SJl (Sub S) := do
  let first ← range.first range.value
  let last ← range.last range.value
  ctor s first last

structure NestedCtorInput (S : Type) where
  substring : Sub S
  first : JInt64
  last : JInt64
  checkbounds : Sub S → JInt64 → JInt64 → SJl Unit
  parentCtor : S → JInt64 → JInt64 → SJl (Sub S)

def nestedCtor (input : NestedCtorInput S) : SJl (Sub S) := do
  if input.first ≤ input.last then
    let _ ← input.checkbounds input.substring input.first input.last
    pure ()
  else pure ()
  input.parentCtor input.substring.string
    (input.substring.offset + input.first) (input.substring.offset + input.last)

def wholeAbstract (s : S) (ncodeunits : S → SJl JInt64)
    (rawUnchecked : S → JInt64 → JInt64 → SJl (Sub S)) : SJl (Sub S) := do
  let count ← ncodeunits s
  rawUnchecked s (ix 1) count

def wholeIdentity (s : Sub S) : Sub S := s

def viewRange (s : S) (range : R) (ctor : S → R → SJl V) : SJl V := ctor s range

def maybeviewRange (s : S) (range : R) (view : S → R → SJl V) : SJl V := view s range

def maybeviewArgs (s : S) (args : Args) (getindex : S → Args → SJl V) : SJl V :=
  getindex s args

structure ConvertInput (S T : Type) where
  source : S
  convertParent : S → SJl T
  substring : T → SJl (Sub T)
  typeAssert : Sub T → SJl (Sub T)

def convertSub (input : ConvertInput S T) : SJl (Sub T) := do
  let parent ← input.convertParent input.source
  let substring ← input.substring parent
  input.typeAssert substring

def convertIdentity (s : Sub S) : Sub S := s

structure CopyInput (P : Type) where
  parent : JStr
  offset : JInt64
  count : JInt64
  pointer : JStr → JInt64 → SJl P
  unsafeString : P → JInt64 → SJl JStr

def toString (input : CopyInput P) : SJl JStr := do
  let pointer ← input.pointer input.parent (input.offset + ix 1)
  input.unsafeString pointer input.count

/-! Generic accessors and pointer operations, lines 139-206. -/

def ncodeunits (s : Sub S) : JInt64 := s.ncodeunits

def codeunitType (s : Sub S) (codeunit : S → SJl T) : SJl T := codeunit s.string

def lengthSub (s : Sub S) (length : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 :=
  length s.string (s.offset + ix 1) (s.offset + s.ncodeunits)

def codeunitAt (s : Sub S) (index : I) (checkbounds : Sub S → I → SJl Unit)
    (add : JInt64 → I → SJl JInt64) (codeunit : S → JInt64 → SJl T) : SJl T := do
  let _ ← checkbounds s index
  let parentIndex ← add s.offset index
  codeunit s.string parentIndex

def getindexAt (s : Sub S) (index : I) (checkbounds : Sub S → I → SJl Unit)
    (add : JInt64 → I → SJl JInt64) (getindex : S → JInt64 → SJl T) : SJl T := do
  let _ ← checkbounds s index
  let parentIndex ← add s.offset index
  getindex s.string parentIndex

def isvalidAt (s : Sub S) (index : I) (checkbounds : Sub S → I → SJl Bool)
    (add : JInt64 → I → SJl JInt64) (isvalid : S → JInt64 → SJl Bool) : SJl Bool := do
  let inbounds ← checkbounds s index
  if !inbounds then return false
  let parentIndex ← add s.offset index
  isvalid s.string parentIndex

def thisindString (s : JSub) (index : JInt64) : SJl JInt64 :=
  Strings.thisind s.view index

def nextindString (s : JSub) (index : JInt64) : SJl JInt64 :=
  Strings.nextind s.view index

def lastindexString (s : JSub) : SJl JInt64 := thisindString s s.ncu

def parent (s : Sub S) : S := s.string

def parentindices (s : Sub S) (thisind : S → JInt64 → SJl JInt64) : SJl (JInt64 × JInt64) := do
  let last ← thisind s.string (s.offset + s.ncodeunits)
  return (s.offset + ix 1, last)

inductive StringOrSub where
  | string (value : JStr)
  | substring (value : JSub)

def stringSize : StringOrSub → JInt64
  | .string value => Strings.ncodeunits value
  | .substring value => value.ncu

def eqStringSub (a b : StringOrSub) (memcmp : StringOrSub → StringOrSub → Int) : Bool :=
  stringSize a == stringSize b && memcmp a b == 0

def cmpSub (a b : JSub) (memcmp : JSub → JSub → Int) : Int :=
  let comparison := memcmp a b
  if comparison < 0 then -1 else if comparison > 0 then 1
  else if a.ncu < b.ncu then -1 else if b.ncu < a.ncu then 1 else 0

def pointerAt (base : Nat) (s : JSub) (index : IntegerInput I)
    (subtractOne : I → SJl Int) : SJl Nat := do
  let delta ← subtractOne index.value
  return base + s.offset.val.toNat + delta.toNat

structure HashInput where
  substring : JSub
  seed : UInt64
  secret : UInt64
  pointer : JSub → SJl Nat
  sizeof : JSub → SJl Nat
  hashBytes : Nat → Nat → UInt64 → UInt64 → SJl UInt64
  toUInt : UInt64 → UInt64

def hashSub (input : HashInput) : SJl UInt64 := do
  let pointer ← input.pointer input.substring
  let size ← input.sizeof input.substring
  let hash ← input.hashBytes pointer size input.seed input.secret
  return input.toUInt hash

inductive ParentTypeKind where | annotatedString | annotatedChar | other deriving DecidableEq
def isannotatedSub : ParentTypeKind → Bool
  | .annotatedString => true
  | .annotatedChar => true
  | .other => false

/-! Unsafe writers, string construction, repeat, filter, and range indexing. -/

structure WriterInput (Out Source I : Type) where
  output : Out
  source : Source
  offset : I
  size : Source → SJl JInt64
  pointerOut : Out → I → SJl Nat
  pointerSource : Source → SJl Nat
  copy : Nat → Nat → JInt64 → SJl Out
  writable : Out → I → JInt64 → Prop

def writeBytes (input : WriterInput Out Source I) : SJl (Out × JInt64) := do
  let count ← input.size input.source
  let destination ← input.pointerOut input.output input.offset
  let source ← input.pointerSource input.source
  let output ← input.copy destination source count
  return (output, count)

structure CharWriterInput (Out I : Type) where
  output : Out
  character : UInt32
  offset : I
  pointer : Out → I → Nat → SJl Nat
  store : Out → Nat → UInt8 → SJl Out
  writable : Out → I → Nat → Prop

def writeCharStores (input : CharWriterInput Out I) : List UInt8 :=
  let bits := bswap32 input.character
  (List.range (ncodeunitsChar input.character)).map
    (fun offset => (bits >>> (UInt32.ofNat (8 * offset))).toUInt8)

def writeCharLoop (input : CharWriterInput Out I) : List UInt8 → Nat → Out → SJl Out
  | [], _, output => .ok output
  | byte :: rest, position, output => do
      let pointer ← input.pointer output input.offset position
      let output ← input.store output pointer byte
      writeCharLoop input rest (position + 1) output

def writeChar (input : CharWriterInput Out I) : SJl (Out × Nat) := do
  let output ← writeCharLoop input (writeCharStores input) 0 input.output
  return (output, ncodeunitsChar input.character)

inductive RestrictedValue where
  | char (value : UInt32)
  | string (value : JStr)
  | symbol (bytes : List UInt8)

inductive FullValue where
  | char (value : UInt32)
  | string (value : JStr)
  | substring (value : JSub)
  | symbol (bytes : List UInt8)

def stringRestricted (values : List RestrictedValue)
    (build : List RestrictedValue → SJl JStr) : SJl JStr := build values

def fullValueSize : FullValue → JInt64
  | .char value => ix (ncodeunitsChar value)
  | .string value => Strings.ncodeunits value
  | .substring value => value.ncu
  | .symbol bytes => ix bytes.length

def sumSizes : List FullValue → JInt64
  | [] => ix 0
  | value :: rest => fullValueSize value + sumSizes rest

def writeValues (write : Out → FullValue → JInt64 → SJl (Out × JInt64)) :
    List FullValue → Out → JInt64 → SJl Out
  | [], output, _ => .ok output
  | value :: rest, output, offset => do
      let written ← write output value offset
      writeValues write rest written.1 (offset + written.2)

def buildString (values : List FullValue) (allocate : JInt64 → SJl Out)
    (write : Out → FullValue → JInt64 → SJl (Out × JInt64)) : SJl Out := do
  let output ← allocate (sumSizes values)
  writeValues write values output (ix 1)

def repeatBitInteger (s : JStr) (count : I)
    (invokeInteger : JStr → I → SJl JStr) : SJl JStr := invokeInteger s count

structure RepeatInput (I : Type) where
  bytes : List UInt8
  count : I
  negative : I → SJl Bool
  toUInt : I → SJl UInt64

def repeatInteger (input : RepeatInput I) : SJl (List UInt8) := do
  let negative ← input.negative input.count
  if negative then .error (.jl (.argumentError "negative repeat count"))
  else
    let count ← input.toUInt input.count
    if count = 0 then .ok []
    else if count = 1 then .ok input.bytes
    else if input.bytes.isEmpty then .ok []
    else if UInt64.ofNat input.bytes.length > UInt64.ofNat (2 ^ 64 - 1) / count then
      .error .outOfMemory
    else .ok (List.flatten (List.replicate count.toNat input.bytes))

structure FilterInput (B : Type) where
  bytes : JStr
  characters : SJl (List UInt32)
  allocate : JInt64 → SJl B
  predicate : UInt32 → SJl Bool
  write : B → UInt32 → JInt64 → SJl (B × JInt64)
  resize : B → JInt64 → SJl B
  sizehint : B → JInt64 → SJl B
  makeString : B → SJl JStr

def filterLoop (input : FilterInput B) : List UInt32 → B → JInt64 → SJl (B × JInt64)
  | [], output, offset => .ok (output, offset)
  | character :: rest, output, offset => do
      let keep ← input.predicate character
      let result ← if keep then input.write output character offset else .ok (output, ix 0)
      filterLoop input rest result.1 (offset + result.2)

def filterString (input : FilterInput B) : SJl JStr := do
  let output ← input.allocate (Strings.ncodeunits input.bytes)
  let characters ← input.characters
  let result ← filterLoop input characters output (ix 1)
  let resized ← input.resize result.1 (result.2 - ix 1)
  let hinted ← input.sizehint resized (result.2 - ix 1)
  input.makeString hinted

def rangeGetindex (s : S) (range : UnitRangeInput R I)
    (substring : S → UnitRangeInput R I → SJl V) : SJl V := substring s range

end JuliaLean.StringsCovA.SubstringRebuilt

namespace JuliaLean.ShellCmd

open JuliaLean

/-- `SubString(s, i, k)` and `s[i:k]` (`base/strings/substring.jl:76-84,114-117,322`):
empty if `k < i`; otherwise a `BoundsError` unless `1 ≤ i` and `k ≤ ncodeunits(s)`,
and a `StringIndexError` unless `i` and `k` are character indices. -/
def slice (s : JS) (i k : Int) : SH JS :=
  if k < i then .ok []
  else if i < 1 ∨ k > ncu s then .error (.jl .boundsError)
  else if !isStart s i then .error .stringIndex
  else if !isStart s k then .error .stringIndex
  else .ok (((pairsFrom 1 s).filter (fun q => i ≤ (q.1 : Int) ∧ (q.1 : Int) ≤ k)).map (·.2))

end JuliaLean.ShellCmd

namespace JuliaLean.MiscCov.Shell

open JuliaLean JuliaLean.ShellCmd

/-- `SubString(s, j)` of a `SubString` `s` with offset `off`: its characters and
offset (`base/strings/substring.jl:37-49`; an empty result has offset 0). -/
def subFrom (s : JS) (off : Nat) (j : Int) : SH (JS × Nat) := do
  let t ← slice s j (lastindex s)
  pure (t, if t.isEmpty then 0 else off + (j - 1).toNat)

end JuliaLean.MiscCov.Shell
