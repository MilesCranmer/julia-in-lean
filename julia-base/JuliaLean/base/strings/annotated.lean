import JuliaLean.base.io
import JuliaLean.base.range
import JuliaLean.base.strings.substring
import JuliaLean.base.hashing
import JuliaLean.base.strings.stringview

/-!
# Model of `base/strings/annotated.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Underlying strings, characters and metadata values remain generic. Annotation
vectors are typed mutable references through `Store`, preserving sharing and
mutation on exceptions. Substrings and unit ranges reuse the installed models.
Range endpoints and byte offsets use Julia's wrapping Int64 arithmetic. Generic
string/character operations and later-loaded IO methods are typed callees.
Annotation order, source short-circuit order and byte-based boundaries are retained.
-/

namespace JuliaLean.base.strings.annotated
open JuliaLean
open JuliaLean.base.io (M Error)
abbrev I := JInt64
abbrev Region := JuliaLean.base.range.UnitRange I
abbrev SubString := JuliaLean.base.strings.substring.SubString
def i (z : Int) : I := JInt.wrap .i64 z
def region (first last : I) : Region := ⟨first, if first ≤ last then last else first - i 1⟩
def shift (r : Region) (offset : I) : Region := region (r.start + offset) (r.stop + offset)
def emptyRegion (r : Region) : Bool := r.stop < r.start
def sameRegion (a b : Region) : Bool := (emptyRegion a && emptyRegion b) || (a.start == b.start && a.stop == b.stop)

structure Store (World Ref Element : Type) where
  new : List Element → M World Ref
  read : Ref → M World (List Element)
  push : Ref → Element → M World Unit
  write : Ref → List Element → M World Unit
  copy : Ref → M World Ref

structure StringOps (World S C : Type) where
  firstindex : S → M World I
  lastindex : S → M World I
  ncodeunits : S → M World I
  isEmpty : S → M World Bool
  thisind : S → I → M World I
  prevind : S → I → M World I
  nextind : S → I → M World I
  getindex : S → I → M World C
  checkbounds : S → I → M World Unit
  isvalid : S → I → M World Bool
  stringIndexError : S → I → M World C
  rawSubstring : S → I → I → M World (SubString S)
  substring : S → Region → M World (SubString S)
  charNcodeunits : C → M World I
  reverse : S → M World S
  emptyString : S

/--
Julia source: base/strings/annotated.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const Annotation = NamedTuple{(:label, :value), Tuple{Symbol, Any}}
```
-/
structure Annotation (Value : Type) where
  label : String
  value : Value

/--
Julia source: base/strings/annotated.jl:4-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const RegionAnnotation = NamedTuple{(:region, :label, :value), Tuple{UnitRange{Int}, Symbol, Any}}
```
-/
structure RegionAnnotation (Value : Type) where
  region : Region
  label : String
  value : Value

/--
Julia source: base/strings/annotated.jl:64-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct AnnotatedString{S <: AbstractString} <: AbstractString
    string::S
    annotations::Vector{RegionAnnotation}
end
```
-/
structure AnnotatedString (S Regions : Type) where
  string : S
  annotations : Regions

/--
Julia source: base/strings/annotated.jl:95-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct AnnotatedChar{C <: AbstractChar} <: AbstractChar
    char::C
    annotations::Vector{Annotation}
end
```
-/
structure AnnotatedChar (C Annots : Type) where
  char : C
  annotations : Annots

inductive StringPart (S C Regions Annots Other : Type) where
  | string (s : AnnotatedString S Regions)
  | substring (s : SubString (AnnotatedString S Regions))
  | char (c : AnnotatedChar C Annots)
  | other (value : Other)

structure Event where
  pos : I
  active : Bool
  index : I


/--
Julia source: base/strings/annotated.jl:104-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedString(s::AbstractString, annots::Vector) =
    AnnotatedString(s, Vector{RegionAnnotation}(annots))
```
-/
def stringVectorCtor {World S Input Ref : Type} (convert : Input → M World Ref)
    (value : S) (annots : Input) : M World (AnnotatedString S Ref) := do
  pure ⟨value, ← convert annots⟩

/--
Julia source: base/strings/annotated.jl:107-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedString(s::AbstractString, annots) =
    AnnotatedString(s, collect(RegionAnnotation, annots))
```
-/
def stringIterableCtor {World S Input Ref : Type} (convert : Input → M World Ref)
    (value : S) (annots : Input) : M World (AnnotatedString S Ref) := do
  pure ⟨value, ← convert annots⟩

/--
Julia source: base/strings/annotated.jl:110-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedChar(c::AbstractChar, annots::Vector) =
    AnnotatedChar(c, Vector{Annotation}(annots))
```
-/
def charVectorCtor {World C Input Ref : Type} (convert : Input → M World Ref)
    (value : C) (annots : Input) : M World (AnnotatedChar C Ref) := do
  pure ⟨value, ← convert annots⟩

/--
Julia source: base/strings/annotated.jl:113-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedChar(c::AbstractChar, annots) =
    AnnotatedChar(c, collect(Annotation, annots))
```
-/
def charIterableCtor {World C Input Ref : Type} (convert : Input → M World Ref)
    (value : C) (annots : Input) : M World (AnnotatedChar C Ref) := do
  pure ⟨value, ← convert annots⟩

/--
Julia source: base/strings/annotated.jl:118-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedString(s::AnnotatedString, annots::Vector{RegionAnnotation}) =
    AnnotatedString(s.string, vcat(s.annotations, annots))
```
-/
def flattenString {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (s : AnnotatedString S Ref) (annots : Ref) : M World (AnnotatedString S Ref) := do
  let left ← store.read s.annotations
  let right ← store.read annots
  pure ⟨s.string, ← store.new (left ++ right)⟩

/--
Julia source: base/strings/annotated.jl:121-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedChar(c::AnnotatedChar, annots::Vector{Annotation}) =
    AnnotatedChar(c.char, vcat(c.annotations, Vector{Annotation}(annots)))
```
-/
def flattenChar {World C Ref Value : Type} (store : Store World Ref (Annotation Value))
    (convertVector : Ref → M World Ref) (c : AnnotatedChar C Ref) (annots : Ref) : M World (AnnotatedChar C Ref) := do
  let left ← store.read c.annotations
  let copied ← convertVector annots
  pure ⟨c.char, ← store.new (left ++ (← store.read copied))⟩

/--
Julia source: base/strings/annotated.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
String(s::AnnotatedString{String}) = s.string
```
-/
def toString {S Ref : Type} (s : AnnotatedString S Ref) : S := s.string

/--
Julia source: base/strings/annotated.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AnnotatedString}, s::AnnotatedString) = s
```
-/
def convertAnnotatedString {S Ref : Type} (s : AnnotatedString S Ref) : AnnotatedString S Ref := s

/--
Julia source: base/strings/annotated.jl:130-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AnnotatedString{S}}, s::S) where {S <: AbstractString} =
    AnnotatedString(s, Vector{RegionAnnotation}())
```
-/
def convertStringTyped {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (s : S) : M World (AnnotatedString S Ref) := do pure ⟨s, ← store.new []⟩

/--
Julia source: base/strings/annotated.jl:132-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AnnotatedString}, s::S) where {S <: AbstractString} =
    convert(AnnotatedString{S}, s)
```
-/
def convertString {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (s : S) : M World (AnnotatedString S Ref) := convertStringTyped store s

/--
Julia source: base/strings/annotated.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedString(s::S) where {S <: AbstractString} = convert(AnnotatedString{S}, s)
```
-/
def newAnnotatedString {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (s : S) : M World (AnnotatedString S Ref) := convertStringTyped store s

/--
Julia source: base/strings/annotated.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AnnotatedChar}, c::AnnotatedChar) = c
```
-/
def convertAnnotatedChar {C Ref : Type} (c : AnnotatedChar C Ref) : AnnotatedChar C Ref := c

/--
Julia source: base/strings/annotated.jl:137-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AnnotatedChar{C}}, c::C) where { C <: AbstractChar } =
    AnnotatedChar{C}(c, Vector{Annotation}())
```
-/
def convertCharTyped {World C Ref Value : Type} (store : Store World Ref (Annotation Value))
    (c : C) : M World (AnnotatedChar C Ref) := do pure ⟨c, ← store.new []⟩

/--
Julia source: base/strings/annotated.jl:139-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{AnnotatedChar}, c::C) where { C <: AbstractChar } =
    convert(AnnotatedChar{C}, c)
```
-/
def convertChar {World C Ref Value : Type} (store : Store World Ref (Annotation Value))
    (c : C) : M World (AnnotatedChar C Ref) := convertCharTyped store c

/--
Julia source: base/strings/annotated.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedChar(c::AbstractChar) = convert(AnnotatedChar, c)
```
-/
def newAnnotatedChar {World C Ref Value : Type} (store : Store World Ref (Annotation Value))
    (c : C) : M World (AnnotatedChar C Ref) := convertChar store c

/--
Julia source: base/strings/annotated.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedChar(c::UInt32) = convert(AnnotatedChar, Char(c))
```
-/
def charFromUInt32 {World C Ref Value : Type} (store : Store World Ref (Annotation Value))
    (charConstructor : JInt .u32 → M World C) (c : JInt .u32) : M World (AnnotatedChar C Ref) := do
  convertChar store (← charConstructor c)

/--
Julia source: base/strings/annotated.jl:144-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedChar{C}(c::UInt32) where {C <: AbstractChar} = convert(AnnotatedChar, C(c))
```
-/
def typedCharFromUInt32 {World C Ref Value : Type} (store : Store World Ref (Annotation Value))
    (charConstructor : JInt .u32 → M World C) (c : JInt .u32) : M World (AnnotatedChar C Ref) := do
  convertChar store (← charConstructor c)

/--
Julia source: base/strings/annotated.jl:146-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{<:AnnotatedString}, ::Type{<:AbstractString}) = AnnotatedString
```
-/
def promoteRule {TypeTag : Type} (annotatedStringType : TypeTag) : TypeTag := annotatedStringType

/--
Julia source: base/strings/annotated.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(s::AnnotatedString) = ncodeunits(s.string)::Int
```
-/
def ncodeunits {World S Ref : Type} (callee : S → M World I)
    (s : AnnotatedString S Ref) : M World I := callee s.string

/--
Julia source: base/strings/annotated.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunits(s::AnnotatedString) = codeunits(s.string)
```
-/
def codeunits {World S Ref Result : Type} (callee : S → M World Result)
    (s : AnnotatedString S Ref) : M World Result := callee s.string

/--
Julia source: base/strings/annotated.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::AnnotatedString) = codeunit(s.string)
```
-/
def codeunitType {World S Ref Result : Type} (callee : S → M World Result)
    (s : AnnotatedString S Ref) : M World Result := callee s.string

/--
Julia source: base/strings/annotated.jl:158-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(s::AnnotatedString) = firstindex(s.string)
```
-/
def firstindex {World S Ref : Type} (callee : S → M World I)
    (s : AnnotatedString S Ref) : M World I := callee s.string

/--
Julia source: base/strings/annotated.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(s::AnnotatedString) = lastindex(s.string)
```
-/
def lastindex {World S Ref : Type} (callee : S → M World I)
    (s : AnnotatedString S Ref) : M World I := callee s.string

/--
Julia source: base/strings/annotated.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::AnnotatedString, i::Integer) = codeunit(s.string, i)
```
-/
def codeunitAt {World S Ref Index Result : Type} (callee : S → Index → M World Result)
    (s : AnnotatedString S Ref) (index : Index) : M World Result := callee s.string index

/--
Julia source: base/strings/annotated.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(s::AnnotatedString, i::Integer) = isvalid(s.string, i)::Bool
```
-/
def isvalidAt {World S Ref Index : Type} (callee : S → Index → M World Bool)
    (s : AnnotatedString S Ref) (index : Index) : M World Bool := callee s.string index

/--
Julia source: base/strings/annotated.jl:157-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:AnnotatedString{S}}) where {S} = AnnotatedChar{eltype(S)}
```
-/
def eltypeString {TypeTag : Type} (eltype annotatedCharType : TypeTag → TypeTag)
    (underlying : TypeTag) : TypeTag := annotatedCharType (eltype underlying)

/--
Julia source: base/strings/annotated.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unannotate(s::AnnotatedString) = s.string
```
-/
def unannotate {S Ref : Type} (s : AnnotatedString S Ref) : S := s.string

/--
Julia source: base/strings/annotated.jl:186-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unannotate(s::SubString{<:AnnotatedString})
    start_index = first(parentindices(s)[1])
    @inbounds raw_substring(parent(s).string, start_index, ncodeunits(s))
end
```
-/
def unannotateSubstring {World S Ref C : Type} (ops : StringOps World S C)
    (s : SubString (AnnotatedString S Ref)) : M World (SubString S) :=
  ops.rawSubstring s.string.string (s.offset + i 1) s.ncodeunits

/--
Julia source: base/strings/annotated.jl:418-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotations(s::AnnotatedString) = s.annotations
```
-/
def annotations {S Ref : Type} (s : AnnotatedString S Ref) : Ref := s.annotations

/--
Julia source: base/strings/annotated.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotations(c::AnnotatedChar) = c.annotations
```
-/
def charAnnotations {C Ref : Type} (c : AnnotatedChar C Ref) : Ref := c.annotations

/--
Julia source: base/strings/annotated.jl:432-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function annotations(s::AnnotatedString, pos::UnitRange{<:Integer})
    # TODO optimise
    result = RegionAnnotation[]
    for ann in s.annotations
        if !isempty(intersect(pos, ann.region))
            clamped_region = max(first(pos), first(ann.region)):min(last(pos), last(ann.region))
            # @inline setindex makes :region const knowable (#60365)
            push!(result, @inline(setindex(ann, clamped_region, :region)))
        end
    end
    return result
end
```
-/
def annotationsRange {World S Ref Value Position : Type} (store : Store World Ref (RegionAnnotation Value))
    (intersects : Position → Region → M World Bool) (maxFirst minLast : Position → I → M World I)
    (s : AnnotatedString S Ref) (pos : Position) : M World Ref := do
  let result ← store.new []
  for ann in ← store.read s.annotations do
    if ← intersects pos ann.region then
      let clamped := region (← maxFirst pos ann.region.start) (← minLast pos ann.region.stop)
      store.push result { ann with region := clamped }
  pure result

def queryRegion {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (s : AnnotatedString S Ref) (pos : Region) : M World Ref :=
  annotationsRange store
    (fun p r => pure (!emptyRegion p && !emptyRegion r && max p.start r.start ≤ min p.stop r.stop))
    (fun p first => pure (max p.start first)) (fun p last => pure (min p.stop last)) s pos

/--
Julia source: base/strings/annotated.jl:445-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotations(s::AnnotatedString, pos::Integer) = annotations(s, pos:pos)
```
-/
def annotationsAt {World S Ref Position Range : Type}
    (singleton : Position → Range) (annotations : AnnotatedString S Ref → Range → M World Ref)
    (s : AnnotatedString S Ref) (pos : Position) : M World Ref := annotations s (singleton pos)

/--
Julia source: base/strings/annotated.jl:420-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function annotations(s::SubString{<:AnnotatedString})
    substr_range = s.offset+1:s.offset+s.ncodeunits
    result = RegionAnnotation[]
    for ann in annotations(s.string, substr_range)
        # Shift the region to be relative to the substring start
        shifted_region = first(ann.region)-s.offset:last(ann.region)-s.offset
        # @inline setindex makes :region const knowable (#60365)
        push!(result, @inline(setindex(ann, shifted_region, :region)))
    end
    return result
end
```
-/
def annotationsSubstring {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (s : SubString (AnnotatedString S Ref)) : M World Ref := do
  let subrange := region (s.offset + i 1) (s.offset + s.ncodeunits)
  let result ← store.new []
  for ann in ← store.read (← queryRegion store s.string subrange) do
    store.push result { ann with region := region (ann.region.start - s.offset) (ann.region.stop - s.offset) }
  pure result

/--
Julia source: base/strings/annotated.jl:447-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotations(s::SubString{<:AnnotatedString}, pos::Integer) =
    annotations(s.string, s.offset + pos)
```
-/
def annotationsSubstringAt {World S Ref Position Sum : Type}
    (addOffset : I → Position → Sum) (annotations : AnnotatedString S Ref → Sum → M World Ref)
    (s : SubString (AnnotatedString S Ref)) (pos : Position) : M World Ref :=
  annotations s.string (addOffset s.offset pos)

/--
Julia source: base/strings/annotated.jl:450-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotations(s::SubString{<:AnnotatedString}, pos::UnitRange{<:Integer}) =
    annotations(s.string, first(pos)+s.offset:last(pos)+s.offset)
```
-/
def annotationsSubstringRange {World S Ref Position : Type}
    (shiftPosition : Position → I → Position)
    (annotations : AnnotatedString S Ref → Position → M World Ref)
    (s : SubString (AnnotatedString S Ref)) (pos : Position) : M World Ref :=
  annotations s.string (shiftPosition pos s.offset)

/--
Julia source: base/strings/annotated.jl:192-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(s::AnnotatedString, i::Integer)
    @boundscheck checkbounds(s, i)
    @inbounds if isvalid(s, i)
        AnnotatedChar(s.string[i], Annotation[(; label, value) for (; label, value) in annotations(s, i)])
    else
        string_index_err(s, i)
    end
end
```
-/
def getindex {World S C Regions Annots Value Index : Type}
    (regionStore : Store World Regions (RegionAnnotation Value)) (charStore : Store World Annots (Annotation Value))
    (checkbounds : AnnotatedString S Regions → Index → M World Unit)
    (isvalid : AnnotatedString S Regions → Index → M World Bool)
    (getChar : S → Index → M World C)
    (annotations : AnnotatedString S Regions → Index → M World Regions)
    (indexError : AnnotatedString S Regions → Index → M World (AnnotatedChar C Annots))
    (s : AnnotatedString S Regions) (index : Index) : M World (AnnotatedChar C Annots) := do
  checkbounds s index
  if ← isvalid s index then
    let char ← getChar s.string index
    let values ← regionStore.read (← annotations s index)
    pure ⟨char, ← charStore.new (values.map (fun a => ⟨a.label, a.value⟩))⟩
  else indexError s index

/--
Julia source: base/strings/annotated.jl:155-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds iterate(s::AnnotatedString, i::Integer=firstindex(s)) =
    if i <= lastindex(s.string); (s[i], nextind(s, i)) end
```
-/
def iterateString {World S C Ref Index : Type}
    (firstindex : AnnotatedString S Ref → M World Index) (lastindex : S → M World Index)
    (le : Index → Index → Bool) (getindex : AnnotatedString S Ref → Index → M World C)
    (nextind : AnnotatedString S Ref → Index → M World Index)
    (s : AnnotatedString S Ref) (index : Option Index := none) : M World (Option (C × Index)) := do
  let index ← match index with | some i => pure i | none => firstindex s
  if le index (← lastindex s.string) then return some (← getindex s index, ← nextind s index)
  pure none

/--
Julia source: base/strings/annotated.jl:204-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, s::A) where {A <: AnnotatedString}
    show(io, A)
    print(io, '(')
    show(io, s.string)
    print(io, ", ")
    tupanns = Vector{Tuple{UnitRange{Int}, Symbol, Any}}(map(values, s.annotations))
    show(IOContext(io, :typeinfo => typeof(tupanns)), tupanns)
    print(io, ')')
end
```
-/
def showString {World Io S Ref Value TypeTag : Type} (store : Store World Ref (RegionAnnotation Value))
    (showType : Io → TypeTag → M World Unit) (typeOf : AnnotatedString S Ref → TypeTag)
    (print : Io → String → M World Unit) (showString : Io → S → M World Unit)
    (showTuplesWithTypeinfo : Io → List (Region × String × Value) → M World Unit)
    (io : Io) (s : AnnotatedString S Ref) : M World Unit := do
  showType io (typeOf s)
  print io "("
  showString io s.string
  print io ", "
  let tuples := (← store.read s.annotations).map (fun a => (a.region, a.label, a.value))
  showTuplesWithTypeinfo io tuples
  print io ")"

/--
Julia source: base/strings/annotated.jl:215-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/plain", s::AnnotatedString) =
    invoke(show, Tuple{IO, AbstractString}, io, s)
```
-/
def showTextPlain {World Io S Ref : Type}
    (invokeAbstractStringShow : Io → AnnotatedString S Ref → M World Unit)
    (io : Io) (s : AnnotatedString S Ref) : M World Unit := invokeAbstractStringShow io s

/--
Julia source: base/strings/annotated.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(c::AnnotatedChar) = ncodeunits(c.char)
```
-/
def charNcodeunits {World C Ref Result : Type} (callee : C → M World Result)
    (c : AnnotatedChar C Ref) : M World Result := callee c.char

/--
Julia source: base/strings/annotated.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codepoint(c::AnnotatedChar) = codepoint(c.char)
```
-/
def codepoint {World C Ref Result : Type} (callee : C → M World Result)
    (c : AnnotatedChar C Ref) : M World Result := callee c.char

/--
Julia source: base/strings/annotated.jl:224-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(a::AnnotatedString, b::AbstractString) = cmp(a.string, b)
```
-/
def cmpLeft {World S T Ref Result : Type} (cmp : S → T → M World Result)
    (a : AnnotatedString S Ref) (b : T) : M World Result := cmp a.string b

/--
Julia source: base/strings/annotated.jl:225-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(a::AbstractString, b::AnnotatedString) = cmp(a, b.string)
```
-/
def cmpRight {World S T Ref Result : Type} (cmp : S → T → M World Result)
    (a : S) (b : AnnotatedString T Ref) : M World Result := cmp a b.string

/--
Julia source: base/strings/annotated.jl:227-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmp(a::AnnotatedString, b::AnnotatedString) = cmp(a.string, b.string)
```
-/
def cmpBoth {World S T Ref Result : Type} (cmp : S → T → M World Result)
    (a : AnnotatedString S Ref) (b : AnnotatedString T Ref) : M World Result := cmp a.string b.string

/--
Julia source: base/strings/annotated.jl:229-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::AnnotatedString, b::AnnotatedString) =
    a.string == b.string && a.annotations == b.annotations
```
-/
def equalBoth {World S T Ref : Type} (equalString : S → T → M World Bool)
    (equalAnnots : Ref → Ref → M World Bool) (a : AnnotatedString S Ref)
    (b : AnnotatedString T Ref) : M World Bool := do
  if !(← equalString a.string b.string) then return false
  equalAnnots a.annotations b.annotations

/--
Julia source: base/strings/annotated.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::AnnotatedString, b::AbstractString) = isempty(a.annotations) && a.string == b
```
-/
def equalLeft {World S T Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (equalString : S → T → M World Bool) (a : AnnotatedString S Ref) (b : T) : M World Bool := do
  if !(← store.read a.annotations).isEmpty then return false
  equalString a.string b

/--
Julia source: base/strings/annotated.jl:233-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::AbstractString, b::AnnotatedString) = isempty(b.annotations) && a == b.string
```
-/
def equalRight {World S T Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (equalString : S → T → M World Bool) (a : S) (b : AnnotatedString T Ref) : M World Bool := do
  if !(← store.read b.annotations).isEmpty then return false
  equalString a b.string

/--
Julia source: base/strings/annotated.jl:237-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(a::SubString{<:AnnotatedString}, b::SubString{<:AnnotatedString})
    unannotate(a) == unannotate(b) && annotations(a) == annotations(b)
end
```
-/
def equalSubstrings {World S T R : Type}
    (unannotateLeft : SubString (AnnotatedString S R) → M World (SubString S))
    (unannotateRight : SubString (AnnotatedString T R) → M World (SubString T))
    (equalString : SubString S → SubString T → M World Bool)
    (annotationsLeft : SubString (AnnotatedString S R) → M World R)
    (annotationsRight : SubString (AnnotatedString T R) → M World R)
    (equalAnnots : R → R → M World Bool)
    (a : SubString (AnnotatedString S R)) (b : SubString (AnnotatedString T R)) : M World Bool := do
  if !(← equalString (← unannotateLeft a) (← unannotateRight b)) then return false
  equalAnnots (← annotationsLeft a) (← annotationsRight b)

/--
Julia source: base/strings/annotated.jl:241-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::SubString{<:AnnotatedString}, b::AnnotatedString) =
    annotations(a) == annotations(b) && unannotate(a) == b.string
```
-/
def equalSubstringAnnotated {World S T R : Type}
    (annotations : SubString (AnnotatedString S R) → M World R) (equalAnnots : R → R → M World Bool)
    (unannotate : SubString (AnnotatedString S R) → M World (SubString S))
    (equalString : SubString S → T → M World Bool)
    (a : SubString (AnnotatedString S R)) (b : AnnotatedString T R) : M World Bool := do
  if !(← equalAnnots (← annotations a) b.annotations) then return false
  equalString (← unannotate a) b.string

/--
Julia source: base/strings/annotated.jl:244-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::SubString{<:AnnotatedString}, b::AbstractString) =
    isempty(annotations(a)) && unannotate(a) == b
```
-/
def equalSubstringPlain {World S T R Value : Type} (store : Store World R (RegionAnnotation Value))
    (annotations : SubString (AnnotatedString S R) → M World R)
    (unannotate : SubString (AnnotatedString S R) → M World (SubString S))
    (equalString : SubString S → T → M World Bool)
    (a : SubString (AnnotatedString S R)) (b : T) : M World Bool := do
  if !(← store.read (← annotations a)).isEmpty then return false
  equalString (← unannotate a) b

/--
Julia source: base/strings/annotated.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::AbstractString, b::SubString{<:AnnotatedString}) = b == a
```
-/
def equalPlainSubstring {World A B : Type} (equal : B → A → M World Bool)
    (a : A) (b : B) : M World Bool := equal b a

/--
Julia source: base/strings/annotated.jl:249-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::AnnotatedString, b::SubString{<:AnnotatedString}) = b == a
```
-/
def equalAnnotatedSubstring {World A B : Type} (equal : B → A → M World Bool)
    (a : A) (b : B) : M World Bool := equal b a

/--
Julia source: base/strings/annotated.jl:272-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function annotatedstring(xs...)
    isempty(xs) && return AnnotatedString("")
    size = mapreduce(_str_sizehint, +, xs)
    buf = IOBuffer(sizehint=size)
    s = IOContext(buf, :color => true)
    annotations = Vector{RegionAnnotation}()
    for x in xs
        size = filesize(s.io)
        if x isa AnnotatedString
            for annot in x.annotations
                push!(annotations, @inline(setindex(annot, annot.region .+ size, :region)))
            end
            print(s, x.string)
        elseif x isa SubString{<:AnnotatedString}
            for annot in x.string.annotations
                start, stop = first(annot.region), last(annot.region)
                if start <= x.offset + x.ncodeunits && stop > x.offset
                    rstart = size + max(0, start - x.offset - 1) + 1
                    rstop = size + min(stop, x.offset + x.ncodeunits) - x.offset
                    push!(annotations, @inline(setindex(annot, rstart:rstop, :region)))
                end
            end
            print(s, unannotate(x))
        elseif x isa AnnotatedChar
            for annot in x.annotations
                push!(annotations, (region=1+size:1+size, annot...))
            end
            print(s, x.char)
        else
            print(s, x)
        end
    end
    str = takestring!(buf)
    AnnotatedString(str, annotations)
end
```
-/
def annotatedstring {World S Out C Regions Annots Value Other Buffer Io : Type}
    (regions : Store World Regions (RegionAnnotation Value)) (annots : Store World Annots (Annotation Value))
    (ops : StringOps World S C) (empty : Out)
    (sizehint : StringPart S C Regions Annots Other → M World I)
    (newBuffer : I → M World Buffer) (colorContext : Buffer → M World Io)
    (filesize : Io → M World I) (printString : Io → S → M World Unit)
    (printSubstring : Io → SubString S → M World Unit) (printChar : Io → C → M World Unit)
    (printOther : Io → Other → M World Unit) (takeString : Buffer → M World Out)
    (xs : List (StringPart S C Regions Annots Other)) : M World (AnnotatedString Out Regions) := do
  if xs.isEmpty then return ⟨empty, ← regions.new []⟩
  let mut totalSize := i 0
  for x in xs do totalSize := totalSize + (← sizehint x)
  let buf ← newBuffer totalSize
  let s ← colorContext buf
  let annotations ← regions.new []
  for x in xs do
    let size ← filesize s
    match x with
    | .string x =>
      for annot in ← regions.read x.annotations do
        regions.push annotations { annot with region := shift annot.region size }
      printString s x.string
    | .substring x =>
      for annot in ← regions.read x.string.annotations do
        let start := annot.region.start
        let stop := annot.region.stop
        if start ≤ x.offset + x.ncodeunits && stop > x.offset then
          let rstart := size + max (i 0) (start - x.offset - i 1) + i 1
          let rstop := size + min stop (x.offset + x.ncodeunits) - x.offset
          regions.push annotations { annot with region := region rstart rstop }
      printSubstring s (← unannotateSubstring ops x)
    | .char x =>
      for annot in ← annots.read x.annotations do
        regions.push annotations ⟨region (i 1 + size) (i 1 + size), annot.label, annot.value⟩
      printChar s x.char
    | .other x => printOther s x
  let str ← takeString buf
  pure ⟨str, annotations⟩

/--
Julia source: base/strings/annotated.jl:308-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotatedstring(s::AnnotatedString) = s
```
-/
def annotatedstringIdentity {S Ref : Type} (s : AnnotatedString S Ref) : AnnotatedString S Ref := s

/--
Julia source: base/strings/annotated.jl:309-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotatedstring(c::AnnotatedChar) =
    AnnotatedString(string(c.char), [(region=1:ncodeunits(c), annot...) for annot in c.annotations])
```
-/
def annotatedstringChar {World C S Regions Annots Value : Type}
    (regions : Store World Regions (RegionAnnotation Value)) (annots : Store World Annots (Annotation Value))
    (string : C → M World S) (ncodeunits : AnnotatedChar C Annots → M World I)
    (c : AnnotatedChar C Annots) : M World (AnnotatedString S Regions) := do
  let str ← string c.char
  let mut values := []
  for annot in ← annots.read c.annotations do
    values := values ++ [⟨region (i 1) (← ncodeunits c), annot.label, annot.value⟩]
  pure ⟨str, ← regions.new values⟩

/--
Julia source: base/strings/annotated.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AnnotatedString(s::SubString{<:AnnotatedString}) = annotatedstring(s)
```
-/
def stringFromSubstring {World S Out Ref : Type}
    (annotatedstring : SubString (AnnotatedString S Ref) → M World (AnnotatedString Out Ref))
    (s : SubString (AnnotatedString S Ref)) : M World (AnnotatedString Out Ref) := annotatedstring s

/--
Julia source: base/strings/annotated.jl:314-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat(str::AnnotatedString, r::Integer)
    r == 0 && return one(AnnotatedString)
    r == 1 && return str
    unannot = repeat(str.string, r)
    annotations = Vector{RegionAnnotation}()
    len = ncodeunits(str)
    fullregion = firstindex(str):lastindex(str)
    if isempty(str.annotations)
    elseif allequal(a -> a.region, str.annotations) && first(str.annotations).region == fullregion
        newfullregion = firstindex(unannot):lastindex(unannot)
        for annot in str.annotations
            push!(annotations, @inline(setindex(annot, newfullregion, :region)))
        end
    else
        for offset in 0:len:(r-1)*len
            for annot in str.annotations
                push!(annotations, @inline(setindex(annot, annot.region .+ offset, :region)))
            end
        end
    end
    AnnotatedString(unannot, annotations)
end
```
-/
def repeatString {World S T C Ref Value Count : Type}
    (store : Store World Ref (RegionAnnotation Value)) (ops : StringOps World S C)
    (isZero isOne : Count → Bool) (one : M World (AnnotatedString T Ref))
    (repeatUnderlying : S → Count → M World T) (firstTarget lastTarget : T → M World I)
    (offsets : I → Count → M World (List I))
    (str : AnnotatedString S Ref) (r : Count) : M World (Sum (AnnotatedString S Ref) (AnnotatedString T Ref)) := do
  if isZero r then return .inr (← one)
  if isOne r then return .inl str
  let unannot ← repeatUnderlying str.string r
  let annotations ← store.new []
  let len ← ops.ncodeunits str.string
  let fullregion := region (← ops.firstindex str.string) (← ops.lastindex str.string)
  let old ← store.read str.annotations
  if old.isEmpty then pure ()
  else if old.head?.any (fun first => old.all (fun a => sameRegion a.region first.region) && sameRegion first.region fullregion) then
    let newfullregion := region (← firstTarget unannot) (← lastTarget unannot)
    for annot in old do store.push annotations { annot with region := newfullregion }
  else
    for offset in ← offsets len r do
      for annot in ← store.read str.annotations do
        store.push annotations { annot with region := shift annot.region offset }
  pure (.inr ⟨unannot, annotations⟩)

/--
Julia source: base/strings/annotated.jl:337-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeat(str::SubString{<:AnnotatedString}, r::Integer) =
    repeat(AnnotatedString(str), r)
```
-/
def repeatSubstring {World S T Ref Count Result : Type}
    (construct : SubString (AnnotatedString S Ref) → M World (AnnotatedString T Ref))
    (repeatUnderlying : AnnotatedString T Ref → Count → M World Result)
    (str : SubString (AnnotatedString S Ref)) (r : Count) : M World Result := do
  repeatUnderlying (← construct str) r

/--
Julia source: base/strings/annotated.jl:340-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat(c::AnnotatedChar, r::Integer)
    str = repeat(c.char, r)
    fullregion = firstindex(str):lastindex(str)
    AnnotatedString(str, [(region=fullregion, annot...) for annot in c.annotations])
end
```
-/
def repeatChar {World C S Annots Regions Value Count : Type}
    (regions : Store World Regions (RegionAnnotation Value)) (annots : Store World Annots (Annotation Value))
    (repeatUnderlying : C → Count → M World S) (firstindex lastindex : S → M World I)
    (c : AnnotatedChar C Annots) (r : Count) : M World (AnnotatedString S Regions) := do
  let str ← repeatUnderlying c.char r
  let fullregion := region (← firstindex str) (← lastindex str)
  let values := (← annots.read c.annotations).map (fun a => RegionAnnotation.mk fullregion a.label a.value)
  pure ⟨str, ← regions.new values⟩

/--
Julia source: base/strings/annotated.jl:346-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reverse(s::AnnotatedString)
    lastind = lastindex(s)
    AnnotatedString(
        reverse(s.string),
        [@inline(setindex(annot,
                  UnitRange(1 + lastind - last(annot.region),
                            1 + lastind - first(annot.region)),
                  :region))
         for annot in s.annotations])
end
```
-/
def reverseString {World S T C Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : StringOps World S C) (reverse : S → M World T)
    (s : AnnotatedString S Ref) : M World (AnnotatedString T Ref) := do
  let lastind ← ops.lastindex s.string
  let reversed ← reverse s.string
  let values := (← store.read s.annotations).map fun a =>
    { a with region := region (i 1 + lastind - a.region.stop) (i 1 + lastind - a.region.start) }
  pure ⟨reversed, ← store.new values⟩

/--
Julia source: base/strings/annotated.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(s::SubString{<:AnnotatedString}) = reverse(AnnotatedString(s))
```
-/
def reverseSubstring {World S T Ref Result : Type}
    (construct : SubString (AnnotatedString S Ref) → M World (AnnotatedString T Ref))
    (reverse : AnnotatedString T Ref → M World Result) (s : SubString (AnnotatedString S Ref)) : M World Result := do
  reverse (← construct s)

/--
Julia source: base/strings/annotated.jl:364-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _annotate!(annlist::Vector{RegionAnnotation}, region::UnitRange{Int}, label::Symbol, @nospecialize(value::Any))
    if value === nothing
        deleteat!(annlist, findall(ann -> ann.region == region && ann.label === label, annlist))
    else
        push!(annlist, RegionAnnotation((; region, label, value)))
    end
end
```
-/
def annotateList {World Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (isNothing : Value → Bool) (annlist : Ref) (range : Region) (label : String) (value : Value) : M World Ref := do
  if isNothing value then
    let old ← store.read annlist
    store.write annlist (old.filter (fun a => !(sameRegion a.region range && a.label == label)))
  else store.push annlist ⟨range, label, value⟩
  pure annlist

/--
Julia source: base/strings/annotated.jl:382-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotate!(s::AnnotatedString, range::UnitRange{Int}, label::Symbol, @nospecialize(val::Any)) =
    (_annotate!(s.annotations, range, label, val); s)
```
-/
def annotateString {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (isNothing : Value → Bool) (s : AnnotatedString S Ref) (range : Region) (label : String)
    (value : Value) : M World (AnnotatedString S Ref) := do
  let _ ← annotateList store isNothing s.annotations range label value
  pure s

/--
Julia source: base/strings/annotated.jl:385-386 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotate!(ss::AnnotatedString, label::Symbol, @nospecialize(val::Any)) =
    annotate!(ss, firstindex(ss):lastindex(ss), label, val)
```
-/
def annotateStringAll {World S C Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : StringOps World S C) (isNothing : Value → Bool)
    (s : AnnotatedString S Ref) (label : String) (value : Value) : M World (AnnotatedString S Ref) := do
  annotateString store isNothing s (region (← ops.firstindex s.string) (← ops.lastindex s.string)) label value

/--
Julia source: base/strings/annotated.jl:388-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotate!(s::SubString{<:AnnotatedString}, range::UnitRange{Int}, label::Symbol, @nospecialize(val::Any)) =
    (annotate!(s.string, s.offset .+ (range), label, val); s)
```
-/
def annotateSubstring {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (isNothing : Value → Bool) (s : SubString (AnnotatedString S Ref)) (range : Region)
    (label : String) (value : Value) : M World (SubString (AnnotatedString S Ref)) := do
  let _ ← annotateString store isNothing s.string (shift range s.offset) label value
  pure s

/--
Julia source: base/strings/annotated.jl:391-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotate!(s::SubString{<:AnnotatedString}, label::Symbol, @nospecialize(val::Any)) =
    (annotate!(s.string, s.offset .+ (1:s.ncodeunits), label, val); s)
```
-/
def annotateSubstringAll {World S Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (isNothing : Value → Bool) (s : SubString (AnnotatedString S Ref)) (label : String)
    (value : Value) : M World (SubString (AnnotatedString S Ref)) := do
  let _ ← annotateString store isNothing s.string (shift (region (i 1) s.ncodeunits) s.offset) label value
  pure s

/--
Julia source: base/strings/annotated.jl:399-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotate!(c::AnnotatedChar, label::Symbol, @nospecialize(value::Any)) =
    (push!(c.annotations, Annotation((; label, value))); c)
```
-/
def annotateChar {World C Ref Value : Type} (store : Store World Ref (Annotation Value))
    (c : AnnotatedChar C Ref) (label : String) (value : Value) : M World (AnnotatedChar C Ref) := do
  store.push c.annotations ⟨label, value⟩
  pure c

/--
Julia source: base/strings/annotated.jl:477-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function annotated_chartransform(f::Function, str::AnnotatedString, state=nothing)
    outstr = IOBuffer()
    annots = RegionAnnotation[]
    bytepos = firstindex(str) - 1
    offsets = [bytepos => 0]
    for c in str.string
        oldnb = ncodeunits(c)
        bytepos += oldnb
        if isnothing(state)
            c = f(c)
        else
            c, state = f(c, state)
        end
        nb = write(outstr, c)
        if nb != oldnb
            push!(offsets, bytepos => last(last(offsets)) + nb - oldnb)
        end
    end
    for annot in str.annotations
        start, stop = first(annot.region), last(annot.region)
        start_offset = last(offsets[findlast(<=(start) ∘ first, offsets)::Int])
        stop_offset  = last(offsets[findlast(<=(stop) ∘ first, offsets)::Int])
        push!(annots, @inline(setindex(annot, (start + start_offset):(stop + stop_offset), :region)))
    end
    AnnotatedString(takestring!(outstr), annots)
end
```
-/
def annotatedChartransform {World S T C Regions Value State Buffer IterState : Type}
    (store : Store World Regions (RegionAnnotation Value)) (ops : StringOps World S C)
    (newBuffer : M World Buffer) (write : Buffer → C → M World I) (takeString : Buffer → M World T)
    (iterate : S → Option IterState → M World (Option (C × IterState)))
    (transform : C → M World C) (transformState : C → State → M World (C × Option State))
    (str : AnnotatedString S Regions) (state : Option State := none) : M World (AnnotatedString T Regions) := do
  let outstr ← newBuffer
  let annots ← store.new []
  let bytepos := (← ops.firstindex str.string) - i 1
  let offsets := [(bytepos, i 0)]
  let (_, _, offsets) ← JuliaLean.base.io.whileLoop (fun (iterState, state, bytepos, offsets) => do
    match ← iterate str.string iterState with
    | none => pure (.inl (state, bytepos, offsets))
    | some (c, next) =>
      let oldnb ← ops.charNcodeunits c
      let bytepos := bytepos + oldnb
      let (c, state) ← match state with
        | none => do pure (← transform c, none)
        | some state => transformState c state
      let nb ← write outstr c
      let offsets ← if nb != oldnb then do
          match offsets.getLast? with
          | some last => pure (offsets ++ [(bytepos, last.2 + nb - oldnb)])
          | none => throw (.jl .boundsError)
        else pure offsets
      pure (.inr (some next, state, bytepos, offsets))) (none, state, bytepos, offsets)
  for annot in ← store.read str.annotations do
    let start := annot.region.start
    let stop := annot.region.stop
    let startOffset ← match offsets.reverse.find? (fun pair => pair.1 ≤ start) with
      | some pair => pure pair.2
      | none => throw (.foreignError "TypeError" "findlast result is not Int")
    let stopOffset ← match offsets.reverse.find? (fun pair => pair.1 ≤ stop) with
      | some pair => pure pair.2
      | none => throw (.foreignError "TypeError" "findlast result is not Int")
    store.push annots { annot with region := region (start + startOffset) (stop + stopOffset) }
  pure ⟨← takeString outstr, annots⟩

/--
Julia source: base/strings/annotated.jl:504-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct RegionIterator{S <: AbstractString}
    str::S
    regions::Vector{UnitRange{Int}}
    annotations::Vector{Vector{Annotation}}
end
```
-/
structure RegionIterator (S Annots : Type) where
  str : S
  regions : List Region
  annotations : List Annots

/--
Julia source: base/strings/annotated.jl:510-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.length(si::RegionIterator) = length(si.regions)
```
-/
def regionIteratorLength {S A : Type} (si : RegionIterator S A) : I := i si.regions.length

/--
Julia source: base/strings/annotated.jl:512-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@propagate_inbounds function Base.iterate(si::RegionIterator, i::Integer=1)
    if i <= length(si.regions)
        @inbounds ((SubString(si.str, si.regions[i]), si.annotations[i]), i+1)
    end
end
```
-/
def regionIteratorIterate {World S A Sub Index : Type}
    (leLength : Index → I → Bool) (toIndex : Index → M World I) (addOne : Index → Index)
    (one : Index) (substring : S → Region → M World Sub)
    (si : RegionIterator S A) (index : Index := one) : M World (Option ((Sub × A) × Index)) := do
  if leLength index (i si.regions.length) then
    let indexInt ← toIndex index
    match si.regions[(indexInt.val - 1).toNat]?, si.annotations[(indexInt.val - 1).toNat]? with
    | some range, some annots =>
      if indexInt.val ≤ 0 then throw (.jl .boundsError)
      pure (some ((← substring si.str range, annots), addOne index))
    | _, _ => throw (.jl .boundsError)
  else pure none

/--
Julia source: base/strings/annotated.jl:518-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.eltype(::RegionIterator{S}) where { S <: AbstractString} =
    Tuple{SubString{S}, Vector{Annotation}}
```
-/
def regionIteratorEltype {TypeTag : Type} (substringType : TypeTag → TypeTag)
    (annotationVectorType : TypeTag) (tupleType : TypeTag → TypeTag → TypeTag)
    (underlying : TypeTag) : TypeTag := tupleType (substringType underlying) annotationVectorType

/--
Julia source: base/strings/annotated.jl:595-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function annotation_events(s::AbstractString, annots::Vector{RegionAnnotation}, subregion::UnitRange{Int})
    events = Vector{NamedTuple{(:pos, :active, :index), Tuple{Int, Bool, Int}}}() # Position, Active?, Annotation index
    for (i, (; region)) in enumerate(annots)
        if !isempty(intersect(subregion, region))
            start, stop = max(first(subregion), first(region)), min(last(subregion), last(region))
            start <= stop || continue # Currently can't handle empty regions
            push!(events, (pos=thisind(s, start), active=true, index=i))
            push!(events, (pos=nextind(s, stop), active=false, index=i))
        end
    end
    sort(events, by=e -> e.pos)
end
```
-/
def annotationEvents {World S C Value : Type} (ops : StringOps World S C)
    (s : S) (annots : List (RegionAnnotation Value)) (subregion : Region) : M World (List Event) := do
  let mut events := []
  for (annot, index) in annots.zipIdx do
    let start := max subregion.start annot.region.start
    let stop := min subregion.stop annot.region.stop
    if !emptyRegion subregion && !emptyRegion annot.region && start ≤ stop then
      if start > stop then continue
      events := events ++ [⟨← ops.thisind s start, true, i index + i 1⟩]
      events := events ++ [⟨← ops.nextind s stop, false, i index + i 1⟩]
  pure (events.mergeSort (fun a b => a.pos ≤ b.pos))

/--
Julia source: base/strings/annotated.jl:608-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
annotation_events(s::AnnotatedString, subregion::UnitRange{Int}) =
    annotation_events(s.string, annotations(s), subregion)
```
-/
def annotationEventsAnnotated {World S C Ref Value : Type} (store : Store World Ref (RegionAnnotation Value))
    (ops : StringOps World S C) (s : AnnotatedString S Ref) (subregion : Region) : M World (List Event) := do
  annotationEvents ops s.string (← store.read s.annotations) subregion

/--
Julia source: base/strings/annotated.jl:541-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachregion(s::AnnotatedString, subregion::UnitRange{Int}=firstindex(s):lastindex(s))
    isempty(s) || isempty(subregion) &&
        return RegionIterator(s.string, UnitRange{Int}[], Vector{Annotation}[])
    events = annotation_events(s, subregion)
    isempty(events) && return RegionIterator(s.string, [subregion], [Annotation[]])
    annotvals = Annotation[
        (; label, value) for (; label, value) in annotations(s)]
    regions = Vector{UnitRange{Int}}()
    annots = Vector{Vector{Annotation}}()
    pos = first(events).pos
    if pos > first(subregion)
        push!(regions, thisind(s, first(subregion)):prevind(s, pos))
        push!(annots, Annotation[])
    end
    activelist = Int[]
    for event in events
        if event.pos != pos
            push!(regions, pos:prevind(s, event.pos))
            push!(annots, annotvals[activelist])
            pos = event.pos
        end
        if event.active
            insert!(activelist, searchsortedfirst(activelist, event.index), event.index)
        else
            deleteat!(activelist, searchsortedfirst(activelist, event.index))
        end
    end
    if last(events).pos < nextind(s, last(subregion))
        push!(regions, last(events).pos:thisind(s, last(subregion)))
        push!(annots, Annotation[])
    end
    RegionIterator(s.string, regions, annots)
end
```
-/
def eachregion {World S C Regions Annots Value : Type}
    (regions : Store World Regions (RegionAnnotation Value)) (annots : Store World Annots (Annotation Value))
    (ops : StringOps World S C) (s : AnnotatedString S Regions) (subregion : Option Region := none)
    : M World (RegionIterator S Annots) := do
  let subregion ← match subregion with
    | some subregion => pure subregion
    | none => do pure (region (← ops.firstindex s.string) (← ops.lastindex s.string))
  if !(← ops.isEmpty s.string) && emptyRegion subregion then return ⟨s.string, [], []⟩
  let events ← annotationEventsAnnotated regions ops s subregion
  if events.isEmpty then return ⟨s.string, [subregion], [← annots.new []]⟩
  let annotvals := (← regions.read s.annotations).map (fun a => Annotation.mk a.label a.value)
  let mut outputRegions := []
  let mut outputAnnots := []
  let mut pos ← match events.head? with
    | some event => pure event.pos
    | none => throw (.jl .boundsError)
  if pos > subregion.start then
    outputRegions := outputRegions ++ [region (← ops.thisind s.string subregion.start) (← ops.prevind s.string pos)]
    outputAnnots := outputAnnots ++ [← annots.new []]
  let mut active : List I := []
  for event in events do
    if event.pos != pos then
      outputRegions := outputRegions ++ [region pos (← ops.prevind s.string event.pos)]
      let values ← active.mapM fun index => do
        if index.val ≤ 0 then throw (.jl .boundsError)
        match annotvals[(index.val - 1).toNat]? with
        | some value => pure value
        | none => throw (.jl .boundsError)
      outputAnnots := outputAnnots ++ [← annots.new values]
      pos := event.pos
    let before := active.takeWhile (fun index => index < event.index)
    let after := active.drop before.length
    if event.active then active := before ++ [event.index] ++ after
    else
      match after with
      | [] => throw (.jl .boundsError)
      | _ :: tail => active := before ++ tail
  let last ← match events.getLast? with
    | some event => pure event
    | none => throw (.jl .boundsError)
  if last.pos < (← ops.nextind s.string subregion.stop) then
    outputRegions := outputRegions ++ [region last.pos (← ops.thisind s.string subregion.stop)]
    outputAnnots := outputAnnots ++ [← annots.new []]
  pure ⟨s.string, outputRegions, outputAnnots⟩

/--
Julia source: base/strings/annotated.jl:575-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachregion(s::SubString{<:AnnotatedString}, pos::UnitRange{Int}=firstindex(s):lastindex(s))
    if isempty(s)
        RegionIterator(s.string, Vector{UnitRange{Int}}(), Vector{Vector{Annotation}}())
    else
        eachregion(s.string, first(pos)+s.offset:last(pos)+s.offset)
    end
end
```
-/
def eachregionSubstring {World S C Regions Annots Value : Type}
    (regions : Store World Regions (RegionAnnotation Value)) (annots : Store World Annots (Annotation Value))
    (ops : StringOps World S C) (isEmpty : SubString (AnnotatedString S Regions) → M World Bool)
    (firstindex lastindex : SubString (AnnotatedString S Regions) → M World I)
    (s : SubString (AnnotatedString S Regions)) (pos : Option Region := none)
    : M World (Sum (RegionIterator (AnnotatedString S Regions) Annots) (RegionIterator S Annots)) := do
  let pos ← match pos with
    | some pos => pure pos
    | none => do pure (region (← firstindex s) (← lastindex s))
  if ← isEmpty s then pure (.inl ⟨s.string, [], []⟩)
  else do
    let result ← eachregion regions annots ops s.string (some (shift pos s.offset))
    pure (.inr result)


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/strings/annotated.jl:1-2 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- /Source

-- Source: base/strings/annotated.jl:5-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     AnnotatedString{S <: AbstractString} <: AbstractString
-- 
-- A string with metadata, in the form of annotated regions.
-- 
-- More specifically, this is a simple wrapper around any other
-- [`AbstractString`](@ref) that allows for regions of the wrapped string to be
-- annotated with labeled values.
-- 
-- ```text
--                            C
--                     ┌──────┸─────────┐
--   "this is an example annotated string"
--   └──┰────────┼─────┘         │
--      A        └─────┰─────────┘
--                     B
-- ```
-- 
-- The above diagram represents a `AnnotatedString` where three ranges have been
-- annotated (labeled `A`, `B`, and `C`). Each annotation holds a label (`Symbol`)
-- and a value (`Any`). These three pieces of information are held as a
-- `$RegionAnnotation`.
-- 
-- Labels do not need to be unique, the same region can hold multiple annotations
-- with the same label.
-- 
-- Code written for `AnnotatedString`s in general should conserve the following
-- properties:
-- - Which characters an annotation is applied to
-- - The order in which annotations are applied to each character
-- 
-- Additional semantics may be introduced by specific uses of `AnnotatedString`s.
-- 
-- A corollary of these rules is that adjacent, consecutively placed, annotations
-- with identical labels and values are equivalent to a single annotation spanning
-- the combined range.
-- 
-- See also [`AnnotatedChar`](@ref), [`annotatedstring`](@ref),
-- [`annotations`](@ref), and [`annotate!`](@ref).
-- 
-- # Constructors
-- 
-- ```julia
-- AnnotatedString(s::S<:AbstractString) -> AnnotatedString{S}
-- AnnotatedString(s::S<:AbstractString, annotations::Vector{$RegionAnnotation})
-- ```
-- 
-- An AnnotatedString can also be created with [`annotatedstring`](@ref), which acts much
-- like [`string`](@ref) but preserves any annotations present in the arguments.
-- 
-- # Examples
-- 
-- ```jldoctest; setup=:(using Base: AnnotatedString)
-- julia> AnnotatedString("this is an example annotated string",
--                     [(1:18, :A, 1), (12:28, :B, 2), (18:35, :C, 3)])
-- "this is an example annotated string"
-- ```
-- """
-- /Source

-- Source: base/strings/annotated.jl:68-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     AnnotatedChar{S <: AbstractChar} <: AbstractChar
-- 
-- A Char with annotations.
-- 
-- More specifically, this is a simple wrapper around any other
-- [`AbstractChar`](@ref), which holds a list of arbitrary labelled annotations
-- (`$Annotation`) with the wrapped character.
-- 
-- See also [`AnnotatedString`](@ref), [`annotatedstring`](@ref), `annotations`,
-- `annotate!`.
-- 
-- # Constructors
-- 
-- ```julia
-- AnnotatedChar(s::S) -> AnnotatedChar{S}
-- AnnotatedChar(s::S, annotations::Vector{$Annotation})
-- ```
-- 
-- # Examples
-- 
-- ```jldoctest; setup=:(using Base: AnnotatedChar)
-- julia> AnnotatedChar('j', [(:label, 1)])
-- 'j': ASCII/Unicode U+006A (category Ll: Letter, lowercase)
-- ```
-- """
-- /Source

-- Source: base/strings/annotated.jl:99-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## Constructors ##
-- 
-- # When called with overly-specialised arguments
-- 
-- /Source

-- Source: base/strings/annotated.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:109-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:115-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Constructors to avoid recursive wrapping
-- 
-- /Source

-- Source: base/strings/annotated.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:123-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # To avoid pointless overhead
-- /Source

-- Source: base/strings/annotated.jl:126-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## Conversion/promotion ##
-- 
-- /Source

-- Source: base/strings/annotated.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:141-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:145-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:147-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## AbstractString interface ##
-- 
-- /Source

-- Source: base/strings/annotated.jl:160-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     unannotate(s::AnnotatedString{S})::S
--     unannotate(s::SubString{AnnotatedString{S}})::SubString{S}
--     unannotate(s::SubString{AnnotatedString{SubString{S}}})::SubString{S}
-- 
-- Get the underlying string of `s`, without copying.
-- 
-- # Examples
-- ```jldoctest; setup=:(using Base: AnnotatedString)
-- julia> s = AnnotatedString("abcde", [(1:3, :A, 4)])
-- "abcde"
-- 
-- julia> u = Base.unannotate(s)
-- "abcde"
-- 
-- julia> typeof(u)
-- String
-- ```
-- 
-- !!! compat "Julia 1.14"
--     This function requires at least Julia 1.14.
-- 
-- """
-- /Source

-- Source: base/strings/annotated.jl:185-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:190-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Source: base/strings/annotated.jl:200-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # To make `AnnotatedString`s repr-evaluable, we need to override
-- # the generic `AbstractString` 2-arg show method.
-- 
-- /Source

-- Source: base/strings/annotated.jl:213-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # But still use the generic `AbstractString` fallback for the 3-arg show.
-- /Source

-- Source: base/strings/annotated.jl:217-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## AbstractChar interface ##
-- 
-- /Source

-- Source: base/strings/annotated.jl:222-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Avoid the iteration fallback with comparison
-- /Source

-- Source: base/strings/annotated.jl:226-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # To avoid method ambiguity
-- /Source

-- Source: base/strings/annotated.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:231-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:234-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # To prevent substring equality from hitting the generic fallback
-- 
-- /Source

-- Source: base/strings/annotated.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:248-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:250-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     annotatedstring(values...)
-- 
-- Create a `AnnotatedString` from any number of `values` using their
-- [`print`](@ref)ed representation.
-- 
-- This acts like [`string`](@ref), but takes care to preserve any annotations
-- present (in the form of [`AnnotatedString`](@ref) or [`AnnotatedChar`](@ref) values).
-- 
-- See also [`AnnotatedString`](@ref), [`AnnotatedChar`](@ref).
-- 
-- ## Examples
-- 
-- ```jldoctest; setup=:(using Base: AnnotatedString, annotatedstring)
-- julia> annotatedstring("now an AnnotatedString")
-- "now an AnnotatedString"
-- 
-- julia> annotatedstring(AnnotatedString("annotated", [(1:9, :label, 1)]), ", and unannotated")
-- "annotated, and unannotated"
-- ```
-- """
-- /Source

-- Source: base/strings/annotated.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:311-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:336-336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:339-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:356-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # TODO optimise?
-- /Source

-- Source: base/strings/annotated.jl:359-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # TODO implement `replace(::AnnotatedString, ...)`
-- 
-- ## End AbstractString interface ##
-- 
-- /Source

-- Source: base/strings/annotated.jl:371-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     annotate!(str::AnnotatedString, [range::UnitRange{Int}], label::Symbol, value)
--     annotate!(str::SubString{AnnotatedString}, [range::UnitRange{Int}], label::Symbol, value)
-- 
-- Annotate a `range` of `str` (or the entire string) with a labeled value `(label, value)`.
-- To remove existing `label` annotations, use a value of `nothing`.
-- 
-- The order in which annotations are applied to `str` is semantically meaningful,
-- as described in [`AnnotatedString`](@ref).
-- """
-- /Source

-- Source: base/strings/annotated.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:390-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:393-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     annotate!(char::AnnotatedChar, label::Symbol, value::Any)
-- 
-- Annotate `char` with the labeled value `(label, value)`.
-- """
-- /Source

-- Source: base/strings/annotated.jl:401-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     annotations(str::Union{AnnotatedString, SubString{AnnotatedString}},
--                 [position::Union{Integer, UnitRange}]) ->
--         Vector{$RegionAnnotation}
-- 
-- Get all annotations that apply to `str`. Should `position` be provided, only
-- annotations that overlap with `position` will be returned.
-- 
-- Annotations are provided together with the regions they apply to, in the form of
-- a vector of region–annotation tuples.
-- 
-- In accordance with the semantics documented in [`AnnotatedString`](@ref), the
-- order of annotations returned matches the order in which they were applied.
-- 
-- See also [`annotate!`](@ref).
-- """
-- /Source

-- Source: base/strings/annotated.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:446-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:449-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:452-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     annotations(chr::AnnotatedChar)::Vector{$Annotation}
-- 
-- Get all annotations of `chr`, in the form of a vector of annotation pairs.
-- """
-- /Source

-- Source: base/strings/annotated.jl:459-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## Character transformation helper function, c.f. `unicode.jl`.
-- 
-- """
--     annotated_chartransform(f::Function, str::AnnotatedString, state=nothing)
-- 
-- Transform every character in `str` with `f`, adjusting annotation regions as
-- appropriate. `f` must take one of two forms, either:
-- - `f(c::Char) -> Char`, or
-- - `f(c::Char, state) -> (Char, state)`.
-- 
-- This works by comparing the number of code units of each character before and
-- after transforming with `f`, recording and aggregating any differences, then
-- applying them to the annotation regions.
-- 
-- Returns an `AnnotatedString{String}` (regardless of the original underlying
-- string type of `str`).
-- """
-- /Source

-- Source: base/strings/annotated.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:520-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     eachregion(s::AnnotatedString{S})
--     eachregion(s::SubString{AnnotatedString{S}})
-- 
-- Identify the contiguous substrings of `s` with a constant annotations, and return
-- an iterator which provides each substring and the applicable annotations as a
-- `Tuple{SubString{S}, Vector{$Annotation}}`.
-- 
-- # Examples
-- 
-- ```jldoctest; setup=:(using Base: AnnotatedString, eachregion)
-- julia> collect(eachregion(AnnotatedString(
--            "hey there", [(1:3, :face, :bold),
--                          (5:9, :face, :italic)])))
-- 3-element Vector{Tuple{SubString{String}, Vector{$Annotation}}}:
--  ("hey", [$Annotation((:face, :bold))])
--  (" ", [])
--  ("there", [$Annotation((:face, :italic))])
-- ```
-- """
-- /Source

-- Source: base/strings/annotated.jl:574-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/strings/annotated.jl:582-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     annotation_events(string::AbstractString, annots::Vector{$RegionAnnotation}, subregion::UnitRange{Int})
--     annotation_events(string::AnnotatedString, subregion::UnitRange{Int})
-- 
-- Find all annotation "change events" that occur within a `subregion` of `annots`,
-- with respect to `string`. When `string` is styled, `annots` is inferred.
-- 
-- Each change event is given in the form of a `@NamedTuple{pos::Int, active::Bool,
-- index::Int}` where `pos` is the position of the event, `active` is a boolean
-- indicating whether the annotation is being activated or deactivated, and `index`
-- is the index of the annotation in question.
-- """
-- /Source

-- Source: base/strings/annotated.jl:607-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


end JuliaLean.base.strings.annotated

namespace JuliaLean.HashOps

open JuliaLean

/-! ## Annotated strings, `base/strings/annotated.jl:64-67,224-249` -/

structure Annotation where
  label : Nat
  value : Nat
  deriving DecidableEq, Repr

structure AnnotatedText where
  chars : List Nat
  annotations : List Annotation
  deriving DecidableEq, Repr

def annotatedIsequal (a b : AnnotatedText) : Bool :=
  a.chars == b.chars && a.annotations == b.annotations

def cmpChars : List Nat → List Nat → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a < b then -1 else if b < a then 1 else cmpChars as bs

/-- AnnotatedString's `cmp` methods discard annotations. -/
def annotatedCmp (a b : AnnotatedText) : Int := cmpChars a.chars b.chars
def annotatedIsless (a b : AnnotatedText) : Bool := annotatedCmp a b < 0

/-- `UTF8Units` calls `reinterpret(UInt32, char)`. Plain `Char` is isbits; an
`AnnotatedChar` contains a vector and raises `ArgumentError`. -/
def hashNonByteUnderlying (chars : List Nat) (h : Nat) : Except JlError ByteHash :=
  .ok (.call (chars.flatMap utf8) h)

def hashNonByteAnnotated (_ : AnnotatedText) (_ : Nat) : Except JlError ByteHash :=
  .error (.argumentError "Source type for reinterpret must be isbits")
end JuliaLean.HashOps

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings

/-- A `UnitRange{Int}` as its stored `(first, last)`. -/
abbrev Region := JInt64 × JInt64

/-- `RegionAnnotation = @NamedTuple{region::UnitRange{Int}, label::Symbol, value}`,
`base/strings/annotated.jl:3-6`, with a `Nat` label and no value. -/
structure RAnn where
  lo : JInt64
  hi : JInt64
  label : Nat
  deriving DecidableEq

/-- `AnnotatedString{String}`, `base/strings/annotated.jl:64-67`. -/
structure AStr where
  str : JStr
  anns : List RAnn

/-- `SubString{AnnotatedString{String}}`: parent, `offset`, `ncodeunits`
(`base/strings/substring.jl:71-106`). -/
structure ASub where
  parent : AStr
  offset : JInt64
  ncu : JInt64

/-- `a:b` for `a b :: Int`: `UnitRange(a, b)` stores `unitrange_last(a, b)`,
`base/range.jl:428,439-441`, which is `b` when `b ≥ a` and the wrapping
`a - 1` otherwise. -/
def urange (a b : JInt64) : Region := (a, if b.val ≥ a.val then b else a - ix 1)

/-- `isempty(r::AbstractUnitRange) = first(r) > last(r)`, `base/range.jl`. -/
def isemptyR (r : Region) : Bool := decide (r.1.val > r.2.val)

/-- `@inline(setindex(annot, region, :region))`: the annotation with a new region. -/
def RAnn.setR (a : RAnn) (r : Region) : RAnn := { a with lo := r.1, hi := r.2 }

/-! ## `annotations` -/

/-- The loop of `annotations(s::AnnotatedString, pos::UnitRange{<:Integer})`,
`base/strings/annotated.jl:432-443`: keep each annotation whose region meets
`pos` (`intersect(pos, region) = max(first(pos), first(region)):min(last(pos),
last(region))`, `base/range.jl:1199`) and clamp its region to that same range. -/
def annsRange (pos : Region) : List RAnn → List RAnn
  | [] => []
  | ann :: rest =>
    if !isemptyR (urange (imax pos.1 ann.lo) (imin pos.2 ann.hi)) then
      ann.setR (urange (imax pos.1 ann.lo) (imin pos.2 ann.hi)) :: annsRange pos rest
    else annsRange pos rest

/-- `annotations(s::AnnotatedString, pos::UnitRange)`, `base/strings/annotated.jl:432-443`. -/
def annotationsRange (s : AStr) (pos : Region) : List RAnn := annsRange pos s.anns

/-- `annotations(s::AnnotatedString, pos::Integer) = annotations(s, pos:pos)`,
`base/strings/annotated.jl:445`. -/
def annotationsAt (s : AStr) (p : JInt64) : List RAnn := annotationsRange s (urange p p)

/-- The labels of the annotations that apply to position `p`, in order. -/
def labelsAt (s : AStr) (p : JInt64) : List Nat := (annotationsAt s p).map RAnn.label

/-- `annotations(s::SubString{<:AnnotatedString})`, `base/strings/annotated.jl:420-430`:
the parent's annotations over `s.offset+1:s.offset+s.ncodeunits`, shifted by
`-s.offset`. -/
def annotationsSub (s : ASub) : List RAnn :=
  let substrRange := urange (s.offset + ix 1) (s.offset + s.ncu)
  (annotationsRange s.parent substrRange).map fun ann =>
    ann.setR (urange (ann.lo - s.offset) (ann.hi - s.offset))

/-- `annotations(s::SubString{<:AnnotatedString}, pos::Integer) =
annotations(s.string, s.offset + pos)`, `base/strings/annotated.jl:447-448`. -/
def annotationsSubAt (s : ASub) (p : JInt64) : List RAnn := annotationsAt s.parent (s.offset + p)

/-- `annotations(s::SubString{<:AnnotatedString}, pos::UnitRange) =
annotations(s.string, first(pos)+s.offset:last(pos)+s.offset)`,
`base/strings/annotated.jl:450-451`. -/
def annotationsSubRange (s : ASub) (pos : Region) : List RAnn :=
  annotationsRange s.parent (urange (pos.1 + s.offset) (pos.2 + s.offset))

/-! ## `annotatedstring` -/

/-- An argument of `annotatedstring(xs...)`: an `AnnotatedString` or a
`SubString{<:AnnotatedString}`. -/
inductive AArg where
  | str (a : AStr)
  | sub (s : ASub)

/-- `@inline(setindex(annot, annot.region .+ size, :region))`,
`base/strings/annotated.jl:282`; `r .+ x = range(first(r) + x, last(r) + x)` for
a `UnitRange` and an `Integer` (`base/broadcast.jl:1188`). -/
def shiftAnn (size : JInt64) (a : RAnn) : RAnn := a.setR (urange (a.lo + size) (a.hi + size))

/-- `rstart = size + max(0, start - x.offset - 1) + 1`, `base/strings/annotated.jl:289`. -/
def rstartOf (size off : JInt64) (a : RAnn) : JInt64 := size + imax (ix 0) (a.lo - off - ix 1) + ix 1

/-- `rstop = size + min(stop, x.offset + x.ncodeunits) - x.offset`,
`base/strings/annotated.jl:290`. -/
def rstopOf (size off n : JInt64) (a : RAnn) : JInt64 := size + imin a.hi (off + n) - off

/-- The SubString branch of `annotatedstring`, `base/strings/annotated.jl:286-293`. -/
def subAnns (size off n : JInt64) : List RAnn → List RAnn
  | [] => []
  | ann :: rest =>
    if ann.lo.val ≤ (off + n).val ∧ ann.hi.val > off.val then
      ann.setR (urange (rstartOf size off ann) (rstopOf size off n ann)) :: subAnns size off n rest
    else subAnns size off n rest

/-- `print(s, unannotate(x))` for a SubString: `unannotate` is
`raw_substring(parent(s).string, s.offset + 1, ncodeunits(s))` under `@inbounds`
(`base/strings/annotated.jl:186-189`), whose bytes are the parent's code units
`offset+1 .. offset+ncodeunits`. -/
def subBytes (s : ASub) : List UInt8 := (JSub.view ⟨s.parent.str, s.offset, s.ncu⟩).bytes

/-- The loop of `annotatedstring(xs...)`, `base/strings/annotated.jl:278-303`:
`buf` holds the bytes written so far, so `size = filesize(s.io)` is its length. -/
def asLoop : List AArg → List UInt8 → List RAnn → List UInt8 × List RAnn
  | [], buf, anns => (buf, anns)
  | x :: xs, buf, anns =>
    let size := ix buf.length
    match x with
    | .str a => asLoop xs (buf ++ a.str.bytes) (anns ++ a.anns.map (shiftAnn size))
    | .sub s => asLoop xs (buf ++ subBytes s) (anns ++ subAnns size s.offset s.ncu s.parent.anns)

/-- `annotatedstring(xs...)`, `base/strings/annotated.jl:272-306`, for arguments
that are `AnnotatedString`s or SubStrings of them. The `sizehint` (`:274-275`)
only preallocates. A result of `2^62` bytes or more cannot be allocated. -/
def annotatedstring (xs : List AArg) : SJl AStr :=
  match xs with
  | [] => .ok ⟨JStr.empty, []⟩
  | _ :: _ =>
    let r := asLoop xs [] []
    if h : r.1.length < 2 ^ 62 then .ok ⟨⟨r.1, h⟩, r.2⟩ else .error .outOfMemory

/-- `AnnotatedString(s::SubString{<:AnnotatedString}) = annotatedstring(s)`,
`base/strings/annotated.jl:312`. -/
def annotatedStringOfSub (s : ASub) : SJl AStr := annotatedstring [.sub s]

/-! ## `reverse` -/

/-- `reverse(s::AnnotatedString)`, `base/strings/annotated.jl:346-355`. -/
def areverse (s : AStr) : AStr :=
  let lastind := lastindex s.str
  ⟨Strings.reverse s.str, s.anns.map fun annot =>
    annot.setR (urange (ix 1 + lastind - annot.hi) (ix 1 + lastind - annot.lo))⟩

/-! ## `eachregion` -/

/-- An annotation change event `(pos, active, index)`, `base/strings/annotated.jl:596`. -/
structure Event where
  pos : JInt64
  active : Bool
  index : Nat

/-- The loop of `annotation_events`, `base/strings/annotated.jl:597-604`; `i` is
the one-based index from `enumerate`. -/
def eventsLoop (s : JStr) (sub : Region) : Nat → List RAnn → SJl (List Event)
  | _, [] => .ok []
  | i, ann :: rest =>
    if !isemptyR (urange (imax sub.1 ann.lo) (imin sub.2 ann.hi)) then
      let start := imax sub.1 ann.lo
      let stop := imin sub.2 ann.hi
      if !decide (start.val ≤ stop.val) then eventsLoop s sub (i + 1) rest
      else do
        let a ← thisind s start
        let b ← nextind s stop
        let tl ← eventsLoop s sub (i + 1) rest
        pure ({ pos := a, active := true, index := i } :: { pos := b, active := false, index := i } :: tl)
    else eventsLoop s sub (i + 1) rest

/-- Insert `e` before the first event whose position is not smaller. -/
def insertByPos (e : Event) : List Event → List Event
  | [] => [e]
  | f :: fs => if f.pos.val < e.pos.val then f :: insertByPos e fs else e :: f :: fs

/-- `sort(events, by=e -> e.pos)`, `base/strings/annotated.jl:605`. Julia's default
sort is stable, and so is this insertion sort, so both give the same order. -/
def sortByPos : List Event → List Event
  | [] => []
  | e :: es => insertByPos e (sortByPos es)

/-- `annotation_events(s, annots, subregion)`, `base/strings/annotated.jl:595-606`,
called as `annotation_events(s.string, annotations(s), subregion)` (`:608-609`). -/
def annotationEvents (s : JStr) (anns : List RAnn) (sub : Region) : SJl (List Event) := do
  let evs ← eventsLoop s sub 1 anns
  pure (sortByPos evs)

/-- `searchsortedfirst(activelist, idx)` on the sorted `activelist`: one plus the
number of entries smaller than `idx`. -/
def searchsortedfirst (l : List Nat) (x : Nat) : Nat := (l.takeWhile (· < x)).length + 1

/-- `annotvals[activelist]`: indexing throws `BoundsError` outside `1:length`. -/
def pick (annotvals : List Nat) (active : List Nat) : SJl (List Nat) :=
  active.mapM fun k =>
    if 1 ≤ k ∧ k ≤ annotvals.length then .ok (annotvals.getD (k - 1) 0) else .error boundsErr

/-- The `for event in events` loop of `eachregion`, `base/strings/annotated.jl:556-567`.
The state is `pos` and `activelist`. -/
def regionLoop (s : JStr) (annotvals : List Nat) :
    List Event → JInt64 → List Nat → SJl (List (Region × List Nat))
  | [], _, _ => .ok []
  | e :: es, pos, active => do
    let out : List (Region × List Nat) ← if e.pos.val ≠ pos.val then do
        let b ← prevind s e.pos
        let vals ← pick annotvals active
        pure [(urange pos b, vals)]
      else pure []
    let pos := if e.pos.val ≠ pos.val then e.pos else pos
    let k := searchsortedfirst active e.index
    let active : List Nat ← if e.active then pure (active.take (k - 1) ++ e.index :: active.drop (k - 1))
      else if k ≤ active.length then pure (active.eraseIdx (k - 1)) else .error boundsErr
    let rest ← regionLoop s annotvals es pos active
    pure (out ++ rest)

/-- `firstindex(s):lastindex(s)`, the default `subregion` of `eachregion`
(`base/strings/annotated.jl:541`). -/
def defaultRegion (s : AStr) : Region := urange (firstindex s.str) (lastindex s.str)

/-- `eachregion(s::AnnotatedString, subregion)`, `base/strings/annotated.jl:541-573`:
the regions and the labels of `annotvals[activelist]` of the `RegionIterator`.
The guard `isempty(s) || isempty(subregion) && return ...` (`:542-543`) parses as
`isempty(s) || (isempty(subregion) && return ...)`. -/
def eachregion (s : AStr) (sub : Region) : SJl (List (Region × List Nat)) := do
  if !decide ((ncodeunits s.str).val = 0) && isemptyR sub then return []
  let events ← annotationEvents s.str s.anns sub
  match events with
  | [] => return [(sub, [])]
  | e0 :: _ =>
    let annotvals := s.anns.map RAnn.label
    let pos := e0.pos
    let pre : List (Region × List Nat) ← if pos.val > sub.1.val then do
        let a ← thisind s.str sub.1
        let b ← prevind s.str pos
        pure [(urange a b, [])]
      else pure []
    let mid ← regionLoop s.str annotvals events pos []
    let lastPos := (events.getLast?.map Event.pos).getD pos
    let nx ← nextind s.str sub.2
    let post : List (Region × List Nat) ← if lastPos.val < nx.val then do
        let t ← thisind s.str sub.2
        pure [(urange lastPos t, [])]
      else pure []
    return pre ++ mid ++ post

/-- `eachregion(s::SubString{<:AnnotatedString}, pos)`, `base/strings/annotated.jl:575-581`;
`isempty(s)` is `iszero(ncodeunits(s))` (`base/strings/basic.jl:181`). -/
def eachregionSub (s : ASub) (pos : Region) : SJl (List (Region × List Nat)) :=
  if s.ncu.val = 0 then .ok []
  else eachregion s.parent (urange (pos.1 + s.offset) (pos.2 + s.offset))

end JuliaLean.StringUtil

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-- Exceptions of the modelled Unicode functions: those of the shared String/Char
model (`InvalidCharError`, `CodePointError`, `BoundsError`, ...), the
`ErrorException` of `utf8proc_error` (`base/strings/unicode.jl:153`), the
`TypeError` of a failed `::T` assertion, and `fuel`, the value of a loop whose
iteration bound ran out (the proofs show the bounds are never reached). -/
inductive UErr where
  | str (e : SErr)
  | errorException
  | typeError
  | fuel
  deriving Repr, DecidableEq, Inhabited

abbrev UJl (α : Type) := Except UErr α

/-- Lift a String-model result. -/
def liftS {α : Type} : SJl α → UJl α
  | .ok a => .ok a
  | .error e => .error (.str e)

/-- `true` when a call returns. -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false
end JuliaLean.RegexUnicode.Uni
namespace JuliaLean.StringsCovB.Ann

open JuliaLean JuliaLean.Strings

abbrev Region := JInt64 × JInt64
abbrev Val := Option Nat

/-- `a:b` for `Int`s, `base/range.jl:428,439-441`. -/
abbrev urange := StringUtil.urange
/-- `isempty(r::UnitRange)`. -/
abbrev isemptyR := StringUtil.isemptyR

/-- `==(r::UnitRange, s::UnitRange)`, `base/range.jl:1141-1145`: two empty ranges
are equal; otherwise first and last agree (the step is 1). -/
def rangeEq (r s : Region) : Bool :=
  if isemptyR r then isemptyR s else !isemptyR s && r.1 == s.1 && r.2 == s.2

/-- `RegionAnnotation`, `base/strings/annotated.jl:4`. -/
structure RA where
  lo : JInt64
  hi : JInt64
  label : Nat
  value : Val
  deriving DecidableEq, Repr

/-- `Annotation`, `base/strings/annotated.jl:3`. -/
structure Ann where
  label : Nat
  value : Val
  deriving DecidableEq, Repr

/-- `AnnotatedString{String}`, `base/strings/annotated.jl:64-67`. -/
structure AS where
  str : JStr
  anns : List RA
  deriving DecidableEq, Repr

/-- `AnnotatedChar{Char}`, `base/strings/annotated.jl:95-98`. -/
structure AC where
  char : UInt32
  anns : List Ann
  deriving DecidableEq, Repr

/-- `SubString{AnnotatedString{String}}`, `base/strings/substring.jl:71-106`. -/
structure ASub where
  parent : AS
  offset : JInt64
  ncu : JInt64
  deriving DecidableEq, Repr

def RA.region (a : RA) : Region := (a.lo, a.hi)
/-- `@inline(setindex(annot, region, :region))`. -/
def RA.setR (a : RA) (r : Region) : RA := { a with lo := r.1, hi := r.2 }
/-- `(; label, value)` of a `RegionAnnotation`. -/
def RA.toAnn (a : RA) : Ann := ⟨a.label, a.value⟩
/-- `(region=r, annot...)` for an `Annotation`. -/
def RA.ofAnn (r : Region) (a : Ann) : RA := ⟨r.1, r.2, a.label, a.value⟩

/-- `==` on `RegionAnnotation` NamedTuples: fieldwise `==`, with `UnitRange` `==`
on the region. -/
def RA.jeq (a b : RA) : Bool := rangeEq a.region b.region && a.label == b.label && a.value == b.value

/-- `==` on `Vector{RegionAnnotation}`: equal lengths and elementwise `==`
(`base/abstractarray.jl` `==(A::AbstractArray, B::AbstractArray)`). -/
def annsEq : List RA → List RA → Bool
  | [], [] => true
  | a :: as, b :: bs => a.jeq b && annsEq as bs
  | _, _ => false

/-- The projection to the region-only annotations of `StringUtil`. -/
def RA.toU (a : RA) : StringUtil.RAnn := ⟨a.lo, a.hi, a.label⟩

/-! ## Constructors, `base/strings/annotated.jl:104-144` -/

/-- A tuple `(region, label, value)` as passed in a `Vector` or iterator. -/
abbrev Tup := Region × Nat × Val

/-- `RegionAnnotation(t)`: the NamedTuple conversion of a tuple. -/
def RA.ofTup (t : Tup) : RA := ⟨t.1.1, t.1.2, t.2.1, t.2.2⟩

/-- The string argument of an `AnnotatedString` constructor: a `String` or an
`AnnotatedString`. -/
inductive SArg where
  | plain (s : JStr)
  | ann (a : AS)

/-- `AnnotatedString(s, annots::Vector{RegionAnnotation})`: the inner constructor
for a `String` (`base/strings/annotated.jl:64-67`), and
`AnnotatedString(s::AnnotatedString, annots::Vector{RegionAnnotation}) =
AnnotatedString(s.string, vcat(s.annotations, annots))`
(`base/strings/annotated.jl:118-119`). -/
def ctorRA : SArg → List RA → AS
  | .plain s, anns => ⟨s, anns⟩
  | .ann a, anns => ⟨a.str, a.anns ++ anns⟩

/-- `AnnotatedString(s::AbstractString, annots::Vector) =
AnnotatedString(s, Vector{RegionAnnotation}(annots))`, `base/strings/annotated.jl:104-105`. -/
def ctorVector (s : SArg) (annots : List Tup) : AS := ctorRA s (annots.map RA.ofTup)

/-- `AnnotatedString(s::AbstractString, annots) =
AnnotatedString(s, collect(RegionAnnotation, annots))`, `base/strings/annotated.jl:107-108`;
an iterator is its list of elements. -/
def ctorIter (s : SArg) (annots : List Tup) : AS := ctorRA s (annots.map RA.ofTup)

/-- The char argument of an `AnnotatedChar` constructor. -/
inductive CArg where
  | plain (c : UInt32)
  | ann (a : AC)

/-- The inner constructor `AnnotatedChar{C}(char, annotations)`
(`base/strings/annotated.jl:95-98`) and `AnnotatedChar(c::AnnotatedChar,
annots::Vector{Annotation}) = AnnotatedChar(c.char, vcat(c.annotations,
Vector{Annotation}(annots)))`, `base/strings/annotated.jl:121-122`. -/
def cctorA : CArg → List Ann → AC
  | .plain c, anns => ⟨c, anns⟩
  | .ann a, anns => ⟨a.char, a.anns ++ anns⟩

/-- `Annotation(t)` for a tuple `(label, value)`. -/
def Ann.ofTup (t : Nat × Val) : Ann := ⟨t.1, t.2⟩

/-- `AnnotatedChar(c::AbstractChar, annots::Vector) =
AnnotatedChar(c, Vector{Annotation}(annots))`, `base/strings/annotated.jl:110-111`. -/
def cctorVector (c : CArg) (annots : List (Nat × Val)) : AC := cctorA c (annots.map Ann.ofTup)

/-- `AnnotatedChar(c::AbstractChar, annots) = AnnotatedChar(c, collect(Annotation, annots))`,
`base/strings/annotated.jl:113-114`. -/
def cctorIter (c : CArg) (annots : List (Nat × Val)) : AC := cctorA c (annots.map Ann.ofTup)

/-- `String(s::AnnotatedString{String}) = s.string`, `base/strings/annotated.jl:125`. -/
def toString (s : AS) : JStr := s.str

/-- `convert(::Type{AnnotatedString}, s::AnnotatedString) = s`, `base/strings/annotated.jl:129`. -/
def convertAS (s : AS) : AS := s

/-- `convert(::Type{AnnotatedString{S}}, s::S) = AnnotatedString(s, Vector{RegionAnnotation}())`,
`base/strings/annotated.jl:130-131`. For `S = AnnotatedString{String}` the
constructor of line 118 applies. -/
def convertASOfS (s : SArg) : AS := ctorRA s []

/-- `convert(::Type{AnnotatedString}, s::S) = convert(AnnotatedString{S}, s)`,
`base/strings/annotated.jl:132-133`. -/
def convertASOf (s : SArg) : AS := convertASOfS s

/-- `AnnotatedString(s::S) = convert(AnnotatedString{S}, s)`, `base/strings/annotated.jl:134`. -/
def ofS (s : SArg) : AS := convertASOfS s

/-- `convert(::Type{AnnotatedChar}, c::AnnotatedChar) = c`, `base/strings/annotated.jl:136`. -/
def convertAC (c : AC) : AC := c

/-- `convert(::Type{AnnotatedChar{C}}, c::C) = AnnotatedChar{C}(c, Vector{Annotation}())`,
`base/strings/annotated.jl:137-138`. -/
def convertACOfC (c : UInt32) : AC := cctorA (.plain c) []

/-- `convert(::Type{AnnotatedChar}, c::C) = convert(AnnotatedChar{C}, c)`,
`base/strings/annotated.jl:139-140`. -/
def convertACOf (c : UInt32) : AC := convertACOfC c

/-- `AnnotatedChar(c::AbstractChar) = convert(AnnotatedChar, c)`, `base/strings/annotated.jl:142`. -/
def ofChar (c : UInt32) : AC := convertACOf c

/-- `AnnotatedChar(c::UInt32) = convert(AnnotatedChar, Char(c))`,
`base/strings/annotated.jl:143`; `Char(::UInt32)` throws `CodePointError` above
`0x1fffff` (`charOfU32`). -/
def ofU32 (u : UInt32) : SJl AC := do
  let c ← charOfU32 u
  pure (convertACOf c)

/-- `AnnotatedChar{C}(c::UInt32) = convert(AnnotatedChar, C(c))`,
`base/strings/annotated.jl:144`, for `C = Char`. -/
def ofU32C (u : UInt32) : SJl AC := do
  let c ← charOfU32 u
  pure (convertACOf c)

/-! ## Type-level methods -/

/-- String and character types, for the type-level methods. -/
inductive JTy where
  | string
  | char
  | annotatedString (s : JTy)
  | annotatedStringAll
  | annotatedChar (c : JTy)
  | subString (s : JTy)
  | other
  deriving DecidableEq, Repr

/-- `eltype` of the modelled string types: `Char` for `String`
(`base/strings/basic.jl`), `AnnotatedChar{eltype(S)}` for `AnnotatedString{S}`,
`eltype(S)` for `SubString{S}`. -/
def eltypeS : JTy → JTy
  | .string => .char
  | .annotatedString s => .annotatedChar (eltypeS s)
  | .subString s => eltypeS s
  | _ => .other

/-- `eltype(::Type{<:AnnotatedString{S}}) = AnnotatedChar{eltype(S)}`,
`base/strings/annotated.jl:157`. -/
def eltypeAS (S : JTy) : JTy := .annotatedChar (eltypeS S)

/-- `promote_rule(::Type{<:AnnotatedString}, ::Type{<:AbstractString}) = AnnotatedString`,
`base/strings/annotated.jl:146`. -/
def promoteRule (_a _b : JTy) : JTy := .annotatedStringAll

/-! ## `AbstractString` interface, `base/strings/annotated.jl:150-159` -/

/-- `ncodeunits(s::AnnotatedString) = ncodeunits(s.string)::Int`, `:150`. -/
def ncodeunitsA (s : AS) : JInt64 := ncodeunits s.str
/-- `codeunits(s::AnnotatedString) = codeunits(s.string)`, `:151`: the bytes. -/
def codeunitsA (s : AS) : List UInt8 := s.str.bytes
/-- `codeunit(s::AnnotatedString) = codeunit(s.string)`, `:152`: `UInt8`, of 8 bits. -/
def codeunitTyA (_s : AS) : Nat := 8
/-- `codeunit(s::AnnotatedString, i::Integer) = codeunit(s.string, i)`, `:153`. -/
def codeunitA (s : AS) (i : JInt64) : SJl UInt8 := codeunit s.str i
/-- `isvalid(s::AnnotatedString, i::Integer) = isvalid(s.string, i)::Bool`, `:154`. -/
def isvalidA (s : AS) (i : JInt64) : Bool := isvalidAt s.str i
/-- `firstindex(s::AnnotatedString) = firstindex(s.string)`, `:158`. -/
def firstindexA (s : AS) : JInt64 := firstindex s.str
/-- `lastindex(s::AnnotatedString) = lastindex(s.string)`, `:159`. -/
def lastindexA (s : AS) : JInt64 := lastindex s.str

/-- `nextind(s::AnnotatedString, i::Int)`: the generic `nextind(s, i, 1)`
(`base/strings/basic.jl:562-573`) with `isvalid(s, i) = isvalid(s.string, i)`. -/
def nextindA (s : AS) (i : JInt64) : SJl JInt64 := nextindN s.str i (ix 1)

/-! ## `annotations` -/

/-- The loop of `annotations(s::AnnotatedString, pos::UnitRange{<:Integer})`,
`base/strings/annotated.jl:432-443`: keep each annotation whose region meets
`pos` (`intersect(pos, region) = max(first):min(last)`) and clamp its region to
that intersection. -/
def annsRange (pos : Region) : List RA → List RA
  | [] => []
  | ann :: rest =>
    if !isemptyR (urange (imax pos.1 ann.lo) (imin pos.2 ann.hi)) then
      ann.setR (urange (imax pos.1 ann.lo) (imin pos.2 ann.hi)) :: annsRange pos rest
    else annsRange pos rest

/-- `annotations(s::AnnotatedString) = s.annotations`, `base/strings/annotated.jl:418`. -/
def annotations (s : AS) : List RA := s.anns

/-- `annotations(s::AnnotatedString, pos::UnitRange{<:Integer})`,
`base/strings/annotated.jl:432-443`. -/
def annotationsRange (s : AS) (pos : Region) : List RA := annsRange pos s.anns

/-- `annotations(s::AnnotatedString, pos::Integer) = annotations(s, pos:pos)`,
`base/strings/annotated.jl:445`. -/
def annotationsAt (s : AS) (p : JInt64) : List RA := annotationsRange s (urange p p)

/-- `annotations(s::SubString{<:AnnotatedString})`, `base/strings/annotated.jl:420-430`. -/
def annotationsSub (s : ASub) : List RA :=
  (annotationsRange s.parent (urange (s.offset + ix 1) (s.offset + s.ncu))).map fun ann =>
    ann.setR (urange (ann.lo - s.offset) (ann.hi - s.offset))

/-- `annotations(c::AnnotatedChar) = c.annotations`, `base/strings/annotated.jl:458`. -/
def annotationsC (c : AC) : List Ann := c.anns

/-! ## `getindex`, `iterate`, `unannotate` -/

/-- `getindex(s::AnnotatedString, i::Integer)`, `base/strings/annotated.jl:192-199`:
`checkbounds(s, i)` (`1 ≤ i ≤ ncodeunits(s)`, `base/strings/basic.jl:204-213`),
then for a valid `i` the character `s.string[i]` with the labels and values of
`annotations(s, i)`, else `string_index_err`. -/
def getindexA (s : AS) (i : JInt64) : SJl AC :=
  if !(decide (1 ≤ i.val) && decide (i.val ≤ (ncodeunits s.str).val)) then .error boundsErr
  else if isvalidA s i then do
    let c ← getindex s.str i
    pure ⟨c, (annotationsAt s i).map RA.toAnn⟩
  else .error (.stringIndexError i.val)

/-- `iterate(s::AnnotatedString, i::Integer=firstindex(s))`,
`base/strings/annotated.jl:155-156`. -/
def iterateA (s : AS) (i : JInt64) : SJl (Option (AC × JInt64)) :=
  if i.val ≤ (lastindex s.str).val then do
    let c ← getindexA s i
    let j ← nextindA s i
    pure (some (c, j))
  else .ok none

/-- `unannotate(s::AnnotatedString) = s.string`, `base/strings/annotated.jl:184`. -/
def unannotate (s : AS) : JStr := s.str

/-- `unannotate(s::SubString{<:AnnotatedString})`, `base/strings/annotated.jl:186-189`:
`@inbounds raw_substring(parent(s).string, first(parentindices(s)[1]), ncodeunits(s))`
with `first(parentindices(s)[1]) = s.offset + 1`. -/
def unannotateSub (s : ASub) : JSub := ⟨s.parent.str, s.offset, s.ncu⟩

/-! ## `show` -/

/-- `show(io, s::A) where {A <: AnnotatedString}`, `base/strings/annotated.jl:204-212`:
`show(io, A)`, `'('`, `show(io, s.string)`, `", "`, the annotations as a
`Vector{Tuple{UnitRange{Int}, Symbol, Any}}` shown with that `:typeinfo`, `')'`.
The printers of the type, of a `String` and of the tuple vector are parameters. -/
def showAS (showType : List UInt8) (showStr : JStr → List UInt8)
    (showTups : List Tup → List UInt8) (s : AS) : List UInt8 :=
  showType ++ [0x28] ++ showStr s.str ++ [0x2c, 0x20] ++
    showTups (s.anns.map fun a => (a.region, a.label, a.value)) ++ [0x29]

/-- `show(io, ::MIME"text/plain", s::AnnotatedString) = invoke(show, Tuple{IO,
AbstractString}, io, s)`, `base/strings/annotated.jl:215-216`: the generic
`AbstractString` show, which prints the quoted, escaped characters of `s`
(`print_quoted`, `base/strings/io.jl`); without StyledStrings an `AnnotatedChar`
prints as its character (`base/strings/annotated_io.jl:356-357,387-388`). The
generic printer of a character sequence is a parameter. -/
def showPlainAS (showChars : List UInt32 → List UInt8) (s : AS) : List UInt8 :=
  showChars (chars s.str)

/-! ## `AbstractChar` interface -/

/-- `ncodeunits(c::AnnotatedChar) = ncodeunits(c.char)`, `base/strings/annotated.jl:220`. -/
def ncodeunitsC (c : AC) : Nat := ncodeunitsChar c.char

/-- `codepoint(c::AnnotatedChar) = codepoint(c.char)`, `base/strings/annotated.jl:221`. -/
def codepointC (c : AC) : SJl UInt32 := codepoint c.char

/-! ## Comparison -/

/-- `cmp(a::AnnotatedString, b::AbstractString) = cmp(a.string, b)`, `:224`. -/
def cmpAS (a : AS) (b : JStr) : Int := Strings.cmp a.str b
/-- `cmp(a::AbstractString, b::AnnotatedString) = cmp(a, b.string)`, `:225`. -/
def cmpSA (a : JStr) (b : AS) : Int := Strings.cmp a b.str

/-- `==(a::AnnotatedString, b::AnnotatedString)`, `base/strings/annotated.jl:229-230`. -/
def eqAA (a b : AS) : Bool := a.str == b.str && annsEq a.anns b.anns
/-- `==(a::AnnotatedString, b::AbstractString)`, `base/strings/annotated.jl:232`. -/
def eqAS (a : AS) (b : JStr) : Bool := a.anns.isEmpty && a.str == b
/-- `==(a::AbstractString, b::AnnotatedString)`, `base/strings/annotated.jl:233`. -/
def eqSA (a : JStr) (b : AS) : Bool := b.anns.isEmpty && a == b.str

/-- `unannotate(a) == unannotate(b)` for two `SubString{String}`s: their code units
are equal (`==(a::SubString{String}, b::SubString{String})` compares lengths and
bytes). -/
def subEq (a b : JSub) : Bool := a.view.bytes == b.view.bytes

/-- `==(a::SubString{<:AnnotatedString}, b::SubString{<:AnnotatedString})`,
`base/strings/annotated.jl:237-239`. -/
def eqUU (a b : ASub) : Bool :=
  subEq (unannotateSub a) (unannotateSub b) && annsEq (annotationsSub a) (annotationsSub b)
/-- `==(a::SubString{<:AnnotatedString}, b::AnnotatedString)`, `:241-242`. -/
def eqUA (a : ASub) (b : AS) : Bool :=
  annsEq (annotationsSub a) b.anns && (unannotateSub a).view.bytes == b.str.bytes
/-- `==(a::SubString{<:AnnotatedString}, b::AbstractString)`, `:244-245`. -/
def eqUS (a : ASub) (b : JStr) : Bool :=
  (annotationsSub a).isEmpty && (unannotateSub a).view.bytes == b.bytes
/-- `==(a::AbstractString, b::SubString{<:AnnotatedString}) = b == a`, `:247`. -/
def eqSU (a : JStr) (b : ASub) : Bool := eqUS b a
/-- `==(a::AnnotatedString, b::SubString{<:AnnotatedString}) = b == a`, `:249`. -/
def eqAU (a : AS) (b : ASub) : Bool := eqUA b a

/-! ## `annotatedstring` -/

/-- An argument of `annotatedstring(xs...)`: an `AnnotatedString`, a SubString of
one, an `AnnotatedChar`, or any other value, given by the bytes `print` writes. -/
inductive XArg where
  | str (a : AS)
  | sub (s : ASub)
  | achar (c : AC)
  | other (bs : List UInt8)

/-- `@inline(setindex(annot, annot.region .+ size, :region))`, `base/strings/annotated.jl:282`. -/
def shiftRA (size : JInt64) (a : RA) : RA := a.setR (urange (a.lo + size) (a.hi + size))

/-- The SubString branch of `annotatedstring`, `base/strings/annotated.jl:286-293`. -/
def subRAs (size off n : JInt64) : List RA → List RA
  | [] => []
  | ann :: rest =>
    if ann.lo.val ≤ (off + n).val ∧ ann.hi.val > off.val then
      ann.setR (urange (StringUtil.rstartOf size off ann.toU) (StringUtil.rstopOf size off n ann.toU))
        :: subRAs size off n rest
    else subRAs size off n rest

/-- `unannotate(x)` of a SubString: the parent's code units `offset+1 .. offset+ncodeunits`. -/
def subBytes (s : ASub) : List UInt8 := (unannotateSub s).view.bytes

/-- The loop of `annotatedstring(xs...)`, `base/strings/annotated.jl:278-303`.
`buf` holds the bytes printed so far, so `size = filesize(s.io)` is its length.
`print(s, x.char)` writes the character's code units (`charBytes`). -/
def asLoop : List XArg → List UInt8 → List RA → List UInt8 × List RA
  | [], buf, anns => (buf, anns)
  | x :: xs, buf, anns =>
    let size := ix buf.length
    match x with
    | .str a => asLoop xs (buf ++ a.str.bytes) (anns ++ a.anns.map (shiftRA size))
    | .sub s => asLoop xs (buf ++ subBytes s) (anns ++ subRAs size s.offset s.ncu s.parent.anns)
    | .achar c =>
      asLoop xs (buf ++ charBytes c.char)
        (anns ++ c.anns.map (RA.ofAnn (urange (ix 1 + size) (ix 1 + size))))
    | .other bs => asLoop xs (buf ++ bs) anns

/-- `annotatedstring(xs...)`, `base/strings/annotated.jl:272-306`. The `sizehint`
(`:274-275`) only preallocates. A result of `2^62` bytes or more cannot be
allocated. -/
def annotatedstring (xs : List XArg) : SJl AS :=
  match xs with
  | [] => .ok ⟨JStr.empty, []⟩
  | _ :: _ =>
    let r := asLoop xs [] []
    if h : r.1.length < 2 ^ 62 then .ok ⟨⟨r.1, h⟩, r.2⟩ else .error .outOfMemory

/-- `annotatedstring(s::AnnotatedString) = s`, `base/strings/annotated.jl:308`. -/
def annotatedstringAS (s : AS) : AS := s

/-- `annotatedstring(c::AnnotatedChar) = AnnotatedString(string(c.char),
[(region=1:ncodeunits(c), annot...) for annot in c.annotations])`,
`base/strings/annotated.jl:309-310`. -/
def annotatedstringAC (c : AC) : SJl AS := do
  let s ← stringOfChars [c.char]
  pure ⟨s, c.anns.map (RA.ofAnn (urange (ix 1) (ix (ncodeunitsC c))))⟩

/-- `AnnotatedString(s::SubString{<:AnnotatedString}) = annotatedstring(s)`,
`base/strings/annotated.jl:312`. -/
def ofSub (s : ASub) : SJl AS := annotatedstring [.sub s]

/-! ## `repeat` and `reverse` -/

/-- `one(AnnotatedString) = convert(AnnotatedString, "")`, the empty
`AnnotatedString{String}` without annotations. -/
def oneAS : AS := ⟨JStr.empty, []⟩

/-- `repeat(str::AnnotatedString, r::Integer)`, `base/strings/annotated.jl:314-335`.
`allequal(a -> a.region, str.annotations)` compares regions with `==`
(`rangeEq`). The loop `for offset in 0:len:(r-1)*len` has the `r` offsets
`k * len`, `0 ≤ k < r`, when `len > 0` (`r * len` fits in an `Int` because
`repeat(str.string, r)` succeeded); a zero step throws
`ArgumentError("step cannot be zero")` (`base/range.jl`). -/
def repeatAS (str : AS) (r : JInt64) : SJl AS :=
  if r.val = 0 then .ok oneAS
  else if r.val = 1 then .ok str
  else do
    let unannot ← repeatStr str.str r
    let len := ncodeunits str.str
    let fullregion := urange (firstindex str.str) (lastindex str.str)
    match str.anns with
    | [] => pure ⟨unannot, []⟩
    | a0 :: _ =>
      if str.anns.all (fun a => rangeEq a.region a0.region) && rangeEq a0.region fullregion then
        let newfullregion := urange (firstindex unannot) (lastindex unannot)
        pure ⟨unannot, str.anns.map (·.setR newfullregion)⟩
      else if len.val = 0 then .error (.jl (.argumentError "step cannot be zero"))
      else
        pure ⟨unannot, (List.range r.val.toNat).flatMap fun (k : Nat) =>
          str.anns.map (shiftRA (ix ((k : Int) * len.val)))⟩

/-- `repeat(str::SubString{<:AnnotatedString}, r::Integer) = repeat(AnnotatedString(str), r)`,
`base/strings/annotated.jl:337-338`. -/
def repeatSub (str : ASub) (r : JInt64) : SJl AS := do
  let a ← ofSub str
  repeatAS a r

/-- `repeat(c::AnnotatedChar, r::Integer)`, `base/strings/annotated.jl:340-344`. -/
def repeatAC (c : AC) (r : JInt64) : SJl AS := do
  let str ← repeatChar c.char r
  let fullregion := urange (firstindex str) (lastindex str)
  pure ⟨str, c.anns.map (RA.ofAnn fullregion)⟩

/-- `reverse(s::AnnotatedString)`, `base/strings/annotated.jl:346-355`. -/
def reverseAS (s : AS) : AS :=
  let lastind := lastindex s.str
  ⟨Strings.reverse s.str, s.anns.map fun annot =>
    annot.setR (urange (ix 1 + lastind - annot.hi) (ix 1 + lastind - annot.lo))⟩

/-- `reverse(s::SubString{<:AnnotatedString}) = reverse(AnnotatedString(s))`,
`base/strings/annotated.jl:358`. -/
def reverseSub (s : ASub) : SJl AS := do
  let a ← ofSub s
  pure (reverseAS a)

/-! ## `annotate!` -/

/-- `_annotate!(annlist, region, label, value)`, `base/strings/annotated.jl:364-370`:
for `value === nothing`, `deleteat!(annlist, findall(ann -> ann.region == region &&
ann.label === label, annlist))`; otherwise push the new annotation. -/
def annotateBang (annlist : List RA) (region : Region) (label : Nat) (value : Val) : List RA :=
  match value with
  | none => annlist.filter fun ann => !(rangeEq ann.region region && ann.label == label)
  | some _ => annlist ++ [⟨region.1, region.2, label, value⟩]

/-- `annotate!(s::AnnotatedString, range, label, val)`, `base/strings/annotated.jl:382-383`. -/
def annotateAS (s : AS) (range : Region) (label : Nat) (val : Val) : AS :=
  { s with anns := annotateBang s.anns range label val }

/-- `annotate!(ss::AnnotatedString, label, val) = annotate!(ss, firstindex(ss):lastindex(ss), label, val)`,
`base/strings/annotated.jl:385-386`. -/
def annotateASAll (s : AS) (label : Nat) (val : Val) : AS :=
  annotateAS s (urange (firstindex s.str) (lastindex s.str)) label val

/-- `r .+ x` and `x .+ r` for a `UnitRange{Int}` and an `Int`: `first + x : last + x`. -/
def shiftRegion (x : JInt64) (r : Region) : Region := urange (x + r.1) (x + r.2)

/-- `annotate!(s::SubString{<:AnnotatedString}, range, label, val) =
(annotate!(s.string, s.offset .+ (range), label, val); s)`,
`base/strings/annotated.jl:388-389`: the parent is mutated. -/
def annotateSub (s : ASub) (range : Region) (label : Nat) (val : Val) : ASub :=
  { s with parent := annotateAS s.parent (shiftRegion s.offset range) label val }

/-- `annotate!(s::SubString{<:AnnotatedString}, label, val) =
(annotate!(s.string, s.offset .+ (1:s.ncodeunits), label, val); s)`,
`base/strings/annotated.jl:391-392`. -/
def annotateSubAll (s : ASub) (label : Nat) (val : Val) : ASub :=
  { s with parent := annotateAS s.parent (shiftRegion s.offset (urange (ix 1) s.ncu)) label val }

/-- `annotate!(c::AnnotatedChar, label, value) = (push!(c.annotations,
Annotation((; label, value))); c)`, `base/strings/annotated.jl:399-400`. -/
def annotateAC (c : AC) (label : Nat) (value : Val) : AC :=
  { c with anns := c.anns ++ [⟨label, value⟩] }

/-! ## `annotated_chartransform` -/

/-- The `for c in str.string` loop of `annotated_chartransform`,
`base/strings/annotated.jl:482-494`. `f st c` is `f(c)` (stateless form,
`σ = Unit`) or `f(c, state)`. `write(outstr, c)` writes the code units of the
new character and returns their number; `offsets` is the vector of
`bytepos => cumulative change` pairs. -/
def actLoop {σ : Type} (f : σ → UInt32 → RegexUnicode.Uni.UJl (UInt32 × σ)) :
    List UInt32 → σ → JInt64 → List UInt8 → List (JInt64 × JInt64) →
      RegexUnicode.Uni.UJl (List UInt8 × List (JInt64 × JInt64))
  | [], _, _, out, offs => .ok (out, offs)
  | c :: cs, st, bytepos, out, offs =>
    match f st c with
    | .error e => .error e
    | .ok (c', st') =>
      let oldnb := ncodeunitsChar c
      let bytepos := bytepos + ix oldnb
      let nb := ncodeunitsChar c'
      let last := (offs.getLast?.map (·.2)).getD (ix 0)
      let offs := if nb ≠ oldnb then offs ++ [(bytepos, last + ix nb - ix oldnb)] else offs
      actLoop f cs st' bytepos (out ++ charBytes c') offs

/-- `last(offsets[findlast(<=(x) ∘ first, offsets)::Int])`: `none` when no entry
qualifies (the `::Int` assertion then throws `TypeError`). -/
def offsetAt (offs : List (JInt64 × JInt64)) (x : JInt64) : Option JInt64 :=
  ((offs.filter fun p => decide (p.1.val ≤ x.val)).getLast?).map (·.2)

/-- The `for annot in str.annotations` loop, `base/strings/annotated.jl:495-500`. -/
def actAnns (offs : List (JInt64 × JInt64)) : List RA → RegexUnicode.Uni.UJl (List RA)
  | [] => .ok []
  | a :: as =>
    match offsetAt offs a.lo, offsetAt offs a.hi with
    | some so, some eo =>
      match actAnns offs as with
      | .error e => .error e
      | .ok rest => .ok (a.setR (urange (a.lo + so) (a.hi + eo)) :: rest)
    | _, _ => .error .typeError

/-- The end of `annotated_chartransform`, `base/strings/annotated.jl:495-501`: the
annotations loop, then `AnnotatedString(takestring!(outstr), annots)`. -/
def actFinish (offs : List (JInt64 × JInt64)) (anns : List RA) (out : List UInt8) :
    RegexUnicode.Uni.UJl AS :=
  match actAnns offs anns with
  | .error e => .error e
  | .ok annots => if h : out.length < 2 ^ 62 then .ok ⟨⟨out, h⟩, annots⟩ else .error (.str .outOfMemory)

/-- `bytepos = firstindex(str) - 1`, `base/strings/annotated.jl:481`. -/
def actStart (str : AS) : JInt64 := firstindex str.str - ix 1

/-- The character loop with the exact initial state used by `annotated_chartransform`. -/
def actRun {σ : Type} (f : σ → UInt32 → RegexUnicode.Uni.UJl (UInt32 × σ)) (str : AS) (st : σ) :=
  actLoop f (chars str.str) st (actStart str) [] [(actStart str, ix 0)]

/-- `annotated_chartransform(f, str::AnnotatedString, state=nothing)`,
`base/strings/annotated.jl:477-502`. -/
def annotatedChartransform {σ : Type} (f : σ → UInt32 → RegexUnicode.Uni.UJl (UInt32 × σ)) (str : AS)
    (st : σ) : RegexUnicode.Uni.UJl AS :=
  match actRun f str st with
  | .error e => .error e
  | .ok (out, offs) => actFinish offs str.anns out

/-! ## `RegionIterator` -/

/-- `RegionIterator{S}`, `base/strings/annotated.jl:504-508`. -/
structure RegionIter where
  str : JStr
  regions : List Region
  annotations : List (List Ann)

/-- `Base.length(si::RegionIterator) = length(si.regions)`, `base/strings/annotated.jl:510`. -/
def riLength (si : RegionIter) : Nat := si.regions.length

/-- `Base.iterate(si::RegionIterator, i::Integer=1)`, `base/strings/annotated.jl:512-516`.
The two element reads are under `@inbounds`; a read outside `1:length` of either
vector is the explicit out-of-bounds result `.error boundsErr` (an unchecked
access in Julia). `SubString(si.str, r)` is `SubString(si.str, first(r), last(r))`. -/
def riIterate (si : RegionIter) (i : JInt64) : SJl (Option ((JSub × List Ann) × JInt64)) :=
  if i.val ≤ si.regions.length then
    if 1 ≤ i.val ∧ i.val ≤ si.annotations.length then do
      let r := si.regions.getD (i.val.toNat - 1) (ix 0, ix 0)
      let sub ← substring si.str r.1 r.2
      pure (some ((sub, si.annotations.getD (i.val.toNat - 1) []), i + ix 1))
    else .error boundsErr
  else .ok none

/-- `Base.eltype(::RegionIterator{S}) = Tuple{SubString{S}, Vector{Annotation}}`,
`base/strings/annotated.jl:518-519`, as the pair of the element types. -/
def riEltype (S : JTy) : JTy × String := (.subString S, "Vector{Annotation}")

/-! ## `annotation_events` -/

/-- `annotation_events(s::AbstractString, annots, subregion)`,
`base/strings/annotated.jl:595-606`: the region-only `StringUtil` model (values
play no role). -/
def annotationEvents (s : JStr) (annots : List RA) (sub : Region) : SJl (List StringUtil.Event) :=
  StringUtil.annotationEvents s (annots.map RA.toU) sub

/-- `annotation_events(s::AnnotatedString, subregion) =
annotation_events(s.string, annotations(s), subregion)`, `base/strings/annotated.jl:608-609`. -/
def annotationEventsAS (s : AS) (sub : Region) : SJl (List StringUtil.Event) :=
  annotationEvents s.str (annotations s) sub

end JuliaLean.StringsCovB.Ann
