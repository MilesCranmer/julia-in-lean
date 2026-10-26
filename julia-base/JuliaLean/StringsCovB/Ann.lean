import JuliaLean.Strings.Theory
import JuliaLean.StringUtil.Annotated
import JuliaLean.RegexUnicode.UniBasic

/-!
# `base/strings/annotated.jl`

Models of the methods of `base/strings/annotated.jl` (master `bbfa0ce4150`).

* `AnnotatedString{String}` is `AS`: its `String` and its vector of
  `RegionAnnotation`s (`base/strings/annotated.jl:3-4,64-67`). An annotation's
  `Symbol` label is a `Nat`; its value is `Option Nat`, with `none` for
  `nothing` (the only value `_annotate!` distinguishes) and `some n` for any
  other value, compared with `==`.
* `AnnotatedChar{Char}` is `AC`: its `Char` bit pattern (the String model's
  `UInt32` encoding) and its `Annotation`s.
* `SubString{AnnotatedString{String}}` is `ASub`: parent, `offset`, `ncodeunits`.
* Regions are `UnitRange{Int}` values `(first, last)` built with
  `StringUtil.urange` (`unitrange_last`), so empty ranges are normalized as in
  Julia; `rangeEq` is `==` on `UnitRange`s (`base/range.jl:1141-1145`), under
  which all empty ranges are equal.
* A mutating method returns the mutated value.
* Only the String instantiation `S = String`, `C = Char` is modelled; the
  methods are generic in `S` and `C` and do not inspect them.
-/

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
