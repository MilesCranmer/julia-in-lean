import JuliaLean.RegexUnicode.UniGraphemes
import JuliaLean.StringsCovB.Ann

/-!
# `base/strings/unicode.jl`

Models of the methods of `base/strings/unicode.jl` (master `bbfa0ce4150`) not
already modelled in `JuliaLean.RegexUnicode`: `isvalid`, the utf8proc wrappers
and `normalize`, `textwidth`, the category functions and character predicates,
the `AnnotatedChar`/`AnnotatedString` case mappings, `uppercasefirst` and
`lowercasefirst`, `isgraphemebreak` and the `GraphemeIterator` methods.

* A `Char` is its 32-bit bit pattern; utf8proc's table functions are the
  `RegexUnicode.Uni.Utf8proc` primitive, extended by `Ext` with the other entry
  points Julia calls.
* `utf8proc_decompose_custom` applies the callback to each decoded code point and
  decomposes the result (utf8proc.h); canonical reordering does not change the
  number of code points and is not modelled here (it is in
  `RegexUnicode.UniNormalize`). A callback may keep state between calls: it is a
  function of a state `σ`.
-/

namespace JuliaLean.StringsCovB.Uni

open JuliaLean JuliaLean.Strings
open JuliaLean.RegexUnicode.Uni (Utf8proc UErr UJl liftS lowercaseChar uppercaseChar titlecaseChar
  categoryCode unsafeCodepoint isletterChar isgraphemebreakBang NormKw normalizeFlags STABLE COMPOSE
  DECOMPOSE COMPAT)

/-- The other utf8proc entry points. -/
structure Ext where
  /-- `utf8proc_charwidth(c)` -/
  charwidth : UInt32 → Int
  /-- `utf8proc_islower(c) != 0` -/
  islower : UInt32 → Bool
  /-- `utf8proc_isupper(c) != 0` -/
  isupper : UInt32 → Bool
  /-- `unsafe_string(utf8proc_category_string(c))` -/
  catString : UInt32 → List UInt8
  /-- `utf8proc_grapheme_break(c1, c2)` -/
  gb : UInt32 → UInt32 → Bool
  /-- `utf8proc_reencode(buffer, nwords, options)` on the code points of the buffer:
  the UTF-8 bytes or a negative error code. -/
  reencode : List UInt32 → Nat → Except Int (List UInt8)

/-! ## `isvalid`, `base/strings/unicode.jl:58-63` -/

/-- `isvalid(c::AbstractChar)`, `base/strings/unicode.jl:58`, with `Char` comparisons
on bit patterns: `'\ud7ff'` is `0xed9fbf00`, `'\ue000'` is `0xee808000`,
`'\U10ffff'` is `0xf48fbfbf`. -/
def isvalidC (c : UInt32) : Bool :=
  !ismalformed c && !isoverlong c && (decide (c ≤ 0xed9fbf00) || (decide (0xee808000 ≤ c) && decide (c ≤ 0xf48fbfbf)))

/-- `isvalid(::Type{<:AbstractChar}, c::Unsigned)`, `base/strings/unicode.jl:59`. -/
def isvalidU (c : Nat) : Bool := decide (c ≤ 0xd7ff) || (decide (0xe000 ≤ c) && decide (c ≤ 0x10ffff))

/-- `isvalid(::Type{T}, c::Integer) = isvalid(T, Unsigned(c))`, `base/strings/unicode.jl:60`:
`Unsigned(c)` throws `InexactError` for a negative `c`. -/
def isvalidI (c : Int) : Jl Bool :=
  if c < 0 then .error (.inexactError "UInt64") else .ok (isvalidU c.toNat)

/-- `isvalid(::Type{<:AbstractChar}, c::AbstractChar) = isvalid(c)`, `:61`. -/
def isvalidTC (c : UInt32) : Bool := isvalidC c

/-- `isvalid(::Type{Union{}}, value) = false`, `:62`. -/
def isvalidUnion {α : Type} (_value : α) : Bool := false

/-- `isvalid(::Type{Union{}}, slurp...)` throws `MethodError`, `:63`. -/
def isvalidUnionSlurp {α : Type} (_slurp : List α) : Jl Bool := .error (.methodError "isvalid")

/-! ## utf8proc wrappers, `base/strings/unicode.jl:153-199` -/

/-- Errors of `utf8proc_map`: a Julia exception, or a read beyond the buffer
(undefined behaviour in Julia). -/
inductive MErr where
  | u (e : UErr)
  | outOfBounds
  deriving DecidableEq, Repr

/-- `utf8proc_error(result) = error(unsafe_string(utf8proc_errmsg(result)))`, `:153`. -/
def utf8procError {α : Type} (_result : Int) : Except MErr α := .error (.u .errorException)

/-- `utf8proc_custom_func(codepoint, callback) = UInt32(callback(codepoint))::UInt32`, `:156-157`:
the callback's result (an integer or a code point) converted to `UInt32`. -/
def utf8procCustomFunc {σ : Type} (callback : σ → UInt32 → Int × σ) (st : σ) (codepoint : UInt32) :
    Except MErr (UInt32 × σ) :=
  let (r, st) := callback st codepoint
  if 0 ≤ r ∧ r < 2 ^ 32 then .ok (UInt32.ofNat r.toNat, st) else .error (.u (.str (.jl (.inexactError "UInt32"))))

/-- The code points `utf8proc_decompose_custom` produces for the code points `cps`
of the string: each is passed through the callback and decomposed. -/
def decompLoop {σ : Type} (P : Utf8proc) (options : Nat) (callback : σ → UInt32 → Int × σ) :
    List UInt32 → σ → Except MErr (List UInt32 × σ)
  | [], st => .ok ([], st)
  | c :: cs, st =>
    match utf8procCustomFunc callback st c with
    | .error e => .error e
    | .ok (c', st) =>
      match P.decomposeChar c' options with
      | .error r => utf8procError r
      | .ok d =>
        match decompLoop P options callback cs st with
        | .error e => .error e
        | .ok (ds, st) => .ok (d ++ ds, st)

/-- The code points of `s` that utf8proc decodes (a String argument of `utf8proc_map`
is valid UTF-8 whenever decoding succeeds; an invalid one is `UTF8PROC_ERROR_INVALIDUTF8`). -/
def cpsOf (s : JStr) : Except MErr (List UInt32) :=
  (chars s).mapM fun c => match codepoint c with
    | .ok u => if ismalformed c || isoverlong c then utf8procError (-3) else .ok u
    | .error _ => utf8procError (-3)

/-- `utf8proc_decompose(str, options, buffer, nwords, chartransform)`, both methods
(`:159-171`; `identity` is the callback `c ↦ c`): the number of code points of the
result (`ret`), and the first `nwords` of them stored in the buffer. -/
def utf8procDecompose {σ : Type} (P : Utf8proc) (s : JStr) (options : Nat) (nwords : Nat)
    (callback : σ → UInt32 → Int × σ) (st : σ) : Except MErr (Nat × List UInt32 × σ) := do
  let cps ← cpsOf s
  let (ds, st) ← decompLoop P options callback cps st
  pure (ds.length, ds.take nwords, st)

/-- `utf8proc_map(str::String, options, chartransform)`, `base/strings/unicode.jl:173-180`:
size the buffer with a first decomposition, decompose again into it, then
`utf8proc_reencode(buffer, nwords, options)` reads `nwords` entries of a buffer of
the first size. -/
def utf8procMap {σ : Type} (P : Utf8proc) (E : Ext) (s : JStr) (options : Nat)
    (callback : σ → UInt32 → Int × σ) (st : σ) : Except MErr JStr := do
  let (nwords, _, st) ← utf8procDecompose P s options 0 callback st
  let bufWords := nwords
  let (nwords, buffer, _) ← utf8procDecompose P s options nwords callback st
  if nwords > bufWords then throw .outOfBounds
  match E.reencode buffer options with
  | .error r => utf8procError r
  | .ok bytes =>
    if h : bytes.length < 2 ^ 62 then pure ⟨bytes, h⟩ else throw (.u (.str .outOfMemory))

/-- `utf8proc_map(s::AbstractString, flags, chartransform) = utf8proc_map(String(s), ...)`,
`base/strings/unicode.jl:199`, for a SubString. -/
def utf8procMapSub {σ : Type} (P : Utf8proc) (E : Ext) (s : JSub) (options : Nat)
    (callback : σ → UInt32 → Int × σ) (st : σ) : Except MErr JStr :=
  utf8procMap P E s.view options callback st

/-- `normalize(s; kwargs...)`, `base/strings/unicode.jl:202-241`: the flags of
`RegexUnicode.Uni.normalizeFlags` (which mirrors the keyword checks), then `utf8proc_map`. -/
def normalizeKw {σ : Type} (P : Utf8proc) (E : Ext) (s : JStr) (k : NormKw)
    (callback : σ → UInt32 → Int × σ) (st : σ) : Except MErr JStr :=
  match normalizeFlags k with
  | .error e => .error (.u (.str (.jl e)))
  | .ok flags => utf8procMap P E s flags callback st

/-- The normal forms of `normalize(s, nf::Symbol)`. -/
inductive NF where
  | nfc | nfd | nfkc | nfkd | other

/-- `normalize(s, nf::Symbol)`, `base/strings/unicode.jl:243-251`. -/
def nfFlags : NF → Jl Nat
  | .nfc => .ok (STABLE ||| COMPOSE)
  | .nfd => .ok (STABLE ||| DECOMPOSE)
  | .nfkc => .ok (STABLE ||| COMPOSE ||| COMPAT)
  | .nfkd => .ok (STABLE ||| DECOMPOSE ||| COMPAT)
  | .other => .error (.argumentError "is not one of :NFC, :NFD, :NFKC, :NFKD")

def normalizeNf (P : Utf8proc) (E : Ext) (s : JStr) (nf : NF) : Except MErr JStr :=
  match nfFlags nf with
  | .error e => .error (.u (.str (.jl e)))
  | .ok flags => utf8procMap P E s flags (fun (u : Unit) c => ((c.toNat : Int), u)) ()

/-! ## `textwidth`, `base/strings/unicode.jl:270-300` -/

/-- `textwidth(c::Char)`, `base/strings/unicode.jl:272-282`. -/
def textwidthChar (E : Ext) (c : UInt32) : Int :=
  let u := c
  let b := bswap32 u
  if b < 0x7f then (if b ≥ 0x20 then 1 else 0)
  else if ismalformed c || isOverlongEnc u then 1
  else E.charwidth (unsafeCodepoint c)

/-- `textwidth(c::AbstractChar) = textwidth(Char(c)::Char)`, `:270`, for an
`AnnotatedChar` (`Char(c) = c.char`). -/
def textwidthAC (E : Ext) (c : Ann.AC) : Int := textwidthChar E c.char

/-- `mapreduce(textwidth, +, s; init=0)`: `textwidth(s::AbstractString)`, `(s::String)`
and `(s::SubString{String})`, `:295-298`. The sum stays far below `typemax(Int)`
(a string has fewer than `2^62` characters of width at most `2^31`). -/
def textwidthStr (E : Ext) (s : JStr) : Int := (chars s).foldl (fun acc c => acc + textwidthChar E c) 0

def textwidthSub (E : Ext) (s : JSub) : Int := textwidthStr E s.view

/-- `textwidth(s::AnnotatedString) = textwidth(s.string)`, `:300`. -/
def textwidthAS (E : Ext) (s : Ann.AS) : Int := textwidthStr E s.str

/-! ## Case mappings of `AnnotatedChar`, `:321`, `:342`, `:367` -/

def lowercaseAC (P : Utf8proc) (c : Ann.AC) : UJl Ann.AC := do
  let c' ← lowercaseChar P c.char
  pure ⟨c', c.anns⟩

def uppercaseAC (P : Utf8proc) (c : Ann.AC) : UJl Ann.AC := do
  let c' ← uppercaseChar P c.char
  pure ⟨c', c.anns⟩

def titlecaseAC (P : Utf8proc) (c : Ann.AC) : UJl Ann.AC := do
  let c' ← titlecaseChar P c.char
  pure ⟨c', c.anns⟩

/-! ## Categories, `base/strings/unicode.jl:372-405` -/

/-- `category_code(x::Integer)`, `base/strings/unicode.jl:379-381`: `UInt32(x)` throws
`InexactError` for a negative `x`. -/
def categoryCodeInt (P : Utf8proc) (x : Int) : UJl Nat :=
  if x ≤ 0x10ffff then
    if 0 ≤ x then .ok (P.category (UInt32.ofNat x.toNat)) else .error (.str (.jl (.inexactError "trunc")))
  else .ok 30

/-- `"Ma"` and `"In"`. -/
def strMa : List UInt8 := [0x4d, 0x61]
def strIn : List UInt8 := [0x49, 0x6e]

/-- `category_abbrev(c::AbstractChar)`, `base/strings/unicode.jl:384-388` (`UInt32(c)`). -/
def categoryAbbrevAC (E : Ext) (c : UInt32) : UJl (List UInt8) :=
  if ismalformed c then .ok strMa
  else if !decide (c ≤ 0xf48fbfbf) then .ok strIn
  else do
    let u ← liftS (codepoint c)
    pure (E.catString u)

/-- `category_abbrev(c::Char)`, `base/strings/unicode.jl:392-396` (`unsafe_codepoint(c)`). -/
def categoryAbbrev (E : Ext) (c : UInt32) : List UInt8 :=
  if ismalformed c then strMa
  else if !decide (c ≤ 0xf48fbfbf) then strIn
  else E.catString (unsafeCodepoint c)

/-- `category_strings`, `base/strings/unicode.jl:100-133`: 32 names (the first is
`"Other, not assigned"`); only their positions matter here. -/
def categoryStrings : List Nat := List.range 32

/-- `category_string(c) = category_strings[category_code(c)+1]` (checked), `:400`, for an
integer argument. -/
def categoryStringInt (P : Utf8proc) (x : Int) : UJl Nat := do
  let k ← categoryCodeInt P x
  if k + 1 ≤ categoryStrings.length then pure (categoryStrings.getD k 0) else throw (.str boundsErr)

/-- `category_string(c::Char) = @inbounds category_strings[category_code(c)+1]`, `:403`:
`none` marks an out-of-bounds `@inbounds` read. -/
def categoryString (P : Utf8proc) (c : UInt32) : Option Nat :=
  let k := categoryCode P c
  if k + 1 ≤ categoryStrings.length then some (categoryStrings.getD k 0) else none

/-- `isassigned(c) = UTF8PROC_CATEGORY_CN < category_code(c) <= UTF8PROC_CATEGORY_CO`, `:405`,
for a `Char` and for an integer. -/
def isassignedC (P : Utf8proc) (c : UInt32) : Bool := decide (0 < categoryCode P c) && decide (categoryCode P c ≤ 29)

def isassignedInt (P : Utf8proc) (x : Int) : UJl Bool := do
  let k ← categoryCodeInt P x
  pure (decide (0 < k) && decide (k ≤ 29))

/-! ## Character predicates, `base/strings/unicode.jl:429-659` -/

/-- `islowercase(c)`, `:429-434`. -/
def islowercaseC (E : Ext) (c : UInt32) : Bool := if ismalformed c then false else E.islower (unsafeCodepoint c)

/-- `isuppercase(c)`, `:458-463`. -/
def isuppercaseC (E : Ext) (c : UInt32) : Bool := if ismalformed c then false else E.isupper (unsafeCodepoint c)

/-- `iscased(c)`, `:472-477`: `LU = 1`, `LT = 3`, `LL = 2`. -/
def iscasedC (P : Utf8proc) (c : UInt32) : Bool :=
  let cat := categoryCode P c
  cat == 1 || cat == 3 || cat == 2

/-- `isdigit(c) = (c >= '0') & (c <= '9')`, `:499`. -/
def isdigitC (c : UInt32) : Bool := decide (c ≥ 0x30000000) && decide (c ≤ 0x39000000)

/-- `isnumeric(c)`: `ND = 9 ≤ category_code(c) ≤ NO = 11`, `:549`. -/
def isnumericC (P : Utf8proc) (c : UInt32) : Bool := decide (9 ≤ categoryCode P c) && decide (categoryCode P c ≤ 11)

/-- `ispunct(c)`: `PC = 12 ≤ category_code(c) ≤ PO = 18`, `:594`. -/
def ispunctC (P : Utf8proc) (c : UInt32) : Bool := decide (12 ≤ categoryCode P c) && decide (categoryCode P c ≤ 18)

/-- `isspace(c)`, `:624-626`: `' '`, `'\t':'\r'`, `'\u85'` (`0xc2850000`), or from
`'\ua0'` (`0xc2a00000`) on, a category `ZS = 23 .. ZP = 25`. -/
def isspaceC (P : Utf8proc) (c : UInt32) : Bool :=
  c == 0x20000000 || (decide (0x09000000 ≤ c) && decide (c ≤ 0x0d000000)) || c == 0xc2850000 ||
    (decide (0xc2a00000 ≤ c) && decide (23 ≤ categoryCode P c) && decide (categoryCode P c ≤ 25))

/-- `isprint(c)`: `LU = 1 ≤ category_code(c) ≤ ZS = 23`, `:642`. -/
def isprintC (P : Utf8proc) (c : UInt32) : Bool := decide (1 ≤ categoryCode P c) && decide (categoryCode P c ≤ 23)

/-- `isxdigit(c)`, `:659`. -/
def isxdigitC (c : UInt32) : Bool :=
  (decide (0x30000000 ≤ c) && decide (c ≤ 0x39000000)) || (decide (0x61000000 ≤ c) && decide (c ≤ 0x66000000)) ||
    (decide (0x41000000 ≤ c) && decide (c ≤ 0x46000000))

/-! ## `AnnotatedString` case mappings, `base/strings/unicode.jl:677-832` -/

/-- A stateless character map as an `annotated_chartransform` function. -/
def stateless (f : UInt32 → UJl UInt32) : Unit → UInt32 → UJl (UInt32 × Unit) :=
  fun st c => (f c).map (·, st)

/-- `uppercase(s::AnnotatedString) = annotated_chartransform(uppercase, s)`, `:677`. -/
def uppercaseAS (P : Utf8proc) (s : Ann.AS) : UJl Ann.AS := Ann.annotatedChartransform (stateless (uppercaseChar P)) s ()

/-- `uppercase(s::SubString{<:AnnotatedString}) = uppercase(AnnotatedString(s))`, `:678`. -/
def uppercaseSub (P : Utf8proc) (s : Ann.ASub) : UJl Ann.AS := do
  let a ← liftS (Ann.ofSub s)
  uppercaseAS P a

/-- `lowercase(s::AnnotatedString) = annotated_chartransform(lowercase, s)`, `:694`. -/
def lowercaseAS (P : Utf8proc) (s : Ann.AS) : UJl Ann.AS := Ann.annotatedChartransform (stateless (lowercaseChar P)) s ()

/-- `lowercase(s::SubString{<:AnnotatedString})`, `:695`. -/
def lowercaseSub (P : Utf8proc) (s : Ann.ASub) : UJl Ann.AS := do
  let a ← liftS (Ann.ofSub s)
  lowercaseAS P a

/-- The state of `titlecase(s::AnnotatedString)`: `startword`, `state[]`, `c0`. -/
abbrev TState := Bool × Int32 × UInt32

/-- The `do c, state ... end` block of `titlecase(s::AnnotatedString)`, `:748-758`. -/
def titleStep (P : Utf8proc) (wordsep : UInt32 → Bool) (strict : Bool) (st : TState) (c : UInt32) :
    UJl (UInt32 × TState) := do
  let (startword, gst, c0) := st
  let (b, gst) ← isgraphemebreakBang P gst c0 c
  if b && wordsep c then pure (c, (true, gst, c))
  else
    let cnew ← if startword then titlecaseChar P c else if strict then lowercaseChar P c else pure c
    pure (cnew, (false, gst, c))

/-- `titlecase(s::AnnotatedString; wordsep, strict)`, `base/strings/unicode.jl:745-759`:
the initial state is `startword = true`, `state = Ref{Int32}(0)`, `c0 = '\0'`. -/
def titlecaseAS (P : Utf8proc) (wordsep : UInt32 → Bool) (strict : Bool) (s : Ann.AS) : UJl Ann.AS :=
  Ann.annotatedChartransform (titleStep P wordsep strict) s (true, 0, 0)

/-- `titlecase(s::SubString{<:AnnotatedString}; ...)`, `:761-762`. -/
def titlecaseSub (P : Utf8proc) (wordsep : UInt32 → Bool) (strict : Bool) (s : Ann.ASub) : UJl Ann.AS := do
  let a ← liftS (Ann.ofSub s)
  titlecaseAS P wordsep strict a

/-- `uppercasefirst(s::AbstractString)`, `:780-786`, and `lowercasefirst`, `:814-820`, with
the character map `f` (`titlecase` resp. `lowercase`). -/
def mapfirstStr (f : UInt32 → UJl UInt32) (s : JStr) : UJl JStr := do
  if s.bytes.isEmpty then return JStr.empty
  let c ← liftS (getindex s (ix 1))
  let c' ← f c
  if c == c' then return s
  let k ← liftS (nextind s (ix 1))
  let rest ← liftS (substring s k (lastindex s))
  liftS (stringOfChars [c'] >>= fun a => if h : (a.bytes ++ rest.view.bytes).length < 2 ^ 62 then
    .ok ⟨a.bytes ++ rest.view.bytes, h⟩ else .error .outOfMemory)

def uppercasefirstStr (P : Utf8proc) (s : JStr) : UJl JStr := mapfirstStr (titlecaseChar P) s
def lowercasefirstStr (P : Utf8proc) (s : JStr) : UJl JStr := mapfirstStr (lowercaseChar P) s

/-- The `do c, state ... end` block of `uppercasefirst(s::AnnotatedString)` and
`lowercasefirst(s::AnnotatedString)`, `:789-797`, `:823-831`. -/
def firstStep (f : UInt32 → UJl UInt32) (st : Bool) (c : UInt32) : UJl (UInt32 × Bool) :=
  if st then (f c).map (·, false) else .ok (c, st)

def uppercasefirstAS (P : Utf8proc) (s : Ann.AS) : UJl Ann.AS :=
  Ann.annotatedChartransform (firstStep (titlecaseChar P)) s true
def lowercasefirstAS (P : Utf8proc) (s : Ann.AS) : UJl Ann.AS :=
  Ann.annotatedChartransform (firstStep (lowercaseChar P)) s true

/-- `uppercasefirst(s::SubString{<:AnnotatedString})`, `:798`, and `lowercasefirst`, `:832`. -/
def uppercasefirstSub (P : Utf8proc) (s : Ann.ASub) : UJl Ann.AS := do
  let a ← liftS (Ann.ofSub s)
  uppercasefirstAS P a
def lowercasefirstSub (P : Utf8proc) (s : Ann.ASub) : UJl Ann.AS := do
  let a ← liftS (Ann.ofSub s)
  lowercasefirstAS P a

/-! ## Graphemes, `base/strings/unicode.jl:837-896` -/

/-- `isgraphemebreak(c1, c2)`, `:837-839`: the `ccall` converts both characters with
`UInt32(c)`. -/
def isgraphemebreakC (E : Ext) (c1 c2 : UInt32) : UJl Bool :=
  if ismalformed c1 || ismalformed c2 then .ok true
  else do
    let u1 ← liftS (codepoint c1)
    let u2 ← liftS (codepoint c2)
    pure (E.gb u1 u2)

/-- `GraphemeIterator{S}(s)`; `graphemes(s) = GraphemeIterator{typeof(s)}(s)`, `:858`. -/
structure GI where
  s : JStr
  deriving DecidableEq

def graphemes (s : JStr) : GI := ⟨s⟩

/-- `eltype(::Type{GraphemeIterator{S}}) = SubString{S}` and, for `S = SubString{T}`,
`SubString{T}`, `:860-861`. -/
def giEltype (S : Ann.JTy) : Ann.JTy :=
  match S with
  | .subString T => .subString T
  | T => .subString T

/-- `length(g)`, `:863-872`, and `iterate(g, (state, i))`, `:874-890`: the loops of
`RegexUnicode.Uni.gLength` and `RegexUnicode.Uni.gIterate`. -/
def giLength (P : Utf8proc) (g : GI) : UJl JInt64 := RegexUnicode.Uni.gLength P g.s
def giIterate (P : Utf8proc) (g : GI) (st : Int32) (i : JInt64) : UJl (Option (JSub × Int32 × JInt64)) :=
  RegexUnicode.Uni.gIterate (RegexUnicode.Uni.gops P g.s) st i

/-- `==(g1, g2) = g1.s == g2.s`, `hash(g, h) = hash(g.s, h)`,
`isless(g1, g2) = isless(g1.s, g2.s)`, `:892-894`. -/
def giEq (g1 g2 : GI) : Bool := g1.s == g2.s
def giHash (hs : JStr → UInt64 → UInt64) (g : GI) (h : UInt64) : UInt64 := hs g.s h
def giIsless (g1 g2 : GI) : Bool := decide (Strings.cmp g1.s g2.s < 0)

/-- `show(io, g)`, `:896`: `"length-$(length(g)) GraphemeIterator{$S} for \"$(g.s)\""`,
with the printed length and type name as parameters. -/
def giShow (lenStr typeName : List UInt8) (g : GI) : List UInt8 :=
  "length-".toUTF8.toList ++ lenStr ++ " GraphemeIterator{".toUTF8.toList ++ typeName ++
    "} for \"".toUTF8.toList ++ g.s.bytes ++ "\"".toUTF8.toList

end JuliaLean.StringsCovB.Uni
