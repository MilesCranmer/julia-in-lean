import JuliaLean.Core
import JuliaLean.base.char
import JuliaLean.base.int
import JuliaLean.base.rational
import JuliaLean.base.strings.basic
import JuliaLean.Runtime.Strings
import JuliaLean.base.reduce
import JuliaLean.base.iterators
import JuliaLean.base.strings.annotated

namespace JuliaLean.base.strings.unicode

open JuliaLean
open JuliaLean.base.char
open JuliaLean.base.strings.basic
open JuliaLean.base.rational

abbrev JString := JuliaLean.Strings.JStr
abbrev Index := JuliaLean.base.strings.basic.Index


abbrev UResult (α : Type) := Except UnicodeError α

def liftChar {α : Type} : CharResult α → UResult α
  | .ok value => .ok value
  | .error (.invalidChar _) => .error .invalidChar
  | .error (.codePointError _) => .error .codePointError
  | .error (.unicodeError error) => .error error
  | .error .boundsError => .error .boundsError
  | .error (.foreign error) => .error (.jl error)
  | .error (.showError error) => .error (.showError error)

def liftJl {α : Type} : Jl α → UResult α
  | .ok value => .ok value
  | .error error => .error (.jl error)

structure IntegerValidityOps (I : Type) where
  integer : RatIntOps I
  unsignedType : Type
  toUnsigned : I → UResult unsignedType
  unsignedToNat : unsignedType → Nat

/- AbstractChar operations. `toChar` is Julia's `Char(c)` conversion and
`toUInt32` is `codepoint(c)`. The Char instance uses `Char(c) == c`. -/
structure AbstractCharOps (C : Type) where
  malformed : C → Bool
  overlong : C → Bool
  toUInt32 : C → CharResult UInt32
  toChar : C → CharResult UInt32
  fromUInt32 : UInt32 → CharResult C
  unsafeCodepoint : C → UInt32
  isAscii : C → Bool
  le : C → C → Bool
  eq : C → C → Bool
  addInt : C → Nat → CharResult C
  subInt : C → Nat → CharResult C
  zero : C
  d7ff : C
  e000 : C
  maxScalar : C
  ascii0 : C
  ascii9 : C
  asciiA : C
  asciiF : C
  asciiZ : C
  asciia : C
  asciif : C
  asciiz : C
  space : C

  tab : C
  cr : C
  nel : C
  nbsp : C
  control1f : C
  del : C
  latin1Control : C
  zSpace : C
  zParagraph : C
abbrev CharOps (C : Type) := AbstractCharOps C

 def charOps : CharOps JChar where
  malformed := ismalformed_Char charBitOps
  overlong := isoverlong_Char
  toUInt32 := uint32_Char charBitOps
  toChar := fun c => .ok (constructor_Same_AbstractChar c)
  fromUInt32 := char_UInt32
  unsafeCodepoint := unsafe_codepoint_Char charBitOps
  isAscii := JuliaLean.base.strings.basic.isasciiChar
  le a b := decide (a ≤ b)
  eq a b := a == b
  addInt c n := add_AbstractChar_Integer charIntegerOps c (JInt.lit .i64 n)
  subInt c n := sub_AbstractChar_Integer charIntegerOps c (JInt.lit .i64 n)
  zero := 0
  d7ff := 0xed9fbf00
  e000 := 0xee808000
  maxScalar := 0xf48fbfbf
  ascii0 := 0x30000000
  ascii9 := 0x39000000
  asciiA := 0x41000000
  asciiF := 0x46000000
  asciiZ := 0x5a000000
  asciia := 0x61000000
  asciif := 0x66000000
  asciiz := 0x7a000000
  space := 0x20000000
  tab := 0x09000000
  cr := 0x0d000000
  nel := 0xc2850000
  nbsp := 0xc2a00000
  control1f := 0x1f000000
  del := 0x7f000000
  latin1Control := 0xc29f0000
  zSpace := 0xc2a00000
  zParagraph := 0xe280a900

structure Utf8proc where
  toupper : UInt32 → UInt32
  tolower : UInt32 → UInt32
  totitle : UInt32 → UInt32
  category : UInt32 → Int
  categoryString : UInt32 → String
  categoryAbbrev : UInt32 → String
  islower : UInt32 → Int
  isupper : UInt32 → Int
  charwidth : UInt32 → Int
  graphemeBreak : UInt32 → UInt32 → Bool
  graphemeBreakStateful : Int32 → UInt32 → UInt32 → Bool × Int32

 def Utf8procLaws (P : Utf8proc) : Prop :=
  (∀ u, u ≤ 0x10ffff → 0 ≤ P.category u ∧ P.category u ≤ 29) ∧
  (∀ u, u ≤ 0x10ffff → P.toupper u ≤ 0x10ffff ∧
    P.tolower u ≤ 0x10ffff ∧ P.totitle u ≤ 0x10ffff)

/--
Julia source: base/strings/unicode.jl:65-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# utf8 category constants
const UTF8PROC_CATEGORY_CN = 0
const UTF8PROC_CATEGORY_LU = 1
const UTF8PROC_CATEGORY_LL = 2
const UTF8PROC_CATEGORY_LT = 3
const UTF8PROC_CATEGORY_LM = 4
const UTF8PROC_CATEGORY_LO = 5
const UTF8PROC_CATEGORY_MN = 6
const UTF8PROC_CATEGORY_MC = 7
const UTF8PROC_CATEGORY_ME = 8
const UTF8PROC_CATEGORY_ND = 9
const UTF8PROC_CATEGORY_NL = 10
const UTF8PROC_CATEGORY_NO = 11
const UTF8PROC_CATEGORY_PC = 12
const UTF8PROC_CATEGORY_PD = 13
const UTF8PROC_CATEGORY_PS = 14
const UTF8PROC_CATEGORY_PE = 15
const UTF8PROC_CATEGORY_PI = 16
const UTF8PROC_CATEGORY_PF = 17
const UTF8PROC_CATEGORY_PO = 18
const UTF8PROC_CATEGORY_SM = 19
const UTF8PROC_CATEGORY_SC = 20
const UTF8PROC_CATEGORY_SK = 21
const UTF8PROC_CATEGORY_SO = 22
const UTF8PROC_CATEGORY_ZS = 23
const UTF8PROC_CATEGORY_ZL = 24
const UTF8PROC_CATEGORY_ZP = 25
const UTF8PROC_CATEGORY_CC = 26
const UTF8PROC_CATEGORY_CF = 27
const UTF8PROC_CATEGORY_CS = 28
const UTF8PROC_CATEGORY_CO = 29

# strings corresponding to the category constants
const category_strings = [
    "Other, not assigned",
    "Letter, uppercase",
    "Letter, lowercase",
    "Letter, titlecase",
    "Letter, modifier",
    "Letter, other",
    "Mark, nonspacing",
    "Mark, spacing combining",
    "Mark, enclosing",
    "Number, decimal digit",
    "Number, letter",
    "Number, other",
    "Punctuation, connector",
    "Punctuation, dash",
    "Punctuation, open",
    "Punctuation, close",
    "Punctuation, initial quote",
    "Punctuation, final quote",
    "Punctuation, other",
    "Symbol, math",
    "Symbol, currency",
    "Symbol, modifier",
    "Symbol, other",
    "Separator, space",
    "Separator, line",
    "Separator, paragraph",
    "Other, control",
    "Other, format",
    "Other, surrogate",
    "Other, private use",
    "Invalid, too high",
    "Malformed, bad data",
]
# category_code returns a value in 0:31; keep category_strings sized to match so
# `category_string` remains nothrow.
@assert length(category_strings) == 32

const UTF8PROC_STABLE    = (1<<1)
const UTF8PROC_COMPAT    = (1<<2)
const UTF8PROC_COMPOSE   = (1<<3)
const UTF8PROC_DECOMPOSE = (1<<4)
const UTF8PROC_IGNORE    = (1<<5)
const UTF8PROC_REJECTNA  = (1<<6)
const UTF8PROC_NLF2LS    = (1<<7)
const UTF8PROC_NLF2PS    = (1<<8)
const UTF8PROC_NLF2LF    = (UTF8PROC_NLF2LS | UTF8PROC_NLF2PS)
const UTF8PROC_STRIPCC   = (1<<9)
const UTF8PROC_CASEFOLD  = (1<<10)
const UTF8PROC_CHARBOUND = (1<<11)
const UTF8PROC_LUMP      = (1<<12)
const UTF8PROC_STRIPMARK = (1<<13)
```
-/

def UTF8PROC_CATEGORY_CN : Int := 0
def UTF8PROC_CATEGORY_LU : Int := 1
def UTF8PROC_CATEGORY_LL : Int := 2
def UTF8PROC_CATEGORY_LT : Int := 3
def UTF8PROC_CATEGORY_LM : Int := 4
def UTF8PROC_CATEGORY_LO : Int := 5
def UTF8PROC_CATEGORY_MN : Int := 6
def UTF8PROC_CATEGORY_MC : Int := 7
def UTF8PROC_CATEGORY_ME : Int := 8
def UTF8PROC_CATEGORY_ND : Int := 9
def UTF8PROC_CATEGORY_NL : Int := 10
def UTF8PROC_CATEGORY_NO : Int := 11
def UTF8PROC_CATEGORY_PC : Int := 12
def UTF8PROC_CATEGORY_PD : Int := 13
def UTF8PROC_CATEGORY_PS : Int := 14
def UTF8PROC_CATEGORY_PE : Int := 15
def UTF8PROC_CATEGORY_PI : Int := 16
def UTF8PROC_CATEGORY_PF : Int := 17
def UTF8PROC_CATEGORY_PO : Int := 18
def UTF8PROC_CATEGORY_SM : Int := 19
def UTF8PROC_CATEGORY_SC : Int := 20
def UTF8PROC_CATEGORY_SK : Int := 21
def UTF8PROC_CATEGORY_SO : Int := 22
def UTF8PROC_CATEGORY_ZS : Int := 23
def UTF8PROC_CATEGORY_ZL : Int := 24
def UTF8PROC_CATEGORY_ZP : Int := 25
def UTF8PROC_CATEGORY_CC : Int := 26
def UTF8PROC_CATEGORY_CF : Int := 27
def UTF8PROC_CATEGORY_CS : Int := 28
def UTF8PROC_CATEGORY_CO : Int := 29

def categoryStrings : List String :=
  ["Other, not assigned", "Letter, uppercase", "Letter, lowercase", "Letter, titlecase",
   "Letter, modifier", "Letter, other", "Mark, nonspacing", "Mark, spacing combining",
   "Mark, enclosing", "Number, decimal digit", "Number, letter", "Number, other",
   "Punctuation, connector", "Punctuation, dash", "Punctuation, open", "Punctuation, close",
   "Punctuation, initial quote", "Punctuation, final quote", "Punctuation, other", "Symbol, math",
   "Symbol, currency", "Symbol, modifier", "Symbol, other", "Separator, space", "Separator, line",
   "Separator, paragraph", "Other, control", "Other, format", "Other, surrogate", "Other, private use",
   "Invalid, too high", "Malformed, bad data"]

 def UTF8PROC_STABLE : Nat := 1 <<< 1
 def UTF8PROC_COMPAT : Nat := 1 <<< 2
 def UTF8PROC_COMPOSE : Nat := 1 <<< 3
 def UTF8PROC_DECOMPOSE : Nat := 1 <<< 4
 def UTF8PROC_IGNORE : Nat := 1 <<< 5
 def UTF8PROC_REJECTNA : Nat := 1 <<< 6
 def UTF8PROC_NLF2LS : Nat := 1 <<< 7
 def UTF8PROC_NLF2PS : Nat := 1 <<< 8
 def UTF8PROC_NLF2LF : Nat := UTF8PROC_NLF2LS ||| UTF8PROC_NLF2PS
 def UTF8PROC_STRIPCC : Nat := 1 <<< 9
 def UTF8PROC_CASEFOLD : Nat := 1 <<< 10
 def UTF8PROC_CHARBOUND : Nat := 1 <<< 11
 def UTF8PROC_LUMP : Nat := 1 <<< 12
 def UTF8PROC_STRIPMARK : Nat := 1 <<< 13

/--
 Julia source: base/strings/unicode.jl:190-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _julia_charmap = Dict{UInt32,UInt32}(
    0x025B => 0x03B5, # latin small letter open e -> greek small letter epsilon
    0x00B5 => 0x03BC, # micro sign -> greek small letter mu
    0x00B7 => 0x22C5, # middot char -> dot operator (#25098)
    0x0387 => 0x22C5, # Greek interpunct -> dot operator (#25098)
    0x2212 => 0x002D, # minus -> hyphen-minus (#26193)
    0x210F => 0x0127, # hbar -> small letter h with stroke (#48870)
)
```
-/

def juliaCharmap : List (UInt32 × UInt32) :=
  [(0x025b, 0x03b5), (0x00b5, 0x03bc), (0x00b7, 0x22c5),
   (0x0387, 0x22c5), (0x2212, 0x002d), (0x210f, 0x0127)]

/-- `inRange`. -/
def inRange {C : Type} (ops : CharOps C) (lo hi c : C) : Bool :=
  ops.le lo c && ops.le c hi

/--
Julia source: base/strings/unicode.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(c::AbstractChar) = !ismalformed(c) & !isoverlong(c) & ((c ≤ '\ud7ff') | ('\ue000' ≤ c) & (c ≤ '\U10ffff'))
```
-/

def isvalidAbstractChar {C : Type} (ops : CharOps C) (c : C) : Bool := Id.run do
  let notMalformed := !ops.malformed c
  let notOverlong := !ops.overlong c
  let belowD7ff := ops.le c ops.d7ff
  let aboveE000 := ops.le ops.e000 c
  let belowMax := ops.le c ops.maxScalar
  return Bool.and (Bool.and notMalformed notOverlong)
    (Bool.or belowD7ff (Bool.and aboveE000 belowMax))

/--
Julia source: base/strings/unicode.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(::Type{<:AbstractChar}, c::Unsigned) = ((c ≤  0xd7ff ) | ( 0xe000  ≤ c) & (c ≤  0x10ffff ))
```
-/

def isvalidUnsigned {U : Type} (toNat : U → Nat) (c : U) : Bool := Id.run do
  let belowD7ff := toNat c ≤ 0xd7ff
  let aboveE000 := 0xe000 ≤ toNat c
  let belowMax := toNat c ≤ 0x10ffff
  return Bool.or belowD7ff (Bool.and aboveE000 belowMax)

/--
Julia source: base/strings/unicode.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(::Type{T}, c::Integer) where {T<:AbstractChar}  = isvalid(T, Unsigned(c))
```
-/

def isvalidInteger {C I : Type} (_charOps : CharOps C)
    (ops : IntegerValidityOps I) (c : I) : UResult Bool := do
  let u ← ops.toUnsigned c
  pure (isvalidUnsigned ops.unsignedToNat u)

/--
Julia source: base/strings/unicode.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(::Type{<:AbstractChar}, c::AbstractChar)     = isvalid(c)
```
-/

def isvalidAbstractCharType {C : Type} (ops : CharOps C) (c : C) : Bool :=
  isvalidAbstractChar ops c

/--
Julia source: base/strings/unicode.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(::Type{Union{}}, value) = false
```
-/

def isvalidUnion {A : Type} (_value : A) : Bool := false

/--
Julia source: base/strings/unicode.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(::Type{Union{}}, slurp...) = throw(MethodError(isvalid, (Union{}, slurp...)))
```
-/

def isvalidUnionVararg {A : Type} (_values : List A) : UResult Bool := .error .methodError

/--
Julia source: base/strings/unicode.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
utf8proc_error(result) = error(unsafe_string(ccall(:utf8proc_errmsg, Cstring, (Cssize_t,), result)))
```
-/

def utf8proc_error {α : Type} (errorMessage : Int → String) (result : Int) : UResult α :=
  .error (.errorException (errorMessage result))

/--
Julia source: base/strings/unicode.jl:156-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
utf8proc_custom_func(codepoint::UInt32, callback::Any) =
    UInt32(callback(codepoint))::UInt32
```
-/

def utf8proc_custom_func {A State : Type} (callback : UInt32 → State → A × State)
    (toUInt32 : A → UResult UInt32) (codepoint : UInt32) (state : State) :
    UResult (UInt32 × State) := do
  let (value, state) := callback codepoint state
  let value ← toUInt32 value
  pure (value, state)

structure CharTransform where
  identity : Bool
  state : Type
  output : Type
  initial : state
  callback : UInt32 → state → output × state
  convert : output → UResult UInt32

def identityTransform : CharTransform :=
  ⟨true, Unit, UInt32, (), fun c state => (c, state), fun c => .ok c⟩

def customTransform {State A : Type} (initial : State)
    (callback : UInt32 → State → A × State) (convert : A → UResult UInt32) : CharTransform :=
  ⟨false, State, A, initial, callback, convert⟩

structure Utf8procMapOps (S B : Type) where
  sizeof : S → Int
  decompose : S → Int → B → Int → Int → Int
  decomposeCustom : {State : Type} → S → Int → B → Int → Int →
    (UInt32 → State → UResult (UInt32 × State)) → State → UResult (Int × State)
  null : B
  allocate : Int → B
  reencode : B → Int → Int → Int
  resize : B → Int → B
  string : B → Int → UResult JString
  errorMessage : Int → String

/--
Julia source: base/strings/unicode.jl:159-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function utf8proc_decompose(str, options, buffer, nwords, chartransform::typeof(identity))
    ret = ccall(:utf8proc_decompose, Int, (Ptr{UInt8}, Int, Ptr{UInt8}, Int, Cint),
                str, sizeof(str), buffer, nwords, options)
    ret < 0 && utf8proc_error(ret)
    return ret
end
```
-/

def utf8procDecomposeIdentity {S B State : Type} (ops : Utf8procMapOps S B)
    (str : S) (options : Int) (buffer : B) (nwords : Int) (state : State) :
    UResult (Int × State) := do
  let ret := ops.decompose str (ops.sizeof str) buffer nwords options
  if ret < 0 then utf8proc_error ops.errorMessage ret else pure (ret, state)

/--
Julia source: base/strings/unicode.jl:165-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function utf8proc_decompose(str, options, buffer, nwords, chartransform::F) where F
    ret = ccall(:utf8proc_decompose_custom, Int, (Ptr{UInt8}, Int, Ptr{UInt8}, Int, Cint, Ptr{Cvoid}, Ref{F}),
                str, sizeof(str), buffer, nwords, options,
                @cfunction(utf8proc_custom_func, UInt32, (UInt32, Ref{F})), chartransform)
    ret < 0 && utf8proc_error(ret)
    return ret
end
```
-/

def utf8procDecomposeCustom {S B State : Type} (ops : Utf8procMapOps S B)
    (str : S) (options : Int) (buffer : B) (nwords : Int)
    (chartransform : UInt32 → State → UResult (UInt32 × State)) (state : State) :
    UResult (Int × State) := do
  let (ret, state) ← ops.decomposeCustom str (ops.sizeof str) buffer nwords options chartransform state
  if ret < 0 then utf8proc_error ops.errorMessage ret else pure (ret, state)

/-- Dispatch the two Julia overloads of `utf8proc_decompose`. -/
def utf8procDecompose {S B : Type} (ops : Utf8procMapOps S B)
    (str : S) (options : Int) (buffer : B) (nwords : Int) (chartransform : CharTransform) :
    UResult (Int × chartransform.state) :=
  if chartransform.identity then
    utf8procDecomposeIdentity ops str options buffer nwords chartransform.initial
  else
    utf8procDecomposeCustom ops str options buffer nwords
      (fun c state => utf8proc_custom_func chartransform.callback chartransform.convert c state)
      chartransform.initial

/--
Julia source: base/strings/unicode.jl:173-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function utf8proc_map(str::Union{String,SubString{String}}, options::Integer, chartransform::F = identity) where F
    nwords = utf8proc_decompose(str, options, C_NULL, 0, chartransform)
    buffer = Base.StringVector(nwords*4)
    nwords = utf8proc_decompose(str, options, buffer, nwords, chartransform)
    nbytes = ccall(:utf8proc_reencode, Int, (Ptr{UInt8}, Int, Cint), buffer, nwords, options)
    nbytes < 0 && utf8proc_error(nbytes)
    return String(resize!(buffer, nbytes))
end
```
-/

def utf8proc_map {S B : Type} (ops : Utf8procMapOps S B)
    (str : S) (options : Int) (chartransform : CharTransform := identityTransform) :
    UResult (JString × chartransform.state) := do
  let (nwords, state) ← utf8procDecompose ops str options ops.null 0 chartransform
  let buffer := ops.allocate (nwords * 4)
  let chartransform := { chartransform with initial := state }
  let (nwords, state) ← utf8procDecompose ops str options buffer nwords chartransform
  let nbytes := ops.reencode buffer nwords options
  if nbytes < 0 then utf8proc_error ops.errorMessage nbytes
  else do
    let string ← ops.string (ops.resize buffer nbytes) nbytes
    pure (string, state)

/--
Julia source: base/strings/unicode.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
utf8proc_map(s::AbstractString, flags::Integer, chartransform::F = identity) where F = utf8proc_map(String(s)::String, flags, chartransform)
```
-/

def utf8proc_mapAbstract {S B : Type} (ops : Utf8procMapOps JString B)
    (toString : S → UResult JString) (s : S) (options : Int)
    (chartransform : CharTransform := identityTransform) :
    UResult (JString × chartransform.state) := do
  let string ← toString s
  utf8proc_map ops string options chartransform

structure NormKw where
  stable : Bool := false
  compat : Bool := false
  compose : Bool := true
  decompose : Bool := false
  stripignore : Bool := false
  rejectna : Bool := false
  newline2ls : Bool := false
  newline2ps : Bool := false
  newline2lf : Bool := false
  stripcc : Bool := false
  casefold : Bool := false
  lump : Bool := false
  stripmark : Bool := false

def boolNat (b : Bool) : Nat := if b then 1 else 0

def orFlag (enabled : Bool) (flags bit : Nat) : Nat := if enabled then flags ||| bit else flags

/--
Julia source: base/strings/unicode.jl:202-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function normalize(
    s::AbstractString;
    stable::Bool=false,
    compat::Bool=false,
    compose::Bool=true,
    decompose::Bool=false,
    stripignore::Bool=false,
    rejectna::Bool=false,
    newline2ls::Bool=false,
    newline2ps::Bool=false,
    newline2lf::Bool=false,
    stripcc::Bool=false,
    casefold::Bool=false,
    lump::Bool=false,
    stripmark::Bool=false,
    chartransform=identity,
)
    flags = 0
    stable && (flags = flags | UTF8PROC_STABLE)
    compat && (flags = flags | UTF8PROC_COMPAT)
    # TODO: error if compose & decompose?
    if decompose
        flags = flags | UTF8PROC_DECOMPOSE
    elseif compose
        flags = flags | UTF8PROC_COMPOSE
    elseif compat || stripmark
        throw(ArgumentError("compat=true or stripmark=true require compose=true or decompose=true"))
    end
    stripignore && (flags = flags | UTF8PROC_IGNORE)
    rejectna && (flags = flags | UTF8PROC_REJECTNA)
    newline2ls + newline2ps + newline2lf > 1 && throw(ArgumentError("only one newline conversion may be specified"))
    newline2ls && (flags = flags | UTF8PROC_NLF2LS)
    newline2ps && (flags = flags | UTF8PROC_NLF2PS)
    newline2lf && (flags = flags | UTF8PROC_NLF2LF)
    stripcc && (flags = flags | UTF8PROC_STRIPCC)
    casefold && (flags = flags | UTF8PROC_CASEFOLD)
    lump && (flags = flags | UTF8PROC_LUMP)
    stripmark && (flags = flags | UTF8PROC_STRIPMARK)
    utf8proc_map(s, flags, chartransform)
end
```
-/

def normalize {S B : Type} (ops : Utf8procMapOps JString B)
    (toString : S → UResult JString) (s : S) (kw : NormKw)
    (chartransform : CharTransform := identityTransform) : UResult (JString × chartransform.state) := do
  let mut flags := 0
  if kw.stable then flags := flags ||| UTF8PROC_STABLE
  if kw.compat then flags := flags ||| UTF8PROC_COMPAT
  if kw.decompose then
    flags := flags ||| UTF8PROC_DECOMPOSE
  else if kw.compose then
    flags := flags ||| UTF8PROC_COMPOSE
  else if kw.compat || kw.stripmark then
    throw (.argumentError "compat=true or stripmark=true require compose=true or decompose=true")
  if kw.stripignore then flags := flags ||| UTF8PROC_IGNORE
  if kw.rejectna then flags := flags ||| UTF8PROC_REJECTNA
  if boolNat kw.newline2ls + boolNat kw.newline2ps + boolNat kw.newline2lf > 1 then
    throw (.argumentError "only one newline conversion may be specified")
  if kw.newline2ls then flags := flags ||| UTF8PROC_NLF2LS
  if kw.newline2ps then flags := flags ||| UTF8PROC_NLF2PS
  if kw.newline2lf then flags := flags ||| UTF8PROC_NLF2LF
  if kw.stripcc then flags := flags ||| UTF8PROC_STRIPCC
  if kw.casefold then flags := flags ||| UTF8PROC_CASEFOLD
  if kw.lump then flags := flags ||| UTF8PROC_LUMP
  if kw.stripmark then flags := flags ||| UTF8PROC_STRIPMARK
  utf8proc_mapAbstract ops toString s (Int.ofNat flags) chartransform

inductive NormForm where
  | nfc
  | nfd
  | nfkc
  | nfkd
  | other (name : String)

def normFormName : NormForm → String
  | .nfc => "NFC"
  | .nfd => "NFD"
  | .nfkc => "NFKC"
  | .nfkd => "NFKD"
  | .other name => name

/--
Julia source: base/strings/unicode.jl:243-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function normalize(s::AbstractString, nf::Symbol)
    utf8proc_map(s, nf === :NFC ? (UTF8PROC_STABLE | UTF8PROC_COMPOSE) :
                    nf === :NFD ? (UTF8PROC_STABLE | UTF8PROC_DECOMPOSE) :
                    nf === :NFKC ? (UTF8PROC_STABLE | UTF8PROC_COMPOSE
                                   | UTF8PROC_COMPAT) :
                    nf === :NFKD ? (UTF8PROC_STABLE | UTF8PROC_DECOMPOSE
                                   | UTF8PROC_COMPAT) :
                    throw(ArgumentError(":$nf is not one of :NFC, :NFD, :NFKC, :NFKD")))
end
```
-/

def normalizeForm {S B : Type} (ops : Utf8procMapOps JString B)
    (toString : S → UResult JString) (s : S) (nf : NormForm) : UResult (JString × Unit) := do
  let flags := match nf with
    | .nfc => UTF8PROC_STABLE ||| UTF8PROC_COMPOSE
    | .nfd => UTF8PROC_STABLE ||| UTF8PROC_DECOMPOSE
    | .nfkc => UTF8PROC_STABLE ||| UTF8PROC_COMPOSE ||| UTF8PROC_COMPAT
    | .nfkd => UTF8PROC_STABLE ||| UTF8PROC_DECOMPOSE ||| UTF8PROC_COMPAT
    | .other _ => 0
  match nf with
  | .other _ => throw (.argumentError s!":{normFormName nf} is not one of :NFC, :NFD, :NFKC, :NFKD")
  | _ => utf8proc_mapAbstract ops toString s (Int.ofNat flags)

/--
Julia source: base/strings/unicode.jl:272-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function textwidth(c::Char)
    u = reinterpret(UInt32, c)
    b = bswap(u) # from isascii(c)
    b < 0x7f && return Int(b >= 0x20) # ASCII fast path
    # We can't know a priori how terminals will render invalid UTF8 chars,
    # so we conservatively decide a width of 1.
    (ismalformed(c) || is_overlong_enc(u)) && return 1
    # `unsafe_codepoint` is sound here because both malformed-encoding cases
    # have been ruled out above; this lets the compiler infer `:nothrow`.
    Int(@assume_effects :foldable :nothrow @ccall utf8proc_charwidth(unsafe_codepoint(c)::UInt32)::Cint)
end
```
-/

def textwidthChar (P : Utf8proc) (c : JChar) : Int :=
  let b := JuliaLean.base.strings.basic.bswap32 c
  if b < 0x7f then Int.ofNat (if 0x20 ≤ b then 1 else 0)
  else if ismalformed_Char charBitOps c || isoverlong_Char c then 1
  else P.charwidth (unsafe_codepoint_Char charBitOps c)
/--
Julia source: base/strings/unicode.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
textwidth(c::AbstractChar) = textwidth(Char(c)::Char)
```
-/

def textwidthAbstractChar {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Int := do
  let char ← liftChar (ops.toChar c)
  pure (textwidthChar P char)

/-- `textwidth(c)` as the `Int` it returns: unicode.jl:270 `textwidth(c::AbstractChar) =
textwidth(Char(c)::Char)` and unicode.jl:255-268 `textwidth(c::Char)`, whose results are
`Int(b >= 0x20)`, `1` and `Int` of utf8proc's `Cint` width; `textwidthChar` computes exactly those
values, so they are `Int64` values. -/
def textwidthAbstractCharInt {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) :
    UResult (JInt .i64) := do
  return JInt.wrap .i64 (← textwidthAbstractChar ops P c)

/-- The `+` of unicode.jl:295 on the accumulator `0::Int` and the `Int` widths: int.jl:88
`(+)(x::T, y::T) where {T<:BitInteger} = add_int(x, y)` (int.lean `add`, wrapping at `2^63`).
`reduce_first(+, x) = x` (reduce.jl:411 `reduce_first(op, x)`; `Int` is not `BitSignedSmall`);
`+(::_InitialValue, ::Int)` has no method. -/
def textwidthAddReducer :
    JuliaLean.base.reduce.ProtocolReducer UnicodeError (JInt .i64) (JInt .i64) where
  first x := .ok (.value x)
  step state x :=
    match state with
    | .initial => .error .methodError
    | .value acc => .ok (.value (JuliaLean.base.int.add acc x))

/--
Julia source: base/strings/unicode.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
textwidth(s::AbstractString) = mapreduce(textwidth, +, s; init=0)
```
-/
def textwidthAbstractString {S C St : Type}
    (iterateFirst : S → UResult (Option (C × St)))
    (iterateAt : S → St → UResult (Option (C × St)))
    (ops : CharOps C) (P : Utf8proc) (s : S) : Option (UResult (JInt .i64)) :=
  JuliaLean.base.reduce.mapreduce_protocol
    JuliaLean.base.iterators.restWithState
    (fun run r st => ((JuliaLean.base.iterators.iterateRest
      (fun i s heap => some (run i s, heap)) r st ()).get
        (by simp [JuliaLean.base.iterators.iterateRest])).1)
    -- reduce_empty_iter(MappingRF(textwidth, BottomRF(+)), s): HasEltype (eltype Char), so
    -- reduce.jl:384, 359 and the generic mapreduce_empty, reduce.jl:320.
    (Except.mapError UnicodeError.jl JuliaLean.base.reduce._empty_reduce_error)
    (textwidthAbstractCharInt ops P)
    textwidthAddReducer
    (fun | none => iterateFirst s | some st => iterateAt s st)
    (.value (JInt.wrap .i64 0))

/--
Julia source: base/strings/unicode.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow :foldable textwidth(s::String) = mapreduce(textwidth, +, s; init=0)
```
-/

def textwidthString {C : Type}
    (mapreduce : (C → UResult Int) → (Int → Int → Int) → JString → Int → UResult Int)
    (ops : CharOps C) (P : Utf8proc) (s : JString) : UResult Int :=
  mapreduce (textwidthAbstractChar ops P) (· + ·) s 0

/--
Julia source: base/strings/unicode.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow :foldable textwidth(s::SubString{String}) = mapreduce(textwidth, +, s; init=0)
```
-/

def textwidthSubString {S C : Type}
    (mapreduce : (C → UResult Int) → (Int → Int → Int) → S → Int → UResult Int)
    (ops : CharOps C) (P : Utf8proc) (s : S) : UResult Int :=
  mapreduce (textwidthAbstractChar ops P) (· + ·) s 0

/--
Julia source: base/strings/unicode.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
textwidth(s::AnnotatedString) = textwidth(s.string)
```
-/

def textwidthAnnotatedString {A C : Type}
    (getString : A → JString)
    (mapreduce : (C → UResult Int) → (Int → Int → Int) → JString → Int → UResult Int)
    (ops : CharOps C) (P : Utf8proc) (s : A) : UResult Int :=
  textwidthString mapreduce ops P (getString s)

/--
Julia source: base/strings/unicode.jl:318-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lowercase(c::T) where {T<:AbstractChar} = isascii(c) ? ('A' <= c <= 'Z' ? c + 0x20 : c) :
    T(@assume_effects :foldable :nothrow @ccall utf8proc_tolower(c::UInt32)::UInt32)
```
-/

def lowercaseAbstractChar {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult C := do
  if ops.isAscii c then
    if inRange ops ops.asciiA ops.asciiZ c then liftChar (ops.addInt c 32) else pure c
  else do
    let u ← liftChar (ops.toUInt32 c)
    liftChar (ops.fromUInt32 (P.tolower u))

/-- `lowercase(c::AnnotatedChar)` preserves annotations. -/
structure AnnotatedCharOps (A C Ann : Type) where
  char : A → C
  annotations : A → Ann
  construct : C → Ann → UResult A

/--
Julia source: base/strings/unicode.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lowercase(c::AnnotatedChar) = AnnotatedChar(lowercase(c.char), annotations(c))
```
-/

def lowercaseAnnotatedChar {A C Ann : Type} (ops : CharOps C)
    (annotated : AnnotatedCharOps A C Ann) (P : Utf8proc) (c : A) : UResult A := do
  let mapped ← lowercaseAbstractChar ops P (annotated.char c)
  annotated.construct mapped (annotated.annotations c)

/--
Julia source: base/strings/unicode.jl:339-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uppercase(c::T) where {T<:AbstractChar} = isascii(c) ? ('a' <= c <= 'z' ? c - 0x20 : c) :
    T(@assume_effects :foldable :nothrow @ccall utf8proc_toupper(c::UInt32)::UInt32)
```
-/

def uppercaseAbstractChar {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult C := do
  if ops.isAscii c then
    if inRange ops ops.asciia ops.asciiz c then liftChar (ops.subInt c 32) else pure c
  else do
    let u ← liftChar (ops.toUInt32 c)
    liftChar (ops.fromUInt32 (P.toupper u))

/--
Julia source: base/strings/unicode.jl:342-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uppercase(c::AnnotatedChar) = AnnotatedChar(uppercase(c.char), annotations(c))
```
-/

def uppercaseAnnotatedChar {A C Ann : Type} (ops : CharOps C)
    (annotated : AnnotatedCharOps A C Ann) (P : Utf8proc) (c : A) : UResult A := do
  let mapped ← uppercaseAbstractChar ops P (annotated.char c)
  annotated.construct mapped (annotated.annotations c)

/--
Julia source: base/strings/unicode.jl:364-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
titlecase(c::T) where {T<:AbstractChar} = isascii(c) ? ('a' <= c <= 'z' ? c - 0x20 : c) :
    T(@assume_effects :foldable :nothrow @ccall utf8proc_totitle(c::UInt32)::UInt32)
```
-/

def titlecaseAbstractChar {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult C := do
  if ops.isAscii c then
    if inRange ops ops.asciia ops.asciiz c then liftChar (ops.subInt c 32) else pure c
  else do
    let u ← liftChar (ops.toUInt32 c)
    liftChar (ops.fromUInt32 (P.totitle u))

/--
Julia source: base/strings/unicode.jl:367-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
titlecase(c::AnnotatedChar) = AnnotatedChar(titlecase(c.char), annotations(c))
```
-/

def titlecaseAnnotatedChar {A C Ann : Type} (ops : CharOps C)
    (annotated : AnnotatedCharOps A C Ann) (P : Utf8proc) (c : A) : UResult A := do
  let mapped ← titlecaseAbstractChar ops P (annotated.char c)
  annotated.construct mapped (annotated.annotations c)

/--
Julia source: base/strings/unicode.jl:379-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function category_code(x::Integer)
    x ≤ 0x10ffff ? (@assume_effects :foldable :nothrow @ccall utf8proc_category(UInt32(x)::UInt32)::Cint) : Cint(30)
end
```
-/

def category_code_Integer {I : Type} (toInt : I → Int) (toUInt32 : I → UResult UInt32)
    (P : Utf8proc) (x : I) : UResult Int := do
  if toInt x ≤ 0x10ffff then
    let u ← toUInt32 x
    pure (P.category u)
  else pure 30
/--
Julia source: base/strings/unicode.jl:372-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function category_code(c::AbstractChar)
    # `unsafe_codepoint` is sound here because the `ismalformed` guard has ruled
    # out the throwing path of `UInt32(::Char)`, allowing the compiler to infer
    # `:nothrow` for `category_code(::Char)`.
    !ismalformed(c) ? category_code(unsafe_codepoint(c)) : Cint(31)
end
```
-/

def category_code_AbstractChar {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Int :=
  if ops.malformed c then .ok 31
  else category_code_Integer (fun u => Int.ofNat u.toNat) (fun u => .ok u) P (ops.unsafeCodepoint c)


/--
Julia source: base/strings/unicode.jl:384-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function category_abbrev(c::AbstractChar)
    ismalformed(c) && return "Ma"
    c ≤ '\U10ffff' || return "In"
    unsafe_string(@ccall utf8proc_category_string(UInt32(c)::UInt32)::Cstring)
end
```
-/

def category_abbrev_AbstractChar {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult String := do
  if ops.malformed c then pure "Ma"
  else if !ops.le c ops.maxScalar then pure "In"
  else do
    let u ← liftChar (ops.toUInt32 c)
    pure (P.categoryAbbrev u)

/--
Julia source: base/strings/unicode.jl:392-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow :foldable function category_abbrev(c::Char)
    ismalformed(c) && return "Ma"
    c ≤ '\U10ffff' || return "In"
    unsafe_string(@ccall utf8proc_category_string(unsafe_codepoint(c)::UInt32)::Cstring)
end
```
-/

def category_abbrev_Char (P : Utf8proc) (c : JChar) : String :=
  if ismalformed_Char charBitOps c then "Ma"
  else if !(c ≤ charOps.maxScalar) then "In"
  else P.categoryAbbrev (unsafe_codepoint_Char charBitOps c)

inductive CategoryValue (C I : Type) where
  | character (value : C)
  | integer (value : I)

/-- Dispatch for `category_code` on any AbstractChar or Integer type. -/
def category_code_Value {C I : Type} (charOps : CharOps C) (integerOps : RatIntOps I)
    (P : Utf8proc) (toUInt32 : I → UResult UInt32) : CategoryValue C I → UResult Int
  | .character c => category_code_AbstractChar charOps P c
  | .integer x => category_code_Integer integerOps.toInt toUInt32 P x

/-- The source table index is the zero-based Unicode category code. -/
def CategoryCodeBounds {C : Type} (categoryCode : C → UResult Int) : Prop :=
  ∀ value category, categoryCode value = .ok category →
    0 ≤ category ∧ category.toNat < categoryStrings.length
/--
Julia source: base/strings/unicode.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
category_string(c) = category_strings[category_code(c)+1]
```
-/


def category_string {C I : Type} (charOps : CharOps C) (integerOps : RatIntOps I)
    (P : Utf8proc) (toUInt32 : I → UResult UInt32) (c : CategoryValue C I) : UResult String := do
  let category ← category_code_Value charOps integerOps P toUInt32 c
  match categoryStrings[category.toNat]? with
  | some value => pure value
  | none => .error .boundsError

/--
Julia source: base/strings/unicode.jl:403-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow :foldable category_string(c::Char) = @inbounds category_strings[category_code(c)+1]
```
-/

def category_string_Char (ops : CharOps JChar) (P : Utf8proc)
    (categoryCodeBounds : CategoryCodeBounds (category_code_AbstractChar ops P))
    (c : JChar) : UResult String :=
  match h : category_code_AbstractChar ops P c with
  | .error error => .error error
  | .ok category =>
      .ok (categoryStrings.get ⟨category.toNat, (categoryCodeBounds c category h).2⟩)

/--
Julia source: base/strings/unicode.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isassigned(c) = UTF8PROC_CATEGORY_CN < category_code(c) <= UTF8PROC_CATEGORY_CO
```
-/

def isassigned {C I : Type} (charOps : CharOps C) (integerOps : RatIntOps I)
    (P : Utf8proc) (toUInt32 : I → UResult UInt32) (c : CategoryValue C I) : UResult Bool := do
  let category ← category_code_Value charOps integerOps P toUInt32 c
  pure (UTF8PROC_CATEGORY_CN < category && category ≤ UTF8PROC_CATEGORY_CO)

/--
Julia source: base/strings/unicode.jl:429-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function islowercase(c::AbstractChar)
    # `unsafe_codepoint` is sound here because of the `ismalformed` guard;
    # this lets the compiler infer `:nothrow` for `islowercase(::Char)`.
    ismalformed(c) ? false :
        !iszero(@assume_effects :foldable :nothrow @ccall utf8proc_islower(unsafe_codepoint(c)::UInt32)::Cint)
end
```
-/

def islowercase {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool :=
  if ops.malformed c then .ok false
  else .ok (P.islower (ops.unsafeCodepoint c) != 0)

/--
Julia source: base/strings/unicode.jl:458-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isuppercase(c::AbstractChar)
    # `unsafe_codepoint` is sound here because of the `ismalformed` guard;
    # this lets the compiler infer `:nothrow` for `isuppercase(::Char)`.
    ismalformed(c) ? false :
        !iszero(@assume_effects :foldable :nothrow @ccall utf8proc_isupper(unsafe_codepoint(c)::UInt32)::Cint)
end
```
-/

def isuppercase {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool :=
  if ops.malformed c then .ok false
  else .ok (P.isupper (ops.unsafeCodepoint c) != 0)

/--
Julia source: base/strings/unicode.jl:472-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iscased(c::AbstractChar)
    cat = category_code(c)
    return cat == UTF8PROC_CATEGORY_LU ||
           cat == UTF8PROC_CATEGORY_LT ||
           cat == UTF8PROC_CATEGORY_LL
end
```
-/

def iscased {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool := do
  let cat ← category_code_AbstractChar ops P c
  pure (cat == UTF8PROC_CATEGORY_LU || cat == UTF8PROC_CATEGORY_LT || cat == UTF8PROC_CATEGORY_LL)

/--
Julia source: base/strings/unicode.jl:499-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdigit(c::AbstractChar) = (c >= '0') & (c <= '9')
```
-/

def isdigit {C : Type} (ops : CharOps C) (c : C) : Bool := Id.run do
  let atLeastZero := ops.le ops.ascii0 c
  let atMostNine := ops.le c ops.ascii9
  return Bool.and atLeastZero atMostNine

/--
Julia source: base/strings/unicode.jl:522-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isletter(c::AbstractChar) = UTF8PROC_CATEGORY_LU <= category_code(c) <= UTF8PROC_CATEGORY_LO
```
-/

def isletter {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool := do
  let cat ← category_code_AbstractChar ops P c
  pure (UTF8PROC_CATEGORY_LU ≤ cat && cat ≤ UTF8PROC_CATEGORY_LO)

/--
Julia source: base/strings/unicode.jl:549-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnumeric(c::AbstractChar) = UTF8PROC_CATEGORY_ND <= category_code(c) <= UTF8PROC_CATEGORY_NO
```
-/

def isnumeric {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool := do
  let cat ← category_code_AbstractChar ops P c
  pure (UTF8PROC_CATEGORY_ND ≤ cat && cat ≤ UTF8PROC_CATEGORY_NO)

/--
Julia source: base/strings/unicode.jl:568-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iscntrl(c::AbstractChar) = c <= '\x1f' || '\x7f' <= c <= '\u9f'
```
-/

def iscntrl {C : Type} (ops : CharOps C) (c : C) : Bool :=
  ops.le c ops.control1f || (ops.le ops.del c && ops.le c ops.latin1Control)

/--
Julia source: base/strings/unicode.jl:594-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispunct(c::AbstractChar) = UTF8PROC_CATEGORY_PC <= category_code(c) <= UTF8PROC_CATEGORY_PO
```
-/

def ispunct {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool := do
  let cat ← category_code_AbstractChar ops P c
  pure (UTF8PROC_CATEGORY_PC ≤ cat && cat ≤ UTF8PROC_CATEGORY_PO)

/--
Julia source: base/strings/unicode.jl:624-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isspace(c::AbstractChar) =
    c == ' ' || '\t' <= c <= '\r' || c == '\u85' ||
    '\ua0' <= c && UTF8PROC_CATEGORY_ZS <= category_code(c) <= UTF8PROC_CATEGORY_ZP
```
-/

def isspace {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool :=
  if ops.eq c ops.space then .ok true
  else if ops.le ops.tab c && ops.le c ops.cr then .ok true
  else if ops.eq c ops.nel then .ok true
  else if ops.le ops.nbsp c then do
    let cat ← category_code_AbstractChar ops P c
    pure (UTF8PROC_CATEGORY_ZS ≤ cat && cat ≤ UTF8PROC_CATEGORY_ZP)
  else .ok false

/--
Julia source: base/strings/unicode.jl:642-642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isprint(c::AbstractChar) = UTF8PROC_CATEGORY_LU <= category_code(c) <= UTF8PROC_CATEGORY_ZS
```
-/

def isprint {C : Type} (ops : CharOps C) (P : Utf8proc) (c : C) : UResult Bool := do
  let cat ← category_code_AbstractChar ops P c
  pure (UTF8PROC_CATEGORY_LU ≤ cat && cat ≤ UTF8PROC_CATEGORY_ZS)

/--
Julia source: base/strings/unicode.jl:659-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isxdigit(c::AbstractChar) = '0'<=c<='9' || 'a'<=c<='f' || 'A'<=c<='F'
```
-/

def isxdigit {C : Type} (ops : CharOps C) (c : C) : Bool :=
  (ops.le ops.ascii0 c && ops.le c ops.ascii9) ||
  (ops.le ops.asciia c && ops.le c ops.asciif) ||
  (ops.le ops.asciiA c && ops.le c ops.asciiF)

/--
Julia source: base/strings/unicode.jl:676-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uppercase(s::AbstractString) = map(uppercase, s)
```
-/

def uppercaseAbstractString {S R C CU CT B O : Type}
    (stringOps : StringOps S R C CU CT UnicodeError)
    (iterate : S → IterSteps C Index UnicodeError)
    (builder : StringBuilderOps B C UnicodeError O) (charOps : CharOps C)
    (P : Utf8proc) (s : S) : UResult O :=
  JuliaLean.base.strings.basic.mapString stringOps iterate builder (uppercaseAbstractChar charOps P) s

/--
Julia source: base/strings/unicode.jl:677-677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uppercase(s::AnnotatedString) = annotated_chartransform(uppercase, s)
```
-/

def uppercaseAnnotatedString {A C : Type}
    (annotatedCharTransform : (C → UResult C) → A → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : A) : UResult A :=
  annotatedCharTransform (uppercaseAbstractChar charOps P) s

/--
Julia source: base/strings/unicode.jl:678-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uppercase(s::SubString{<:AnnotatedString}) = uppercase(AnnotatedString(s))
```
-/

def uppercaseAnnotatedSubString {A Sub C : Type}
    (toAnnotated : Sub → A) (annotatedCharTransform : (C → UResult C) → A → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : Sub) : UResult A :=
  uppercaseAnnotatedString annotatedCharTransform charOps P (toAnnotated s)

/--
Julia source: base/strings/unicode.jl:693-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lowercase(s::AbstractString) = map(lowercase, s)
```
-/

def lowercaseAbstractString {S R C CU CT B O : Type}
    (stringOps : StringOps S R C CU CT UnicodeError)
    (iterate : S → IterSteps C Index UnicodeError)
    (builder : StringBuilderOps B C UnicodeError O) (charOps : CharOps C)
    (P : Utf8proc) (s : S) : UResult O :=
  JuliaLean.base.strings.basic.mapString stringOps iterate builder (lowercaseAbstractChar charOps P) s

/--
Julia source: base/strings/unicode.jl:694-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lowercase(s::AnnotatedString) = annotated_chartransform(lowercase, s)
```
-/

def lowercaseAnnotatedString {A C : Type}
    (annotatedCharTransform : (C → UResult C) → A → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : A) : UResult A :=
  annotatedCharTransform (lowercaseAbstractChar charOps P) s

/--
Julia source: base/strings/unicode.jl:695-695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lowercase(s::SubString{<:AnnotatedString}) = lowercase(AnnotatedString(s))
```
-/

def lowercaseAnnotatedSubString {A Sub C : Type}
    (toAnnotated : Sub → A) (annotatedCharTransform : (C → UResult C) → A → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : Sub) : UResult A :=
  lowercaseAnnotatedString annotatedCharTransform charOps P (toAnnotated s)

structure TitlecaseOps (S C B : Type) where
  iterate : S → IterSteps C Index UnicodeError
  newBuffer : Unit → UResult B
  printChar : B → C → UResult B
  takeString : B → UResult JString
  zeroChar : S → C
/--
Julia source: base/strings/unicode.jl:844-851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function isgraphemebreak!(state::Ref{Int32}, c1::AbstractChar, c2::AbstractChar)
    if ismalformed(c1) || ismalformed(c2)
        state[] = 0
        return true
    end
    ccall(:utf8proc_grapheme_break_stateful, Bool,
          (UInt32, UInt32, Ref{Int32}), c1, c2, state)
end
```
-/

def isgraphemebreakBang {C : Type} (ops : CharOps C) (P : Utf8proc)
    (state : Int32) (c1 c2 : C) : UResult (Bool × Int32) := do
  if ops.malformed c1 || ops.malformed c2 then pure (true, 0)
  else
    let u1 ← liftChar (ops.toUInt32 c1)
    let u2 ← liftChar (ops.toUInt32 c2)
    pure (P.graphemeBreakStateful state u1 u2)

def titlecaseLoop {S C B : Type} (ops : TitlecaseOps S C B)
    (charOps : CharOps C) (P : Utf8proc) (wordsep : C → Bool) (strict : Bool) :
    IterSteps C Index UnicodeError → Bool → Int32 → C → B → UResult B
  | .done, _, _, _, buffer => .ok buffer
  | .fail error, _, _, _, _ => .error error
  | .yield c state next, startword, stateValue, c0, buffer =>
      match isgraphemebreakBang charOps P stateValue c0 c with
      | .error error => .error error
      | .ok (breaks, stateValue) =>
          if breaks && wordsep c then
            match ops.printChar buffer c with
            | .error error => .error error
            | .ok buffer =>
                titlecaseLoop ops charOps P wordsep strict (next state) true stateValue c buffer
          else
            match (if startword then titlecaseAbstractChar charOps P c
              else if strict then lowercaseAbstractChar charOps P c else .ok c) with
            | .error error => .error error
            | .ok mapped =>
                match ops.printChar buffer mapped with
                | .error error => .error error
                | .ok buffer =>
                    titlecaseLoop ops charOps P wordsep strict (next state) false stateValue c buffer
partial_fixpoint

/--
Julia source: base/strings/unicode.jl:723-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function titlecase(s::AbstractString; wordsep::Function = !isletter, strict::Bool=true)
    startword = true
    state = Ref{Int32}(0)
    c0 = eltype(s)(0x00000000)
    b = IOBuffer()
    for c in s
        # Note: It would be better to have a word iterator following UAX#29,
        # similar to our grapheme iterator, but utf8proc does not yet have
        # this information.  At the very least we shouldn't break inside graphemes.
        if isgraphemebreak!(state, c0, c) && wordsep(c)
            print(b, c)
            startword = true
        else
            print(b, startword ? titlecase(c) : strict ? lowercase(c) : c)
            startword = false
        end
        c0 = c
    end
    return takestring!(b)
end
```
-/

def titlecaseAbstractString {S C B : Type} (ops : TitlecaseOps S C B)
    (charOps : CharOps C) (P : Utf8proc) (wordsep : C → Bool) (strict : Bool)
    (s : S) : UResult JString := do
  let buffer ← ops.newBuffer ()
  let initialChar := ops.zeroChar s
  let buffer ← titlecaseLoop ops charOps P wordsep strict
    (ops.iterate s) true 0 initialChar buffer
  ops.takeString buffer

structure TitleState (C : Type) where
  startword : Bool
  state : Int32
  c0 : C
  wordsep : C → Bool
  strict : Bool

/--
Julia source: base/strings/unicode.jl:745-759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function titlecase(s::AnnotatedString; wordsep::Function = !isletter, strict::Bool=true)
    initial_state = (; startword = true, state = Ref{Int32}(0),
             c0 = eltype(s)(zero(UInt32)), wordsep, strict)
    annotated_chartransform(s, initial_state) do c, state
        if isgraphemebreak!(state.state, state.c0, c) && state.wordsep(c)
            state = Base.setindex(state, true, :startword)
            cnew = c
        else
            cnew = state.startword ? titlecase(c) : state.strict ? lowercase(c) : c
            state = Base.setindex(state, false, :startword)
        end
        state = Base.setindex(state, c, :c0)
        cnew, state
    end
end
```
-/

def titlecaseAnnotatedString {A C : Type}
    (annotatedCharTransform : {State : Type} → (C → State → UResult (C × State)) → A → State → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (wordsep : C → Bool) (strict : Bool)
    (zero : C) (s : A) : UResult A :=
  let initial : TitleState C := ⟨true, 0, zero, wordsep, strict⟩
  annotatedCharTransform (fun c state => do
    let (breaks, graphemeState) ← isgraphemebreakBang charOps P state.state state.c0 c
    if breaks && state.wordsep c then
      pure (c, { state with startword := true, state := graphemeState, c0 := c })
    else
      let mapped ← if state.startword then titlecaseAbstractChar charOps P c
        else if state.strict then lowercaseAbstractChar charOps P c else pure c
      pure (mapped, { state with startword := false, state := graphemeState, c0 := c })) s initial

/--
Julia source: base/strings/unicode.jl:761-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
titlecase(s::SubString{<:AnnotatedString}; wordsep::Function = !isletter, strict::Bool=true) =
    titlecase(AnnotatedString(s); wordsep=wordsep, strict=strict)
```
-/

def titlecaseAnnotatedSubString {A Sub C : Type}
    (toAnnotated : Sub → A)
    (annotatedCharTransform : {State : Type} → (C → State → UResult (C × State)) → A → State → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (wordsep : C → Bool) (strict : Bool)
    (zero : C) (s : Sub) : UResult A :=
  titlecaseAnnotatedString annotatedCharTransform charOps P wordsep strict zero (toAnnotated s)

structure FirstCaseOps (S C Sub : Type) where
  isempty : S → Bool
  getindex : S → Index → UResult C
  equalChar : C → C → Bool
  convertString : S → UResult JString
  nextind : S → Index → UResult Index
  substring : S → Index → UResult Sub
  string : C → Sub → UResult JString

/--
Julia source: base/strings/unicode.jl:780-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uppercasefirst(s::AbstractString)
    isempty(s) && return ""
    c = s[1]
    c′ = titlecase(c)
    c == c′ ? convert(String, s) :
    string(c′, SubString(s, nextind(s, 1)))
end
```
-/

def uppercasefirstAbstractString {S C Sub : Type} (ops : FirstCaseOps S C Sub)
    (charOps : CharOps C) (P : Utf8proc) (s : S) : UResult JString := do
  if ops.isempty s then pure JuliaLean.Strings.JStr.empty
  else
    let c ← ops.getindex s (JInt.lit .i64 1)
    let cPrime ← titlecaseAbstractChar charOps P c
    if ops.equalChar c cPrime then ops.convertString s
    else ops.string cPrime (← ops.substring s (← ops.nextind s (JInt.lit .i64 1)))

/--
Julia source: base/strings/unicode.jl:814-820 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lowercasefirst(s::AbstractString)
    isempty(s) && return ""
    c = s[1]
    c′ = lowercase(c)
    c == c′ ? convert(String, s) :
    string(c′, SubString(s, nextind(s, 1)))
end
```
-/

def lowercasefirstAbstractString {S C Sub : Type} (ops : FirstCaseOps S C Sub)
    (charOps : CharOps C) (P : Utf8proc) (s : S) : UResult JString := do
  if ops.isempty s then pure JuliaLean.Strings.JStr.empty
  else
    let c ← ops.getindex s (JInt.lit .i64 1)
    let cPrime ← lowercaseAbstractChar charOps P c
    if ops.equalChar c cPrime then ops.convertString s
    else ops.string cPrime (← ops.substring s (← ops.nextind s (JInt.lit .i64 1)))

/--
Julia source: base/strings/unicode.jl:789-797 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uppercasefirst(s::AnnotatedString)
    annotated_chartransform(s, true) do c, state
        if state
            (titlecase(c), false)
        else
            (c, state)
        end
    end
end
```
-/

def uppercasefirstAnnotatedString {A C : Type}
    (annotatedCharTransform : {State : Type} → (C → State → UResult (C × State)) → A → State → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : A) : UResult A :=
  annotatedCharTransform (fun c first =>
    if first then do
      let mapped ← titlecaseAbstractChar charOps P c
      pure (mapped, false)
    else pure (c, first)) s true

/--
Julia source: base/strings/unicode.jl:798-798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uppercasefirst(s::SubString{<:AnnotatedString}) = uppercasefirst(AnnotatedString(s))
```
-/

def uppercasefirstAnnotatedSubString {A Sub C : Type}
    (toAnnotated : Sub → A)
    (annotatedCharTransform : {State : Type} → (C → State → UResult (C × State)) → A → State → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : Sub) : UResult A :=
  uppercasefirstAnnotatedString annotatedCharTransform charOps P (toAnnotated s)

/--
Julia source: base/strings/unicode.jl:823-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lowercasefirst(s::AnnotatedString)
    annotated_chartransform(s, true) do c, state
        if state
            (lowercase(c), false)
        else
            (c, state)
        end
    end
end
```
-/

def lowercasefirstAnnotatedString {A C : Type}
    (annotatedCharTransform : {State : Type} → (C → State → UResult (C × State)) → A → State → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : A) : UResult A :=
  annotatedCharTransform (fun c first =>
    if first then do
      let mapped ← lowercaseAbstractChar charOps P c
      pure (mapped, false)
    else pure (c, first)) s true

/--
Julia source: base/strings/unicode.jl:832-832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lowercasefirst(s::SubString{<:AnnotatedString}) = lowercasefirst(AnnotatedString(s))
```
-/

def lowercasefirstAnnotatedSubString {A Sub C : Type}
    (toAnnotated : Sub → A)
    (annotatedCharTransform : {State : Type} → (C → State → UResult (C × State)) → A → State → UResult A)
    (charOps : CharOps C) (P : Utf8proc) (s : Sub) : UResult A :=
  lowercasefirstAnnotatedString annotatedCharTransform charOps P (toAnnotated s)

/--
Julia source: base/strings/unicode.jl:837-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isgraphemebreak(c1::AbstractChar, c2::AbstractChar) =
    ismalformed(c1) || ismalformed(c2) ||
    ccall(:utf8proc_grapheme_break, Bool, (UInt32, UInt32), c1, c2)

```
-/

def isgraphemebreak {C : Type} (ops : CharOps C) (P : Utf8proc) (c1 c2 : C) : UResult Bool := do
  if ops.malformed c1 || ops.malformed c2 then pure true
  else
    let u1 ← liftChar (ops.toUInt32 c1)
    let u2 ← liftChar (ops.toUInt32 c2)
    pure (P.graphemeBreak u1 u2)


/--
Julia source: base/strings/unicode.jl:853-855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct GraphemeIterator{S<:AbstractString}
    s::S # original string (for generation of SubStrings)
end
```
-/

structure GraphemeIterator (S : Type) where
  s : S

/--
Julia source: base/strings/unicode.jl:858-858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
graphemes(s::AbstractString) = GraphemeIterator{typeof(s)}(s)
```
-/

def graphemes {S : Type} (s : S) : GraphemeIterator S := ⟨s⟩

/--
Julia source: base/strings/unicode.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{GraphemeIterator{S}}) where {S} = SubString{S}
```
-/

def eltypeGrapheme (subStringType : Type → Type) (S : Type) : Type := subStringType S

/--
Julia source: base/strings/unicode.jl:861-861 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{GraphemeIterator{SubString{S}}}) where {S} = SubString{S}
```
-/

def eltypeGraphemeSubString (subStringType : Type → Type) (S : Type) : Type := subStringType S

structure GraphemeStringOps (S C Sub : Type) where
  iterateChars : S → IterSteps C Index UnicodeError
  zeroChar : S → C
  firstindex : S → Index
  ncodeunits : S → Index
  iterateAt : S → Index → UResult (Option (C × Index))
  substring : S → Index → Index → UResult Sub

def graphemeLengthLoop {C : Type} (ops : CharOps C) (P : Utf8proc) :
    IterSteps C Index UnicodeError → C → Int32 → JInt64 → UResult JInt64
  | .done, _, _, count => .ok count
  | .fail error, _, _, _ => .error error
  | .yield c state next, c0, stateValue, count =>
      match isgraphemebreakBang ops P stateValue c0 c with
      | .error error => .error error
      | .ok (breaks, stateValue) =>
          let count := count + JInt.lit .i64 (if breaks then 1 else 0)
          graphemeLengthLoop ops P (next state) c stateValue count
partial_fixpoint

/--
Julia source: base/strings/unicode.jl:863-872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(g::GraphemeIterator{S}) where {S}
    c0 = eltype(S)(0x00000000)
    n = 0
    state = Ref{Int32}(0)
    for c in g.s
        n += isgraphemebreak!(state, c0, c)
        c0 = c
    end
    return n
end
```
-/

def lengthGraphemeIterator {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
    (charOps : CharOps C) (P : Utf8proc) (g : GraphemeIterator S) : UResult JInt64 :=
  graphemeLengthLoop charOps P (ops.iterateChars g.s)
    (ops.zeroChar g.s) 0 (JInt.lit .i64 0)

def graphemeIterLoop {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
    (charOps : CharOps C) (P : Utf8proc) (s : S)
    (state : Int32) (c0 : C) (j k : Index) :
    Option (UResult (Int32 × Index × Index)) :=
  if k.val ≤ (ops.ncodeunits s).val then
    match ops.iterateAt s k with
    | .error error => some (.error error)
    | .ok none => some (.error .typeError)
    | .ok (some (c, ell)) =>
        match isgraphemebreakBang charOps P state c0 c with
        | .error error => some (.error error)
        | .ok (true, state) => some (.ok (state, j, k))
        | .ok (false, state) => graphemeIterLoop ops charOps P s state c k ell
  else some (.ok (state, j, k))
partial_fixpoint

/--
Julia source: base/strings/unicode.jl:874-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(g::GraphemeIterator, i_=(Int32(0),firstindex(g.s)))
    s = g.s
    statei, i = i_
    state = Ref{Int32}(statei)
    j = i
    y = iterate(s, i)
    y === nothing && return nothing
    c0, k = y
    while k <= ncodeunits(s) # loop until next grapheme is s[i:j]
        c, ℓ = iterate(s, k)::NTuple{2,Any}
        isgraphemebreak!(state, c0, c) && break
        j = k
        k = ℓ
        c0 = c
    end
    return (SubString(s, i, j), (state[], k))
end
```
-/

def iterateGraphemeIterator {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
    (charOps : CharOps C) (P : Utf8proc) (g : GraphemeIterator S)
    (stateInput : Option (Int32 × Index)) :
    Option (UResult (Option (Sub × (Int32 × Index)))) :=
  let (statei, i) := match stateInput with
    | some state => state
    | none => (0, ops.firstindex g.s)
  match ops.iterateAt g.s i with
  | .error error => some (.error error)
  | .ok none => some (.ok none)
  | .ok (some (c0, k)) =>
      match graphemeIterLoop ops charOps P g.s statei c0 i k with
      | none => none
      | some (.error error) => some (.error error)
      | some (.ok (state, j, k)) =>
          match ops.substring g.s i j with
          | .error error => some (.error error)
          | .ok substring => some (.ok (some (substring, (state, k))))

/--
Julia source: base/strings/unicode.jl:892-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(g1::GraphemeIterator, g2::GraphemeIterator) = g1.s == g2.s
```
-/

def eqGraphemeIterator {S : Type} (equalString : S → S → Bool)
    (g1 g2 : GraphemeIterator S) : Bool := equalString g1.s g2.s

/--
Julia source: base/strings/unicode.jl:893-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(g::GraphemeIterator, h::UInt) = hash(g.s, h)
```
-/

def hashGraphemeIterator {S : Type} (hashString : S → UInt64 → UInt64)
    (g : GraphemeIterator S) (h : UInt64) : UInt64 := hashString g.s h

/--
Julia source: base/strings/unicode.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(g1::GraphemeIterator, g2::GraphemeIterator) = isless(g1.s, g2.s)
```
-/

def islessGraphemeIterator {S : Type} (lessString : S → S → Bool)
    (g1 g2 : GraphemeIterator S) : Bool := lessString g1.s g2.s

/--
Julia source: base/strings/unicode.jl:896-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, g::GraphemeIterator{S}) where {S} = print(io, "length-$(length(g)) GraphemeIterator{$S} for \"$(g.s)\"")
```
-/

def showGraphemeIterator {S IO C Sub : Type}
    (ops : GraphemeStringOps S C Sub) (charOps : CharOps C) (P : Utf8proc)
    (typeName : Type → String) (string : S → String) (toString : JInt64 → String)
    (print : IO → List String → IO) (io : IO) (g : GraphemeIterator S) : UResult IO := do
  let len ← lengthGraphemeIterator ops charOps P g
  pure (print io ["length-", toString len, " GraphemeIterator{", typeName S,
    "} for \"", string g.s, "\""])

end JuliaLean.base.strings.unicode

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-- The utf8proc entry points Julia calls. -/
structure Utf8proc where
  /-- `utf8proc_toupper(c::UInt32)::UInt32` -/
  toupper : UInt32 → UInt32
  /-- `utf8proc_tolower(c::UInt32)::UInt32` -/
  tolower : UInt32 → UInt32
  /-- `utf8proc_totitle(c::UInt32)::UInt32` -/
  totitle : UInt32 → UInt32
  /-- `utf8proc_category(c::UInt32)::Cint`, a code in `0:29`. -/
  category : UInt32 → Nat
  /-- `utf8proc_grapheme_break_stateful(c1::UInt32, c2::UInt32, state::Ref{Int32})::Bool`:
  the result and the new value of `state[]`. -/
  gbStateful : Int32 → UInt32 → UInt32 → Bool × Int32
  /-- `utf8proc_decompose_char(uc, dst, bufsize, options, C_NULL)`: the code points of
  the decomposition of `uc` under `options` (`.ok`), or the negative error code it
  returns. It stores the first `min(length, bufsize)` of them at `dst` and returns the
  full length. -/
  decomposeChar : UInt32 → Nat → Except Int (List UInt32)
  /-- `utf8proc_get_property(uc).combining_class` (the `UInt16` that
  `combining_class` loads, `stdlib/Unicode/src/Unicode.jl:228`). -/
  combiningClass : UInt32 → UInt16

/-! ## Option bits, `base/strings/unicode.jl:136-149` -/

def STABLE : Nat := 1 <<< 1
def COMPAT : Nat := 1 <<< 2
def COMPOSE : Nat := 1 <<< 3
def DECOMPOSE : Nat := 1 <<< 4
def IGNORE : Nat := 1 <<< 5
def REJECTNA : Nat := 1 <<< 6
def NLF2LS : Nat := 1 <<< 7
def NLF2PS : Nat := 1 <<< 8
def NLF2LF : Nat := NLF2LS ||| NLF2PS
def STRIPCC : Nat := 1 <<< 9
def CASEFOLD : Nat := 1 <<< 10
def LUMP : Nat := 1 <<< 12
def STRIPMARK : Nat := 1 <<< 13

/-! ## Character functions -/

/-- `'a' <= c <= 'z'` on bit patterns (`isless(x::Char, y::Char)`, `base/char.jl:264`). -/
abbrev inRange (lo hi c : UInt32) : Bool := decide (lo ≤ c) && decide (c ≤ hi)

/-- The non-ASCII branch of the case mappings: `T(@ccall f(c::UInt32)::UInt32)`. The
argument conversion `UInt32(c)` throws `InvalidCharError` for a malformed `c`;
`Char(::UInt32)` throws `CodePointError` above `0x1fffff`. -/
def viaUtf8proc (f : UInt32 → UInt32) (c : UInt32) : UJl UInt32 := do
  let u ← liftS (codepoint c)
  liftS (charOfU32 (f u))

/-- `lowercase(c::T)`, `base/strings/unicode.jl:318-319`. For an ASCII `c`,
`c + 0x20` is `bitcast(Char, (z % UInt32) << 24)` with `z` the code point plus 32
(`+%`, `base/char.jl:285-294`), i.e. the bit pattern plus `0x20000000`. -/
def lowercaseChar (P : Utf8proc) (c : UInt32) : UJl UInt32 :=
  if isasciiChar c then .ok (if inRange 0x41000000 0x5a000000 c then c + 0x20000000 else c)
  else viaUtf8proc P.tolower c

/-- `uppercase(c::T)`, `base/strings/unicode.jl:339-340`. -/
def uppercaseChar (P : Utf8proc) (c : UInt32) : UJl UInt32 :=
  if isasciiChar c then .ok (if inRange 0x61000000 0x7a000000 c then c - 0x20000000 else c)
  else viaUtf8proc P.toupper c

/-- `titlecase(c::T)`, `base/strings/unicode.jl:364-365`. -/
def titlecaseChar (P : Utf8proc) (c : UInt32) : UJl UInt32 :=
  if isasciiChar c then .ok (if inRange 0x61000000 0x7a000000 c then c - 0x20000000 else c)
  else viaUtf8proc P.totitle c

/-- `unsafe_codepoint(c::Char)`, `base/char.jl:183-191`: `UInt32(c)` without the
malformation check. -/
def unsafeCodepoint (c : UInt32) : UInt32 :=
  let u := c
  if u < 0x80000000 then u >>> 24
  else
    let l1 := clo32 u
    let t0 := land56 (ctz32 u)
    let u := u &&& ushr32 0xffffffff l1
    let u := ushr32 u t0
    ((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
      ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)

/-- `category_code(c::AbstractChar)` and `category_code(x::Integer)`,
`base/strings/unicode.jl:372-381`. -/
def categoryCode (P : Utf8proc) (c : UInt32) : Nat :=
  if !ismalformed c then
    let x := unsafeCodepoint c
    if x ≤ 0x10ffff then P.category x else 30
  else 31

/-- `isletter(c) = UTF8PROC_CATEGORY_LU <= category_code(c) <= UTF8PROC_CATEGORY_LO`
(`LU = 1`, `LO = 5`), `base/strings/unicode.jl:522`. -/
def isletterChar (P : Utf8proc) (c : UInt32) : Bool :=
  decide (1 ≤ categoryCode P c) && decide (categoryCode P c ≤ 5)

/-- `iscntrl(c::AbstractChar) = c <= '\x1f' || '\x7f' <= c <= '\u9f'`,
`base/strings/unicode.jl:568`, with the bit-pattern comparison of `Char`:
`'\x1f'` is `0x1f000000`, `'\x7f'` is `0x7f000000`, `'\u9f'` is `0xc29f0000`. -/
def iscntrlChar (c : UInt32) : Bool :=
  decide (c ≤ 0x1f000000) || (decide (0x7f000000 ≤ c) && decide (c ≤ 0xc29f0000))

/-- `isvalid(::Type{T}, c::Integer) = isvalid(T, Unsigned(c))` and
`isvalid(::Type{<:AbstractChar}, c::Unsigned)`, `base/strings/unicode.jl:59-60`, for
`c::Int`: `Unsigned(x::Int64) = UInt64(x)` (`base/int.jl:1213`) throws
`InexactError` for a negative `x`. -/
def isvalidCharInt (x : JInt64) : Jl Bool := do
  let c ← JInt.convert (IntTy.u64.name) .u64 x.val
  pure (decide (c.val ≤ 0xd7ff) || (decide (0xe000 ≤ c.val) && decide (c.val ≤ 0x10ffff)))

/-! ## String case mappings -/

/-- The loop of `map(f, s::AbstractString)`, `base/strings/basic.jl:657-671`: `f` is
applied to each character in iteration order; its results are stored with
`__unsafe_string!` (the character's bytes). -/
def mapCharsM (f : UInt32 → UJl UInt32) : List UInt32 → UJl (List UInt32)
  | [] => .ok []
  | c :: cs => do
    let c' ← f c
    let rest ← mapCharsM f cs
    pure (c' :: rest)

/-- `map(f, s::AbstractString)`, `base/strings/basic.jl:657-671`. -/
def mapStr (f : UInt32 → UJl UInt32) (s : JStr) : UJl JStr := do
  let cs ← mapCharsM f (chars s)
  liftS (stringOfChars cs)

/-- `uppercase(s::AbstractString) = map(uppercase, s)`, `base/strings/unicode.jl:676`. -/
def uppercaseStr (P : Utf8proc) (s : JStr) : UJl JStr := mapStr (uppercaseChar P) s

/-- `lowercase(s::AbstractString) = map(lowercase, s)`, `base/strings/unicode.jl:693`. -/
def lowercaseStr (P : Utf8proc) (s : JStr) : UJl JStr := mapStr (lowercaseChar P) s

/-! ## `normalize` keywords -/

/-- The Boolean keywords of `normalize(s; ...)`, `base/strings/unicode.jl:202-217`. -/
structure NormKw where
  stable : Bool := false
  compat : Bool := false
  compose : Bool := true
  decompose : Bool := false
  stripignore : Bool := false
  rejectna : Bool := false
  newline2ls : Bool := false
  newline2ps : Bool := false
  newline2lf : Bool := false
  stripcc : Bool := false
  casefold : Bool := false
  lump : Bool := false
  stripmark : Bool := false
  deriving Repr, DecidableEq

/-- `x | y` on the `Int` flags; all values are in `0:2^14-1`, where `Int` bitwise or
is `Nat.lor`. -/
abbrev orIf (b : Bool) (flags bit : Nat) : Nat := if b then flags ||| bit else flags

/-- `Bool` to `Int` in `newline2ls + newline2ps + newline2lf`. -/
abbrev b2n (b : Bool) : Nat := if b then 1 else 0

/-- The flag computation of `normalize(s; kw...)`, `base/strings/unicode.jl:218-240`:
the `flags` passed to `utf8proc_map`, or the `ArgumentError` thrown before the call. -/
def normalizeFlags (k : NormKw) : Jl Nat :=
  let flags := 0
  let flags := orIf k.stable flags STABLE
  let flags := orIf k.compat flags COMPAT
  let r : Jl Nat :=
    if k.decompose then .ok (flags ||| DECOMPOSE)
    else if k.compose then .ok (flags ||| COMPOSE)
    else if k.compat || k.stripmark then
      .error (.argumentError "compat=true or stripmark=true require compose=true or decompose=true")
    else .ok flags
  match r with
  | .error e => .error e
  | .ok flags =>
    let flags := orIf k.stripignore flags IGNORE
    let flags := orIf k.rejectna flags REJECTNA
    if b2n k.newline2ls + b2n k.newline2ps + b2n k.newline2lf > 1 then
      .error (.argumentError "only one newline conversion may be specified")
    else
      let flags := orIf k.newline2ls flags NLF2LS
      let flags := orIf k.newline2ps flags NLF2PS
      let flags := orIf k.newline2lf flags NLF2LF
      let flags := orIf k.stripcc flags STRIPCC
      let flags := orIf k.casefold flags CASEFOLD
      let flags := orIf k.lump flags LUMP
      .ok (orIf k.stripmark flags STRIPMARK)
end JuliaLean.RegexUnicode.Uni
/-!
# Unicode character classes used by the printers

`isprint`, `jl_id_start_char` and `jl_id_char` consult the utf8proc tables for
non-ASCII code points. Those tables are data, not code, so the model takes
them as a parameter `UData`; every property quantifies over all tables. The
ASCII part of each predicate and the out-of-range behaviour are fixed by the
Julia and C sources and are modelled exactly.
-/

namespace JuliaLean.Show

open JuliaLean.Strings

/-- The Unicode data the printers consult for code points `≥ 0x80`.
* `cat u` is `utf8proc_category(u)` (`base/strings/unicode.jl:379-381`) for
  `0x80 ≤ u ≤ 0x10ffff`;
* `idStart u` is `is_wc_cat_id_start(u, utf8proc_category(u))`
  (`src/flisp/julia_extensions.c:67-125`) for `0xa1 ≤ u ≤ 0x10ffff`;
* `idChar u` is the non-ASCII disjunction of `jl_id_char`
  (`src/flisp/julia_extensions.c:139-155`) for `0xa1 ≤ u ≤ 0x10ffff`. -/
structure UData where
  cat : UInt32 → Nat
  idStart : UInt32 → Bool
  idChar : UInt32 → Bool

/-- `utf8proc_category(u)` for the 128 ASCII code points, as printed by
`[Base.Unicode.category_code(Char(i)) for i in 0:127]` on Julia 1.13.2 and
master. -/
def asciiCats : List Nat :=
  [26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,
   23,18,18,18,20,18,18,18,14,15,18,19,18,13,18,18,9,9,9,9,9,9,9,9,9,9,18,18,19,19,19,18,
   18,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,14,18,15,21,12,
   21,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,14,19,15,19,26]

/-- `utf8proc_category(u)` for `u ≤ 0x10ffff`. -/
def utf8procCategory (d : UData) (u : UInt32) : Nat :=
  if u < 0x80 then asciiCats.getD u.toNat 0 else d.cat u

/-- `category_code(c::Char)`, `base/strings/unicode.jl:372-381`: 31 for
malformed chars, 30 for code points above `0x10ffff`. -/
def categoryCode (d : UData) (c : UInt32) : Nat :=
  if ismalformed c then 31
  else match codepoint c with
    | .ok u => if u ≤ 0x10ffff then utf8procCategory d u else 30
    | .error _ => 31

/-- `isprint(c) = UTF8PROC_CATEGORY_LU <= category_code(c) <= UTF8PROC_CATEGORY_ZS`,
`base/strings/unicode.jl:642` (`LU = 1`, `ZS = 23`). -/
def isprint (d : UData) (c : UInt32) : Bool :=
  decide (1 ≤ categoryCode d c) && decide (categoryCode d c ≤ 23)

/-- `jl_id_start_char(wc)`, `src/flisp/julia_extensions.c:127-137`. -/
def idStartChar (d : UData) (wc : UInt32) : Bool :=
  if (decide (65 ≤ wc) && decide (wc ≤ 90)) || (decide (97 ≤ wc) && decide (wc ≤ 122)) || wc == 95 then true
  else if decide (wc < 0xa1) || decide (wc > 0x10ffff) then false
  else if wc == 0x1f8b2 then true
  else d.idStart wc

/-- `jl_id_char(wc)`, `src/flisp/julia_extensions.c:139-157`. -/
def idChar (d : UData) (wc : UInt32) : Bool :=
  if (decide (65 ≤ wc) && decide (wc ≤ 90)) || (decide (97 ≤ wc) && decide (wc ≤ 122)) || wc == 95 ||
      (decide (48 ≤ wc) && decide (wc ≤ 57)) || wc == 33 then true
  else if decide (wc < 0xa1) || decide (wc > 0x10ffff) then false
  else d.idChar wc

/-- The Unicode data that classifies every non-ASCII code point as unassigned
(category `Cn = 0`) and not an identifier character; used to instantiate
counterexamples whose behaviour does not depend on the tables. -/
def UData.empty : UData := ⟨fun _ => 0, fun _ => false, fun _ => false⟩

end JuliaLean.Show

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-- `isgraphemebreak!(state, c1, c2)`, `base/strings/unicode.jl:844-851`: a malformed
character resets the state and breaks; otherwise the `ccall` converts both characters
with `UInt32(c)` (`base/char.jl:158-171`, which on master converts overlong encodings;
1.13.2 throws `InvalidCharError` for them). Returns the result and the new `state[]`. -/
def isgraphemebreakBang (P : Utf8proc) (st : Int32) (c1 c2 : UInt32) : UJl (Bool × Int32) :=
  if ismalformed c1 || ismalformed c2 then .ok (true, 0)
  else
    match codepoint c1 with
    | .error e => .error (.str e)
    | .ok u1 =>
      match codepoint c2 with
      | .error e => .error (.str e)
      | .ok u2 => .ok (P.gbStateful st u1 u2)

/-- Prepend to a result. -/
def consM {α : Type} (c : α) : UJl (List α) → UJl (List α)
  | .ok r => .ok (c :: r)
  | .error e => .error e

/-- The type of `isgraphemebreak!(state, c1, c2)`: old `state[]`, `c1`, `c2` to the
result and the new `state[]`. -/
abbrev GbFn := Int32 → UInt32 → UInt32 → UJl (Bool × Int32)

/-! ## `titlecase` -/

/-- The loop of `titlecase(s; wordsep, strict)`, `base/strings/unicode.jl:723-741`:
the characters printed to `b`. `gb` is `isgraphemebreak!`, `tc` is `titlecase(c)`,
`lc` is `lowercase(c)`. `wordsep` is a pure predicate (any Julia function returning
`Bool` without side effects). -/
def titleLoop (gb : GbFn) (tc lc : UInt32 → UJl UInt32) (wordsep : UInt32 → Bool)
    (strict : Bool) : List UInt32 → Bool → Int32 → UInt32 → UJl (List UInt32)
  | [], _, _, _ => .ok []
  | c :: cs, startword, st, c0 =>
    match gb st c0 c with
    | .error e => .error e
    | .ok (b, st) =>
      if b && wordsep c then consM c (titleLoop gb tc lc wordsep strict cs true st c)
      else
        let out : UJl UInt32 := if startword then tc c else if strict then lc c else .ok c
        match out with
        | .error e => .error e
        | .ok c' => consM c' (titleLoop gb tc lc wordsep strict cs false st c)

/-- `titlecase` on the characters `cs` of `s`: `print(b, c)` writes the bytes of `c`
and `takestring!(b)` returns them. `c0 = eltype(s)(0x00000000)` is the bit pattern `0`. -/
def titlecaseOf (gb : GbFn) (tc lc : UInt32 → UJl UInt32) (wordsep : UInt32 → Bool)
    (strict : Bool) (cs : List UInt32) : UJl JStr :=
  match titleLoop gb tc lc wordsep strict cs true 0 0 with
  | .error e => .error e
  | .ok cs => liftS (stringOfChars cs)

/-- `titlecase(s; wordsep, strict)`, `base/strings/unicode.jl:723-741`. -/
def titlecaseStr (P : Utf8proc) (wordsep : UInt32 → Bool) (strict : Bool) (s : JStr) :
    UJl JStr :=
  titlecaseOf (isgraphemebreakBang P) (titlecaseChar P) (lowercaseChar P) wordsep strict
    (chars s)
/-! ## Grapheme iteration -/

/-- The calls the grapheme functions make on one string `s`. -/
structure GOps where
  /-- `iterate(s, i)` -/
  it : JInt64 → Option (UInt32 × JInt64)
  /-- `s[i]` -/
  gi : JInt64 → SJl UInt32
  /-- `nextind(s, i)` -/
  nx : JInt64 → SJl JInt64
  /-- `SubString(s, i, j)` -/
  sub : JInt64 → JInt64 → SJl JSub
  /-- `isgraphemebreak!` -/
  gb : GbFn
  /-- `ncodeunits(s)` -/
  ncu : JInt64
  /-- `lastindex(s)` -/
  ilast : JInt64
  /-- Iteration bound: every loop advances the index, so `ncodeunits(s) + 1` steps
  reach the end. -/
  fuel : Nat

/-- `lastindex(s::String) = thisind(s, ncodeunits(s))`, `base/strings/string.jl:249`:
the index `thisind` returns (it cannot throw: `ncodeunits(s)` is in bounds or `0`). -/
def lastOf : SJl JInt64 → JInt64
  | .ok j => j
  | .error _ => ix 0

/-- The calls on a `String` `s` with utf8proc table `P`. -/
def gops (P : Utf8proc) (s : JStr) : GOps where
  it := iterate s
  gi := getindex s
  nx := nextind s
  sub := fun i j => substring s i j
  gb := isgraphemebreakBang P
  ncu := ncodeunits s
  ilast := lastOf (thisind s (ncodeunits s))
  fuel := s.bytes.length + 1

/-- The `while` loop of `iterate(g::GraphemeIterator, i_)`,
`base/strings/unicode.jl:882-887`, from `j`, `k` with previous character `c0`. The
`::NTuple{2,Any}` assertion throws `TypeError` when `iterate` returns `nothing`.
Returns `state[]`, `j`, `k`. -/
def gIterLoop (O : GOps) : Nat → Int32 → UInt32 → JInt64 → JInt64 →
    UJl (Int32 × JInt64 × JInt64)
  | 0, _, _, _, _ => .error .fuel
  | f + 1, st, c0, j, k =>
    if k.val ≤ O.ncu.val then
      match O.it k with
      | none => .error .typeError
      | some (c, l) =>
        match O.gb st c0 c with
        | .error e => .error e
        | .ok (true, st) => .ok (st, j, k)
        | .ok (false, st) => gIterLoop O f st c k l
    else .ok (st, j, k)

/-- `iterate(g::GraphemeIterator, (statei, i))`, `base/strings/unicode.jl:874-890`. -/
def gIterate (O : GOps) (st : Int32) (i : JInt64) : UJl (Option (JSub × Int32 × JInt64)) :=
  match O.it i with
  | none => .ok none
  | some (c0, k) =>
    match gIterLoop O O.fuel st c0 i k with
    | .error e => .error e
    | .ok (st, j, k) =>
      match O.sub i j with
      | .error e => .error (.str e)
      | .ok g => .ok (some (g, st, k))

/-- The elements of `collect(graphemes(s))`: `iterate` from `(Int32(0), firstindex(s))`
until `nothing`. -/
def gCollectFrom (O : GOps) : Nat → Int32 → JInt64 → UJl (List JSub)
  | 0, _, _ => .error .fuel
  | f + 1, st, i =>
    match gIterate O st i with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (g, st, i)) => consM g (gCollectFrom O f st i)

/-- `collect(graphemes(s))`. -/
def gCollect (P : Utf8proc) (s : JStr) : UJl (List JSub) :=
  gCollectFrom (gops P s) (s.bytes.length + 1) 0 (ix 1)

/-- The loop of `length(g::GraphemeIterator)`, `base/strings/unicode.jl:863-871`:
`for c in g.s` calls `iterate(s, i)` from `firstindex(s) = 1` until `nothing`. -/
def gLengthLoop (O : GOps) : Nat → Int32 → UInt32 → JInt64 → JInt64 → UJl JInt64
  | 0, _, _, _, _ => .error .fuel
  | f + 1, st, c0, i, n =>
    match O.it i with
    | none => .ok n
    | some (c, i) =>
      match O.gb st c0 c with
      | .error e => .error e
      | .ok (b, st) => gLengthLoop O f st c i (n + bInt b)

/-- `length(graphemes(s))`. -/
def gLength (P : Utf8proc) (s : JStr) : UJl JInt64 :=
  gLengthLoop (gops P s) (s.bytes.length + 1) 0 0 (ix 1) (ix 0)
end JuliaLean.RegexUnicode.Uni
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

namespace JuliaLean.Show

/-- `isxdigit(c::AbstractChar)`, `base/strings/unicode.jl:659`. -/
def isxdigit (c : UInt32) : Bool :=
  (decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x39)) || (decide (ac 0x61 ≤ c) && decide (c ≤ ac 0x66)) ||
    (decide (ac 0x41 ≤ c) && decide (c ≤ ac 0x46))

end JuliaLean.Show

namespace JuliaLean.MissingChar

/-- `isvalid(::Type{<:AbstractChar}, c::Unsigned)`, `base/strings/unicode.jl:59`. -/
def isvalidCharU (c : Nat) : Bool := decide (c ≤ 0xd7ff) || (decide (0xe000 ≤ c) && decide (c ≤ 0x10ffff))

/-- `isvalid(::Type{T}, c::Integer) = isvalid(T, Unsigned(c))`,
`base/strings/unicode.jl:60`, for `c::Int64`: `Unsigned(c)` is
`convert(UInt64, c)`, an `InexactError` for negative `c`. -/
def isvalidCharInt (c : JInt64) : Jl Bool := do
  let u ← JInt.convert (IntTy.u64.name) .u64 c.val
  .ok (isvalidCharU u.val.toNat)
end JuliaLean.MissingChar
/-!
# `textwidth`, `base/strings/unicode.jl:270-298`

The column width of a valid non-ASCII character comes from the C library
call `utf8proc_charwidth`, which the model does not contain. Every
definition here takes that function as the parameter `cw`, mapping a code
point to its width; properties quantify over all `cw` (utf8proc returns 0, 1
or 2).
-/

namespace JuliaLean.StringUtil

open JuliaLean.Strings

/-- `textwidth(c::Char)`, `base/strings/unicode.jl:272-282`:
`b = bswap(u)`; `b < 0x7f && return Int(b >= 0x20)`; malformed or overlong
characters have width 1; otherwise `utf8proc_charwidth(unsafe_codepoint(c))`,
here `cw` of the code point. `codepoint` cannot fail on that branch (it
rejects exactly the malformed characters), so its error case is unreachable. -/
def textwidthChar (cw : UInt32 → Int) (c : UInt32) : Int :=
  let b := bswap32 c
  if b < 0x7f then (if b ≥ 0x20 then 1 else 0)
  else if ismalformed c || isOverlongEnc c then 1
  else
    match codepoint c with
    | .ok u => cw u
    | .error _ => 1

/-- `textwidth(s::String) = mapreduce(textwidth, +, s; init=0)`,
`base/strings/unicode.jl:297`: the sum over the characters that iterating `s`
yields (`Strings.chars`). The sum is an `Int` in Julia; with widths `0 ≤ cw ≤ 2`
and fewer than `2^62` characters it stays below `2^63`, so it never wraps. -/
def textwidth (cw : UInt32 → Int) (s : JStr) : Int :=
  (chars s).foldl (fun acc c => acc + textwidthChar cw c) 0

end JuliaLean.StringUtil

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean JuliaLean.ParsePrint

/-- Code points of Unicode categories Zs, Zl and Zp. -/
def isZsZlZp (cp : Nat) : Bool :=
  cp == 0x20 || cp == 0xa0 || cp == 0x1680 || (0x2000 ≤ cp && cp ≤ 0x200a) ||
    cp == 0x2028 || cp == 0x2029 || cp == 0x202f || cp == 0x205f || cp == 0x3000

/-- `isspace(c::Char)` on the raw `UInt32` of `c`, `base/strings/unicode.jl:624-626`:
`Char` comparisons compare raw values; `category_code` is 31 for malformed
characters (`base/strings/unicode.jl:372-382`). -/
def isspaceChar (u : Nat) : Bool :=
  u == 0x20000000 || (0x09000000 ≤ u && u ≤ 0x0d000000) || u == 0xc2850000 ||
    (0xc2a00000 ≤ u && !ismalformed u && isZsZlZp (unsafeCodepoint u))

end JuliaLean.ParsePrint.IntParse
