import JuliaLean.Core
import JuliaLean.base.char
import JuliaLean.base.int
import JuliaLean.base.rational
import JuliaLean.base.strings.basic
import JuliaLean.Strings.Ops

namespace JuliaLean.base.strings.unicode

open JuliaLean
open JuliaLean.base.char
open JuliaLean.base.strings.basic
open JuliaLean.base.rational

abbrev JString := JuliaLean.Strings.JStr
abbrev JSubString := JuliaLean.Strings.JSub
abbrev Index := JuliaLean.base.strings.basic.Index

inductive UnicodeError where
  | invalidChar
  | codePointError
  | jl (error : JlError)
  | string (error : JuliaLean.Strings.SErr)
  | errorException (message : String)
  | argumentError (message : String)
  | methodError
  | typeError
  | boundsError

abbrev UResult (α : Type) := Except UnicodeError α

def liftChar {α : Type} : CharResult α → UResult α
  | .ok value => .ok value
  | .error (.invalidChar _) => .error .invalidChar
  | .error (.codePointError _) => .error .codePointError
  | .error .boundsError => .error .boundsError
  | .error (.foreign error) => .error (.jl error)

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


/--
Julia source: base/strings/unicode.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
textwidth(s::AbstractString) = mapreduce(textwidth, +, s; init=0)
```
-/

def textwidthAbstractString {S C : Type}
    (mapreduce : (C → UResult Int) → (Int → Int → Int) → S → Int → UResult Int)
    (ops : CharOps C) (P : Utf8proc) (s : S) : UResult Int :=
  mapreduce (textwidthAbstractChar ops P) (· + ·) s 0

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

def category_string_Char (P : Utf8proc)
    (categoryCodeBounds : CategoryCodeBounds (category_code_AbstractChar charOps P))
    (c : JChar) : UResult String :=
  match h : category_code_AbstractChar charOps P c with
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
