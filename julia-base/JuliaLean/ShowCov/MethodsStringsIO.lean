import JuliaLean.ShowCov.MethodSupport
import JuliaLean.ShowCov.StringsIO
import JuliaLean.Show.Escape

namespace JuliaLean.ShowCov.Methods.StringsIOFile

open JuliaLean.Registry
open JuliaLean.ShowCov.StringsIO
open JuliaLean.ShowCov.Methods
open JuliaLean.Show JuliaLean.Strings

def m32 (shown : Shown) := printAny shown
def P32 : Prop := ∀ shown, HasResult (m32 shown)
theorem p32 : P32 := fun shown => hasResult (m32 shown)

def m42 (shown : List Shown) := printMany shown
def P42 : Prop := ∀ shown, HasResult (m42 shown)
theorem p42 : P42 := fun shown => hasResult (m42 shown)

def m77 (shown : List Shown) := printlnMany shown
def P77 : Prop := ∀ shown, HasResult (m77 shown)
theorem p77 : P77 := fun shown => hasResult (m77 shown)

def m104 (f : Props → Shown) (context : Ctx) (sizehint : Nat) := sprint f context sizehint
def P104 : Prop := ∀ f context sizehint, HasResult (m104 f context sizehint)
theorem p104 : P104 := fun f context sizehint => hasResult (m104 f context sizehint)

def m116 (x : Arg) := strSizehint x
def P116 : Prop := ∀ x, HasResult (m116 x)
theorem p116 : P116 := fun x => hasResult (m116 x)

def m134 (xs : List (Arg × Shown)) := printToString xs
def P134 : Prop := ∀ xs, HasResult (m134 xs)
theorem p134 : P134 := fun xs => hasResult (m134 xs)

def m150 (env : Props) (xs : List (Arg × (Props → Shown))) := stringWithEnv env xs
def P150 : Prop := ∀ env xs, HasResult (m150 env xs)
theorem p150 : P150 := fun env xs => hasResult (m150 env xs)

def m186 (xs : List (Arg × Shown)) := string xs
def P186 : Prop := ∀ xs, HasResult (m186 xs)
theorem p186 : P186 := fun xs => hasResult (m186 xs)

def m188 (symbolName : String) := stringSym symbolName
def P188 : Prop := ∀ name, m188 name = name
theorem p188 : P188 := by intro; rfl

def m192 (chars : List Char) := printAbstractString chars
def P192 : Prop := ∀ chars, HasResult (m192 chars)
theorem p192 : P192 := fun chars => hasResult (m192 chars)

def m193 (chars : List Char) := writeAbstractString chars
def P193 : Prop := ∀ chars, HasResult (m193 chars)
theorem p193 : P193 := fun chars => hasResult (m193 chars)

def m194 (data : UData) (s : JStr) := printQuoted data s
def P194 : Prop := ∀ data s, HasResult (m194 data s)
theorem p194 : P194 := fun data s => hasResult (m194 data s)

def m197 (input : LimitIn) (limit : Option Int) := showLimited input limit
def P197 : Prop := ∀ input limit, HasResult (m197 input limit)
theorem p197 : P197 := fun input limit => hasResult (m197 input limit)

def m217 (units : String) (skip : Int) := skipText units skip
def P217 : Prop := ∀ units skip, HasResult (m217 units skip)
theorem p217 : P217 := fun units skip => hasResult (m217 units skip)

def m242 (s : String) := writeString s
def P242 : Prop := ∀ s, HasResult (m242 s)
theorem p242 : P242 := fun s => hasResult (m242 s)

def m246 (s : String) := printString s
def P246 : Prop := ∀ s, HasResult (m246 s)
theorem p246 : P246 := fun s => hasResult (m246 s)

def m284 (f : Props → Shown) (context : Ctx) := repr f context
def P284 : Prop := ∀ f context, HasResult (m284 f context)
theorem p284 : P284 := fun f context => hasResult (m284 f context)

def m286 (f : Props → Shown) := limitrepr f
def P286 : Prop := ∀ f, HasResult (m286 f)
theorem p286 : P286 := fun f => hasResult (m286 f)

structure BufferSlice where
  parentBytes : Nat
  firstByte : Nat
  byteCount : Nat
  deriving DecidableEq, Repr

/-- `IOBuffer(str::String)` wraps all string bytes, `base/strings/io.jl:306`. -/
def m306 (bytes : Nat) : BufferSlice := ⟨bytes, 1, bytes⟩
def P306 : Prop := ∀ bytes, m306 bytes = ⟨bytes, 1, bytes⟩
theorem p306 : P306 := by intro; rfl

/-- `IOBuffer(s::SubString{String})` wraps the parent then views
`offset+1:offset+sizeof(s)`, `base/strings/io.jl:307`. -/
def m307 (parentBytes offset bytes : Nat) : BufferSlice := ⟨parentBytes, offset + 1, bytes⟩
def P307 : Prop := ∀ parent offset bytes, offset + bytes ≤ parent →
  m307 parent offset bytes = ⟨parent, offset + 1, bytes⟩
theorem p307 : P307 := by intro parent offset bytes _; rfl

def m330 (items : List String) (delim last : String) := joinLast items delim last
def P330 : Prop := ∀ items delim last, HasResult (m330 items delim last)
theorem p330 : P330 := fun items delim last => hasResult (m330 items delim last)

def m346 (items : List String) (delim : String) := join2 items delim
def P346 : Prop := ∀ items delim, HasResult (m346 items delim)
theorem p346 : P346 := fun items delim => hasResult (m346 items delim)

def m356 (info : JoinInfo) (items : List String) (delim last : Option String) :=
  (joinKindGeneric info, joinText items delim last)
def P356 : Prop := ∀ info items delim last, HasResult (m356 info items delim last)
theorem p356 : P356 := fun info items delim last => hasResult (m356 info items delim last)

def m378 (info : JoinInfo) (items : List String) (delim last : Option String) :=
  (joinKindTuple info, joinText items delim last)
def P378 : Prop := ∀ info items delim last, HasResult (m378 info items delim last)
theorem p378 : P378 := fun info items delim last => hasResult (m378 info items delim last)

def m389 (info : JoinInfo) (items : List String) := m356 info items none none
def P389 : Prop := ∀ info items, HasResult (m389 info items)
theorem p389 : P389 := fun info items => hasResult (m389 info items)

def m390 (info : JoinInfo) (items : List String) (delim : String) :=
  m356 info items (some delim) none
def P390 : Prop := ∀ info items delim, HasResult (m390 info items delim)
theorem p390 : P390 := fun info items delim => hasResult (m390 info items delim)

def m391 (info : JoinInfo) (items : List String) (delim last : String) :=
  m356 info items (some delim) (some last)
def P391 : Prop := ∀ info items delim last, HasResult (m391 info items delim last)
theorem p391 : P391 := fun info items delim last => hasResult (m391 info items delim last)

def m395 (c : Option UInt32) := needFullHex c
def P395 : Prop := ∀ c, HasResult (m395 c)
theorem p395 : P395 := fun c => hasResult (m395 c)

def m396 (c : Option UInt32) := escapeNul c
def P396 : Prop := ∀ c, HasResult (m396 c)
theorem p396 : P396 := fun c => hasResult (m396 c)

def m459 (d : UData) (s : JStr) (esc keep : List UInt32) (ascii fullhex : Bool) :=
  escapeStringIO d s esc keep ascii fullhex
def P459 : Prop := ∀ d s esc keep ascii fullhex, HasResult (m459 d s esc keep ascii fullhex)
theorem p459 : P459 := fun d s esc keep ascii fullhex => hasResult (m459 d s esc keep ascii fullhex)

def m488 (d : UData) (s : JStr) (esc keep : List UInt32) (ascii fullhex : Bool) :=
  escapeString d s esc keep ascii fullhex
def P488 : Prop := ∀ d s esc keep ascii fullhex, HasResult (m488 d s esc keep ascii fullhex)
theorem p488 : P488 := fun d s esc keep ascii fullhex => hasResult (m488 d s esc keep ascii fullhex)

def m491 (d : UData) (s : JStr) := printQuoted d s
def P491 : Prop := ∀ d s, HasResult (m491 d s)
theorem p491 : P491 := fun d s => hasResult (m491 d s)

def m535 (s : JStr) (keep : List UInt32) := unescapeString s keep
def P535 : Prop := ∀ s keep, HasResult (m535 s keep)
theorem p535 : P535 := fun s keep => hasResult (m535 s keep)

def m592 (s : JStr) (keep : List UInt32) := unescapeString s keep
def P592 : Prop := ∀ s keep, HasResult (m592 s keep)
theorem p592 : P592 := fun s keep => hasResult (m592 s keep)

def m613 (s : JStr) := bStr s
def P613 : Prop := ∀ s, HasResult (m613 s)
theorem p613 : P613 := fun s => hasResult (m613 s)

def m643 (s : List Char) := rawStr s
def P643 : Prop := ∀ s, m643 s = s
theorem p643 : P643 := by intro; rfl

def m663 (s : List Char) (delim : Char) := escapeRawStringIO s delim
def P663 : Prop := ∀ s delim, HasResult (m663 s delim)
theorem p663 : P663 := fun s delim => hasResult (m663 s delim)

def m694 (s : List Char) (delim : Char) := escapeRawString s delim
def P694 : Prop := ∀ s delim, HasResult (m694 s delim)
theorem p694 : P694 := fun s delim => hasResult (m694 s delim)

def m719 (s : List Char) (tabwidth : Nat) := indentation tabwidth s 0
def P719 : Prop := ∀ s tabwidth, HasResult (m719 s tabwidth)
theorem p719 : P719 := fun s tabwidth => hasResult (m719 s tabwidth)

def m749 (s : List Char) (indent : Int) (tabwidth : Nat) := unindent s indent tabwidth
def P749 : Prop := ∀ s indent tabwidth, HasResult (m749 s indent tabwidth)
theorem p749 : P749 := fun s indent tabwidth => hasResult (m749 s indent tabwidth)

def m805 (chars : List Char) := stringOfChars chars
def P805 : Prop := ∀ chars, HasResult (m805 chars)
theorem p805 : P805 := fun chars => hasResult (m805 chars)

def m818 {C} (printChar : C → List Char) (chars : List C) := stringOfAbstractChars printChar chars
def P818 : Prop := ∀ (C : Type) (printChar : C → List Char) (chars : List C), HasResult (m818 printChar chars)
theorem p818 : P818 := fun _ printChar chars => hasResult (m818 printChar chars)

def m826 (chars : List AChar) := annotatedStringOfChars chars
def P826 : Prop := ∀ chars, HasResult (m826 chars)
theorem p826 : P826 := fun chars => hasResult (m826 chars)

def e (line : Nat) (fn statement : String) (prop thm : Lean.Name) : Entry :=
  entry ("showcov-strings-io-l" ++ toString line) "base/strings/io.jl" fn statement prop thm

def entries : List Entry := [
  e 32 "print(::IO, x)" "Single-value print locks, calls show, unlocks in finally, and returns nothing." ``P32 ``p32,
  e 42 "print(::IO, xs...)" "Vararg print locks once, prints each field in order, unlocks in finally, and returns nothing." ``P42 ``p42,
  e 77 "println(::IO, xs...)" "println forwards all arguments followed by one newline." ``P77 ``p77,
  e 104 "sprint(::Function, args...)" "sprint creates a buffer, applies the selected context branch, calls f, and takes the string." ``P104 ``p104,
  e 116 "_str_sizehint(x)" "The size hint follows the source type-test order and returns its exact estimate." ``P116 ``p116,
  e 134 "print_to_string(xs...)" "print_to_string handles empty input, sums hints, prints every field, then takes the buffer." ``P134 ``p134,
  e 150 "string_with_env(env, xs...)" "string_with_env follows the sizing loop and prints through the environment context." ``P150 ``p150,
  e 186 "string(xs...)" "string forwards its arguments to print_to_string." ``P186 ``p186,
  e 188 "string(::Symbol)" "Symbol string conversion returns the symbol name." ``P188 ``p188,
  e 192 "print(::IO, ::AbstractString)" "AbstractString print iterates characters and prints each in order." ``P192 ``p192,
  e 193 "write(::IO, ::AbstractString)" "AbstractString write iterates characters and accumulates every returned byte count." ``P193 ``p193,
  e 194 "show(::IO, ::AbstractString)" "AbstractString show delegates to print_quoted." ``P194 ``p194,
  e 197 "show(::IO, ::MIME\"text/plain\", ::AbstractString)" "Limited text show computes the limit, boundaries, replacement threshold, and selected three-part output." ``P197 ``p197,
  e 217 "skip_text(skip)" "The nested skip_text helper formats the skipped count and unit name." ``P217 ``p217,
  e 242 "write(::IO, ::Union{String,SubString{String}})" "Optimized string write selects the cancellable unsafe_write call and converts its return to Int." ``P242 ``p242,
  e 246 "print(::IO, ::Union{String,SubString{String}})" "Optimized string print calls write and returns nothing." ``P246 ``p246,
  e 284 "repr(x)" "repr calls sprint(show, x) with the supplied context." ``P284 ``p284,
  e 286 "limitrepr(x)" "limitrepr calls repr with limit true." ``P286 ``p286,
  e 306 "IOBuffer(::String)" "String IOBuffer unsafe-wraps every byte then constructs the buffer." ``P306 ``p306,
  e 307 "IOBuffer(::SubString{String})" "SubString IOBuffer wraps the parent and views exactly the stored byte interval." ``P307 ``p307,
  e 330 "join(::IO, iterator, delim, last)" "Four-argument join delays one item, writes delimiters in source order, and uses last for the final pair." ``P330 ``p330,
  e 346 "join(::IO, iterator, delim)" "Three-argument join writes one delimiter between adjacent printed items." ``P346 ``p346,
  e 356 "_join_preserve_annotations(iterator, args...)" "Generic annotation-preserving join follows concrete-type and dynamic-annotation branches." ``P356 ``p356,
  e 378 "_join_preserve_annotations(::Tuple, args...)" "Tuple annotation-preserving join branches on tuple elements and arguments." ``P378 ``p378,
  e 389 "join(iterator)" "One-argument join forwards to _join_preserve_annotations." ``P389 ``p389,
  e 390 "join(iterator, delim)" "Two-argument join forwards iterator and delimiter." ``P390 ``p390,
  e 391 "join(iterator, delim, last)" "Three-argument join forwards iterator and both delimiters." ``P391 ``p391,
  e 395 "need_full_hex(::Union{Nothing,AbstractChar})" "need_full_hex checks presence before the hexadecimal-digit predicate." ``P395 ``p395,
  e 396 "escape_nul(::Union{Nothing,AbstractChar})" "escape_nul selects the unambiguous NUL spelling from the following character." ``P396 ``p396,
  e 459 "escape_string(::IO, ::AbstractString)" "IO escape_string follows the exact character classification and malformed-byte loops." ``P459 ``p459,
  e 488 "escape_string(::AbstractString)" "String escape_string calls the IO method through sprint with lastindex size hint." ``P488 ``p488,
  e 491 "print_quoted(::IO, ::AbstractString)" "print_quoted writes a quote, the escaped body, then a quote." ``P491 ``p491,
  e 535 "unescape_string(::IO, ::AbstractString)" "IO unescape_string follows backslash, hex, Unicode, octal, simple, and error branches." ``P535 ``p535,
  e 592 "unescape_string(::AbstractString)" "String unescape_string calls the IO method through sprint." ``P592 ``p592,
  e 613 "b_str(::String)" "The byte-string macro unescapes, takes code units, and returns a QuoteNode value." ``P613 ``p613,
  e 643 "raw_str(s)" "The raw-string macro returns its argument." ``P643 ``p643,
  e 663 "escape_raw_string(::IO, ::AbstractString, ::Char)" "IO raw escaping counts and writes delimiter and trailing backslashes in source order." ``P663 ``p663,
  e 694 "escape_raw_string(::AbstractString, ::Char)" "String raw escaping probes with devnull and returns the original or a sprint copy." ``P694 ``p694,
  e 719 "indentation(::AbstractString)" "indentation counts spaces and tab stops until the first other character." ``P719 ``p719,
  e 749 "unindent(::AbstractString, ::Int)" "unindent follows cutting, internal-tab, newline, character, and trailing-space branches." ``P749 ``p749,
  e 805 "String(::AbstractVector{Char})" "The Char vector constructor sizes UTF-8 storage then writes every character at the running offset." ``P805 ``p805,
  e 818 "String(::AbstractVector{<:AbstractChar})" "The abstract-character constructor prints every character through sprint." ``P818 ``p818,
  e 826 "AnnotatedString(::AbstractVector{<:AbstractChar})" "The annotated constructor builds text then collects every annotation at its byte region." ``P826 ``p826
]

end JuliaLean.ShowCov.Methods.StringsIOFile
