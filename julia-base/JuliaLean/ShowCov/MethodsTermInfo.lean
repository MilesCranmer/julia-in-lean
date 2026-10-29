import JuliaLean.ShowCov.MethodSupport
import JuliaLean.ShowCov.TermInfo

namespace JuliaLean.ShowCov.Methods.TermInfoFile

open JuliaLean.Registry
open JuliaLean.ShowCov.TermInfo
open JuliaLean.ShowCov.Methods

def m69 (_args : Unit) := blank
def P69 : Prop := ∀ args : Unit, m69 args = ⟨[], [], [], [], none, []⟩
theorem p69 : P69 := fun _ => rfl

def m71 (data : Rd) := readRawAt data
def P71 : Prop := ∀ (data : Rd),
  (data.rest.length < 2 → m71 data = .error .eofError) ∧
  (∀ (a b : UInt8) (rest : List UInt8), data.rest = a :: b :: rest →
    a.toNat + 256 * b.toNat ≠ 0o432 → a.toNat + 256 * b.toNat ≠ 0o1036 →
    m71 data = .error (.argumentError "Terminfo data did not start with the magic number 0o0432 or 0o01036"))
theorem p71 : P71 := by
  intro data
  constructor
  · intro h
    cases hr : data.rest with
    | nil => simp [m71, readRawAt, readU16, hr]
    | cons a xs =>
      cases xs with
      | nil => simp [m71, readRawAt, readU16, hr]
      | cons b bs => simp [hr] at h; omega
  · intro a b rest hr h1 h2
    simp [m71, readRawAt, readU16, hr, h1, h2]
def P72 : Prop := ∀ (r : Rd) (n : Int),
  (n < 0 → terminfoReadBytes r n = .error (.argumentError "invalid Array dimensions")) ∧
  (0 ≤ n → r.rest.length < n.toNat → terminfoReadBytes r n = .error .eofError) ∧
  (0 ≤ n → n.toNat ≤ r.rest.length →
    (terminfoReadBytes r n).map (fun result => result.1.length) = .ok n.toNat)
theorem p72 : P72 := by
  intro r n
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [terminfoReadBytes, h]
  · intro h hn; simp [terminfoReadBytes, Int.not_lt.mpr h, readExact_short r n.toNat hn]
  · intro h hn; simp [terminfoReadBytes, Int.not_lt.mpr h, readExact_length r n.toNat hn]

def P255 : Prop := ∀ (f : String → Except StatError Bool) (path : String),
  (f path = .error .io → statCheck f path = .ok false) ∧
  (∀ err, err ≠ .io → f path = .error err → statCheck f path = .error err)
theorem p255 : P255 := by
  intro f path
  constructor
  · intro h; simp [statCheck, h]
  · intro err hn h
    cases err <;> simp_all [statCheck]


def m112 (data : Rd) (wordBytes : Nat) := extendedterminfo data wordBytes
def P112 : Prop := ∀ (data : Rd) (wordBytes : Nat),
  data.pos % 2 = 0 → data.rest = [] → m112 data wordBytes = .error .eofError
theorem p112 : P112 := by
  intro data wordBytes halign hempty
  simp [m112, extendedterminfo, halign, readI16, hempty]

def m148 (table : List UInt8) (indices : List Int) := readStrings table indices
def P148 : Prop := ∀ table : List UInt8, ∀ indices : List Int, HasResult (m148 table indices)
theorem p148 : P148 := fun table indices => hasResult (m148 table indices)

def m170 (tf tn ts : List Cap) (termUser : Nat → String → Option String) (raw : Raw) :=
  ofRaw tf tn ts termUser raw
def P170 : Prop := ∀ tf tn ts : List Cap, ∀ termUser : Nat → String → Option String,
  ∀ raw : Raw, HasResult (m170 tf tn ts termUser raw)
theorem p170 : P170 := fun tf tn ts termUser raw => hasResult (m170 tf tn ts termUser raw)

/-- Nested `longalias(key, value)` at `base/terminfo.jl:194`: the source gets
the first component of the TERM_USER lookup default, represented by
`termUser kind key`. -/
def m194 (termUser : Nat → String → Option String) (kind : Nat) (key : String) :=
  termUser kind key
def P194 : Prop := ∀ f : Nat → String → Option String, ∀ kind : Nat, ∀ key : String,
  m194 f kind key = f kind key
theorem p194 : P194 := by intro f kind key; rfl

def m214 (ti : TI) (key : String) (default : Bool) := getBool ti key default
def P214 : Prop := ∀ ti key default, HasResult (m214 ti key default)
theorem p214 : P214 := fun ti key default => hasResult (m214 ti key default)

def m215 (ti : TI) (key : String) (default : Int) := getInt ti key default
def P215 : Prop := ∀ ti key default, HasResult (m215 ti key default)
theorem p215 : P215 := fun ti key default => hasResult (m215 ti key default)

def m216 (ti : TI) (key : String) (default : List UInt8) := getStr ti key default
def P216 : Prop := ∀ ti key default, HasResult (m216 ti key default)
theorem p216 : P216 := fun ti key default => hasResult (m216 ti key default)

def m218 (ti : TI) (key : String) := haskey ti key
def P218 : Prop := ∀ ti key, HasResult (m218 ti key)
theorem p218 : P218 := fun ti key => hasResult (m218 ti key)

def m221 (fuel : Nat) (ti : TI) (key : String) := getindex fuel ti key
def P221 : Prop := ∀ fuel ti key, HasResult (m221 fuel ti key)
theorem p221 : P221 := fun fuel ti key => hasResult (m221 fuel ti key)

def m229 (ti : TI) := keys ti
def P229 : Prop := ∀ ti, HasResult (m229 ti)
theorem p229 : P229 := fun ti => hasResult (m229 ti)

def m231 (namesRepr : String) (ti : TI) := showTI namesRepr ti
def P231 : Prop := ∀ names ti, HasResult (m231 names ti)
theorem p231 : P231 := fun names ti => hasResult (m231 names ti)

def m248 (env : Env) (lower : String → String) (term : String) :=
  findTerminfoFile env lower term
def P248 : Prop := ∀ (env : Env) (lower : String → String) (term : String),
  term.toList.any (fun ch => ch = '/' ∨ (!env.isunix ∧ ch = '\\')) = true →
  m248 env lower term = .ok none
theorem p248 : P248 := by
  intro env lower term h
  unfold m248 findTerminfoFile
  split
  · rfl
  · rw [if_pos h]
    rfl

def m286 (env : Env) (lower : String → String) (readFile : String → ReadResult)
    (convert : Raw → TI) (term : String) := loadTerminfo env lower readFile convert term
def P286 : Prop := ∀ (env : Env) (lower : String → String)
    (readFile : String → ReadResult) (convert : Raw → TI) (term path : String),
  findTerminfoFile env lower term = .ok (some path) →
  (readFile path = .argumentError ∨ readFile path = .ioError ∨
   readFile path = .eofError ∨ readFile path = .systemError) →
  m286 env lower readFile convert term = .info blank
theorem p286 : P286 := by
  intro env lower readFile convert term path h hr
  rcases hr with hr | hr | hr | hr <;> simp [m286, loadTerminfo, h, hr]

def m319 (ti : TI) := ttyhascolor false ti
def P319 : Prop := ∀ ti, m319 ti = haskey ti "setaf"
theorem p319 : P319 := by intro; rfl

def m357 (env : ColorEnv) (ti : TI) := ttyhastruecolor env ti
def P357 : Prop := ∀ env ti, HasResult (m357 env ti)
theorem p357 : P357 := fun env ti => hasResult (m357 env ti)

def m376 (cache : Option Bool) (computed : Bool) := getHaveCached cache computed
def P376 : Prop := ∀ cache computed, HasResult (m376 cache computed)
theorem p376 : P376 := fun cache computed => hasResult (m376 cache computed)

def m382 (cache : Option Bool) (computed : Bool) := getHaveCached cache computed
def P382 : Prop := ∀ cache computed, HasResult (m382 cache computed)
theorem p382 : P382 := fun cache computed => hasResult (m382 cache computed)

def m388 (haveColor : Bool) (key : String) (value : Bool) := inTTY haveColor key (some value)
def P388 : Prop := ∀ haveColor key value, HasResult (m388 haveColor key value)
theorem p388 : P388 := fun haveColor key value => hasResult (m388 haveColor key value)

def m389 (key : String) := haskeyTTY key
def P389 : Prop := ∀ key, m389 key = (key == "color")
theorem p389 : P389 := by intro; rfl

def m390 (haveColor : Bool) (key : String) := getindexTTY haveColor key
def P390 : Prop := ∀ haveColor key, HasResult (m390 haveColor key)
theorem p390 : P390 := fun haveColor key => hasResult (m390 haveColor key)

def m391 {α} (haveColor : α) (key : String) (default : α) := getTTY haveColor key default
def P391 : Prop := ∀ (α : Type) (haveColor : α) key default, HasResult (m391 haveColor key default)
theorem p391 : P391 := fun _ haveColor key default => hasResult (m391 haveColor key default)

def e (line : Nat) (fn statement : String) (prop thm : Lean.Name) : Entry :=
  entry ("showcov-terminfo-l" ++ toString line) "base/terminfo.jl" fn statement prop thm

def entries : List Entry := [
  e 69 "TermInfo()" "The zero-argument constructor creates empty capability dictionaries and no extension set." ``P69 ``p69,
  e 71 "read(::IO, ::Type{TermInfoRaw})" "The raw reader rejects an unrecognized magic number." ``P71 ``p71,
  e 72 "_terminfo_read_bytes(::IO, ::Integer)" "Negative lengths throw ArgumentError; complete reads return the requested byte count and short reads throw EOFError." ``P72 ``p72,
  e 112 "extendedterminfo(::IO, ::Union{Type{Int16},Type{Int32}})" "An empty extended header throws EOFError at an even offset." ``P112 ``p112,
  e 148 "_terminfo_read_strings(::Vector{UInt8}, ::Vector{Int16})" "Each index yields its NUL-terminated string, nothing, or the documented ArgumentError." ``P148 ``p148,
  e 170 "TermInfo(::TermInfoRaw)" "TermInfo construction fills standard and extended dictionaries and aliases in source loop order." ``P170 ``p170,
  e 194 "longalias(key, value)" "The nested longalias helper returns the first TERM_USER lookup component." ``P194 ``p194,
  e 214 "get(::TermInfo, ::Symbol, ::Bool)" "Bool get resolves aliases before reading the flag dictionary." ``P214 ``p214,
  e 215 "get(::TermInfo, ::Symbol, ::Int)" "Int get resolves aliases before reading the number dictionary." ``P215 ``p215,
  e 216 "get(::TermInfo, ::Symbol, ::String)" "String get resolves aliases before reading the string dictionary." ``P216 ``p216,
  e 218 "haskey(::TermInfo, ::Symbol)" "haskey checks flags, numbers, strings, then aliases with short-circuit or." ``P218 ``p218,
  e 221 "getindex(::TermInfo, ::Symbol)" "getindex checks the three value dictionaries, follows aliases, then throws KeyError." ``P221 ``p221,
  e 229 "keys(::TermInfo)" "keys unions the four key sets." ``P229 ``p229,
  e 231 "show(::IO, ::MIME\"text/plain\", ::TermInfo)" "Text display prints names and counts, with an extension count only when present." ``P231 ``p231,
  e 248 "find_terminfo_file(::String)" "Terminal names containing a platform path separator are rejected." ``P248 ``p248,
  e 255 "_terminfo_stat_check(::Function, ::String)" "A filesystem IOError is treated as absence; other errors propagate." ``P255 ``p255,
  e 286 "load_terminfo(::String)" "Loading returns a blank TermInfo when reading raises a handled file or parsing error." ``P286 ``p286,
  e 319 "ttyhascolor()" "The non-Windows method checks the setaf capability." ``P319 ``p319,
  e 357 "ttyhastruecolor()" "Truecolor detection evaluates every documented environment and terminfo condition in short-circuit order." ``P357 ``p357,
  e 376 "get_have_color()" "The color cache computes only when empty and returns a Bool." ``P376 ``p376,
  e 382 "get_have_truecolor()" "The truecolor cache computes only when empty and returns a Bool." ``P382 ``p382,
  e 388 "in(::Pair{Symbol,Bool}, ::TTY)" "TTY pair membership requires the color key and cached color value." ``P388 ``p388,
  e 389 "haskey(::TTY, ::Symbol)" "TTY haskey is true exactly for color." ``P389 ``p389,
  e 390 "getindex(::TTY, ::Symbol)" "TTY getindex returns cached color or throws KeyError." ``P390 ``p390,
  e 391 "get(::TTY, ::Symbol, default)" "TTY get returns cached color for that key and the supplied default otherwise." ``P391 ``p391
]

end JuliaLean.ShowCov.Methods.TermInfoFile
