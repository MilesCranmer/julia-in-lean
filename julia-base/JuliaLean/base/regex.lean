import JuliaLean.base.strings.annotated
import JuliaLean.base.strings.substring
import JuliaLean.Runtime.Strings
import JuliaLean.Core
import JuliaLean.base.range
import JuliaLean.base.strings.basic
import JuliaLean.base.pcre
import JuliaLean.base.strings.string

/-!
# Model of base/regex.jl

`findnext` on a `Regex` (regex.jl:485-515), the splitter search `split`/`rsplit` call.
`RegexOps.ofPCRE` binds compilation and PCRE wrappers to the installed models for
String and SubString{String} subjects; native memory, global and lock operations remain typed inputs.
-/

namespace JuliaLean.base.regex

open JuliaLean
open JuliaLean.base.strings.basic

/-- Typed callees used by regex.jl. `RegexOps.ofPCRE` supplies the installed compile
and PCRE wrapper bodies for standard dense subjects; native reads stay external. -/
structure RegexOps (Re S Data Ptr E : Type) where
  matchOptions : Re → UInt32
  compile : Re → Except E Re
  execRData : Re → S → Index → UInt32 → Except E (Bool × Data)
  ovecPtr : Data → Ptr
  unsafeLoad : Ptr → Nat → Except E UInt64
  freeMatchData : Data → Except E Unit
  boundsError : E

/--
Julia source: base/regex.jl:485-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(re::Regex, str::DenseUTF8String, idx::Integer)
    _findnext_re(re, str, idx, C_NULL)
end
```
Julia source: base/regex.jl:491-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findnext_re(re::Regex, str, idx::Integer, match_data::Ptr{Cvoid})
    if idx > nextind(str,lastindex(str))
        throw(BoundsError())
    end
    opts = re.match_options
    compile(re)
    alloc = match_data == C_NULL
    if alloc
        matched, data = PCRE.exec_r_data(re.regex, str, idx-1, opts)
    else
        matched = PCRE.exec(re.regex, str, idx-1, opts, match_data)
        data = match_data
    end
    if matched
        p = PCRE.ovec_ptr(data)
        ans = (Int(unsafe_load(p,1))+1):prevind(str,Int(unsafe_load(p,2))+1)
    else
        ans = nothing
    end
    alloc && PCRE.free_match_data(data)
    return ans
end
```
regex.jl:485-487 `findnext(re::Regex, str::DenseUTF8String, idx::Integer)` and
regex.jl:491-512 `_findnext_re(re, str, idx, C_NULL)`. regex.jl:506 evaluates, left to right,
`unsafe_load(p,1)`, `Int(...)` (Core.lean `convert .i64`, `InexactError` at `2^63`), `+ 1`
(`Int` addition), `unsafe_load(p,2)`, `Int(...)`, `+ 1`, `prevind(str, ...)`, then `(:)` on two
`Int`s: range.jl:5 `UnitRange{Int}(start, stop)`, whose constructor (range.jl:428, 439-441)
sets `stop` to `start - 1` when `stop < start` (range.lean `colon_T_T_Real`, with the `Int`
instances in range.lean's `IntRangeInstances` section). -/
def findnextRegex {Re S Data Ptr E : Type} (rx : RegexOps Re S Data Ptr E)
    (liftJ : JlError → E) (liftX : JuliaLean.base.range.Exc → E)
    (lastindex : S → Except E Index) (nextind prevind : S → Index → Except E Index)
    (re : Re) (str : S) (idx : Index) :
    Except E (Option (JuliaLean.base.range.UnitRange Index)) := do
  if idx.val > (← nextind str (← lastindex str)).val then throw rx.boundsError
  let opts := rx.matchOptions re
  let re ← rx.compile re
  let (matched, data) ← rx.execRData re str (idx - int 1) opts
  let ans ← if matched then do
      let p := rx.ovecPtr data
      let lo ← rx.unsafeLoad p 1
      let first ← (JInt.convert "convert" .i64 lo.toNat).mapError liftJ
      let start := first + int 1
      let hi ← rx.unsafeLoad p 2
      let last ← (JInt.convert "convert" .i64 hi.toNat).mapError liftJ
      let stop ← prevind str (last + int 1)
      let r ← (JuliaLean.base.range.colon_T_T_Real start stop).mapError liftX
      pure (some r)
    else pure none
  rx.freeMatchData data
  pure ans

/-- util.jl:793, 795, 803 for a `Regex` splitter: `first(r)`, `last(r)` of the `UnitRange{Int}`
(range.jl:867, 877: `convert(Int, r.start)`, `convert(Int, r.stop)`, the identity on `Int`). -/
def regexSplitterFindnext {Re S Data Ptr E : Type} (rx : RegexOps Re S Data Ptr E)
    (liftJ : JlError → E) (liftX : JuliaLean.base.range.Exc → E)
    (lastindex : S → Except E Index) (nextind prevind : S → Index → Except E Index)
    (re : Re) (str : S) (k : Index) : Except E (Option (Index × Index)) := do
  return (← findnextRegex rx liftJ liftX lastindex nextind prevind re str k).map
    fun r => (r.start, r.stop)

/--
Julia source: base/regex.jl:513-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(r::Regex, s::AbstractString, idx::Integer) = throw(ArgumentError(
    "regex search is only available for the String type; use String(s) to convert"
))
```
regex.jl:513-515 `findnext(r::Regex, s::AbstractString, idx::Integer)` for every other
string type. -/
def findnextRegexOther {Re S E : Type} (argumentError : String → E) (_re : Re) (_s : S)
    (_idx : Index) : Except E (Option (Index × Index)) :=
  throw (argumentError "regex search is only available for the String type; use String(s) to convert")

/-- util.jl:903 `findprev(it.splitter, it.str, to)` with a `Regex` splitter: regex.jl defines no
`findprev` method for `Regex`, and none of search.jl's `findprev` methods accepts one, so the
call throws `MethodError`. -/
def findprevRegex {Re S E : Type} (methodError : String → E) (_re : Re) (_s : S)
    (_idx : Index) : Except E (Option (Index × Index)) :=
  throw (methodError "findprev")

abbrev PCREString := JuliaLean.base.strings.string.JString
abbrev PCRESubstring := JuliaLean.base.strings.substring.SubString PCREString

inductive DenseSubject where
  | string (value : PCREString)
  | substring (value : PCRESubstring)

/-- Core.sizeof is the primitive called by the installed String ncodeunits body.
SubString ncodeunits reads its stored length through the installed body. -/
def denseNcodeunits (coreSizeof : PCREString → Index) : DenseSubject → Index
  | .string value => JuliaLean.base.strings.string.ncodeunits coreSizeof value
  | .substring value => JuliaLean.base.strings.substring.ncodeunitsSubString value

/-- Native Core.getfield/setfield! and isdefinedglobal operations on Regex and PCRE. -/
structure RegexHeap (E Re Code : Type) where
  code : Re → Except E Code
  setCode : Re → Code → Except E Unit
  pattern : Re → Except E PCREString
  compileOptions : Re → Except E UInt32
  matchOptions : Re → UInt32
  compileLockDefined : Except E Bool

/-- Native operations only. Memory supplies allocation, reference access,
array length/pointer access, unsafe_string and preservation primitives.
ContextOps supplies thread/global/vector/lock/native-PCRE primitives. -/
structure PCREBindingNative (E Code Data Ptr Buffer ContextVector Lock : Type) (Ref : Type → Type) where
  errors : JuliaLean.base.pcre.Errors E
  codes : JuliaLean.base.pcre.Codes
  bytesMemory : JuliaLean.base.pcre.Memory (Except E) Code Buffer PCREString Ref
  messageMemory : JuliaLean.base.pcre.Memory (Except E) Code Buffer String Ref
  contexts : JuliaLean.base.pcre.ContextOps (Except E) Code ContextVector Lock
  coreSizeof : PCREString → Index
  compile8 : PCREString → JuliaLean.base.pcre.Size → JuliaLean.base.pcre.Options →
    Ref JuliaLean.base.pcre.Cint → Ref JuliaLean.base.pcre.Size → Code → Except E Code
  jitCompile8 : Code → JuliaLean.base.pcre.Options → Except E JuliaLean.base.pcre.Cint
  getErrorMessage8 : JuliaLean.base.pcre.Cint → Buffer → JuliaLean.base.pcre.Size →
    Except E JuliaLean.base.pcre.Cint
  nullData : Data
  isNullData : Data → Bool
  createFromPattern8 : Code → Data → Except E Data
  match8 : Code → DenseSubject → Index → Index → UInt32 → Data → Code →
    Except E JuliaLean.base.pcre.Cint
  ovectorPointer8 : Data → Ptr
  unsafeLoadSize : Ptr → Nat → Except E UInt64
  freeMatchData8 : Data → Except E Unit

/-- Bind the installed PCRE error-message body, including ERROR_BADDATA. -/
def boundErrorMessage {E Code Data Ptr Buffer ContextVector Lock : Type} {Ref : Type → Type}
    (native : PCREBindingNative E Code Data Ptr Buffer ContextVector Lock Ref)
    (errno : JuliaLean.base.pcre.Cint) : Except E String :=
  JuliaLean.base.pcre.errMessage native.errors native.codes native.messageMemory
    (fun value => pure value) native.getErrorMessage8 (fun value => toString value.val) errno

/-- Regex.pattern is a String, so PCRE.compile's String-conversion branch is
not taken. Both standard byte counts and raw PCRE checks use installed bodies. -/
def boundPatternCompile {E Code Data Ptr Buffer ContextVector Lock : Type} {Ref : Type → Type}
    (native : PCREBindingNative E Code Data Ptr Buffer ContextVector Lock Ref)
    (pattern : PCREString) (options : UInt32) : Except E Code :=
  JuliaLean.base.pcre.compile native.errors native.bytesMemory
    (fun _ => true) (fun value => pure value) (fun value => value)
    (fun value => pure (JuliaLean.base.strings.string.ncodeunits native.coreSizeof value))
    (fun value => pure (JInt.wrap .u32 value.toNat)) native.compile8
    (boundErrorMessage native) pattern options

/--
Julia source: base/regex.jl:70-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compile(regex::Regex)
    if regex.regex == C_NULL
        if !isdefinedglobal(PCRE, :PCRE_COMPILE_LOCK)
            regex.regex = PCRE.compile(regex.pattern, regex.compile_options)
            PCRE.jit_compile(regex.regex)
        else
            l = PCRE.PCRE_COMPILE_LOCK
            lock(l)
            try
                if regex.regex == C_NULL
                    regex.regex = PCRE.compile(regex.pattern, regex.compile_options)
                    PCRE.jit_compile(regex.regex)
                end
            finally
                unlock(l)
            end
        end
    end
    regex
end
```
-/
def compileRegex {E Re Code Data Ptr Buffer ContextVector Lock : Type} {Ref : Type → Type}
    (heap : RegexHeap E Re Code)
    (native : PCREBindingNative E Code Data Ptr Buffer ContextVector Lock Ref)
    (regex : Re) : Except E Re := do
  if native.bytesMemory.isNull (← heap.code regex) then
    if !(← heap.compileLockDefined) then
      let pointer ← boundPatternCompile native (← heap.pattern regex) (← heap.compileOptions regex)
      heap.setCode regex pointer
      let _ ← JuliaLean.base.pcre.jitCompile native.errors native.codes native.jitCompile8
        (boundErrorMessage native) (← heap.code regex)
    else
      let lock ← native.contexts.getCompileLock
      native.contexts.lock lock
      JuliaLean.base.pcre.finallyDo (E := E) (do
        if native.bytesMemory.isNull (← heap.code regex) then
          let pointer ← boundPatternCompile native (← heap.pattern regex) (← heap.compileOptions regex)
          heap.setCode regex pointer
          let _ ← JuliaLean.base.pcre.jitCompile native.errors native.codes native.jitCompile8
            (boundErrorMessage native) (← heap.code regex)
        pure ()) (native.contexts.unlock lock)
  pure regex

/-- Additive adapter for the installed public DenseUTF8String search route. -/
def RegexOps.ofPCRE {E Re Code Data Ptr Buffer ContextVector Lock : Type} {Ref : Type → Type}
    (heap : RegexHeap E Re Code)
    (native : PCREBindingNative E Code Data Ptr Buffer ContextVector Lock Ref)
    (boundsError : E) : RegexOps Re DenseSubject Data Ptr E where
  matchOptions := heap.matchOptions
  compile := compileRegex heap native
  execRData re subject offset options := do
    let code ← heap.code re
    JuliaLean.base.pcre.execRData
      (fun code => JuliaLean.base.pcre.createMatchData native.errors native.nullData native.isNullData
        native.createFromPattern8 code)
      (fun code subject offset options data =>
        JuliaLean.base.pcre.execCore native.errors
          (fun subject => pure (denseNcodeunits native.coreSizeof subject))
          (JuliaLean.base.pcre.getLocalMatchContext (E := E) native.contexts)
          native.match8 (boundErrorMessage native) code subject offset options data)
      code subject offset options
  ovecPtr data := JuliaLean.base.pcre.ovecPtr (m := Id) native.ovectorPointer8 data
  unsafeLoad := native.unsafeLoadSize
  freeMatchData := JuliaLean.base.pcre.freeMatchData native.freeMatchData8
  boundsError := boundsError


end JuliaLean.base.regex

/-!
# Julia's regex wrappers

Line-by-line models of `match`, `findnext`, `count`, `findall`, `eachmatch` and
single-pattern `replace` for `Regex` on `String` (master `bbfa0ce4150`;
identical in 1.13.2). PCRE2 is the primitive `Pcre` of `CorePcre.lean`.

* Code-unit offsets from the ovector are below `2^62` (the axioms of `Pcre` put
  them inside the subject), so the `Csize_t` arithmetic `unsafe_load(p, 1) + 1`
  and its conversion to `Int` are exact; they are written `ix (v.start + 1)`.
* Julia's `while` loops are structural recursion on an explicit bound; each
  docstring states why the bound is never reached.
* Output written to an `IOBuffer` is the list of its code units.
-/

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- `DEFAULT_MATCH_OPTS = PCRE.NO_UTF_CHECK`, `base/regex.jl:8`. -/
def DEFAULT_MATCH_OPTS : UInt32 := NO_UTF_CHECK

/-- A compiled `Regex` (`base/regex.jl:22-27`): the compiled pattern and its
`match_options`. Compile options only influence `pcre`. -/
structure Regex where
  pcre : Pcre
  matchOptions : UInt32

/-- `Regex(pattern)` with the default match options (`base/regex.jl:68`). -/
def mkRegex (pat : Pattern) : Regex := ⟨interp pat, DEFAULT_MATCH_OPTS⟩

end JuliaLean.RegexUnicode.Core

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- `RegexMatch` (`base/regex.jl:178-184`) without its `regex` field. -/
structure RegexMatch where
  mat : JSub
  captures : List (Option JSub)
  offset : JInt64
  offsets : List JInt64
  deriving DecidableEq, Repr

/-- `SubString(str, a + 1, prevind(str, b + 1))` for a zero-based ovector pair
`(a, b)`, `base/regex.jl:441` and `:448-449`. -/
def capSub (s : JStr) (a b : Int) : RJl JSub :=
  match prevind s (ix (b + 1)) with
  | .error e => .error (.str e)
  | .ok j => liftS (substring s (ix (a + 1)) j)

/-- `match(re, str, idx, add_opts)`, `base/regex.jl:430-454`. `compile(re)` and
the match-data allocation are not modelled. -/
def regexMatch (re : Regex) (s : JStr) (idx : JInt64) (addOpts : UInt32 := 0) :
    RJl (Option RegexMatch) :=
  match exec re.pcre s (idx - ix 1) (re.matchOptions ||| addOpts) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some v) =>
    match capSub s v.start v.stop with
    | .error e => .error e
    | .ok mat =>
      match v.caps.mapM (fun x => (match x with
          | none => .ok none
          | some (a, b) => some <$> capSub s a b : RJl (Option JSub))) with
      | .error e => .error e
      | .ok cap =>
        let off := v.caps.map (fun x => match x with
          | none => ix 0
          | some (a, _) => ix (a + 1))
        .ok (some ⟨mat, cap, ix (v.start + 1), off⟩)

/-- `UnitRange{Int}(a, b)`: `unitrange_last(a, b) = b >= a ? b : a - 1`,
`base/range.jl:428`, `:439-441`. A range is `(first, last)`. -/
def mkRange (a b : JInt64) : JInt64 × JInt64 := (a, if b.val ≥ a.val then b else a - ix 1)

/-- `_findnext_re(re, str, idx, match_data)`, `base/regex.jl:491-512`, after its
first call: `e1r` is the result of `nextind(str, lastindex(str))` (`:492`). -/
def findnextReFrom (re : Regex) (s : JStr) (idx : JInt64) (e1r : SJl JInt64) :
    RJl (Option (JInt64 × JInt64)) :=
  match e1r with
  | .error e => .error (.str e)
  | .ok e1 =>
    if idx.val > e1.val then .error (.str boundsErr)
    else
      match exec re.pcre s (idx - ix 1) re.matchOptions with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some v) =>
        match prevind s (ix (v.stop + 1)) with
        | .error e => .error (.str e)
        | .ok b => .ok (some (mkRange (ix (v.start + 1)) b))

/-- `_findnext_re(re, str, idx, match_data)`, `base/regex.jl:491-512`; this is
`findnext(re, str, idx)` (`:485-487`) and `findnext(::RegexAndMatchData, ...)`
(`:646`). The range is `(Int(ovec[1]) + 1):prevind(str, Int(ovec[2]) + 1)`. -/
def findnextRe (re : Regex) (s : JStr) (idx : JInt64) : RJl (Option (JInt64 × JInt64)) :=
  findnextReFrom re s idx (nextind s (lastindex s))

/-- The loop of `count(t, s; overlap)`, `base/regex.jl:573-585`, with `find i =
findnext(t, s, i)` and `e = lastindex(s)`. Bound: `i` starts at 1 and every pass
that continues sets `i = nextind(s, j)` with `first(r) ≤ j ≤ e` and `first(r) ≥ i`
(`pcre2_match` starts at or after its offset), so `i` increases strictly and stays
at most `e + 1 ≤ ncodeunits(s) + 1`: at most `ncodeunits(s) + 2` passes. -/
def countLoop (find : JInt64 → RJl (Option (JInt64 × JInt64))) (s : JStr) (overlap : Bool)
    (e : JInt64) : Nat → JInt64 → JInt64 → RJl JInt64
  | 0, _, n => .ok n
  | f + 1, i, n =>
    match find i with
    | .error err => .error err
    | .ok none => .ok n
    | .ok (some r) =>
      let n := n + ix 1
      let j := if overlap || decide (r.2.val < r.1.val) then r.1 else r.2
      if j.val > e.val then .ok n
      else
        match nextind s j with
        | .error err => .error (.str err)
        | .ok i => countLoop find s overlap e f i n

/-- `count(re, s; overlap)`, `base/regex.jl:573-585`. -/
def count (re : Regex) (s : JStr) (overlap : Bool := false) : RJl JInt64 :=
  countLoop (findnextRe re s) s overlap (lastindex s) (s.bytes.length + 2) (ix 1) (ix 0)

abbrev State := JInt64 × Bool

/-- `opts_nonempty = UInt32(PCRE.ANCHORED | PCRE.NOTEMPTY_ATSTART)`, `base/regex.jl:750`. -/
def optsNonempty : UInt32 := ANCHORED ||| NOTEMPTY_ATSTART

/-- The `while true` loop of `iterate(itr::RegexMatchIterator, (offset, prevempty))`,
`base/regex.jl:749-777`. Bound 2: the body continues only when `prevempty` is
true and then sets it to false, so the second pass never continues.
`isempty(mat.match)` is `ncodeunits(mat.match) == 0`. -/
def iterLoop (re : Regex) (s : JStr) (overlap : Bool) :
    Nat → JInt64 → Bool → RJl (Option (RegexMatch × State))
  | 0, _, _ => .ok none
  | f + 1, offset, prevempty =>
    match regexMatch re s offset (if prevempty then optsNonempty else 0) with
    | .error e => .error e
    | .ok none =>
      if prevempty && decide (offset.val ≤ (ncodeunits s).val) then
        match nextind s offset with
        | .error e => .error (.str e)
        | .ok o' => iterLoop re s overlap f o' false
      else .ok none
    | .ok (some mat) =>
      let empty := decide (mat.mat.ncu.val = 0)
      let next : RJl JInt64 :=
        if overlap then
          if !empty then liftS (nextind s mat.offset) else .ok mat.offset
        else .ok (mat.offset + mat.mat.ncu)
      match next with
      | .error e => .error e
      | .ok o' => .ok (some (mat, (o', empty)))

/-- `iterate(eachmatch(re, s; overlap), state)`. -/
def iterate (re : Regex) (s : JStr) (overlap : Bool) (st : State) : RJl (Option (RegexMatch × State)) :=
  iterLoop re s overlap 2 st.1 st.2

/-- The initial state `(1, false)` of `iterate(itr::RegexMatchIterator)`. -/
def startState : State := (ix 1, false)


/-! ## replace -/

end JuliaLean.RegexUnicode.Core

/-!
# Regex substitution: `replace([io], s, r => s"...")`

Model of the substitution-string path of `replace` with a `Regex` pattern (master
`bbfa0ce4150`):

* `_replace(io, repl_s::SubstitutionString, str, r, re)`, `base/regex.jl:675-733`, walking
  `repl = unescape_string(repl_s.string, KEEP_ESC)` (the model input is the unescaped
  text) byte by byte. `write(io, c::Char)` (`base/io.jl:973-980`) writes the bytes of `c`
  one at a time with `write(io, ::UInt8)` and sums the counts, so for valid UTF-8 the
  byte walk issues exactly the same writes; the model is stated for ASCII text.
* `_write_capture(io, group, str, r, re::RegexAndMatchData)`, `base/regex.jl:654-664`,
  on the `IOBuffer` model of `JuliaLean.IOBuffers.Model`: `ensureroom(io, len+1)`, then
  `PCRE.substring_copy_bynumber` copies `len` bytes and a NUL terminator through
  `pointer(io.data, io.ptr)` (unchecked: `writeAt` with `isMem = true`), then
  `io.ptr += len; io.size = max(io.size, io.ptr - 1)`.
* the `replace` driver `_replace_`, `_replace_init`, `_replace_finish`, `_replace_once`
  (`base/strings/util.jl:1036-1131`) for one `Regex => SubstitutionString` pair and the
  default `count = typemax(Int)`, both into an `io` and into a fresh `IOBuffer`
  (`replace(s, pat => r)`, `takestring!`).

The `io` argument is an `IOBuffer` state or another `IO` (an `IOContext`, `IOStream` or
`devnull`), modelled as a byte sink: `write`/`unsafe_write` append, while `ensureroom` and
the field `io.data` exist only for `GenericIOBuffer` (`MethodError` otherwise).

PCRE2 is a primitive. Matching is a leftmost-first backtracking interpreter for the
fragment literals, concatenation, alternation, greedy `+` and numbered capture groups,
which is how PCRE2 matches that fragment. `pcre2_substring_length_bynumber`,
`pcre2_substring_copy_bynumber` and `pcre2_substring_number_from_name` follow the PCRE2
API documentation (`pcre2api(3)`, "Extracting captured substrings by number/name"):
a group number above the highest group is `PCRE2_ERROR_NOSUBSTRING` ("unknown
substring"), an unset group is `PCRE2_ERROR_UNSET`, an unknown name is
`PCRE2_ERROR_NOSUBSTRING` (-49) and a name used by several groups is
`PCRE2_ERROR_NOUNIQUESUBSTRING` (-50).

Subjects are ASCII, so `nextind(str, k) = k + 1` and `prevind(str, k) = k - 1`.
Exception messages are modelled only as far as the properties need them: the text that
Julia interpolates into `replace_err` messages is omitted.
-/

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## The `io` argument -/

/-- The `io` argument of `replace(io, ...)`. -/
inductive Sink where
  /-- An `IOBuffer` (`GenericIOBuffer`). -/
  | buf (io : IOBuf)
  /-- Any other `IO`: the bytes written to it so far. -/
  | other (out : List UInt8)
  deriving DecidableEq

/-- Mutating calls on the `io` argument; state changes made before an exception persist. -/
abbrev SM := EStateM IOErr Sink

def liftE {α} : Except IOErr α → SM α
  | .ok a => pure a
  | .error e => throw e

/-- A method or field that exists only for `GenericIOBuffer`: on another `IO` it is a
`MethodError` (`ensureroom`) or a missing field (`io.data`). -/
def onBuf {α} (f : String) (x : M α) : SM α := fun s =>
  match s with
  | .buf io =>
    match x io with
    | .ok a io' => .ok a (.buf io')
    | .error e io' => .error e (.buf io')
  | .other _ => .error (.jl (.methodError f)) s

/-- `write(io, b::UInt8)`: `base/iobuffer.jl:948-963` for an `IOBuffer`; one byte for a
sink. -/
def writeU8 (b : UInt8) : SM I := fun s =>
  match s with
  | .buf io => onBuf "write" (writeByte b) (.buf io)
  | .other out => .ok (i 1) (.other (out ++ [b]))

/-- `unsafe_write(io, p, n)` of the bytes `bs`: `base/iobuffer.jl:902-921` for an
`IOBuffer`; `write(io, ::String)` and `write(io, ::SubString{String})` call it. -/
def unsafeWriteIO (bs : List UInt8) : SM I := fun s =>
  match s with
  | .buf io => onBuf "unsafe_write" (unsafeWrite bs) (.buf io)
  | .other out => .ok (i bs.length) (.other (out ++ bs))

/-! ## `_write_capture` and `_replace` -/

/-- `_write_capture(io, group, str, r, re::RegexAndMatchData)`, `base/regex.jl:654-664`. -/
def writeCapture (md : Ovec) (subj : List UInt8) (group : I) : SM I := do
  let len ← liftE (substringLengthBynumber md group)
  -- regex.jl:657: an optional group that does not match has length 0
  if len.val = 0 then return len
  -- regex.jl:658, `ensureroom(io::GenericIOBuffer, nshort::Int)` (iobuffer.jl:597)
  onBuf "ensureroom" (do let n ← lift (toU (len + i 1).val); ensureroom n)
  -- regex.jl:659-660: copy `len + 1` bytes to `pointer(io.data, io.ptr)`
  let bytes ← liftE (substringCopyBynumber md subj group (len + i 1))
  onBuf "getproperty" (do
    let io ← get
    let data ← lift (writeAt true io.data io.ptr bytes)
    -- regex.jl:661-662
    let ptr := io.ptr + len
    set { io with data, ptr, size := imax io.size (ptr - i 1) })
  return len

/-- `SUB_CHAR = '\\'`, `base/regex.jl:671`. -/
def SUB : UInt8 := 92
/-- `GROUP_CHAR = 'g'`, `base/regex.jl:672`. -/
def GRP : UInt8 := 103
/-- `LBRACKET = '<'`, `base/regex.jl:676`. -/
def LB : UInt8 := 60
/-- `RBRACKET = '>'`, `base/regex.jl:677`. -/
def RB : UInt8 := 62

/-- `isdigit(c)`: `'0' <= c <= '9'`. -/
def isDigitB (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- Value of a decimal digit string as a mathematical number. -/
def digitsValue (ds : List UInt8) : Nat := ds.foldl (fun acc d => 10 * acc + (d.toNat - 48)) 0

/-- `parse(Int, s)` for a string of ASCII digits: empty is an `ArgumentError`, a value above
`typemax(Int)` an `OverflowError`. -/
def parseIntDigits (ds : List UInt8) : Except IOErr I :=
  if ds = [] then .error (.jl (.argumentError "input string is empty or only contains whitespace"))
  else if 2 ^ 63 - 1 < digitsValue ds then .error (.jl (.overflowError "overflow parsing"))
  else .ok (i (digitsValue ds))

/-- `replace_err(repl)`, `base/regex.jl:652`. -/
def replaceErr {α} (what : String) : SM α :=
  throw (.errorException ("Bad replacement string: " ++ what))

/-- What `_write_capture` needs from the match: the subject, the match data and the
regex's name table. -/
structure Ctx where
  subj : List UInt8
  md : Ovec
  names : NameTable

/-- The digit loop `group = 10group + parse(Int, repl[i])`, `base/regex.jl:692-699`, with
Julia's wrapping `Int` arithmetic: the final `group` and index. -/
def digitsLoop (repl : List UInt8) : Nat → Nat → I → I × Nat
  | 0, p, g => (g, p)
  | f + 1, p, g =>
    if p < repl.length ∧ isDigitB (repl.getD p 0) = true then
      digitsLoop repl f (p + 1) (i 10 * g + i ((repl.getD p 0).toNat - 48))
    else (g, p)

/-- `while repl[i] != RBRACKET; i = nextind(repl, i); i > e && replace_err(repl); end`,
`base/regex.jl:708-711`: the index of the closing `>`, or `none` for `replace_err`. -/
def scanName (repl : List UInt8) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, q =>
    if repl.getD q 0 = RB then some q
    else if repl.length ≤ q + 1 then none
    else scanName repl f (q + 1)

/-- The `while i <= e` loop of `_replace(io, repl_s::SubstitutionString, str, r, re)`,
`base/regex.jl:683-731`, over 0-based index `p` of the unescaped `repl`, with running count
`nb`. -/
def substLoop (ctx : Ctx) (repl : List UInt8) : Nat → Nat → I → SM I
  | 0, _, nb => pure nb
  | fuel + 1, p, nb =>
    if repl.length ≤ p then pure nb
    else if repl.getD p 0 = SUB then
      let nx := p + 1
      -- regex.jl:686
      if repl.length ≤ nx then replaceErr "repl"
      -- regex.jl:687-689
      else if repl.getD nx 0 = SUB then do
        let w ← writeU8 SUB
        substLoop ctx repl fuel (nx + 1) (nb + w)
      -- regex.jl:690-700
      else if isDigitB (repl.getD nx 0) then do
        let (group, q) := digitsLoop repl repl.length (nx + 1) (i ((repl.getD nx 0).toNat - 48))
        let w ← writeCapture ctx.md ctx.subj group
        substLoop ctx repl fuel q (nb + w)
      -- regex.jl:701-723
      else if repl.getD nx 0 = GRP then do
        let q := nx + 1
        if repl.length ≤ q ∨ repl.getD q 0 ≠ LB then replaceErr "repl"
        let q := q + 1
        if repl.length ≤ q then replaceErr "repl"
        let gs := q
        match scanName repl repl.length q with
        | none => replaceErr "repl"
        | some q' =>
          let name := (repl.drop gs).take (q' - gs)
          let group ←
            if name.all isDigitB then liftE (parseIntDigits name)
            else do
              let g ← liftE (substringNumberFromName ctx.names name)
              if g.val < 0 then replaceErr "Group not found in regex"
              pure g
          let w ← writeCapture ctx.md ctx.subj group
          substLoop ctx repl fuel (q' + 1) (nb + w)
      -- regex.jl:724-726
      else replaceErr "repl"
    else do
      -- regex.jl:727-730
      let w ← writeU8 (repl.getD p 0)
      substLoop ctx repl fuel (p + 1) (nb + w)

/-- `_replace(io, repl_s::SubstitutionString, str, r, re)`, `base/regex.jl:675-733`, on the
unescaped replacement `repl`; returns `nb`. -/
def substStep (ctx : Ctx) (repl : List UInt8) : SM I :=
  substLoop ctx repl (repl.length + 1) 0 (i 0)

/-- `nb += write(io, c)` for each character `c` of `cs`, in order. -/
def writeChars : List UInt8 → I → SM I
  | [], nb => pure nb
  | c :: t, nb => do
    let w ← writeU8 c
    writeChars t (nb + w)

end JuliaLean.RegexUnicode.Subst

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## `Regex` values and the builders -/

/-- The `CASELESS`, `MULTILINE`, `DOTALL`, `EXTENDED` bits (`imsx`) of `compile_options`. -/
structure Flags where
  i : Bool
  m : Bool
  s : Bool
  x : Bool
  deriving DecidableEq, Repr

def Flags.and (a b : Flags) : Flags := ⟨a.i && b.i, a.m && b.m, a.s && b.s, a.x && b.x⟩
def Flags.andNot (a b : Flags) : Flags := ⟨a.i && !b.i, a.m && !b.m, a.s && !b.s, a.x && !b.x⟩
/-- `mask = CASELESS | MULTILINE | DOTALL | EXTENDED`, `base/regex.jl:857`. -/
def maskAll : Flags := ⟨true, true, true, true⟩
def noFlags : Flags := ⟨false, false, false, false⟩

/-- A `Regex`: `pattern`, `compile_options` (the `imsx` bits and the other bits),
`match_options`. -/
structure Regex where
  pattern : List Char
  flags : Flags
  other : Nat
  mopts : Nat
  deriving DecidableEq

/-- Exceptions of the builders. -/
inductive RErr where
  /-- `ArgumentError("cannot multiply regexes: incompatible options")`. -/
  | argumentError
  /-- `ErrorException("PCRE compilation error: ...")`. -/
  | compile (e : LexErr)
  /-- Outside the modelled fragment. -/
  | unsupported
  /-- No `Regex` argument: `*` is the `String` method instead. -/
  | noMethod
  deriving DecidableEq

/-- Whether a pattern compiles. -/
def compiles (r : Regex) : Bool :=
  match lex r.pattern r.flags.x with
  | .ok _ => true
  | .error _ => false

/-- `Regex(pattern, compile_options, match_options)`, `base/regex.jl:29-45`: it compiles the
pattern. -/
def mkRegex (pattern : List Char) (flags : Flags) (other mopts : Nat) : Except RErr Regex :=
  match lex pattern flags.x with
  | .ok _ => .ok ⟨pattern, flags, other, mopts⟩
  | .error .unsupported => .error .unsupported
  | .error e => .error (.compile e)

/-- `string(i)` for an integer `i`. -/
def intDigits (n : Int) : List Char :=
  if n < 0 then '-' :: Nat.toDigits 10 n.natAbs else Nat.toDigits 10 n.toNat

/-- `^(r::Regex, i::Integer)`, `base/regex.jl:929`:
`Regex(string("(?:", r.pattern, "){$i}"), r.compile_options, r.match_options)`. -/
def pow (r : Regex) (n : Int) : Except RErr Regex :=
  mkRegex (['(', '?', ':'] ++ r.pattern ++ [')', '{'] ++ intDigits n ++ ['}']) r.flags r.other r.mopts

/-- `replace(s, raw"\E" => raw"\\E\QE")` (`base/regex.jl:881`): each `\E`, searched left
to right without overlap, becomes `\\E\QE`. -/
def replaceE : List Char → List Char
  | [] => []
  | [c] => [c]
  | c :: d :: t =>
    if c = '\\' ∧ d = 'E' then ['\\', '\\', 'E', '\\', 'Q', 'E'] ++ replaceE t else c :: replaceE (d :: t)

/-- `wrap_string(s::AbstractString, ::UInt32)`, `base/regex.jl:881`. -/
def wrapString (s : List Char) : List Char := ['\\', 'Q'] ++ replaceE s ++ ['\\', 'E']

/-- `regex_opts_str(opts)`, `base/regex.jl:884-907`: the letters `imsx` that are set. -/
def optsStr (f : Flags) : List Char :=
  (if f.i then ['i'] else []) ++ (if f.m then ['m'] else []) ++ (if f.s then ['s'] else []) ++
    (if f.x then ['x'] else [])

/-- An argument of `*`. -/
inductive Arg where
  | rx (r : Regex)
  | str (s : List Char)
  | chr (c : Char)

/-- `wrap_string`, `base/regex.jl:879-882`. -/
def wrapArg (unshared : Flags) : Arg → List Char
  | .rx r => ['(', '?'] ++ optsStr (r.flags.and unshared) ++ [':'] ++ r.pattern ++ [')']
  | .str s => wrapString s
  | .chr c => ['\\', 'Q', c, '\\', 'E']

/-- The option loop of `*`, `base/regex.jl:861-872`: `(match_opts, compile_opts)` of the
first `Regex`, and `shared`. -/
def mulOpts : List Arg → Option (Nat × Nat) → Flags → Except RErr (Option (Nat × Nat) × Flags)
  | [], o, sh => .ok (o, sh)
  | .rx r :: t, none, sh => mulOpts t (some (r.mopts, r.other)) (sh.and r.flags)
  | .rx r :: t, some (mo, co), sh =>
    if r.mopts = mo ∧ r.other = co then mulOpts t (some (mo, co)) (sh.and r.flags)
    else .error .argumentError
  | _ :: t, o, sh => mulOpts t o sh

/-- `*(r1::Union{Regex,AbstractString,AbstractChar}, rs...)`, `base/regex.jl:856-875`. -/
def mul (args : List Arg) : Except RErr Regex := do
  let (o, shared) ← mulOpts args none maskAll
  match o with
  | none => .error .noMethod
  | some (mo, co) =>
    let unshared := maskAll.andNot shared
    mkRegex (args.flatMap (wrapArg unshared)) shared co mo

/-! ## Capture names -/

/-- A key of `keys(m::RegexMatch)`. -/
inductive Key where
  | num (n : Nat)
  | name (s : List UInt8)
  deriving DecidableEq

/-- `keys(m::RegexMatch)`, `base/regex.jl:260-266`, for a regex with `ncap` groups. -/
def keys (ncap : Nat) (tbl : NameTable) : List Key :=
  (List.range ncap).map fun j =>
    match captureName tbl (j + 1) with
    | some s => .name s
    | none => .num (j + 1)

/-- `haskey(m::RegexMatch, idx::Integer)` and `haskey(m::RegexMatch, name)`,
`base/regex.jl:293-297`. -/
def haskey (ncap : Nat) (tbl : NameTable) : Key → Except IOErr Bool
  | .num n => .ok (1 ≤ n && n ≤ ncap)
  | .name s => do
    let g ← substringNumberFromName tbl s
    pure (decide (0 < g.val))

end JuliaLean.RegexUnicode.Subst

namespace JuliaLean.StringsCovB.Rx

open JuliaLean JuliaLean.Strings
open JuliaLean.RegexUnicode.Core (Pcre Ovec RErr RJl capSub mkRange)

/-- `DEFAULT_COMPILER_OPTS`, `base/regex.jl:7`. -/
def DEFAULT_COMPILER_OPTS : UInt32 := UTF ||| MATCH_INVALID_UTF ||| ALT_BSUX ||| UCP
/-- `DEFAULT_MATCH_OPTS`, `base/regex.jl:8`. -/
def DEFAULT_MATCH_OPTS : UInt32 := NO_UTF_CHECK
/-! ## `Regex` -/

/-- A `Regex` object: its fields, `regex == C_NULL` being `code = none`. -/
structure RegexObj where
  pattern : JStr
  copts : UInt32
  mopts : UInt32
  code : Option Code

/-- `UInt32(x)` for an `Integer`. -/
def toU32 (x : Int) : RJl UInt32 :=
  if 0 ≤ x ∧ x < 2 ^ 32 then .ok (UInt32.ofNat x.toNat)
  else .error (.str (.jl (.inexactError "trunc")))

/-- `compile(regex::Regex)`, `base/regex.jl:70-89` (the lock only serializes the
same steps): compile and JIT-compile once. -/
def compileRegex (lib : Lib) (re : RegexObj) : RJl (RegexObj × Code) :=
  match re.code with
  | some c => .ok (re, c)
  | none =>
    match compileP lib re.pattern re.copts with
    | .error e => .error e
    | .ok c =>
      match jitCompile lib c with
      | .error e => .error e
      | .ok _ => .ok ({ re with code := some c }, c)

/-- The inner constructor `Regex(pattern, compile_options, match_options)`,
`base/regex.jl:29-45`. -/
def regexCtor (lib : Lib) (pattern : JStr) (copts mopts : Int) : RJl RegexObj := do
  let co ← toU32 copts
  let mo ← toU32 mopts
  if co &&& ~~~COMPILE_MASK != 0 then
    throw (.str (.jl (.argumentError s!"invalid regex compile options: {co}")))
  if mo &&& ~~~EXECUTE_MASK != 0 then
    throw (.str (.jl (.argumentError s!"invalid regex match options: {mo}")))
  let (re, _) ← compileRegex lib ⟨pattern, co, mo, none⟩
  pure re

/-- The flag loop of `Regex(pattern, flags::AbstractString)`, `base/regex.jl:48-67`. -/
def flagsLoop : List UInt32 → UInt32 → UInt32 → RJl (UInt32 × UInt32)
  | [], co, mo => .ok (co, mo)
  | f :: fs, co, mo =>
    if f = 0x61000000 then -- 'a'
      flagsLoop fs (co &&& ~~~UCP &&& ~~~UTF &&& ~~~MATCH_INVALID_UTF) (mo &&& ~~~NO_UTF_CHECK)
    else if f = 0x69000000 then flagsLoop fs (co ||| CASELESS) mo
    else if f = 0x6d000000 then flagsLoop fs (co ||| MULTILINE) mo
    else if f = 0x73000000 then flagsLoop fs (co ||| DOTALL) mo
    else if f = 0x78000000 then flagsLoop fs (co ||| EXTENDED) mo
    else .error (.str (.jl (.argumentError "unknown regex flag")))

/-- `Regex(pattern, flags::AbstractString)`, `base/regex.jl:48-67`. -/
def regexFlags (lib : Lib) (pattern flags : JStr) : RJl RegexObj := do
  let (co, mo) ← flagsLoop (chars flags) DEFAULT_COMPILER_OPTS DEFAULT_MATCH_OPTS
  regexCtor lib pattern co.toNat mo.toNat

/-- `Regex(pattern) = Regex(pattern, DEFAULT_COMPILER_OPTS, DEFAULT_MATCH_OPTS)`,
`base/regex.jl:68`. -/
def regexDefault (lib : Lib) (pattern : JStr) : RJl RegexObj :=
  regexCtor lib pattern DEFAULT_COMPILER_OPTS.toNat DEFAULT_MATCH_OPTS.toNat

/-- `@r_str(pattern, flags...) = Regex(pattern, flags...)`, `base/regex.jl:123`. -/
def rStr (lib : Lib) (pattern : JStr) (flags : Option JStr) : RJl RegexObj :=
  match flags with
  | none => regexDefault lib pattern
  | some f => regexFlags lib pattern f

/-- The output of `show(io, re::Regex)`, `base/regex.jl:125-159`: in the default
form, the escaped pattern and the flag letters (`none` for the
`Regex(pattern, opts, mopts)` form). -/
def showFlags (opts mopts : UInt32) : Option (List UInt32) :=
  let imsx := CASELESS ||| MULTILINE ||| DOTALL ||| EXTENDED
  let ac := UTF ||| MATCH_INVALID_UTF ||| UCP
  let am := NO_UTF_CHECK
  let default := ((opts &&& ~~~imsx) ||| ac) == DEFAULT_COMPILER_OPTS
  let default := if default then
      (if opts &&& ac == ac then mopts == DEFAULT_MATCH_OPTS
       else if opts &&& ac == 0 then mopts == (DEFAULT_MATCH_OPTS &&& ~~~am)
       else false)
    else default
  if default then
    some ((if opts &&& CASELESS != 0 then [0x69000000] else []) ++
      (if opts &&& MULTILINE != 0 then [0x6d000000] else []) ++
      (if opts &&& DOTALL != 0 then [0x73000000] else []) ++
      (if opts &&& EXTENDED != 0 then [0x78000000] else []) ++
      (if opts &&& ac == 0 then [0x61000000] else []))
  else none

/-- `show(io, re::Regex)`: the printed bytes, with `escape_raw_string` and `show` of
the pattern and of the `UInt32` options as parameters. -/
def showRegex (escRaw showStr : JStr → List UInt8) (showU32 : UInt32 → List UInt8) (re : RegexObj) :
    List UInt8 :=
  match showFlags re.copts re.mopts with
  | some fl => "r\"".toUTF8.toList ++ escRaw re.pattern ++ "\"".toUTF8.toList ++ fl.flatMap charBytes
  | none => "Regex(".toUTF8.toList ++ showStr re.pattern ++ ", ".toUTF8.toList ++ showU32 re.copts ++
      ", ".toUTF8.toList ++ showU32 re.mopts ++ ")".toUTF8.toList

/-- `==(a::Regex, b::Regex)`, `base/regex.jl:814-816`. -/
def regexEq (a b : RegexObj) : Bool :=
  a.pattern == b.pattern && a.copts == b.copts && a.mopts == b.mopts

/-- `hash(r::Regex, h)`, `base/regex.jl:820-825`, with the hashes of `String` and
`UInt32` as parameters. -/
def hashRegex (hs : JStr → UInt64 → UInt64) (hu : UInt32 → UInt64 → UInt64) (r : RegexObj) (h : UInt64) :
    UInt64 :=
  let h := h ^^^ 0x67e195eb8555e72d
  let h := hs r.pattern h
  let h := hu r.copts h
  hu r.mopts h

/-! ## Concatenation, `base/regex.jl:856-909` -/

/-- An argument of `*`. -/
inductive Arg where
  | re (r : RegexObj)
  | str (s : JStr)
  | char (c : UInt32)

/-- The 16 entries of `_regex_opts_str[]` built by `init_regex()`,
`base/regex.jl:889-909`: `o` ranges over `0:15`. -/
def initRegex : List (UInt32 × List UInt32) :=
  (List.range 16).map fun o =>
    let opt : UInt32 := 0
    let str : List UInt32 := []
    let (opt, str) := if o &&& 1 != 0 then (opt ||| CASELESS, str ++ [0x69000000]) else (opt, str)
    let (opt, str) := if o &&& 2 != 0 then (opt ||| MULTILINE, str ++ [0x6d000000]) else (opt, str)
    let (opt, str) := if o &&& 4 != 0 then (opt ||| DOTALL, str ++ [0x73000000]) else (opt, str)
    let (opt, str) := if o &&& 8 != 0 then (opt ||| EXTENDED, str ++ [0x78000000]) else (opt, str)
    (opt, str)

/-- `regex_opts_str(opts)`, `base/regex.jl:884`: `ImmutableDict` lookup (the most
recent entry first), `KeyError` if absent. -/
def regexOptsStr (opts : UInt32) : RJl (List UInt32) :=
  match (initRegex.reverse.find? (·.1 == opts)) with
  | some (_, s) => .ok s
  | none => .error (.str (.jl (.argumentError "KeyError")))

/-- `wrap_string(s::AbstractChar, ::UInt32) = string("\\Q", s, "\\E")`, `base/regex.jl:882`. -/
def wrapChar (c : UInt32) : List UInt8 := "\\Q".toUTF8.toList ++ charBytes c ++ "\\E".toUTF8.toList

/-- The option loop of `*`, `base/regex.jl:857-871`: `(match_opts, compile_opts, shared)`. -/
def mulOpts (mask : UInt32) : List Arg → Option UInt32 → Option UInt32 → UInt32 →
    RJl (Option UInt32 × Option UInt32 × UInt32)
  | [], mo, co, shared => .ok (mo, co, shared)
  | .re r :: rest, mo, co, shared =>
    match mo with
    | none => mulOpts mask rest (some r.mopts) (some (r.copts &&& ~~~mask)) (shared &&& r.copts)
    | some m =>
      if r.mopts == m && some (r.copts &&& ~~~mask) == co then
        mulOpts mask rest mo co (shared &&& r.copts)
      else .error (.str (.jl (.argumentError "cannot multiply regexes: incompatible options")))
  | _ :: rest, mo, co, shared => mulOpts mask rest mo co shared

/-- `*(r1, rs...)`, `base/regex.jl:856-875`, given `wrap` for the `Regex` and
`String` cases of `wrap_string`: the pattern and options passed to `Regex`.
(At least one argument is a `Regex` by dispatch.) -/
def mulPattern (wrap : Arg → UInt32 → RJl (List UInt8)) (args : List Arg) :
    RJl (List UInt8 × UInt32 × UInt32) := do
  let mask := CASELESS ||| MULTILINE ||| DOTALL ||| EXTENDED
  let (mo, co, shared) ← mulOpts mask args none none mask
  let unshared := mask &&& ~~~shared
  let parts ← args.mapM (wrap · unshared)
  pure (parts.flatten, co.getD 0 ||| shared, mo.getD 0)

/-- `*(r::Regex) = r`, `base/regex.jl:877`. -/
def mulOne (r : RegexObj) : RegexObj := r

/-! ## `RegexMatch` -/

/-- A `RegexMatch` with the compiled pattern of its `regex` field. -/
structure RM where
  m : RegexUnicode.Core.RegexMatch
  code : Code

/-- The `RegexMatch(match, captures, offset, offsets, regex)` outer constructor,
`base/regex.jl:234-236`: an `offset::UInt` is converted to the `Int` field. -/
def regexMatchCtor (mat : JSub) (caps : List (Option JSub)) (offset : Int) (offsets : List JInt64)
    (code : Code) : RJl RM :=
  match JInt.convert (IntTy.i64.name) .i64 offset with
  | .error e => .error (.str (.jl e))
  | .ok off => .ok ⟨⟨mat, caps, off, offsets⟩, code⟩

/-- A key of `keys(m)`: a name or a group number. -/
inductive Key where
  | num (i : Nat)
  | name (n : List UInt8)
  deriving DecidableEq, Repr

/-- `keys(m::RegexMatch)`, `base/regex.jl:260-266`: `get(names, i, i)` for each group. -/
def keysM (m : RM) : RJl (List Key) := do
  let names ← captureNames m.code
  pure ((List.range m.m.captures.length).map fun i =>
    match names.find? (·.1 == i + 1) with
    | some (_, n) => .name n
    | none => .num (i + 1))

/-- `getindex(m::RegexMatch, idx::Integer) = m.captures[idx]`, `base/regex.jl:286`. -/
def getindexIdx (m : RM) (idx : JInt64) : RJl (Option JSub) :=
  if 1 ≤ idx.val ∧ idx.val ≤ m.m.captures.length then .ok (m.m.captures.getD (idx.val.toNat - 1) none)
  else .error (.str boundsErr)

/-- `getindex(m::RegexMatch, name)`, `base/regex.jl:287-291`. -/
def getindexName (m : RM) (name : List UInt8) : RJl (Option JSub) := do
  let idx ← substringNumberFromName m.code name
  if idx ≤ 0 then throw (.errorException "no capture group named found in regex")
  getindexIdx m (ix idx)

/-- `haskey(m::RegexMatch, idx::Integer) = idx in eachindex(m.captures)`, `base/regex.jl:293`. -/
def haskeyIdx (m : RM) (idx : JInt64) : Bool := decide (1 ≤ idx.val ∧ idx.val ≤ m.m.captures.length)

/-- `haskey(m::RegexMatch, name)`, `base/regex.jl:294-297`. -/
def haskeyName (m : RM) (name : List UInt8) : RJl Bool := do
  let idx ← substringNumberFromName m.code name
  pure (decide (idx > 0))

/-- `iterate(m::RegexMatch, i = 1) = iterate(m.captures, i)`, `base/regex.jl:299`. -/
def iterateM (m : RM) (i : Nat) : Option (Option JSub × Nat) :=
  if 1 ≤ i ∧ i ≤ m.m.captures.length then some (m.m.captures.getD (i - 1) none, i + 1) else none

/-- `length(m::RegexMatch) = length(m.captures)`, `base/regex.jl:300`. -/
def lengthM (m : RM) : Nat := m.m.captures.length

/-- `eltype(m::RegexMatch) = eltype(m.captures)` = `Union{Nothing, SubString{S}}`, `:301`. -/
def eltypeM (_m : RM) : String := "Union{Nothing, SubString{String}}"

/-- `NamedTuple(m) = NamedTuple{Symbol.(Tuple(keys(m)))}(values(m))`, `base/regex.jl:303`:
field names must be distinct. -/
def namedTupleM (m : RM) : RJl (List (Key × Option JSub)) := do
  let ks ← keysM m
  if ks.Nodup then pure (ks.zip m.m.captures)
  else throw (.errorException "duplicate field name in NamedTuple")

/-- `Dict(m) = Dict(pairs(m))`, `base/regex.jl:304`: `pairs(m)` iterates `keys(m)`
with `m[k]`; a later equal key replaces an earlier one. -/
def dictM (m : RM) : RJl (List (Key × Option JSub)) := do
  let ks ← keysM m
  ks.foldlM (fun d k => do
    let v ← match k with
      | .num i => getindexIdx m (ix i)
      | .name n => getindexName m n
    pure ((d.filter (·.1 != k)) ++ [(k, v)])) []

/-- `show(io, m::RegexMatch)`, `base/regex.jl:268-283`, with `show` of the match and of
a capture and `print` of a key as parameters. -/
def showM (showSub : JSub → List UInt8) (showCap : Option JSub → List UInt8) (printKey : Key → List UInt8)
    (m : RM) : RJl (List UInt8) := do
  let ks ← keysM m
  let body := if ks.isEmpty then [] else
    ", ".toUTF8.toList ++ ((ks.zip (List.range ks.length)).flatMap fun (k, i) =>
      printKey k ++ "=".toUTF8.toList ++ showCap (m.m.captures.getD i none) ++
        (if i + 1 < lengthM m then ", ".toUTF8.toList else []))
  pure ("RegexMatch(".toUTF8.toList ++ showSub m.m.mat ++ body ++ ")".toUTF8.toList)

/-! ## Matching -/

/-- `match(re, str::DenseUTF8String, idx, add_opts)`, `base/regex.jl:430-454`. -/
def matchRe (lib : Lib) (re : RegexObj) (s : JStr) (idx : JInt64) (addOpts : UInt32 := 0) :
    PM (RegexObj × Option RM) := do
  let (re, c) ← liftR (compileRegex lib re)
  let opts := re.mopts ||| addOpts
  let (matched, data) ← execRData c s (idx - ix 1) opts
  if !matched then
    freeMatchData data
    return (re, none)
  let some v ← ovecPtr data | return (re, none)
  let mat ← liftR (capSub s v.start v.stop)
  let cap ← liftR (v.caps.mapM (fun x => (match x with
      | none => .ok none
      | some (a, b) => some <$> capSub s a b : RJl (Option JSub))))
  let off := v.caps.map fun x => match x with
    | none => ix 0
    | some (a, _) => ix (a + 1)
  let result := RM.mk ⟨mat, cap, ix (v.start + 1), off⟩ c
  freeMatchData data
  return (re, some result)

/-- `match(r::Regex, s::AbstractString) = match(r, s, firstindex(s))`, `base/regex.jl:480`. -/
def matchFirst (lib : Lib) (re : RegexObj) (s : JStr) : PM (RegexObj × Option RM) :=
  matchRe lib re s (firstindex s)

/-- `match(r::Regex, s::AbstractString, i::Integer)` for a string that is not a
`DenseUTF8String`, `base/regex.jl:481-483`. -/
def matchNonDense : RJl Unit :=
  .error (.str (.jl (.argumentError "regex matching is only available for some dense (memory backed strings); use String(s) to convert s to String")))

/-- `_findnext_re(re, str, idx, C_NULL)`, `base/regex.jl:491-512` with allocation:
this is `findnext(re::Regex, str::DenseUTF8String, idx)` (`:485-487`). -/
def findnextRe (lib : Lib) (re : RegexObj) (s : JStr) (idx : JInt64) :
    PM (RegexObj × Option (JInt64 × JInt64)) := do
  let e1 ← liftR (RegexUnicode.Core.liftS (nextind s (lastindex s)))
  if idx.val > e1.val then throw (.str boundsErr)
  let opts := re.mopts
  let (re, c) ← liftR (compileRegex lib re)
  let (matched, data) ← execRData c s (idx - ix 1) opts
  let ans ← if matched then do
      let some v ← ovecPtr data | pure none
      let b ← liftR (RegexUnicode.Core.liftS (prevind s (ix (v.stop + 1))))
      pure (some (mkRange (ix (v.start + 1)) b))
    else pure none
  freeMatchData data
  return (re, ans)

/-- `findnext(r::Regex, s::AbstractString, idx)` for other strings, `base/regex.jl:513-515`. -/
def findnextNonString : RJl Unit :=
  .error (.str (.jl (.argumentError "regex search is only available for the String type; use String(s) to convert")))

/-- `occursin(r::Regex, s; offset)`, `base/regex.jl:306-314` (both methods; `String(s)`
of the generic method is the code units of `s`). -/
def occursinRe (lib : Lib) (re : RegexObj) (s : JStr) (offset : JInt64 := ix 0) : PM Bool := do
  let (re, c) ← liftR (compileRegex lib re)
  execR c s offset re.mopts

/-- `startswith(s, r::Regex)`, `base/regex.jl:338-346`. -/
def startswithRe (lib : Lib) (s : JStr) (re : RegexObj) : PM Bool := do
  let (re, c) ← liftR (compileRegex lib re)
  execR c s (ix 0) (re.mopts ||| ANCHORED)

/-- `endswith(s, r::Regex)`, `base/regex.jl:370-378`. -/
def endswithRe (lib : Lib) (s : JStr) (re : RegexObj) : PM Bool := do
  let (re, c) ← liftR (compileRegex lib re)
  execR c s (ix 0) (re.mopts ||| ENDANCHORED)

/-- `chopprefix(s, prefix::Regex)`, `base/regex.jl:380-384`. -/
def chopprefixRe (lib : Lib) (s : JStr) (re : RegexObj) : PM JSub := do
  let (_, m) ← matchRe lib re s (firstindex s) ANCHORED
  match m with
  | none => liftR (RegexUnicode.Core.liftS (substring s (ix 1) (lastindex s)))
  | some m => liftR (RegexUnicode.Core.liftS (substring s (ncodeunits m.m.mat.view + ix 1) (lastindex s)))

/-- `chopsuffix(s, suffix::Regex)`, `base/regex.jl:386-391`. -/
def chopsuffixRe (lib : Lib) (s : JStr) (re : RegexObj) : PM JSub := do
  let (_, m) ← matchRe lib re s (firstindex s) ENDANCHORED
  match m with
  | none => liftR (RegexUnicode.Core.liftS (substring s (ix 1) (lastindex s)))
  | some m =>
    if m.m.mat.ncu.val = 0 then liftR (RegexUnicode.Core.liftS (substring s (ix 1) (lastindex s)))
    else do
      let j ← liftR (RegexUnicode.Core.liftS (prevind s m.m.offset))
      liftR (RegexUnicode.Core.liftS (substring s (firstindex s) j))

/-- `_annotatedmatch(m, str)`, `base/regex.jl:456-464`: the match and the captures
become SubStrings of the `AnnotatedString` with the same offsets. -/
def annotatedMatch (m : RM) (str : Ann.AS) : Ann.ASub × List (Option Ann.ASub) :=
  (⟨str, m.m.mat.offset, m.m.mat.ncu⟩, m.m.captures.map (Option.map fun c => ⟨str, c.offset, c.ncu⟩))

/-- `match(re, str::AnnotatedString[, idx, add_opts])`, `base/regex.jl:466-478`. -/
def matchAnnotated (lib : Lib) (re : RegexObj) (str : Ann.AS) (idx : JInt64) (addOpts : UInt32 := 0) :
    PM (Option (Ann.ASub × List (Option Ann.ASub))) := do
  let (_, m) ← matchRe lib re str.str idx addOpts
  pure (m.map (annotatedMatch · str))

/-! ## `SubstitutionString`, replacement helpers and `RegexMatchIterator` -/

/-- `SubstitutionString{String}`, `base/regex.jl:606-608`. -/
structure SubstStr where
  string : JStr

/-- `ncodeunits`, `codeunit`, `isvalid` and `iterate` of a `SubstitutionString` forward
to its string, `base/regex.jl:609-613`. -/
def ssNcodeunits (s : SubstStr) : JInt64 := ncodeunits s.string
def ssCodeunitType (_s : SubstStr) : Nat := 8
def ssCodeunit (s : SubstStr) (i : JInt64) : SJl UInt8 := codeunit s.string i
def ssIsvalid (s : SubstStr) (i : JInt64) : Bool := isvalidAt s.string i
def ssIterate (s : SubstStr) (i : JInt64) : Option (UInt32 × JInt64) := iterate s.string i

/-- `show(io, s::SubstitutionString)`, `base/regex.jl:615-619`. -/
def showSubst (escRaw : JStr → List UInt8) (s : SubstStr) : List UInt8 :=
  "s\"".toUTF8.toList ++ escRaw s.string ++ "\"".toUTF8.toList

/-- `@s_str(string) = SubstitutionString(string)`, `base/regex.jl:636`. -/
def sStr (s : JStr) : SubstStr := ⟨s⟩

/-- `RegexAndMatchData(re)`, `base/regex.jl:640-644`: compile and allocate match data. -/
def regexAndMatchData (lib : Lib) (re : RegexObj) : PM (RegexObj × Code × Nat) := do
  let (re, c) ← liftR (compileRegex lib re)
  let md ← createMatchData c
  pure (re, c, md)

/-- `_findnext_re(re, str, idx, match_data)` with a given block: this is
`findnext(pat::RegexAndMatchData, str, i)`, `base/regex.jl:646`. -/
def findnextRMD (re : RegexObj) (c : Code) (md : Nat) (s : JStr) (idx : JInt64) :
    PM (Option (JInt64 × JInt64)) := do
  let e1 ← liftR (RegexUnicode.Core.liftS (nextind s (lastindex s)))
  if idx.val > e1.val then throw (.str boundsErr)
  let matched ← exec c s (idx - ix 1) re.mopts md
  if matched then do
    let some v ← ovecPtr md | pure none
    let b ← liftR (RegexUnicode.Core.liftS (prevind s (ix (v.stop + 1))))
    pure (some (mkRange (ix (v.start + 1)) b))
  else pure none

/-- `_pat_replacer(r::Regex) = RegexAndMatchData(r)`, `base/regex.jl:648`. -/
def patReplacer (lib : Lib) (re : RegexObj) : PM (RegexObj × Code × Nat) := regexAndMatchData lib re

/-- `_free_pat_replacer(r::RegexAndMatchData) = free_match_data(r.match_data)`, `:650`. -/
def freePatReplacer (md : Nat) : PM Unit := freeMatchData md

/-- `replace_err(repl) = error("Bad replacement string: $repl")`, `base/regex.jl:652`. -/
def replaceErr {α : Type} (repl : String) : RJl α := .error (.errorException s!"Bad replacement string: {repl}")

/-- `_write_capture(io, group, str, r, re)` for a pattern that is not a Regex,
`base/regex.jl:665-668`: only group 0 (the whole match `SubString(str, r)`). -/
def writeCaptureGeneric (out : List UInt8) (group : Int) (s : JStr) (r : JInt64 × JInt64) :
    RJl (JInt64 × List UInt8) := do
  if group ≠ 0 then replaceErr "pattern is not a Regex"
  let sub ← RegexUnicode.Core.liftS (substring s r.1 r.2)
  pure (ix sub.view.bytes.length, out ++ sub.view.bytes)

/-- `RegexMatchIterator(regex, string, ovr)`, `base/regex.jl:740-743`: the string is
converted to `String` (an `AnnotatedString` keeps its annotations). -/
structure RMI where
  regex : RegexObj
  string : Ann.AS
  overlap : Bool

def rmiCtor (re : RegexObj) (s : JStr) (ovr : Bool := false) : RMI := ⟨re, ⟨s, []⟩, ovr⟩
def rmiCtorAnnotated (re : RegexObj) (s : Ann.AS) (ovr : Bool := false) : RMI := ⟨re, ⟨s.str, s.anns⟩, ovr⟩

/-- `compile(itr::RegexMatchIterator) = (compile(itr.regex); itr)`, `base/regex.jl:745`. -/
def compileItr (lib : Lib) (itr : RMI) : RJl RMI :=
  (compileRegex lib itr.regex).map fun (re, _) => { itr with regex := re }

/-- `eltype(::Type{<:RegexMatchIterator}) = RegexMatch` and
`IteratorSize(::Type{<:RegexMatchIterator}) = SizeUnknown()`, `base/regex.jl:746-747`. -/
def rmiEltype : String := "RegexMatch"
def rmiIteratorSize : String := "SizeUnknown"

end JuliaLean.StringsCovB.Rx
