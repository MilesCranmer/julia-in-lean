import JuliaLean.RegexUnicode.CoreWrappers
import JuliaLean.StringsCovB.Ann

/-!
# `base/regex.jl` and `base/pcre.jl`

Models of the `Regex`, `RegexMatch`, `SubstitutionString` and `RegexMatchIterator`
methods of `base/regex.jl` and of the PCRE2 wrappers of `base/pcre.jl` (master
`bbfa0ce4150`; identical in 1.13.2 apart from line numbers).

* The C library is a primitive. A compiled pattern (`Code`) carries the
  matching primitive `Core.Pcre` of `JuliaLean.RegexUnicode.Core` together with
  its capture count, name table and `pcre2_pattern_info` answers; `Lib` holds the
  other entry points (`pcre2_compile`, `pcre2_get_error_message`,
  `pcre2_jit_compile`).
* `pcre2_match` (`execC`) first rejects options outside `PUBLIC_MATCH_OPTIONS`
  (`PCRE2_ERROR_BADOPTION`, pcre2api "Option bits for pcre2_match()") and start
  offsets beyond the subject (`PCRE2_ERROR_BADOFFSET`), then runs the primitive.
* Match-data blocks live in a `World`: `create_match_data` allocates a block,
  `pcre2_match` stores its output vector in it, `free_match_data` releases it.
* Option values are those of `pcre_h.jl` (observed for both versions).
-/

namespace JuliaLean.StringsCovB.Rx

open JuliaLean JuliaLean.Strings
open JuliaLean.RegexUnicode.Core (Pcre Ovec RErr RJl capSub mkRange)

/-! ## PCRE2 constants -/

def CASELESS : UInt32 := 0x00000008
def MULTILINE : UInt32 := 0x00000400
def DOTALL : UInt32 := 0x00000020
def EXTENDED : UInt32 := 0x00000080
def UTF : UInt32 := 0x00080000
def UCP : UInt32 := 0x00020000
def MATCH_INVALID_UTF : UInt32 := 0x04000000
def ALT_BSUX : UInt32 := 0x00000002
def NO_UTF_CHECK : UInt32 := 0x40000000
def ANCHORED : UInt32 := 0x80000000
def ENDANCHORED : UInt32 := 0x20000000
def NOTEMPTY_ATSTART : UInt32 := 0x00000008
/-- `PCRE.COMPILE_MASK`, `base/pcre.jl:67-96`. -/
def COMPILE_MASK : UInt32 := 0xe7ffffba
/-- `PCRE.EXECUTE_MASK`, `base/pcre.jl:119-130`: `NOTBOL | NOTEMPTY |
NOTEMPTY_ATSTART | NOTEOL | NO_START_OPTIMIZE | NO_UTF_CHECK | PARTIAL_HARD |
PARTIAL_SOFT`; `NO_START_OPTIMIZE` is the compile option `0x00010000`. -/
def EXECUTE_MASK : UInt32 := 0x4001003f
/-- The options `pcre2_match` accepts, `PUBLIC_MATCH_OPTIONS` of
`pcre2_internal.h`: `ANCHORED | ENDANCHORED | NOTBOL | NOTEOL | NOTEMPTY |
NOTEMPTY_ATSTART | NO_UTF_CHECK | PARTIAL_HARD | PARTIAL_SOFT | NO_JIT |
COPY_MATCHED_SUBJECT | DISABLE_RECURSELOOP_CHECK`. -/
def PUBLIC_MATCH_OPTIONS : UInt32 :=
  ANCHORED ||| ENDANCHORED ||| 0x1 ||| 0x2 ||| 0x4 ||| NOTEMPTY_ATSTART ||| NO_UTF_CHECK |||
    0x20 ||| 0x10 ||| 0x2000 ||| 0x4000 ||| 0x40000
/-- `DEFAULT_COMPILER_OPTS`, `base/regex.jl:7`. -/
def DEFAULT_COMPILER_OPTS : UInt32 := UTF ||| MATCH_INVALID_UTF ||| ALT_BSUX ||| UCP
/-- `DEFAULT_MATCH_OPTS`, `base/regex.jl:8`. -/
def DEFAULT_MATCH_OPTS : UInt32 := NO_UTF_CHECK
/-- `PCRE2_ERROR_UNSET`, `PCRE2_ERROR_BADDATA`, `PCRE2_ERROR_JIT_BADOPTION`, `PCRE2_ERROR_NULL`,
`PCRE2_ERROR_BADMAGIC`, `PCRE2_ERROR_BADOPTION`. -/
def ERROR_UNSET : Int := -55
def ERROR_BADDATA : Int := -29
def ERROR_JIT_BADOPTION : Int := -45
def ERROR_NULL : Int := -51
def ERROR_BADMAGIC : Int := -31
def ERROR_BADOPTION : Int := -34
def INFO_NAMECOUNT : UInt32 := 0x11
def INFO_NAMEENTRYSIZE : UInt32 := 0x12

/-! ## The C library -/

/-- A compiled pattern (`pcre2_code`). -/
structure Code where
  /-- `pcre2_match` on valid options and offsets. -/
  pcre : Pcre
  /-- Number of capture groups (the ovector has `ncaps + 1` pairs). -/
  ncaps : Nat
  /-- `pcre2_pattern_info(code, what, buf)` for integer answers: the value, or the
  negative return code. -/
  info : UInt32 → Except Int Nat
  /-- The bytes of the name table (`PCRE2_INFO_NAMETABLE`). -/
  nametable : List UInt8
  /-- `pcre2_substring_number_from_name(code, name)` for a NUL-free name. -/
  nameNumber : List UInt8 → Int
  /-- The return code of `pcre2_jit_compile(code, PCRE2_JIT_COMPLETE)`. -/
  jitRc : Int

/-- The other entry points. -/
structure Lib where
  /-- `pcre2_compile(pattern, length, options, &errno, &erroff, NULL)`: the code or
  `(errno, erroff)`. -/
  compile : List UInt8 → UInt32 → Except (Int × Nat) Code
  /-- `pcre2_get_error_message(errno, buffer, 1024)`: the message bytes, or `none`
  for `PCRE2_ERROR_BADDATA`. -/
  errmsg : Int → Option (List UInt8)

/-- Allocated match-data blocks and the output vector stored in each. -/
structure World where
  live : List Nat
  next : Nat
  ovecs : List (Nat × Option Ovec)

abbrev PM := EStateM RErr World

def liftR {α : Type} (x : RJl α) : PM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

def err {α : Type} (msg : String) : PM α := throw (.errorException msg)

/-- `create_match_data(re)`, `base/pcre.jl:232-237`
(`pcre2_match_data_create_from_pattern`; allocation failure is not modelled). -/
def createMatchData (_c : Code) : PM Nat := modifyGet fun w =>
  (w.next, { w with live := w.next :: w.live, next := w.next + 1 })

/-- `free_match_data(match_data)`, `base/pcre.jl:184-185`. -/
def freeMatchData (p : Nat) : PM Unit := modify fun w => { w with live := w.live.erase p }

/-- `free_re(re)`, `free_jit_stack(stack)` and `free_match_context(context)`,
`base/pcre.jl:187-194`: release one C object of the respective kind. -/
def freeObj (live : List Nat) (p : Nat) : List Nat := live.erase p

/-- The output vector stored in a block. -/
def ovecOf (p : Nat) : PM (Option Ovec) := do
  let w ← get
  pure ((w.ovecs.find? (·.1 == p)).bind (·.2))

/-- `pcre2_match(re, subject, ncodeunits(subject), offset, options, match_data, ctx)`
with the `Csize_t` conversion of `offset` done by `ccall`. -/
def execC (c : Code) (s : JStr) (offset : JInt64) (opts : UInt32) : RJl (Option Ovec) :=
  match JInt.convert .u64 offset.val with
  | .error e => .error (.str (.jl e))
  | .ok off =>
    if opts &&& ~~~PUBLIC_MATCH_OPTIONS != 0 then .error (.errorException "PCRE.exec error: bad option value")
    else if off.val > (s.bytes.length : Int) then .error (.errorException "PCRE.exec error: bad offset value")
    else .ok (c.pcre.run s off.val.toNat opts)

/-- `_exec(re, subject, offset, options, match_data)`, `base/pcre.jl:210-217`, and the
two `exec` methods (`:205-208`; `String(subject)` is the identity on a `String`):
`rc < -2` raises, otherwise the result is `rc >= 0`. -/
def exec (c : Code) (s : JStr) (offset : JInt64) (opts : UInt32) (md : Nat) : PM Bool := do
  let r ← liftR (execC c s offset opts)
  modify fun w => { w with ovecs := (md, r) :: w.ovecs }
  pure r.isSome

/-- `exec_r(re, subject, offset, options)`, `base/pcre.jl:219-224`. -/
def execR (c : Code) (s : JStr) (offset : JInt64) (opts : UInt32) : PM Bool := do
  let md ← createMatchData c
  let ans ← exec c s offset opts md
  freeMatchData md
  pure ans

/-- `exec_r_data(re, subject, offset, options)`, `base/pcre.jl:226-230`. -/
def execRData (c : Code) (s : JStr) (offset : JInt64) (opts : UInt32) : PM (Bool × Nat) := do
  let md ← createMatchData c
  let ans ← exec c s offset opts md
  pure (ans, md)

/-- `ovec_length(match_data) = 2Int(pcre2_get_ovector_count(match_data))`,
`base/pcre.jl:149-153`; the ovector of a match-data block created from a pattern
has `ncaps + 1` pairs. -/
def ovecLength (c : Code) : Nat := 2 * (c.ncaps + 1)

/-- `ovec_ptr(match_data)`, `base/pcre.jl:155-159`: the ovector, read through
`unsafe_load`. -/
def ovecPtr (md : Nat) : PM (Option Ovec) := ovecOf md

/-- `err_message(errno)`, `base/pcre.jl:196-203`: `PCRE2_ERROR_BADDATA` raises; otherwise
the NUL-terminated buffer is read with `unsafe_string`. -/
def errMessage (lib : Lib) (errno : Int) : RJl (List UInt8) :=
  match lib.errmsg errno with
  | none => .error (.errorException s!"PCRE error: invalid errno ({errno})")
  | some bs => .ok (bs.takeWhile (· != 0))

/-- `compile(pattern, options)`, `base/pcre.jl:161-174`. -/
def compileP (lib : Lib) (pattern : JStr) (options : UInt32) : RJl Code :=
  match lib.compile pattern.bytes options with
  | .ok c => .ok c
  | .error (errno, erroff) =>
    match errMessage lib errno with
    | .error e => .error e
    | .ok m => .error (.errorException
        s!"PCRE compilation error: {String.fromUTF8! ⟨m.toArray⟩} at offset {erroff}")

/-- `jit_compile(regex)`, `base/pcre.jl:176-182`. -/
def jitCompile (lib : Lib) (c : Code) : RJl Bool :=
  if c.jitRc = 0 then .ok true
  else if c.jitRc = ERROR_JIT_BADOPTION then .ok false
  else match errMessage lib c.jitRc with
    | .error e => .error e
    | .ok m => .error (.errorException s!"PCRE JIT error: {String.fromUTF8! ⟨m.toArray⟩}")

/-- `info(regex, what, T)`, `base/pcre.jl:135-147`. -/
def info (c : Code) (what : UInt32) : RJl Nat :=
  match c.info what with
  | .ok v => .ok v
  | .error ret => .error (.errorException
      (if ret = ERROR_NULL then "PCRE error: NULL regex object"
       else if ret = ERROR_BADMAGIC then "PCRE error: invalid regex object"
       else if ret = ERROR_BADOPTION then "PCRE error: invalid option flags"
       else s!"PCRE error: unknown error ({ret})"))

/-- `cconvert(Cstring, name)`: an embedded NUL is an `ArgumentError`
(`base/c.jl:211-224`). -/
def cstring (name : List UInt8) : RJl (List UInt8) :=
  if name.contains 0 then .error (.str (.jl (.argumentError "embedded NULs are not allowed in C strings")))
  else .ok name

/-- `substring_number_from_name(re, name)`, `base/pcre.jl:239-243`. -/
def substringNumberFromName (c : Code) (name : List UInt8) : RJl Int := do
  let n ← cstring name
  pure (c.nameNumber n)

/-- `substring_length_bynumber(match_data, number)`, `base/pcre.jl:245-254`, for a
group number that fits `Cint`: the length of the captured substring, `0` for an
unset group, an error for a group beyond the pattern. -/
def substringLengthBynumber (lib : Lib) (c : Code) (v : Ovec) (number : Nat) : RJl Nat :=
  if number = 0 then .ok (v.stop - v.start).toNat
  else if number ≤ c.ncaps then
    match v.caps.getD (number - 1) none with
    | none => .ok 0
    | some (a, b) => .ok (b - a).toNat
  else match errMessage lib (-49) with
    | .error e => .error e
    | .ok m => .error (.errorException s!"PCRE error: {String.fromUTF8! ⟨m.toArray⟩}")

/-- `substring_copy_bynumber(match_data, number, buf, buf_size)`,
`base/pcre.jl:256-263`: the copied bytes (without the terminating NUL). -/
def substringCopyBynumber (lib : Lib) (c : Code) (s : JStr) (v : Ovec) (number : Nat) :
    RJl (List UInt8) := do
  let n ← substringLengthBynumber lib c v number
  let a := if number = 0 then v.start else ((v.caps.getD (number - 1) none).map (·.1)).getD 0
  pure ((s.bytes.drop a.toNat).take n)

/-- One entry of the name table at the one-based `offset`: the big-endian group
index and the NUL-terminated name after it. -/
def nameEntry (tbl : List UInt8) (offset : Nat) : Nat × List UInt8 :=
  let high := (tbl.getD (offset - 1) 0).toNat
  let low := (tbl.getD offset 0).toNat
  ((high <<< 8) ||| low, (tbl.drop (offset + 1)).takeWhile (· != 0))

/-- `names[idx] = name` on a `Dict{Int,String}` held as an association list. -/
def dictSet (d : List (Nat × List UInt8)) (k : Nat) (v : List UInt8) : List (Nat × List UInt8) :=
  (d.filter (·.1 != k)) ++ [(k, v)]

/-- `capture_names(re)`, `base/pcre.jl:265-282`. -/
def captureNames (c : Code) : RJl (List (Nat × List UInt8)) := do
  let nameCount ← info c INFO_NAMECOUNT
  let entrySize ← info c INFO_NAMEENTRYSIZE
  pure ((List.range nameCount).foldl (fun d i =>
    let e := nameEntry c.nametable (i * entrySize + 1)
    dictSet d e.1 e.2) [])

/-! ## Thread-local match contexts, `base/pcre.jl:20-63` -/

/-- The global `THREAD_MATCH_CONTEXTS` and the C objects allocated so far. -/
structure Ctxs where
  ctxs : List Nat
  /-- Next fresh (non-null) pointer; `0` is `C_NULL`. -/
  next : Nat
  deriving DecidableEq, Repr

/-- `create_match_context()`, `base/pcre.jl:20-31`: a JIT stack and a match context
(two fresh objects); the context is returned. -/
def createMatchContext (w : Ctxs) : Nat × Ctxs := (w.next + 1, { w with next := w.next + 2 })

/-- `_tid() = Int(jl_threadid()) + 1`, `base/pcre.jl:37`, for the zero-based thread id. -/
def tid (threadid : Nat) : Nat := threadid + 1

/-- `_mth() = Threads.maxthreadid()`, `base/pcre.jl:38`. -/
def mth (maxthreadid : Nat) : Nat := maxthreadid

/-- The slow path growing `THREAD_MATCH_CONTEXTS` in `get_local_match_context()`,
`base/pcre.jl:43-55`: `copyto!(fill(C_NULL, length(ctxs) + _mth()), ctxs)` when the
vector is shorter than `tid`. -/
def growCtxs (t m : Nat) (w : Ctxs) : Ctxs :=
  if w.ctxs.length < t then { w with ctxs := w.ctxs ++ List.replicate m 0 } else w

/-- The rest of `get_local_match_context()`, `base/pcre.jl:56-62`: read slot `tid`;
if it is `C_NULL`, create a context and store it there. -/
def fetchCtx (t : Nat) (w : Ctxs) : Nat × Ctxs :=
  let ctx := w.ctxs.getD (t - 1) 0
  if ctx = 0 then
    let (ctx, w) := createMatchContext w
    (ctx, { w with ctxs := w.ctxs.set (t - 1) ctx })
  else (ctx, w)

/-- `get_local_match_context()`, `base/pcre.jl:40-63`, on thread `threadid` with
`maxthreadid` threads. -/
def getLocalMatchContext (threadid maxthreadid : Nat) (w : Ctxs) : Nat × Ctxs :=
  fetchCtx (tid threadid) (growCtxs (tid threadid) (mth maxthreadid) w)

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
  match JInt.convert .i64 offset with
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
