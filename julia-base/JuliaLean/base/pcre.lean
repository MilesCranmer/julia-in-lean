import JuliaLean.base.iobuffer
import JuliaLean.Runtime.Strings
import JuliaLean.Core

/-!
# Model of `base/pcre.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
PCRE2, allocation, pointer access, preservation, locks and thread-local state are
typed primitives in a caller-supplied monad. Their C ABI argument types are explicit.
Compile/execute status checks and source cleanup order are implemented here; no
regular-expression matching algorithm is substituted for PCRE2. `Codes` and option
values come from the included generated `pcre_h.jl`. A generic monad lets the
installed regex model instantiate these callees with its `Except` interface.
-/

namespace JuliaLean.base.pcre
open JuliaLean
abbrev I := JInt64
abbrev Size := JInt .u64
abbrev Cint := JInt .i32
abbrev Options := JInt .u32
def i (z : Int) : I := JInt.wrap .i64 z

def orOptions (a b : Options) : Options :=
  JInt.wrap .u32 ((BitVec.ofInt 32 a.val ||| BitVec.ofInt 32 b.val).toNat)

structure Codes where
  errorNull : Cint
  errorBadmagic : Cint
  errorBadoption : Cint
  errorJitBadoption : Cint
  errorBaddata : Cint
  errorUnset : Cint
  jitComplete : Options
  infoNamecount : Options
  infoNameentrysize : Options
  infoNametable : Options

structure Errors (E : Type) where
  errorException : String → E
  jl : JlError → E

structure Memory (m : Type → Type) (Handle Buffer Str : Type) (Ref : Type → Type) where
  null : Handle
  isNull : Handle → Bool
  newRef : {T : Type} → Option T → m (Ref T)
  readRef : {T : Type} → Ref T → m T
  newBuffer : I → m Buffer
  bufferLength : Buffer → m I
  bufferPointer : Buffer → m Handle
  unsafeString : Handle → m Str
  preserve : {T : Type} → Buffer → m T → m T

structure ContextOps (m : Type → Type) (Handle Vector Lock : Type) where
  null : Handle
  isNull : Handle → Bool
  jitStackCreate : Size → Size → Handle → m Handle
  contextCreate : Handle → m Handle
  jitStackAssign : Handle → Handle → Handle → m Unit
  jlThreadid : m (JInt .i16)
  maxthreadid : m I
  getContexts : m Vector
  setContexts : Vector → m Unit
  length : Vector → m I
  getindex : Vector → I → m Handle
  setindex : Vector → I → Handle → m Unit
  fillNull : I → m Vector
  copyto : Vector → Vector → m Vector
  getCompileLock : m Lock
  lock : Lock → m Unit
  unlock : Lock → m Unit

section
variable {m : Type → Type} [Monad m] {E : Type} [MonadExceptOf E m]

def liftJl {A : Type} (errors : Errors E) (result : Jl A) : m A :=
  match result with | .ok value => pure value | .error e => throwThe E (errors.jl e)

def finallyDo {A B : Type} (body : m A) (cleanup : m B) : m A := do
  let result ← tryCatchThe E (do pure (Except.ok (← body))) (fun e => pure (Except.error e))
  let _ ← cleanup
  match result with | .ok value => pure value | .error error => throwThe E error

/--
Julia source: base/pcre.jl:12-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.iswindows()
    const PCRE_LIB = "libpcre2-8-0.dll"
elseif Sys.isapple()
    const PCRE_LIB = "@rpath/libpcre2-8.0.dylib"
else
    const PCRE_LIB = "libpcre2-8.so.0"
end
```
-/
def pcreLibrary (iswindows isapple : Bool) : String :=
  if iswindows then "libpcre2-8-0.dll"
  else if isapple then "@rpath/libpcre2-8.0.dylib"
  else "libpcre2-8.so.0"

/--
Julia source: base/pcre.jl:20-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function create_match_context()
    JIT_STACK_START_SIZE = 32768
    JIT_STACK_MAX_SIZE = 1048576
    jit_stack = ccall((:pcre2_jit_stack_create_8, PCRE_LIB), Ptr{Cvoid},
                      (Csize_t, Csize_t, Ptr{Cvoid}),
                      JIT_STACK_START_SIZE, JIT_STACK_MAX_SIZE, C_NULL)
    ctx = ccall((:pcre2_match_context_create_8, PCRE_LIB),
                Ptr{Cvoid}, (Ptr{Cvoid},), C_NULL)
    ccall((:pcre2_jit_stack_assign_8, PCRE_LIB), Cvoid,
          (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}), ctx, C_NULL, jit_stack)
    return ctx
end
```
-/
def createMatchContext {Handle Vector Lock : Type} (ops : ContextOps m Handle Vector Lock) : m Handle := do
  let jitStack ← ops.jitStackCreate (JInt.wrap .u64 32768) (JInt.wrap .u64 1048576) ops.null
  let ctx ← ops.contextCreate ops.null
  ops.jitStackAssign ctx ops.null jitStack
  pure ctx

/--
Julia source: base/pcre.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_tid() = Int(ccall(:jl_threadid, Int16, ())) + 1
```
-/
def tid {Handle Vector Lock : Type} (ops : ContextOps m Handle Vector Lock) : m I := do
  pure (i (← ops.jlThreadid).val + i 1)

/--
Julia source: base/pcre.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_mth() = Threads.maxthreadid()
```
-/
def mth {Handle Vector Lock : Type} (ops : ContextOps m Handle Vector Lock) : m I := ops.maxthreadid

/--
Julia source: base/pcre.jl:40-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_local_match_context()
    tid = _tid()
    ctxs = THREAD_MATCH_CONTEXTS
    if length(ctxs) < tid
        # slow path to allocate it
        l = PCRE_COMPILE_LOCK
        lock(l)
        try
            ctxs = THREAD_MATCH_CONTEXTS
            if length(ctxs) < tid
                global THREAD_MATCH_CONTEXTS = ctxs = copyto!(fill(C_NULL, length(ctxs) + _mth()), ctxs)
            end
        finally
            unlock(l)
        end
    end
    ctx = @inbounds ctxs[tid]
    if ctx == C_NULL
        # slow path to allocate it
        ctx = create_match_context()
        THREAD_MATCH_CONTEXTS[tid] = ctx
    end
    return ctx
end
```
-/
def getLocalMatchContext {Handle Vector Lock : Type} (ops : ContextOps m Handle Vector Lock) : m Handle := do
  let tid ← tid ops
  let mut ctxs ← ops.getContexts
  if (← ops.length ctxs) < tid then
    let lock ← ops.getCompileLock
    ops.lock lock
    let grown ← finallyDo (E := E) (do
        let current ← ops.getContexts
        if (← ops.length current) < tid then
          let filled ← ops.fillNull ((← ops.length current) + (← mth ops))
          let copied ← ops.copyto filled current
          ops.setContexts copied
          pure copied
        else pure current) (ops.unlock lock)
    ctxs := grown
  let mut ctx ← ops.getindex ctxs tid
  if ops.isNull ctx then
    ctx := ← createMatchContext ops
    ops.setindex (← ops.getContexts) tid ctx
  pure ctx

/--
Julia source: base/pcre.jl:68-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const COMPILE_MASK      =
      ALT_BSUX          |
      ALT_CIRCUMFLEX    |
      ALT_VERBNAMES     |
      ANCHORED          |
      # AUTO_CALLOUT    |
      CASELESS          |
      DOLLAR_ENDONLY    |
      DOTALL            |
      # DUPNAMES        |
      ENDANCHORED       |
      EXTENDED          |
      EXTENDED_MORE     |
      FIRSTLINE         |
      LITERAL           |
      MATCH_INVALID_UTF |
      MATCH_UNSET_BACKREF |
      MULTILINE         |
      NEVER_BACKSLASH_C |
      NEVER_UCP         |
      NEVER_UTF         |
      NO_AUTO_CAPTURE   |
      NO_AUTO_POSSESS   |
      NO_DOTSTAR_ANCHOR |
      NO_START_OPTIMIZE |
      NO_UTF_CHECK      |
      UCP               |
      UNGREEDY          |
      USE_OFFSET_LIMIT  |
      UTF
```
-/
def compileMask (constant : String → Options) : Options :=
  ["ALT_BSUX", "ALT_CIRCUMFLEX", "ALT_VERBNAMES", "ANCHORED", "CASELESS", "DOLLAR_ENDONLY", "DOTALL", "ENDANCHORED", "EXTENDED", "EXTENDED_MORE", "FIRSTLINE", "LITERAL", "MATCH_INVALID_UTF", "MATCH_UNSET_BACKREF", "MULTILINE", "NEVER_BACKSLASH_C", "NEVER_UCP", "NEVER_UTF", "NO_AUTO_CAPTURE", "NO_AUTO_POSSESS", "NO_DOTSTAR_ANCHOR", "NO_START_OPTIMIZE", "NO_UTF_CHECK", "UCP", "UNGREEDY", "USE_OFFSET_LIMIT", "UTF"].foldl (fun mask name => orOptions mask (constant name)) (JInt.wrap .u32 0)

/--
Julia source: base/pcre.jl:109-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const COMPILE_EXTRA_MASK            =
      EXTRA_ALLOW_SURROGATE_ESCAPES |
      EXTRA_ALT_BSUX                |
      EXTRA_BAD_ESCAPE_IS_LITERAL   |
      EXTRA_ESCAPED_CR_IS_LF        |
      EXTRA_MATCH_LINE              |
      EXTRA_MATCH_WORD
```
-/
def compileExtraMask (constant : String → Options) : Options :=
  ["EXTRA_ALLOW_SURROGATE_ESCAPES", "EXTRA_ALT_BSUX", "EXTRA_BAD_ESCAPE_IS_LITERAL", "EXTRA_ESCAPED_CR_IS_LF", "EXTRA_MATCH_LINE", "EXTRA_MATCH_WORD"].foldl (fun mask name => orOptions mask (constant name)) (JInt.wrap .u32 0)

/--
Julia source: base/pcre.jl:118-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const EXECUTE_MASK      =
      # ANCHORED        |
      # COPY_MATCHED_SUBJECT |
      # ENDANCHORED     |
      NOTBOL            |
      NOTEMPTY          |
      NOTEMPTY_ATSTART  |
      NOTEOL            |
      # NO_JIT          |
      NO_START_OPTIMIZE |
      NO_UTF_CHECK      |
      PARTIAL_HARD      |
      PARTIAL_SOFT
```
-/
def executeMask (constant : String → Options) : Options :=
  ["NOTBOL", "NOTEMPTY", "NOTEMPTY_ATSTART", "NOTEOL", "NO_START_OPTIMIZE", "NO_UTF_CHECK", "PARTIAL_HARD", "PARTIAL_SOFT"].foldl (fun mask name => orOptions mask (constant name)) (JInt.wrap .u32 0)

/--
Julia source: base/pcre.jl:100-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const COMPILE_NEWLINE_MASK = (
      NEWLINE_CR,
      NEWLINE_LF,
      NEWLINE_CRLF,
      NEWLINE_ANY,
      NEWLINE_ANYCRLF,
      NEWLINE_NUL)
```
-/
def compileNewlineMask (constant : String → Options) : List Options :=
  ["NEWLINE_CR", "NEWLINE_LF", "NEWLINE_CRLF", "NEWLINE_ANY", "NEWLINE_ANYCRLF", "NEWLINE_NUL"].map constant

/--
Julia source: base/pcre.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const UNSET = ~Csize_t(0)  # Indicates that an output vector element is unset
```
-/
def unset : Size := JInt.wrap .u64 (-1)

/--
Julia source: base/pcre.jl:135-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function info(regex::Ptr{Cvoid}, what::Integer, ::Type{T}) where T
    buf = RefValue{T}()
    ret = ccall((:pcre2_pattern_info_8, PCRE_LIB), Cint,
                (Ptr{Cvoid}, UInt32, Ptr{Cvoid}),
                regex, what, buf)
    if ret != 0
        error(ret == ERROR_NULL      ? "PCRE error: NULL regex object" :
              ret == ERROR_BADMAGIC  ? "PCRE error: invalid regex object" :
              ret == ERROR_BADOPTION ? "PCRE error: invalid option flags" :
                                       "PCRE error: unknown error ($ret)")
    end
    return buf[]
end
```
-/
def info {Handle Buffer Str T Integer : Type} {Ref : Type → Type}
    (errors : Errors E) (codes : Codes) (memory : Memory m Handle Buffer Str Ref)
    (convertWhat : Integer → m Options)
    (patternInfo : Handle → Options → Ref T → m Cint)
    (regex : Handle) (what : Integer) : m T := do
  let buf ← memory.newRef (T := T) none
  let ret ← patternInfo regex (← convertWhat what) buf
  if ret.val != 0 then
    let message := if ret == codes.errorNull then "PCRE error: NULL regex object"
      else if ret == codes.errorBadmagic then "PCRE error: invalid regex object"
      else if ret == codes.errorBadoption then "PCRE error: invalid option flags"
      else "PCRE error: unknown error (" ++ toString ret.val ++ ")"
    throwThe E (errors.errorException message)
  memory.readRef buf

/--
Julia source: base/pcre.jl:149-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ovec_length(match_data)
    n = ccall((:pcre2_get_ovector_count_8, PCRE_LIB), UInt32,
              (Ptr{Cvoid},), match_data)
    return 2Int(n)
end
```
-/
def ovecLength {Data : Type} (getOvectorCount : Data → m Options) (matchData : Data) : m I := do
  pure (i 2 * i (← getOvectorCount matchData).val)

/--
Julia source: base/pcre.jl:155-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ovec_ptr(match_data)
    ptr = ccall((:pcre2_get_ovector_pointer_8, PCRE_LIB), Ptr{Csize_t},
                (Ptr{Cvoid},), match_data)
    return ptr
end
```
-/
def ovecPtr {Data Pointer : Type} (getOvectorPointer : Data → m Pointer) (matchData : Data) : m Pointer := do
  let ptr ← getOvectorPointer matchData
  pure ptr

/--
Julia source: base/pcre.jl:161-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compile(pattern::AbstractString, options::Integer)
    if !(pattern isa Union{String,SubString{String}})
        pattern = String(pattern)
    end
    errno = RefValue{Cint}(0)
    erroff = RefValue{Csize_t}(0)
    re_ptr = ccall((:pcre2_compile_8, PCRE_LIB), Ptr{Cvoid},
                   (Ptr{UInt8}, Csize_t, UInt32, Ref{Cint}, Ref{Csize_t}, Ptr{Cvoid}),
                   pattern, ncodeunits(pattern), options, errno, erroff, C_NULL)
    if re_ptr == C_NULL
        error("PCRE compilation error: $(err_message(errno[])) at offset $(erroff[])")
    end
    return re_ptr
end
```
-/
def compile {Handle Buffer Str Pattern Integer : Type} {Ref : Type → Type}
    (errors : Errors E) (memory : Memory m Handle Buffer Str Ref)
    (isDense : Pattern → Bool) (convertString : Pattern → m Str) (denseString : Pattern → Str)
    (ncodeunits : Str → m I) (convertOptions : Integer → m Options)
    (compile8 : Str → Size → Options → Ref Cint → Ref Size → Handle → m Handle)
    (errMessage : Cint → m String) (pattern : Pattern) (options : Integer) : m Handle := do
  let pattern ← if isDense pattern then pure (denseString pattern) else convertString pattern
  let errno ← memory.newRef (some (JInt.wrap .i32 0))
  let erroff ← memory.newRef (some (JInt.wrap .u64 0))
  let count ← ncodeunits pattern
  let count ← liftJl errors (JInt.convert "convert" .u64 count.val)
  let re ← compile8 pattern count (← convertOptions options) errno erroff memory.null
  if memory.isNull re then
    let msg ← errMessage (← memory.readRef errno)
    let offset ← memory.readRef erroff
    throwThe E (errors.errorException ("PCRE compilation error: " ++ msg ++ " at offset " ++ toString offset.val))
  pure re

/--
Julia source: base/pcre.jl:176-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function jit_compile(regex::Ptr{Cvoid})
    errno = ccall((:pcre2_jit_compile_8, PCRE_LIB), Cint,
                  (Ptr{Cvoid}, UInt32), regex, JIT_COMPLETE)
    errno == 0 && return true
    errno == ERROR_JIT_BADOPTION && return false
    error("PCRE JIT error: $(err_message(errno))")
end
```
-/
def jitCompile {Handle : Type} (errors : Errors E) (codes : Codes)
    (jitCompile8 : Handle → Options → m Cint) (errMessage : Cint → m String) (regex : Handle) : m Bool := do
  let errno ← jitCompile8 regex codes.jitComplete
  if errno.val == 0 then return true
  if errno == codes.errorJitBadoption then return false
  throwThe E (errors.errorException ("PCRE JIT error: " ++ (← errMessage errno)))

/--
Julia source: base/pcre.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
free_match_data(match_data) =
    ccall((:pcre2_match_data_free_8, PCRE_LIB), Cvoid, (Ptr{Cvoid},), match_data)
```
-/
def freeMatchData {Handle : Type} (free : Handle → m Unit) (value : Handle) : m Unit := free value

/--
Julia source: base/pcre.jl:187-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
free_re(re) =
    ccall((:pcre2_code_free_8, PCRE_LIB), Cvoid, (Ptr{Cvoid},), re)
```
-/
def freeRe {Handle : Type} (free : Handle → m Unit) (value : Handle) : m Unit := free value

/--
Julia source: base/pcre.jl:190-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
free_jit_stack(stack) =
    ccall((:pcre2_jit_stack_free_8, PCRE_LIB), Cvoid, (Ptr{Cvoid},), stack)
```
-/
def freeJitStack {Handle : Type} (free : Handle → m Unit) (value : Handle) : m Unit := free value

/--
Julia source: base/pcre.jl:193-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
free_match_context(context) =
    ccall((:pcre2_match_context_free_8, PCRE_LIB), Cvoid, (Ptr{Cvoid},), context)
```
-/
def freeMatchContext {Handle : Type} (free : Handle → m Unit) (value : Handle) : m Unit := free value

/--
Julia source: base/pcre.jl:196-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function err_message(errno::Integer)
    buffer = Vector{UInt8}(undef, 1024)
    ret = ccall((:pcre2_get_error_message_8, PCRE_LIB), Cint,
                (Cint, Ptr{UInt8}, Csize_t), errno, buffer, length(buffer))
    ret == ERROR_BADDATA && error("PCRE error: invalid errno ($errno)")
    # TODO: seems like there should be a better way to get this string
    return GC.@preserve buffer unsafe_string(pointer(buffer))
end
```
-/
def errMessage {Handle Buffer Str Integer : Type} {Ref : Type → Type}
    (errors : Errors E) (codes : Codes) (memory : Memory m Handle Buffer Str Ref)
    (convertErrno : Integer → m Cint)
    (getErrorMessage8 : Cint → Buffer → Size → m Cint) (errnoString : Integer → String)
    (errno : Integer) : m Str := do
  let buffer ← memory.newBuffer (i 1024)
  let length ← memory.bufferLength buffer
  let length ← liftJl errors (JInt.convert "convert" .u64 length.val)
  let ret ← getErrorMessage8 (← convertErrno errno) buffer length
  if ret == codes.errorBaddata then
    throwThe E (errors.errorException ("PCRE error: invalid errno (" ++ errnoString errno ++ ")"))
  memory.preserve buffer (do memory.unsafeString (← memory.bufferPointer buffer))

/--
Julia source: base/pcre.jl:210-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _exec(re, subject, offset, options, match_data)
    rc = ccall((:pcre2_match_8, PCRE_LIB), Cint,
               (Ptr{Cvoid}, Ptr{UInt8}, Csize_t, Csize_t, UInt32, Ptr{Cvoid}, Ptr{Cvoid}),
               re, subject, ncodeunits(subject), offset, options, match_data, get_local_match_context())
    # rc == -1 means no match, -2 means partial match.
    rc < -2 && error("PCRE.exec error: $(err_message(rc))")
    return rc >= 0
end
```
-/
def execCore {Handle Subject Offset MatchOptions Data : Type}
    (errors : Errors E) (ncodeunits : Subject → m I) (localContext : m Handle)
    (match8 : Handle → Subject → I → Offset → MatchOptions → Data → Handle → m Cint)
    (errMessage : Cint → m String) (re : Handle) (subject : Subject) (offset : Offset)
    (options : MatchOptions) (matchData : Data) : m Bool := do
  let count ← ncodeunits subject
  let context ← localContext
  let rc ← match8 re subject count offset options matchData context
  if rc.val < -2 then
    throwThe E (errors.errorException ("PCRE.exec error: " ++ (← errMessage rc)))
  pure (rc.val ≥ 0)

/--
Julia source: base/pcre.jl:205-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exec(re, subject::DenseUTF8String, offset, options, match_data) =
    _exec(re, subject, offset, options, match_data)
```
-/
def execDense {Re Subject Offset Options Data : Type}
    (exec : Re → Subject → Offset → Options → Data → m Bool)
    (re : Re) (subject : Subject) (offset : Offset) (options : Options) (matchData : Data) : m Bool :=
  exec re subject offset options matchData

/--
Julia source: base/pcre.jl:207-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exec(re, subject, offset, options, match_data) =
    _exec(re, String(subject)::String, offset, options, match_data)
```
-/
def execOther {Re Subject Str Offset Options Data : Type}
    (toString : Subject → m Str) (exec : Re → Str → Offset → Options → Data → m Bool)
    (re : Re) (subject : Subject) (offset : Offset) (options : Options) (matchData : Data) : m Bool := do
  exec re (← toString subject) offset options matchData

/--
Julia source: base/pcre.jl:219-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exec_r(re, subject, offset, options)
    match_data = create_match_data(re)
    ans = exec(re, subject, offset, options, match_data)
    free_match_data(match_data)
    return ans
end
```
-/
def execR {Re Subject Offset Options Data : Type} (createMatchData : Re → m Data)
    (exec : Re → Subject → Offset → Options → Data → m Bool) (freeMatchData : Data → m Unit)
    (re : Re) (subject : Subject) (offset : Offset) (options : Options) : m Bool := do
  let matchData ← createMatchData re
  let ans ← exec re subject offset options matchData
  freeMatchData matchData
  pure ans

/--
Julia source: base/pcre.jl:226-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exec_r_data(re, subject, offset, options)
    match_data = create_match_data(re)
    ans = exec(re, subject, offset, options, match_data)
    return ans, match_data
end
```
-/
def execRData {Re Subject Offset Options Data : Type} (createMatchData : Re → m Data)
    (exec : Re → Subject → Offset → Options → Data → m Bool)
    (re : Re) (subject : Subject) (offset : Offset) (options : Options) : m (Bool × Data) := do
  let matchData ← createMatchData re
  let ans ← exec re subject offset options matchData
  pure (ans, matchData)

/--
Julia source: base/pcre.jl:232-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function create_match_data(re)
    p = ccall((:pcre2_match_data_create_from_pattern_8, PCRE_LIB),
              Ptr{Cvoid}, (Ptr{Cvoid}, Ptr{Cvoid}), re, C_NULL)
    p == C_NULL && error("PCRE error: could not allocate memory")
    return p
end
```
-/
def createMatchData {Re Handle : Type} (errors : Errors E) (null : Handle)
    (isNull : Handle → Bool) (createFromPattern8 : Re → Handle → m Handle) (re : Re) : m Handle := do
  let p ← createFromPattern8 re null
  if isNull p then throwThe E (errors.errorException "PCRE error: could not allocate memory")
  pure p

/--
Julia source: base/pcre.jl:239-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function substring_number_from_name(re, name)
    n = ccall((:pcre2_substring_number_from_name_8, PCRE_LIB), Cint,
               (Ptr{Cvoid}, Cstring), re, name)
    return Int(n)
end
```
-/
def substringNumberFromName {Re Name : Type}
    (numberFromName8 : Re → Name → m Cint) (re : Re) (name : Name) : m I := do
  pure (i (← numberFromName8 re name).val)

/--
Julia source: base/pcre.jl:245-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function substring_length_bynumber(match_data, number)
    s = RefValue{Csize_t}()
    rc = ccall((:pcre2_substring_length_bynumber_8, PCRE_LIB), Cint,
               (Ptr{Cvoid}, Cint, Ref{Csize_t}), match_data, number, s)
    if rc < 0
        rc == ERROR_UNSET && return 0
        error("PCRE error: $(err_message(rc))")
    end
    return Int(s[])
end
```
-/
def substringLengthByNumber {Handle Buffer Str Number Data : Type} {Ref : Type → Type}
    (errors : Errors E) (codes : Codes) (memory : Memory m Handle Buffer Str Ref)
    (lengthByNumber8 : Data → Number → Ref Size → m Cint) (errMessage : Cint → m String)
    (matchData : Data) (number : Number) : m I := do
  let s ← memory.newRef (T := Size) none
  let rc ← lengthByNumber8 matchData number s
  if rc.val < 0 then
    if rc == codes.errorUnset then return i 0
    throwThe E (errors.errorException ("PCRE error: " ++ (← errMessage rc)))
  liftJl errors (JInt.convert "convert" .i64 (← memory.readRef s).val)

/--
Julia source: base/pcre.jl:256-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function substring_copy_bynumber(match_data, number, buf, buf_size)
    s = RefValue{Csize_t}(buf_size)
    rc = ccall((:pcre2_substring_copy_bynumber_8, PCRE_LIB), Cint,
               (Ptr{Cvoid}, UInt32, Ptr{UInt8}, Ref{Csize_t}),
               match_data, number, buf, s)
    rc < 0 && error("PCRE error: $(err_message(rc))")
    return Int(s[])
end
```
-/
def substringCopyByNumber {Handle Buffer Str Number Data BufferSize : Type} {Ref : Type → Type}
    (errors : Errors E) (memory : Memory m Handle Buffer Str Ref)
    (convertSize : BufferSize → m Size)
    (copyByNumber8 : Data → Number → Buffer → Ref Size → m Cint) (errMessage : Cint → m String)
    (matchData : Data) (number : Number) (buf : Buffer) (bufSize : BufferSize) : m I := do
  let s ← memory.newRef (some (← convertSize bufSize))
  let rc ← copyByNumber8 matchData number buf s
  if rc.val < 0 then throwThe E (errors.errorException ("PCRE error: " ++ (← errMessage rc)))
  liftJl errors (JInt.convert "convert" .i64 (← memory.readRef s).val)

/--
Julia source: base/pcre.jl:265-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function capture_names(re)
    name_count = info(re, INFO_NAMECOUNT, UInt32)
    name_entry_size = info(re, INFO_NAMEENTRYSIZE, UInt32)
    nametable_ptr = info(re, INFO_NAMETABLE, Ptr{UInt8})
    names = Dict{Int,String}()
    for i = 1:name_count
        offset = (i-1)*name_entry_size + 1
        # The capture group index corresponding to name 'i' is stored as a
        # big-endian 16-bit value.
        high_byte = UInt16(unsafe_load(nametable_ptr, offset))
        low_byte = UInt16(unsafe_load(nametable_ptr, offset+1))
        idx = (high_byte << 8) | low_byte
        # The capture group name is a null-terminated string located directly
        # after the index.
        names[idx] = unsafe_string(nametable_ptr+offset+1)
    end
    return names
end
```
-/
def captureNames {Re Handle Str Dict : Type}
    (nameCount : Re → m Options) (nameEntrySize : Re → m Options) (nameTable : Re → m Handle)
    (newDict : m Dict) (loadByte : Handle → I → m (JInt .u8))
    (addPointer : Handle → I → m Handle) (unsafeString : Handle → m Str)
    (set : Dict → I → Str → m Unit) (re : Re) : m Dict := do
  let count ← nameCount re
  let entrySize ← nameEntrySize re
  let table ← nameTable re
  let names ← newDict
  for n in List.range count.val.toNat do
    let index := i n + i 1
    let offset := (index - i 1) * i entrySize.val + i 1
    let high := JInt.wrap .u16 (← loadByte table offset).val
    let low := JInt.wrap .u16 (← loadByte table (offset + i 1)).val
    let idx := JInt.wrap .u16 ((BitVec.ofInt 16 high.val <<< 8 ||| BitVec.ofInt 16 low.val).toNat)
    let name ← unsafeString (← addPointer table (offset + i 1))
    set names (i idx.val) name
  pure names


end

/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/pcre.jl:1-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## low-level pcre2 interface ##
-- 
-- module PCRE
-- 
-- import ..RefValue, ..DenseUTF8String
-- 
-- # include($BUILDROOT/base/pcre_h.jl)
-- include(string(Base.BUILDROOT, "pcre_h.jl"))
-- 
-- /Source

-- Source: base/pcre.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:32-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- global THREAD_MATCH_CONTEXTS::Vector{Ptr{Cvoid}} = [C_NULL]
-- 
-- global PCRE_COMPILE_LOCK::Threads.SpinLock
-- 
-- /Source

-- Source: base/pcre.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:64-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # supported options for different use cases
-- 
-- # arguments to pcre2_compile
-- /Source

-- Source: base/pcre.jl:98-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # arguments to pcre2_set_newline
-- /Source

-- Source: base/pcre.jl:107-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # arguments to pcre2_set_compile_extra_options
-- /Source

-- Source: base/pcre.jl:116-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # arguments to match
-- /Source

-- Source: base/pcre.jl:131-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Source: base/pcre.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:204-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:218-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:225-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:231-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:244-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:264-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/pcre.jl:283-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end # module
-- /Source


end JuliaLean.base.pcre

/-!
# PCRE2 matching as a primitive

`pcre2_match` (PCRE2 10.46 in Julia 1.13.2, 10.49 on master) is modelled by its
documented behaviour only: a `Pcre` bundles a matching function with the
documented facts about the offsets it returns. Properties of the Julia wrappers
quantify over every `Pcre`; refutations use a concrete instance.

* `interp` is a leftmost-first backtracking interpreter for a small pattern
  fragment (literals, concatenation, alternation, greedy star, empty, capture
  groups) and is proven to satisfy the documented facts.
* `emptyAt` is a primitive that reports empty matches at a fixed list of
  positions; it describes patterns made only of assertions, such as
  `r"(?<!a)(?!a)"`, on one subject.
-/

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-! ## Errors -/

/-- Exceptions thrown by the modelled regex functions: those of the String model
(`BoundsError`, `InexactError`, `StringIndexError`, ...) and `ErrorException`
from `error(msg)` (`base/error.jl:35-44`). -/
inductive RErr where
  | str (e : SErr)
  | errorException (msg : String)
  deriving Repr, DecidableEq, Inhabited

abbrev RJl (α : Type) := Except RErr α

/-- A String-model call inside a regex function. -/
def liftS {α : Type} (x : SJl α) : RJl α := x.mapError .str

/-! ## Match options (`pcre2.h`) -/

/-- `PCRE2_ANCHORED`. -/
def ANCHORED : UInt32 := 0x80000000
/-- `PCRE2_NO_UTF_CHECK`. -/
def NO_UTF_CHECK : UInt32 := 0x40000000
/-- `PCRE2_NOTEMPTY_ATSTART`. -/
def NOTEMPTY_ATSTART : UInt32 := 0x00000008

/-- `opts & bit != 0`. -/
def hasOpt (opts bit : UInt32) : Bool := (opts &&& bit) != 0

/-! ## The primitive -/

/-- The output vector of a successful `pcre2_match`: zero-based code-unit
offsets of the whole match (`start`, `stop`) and one pair per capture group
(`none` is the pair `(PCRE2_UNSET, PCRE2_UNSET)`). The `Csize_t` offsets are
held as integers; the axioms of `Pcre` make them nonnegative. -/
structure Ovec where
  start : Int
  stop : Int
  caps : List (Option (Int × Int))
  deriving Repr, DecidableEq

/-- `pcre2_match(code, subject, length, startoffset, options, ...)` for a fixed
compiled pattern, for `startoffset ≤ length`, returning `none` for
`PCRE2_ERROR_NOMATCH` (and partial matches, which `PCRE.exec` also reports as
no match, `base/pcre.jl:214-216`).

Documented facts (pcre2api, "The string to be matched by pcre2_match()",
"Option bits for pcre2_match()", "How pcre2_match() returns a string and captured
substrings"):
* the match starts at or after `startoffset`, and `start ≤ stop ≤ length`
  (`\K` inside lookarounds, the only way to get `start > stop`, is disabled by
  default since 10.38);
* captured substrings lie within the subject;
* `PCRE2_ANCHORED`: the match is constrained to start at `startoffset`;
* `PCRE2_NOTEMPTY_ATSTART`: an empty string at the start of the subject
  (`startoffset`) is not a valid match.
With `PCRE2_NO_UTF_CHECK` (Julia's default) the start offset is not checked, so
it may point inside a character; `run` is defined for every `startoffset ≤ length`.
Other errors (match limits, out of memory) are not modelled. -/
structure Pcre where
  run : JStr → Nat → UInt32 → Option Ovec
  start_ge : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v → (o : Int) ≤ v.start
  start_le_stop : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v → v.start ≤ v.stop
  stop_le : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    v.stop ≤ (s.bytes.length : Int)
  caps_le : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    ∀ x ∈ v.caps, ∀ a b, x = some (a, b) →
      0 ≤ a ∧ a ≤ (s.bytes.length : Int) ∧ 0 ≤ b ∧ b ≤ (s.bytes.length : Int)
  anchored : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    hasOpt opts ANCHORED = true → v.start = o
  notempty_atstart : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    hasOpt opts NOTEMPTY_ATSTART = true → ¬ (v.start = o ∧ v.stop = o)

/-! ## A backtracking interpreter -/

/-- Pattern fragment. `lit bs` matches the code units `bs` (a character literal
is its UTF-8 bytes); `group k r` is capture group `k + 1`. -/
inductive Re where
  | empty
  | lit (bs : List UInt8)
  | seq (a b : Re)
  | alt (a b : Re)
  | star (a : Re)
  | group (k : Nat) (a : Re)
  deriving Repr, DecidableEq

def Re.size : Re → Nat
  | .empty => 1
  | .lit _ => 1
  | .seq a b => a.size + b.size + 1
  | .alt a b => a.size + b.size + 1
  | .star a => a.size + 1
  | .group _ a => a.size + 1

/-- A pattern with its number of capture groups. -/
structure Pattern where
  re : Re
  ngroups : Nat

abbrev Caps := List (Option (Nat × Nat))

/-- Match the literal `l` at zero-based position `p`; the end position. -/
def litAt (bs : List UInt8) : Nat → List UInt8 → Option Nat
  | p, [] => some p
  | p, b :: rest => if bs[p]? = some b then litAt bs (p + 1) rest else none

/-- Leftmost-first backtracking in continuation-passing style: run `r` at `p`
with captures `c`, calling `k` on each candidate end position in priority order
and returning the first result `k` accepts. Alternation tries the left branch
first; star is greedy, and an iteration that matches the empty string ends the
repetition (as in PCRE). `fuel` bounds the recursion depth. -/
def runRe {β : Type} (bs : List UInt8) : Nat → Re → Nat → Caps → (Nat → Caps → Option β) → Option β
  | 0, _, _, _, _ => none
  | _ + 1, .empty, p, c, k => k p c
  | _ + 1, .lit l, p, c, k =>
    match litAt bs p l with
    | some q => k q c
    | none => none
  | f + 1, .seq a b, p, c, k => runRe bs f a p c (fun q c' => runRe bs f b q c' k)
  | f + 1, .alt a b, p, c, k =>
    match runRe bs f a p c k with
    | some x => some x
    | none => runRe bs f b p c k
  | f + 1, .star a, p, c, k =>
    match runRe bs f a p c (fun q c' => if q = p then k q c' else runRe bs f (.star a) q c' k) with
    | some x => some x
    | none => k p c
  | f + 1, .group i a, p, c, k => runRe bs f a p c (fun q c' => k q (c'.set i (some (p, q))))

/-- Skip continuation bytes starting at `p`. -/
def skipCont (bs : List UInt8) : Nat → Nat → Nat
  | 0, p => p
  | f + 1, p =>
    match bs[p]? with
    | some b => if isCont b then skipCont bs f (p + 1) else p
    | none => p

/-- PCRE2's advance of the start position in UTF mode after a failed attempt at
`p`: one code unit, then past continuation bytes (`ACROSSCHAR`). On a valid
string this is the next character boundary. -/
def advance (bs : List UInt8) (p : Nat) : Nat := skipCont bs bs.length (p + 1)

/-- One anchored attempt at `p` for start offset `o`, honouring
`PCRE2_NOTEMPTY_ATSTART`. -/
def attempt (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) (p : Nat) : Option (Nat × Caps) :=
  runRe s.bytes ((s.bytes.length + 2) * (pat.re.size + 1)) pat.re p (List.replicate pat.ngroups none)
    (fun q c => if hasOpt opts NOTEMPTY_ATSTART && decide (p = o) && decide (q = o) then none
      else some (q, c))

/-- Try start positions `p, advance p, ...` up to the end of the subject (only
`p = o` when anchored); the result is `(start, stop, captures)`. The fuel is
`length + 1 - o`: positions increase. -/
def searchFrom (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) :
    Nat → Nat → Option (Nat × Nat × Caps)
  | 0, _ => none
  | f + 1, p =>
    match attempt s pat o opts p with
    | some (q, c) => some (p, q, c)
    | none =>
      if hasOpt opts ANCHORED || decide (s.bytes.length ≤ p) then none
      else searchFrom s pat o opts f (advance s.bytes p)

def capInt : Option (Nat × Nat) → Option (Int × Int)
  | none => none
  | some (a, b) => some (a, b)

def interpRun (pat : Pattern) (s : JStr) (o : Nat) (opts : UInt32) : Option Ovec :=
  (searchFrom s pat o opts (s.bytes.length + 1 - o) o).map
    (fun t => ⟨t.1, t.2.1, t.2.2.map capInt⟩)

/-! ### The interpreter satisfies the documented facts -/

def CapsOk (n : Nat) (c : Caps) : Prop := ∀ x ∈ c, ∀ a b, x = some (a, b) → a ≤ n ∧ b ≤ n

theorem capsOk_replicate (n k : Nat) : CapsOk n (List.replicate k none) := by
  intro x hx a b h
  rw [List.eq_of_mem_replicate hx] at h; cases h

theorem capsOk_set (n : Nat) (c : Caps) (i a b : Nat) (hc : CapsOk n c) (ha : a ≤ n) (hb : b ≤ n) :
    CapsOk n (c.set i (some (a, b))) := by
  intro x hx a' b' h
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact hc x hx a' b' h
  · subst hx; cases h; exact ⟨ha, hb⟩

theorem litAt_spec (bs : List UInt8) : ∀ (l : List UInt8) (p q : Nat), p ≤ bs.length →
    litAt bs p l = some q → p ≤ q ∧ q ≤ bs.length := by
  intro l
  induction l with
  | nil => intro p q hp h; simp [litAt] at h; omega
  | cons b rest ih =>
    intro p q hp h
    simp only [litAt] at h
    split at h
    · rename_i hb
      have hlt : p < bs.length := by
        rcases Nat.lt_or_ge p bs.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none_iff.mpr h'] at hb; cases hb
      have := ih (p + 1) q (by omega) h
      omega
    · cases h

theorem runRe_spec {β : Type} (bs : List UInt8) : ∀ (f : Nat) (r : Re) (p : Nat) (c : Caps)
    (k : Nat → Caps → Option β) (res : β), p ≤ bs.length → CapsOk bs.length c →
    runRe bs f r p c k = some res →
    ∃ q c', p ≤ q ∧ q ≤ bs.length ∧ CapsOk bs.length c' ∧ k q c' = some res := by
  intro f
  induction f with
  | zero => intro r p c k res _ _ h; simp [runRe] at h
  | succ f ih =>
    intro r p c k res hp hc h
    cases r with
    | empty => exact ⟨p, c, Nat.le_refl p, hp, hc, h⟩
    | lit l =>
      simp only [runRe] at h
      split at h
      · rename_i q hq
        have := litAt_spec bs l p q hp hq
        exact ⟨q, c, this.1, this.2, hc, h⟩
      · cases h
    | seq a b =>
      simp only [runRe] at h
      obtain ⟨q1, c1, h1, h2, h3, h4⟩ := ih a p c _ res hp hc h
      obtain ⟨q2, c2, g1, g2, g3, g4⟩ := ih b q1 c1 k res h2 h3 h4
      exact ⟨q2, c2, by omega, g2, g3, g4⟩
    | alt a b =>
      simp only [runRe] at h
      split at h
      · rename_i x hx
        cases h
        exact ih a p c k _ hp hc hx
      · exact ih b p c k res hp hc h
    | star a =>
      simp only [runRe] at h
      split at h
      · rename_i x hx
        cases h
        obtain ⟨q1, c1, h1, h2, h3, h4⟩ := ih a p c _ _ hp hc hx
        try simp only at h4
        split at h4
        · exact ⟨q1, c1, h1, h2, h3, h4⟩
        · obtain ⟨q2, c2, g1, g2, g3, g4⟩ := ih (.star a) q1 c1 k _ h2 h3 h4
          exact ⟨q2, c2, by omega, g2, g3, g4⟩
      · exact ⟨p, c, Nat.le_refl p, hp, hc, h⟩
    | group i a =>
      simp only [runRe] at h
      obtain ⟨q1, c1, h1, h2, h3, h4⟩ := ih a p c _ res hp hc h
      exact ⟨q1, _, h1, h2, capsOk_set _ c1 i p q1 h3 hp h2, h4⟩

theorem skipCont_spec (bs : List UInt8) : ∀ (f p : Nat), p ≤ bs.length →
    p ≤ skipCont bs f p ∧ skipCont bs f p ≤ bs.length := by
  intro f
  induction f with
  | zero => intro p hp; simp [skipCont]; omega
  | succ f ih =>
    intro p hp
    simp only [skipCont]
    split
    · rename_i b hb
      have hlt : p < bs.length := by
        rcases Nat.lt_or_ge p bs.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none_iff.mpr h'] at hb; cases hb
      split
      · have := ih (p + 1) (by omega); omega
      · omega
    · omega

theorem attempt_spec (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) (p q : Nat) (c : Caps)
    (hp : p ≤ s.bytes.length) (h : attempt s pat o opts p = some (q, c)) :
    p ≤ q ∧ q ≤ s.bytes.length ∧ CapsOk s.bytes.length c ∧
      ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ p = o ∧ q = o) := by
  unfold attempt at h
  obtain ⟨q', c', h1, h2, h3, h4⟩ :=
    runRe_spec s.bytes _ pat.re p _ _ _ hp (capsOk_replicate _ _) h
  try simp only at h4
  split at h4
  · cases h4
  · rename_i hne
    cases h4
    refine ⟨h1, h2, h3, fun ⟨a, b, d⟩ => hne ?_⟩
    simp [a, b, d]

/-- Every result of `searchFrom` started at a position `p` with `o ≤ p ≤ length`
(and `p = o` when anchored). -/
theorem searchFrom_spec (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) :
    ∀ (f p p' q : Nat) (c : Caps), o ≤ p → p ≤ s.bytes.length →
      (hasOpt opts ANCHORED = true → p = o) → searchFrom s pat o opts f p = some (p', q, c) →
      o ≤ p' ∧ p' ≤ q ∧ q ≤ s.bytes.length ∧ CapsOk s.bytes.length c ∧
        (hasOpt opts ANCHORED = true → p' = o) ∧
        ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ p' = o ∧ q = o) := by
  intro f
  induction f with
  | zero => intro p p' q c _ _ _ h; simp [searchFrom] at h
  | succ f ih =>
    intro p p' q c h1 h2 ha h
    simp only [searchFrom] at h
    split at h
    · rename_i q' c' hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have := attempt_spec s pat o opts p q' c' h2 hq
      exact ⟨h1, this.1, this.2.1, this.2.2.1, ha, this.2.2.2⟩
    · split at h
      · cases h
      · rename_i hn
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hn
        have hs := skipCont_spec s.bytes s.bytes.length (p + 1) (by omega)
        exact ih _ p' q c (by unfold advance; omega) (by unfold advance; omega)
          (fun h' => absurd h' hn.1) h

theorem interpRun_spec (pat : Pattern) (s : JStr) (o : Nat) (opts : UInt32) (v : Ovec)
    (ho : o ≤ s.bytes.length) (h : interpRun pat s o opts = some v) :
    (o : Int) ≤ v.start ∧ v.start ≤ v.stop ∧ v.stop ≤ (s.bytes.length : Int) ∧
      (∀ x ∈ v.caps, ∀ a b, x = some (a, b) →
        0 ≤ a ∧ a ≤ (s.bytes.length : Int) ∧ 0 ≤ b ∧ b ≤ (s.bytes.length : Int)) ∧
      (hasOpt opts ANCHORED = true → v.start = o) ∧
      ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ v.start = o ∧ v.stop = o) := by
  unfold interpRun at h
  cases hs : searchFrom s pat o opts (s.bytes.length + 1 - o) o with
  | none => rw [hs] at h; cases h
  | some t =>
    rw [hs] at h
    obtain ⟨p, q, c⟩ := t
    simp only [Option.map, Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      searchFrom_spec s pat o opts _ o p q c (Nat.le_refl o) ho (fun _ => rfl) hs
    refine ⟨by simp only; omega, by simp only; omega, by simp only; omega, ?_,
      fun ha => by simp only; rw [h5 ha], fun ⟨a, b, d⟩ => h6 ⟨a, ?_, ?_⟩⟩
    · intro x hx a b hx'
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      cases y with
      | none => simp [capInt] at hx'
      | some ab =>
        obtain ⟨a', b'⟩ := ab
        simp only [capInt, Option.some.injEq, Prod.mk.injEq] at hx'
        obtain ⟨rfl, rfl⟩ := hx'
        have := h4 _ hy a' b' rfl
        omega
    · simp only at b; omega
    · simp only at d; omega

/-- The interpreter as a `Pcre` primitive. -/
def interp (pat : Pattern) : Pcre where
  run := interpRun pat
  start_ge s o opts v ho h := (interpRun_spec pat s o opts v ho h).1
  start_le_stop s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.1
  stop_le s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.2.1
  caps_le s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.2.2.1
  anchored s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.2.2.2.1
  notempty_atstart s o opts v ho h ha := fun h' =>
    (interpRun_spec pat s o opts v ho h).2.2.2.2.2 ⟨ha, h'⟩

/-! ## A primitive given by its empty matches -/

/-- The leftmost position of `ps` (listed in increasing order) that is an
admissible empty match for start offset `o`. -/
def emptyAtRun (ps : List Nat) (s : JStr) (o : Nat) (opts : UInt32) : Option Ovec :=
  match ps.find? (fun p => decide (o ≤ p) && decide (p ≤ s.bytes.length) &&
      !(hasOpt opts NOTEMPTY_ATSTART && decide (p = o)) &&
      (!hasOpt opts ANCHORED || decide (p = o))) with
  | some p => some ⟨p, p, []⟩
  | none => none

theorem emptyAtRun_spec (ps : List Nat) (s : JStr) (o : Nat) (opts : UInt32) (v : Ovec)
    (h : emptyAtRun ps s o opts = some v) :
    (o : Int) ≤ v.start ∧ v.start = v.stop ∧ v.stop ≤ (s.bytes.length : Int) ∧ v.caps = [] ∧
      (hasOpt opts ANCHORED = true → v.start = o) ∧
      ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ v.start = o ∧ v.stop = o) := by
  unfold emptyAtRun at h
  split at h
  · rename_i p hp
    cases h
    have hc := List.find?_some hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    refine ⟨by simp only; omega, rfl, by simp only; omega, rfl, fun ha => ?_,
      fun ⟨hn, hpo, _⟩ => ?_⟩
    · rcases h4 with h4 | h4
      · rw [ha] at h4; cases h4
      · simp only; rw [h4]
    · rcases h3 with h3 | h3
      · rw [hn] at h3; cases h3
      · simp only at hpo; exact h3 (by omega)
  · cases h

/-- A primitive reporting the empty matches of an assertion-only pattern at the
zero-based positions `ps` (in increasing order). -/
def emptyAt (ps : List Nat) : Pcre where
  run := emptyAtRun ps
  start_ge s o opts v _ h := (emptyAtRun_spec ps s o opts v h).1
  start_le_stop s o opts v _ h := Int.le_of_eq (emptyAtRun_spec ps s o opts v h).2.1
  stop_le s o opts v _ h := (emptyAtRun_spec ps s o opts v h).2.2.1
  caps_le s o opts v _ h := by
    rw [(emptyAtRun_spec ps s o opts v h).2.2.2.1]; intro x hx; cases hx
  anchored s o opts v _ h := (emptyAtRun_spec ps s o opts v h).2.2.2.2.1
  notempty_atstart s o opts v _ h ha := fun h' =>
    (emptyAtRun_spec ps s o opts v h).2.2.2.2.2 ⟨ha, h'⟩

end JuliaLean.RegexUnicode.Core

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- `PCRE.exec(re, subject, offset, options, match_data)`, `base/pcre.jl:205-217`,
with the implicit `Csize_t` conversion of `offset` in the `ccall` (`InexactError`
for a negative offset) and `pcre2_match`'s `PCRE2_ERROR_BADOFFSET` for
`offset > length`, reported by `error("PCRE.exec error: $(err_message(rc))")`. -/
def exec (P : Pcre) (s : JStr) (offset : JInt64) (opts : UInt32) : RJl (Option Ovec) :=
  match JInt.convert (IntTy.u64.name) .u64 offset.val with
  | .error e => .error (.str (.jl e))
  | .ok off =>
    if off.val > (s.bytes.length : Int) then .error (.errorException "PCRE.exec error: bad offset value")
    else .ok (P.run s off.val.toNat opts)

end JuliaLean.RegexUnicode.Core

/-!
# Regex pattern builders and a PCRE2 pattern lexer

* `^(r::Regex, i::Integer)`, `base/regex.jl:929`, and `*(r1, rs...)` with `wrap_string`,
  `base/regex.jl:856-882`, as string builders over `Regex` values (master `bbfa0ce4150`).
* A lexer for the part of PCRE2 pattern syntax these builders rely on (`pcre2pattern(3)`):
  - `\Q...\E` quoting ("Quoting"): inside, only `\E` is special; an isolated `\E` is
    ignored.
  - `PCRE2_EXTENDED` (`x`): white space is ignored and `#` starts a comment that runs to
    the next newline (Julia builds PCRE2 with the default newline, LF); neither applies
    inside `\Q...\E`.
  - `(?:`, `(?imsx-imsx:`, `(?imsx-imsx)` (option changes last to the end of the
    enclosing group), capturing, named and lookaround groups; parentheses must balance
    ("missing closing parenthesis", "unmatched closing parenthesis").
  - `{` starts a repetition quantifier `{n}`, `{n,}`, `{n,m}` only when followed by that
    syntax with decimal digits ("Repetition"); otherwise it is a literal `{`. Counts
    above 65535 are a compile error.
  Constructs outside this fragment (character classes, `\x`-style escapes, verbs,
  quantifier forms that differ between PCRE2 versions, a quantifier after an item that
  cannot be repeated) give `LexErr.unsupported`, which is never treated as a PCRE2
  compile error.
* The PCRE2 name table behind `keys(::RegexMatch)` and `haskey(::RegexMatch, name)`,
  `base/regex.jl:238-286`, `PCRE.capture_names` (`base/pcre.jl:265-282`).
-/

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## PCRE2 match data -/

/-- The ovector of a match: for each group `0..top`, its 0-based byte range `[start, end)`,
or `none` (`PCRE2_UNSET`) when the group did not participate. -/
abbrev Ovec := List (Option (Nat × Nat))

/-- `PCRE.substring_length_bynumber(match_data, number)`, `base/pcre.jl:245-254`. The
`Cint` argument converts the `Int` (`InexactError` outside `Int32`); PCRE2 reads it as a
`uint32_t`. `PCRE2_ERROR_UNSET` gives 0; other errors throw
`ErrorException("PCRE error: ...")`. -/
def substringLengthBynumber (md : Ovec) (g : I) : Except IOErr I :=
  if g.val < -2 ^ 31 ∨ 2 ^ 31 ≤ g.val then .error (.jl (.inexactError "Int32"))
  else
    let n : Int := if g.val < 0 then g.val + 2 ^ 32 else g.val
    if (md.length : Int) ≤ n then .error (.errorException "PCRE error: unknown substring")
    else match md.getD n.toNat none with
      | none => .ok (i 0)
      | some (a, b) => .ok (i (b - a : Nat))

/-- `PCRE.substring_copy_bynumber(match_data, number, buf, buf_size)`,
`base/pcre.jl:256-263`: the bytes PCRE2 stores at `buf` (the group and a NUL). The
`UInt32` argument converts the `Int`. -/
def substringCopyBynumber (md : Ovec) (subj : List UInt8) (g : I) (bufSize : I) :
    Except IOErr (List UInt8) :=
  if g.val < 0 ∨ 2 ^ 32 ≤ g.val then .error (.jl (.inexactError "UInt32"))
  else if (md.length : Int) ≤ g.val then .error (.errorException "PCRE error: unknown substring")
  else match md.getD g.val.toNat none with
    | none => .error (.errorException "PCRE error: requested value is not set")
    | some (a, b) =>
      if bufSize.val ≤ (b - a : Nat) then .error (.errorException "PCRE error: no more memory")
      else .ok ((subj.drop a).take (b - a) ++ [0])

/-- A PCRE2 name table: `(group number, name)` entries. -/
abbrev NameTable := List (Nat × List UInt8)

/-- `pcre2_substring_number_from_name`: the number of the unique group called `name`,
`PCRE2_ERROR_NOSUBSTRING` (-49) if none, `PCRE2_ERROR_NOUNIQUESUBSTRING` (-50) if several. -/
def numberFromName (tbl : NameTable) (name : List UInt8) : Int :=
  match tbl.filter (fun e => e.2 == name) with
  | [] => -49
  | [e] => e.1
  | _ => -50

/-- `PCRE.substring_number_from_name(re, name)`, `base/pcre.jl:239-243`: the `Cstring`
conversion rejects an embedded NUL. -/
def substringNumberFromName (tbl : NameTable) (name : List UInt8) : Except IOErr I :=
  if name.contains 0 then .error (.jl (.argumentError "embedded NULs are not allowed in C strings"))
  else .ok (i (numberFromName tbl name))


/-! ## PCRE2 matching for a pattern fragment -/

/-- Regex fragment: a byte, concatenation, alternation, greedy `+`, numbered capture group. -/
inductive Pat where
  | lit (b : UInt8)
  | seq (a b : Pat)
  | alt (a b : Pat)
  | plus (a : Pat)
  | grp (n : Nat) (a : Pat)
  deriving DecidableEq, Repr

/-- Highest capture group number (`PCRE2_INFO_CAPTURECOUNT`). -/
def Pat.top : Pat → Nat
  | .lit _ => 0
  | .seq a b | .alt a b => max a.top b.top
  | .plus a => a.top
  | .grp n a => max n a.top

def Pat.size : Pat → Nat
  | .lit _ => 1
  | .seq a b | .alt a b => a.size + b.size + 1
  | .plus a | .grp _ a => a.size + 1

/-- Backtracking matcher in continuation-passing style: match `p` at byte `pos` with
captures `ov`, then run the continuation `k`. Alternatives are tried left to right, `+`
is greedy and stops on an empty iteration. -/
def mt (s : List UInt8) : Nat → Pat → Nat → Ovec → (Nat → Ovec → Option Ovec) → Option Ovec
  | 0, _, _, _, _ => none
  | _ + 1, .lit b, pos, ov, k => if pos < s.length ∧ s.getD pos 0 = b then k (pos + 1) ov else none
  | f + 1, .seq a b, pos, ov, k => mt s f a pos ov (fun q ov' => mt s f b q ov' k)
  | f + 1, .alt a b, pos, ov, k =>
    match mt s f a pos ov k with
    | some r => some r
    | none => mt s f b pos ov k
  | f + 1, .grp n a, pos, ov, k => mt s f a pos ov (fun q ov' => k q (ov'.set n (some (pos, q))))
  | f + 1, .plus a, pos, ov, k =>
    mt s f a pos ov (fun q ov' =>
      match (if pos < q then mt s f (.plus a) q ov' k else none) with
      | some r => some r
      | none => k q ov')

/-- Leftmost match starting at a byte offset `≥ st`. -/
def execFrom (p : Pat) (s : List UInt8) (fuel : Nat) : Nat → Nat → Option Ovec
  | 0, _ => none
  | n + 1, st =>
    if s.length < st then none
    else
      match mt s fuel p st (List.replicate (p.top + 1) none)
          (fun q ov => some (ov.set 0 (some (st, q)))) with
      | some ov => some ov
      | none => execFrom p s fuel n (st + 1)

/-- `pcre2_match(re, subject, length, offset, NO_UTF_CHECK, match_data)` for a fragment
pattern: the ovector of the leftmost match at or after `offset`. -/
def exec (p : Pat) (s : List UInt8) (offset : Nat) : Option Ovec :=
  execFrom p s ((s.length + 2) * (p.size + 2)) (s.length + 1) offset

end JuliaLean.RegexUnicode.Subst

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

open JuliaLean JuliaLean.IOBuffers

/-! ## Lexer -/

/-- A pattern token. -/
inductive Tok where
  /-- A literal character. -/
  | lit (c : Char)
  /-- A backslash escape such as `\d` or `\.`. -/
  | esc (c : Char)
  /-- `.`, `^`, `$`, `|`, or a lazy/possessive suffix `?`/`+` after a quantifier. -/
  | sym (c : Char)
  /-- `(`: capturing, named or lookaround group. -/
  | openG
  /-- `(?:` or `(?imsx-imsx:`. -/
  | openNC
  | close
  /-- A repetition quantifier `{lo,hi}` (`*`, `+`, `?` included). -/
  | quant (lo : Nat) (hi : Option Nat)
  deriving DecidableEq, Repr

/-- Pattern compile errors of the fragment. -/
inductive LexErr where
  | missingClose
  | unmatchedClose
  | trailingBackslash
  | quantTooBig
  | quantOrder
  /-- Outside the modelled fragment. -/
  | unsupported
  deriving DecidableEq, Repr

def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- White space ignored under `PCRE2_EXTENDED` in UTF mode (Pattern_White_Space). -/
def isXSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\x0b' || c = '\x0c' || c = '\r' ||
  c = '\u0085' || c = '\u200e' || c = '\u200f' || c = '\u2028' || c = '\u2029'

/-- Escapes whose argument syntax is not modelled (`\x{..}`, `\p{..}`, `\g{..}`,
back references and octal digits, ...). -/
def unsupportedEsc (c : Char) : Bool := isDigitC c || "xoNpPgkcuU".toList.contains c

/-- Escapes that are assertions (cannot be repeated). -/
def assertionEsc (c : Char) : Bool := "bBAzZGK".toList.contains c

/-- The rest of an `x`-mode comment: everything after the next newline. -/
def skipComment (t : List Char) : List Char := (t.dropWhile (· ≠ '\n')).drop 1

def digitsNat (ds : List Char) : Nat := ds.foldl (fun acc d => 10 * acc + (d.toNat - 48)) 0

/-- Result of reading a `{`. -/
inductive QRes where
  | quant (lo : Nat) (hi : Option Nat) (rest : List Char)
  | literal
  | unsupported

/-- Quantifier syntax after `{`. Text up to the next `}` made only of digits, commas and
spaces that is not `n`, `n,` or `n,m` is a quantifier in some PCRE2 versions only
(`{,m}`, spaces), so it is `unsupported`; anything else makes `{` literal. -/
def parseQuant (t : List Char) : QRes :=
  let d1 := t.takeWhile isDigitC
  let r1 := t.dropWhile isDigitC
  let fallback : QRes :=
    let inner := t.takeWhile (· ≠ '}')
    if (t.dropWhile (· ≠ '}')).isEmpty then .literal
    else if inner.all (fun c => isDigitC c || c = ',' || c = ' ') then .unsupported
    else .literal
  if d1.isEmpty then fallback
  else
    match r1 with
    | '}' :: r => .quant (digitsNat d1) (some (digitsNat d1)) r
    | ',' :: '}' :: r => .quant (digitsNat d1) none r
    | ',' :: r2 =>
      let d2 := r2.takeWhile isDigitC
      match r2.dropWhile isDigitC with
      | '}' :: r => if d2.isEmpty then fallback else .quant (digitsNat d1) (some (digitsNat d2)) r
      | _ => fallback
    | _ => fallback

/-- Whether the last token can take a quantifier. -/
def repeatable : List Tok → Bool
  | .lit _ :: _ | .close :: _ | .sym '.' :: _ => true
  | .esc c :: _ => !assertionEsc c
  | _ => false

def afterQuant : List Tok → Bool
  | .quant _ _ :: _ => true
  | _ => false

/-- Option letters `[imsx]*(-[imsx]*)?` after `(?`: the new `x` setting and the rest. -/
def optLetters (ext : Bool) : Bool → List Char → Option (Bool × List Char)
  | _, [] => none
  | neg, c :: t =>
    if c = 'x' then optLetters (!neg) neg t
    else if c = 'i' ∨ c = 'm' ∨ c = 's' then optLetters ext neg t
    else if c = '-' ∧ !neg then optLetters ext true t
    else if c = ':' ∨ c = ')' then some (ext, c :: t)
    else none

def isNameChar (c : Char) : Bool := c.isAlphanum || c = '_'

/-- What follows `(`: the group token (`none` for an option setting `(?x)`), the `x`
setting inside, and the rest. -/
def openGroup (ext : Bool) (t : List Char) : Except LexErr (Option Tok × Bool × List Char) :=
  match t with
  | '?' :: ':' :: r => .ok (some .openNC, ext, r)
  | '?' :: '=' :: r | '?' :: '!' :: r | '?' :: '<' :: '=' :: r | '?' :: '<' :: '!' :: r =>
    .ok (some .openG, ext, r)
  | '?' :: '<' :: r | '?' :: 'P' :: '<' :: r =>
    let name := r.takeWhile isNameChar
    match r.dropWhile isNameChar with
    | '>' :: r' => if name.isEmpty then .error .unsupported else .ok (some .openG, ext, r')
    | _ => .error .unsupported
  | '?' :: r =>
    match optLetters ext false r with
    | some (ext', ':' :: r') => .ok (some .openNC, ext', r')
    | some (ext', ')' :: r') => .ok (none, ext', r')
    | _ => .error .unsupported
  | '*' :: _ => .error .unsupported
  | r => .ok (some .openG, ext, r)

/-- A quantifier token after checking PCRE2's limits. -/
def quantTok (lo : Nat) (hi : Option Nat) : Except LexErr Tok :=
  if 65535 < lo then .error .quantTooBig
  else match hi with
    | some h => if 65535 < h then .error .quantTooBig else if h < lo then .error .quantOrder
      else .ok (.quant lo hi)
    | none => .ok (.quant lo hi)

/-- The lexer: remaining text, inside `\Q...\E`, `x` setting, the `x` settings to restore
at each enclosing `)`, tokens so far (reversed). -/
def lexAux : Nat → List Char → Bool → Bool → List Bool → List Tok → Except LexErr (List Tok)
  | 0, _, _, _, _, _ => .error .unsupported
  | _ + 1, [], _, _, stk, acc => if stk.isEmpty then .ok acc.reverse else .error .missingClose
  | f + 1, c :: t, true, ext, stk, acc =>
    if c = '\\' ∧ t.head? = some 'E' then lexAux f t.tail false ext stk acc
    else lexAux f t true ext stk (.lit c :: acc)
  | f + 1, c :: t, false, ext, stk, acc =>
    if c = '\\' then
      match t with
      | [] => .error .trailingBackslash
      | d :: t' =>
        if d = 'Q' then lexAux f t' true ext stk acc
        else if d = 'E' then lexAux f t' false ext stk acc
        else if unsupportedEsc d then .error .unsupported
        else lexAux f t' false ext stk (.esc d :: acc)
    else if ext ∧ isXSpace c then lexAux f t false ext stk acc
    else if ext ∧ c = '#' then lexAux f (skipComment t) false ext stk acc
    else if c = '(' then
      match openGroup ext t with
      | .error e => .error e
      | .ok (some tok, ext', t') => lexAux f t' false ext' (ext :: stk) (tok :: acc)
      | .ok (none, ext', t') => lexAux f t' false ext' stk acc
    else if c = ')' then
      match stk with
      | [] => .error .unmatchedClose
      | e :: stk' => lexAux f t false e stk' (.close :: acc)
    else if c = '[' then .error .unsupported
    else if c = '{' then
      match parseQuant t with
      | .literal => lexAux f t false ext stk (.lit '{' :: acc)
      | .unsupported => .error .unsupported
      | .quant lo hi t' =>
        if repeatable acc then
          match quantTok lo hi with
          | .ok tok => lexAux f t' false ext stk (tok :: acc)
          | .error e => .error e
        else .error .unsupported
    else if c = '*' ∨ c = '+' ∨ c = '?' then
      if repeatable acc then
        lexAux f t false ext stk
          (.quant (if c = '+' then 1 else 0) (if c = '?' then some 1 else none) :: acc)
      else if afterQuant acc ∧ (c = '?' ∨ c = '+') then lexAux f t false ext stk (.sym c :: acc)
      else .error .unsupported
    else if c = '.' ∨ c = '^' ∨ c = '$' ∨ c = '|' then lexAux f t false ext stk (.sym c :: acc)
    else lexAux f t false ext stk (.lit c :: acc)

/-- Lex a pattern compiled with or without `PCRE2_EXTENDED`. -/
def lex (p : List Char) (ext : Bool) : Except LexErr (List Tok) :=
  lexAux (p.length + 1) p false ext [] []
/-- `PCRE.capture_names(re)`, `base/pcre.jl:265-282`: a `Dict` from group number to name
filled from the name table in order. -/
def captureName (tbl : NameTable) (idx : Nat) : Option (List UInt8) :=
  tbl.foldl (fun acc e => if e.1 = idx then some e.2 else acc) none

end JuliaLean.RegexUnicode.Subst

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
open JuliaLean.RegexUnicode.Core (Pcre Ovec RErr RJl)

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
  match JInt.convert (IntTy.u64.name) .u64 offset.val with
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

end JuliaLean.StringsCovB.Rx
