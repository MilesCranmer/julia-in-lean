import JuliaLean.Registry.Types
import JuliaLean.Core
import JuliaLean.base.io

/-!
# Model of `base/env.jl`

Typed source models of `base/env.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a
64-bit platform (`Int === Int64`). OS calls, wide-string conversion, pointer access, string indexing,
dictionary iteration, and stringification are explicit interfaces; methods preserve Julia's branch
order, errors, mutation, and cleanup behavior.
-/

namespace JuliaLean.base.env

open JuliaLean

abbrev U32 := JInt .u32
abbrev I32 := JInt .i32
abbrev I64 := JInt .i64
abbrev U64 := JInt .u64
abbrev U16 := JInt .u16
abbrev EnvAction (World : Type) (A : Type) := JuliaLean.base.io.M World A

structure EnvStringOps where
  isEmpty : String → Bool
  firstIndex : String → Nat
  nextIndex : String → Nat → Nat
  prevIndex : String → Nat → Nat
  lastIndex : String → Nat
  findFirstEquals : String → Option Nat
  findNextEquals : String → Nat → Option Nat
  slice : String → Nat → Nat → String

abbrev EnvAccess (World Key : Type) :=
  {R : Type} → (String → R) → (Key → EnvAction World R) → Key → EnvAction World R

-- Source: base/env.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- if Sys.iswindows()
--     const ERROR_ENVVAR_NOT_FOUND = UInt32(203)
-- /Source

private def winErrorEnvVarNotFound : U32 := JInt.lit .u32 203

-- Source: base/env.jl:6-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     const env_dict = Lockable(Dict{String, Vector{Cwchar_t}}())
-- 
-- /Source
structure WindowsEnvOps (World Cache Key WString WBuffer : Type) where
  cache : Cache
  withCacheLock : {A : Type} → Cache → (Unit → EnvAction World A) → EnvAction World A
  cacheGet : Cache → Key → EnvAction World (Option WString)
  cacheSet : Cache → Key → WString → EnvAction World Unit
  toWideKey : Key → EnvAction World WString
  toWideValue : {Value : Type} → Value → EnvAction World WString
  getVariableLength : WString → EnvAction World U32
  getLastError : EnvAction World U32
  allocateWide : U32 → EnvAction World WBuffer
  getVariable : WString → WBuffer → U32 → EnvAction World U32
  lastWideChar : WBuffer → EnvAction World U16
  popWideNul : WBuffer → EnvAction World (List U16)
  transcodeWide : List U16 → EnvAction World String
  windowsError : String → Bool → EnvAction World Unit
  setVariable : WString → Option WString → EnvAction World I32


/--
Julia source: base/env.jl:8-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function memoized_env_lookup(str::AbstractString)
        # Windows environment variables have a different format from Linux / MacOS, and previously
        # incurred allocations because we had to convert a String to a Vector{Cwchar_t} each time
        # an environment variable was looked up. This function memoizes that lookup process, storing
        # the String => Vector{Cwchar_t} pairs in env_dict
        @lock env_dict begin
            var = get(env_dict[], str, nothing)
            if isnothing(var)
                var = cwstring(str)
                env_dict[][str] = var
            end
            return var
        end
    end
```
-/
def memoizedEnvLookup {World Cache Key WString WBuffer : Type}
    (ops : WindowsEnvOps World Cache Key WString WBuffer) (key : Key) : EnvAction World WString :=
  ops.withCacheLock ops.cache (fun _ => do
    match ← ops.cacheGet ops.cache key with
    | some value => pure value
    | none => do
      let value ← ops.toWideKey key
      ops.cacheSet ops.cache key value
      pure value)

/--
Julia source: base/env.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _getenvlen(var::Vector{UInt16}) = ccall(:GetEnvironmentVariableW,stdcall,UInt32,(Ptr{UInt16},Ptr{UInt16},UInt32),var,C_NULL,0)
```
-/
def getenvLengthWindows {World Cache Key WString WBuffer : Type}
    (ops : WindowsEnvOps World Cache Key WString WBuffer) (name : WString) :
    EnvAction World U32 :=
  ops.getVariableLength name

/--
Julia source: base/env.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _hasenv(s::Vector{UInt16}) = _getenvlen(s) != 0 || Libc.GetLastError() != ERROR_ENVVAR_NOT_FOUND
```
-/
def hasEnvWide {World Cache Key WString WBuffer : Type}
    (ops : WindowsEnvOps World Cache Key WString WBuffer) (name : WString) :
    EnvAction World Bool := do
  let length ← getenvLengthWindows ops name
  if length.val != 0 then pure true
  else
    let error ← ops.getLastError
    pure (error != winErrorEnvVarNotFound)

/--
Julia source: base/env.jl:25-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _hasenv(s::AbstractString) = _hasenv(memoized_env_lookup(s))
```
-/
def hasEnvWindows {World Cache Key WString WBuffer : Type}
    (ops : WindowsEnvOps World Cache Key WString WBuffer) (name : Key) :
    EnvAction World Bool := do
  let wideName ← memoizedEnvLookup ops name
  hasEnvWide ops wideName

/--
Julia source: base/env.jl:27-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function access_env(onError::Function, str::AbstractString)
        var = memoized_env_lookup(str)
        len = _getenvlen(var)
        if len == 0
            return Libc.GetLastError() != ERROR_ENVVAR_NOT_FOUND ? "" : onError(str)
        end
        val = zeros(UInt16,len)
        ret = ccall(:GetEnvironmentVariableW,stdcall,UInt32,(Ptr{UInt16},Ptr{UInt16},UInt32),var,val,len)
        windowserror(:getenv, (ret == 0 && len != 1) || ret != len-1 || val[end] != 0)
        pop!(val) # NUL
        return transcode(String, val)
    end
```
-/
def accessEnvWindows {World Cache Key WString WBuffer R : Type}
    (ops : WindowsEnvOps World Cache Key WString WBuffer)
    (fromString : String → R) (onError : Key → EnvAction World R) (name : Key) :
    EnvAction World R := do
  let wideName ← memoizedEnvLookup ops name
  let length ← getenvLengthWindows ops wideName
  if length.val == 0 then
    let error ← ops.getLastError
    if error != winErrorEnvVarNotFound then pure (fromString "") else onError name
  else do
    let value ← ops.allocateWide length
    let result ← ops.getVariable wideName value length
    let invalid ← if result.val == 0 && length.val != 1 then pure true
      else if result != length - JInt.lit .u32 1 then pure true
      else do
        let lastChar ← ops.lastWideChar value
        pure (lastChar.val != 0)
    ops.windowsError "getenv" invalid
    let chars ← ops.popWideNul value
    let string ← ops.transcodeWide chars
    pure (fromString string)

/--
Julia source: base/env.jl:40-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _setenv(svar::AbstractString, sval::AbstractString, overwrite::Bool=true)
        var = memoized_env_lookup(svar)
        val = cwstring(sval)
        if overwrite || !_hasenv(var)
            ret = ccall(:SetEnvironmentVariableW,stdcall,Int32,(Ptr{UInt16},Ptr{UInt16}),var,val)
            windowserror(:setenv, ret == 0)
        end
    end
```
-/
def setEnvWindows {World Cache Key WString WBuffer Value : Type}
    (ops : WindowsEnvOps World Cache Key WString WBuffer)
    (name : Key) (value : Value) (overwrite : Bool := true) : EnvAction World Unit := do
  let wideName ← memoizedEnvLookup ops name
  let wideValue ← ops.toWideValue value
  if overwrite || !(← hasEnvWide ops wideName) then
    let result ← ops.setVariable wideName (some wideValue)
    ops.windowsError "setenv" (result.val == 0)

/--
Julia source: base/env.jl:49-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _unsetenv(svar::AbstractString)
        var = memoized_env_lookup(svar)
        ret = ccall(:SetEnvironmentVariableW,stdcall,Int32,(Ptr{UInt16},Ptr{UInt16}),var,C_NULL)
        windowserror(:setenv, ret == 0 && Libc.GetLastError() != ERROR_ENVVAR_NOT_FOUND)
    end
```
-/
def unsetEnvWindows {World Cache Key WString WBuffer : Type}
    (ops : WindowsEnvOps World Cache Key WString WBuffer) (name : Key) :
    EnvAction World Unit := do
  let wideName ← memoizedEnvLookup ops name
  let result ← ops.setVariable wideName none
  let invalid ← if result.val == 0 then do
    let error ← ops.getLastError
    pure (error != winErrorEnvVarNotFound)
  else pure false
  ops.windowsError "setenv" invalid

structure PosixEnvOps (World Key Ptr : Type) where
  getenv : Key → EnvAction World Ptr
  isNull : Ptr → Bool
  unsafeString : Ptr → EnvAction World String
  setenv : {Value : Type} → Key → Value → I32 → EnvAction World I32
  unsetenv : Key → EnvAction World I32
  systemError : String → Bool → EnvAction World Unit

/--
Julia source: base/env.jl:54-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
else # !windows
    _getenv(var::AbstractString) = ccall(:getenv, Cstring, (Cstring,), var)
```
-/
def getenvPosix {World Key Ptr : Type} (ops : PosixEnvOps World Key Ptr)
    (name : Key) : EnvAction World Ptr :=
  ops.getenv name

/--
Julia source: base/env.jl:56-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    _hasenv(s::AbstractString) = _getenv(s) != C_NULL

```
-/
def hasEnvPosix {World Key Ptr : Type} (ops : PosixEnvOps World Key Ptr)
    (name : Key) : EnvAction World Bool := do
  let value ← getenvPosix ops name
  pure (!ops.isNull value)

structure PosixEnvironOps (World Ptr Environ : Type) where
  isApple : Bool
  nsGetEnviron : EnvAction World Ptr
  resolveEnvironSymbolOnce : EnvAction World Ptr
  unsafeLoad : Ptr → EnvAction World Environ

/--
Julia source: base/env.jl:58-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    if Sys.isapple()
        _environ() = unsafe_load(ccall(:_NSGetEnviron, Ptr{Ptr{Cstring}}, ()))
```
-/
def environApple {World Ptr Environ : Type} (ops : PosixEnvironOps World Ptr Environ) :
    EnvAction World Environ := do
  let pointer ← ops.nsGetEnviron
  ops.unsafeLoad pointer

/--
Julia source: base/env.jl:60-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    else
        const _environ_ptr = Base.OncePerProcess{Ptr{Ptr{Cstring}}}() do
            # Look up `environ` in the main executable, since if Julia is loaded
            # via RTLD_DEEPBIND this may resolve to NULL in our own namespace.
            # (see https://gcc.gnu.org/bugzilla/show_bug.cgi?id=111413)
            executable_handle = ccall(:jl_dlopen, Ptr{Cvoid}, (Ptr{Cchar}, Cint),
                C_NULL, Libc.Libdl.RTLD_LAZY)
            return Ptr{Ptr{Cstring}}(Libc.Libdl.dlsym(executable_handle, :environ))
        end

        _environ() = unsafe_load(_environ_ptr())
    end
```
-/
def environOther {World Ptr Environ : Type} (ops : PosixEnvironOps World Ptr Environ) :
    EnvAction World Environ := do
  let pointer ← ops.resolveEnvironSymbolOnce
  ops.unsafeLoad pointer

def environPosix {World Ptr Environ : Type} (ops : PosixEnvironOps World Ptr Environ) :
    EnvAction World Environ :=
  if ops.isApple then environApple ops else environOther ops

/--
Julia source: base/env.jl:73-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function access_env(onError::Function, var::AbstractString)
        val = _getenv(var)
        val == C_NULL ? onError(var) : unsafe_string(val)
    end
```
-/
def accessEnvPosix {World Key Ptr R : Type} (ops : PosixEnvOps World Key Ptr)
    (fromString : String → R) (onError : Key → EnvAction World R) (name : Key) :
    EnvAction World R := do
  let value ← getenvPosix ops name
  if ops.isNull value then onError name
  else fromString <$> ops.unsafeString value

/--
Julia source: base/env.jl:78-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _setenv(var::AbstractString, val::AbstractString, overwrite::Bool=true)
        ret = ccall(:setenv, Int32, (Cstring,Cstring,Int32), var, val, overwrite)
        systemerror(:setenv, ret != 0)
    end
```
-/
def setEnvPosix {World Key Ptr Value : Type} (ops : PosixEnvOps World Key Ptr)
    (name : Key) (value : Value) (overwrite : Bool := true) : EnvAction World Unit := do
  let overwriteValue := if overwrite then JInt.lit .i32 1 else JInt.lit .i32 0
  let result ← ops.setenv name value overwriteValue
  ops.systemError "setenv" (result.val != 0)

/--
Julia source: base/env.jl:83-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _unsetenv(var::AbstractString)
        ret = ccall(:unsetenv, Int32, (Cstring,), var)
        systemerror(:unsetenv, ret != 0)
    end
end # os test
```
-/
def unsetEnvPosix {World Key Ptr : Type} (ops : PosixEnvOps World Key Ptr)
    (name : Key) : EnvAction World Unit := do
  let result ← ops.unsetenv name
  ops.systemError "unsetenv" (result.val != 0)

def accessEnv {World Cache Key WString WBuffer Ptr R : Type}
    (windows : Bool) (windowsOps : WindowsEnvOps World Cache Key WString WBuffer)
    (posixOps : PosixEnvOps World Key Ptr) (fromString : String → R)
    (onError : Key → EnvAction World R) (name : Key) : EnvAction World R :=
  if windows then accessEnvWindows windowsOps fromString onError name
  else accessEnvPosix posixOps fromString onError name

def hasEnv {World Cache Key WString WBuffer Ptr : Type}
    (windows : Bool) (windowsOps : WindowsEnvOps World Cache Key WString WBuffer)
    (posixOps : PosixEnvOps World Key Ptr) (name : Key) : EnvAction World Bool :=
  if windows then hasEnvWindows windowsOps name else hasEnvPosix posixOps name

def setEnvironment {World Cache Key WString WBuffer Ptr Value : Type}
    (windows : Bool) (windowsOps : WindowsEnvOps World Cache Key WString WBuffer)
    (posixOps : PosixEnvOps World Key Ptr) (name : Key) (value : Value)
    (overwrite : Bool := true) : EnvAction World Unit :=
  if windows then setEnvWindows windowsOps name value overwrite
  else setEnvPosix posixOps name value overwrite

def unsetEnvironment {World Cache Key WString WBuffer Ptr : Type}
    (windows : Bool) (windowsOps : WindowsEnvOps World Cache Key WString WBuffer)
    (posixOps : PosixEnvOps World Key Ptr) (name : Key) : EnvAction World Unit :=
  if windows then unsetEnvWindows windowsOps name else unsetEnvPosix posixOps name

inductive EnvUpperResult (Original : Type) where
  | original (value : Original)
  | normalized (value : String)

structure WindowsUpperOps (World Original Wide : Type) where
  isEmpty : Original → Bool
  toString : Original → EnvAction World String
  toWide : String → EnvAction World Wide
  length : Wide → I64
  toCint : I64 → EnvAction World I32
  mapString : U32 → U32 → Wide → I32 → Wide → I32 → EnvAction World I32
  systemError : String → Bool → EnvAction World Unit
  fromWide : Wide → EnvAction World String

/--
Julia source: base/env.jl:193-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.iswindows()
    GESW() = (pos = ccall(:GetEnvironmentStringsW, stdcall, Ptr{UInt16}, ()); (pos, pos))
```
-/
def GESW {World Ptr : Type} (getEnvironmentStrings : EnvAction World Ptr) :
    EnvAction World (Ptr × Ptr) := do
  let position ← getEnvironmentStrings
  pure (position, position)

/--
Julia source: base/env.jl:195-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function winuppercase(s::AbstractString)
        isempty(s) && return s
        LOCALE_INVARIANT = 0x0000007f
        LCMAP_UPPERCASE  = 0x00000200
        ws = transcode(UInt16, String(s))
        result = ccall(:LCMapStringW, stdcall, Cint, (UInt32, UInt32, Ptr{UInt16}, Cint, Ptr{UInt16}, Cint),
                       LOCALE_INVARIANT, LCMAP_UPPERCASE, ws, length(ws), ws, length(ws))
        systemerror(:LCMapStringW, iszero(result))
        return transcode(String, ws)
    end
```
-/
def winuppercase {World Original Wide : Type}
    (ops : WindowsUpperOps World Original Wide) (value : Original) :
    EnvAction World (EnvUpperResult Original) := do
  if ops.isEmpty value then pure (.original value)
  else do
    let string ← ops.toString value
    let wide ← ops.toWide string
    let sourceLength ← ops.toCint (ops.length wide)
    let destinationLength ← ops.toCint (ops.length wide)
    let result ← ops.mapString (JInt.lit .u32 0x7f) (JInt.lit .u32 0x200)
      wide sourceLength wide destinationLength
    ops.systemError "LCMapStringW" (result.val == 0)
    let upper ← ops.fromWide wide
    pure (.normalized upper)

private def winuppercaseString {World Wide : Type}
    (ops : WindowsUpperOps World String Wide) (value : String) : EnvAction World String := do
  match ← winuppercase ops value with
  | .original original => pure original
  | .normalized upper => pure upper

structure WindowsIterState (Ptr : Type) where
  position : Ptr
  base : Ptr

structure WindowsIterOps (World Ptr WideBuffer : Type) where
  getEnvironmentStrings : EnvAction World Ptr
  loadUInt16 : Ptr → EnvAction World U16
  freeEnvironmentStrings : Ptr → EnvAction World Unit
  wcslen : Ptr → EnvAction World U64
  allocateWide : U64 → EnvAction World WideBuffer
  copyWide : WideBuffer → Ptr → U64 → EnvAction World Unit
  wideToString : WideBuffer → EnvAction World String
  advancePointer : Ptr → U64 → EnvAction World Ptr
  warnMalformed : String → EnvAction World Unit

/--
Julia source: base/env.jl:205-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function iterate(hash::EnvDict, block::Tuple{Ptr{UInt16},Ptr{UInt16}} = GESW())
        while true
            if unsafe_load(block[1]) == 0
                ccall(:FreeEnvironmentStringsW, stdcall, Int32, (Ptr{UInt16},), block[2])
                return nothing
            end
            pos = block[1]
            blk = block[2]
            len = ccall(:wcslen, UInt, (Ptr{UInt16},), pos)
            buf = Vector{UInt16}(undef, len)
            GC.@preserve buf unsafe_copyto!(pointer(buf), pos, len)
            env = transcode(String, buf)
            pos += (len + 1) * 2
            if !isempty(env)
                m = findnext('=', env, nextind(env, firstindex(env)))
            else
                m = nothing
            end
            if m === nothing
                @warn "malformed environment entry" env
                continue
            end
            return (Pair{String,String}(winuppercase(env[1:prevind(env, m)]), env[nextind(env, m):end]), (pos, blk))
        end
    end
```
-/
def iterateWindows {World Ptr WideBuffer : Type}
    (ops : WindowsIterOps World Ptr WideBuffer)
    (strings : EnvStringOps) (upperOps : WindowsUpperOps World String WideBuffer)
    (state : Option (WindowsIterState Ptr) := none) :
    EnvAction World (Option ((String × String) × WindowsIterState Ptr)) := do
  let initial ← match state with
    | some state => pure state
    | none => do
      let (position, base) ← GESW ops.getEnvironmentStrings
      pure ⟨position, base⟩
  JuliaLean.base.io.whileLoop (fun state => do
    let first ← ops.loadUInt16 state.position
    if first.val == 0 then do
      ops.freeEnvironmentStrings state.base
      pure (.inl none)
    else do
      let length ← ops.wcslen state.position
      let buffer ← ops.allocateWide length
      ops.copyWide buffer state.position length
      let environment ← ops.wideToString buffer
      let byteOffset := (length + JInt.lit .u64 1) * JInt.lit .u64 2
      let nextPosition ← ops.advancePointer state.position byteOffset
      let nextState := { state with position := nextPosition }
      let separator := if strings.isEmpty environment then none
        else strings.findNextEquals environment
          (strings.nextIndex environment (strings.firstIndex environment))
      match separator with
      | none => do
        ops.warnMalformed environment
        pure (.inr nextState)
      | some index => do
        let key := strings.slice environment 1 (strings.prevIndex environment index)
        let value := strings.slice environment (strings.nextIndex environment index)
          (strings.lastIndex environment)
        let key ← winuppercaseString upperOps key
        pure (.inl (some ((key, value), nextState)))) initial

structure PosixIterOps (World Environ Ptr : Type) where
  environOps : PosixEnvironOps World Ptr Environ
  environIsNull : Environ → Bool
  loadEntry : Environ → I64 → EnvAction World Ptr
  isNull : Ptr → Bool
  unsafeString : Ptr → EnvAction World String
  warnMalformed : String → EnvAction World Unit

/--
Julia source: base/env.jl:230-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
else # !windows
    function iterate(::EnvDict, i=0)
        envs = _environ()
        envs == C_NULL && error("Failed to resolve `environ`.")
        while true
            envp = unsafe_load(envs, i + 1)
            envp == C_NULL && return nothing
            env = unsafe_string(envp)
            i += 1
            m = findfirst('=', env)
            if m === nothing
                @warn "malformed environment entry" env
                continue
            end
            return (Pair{String,String}(env[1:prevind(env, m)], env[nextind(env, m):end]), i)
        end
    end
end # os-test
```
-/
def iteratePosix {World Environ Ptr : Type}
    (ops : PosixIterOps World Environ Ptr) (strings : EnvStringOps)
    (state : Option I64 := none) :
    EnvAction World (Option ((String × String) × I64)) := do
  let environment ← environPosix ops.environOps
  if ops.environIsNull environment then
    throw (.errorException "Failed to resolve `environ`.")
  let index := state.getD (JInt.lit .i64 0)
  JuliaLean.base.io.whileLoop (fun index => do
    let pointer ← ops.loadEntry environment (index + JInt.lit .i64 1)
    if ops.isNull pointer then pure (.inl none)
    else do
      let entry ← ops.unsafeString pointer
      let nextIndex := index + JInt.lit .i64 1
      match strings.findFirstEquals entry with
      | none => do
        ops.warnMalformed entry
        pure (.inr nextIndex)
      | some separator => do
        let key := strings.slice entry 1 (strings.prevIndex entry separator)
        let value := strings.slice entry (strings.nextIndex entry separator)
          (strings.lastIndex entry)
        pure (.inl (some ((key, value), nextIndex)))) index

abbrev EnvIterator (World State : Type) :=
  Option State → EnvAction World (Option ((String × String) × State))

/--
Julia source: base/env.jl:249-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#TODO: Make these more efficient
function length(::EnvDict)
    i = 0
    for _ in ENV
        i += 1
    end
    return i
end
```
-/
def envLength {World State : Type} (iterate : EnvIterator World State) :
    EnvAction World I64 := do
  let (length, _) ← JuliaLean.base.io.whileLoop (fun state => do
    match ← iterate state.2 with
    | none => pure (.inl state)
    | some (_, next) => pure (.inr (state.1 + JInt.lit .i64 1, some next)))
      (JInt.lit .i64 0, none)
  pure length

/--
Julia source: base/env.jl:258-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::EnvDict)
    for (k,v) = ENV
        println(io, "$k=$v")
    end
end
```
-/
def showEnv {World State Io : Type} (iterate : EnvIterator World State)
    (println : Io → String → EnvAction World Unit) (io : Io) : EnvAction World Unit := do
  let _ ← JuliaLean.base.io.whileLoop (fun state => do
    match ← iterate state with
    | none => pure (.inl ())
    | some ((key, value), next) => do
      println io (key ++ "=" ++ value)
      pure (.inr (some next))) none
  pure ()

-- This sum records the value type returned by `get` when its default can differ from String.
inductive EnvLookup (Default : Type) where
  | fromEnv (value : String)
  | default (value : Default)

/--
Julia source: base/env.jl:89-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
## ENV: hash interface ##

"""
    EnvDict()::EnvDict

A singleton of this type provides a hash table interface to environment variables.
"""
struct EnvDict <: AbstractDict{String,String}; end

"""
    ENV

Reference to the singleton `EnvDict`, providing a dictionary interface to system environment
variables.

(On Windows, system environment variables are case-insensitive, and `ENV` correspondingly converts
all keys to uppercase for display, iteration, and copying. Portable code should not rely on the
ability to distinguish variables by case, and should beware that setting an ostensibly lowercase
variable may result in an uppercase `ENV` key.)

!!! warning
    Mutating the environment is not thread-safe.

# Examples
```julia-repl
julia> ENV
Base.EnvDict with "50" entries:
  "SECURITYSESSIONID"            => "123"
  "USER"                         => "username"
  "MallocNanoZone"               => "0"
  ⋮                              => ⋮

julia> ENV["JULIA_EDITOR"] = "vim"
"vim"

julia> ENV["JULIA_EDITOR"]
"vim"
```

See also: [`withenv`](@ref), [`addenv`](@ref).
"""
const ENV = EnvDict()
````
-/
inductive EnvDict where
  | singleton
  deriving DecidableEq, Repr

def ENV : EnvDict := .singleton

-- Source: base/env.jl:132-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const get_bool_env_truthy = (
--     "t", "T",
--     "true", "True", "TRUE",
--     "y", "Y",
--     "yes", "Yes", "YES",
--     "1")
-- const get_bool_env_falsy = (
--     "f", "F",
--     "false", "False", "FALSE",
--     "n", "N",
--     "no", "No", "NO",
--     "0")
-- /Source
def getBoolEnvTruthy : List String :=
  ["t", "T", "true", "True", "TRUE", "y", "Y", "yes", "Yes", "YES", "1"]

def getBoolEnvFalsy : List String :=
  ["f", "F", "false", "False", "FALSE", "n", "N", "no", "No", "NO", "0"]

structure BoolEnvOps (World : Type) where
  hasKey : String → EnvAction World Bool
  getIndex : String → EnvAction World String
  isEmpty : String → Bool
  reprString : String → String

/--
Julia source: base/env.jl:145-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.get_bool_env(name::String, default::Bool; throw=false)::Union{Bool,Nothing}
    Base.get_bool_env(f_default::Callable, name::String; throw=false)::Union{Bool,Nothing}

Evaluate whether the value of environment variable `name` is a truthy or falsy string,
and return `nothing` (or throw if `throw=true`) if it is not recognized as either. If
the variable is not set, or is set to "", return `default` or the result of executing `f_default()`.

Recognized values are the following, and their Capitalized and UPPERCASE forms:
    truthy: "t", "true", "y", "yes", "1"
    falsy:  "f", "false", "n", "no", "0"
"""
get_bool_env(name::String, default::Bool; kwargs...) = get_bool_env(Returns(default), name; kwargs...)
function get_bool_env(f_default::Callable, name::String; kwargs...)
    if haskey(ENV, name)
        val = ENV[name]
        if !isempty(val)
            return parse_bool_env(name, val; kwargs...)
        end
    end
    return f_default()
end
function parse_bool_env(name::String, val::String = ENV[name]; throw::Bool=false)
    if val in get_bool_env_truthy
        return true
    elseif val in get_bool_env_falsy
        return false
    elseif throw
        Base.throw(ArgumentError("Value for environment variable `$name` could not be parsed as Boolean: $(repr(val))"))
    else
        return nothing
    end
end
```
-/
def parseBoolEnv {World : Type} (ops : BoolEnvOps World) (name : String)
    (value : Option String := none) (throwOnInvalid : Bool := false) :
    EnvAction World (Option Bool) := do
  let value ← match value with
    | some value => pure value
    | none => ops.getIndex name
  if getBoolEnvTruthy.contains value then pure (some true)
  else if getBoolEnvFalsy.contains value then pure (some false)
  else if throwOnInvalid then
    throw (.jl (.argumentError ("Value for environment variable `" ++ name ++
      "` could not be parsed as Boolean: " ++ ops.reprString value)))
  else pure none

def getBoolEnvLazy {World : Type} (ops : BoolEnvOps World)
    (default : Unit → EnvAction World Bool) (name : String)
    (throwOnInvalid : Bool := false) : EnvAction World (Option Bool) := do
  if ← ops.hasKey name then
    let value ← ops.getIndex name
    if !ops.isEmpty value then parseBoolEnv ops name (some value) throwOnInvalid
    else some <$> default ()
  else some <$> default ()

def getBoolEnvDefault {World : Type} (ops : BoolEnvOps World)
    (name : String) (default : Bool) (throwOnInvalid : Bool := false) :
    EnvAction World (Option Bool) :=
  getBoolEnvLazy ops (fun _ => pure default) name throwOnInvalid

/--
Julia source: base/env.jl:179-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(::EnvDict, k::AbstractString) = access_env(k->throw(KeyError(k)), k)
```
-/
def getIndexEnv {World Key : Type} (access : EnvAccess World Key)
    (keyError : Key → JuliaLean.base.io.Error) (key : Key) :
    EnvAction World String :=
  access id (fun missing => throw (keyError missing)) key

/--
Julia source: base/env.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(::EnvDict, k::AbstractString, def) = access_env(Returns(def), k)
```
-/
def getEnvDefault {World Key Default : Type} (access : EnvAccess World Key)
    (key : Key) (default : Default) : EnvAction World (EnvLookup Default) :=
  access EnvLookup.fromEnv (fun _ => pure (.default default)) key

/--
Julia source: base/env.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Callable, ::EnvDict, k::AbstractString) = access_env(k->f(), k)
```
-/
def getEnvWithDefault {World Key Default : Type} (access : EnvAccess World Key)
    (key : Key) (default : Unit → EnvAction World Default) :
    EnvAction World (EnvLookup Default) :=
  access EnvLookup.fromEnv (fun _ => do pure (.default (← default ()))) key

/--
Julia source: base/env.jl:182-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get!(default::Callable, ::EnvDict, k::AbstractString)
    haskey(ENV, k) && return ENV[k]
    ENV[k] = default()
end
```
-/
def getEnvBang {World Key Value : Type} (hasKey : Key → EnvAction World Bool)
    (getIndex : Key → EnvAction World String) (setIndex : Key → Value → EnvAction World Unit)
    (key : Key) (default : Unit → EnvAction World Value) : EnvAction World (EnvLookup Value) := do
  if ← hasKey key then EnvLookup.fromEnv <$> getIndex key
  else do
    let value ← default ()
    setIndex key value
    pure (.default value)
/--
Julia source: base/env.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(k::AbstractString, ::KeySet{String, EnvDict}) = _hasenv(k)
```
-/
def envKeyIn {World Key : Type} (hasKey : Key → EnvAction World Bool)
    (key : Key) : EnvAction World Bool :=
  hasKey key

/--
Julia source: base/env.jl:187-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(::EnvDict, k::AbstractString) = (v = ENV[k]; _unsetenv(k); v)
```
-/
def popEnv {World Key : Type} (getIndex : Key → EnvAction World String)
    (unset : Key → EnvAction World Unit) (key : Key) : EnvAction World String := do
  let value ← getIndex key
  unset key
  pure value

/--
Julia source: base/env.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pop!(::EnvDict, k::AbstractString, def) = haskey(ENV,k) ? pop!(ENV,k) : def
```
-/
def popEnvDefault {World Key Default : Type} (hasKey : Key → EnvAction World Bool)
    (pop : Key → EnvAction World String) (key : Key) (default : Default) :
    EnvAction World (EnvLookup Default) := do
  if ← hasKey key then EnvLookup.fromEnv <$> pop key
  else pure (.default default)

/--
Julia source: base/env.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
delete!(::EnvDict, k::AbstractString) = (_unsetenv(k); ENV)
```
-/
def deleteEnv {World Key : Type} (unset : Key → EnvAction World Unit)
    (key : Key) : EnvAction World EnvDict := do
  unset key
  pure ENV

/--
Julia source: base/env.jl:190-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(::EnvDict, v, k::AbstractString) = _setenv(k,string(v))
```
-/
def setIndexEnv {World Key Value : Type}
    (stringify : Value → EnvAction World String)
    (setEnv : Key → String → Bool → EnvAction World Unit)
    (value : Value) (key : Key) : EnvAction World Unit := do
  let text ← stringify value
  setEnv key text true

/--
Julia source: base/env.jl:191-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(::EnvDict, kv::Pair{<:AbstractString}) = setindex!(ENV, kv.second, kv.first)
```
-/
def pushEnv {World Key Value : Type}
    (setIndex : Value → Key → EnvAction World Unit) (value : Value) (key : Key) :
    EnvAction World Unit :=
  setIndex value key

structure WithenvOps (World Key Map : Type) where
  get : Key → EnvAction World (Option String)
  set : {Value : Type} → Key → Value → EnvAction World Unit
  delete : Key → EnvAction World Unit
  emptyMap : Map
  save : Map → Key → Option String → Map
  entries : Map → List (Key × Option String)

/--
Julia source: base/env.jl:264-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    withenv(f, kv::Pair...)

Execute `f` in an environment that is temporarily modified (not replaced as in `setenv`)
by zero or more `"var"=>val` arguments `kv`. `withenv` is generally used via the
`withenv(kv...) do ... end` syntax. A value of `nothing` can be used to temporarily unset an
environment variable (if it is set). When `withenv` returns, the original environment has
been restored.

!!! warning
    Changing the environment is not thread-safe. For running external commands with a different
    environment from the parent process, prefer using [`addenv`](@ref) over `withenv`.
"""
function withenv(f, keyvals::Pair{T}...) where T<:AbstractString
    old = Dict{T,Any}()
    for (key,val) in keyvals
        old[key] = get(ENV,key,nothing)
        val !== nothing ? (ENV[key]=val) : delete!(ENV, key)
    end
    try f()
    finally
        for (key,val) in old
            val !== nothing ? (ENV[key]=val) : delete!(ENV, key)
        end
    end
end
withenv(f) = f() # handle empty keyvals case; see #10853
```
-/
def withenv {World Key Map Value A : Type}
    (ops : WithenvOps World Key Map) (f : Unit → EnvAction World A)
    (keyvals : List (Key × Option Value)) : EnvAction World A := do
  let mut old := ops.emptyMap
  for (key, value) in keyvals do
    let previous ← ops.get key
    old := ops.save old key previous
    match value with
    | some value => ops.set key value
    | none => ops.delete key
  JuliaLean.base.io.finallyDo (f ()) (do
    for (key, value) in ops.entries old do
      match value with
      | some value => ops.set key value
      | none => ops.delete key)

def withenvEmpty {World A : Type} (f : Unit → EnvAction World A) : EnvAction World A :=
  f ()

end JuliaLean.base.env

section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Env

open JuliaLean JuliaLean.IOCov

abbrev Bytes := List UInt8
abbrev Environ := List Bytes

def eqB : UInt8 := 61   -- '='

/-- `findfirst('=', env)` split: `(name, value)` of an entry with a `'='`. -/
def splitEntry (e : Bytes) : Option (Bytes × Bytes) :=
  match e.idxOf? eqB with
  | none => none
  | some k => some (e.take k, e.drop (k + 1))

/-- Value of `name` in an entry, as `getenv` matches it. -/
def entryValue (name : Bytes) (e : Bytes) : Option Bytes :=
  if (name ++ [eqB]).isPrefixOf e then some (e.drop (name.length + 1)) else none

/-- C `getenv(name)`; `none` is `C_NULL`. -/
def cgetenv (env : Environ) (name : Bytes) : Option Bytes :=
  env.findSome? (entryValue name)

def validName (name : Bytes) : Bool := !name.isEmpty && !name.contains eqB

/-- The first entry for `name` replaced by `new`. -/
def replaceFirst (name new : Bytes) : Environ → Environ
  | [] => []
  | e :: es => if (entryValue name e).isSome then new :: es else e :: replaceFirst name new es

/-- C `setenv(name, value, overwrite)`: `none` is the `-1` (`EINVAL`) return. -/
def csetenv (env : Environ) (name value : Bytes) (overwrite : Bool) : Option Environ :=
  if !validName name then none
  else match cgetenv env name with
    | none => some (env ++ [name ++ eqB :: value])
    | some _ => if overwrite then some (replaceFirst name (name ++ eqB :: value) env) else some env

/-- C `unsetenv(name)`. -/
def cunsetenv (env : Environ) (name : Bytes) : Option Environ :=
  if !validName name then none else some (env.filter (fun e => (entryValue name e).isNone))

/-- `Cstring` conversion of a Julia string argument. -/
def cstring (s : Bytes) : R Bytes :=
  if s.contains 0 then argErr "embedded NULs are not allowed in C strings" else .ok s

/-! ## Primitive accessors, lines 55-86 -/

/-- `_getenv(var) = getenv(var)`, line 55. -/
def getenvP (env : Environ) (var : Bytes) : R (Option Bytes) := do
  let v ← cstring var
  pure (cgetenv env v)
/-- `_hasenv(s) = _getenv(s) != C_NULL`, line 56. -/
def hasenv (env : Environ) (s : Bytes) : R Bool := do
  let r ← getenvP env s
  pure r.isSome
/-- `_environ()`, line 70 (Linux): the `environ` array. -/
def environ (env : Environ) : Environ := env
/-- `access_env(onError, var)`, lines 73-76. -/
def accessEnv {α} (env : Environ) (onError : Bytes → R α) (ofVal : Bytes → α) (var : Bytes) : R α := do
  let v ← getenvP env var
  match v with
  | none => onError var
  | some s => pure (ofVal s)
/-- `_setenv(var, val, overwrite)`, lines 78-81. -/
def setenvP (env : Environ) (var val : Bytes) (overwrite : Bool := true) : R Environ := do
  let k ← cstring var
  let v ← cstring val
  match csetenv env k v overwrite with
  | none => .error (.systemError "setenv")
  | some e => pure e
/-- `_unsetenv(var)`, lines 83-86. -/
def unsetenvP (env : Environ) (var : Bytes) : R Environ := do
  let k ← cstring var
  match cunsetenv env k with
  | none => .error (.systemError "unsetenv")
  | some e => pure e

/-! ## `EnvDict` methods, lines 179-191 -/

/-- `getindex(::EnvDict, k) = access_env(k->throw(KeyError(k)), k)`, line 179. -/
def getindex (env : Environ) (k : Bytes) : R Bytes :=
  accessEnv env (fun k => .error (.keyError k)) id k
/-- `get(::EnvDict, k, def) = access_env(Returns(def), k)`, line 180. -/
def get (env : Environ) (k def_ : Bytes) : R Bytes := accessEnv env (fun _ => .ok def_) id k
/-- `get(f, ::EnvDict, k) = access_env(k->f(), k)`, line 181. -/
def getF (env : Environ) (f : Unit → R Bytes) (k : Bytes) : R Bytes := accessEnv env (fun _ => f ()) id k
/-- `in(k, keys(ENV)) = _hasenv(k)`, line 186 (`haskey`). -/
def haskey (env : Environ) (k : Bytes) : R Bool := hasenv env k
/-- `setindex!(::EnvDict, v, k) = _setenv(k, string(v))`, line 190. -/
def setindex (env : Environ) (v k : Bytes) : R Environ := setenvP env k v
/-- `push!(::EnvDict, kv) = setindex!(ENV, kv.second, kv.first)`, line 191. -/
def push (env : Environ) (kv : Bytes × Bytes) : R Environ := setindex env kv.2 kv.1
/-- `delete!(::EnvDict, k) = (_unsetenv(k); ENV)`, line 189. -/
def delete (env : Environ) (k : Bytes) : R Environ := unsetenvP env k
/-- `pop!(::EnvDict, k) = (v = ENV[k]; _unsetenv(k); v)`, line 187. -/
def pop (env : Environ) (k : Bytes) : R (Bytes × Environ) := do
  let v ← getindex env k
  let e ← unsetenvP env k
  pure (v, e)
/-- `pop!(::EnvDict, k, def) = haskey(ENV,k) ? pop!(ENV,k) : def`, line 188. -/
def popDef (env : Environ) (k def_ : Bytes) : R (Bytes × Environ) := do
  let h ← haskey env k
  if h then pop env k else pure (def_, env)
/-- `get!(default, ::EnvDict, k)`, lines 182-185: `ENV[k] = default()` returns `default()`. -/
def getBang (env : Environ) (default : Unit → Bytes) (k : Bytes) : R (Bytes × Environ) := do
  let h ← haskey env k
  if h then do let v ← getindex env k; pure (v, env)
  else do let e ← setindex env (default ()) k; pure (default (), e)

/-! ## `get_bool_env`, `parse_bool_env`, lines 133-177 -/

def truthy : List Bytes := ["t", "T", "true", "True", "TRUE", "y", "Y", "yes", "Yes", "YES", "1"].map bs
def falsy : List Bytes := ["f", "F", "false", "False", "FALSE", "n", "N", "no", "No", "NO", "0"].map bs

/-- `parse_bool_env(name, val; throw)`, lines 167-177; `nothing` is `none`. -/
def parseBoolEnv (val : Bytes) (throw : Bool) : R (Option Bool) :=
  if val ∈ truthy then .ok (some true)
  else if val ∈ falsy then .ok (some false)
  else if throw then argErr "Value for environment variable could not be parsed as Boolean"
  else .ok none

/-- `get_bool_env(f_default, name; kwargs...)`, lines 158-166. -/
def getBoolEnvF (env : Environ) (fDefault : Unit → Option Bool) (name : Bytes) (throw : Bool) :
    R (Option Bool) := do
  let h ← haskey env name
  if h then
    let val ← getindex env name
    if !val.isEmpty then return (← parseBoolEnv val throw)
  pure (fDefault ())

/-- `get_bool_env(name, default; kwargs...)`, line 157. -/
def getBoolEnv (env : Environ) (name : Bytes) (default : Bool) (throw : Bool) : R (Option Bool) :=
  getBoolEnvF env (fun _ => some default) name throw

/-! ## Iteration, `length`, `show`, lines 231-262 -/

/-- `iterate(::EnvDict, i)`, lines 231-246: the entries from index `i`, split at the first
`'='`; entries without one are skipped (with a warning). -/
def iterateFrom (env : Environ) : List (Bytes × Bytes) := env.filterMap splitEntry

/-- `length(::EnvDict)`, lines 250-256: the number of iterated pairs. -/
def length (env : Environ) : Nat := (iterateFrom env).length

/-- `show(io, ::EnvDict)`, lines 258-262: one `k=v` line per pair. -/
def showEnv (env : Environ) : Bytes :=
  ((iterateFrom env).map (fun (k, v) => k ++ eqB :: v ++ [10])).flatten

/-! ## `withenv`, lines 277-290 -/

/-- One assignment of `withenv`: `val !== nothing ? (ENV[key]=val) : delete!(ENV, key)`. -/
def assign (env : Environ) (key : Bytes) (val : Option Bytes) : R Environ :=
  match val with
  | some v => setindex env v key
  | none => delete env key

/-- `old[key] = get(ENV, key, nothing)` for each pair, then the assignment. `old` is a
`Dict`: a later value for the same key replaces the earlier one in place. -/
def withenvSetup (env : Environ) : List (Bytes × Option Bytes) → List (Bytes × Option Bytes) →
    R (List (Bytes × Option Bytes) × Environ)
  | old, [] => .ok (old, env)
  | old, (key, val) :: rest => do
    let cur ← getenvP env key
    let old' := if old.any (·.1 == key) then old.map (fun p => if p.1 == key then (key, cur) else p)
      else old ++ [(key, cur)]
    let env' ← assign env key val
    withenvSetup env' old' rest

/-- Restoring loop of `withenv`'s `finally` block. -/
def restore (env : Environ) : List (Bytes × Option Bytes) → R Environ
  | [] => .ok env
  | (key, val) :: rest => do let e ← assign env key val; restore e rest

/-- `withenv(f, keyvals...)`, lines 277-289, with `f` not touching the environment. -/
def withenv (env : Environ) (kvs : List (Bytes × Option Bytes)) : R Environ := do
  let (old, env') ← withenvSetup env [] kvs
  restore env' old

/-- `withenv(f) = f()`, line 290. -/
def withenv0 (env : Environ) : Environ := env
end JuliaLean.IOCov.Env
end

section
namespace JuliaLean.IOCov.EnvFaithful

open JuliaLean JuliaLean.Registry
open JuliaLean.IOCov Env

abbrev Bytes := Env.Bytes
abbrev Environ := Env.Environ

/-- Linux `_environ() = unsafe_load(_environ_ptr())`, `base/env.jl:70`.
The argument is the result of the OncePerProcess pointer load. -/
def environLoad (loaded : R Environ) : R Environ := loaded

/-- `get_bool_env(name, default)`, `base/env.jl:157`. -/
def getBoolDefault (env : Environ) (name : Bytes) (default : Bool) (throw : Bool) : R (Option Bool) :=
  Env.getBoolEnvF env (fun _ => some default) name throw

/-- `parse_bool_env(name, val; throw)`, `base/env.jl:167-177`, including the
name and value used in the thrown message. -/
def parseBoolNamed (name val : Bytes) (throw : Bool) : R (Option Bool) :=
  if val ∈ Env.truthy then .ok (some true)
  else if val ∈ Env.falsy then .ok (some false)
  else if throw then .error (.jl (.argumentError
    ("Value for environment variable `" ++ String.ofList (name.map (Char.ofNat ∘ UInt8.toNat)) ++
     "` could not be parsed as Boolean")))
  else .ok none

/-- Callable-default `get_bool_env`, `base/env.jl:158-166`. -/
def getBoolCallable (env : Environ) (fDefault : Unit -> Option Bool)
    (name : Bytes) (throw : Bool) : R (Option Bool) := do
  let present <- Env.haskey env name
  if present then
    let val <- Env.getindex env name
    if !val.isEmpty then return <- parseBoolNamed name val throw
  pure (fDefault ())

/-- `get!(default, ENV, k)`, `base/env.jl:182-185`.  The callback result is
bound once and reused for the assignment and return. -/
def getBangOnce (env : Environ) (default : Unit -> Bytes) (k : Bytes) : R (Bytes × Environ) := do
  let present <- Env.haskey env k
  if present then
    let v <- Env.getindex env k
    pure (v, env)
  else
    let v := default ()
    let env' <- Env.setindex env v k
    pure (v, env')

/-- `setindex!(ENV, v, k)` for arbitrary values, `base/env.jl:190`.
`stringify` is Julia's `string(v)`. -/
def setindexAny {alpha : Type} (stringify : alpha -> Bytes)
    (env : Environ) (v : alpha) (k : Bytes) : R Environ :=
  Env.setenvP env k (stringify v)

/-- `push!(ENV, kv)`, `base/env.jl:191`, for arbitrary pair values. -/
def pushAny {alpha : Type} (stringify : alpha -> Bytes)
    (env : Environ) (k : Bytes) (v : alpha) : R Environ :=
  setindexAny stringify env v k

structure IterStep where
  value : Option (Bytes × Bytes)
  next : Nat
  warnings : List Bytes
  deriving DecidableEq

def iterateLoop : Nat -> Environ -> Nat -> List Bytes -> IterStep
  | 0, _, i, warnings => ⟨none, i, warnings⟩
  | fuel + 1, env, i, warnings =>
      if hi : i < env.length then
        let entry := env.get ⟨i, hi⟩
          match Env.splitEntry entry with
          | some kv => ⟨some kv, i + 1, warnings⟩
          | none => iterateLoop fuel env (i + 1) (warnings ++ [entry])
      else ⟨none, i, warnings⟩

/-- Non-Windows `iterate(::EnvDict, i)`, `base/env.jl:231-246`.
`none` for `environ` models C_NULL and throws before the loop. -/
def iterateEnv (environ : Option Environ) (i : Nat) : R IterStep :=
  match environ with
  | none => .error (.errorException "Failed to resolve `environ`.")
  | some env => .ok (iterateLoop (env.length - i + 1) env i [])

def collectEnv : Nat -> Environ -> Nat -> List (Bytes × Bytes)
  | 0, _, _ => []
  | fuel + 1, env, i =>
      let step := iterateLoop (env.length - i + 1) env i []
      match step.value with
      | none => []
      | some kv => kv :: collectEnv fuel env step.next

/-- `length(::EnvDict)`, `base/env.jl:250-256`, by repeated iteration. -/
def envLength (env : Environ) : Nat := (collectEnv (env.length + 1) env 0).length

/-- `show(io, ::EnvDict)`, `base/env.jl:258-262`, as bytes printed to IO. -/
def showEnvIO (env : Environ) : Bytes :=
  (collectEnv (env.length + 1) env 0).flatMap (fun kv => kv.1 ++ Env.eqB :: kv.2 ++ [10])

abbrev CallbackResult (alpha : Type) := R alpha × Environ

/-- `withenv(f, keyvals...)`, `base/env.jl:277-289`, including callback
execution, its returned value or exception, and finally restoration. -/
def withenvCall {alpha : Type} (env : Environ) (kvs : List (Bytes × Option Bytes))
    (f : Environ -> CallbackResult alpha) : R alpha × Environ :=
  match Env.withenvSetup env [] kvs with
  | .error e => (.error e, env)
  | .ok (old, temporary) =>
      let callback := f temporary
      match Env.restore callback.2 old with
      | .error e => (.error e, callback.2)
      | .ok restored => (callback.1, restored)

/-- `withenv(f) = f()`, `base/env.jl:290`. -/
def withenvZero {alpha : Type} (env : Environ) (f : Environ -> CallbackResult alpha) :
    R alpha × Environ := f env
end JuliaLean.IOCov.EnvFaithful
end
