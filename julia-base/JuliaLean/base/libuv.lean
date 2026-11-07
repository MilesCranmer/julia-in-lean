import JuliaLean.Core
import JuliaLean.base.expr
import JuliaLean.base.io

/-!
# Model of `base/libuv.jl`

The mutable world retains handle reference counts, both lock states and the
standard streams. libuv calls and runtime-owned values are typed operations;
errors preserve world changes made before the error. The model does not encode
thread interleavings. A spinlock acquisition while already held diverges.
-/
-- UNTRANSLATED
-- Source: base/libuv.jl:1-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Core definitions for interacting with the libuv library from Julia
-- 
-- include(string(Base.BUILDROOT, "uv_constants.jl"))  # include($BUILDROOT/base/uv_constants.jl)
-- /Source
-- Reason: The file-level comments and build-root include are not method bodies; `uv_constants.jl` is supplied by the Julia build.

namespace JuliaLean.base.libuv

open JuliaLean
open JuliaLean.base.expr

abbrev I := JInt .i64
abbrev CInt := JInt .i32
abbrev CSize := JInt .u64
abbrev Sym := String

def int (value : Int) : I := JInt.wrap .i64 value

structure IOError where
  msg : String
  code : CInt

inductive Error (RuntimeError : Type) where
  | domainError
  | typeError (expected : String)
  | keyError
  | argumentError (message : String)
  | errorException (message : String)
  | ioError (error : IOError)
  | runtime (error : RuntimeError)

abbrev M (World RuntimeError A : Type) :=
  World → Option (Except (Error RuntimeError × World) (A × World))

instance {World RuntimeError : Type} : Monad (M World RuntimeError) where
  pure value := fun world => some (.ok (value, world))
  bind action next := fun world =>
    match action world with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok (value, world)) => next value world

instance {World RuntimeError : Type} : MonadExceptOf (Error RuntimeError) (M World RuntimeError) where
  throw error := fun world => some (.error (error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok result) => some (.ok result)
    | some (.error (error, world)) => handler error world

inductive HandleCount where
  | integer (value : I)
  | other
  deriving DecidableEq, Repr

structure World (Object IO Runtime : Type) where
  handles : List (Object × HandleCount)
  preserveLockHeld : Bool
  ioLockDepth : Nat
  stdin : IO
  stdout : IO
  stderr : IO
  runtime : Runtime

private def getWorld {Object IO Runtime RuntimeError : Type} :
    M (World Object IO Runtime) RuntimeError (World Object IO Runtime) :=
  fun world => some (.ok (world, world))

private def setWorld {Object IO Runtime RuntimeError : Type}
    (next : World Object IO Runtime) : M (World Object IO Runtime) RuntimeError Unit :=
  fun _ => some (.ok ((), next))

private def lookupHandleCount {Object : Type} (sameObject : Object → Object → Bool)
    (handles : List (Object × HandleCount)) (key : Object) : HandleCount :=
  match handles with
  | [] => .integer (int 0)
  | (storedKey, value) :: rest =>
      if sameObject storedKey key then value else lookupHandleCount sameObject rest key

private def setHandleCount {Object : Type} (sameObject : Object → Object → Bool)
    (handles : List (Object × HandleCount)) (key : Object) (value : HandleCount) :
    List (Object × HandleCount) :=
  match handles with
  | [] => [(key, value)]
  | (storedKey, oldValue) :: rest =>
      if sameObject storedKey key then (storedKey, value) :: rest
      else (storedKey, oldValue) :: setHandleCount sameObject rest key value

private def removeHandleCount {Object : Type} (sameObject : Object → Object → Bool)
    (handles : List (Object × HandleCount)) (key : Object) : Option (List (Object × HandleCount)) :=
  match handles with
  | [] => none
  | (storedKey, value) :: rest =>
      if sameObject storedKey key then some rest
      else (removeHandleCount sameObject rest key).map (fun changed => (storedKey, value) :: changed)

private def acquirePreserveLock {Object IO Runtime RuntimeError : Type} :
    M (World Object IO Runtime) RuntimeError Unit := fun world =>
  if world.preserveLockHeld then none
  else some (.ok ((), { world with preserveLockHeld := true }))

private def releasePreserveLock {Object IO Runtime RuntimeError : Type} :
    M (World Object IO Runtime) RuntimeError Unit := fun world =>
  some (.ok ((), { world with preserveLockHeld := false }))

structure Ops (Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type) where
  unknownHandle : Handle
  handleTypeMax : Handle
  unknownRequest : Request
  requestTypeMax : Request
  handleLessThan : Handle → Handle → M (World Object IO Runtime) RuntimeError Bool
  requestLessThan : Request → Request → M (World Object IO Runtime) RuntimeError Bool
  handleToCint : Handle → M (World Object IO Runtime) RuntimeError CInt
  requestToCint : Request → M (World Object IO Runtime) RuntimeError CInt
  uvHandleSize : CInt → M (World Object IO Runtime) RuntimeError CSize
  uvRequestSize : CInt → M (World Object IO Runtime) RuntimeError CSize
  nullPtr : Ptr
  pointerIsNull : Ptr → Bool
  uvHandleGetData : Ptr → M (World Object IO Runtime) RuntimeError Ptr
  uvRequestGetData : Ptr → M (World Object IO Runtime) RuntimeError Ptr
  uvRequestSetDataAny : Ptr → Object → M (World Object IO Runtime) RuntimeError Unit
  uvHandleSetData : Ptr → Ptr → M (World Object IO Runtime) RuntimeError Unit
  handleField : Object → Ptr
  compileCloseHook : Object → M (World Object IO Runtime) RuntimeError Unit
  associateJuliaStruct : Ptr → Object → M (World Object IO Runtime) RuntimeError Unit
  disassociateJuliaStruct : Ptr → M (World Object IO Runtime) RuntimeError Unit
  eventLoop : M (World Object IO Runtime) RuntimeError Ptr
  uvUnref : Ptr → M (World Object IO Runtime) RuntimeError Unit
  uvRef : Ptr → M (World Object IO Runtime) RuntimeError Unit
  processEvents : M (World Object IO Runtime) RuntimeError CInt
  integerToCint : Integer → M (World Object IO Runtime) RuntimeError CInt
  integerLessThanZero : Integer → M (World Object IO Runtime) RuntimeError Bool
  boolToCint : Bool → CInt
  textToString : Text → M (World Object IO Runtime) RuntimeError String
  symbolToText : Sym → Text
  uvStrError : CInt → M (World Object IO Runtime) RuntimeError String
  uvErrorName : CInt → M (World Object IO Runtime) RuntimeError String
  uvEnoent : CInt
  writeString : IO → String → M (World Object IO Runtime) RuntimeError Unit
  sameObject : Object → Object → Bool
  typeName : Object → String
  stdinStream : M (World Object IO Runtime) RuntimeError Ptr
  stdoutStream : M (World Object IO Runtime) RuntimeError Ptr
  stderrStream : M (World Object IO Runtime) RuntimeError Ptr
  initStdio : Ptr → M (World Object IO Runtime) RuntimeError IO
  juliaOptions : M (World Object IO Runtime) RuntimeError Options
  coloredText : Options → M (World Object IO Runtime) RuntimeError (Option Bool)
  isTTY : IO → Bool
  ioContextColor : IO → Bool → M (World Object IO Runtime) RuntimeError IO

inductive IntegerArg (Integer : Type) where
  | integer (value : Integer)
  | boolean (value : Bool)


private def integerArgToCint {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (value : IntegerArg Integer) : M (World Object IO Runtime) RuntimeError CInt :=
  match value with
  | .integer integer => ops.integerToCint integer
  | .boolean boolean => pure (ops.boolToCint boolean)

private def textListToString {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError) :
    List Text → M (World Object IO Runtime) RuntimeError String
  | [] => pure ""
  | text :: rest => do
      let first ← ops.textToString text
      let suffix ← textListToString ops rest
      pure (first ++ suffix)

/--
Julia source: base/libuv.jl:7-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# convert UV handle data to julia object, checking for null
function uv_sizeof_handle(handle)
    if !(UV_UNKNOWN_HANDLE < handle < UV_HANDLE_TYPE_MAX)
        throw(DomainError(handle))
    end
    return ccall(:uv_handle_size, Csize_t, (Int32,), handle)
end
```
-/
def uvSizeofHandle {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (handle : Handle) : M (World Object IO Runtime) RuntimeError CSize := do
  if ← ops.handleLessThan ops.unknownHandle handle then
    if ← ops.handleLessThan handle ops.handleTypeMax then
      let code ← ops.handleToCint handle
      ops.uvHandleSize code
    else
      throw .domainError
  else
    throw .domainError

/--
Julia source: base/libuv.jl:15-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_sizeof_req(req)
    if !(UV_UNKNOWN_REQ < req < UV_REQ_TYPE_MAX)
        throw(DomainError(req))
    end
    return ccall(:uv_req_size, Csize_t, (Int32,), req)
end
```
-/
def uvSizeofRequest {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (request : Request) : M (World Object IO Runtime) RuntimeError CSize := do
  if ← ops.requestLessThan ops.unknownRequest request then
    if ← ops.requestLessThan request ops.requestTypeMax then
      let code ← ops.requestToCint request
      ops.uvRequestSize code
    else
      throw .domainError
  else
    throw .domainError

-- UNTRANSLATED
-- Source: base/libuv.jl:22-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for h in uv_handle_types
-- @eval const $(Symbol("_sizeof_", lowercase(string(h)))) = uv_sizeof_handle($h)
-- end
-- for r in uv_req_types
-- @eval const $(Symbol("_sizeof_", lowercase(string(r)))) = uv_sizeof_req($r)
-- end
-- /Source
-- Reason: These loops generate module-level constant names from the external `uv_constants.jl` inventory using `@eval`; the model keeps the size methods themselves.
/--
Julia source: base/libuv.jl:29-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uv_handle_data(handle) = ccall(:uv_handle_get_data, Ptr{Cvoid}, (Ptr{Cvoid},), handle)
uv_req_data(handle) = ccall(:uv_req_get_data, Ptr{Cvoid}, (Ptr{Cvoid},), handle)
uv_req_set_data(req, data) = ccall(:uv_req_set_data, Cvoid, (Ptr{Cvoid}, Any), req, data)
uv_req_set_data(req, data::Ptr{Cvoid}) = ccall(:uv_handle_set_data, Cvoid, (Ptr{Cvoid}, Ptr{Cvoid}), req, data)
```
-/
def uvHandleData {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (handle : Ptr) : M (World Object IO Runtime) RuntimeError Ptr :=
  ops.uvHandleGetData handle

def uvRequestData {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (request : Ptr) : M (World Object IO Runtime) RuntimeError Ptr :=
  ops.uvRequestGetData request

def uvRequestSetDataAny {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (request : Ptr) (data : Object) : M (World Object IO Runtime) RuntimeError Unit :=
  ops.uvRequestSetDataAny request data

def uvRequestSetDataPointer {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (request data : Ptr) : M (World Object IO Runtime) RuntimeError Unit :=
  ops.uvHandleSetData request data

/--
Julia source: base/libuv.jl:34-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro handle_as(hand, typ)
    return quote
        local data = uv_handle_data($(esc(hand)))
        data == C_NULL && return
        unsafe_pointer_to_objref(data)::($(esc(typ)))
    end
end
```
-/
def handleAs {L : Type} (uvHandleData cNull unsafePointerToObjref : Value L)
    (hand typ : Value L) : Value L :=
  .expr "block"
    [.expr "local" [.expr "=" [.symbol "data", .expr "call" [uvHandleData, esc hand]]],
     .expr "&&" [.expr "call" [.symbol "==", .symbol "data", cNull], .returnNode none],
     .expr "::" [.expr "call" [unsafePointerToObjref, .symbol "data"], esc typ]]

-- UNTRANSLATED
-- Source: base/libuv.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _uv_hook_close end
-- /Source
-- Reason: This line declares `_uv_hook_close` without a method body; the native close callback dispatches to methods defined elsewhere.
/--
Julia source: base/libuv.jl:44-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function associate_julia_struct(handle::Ptr{Cvoid}, jlobj::T) where T
    # This `cfunction` is not used anywhere, but it triggers compilation of this
    # MethodInstance for `--trim` so that it will be available when dispatched to
    # by `jl_uv_call_close_callback()`
    _ = @cfunction(Base._uv_hook_close, Cvoid, (Ref{T},))
    ccall(:jl_uv_associate_julia_struct, Cvoid, (Ptr{Cvoid}, Any), handle, jlobj)
end
```
-/
def associateJuliaStruct {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (handle : Ptr) (object : Object) : M (World Object IO Runtime) RuntimeError Unit := do
  let _ ← ops.compileCloseHook object
  ops.associateJuliaStruct handle object

/--
Julia source: base/libuv.jl:51-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
disassociate_julia_struct(uv) = disassociate_julia_struct(uv.handle)
disassociate_julia_struct(handle::Ptr{Cvoid}) =
    handle != C_NULL && ccall(:jl_uv_disassociate_julia_struct, Cvoid, (Ptr{Cvoid},), handle)
```
-/
def disassociateJuliaStructPointer {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (handle : Ptr) : M (World Object IO Runtime) RuntimeError Unit := do
  if !ops.pointerIsNull handle then
    ops.disassociateJuliaStruct handle
  else
    pure ()

def disassociateJuliaStructObject {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (uv : Object) : M (World Object IO Runtime) RuntimeError Unit :=
  disassociateJuliaStructPointer ops (ops.handleField uv)

/--
Julia source: base/libuv.jl:55-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iolock_begin() = ccall(:jl_iolock_begin, Cvoid, ())
iolock_end() = ccall(:jl_iolock_end, Cvoid, ())
```
-/
def ioLockBegin {Object IO Runtime RuntimeError : Type} : M (World Object IO Runtime) RuntimeError Unit := do
  let world ← getWorld
  setWorld { world with ioLockDepth := world.ioLockDepth + 1 }

def ioLockEnd {Object IO Runtime RuntimeError : Type} : M (World Object IO Runtime) RuntimeError Unit := do
  let world ← getWorld
  setWorld { world with ioLockDepth := world.ioLockDepth - 1 }

/--
Julia source: base/libuv.jl:58-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A dict of all libuv handles that are being waited on somewhere in the system
# and should thus not be garbage collected
const uvhandles = IdDict()
const preserve_handle_lock = Threads.SpinLock()
```
-/
def initialWorld {Object IO Runtime : Type} (stdin stdout stderr : IO) (runtime : Runtime) :
    World Object IO Runtime :=
  ⟨[], false, 0, stdin, stdout, stderr, runtime⟩

/--
Julia source: base/libuv.jl:62-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function preserve_handle(@nospecialize(x))
    lock(preserve_handle_lock)
    v = get(uvhandles, x, 0)::Int
    uvhandles[x] = v + 1
    unlock(preserve_handle_lock)
    nothing
end
```
-/
def preserveHandle {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (x : Object) : M (World Object IO Runtime) RuntimeError Unit := do
  acquirePreserveLock
  let world ← getWorld
  match lookupHandleCount ops.sameObject world.handles x with
  | .integer value =>
      setWorld { world with handles := setHandleCount ops.sameObject world.handles x (.integer (value + int 1)) }
      releasePreserveLock
      pure ()
  | .other => throw (.typeError "Int")

/--
Julia source: base/libuv.jl:69-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer function unpreserve_handle(@nospecialize(x))
    lock(preserve_handle_lock)
    v = get(uvhandles, x, 0)::Int
    if v == 0
        unlock(preserve_handle_lock)
        error(lazy"unbalanced call to unpreserve_handle for $(typeof(x))")
    elseif v == 1
        pop!(uvhandles, x)
    else
        uvhandles[x] = v - 1
    end
    unlock(preserve_handle_lock)
    nothing
end
```
-/
def unpreserveHandle {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (x : Object) : M (World Object IO Runtime) RuntimeError Unit := do
  acquirePreserveLock
  let world ← getWorld
  let value ← match lookupHandleCount ops.sameObject world.handles x with
    | .integer value => pure value
    | .other => throw (.typeError "Int")
  if value == int 0 then
    releasePreserveLock
    throw (.errorException ("unbalanced call to unpreserve_handle for " ++ ops.typeName x))
  else if value == int 1 then
    match removeHandleCount ops.sameObject world.handles x with
    | none => throw .keyError
    | some handles => setWorld { world with handles := handles }
  else
    setWorld { world with handles := setHandleCount ops.sameObject world.handles x (.integer (value - int 1)) }
  releasePreserveLock
  pure ()

-- UNTRANSLATED
-- Source: base/libuv.jl:84-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ## Libuv error handling ##
-- 
-- /Source
-- Reason: This section heading has no executable Julia body.

/--
Julia source: base/libuv.jl:86-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct IOError <: Exception
    msg::String
    code::Int32
    IOError(msg::AbstractString, code::Integer) = new(msg, code)
end
```
-/
def ioErrorConstructor {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (msg : Text) (code : IntegerArg Integer) : M (World Object IO Runtime) RuntimeError IOError := do
  let msg ← ops.textToString msg
  let code ← integerArgToCint ops code
  pure ⟨msg, code⟩

/--
Julia source: base/libuv.jl:92-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, e::IOError)
    print(io, "IOError: ", e.msg)
    if e.code == UV_ENOENT && '~' in e.msg
        print(io, "\nMany shells expand '~' to the home directory in unquoted strings. To replicate this behavior, call",
                  " `expanduser` to expand the '~' character to the user’s home directory.")
    end
end
```
-/
def showError {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (io : IO) (error : IOError) : M (World Object IO Runtime) RuntimeError Unit := do
  ops.writeString io ("IOError: " ++ error.msg)
  if error.code == ops.uvEnoent && error.msg.toList.contains '~' then
    ops.writeString io
      "\nMany shells expand '~' to the home directory in unquoted strings. To replicate this behavior, call `expanduser` to expand the '~' character to the user’s home directory."
  else
    pure ()

/--
Julia source: base/libuv.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _UVError(pfx::AbstractString, code::Integer)
    code = Int32(code)
    IOError(string(pfx, ": ", struverror(code), " (", uverrorname(code), ")"), code)
end
```
-/
def uvErrorObject {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
(pfx : Text) (code : IntegerArg Integer) : M (World Object IO Runtime) RuntimeError IOError := do
  let code ← integerArgToCint ops code
  let pfx ← ops.textToString pfx
  let errorText ← ops.uvStrError code
  let errorName ← ops.uvErrorName code
  pure ⟨pfx ++ ": " ++ errorText ++ " (" ++ errorName ++ ")", code⟩

/--
Julia source: base/libuv.jl:104-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _UVError(pfx::AbstractString, code::Integer, sfxs::AbstractString...)
    code = Int32(code)
    IOError(string(pfx, ": ", struverror(code), " (", uverrorname(code), ")", " ", sfxs...), code)
end
```
-/
def uvErrorObjectWithSuffixes {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
(pfx : Text) (code : IntegerArg Integer) (suffixes : List Text) :
    M (World Object IO Runtime) RuntimeError IOError := do
  let code ← integerArgToCint ops code
  let pfx ← ops.textToString pfx
  let errorText ← ops.uvStrError code
  let errorName ← ops.uvErrorName code
  let suffixes ← textListToString ops suffixes
  pure ⟨pfx ++ ": " ++ errorText ++ " (" ++ errorName ++ ") " ++ suffixes, code⟩

/--
Julia source: base/libuv.jl:109-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struverror(err::Int32) = unsafe_string(ccall(:uv_strerror, Cstring, (Int32,), err))
uverrorname(err::Int32) = unsafe_string(ccall(:uv_err_name, Cstring, (Int32,), err))
```
-/
def struvError {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (error : CInt) : M (World Object IO Runtime) RuntimeError String :=
  ops.uvStrError error

def uvErrorName {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (error : CInt) : M (World Object IO Runtime) RuntimeError String :=
  ops.uvErrorName error

/--
Julia source: base/libuv.jl:112-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uv_error(prefix::Symbol, c::Integer) = uv_error(string(prefix), c)
uv_error(prefix::AbstractString, c::Integer) = c < 0 ? _uv_error(prefix, c) : nothing
uv_error(prefix::AbstractString, c::Bool) = error("uv_error: Bool argument is a mistake, pass the raw error code instead")
_uv_error(prefix::AbstractString, c::Integer) = throw(_UVError(prefix, c))
```
-/
def throwUvError {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
(pfx : Text) (code : IntegerArg Integer) : M (World Object IO Runtime) RuntimeError Unit := do
  let error ← uvErrorObject ops pfx code
  throw (.ioError error)

def uvErrorStringBool {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (_ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (_prefix : Text) (_code : Bool) : M (World Object IO Runtime) RuntimeError Unit :=
  throw (.errorException "uv_error: Bool argument is a mistake, pass the raw error code instead")

def uvErrorStringInteger {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
(pfx : Text) (code : Integer) : M (World Object IO Runtime) RuntimeError Unit := do
  if ← ops.integerLessThanZero code then
    throwUvError ops pfx (.integer code)
  else
    pure ()

def uvErrorSymbol {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
(pfx : Sym) (code : IntegerArg Integer) : M (World Object IO Runtime) RuntimeError Unit := do
  let pfx := ops.symbolToText pfx
  match code with
  | .integer value => uvErrorStringInteger ops pfx value
  | .boolean value => uvErrorStringBool ops pfx value


/--
Julia source: base/libuv.jl:117-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## event loop ##

eventloop() = ccall(:jl_global_event_loop, Ptr{Cvoid}, ())
```
-/
def eventLoop {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError) :
    M (World Object IO Runtime) RuntimeError Ptr :=
  ops.eventLoop

/--
Julia source: base/libuv.jl:121-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_unref(h::Ptr{Cvoid})
    iolock_begin()
    ccall(:uv_unref, Cvoid, (Ptr{Cvoid},), h)
    iolock_end()
end
```
-/
def uvUnref {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (handle : Ptr) : M (World Object IO Runtime) RuntimeError Unit := do
  ioLockBegin
  ops.uvUnref handle
  ioLockEnd

/--
Julia source: base/libuv.jl:127-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_ref(h::Ptr{Cvoid})
    iolock_begin()
    ccall(:uv_ref, Cvoid, (Ptr{Cvoid},), h)
    iolock_end()
end
```
-/
def uvRef {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError)
    (handle : Ptr) : M (World Object IO Runtime) RuntimeError Unit := do
  ioLockBegin
  ops.uvRef handle
  ioLockEnd

/--
Julia source: base/libuv.jl:133-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function process_events()
    return ccall(:jl_process_events, Int32, ())
end
```
-/
def processEvents {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError) :
    M (World Object IO Runtime) RuntimeError CInt :=
  ops.processEvents

-- UNTRANSLATED
-- Source: base/libuv.jl:137-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function uv_alloc_buf end
-- function uv_readcb end
-- function uv_writecb_task end
-- function uv_shutdowncb_task end
-- function uv_return_spawn end
-- function uv_asynccb end
-- function uv_timercb end
-- /Source
-- Reason: These generic function declarations contain no method bodies; runtime or client files supply their implementations.

/--
Julia source: base/libuv.jl:148-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reinit_stdio()
    global stdin = init_stdio(ccall(:jl_stdin_stream, Ptr{Cvoid}, ()))::IO
    global stdout = init_stdio(ccall(:jl_stdout_stream, Ptr{Cvoid}, ()))::IO
    global stderr = init_stdio(ccall(:jl_stderr_stream, Ptr{Cvoid}, ()))::IO
    opts = JLOptions()
    color = colored_text(opts)
    if !isnothing(color)
        if !isa(stdout, TTY)
            global stdout = IOContext(stdout, :color => color::Bool)
        end
        if !isa(stderr, TTY)
            global stderr = IOContext(stderr, :color => color::Bool)
        end
    end
    nothing
end
```
-/
def reinitStdioInternal {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError) :
    M (World Object IO Runtime) RuntimeError Unit := do
  let stdinPointer ← ops.stdinStream
  let stdin ← ops.initStdio stdinPointer
  let world ← getWorld
  setWorld { world with stdin := stdin }
  let stdoutPointer ← ops.stdoutStream
  let stdout ← ops.initStdio stdoutPointer
  let world ← getWorld
  setWorld { world with stdout := stdout }
  let stderrPointer ← ops.stderrStream
  let stderr ← ops.initStdio stderrPointer
  let world ← getWorld
  setWorld { world with stderr := stderr }
  let options ← ops.juliaOptions
  let color ← ops.coloredText options
  match color with
  | none => pure ()
  | some color => do
      let world ← getWorld
      if !ops.isTTY world.stdout then
        let stdout ← ops.ioContextColor world.stdout color
        setWorld { world with stdout := stdout }
      let world ← getWorld
      if !ops.isTTY world.stderr then
        let stderr ← ops.ioContextColor world.stderr color
        setWorld { world with stderr := stderr }
      pure ()

/--
Julia source: base/libuv.jl:145-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reinit_stdio() = _reinit_stdio()
# we need this so it can be called by codegen to print errors, even after
# reinit_stdio has been redefined by the juliac build script.
```
-/
def reinitStdio {Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError : Type}
    (ops : Ops Handle Request Integer Object Ptr IO Options Text Runtime RuntimeError) :
    M (World Object IO Runtime) RuntimeError Unit :=
  reinitStdioInternal ops

/--
Julia source: base/libuv.jl:165-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    stdin::IO

Global variable referring to the standard input stream.
"""
:stdin

"""
    stdout::IO

Global variable referring to the standard out stream.
"""
:stdout

"""
    stderr::IO

Global variable referring to the standard error stream.
"""
:stderr
```
-/
def stdioNames : List Sym := ["stdin", "stdout", "stderr"]

end JuliaLean.base.libuv

namespace JuliaLean.Streams

/-! ## `base/libuv.jl` -/

structure HandleDataM where
  associated : Bool
  preserved : Bool
  referenced : Bool
  deriving Repr, DecidableEq

def associateHandle (_ : α) : HandleDataM := ⟨true, false, true⟩
def disassociateHandle (h : HandleDataM) : HandleDataM := { h with associated := false }
def preserveHandle (h : HandleDataM) : HandleDataM := { h with preserved := true }
def unpreserveHandle (h : HandleDataM) : HandleDataM := { h with preserved := false }
def uvRef (h : HandleDataM) : HandleDataM := { h with referenced := true }
def uvUnref (h : HandleDataM) : HandleDataM := { h with referenced := false }

def uvSizeResult (size : Option Nat) : Except StreamErr Nat :=
  match size with | some n => .ok n | none => .error .argumentError

def iolockDepth (depth : Nat) (beginning : Bool) : Nat :=
  if beginning then depth + 1 else depth - 1

def uvErrorResult (code : Int) : Except StreamErr Unit :=
  if code < 0 then .error .ioError else .ok ()

def uvErrorText (pfx name description : String) (code : Int) : String :=
  pfx ++ ": " ++ name ++ " (" ++ description ++ ")" ++ " [" ++ toString code ++ "]"

inductive HandleKind where | file | tty | tcp | pipe | invalid
  deriving Repr, DecidableEq

def reinitStdioKind : HandleKind → Except StreamErr StreamKind
  | .file => .ok .ioStream
  | .tty | .tcp | .pipe => .ok .libuvStream
  | .invalid => .error .argumentError

def initStdioModel (kind : HandleKind) : Except StreamErr StreamKind :=
  reinitStdioKind kind


end JuliaLean.Streams

namespace JuliaLean.Streams.Methods.Libuv

open JuliaLean.Streams

inductive LibuvErr where
  | domain
  | io (message : String) (code : Int)
  | argument (message : String)
  | unbalanced
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except LibuvErr α

structure IOErrorM where
  message : String
  code : Int
  deriving Repr, DecidableEq

structure StdioM where
  input : StreamKind
  output : StreamKind
  error : StreamKind
  outputColorContext : Bool
  errorColorContext : Bool
  deriving Repr, DecidableEq

/-- `uv_sizeof_handle(handle)`, `base/libuv.jl:8-13`. -/
def m8 (handle lower upper size : Int) : Result Int :=
  if !(lower < handle && handle < upper) then .error .domain else .ok size

/-- `uv_sizeof_req(req)`, `base/libuv.jl:15-20`. -/
def m15 (req lower upper size : Int) : Result Int :=
  if !(lower < req && req < upper) then .error .domain else .ok size

/-- `uv_handle_data(handle)`, `base/libuv.jl:29`. -/
def m29 (foreignData : Nat) : Nat := foreignData

/-- `uv_req_data(handle)`, `base/libuv.jl:30`. -/
def m30 (foreignData : Nat) : Nat := foreignData

/-- `uv_req_set_data(req, data)`, `base/libuv.jl:31`. -/
def m31 (data : α) : α := data

/-- `uv_req_set_data(req, data::Ptr{Cvoid})`, `base/libuv.jl:32`. -/
def m32 (data : Nat) : Nat := data

/-- Expansion of `@handle_as hand typ`, `base/libuv.jl:34-40`. -/
def m34 (data : Option α) : Option α :=
  match data with
  | none => none
  | some object => some object

/-- `associate_julia_struct`, `base/libuv.jl:44-50`. -/
def m44 (handleNonNull compiled associated : Bool) : Bool × Bool × Bool :=
  (handleNonNull, compiled, associated)

/-- `disassociate_julia_struct(uv)`, `base/libuv.jl:51`. -/
def m51 (handle : Nat) : Nat := handle

/-- `disassociate_julia_struct(handle::Ptr{Cvoid})`, `base/libuv.jl:52-53`. -/
def m52 (handleNonNull foreignCalled : Bool) : Bool :=
  handleNonNull && foreignCalled

/-- `iolock_begin()`, `base/libuv.jl:55`. -/
def m55 (foreignDepth : Nat) : Nat := foreignDepth

/-- `iolock_end()`, `base/libuv.jl:56`. -/
def m56 (foreignDepth : Nat) : Nat := foreignDepth

/-- `preserve_handle(x)`, `base/libuv.jl:62-68`. -/
def m62 (storedCount : Nat) : Nat := storedCount + 1

/-- `unpreserve_handle(x)`, `base/libuv.jl:69-82`. -/
def m69 (storedCount : Nat) : Result (Option Nat) :=
  if storedCount = 0 then .error .unbalanced
  else if storedCount = 1 then .ok none
  else .ok (some (storedCount - 1))

/-- Inner `IOError` constructor, `base/libuv.jl:89`. -/
def m89 (message : String) (code : Int) : IOErrorM := ⟨message, code⟩

/-- `showerror(io, e::IOError)`, `base/libuv.jl:92-98`. -/
def m92 (e : IOErrorM) (enoent : Int) : String :=
  let base := "IOError: " ++ e.message
  if e.code = enoent && e.message.contains '~' then
    base ++ "\nMany shells expand '~' to the home directory in unquoted strings. To replicate this behavior, call `expanduser` to expand the '~' character to the user’s home directory."
  else base

/-- `_UVError(pfx, code)`, `base/libuv.jl:100-103`. -/
def m100 (pfx description name : String) (code : Int) : IOErrorM :=
  ⟨pfx ++ ": " ++ description ++ " (" ++ name ++ ")", code⟩

/-- `_UVError(pfx, code, sfxs...)`, `base/libuv.jl:104-107`. -/
def m104 (pfx description name suffix : String) (code : Int) : IOErrorM :=
  ⟨pfx ++ ": " ++ description ++ " (" ++ name ++ ") " ++ suffix, code⟩

/-- `struverror(err)`, `base/libuv.jl:109`. -/
def m109 (foreignText : String) : String := foreignText

/-- `uverrorname(err)`, `base/libuv.jl:110`. -/
def m110 (foreignText : String) : String := foreignText

/-- `uv_error(prefix::Symbol, c)`, `base/libuv.jl:112`. -/
def m112 (symbolText : String) (code : Int) : Result Unit :=
  if code < 0 then .error (.io symbolText code) else .ok ()

/-- `uv_error(prefix::AbstractString, c)`, `base/libuv.jl:113`. -/
def m113 (pfx : String) (code : Int) : Result Unit :=
  if code < 0 then .error (.io pfx code) else .ok ()

/-- The rejected Bool overload of `uv_error`, `base/libuv.jl:114`. -/
def m114 (_code : Bool) : Result Unit :=
  .error (.argument "uv_error: Bool argument is a mistake, pass the raw error code instead")

/-- `_uv_error(prefix, c)`, `base/libuv.jl:115`. -/
def m115 (pfx : String) (code : Int) : Result Unit := .error (.io pfx code)

/-- `eventloop()`, `base/libuv.jl:119`. -/
def m119 (foreignLoop : Nat) : Nat := foreignLoop

/-- `uv_unref(h)`, `base/libuv.jl:121-125`. -/
def m121 (h : HandleDataM) : HandleDataM := uvUnref h

/-- `uv_ref(h)`, `base/libuv.jl:127-131`. -/
def m127 (h : HandleDataM) : HandleDataM := uvRef h

/-- `process_events()`, `base/libuv.jl:133-135`. -/
def m133 (foreignResult : Int) : Int := foreignResult

/-- `reinit_stdio()`, `base/libuv.jl:145`. -/
def m145 (result : StdioM) : StdioM := result

/-- `_reinit_stdio()`, `base/libuv.jl:148-163`. -/
def m148 (input output error : StreamKind) (color : Option Bool)
    (outputIsTTY errorIsTTY : Bool) : StdioM :=
  { input, output, error,
    outputColorContext := color.isSome && !outputIsTTY,
    errorColorContext := color.isSome && !errorIsTTY }


end JuliaLean.Streams.Methods.Libuv
