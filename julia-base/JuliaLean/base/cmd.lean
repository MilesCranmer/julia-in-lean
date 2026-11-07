import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.io
import JuliaLean.base.shell
import JuliaLean.base.generator

/-!
# Model of `base/cmd.jl`

Source-mirrored command records, redirections and interpolation at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Argument, environment and CPU vectors
are references supplied by the chosen heap; constructing a Cmd retains the
argument-vector reference. String conversion, field conversion, iteration and
user-defined dispatch are typed callees. Computations retain their world on
errors and represent divergence by none, through base.io.M.
-/
namespace JuliaLean.base.cmd
open JuliaLean
abbrev I := JInt .i64
abbrev U32 := JInt .u32
abbrev M := JuliaLean.base.io.M
abbrev Error := JuliaLean.base.io.Error

def i (value : Int) : I := JInt.wrap .i64 value
def u32 (value : Int) : U32 := JInt.wrap .u32 value

def liftResult (value : Except Error A) : M W A :=
  match value with
  | .ok value => pure value
  | .error error => throwThe Error error

/-- A field's existing-type check, selected convert method, and final new-field
check. Conversion can return a value of another type; that check is delayed
until new constructs the record, after all field expressions were evaluated. -/
structure FieldCast (W Input Raw Output : Type) where
  existing : Input → Option Output
  convert : Input → M W Raw
  assertResult : Raw → Except Error Output
inductive Prepared (Output Raw : Type) where
  | existing (value : Output)
  | converted (value : Raw)
def prepare (cast : FieldCast W Input Raw Output) (value : Input) :
    M W (Prepared Output Raw) := do
  match cast.existing value with
  | some value => pure (.existing value)
  | none => pure (.converted (← cast.convert value))
def finish (cast : FieldCast W Input Raw Output) : Prepared Output Raw → M W Output
  | .existing value => pure value
  | .converted value => liftResult (cast.assertResult value)

def foreach (iterate : A → Option State → M W (Option (B × State)))
    (body : B → M W Unit) (source : A) : M W Unit :=
  JuliaLean.base.io.whileLoop (fun state => do
    match ← iterate source state with
    | none => pure (.inl ())
    | some (value,next) => body value; pure (.inr (some next))) none

structure Vectors (W Vec S : Type) where
  empty : M W Vec
  singleton : S → M W Vec
  push : Vec → S → M W Unit
  append : Vec → Vec → M W Unit

variable {W Vec S Cpu Handle Custom A B C D E F G U V R RB RF RE RC RU RG State : Type}


/--
Julia source: base/cmd.jl:6-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const UV_PROCESS_WINDOWS_VERBATIM_ARGUMENTS = UInt32(1 << 2)
const UV_PROCESS_DETACHED = UInt32(1 << 3)
const UV_PROCESS_WINDOWS_HIDE = UInt32(1 << 4)
const UV_PROCESS_SETUID = UInt32(1 << 5)
const UV_PROCESS_SETGID = UInt32(1 << 6)
const UV_PROCESS_WINDOWS_DISABLE_EXACT_NAME = UInt32(1 << 7)
```
-/
def windowsVerbatim : U32 := u32 (2^2)
def detached : U32 := u32 (2^3)
def windowsHide : U32 := u32 (2^4)
def processSetuid : U32 := u32 (2^5)
def processSetgid : U32 := u32 (2^6)
def windowsDisableExactName : U32 := u32 (2^7)

/--
Julia source: base/cmd.jl:13-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Cmd <: AbstractCmd
    exec::Vector{String}
    ignorestatus::Bool
    flags::UInt32 # libuv process flags
    env::Union{Vector{String},Nothing}
    dir::String
    cpus::Union{Nothing,Vector{UInt16}}
    uid::Union{Nothing,UInt32}
    gid::Union{Nothing,UInt32}
    Cmd(exec::Vector{<:AbstractString}) =
        new(exec, false, 0x00, nothing, "", nothing, nothing, nothing)
    Cmd(cmd::Cmd, ignorestatus, flags, env, dir, cpus = nothing, uid = nothing, gid = nothing) =
        new(cmd.exec, ignorestatus, flags, env,
            dir === cmd.dir ? dir : cstr(dir), cpus, uid, gid)
    function Cmd(cmd::Cmd; ignorestatus::Bool=cmd.ignorestatus, env=cmd.env, dir::AbstractString=cmd.dir,
                 cpus::Union{Nothing,Vector{UInt16}} = cmd.cpus,
                 uid::Union{Nothing,UInt32} = cmd.uid,
                 gid::Union{Nothing,UInt32} = cmd.gid,
                 detach::Bool = 0 != cmd.flags & UV_PROCESS_DETACHED,
                 windows_verbatim::Bool = 0 != cmd.flags & UV_PROCESS_WINDOWS_VERBATIM_ARGUMENTS,
                 windows_hide::Bool = 0 != cmd.flags & UV_PROCESS_WINDOWS_HIDE)
        flags = detach * UV_PROCESS_DETACHED |
                windows_verbatim * UV_PROCESS_WINDOWS_VERBATIM_ARGUMENTS |
                windows_hide * UV_PROCESS_WINDOWS_HIDE
        new(cmd.exec, ignorestatus, flags, byteenv(env),
            dir === cmd.dir ? dir : cstr(dir), cpus, uid, gid)
    end
end
```
-/
structure Cmd (Vec S Cpu : Type) where
  exec : Vec
  ignorestatus : Bool
  flags : U32
  env : Option Vec
  dir : S
  cpus : Option Cpu
  uid : Option U32
  gid : Option U32

/--
Julia source: base/cmd.jl:22-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Cmd(exec::Vector{<:AbstractString}) =
        new(exec, false, 0x00, nothing, "", nothing, nothing, nothing)
```
-/
def cmdExec (empty : S) (cast : FieldCast W A R Vec) (exec : A) : M W (Cmd Vec S Cpu) := do
  let exec ← prepare cast exec
  let exec ← finish cast exec
  pure ⟨exec,false,u32 0,none,empty,none,none,none⟩

/--
Julia source: base/cmd.jl:24-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Cmd(cmd::Cmd, ignorestatus, flags, env, dir, cpus = nothing, uid = nothing, gid = nothing) =
        new(cmd.exec, ignorestatus, flags, env,
            dir === cmd.dir ? dir : cstr(dir), cpus, uid, gid)
```
-/
def cmdCopy
    (boolean : FieldCast W B RB Bool) (flag : FieldCast W F RF U32)
    (environment : FieldCast W E RE (Option Vec)) (cpu : FieldCast W C RC (Option Cpu))
    (user : FieldCast W U RU (Option U32)) (group : FieldCast W G RG (Option U32))
    (sameDirectory : D → S → Bool) (cstr : D → M W S)
    (command : Cmd Vec S Cpu) (ignorestatus : B) (flags : F) (env : E) (dir : D)
    (cpus : C) (uid : U) (gid : G) : M W (Cmd Vec S Cpu) := do
  let ignorestatus ← prepare boolean ignorestatus
  let flags ← prepare flag flags
  let env ← prepare environment env
  let dir ← if sameDirectory dir command.dir then pure command.dir else cstr dir
  let cpus ← prepare cpu cpus
  let uid ← prepare user uid
  let gid ← prepare group gid
  let ignorestatus ← finish boolean ignorestatus
  let flags ← finish flag flags
  let env ← finish environment env
  let cpus ← finish cpu cpus
  let uid ← finish user uid
  let gid ← finish group gid
  pure ⟨command.exec,ignorestatus,flags,env,dir,cpus,uid,gid⟩

/--
Julia source: base/cmd.jl:27-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Cmd(cmd::Cmd; ignorestatus::Bool=cmd.ignorestatus, env=cmd.env, dir::AbstractString=cmd.dir,
                 cpus::Union{Nothing,Vector{UInt16}} = cmd.cpus,
                 uid::Union{Nothing,UInt32} = cmd.uid,
                 gid::Union{Nothing,UInt32} = cmd.gid,
                 detach::Bool = 0 != cmd.flags & UV_PROCESS_DETACHED,
                 windows_verbatim::Bool = 0 != cmd.flags & UV_PROCESS_WINDOWS_VERBATIM_ARGUMENTS,
                 windows_hide::Bool = 0 != cmd.flags & UV_PROCESS_WINDOWS_HIDE)
        flags = detach * UV_PROCESS_DETACHED |
                windows_verbatim * UV_PROCESS_WINDOWS_VERBATIM_ARGUMENTS |
                windows_hide * UV_PROCESS_WINDOWS_HIDE
        new(cmd.exec, ignorestatus, flags, byteenv(env),
            dir === cmd.dir ? dir : cstr(dir), cpus, uid, gid)
    end
```
-/
def cmdKeyword
    (byteenv : E → M W A) (environment : FieldCast W A R (Option Vec))
    (sameDirectory : D → S → Bool) (cstr : D → M W S)
    (command : Cmd Vec S Cpu) (ignorestatus : Bool) (env : E) (dir : D)
    (cpus : Option Cpu) (uid gid : Option U32)
    (detach verbatim hide : Bool) : M W (Cmd Vec S Cpu) := do
  let flags := JuliaLean.base.int.bor
    (JuliaLean.base.int.bor (JuliaLean.base.int.mulBool detach detached)
      (JuliaLean.base.int.mulBool verbatim windowsVerbatim))
    (JuliaLean.base.int.mulBool hide windowsHide)
  let env ← prepare environment (← byteenv env)
  let dir ← if sameDirectory dir command.dir then pure command.dir else cstr dir
  let env ← finish environment env
  pure ⟨command.exec,ignorestatus,flags,env,dir,cpus,uid,gid⟩

/-- Default keyword expressions, evaluated from the current immutable record. -/
def defaultDetach (command : Cmd Vec S Cpu) : Bool :=
  !(JuliaLean.base.int.eq (JuliaLean.base.int.band command.flags detached) (u32 0))
def defaultVerbatim (command : Cmd Vec S Cpu) : Bool :=
  !(JuliaLean.base.int.eq (JuliaLean.base.int.band command.flags windowsVerbatim) (u32 0))
def defaultHide (command : Cmd Vec S Cpu) : Bool :=
  !(JuliaLean.base.int.eq (JuliaLean.base.int.band command.flags windowsHide) (u32 0))

/--
Julia source: base/cmd.jl:42-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_nondefault_cmd_flags(c::Cmd) =
    c.ignorestatus ||
    c.flags != 0x00 ||
    c.env !== nothing ||
    c.dir !== "" ||
    c.cpus !== nothing ||
    c.uid !== nothing ||
    c.gid !== nothing
```
-/
def hasNondefaultCmdFlags (sameEmpty : S → Bool) (command : Cmd Vec S Cpu) : Bool :=
  command.ignorestatus || !(JuliaLean.base.int.eq command.flags (u32 0)) ||
  command.env.isSome || !sameEmpty command.dir || command.cpus.isSome ||
  command.uid.isSome || command.gid.isSome

/--
Julia source: base/cmd.jl:103-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct OrCmds <: AbstractCmd
    a::AbstractCmd
    b::AbstractCmd
    OrCmds(a::AbstractCmd, b::AbstractCmd) = new(a, b)
end

struct ErrOrCmds <: AbstractCmd
    a::AbstractCmd
    b::AbstractCmd
    ErrOrCmds(a::AbstractCmd, b::AbstractCmd) = new(a, b)
end

struct AndCmds <: AbstractCmd
    a::AbstractCmd
    b::AbstractCmd
    AndCmds(a::AbstractCmd, b::AbstractCmd) = new(a, b)
end
```
-/
inductive Command (Vec S Cpu Handle Custom : Type) where
  | cmd (value : Cmd Vec S Cpu)
  | orCmds (a b : Command Vec S Cpu Handle Custom)
  | errOrCmds (a b : Command Vec S Cpu Handle Custom)
  | andCmds (a b : Command Vec S Cpu Handle Custom)
  | redirect (command : Command Vec S Cpu Handle Custom) (handle : Handle)
      (stream : I) (readable : Bool)
  | custom (value : Custom)

/--
Julia source: base/cmd.jl:242-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const STDIN_NO  = 0
const STDOUT_NO = 1
const STDERR_NO = 2
```
-/
def stdinNo : I := i 0
def stdoutNo : I := i 1
def stderrNo : I := i 2

/--
Julia source: base/cmd.jl:246-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct FileRedirect
    filename::String
    append::Bool
    FileRedirect(filename::AbstractString, append::Bool) = FileRedirect(convert(String, filename), append)
    function FileRedirect(filename::String, append::Bool)
        if lowercase(filename) == (@static Sys.iswindows() ? "nul" : "/dev/null")
            @warn "For portability use devnull instead of a file redirect" maxlog=1
        end
        return new(filename, append)
    end
end
```
-/
structure FileRedirect (S : Type) where
  filename : S
  append : Bool

def fileRedirectString (lowercase : S → M W S) (equal : S → S → M W Bool)
    (literal : String → S) (warn : String → M W Unit) (windows : Bool)
    (filename : S) (append : Bool) : M W (FileRedirect S) := do
  if ← equal (← lowercase filename) (literal (if windows then "nul" else "/dev/null")) then
    warn "For portability use devnull instead of a file redirect"
  pure ⟨filename,append⟩

def fileRedirectAbstract (convert : A → M W S)
    (lowercase : S → M W S) (equal : S → S → M W Bool)
    (literal : String → S) (warn : String → M W Unit) (windows : Bool)
    (filename : A) (append : Bool) : M W (FileRedirect S) := do
  fileRedirectString lowercase equal literal warn windows (← convert filename) append

/--
Julia source: base/cmd.jl:270-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct CmdRedirect <: AbstractCmd
    cmd::AbstractCmd
    handle::Redirectable
    stream_no::Int
    readable::Bool
end
CmdRedirect(cmd, handle, stream_no) = CmdRedirect(cmd, handle, stream_no, stream_no == STDIN_NO)
```
-/
def cmdRedirect (command : Command Vec S Cpu Handle Custom) (handle : Handle)
    (stream : I) : Command Vec S Cpu Handle Custom :=
  .redirect command handle stream (JuliaLean.base.int.eq stream stdinNo)

/--
Julia source: base/cmd.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ignorestatus(cmd::Cmd) = Cmd(cmd, ignorestatus=true)
```
-/
def ignorestatusCmd (byteenv : Option Vec → M W A)
    (environment : FieldCast W A R (Option Vec)) (same : S → S → Bool)
    (cstr : S → M W S) (command : Cmd Vec S Cpu) : M W (Cmd Vec S Cpu) :=
  cmdKeyword byteenv environment same cstr command true command.env command.dir
    command.cpus command.uid command.gid (defaultDetach command)
    (defaultVerbatim command) (defaultHide command)

/--
Julia source: base/cmd.jl:302-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ignorestatus(cmd::Union{OrCmds,AndCmds}) =
    typeof(cmd)(ignorestatus(cmd.a), ignorestatus(cmd.b))
ignorestatus(cmd::CmdRedirect) =
    CmdRedirect(ignorestatus(cmd.cmd), cmd.handle, cmd.stream_no, cmd.readable)
```
-/
def ignorestatus (leaf : Cmd Vec S Cpu → M W (Cmd Vec S Cpu))
    (other : Command Vec S Cpu Handle Custom → M W (Command Vec S Cpu Handle Custom)) :
    Command Vec S Cpu Handle Custom → M W (Command Vec S Cpu Handle Custom)
  | .cmd command => return .cmd (← leaf command)
  | .orCmds a b => return .orCmds (← ignorestatus leaf other a) (← ignorestatus leaf other b)
  | .andCmds a b => return .andCmds (← ignorestatus leaf other a) (← ignorestatus leaf other b)
  | .redirect command handle stream readable =>
      return .redirect (← ignorestatus leaf other command) handle stream readable
  | command => other command

/--
Julia source: base/cmd.jl:312-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
detach(cmd::Cmd) = Cmd(cmd; detach=true)
```
-/
def detachCmd (byteenv : Option Vec → M W A)
    (environment : FieldCast W A R (Option Vec)) (same : S → S → Bool)
    (cstr : S → M W S) (command : Cmd Vec S Cpu) : M W (Cmd Vec S Cpu) :=
  cmdKeyword byteenv environment same cstr command command.ignorestatus command.env command.dir
    command.cpus command.uid command.gid true (defaultVerbatim command) (defaultHide command)

/--
Julia source: base/cmd.jl:316-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cstr(s)
    if Base.containsnul(s)
        throw(ArgumentError("strings containing NUL cannot be passed to spawned processes"))
    end
    return String(s)::String
end
```
-/
def cstr (containsnul : A → M W Bool) (string : A → M W R)
    (assertString : R → Except Error S) (value : A) : M W S := do
  if ← containsnul value then
    throwThe Error (.jl (.argumentError "strings containing NUL cannot be passed to spawned processes"))
  liftResult (assertString (← string value))

/--
Julia source: base/cmd.jl:324-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
byteenv(env::AbstractArray{<:AbstractString}) =
    String[cstr(x) for x in env]
```
-/
def byteenvArray
    (collectString : JuliaLean.base.generator.Generator A (B → M W S) → M W R)
    (cstr : B → M W S) (env : A) : M W R :=
  collectString ⟨cstr,env⟩

/--
Julia source: base/cmd.jl:326-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
byteenv(env::AbstractDict) =
    String[cstr(string(k)*"="*string(v)) for (k,v) in env]
```
-/
def byteenvDict
    (collectString : JuliaLean.base.generator.Generator A ((B × C) → M W S) → M W R)
    (keyString : B → M W S) (valueString : C → M W S)
    (concat : S → S → M W S) (equals : S) (cstr : S → M W S)
    (env : A) : M W R :=
  collectString ⟨(fun (key,value) => do
    let entry ← concat (← concat (← keyString key) equals) (← valueString value)
    cstr entry),env⟩

/--
Julia source: base/cmd.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
byteenv(env::Nothing) = nothing
```
-/
def byteenvNothing : Option Vec := none

/--
Julia source: base/cmd.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
byteenv(env::Union{AbstractVector{<:Pair{<:AbstractString}}, Tuple{Vararg{Pair{<:AbstractString}}}}) =
    String[cstr(k*"="*string(v)) for (k,v) in env]
```
-/
def byteenvPairs
    (collectString : JuliaLean.base.generator.Generator A ((S × B) → M W S) → M W R)
    (string : B → M W S) (concat : S → S → M W S) (equals : S)
    (cstr : S → M W S) (env : A) : M W R :=
  collectString ⟨(fun (key,value) => do
    let entry ← concat (← concat key equals) (← string value)
    cstr entry),env⟩

/--
Julia source: base/cmd.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setenv(cmd::Cmd, env; dir=cmd.dir) = Cmd(cmd; env=byteenv(env), dir=dir)
```
-/
def setenv (byteenv : E → M W A) (byteenvAgain : A → M W B)
    (environment : FieldCast W B R (Option Vec)) (same : D → S → Bool)
    (cstr : D → M W S) (command : Cmd Vec S Cpu) (env : E) (dir : D) :
    M W (Cmd Vec S Cpu) := do
  let env ← byteenv env
  cmdKeyword byteenvAgain environment same cstr command command.ignorestatus env dir
    command.cpus command.uid command.gid (defaultDetach command)
    (defaultVerbatim command) (defaultHide command)

/--
Julia source: base/cmd.jl:359-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setenv(cmd::Cmd, env::Pair{<:AbstractString}...; dir=cmd.dir) =
    setenv(cmd, env; dir=dir)
```
-/
def setenvPairs (setenv : Cmd Vec S Cpu → A → D → M W (Cmd Vec S Cpu))
    (command : Cmd Vec S Cpu) (pairs : A) (dir : D) : M W (Cmd Vec S Cpu) :=
  setenv command pairs dir

/--
Julia source: base/cmd.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setenv(cmd::Cmd; dir=cmd.dir) = Cmd(cmd; dir=dir)
```
-/
def setDirectory (byteenv : Option Vec → M W A)
    (environment : FieldCast W A R (Option Vec)) (same : D → S → Bool)
    (cstr : D → M W S) (command : Cmd Vec S Cpu) (dir : D) : M W (Cmd Vec S Cpu) :=
  cmdKeyword byteenv environment same cstr command command.ignorestatus command.env dir
    command.cpus command.uid command.gid (defaultDetach command)
    (defaultVerbatim command) (defaultHide command)

/--
Julia source: base/cmd.jl:364-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splitenv(e::String)
    i = findnext('=', e, 2)
    if i === nothing
        throw(ArgumentError("malformed environment entry"))
    end
    e[1:prevind(e, i)], e[nextind(e, i):end]
end
```
-/
def splitenv (findnext : S → Char → I → M W (Option I))
    (prevind nextind : S → I → M W I) (slice : S → I → Option I → M W S)
    (entry : S) : M W (S × S) := do
  let position ← findnext entry '=' (i 2)
  match position with
  | none => throwThe Error (.jl (.argumentError "malformed environment entry"))
  | some position =>
      let key ← slice entry (i 1) (some (← prevind entry position))
      let value ← slice entry (← nextind entry position) none
      pure (key,value)

/--
Julia source: base/cmd.jl:444-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setcpuaffinity(cmd::Cmd, ::Nothing) = Cmd(cmd; cpus = nothing)
```
-/
def setcpuaffinityNothing (constructor : Cmd Vec S Cpu → Option Cpu → M W (Cmd Vec S Cpu))
    (command : Cmd Vec S Cpu) : M W (Cmd Vec S Cpu) := do
  constructor command (none)

/--
Julia source: base/cmd.jl:445-445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setcpuaffinity(cmd::Cmd, cpus) = Cmd(cmd; cpus = collect(UInt16, cpus))
```
-/
def setcpuaffinity (constructor : Cmd Vec S Cpu → Option Cpu → M W (Cmd Vec S Cpu))
    (command : Cmd Vec S Cpu) (collect : A → M W Cpu) (cpus : A) : M W (Cmd Vec S Cpu) := do
  constructor command (some (← collect cpus))

/--
Julia source: base/cmd.jl:468-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setuid(cmd::Cmd, ::Nothing) = Cmd(cmd; uid = nothing)
```
-/
def setuidNothing (constructor : Cmd Vec S Cpu → Option U32 → M W (Cmd Vec S Cpu))
    (command : Cmd Vec S Cpu) : M W (Cmd Vec S Cpu) := do
  constructor command (none)

/--
Julia source: base/cmd.jl:469-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setuid(cmd::Cmd, uid::Integer) = Cmd(cmd; uid = UInt32(uid))
```
-/
def setuid (constructor : Cmd Vec S Cpu → Option U32 → M W (Cmd Vec S Cpu))
    (command : Cmd Vec S Cpu) (convert : A → M W U32) (uid : A) : M W (Cmd Vec S Cpu) := do
  constructor command (some (← convert uid))

/--
Julia source: base/cmd.jl:492-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setgid(cmd::Cmd, ::Nothing) = Cmd(cmd; gid = nothing)
```
-/
def setgidNothing (constructor : Cmd Vec S Cpu → Option U32 → M W (Cmd Vec S Cpu))
    (command : Cmd Vec S Cpu) : M W (Cmd Vec S Cpu) := do
  constructor command (none)

/--
Julia source: base/cmd.jl:493-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setgid(cmd::Cmd, gid::Integer) = Cmd(cmd; gid = UInt32(gid))
```
-/
def setgid (constructor : Cmd Vec S Cpu → Option U32 → M W (Cmd Vec S Cpu))
    (command : Cmd Vec S Cpu) (convert : A → M W U32) (gid : A) : M W (Cmd Vec S Cpu) := do
  constructor command (some (← convert gid))

/--
Julia source: base/cmd.jl:495-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(&)(left::AbstractCmd, right::AbstractCmd) = AndCmds(left, right)
```
-/
def andCmds (a b : Command Vec S Cpu Handle Custom) : Command Vec S Cpu Handle Custom :=
  .andCmds a b

/--
Julia source: base/cmd.jl:496-496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_out(src::AbstractCmd, dest::AbstractCmd) = OrCmds(src, dest)
```
-/
def redirOutCommands (a b : Command Vec S Cpu Handle Custom) : Command Vec S Cpu Handle Custom :=
  .orCmds a b

/--
Julia source: base/cmd.jl:497-497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_err(src::AbstractCmd, dest::AbstractCmd) = ErrOrCmds(src, dest)
```
-/
def redirErrCommands (a b : Command Vec S Cpu Handle Custom) : Command Vec S Cpu Handle Custom :=
  .errOrCmds a b

/--
Julia source: base/cmd.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_out(dest::Redirectable, src::AbstractCmd) = CmdRedirect(src, dest, STDIN_NO)
```
-/
def redirIn (handle : Handle) (command : Command Vec S Cpu Handle Custom) :
    Command Vec S Cpu Handle Custom := cmdRedirect command handle stdinNo

/--
Julia source: base/cmd.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_out(src::AbstractCmd, dest::Redirectable) = CmdRedirect(src, dest, STDOUT_NO)
```
-/
def redirOut (command : Command Vec S Cpu Handle Custom) (handle : Handle) :
    Command Vec S Cpu Handle Custom := cmdRedirect command handle stdoutNo

/--
Julia source: base/cmd.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_err(src::AbstractCmd, dest::Redirectable) = CmdRedirect(src, dest, STDERR_NO)
```
-/
def redirErr (command : Command Vec S Cpu Handle Custom) (handle : Handle) :
    Command Vec S Cpu Handle Custom := cmdRedirect command handle stderrNo

/--
Julia source: base/cmd.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_out(src::AbstractCmd, dest::AbstractString) = CmdRedirect(src, FileRedirect(dest, false), STDOUT_NO)
```
-/
def redirOutFile (fileRedirect : A → Bool → M W (FileRedirect S))
    (fileHandle : FileRedirect S → Handle) (command : Command Vec S Cpu Handle Custom) (filename : A) :
    M W (Command Vec S Cpu Handle Custom) := do
  pure (cmdRedirect command (fileHandle (← fileRedirect filename false)) stdoutNo)

/--
Julia source: base/cmd.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_out(src::AbstractString, dest::AbstractCmd) = CmdRedirect(dest, FileRedirect(src, false), STDIN_NO)
```
-/
def redirInFile (fileRedirect : A → Bool → M W (FileRedirect S))
    (fileHandle : FileRedirect S → Handle) (filename : A) (command : Command Vec S Cpu Handle Custom) :
    M W (Command Vec S Cpu Handle Custom) := do
  pure (cmdRedirect command (fileHandle (← fileRedirect filename false)) stdinNo)

/--
Julia source: base/cmd.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_err(src::AbstractCmd, dest::AbstractString) = CmdRedirect(src, FileRedirect(dest, false), STDERR_NO)
```
-/
def redirErrFile (fileRedirect : A → Bool → M W (FileRedirect S))
    (fileHandle : FileRedirect S → Handle) (command : Command Vec S Cpu Handle Custom) (filename : A) :
    M W (Command Vec S Cpu Handle Custom) := do
  pure (cmdRedirect command (fileHandle (← fileRedirect filename false)) stderrNo)

/--
Julia source: base/cmd.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_out_append(src::AbstractCmd, dest::AbstractString) = CmdRedirect(src, FileRedirect(dest, true), STDOUT_NO)
```
-/
def redirOutAppend (fileRedirect : A → Bool → M W (FileRedirect S))
    (fileHandle : FileRedirect S → Handle) (command : Command Vec S Cpu Handle Custom) (filename : A) :
    M W (Command Vec S Cpu Handle Custom) := do
  pure (cmdRedirect command (fileHandle (← fileRedirect filename true)) stdoutNo)

/--
Julia source: base/cmd.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
redir_err_append(src::AbstractCmd, dest::AbstractString) = CmdRedirect(src, FileRedirect(dest, true), STDERR_NO)
```
-/
def redirErrAppend (fileRedirect : A → Bool → M W (FileRedirect S))
    (fileHandle : FileRedirect S → Handle) (command : Command Vec S Cpu Handle Custom) (filename : A) :
    M W (Command Vec S Cpu Handle Custom) := do
  pure (cmdRedirect command (fileHandle (← fileRedirect filename true)) stderrNo)

/--
Julia source: base/cmd.jl:527-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pipeline(cmd::AbstractCmd; stdin=nothing, stdout=nothing, stderr=nothing, append::Bool=false)
    if append && stdout === nothing && stderr === nothing
        throw(ArgumentError("append set to true, but no output redirections specified"))
    end
    if stdin !== nothing
        cmd = redir_out(stdin, cmd)
    end
    if stdout !== nothing
        cmd = append ? redir_out_append(cmd, stdout) : redir_out(cmd, stdout)
    end
    if stderr !== nothing
        cmd = append ? redir_err_append(cmd, stderr) : redir_err(cmd, stderr)
    end
    return cmd
end
```
-/
def pipeline (redirectInput : A → C → M W C)
    (redirectOutput redirectOutputAppend : C → B → M W C)
    (redirectError redirectErrorAppend : C → D → M W C)
    (command : C) (stdin : Option A) (stdout : Option B) (stderr : Option D)
    (append : Bool := false) : M W C := do
  if append && stdout.isNone && stderr.isNone then
    throwThe Error (.jl (.argumentError "append set to true, but no output redirections specified"))
  let command ← match stdin with
    | none => pure command
    | some input => redirectInput input command
  let command ← match stdout with
    | none => pure command
    | some output => if append then redirectOutputAppend command output else redirectOutput command output
  let command ← match stderr with
    | none => pure command
    | some error => if append then redirectErrorAppend command error else redirectError command error
  pure command

/--
Julia source: base/cmd.jl:543-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipeline(cmd::AbstractCmd, dest::Union{AbstractCmd, AbstractString, Redirectable}) = pipeline(cmd, stdout=dest)
```
-/
def pipelineOutput (pipeline : C → B → M W C) (command : C) (destination : B) : M W C :=
  pipeline command destination

/--
Julia source: base/cmd.jl:544-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipeline(src::Union{Redirectable,AbstractString}, cmd::AbstractCmd) = pipeline(cmd, stdin=src)
```
-/
def pipelineInput (pipeline : C → A → M W C) (source : A) (command : C) : M W C :=
  pipeline command source

/--
Julia source: base/cmd.jl:556-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipeline(cmd::AbstractCmd, redir::Pair{<:Integer, <:Redirectable}) = CmdRedirect(cmd, redir.second, Int(redir.first))
```
-/
def pipelineDescriptor (toInt : A → M W I) (command : Command Vec S Cpu Handle Custom)
    (redirect : A × Handle) : M W (Command Vec S Cpu Handle Custom) := do
  pure (cmdRedirect command redirect.2 (← toInt redirect.1))

/--
Julia source: base/cmd.jl:576-576 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipeline(a, b, c, d...) = pipeline(pipeline(a, b), c, d...)
```
-/
def pipelineMany (first : A → B → M W C) (rest : C → D → E → M W F)
    (a : A) (b : B) (c : D) (remaining : E) : M W F := do
  rest (← first a b) c remaining

/--
Julia source: base/cmd.jl:581-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmd_interpolate(xs...) = cstr(string(map(cmd_interpolate1, xs)...))
```
-/
def cmdInterpolate (map : (A → M W B) → Args → M W Mapped)
    (interpolate1 : A → M W B) (string : Mapped → M W C)
    (cstr : C → M W S) (arguments : Args) : M W S := do
  cstr (← string (← map interpolate1 arguments))

/--
Julia source: base/cmd.jl:582-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmd_interpolate1(x) = x
```
-/
def cmdInterpolate1 (value : A) : A := value

/--
Julia source: base/cmd.jl:583-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmd_interpolate1(::Nothing) = throw(ArgumentError("`nothing` can not be interpolated into commands (`Cmd`)"))
```
-/
def cmdInterpolateNothing : M W A :=
  throwThe Error (.jl (.argumentError "`nothing` can not be interpolated into commands (`Cmd`)"))

/--
Julia source: base/cmd.jl:585-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmd_redirect_target(x::Redirectable) = x
```
-/
def cmdRedirectTarget (handle : Handle) : Handle := handle

/--
Julia source: base/cmd.jl:586-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmd_redirect_target(x) = cmd_interpolate(x)
```
-/
def cmdRedirectTargetGeneric (interpolate : A → M W S) (value : A) : M W S :=
  interpolate value

/--
Julia source: base/cmd.jl:588-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
arg_gen() = String[]
```
-/
def argGenEmpty (vectors : Vectors W Vec S) : M W Vec := vectors.empty

/--
Julia source: base/cmd.jl:589-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
arg_gen(x::AbstractString) = String[cstr(x)]
```
-/
def argGenString (vectors : Vectors W Vec S) (cstr : A → M W S) (value : A) : M W Vec := do
  vectors.singleton (← cstr value)

/--
Julia source: base/cmd.jl:590-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function arg_gen(cmd::Cmd)
    if has_nondefault_cmd_flags(cmd)
        throw(ArgumentError("Non-default environment behavior is only permitted for the first interpolant."))
    end
    cmd.exec
end
```
-/
def argGenCmd (sameEmpty : S → Bool) (command : Cmd Vec S Cpu) : M W Vec := do
  if hasNondefaultCmdFlags sameEmpty command then
    throwThe Error (.jl (.argumentError "Non-default environment behavior is only permitted for the first interpolant."))
  pure command.exec

/--
Julia source: base/cmd.jl:597-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function arg_gen(head)
    if isiterable(typeof(head))
        vals = String[]
        for x in head
            push!(vals, cmd_interpolate(x))
        end
        return vals
    else
        return String[cmd_interpolate(head)]
    end
end
```
-/
def argGenGeneric (vectors : Vectors W Vec S) (typeof : A → TypeRep)
    (isiterable : TypeRep → M W Bool)
    (iterate : A → Option State → M W (Option (B × State)))
    (elementInterpolate : B → M W S) (headInterpolate : A → M W S) (head : A) : M W Vec := do
  if ← isiterable (typeof head) then
    let values ← vectors.empty
    foreach iterate (fun value => do vectors.push values (← elementInterpolate value)) head
    pure values
  else vectors.singleton (← headInterpolate head)

/--
Julia source: base/cmd.jl:609-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function arg_gen(head, tail...)
    head = arg_gen(head)
    tail = arg_gen(tail...)
    vals = String[]
    for h = head, t = tail
        push!(vals, cmd_interpolate(h,t))
    end
    return vals
end
```
-/
def argGenMany (vectors : Vectors W Vec S) (headGen : A → M W Vec)
    (tailGen : B → M W Vec) (iterate : Vec → Option State → M W (Option (S × State)))
    (interpolate : S → S → M W S) (head : A) (tail : B) : M W Vec := do
  let head ← headGen head
  let tail ← tailGen tail
  let values ← vectors.empty
  foreach iterate (fun h =>
    foreach iterate (fun t => do vectors.push values (← interpolate h t)) tail) head
  pure values

/--
Julia source: base/cmd.jl:619-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmd_gen(parsed)
    args = String[]
    if length(parsed) >= 1 && isa(parsed[1], Tuple{Cmd})
        cmd = (parsed[1]::Tuple{Cmd})[1]
        (ignorestatus, flags, env, dir, cpus, uid, gid) = (cmd.ignorestatus, cmd.flags, cmd.env, cmd.dir, cmd.cpus, cmd.uid, cmd.gid)
        append!(args, cmd.exec)
        for arg in tail(parsed)
            append!(args, Base.invokelatest(arg_gen, arg...)::Vector{String})
        end
        return Cmd(Cmd(args), ignorestatus, flags, env, dir, cpus, uid, gid)
    else
        for arg in parsed
            append!(args, arg_gen(arg...)::Vector{String})
        end
        return Cmd(args)
    end
end
```
-/
def cmdGen (vectors : Vectors W Vec S)
    (length : Parsed → M W L) (atLeastOne : L → M W Bool)
    (first : Parsed → M W Word) (isTupleCmd : Word → Bool)
    (assertTupleCmd : Word → M W (Cmd Vec S Cpu))
    (tail : Parsed → M W Tail)
    (iterate : Parsed → Option State → M W (Option (Word × State)))
    (iterateTail : Tail → Option TailState → M W (Option (Word × TailState)))
    (argGen latestArgGen : Word → M W Raw)
    (assertVector : Raw → Except Error Vec)
    (makeCmd : Vec → M W (Cmd Vec S Cpu))
    (copyCmd : Cmd Vec S Cpu → Bool → U32 → Option Vec → S →
      Option Cpu → Option U32 → Option U32 → M W (Cmd Vec S Cpu))
    (parsed : Parsed) : M W (Cmd Vec S Cpu) := do
  let args ← vectors.empty
  let inherited ← if ← atLeastOne (← length parsed) then pure (isTupleCmd (← first parsed)) else pure false
  if inherited then
    let command ← assertTupleCmd (← first parsed)
    vectors.append args command.exec
    let rest ← tail parsed
    foreach iterateTail (fun word => do
      vectors.append args (← liftResult (assertVector (← latestArgGen word)))) rest
    copyCmd (← makeCmd args) command.ignorestatus command.flags command.env command.dir
      command.cpus command.uid command.gid
  else
    foreach iterate (fun word => do
      vectors.append args (← liftResult (assertVector (← argGen word)))) parsed
    makeCmd args

/--
Julia source: base/cmd.jl:637-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable !:consistent function cmd_gen(
    parsed::Tuple{Vararg{Tuple{Vararg{Union{String, SubString{String}}}}}}
)
    return @invoke cmd_gen(parsed::Any)
end
```
-/
def cmdGenStringTuples (invokeGeneric : Parsed → M W (Cmd Vec S Cpu))
    (parsed : Parsed) : M W (Cmd Vec S Cpu) := invokeGeneric parsed

/--
Julia source: base/cmd.jl:659-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro cmd(str::String)
    cmd_ex = shell_parse(str, special=shell_special, filename=String(__source__.file))[1]
    if Meta.isexpr(cmd_ex, :tuple)
        return :(cmd_gen($(esc(cmd_ex))))
    else
        # Pipeline/redirect expression: GlobalRefs inside are already resolved to Base.
        # esc() ensures $interpolations inside are evaluated in the caller's scope.
        return esc(cmd_ex)
    end
end
```
-/
def cmdMacro
    (ops : JuliaLean.base.shell.Ops W S CharValue Atom Expr Pairs Reverse ReverseState Cursor File)
    (fileString : SourceFile → M W File) (isTuple : Expr → M W Bool)
    (esc : Expr → M W Expr) (quoteCmdGen : Expr → M W Expr)
    (sourceFile : SourceFile) (str : S) : M W Expr := do
  let filename ← fileString sourceFile
  let (parsed,_) ← JuliaLean.base.shell.shellParse ops str filename true (ops.literal JuliaLean.base.shell.shellSpecial)
  match parsed with
  | .words _ => throwThe Error (.foreignError "TypeError" "interpolating shell parser returned words")
  | .expression command =>
      if ← isTuple command then quoteCmdGen (← esc command) else esc command

/- Untranslated: the file header and the `AbstractCmd` abstract type declaration: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:1-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- abstract type AbstractCmd end
-- 
-- # libuv process option flags
-- /Source

/- Untranslated: a blank line inside the `Cmd` struct region. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: the `Cmd` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:50-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Cmd(cmd::Cmd; ignorestatus, detach, windows_verbatim, windows_hide, env, dir, uid, gid)
--     Cmd(exec::Vector{String})
-- 
-- Construct a new `Cmd` object, representing an external program and arguments, from `cmd`,
-- while changing the settings of the optional keyword arguments:
-- 
-- * `ignorestatus::Bool`: If `true` (defaults to `false`), then the `Cmd` will not throw an
--   error if the return code is nonzero.
-- * `detach::Bool`: If `true` (defaults to `false`), then the `Cmd` will be run in a new
--   process group, allowing it to outlive the `julia` process and not have Ctrl-C passed to
--   it.
-- * `windows_verbatim::Bool`: If `true` (defaults to `false`), then on Windows the `Cmd` will
--   send a command-line string to the process with no quoting or escaping of arguments, even
--   arguments containing spaces. (On Windows, arguments are sent to a program as a single
--   "command-line" string, and programs are responsible for parsing it into arguments. By
--   default, empty arguments and arguments with spaces or tabs are quoted with double quotes
--   `"` in the command line, and `\\` or `"` are preceded by backslashes.
--   `windows_verbatim=true` is useful for launching programs that parse their command line in
--   nonstandard ways.) Has no effect on non-Windows systems.
-- * `windows_hide::Bool`: If `true` (defaults to `false`), then on Windows no new console
--   window is displayed when the `Cmd` is executed. This has no effect if a console is
--   already open or on non-Windows systems.
-- * `env`: Set environment variables to use when running the `Cmd`. `env` is either a
--   dictionary mapping strings to strings, an array of strings of the form `"var=val"`, an
--   array or tuple of `"var"=>val` pairs. In order to modify (rather than replace) the
--   existing environment, initialize `env` with `copy(ENV)` and then set `env["var"]=val` as
--   desired.  To add to an environment block within a `Cmd` object without replacing all
--   elements, use [`addenv()`](@ref) which will return a `Cmd` object with the updated environment.
-- * `dir::AbstractString`: Specify a working directory for the command (instead
--   of the current directory).
-- * `uid::Union{Nothing,UInt32}`: Set the user ID for the process (Unix only).
-- * `gid::Union{Nothing,UInt32}`: Set the group ID for the process (Unix only).
-- 
-- For any keywords that are not specified, the current settings from `cmd` are used.
-- 
-- Note that the `Cmd(exec)` constructor does not create a copy of `exec`. Any subsequent changes to `exec` will be reflected in the `Cmd` object.
-- 
-- The most common way to construct a `Cmd` object is with command literals (backticks), e.g.
-- 
--     `ls -l`
-- 
-- This can then be passed to the `Cmd` constructor to modify its settings, e.g.
-- 
--     Cmd(`echo "Hello world"`, ignorestatus=true, detach=false)
-- """
-- Cmd
-- 
-- /Source

/--
Julia source: base/cmd.jl:99-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hash(x::Cmd, h::UInt) = hash(x.exec, hash(x.env, hash(x.ignorestatus, hash(x.dir, hash(x.flags, hash(x.uid, hash(x.gid, h)))))))
```
-/
/- `hash(x::Cmd, h)`: the field hashes nest from `gid` outwards, so `gid` is hashed first. Each
`hashX` is `hash(field, h)` of that field's type. -/
def hashCmd {H : Type} (hashExec : Vec → H → M W H) (hashEnv : Option Vec → H → M W H)
    (hashBool : Bool → H → M W H) (hashS : S → H → M W H) (hashU32 : U32 → H → M W H)
    (hashOptU32 : Option U32 → H → M W H) (x : Cmd Vec S Cpu) (h : H) : M W H := do
  let h ← hashOptU32 x.gid h
  let h ← hashOptU32 x.uid h
  let h ← hashU32 x.flags h
  let h ← hashS x.dir h
  let h ← hashBool x.ignorestatus h
  let h ← hashEnv x.env h
  hashExec x.exec h

/-- `==(::Union{Vector{String},Nothing}, ::Union{Vector{String},Nothing})`: `nothing == nothing`,
`nothing == v` is `false`, and two vectors compare with `eqVec`. -/
def eqEnv (eqVec : Vec → Vec → M W Bool) : Option Vec → Option Vec → M W Bool
  | none, none => pure true
  | some a, some b => eqVec a b
  | _, _ => pure false

/-- `==` on `Union{Nothing,UInt32}`. -/
def eqOptU32 : Option U32 → Option U32 → Bool
  | none, none => true
  | some a, some b => JuliaLean.base.int.eq a b
  | _, _ => false

/--
Julia source: base/cmd.jl:100-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Cmd, y::Cmd) = x.exec == y.exec && x.env == y.env && x.ignorestatus == y.ignorestatus &&
                     x.dir == y.dir && isequal(x.flags, y.flags) && x.uid == y.uid && x.gid == y.gid

```
-/
/- `==(x::Cmd, y::Cmd)`: `&&` stops at the first unequal field. -/
def eqCmd (eqVec : Vec → Vec → M W Bool) (eqS : S → S → M W Bool)
    (x y : Cmd Vec S Cpu) : M W Bool := do
  if !(← eqVec x.exec y.exec) then return false
  if !(← eqEnv eqVec x.env y.env) then return false
  if x.ignorestatus != y.ignorestatus then return false
  if !(← eqS x.dir y.dir) then return false
  -- `isequal(x.flags, y.flags)` on `UInt32`
  if !JuliaLean.base.int.eq x.flags y.flags then return false
  if !eqOptU32 x.uid y.uid then return false
  return eqOptU32 x.gid y.gid

/--
Julia source: base/cmd.jl:120-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

hash(x::AndCmds, h::UInt) = hash(x.a, hash(x.b, h))
```
-/
/- `hash(x::AndCmds, h)`: `hashA`/`hashB` are `hash(x.a, ·)`/`hash(x.b, ·)`, dispatched on the
dynamic types of the fields (`hashCommand`). -/
def hashAndCmds {H : Type} (hashA hashB : H → M W H) (h : H) : M W H := do
  hashA (← hashB h)

/--
Julia source: base/cmd.jl:122-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::AndCmds, y::AndCmds) = x.a == y.a && x.b == y.b

```
-/
/- `==(x::AndCmds, y::AndCmds)`: `eqA` is `x.a == y.a` and `eqB` is `x.b == y.b`. -/
def eqAndCmds (eqA eqB : M W Bool) : M W Bool := do
  if ← eqA then eqB else pure false

/-- *dispatch*: `hash(c::AbstractCmd, h)`. `Cmd` and `AndCmds` have the methods above; every other
command uses the generic `hash(x, h)` (`hashOther`, objectid-based). -/
def hashCommand {H : Type} (hashCmd : Cmd Vec S Cpu → H → M W H)
    (hashOther : Command Vec S Cpu Handle Custom → H → M W H) :
    Command Vec S Cpu Handle Custom → H → M W H
  | .cmd c, h => hashCmd c h
  | .andCmds a b, h => hashAndCmds (hashCommand hashCmd hashOther a) (hashCommand hashCmd hashOther b) h
  | x, h => hashOther x h

/-- *dispatch*: `a == b` on two commands. `Cmd`/`Cmd` and `AndCmds`/`AndCmds` have the methods
above; any other pair uses the generic `==`, which is `===` (`egal`). -/
def eqCommand (eqCmd : Cmd Vec S Cpu → Cmd Vec S Cpu → M W Bool)
    (egal : Command Vec S Cpu Handle Custom → Command Vec S Cpu Handle Custom → M W Bool) :
    Command Vec S Cpu Handle Custom → Command Vec S Cpu Handle Custom → M W Bool
  | .cmd a, .cmd b => eqCmd a b
  | .andCmds a1 b1, .andCmds a2 b2 =>
      eqAndCmds (eqCommand eqCmd egal a1 a2) (eqCommand eqCmd egal b1 b2)
  | x, y => egal x y

section shellEscape
variable {SC SAtom SExpr SPairs SRev SRevState SCursor SFile : Type}

/-- `cmd.exec...`: the elements of the argument vector. -/
abbrev ShellOps (W S SC SAtom SExpr SPairs SRev SRevState SCursor SFile : Type) :=
  JuliaLean.base.shell.Ops W S SC SAtom SExpr SPairs SRev SRevState SCursor SFile

/--
Julia source: base/cmd.jl:124-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_escape(cmd::Cmd; special::AbstractString="") =
    shell_escape(cmd.exec..., special=special)
```
-/
/- `shell_escape(cmd; special)`: the installed `base/shell.jl` `shellEscape` over the elements of
`cmd.exec` (`elements`). -/
def shellEscapeCmd (ops : ShellOps W S SC SAtom SExpr SPairs SRev SRevState SCursor SFile)
    (elements : Vec → M W (List S)) (cmd : Cmd Vec S Cpu) (special : S) : M W S := do
  JuliaLean.base.shell.shellEscape ops (← elements cmd.exec) special

/--
Julia source: base/cmd.jl:126-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_escape_posixly(cmd::Cmd) =
    shell_escape_posixly(cmd.exec...)
```
-/
def shellEscapePosixlyCmd (ops : ShellOps W S SC SAtom SExpr SPairs SRev SRevState SCursor SFile)
    (elements : Vec → M W (List S)) (cmd : Cmd Vec S Cpu) : M W S := do
  JuliaLean.base.shell.shellEscapePosixly ops (← elements cmd.exec)

/--
Julia source: base/cmd.jl:128-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_escape_csh(cmd::Cmd) =
    shell_escape_csh(cmd.exec...)
```
-/
def shellEscapeCshCmd (ops : ShellOps W S SC SAtom SExpr SPairs SRev SRevState SCursor SFile)
    (elements : Vec → M W (List S)) (cmd : Cmd Vec S Cpu) : M W S := do
  JuliaLean.base.shell.shellEscapeCsh ops (← elements cmd.exec)

/--
Julia source: base/cmd.jl:130-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
escape_microsoft_c_args(cmd::Cmd) =
    escape_microsoft_c_args(cmd.exec...)
```
-/
def escapeMicrosoftCArgsCmd (ops : ShellOps W S SC SAtom SExpr SPairs SRev SRevState SCursor SFile)
    (elements : Vec → M W (List S)) (cmd : Cmd Vec S Cpu) : M W S := do
  JuliaLean.base.shell.escapeMicrosoftCArgs ops (← elements cmd.exec)

/--
Julia source: base/cmd.jl:132-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
escape_microsoft_c_args(io::IO, cmd::Cmd) =
    escape_microsoft_c_args(io::IO, cmd.exec...)

```
-/
/- `escape_microsoft_c_args(io, cmd)`: the installed `escapeMicrosoftCArgsIO`, whose
`ops.writeString` writes to `io`. -/
def escapeMicrosoftCArgsIOCmd (ops : ShellOps W S SC SAtom SExpr SPairs SRev SRevState SCursor SFile)
    (elements : Vec → M W (List S)) (cmd : Cmd Vec S Cpu) : M W Unit := do
  JuliaLean.base.shell.escapeMicrosoftCArgsIO ops (← elements cmd.exec)

end shellEscape

/--
Julia source: base/cmd.jl:135-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Patterns that indicate a sensitive environment variable name.
# Matched as whole components after splitting on non-alphanumeric characters,
# so e.g. "PAT" matches "GITHUB_PAT" but not "PATH".
const SENSITIVE_ENV_PATTERNS = ("KEY", "TOKEN", "SECRET", "JWT", "PAT",
                                "PASSWORD", "PASSWD", "PASS", "PWD", "PW",
                                "CREDENTIAL", "CRED", "AUTH", "PRIVATE", "PRIV")

```
-/
def SENSITIVE_ENV_PATTERNS : List String :=
  ["KEY", "TOKEN", "SECRET", "JWT", "PAT", "PASSWORD", "PASSWD", "PASS", "PWD", "PW",
   "CREDENTIAL", "CRED", "AUTH", "PRIVATE", "PRIV"]

/--
Julia source: base/cmd.jl:142-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_sensitive_env_name(name::AbstractString)
    uname = uppercase(name)
    parts = eachsplit(uname, r"[^A-Za-z0-9]+")
    return any(part -> part in SENSITIVE_ENV_PATTERNS, parts)
end

```
-/
/- `is_sensitive_env_name(name)`. `eachsplitNonAlnum s` is the parts of
`eachsplit(s, r"[^A-Za-z0-9]+")` (the PCRE regex split, `keepempty=true`); `part in tuple` compares
with `==` (`eqS`). `any` stops at the first match. -/
def is_sensitive_env_name (uppercase : S → M W S) (eachsplitNonAlnum : S → M W (List S))
    (eqS : S → S → M W Bool) (literal : String → S) (name : S) : M W Bool := do
  let uname ← uppercase name
  let parts ← eachsplitNonAlnum uname
  parts.anyM fun part => SENSITIVE_ENV_PATTERNS.anyM fun pattern => eqS part (literal pattern)

/--
Julia source: base/cmd.jl:148-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_show_env_mode(io::IO)
    val = get(io, :show_env, :_unset)
    if val !== :_unset
        return val::Symbol
    end
    envval = get(ENV, "JULIA_SHOW_ENV", nothing)
    envval === nothing && return :redact
    envval = lowercase(envval)
    envval == "all" && return :all
    envval == "none" && return :none
    envval == "keys" && return :keys
    return :redact
end

```
-/
/- `get_show_env_mode(io)`; symbols are their names. `getShowEnv io` is
`get(io, :show_env, :_unset)`, `isUnset v` is `v === :_unset`, and `asSymbol` the `val::Symbol`
assertion. `getEnv k` is `get(ENV, k, nothing)`. -/
def get_show_env_mode {Io V : Type} (getShowEnv : Io → M W V) (isUnset : V → Bool)
    (asSymbol : V → Except Error String) (getEnv : String → M W (Option S))
    (lowercase : S → M W S) (eqS : S → S → M W Bool) (literal : String → S) (io : Io) :
    M W String := do
  let val ← getShowEnv io
  if !isUnset val then
    return ← liftResult (asSymbol val)
  let some envval ← getEnv "JULIA_SHOW_ENV" | return "redact"
  let envval ← lowercase envval
  if ← eqS envval (literal "all") then return "all"
  if ← eqS envval (literal "none") then return "none"
  if ← eqS envval (literal "keys") then return "keys"
  return "redact"

/-- The printing callees of the `show` methods: `print(io, literal)`, `print(io, s)`, `show(io, s)`
of a `String`, `print(io, n)` of an `Int`, `show(io, n)` of an `Int32` and `show(io, v)` of a
`Vector{Int}`. -/
structure ShowOps (W Io S : Type) where
  print : Io → String → M W Unit
  printS : Io → S → M W Unit
  showS : Io → S → M W Unit
  printInt : Io → I → M W Unit
  showInt32 : Io → JInt .i32 → M W Unit
  showInts : Io → List I → M W Unit

/--
Julia source: base/cmd.jl:162-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_env(io::IO, env::Vector{String})
    mode = get_show_env_mode(io)
    print(io, "[")
    for (i, e) in enumerate(env)
        i > 1 && print(io, ", ")
        eqidx = findnext('=', e, 2)
        if eqidx === nothing || mode === :all
            show(io, e)
        elseif mode === :keys
            key = e[1:prevind(e, eqidx)]
            show(io, key)
        else  # :redact
            key = e[1:prevind(e, eqidx)]
            if is_sensitive_env_name(key)
                show(io, key)
            else
                show(io, e)
            end
        end
    end
    print(io, "]")
end

```
-/
/- `show_env(io, env)`. `elements` reads the vector, `findnext`/`prevind`/`slice` are the
`String` methods (`slice e a (some b)` is `e[a:b]`), and `isSensitive` is
`is_sensitive_env_name`. -/
def show_env {Io : Type} (o : ShowOps W Io S) (getShowEnvMode : Io → M W String)
    (elements : Vec → M W (List S)) (findnext : S → Char → I → M W (Option I))
    (prevind : S → I → M W I) (slice : S → I → Option I → M W S) (isSensitive : S → M W Bool)
    (io : Io) (env : Vec) : M W Unit := do
  let mode ← getShowEnvMode io
  o.print io "["
  for (e, k) in (← elements env).zipIdx 1 do
    if k > 1 then o.print io ", "
    let eqidx ← findnext e '=' (i 2)
    match eqidx with
    | none => o.showS io e
    | some q =>
      if mode == "all" then
        o.showS io e
      else if mode == "keys" then
        let key ← slice e (i 1) (some (← prevind e q))
        o.showS io key
      else -- :redact
        let key ← slice e (i 1) (some (← prevind e q))
        if ← isSensitive key then
          o.showS io key
        else
          o.showS io e
  o.print io "]"

/--
Julia source: base/cmd.jl:185-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, cmd::Cmd)
    env = cmd.env
    if env !== nothing && get_show_env_mode(io) === :none
        env = nothing
    end
    print_env = env !== nothing
    print_dir = !isempty(cmd.dir)
    print_uid = cmd.uid !== nothing
    print_gid = cmd.gid !== nothing
    print_cpus = cmd.cpus !== nothing

    (print_env || print_dir) && print(io, "setenv(")
    print_cpus && print(io, "setcpuaffinity(")
    print_gid && print(io, "setgid(")
    print_uid && print(io, "setuid(")

    print(io, '`')
    join(io, map(cmd.exec) do arg
        replace(sprint(context=io) do io
            with_output_color(:underline, io) do io
                # A leading `~` would be expanded when the command is parsed back.
                print_shell_word(io, arg, startswith(arg, '~') ? shell_special * '~' : shell_special)
            end
        end, '`' => "\\`")
    end, ' ')
    print(io, '`')

    print_uid && (print(io, ", "); show(io, Int32(cmd.uid)); print(io, ")"))
    print_gid && (print(io, ", "); show(io, Int32(cmd.gid)); print(io, ")"))
    if print_cpus
        print(io, ", ")
        show(io, collect(Int, something(cmd.cpus)))
        print(io, ")")
    end
    if print_env || print_dir
        env === nothing || (print(io, ","); show_env(io, env))
        print_dir && (print(io, "; dir="); show(io, cmd.dir))
        print(io, ")")
    end
    nothing
end

```
-/
/- `show(io, cmd::Cmd)`. `sprintUnderlined io body` is
`sprint(context=io) do io; with_output_color(:underline, io) do io; body end end` (strings/io.jl,
util.jl), and `printShellWord arg special` is `print_shell_word(io, arg, special)` (the installed
`base/shell.jl` `printShellWord`) writing to that inner stream. `startswithTilde arg` is
`startswith(arg, '~')`, `concat` is `*`, `replaceBacktick s` is `replace(s, '`' => "\\`")`, and
`cpuElements` reads `something(cmd.cpus)`; `collect(Int, ·)` widens each `UInt16`. `Int32(uid)`
throws `InexactError(:convert, Int32, uid)` above `typemax(Int32)` (`int.convert`). -/
def showCmd {Io : Type} (o : ShowOps W Io S) (getShowEnvMode : Io → M W String)
    (showEnv : Io → Vec → M W Unit) (isemptyS : S → M W Bool) (elements : Vec → M W (List S))
    (startswithTilde : S → M W Bool) (literal : String → S) (concat : S → S → M W S)
    (sprintUnderlined : Io → M W Unit → M W S) (printShellWord : S → S → M W Unit)
    (replaceBacktick : S → M W S) (cpuElements : Cpu → M W (List (JInt .u16)))
    (io : Io) (cmd : Cmd Vec S Cpu) : M W Unit := do
  let mut env := cmd.env
  if env.isSome then
    if (← getShowEnvMode io) == "none" then
      env := none
  let print_env := env.isSome
  let print_dir := !(← isemptyS cmd.dir)
  let print_uid := cmd.uid.isSome
  let print_gid := cmd.gid.isSome
  let print_cpus := cmd.cpus.isSome
  if print_env || print_dir then o.print io "setenv("
  if print_cpus then o.print io "setcpuaffinity("
  if print_gid then o.print io "setgid("
  if print_uid then o.print io "setuid("
  o.print io "`"
  let words ← (← elements cmd.exec).mapM fun arg => do
    -- A leading `~` would be expanded when the command is parsed back.
    let special ← if ← startswithTilde arg then
        concat (literal JuliaLean.base.shell.shellSpecial) (literal "~")
      else pure (literal JuliaLean.base.shell.shellSpecial)
    replaceBacktick (← sprintUnderlined io (printShellWord arg special))
  -- `join(io, words, ' ')`
  let mut first := true
  for w in words do
    if !first then o.print io " "
    first := false
    o.printS io w
  o.print io "`"
  if let some uid := cmd.uid then
    o.print io ", "
    o.showInt32 io (← liftResult ((JuliaLean.base.int.convert .i32 uid).mapError JuliaLean.base.io.Error.jl))
    o.print io ")"
  if let some gid := cmd.gid then
    o.print io ", "
    o.showInt32 io (← liftResult ((JuliaLean.base.int.convert .i32 gid).mapError JuliaLean.base.io.Error.jl))
    o.print io ")"
  if let some cpus := cmd.cpus then
    o.print io ", "
    o.showInts io ((← cpuElements cpus).map fun c => i c.val)
    o.print io ")"
  if print_env || print_dir then
    if let some e := env then
      o.print io ","
      showEnv io e
    if print_dir then
      o.print io "; dir="
      o.showS io cmd.dir
    o.print io ")"

/--
Julia source: base/cmd.jl:227-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, cmds::Union{OrCmds,ErrOrCmds})
    print(io, "pipeline(")
    show(io, cmds.a)
    print(io, ", ")
    print(io, isa(cmds, ErrOrCmds) ? "stderr=" : "stdout=")
    show(io, cmds.b)
    print(io, ")")
end

```
-/
/- `show(io, cmds::Union{OrCmds,ErrOrCmds})`; `showA`/`showB` are `show(io, cmds.a)` and
`show(io, cmds.b)`, and `isErr` is `isa(cmds, ErrOrCmds)`. -/
def showOrCmds {Io : Type} (o : ShowOps W Io S) (io : Io) (isErr : Bool) (showA showB : M W Unit) :
    M W Unit := do
  o.print io "pipeline("
  showA
  o.print io ", "
  o.print io (if isErr then "stderr=" else "stdout=")
  showB
  o.print io ")"

/--
Julia source: base/cmd.jl:236-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, cmds::AndCmds)
    show(io, cmds.a)
    print(io, " & ")
    show(io, cmds.b)
end

```
-/
def showAndCmds {Io : Type} (o : ShowOps W Io S) (io : Io) (showA showB : M W Unit) : M W Unit := do
  showA
  o.print io " & "
  showB

/- Untranslated: a blank line between constants. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/cmd.jl:257-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# setup_stdio ≈ cconvert
# rawhandle ≈ unsafe_convert
rawhandle(::DevNull) = C_NULL
rawhandle(x::OS_HANDLE) = x
if OS_HANDLE !== RawFD
    rawhandle(x::RawFD) = Libc._get_osfhandle(x)
end
```
-/
/- `rawhandle(::DevNull) = C_NULL`. -/
def rawhandleDevNull : JInt .u64 := JInt.wrap .u64 0

/-- `rawhandle(x::OS_HANDLE) = x`. -/
def rawhandleOS (x : Handle) : Handle := x

/-- `rawhandle(x::RawFD) = Libc._get_osfhandle(x)`, defined only where `OS_HANDLE !== RawFD`
(Windows); `getOsfhandle` is that `libc.jl` call. -/
def rawhandleRawFD {RawFD : Type} (getOsfhandle : RawFD → M W Handle) (x : RawFD) : M W Handle :=
  getOsfhandle x

/--
Julia source: base/cmd.jl:265-265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setup_stdio(stdio::Union{DevNull,OS_HANDLE,RawFD}, ::Bool) = (stdio, false)
```
-/
def setup_stdio {X : Type} (stdio : X) (_ : Bool) : X × Bool := (stdio, false)

/- Untranslated: the `Redirectable` and `StdIOSet` type aliases: type declarations, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:266-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const Redirectable = Union{IO, IOServer, FileRedirect, RawFD, OS_HANDLE}
-- const StdIOSet = NTuple{3, Redirectable}
-- 
-- /Source

/--
Julia source: base/cmd.jl:277-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function show(io::IO, cr::CmdRedirect)
    print(io, "pipeline(")
    show(io, cr.cmd)
    print(io, ", ")
    if cr.stream_no == STDOUT_NO
        print(io, "stdout")
    elseif cr.stream_no == STDERR_NO
        print(io, "stderr")
    elseif cr.stream_no == STDIN_NO
        print(io, "stdin")
    else
        print(io, cr.stream_no)
    end
    print(io, cr.readable ? "<" : ">")
    show(io, cr.handle)
    print(io, ")")
end

```
-/
/- `show(io, cr::CmdRedirect)`; `showCmd` is `show(io, cr.cmd)` and `showHandle` is
`show(io, cr.handle)`. -/
def showCmdRedirect {Io : Type} (o : ShowOps W Io S) (showHandle : Io → Handle → M W Unit) (io : Io)
    (showCmd : M W Unit) (handle : Handle) (stream_no : I) (readable : Bool) : M W Unit := do
  o.print io "pipeline("
  showCmd
  o.print io ", "
  if JuliaLean.base.int.eq stream_no stdoutNo then
    o.print io "stdout"
  else if JuliaLean.base.int.eq stream_no stderrNo then
    o.print io "stderr"
  else if JuliaLean.base.int.eq stream_no stdinNo then
    o.print io "stdin"
  else
    o.printInt io stream_no
  o.print io (if readable then "<" else ">")
  showHandle io handle
  o.print io ")"

/-- *dispatch*: `show(io, c::AbstractCmd)` over the methods above; `showCustom` is the `show`
method of any other command type. -/
def showCommand {Io : Type} (o : ShowOps W Io S) (showCmd : Io → Cmd Vec S Cpu → M W Unit)
    (showHandle : Io → Handle → M W Unit) (showCustom : Io → Custom → M W Unit) (io : Io) :
    Command Vec S Cpu Handle Custom → M W Unit
  | .cmd c => showCmd io c
  | .orCmds a b => showOrCmds o io false (showCommand o showCmd showHandle showCustom io a)
      (showCommand o showCmd showHandle showCustom io b)
  | .errOrCmds a b => showOrCmds o io true (showCommand o showCmd showHandle showCustom io a)
      (showCommand o showCmd showHandle showCustom io b)
  | .andCmds a b => showAndCmds o io (showCommand o showCmd showHandle showCustom io a)
      (showCommand o showCmd showHandle showCustom io b)
  | .redirect c handle stream readable =>
      showCmdRedirect o showHandle io (showCommand o showCmd showHandle showCustom io c) handle stream readable
  | .custom x => showCustom io x

/-- The `Dict{String,String}` that `addenv` builds: `Dict{String,String}()`,
`merge!(new_env, ENV)`, `new_env[k] = v` and `delete!(new_env, k)`. -/
structure EnvDict (W D S : Type) where
  new : M W D
  mergeENV : D → M W Unit
  set : D → S → S → M W Unit
  delete : D → S → M W Unit

/- Untranslated: the `ignorestatus` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:296-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     ignorestatus(command)
-- 
-- Mark a command object so that running it will not throw an error if the result code is non-zero.
-- """
-- /Source

/- Untranslated: the `detach` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:306-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     detach(command)
-- 
-- Mark a command object so that it will be run in a new process group, allowing it to outlive the julia process, and not have Ctrl-C interrupts passed to it.
-- """
-- /Source

/- Untranslated: a comment before `cstr`: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:313-315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # like String(s), but throw an error if s contains NUL, since
-- # libuv requires NUL-terminated strings
-- /Source

/- Untranslated: a comment before `byteenv`: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:322-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # convert various env representations into an array of "key=val" strings
-- /Source

/- Untranslated: the `setenv` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:331-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     setenv(command::Cmd, env; dir)
-- 
-- Set environment variables to use when running the given `command`. `env` is either a
-- dictionary mapping strings to strings, an array of strings of the form `"var=val"`, or
-- zero or more `"var"=>val` pair arguments. In order to modify (rather than replace) the
-- existing environment, create `env` through `copy(ENV)` and then setting `env["var"]=val`
-- as desired, or use [`addenv`](@ref).
-- 
-- The `dir` keyword argument can be used to specify a working directory for the command.
-- `dir` defaults to the currently set `dir` for `command` (which is the current working
-- directory if not specified already).
-- 
-- !!! warning
--     The display redaction behavior (including the `:show_env` IOContext key
--     and `JULIA_SHOW_ENV` environment variable) is experimental and may change
--     in a non-breaking release of Julia.
-- 
-- When displaying a `Cmd`, environment variables whose names match sensitive patterns
-- (e.g. containing "KEY", "TOKEN", "SECRET", "PASSWORD", "AUTH", "JWT", "PAT") have
-- their values hidden. The display mode can be controlled via the `JULIA_SHOW_ENV`
-- environment variable or the `:show_env` IOContext key (which takes precedence),
-- with values `:none`, `:keys`, `:redact` (default), or `:all`.
-- 
-- See also [`Cmd`](@ref), [`addenv`](@ref), [`ENV`](@ref), [`pwd`](@ref).
-- """
-- /Source

/- Untranslated: a comment before `splitenv`: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:362-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # split environment entry string into before and after first `=` (key and value)
-- /Source

/- Untranslated: the `addenv` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:371-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     addenv(command::Cmd, env...; inherit::Bool = true)
-- 
-- Merge new environment mappings into the given [`Cmd`](@ref) object, returning a new `Cmd` object.
-- Duplicate keys are replaced.  If `command` does not contain any environment values set already,
-- it inherits the current environment at time of `addenv()` call if `inherit` is `true`.
-- Keys with value `nothing` are deleted from the env.
-- 
-- See also [`Cmd`](@ref), [`setenv`](@ref), [`ENV`](@ref).
-- 
-- !!! compat "Julia 1.6"
--     This function requires Julia 1.6 or later.
-- """
-- /Source

/--
Julia source: base/cmd.jl:385-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function addenv(cmd::Cmd, env::Dict; inherit::Bool = true)
    new_env = Dict{String,String}()
    if cmd.env === nothing
        if inherit
            merge!(new_env, ENV)
        end
    else
        for (k, v) in splitenv.(cmd.env)
            new_env[string(k)::String] = string(v)::String
        end
    end
    for (k, v) in env
        if v === nothing
            delete!(new_env, string(k)::String)
        else
            new_env[string(k)::String] = string(v)::String
        end
    end
    return setenv(cmd, new_env)
end

```
-/
/- `addenv(cmd, env::Dict; inherit)`. `splitenv.(cmd.env)` runs over the whole vector before the
loop; `envPairs` iterates `env`, with `none` for a value that is `nothing`. In
`new_env[string(k)::String] = string(v)::String` the value is evaluated before the key. `strS`,
`keyString` and `valString` are `string(·)::String`; `setenv` is `setenv(cmd, new_env)`. -/
def addenvDict {K V D Env : Type} (dict : EnvDict W D S) (elements : Vec → M W (List S))
    (splitenv : S → M W (S × S)) (strS : S → M W S) (envPairs : Env → M W (List (K × Option V)))
    (keyString : K → M W S) (valString : V → M W S)
    (setenv : Cmd Vec S Cpu → D → M W (Cmd Vec S Cpu))
    (cmd : Cmd Vec S Cpu) (env : Env) (inherit : Bool := true) : M W (Cmd Vec S Cpu) := do
  let new_env ← dict.new
  match cmd.env with
  | none =>
    if inherit then
      dict.mergeENV new_env
  | some e =>
    let kvs ← (← elements e).mapM splitenv
    for (k, v) in kvs do
      let value ← strS v
      dict.set new_env (← strS k) value
  for (k, v) in ← envPairs env do
    match v with
    | none => dict.delete new_env (← keyString k)
    | some v =>
      let value ← valString v
      dict.set new_env (← keyString k) value
  setenv cmd new_env

/--
Julia source: base/cmd.jl:406-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function addenv(cmd::Cmd, pairs::Pair{<:AbstractString}...; inherit::Bool = true)
    return addenv(cmd, Dict(k => v for (k, v) in pairs); inherit)
end

```
-/
/- `addenv(cmd, pairs...; inherit)`: `dictOf` is `Dict(k => v for (k, v) in pairs)` and `addenv`
the `Dict` method. -/
def addenvPairs {P D : Type} (dictOf : P → M W D)
    (addenv : Cmd Vec S Cpu → D → Bool → M W (Cmd Vec S Cpu))
    (cmd : Cmd Vec S Cpu) (pairs : P) (inherit : Bool := true) : M W (Cmd Vec S Cpu) := do
  addenv cmd (← dictOf pairs) inherit

/--
Julia source: base/cmd.jl:410-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function addenv(cmd::Cmd, env::Vector{<:AbstractString}; inherit::Bool = true)
    return addenv(cmd, Dict(k => v for (k, v) in splitenv.(env)); inherit)
end

```
-/
/- `addenv(cmd, env::Vector{<:AbstractString}; inherit)`: `splitenv.(env)` builds the whole
vector of pairs before `Dict(...)` (`dictOf`) consumes it. -/
def addenvVector {D EnvVec : Type} (elements : EnvVec → M W (List S)) (splitenv : S → M W (S × S))
    (dictOf : List (S × S) → M W D) (addenv : Cmd Vec S Cpu → D → Bool → M W (Cmd Vec S Cpu))
    (cmd : Cmd Vec S Cpu) (env : EnvVec) (inherit : Bool := true) : M W (Cmd Vec S Cpu) := do
  let kvs ← (← elements env).mapM splitenv
  addenv cmd (← dictOf kvs) inherit

/- Untranslated: the `setcpuaffinity` docstring and its empty generic-function declaration: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:414-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     setcpuaffinity(original_command::Cmd, cpus) -> command::Cmd
-- 
-- Set the CPU affinity of the `command` by a list of CPU IDs (1-based) `cpus`.  Passing
-- `cpus = nothing` means to unset the CPU affinity if the `original_command` has any.
-- 
-- This function is supported only in Linux and Windows.  It is not supported in macOS because
-- libuv does not support affinity setting.
-- 
-- !!! compat "Julia 1.8"
--     This function requires at least Julia 1.8.
-- 
-- # Examples
-- 
-- In Linux, the `taskset` command line program can be used to see how `setcpuaffinity` works.
-- 
-- ```julia
-- julia> run(setcpuaffinity(`sh -c 'taskset -p \$\$'`, [1, 2, 5]));
-- pid 2273's current affinity mask: 13
-- ```
-- 
-- Note that the mask value `13` reflects that the first, second, and the fifth bits (counting
-- from the least significant position) are turned on:
-- 
-- ```julia
-- julia> 0b010011
-- 0x13
-- ```
-- """
-- function setcpuaffinity end
-- /Source

/- Untranslated: the `setuid` docstring and its empty generic-function declaration: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:446-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     setuid(original_command::Cmd, uid) -> command::Cmd
-- 
-- Set the user ID (UID) of the `command`. On Unix systems, this allows
-- the command to run as a different user. Passing `uid = nothing` removes
-- any previously set UID.
-- 
-- This function is only supported on Unix-based systems (Linux, macOS, etc.).
-- Requires appropriate permissions to set UID.
-- 
-- !!! compat "Julia 1.13"
--     This function requires at least Julia 1.13.
-- 
-- # Examples
-- 
-- ```julia
-- julia> run(setuid(`id -u`, 1000));
-- 1000
-- ```
-- """
-- function setuid end
-- /Source

/- Untranslated: the `setgid` docstring and its empty generic-function declaration: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:470-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     setgid(original_command::Cmd, gid) -> command::Cmd
-- 
-- Set the group ID (GID) of the `command`. On Unix systems, this allows
-- the command to run as a different group. Passing `gid = nothing` removes
-- any previously set GID.
-- 
-- This function is only supported on Unix-based systems (Linux, macOS, etc.).
-- Requires appropriate permissions to set GID.
-- 
-- !!! compat "Julia 1.13"
--     This function requires at least Julia 1.13.
-- 
-- # Examples
-- 
-- ```julia
-- julia> run(setgid(`id -g`, 1000));
-- 1000
-- ```
-- """
-- function setgid end
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:494-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: a comment before the stream redirects: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:498-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Stream Redirects
-- /Source

/- Untranslated: a comment before the file redirects: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:503-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # File redirects
-- /Source

/- Untranslated: the `pipeline` keyword docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:510-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     pipeline(command; stdin, stdout, stderr, append=false)
-- 
-- Redirect I/O to or from the given `command`. Keyword arguments specify which of the
-- command's streams should be redirected. `append` controls whether file output appends to the
-- file. This is a more general version of the 2-argument `pipeline` function.
-- `pipeline(from, to)` is equivalent to `pipeline(from, stdout=to)` when `from` is a command,
-- and to `pipeline(to, stdin=from)` when `from` is another kind of data source.
-- 
-- **Examples**:
-- 
-- ```julia
-- run(pipeline(`dothings`, stdout="out.txt", stderr="errs.txt"))
-- run(pipeline(`update`, stdout="log.txt", append=true))
-- ```
-- """
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: the `pipeline(command, redir::Pair)` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:545-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     pipeline(command, redir::Pair{<:Integer, <:Redirectable})
-- 
-- Redirect fd number `redir.first` of `command` to or from the given `redir.second`, which can be
-- an I/O stream, a filename, or a file descriptor. This method is primarily used to pass additional
-- fds beyond the standard ios that are not supported by the keyword argument interface.
-- 
-- !!! compat "Julia 1.13"
--     This method requires Julia 1.13 or later.
-- """
-- /Source

/- Untranslated: the `pipeline(from, to, ...)` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:557-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     pipeline(from, to, ...)
-- 
-- Create a pipeline from a data source to a destination. The source and destination can be
-- commands, I/O streams, strings, or results of other `pipeline` calls. At least one argument
-- must be a command. Strings refer to filenames. When called with more than two arguments,
-- they are chained together from left to right. For example, `pipeline(a,b,c)` is equivalent to
-- `pipeline(pipeline(a,b),c)`. This provides a more concise way to specify multi-stage
-- pipelines.
-- 
-- **Examples**:
-- 
-- ```julia
-- run(pipeline(`ls`, `grep xyz`))
-- run(pipeline(`ls`, "out.txt"))
-- run(pipeline("out.txt", `grep xyz`))
-- ```
-- """
-- /Source

/- Untranslated: a section comment: no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:577-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- ## implementation of `cmd` syntax ##
-- 
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:587-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:608-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:618-618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: a blank line. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:636-636 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: the `@cmd` docstring: documentation, no method body. -/
-- UNTRANSLATED
-- Source: base/cmd.jl:642-658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     @cmd str
-- 
-- Similar to ``` `str` ```, generate a `Cmd` from the `str` string which represents the shell command(s) to be executed.
-- The [`Cmd`](@ref) object can be run as a process and can outlive the spawning julia process (see `Cmd` for more).
-- 
-- # Examples
-- ```jldoctest
-- julia> cm = @cmd " echo 1 "
-- `echo 1`
-- 
-- julia> run(cm)
-- 1
-- Process(`echo 1`, ProcessExited(0))
-- ```
-- """
-- /Source

end JuliaLean.base.cmd

namespace JuliaLean.ShellCmd

/-- `struct Cmd`, `base/cmd.jl:13-21`. -/
structure CmdM where
  exec : List JS
  ignorestatus : Bool
  flags : UInt32
  env : Option (List JS)
  dir : JS
  cpus : Option (List UInt16)
  uid : Option UInt32
  gid : Option UInt32
  deriving DecidableEq, Repr

/-- `Cmd(exec::Vector{String})`, `base/cmd.jl:22-23`. -/
def cmdOf (exec : List JS) : CmdM :=
  { exec, ignorestatus := false, flags := 0, env := none, dir := [], cpus := none,
    uid := none, gid := none }

/-- `==(x::Cmd, y::Cmd)`, `base/cmd.jl:100-101`. -/
def cmdEq (x y : CmdM) : Bool :=
  x.exec == y.exec && x.env == y.env && x.ignorestatus == y.ignorestatus &&
    x.dir == y.dir && x.flags == y.flags && x.uid == y.uid && x.gid == y.gid

/-- `has_nondefault_cmd_flags(c)`, `base/cmd.jl:42-49`. -/
def hasNondefaultFlags (c : CmdM) : Bool :=
  c.ignorestatus || c.flags != 0 || c.env.isSome || !c.dir.isEmpty || c.cpus.isSome ||
    c.uid.isSome || c.gid.isSome

/-- `setcpuaffinity(cmd, cpus)` with a list of CPU ids, `base/cmd.jl:445`. -/
def setcpuaffinity (c : CmdM) (cpus : List UInt16) : CmdM := { c with cpus := some cpus }

/-! ### `show(::IO, ::Cmd)`, `base/cmd.jl:185-225` -/

/-- One argument as printed by `show(::Cmd)`, `base/cmd.jl:203-208`, before the
backtick escaping: `print_shell_word` with `shell_special`, plus `~` for a
word starting with `~`. -/
def showWordRaw (arg : JS) : JS :=
  printShellWord arg (if arg.head? == some (A '~') then shellSpecial ++ [A '~'] else shellSpecial)

/-- One argument as printed: `replace(..., '`' => "\\`")`. -/
def showWord (arg : JS) : JS := replaceC (showWordRaw arg) (A '`') (S "\\`")

/-- The command literal printed for `exec`, `base/cmd.jl:201-210`. -/
def showExec (exec : List JS) : JS := A '`' :: joinSp (exec.map showWord) ++ [A '`']

/-- The text of the literal before backtick escaping: the shell-quoted words. -/
def showBody (exec : List JS) : JS := joinSp (exec.map showWordRaw)

/-- Decimal digits of a natural number. -/
def decimal (n : Nat) : JS := S (toString n)

/-- `show(io, Int32(x))` for `x::UInt32`: `Int32(x)` throws `InexactError`
unless `x < 2^31`. -/
def showInt32OfU32 (x : UInt32) : SH JS :=
  if x.toNat < 2 ^ 31 then .ok (decimal x.toNat) else .error (.jl (.inexactError "convert"))

/-- `show(io, collect(Int, cpus))`: `[1, 2]`. -/
def showCpus (cpus : List UInt16) : JS :=
  A '[' :: (match cpus.map (fun c => decimal c.toNat) with
    | [] => []
    | d :: ds => d ++ ds.flatMap (fun e => S ", " ++ e)) ++ [A ']']

/-- `show(io, cmd)` for a `Cmd` without environment and directory
(`base/cmd.jl:185-225` with `print_env` and `print_dir` false). -/
def showCmdNoEnv (c : CmdM) : SH JS := do
  let uidT ← match c.uid with
    | some u => do let t ← showInt32OfU32 u; pure (S ", " ++ t ++ S ")")
    | none => pure []
  let gidT ← match c.gid with
    | some g => do let t ← showInt32OfU32 g; pure (S ", " ++ t ++ S ")")
    | none => pure []
  let cpusT := match c.cpus with
    | some cs => S ", " ++ showCpus cs ++ S ")"
    | none => []
  pure ((if c.cpus.isSome then S "setcpuaffinity(" else []) ++
    (if c.gid.isSome then S "setgid(" else []) ++
    (if c.uid.isSome then S "setuid(" else []) ++
    showExec c.exec ++ uidT ++ gidT ++ cpusT)

/-- `findnext('=', e, 2)` for a `String` (`base/strings/search.jl:143-166`):
`nothing` if `2 == ncodeunits(e) + 1`, `BoundsError` if `2 > ncodeunits(e) + 1`,
`StringIndexError` unless `2` is a character index, else the index of the first
`'='` at or after byte 2. -/
def findEq2 (e : JS) : SH (Option Int) :=
  let n : Int := ncu e
  if (2 : Int) = n + 1 then .ok none
  else if (2 : Int) > n + 1 then .error (.jl .boundsError)
  else if !isStart e 2 then .error .stringIndex
  else .ok (((pairsFrom 1 e).find? (fun q => 2 ≤ q.1 && q.2 == A '=')).map (fun q => (q.1 : Int)))

/-- The display mode of `show_env`, `base/cmd.jl:148-160`. -/
inductive ShowEnvMode where
  | all | keys | redact | none
  deriving DecidableEq, Repr

/-- `show_env(io, env)`, `base/cmd.jl:162-183`: the strings it passes to
`show`, in order. `sens` is `is_sensitive_env_name` (`base/cmd.jl:142-146`);
it is only consulted after `findnext`. -/
def showEnv (mode : ShowEnvMode) (sens : JS → Bool) : List JS → SH (List JS)
  | [] => .ok []
  | e :: es => do
    let eqidx ← findEq2 e
    let shown ← match eqidx with
      | none => pure e
      | some i =>
        if mode == .all then pure e
        else do
          let key ← slice e 1 (prevind e i)
          pure (if mode == .keys then key else if sens key then key else e)
    let rest ← showEnv mode sens es
    pure (shown :: rest)

/-- Whether `show(io, cmd)` (`base/cmd.jl:185-225`) completes, for a `Cmd`
without uid, gid and CPU list: in mode `:none` the environment is not shown. -/
def showCmdEnvOk (mode : ShowEnvMode) (sens : JS → Bool) (c : CmdM) : Bool :=
  match c.env with
  | some env => mode == .none || (showEnv mode sens env).toOption.isSome
  | none => true

/-! ### `setenv` and `addenv` -/

/-- `cstr(s)`, `base/cmd.jl:316-321`. -/
def cstr (s : JS) : SH JS :=
  if s.contains (A '\x00') then
    .error (.jl (.argumentError "strings containing NUL cannot be passed to spawned processes"))
  else .ok s

/-- `byteenv` of pairs `k => v` with string values, `base/cmd.jl:329-330`. -/
def byteenvPairs (kvs : List (JS × JS)) : SH (List JS) :=
  kvs.mapM (fun kv => cstr (kv.1 ++ [A '='] ++ kv.2))

/-- `setenv(cmd, pairs...)`, `base/cmd.jl:358-360`. -/
def setenvPairs (c : CmdM) (kvs : List (JS × JS)) : SH CmdM := do
  let env ← byteenvPairs kvs
  pure { c with env := some env }

/-- `splitenv(e)`, `base/cmd.jl:364-370`. -/
def splitenv (e : JS) : SH (JS × JS) := do
  let i ← findEq2 e
  match i with
  | none => .error (.jl (.argumentError "malformed environment entry"))
  | some i => do
    let k ← slice e 1 (prevind e i)
    let v ← slice e (i + 1) (lastindex e)
    pure (k, v)

/-- `d[k] = v` for the association-list model of a `Dict`. -/
def dset (d : List (JS × JS)) (k v : JS) : List (JS × JS) :=
  if d.any (·.1 == k) then d.map (fun kv => if kv.1 == k then (k, v) else kv) else d ++ [(k, v)]

/-- `delete!(d, k)`. -/
def ddel (d : List (JS × JS)) (k : JS) : List (JS × JS) := d.filter (·.1 != k)

/-- `get(d, k, nothing)`. -/
def dget (d : List (JS × JS)) (k : JS) : Option JS := (d.find? (·.1 == k)).map (·.2)

/-- `Dict(k => v for (k, v) in pairs)`: later pairs replace earlier ones. -/
def dictOf (kvs : List (JS × Option JS)) : List (JS × Option JS) :=
  kvs.foldl (fun d kv =>
    if d.any (·.1 == kv.1) then d.map (fun x => if x.1 == kv.1 then kv else x) else d ++ [kv]) []

/-- `addenv(cmd, pairs...; inherit)`, `base/cmd.jl:385-408`; `v = none` is
`nothing`. `ENV` is the parent environment as key/value pairs. -/
def addenv (envENV : List (JS × JS)) (inherit : Bool) (c : CmdM) (kvs : List (JS × Option JS)) :
    SH CmdM := do
  let base ← match c.env with
    | none => pure (if inherit then envENV.foldl (fun d kv => dset d kv.1 kv.2) [] else [])
    | some env => do
      let split ← env.mapM splitenv
      pure (split.foldl (fun d kv => dset d kv.1 kv.2) [])
  let newEnv := (dictOf kvs).foldl (fun d kv =>
    match kv.2 with
    | none => ddel d kv.1
    | some v => dset d kv.1 v) base
  let env ← byteenvPairs newEnv
  pure { c with env := some env }

/-! ### Interpolation, `base/cmd.jl:579-635` -/

/-- An element of an interpolated collection: a value with its `string(x)`, or `nothing`. -/
inductive Elem where
  | val (s : JS)
  | nothing
  deriving DecidableEq, Repr

/-- A part of a word of a parsed command literal: a literal or interpolated
`AbstractString`, an interpolated iterable collection, an interpolated `Cmd`,
or an interpolated non-iterable value (or `nothing`). -/
inductive Part where
  | str (s : JS)
  | iter (xs : List Elem)
  | cmd (c : CmdM)
  | scalar (x : Elem)
  deriving Repr

/-- `cmd_interpolate1` followed by `string`, `base/cmd.jl:581-583`. -/
def interp1 : Elem → SH JS
  | .val s => .ok s
  | .nothing => .error (.jl (.argumentError "`nothing` can not be interpolated into commands (`Cmd`)"))

/-- `arg_gen(head)` for one part, `base/cmd.jl:589-607`. -/
def argGen1 : Part → SH (List JS)
  | .str s => do let s ← cstr s; pure [s]
  | .cmd c =>
    if hasNondefaultFlags c then
      .error (.jl (.argumentError "Non-default environment behavior is only permitted for the first interpolant."))
    else .ok c.exec
  | .iter xs => xs.mapM (fun x => do let s ← interp1 x; cstr s)
  | .scalar x => do let s ← interp1 x; let s ← cstr s; pure [s]

/-- `arg_gen(head, tail...)`, `base/cmd.jl:588-617`: `cmd_interpolate(h, t)` for
every `h` of the head and `t` of the tail, head varying slowest. -/
def argGen : List Part → SH (List JS)
  | [] => .ok []
  | [p] => argGen1 p
  | p :: ps => do
    let head ← argGen1 p
    let tail ← argGen ps
    head.flatMap (fun h => tail.map (fun t => h ++ t)) |>.mapM cstr

/-- `cmd_gen(parsed)`, `base/cmd.jl:619-635`. -/
def cmdGen (parsed : List (List Part)) : SH CmdM :=
  match parsed with
  | [Part.cmd c] :: rest => do
    let more ← rest.mapM argGen
    pure { c with exec := c.exec ++ more.flatten }
  | _ => do
    let args ← parsed.mapM argGen
    pure (cmdOf args.flatten)

end JuliaLean.ShellCmd

namespace JuliaLean.Streams

/-! ## Commands and processes -/

abbrev CmdM := JuliaLean.ShellCmd.CmdM

inductive CommandM where
  | leaf (cmd : CmdM)
  | stdoutPipe (left right : CommandM)
  | stderrPipe (left right : CommandM)
  | concurrent (left right : CommandM)
  | redirect (cmd : CommandM)
  deriving Repr, DecidableEq

inductive ProcessErr where
  | methodError
  | processFailed (processes : List Nat)
  deriving Repr, DecidableEq

abbrev PR (α : Type) := Except ProcessErr α

/-- `pipeline(a,b,c...)` is a left fold, `base/cmd.jl:543-576`. -/
def pipelineMany (first : CommandM) (rest : List CommandM) : CommandM :=
  rest.foldl .stdoutPipe first

/-- `ignorestatus`, `base/cmd.jl:297-305`. Master omits `ErrOrCmds`, the
constructor represented by `stderrPipe`. -/
def ignoreStatus : CommandM → PR CommandM
  | .leaf cmd => .ok (.leaf { cmd with ignorestatus := true })
  | .stdoutPipe a b => do return .stdoutPipe (← ignoreStatus a) (← ignoreStatus b)
  | .concurrent a b => do return .concurrent (← ignoreStatus a) (← ignoreStatus b)
  | .redirect cmd => do return .redirect (← ignoreStatus cmd)
  | .stderrPipe _ _ => .error .methodError

def detachedFlag : UInt32 := 8

/-- `detach(::Cmd)`, `base/cmd.jl:308-312`. -/
def detachCmd (cmd : CmdM) : CmdM := { cmd with flags := cmd.flags ||| detachedFlag }

/-- Public `detach(command)`. Master defines only the leaf `Cmd` method. -/
def detachCommand : CommandM → PR CommandM
  | .leaf cmd => .ok (.leaf (detachCmd cmd))
  | _ => .error .methodError

end JuliaLean.Streams

namespace JuliaLean.IOCov.Cmd

open JuliaLean
open JuliaLean.ShellCmd

/-! ## Constructors and command flags -/

/-- `Cmd(exec::Vector{<:AbstractString})`, `base/cmd.jl:22-23`. -/
def cmdExec (exec : List JS) : CmdM := cmdOf exec

/-- `Cmd(cmd, ignorestatus, flags, env, dir, cpus, uid, gid)`,
`base/cmd.jl:24-26`.  `sameDir` models the `dir === cmd.dir` identity test. -/
def cmdCopy (cmd : CmdM) (ignorestatus : Bool) (flags : UInt32)
    (env : Option (List JS)) (dir : JS) (sameDir : Bool)
    (cpus : Option (List UInt16)) (uid gid : Option UInt32) : SH CmdM := do
  let dir <- if sameDir then pure dir else cstr dir
  pure (CmdM.mk cmd.exec ignorestatus flags env dir cpus uid gid)

/-- The three libuv flags assembled by the keyword `Cmd` constructor,
`base/cmd.jl:34-36`. -/
def keywordFlags (detach windowsVerbatim windowsHide : Bool) : UInt32 :=
  (if detach then 8 else 0) ||| (if windowsVerbatim then 4 else 0) |||
    (if windowsHide then 16 else 0)

/-- `Cmd(cmd::Cmd; ...)`, `base/cmd.jl:27-39`, after `byteenv` converts `env`.
`sameDir` is the source identity test. -/
def cmdKeywords (cmd : CmdM) (ignorestatus : Bool) (env : Option (List JS))
    (dir : JS) (sameDir : Bool) (cpus : Option (List UInt16)) (uid gid : Option UInt32)
    (detach windowsVerbatim windowsHide : Bool) : SH CmdM := do
  let dir <- if sameDir then pure dir else cstr dir
  pure (CmdM.mk cmd.exec ignorestatus (keywordFlags detach windowsVerbatim windowsHide)
    env dir cpus uid gid)

/-- `has_nondefault_cmd_flags`, `base/cmd.jl:42-49`. -/
def hasNondefault (c : CmdM) : Bool := hasNondefaultFlags c

structure BinaryCmd where
  a : CmdM
  b : CmdM
  deriving DecidableEq, Repr

/-- `OrCmds(a, b)`, `base/cmd.jl:106`. -/
def orCmds (a b : CmdM) : BinaryCmd := ⟨a, b⟩
/-- `ErrOrCmds(a, b)`, `base/cmd.jl:112`. -/
def errOrCmds (a b : CmdM) : BinaryCmd := ⟨a, b⟩
/-- `AndCmds(a, b)`, `base/cmd.jl:118`. -/
def andCmds (a b : CmdM) : BinaryCmd := ⟨a, b⟩

/-- `hash(x::AndCmds, h)`, `base/cmd.jl:121`. -/
def hashAnd (hashCmd : CmdM -> Nat -> Nat) (x : BinaryCmd) (h : Nat) : Nat :=
  hashCmd x.a (hashCmd x.b h)

/-- `==(x::AndCmds, y::AndCmds)`, `base/cmd.jl:122`. -/
def eqAnd (x y : BinaryCmd) : Bool := x.a == y.a && x.b == y.b

/-! ## Escape forwarding -/

/-- `shell_escape(cmd::Cmd; special)`, `base/cmd.jl:124-125`. -/
def shellEscapeCmd (cmd : CmdM) (special : JS) : JS := shellEscape cmd.exec special
/-- `shell_escape_posixly(cmd::Cmd)`, `base/cmd.jl:126-127`. -/
def shellEscapePosixlyCmd (cmd : CmdM) : JS := shellEscapePosixly cmd.exec
/-- `shell_escape_csh(cmd::Cmd)`, `base/cmd.jl:128-129`. -/
def shellEscapeCshCmd (cmd : CmdM) : SH JS := shellEscapeCsh cmd.exec
/-- `escape_microsoft_c_args(cmd::Cmd)`, `base/cmd.jl:130-131`. -/
def escapeMicrosoftCmd (cmd : CmdM) : SH JS := escapeMicrosoftCArgs cmd.exec
/-- `escape_microsoft_c_args(io, cmd::Cmd)`, `base/cmd.jl:132-133`.
The model returns the bytes written to `io`. -/
def escapeMicrosoftCmdIO (cmd : CmdM) : SH JS := escapeMicrosoftCArgs cmd.exec

/-! ## Sensitive environment display -/

def isAsciiAlphaNum (c : JC) : Bool :=
  (A 'A' <= c && c <= A 'Z') || (A 'a' <= c && c <= A 'z') ||
    (A '0' <= c && c <= A '9')

def upperAscii (c : JC) : JC :=
  if A 'a' <= c && c <= A 'z' then c - A 'a' + A 'A' else c

def lowerAscii (c : JC) : JC :=
  if A 'A' <= c && c <= A 'Z' then c - A 'A' + A 'a' else c

private def splitPartsGo : JS -> JS -> List JS
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | c :: cs, cur =>
      if isAsciiAlphaNum c then splitPartsGo cs (c :: cur)
      else (if cur.isEmpty then [] else [cur.reverse]) ++ splitPartsGo cs []

/-- `eachsplit(uppercase(name), r"[^A-Za-z0-9]+")`, `base/cmd.jl:143-144`. -/
def sensitiveParts (name : JS) : List JS := splitPartsGo (name.map upperAscii) []

def sensitivePatterns : List JS :=
  [S "KEY", S "TOKEN", S "SECRET", S "JWT", S "PAT", S "PASSWORD", S "PASSWD",
   S "PASS", S "PWD", S "PW", S "CREDENTIAL", S "CRED", S "AUTH", S "PRIVATE", S "PRIV"]

/-- `is_sensitive_env_name`, `base/cmd.jl:142-146`. -/
def isSensitiveEnvName (name : JS) : Bool :=
  (sensitiveParts name).any (fun part => sensitivePatterns.contains part)

inductive ContextShowEnv where
  | unset
  | mode (m : ShowEnvMode)
  | wrongType
  deriving DecidableEq, Repr

/-- `get_show_env_mode`, `base/cmd.jl:148-160`. -/
def getShowEnvMode (ctx : ContextShowEnv) (envval : Option JS) : SH ShowEnvMode :=
  match ctx with
  | .mode m => .ok m
  | .wrongType => .error .typeError
  | .unset =>
      match envval with
      | none => .ok .redact
      | some value =>
          let value := value.map lowerAscii
          if value == S "all" then .ok .all
          else if value == S "none" then .ok .none
          else if value == S "keys" then .ok .keys
          else .ok .redact

inductive OrKind where | stdout | stderr deriving DecidableEq, Repr

/-- `show(io, ::Union{OrCmds,ErrOrCmds})`, `base/cmd.jl:227-234`, represented
by its printed character sequence. -/
def showOrCmds (render : CmdM -> JS) (kind : OrKind) (cmds : BinaryCmd) : JS :=
  S "pipeline(" ++ render cmds.a ++ S ", " ++
    (if kind == .stderr then S "stderr=" else S "stdout=") ++ render cmds.b ++ S ")"

/-- `show(io, ::AndCmds)`, `base/cmd.jl:236-240`. -/
def showAndCmds (render : CmdM -> JS) (cmds : BinaryCmd) : JS :=
  render cmds.a ++ S " & " ++ render cmds.b

/-! ## Redirect values -/

structure FileRedirectM where
  filename : JS
  append : Bool
  warned : Bool
  deriving DecidableEq, Repr

/-- Inner `FileRedirect(filename::String, append)`, `base/cmd.jl:250-255`.
`isWindows` selects the static platform branch. -/
def fileRedirectString (isWindows : Bool) (filename : JS) (append : Bool) : FileRedirectM :=
  let nullName := if isWindows then S "nul" else S "/dev/null"
  { filename, append, warned := filename.map lowerAscii == nullName }

/-- Outer `FileRedirect(filename::AbstractString, append)`, `base/cmd.jl:249`. -/
def fileRedirectAbstract (isWindows : Bool) (filename : JS) (append : Bool) : FileRedirectM :=
  fileRedirectString isWindows filename append

inductive RawHandle where
  | null
  | handle (n : Int)
  deriving DecidableEq, Repr

/-- `rawhandle(::DevNull)`, `base/cmd.jl:260`. -/
def rawhandleDevNull : RawHandle := .null
/-- `rawhandle(x::OS_HANDLE)`, `base/cmd.jl:261`. -/
def rawhandleOS (x : Int) : RawHandle := .handle x
/-- `rawhandle(x::RawFD)`, `base/cmd.jl:263`, with the Unix `_get_osfhandle`. -/
def rawhandleFD (x : Int) : RawHandle := .handle x
/-- `setup_stdio`, `base/cmd.jl:265`. -/
def setupStdio (stdio : RawHandle) (_readable : Bool) : RawHandle × Bool := (stdio, false)

structure CmdRedirectM where
  cmd : CmdM
  handle : RawHandle
  streamNo : Int
  readable : Bool
  deriving DecidableEq, Repr

/-- Three-argument `CmdRedirect`, `base/cmd.jl:276`. -/
def cmdRedirect3 (cmd : CmdM) (handle : RawHandle) (streamNo : Int) : CmdRedirectM :=
  { cmd, handle, streamNo, readable := streamNo == 0 }

/-- `show(io, cr::CmdRedirect)`, `base/cmd.jl:278-294`. -/
def showCmdRedirect (renderCmd : CmdM -> JS) (renderHandle : RawHandle -> JS)
    (cr : CmdRedirectM) : JS :=
  let stream := if cr.streamNo == 1 then S "stdout"
    else if cr.streamNo == 2 then S "stderr"
    else if cr.streamNo == 0 then S "stdin"
    else S (toString cr.streamNo)
  S "pipeline(" ++ renderCmd cr.cmd ++ S ", " ++ stream ++
    (if cr.readable then S "<" else S ">") ++ renderHandle cr.handle ++ S ")"

/-! ## Command transformations and environments -/

/-- `ignorestatus(cmd::Cmd)`, `base/cmd.jl:301`. -/
def ignoreStatusCmd (cmd : CmdM) : CmdM := { cmd with ignorestatus := true }

/-- `ignorestatus` for `OrCmds` and `AndCmds`, `base/cmd.jl:302-303`. -/
def ignoreStatusBinary (cmd : BinaryCmd) : BinaryCmd :=
  ⟨ignoreStatusCmd cmd.a, ignoreStatusCmd cmd.b⟩

/-- `ignorestatus(cmd::CmdRedirect)`, `base/cmd.jl:304-305`. -/
def ignoreStatusRedirect (cmd : CmdRedirectM) : CmdRedirectM :=
  { cmd with cmd := ignoreStatusCmd cmd.cmd }

/-- `detach(cmd::Cmd)`, `base/cmd.jl:312`. -/
def detachCmd (cmd : CmdM) : CmdM :=
  { cmd with flags := keywordFlags true (cmd.flags &&& 4 != 0) (cmd.flags &&& 16 != 0) }

/-- `byteenv(env::AbstractArray{<:AbstractString})`, `base/cmd.jl:324-325`. -/
def byteenvArray (env : List JS) : SH (List JS) := env.mapM cstr

/-- `byteenv(env::AbstractDict)`, `base/cmd.jl:326-327`. -/
def byteenvDict (env : List (JS × JS)) : SH (List JS) := byteenvPairs env

/-- `byteenv(::Nothing)`, `base/cmd.jl:328`. -/
def byteenvNothing : Option (List JS) := none

/-- `byteenv` for vectors or tuples of pairs, `base/cmd.jl:329-330`. -/
def byteenvPairList (env : List (JS × JS)) : SH (List JS) := byteenvPairs env

/-- `setenv(cmd, env; dir)`, `base/cmd.jl:358`. -/
def setenvArray (cmd : CmdM) (env : List JS) (dir : JS) : SH CmdM := do
  let env <- byteenvArray env
  cmdKeywords cmd cmd.ignorestatus (some env) dir (dir == cmd.dir) cmd.cpus cmd.uid cmd.gid
    (cmd.flags &&& 8 != 0) (cmd.flags &&& 4 != 0) (cmd.flags &&& 16 != 0)

/-- Vararg-pair `setenv`, `base/cmd.jl:359-360`. -/
def setenvVarargs (cmd : CmdM) (env : List (JS × JS)) : SH CmdM := setenvPairs cmd env

/-- `setenv(cmd; dir)`, `base/cmd.jl:361`. -/
def setenvDir (cmd : CmdM) (dir : JS) : SH CmdM :=
  cmdKeywords cmd cmd.ignorestatus cmd.env dir (dir == cmd.dir) cmd.cpus cmd.uid cmd.gid
    (cmd.flags &&& 8 != 0) (cmd.flags &&& 4 != 0) (cmd.flags &&& 16 != 0)

/-- Dictionary `addenv`, `base/cmd.jl:385-404`. -/
def addenvDict (parent : List (JS × JS)) (cmd : CmdM)
    (env : List (JS × Option JS)) (inherit : Bool) : SH CmdM :=
  addenv parent inherit cmd env

/-- Pair-vararg `addenv`, including the `Dict` conversion, `base/cmd.jl:406-408`. -/
def addenvPairsMethod (parent : List (JS × JS)) (cmd : CmdM)
    (pairs : List (JS × Option JS)) (inherit : Bool) : SH CmdM :=
  addenv parent inherit cmd (dictOf pairs)

/-- Vector-string `addenv`, including `splitenv.(env)` and `Dict`,
`base/cmd.jl:410-412`. -/
def addenvVector (parent : List (JS × JS)) (cmd : CmdM)
    (env : List JS) (inherit : Bool) : SH CmdM := do
  let pairs <- env.mapM splitenv
  addenv parent inherit cmd ((pairs.foldl (fun d kv => dset d kv.1 kv.2) []).map
    (fun kv => (kv.1, some kv.2)))

/-- `setcpuaffinity(cmd, nothing)`, `base/cmd.jl:444`. -/
def setCpuNothing (cmd : CmdM) : CmdM := { cmd with cpus := none }
/-- `setcpuaffinity(cmd, cpus)`, `base/cmd.jl:445`, after `collect(UInt16, cpus)`. -/
def setCpuValues (cmd : CmdM) (cpus : List UInt16) : CmdM := { cmd with cpus := some cpus }
/-- `setuid(cmd, nothing)`, `base/cmd.jl:468`. -/
def setUidNothing (cmd : CmdM) : CmdM := { cmd with uid := none }
/-- `setgid(cmd, nothing)`, `base/cmd.jl:492`. -/
def setGidNothing (cmd : CmdM) : CmdM := { cmd with gid := none }

/-! ## Pipelines and interpolation -/

inductive PipeNode where
  | cmd (c : CmdM)
  | and (a b : PipeNode)
  | out (a b : PipeNode)
  | err (a b : PipeNode)
  | redirect (cmd : PipeNode) (handle : RawHandle) (streamNo : Int) (readable : Bool)
  deriving DecidableEq, Repr

/-- `(&)(left, right)`, `base/cmd.jl:495`. -/
def andNode (left right : PipeNode) : PipeNode := .and left right
/-- Command destination `redir_out`, `base/cmd.jl:496`. -/
def redirOutCmd (src dest : PipeNode) : PipeNode := .out src dest
/-- Command destination `redir_err`, `base/cmd.jl:497`. -/
def redirErrCmd (src dest : PipeNode) : PipeNode := .err src dest
/-- Redirectable source `redir_out`, `base/cmd.jl:500`. -/
def redirOutFromHandle (dest : RawHandle) (src : PipeNode) : PipeNode := .redirect src dest 0 true
/-- Redirectable destination `redir_out`, `base/cmd.jl:501`. -/
def redirOutToHandle (src : PipeNode) (dest : RawHandle) : PipeNode := .redirect src dest 1 false
/-- Redirectable destination `redir_err`, `base/cmd.jl:502`. -/
def redirErrToHandle (src : PipeNode) (dest : RawHandle) : PipeNode := .redirect src dest 2 false

/-- File destination `redir_out`, `base/cmd.jl:505`. -/
def redirOutFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 1 false
/-- File source `redir_out`, `base/cmd.jl:506`. -/
def redirInFile (fileId : Int) (dest : PipeNode) : PipeNode := .redirect dest (.handle fileId) 0 true
/-- File destination `redir_err`, `base/cmd.jl:507`. -/
def redirErrFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 2 false
/-- Append file destination `redir_out_append`, `base/cmd.jl:508`. -/
def redirOutAppendFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 1 false
/-- Append file destination `redir_err_append`, `base/cmd.jl:509`. -/
def redirErrAppendFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 2 false

/-- Keyword `pipeline`, `base/cmd.jl:527-541`. -/
def pipelineKeywords (cmd : PipeNode) (stdin stdout stderr : Option RawHandle)
    (append : Bool) : SH PipeNode := do
  if append && stdout.isNone && stderr.isNone then
    .error (.jl (.argumentError "append set to true, but no output redirections specified"))
  let cmd := match stdin with | none => cmd | some h => redirOutFromHandle h cmd
  let cmd := match stdout with | none => cmd | some h => redirOutToHandle cmd h
  let cmd := match stderr with | none => cmd | some h => redirErrToHandle cmd h
  pure cmd

/-- Two-argument `pipeline(cmd, dest)`, `base/cmd.jl:543`. -/
def pipelineTo (cmd : PipeNode) (dest : RawHandle) : SH PipeNode :=
  pipelineKeywords cmd none (some dest) none false
/-- Two-argument `pipeline(src, cmd)`, `base/cmd.jl:544`. -/
def pipelineFrom (src : RawHandle) (cmd : PipeNode) : SH PipeNode :=
  pipelineKeywords cmd (some src) none none false
/-- File-descriptor-pair `pipeline`, `base/cmd.jl:556`. -/
def pipelineFd (cmd : PipeNode) (fd : Int) (dest : RawHandle) : PipeNode :=
  .redirect cmd dest fd (fd == 0)

/-- Variadic `pipeline(a,b,c,d...)`, `base/cmd.jl:576`, left associated. -/
def pipelineMany : PipeNode -> List PipeNode -> PipeNode
  | a, [] => a
  | a, b :: rest => pipelineMany (.out a b) rest

/-- `cmd_interpolate1(x)`, `base/cmd.jl:582`. -/
def cmdInterpolateIdentity (x : JS) : JS := x
/-- `cmd_interpolate1(::Nothing)`, `base/cmd.jl:583`. -/
def cmdInterpolateNothing : SH JS :=
  .error (.jl (.argumentError "`nothing` can not be interpolated into commands (`Cmd`)"))
/-- `cmd_redirect_target(x::Redirectable)`, `base/cmd.jl:585`. -/
def cmdRedirectTargetHandle (x : RawHandle) : RawHandle := x
/-- Generic `cmd_redirect_target`, `base/cmd.jl:586`. -/
def cmdRedirectTargetValue (x : Elem) : SH JS := interp1 x

/-- `arg_gen()`, `base/cmd.jl:588`. -/
def argGen0 : List JS := []
/-- `arg_gen(x::AbstractString)`, `base/cmd.jl:589`. -/
def argGenString (x : JS) : SH (List JS) := do pure [<- cstr x]
/-- `arg_gen(cmd::Cmd)`, `base/cmd.jl:590-595`. -/
def argGenCmd (cmd : CmdM) : SH (List JS) := argGen1 (.cmd cmd)
/-- Generic one-argument `arg_gen`, `base/cmd.jl:597-607`. -/
def argGenHead (head : Part) : SH (List JS) := argGen1 head
/-- Variadic `arg_gen`, `base/cmd.jl:609-617`. -/
def argGenTail (head : Part) (tail : List Part) : SH (List JS) := argGen (head :: tail)
/-- Generic `cmd_gen`, `base/cmd.jl:619-635`. -/
def cmdGenAny (parsed : List (List Part)) : SH CmdM := cmdGen parsed
/-- Foldable tuple-specialized `cmd_gen`, `base/cmd.jl:637-641`. -/
def cmdGenTuple (parsed : List (List Part)) : SH CmdM := cmdGenAny parsed

inductive CmdMacroResult where
  | tuple (parsed : List (List Part))
  | expression (id : Nat)

/-- `@cmd`, `base/cmd.jl:659-668`, after `shell_parse` returns its expression. -/
def cmdMacro : CmdMacroResult -> Except Nat (SH CmdM)
  | .tuple parsed => .ok (cmdGen parsed)
  | .expression id => .error id


end JuliaLean.IOCov.Cmd
