import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.Runtime.Float
import JuliaLean.base.filesystem
import JuliaLean.base.strings.substring

/-!
# Model of `base/stat.jl`

Typed models of the filesystem metadata methods in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
The stat buffer, C field accessors, path conversions, Julia dispatch, printing, libc lookup, and
IOBuffer operations are explicit inputs. `StatStruct` stores the machine-width fields and IEEE
`Float64` bit patterns used by the source.
-/

namespace JuliaLean.base.stat

open JuliaLean
open JuliaLean.base.io (M)

abbrev I32 := JInt .i32
abbrev I64 := JInt .i64
abbrev U32 := JInt .u32
abbrev U64 := JInt .u64
abbrev Byte := JInt .u8
abbrev F64 := JuliaLean.Promotion.Fl JuliaLean.Promotion.double
abbrev ErrorOps := JuliaLean.base.filesystem.ErrorOps

inductive StatDesc (Handle : Type) where
  | path (value : String)
  | handle (value : Handle)
  deriving Repr

structure StatDisplayOps (World IO : Type) where
  print : {A : Type} → IO → A → M World Unit
  showValue : {A : Type} → IO → A → M World Unit
  fileModeString : U64 → M World String
  uvErrorName : I32 → M World String
  uvErrorText : I32 → M World String
  decimalUnsigned : U64 → M World String
  decimalSigned : I64 → M World String
  octalMode : U64 → M World String
  time : Unit → M World F64
  timeToUInt : F64 → M World U64
  subtractTime : F64 → U64 → M World F64
  absoluteTime : F64 → M World F64
  divideTime : F64 → I64 → M World F64
  roundTimeToInt : F64 → M World I64
  timeIsNegative : F64 → Bool
  strftime : F64 → M World String

def zeroF64 : F64 := JuliaLean.Promotion.Fl.ofBits 0
-- Reason: The export list and module declarations are load-time metadata; the typed methods are modeled below.
-- UNTRANSLATED
-- Source: base/stat.jl:1-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # filesystem operations
-- 
-- export
--     ctime,
--     filemode,
--     filesize,
--     gperm,
--     isblockdev,
--     ischardev,
--     isdir,
--     isfifo,
--     isfile,
--     islink,
--     ismount,
--     ispath,
--     issetgid,
--     issetuid,
--     issocket,
--     issticky,
--     lstat,
--     mtime,
--     operm,
--     stat,
--     uperm
-- 
-- /Source
/--
Julia source: base/stat.jl:28-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    StatStruct

A struct which stores information about a file. Usually
constructed by calling [`stat`](@ref) on a path.

This struct is used internally as the foundation of a number of utility
functions. Some return specific parts of the information stored in it
directly, such as [`filesize`](@ref), [`mtime`](@ref) and [`ctime`](@ref). Others add
some logic on top using bit-manipulation, such as [`isfifo`](@ref), [`ischardev`](@ref), and [`issetuid`](@ref).

The following fields of this struct are considered public API:

| Name    | Type                            | Description                                                        |
|:--------|:--------------------------------|:-------------------------------------------------------------------|
| desc    | `Union{String, Base.OS_HANDLE}` | The path or OS file descriptor                                     |
| size    | `Int64`                         | The size (in bytes) of the file                                    |
| device  | `UInt`                          | ID of the device that contains the file                            |
| inode   | `UInt`                          | The inode number of the file                                       |
| mode    | `UInt`                          | The protection mode of the file                                    |
| nlink   | `Int`                           | The number of hard links to the file                               |
| uid     | `UInt`                          | The user id of the owner of the file                               |
| gid     | `UInt`                          | The group id of the file owner                                     |
| rdev    | `UInt`                          | If this file refers to a device, the ID of the device it refers to |
| blksize | `Int64`                         | The file-system preferred block size for the file                  |
| blocks  | `Int64`                         | The number of 512-byte blocks allocated                            |
| mtime   | `Float64`                       | Unix timestamp of when the file was last modified                  |
| ctime   | `Float64`                       | Unix timestamp of when the file's metadata was changed             |

See also [`stat`](@ref).
"""
struct StatStruct
    desc    :: Union{String, OS_HANDLE} # for show method, not included in equality or hash
    device  :: UInt
    inode   :: UInt
    mode    :: UInt
    nlink   :: Int
    uid     :: UInt
    gid     :: UInt
    rdev    :: UInt
    size    :: Int64
    blksize :: Int64
    blocks  :: Int64
    mtime   :: Float64
    ctime   :: Float64
    ioerrno :: Int32
end
```
-/
structure StatStruct (Handle : Type) where
  desc : StatDesc Handle
  device : U64
  inode : U64
  mode : U64
  nlink : I64
  uid : U64
  gid : U64
  rdev : U64
  size : I64
  blksize : I64
  blocks : I64
  mtime : F64
  ctime : F64
  ioerrno : I32
  deriving Repr
/-- Runtime services and dispatch supplied by the filesystem and libc layers. `PathVal` is a Julia
value of a type the model does not construct itself: an argument of `joinpath`/`stat(path...)`, or an
`AbstractString` that is neither a `String` nor a `SubString{String}` (`PathString.other`). -/
structure StatOps (World Handle CString StatMemory IOBuf User Group PathVal : Type) where
  errors : ErrorOps World
  uvNoEnt : I32
  uvNoDir : I32
  uvInvalid : I32
  sizeofStat : Unit → M World I32
  i32ToI64 : I32 → M World I64
  allocateStat : I64 → M World StatMemory
  zeroStat : StatMemory → M World Unit
  statCString : CString → StatMemory → M World I32
  lstatCString : CString → StatMemory → M World I32
  fstatHandle : Handle → StatMemory → M World I32
  statDevice : StatMemory → M World U32
  statInode : StatMemory → M World U32
  statMode : StatMemory → M World U32
  statNlink : StatMemory → M World U32
  statUid : StatMemory → M World U32
  statGid : StatMemory → M World U32
  statRdev : StatMemory → M World U32
  statSize : StatMemory → M World U64
  statBlockSize : StatMemory → M World U64
  statBlocks : StatMemory → M World U64
  statMtime : StatMemory → M World F64
  statCtime : StatMemory → M World F64
  /-- `Base.unsafe_convert(Cstring, path)` of a `String` (`ArgumentError` when it contains `\0`). -/
  toCString : String → M World CString
  /-- `String(s)::String` of an `AbstractString` other than `String` and `SubString{String}`:
  `String(s::AbstractString) = print_to_string(s)` (`base/strings/string.jl:192`) with the type's own
  `print` method, a typed parameter since AbstractString subtypes are user-extensible. -/
  otherString : PathVal → M World String
  /-- A `SubString{String}` whose bytes are not UTF-8 text the model's `String` can hold. -/
  unrepresentablePath : M World String
  /-- `repr(path)` of a `String`. -/
  repr : String → M World String
  reprDesc : StatDesc Handle → M World String
  /-- `typeof(path)` as printed by `"$(typeof(path))"`. -/
  typeName : PathVal → M World String
  /-- `path2 isa typeof(path)`. -/
  sameType : PathVal → PathVal → Bool
  /-- `joinpath(path)` and `joinpath(path...)`. -/
  joinOne : PathVal → M World PathVal
  joinMany : List PathVal → M World PathVal
  /-- `stat(x)` and `lstat(x)` of one argument: Julia's dispatch over the argument's type. -/
  statDispatch : PathVal → M World (StatStruct Handle)
  lstatDispatch : PathVal → M World (StatStruct Handle)
  pathAccess : CString → I32 → M World I32
  newStringBuffer : Unit → M World IOBuf
  writeString : IOBuf → String → M World I64
  takeString : IOBuf → M World String
  /-- `Libc.getpwuid(uid::Unsigned, false)` and `Libc.getgrgid(gid::Unsigned, false)` for an id of
  any unsigned `BitInteger` type. -/
  getUser : {t : IntTy} → JInt t → Bool → M World (Option User)
  userName : User → M World String
  getGroup : {t : IntTy} → JInt t → Bool → M World (Option Group)
  groupName : Group → M World String
  isEmpty : String → M World Bool
/--
Julia source: base/stat.jl:76-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval function Base.:(==)(x::StatStruct, y::StatStruct) # do not include `desc` in equality or hash
    $(let ex = true
        for fld in fieldnames(StatStruct)[2:end]
            ex = :(getfield(x, $(QuoteNode(fld))) === getfield(y, $(QuoteNode(fld))) && $ex)
        end
        Expr(:return, ex)
    end)
end
@eval function Base.hash(obj::StatStruct, h::UInt)
    $(quote
        $(Any[:(h = hash(getfield(obj, $(QuoteNode(fld))), h)) for fld in fieldnames(StatStruct)[2:end]]...)
        return h
    end)
end
```
-/
def statStructEqual {Handle : Type} (same : {A : Type} → A → A → Bool)
    (x y : StatStruct Handle) : Bool :=
  same x.ioerrno y.ioerrno && same x.ctime y.ctime && same x.mtime y.mtime &&
  same x.blocks y.blocks && same x.blksize y.blksize && same x.size y.size &&
  same x.rdev y.rdev && same x.gid y.gid && same x.uid y.uid &&
  same x.nlink y.nlink && same x.mode y.mode && same x.inode y.inode && same x.device y.device

def statStructHash {Handle : Type} (hashValue : {A : Type} → A → U64 → U64)
    (value : StatStruct Handle) (seed : U64) : U64 :=
  let seed := hashValue value.device seed
  let seed := hashValue value.inode seed
  let seed := hashValue value.mode seed
  let seed := hashValue value.nlink seed
  let seed := hashValue value.uid seed
  let seed := hashValue value.gid seed
  let seed := hashValue value.rdev seed
  let seed := hashValue value.size seed
  let seed := hashValue value.blksize seed
  let seed := hashValue value.blocks seed
  let seed := hashValue value.mtime seed
  let seed := hashValue value.ctime seed
  hashValue value.ioerrno seed
/--
Julia source: base/stat.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StatStruct() = StatStruct("", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Base.UV_ENOENT)
```
-/
def emptyStatStruct {Handle : Type} (uvNoEnt : I32) : StatStruct Handle :=
  ⟨.path "", JInt.lit .u64 0, JInt.lit .u64 0, JInt.lit .u64 0, JInt.lit .i64 0,
    JInt.lit .u64 0, JInt.lit .u64 0, JInt.lit .u64 0, JInt.lit .i64 0,
    JInt.lit .i64 0, JInt.lit .i64 0, zeroF64, zeroF64, uvNoEnt⟩
/--
Julia source: base/stat.jl:92-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StatStruct(buf::Union{Memory{UInt8},Vector{UInt8},Ptr{UInt8}}, ioerrno::Int32) = StatStruct("", buf, ioerrno)
StatStruct(desc::Union{AbstractString, OS_HANDLE}, buf::Union{Memory{UInt8},Vector{UInt8},Ptr{UInt8}}, ioerrno::Int32) = StatStruct(
    desc isa OS_HANDLE ? desc : String(desc),
    ioerrno != 0 ? zero(UInt32) : ccall(:jl_stat_dev,     UInt32,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt32) : ccall(:jl_stat_ino,     UInt32,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt32) : ccall(:jl_stat_mode,    UInt32,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt32) : ccall(:jl_stat_nlink,   UInt32,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt32) : ccall(:jl_stat_uid,     UInt32,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt32) : ccall(:jl_stat_gid,     UInt32,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt32) : ccall(:jl_stat_rdev,    UInt32,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt64) : ccall(:jl_stat_size,    UInt64,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt64) : ccall(:jl_stat_blksize, UInt64,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(UInt64) : ccall(:jl_stat_blocks,  UInt64,  (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(Float64) : ccall(:jl_stat_mtime,   Float64, (Ptr{UInt8},), buf),
    ioerrno != 0 ? zero(Float64) : ccall(:jl_stat_ctime,   Float64, (Ptr{UInt8},), buf),
    ioerrno
)
```
-/
def statStructFromBuffer {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (desc : StatDesc Handle)
    (buffer : Memory) (ioerrno : I32) : M World (StatStruct Handle) := do
  let device ← if ioerrno.val == 0 then ops.statDevice buffer else pure (JInt.lit .u32 0)
  let inode ← if ioerrno.val == 0 then ops.statInode buffer else pure (JInt.lit .u32 0)
  let mode ← if ioerrno.val == 0 then ops.statMode buffer else pure (JInt.lit .u32 0)
  let nlink ← if ioerrno.val == 0 then ops.statNlink buffer else pure (JInt.lit .u32 0)
  let uid ← if ioerrno.val == 0 then ops.statUid buffer else pure (JInt.lit .u32 0)
  let gid ← if ioerrno.val == 0 then ops.statGid buffer else pure (JInt.lit .u32 0)
  let rdev ← if ioerrno.val == 0 then ops.statRdev buffer else pure (JInt.lit .u32 0)
  let size ← if ioerrno.val == 0 then do
    let raw ← ops.statSize buffer
    JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 raw)
    else pure (JInt.lit .i64 0)
  let blksize ← if ioerrno.val == 0 then do
    let raw ← ops.statBlockSize buffer
    JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 raw)
    else pure (JInt.lit .i64 0)
  let blocks ← if ioerrno.val == 0 then do
    let raw ← ops.statBlocks buffer
    JuliaLean.base.io.liftJl (JuliaLean.base.int.convert .i64 raw)
    else pure (JInt.lit .i64 0)
  let mtime ← if ioerrno.val == 0 then ops.statMtime buffer else pure zeroF64
  let ctime ← if ioerrno.val == 0 then ops.statCtime buffer else pure zeroF64
  pure ⟨desc, JInt.wrap .u64 device.val, JInt.wrap .u64 inode.val, JInt.wrap .u64 mode.val,
    JInt.wrap .i64 nlink.val, JInt.wrap .u64 uid.val, JInt.wrap .u64 gid.val,
    JInt.wrap .u64 rdev.val, size, blksize, blocks, mtime, ctime, ioerrno⟩

def statStructFromBufferOnly {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (buffer : Memory) (ioerrno : I32) : M World (StatStruct Handle) := do
  statStructFromBuffer ops (.path "") buffer ioerrno
/--
Julia source: base/stat.jl:110-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iso_datetime_with_relative(t, tnow)
    str = Libc.strftime("%FT%T%z", t)
    secdiff = t - tnow
    for (d, name) in ((24*60*60, "day"), (60*60, "hour"), (60, "minute"), (1, "second"))
        tdiff = round(Int, div(abs(secdiff), d))
        if tdiff != 0 # find first unit difference
            plural = tdiff == 1 ? "" : "s"
            when = secdiff < 0 ? "ago" : "in the future"
            return "$str ($tdiff $name$plural $when)"
        end
    end
    return "$str (just now)"
end
```
-/
def isoDatetimeWithRelative {World IO : Type} (ops : StatDisplayOps World IO)
    (timeValue : F64) (now : U64) : M World String := do
  let formatted ← ops.strftime timeValue
  let difference ← ops.subtractTime timeValue now
  let durations : List (I64 × String) :=
    [(JInt.lit .i64 86400, "day"), (JInt.lit .i64 3600, "hour"),
     (JInt.lit .i64 60, "minute"), (JInt.lit .i64 1, "second")]
  let rec findDifference : List (I64 × String) → M World String
    | [] => pure (formatted ++ " (just now)")
    | (duration, name) :: rest => do
        let absolute ← ops.absoluteTime difference
        let scaled ← ops.divideTime absolute duration
        let rounded ← ops.roundTimeToInt scaled
        if rounded.val != 0 then
          let plural := if rounded.val == 1 then "" else "s"
          let relative := if ops.timeIsNegative difference then "ago" else "in the future"
          let amount ← ops.decimalSigned rounded
          pure (formatted ++ " (" ++ amount ++ " " ++ name ++ plural ++ " " ++ relative ++ ")")
        else findDifference rest
  findDifference durations
/--
Julia source: base/stat.jl:125-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getusername(uid::Unsigned)
    pwd = Libc.getpwuid(uid, false)
    pwd === nothing && return
    isempty(pwd.username) && return
    return pwd.username
end
```
-/
def getUserName {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) {t : IntTy}
    (_unsigned : t.signed = false) (uid : JInt t) :
    M World (Option String) := do
  match ← ops.getUser uid false with
  | none => pure none
  | some entry =>
    let name ← ops.userName entry
    if ← ops.isEmpty name then pure none else pure (some name)
/--
Julia source: base/stat.jl:132-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getgroupname(gid::Unsigned)
    gp = Libc.getgrgid(gid, false)
    gp === nothing && return
    isempty(gp.groupname) && return
    return gp.groupname
end
```
-/
def getGroupName {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) {t : IntTy}
    (_unsigned : t.signed = false) (gid : JInt t) :
    M World (Option String) := do
  match ← ops.getGroup gid false with
  | none => pure none
  | some entry =>
    let name ← ops.groupName entry
    if ← ops.isEmpty name then pure none else pure (some name)
/--
Julia source: base/stat.jl:139-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_statstruct(io::IO, st::StatStruct, oneline::Bool)
    print(io, oneline ? "StatStruct(" : "StatStruct for ")
    show(io, st.desc)
    code = st.ioerrno
    if code != 0
        print(io, oneline ? " " : "\n ")
        print(io, Base.uverrorname(code), ": ", Base.struverror(code))
    else
        oneline || print(io, "\n  ")
        print(io, " size: ", st.size, " bytes")
        oneline || print(io, "\n")
        print(io, " device: ", st.device)
        oneline || print(io, "\n ")
        print(io, " inode: ", st.inode)
        oneline || print(io, "\n  ")
        print(io, " mode: 0o", string(filemode(st), base = 8, pad = 6), " (", filemode_string(st), ")")
        oneline || print(io, "\n ")
        print(io, " nlink: ", st.nlink)
        oneline || print(io, "\n   ")
        print(io, " uid: $(st.uid)")
        username = getusername(st.uid)
        username === nothing || print(io, " (", username, ")")
        oneline || print(io, "\n   ")
        print(io, " gid: ", st.gid)
        groupname = getgroupname(st.gid)
        groupname === nothing || print(io, " (", groupname, ")")
        oneline || print(io, "\n  ")
        print(io, " rdev: ", st.rdev)
        oneline || print(io, "\n ")
        print(io, " blksz: ", st.blksize)
        oneline || print(io, "\n")
        print(io, " blocks: ", st.blocks)
        tnow = round(UInt, time())
        oneline || print(io, "\n ")
        print(io, " mtime: ", iso_datetime_with_relative(st.mtime, tnow))
        oneline || print(io, "\n ")
        print(io, " ctime: ", iso_datetime_with_relative(st.ctime, tnow))
    end
    oneline && print(io, ")")
    return nothing
end
```
-/
def showStatStruct {World Handle CString Memory IOBuf User Group PathVal IO : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (display : StatDisplayOps World IO) (io : IO) (value : StatStruct Handle)
    (oneline : Bool) : M World Unit := do
  display.print io (if oneline then "StatStruct(" else "StatStruct for ")
  display.showValue io value.desc
  let code := value.ioerrno
  if code.val != 0 then
    display.print io (if oneline then " " else "\n ")
    display.print io (← display.uvErrorName code)
    display.print io ": "
    display.print io (← display.uvErrorText code)
  else
    if !oneline then display.print io "  "
    display.print io " size: "
    display.print io value.size
    display.print io " bytes"
    if !oneline then display.print io "\n"
    display.print io " device: "
    display.print io value.device
    if !oneline then display.print io "\n "
    display.print io " inode: "
    display.print io value.inode
    if !oneline then display.print io "\n  "
    let modeOctal ← display.octalMode value.mode
    let modeText ← display.fileModeString value.mode
    display.print io (" mode: 0o" ++ modeOctal ++ " (" ++ modeText ++ ")")
    if !oneline then display.print io "\n "
    display.print io " nlink: "
    display.print io value.nlink
    if !oneline then display.print io "\n   "
    display.print io (" uid: " ++ (← display.decimalUnsigned value.uid))
    match ← getUserName ops (t := .u64) rfl value.uid with
    | none => pure ()
    | some name => display.print io (" (" ++ name ++ ")")
    if !oneline then display.print io "\n   "
    display.print io " gid: "
    display.print io value.gid
    match ← getGroupName ops (t := .u64) rfl value.gid with
    | none => pure ()
    | some name => display.print io (" (" ++ name ++ ")")
    if !oneline then display.print io "\n  "
    display.print io " rdev: "
    display.print io value.rdev
    if !oneline then display.print io "\n "
    display.print io " blksz: "
    display.print io value.blksize
    if !oneline then display.print io "\n"
    display.print io " blocks: "
    display.print io value.blocks
    let now ← display.timeToUInt (← display.time ())
    if !oneline then display.print io "\n "
    display.print io " mtime: "
    display.print io (← isoDatetimeWithRelative display value.mtime now)
    if !oneline then display.print io "\n "
    display.print io " ctime: "
    display.print io (← isoDatetimeWithRelative display value.ctime now)
  if oneline then display.print io ")"
  pure ()
/--
Julia source: base/stat.jl:181-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, st::StatStruct) = show_statstruct(io, st, true)
show(io::IO, ::MIME"text/plain", st::StatStruct) = show_statstruct(io, st, false)
```
-/
def showStat {World Handle CString Memory IOBuf User Group PathVal IO : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (display : StatDisplayOps World IO) (io : IO) (value : StatStruct Handle) : M World Unit :=
  showStatStruct ops display io value true

def showStatPlain {World Handle CString Memory IOBuf User Group PathVal IO MIME : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (display : StatDisplayOps World IO) (_mime : MIME) (io : IO) (value : StatStruct Handle) :
    M World Unit :=
  showStatStruct ops display io value false
/--
Julia source: base/stat.jl:184-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# stat & lstat functions

checkstat(s::StatStruct) = Int(s.ioerrno) in (0, Base.UV_ENOENT, Base.UV_ENOTDIR, Base.UV_EINVAL) ? s :
    _uv_error(string("stat(", repr(s.desc), ")"), s.ioerrno)
```
-/
def checkStat {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (value : StatStruct Handle) : M World (StatStruct Handle) := do
  let code := value.ioerrno
  if code.val == 0 || code.val == ops.uvNoEnt.val || code.val == ops.uvNoDir.val ||
      code.val == ops.uvInvalid.val then pure value
  else do
    let description ← ops.reprDesc value.desc
    ops.errors.uvError ("stat(" ++ description ++ ")") code
    pure value
-- Reason: The @stat_call macro is load-time code generation; its expanded C-call bodies are modeled below.
-- UNTRANSLATED
-- Source: base/stat.jl:189-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro stat_call(sym, arg1type, arg)
--     return quote
--         stat_buf = fill!(Memory{UInt8}(undef, Int(ccall(:jl_sizeof_stat, Int32, ()))), 0x00)
--         # GC-safe, so that a `stat` blocked on a slow or hung filesystem doesn't hold up garbage
--         # collection, and with it every other thread that allocates
--         r = @ccall gc_safe=true $sym($(esc(arg))::$(esc(arg1type)), stat_buf::Ptr{UInt8})::Int32
--         return checkstat(StatStruct($(esc(arg)), stat_buf, r))
--     end
-- end
-- /Source
/--
Julia source: base/stat.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stat(fd::OS_HANDLE)         = @stat_call jl_fstat OS_HANDLE fd
```
-/
def statHandle {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (handle : Handle) : M World (StatStruct Handle) := do
  let size ← ops.i32ToI64 (← ops.sizeofStat ())
  let buffer ← ops.allocateStat size
  ops.zeroStat buffer
  let status ← ops.fstatHandle handle buffer
  checkStat ops (← statStructFromBuffer ops (.handle handle) buffer status)
/-- A `path::AbstractString` argument of `stat`, `lstat`, `samefile` and `ispath`. A `String` and a
`SubString{String}` are the Base types the model converts itself, with the installed
`String(s::SubString{String})` (`base/strings/substring.jl:133-137`); any other `AbstractString`
(`LazyString`, `SubString` of a non-`String`, user types) is a `PathVal` converted by the type's own
`print` method (`StatOps.otherString`). -/
inductive PathString (PathVal : Type) where
  | string (value : String)
  | substring (value : JuliaLean.base.strings.substring.SubString String)
  | other (value : PathVal)

instance {PathVal : Type} : Coe String (PathString PathVal) := ⟨PathString.string⟩

/-- `String(s::SubString{String})` (`base/strings/substring.jl:133-137`): the installed
`stringFromSubString` over a `String` parent, copying `ncodeunits` bytes from `pointer(parent,
offset + 1)`; `none` when the copied bytes are not valid UTF-8. -/
def stringOfSubString (s : JuliaLean.base.strings.substring.SubString String) : Option String :=
  match JuliaLean.base.strings.substring.stringFromSubString (S := String) (Out := Option String)
      (E := Empty)
      { pointer := fun _ index => index
        unsafeString := fun parent first count => .ok
          (String.fromUTF8? (ByteArray.mk
            ((parent.toUTF8.toList.drop (first.val - 1).toNat).take count.val.toNat).toArray)) } s with
  | .ok text => text
  | .error e => nomatch e

/-- `String(path)::String` of a path argument: `String(s::String) = s` (`base/boot.jl:611`),
`String(s::SubString{String})`, and `String(s::AbstractString) = print_to_string(s)`
(`base/strings/string.jl:192`). It is also the `cconvert(Cstring, path)` of the `ccall` in `stat`
(`cconvert(::Type{Cstring}, s::AbstractString) = cconvert(Cstring, String(s)::String)`,
`base/strings/cstring.jl:65-67`). -/
def stringOfPath {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) :
    PathString PathVal → M World String
  | .string value => pure value
  | .substring value =>
      match stringOfSubString value with
      | some text => pure text
      | none => ops.unrepresentablePath
  | .other value => ops.otherString value

/--
Julia source: base/stat.jl:200-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function stat(path::AbstractString)
    # @info "stat($(repr(path)))" exception=(ErrorException("Fake error for backtrace printing"),stacktrace())
    @stat_call jl_stat  Cstring path
end
function lstat(path::AbstractString)
    # @info "lstat($(repr(path)))" exception=(ErrorException("Fake error for backtrace printing"),stacktrace())
    @stat_call jl_lstat Cstring path
end
```
-/
def statPath {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (path : PathString PathVal) : M World (StatStruct Handle) := do
  let size ← ops.i32ToI64 (← ops.sizeofStat ())
  let buffer ← ops.allocateStat size
  ops.zeroStat buffer
  let cpath ← ops.toCString (← stringOfPath ops path)
  let status ← ops.statCString cpath buffer
  checkStat ops (← statStructFromBuffer ops (.path (← stringOfPath ops path)) buffer status)

def lstatPath {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (path : PathString PathVal) : M World (StatStruct Handle) := do
  let size ← ops.i32ToI64 (← ops.sizeofStat ())
  let buffer ← ops.allocateStat size
  ops.zeroStat buffer
  let cpath ← ops.toCString (← stringOfPath ops path)
  let status ← ops.lstatCString cpath buffer
  checkStat ops (← statStructFromBuffer ops (.path (← stringOfPath ops path)) buffer status)
/--
Julia source: base/stat.jl:208-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if RawFD !== OS_HANDLE
    global stat(fd::RawFD)  = stat(Libc._get_osfhandle(fd))
end
```
-/
def statRawFD {World Handle CString Memory IOBuf User Group PathVal RawFD : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (getOsHandle : RawFD → M World Handle) (rawFd : RawFD) : M World (StatStruct Handle) := do
  statHandle ops (← getOsHandle rawFd)
/--
Julia source: base/stat.jl:212-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    stat(path)
    stat(path_elements...)

Return a structure whose fields contain information about the file.
If multiple arguments are given, they are joined by [`joinpath`](@ref).

The fields of the structure are:

| Name    | Type                            | Description                                                        |
|:--------|:--------------------------------|:-------------------------------------------------------------------|
| desc    | `Union{String, Base.OS_HANDLE}` | The path or OS file descriptor                                     |
| size    | `Int64`                         | The size (in bytes) of the file                                    |
| device  | `UInt`                          | ID of the device that contains the file                            |
| inode   | `UInt`                          | The inode number of the file                                       |
| mode    | `UInt`                          | The protection mode of the file                                    |
| nlink   | `Int`                           | The number of hard links to the file                               |
| uid     | `UInt`                          | The user id of the owner of the file                               |
| gid     | `UInt`                          | The group id of the file owner                                     |
| rdev    | `UInt`                          | If this file refers to a device, the ID of the device it refers to |
| blksize | `Int64`                         | The file-system preferred block size for the file                  |
| blocks  | `Int64`                         | The number of 512-byte blocks allocated                            |
| mtime   | `Float64`                       | Unix timestamp of when the file was last modified                  |
| ctime   | `Float64`                       | Unix timestamp of when the file's metadata was changed             |
"""
stat(path) = (path2 = joinpath(path); path2 isa typeof(path) ? error("stat not implemented for $(typeof(path))") : stat(path2))
stat(path...) = stat(joinpath(path...))
```
-/
def statOneFallback {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (path : PathVal) :
    M World (StatStruct Handle) := do
  let joined ← ops.joinOne path
  if ops.sameType path joined then
    let name ← ops.typeName path
    throw (.foreignError "ErrorException" ("stat not implemented for " ++ name))
  else ops.statDispatch joined

def statMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) :
    M World (StatStruct Handle) := do
  ops.statDispatch (← ops.joinMany paths)
/--
Julia source: base/stat.jl:240-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    lstat(path)
    lstat(path_elements...)

Like [`stat`](@ref), but for symbolic links gets the info
for the link itself rather than the file it refers to.

This function must be called on a file path rather
than a file object or a file descriptor.
"""
lstat(path) = (path2 = joinpath(path); path2 isa typeof(path) ? error("lstat not implemented for $(typeof(path))") : lstat(path2))
lstat(path...) = lstat(joinpath(path...))
```
-/
def lstatOneFallback {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (path : PathVal) :
    M World (StatStruct Handle) := do
  let joined ← ops.joinOne path
  if ops.sameType path joined then
    let name ← ops.typeName path
    throw (.foreignError "ErrorException" ("lstat not implemented for " ++ name))
  else ops.lstatDispatch joined

def lstatMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) :
    M World (StatStruct Handle) := do
  ops.lstatDispatch (← ops.joinMany paths)

/--
Julia source: base/stat.jl:255-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const filemode_table = (
    [
        (S_IFLNK, "l"),
        (S_IFSOCK, "s"),  # Must appear before IFREG and IFDIR as IFSOCK == IFREG | IFDIR
        (S_IFREG, "-"),
        (S_IFBLK, "b"),
        (S_IFDIR, "d"),
        (S_IFCHR, "c"),
        (S_IFIFO, "p")
    ],
    [
        (S_IRUSR, "r"),
    ],
    [
        (S_IWUSR, "w"),
    ],
    [
        (S_IXUSR|S_ISUID, "s"),
        (S_ISUID, "S"),
        (S_IXUSR, "x")
    ],
    [
        (S_IRGRP, "r"),
    ],
    [
        (S_IWGRP, "w"),
    ],
    [
        (S_IXGRP|S_ISGID, "s"),
        (S_ISGID, "S"),
        (S_IXGRP, "x")
    ],
    [
        (S_IROTH, "r"),
    ],
    [
        (S_IWOTH, "w"),
    ],
    [
        (S_IXOTH|S_ISVTX, "t"),
        (S_ISVTX, "T"),
        (S_IXOTH, "x")
    ]
)
```
-/
def filemodeTable : List (List (JInt .u16 × String)) :=
  [[(JuliaLean.base.filesystem.sIflnk, "l"),
    (JuliaLean.base.filesystem.sIfsock, "s"),
    (JuliaLean.base.filesystem.sIfreg, "-"),
    (JuliaLean.base.filesystem.sIfblk, "b"),
    (JuliaLean.base.filesystem.sIfdir, "d"),
    (JuliaLean.base.filesystem.sIfchr, "c"),
    (JuliaLean.base.filesystem.sIfifo, "p")],
   [(JuliaLean.base.filesystem.sIrusr, "r")],
   [(JuliaLean.base.filesystem.sIwusr, "w")],
   [(JuliaLean.base.int.or_int JuliaLean.base.filesystem.sIxusr
        JuliaLean.base.filesystem.sIsuid, "s"),
    (JuliaLean.base.filesystem.sIsuid, "S"),
    (JuliaLean.base.filesystem.sIxusr, "x")],
   [(JuliaLean.base.filesystem.sIrgrp, "r")],
   [(JuliaLean.base.filesystem.sIwgrp, "w")],
   [(JuliaLean.base.int.or_int JuliaLean.base.filesystem.sIxgrp
        JuliaLean.base.filesystem.sIsgid, "s"),
    (JuliaLean.base.filesystem.sIsgid, "S"),
    (JuliaLean.base.filesystem.sIxgrp, "x")],
   [(JuliaLean.base.filesystem.sIroth, "r")],
   [(JuliaLean.base.filesystem.sIwoth, "w")],
   [(JuliaLean.base.int.or_int JuliaLean.base.filesystem.sIxoth
        JuliaLean.base.filesystem.sIsvtx, "t"),
    (JuliaLean.base.filesystem.sIsvtx, "T"),
    (JuliaLean.base.filesystem.sIxoth, "x")]]
/--
Julia source: base/stat.jl:300-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    filemode(path)
    filemode(path_elements...)
    filemode(stat_struct)

Return the mode of the file located at `path`,
or the mode indicated by the file descriptor `stat_struct`.

Equivalent to `stat(path).mode` or `stat_struct.mode`.
"""
filemode(st::StatStruct) = st.mode
filemode_string(st::StatStruct) = filemode_string(st.mode)
function filemode_string(mode)
    str = IOBuffer()
    for table in filemode_table
        complete = true
        for (bit, char) in table
            if mode & bit == bit
                write(str, char)
                complete = false
                break
            end
        end
        complete && write(str, "-")
    end
    return unsafe_takestring!(str)
```
-/
def fileMode {Handle : Type} (value : StatStruct Handle) : U64 := value.mode

/-- `x == y` of two `BitInteger`s of any types (`base/int.jl:577-589` for mixed signedness; the
`promote`d `==` otherwise). -/
def eqBitInteger {a b : IntTy} (x : JInt a) (y : JInt b) : Bool :=
  if a.signed && !b.signed then JuliaLean.base.int.eq_BitSigned_BitUnsigned x y
  else if !a.signed && b.signed then JuliaLean.base.int.eq_BitUnsigned_BitSigned x y
  else JuliaLean.base.int.eq_int (JuliaLean.base.int.widenTo (a.promote b) x)
    (JuliaLean.base.int.widenTo (a.promote b) y)

/-- `mode & bit == bit` (`base/stat.jl:317`) for a `BitInteger` `mode` and a `UInt16` bit: `&` of
two `Integer`s of different types converts both with `% T` to `promote_typeof` (`base/int.jl:1092-1100`,
installed `remT`). -/
def modeHasBit {t : IntTy} (mode : JInt t) (bit : JInt .u16) : Bool :=
  let T := t.promote .u16
  eqBitInteger (JuliaLean.base.int.and_int (JuliaLean.base.int.remT T mode)
    (JuliaLean.base.int.remT T bit)) bit

def fileModeGroup {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (buffer : IOBuf)
    {t : IntTy} (mode : JInt t) : List (JInt .u16 × String) → M World Bool
  | [] => pure true
  | (bit, character) :: rest => do
      if modeHasBit mode bit then
        let _ ← ops.writeString buffer character
        pure false
      else fileModeGroup ops buffer mode rest

def fileModeGroups {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (buffer : IOBuf)
    {t : IntTy} (mode : JInt t) : List (List (JInt .u16 × String)) → M World Unit
  | [] => pure ()
  | group :: rest => do
      let complete ← fileModeGroup ops buffer mode group
      if complete then
        let _ ← ops.writeString buffer "-"
        pure ()
      fileModeGroups ops buffer mode rest

/-- `filemode_string(mode)` (`base/stat.jl:312-325`) for a `BitInteger` `mode` of any type. -/
def fileModeString {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) {t : IntTy}
    (mode : JInt t) : M World String := do
  let buffer ← ops.newStringBuffer ()
  fileModeGroups ops buffer mode filemodeTable
  ops.takeString buffer

def fileModeStringStruct {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (value : StatStruct Handle) : M World String :=
  fileModeString ops (fileMode value)
/--
Julia source: base/stat.jl:328-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    filesize(path)
    filesize(path_elements...)
    filesize(stat_struct)

Return the size of the file located at `path`,
or the size indicated by file descriptor `stat_struct`.

Equivalent to `stat(path).size` or `stat_struct.size`.
"""
filesize(st::StatStruct) = st.size
```
-/
def fileSize {Handle : Type} (value : StatStruct Handle) : I64 := value.size
/--
Julia source: base/stat.jl:340-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    mtime(path)
    mtime(path_elements...)
    mtime(stat_struct)

Return the unix timestamp of when the file at `path` was last modified,
or the last modified timestamp indicated by the file descriptor `stat_struct`.

Equivalent to `stat(path).mtime` or `stat_struct.mtime`.
"""
mtime(st::StatStruct) = st.mtime
```
-/
def mtime {Handle : Type} (value : StatStruct Handle) : F64 := value.mtime
/--
Julia source: base/stat.jl:352-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    ctime(path)
    ctime(path_elements...)
    ctime(stat_struct)

Return the unix timestamp of when the metadata of the file at `path` was last modified,
or the last modified metadata timestamp indicated by the file descriptor `stat_struct`.

Equivalent to `stat(path).ctime` or `stat_struct.ctime`.
"""
ctime(st::StatStruct) = st.ctime
```
-/
def ctime {Handle : Type} (value : StatStruct Handle) : F64 := value.ctime
/--
Julia source: base/stat.jl:366-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    ispath(path)::Bool
    ispath(path_elements...)::Bool

Return `true` if a valid filesystem entity exists at `path`,
otherwise returns `false`.

This is the generalization of [`isfile`](@ref), [`isdir`](@ref) etc.
"""
ispath(st::StatStruct) = st.ioerrno == 0
function ispath(path::String)
    # We use `access()` and `F_OK` to determine if a given path exists. `F_OK` comes from `unistd.h`.
    F_OK = 0x00
    r = ccall(:jl_fs_access, Cint, (Cstring, Cint), path, F_OK)
    if !(r in (0, Base.UV_ENOENT, Base.UV_ENOTDIR, Base.UV_EINVAL))
        uv_error(string("ispath(", repr(path), ")"), r)
    end
    return r == 0
end
ispath(path::AbstractString) = ispath(String(path)::String)
```
-/
def isPathStat {Handle : Type} (value : StatStruct Handle) : Bool := value.ioerrno.val == 0

def isPathString {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (path : String) :
    M World Bool := do
  let cpath ← ops.toCString path
  let status ← ops.pathAccess cpath (JInt.lit .i32 0)
  let code := status.val
  if code != 0 && code != ops.uvNoEnt.val && code != ops.uvNoDir.val && code != ops.uvInvalid.val then
    let repr ← ops.repr path
    ops.errors.uvError ("ispath(" ++ repr ++ ")") status
  pure (status.val == 0)

def isPathAbstract {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (path : PathString PathVal) : M World Bool := do
  isPathString ops (← stringOfPath ops path)
def fileModeTypeIs {Handle : Type} (value : StatStruct Handle) (expected : U64) : Bool :=
  (JuliaLean.base.int.and_int (fileMode value) (JInt.lit .u64 0xf000)).val == expected.val

def fileModeFlagSet {Handle : Type} (value : StatStruct Handle) (flag : U64) : Bool :=
  (JuliaLean.base.int.and_int (fileMode value) flag).val > 0
/--
Julia source: base/stat.jl:388-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    isfifo(path)::Bool
    isfifo(path_elements...)::Bool
    isfifo(stat_struct)::Bool

Return `true` if the file at `path` or file descriptor `stat_struct` is FIFO, `false` otherwise.
"""
isfifo(st::StatStruct) = filemode(st) & 0xf000 == 0x1000

```
-/
def isFifo {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeTypeIs value (JInt.lit .u64 0x1000)
/--
Julia source: base/stat.jl:397-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ischardev(path)::Bool
    ischardev(path_elements...)::Bool
    ischardev(stat_struct)::Bool

Return `true` if the path `path` or file descriptor `stat_struct` refer to a character device, `false` otherwise.
"""
ischardev(st::StatStruct) = filemode(st) & 0xf000 == 0x2000
```
-/
def isCharDevice {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeTypeIs value (JInt.lit .u64 0x2000)
/--
Julia source: base/stat.jl:405-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isdir(path)::Bool
    isdir(path_elements...)::Bool

Return `true` if `path` points to a directory, `false` otherwise.

See also [`isfile`](@ref), [`ispath`](@ref).

# Examples
```jldoctest
julia> isdir(homedir())
true

julia> isdir("not/a/directory")
false
```
"""
isdir(st::StatStruct) = filemode(st) & 0xf000 == 0x4000
````
-/
def isDirectory {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeTypeIs value (JInt.lit .u64 0x4000)
/--
Julia source: base/stat.jl:424-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    isblockdev(path)::Bool
    isblockdev(path_elements...)::Bool
    isblockdev(stat_struct)::Bool

Return `true` if the path `path` or file descriptor `stat_struct` refer to a block device, `false` otherwise.
"""
isblockdev(st::StatStruct) = filemode(st) & 0xf000 == 0x6000
```
-/
def isBlockDevice {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeTypeIs value (JInt.lit .u64 0x6000)
/--
Julia source: base/stat.jl:433-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isfile(path)::Bool
    isfile(path_elements...)::Bool

Return `true` if `path` points to a regular file, `false` otherwise.

See also [`isdir`](@ref), [`ispath`](@ref).

# Examples
```jldoctest
julia> isfile(homedir())
false

julia> filename = "test_file.txt";

julia> write(filename, "Hello world!");

julia> isfile(filename)
true

julia> rm(filename);

julia> isfile(filename)
false
```
"""
isfile(st::StatStruct) = filemode(st) & 0xf000 == 0x8000
````
-/
def isRegularFile {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeTypeIs value (JInt.lit .u64 0x8000)
/--
Julia source: base/stat.jl:461-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    islink(path)::Bool
    islink(path_elements...)::Bool

Return `true` if `path` points to a symbolic link, `false` otherwise.
"""
islink(st::StatStruct) = filemode(st) & 0xf000 == 0xa000
```
-/
def isLink {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeTypeIs value (JInt.lit .u64 0xa000)
/--
Julia source: base/stat.jl:469-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    issocket(path)::Bool
    issocket(path_elements...)::Bool

Return `true` if `path` points to a socket, `false` otherwise.
"""
issocket(st::StatStruct) = filemode(st) & 0xf000 == 0xc000
```
-/
def isSocket {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeTypeIs value (JInt.lit .u64 0xc000)
/--
Julia source: base/stat.jl:479-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    issetuid(path)::Bool
    issetuid(path_elements...)::Bool
    issetuid(stat_struct)::Bool

Return `true` if the file at `path` or file descriptor `stat_struct` have the setuid flag set, `false` otherwise.
"""
issetuid(st::StatStruct) = (filemode(st) & 0o4000) > 0
```
-/
def isSetUid {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeFlagSet value (JInt.lit .u64 0o4000)
/--
Julia source: base/stat.jl:488-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    issetgid(path)::Bool
    issetgid(path_elements...)::Bool
    issetgid(stat_struct)::Bool

Return `true` if the file at `path` or file descriptor `stat_struct` have the setgid flag set, `false` otherwise.
"""
issetgid(st::StatStruct) = (filemode(st) & 0o2000) > 0
```
-/
def isSetGid {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeFlagSet value (JInt.lit .u64 0o2000)
/--
Julia source: base/stat.jl:497-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    issticky(path)::Bool
    issticky(path_elements...)::Bool
    issticky(stat_struct)::Bool

Return `true` if the file at `path` or file descriptor `stat_struct` have the sticky bit set, `false` otherwise.
"""
issticky(st::StatStruct) = (filemode(st) & 0o1000) > 0
```
-/
def isSticky {Handle : Type} (value : StatStruct Handle) : Bool :=
  fileModeFlagSet value (JInt.lit .u64 0o1000)
/--
Julia source: base/stat.jl:506-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    uperm(path)
    uperm(path_elements...)
    uperm(stat_struct)

Return a bitfield of the owner permissions for the file at `path` or file descriptor `stat_struct`.

| Value | Description        |
|:------|:-------------------|
| 01    | Execute Permission |
| 02    | Write Permission   |
| 04    | Read Permission    |

The fact that a bitfield is returned means that if the permission
is read+write, the bitfield is "110", which maps to the decimal
value of 0+2+4=6. This is reflected in the printing of the
returned `UInt8` value.

See also [`gperm`](@ref), [`operm`](@ref).

```jldoctest
julia> touch("dummy_file");  # Create test-file without contents

julia> uperm("dummy_file")
0x06

julia> bitstring(ans)
"00000110"

julia> has_read_permission(path) = uperm(path) & 0b00000100 != 0;  # Use bit mask to check specific bit

julia> has_read_permission("dummy_file")
true

julia> rm("dummy_file")     # Clean up test-file
```
"""
uperm(st::StatStruct) = UInt8((filemode(st) >> 6) & 0x7)
````
-/
def userPermissions {Handle : Type} (value : StatStruct Handle) : Byte :=
  let shifted := JuliaLean.base.int.lshr_int (fileMode value) (JInt.lit .u64 6)
  JInt.wrap .u8 (JuliaLean.base.int.and_int shifted (JInt.lit .u64 0x7)).val
/--
Julia source: base/stat.jl:545-554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    gperm(path)
    gperm(path_elements...)
    gperm(stat_struct)

Like [`uperm`](@ref) but gets the permissions of the group owning the file.

See also [`operm`](@ref).
"""
gperm(st::StatStruct) = UInt8((filemode(st) >> 3) & 0x7)
```
-/
def groupPermissions {Handle : Type} (value : StatStruct Handle) : Byte :=
  let shifted := JuliaLean.base.int.lshr_int (fileMode value) (JInt.lit .u64 3)
  JInt.wrap .u8 (JuliaLean.base.int.and_int shifted (JInt.lit .u64 0x7)).val
/--
Julia source: base/stat.jl:556-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    operm(path)
    operm(path_elements...)
    operm(stat_struct)

Like [`uperm`](@ref) but gets the permissions for people who neither own the
file nor are a member of the group owning the file.

See also [`gperm`](@ref).
"""
operm(st::StatStruct) = UInt8((filemode(st)     ) & 0x7)
```
-/
def otherPermissions {Handle : Type} (value : StatStruct Handle) : Byte :=
  JInt.wrap .u8 (JuliaLean.base.int.and_int (fileMode value) (JInt.lit .u64 0x7)).val
/--
Julia source: base/stat.jl:570-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in Symbol[
    :ispath,
    :isfifo,
    :ischardev,
    :isdir,
    :isblockdev,
    :isfile,
    :issocket,
    :issetuid,
    :issetgid,
    :issticky,
    :uperm,
    :gperm,
    :operm,
    :filemode,
    :filesize,
    :mtime,
    :ctime,
]
    @eval ($f)(path...)  = ($f)(stat(path...))
end
```
-/
def isPathMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isPathStat (← statMany ops paths))

def isFifoMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isFifo (← statMany ops paths))

def isCharDeviceMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isCharDevice (← statMany ops paths))

def isDirectoryMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isDirectory (← statMany ops paths))

def isBlockDeviceMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isBlockDevice (← statMany ops paths))

def isRegularFileMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isRegularFile (← statMany ops paths))

def isSocketMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isSocket (← statMany ops paths))

def isSetUidMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isSetUid (← statMany ops paths))

def isSetGidMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isSetGid (← statMany ops paths))

def isStickyMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isSticky (← statMany ops paths))

def userPermissionsMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Byte := do
  pure (userPermissions (← statMany ops paths))

def groupPermissionsMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Byte := do
  pure (groupPermissions (← statMany ops paths))

def otherPermissionsMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Byte := do
  pure (otherPermissions (← statMany ops paths))

def fileModeMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World U64 := do
  pure (fileMode (← statMany ops paths))

def fileSizeMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World I64 := do
  pure (fileSize (← statMany ops paths))

def mtimeMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World F64 := do
  pure (mtime (← statMany ops paths))

def ctimeMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World F64 := do
  pure (ctime (← statMany ops paths))
/--
Julia source: base/stat.jl:592-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islink(path...) = islink(lstat(path...))
```
-/
def isLinkMany {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal) : M World Bool := do
  pure (isLink (← lstatMany ops paths))
/--
Julia source: base/stat.jl:594-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# samefile can be used for files and directories: #11145#issuecomment-99511194
function samefile(a::StatStruct, b::StatStruct)
    ispath(a) && ispath(b) && a.device == b.device && a.inode == b.inode
end
```
-/
def sameFileStat {Handle : Type} (left right : StatStruct Handle) : Bool :=
  isPathStat left && isPathStat right && left.device == right.device && left.inode == right.inode
/--
Julia source: base/stat.jl:599-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    samefile(path_a, path_b)

Check if the paths `path_a` and `path_b` refer to the same existing file or directory.
"""
samefile(a::AbstractString, b::AbstractString) = samefile(stat(a), stat(b))
```
-/
def sameFilePaths {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal)
    (left right : PathString PathVal) : M World Bool := do
  let left ← statPath ops left
  let right ← statPath ops right
  pure (sameFileStat left right)
/--
Julia source: base/stat.jl:606-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    ismount(path)::Bool
    ismount(path_elements...)::Bool

Return `true` if `path` is a mount point, `false` otherwise.
"""
function ismount(path...)
    path = joinpath(path...)
    isdir(path) || return false
    s1 = lstat(path)
    # Symbolic links cannot be mount points
    islink(s1) && return false
    parent_path = joinpath(path, "..")
    s2 = lstat(parent_path)
    # If a directory and its parent are on different devices,  then the
    # directory must be a mount point
    (s1.device != s2.device) && return true
    (s1.inode == s2.inode) && return true
    false
end
```
-/
def isMount {World Handle CString Memory IOBuf User Group PathVal : Type}
    (ops : StatOps World Handle CString Memory IOBuf User Group PathVal) (paths : List PathVal)
    (joinParent : PathVal → String → M World PathVal) : M World Bool := do
  let path ← ops.joinMany paths
  if !(← isDirectoryMany ops [path]) then pure false
  else do
    let first ← lstatMany ops [path]
    if isLink first then pure false
    else do
      let parentPath ← joinParent path ".."
      let parent ← lstatMany ops [parentPath]
      if first.device != parent.device then pure true
      else if first.inode == parent.inode then pure true
      else pure false

end JuliaLean.base.stat

namespace JuliaLean.Files

/-! ## `StatStruct`, `base/stat.jl:59-105,310-338,375-566` -/

structure StatStruct where
  mode : Fin 65536
  size : Int
  ioerrno : Int
  deriving Repr, DecidableEq

def filemode (st : StatStruct) : Fin 65536 := st.mode
def modeType (st : StatStruct) : Nat := st.mode.val / 4096 % 16
def isdir (st : StatStruct) : Bool := modeType st == 4
def islink (st : StatStruct) : Bool := modeType st == 10
def ispath (st : StatStruct) : Bool := st.ioerrno == 0
def uperm (st : StatStruct) : Nat := st.mode.val / 64 % 8
def gperm (st : StatStruct) : Nat := st.mode.val / 8 % 8
def operm (st : StatStruct) : Nat := st.mode.val % 8
def filesize (st : StatStruct) : Int := st.size

end JuliaLean.Files

namespace JuliaLean.Files.Coverage

open JuliaLean.Files

/-! ## Stat construction and wrappers (`base/stat.jl:59-251`) -/

structure FullStat where
  desc : List Nat
  device : Nat
  inode : Nat
  mode : Nat
  nlink : Int
  uid : Nat
  gid : Nat
  rdev : Nat
  size : Int
  blksize : Int
  blocks : Int
  mtime : Int
  ctime : Int
  ioerrno : Int
  deriving Repr, DecidableEq

def statKey (stat : FullStat) : List Int :=
  [stat.device, stat.inode, stat.mode, stat.nlink, stat.uid, stat.gid, stat.rdev,
   stat.size, stat.blksize, stat.blocks, stat.mtime, stat.ctime, stat.ioerrno]

def statEqual (left right : FullStat) : Bool := statKey left == statKey right

def emptyStat : FullStat := ⟨[], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2⟩

def decodeStat (desc : List Nat) (raw : FullStat) (ioerrno : Int) : FullStat :=
  if ioerrno == 0 then { raw with desc, ioerrno }
  else { emptyStat with desc, ioerrno }

def checkStat (stat : FullStat) : Result FullStat :=
  if stat.ioerrno == 0 || stat.ioerrno == -2 || stat.ioerrno == -20 || stat.ioerrno == -22 then
    .ok stat
  else .error .io stat

inductive RelativeUnit where | day | hour | minute | second deriving Repr, DecidableEq

def relativeTime (difference : Int) : Option (RelativeUnit × Nat × Bool) :=
  let magnitude := difference.natAbs
  if magnitude / 86400 != 0 then some (RelativeUnit.day, magnitude / 86400, decide (difference > 0))
  else if magnitude / 3600 != 0 then some (RelativeUnit.hour, magnitude / 3600, decide (difference > 0))
  else if magnitude / 60 != 0 then some (RelativeUnit.minute, magnitude / 60, decide (difference > 0))
  else if magnitude != 0 then some (RelativeUnit.second, magnitude, decide (difference > 0))
  else none

def nonemptyName (name : Option (List Char)) : Option (List Char) :=
  match name with | some (head :: tail) => some (head :: tail) | _ => none

def fileTypeChar (mode : Nat) : Char :=
  match mode / 4096 % 16 with
  | 10 => 'l' | 12 => 's' | 8 => '-' | 6 => 'b' | 4 => 'd' | 2 => 'c' | 1 => 'p'
  | _ => '-'

def bitChar (enabled : Bool) (char : Char) : Char := if enabled then char else '-'

def executeChar (execute special : Bool) (low high : Char) : Char :=
  if special then if execute then low else high else if execute then 'x' else '-'

def fileModeString (mode : Nat) : List Char :=
  [fileTypeChar mode,
   bitChar (mode / 256 % 2 == 1) 'r', bitChar (mode / 128 % 2 == 1) 'w',
   executeChar (mode / 64 % 2 == 1) (mode / 2048 % 2 == 1) 's' 'S',
   bitChar (mode / 32 % 2 == 1) 'r', bitChar (mode / 16 % 2 == 1) 'w',
   executeChar (mode / 8 % 2 == 1) (mode / 1024 % 2 == 1) 's' 'S',
   bitChar (mode / 4 % 2 == 1) 'r', bitChar (mode / 2 % 2 == 1) 'w',
   executeChar (mode % 2 == 1) (mode / 512 % 2 == 1) 't' 'T']

def typeTest (mode kind : Nat) : Bool := mode / 4096 % 16 == kind
def specialTest (mode divisor : Nat) : Bool := mode / divisor % 2 == 1

inductive ShownStatField where
  | error
  | size | device | inode | mode | nlink | uid | gid | rdev | blksize | blocks | mtime | ctime
  deriving Repr, DecidableEq

def shownStatFields (ioerrno : Int) : List ShownStatField :=
  if ioerrno != 0 then [.error]
  else [.size, .device, .inode, .mode, .nlink, .uid, .gid, .rdev, .blksize, .blocks, .mtime, .ctime]

def statField (field : Nat) (stat : FullStat) : Int :=
  match field with
  | 0 => stat.mode | 1 => stat.size | 2 => stat.mtime | 3 => stat.ctime | _ => 0

def pathPredicate (field : Nat) (stat : FullStat) : Int := statField field stat

def pathExistsCall (returnCode : Int) : Result Bool :=
  if returnCode == 0 || returnCode == -2 || returnCode == -20 || returnCode == -22 then
    .ok (returnCode == 0)
  else .error .io false

def sameFile (left right : FullStat) : Bool :=
  left.ioerrno == 0 && right.ioerrno == 0 && left.device == right.device && left.inode == right.inode

def isMount (isDirectory isLink : Bool) (child parent : FullStat) : Bool :=
  isDirectory && !isLink && (child.device != parent.device || child.inode == parent.inode)

def statEqMethod (left right : FullStat) : Bool := statKey left == statKey right
def statHashMethod (stat : FullStat) : List Int := statKey stat
def statEmptyCtorMethod : FullStat := emptyStat
def statBufferCtorMethod (desc : List Nat) (raw : FullStat) (ioerrno : Int) : FullStat :=
  decodeStat desc raw ioerrno

def isoDatetimeMethod (timestamp now : Int) : Option (RelativeUnit × Nat × Bool) :=
  relativeTime (timestamp - now)

def getusernameMethod (lookup : Option (List Char)) : Option (List Char) := nonemptyName lookup
def getgroupnameMethod (lookup : Option (List Char)) : Option (List Char) := nonemptyName lookup

structure ShowStatMethodResult where
  oneline : Bool
  fields : List ShownStatField
  closesParen : Bool
  deriving Repr, DecidableEq

def showStatstructMethod (stat : FullStat) (oneline : Bool) : ShowStatMethodResult :=
  ⟨oneline, shownStatFields stat.ioerrno, oneline⟩

def showStatMethod (stat : FullStat) : ShowStatMethodResult := showStatstructMethod stat true
def showStatTextMethod (stat : FullStat) : ShowStatMethodResult := showStatstructMethod stat false

inductive StatCallEvent where
  | allocate (bytes : Nat)
  | zeroBuffer
  | statCall
  | decode
  | check
  deriving Repr, DecidableEq

def checkstatMethod (stat : FullStat) : Result FullStat := checkStat stat

def statCallMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  ([.allocate bufferBytes, .zeroBuffer, .statCall, .decode, .check], checkStat decoded)

def statHandleMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  statCallMethod bufferBytes decoded
def statPathMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  statCallMethod bufferBytes decoded
def lstatPathMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  statCallMethod bufferBytes decoded
def statRawFdMethod (convertedHandle : Nat) (bufferBytes : Nat) (decoded : FullStat) :
    Nat × (List StatCallEvent × Result FullStat) :=
  (convertedHandle, statHandleMethod bufferBytes decoded)

def statGenericMethod (sameType : Bool) (converted : Result FullStat) : Result FullStat :=
  if sameType then .error .errorException emptyStat else converted
def lstatGenericMethod (sameType : Bool) (converted : Result FullStat) : Result FullStat :=
  if sameType then .error .errorException emptyStat else converted
def statVarargsMethod (joined : Result FullStat) : Result FullStat := joined
def lstatVarargsMethod (joined : Result FullStat) : Result FullStat := joined

def filemodeMethod (stat : FullStat) : Nat := stat.mode
def filemodeStringStatMethod (stat : FullStat) : List Char := fileModeString stat.mode
def filemodeStringMethod (mode : Nat) : List Char := fileModeString mode
def filesizeMethod (stat : FullStat) : Int := stat.size
def mtimeMethod (stat : FullStat) : Int := stat.mtime
def ctimeMethod (stat : FullStat) : Int := stat.ctime
def ispathStatMethod (stat : FullStat) : Bool := stat.ioerrno == 0
def isfifoMethod (stat : FullStat) : Bool := typeTest stat.mode 1
def ischardevMethod (stat : FullStat) : Bool := typeTest stat.mode 2
def isdirMethod (stat : FullStat) : Bool := typeTest stat.mode 4
def isblockdevMethod (stat : FullStat) : Bool := typeTest stat.mode 6
def isfileMethod (stat : FullStat) : Bool := typeTest stat.mode 8
def islinkMethod (stat : FullStat) : Bool := typeTest stat.mode 10
def issocketMethod (stat : FullStat) : Bool := typeTest stat.mode 12
def issetuidMethod (stat : FullStat) : Bool := specialTest stat.mode 2048
def issetgidMethod (stat : FullStat) : Bool := specialTest stat.mode 1024
def isstickyMethod (stat : FullStat) : Bool := specialTest stat.mode 512
def upermMethod (stat : FullStat) : Nat := stat.mode / 64 % 8
def gpermMethod (stat : FullStat) : Nat := stat.mode / 8 % 8
def opermMethod (stat : FullStat) : Nat := stat.mode % 8

def ispathStringMethod (returnCode : Int) : Result Bool := pathExistsCall returnCode
def ispathAbstractStringMethod (stringResult : Result Bool) : Result Bool := stringResult

inductive StatAccessor where
  | path | fifo | charDevice | directory | blockDevice | file | socket
  | setuid | setgid | sticky | userPerm | groupPerm | otherPerm | mode | size | modified | changed
  deriving Repr, DecidableEq

def statAccessorMethod (accessor : StatAccessor) (stat : FullStat) : Int :=
  match accessor with
  | .path => if ispathStatMethod stat then 1 else 0
  | .fifo => if isfifoMethod stat then 1 else 0
  | .charDevice => if ischardevMethod stat then 1 else 0
  | .directory => if isdirMethod stat then 1 else 0
  | .blockDevice => if isblockdevMethod stat then 1 else 0
  | .file => if isfileMethod stat then 1 else 0
  | .socket => if issocketMethod stat then 1 else 0
  | .setuid => if issetuidMethod stat then 1 else 0
  | .setgid => if issetgidMethod stat then 1 else 0
  | .sticky => if isstickyMethod stat then 1 else 0
  | .userPerm => upermMethod stat
  | .groupPerm => gpermMethod stat
  | .otherPerm => opermMethod stat
  | .mode => stat.mode
  | .size => stat.size
  | .modified => stat.mtime
  | .changed => stat.ctime

def statPathAccessorMethod (accessor : StatAccessor) (statResult : FullStat) : Int :=
  statAccessorMethod accessor statResult
def islinkPathMethod (lstatResult : FullStat) : Bool := islinkMethod lstatResult
def samefileStatMethod (left right : FullStat) : Bool := sameFile left right
def samefilePathMethod (left right : FullStat) : Bool := samefileStatMethod left right
def ismountMethod (directory link : Bool) (child parent : FullStat) : Bool :=
  isMount directory link child parent

end JuliaLean.Files.Coverage
