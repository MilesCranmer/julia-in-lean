import JuliaLean.base.runtime_internals
import JuliaLean.base.io

/-!
# Model of `base/sysinfo.jl`

Typed model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Runtime and libuv calls are typed primitives over `base.io.M`. Their outputs,
return codes, allocation, reads, frees, errors and world changes remain explicit.
Julia counters use fixed-width `JInt`; floating division and rounding are supplied
by typed Float64 callees. Paths and CPU model strings remain generic, including
byte strings. CPU summaries group adjacent equal models in source order.
-/

namespace JuliaLean.base.sysinfo
open JuliaLean
open JuliaLean.base.io (M Error)
abbrev I := JInt64
abbrev U := JInt .u64
abbrev Cint := JInt .i32
def i (z : Int) : I := JInt.wrap .i64 z

structure InitOps (World Str : Type) where
  envCpuThreads : M World (Option Str)
  tryparseInt : Str → Option I
  jlCpuThreads : M World Cint
  jlEffectiveThreads : M World Cint
  warning : I → M World Unit
  setCpuThreads : I → M World Unit
  setEffectiveThreads : I → M World Unit
  jlClockTicks : M World I
  setClockTicks : I → M World Unit
  jlCpuName : M World Str
  setCpuName : Str → M World Unit
  jlJit : M World Str
  setJit : Str → M World Unit
  jlPagesize : M World I
  jlAllocationGranularity : M World I
  setPagesize : I → M World Unit
  isunix : Bool
  jlBindir : M World Str
  setBindir : Str → M World Unit
  datarootdir : Str
  versionMajor : Str
  versionMinor : Str
  literal : String → Str
  concat : List Str → M World Str
  abspath : List Str → M World Str
  setStdlib : Str → M World Unit

structure CPUFormat (World Stream Str Float : Type) where
  print : Stream → List Str → M World Unit
  println : Stream → List Str → M World Unit
  literal : String → Str
  length : Str → I
  repeatString : Str → I → M World Str
  lpad : Str → I → M World Str
  intString : I → M World Str
  divide : U → I → M World Float
  roundInt64 : Float → M World I
  concat : Str → Str → M World Str

structure WhichOps (World Path : Type) where
  literal : String → Path
  isEmpty : Path → Bool
  basename : Path → M World Path
  dirname : Path → M World Path
  extension : Path → M World Path
  concat : Path → Path → M World Path
  iswindows : Bool
  envPath : M World Path
  splitPath : Path → Bool → List Path
  abspath : Path → M World Path
  pwd : M World Path
  joinpath : Path → Path → M World Path
  isfile : Path → M World Bool
  isexecutable : Path → M World Bool
  isPermissionDeniedIOError : Error → Bool

/--
Julia source: base/sysinfo.jl:180-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __init_build()
    global BINDIR = ccall(:jl_get_julia_bindir, Any, ())::String
    vers = "v$(string(VERSION.major)).$(string(VERSION.minor))"
    global STDLIB = abspath(BINDIR, DATAROOTDIR, "julia", "stdlib", vers)
    nothing
end
```
-/
def initBuild {World Str : Type} (ops : InitOps World Str) : M World Unit := do
  let bindir ← ops.jlBindir
  ops.setBindir bindir
  let vers ← ops.concat [ops.literal "v", ops.versionMajor, ops.literal ".", ops.versionMinor]
  ops.setStdlib (← ops.abspath [bindir, ops.datarootdir, ops.literal "julia", ops.literal "stdlib", vers])
  pure ()

/--
Julia source: base/sysinfo.jl:155-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __init__()
    env_threads = nothing
    if haskey(ENV, "JULIA_CPU_THREADS")
        env_threads = ENV["JULIA_CPU_THREADS"]
    end
    global CPU_THREADS = if env_threads !== nothing
        env_threads = tryparse(Int, env_threads)
        if env_threads === nothing || env_threads <= 0
            env_threads = Int(ccall(:jl_cpu_threads, Int32, ()))
            Core.print(Core.stderr, "WARNING: couldn't parse `JULIA_CPU_THREADS` environment variable. Defaulting Sys.CPU_THREADS to $env_threads.\n")
        end
        env_threads
    else
        Int(ccall(:jl_cpu_threads, Int32, ()))
    end
    global EFFECTIVE_CPU_THREADS = min(CPU_THREADS, Int(ccall(:jl_effective_threads, Int32, ())))
    global SC_CLK_TCK = ccall(:jl_SC_CLK_TCK, Clong, ())
    global CPU_NAME = ccall(:jl_get_cpu_name, Ref{String}, ())
    global JIT = ccall(:jl_get_JIT, Ref{String}, ())
    global PAGESIZE = Int(Sys.isunix() ? ccall(:jl_getpagesize, Clong, ()) : ccall(:jl_getallocationgranularity, Clong, ()))
    __init_build()
    nothing
end
```
-/
def initSys {World Str : Type} (ops : InitOps World Str) : M World Unit := do
  let envThreads ← ops.envCpuThreads
  let threads ← match envThreads with
    | some str => do
      let parsed := ops.tryparseInt str
      match parsed with
      | some threads =>
        if threads.val > 0 then pure threads
        else do
          let fallback := i (← ops.jlCpuThreads).val
          ops.warning fallback
          pure fallback
      | none =>
        let fallback := i (← ops.jlCpuThreads).val
        ops.warning fallback
        pure fallback
    | none => do pure (i (← ops.jlCpuThreads).val)
  ops.setCpuThreads threads
  ops.setEffectiveThreads (min threads (i (← ops.jlEffectiveThreads).val))
  ops.setClockTicks (← ops.jlClockTicks)
  ops.setCpuName (← ops.jlCpuName)
  ops.setJit (← ops.jlJit)
  let pagesize ← if ops.isunix then ops.jlPagesize else ops.jlAllocationGranularity
  ops.setPagesize pagesize
  initBuild ops
  pure ()

/--
Julia source: base/sysinfo.jl:187-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct UV_cpu_info_t
    model::Ptr{UInt8}
    speed::Int32
    cpu_times!user::UInt64
    cpu_times!nice::UInt64
    cpu_times!sys::UInt64
    cpu_times!idle::UInt64
    cpu_times!irq::UInt64
end
```
-/
structure UVCPUInfo (Pointer : Type) where
  model : Pointer
  speed : Cint
  user : U
  nice : U
  sys : U
  idle : U
  irq : U

/--
Julia source: base/sysinfo.jl:213-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct CPUinfo
    model::String
    speed::Int32
    cpu_times!user::UInt64
    cpu_times!nice::UInt64
    cpu_times!sys::UInt64
    cpu_times!idle::UInt64
    cpu_times!irq::UInt64
    CPUinfo(model,speed,u,n,s,id,ir)=new(model,speed,u,n,s,id,ir)
end
```
-/
structure CPUInfo (Str : Type) where
  model : Str
  speed : Cint
  user : U
  nice : U
  sys : U
  idle : U
  irq : U

/--
Julia source: base/sysinfo.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    CPUinfo(model,speed,u,n,s,id,ir)=new(model,speed,u,n,s,id,ir)
```
-/
def newCPUInfo {World Str Model Speed TUser TNice TSys TIdle TIrq : Type}
    (convertModel : Model → M World Str) (convertSpeed : Speed → M World Cint)
    (convertUser : TUser → M World U) (convertNice : TNice → M World U)
    (convertSys : TSys → M World U) (convertIdle : TIdle → M World U)
    (convertIrq : TIrq → M World U) (model : Model) (speed : Speed)
    (u : TUser) (n : TNice) (s : TSys) (idle : TIdle) (irq : TIrq) : M World (CPUInfo Str) := do
  pure ⟨← convertModel model, ← convertSpeed speed, ← convertUser u,
    ← convertNice n, ← convertSys s, ← convertIdle idle, ← convertIrq irq⟩

/--
Julia source: base/sysinfo.jl:223-225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
CPUinfo(info::UV_cpu_info_t) = CPUinfo(unsafe_string(info.model), info.speed,
    info.cpu_times!user, info.cpu_times!nice, info.cpu_times!sys,
    info.cpu_times!idle, info.cpu_times!irq)
```
-/
def cpuInfoFromUV {World Pointer Str : Type} (unsafeString : Pointer → M World Str)
    (info : UVCPUInfo Pointer) : M World (CPUInfo Str) := do
  pure ⟨← unsafeString info.model, info.speed, info.user, info.nice, info.sys, info.idle, info.irq⟩

/--
Julia source: base/sysinfo.jl:239-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    d(i, unit=unit) = lpad(string(round(Int64,i)), 9) * unit
```
-/
def formatSeconds {World Stream Str Float : Type} (ops : CPUFormat World Stream Str Float)
    (value : Float) (unit : Str) : M World Str := do
  let rounded ← ops.roundInt64 value
  ops.concat (← ops.lpad (← ops.intString rounded) (i 9)) unit

/--
Julia source: base/sysinfo.jl:229-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_cpuinfo(io::IO, info::Sys.CPUinfo, header::Bool=true, prefix::AbstractString="    ")
    if header
        println(io, info.model, ": ")
        print(io, " "^length(prefix))
        println(io, "    ", lpad("speed", 5), "    ", lpad("user", 9), "    ", lpad("nice", 9), "    ",
                lpad("sys", 9), "    ", lpad("idle", 9), "    ", lpad("irq", 9))
    end
    print(io, prefix)
    ms_per_s = 1000
    unit = " s  "
    d(i, unit=unit) = lpad(string(round(Int64,i)), 9) * unit
    print(io,
          lpad(string(info.speed), 5), " MHz  ",
          d(info.cpu_times!user / ms_per_s), d(info.cpu_times!nice / ms_per_s), d(info.cpu_times!sys / ms_per_s),
          d(info.cpu_times!idle / ms_per_s), d(info.cpu_times!irq / ms_per_s))
end
```
-/
def showCPUInfo {World Stream Str Float : Type} (ops : CPUFormat World Stream Str Float)
    (io : Stream) (info : CPUInfo Str) (header : Bool := true)
    (prefixText : Str := ops.literal "    ") : M World Unit := do
  if header then
    ops.println io [info.model, ops.literal ": "]
    ops.print io [← ops.repeatString (ops.literal " ") (ops.length prefixText)]
    let speed ← ops.lpad (ops.literal "speed") (i 5)
    let user ← ops.lpad (ops.literal "user") (i 9)
    let nice ← ops.lpad (ops.literal "nice") (i 9)
    let sys ← ops.lpad (ops.literal "sys") (i 9)
    let idle ← ops.lpad (ops.literal "idle") (i 9)
    let irq ← ops.lpad (ops.literal "irq") (i 9)
    ops.println io [ops.literal "    ", speed, ops.literal "    ", user, ops.literal "    ", nice,
      ops.literal "    ", sys, ops.literal "    ", idle, ops.literal "    ", irq]
  ops.print io [prefixText]
  let msPerS := i 1000
  let unit := ops.literal " s  "
  let speed ← ops.lpad (← ops.intString (i info.speed.val)) (i 5)
  let user ← formatSeconds ops (← ops.divide info.user msPerS) unit
  let nice ← formatSeconds ops (← ops.divide info.nice msPerS) unit
  let sys ← formatSeconds ops (← ops.divide info.sys msPerS) unit
  let idle ← formatSeconds ops (← ops.divide info.idle msPerS) unit
  let irq ← formatSeconds ops (← ops.divide info.irq msPerS) unit
  ops.print io [speed, ops.literal " MHz  ", user, nice, sys, idle, irq]

/--
Julia source: base/sysinfo.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/plain", info::CPUinfo) = _show_cpuinfo(io, info, true, "    ")
```
-/
def showTextPlain {World Stream Str Float : Type} (ops : CPUFormat World Stream Str Float)
    (io : Stream) (info : CPUInfo Str) : M World Unit := showCPUInfo ops io info true (ops.literal "    ")

/--
Julia source: base/sysinfo.jl:248-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cpu_summary(io::IO, cpu::AbstractVector{CPUinfo}, i, j)
    if j-i < 9
        header = true
        for x = i:j
            header || println(io)
            _show_cpuinfo(io, cpu[x], header, "#$(x-i+1) ")
            header = false
        end
    else
        summary = CPUinfo(cpu[i].model,0,0,0,0,0,0)
        count = j - i + 1
        for x = i:j
            summary.speed += cpu[x].speed
            summary.cpu_times!user += cpu[x].cpu_times!user
            summary.cpu_times!nice += cpu[x].cpu_times!nice
            summary.cpu_times!sys += cpu[x].cpu_times!sys
            summary.cpu_times!idle += cpu[x].cpu_times!idle
            summary.cpu_times!irq += cpu[x].cpu_times!irq
        end
        summary.speed = div(summary.speed,count)
        _show_cpuinfo(io, summary, true, "#1-$(count) ")
    end
    println(io)
end
```
-/
def cpuSummaryRange {World Stream Str Float Vector : Type} (ops : CPUFormat World Stream Str Float)
    (get : Vector → I → M World (CPUInfo Str)) (io : Stream) (cpu : Vector) (first last : I) : M World Unit := do
  if (last - first).val < 9 then
    let mut header := true
    for offset in List.range (max 0 (last - first + i 1).val).toNat do
      let x := first + i offset
      if !header then ops.println io []
      let info ← get cpu x
      let prefixText ← ops.concat (← ops.concat (ops.literal "#")
        (← ops.intString (x - first + i 1))) (ops.literal " ")
      showCPUInfo ops io info header prefixText
      header := false
  else
    let firstCPU ← get cpu first
    let mut summary : CPUInfo Str := ⟨firstCPU.model, JInt.wrap .i32 0,
      JInt.wrap .u64 0, JInt.wrap .u64 0, JInt.wrap .u64 0, JInt.wrap .u64 0, JInt.wrap .u64 0⟩
    let count := last - first + i 1
    for offset in List.range count.val.toNat do
      let x := first + i offset
      summary := { summary with speed := summary.speed + (← get cpu x).speed }
      summary := { summary with user := summary.user + (← get cpu x).user }
      summary := { summary with nice := summary.nice + (← get cpu x).nice }
      summary := { summary with sys := summary.sys + (← get cpu x).sys }
      summary := { summary with idle := summary.idle + (← get cpu x).idle }
      summary := { summary with irq := summary.irq + (← get cpu x).irq }
    let average ← JuliaLean.base.io.liftJl (JInt.div (i summary.speed.val) count)
    let speed ← JuliaLean.base.io.liftJl (JInt.convert "convert" .i32 average.val)
    summary := { summary with speed := speed }
    let prefixText ← ops.concat (← ops.concat (ops.literal "#1-") (← ops.intString count)) (ops.literal " ")
    showCPUInfo ops io summary true prefixText
  ops.println io []

/--
Julia source: base/sysinfo.jl:284-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cpu_summary(io::IO=stdout, cpu::AbstractVector{CPUinfo} = cpu_info())
    model = cpu[1].model
    first = 1
    for i = 2:length(cpu)
        if model != cpu[i].model
            _cpu_summary(io, cpu, first, i-1)
            first = i
            model = cpu[i].model
        end
    end
    _cpu_summary(io, cpu, first, length(cpu))
end
```
-/
def cpuSummary {World Stream Str Float Vector : Type} [BEq Str]
    (ops : CPUFormat World Stream Str Float) (length : Vector → M World I)
    (get : Vector → I → M World (CPUInfo Str)) (io : Stream) (cpu : Vector) : M World Unit := do
  let mut model := (← get cpu (i 1)).model
  let mut first := i 1
  let count ← length cpu
  for offset in List.range (max 0 (count - i 1).val).toNat do
    let index := i offset + i 2
    if model != (← get cpu index).model then
      cpuSummaryRange ops get io cpu first (index - i 1)
      first := index
      model := (← get cpu index).model
  cpuSummaryRange ops get io cpu first (← length cpu)

/--
Julia source: base/sysinfo.jl:309-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cpu_info()
    UVcpus = Ref{Ptr{UV_cpu_info_t}}()
    count = Ref{Int32}()
    err = ccall(:uv_cpu_info, Int32, (Ptr{Ptr{UV_cpu_info_t}}, Ptr{Int32}), UVcpus, count)
    Base.uv_error("uv_cpu_info", err)
    cpus = Vector{CPUinfo}(undef, count[])
    for i = 1:length(cpus)
        cpus[i] = CPUinfo(unsafe_load(UVcpus[], i))
        if isempty(cpus[i].model) || cpus[i].model == "unknown"
            # libuv may lack model detection where Julia's CPU detection succeeds.
            cpus[i].model = CPU_NAME
        end
    end
    ccall(:uv_free_cpu_info, Cvoid, (Ptr{UV_cpu_info_t}, Int32), UVcpus[], count[])
    return cpus
end
```
-/
def cpuInfo {World Pointer Str Ref CountRef Vector : Type} [BEq Str]
    (newPointerRef : M World Ref) (newCountRef : M World CountRef)
    (uvCPUInfo : Ref → CountRef → M World Cint) (uvError : String → Cint → M World Unit)
    (readCount : CountRef → M World Cint) (allocate : Cint → M World Vector)
    (length : Vector → M World I) (load : Ref → I → M World (UVCPUInfo Pointer))
    (unsafeString : Pointer → M World Str) (get : Vector → I → M World (CPUInfo Str))
    (set : Vector → I → CPUInfo Str → M World Unit)
    (isEmpty : Str → Bool) (unknown : Str) (cpuName : M World Str)
    (free : Ref → Cint → M World Unit) : M World Vector := do
  let uvcpus ← newPointerRef
  let count ← newCountRef
  uvError "uv_cpu_info" (← uvCPUInfo uvcpus count)
  let cpus ← allocate (← readCount count)
  for offset in List.range (← length cpus).val.toNat do
    let index := i offset + i 1
    set cpus index (← cpuInfoFromUV unsafeString (← load uvcpus index))
    if isEmpty (← get cpus index).model || (← get cpus index).model == unknown then
      set cpus index { (← get cpus index) with model := ← cpuName }
  free uvcpus (← readCount count)
  pure cpus

/--
Julia source: base/sysinfo.jl:342-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sysimage_target()
    return ccall(:jl_get_sysimage_cpu_target, Ref{String}, ())
end
```
-/
def sysimageTarget {World Str : Type} (jlGetSysimageCPUTarget : M World Str) : M World Str :=
  jlGetSysimageCPUTarget

/--
Julia source: base/sysinfo.jl:359-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function matched_sysimage_target()
    match_idx = let
        idx = ccall(:jl_get_sysimage_matched_target_index, Int32, ())
        idx == -1 ? 1 : idx + 1
    end
    return String(split(sysimage_target(), ";")[match_idx])
end
```
-/
def matchedSysimageTarget {World Str : Type} (matchedIndex : M World Cint)
    (sysimageTarget : M World Str) (split : Str → List Str) : M World Str := do
  let index ← matchedIndex
  let matchIndex := if index.val == -1 then JInt.wrap .i32 1 else index + JInt.wrap .i32 1
  let targets := split (← sysimageTarget)
  match targets[(matchIndex.val - 1).toNat]? with
  | some target => if matchIndex.val > 0 then pure target else throw (.jl .boundsError)
  | none => throw (.jl .boundsError)

/--
Julia source: base/sysinfo.jl:372-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uptime()
    uptime_ = Ref{Float64}()
    err = ccall(:uv_uptime, Int32, (Ptr{Float64},), uptime_)
    Base.uv_error("uv_uptime", err)
    return uptime_[]
end
```
-/
def uptime {World Float Ref : Type} (newRef : M World Ref)
    (uvUptime : Ref → M World Cint) (uvError : String → Cint → M World Unit)
    (get : Ref → M World Float) : M World Float := do
  let uptimeRef ← newRef
  uvError "uv_uptime" (← uvUptime uptimeRef)
  get uptimeRef

/--
Julia source: base/sysinfo.jl:384-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function loadavg()
    loadavg_ = Vector{Float64}(undef, 3)
    ccall(:uv_loadavg, Cvoid, (Ptr{Float64},), loadavg_)
    return loadavg_
end
```
-/
def loadavg {World Vector : Type} (allocate : I → M World Vector)
    (uvLoadavg : Vector → M World Unit) : M World Vector := do
  let values ← allocate (i 3)
  uvLoadavg values
  pure values

/--
Julia source: base/sysinfo.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
free_physical_memory() = ccall(:uv_get_free_memory, UInt64, ())
```
-/
def freePhysicalMemory {World : Type} (uvGetFreeMemory : M World U) : M World U := uvGetFreeMemory

/--
Julia source: base/sysinfo.jl:404-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
total_physical_memory() = ccall(:uv_get_total_memory, UInt64, ())
```
-/
def totalPhysicalMemory {World : Type} (uvGetTotalMemory : M World U) : M World U := uvGetTotalMemory

/--
Julia source: base/sysinfo.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
free_memory() = ccall(:uv_get_available_memory, UInt64, ())
```
-/
def freeMemory {World : Type} (uvGetAvailableMemory : M World U) : M World U := uvGetAvailableMemory

/--
Julia source: base/sysinfo.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maxrss() = ccall(:jl_maxrss, Csize_t, ())
```
-/
def maxrss {World : Type} (jlMaxrss : M World U) : M World U := jlMaxrss

/--
Julia source: base/sysinfo.jl:420-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function total_memory()
    constrained = ccall(:uv_get_constrained_memory, UInt64, ())
    physical = total_physical_memory()
    if 0 < constrained <= physical
        return constrained
    else
        return physical
    end
end
```
-/
def totalMemory {World : Type} (uvGetConstrainedMemory totalPhysicalMemory : M World U) : M World U := do
  let constrained ← uvGetConstrainedMemory
  let physical ← totalPhysicalMemory
  if 0 < constrained.val && constrained ≤ physical then pure constrained else pure physical

/--
Julia source: base/sysinfo.jl:435-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_process_title()
    buf = Vector{UInt8}(undef, 512)
    err = ccall(:uv_get_process_title, Cint, (Ptr{UInt8}, Cint), buf, 512)
    Base.uv_error("get_process_title", err)
    return unsafe_string(pointer(buf))
end
```
-/
def getProcessTitle {World Buffer Str : Type} (allocate : I → M World Buffer)
    (uvGetProcessTitle : Buffer → Cint → M World Cint) (uvError : String → Cint → M World Unit)
    (unsafeString : Buffer → M World Str) : M World Str := do
  let buf ← allocate (i 512)
  uvError "get_process_title" (← uvGetProcessTitle buf (JInt.wrap .i32 512))
  unsafeString buf

/--
Julia source: base/sysinfo.jl:447-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function set_process_title(title::AbstractString)
    err = ccall(:uv_set_process_title, Cint, (Cstring,), title)
    Base.uv_error("set_process_title", err)
end
```
-/
def setProcessTitle {World Title : Type} (uvSetProcessTitle : Title → M World Cint)
    (uvError : String → Cint → M World Unit) (title : Title) : M World Unit := do
  uvError "set_process_title" (← uvSetProcessTitle title)

/--
Julia source: base/sysinfo.jl:463-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function windows_version()
        verinfo = ccall(:GetVersion, UInt32, ())
        VersionNumber(verinfo & 0xFF, (verinfo >> 8) & 0xFF, verinfo >> 16)
    end
```
-/
def windowsVersion {World Version : Type} (getVersion : M World (JInt .u32))
    (versionNumber : JInt .u32 → JInt .u32 → JInt .u32 → M World Version) : M World Version := do
  let verinfo ← getVersion
  let bits := BitVec.ofInt 32 verinfo.val
  let major := JInt.wrap .u32 (bits.toNat % 256)
  let minor := JInt.wrap .u32 ((bits.toNat / 256) % 256)
  let build := JInt.wrap .u32 (bits.toNat / 65536)
  versionNumber major minor build

/--
Julia source: base/sysinfo.jl:468-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    windows_version() = v"0.0"
```
-/
def windowsVersionOther {Version : Type} (zeroVersion : Version) : Version := zeroVersion

/--
Julia source: base/sysinfo.jl:495-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function which(program_name::String)
    if isempty(program_name)
       return nothing
    end
    # Build a list of program names that we're going to try
    program_names = String[]
    base_pname = basename(program_name)
    if iswindows()
        # If the file already has an extension, try that name first
        if !isempty(splitext(base_pname)[2])
            push!(program_names, base_pname)
        end

        # But also try appending .exe and .com
        for pe in (".exe", ".com")
            push!(program_names, string(base_pname, pe))
        end
    else
        # On non-windows, we just always search for what we've been given
        push!(program_names, base_pname)
    end

    path_dirs = String[]
    program_dirname = dirname(program_name)
    # If we've been given a path that has a directory name in it, then we
    # check to see if that path exists.  Otherwise, we search the PATH.
    if isempty(program_dirname)
        # If we have been given just a program name (not a relative or absolute
        # path) then we should search `PATH` for it here:
        pathsep = iswindows() ? ';' : ':'
        path_dirs = map(abspath, eachsplit(get(ENV, "PATH", ""), pathsep))

        # On windows we always check the current directory as well
        if iswindows()
            pushfirst!(path_dirs, pwd())
        end
    else
        push!(path_dirs, abspath(program_dirname))
    end

    # Here we combine our directories with our program names, searching for the
    # first match among all combinations.
    for path_dir in path_dirs
        for pname in program_names
            program_path = joinpath(path_dir, pname)
            try
                # If we find something that matches our name and we can execute
                if isfile(program_path) && isexecutable(program_path)
                    return program_path
                end
            catch e
                # If we encounter a permission error, we skip this directory
                # and continue to the next directory in the PATH variable.
                if isa(e, Base.IOError) && e.code == Base.UV_EACCES
                    # Permission denied, continue searching
                    continue
                else
                    # Rethrow the exception if it's not a permission error
                    rethrow(e)
                end
            end
        end
    end

    # If we couldn't find anything, don't return anything
    nothing
end
```
-/
def which {World Path : Type} (ops : WhichOps World Path) (programName : Path) : M World (Option Path) := do
  if ops.isEmpty programName then return none
  let mut programNames := []
  let baseName ← ops.basename programName
  if ops.iswindows then
    if !ops.isEmpty (← ops.extension baseName) then programNames := programNames ++ [baseName]
    for extension in [".exe", ".com"] do
      programNames := programNames ++ [← ops.concat baseName (ops.literal extension)]
  else programNames := programNames ++ [baseName]
  let mut pathDirs := []
  let programDir ← ops.dirname programName
  if ops.isEmpty programDir then
    pathDirs := ← (ops.splitPath (← ops.envPath) ops.iswindows).mapM ops.abspath
    if ops.iswindows then pathDirs := (← ops.pwd) :: pathDirs
  else pathDirs := pathDirs ++ [← ops.abspath programDir]
  for pathDir in pathDirs do
    for pname in programNames do
      let programPath ← ops.joinpath pathDir pname
      let found ← try
          if ← ops.isfile programPath then ops.isexecutable programPath else pure false
        catch error =>
          if ops.isPermissionDeniedIOError error then pure false else throw error
      if found then return some programPath
  pure none

/--
Julia source: base/sysinfo.jl:562-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
which(program_name::AbstractString) = which(String(program_name)::String)
```
-/
def whichAbstract {World Path AbstractString : Type} (toString : AbstractString → M World Path)
    (which : Path → M World (Option Path)) (programName : AbstractString) : M World (Option Path) := do
  which (← toString programName)

/--
Julia source: base/sysinfo.jl:581-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function username()
    pw = Libc.getpw()
    isempty(pw.username) && Base.uv_error("username", Base.UV_ENOENT)
    return pw.username
end
```
-/
def username {World Passwd Str : Type} (getpw : M World Passwd) (getUsername : Passwd → Str)
    (isEmpty : Str → Bool) (uvErrorENOENT : String → M World Unit) : M World Str := do
  let pw ← getpw
  if isEmpty (getUsername pw) then uvErrorENOENT "username"
  pure (getUsername pw)


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/sysinfo.jl:1-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # NB: This file is `Core.eval`-uated into the (pre-existing) module Sys
-- 
-- @doc """
-- Provide methods for retrieving information about hardware and the operating system.
-- """ Sys
-- 
-- export BINDIR,
--        STDLIB,
--        CPU_THREADS,
--        EFFECTIVE_CPU_THREADS,
--        CPU_NAME,
--        WORD_SIZE,
--        ARCH,
--        MACHINE,
--        JIT,
--        PAGESIZE,
--        cpu_info,
--        cpu_summary,
--        sysimage_target,
--        matched_sysimage_target,
--        uptime,
--        loadavg,
--        free_memory,
--        total_memory,
--        free_physical_memory,
--        total_physical_memory,
--        isexecutable,
--        isreadable,
--        iswritable,
--        username,
--        which
-- 
-- import ..Base: DATAROOTDIR, show
-- 
-- """
--     Sys.BINDIR::String
-- 
-- A string containing the full path to the directory containing the `julia` executable.
-- """
-- global BINDIR::String = ccall(:jl_get_julia_bindir, Any, ())::String
-- 
-- """
--     Sys.STDLIB::String
-- 
-- A string containing the full path to the directory containing the `stdlib` packages.
-- """
-- global STDLIB::String = "$BINDIR/$DATAROOTDIR/julia/stdlib/v$(VERSION.major).$(VERSION.minor)" # for bootstrap
-- # In case STDLIB change after julia is built, the variable below can be used
-- # to update cached method locations to updated ones.
-- const BUILD_STDLIB_PATH = STDLIB
-- 
-- # helper to avoid triggering precompile warnings
-- 
-- """
--     Sys.CPU_THREADS::Int
-- 
-- The number of logical CPU cores available in the system, i.e. the number of threads
-- that the CPU can run concurrently. Note that this is not necessarily the number of
-- CPU cores, for example, in the presence of
-- [hyper-threading](https://en.wikipedia.org/wiki/Hyper-threading).
-- 
-- See Hwloc.jl or CpuId.jl for extended information, including number of physical cores.
-- 
-- See also: [`Sys.EFFECTIVE_CPU_THREADS`](@ref) for a container-aware CPU count that respects
-- cgroup limits.
-- """
-- global CPU_THREADS::Int = 1 # for bootstrap, changed on startup
-- 
-- """
--     Sys.EFFECTIVE_CPU_THREADS::Int
-- 
-- The effective number of logical CPU cores available to the Julia process, taking into
-- account container limits (e.g., Docker `--cpus`, Kubernetes CPU limits, cgroup quotas).
-- This is the minimum of the hardware CPU thread count and any imposed CPU limits.
-- 
-- In non-containerized environments, this typically equals `Sys.CPU_THREADS`. In containerized
-- environments, it respects cgroup CPU limits and provides a more accurate measure of
-- available parallelism.
-- 
-- Use this constant when determining default thread pool sizes or parallelism levels to
-- ensure proper behavior in containerized deployments.
-- """
-- global EFFECTIVE_CPU_THREADS::Int = 1 # for bootstrap, changed on startup
-- 
-- """
--     Sys.ARCH::Symbol
-- 
-- A symbol representing the architecture of the build configuration.
-- """
-- const ARCH = ccall(:jl_get_ARCH, Any, ())::Symbol
-- 
-- 
-- """
--     Sys.MACHINE::String
-- 
-- A string containing the build triple.
-- """
-- const MACHINE = Base.MACHINE::String
-- 
-- """
--     Sys.WORD_SIZE::Int
-- 
-- Standard word size on the current machine, in bits.
-- """
-- const WORD_SIZE = Core.sizeof(Int) * 8
-- 
-- """
--     Sys.SC_CLK_TCK::Clong
-- 
-- The number of system "clock ticks" per second, corresponding to `sysconf(_SC_CLK_TCK)` on
-- POSIX systems, or `0` if it is unknown.
-- """
-- global SC_CLK_TCK::Clong
-- 
-- """
--     Sys.CPU_NAME::String
-- 
-- A string representing the name of the host CPU.
-- 
-- # Examples
-- For example, `Sys.CPU_NAME` might equal `"tigerlake"` on an
-- [Intel Core "Tiger Lake" CPU](https://en.wikipedia.org/wiki/Tiger_Lake),
-- or `"apple-m1"` on an [Apple M1 CPU](https://en.wikipedia.org/wiki/Apple_M1).
-- 
-- Note: Included in the output of `versioninfo()`.
-- """
-- global CPU_NAME::String
-- 
-- """
--     Sys.JIT::String
-- 
-- A string representing the specific Just-In-Time (JIT) compiler being utilized in the current runtime.
-- 
-- # Examples
-- Currently, this equals `"ORCJIT"` for the LLVM "ORC" ("On-Request Compilation") JIT library:
-- ```jldoctest
-- julia> Sys.JIT
-- "ORCJIT"
-- ```
-- 
-- Note: Included in the output of `versioninfo()`.
-- """
-- global JIT::String
-- 
-- """
--     Sys.PAGESIZE::Clong
-- 
-- A number providing the pagesize of the given OS.  Common values being 4kb or 64kb on Linux.
-- On Windows, this stores the allocation granularity, not the page size.
-- """
-- global PAGESIZE::Clong
-- 
-- /Source

-- Source: base/sysinfo.jl:178-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Populate the paths needed by sysimg compilation, e.g. `generate_precompile.jl`,
-- # without pulling in anything unnecessary like `CPU_NAME`
-- /Source

-- Source: base/sysinfo.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/sysinfo.jl:196-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.CPUinfo
-- 
-- The `CPUinfo` type is a mutable struct with the following fields:
-- - `model::String`: CPU model information.
-- - `speed::Int32`: CPU speed (in MHz).
-- - `cpu_times!user::UInt64`: Time spent in user mode. CPU state shows CPU time used by user space processes.
-- - `cpu_times!nice::UInt64`: Time spent in nice mode. CPU state is a subset of the "user" state and shows the CPU time used by processes that have a positive niceness, meaning a lower priority than other tasks.
-- - `cpu_times!sys::UInt64`: Time spent in system mode. CPU state shows the amount of CPU time used by the kernel.
-- - `cpu_times!idle::UInt64`: Time spent in idle mode. CPU state shows the CPU time that's not actively being used.
-- - `cpu_times!irq::UInt64`: Time spent handling interrupts. CPU state shows the amount of time the CPU has been servicing hardware interrupts.
-- 
-- The times are in units of milliseconds.
-- 
-- Note: Included in the detailed system information via `versioninfo(verbose=true)`.
-- """
-- /Source

-- Source: base/sysinfo.jl:226-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- public CPUinfo
-- 
-- /Source

-- Source: base/sysinfo.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/sysinfo.jl:247-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/sysinfo.jl:272-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.cpu_summary(io::IO=stdout, cpu::AbstractVector{CPUinfo}=cpu_info())
-- 
-- Print a summary of CPU information to the `io` stream (defaulting to [`stdout`](@ref)), organizing and displaying aggregated data for CPUs with the same model, for a given array of `CPUinfo` data structures
-- describing a set of CPUs (which defaults to the return value of the [`Sys.cpu_info`](@ref) function).
-- 
-- The summary includes aggregated information for each distinct CPU model,
-- providing details such as average CPU speed and total time spent in different modes (user, nice, sys, idle, irq) across all cores with the same model.
-- 
-- Note: Included in the detailed system information via `versioninfo(verbose=true)`.
-- """
-- /Source

-- Source: base/sysinfo.jl:296-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.cpu_info()
-- 
-- Return a vector of `CPUinfo` objects, where each object represents information about a CPU core.
-- 
-- This is pretty-printed in a tabular format by `Sys.cpu_summary`, which is included in the output
-- of `versioninfo(verbose=true)`, so most users will not need to access the `CPUinfo`
-- data structures directly.
-- 
-- The function provides information about each CPU, including model, speed, and usage statistics such as user time, nice time, system time, idle time, and interrupt time.
-- 
-- """
-- /Source

-- Source: base/sysinfo.jl:325-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.sysimage_target()
-- 
-- Return the CPU target string that was used to build the current system image.
-- 
-- This function returns the original CPU target specification that was passed to Julia
-- when the system image was compiled. This can be useful for reproducing the same
-- system image or for understanding what CPU features were enabled during compilation.
-- 
-- If the system image was built with the default settings this will return `"native"`.
-- 
-- !!! compat "Julia 1.13"
--     This function requires at least Julia 1.13.
-- 
-- See also [`Sys.matched_sysimage_target`](@ref), [`JULIA_CPU_TARGET`](@ref).
-- """
-- /Source

-- Source: base/sysinfo.jl:345-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.matched_sysimage_target()
-- 
-- Return the entry of [`Sys.sysimage_target`](@ref) that was selected for the host CPU
-- when the system image was loaded.
-- 
-- If the system image was built with the default settings this will return `"native"`.
-- 
-- !!! compat "Julia 1.14"
--     This function requires at least Julia 1.14.
-- 
-- See also [`Sys.sysimage_target`](@ref), [`JULIA_CPU_TARGET`](@ref).
-- """
-- /Source

-- Source: base/sysinfo.jl:366-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.uptime()
-- 
-- Get the current system uptime in seconds.
-- """
-- /Source

-- Source: base/sysinfo.jl:378-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.loadavg()
-- 
-- Get the load average. See: https://en.wikipedia.org/wiki/Load_(computing).
-- """
-- /Source

-- Source: base/sysinfo.jl:389-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.free_physical_memory()
-- 
-- Get the free memory of the system in bytes. The entire amount may not be available to the
-- current process; use `Sys.free_memory()` for the actually available amount.
-- """
-- /Source

-- Source: base/sysinfo.jl:397-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.total_physical_memory()
-- 
-- Get the total memory in RAM (including that which is currently used) in bytes. The entire
-- amount may not be available to the current process; see `Sys.total_memory()`.
-- """
-- /Source

-- Source: base/sysinfo.jl:405-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.free_memory()
-- 
-- Get the total free memory in RAM in bytes.
-- """
-- /Source

-- Source: base/sysinfo.jl:412-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.total_memory()
-- 
-- Get the total memory in RAM (including that which is currently used) in bytes.
-- This amount may be constrained, e.g., by Linux control groups. For the unconstrained
-- amount, see `Sys.total_physical_memory()`.
-- """
-- /Source

-- Source: base/sysinfo.jl:429-434 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.get_process_title()
-- 
-- Get the process title. On some systems, will always return an empty string.
-- """
-- /Source

-- Source: base/sysinfo.jl:441-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.set_process_title(title::AbstractString)
-- 
-- Set the process title. No-op on some operating systems.
-- """
-- /Source

-- Source: base/sysinfo.jl:451-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.maxrss()
-- 
-- Get the maximum resident set size utilized in bytes.
-- See also:
--     - man page of `getrusage`(2) on Linux and BSD.
--     - Windows API `GetProcessMemoryInfo`.
-- """
-- /Source

-- Source: base/sysinfo.jl:461-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if iswindows()
-- /Source

-- Source: base/sysinfo.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- else
-- /Source

-- Source: base/sysinfo.jl:469-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- """
--     Sys.windows_version()
-- 
-- Return the version number for the Windows NT Kernel as a `VersionNumber`,
-- i.e. `v"major.minor.build"`, or `v"0.0.0"` if this is not running on Windows.
-- """
-- windows_version
-- 
-- const WINDOWS_VISTA_VER = v"6.0"
-- 
-- const isexecutable = Base.isexecutable
-- const isreadable   = Base.isreadable
-- const iswritable   = Base.iswritable
-- 
-- """
--     Sys.which(program_name::String)
-- 
-- Given a program name, search the current `PATH` to find the first binary with
-- the proper executable permissions that can be run and return an absolute path
-- to it, or return `nothing` if no such program is available. If a path with
-- a directory in it is passed in for `program_name`, tests that exact path
-- for executable permissions only (with `.exe` and `.com` extensions added on
-- Windows platforms); no searching of `PATH` is performed.
-- """
-- /Source

-- Source: base/sysinfo.jl:563-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Sys.username()::String
-- 
-- Return the username for the current user. If the username cannot be determined
-- or is empty, this function throws an error.
-- 
-- To retrieve a username that is overridable via an environment variable,
-- e.g., `USER`, consider using
-- ```julia
-- user = get(Sys.username, ENV, "USER")
-- ```
-- 
-- !!! compat "Julia 1.11"
--     This function requires at least Julia 1.11.
-- 
-- See also [`homedir`](@ref).
-- """
-- /Source


end JuliaLean.base.sysinfo

section
namespace JuliaLean.RuntimeCov.SysInfo

open JuliaLean.RuntimeCov

/-- The globals set by `Sys.__init__`. -/
structure SysGlobals where
  cpuThreads : Int
  effectiveCpuThreads : Int
  warned : Bool
  pagesize : Int
  deriving DecidableEq, Repr

/-- `Sys.__init__()`, base/sysinfo.jl:155-177: `env` is `ENV["JULIA_CPU_THREADS"]`
if set, `tryparse` is `tryparse(Int, _)`, `jlCpuThreads`/`jlEffective` the
runtime counts, `unixPage`/`winGranularity` the two page-size queries. -/
def cpuThreadsOf (env : Option String) (tryparse : String → Option Int) (jlCpuThreads : Int) :
    Int × Bool :=
  match env with
  | some s =>
    match tryparse s with
    | some n => if n ≤ 0 then (jlCpuThreads, true) else (n, false)
    | none => (jlCpuThreads, true)
  | none => (jlCpuThreads, false)

def init (env : Option String) (tryparse : String → Option Int)
    (jlCpuThreads jlEffective : Int) (isunix : Bool) (unixPage winGranularity : Int) : SysGlobals :=
  let r := cpuThreadsOf env tryparse jlCpuThreads
  { cpuThreads := r.1, effectiveCpuThreads := min r.1 jlEffective, warned := r.2,
    pagesize := if isunix then unixPage else winGranularity }

/-- `Sys.__init_build()`, base/sysinfo.jl:180-185: the path components passed to
`abspath(BINDIR, DATAROOTDIR, "julia", "stdlib", vers)`. -/
def initBuild (bindir datarootdir : String) (major minor : Nat) : List String :=
  [bindir, datarootdir, "julia", "stdlib", "v" ++ toString major ++ "." ++ toString minor]

/-- `Sys.CPUinfo`, base/sysinfo.jl:211-222 (inner constructor at line 221). -/
structure CPUinfo where
  model : String
  speed : JInt .i32
  user : JInt .u64
  nice : JInt .u64
  sys : JInt .u64
  idle : JInt .u64
  irq : JInt .u64

/-- `CPUinfo(model,speed,u,n,s,id,ir)`, base/sysinfo.jl:221. -/
def mkCPUinfo (model : String) (speed : JInt .i32) (u n s id ir : JInt .u64) : CPUinfo :=
  ⟨model, speed, u, n, s, id, ir⟩

/-- `UV_cpu_info_t` with its model C string already read. -/
structure UVCpuInfo where
  model : String
  speed : JInt .i32
  user : JInt .u64
  nice : JInt .u64
  sys : JInt .u64
  idle : JInt .u64
  irq : JInt .u64

/-- `CPUinfo(info::UV_cpu_info_t)`, base/sysinfo.jl:223-225. -/
def ofUV (i : UVCpuInfo) : CPUinfo := ⟨i.model, i.speed, i.user, i.nice, i.sys, i.idle, i.irq⟩

/-- `d(i, unit=unit)`, base/sysinfo.jl:239, given the rounded integer `round(Int64, i)`. -/
def dcol (rounded : Int) (unit : String := " s  ") : String := lpad (toString rounded) 9 ++ unit

/-- `_show_cpuinfo(io, info, header, prefix)`, base/sysinfo.jl:229-244. `round`
maps a millisecond count to `round(Int64, ms / 1000)`. -/
def showCpuinfo (round : JInt .u64 → Int) (info : CPUinfo) (header : Bool) (pfx : String) : String :=
  (if header then
      info.model ++ ": \n" ++ String.ofList (List.replicate pfx.length ' ') ++
      "    " ++ lpad "speed" 5 ++ "    " ++ lpad "user" 9 ++ "    " ++ lpad "nice" 9 ++ "    " ++
      lpad "sys" 9 ++ "    " ++ lpad "idle" 9 ++ "    " ++ lpad "irq" 9 ++ "\n"
    else "") ++
  pfx ++ lpad (toString info.speed.val) 5 ++ " MHz  " ++
    dcol (round info.user) ++ dcol (round info.nice) ++ dcol (round info.sys) ++
    dcol (round info.idle) ++ dcol (round info.irq)

/-- `show(io, ::MIME"text/plain", info::CPUinfo)`, base/sysinfo.jl:246. -/
def showPlain (round : JInt .u64 → Int) (info : CPUinfo) : String :=
  showCpuinfo round info true "    "

/-- The aggregate built by `_cpu_summary` for a run of ten or more CPUs,
base/sysinfo.jl:257-268 (`Int32` and `UInt64` additions wrap). -/
def summaryOf (run : List CPUinfo) (model : String) : CPUinfo :=
  let z64 : JInt .u64 := JInt.lit .u64 0
  let s := run.foldl (fun (acc c : CPUinfo) =>
      { acc with speed := acc.speed + c.speed, user := acc.user + c.user, nice := acc.nice + c.nice,
                 sys := acc.sys + c.sys, idle := acc.idle + c.idle, irq := acc.irq + c.irq })
    (⟨model, JInt.lit .i32 0, z64, z64, z64, z64, z64⟩ : CPUinfo)
  { s with speed := JInt.lit .i32 (s.speed.val / (run.length : Int)) }

/-- What `_cpu_summary(io, cpu, i, j)` prints, base/sysinfo.jl:248-271: one row
per CPU numbered from `#1` with a header only on the first, or one `#1-count`
summary row. Rows are given as `(info, header, prefix)`. -/
def cpuSummaryRows (cpu : List CPUinfo) (i j : Nat) : List (CPUinfo × Bool × String) :=
  let run := (cpu.drop (i - 1)).take (j - i + 1)
  if j - i < 9 then
    ((List.range run.length).zip run).map fun p => (p.2, p.1 == 0, "#" ++ toString (p.1 + 1) ++ " ")
  else
    [(summaryOf run (run.headD ⟨"", JInt.lit .i32 0, JInt.lit .u64 0, JInt.lit .u64 0,
        JInt.lit .u64 0, JInt.lit .u64 0, JInt.lit .u64 0⟩).model, true,
      "#1-" ++ toString run.length ++ " ")]

/-- Maximal runs of consecutive equal models, as 1-based inclusive `(first, last)`. -/
def modelRuns : List String → Nat → List (Nat × Nat)
  | [], _ => []
  | m :: ms, start =>
    let k := (ms.takeWhile (· == m)).length
    (start, start + k) :: modelRuns (ms.drop k) (start + k + 1)
termination_by l => l.length
decreasing_by simp; omega

/-- `cpu_summary(io, cpu)`, base/sysinfo.jl:284-295: the `(first, last)` ranges
handed to `_cpu_summary`; `cpu[1]` throws a `BoundsError` on an empty vector. -/
def cpuSummary (cpu : List CPUinfo) : Rt (List (Nat × Nat)) :=
  match cpu with
  | [] => .error .boundsError
  | c :: cs =>
    -- the loop at lines 287-293 compares each model with the current run's model
    .ok (modelRuns (c.model :: cs.map (·.model)) 1)

/-- `cpu_info()`, base/sysinfo.jl:309-324. -/
def cpuInfo (err : Int) (uv : List UVCpuInfo) (cpuName : String) : Rt (List CPUinfo) := do
  uvError err
  pure (uv.map fun u =>
    let c := ofUV u
    if c.model.isEmpty || c.model == "unknown" then { c with model := cpuName } else c)

/-- `sysimage_target()`, base/sysinfo.jl:342-344. -/
def sysimageTarget (runtime : String) : String := runtime

/-- `matched_sysimage_target()`, base/sysinfo.jl:359-365: `parts` is
`split(sysimage_target(), ";")` and the result is `parts[idx]`. -/
def matchedSysimageTarget (idx : Int) (parts : List String) : Rt String :=
  let m : Int := if idx = -1 then 1 else idx + 1
  if 1 ≤ m ∧ m.toNat ≤ parts.length then .ok (parts.getD (m.toNat - 1) "") else .error .boundsError

/-- `uptime()`, base/sysinfo.jl:372-377, and the other libuv value queries. -/
def uptime (err : Int) (value : Float) : Rt Float := do uvError err; pure value
/-- `loadavg()`, base/sysinfo.jl:384-388: the three-element vector filled by libuv. -/
def loadavg (a b c : Float) : List Float := [a, b, c]
/-- `free_physical_memory()`, `total_physical_memory()`, `free_memory()`,
`maxrss()`, base/sysinfo.jl:396, 404, 411, 460: the runtime's `UInt64`/`Csize_t`. -/
def memQuery (runtime : Nat) : Nat := runtime

/-- `total_memory()`, base/sysinfo.jl:420-428. -/
def totalMemory (constrained physical : Nat) : Nat :=
  if 0 < constrained ∧ constrained ≤ physical then constrained else physical

/-- `get_process_title()`, base/sysinfo.jl:435-440: the 512-byte buffer read as
a C string. -/
def getProcessTitle (err : Int) (buf : List Nat) : Rt (List Nat) := do
  uvError err
  pure ((buf.take 512).takeWhile (· ≠ 0))

/-- `set_process_title(title)`, base/sysinfo.jl:447-450. -/
def setProcessTitle (err : Int) : Rt Unit := uvError err

/-- `windows_version()` on Windows, base/sysinfo.jl:463-466: fields of `GetVersion()`. -/
def windowsVersionWin (verinfo : Nat) : Nat × Nat × Nat :=
  (verinfo % 256, (verinfo / 256) % 256, verinfo / 65536)
/-- `windows_version()` elsewhere, base/sysinfo.jl:468: `v"0.0"`. -/
def windowsVersionOther : Nat × Nat × Nat := (0, 0, 0)

/-- The file-system facts `which` consults for one candidate path. -/
inductive Probe where
  | found
  | notFound
  | eacces
  | otherError (code : Int)
  deriving DecidableEq, Repr

/-- The candidate search of `which`, base/sysinfo.jl:535-557: the first
directory/name combination that is an executable file, skipping permission
errors and rethrowing other I/O errors. `rest` holds the names still to try
in the current directory. -/
def searchCandidates (join : String → String → String) (probe : String → Probe)
    (names : List String) : List String → List String → Rt (Option String)
  | [], _ => .ok none
  | _ :: ds, [] => searchCandidates join probe names ds names
  | d :: ds, n :: ns =>
    match probe (join d n) with
    | .found => .ok (some (join d n))
    | .notFound => searchCandidates join probe names (d :: ds) ns
    | .eacces => searchCandidates join probe names (d :: ds) ns
    | .otherError c => .error (.ioError c)
termination_by dirs rest => (dirs.length, rest.length)

/-- The host and path primitives `which` uses. -/
structure WhichEnv where
  iswindows : Bool
  basename : String → String
  dirname : String → String
  extension : String → String
  abspath : String → String
  join : String → String → String
  pwd : String
  pathEnv : Option String
  probe : String → Probe

/-- `which(program_name::String)`, base/sysinfo.jl:495-561. -/
def which (e : WhichEnv) (programName : String) : Rt (Option String) :=
  if programName.isEmpty then .ok none else
  let base := e.basename programName
  let names :=
    if e.iswindows then
      (if !(e.extension base).isEmpty then [base] else []) ++ [base ++ ".exe", base ++ ".com"]
    else [base]
  let dir := e.dirname programName
  let dirs :=
    if dir.isEmpty then
      let sep := if e.iswindows then ";" else ":"
      let ds := ((e.pathEnv.getD "").splitOn sep).map e.abspath
      if e.iswindows then e.pwd :: ds else ds
    else [e.abspath dir]
  searchCandidates e.join e.probe names dirs names

/-- `which(program_name::AbstractString)`, base/sysinfo.jl:562: converts to `String`. -/
def whichAbstract (e : WhichEnv) (toStr : α → String) (p : α) : Rt (Option String) :=
  which e (toStr p)

/-- `username()`, base/sysinfo.jl:581-585. -/
def username (pwName : String) : Rt String :=
  if pwName.isEmpty then .error (.ioError UV_ENOENT) else .ok pwName
end JuliaLean.RuntimeCov.SysInfo
end
