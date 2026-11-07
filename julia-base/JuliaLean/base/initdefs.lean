import JuliaLean.base.path
import JuliaLean.base.runtime_internals
import JuliaLean.base.io

/-!
# Model of `base/initdefs.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Path strings are generic typed values; `PathOps` supplies the earlier string and
filesystem callees, so malformed UTF-8 paths remain representable. Mutable global
vectors retain their reference identity through `VectorOps`. The IO world and
exceptions use `base.io.M`, including changes made before errors. The mutually
calling active-project and load-path-expansion methods expose their calls as typed
interfaces. Locks, process exit, task state, cancellation scopes and callback
invocation are typed runtime primitives. Macro syntax is represented by its
execution on a typed body, preserving the try/finally scope.
The path rules are documented in `doc/src/manual/environment-variables.md`
(`JULIA_PROJECT`, `JULIA_LOAD_PATH`, `JULIA_DEPOT_PATH`) and
`doc/src/manual/code-loading.md` (project environments and environment stacks).
-/

namespace JuliaLean.base.initdefs
open JuliaLean
open JuliaLean.base.io (M Error whileLoop finallyDo)
abbrev I := JInt64
def i (z : Int) : I := JInt.wrap .i64 z

structure VectorOps (World Vector Element : Type) where
  newVector : M World Vector
  values : Vector → M World (List Element)
  empty : Vector → M World Unit
  push : Vector → Element → M World Unit
  pushfirst : Vector → Element → M World Unit
  pop : Vector → M World Element
  popfirst : Vector → M World Element

structure PathOps (World Path : Type) where
  literal : String → Path
  isEmpty : Path → Bool
  startsWith : Path → String → Bool
  concat : Path → Path → M World Path
  sliceFrom : Path → I → M World Path
  replaceFirstHash : Path → I → M World Path
  split : Path → Bool → List Path
  env : String → M World (Option Path)
  expanduser : Path → M World Path
  home : M World Path
  pwd : M World Path
  joinpath : List Path → M World Path
  abspath : List Path → M World Path
  dirname : Path → M World Path
  basename : Path → M World Path
  isfileCasesensitive : Path → M World Bool
  isdir : Path → M World Bool
  ispath : Path → M World Bool
  mktempdir : M World Path
  iswindows : Bool
  bindir : Path
  datarootdir : Path
  stdlib : Path
  versionMajor : I
  versionMinor : I
  versionPatch : I
  projectNames : List Path

structure ProjectOps (World Path Vector Callback : Type) where
  depotPath : Vector
  loadPath : Vector
  activeValue : M World (Option Path)
  setActiveValue : Option Path → M World Unit
  activeCallbacks : M World (List Callback)
  invoke : Callback → M World Unit
  logCallbackError : Callback → M World Unit
  optionProject : M World (Option Path)
  optionProgramFile : M World (Option Path)
  activeProject : Bool → M World (Option Path)
  currentProject : M World (Option Path)
  currentProjectFrom : Path → M World (Option Path)
  expand : Option Path → M World (Option Path)
  setActiveProject : Option Path → M World Unit
  initNamedEnv : Path → M World (Option Path)
  manifestPath : Path → M World (Option Path)
  loadingCache : M World (Option Vector)

structure HookOps (World Hook Lock : Type) where
  lock : Lock → M World Unit
  unlock : Lock → M World Unit
  exitLock : Lock
  exitHooks : M World (List Hook)
  popExitFirst : M World Hook
  pushExitFirst : Hook → M World Unit
  hooksFinished : M World Bool
  setHooksFinished : Bool → M World Unit
  generatingOutput : M World Bool
  precompileInt : Hook → M World Bool
  precompileEmpty : Hook → M World Bool
  hasIntMethod : Hook → M World Bool
  invokeInt : Hook → JInt .i32 → M World Unit
  invokeEmpty : Hook → M World Unit
  showError : Error → M World Unit
  showBacktrace : M World Unit
  println : M World Unit
  postHooks : M World (List Hook)
  pushPostFirst : Hook → M World Unit
  popPostFirst : M World Hook
  threadingHooks : M World (List Hook)
  pushThreading : Hook → M World Unit
  popThreading : M World Hook
  threadingEnabled : M World Bool
  setThreadingEnabled : Bool → M World Unit
  disableThreading : M World Unit
  warnThreading : Error → M World Unit

def locked {World Hook Lock A : Type} (ops : HookOps World Hook Lock) (body : M World A) : M World A := do
  ops.lock ops.exitLock
  finallyDo body (ops.unlock ops.exitLock)

/--
Julia source: base/initdefs.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exit(n) = ccall(:jl_exit, Union{}, (Int32,), n)
```
-/
def exitCode {World Number : Type} (convertInt32 : Number → M World (JInt .i32))
    (jlExit : JInt .i32 → M World Empty) (n : Number) : M World Empty := do
  jlExit (← convertInt32 n)

/--
Julia source: base/initdefs.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exit() = exit(0)
```
-/
def exitDefault {World : Type} (exit : I → M World Empty) : M World Empty := exit (i 0)

/--
Julia source: base/initdefs.jl:42-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
foreground_task() = lock(getindex, _foreground_task)
```
-/
def foregroundTask {World Task Ref : Type}
    (foreground : Ref) (lockGetindex : Ref → M World (Option Task)) : M World (Option Task) :=
  lockGetindex foreground

/--
Julia source: base/initdefs.jl:52-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro as_foreground_task(expr)
    quote
        local ref = $(GlobalRef(@__MODULE__, :_foreground_task))
        local prev = lock(ref) do r
            local old = r[]
            r[] = current_task()
            old
        end
        try
            $(esc(expr))
        finally
            lock(r -> r[] = prev, ref)
        end
    end
end
```
-/
def asForegroundTask {World Task Ref A : Type}
    (currentTask : M World Task) (get : Ref → M World (Option Task))
    (set : Ref → Option Task → M World Unit)
    (withForegroundLock : {B : Type} → (Ref → M World B) → M World B)
    (body : M World A) : M World A := do
  let previous ← withForegroundLock fun ref => do
    let old ← get ref
    set ref (some (← currentTask))
    pure old
  finallyDo body (withForegroundLock (fun ref => set ref previous))

/--
Julia source: base/initdefs.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinteractive() = is_interactive
```
-/
def isinteractive {World : Type} (isInteractive : M World Bool) : M World Bool := isInteractive

/--
Julia source: base/initdefs.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const DEFAULT_LOAD_PATH = ["@", "@v#.#", "@stdlib"]
```
-/
def defaultLoadPath {World Path : Type} (ops : PathOps World Path) : List Path :=
  [ops.literal "@", ops.literal "@v#.#", ops.literal "@stdlib"]

/--
Julia source: base/initdefs.jl:132-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append_bundled_depot_path!(DEPOT_PATH)
    path = abspath(Sys.BINDIR, "..", "local", "share", "julia")
    path in DEPOT_PATH || push!(DEPOT_PATH, path)
    path = abspath(Sys.BINDIR, DATAROOTDIR, "julia")
    path in DEPOT_PATH || push!(DEPOT_PATH, path)
    return DEPOT_PATH
end
```
-/
def appendBundledDepotPath {World Path Vector : Type} [BEq Path]
    (ops : PathOps World Path) (vec : VectorOps World Vector Path) (depot : Vector) : M World Vector := do
  let path ← ops.abspath [ops.bindir, ops.literal "..", ops.literal "local", ops.literal "share", ops.literal "julia"]
  if !(← vec.values depot).contains path then vec.push depot path
  let path ← ops.abspath [ops.bindir, ops.datarootdir, ops.literal "julia"]
  if !(← vec.values depot).contains path then vec.push depot path
  pure depot

/--
Julia source: base/initdefs.jl:140-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function init_depot_path()
    empty!(DEPOT_PATH)
    if haskey(ENV, "JULIA_DEPOT_PATH")
        str = ENV["JULIA_DEPOT_PATH"]

        # explicitly setting JULIA_DEPOT_PATH to the empty string means using no depot
        isempty(str) && return

        # otherwise, populate the depot path with the entries in JULIA_DEPOT_PATH,
        # expanding empty strings to the bundled depot
        pushfirst_default = true
        for (i, path) in enumerate(eachsplit(str, Sys.iswindows() ? ';' : ':'))
            if isempty(path)
                append_bundled_depot_path!(DEPOT_PATH)
            else
                path = expanduser(path)
                path in DEPOT_PATH || push!(DEPOT_PATH, path)
                if i == 1
                    # if a first entry is given, don't add the default depot at the start
                    pushfirst_default = false
                end
            end
        end

        # backwards compatibility: if JULIA_DEPOT_PATH only contains empty entries
        # (e.g., JULIA_DEPOT_PATH=':'), make sure to use the default depot
        if pushfirst_default
            pushfirst!(DEPOT_PATH, joinpath(homedir(), ".julia"))
        end
    else
        push!(DEPOT_PATH, joinpath(homedir(), ".julia"))
        append_bundled_depot_path!(DEPOT_PATH)
    end
    nothing
end
```
-/
def initDepotPath {World Path Vector : Type} [BEq Path]
    (ops : PathOps World Path) (vec : VectorOps World Vector Path) (depot : Vector) : M World Unit := do
  vec.empty depot
  if let some str ← ops.env "JULIA_DEPOT_PATH" then
    if ops.isEmpty str then return
    let mut pushfirstDefault := true
    for (path, index) in (ops.split str ops.iswindows).zipIdx do
      if ops.isEmpty path then
        let _ ← appendBundledDepotPath ops vec depot
      else
        let path ← ops.expanduser path
        if !(← vec.values depot).contains path then vec.push depot path
        if index == 0 then pushfirstDefault := false
    if pushfirstDefault then vec.pushfirst depot (← ops.joinpath [← ops.home, ops.literal ".julia"])
  else
    vec.push depot (← ops.joinpath [← ops.home, ops.literal ".julia"])
    let _ ← appendBundledDepotPath ops vec depot
  pure ()

/--
Julia source: base/initdefs.jl:237-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function current_project(dir::AbstractString)
    # look for project file in current dir and parents
    home = homedir()
    while true
        for proj in project_names
            file = joinpath(dir, proj)
            isfile_casesensitive(file) && return file
        end
        # bail at home directory
        dir == home && break
        old, dir = dir, dirname(dir)
        dir == old && break
    end
end
```
-/
def currentProjectFrom {World Path : Type} [BEq Path]
    (ops : PathOps World Path) (dir : Path) : M World (Option Path) := do
  let home ← ops.home
  whileLoop (fun dir => do
    for proj in ops.projectNames do
      let file ← ops.joinpath [dir, proj]
      if ← ops.isfileCasesensitive file then return .inl (some file)
    if dir == home then return .inl none
    let old := dir
    let dir ← ops.dirname dir
    if dir == old then return .inl none
    pure (.inr dir)) dir

/--
Julia source: base/initdefs.jl:252-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function current_project()
    dir = try pwd()
    catch err
        err isa IOError || rethrow()
        return nothing
    end
    return current_project(dir)
end
```
-/
def currentProject {World Path : Type} [BEq Path]
    (ops : PathOps World Path) : M World (Option Path) := do
  let dir ← try
      pure (some (← ops.pwd))
    catch error =>
      match error with
      | .foreignError "IOError" _ => pure none
      | _ => throw error
  match dir with
  | none => pure none
  | some dir => currentProjectFrom ops dir

/--
Julia source: base/initdefs.jl:261-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_load_path(str::String)
    envs = String[]
    isempty(str) && return envs
    for env in eachsplit(str, Sys.iswindows() ? ';' : ':')
        if isempty(env)
            for env′ in DEFAULT_LOAD_PATH
                env′ in envs || push!(envs, env′)
            end
        else
            if env == "@."
                env = current_project()
                env === nothing && continue
            end
            env = expanduser(env)
            env in envs || push!(envs, env)
        end
    end
    return envs
end
```
-/
def parseLoadPath {World Path : Type} [BEq Path]
    (ops : PathOps World Path) (currentProject : M World (Option Path))
    (str : Path) : M World (List Path) := do
  let mut envs := []
  if ops.isEmpty str then return envs
  for env in ops.split str ops.iswindows do
    if ops.isEmpty env then
      for env in defaultLoadPath ops do
        if !envs.contains env then envs := envs ++ [env]
    else
      let env ← if env == ops.literal "@." then currentProject else pure (some env)
      if let some env := env then
        let env ← ops.expanduser env
        if !envs.contains env then envs := envs ++ [env]
  pure envs

/--
Julia source: base/initdefs.jl:281-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function init_load_path()
    if haskey(ENV, "JULIA_LOAD_PATH")
        paths = parse_load_path(ENV["JULIA_LOAD_PATH"])
    else
        paths = String[]
        for env in DEFAULT_LOAD_PATH
            if env == "@."
                env = current_project()
                env === nothing && continue
            end
            push!(paths, env)
        end
    end
    append!(empty!(LOAD_PATH), paths)
end
```
-/
def initLoadPath {World Path Vector : Type} [BEq Path]
    (ops : PathOps World Path) (vec : VectorOps World Vector Path)
    (currentProject : M World (Option Path)) (loadPath : Vector) : M World Vector := do
  let paths ← if let some str ← ops.env "JULIA_LOAD_PATH" then
      parseLoadPath ops currentProject str
    else do
      let mut paths := []
      for env in defaultLoadPath ops do
        let env ← if env == ops.literal "@." then currentProject else pure (some env)
        if let some env := env then paths := paths ++ [env]
      pure paths
  vec.empty loadPath
  for path in paths do vec.push loadPath path
  pure loadPath

/--
Julia source: base/initdefs.jl:297-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function init_active_project()
    project = (JLOptions().project != C_NULL ?
        unsafe_string(JLOptions().project) :
        get(ENV, "JULIA_PROJECT", nothing))
    set_active_project(
        project === nothing ? nothing :
        project == "" ? nothing :
        startswith(project, "@") ? load_path_expand(project) : abspath(expanduser(project))
    )
end
```
-/
def initActiveProject {World Path Vector Callback : Type} [BEq Path]
    (ops : PathOps World Path) (proj : ProjectOps World Path Vector Callback) : M World Unit := do
  let project ← match ← proj.optionProject with
    | some project => pure (some project)
    | none => ops.env "JULIA_PROJECT"
  let expanded ← match project with
    | none => pure none
    | some path =>
      if ops.isEmpty path then pure none
      else if ops.startsWith path "@" then proj.expand (some path)
      else do pure (some (← ops.abspath [← ops.expanduser path]))
  proj.setActiveProject expanded

/--
Julia source: base/initdefs.jl:308-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function init_named_env!(path)
    try
        mkpath(dirname(path))
        io = open(path, "w")
        try
            print(io, "syntax.julia_version = \"",VERSION,"\"")
        finally
            close(io)
        end
        return path
    catch e
        @warn "Failed to initialize named environment at $path: $e"
        return nothing
    end
end
```
-/
def initNamedEnv {World Path Stream : Type} (ops : PathOps World Path)
    (mkpath : Path → M World Unit) (openWrite : Path → M World Stream)
    (printVersion : Stream → M World Unit) (close : Stream → M World Unit)
    (warn : Path → Error → M World Unit) (path : Path) : M World (Option Path) := do
  try
    mkpath (← ops.dirname path)
    let io ← openWrite path
    finallyDo (printVersion io) (close io)
    pure (some path)
  catch error =>
    warn path error
    pure none

/--
Julia source: base/initdefs.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmd_suppresses_program(cmd) = cmd in ('e', 'E')
```
-/
def cmdSuppressesProgram {Command : Type} [BEq Command] (e E : Command) (cmd : Command) : Bool :=
  cmd == e || cmd == E

/--
Julia source: base/initdefs.jl:327-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function load_path_expand(env::AbstractString)::Union{String, Nothing}
    # named environment?
    if startswith(env, '@')
        # `@.` in JULIA_LOAD_PATH is expanded early (at startup time)
        # if you put a `@.` in LOAD_PATH manually, it's expanded late
        env == "@" && return active_project(false)
        env == "@." && return current_project()
        env == "@temp" && return mktempdir()
        env == "@stdlib" && return Sys.STDLIB
        if startswith(env, "@script")
            program_file = JLOptions().program_file
            program_file = program_file != C_NULL ? unsafe_string(program_file) : nothing
            isnothing(program_file) && return nothing # User did not pass a script

            # Expand trailing relative path
            dir = dirname(program_file)
            dir = env != "@script" ? (dir * env[length("@script")+1:end]) : dir
            return current_project(dir)
        end
        env = replace(env, '#' => VERSION.major, count=1)
        env = replace(env, '#' => VERSION.minor, count=1)
        env = replace(env, '#' => VERSION.patch, count=1)
        name = env[2:end]
        # look for named env in each depot
        for depot in DEPOT_PATH
            path = joinpath(depot, "environments", name)
            isdir(path) || continue
            for proj in project_names
                file = abspath(path, proj)
                isfile_casesensitive(file) && return file
            end
        end
        isempty(DEPOT_PATH) && return nothing
        new_named_env_path = abspath(DEPOT_PATH[1], "environments", name, project_names[end])
        return init_named_env!(new_named_env_path)
    end
    # otherwise, it's a path
    path = abspath(env)
    if isdir(path)
        # directory with a project file?
        for proj in project_names
            file = joinpath(path, proj)
            isfile_casesensitive(file) && return file
        end
    end
    # package dir or path to project file
    return path
end
```
-/
def loadPathExpand {World Path Vector Callback : Type} [BEq Path]
    (ops : PathOps World Path) (vec : VectorOps World Vector Path)
    (proj : ProjectOps World Path Vector Callback) (env : Path) : M World (Option Path) := do
  if ops.startsWith env "@" then
    if env == ops.literal "@" then return ← proj.activeProject false
    if env == ops.literal "@." then return ← proj.currentProject
    if env == ops.literal "@temp" then return some (← ops.mktempdir)
    if env == ops.literal "@stdlib" then return some ops.stdlib
    if ops.startsWith env "@script" then
      let programFile ← proj.optionProgramFile
      match programFile with
      | none => pure none
      | some programFile =>
        let mut dir ← ops.dirname programFile
        if env != ops.literal "@script" then
          dir := ← ops.concat dir (← ops.sliceFrom env (i 8))
        proj.currentProjectFrom dir
    else
      let env ← ops.replaceFirstHash env ops.versionMajor
      let env ← ops.replaceFirstHash env ops.versionMinor
      let env ← ops.replaceFirstHash env ops.versionPatch
      let name ← ops.sliceFrom env (i 2)
      for depot in ← vec.values proj.depotPath do
        let path ← ops.joinpath [depot, ops.literal "environments", name]
        if !(← ops.isdir path) then continue
        for project in ops.projectNames do
          let file ← ops.abspath [path, project]
          if ← ops.isfileCasesensitive file then return some file
      let depots ← vec.values proj.depotPath
      match depots, ops.projectNames.getLast? with
      | [], _ => pure none
      | depot :: _, some last =>
        let newPath ← ops.abspath [depot, ops.literal "environments", name, last]
        proj.initNamedEnv newPath
      | _, none => throw (.jl .boundsError)
  else
    let path ← ops.abspath [env]
    if ← ops.isdir path then
      for project in ops.projectNames do
        let file ← ops.joinpath [path, project]
        if ← ops.isfileCasesensitive file then return some file
    pure (some path)

/--
Julia source: base/initdefs.jl:375-375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
load_path_expand(::Nothing) = nothing
```
-/
def loadPathExpandNothing {Path : Type} : Option Path := none

/--
Julia source: base/initdefs.jl:382-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function active_project(search_load_path::Bool=true)
    for project in (ACTIVE_PROJECT[],)
        project == "@" && continue
        project = load_path_expand(project)
        project === nothing && continue
        # while this seems well-inferred, nevertheless without the type annotation below
        # there are backedges here from abspath(::AbstractString, ::String)
        project = project::String
        if !isfile_casesensitive(project) && basename(project) ∉ project_names
            project = abspath(project, "Project.toml")
        end
        return project
    end
    search_load_path || return
    for project in LOAD_PATH
        project == "@" && continue
        project = load_path_expand(project)
        project === nothing && continue
        isfile_casesensitive(project) && return project
        ispath(project) && continue
        basename(project) in project_names && return project
    end
end
```
-/
def activeProject {World Path Vector Callback : Type} [BEq Path]
    (ops : PathOps World Path) (vec : VectorOps World Vector Path)
    (proj : ProjectOps World Path Vector Callback) (searchLoadPath : Bool := true) : M World (Option Path) := do
  let initial ← proj.activeValue
  if initial != some (ops.literal "@") then
    if let some project ← proj.expand initial then
      let mut project := project
      if !(← ops.isfileCasesensitive project) then
        if !ops.projectNames.contains (← ops.basename project) then
          project := ← ops.abspath [project, ops.literal "Project.toml"]
      return some project
  if !searchLoadPath then return none
  for project in ← vec.values proj.loadPath do
    if project == ops.literal "@" then continue
    if let some project ← proj.expand (some project) then
      if ← ops.isfileCasesensitive project then return some project
      if ← ops.ispath project then continue
      if ops.projectNames.contains (← ops.basename project) then return some project
  pure none

/--
Julia source: base/initdefs.jl:414-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function set_active_project(projfile::Union{AbstractString,Nothing})
    ACTIVE_PROJECT[] = projfile
    for f in active_project_callbacks
        try
            invokelatest(f)
        catch
            @error "active project callback $f failed" maxlog=1
        end
    end
end
```
-/
def setActiveProject {World Path Vector Callback : Type}
    (proj : ProjectOps World Path Vector Callback) (projfile : Option Path) : M World Unit := do
  proj.setActiveValue projfile
  whileLoop (fun index => do
    let callbacks ← proj.activeCallbacks
    match callbacks[index]? with
    | none => pure (.inl ())
    | some f =>
      try proj.invoke f
      catch _ => proj.logCallbackError f
      pure (.inr (index + 1))) (0 : Nat)

/--
Julia source: base/initdefs.jl:443-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function active_manifest(project_file::Union{AbstractString,Nothing}=nothing; search_load_path::Bool=true)
    # If `project_file` was specified, use that, otherwise get the active project:
    project_file = !isnothing(project_file) ? project_file : active_project(search_load_path)
    project_file === nothing && return nothing
    return project_file_manifest_path(project_file)
end
```
-/
def activeManifest {World Path Vector Callback : Type}
    (proj : ProjectOps World Path Vector Callback) (projectFile : Option Path := none)
    (searchLoadPath : Bool := true) : M World (Option Path) := do
  let projectFile ← if projectFile.isSome then pure projectFile else proj.activeProject searchLoadPath
  match projectFile with
  | none => pure none
  | some project => proj.manifestPath project

/--
Julia source: base/initdefs.jl:460-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function load_path()
    cache = LOADING_CACHE[]
    cache !== nothing && return cache.load_path
    paths = String[]
    for env in LOAD_PATH
        path = load_path_expand(env)
        path !== nothing && path ∉ paths && push!(paths, path)
    end
    return paths
end
```
-/
def loadPath {World Path Vector Callback : Type} [BEq Path]
    (vec : VectorOps World Vector Path) (proj : ProjectOps World Path Vector Callback) : M World Vector := do
  if let some cache ← proj.loadingCache then return cache
  let paths ← vec.newVector
  for env in ← vec.values proj.loadPath do
    if let some path ← proj.expand (some env) then
      if !(← vec.values paths).contains path then vec.push paths path
  pure paths

/--
Julia source: base/initdefs.jl:502-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function atexit(f::Function)
    # HACK: if generating output, hint that we might want to compile `f`, so that it is available for the no-codegen test
    generating_output() && (precompile(f, (Cint,)) || precompile(f, ()))
    @lock _atexit_hooks_lock begin
        _atexit_hooks_finished && error("cannot register new atexit hook; already exiting.")
        pushfirst!(atexit_hooks, f)
        return nothing
    end
end
```
-/
def atexit {World Hook Lock : Type} (ops : HookOps World Hook Lock) (f : Hook) : M World Unit := do
  if ← ops.generatingOutput then
    if !(← ops.precompileInt f) then
      let _ ← ops.precompileEmpty f
  locked ops do
    if ← ops.hooksFinished then throw (.errorException "cannot register new atexit hook; already exiting.")
    ops.pushExitFirst f

/--
Julia source: base/initdefs.jl:512-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _atexit(exitcode::Cint)
    # this current task shouldn't be scheduled anywhere, but if it was (because
    # this exit came from a signal for example), then try to clear that state
    # to minimize scheduler issues later
    ct = current_task()
    q = ct.queue
    if q !== nothing
        try
            list_deletefirst!(q::StickyWorkqueue, ct)
        catch
            # best-effort cleanup on the way out
        end
    end
    # If this task's wait registration is still armed (e.g. this exit came
    # from a signal while parked), disarm it: the waitee-queue entry is
    # stale and gets dropped by whoever pops it, and the sticky source
    # registration is collected by a walk once this task is done.
    @atomicswap ct.waiting_on = nothing
    # We are exiting: any pending cancellation of this task's scope is moot
    # and would only disrupt the atexit hooks - run them in a shielded scope.
    return ScopedValues.@with(CANCEL_TOKEN => nothing, _run_atexit_hooks(exitcode))
end
```
-/
def atexitCleanup {World Task Queue : Type} (currentTask : M World Task)
    (queue : Task → M World (Option Queue)) (deleteFirst : Queue → Task → M World Unit)
    (atomicClearWaiting : Task → M World Unit) (withCancellationDisabled : M World Unit → M World Unit)
    (runHooks : JInt .i32 → M World Unit) (exitcode : JInt .i32) : M World Unit := do
  let ct ← currentTask
  if let some q ← queue ct then
    try deleteFirst q ct
    catch _ => pure ()
  atomicClearWaiting ct
  withCancellationDisabled (runHooks exitcode)

/--
Julia source: base/initdefs.jl:535-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _run_atexit_hooks(exitcode::Cint)
    # Don't hold the lock around the iteration, just in case any other thread executing in
    # parallel tries to register a new atexit hook while this is running. We don't want to
    # block that thread from proceeding, and we can allow it to register its hook which we
    # will immediately run here.
    while true
        local f
        @lock _atexit_hooks_lock begin
            # If this is the last iteration, atomically disable atexit hooks to prevent
            # someone from registering a hook that will never be run.
            # (We do this inside the loop, so that it is atomic: no one can have registered
            #  a hook that never gets run, and we run all the hooks we know about until
            #  the vector is empty.)
            if isempty(atexit_hooks)
                global _atexit_hooks_finished = true
                break
            end

            f = popfirst!(atexit_hooks)
        end
        try
            if hasmethod(f, (Cint,))
                f(exitcode)
            else
                f()
            end
        catch ex
            showerror(stderr, ex)
            show_backtrace(stderr, catch_backtrace())
            println(stderr)
        end
    end
end
```
-/
def runAtexitHooks {World Hook Lock : Type} (ops : HookOps World Hook Lock)
    (exitcode : JInt .i32) : M World Unit :=
  whileLoop (fun (_ : Unit) => do
    let next ← locked ops do
      if (← ops.exitHooks).isEmpty then
        ops.setHooksFinished true
        pure none
      else return some (← ops.popExitFirst)
    match next with
    | none => pure (.inl ())
    | some f =>
      try
        if ← ops.hasIntMethod f then ops.invokeInt f exitcode else ops.invokeEmpty f
      catch error =>
        ops.showError error
        ops.showBacktrace
        ops.println
      pure (.inr ())) ()

/--
Julia source: base/initdefs.jl:574-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
postoutput(f::Function) = (pushfirst!(postoutput_hooks, f); nothing)
```
-/
def postoutput {World Hook Lock : Type} (ops : HookOps World Hook Lock) (f : Hook) : M World Unit :=
  ops.pushPostFirst f

/--
Julia source: base/initdefs.jl:576-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _postoutput()
    while !isempty(postoutput_hooks)
        f = popfirst!(postoutput_hooks)
        try
            f()
        catch ex
            showerror(stderr, ex)
            show_backtrace(stderr, catch_backtrace())
            println(stderr)
        end
    end
end
```
-/
def runPostoutput {World Hook Lock : Type} (ops : HookOps World Hook Lock) : M World Unit :=
  whileLoop (fun (_ : Unit) => do
    if (← ops.postHooks).isEmpty then return .inl ()
    let f ← ops.popPostFirst
    try ops.invokeEmpty f
    catch error =>
      ops.showError error
      ops.showBacktrace
      ops.println
    pure (.inr ())) ()

/--
Julia source: base/initdefs.jl:597-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function at_disable_library_threading(f)
    push!(disable_library_threading_hooks(), f)
    if !library_threading_enabled
        disable_library_threading()
    end
    return
end
```
-/
def atDisableLibraryThreading {World Hook Lock : Type}
    (ops : HookOps World Hook Lock) (f : Hook) : M World Unit := do
  ops.pushThreading f
  if !(← ops.threadingEnabled) then ops.disableThreading
  pure ()

/--
Julia source: base/initdefs.jl:605-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function disable_library_threading()
    global library_threading_enabled = false
    while !isempty(disable_library_threading_hooks())
        f = pop!(disable_library_threading_hooks())
        try
            f()
        catch err
            @warn("a hook from a library to disable threading failed:",
                  exception = (err, catch_backtrace()))
        end
    end
    return
end
```
-/
def disableLibraryThreading {World Hook Lock : Type} (ops : HookOps World Hook Lock) : M World Unit := do
  ops.setThreadingEnabled false
  whileLoop (fun (_ : Unit) => do
    if (← ops.threadingHooks).isEmpty then return .inl ()
    let f ← ops.popThreading
    try ops.invokeEmpty f
    catch error => ops.warnThreading error
    pure (.inr ())) ()


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/initdefs.jl:1-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## initdefs.jl - initialization and runtime management definitions
-- 
-- """
--     PROGRAM_FILE
-- 
-- A string containing the script name passed to Julia from the command line. Note that the
-- script name remains unchanged from within included files. Alternatively see
-- [`@__FILE__`](@ref).
-- """
-- global PROGRAM_FILE::String = ""
-- 
-- """
--     ARGS
-- 
-- An array of the command line arguments passed to Julia, as strings.
-- """
-- const ARGS = String[]
-- 
-- """
--     exit(code=0)
-- 
-- Stop the program with an exit code. The default exit code is zero, indicating that the
-- program completed successfully. In an interactive session, `exit()` can be called with
-- the keyboard shortcut `^D`.
-- """
-- /Source

-- Source: base/initdefs.jl:30-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- const roottask = current_task()
-- 
-- const _foreground_task = Lockable(Ref{Union{Task, Nothing}}(nothing))
-- 
-- """
--     Base.foreground_task() -> Union{Task, Nothing}
-- 
-- Return the task currently designated as the "foreground" task — typically the task
-- that owns interactive stdin (e.g. a REPL command-execution task). Returns `nothing`
-- if no task has been registered as foreground.
-- """
-- /Source

-- Source: base/initdefs.jl:43-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     Base.@as_foreground_task expr
-- 
-- Evaluate `expr` with [`current_task()`](@ref) registered as the foreground task
-- (see [`foreground_task`](@ref)), restoring the previous foreground task on exit.
-- Used to mark the section of code where a particular task "owns" interactive stdin
-- so that other components (e.g. the precompile keyboard menu) can defer to it.
-- """
-- /Source

-- Source: base/initdefs.jl:67-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- is_interactive::Bool = false
-- 
-- """
--     isinteractive()::Bool
-- 
-- Determine whether Julia is running an interactive session.
-- """
-- /Source

-- Source: base/initdefs.jl:76-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## package depots (registries, packages, environments) ##
-- 
-- """
--     DEPOT_PATH
-- 
-- A stack of "depot" locations where the package manager, as well as Julia's code
-- loading mechanisms, look for package registries, installed packages, named
-- environments, repo clones, cached compiled package images, and configuration
-- files. By default it includes:
-- 
-- 1. `~/.julia` where `~` is the user home as appropriate on the system;
-- 2. an architecture-specific shared system directory, e.g. `/usr/local/share/julia`;
-- 3. an architecture-independent shared system directory, e.g. `/usr/share/julia`.
-- 
-- So `DEPOT_PATH` might be:
-- ```julia
-- [joinpath(homedir(), ".julia"), "/usr/local/share/julia", "/usr/share/julia"]
-- ```
-- The first entry is the "user depot" and should be writable by and owned by the
-- current user. The user depot is where: registries are cloned, new package versions
-- are installed, named environments are created and updated, package repos are cloned,
-- newly compiled package image files are saved, log files are written, development
-- packages are checked out by default, and global configuration data is saved. Later
-- entries in the depot path are treated as read-only and are appropriate for
-- registries, packages, etc. installed and managed by system administrators.
-- 
-- `DEPOT_PATH` is populated based on the [`JULIA_DEPOT_PATH`](@ref JULIA_DEPOT_PATH)
-- environment variable if set.
-- 
-- ## DEPOT_PATH contents
-- 
-- Each entry in `DEPOT_PATH` is a path to a directory which contains subdirectories used by Julia for various purposes.
-- Here is an overview of some of the subdirectories that may exist in a depot:
-- 
-- * `artifacts`: Contains content that packages use for which Pkg manages the installation of.
-- * `clones`: Contains full clones of package repos. Maintained by `Pkg.jl` and used as a cache.
-- * `config`: Contains julia-level configuration such as a `startup.jl`.
-- * `compiled`: Contains precompiled `*.ji` files for packages. Maintained by Julia.
-- * `dev`: Default directory for `Pkg.develop`. Maintained by `Pkg.jl` and the user.
-- * `environments`: Default package environments. For instance the global environment for a specific julia version. Maintained by `Pkg.jl`.
-- * `logs`: Contains logs of `Pkg` and `REPL` operations. Maintained by `Pkg.jl` and Julia.
-- * `packages`: Contains packages, some of which were explicitly installed and some which are implicit dependencies. Maintained by `Pkg.jl`.
-- * `registries`: Contains package registries. By default only `General`. Maintained by `Pkg.jl`.
-- * `scratchspaces`: Contains content that a package itself installs via the [`Scratch.jl`](https://github.com/JuliaPackaging/Scratch.jl) package. `Pkg.gc()` will delete content that is known to be unused.
-- 
-- !!! note
--     Packages that want to store content should use the `scratchspaces` subdirectory via
--     [`Scratch.jl`](https://github.com/JuliaPackaging/Scratch.jl) instead of creating new
--     subdirectories in the depot root.
-- 
-- See also [`JULIA_DEPOT_PATH`](@ref JULIA_DEPOT_PATH), and
-- [Code Loading](@ref code-loading).
-- """
-- const DEPOT_PATH = String[]
-- 
-- /Source

-- Source: base/initdefs.jl:139-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:175-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## LOAD_PATH & ACTIVE_PROJECT ##
-- 
-- # JULIA_LOAD_PATH: split on `:` (or `;` on Windows)
-- # first empty entry is replaced with DEFAULT_LOAD_PATH, the rest are skipped
-- # entries starting with `@` are named environments:
-- #  - the first three `#`s in a named environment are replaced with version numbers
-- #  - `@stdlib` is a special name for the standard library and expands to its path
-- 
-- # if you want a current env setup, use direnv and
-- # have your .envrc do something like this:
-- #
-- #   export JULIA_LOAD_PATH="$(pwd):$JULIA_LOAD_PATH"
-- #
-- # this will inherit an existing JULIA_LOAD_PATH value or if there is none, leave
-- # a trailing empty entry in JULIA_LOAD_PATH which will be replaced with defaults.
-- 
-- /Source

-- Source: base/initdefs.jl:193-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     LOAD_PATH
-- 
-- An array of paths for `using` and `import` statements to consider as project
-- environments or package directories when loading code. It is populated based on
-- the [`JULIA_LOAD_PATH`](@ref JULIA_LOAD_PATH) environment variable if set;
-- otherwise it defaults to `["@", "@v#.#", "@stdlib"]`. Entries starting with `@`
-- have special meanings:
-- 
-- - `@` refers to the "current active environment", whose value is determined by the [`JULIA_PROJECT`](@ref JULIA_PROJECT) environment
--   variable or the `--project` command-line option.
-- 
-- - `@stdlib` expands to the absolute path of the current Julia installation's
--   standard library directory.
-- 
-- - `@name` refers to a named environment, which are stored in depots (see
--   [`JULIA_DEPOT_PATH`](@ref JULIA_DEPOT_PATH)) under the `environments`
--   subdirectory. The user's named environments are stored in
--   `~/.julia/environments` so `@name` would refer to the environment in
--   `~/.julia/environments/name` if it exists and contains a `Project.toml` file.
--   If `name` contains `#` characters, then they are replaced with the major, minor
--   and patch components of the Julia version number. For example, if you are
--   running Julia 1.2 then `@v#.#` expands to `@v1.2` and will look for an
--   environment by that name, typically at `~/.julia/environments/v1.2`.
-- 
-- The fully expanded value of `LOAD_PATH` that is searched for projects and packages
-- can be seen by calling the `Base.load_path()` function.
-- 
-- See also
-- [`JULIA_LOAD_PATH`](@ref JULIA_LOAD_PATH),
-- [`JULIA_PROJECT`](@ref JULIA_PROJECT),
-- [`JULIA_DEPOT_PATH`](@ref JULIA_DEPOT_PATH), and
-- [Code Loading](@ref code-loading).
-- """
-- const LOAD_PATH = copy(DEFAULT_LOAD_PATH)
-- # HOME_PROJECT is no longer used, here just to avoid breaking things
-- const HOME_PROJECT = Ref{Union{String,Nothing}}(nothing)
-- const ACTIVE_PROJECT = Ref{Union{String,Nothing}}(nothing) # Modify this only via `Base.set_active_project(proj)`
-- ## Watchers for when the active project changes (e.g., Revise)
-- # Each should be a thunk, i.e., `f()`. To determine the current active project,
-- # the thunk can query `Base.active_project()`.
-- const active_project_callbacks = []
-- 
-- /Source

-- Source: base/initdefs.jl:251-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:260-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:323-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## load path expansion: turn LOAD_PATH entries into concrete paths ##
-- /Source

-- Source: base/initdefs.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:376-381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     active_project()
-- 
-- Return the path of the active `Project.toml` file. See also [`Base.set_active_project`](@ref).
-- """
-- /Source

-- Source: base/initdefs.jl:405-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     set_active_project(projfile::Union{AbstractString,Nothing})
-- 
-- Set the active `Project.toml` file to `projfile`. See also [`Base.active_project`](@ref).
-- 
-- !!! compat "Julia 1.8"
--     This function requires at least Julia 1.8.
-- """
-- /Source

-- Source: base/initdefs.jl:424-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     active_manifest()
--     active_manifest(project_file::AbstractString)
-- 
-- Return the path of the active manifest file, or the manifest file that would be used for a given `project_file`.
-- 
-- In a stacked environment (where multiple environments exist in the load path), this returns the manifest
-- file for the primary (active) environment only, not the manifests from other environments in the stack.
-- See the manual section on [Environment stacks](@ref) for more details on how stacked environments work.
-- 
-- See [`Project environments`](@ref project-environments) for details on the difference between a project and a manifest, and the naming
-- options and their priority in package loading.
-- 
-- See also [`Base.active_project`](@ref), [`Base.set_active_project`](@ref).
-- 
-- !!! compat "Julia 1.13"
--     This function requires at least Julia 1.13.
-- """
-- /Source

-- Source: base/initdefs.jl:449-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     load_path()
-- 
-- Return the fully expanded value of [`LOAD_PATH`](@ref) that is searched for projects and
-- packages.
-- 
-- !!! note
--     `load_path` may return a reference to a cached value so it is not safe to modify the
--     returned vector.
-- """
-- /Source

-- Source: base/initdefs.jl:470-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## atexit: register exit hooks ##
-- 
-- const atexit_hooks = Callable[]
-- const _atexit_hooks_lock = ReentrantLock()
-- global _atexit_hooks_finished::Bool = false
-- 
-- """
--     atexit(f)
-- 
-- Register a zero- or one-argument function `f()` to be called at process exit.
-- `atexit()` hooks are called in last in first out (LIFO) order and run before
-- object finalizers.
-- 
-- If `f` has a method defined for one integer argument, it will be called as
-- `f(n::Int32)`, where `n` is the current exit code, otherwise it will be called
-- as `f()`.
-- 
-- !!! compat "Julia 1.9"
--     The one-argument form requires Julia 1.9
-- 
-- Exit hooks are allowed to call `exit(n)`, in which case Julia will exit with
-- exit code `n` (instead of the original exit code). If more than one exit hook
-- calls `exit(n)`, then Julia will exit with the exit code corresponding to the
-- last called exit hook that calls `exit(n)`. (Because exit hooks are called in
-- LIFO order, "last called" is equivalent to "first registered".)
-- 
-- Note: Once all exit hooks have been called, no more exit hooks can be registered,
-- and any call to `atexit(f)` after all hooks have completed will throw an exception.
-- This situation may occur if you are registering exit hooks from background Tasks that
-- may still be executing concurrently during shutdown.
-- """
-- /Source

-- Source: base/initdefs.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:534-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:568-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## postoutput: register post output hooks ##
-- ## like atexit but runs after any requested output.
-- ## any hooks saved in the sysimage are cleared in Base._start
-- const postoutput_hooks = Callable[]
-- 
-- /Source

-- Source: base/initdefs.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/initdefs.jl:588-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## hook for disabling threaded libraries ##
-- 
-- library_threading_enabled::Bool = true
-- 
-- # Base.OncePerProcess ensures that any registered hooks do not outlive the session.
-- # (even if they are registered during the sysimage build process by top-level code)
-- const disable_library_threading_hooks = OncePerProcess(Vector{Any})
-- 
-- /Source

-- Source: base/initdefs.jl:604-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


end JuliaLean.base.initdefs

section
namespace JuliaLean.RuntimeCov.InitDefs

open JuliaLean.RuntimeCov

abbrev Str := List Char

/-- `eachsplit(str, sep)` (keeping empty pieces). -/
def splitOn (c : Char) : Str → List Str
  | [] => [[]]
  | x :: xs =>
    if x = c then [] :: splitOn c xs
    else match splitOn c xs with
      | [] => [[x]]
      | s :: ss => (x :: s) :: ss

/-- `replace(s, '#' => r, count=1)`. -/
def replaceFirst (c : Char) (r : Str) : Str → Str
  | [] => []
  | x :: xs => if x = c then r ++ xs else x :: replaceFirst c r xs

/-! ## exit, foreground task, interactivity -/

/-- `exit(n)`, base/initdefs.jl:28: converts `n` to `Int32` (an `InexactError`
outside its range) and never returns; `.ok n` is the process exit code. -/
def exit (n : Int) : Rt Int :=
  if (JuliaLean.IntTy.i32).min ≤ n ∧ n ≤ (JuliaLean.IntTy.i32).max then .ok n else .error .inexactError
/-- `exit()`, base/initdefs.jl:29. -/
def exit0 : Rt Int := exit 0

/-- `foreground_task()`, base/initdefs.jl:42: the value stored in the lockable ref. -/
def foregroundTask {τ : Type} (stored : Option τ) : Option τ := stored

/-- `@as_foreground_task expr`, base/initdefs.jl:52-66: the foreground task
while `expr` runs and after it finishes (normally or by throwing). -/
def asForegroundTask {τ : Type} (prev : Option τ) (current : τ) : Option τ × Option τ :=
  (some current, prev)

/-- `isinteractive()`, base/initdefs.jl:75. -/
def isinteractive (flag : Bool) : Bool := flag

/-! ## DEPOT_PATH -/

/-- `append_bundled_depot_path!(DEPOT_PATH)`, base/initdefs.jl:132-138, with the
two bundled depot paths as inputs. -/
def appendBundled (b1 b2 : Str) (dp : List Str) : List Str :=
  let dp := if b1 ∈ dp then dp else dp ++ [b1]
  if b2 ∈ dp then dp else dp ++ [b2]

/-- The loop of `init_depot_path`, base/initdefs.jl:150-161: `first` is
`i == 1`; the result is the depot list and `pushfirst_default`. -/
def depotLoop (eu : Str → Str) (b1 b2 : Str) : Bool → List Str → List Str → Bool → List Str × Bool
  | _, [], dp, pf => (dp, pf)
  | first, p :: ps, dp, pf =>
    if p.isEmpty then depotLoop eu b1 b2 false ps (appendBundled b1 b2 dp) pf
    else
      let q := eu p
      let dp := if q ∈ dp then dp else dp ++ [q]
      depotLoop eu b1 b2 false ps dp (if first then false else pf)

/-- `init_depot_path()`, base/initdefs.jl:140-174: `env` is
`ENV["JULIA_DEPOT_PATH"]`, `user` is `joinpath(homedir(), ".julia")`. -/
def initDepotPath (env : Option Str) (sep : Char) (eu : Str → Str) (user b1 b2 : Str) : List Str :=
  match env with
  | none => appendBundled b1 b2 [user]
  | some str =>
    if str.isEmpty then []
    else
      let (dp, pf) := depotLoop eu b1 b2 true (splitOn sep str) [] true
      if pf then user :: dp else dp

/-! ## LOAD_PATH -/

/-- `DEFAULT_LOAD_PATH`, base/initdefs.jl:193. -/
def defaultLoadPath : List Str := [['@'], ['@', 'v', '#', '.', '#'], ['@', 's', 't', 'd', 'l', 'i', 'b']]

/-- `current_project(dir)`, base/initdefs.jl:237-250: walks to parents until the
home directory or a fixed point of `dirname`; `fuel` bounds the walk (the
parent chain of a real path is finite). -/
def currentProjectAt (projectNames : List Str) (join : Str → Str → Str) (isfileCS : Str → Bool)
    (dirname : Str → Str) (home : Str) : Nat → Str → Option Str
  | 0, _ => none
  | fuel + 1, dir =>
    match projectNames.find? (fun p => isfileCS (join dir p)) with
    | some p => some (join dir p)
    | none =>
      if dir = home then none
      else
        let parent := dirname dir
        if parent = dir then none else currentProjectAt projectNames join isfileCS dirname home fuel parent

/-- `current_project()`, base/initdefs.jl:252-259: `pwd` is `none` when it
throws an `IOError`. -/
def currentProject (pwd : Option Str) (search : Str → Option Str) : Option Str :=
  match pwd with
  | none => none
  | some d => search d

/-- `parse_load_path(str)`, base/initdefs.jl:261-279. -/
def parseLoadPath (sep : Char) (curProj : Option Str) (eu : Str → Str) (str : Str) : List Str :=
  if str.isEmpty then [] else
  (splitOn sep str).foldl (fun envs env =>
    if env.isEmpty then
      defaultLoadPath.foldl (fun envs e => if e ∈ envs then envs else envs ++ [e]) envs
    else
      let env' := if env = ['@', '.'] then curProj else some env
      match env' with
      | none => envs
      | some e => let e := eu e; if e ∈ envs then envs else envs ++ [e]) []

/-- `init_load_path()`, base/initdefs.jl:281-295. -/
def initLoadPath (sep : Char) (curProj : Option Str) (eu : Str → Str) (env : Option Str) : List Str :=
  match env with
  | some s => parseLoadPath sep curProj eu s
  | none => defaultLoadPath.filterMap fun e => if e = ['@', '.'] then curProj else some e

/-- `cmd_suppresses_program(cmd)`, base/initdefs.jl:325. -/
def cmdSuppressesProgram (c : Char) : Bool := c = 'e' || c = 'E'

/-- The runtime facts used by `load_path_expand`. -/
structure ExpandEnv where
  activeProjectNoSearch : Option Str
  currentProject : Option Str
  tempdir : Str
  stdlib : Str
  programFile : Option Str
  dirname : Str → Str
  currentProjectAt : Str → Option Str
  major : Str
  minor : Str
  patch : Str
  depots : List Str
  envDir : Str → Str → Str
  isdir : Str → Bool
  absJoin : Str → Str → Str
  isfileCS : Str → Bool
  projectNames : List Str
  newNamedEnvPath : Str → Str → Str
  initNamedEnv : Str → Option Str
  abspath : Str → Str

/-- The named-environment search of `load_path_expand`, base/initdefs.jl:351-362. -/
def namedSearch (e : ExpandEnv) (name : Str) : Option Str :=
  let rec go : List Str → Option Str
    | [] =>
      match e.depots with
      | [] => none
      | d :: _ => e.initNamedEnv (e.newNamedEnvPath d name)
    | d :: ds =>
      let path := e.envDir d name
      if !e.isdir path then go ds
      else match e.projectNames.find? (fun p => e.isfileCS (e.absJoin path p)) with
        | some p => some (e.absJoin path p)
        | none => go ds
  go e.depots

def kAt : Str := ['@']
def kDot : Str := ['@', '.']
def kTemp : Str := ['@', 't', 'e', 'm', 'p']
def kStdlib : Str := ['@', 's', 't', 'd', 'l', 'i', 'b']
def kScript : Str := ['@', 's', 'c', 'r', 'i', 'p', 't']

/-- `load_path_expand(env::AbstractString)`, base/initdefs.jl:327-374. -/
def loadPathExpand (e : ExpandEnv) (env : Str) : Option Str :=
  if kAt.isPrefixOf env then
    if env = kAt then e.activeProjectNoSearch
    else if env = kDot then e.currentProject
    else if env = kTemp then some e.tempdir
    else if env = kStdlib then some e.stdlib
    else if kScript.isPrefixOf env then
      match e.programFile with
      | none => none
      | some pf =>
        let dir := e.dirname pf
        let dir := if env ≠ kScript then dir ++ env.drop kScript.length else dir
        e.currentProjectAt dir
    else
      let env := replaceFirst '#' e.major env
      let env := replaceFirst '#' e.minor env
      let env := replaceFirst '#' e.patch env
      namedSearch e (env.drop 1)
  else
    let path := e.abspath env
    if e.isdir path then
      match e.projectNames.find? (fun p => e.isfileCS (e.absJoin path p)) with
      | some p => some (e.absJoin path p)
      | none => some path
    else some path

/-- `load_path_expand(::Nothing)`, base/initdefs.jl:375. -/
def loadPathExpandNothing : Option Str := none

/-- `init_active_project()`, base/initdefs.jl:297-306: the value passed to
`set_active_project`. -/
def initActiveProject (opt env : Option Str) (expand : Str → Option Str) (absUser : Str → Str) : Option Str :=
  let project := match opt with | some p => some p | none => env
  match project with
  | none => none
  | some p => if p.isEmpty then none else if kAt.isPrefixOf p then expand p else some (absUser p)

/-- `init_named_env!(path)`, base/initdefs.jl:308-322: returns the path when
`mkpath`/`open`/`print` succeed, `nothing` (with a warning) otherwise. -/
def initNamedEnv (writeOk : Bool) (path : Str) : Option Str := if writeOk then some path else none

/-- `active_project(search_load_path)`, base/initdefs.jl:382-404. -/
def activeProject (activeRef : Option Str) (expand : Str → Option Str) (isfileCS : Str → Bool)
    (ispath : Str → Bool) (isProjectName : Str → Bool) (withProject : Str → Str)
    (loadPath : List Str) (search : Bool) : Option Str :=
  let fromRef : Option (Option Str) :=
    match activeRef with
    | none => none
    | some p =>
      if p = kAt then none
      else match expand p with
        | none => none
        | some q => some (some (if !isfileCS q && !isProjectName q then withProject q else q))
  match fromRef with
  | some r => r
  | none =>
    if !search then none
    else loadPath.foldr (fun p acc =>
      if p = kAt then acc
      else match expand p with
        | none => acc
        | some q => if isfileCS q then some q else if ispath q then acc
                    else if isProjectName q then some q else acc) none

/-- `set_active_project(projfile)`, base/initdefs.jl:414-423: stores the value
and calls each callback once in order, catching their errors. -/
def setActiveProject (projfile : Option Str) (callbacks : List Nat) : Option Str × List Nat :=
  (projfile, callbacks)

/-- `active_manifest(project_file; search_load_path)`, base/initdefs.jl:443-448. -/
def activeManifest (projectFile : Option Str) (active : Option Str) (manifestOf : Str → Option Str) :
    Option Str :=
  match (match projectFile with | some p => some p | none => active) with
  | none => none
  | some p => manifestOf p

/-- `load_path()`, base/initdefs.jl:460-469 (no cache). -/
def loadPath (expand : Str → Option Str) (lp : List Str) : List Str :=
  lp.foldl (fun paths env => match expand env with
    | some p => if p ∈ paths then paths else paths ++ [p]
    | none => paths) []

/-! ## Hooks -/

/-- The atexit state: registered hooks (front is run first) and the finished flag. -/
structure AtexitState where
  hooks : List Nat
  finished : Bool
  deriving DecidableEq, Repr

/-- `atexit(f)`, base/initdefs.jl:502-510. -/
def atexit (s : AtexitState) (f : Nat) : Rt AtexitState :=
  if s.finished then .error (.errorException "cannot register new atexit hook; already exiting.")
  else .ok { s with hooks := f :: s.hooks }

/-- `_run_atexit_hooks(exitcode)`, base/initdefs.jl:535-567: pops hooks from the
front until empty, calling each with the exit code when it has a one-argument
method; errors are printed and swallowed. Returns the calls made. -/
def runAtexitHooks (hasCintMethod : Nat → Bool) (exitcode : Int) (s : AtexitState) :
    List (Nat × Option Int) × AtexitState :=
  (s.hooks.map fun f => (f, if hasCintMethod f then some exitcode else none), ⟨[], true⟩)

/-- `_atexit(exitcode)`, base/initdefs.jl:512-533: clears the task's queue and
wait registration, then runs the hooks with cancellation disabled. -/
def atexitImpl (hasCintMethod : Nat → Bool) (exitcode : Int) (s : AtexitState) :
    List (Nat × Option Int) × AtexitState :=
  runAtexitHooks hasCintMethod exitcode s

/-- `postoutput(f)`, base/initdefs.jl:574. -/
def postoutput (hooks : List Nat) (f : Nat) : List Nat := f :: hooks
/-- `_postoutput()`, base/initdefs.jl:576-587: calls in list order and empties it. -/
def runPostoutput (hooks : List Nat) : List Nat × List Nat := (hooks, [])

/-- `at_disable_library_threading(f)`, base/initdefs.jl:597-603 and
`disable_library_threading()`, lines 605-617: the hook vector, the enabled flag,
and the hooks called (popped from the end). -/
def disableLibraryThreading (hooks : List Nat) : List Nat × List Nat := ([], hooks.reverse)
def atDisableLibraryThreading (enabled : Bool) (hooks : List Nat) (f : Nat) :
    List Nat × List Nat :=
  if enabled then (hooks ++ [f], []) else disableLibraryThreading (hooks ++ [f])

/-- The environment for the counterexample: one depot whose `environments/scripts`
holds a `Project.toml`, running without a script file. -/
def scriptsEnv : ExpandEnv where
  activeProjectNoSearch := none
  currentProject := none
  tempdir := ['t']
  stdlib := ['s']
  programFile := none
  dirname := id
  currentProjectAt := fun _ => none
  major := ['1']
  minor := ['1']
  patch := ['0']
  depots := [['d']]
  envDir := fun d n => d ++ ['/'] ++ n
  isdir := fun _ => true
  absJoin := fun p q => p ++ ['/'] ++ q
  isfileCS := fun _ => true
  projectNames := [['P']]
  newNamedEnvPath := fun d n => d ++ n
  initNamedEnv := some
  abspath := id
end JuliaLean.RuntimeCov.InitDefs
end

namespace JuliaLean.Loading

open JuliaLean

abbrev Str := Paths.Str

/-! ## LOAD_PATH expansion -/

structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr

def versionComponent (version : Version) : Nat → Str
  | 0 => Nat.toDigits 10 version.major
  | 1 => Nat.toDigits 10 version.minor
  | 2 => Nat.toDigits 10 version.patch
  | _ => ['#']

/-- The three sequential `replace(..., '#', count=1)` calls in
`base/initdefs.jl:346-348`. Further `#` characters remain unchanged. -/
def expandHashesGo (version : Version) : Str → Nat → Str
  | [], _ => []
  | c :: rest, seen =>
      if c == '#' then versionComponent version seen ++ expandHashesGo version rest (seen + 1)
      else c :: expandHashesGo version rest seen

def expandHashes (version : Version) (name : Str) : Str := expandHashesGo version name 0

def environmentsName : Str := "environments".toList
def projectName : Str := "Project.toml".toList

/-- Named-environment construction before filesystem probing;
`base/initdefs.jl:350-361`. -/
def namedEnvProjectPath (depot name : Str) : Str :=
  Paths.normpath ([environmentsName, name, projectName].foldl Paths.joinStep depot)

def namedEnvRoot (depot : Str) : Str := Paths.normpath (Paths.joinStep depot environmentsName)

def pathContained (root path : Str) : Bool :=
  path == root || (root ++ ['/']).isPrefixOf path

end JuliaLean.Loading
