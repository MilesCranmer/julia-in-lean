import JuliaLean.base.binaryplatforms
import JuliaLean.base.expr
import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.lock
import JuliaLean.base.env
import JuliaLean.base.libdl
import JuliaLean.base.path
import JuliaLean.base.binaryplatforms
import JuliaLean.base.regex
import JuliaLean.base.strings.basic
import JuliaLean.base.cmd


section

/-!
# `base/linking.jl`: `Base.Linking`

Model of `Base.Linking` at master `bbfa0ce4150`. Strings are `List Char`
(`Platforms.Str`, so `parse_dl_name_version` is `Platforms.parseDlNameVersion`). The
process environment (files, directories, loaded libraries, `ENV`, build constants) is
a `Sys` record; `joinpath`/`abspath`/`dirname` are its path functions. A `Cmd` is
its argument words and environment.
-/

namespace JuliaLean.DocsSyntaxCov.Linking

open JuliaLean JuliaLean.DocsSyntaxCov
open JuliaLean.Platforms (Str parseDlNameVersion)

/-- The operating system branches of `base/linking.jl`. -/
inductive OS where
  | windows | apple | other
  deriving DecidableEq, Repr

/-- `Sys.ARCH` as far as `ld()` distinguishes it. -/
inductive Arch where
  | x86_64 | aarch64 | other (name : Str)
  deriving DecidableEq

def Arch.name : Arch → Str
  | .x86_64 => s% "x86_64"
  | .aarch64 => s% "aarch64"
  | .other n => n

/-- The Julia process as `Base.Linking` sees it. -/
structure Sys where
  os : OS
  arch : Arch
  bindir : Str
  libdirRel : Str
  privateLibdirRel : Str
  privateLibexecdirRel : Str
  joinpath : Str → Str → Str
  abspath : Str → Str → Str
  dirname : Str → Str
  isfile : Str → Bool
  isdir : Str → Bool
  /-- `readdir(dir; sort=true)`. -/
  readdir : Str → List Str
  /-- `Libdl.dllist()`. -/
  dllist : List Str
  /-- `Sys.which(name)`. -/
  which : Str → Option Str
  /-- `ENV`. -/
  env : List (Str × Str)
  /-- `Base.get_bool_env("JULIA_VERBOSE_LINKING", false)`: `nothing` for an invalid value. -/
  verboseEnv : Option Bool
  isdebugbuild : Bool
  darwinFramework : Bool
  runtimeLibraryNames : List Str
  codegenLibraryNames : List Str
  compressDebugSections : Str
  macosProductVersion : Str
  macosPlatformVersion : Str

/-- A `Cmd`: argument words and, if set, the environment. -/
structure Cmd where
  exec : List Str
  env : Option (List (Str × Str)) := none

/-- `LIBPATH_env`, `LIBPATH_default` and `pathsep`, `base/linking.jl:11-23`. -/
def libpathEnv : OS → Str
  | .windows => s% "PATH"
  | .apple => s% "DYLD_FALLBACK_LIBRARY_PATH"
  | .other => s% "LD_LIBRARY_PATH"

def libpathDefault : OS → Str
  | .apple => s% "~/lib:/usr/local/lib:/lib:/usr/lib"
  | _ => []

def pathsep : OS → Char
  | .windows => ';'
  | _ => ':'

def lldExe (os : OS) : Str := if os = .windows then s% "lld.exe" else s% "lld"
def dsymutilExe (os : OS) : Str := if os = .windows then s% "dsymutil.exe" else s% "dsymutil"

def eget (env : List (Str × Str)) (k : Str) : Option Str := (env.find? (·.1 == k)).map (·.2)

def eset (env : List (Str × Str)) (k v : Str) : List (Str × Str) :=
  if env.any (·.1 == k) then env.map (fun p => if p.1 == k then (k, v) else p) else env ++ [(k, v)]

/-- `adjust_ENV!(env, PATH, LIBPATH, adjust_PATH, adjust_LIBPATH)`, `base/linking.jl:25-42`.
`expanduser` of the default is given as `expandedDefault`. -/
def adjustEnv (os : OS) (expandedDefault : Str) (env : List (Str × Str)) (PATH LIBPATH : Str)
    (adjustPATH adjustLIBPATH : Bool) : List (Str × Str) :=
  let env :=
    if adjustLIBPATH then
      let base := (eget env (libpathEnv os)).getD expandedDefault
      if !base.isEmpty then eset env (libpathEnv os) (LIBPATH ++ [pathsep os] ++ base)
      else eset env (libpathEnv os) LIBPATH
    else env
  if adjustPATH && (libpathEnv os != s% "PATH" || !adjustLIBPATH) then
    if !((eget env (s% "PATH")).getD []).isEmpty then
      eset env (s% "PATH") (PATH ++ [pathsep os] ++ (eget env (s% "PATH")).getD [])
    else eset env (s% "PATH") PATH
  else env

/-- The body of the `lld_path`/`dsymutil_path` `OncePerProcess`, `base/linking.jl:44-67`:
the first bundled executable that exists, else the one on `PATH`, else the bare name. -/
def toolPath (sys : Sys) (exe : Str) : Str :=
  let cands := [sys.joinpath (sys.joinpath sys.bindir sys.privateLibexecdirRel) exe,
    sys.joinpath (sys.joinpath (sys.joinpath sys.bindir (s% "..")) (s% "tools")) exe,
    sys.joinpath sys.bindir exe]
  match cands.find? sys.isfile with
  | some p => sys.abspath p []
  | none => (sys.which exe).getD exe

def lldPath (sys : Sys) : Str := toolPath sys (lldExe sys.os)
def dsymutilPath (sys : Sys) : Str := toolPath sys (dsymutilExe sys.os)

/-- `PATH() = dirname(lld_path())`, `base/linking.jl:69`. -/
def PATH (sys : Sys) : Str := sys.dirname (lldPath sys)

/-- `libdir()`, `private_libdir()`, and `shlibdir()` (`Sys.BINDIR` on Windows, line 162;
`libdir()` elsewhere, line 164), `base/linking.jl:159-165`. -/
def libdir (sys : Sys) : Str := sys.abspath sys.bindir sys.libdirRel
def privateLibdir (sys : Sys) : Str := sys.abspath sys.bindir sys.privateLibdirRel
def shlibdirWindows (sys : Sys) : Str := sys.bindir
def shlibdirOther (sys : Sys) : Str := libdir sys
def shlibdir (sys : Sys) : Str := if sys.os = .windows then shlibdirWindows sys else shlibdirOther sys

/-- `library_dirs` (`unique!(String[private_libdir(), shlibdir()])`) and `LIBPATH`, lines 73-79. -/
def libraryDirs (sys : Sys) : List Str :=
  if privateLibdir sys == shlibdir sys then [privateLibdir sys] else [privateLibdir sys, shlibdir sys]

def joinSep (sep : Char) : List Str → Str
  | [] => []
  | [x] => x
  | x :: xs => x ++ [sep] ++ joinSep sep xs

def LIBPATH (sys : Sys) : Str := joinSep (pathsep sys.os) (libraryDirs sys)

/-- `lld(; adjust_PATH, adjust_LIBPATH)`, lines 81-84. -/
def lld (sys : Sys) (expandedDefault : Str) (adjustPATH adjustLIBPATH : Bool := true) : Cmd :=
  ⟨[lldPath sys], some (adjustEnv sys.os expandedDefault sys.env (PATH sys) (LIBPATH sys) adjustPATH adjustLIBPATH)⟩

/-- `dsymutil(; adjust_PATH, adjust_LIBPATH)`, lines 86-89. -/
def dsymutil (sys : Sys) (expandedDefault : Str) (adjustPATH adjustLIBPATH : Bool := true) : Cmd :=
  ⟨[dsymutilPath sys], some (adjustEnv sys.os expandedDefault sys.env (PATH sys) (LIBPATH sys) adjustPATH adjustLIBPATH)⟩

/-- The flavor and default arguments of `ld(; strict_definitions)`, lines 91-125. -/
def ldArgs (sys : Sys) (strict : Bool) : Str × List Str :=
  match sys.os with
  | .windows =>
    let m := if sys.arch = .x86_64 then s% "i386pep" else s% "i386pe"
    let entry := if sys.arch = .x86_64 then s% "DllMainCRTStartup" else s% "_DllMainCRTStartup"
    let d := [s% "-m", m, s% "-Bdynamic", s% "-e", entry, s% "--enable-auto-image-base", s% "--disable-auto-import",
      s% "--disable-runtime-pseudo-reloc"]
    (s% "gnu", if !strict then d ++ [s% "--allow-multiple-definition"] else d)
  | .apple =>
    let arch := if sys.arch = .aarch64 then s% "arm64" else sys.arch.name
    let d := [s% "-arch", arch, s% "-platform_version", s% "macos", sys.macosProductVersion, sys.macosPlatformVersion]
    let d := if !strict then d ++ [s% "-undefined", s% "dynamic_lookup"] else d
    (s% "darwin", d ++ [s% "-syslibroot", privateLibdir sys])
  | .other =>
    let d := [s% "--build-id", s% "--eh-frame-hdr", s% "--hash-style=gnu", s% "--as-needed", s% "-z", s% "relro",
      s% "-z", s% "defs", s% "--discard-locals"]
    (s% "gnu", if !sys.compressDebugSections.isEmpty then
      d ++ [s% "--compress-debug-sections=" ++ sys.compressDebugSections] else d)

/-- `ld(; strict_definitions)`: `` `$(lld()) -flavor $flavor $default_args` ``; interpolating a
`Cmd` first keeps its environment. -/
def ld (sys : Sys) (expandedDefault : Str) (strict : Bool := false) : Cmd :=
  let c := lld sys expandedDefault
  let (flavor, d) := ldArgs sys strict
  ⟨c.exec ++ [s% "-flavor", flavor] ++ d, c.env⟩

/-- `cc_arg(a) = is_cc ? "-Wl,$a" : a`, line 145. -/
def ccArg (isCc : Bool) (a : Str) : Str := if isCc then s% "-Wl," ++ a else a

/-- `whole_archive(paths::Vector{String}; is_cc)`, lines 144-151. -/
def wholeArchive (os : OS) (paths : List Str) (isCc : Bool := false) : Cmd :=
  if os = .apple then ⟨paths.flatMap (fun p => [ccArg isCc (s% "-force_load"), p]), none⟩
  else ⟨[ccArg isCc (s% "--whole-archive")] ++ paths ++ [ccArg isCc (s% "--no-whole-archive")], none⟩

/-- `whole_archive(paths::String; is_cc) = whole_archive([paths]; is_cc)`, line 143. -/
def wholeArchive1 (os : OS) (path : Str) (isCc : Bool := false) : Cmd := wholeArchive os [path] isCc

/-- `verbose_linking()`, line 167. -/
def verboseLinking (sys : Sys) : Bool := sys.verboseEnv.getD false

/-- `_find_static(lib)`, lines 169-175. -/
def findStatic (sys : Sys) (lib : Str) : Str :=
  if sys.isfile (sys.joinpath (privateLibdir sys) lib) then sys.joinpath (privateLibdir sys) lib
  else sys.joinpath (libdir sys) lib

/-- `_find_loaded(re)`, lines 177-182: `re` is `occursin(re, ·)`. -/
def findLoaded (sys : Sys) (re : Str → Bool) : DJ Str :=
  match sys.dllist.find? re with
  | some p => pure p
  | none => .error (.errorException "no loaded shared object matching")

/-- `link_image_cmd(path, out; is_sysimage)`, lines 184-228. `libcRe`/`ldRe` are the two
regular expressions of line 216-217 (as `occursin` predicates). -/
def linkImageCmd (sys : Sys) (expandedDefault : Str) (libcRe ldRe : Str → Bool) (path out : Str)
    (isSysimage : Bool := false) : DJ Cmd := do
  let PRIVATE_LIBDIR := s% "-L" ++ privateLibdir sys
  let LIBDIR := s% "-L" ++ libdir sys
  let SHLIBDIR := s% "-L" ++ shlibdir sys
  let libs0 := if sys.isdebugbuild then [s% "-ljulia-debug", s% "-ljulia-internal-debug"]
    else [s% "-ljulia", s% "-ljulia-internal"]
  let (libs, crtbegin, crtend) ← match sys.os with
    | .windows =>
      let l := libs0 ++ [s% "-lopenlibm"] ++
        [s% "-lmingw32", s% "-lgcc_s", s% "-lgcc", s% "-lmoldname", s% "-lmingwex", s% "-lmsvcrt-os", s% "-lmingw32",
          s% "-lmingwex", s% "-lmsvcrt-os", s% "-lkernel32"] ++
        [s% "-lpthread", s% "-ladvapi32", s% "-lshell32", s% "-luser32"]
      let l := if sys.isdebugbuild then l ++ [s% "-lssp"] else l
      let l := l ++ [s% "-lmingwex", s% "-lmsvcrt-os", s% "-lmingw32", s% "-lmingwex", s% "-lmsvcrt-os"]
      pure (l, [findStatic sys (s% "dllcrt2.o"), findStatic sys (s% "crtbegin.o")], [findStatic sys (s% "crtend.o")])
    | .apple =>
      pure (libs0 ++ [findStatic sys (s% "libclang_rt.osx.a"), findStatic sys (s% "libSystem.tbd")], [], [])
    | .other => do
      let libc ← findLoaded sys libcRe
      let ldLinux ← findLoaded sys ldRe
      let libcNonshared := findStatic sys (s% "libc_nonshared.a")
      let l := libs0 ++ [s% "-lgcc", s% "--as-needed", s% "-lgcc_s", s% "-latomic", s% "-lopenlibm", s% "--no-as-needed", libc]
      let l := if sys.isfile libcNonshared then l ++ [libcNonshared] else l
      let l := l ++ [s% "--as-needed", ldLinux, s% "--no-as-needed"]
      pure (l, [findStatic sys (s% "crti.o"), findStatic sys (s% "crtbeginS.o")],
        [findStatic sys (s% "crtendS.o"), findStatic sys (s% "crtn.o")])
  let V := if verboseLinking sys then s% "--verbose" else []
  let SHARED := if sys.os = .apple then s% "-dylib" else s% "-shared"
  let c := ld sys expandedDefault isSysimage
  pure ⟨c.exec ++ [V, SHARED, s% "-o", out] ++ crtbegin ++ (wholeArchive1 sys.os path).exec ++
    [PRIVATE_LIBDIR, LIBDIR, SHLIBDIR] ++ libs ++ crtend, c.env⟩

/-- `link_image(path, out, internal_stderr, internal_stdout; is_sysimage)`, lines 230-233: the
command it runs (with `stdin` from `devnull`). -/
def linkImage (sys : Sys) (expandedDefault : Str) (libcRe ldRe : Str → Bool) (path out : Str)
    (isSysimage : Bool := false) : DJ Cmd :=
  linkImageCmd sys expandedDefault libcRe ldRe path out isSysimage

/-! ## Runtime library dependencies, lines 236-363 -/

def COMPONENTS : List String := ["codegen"]

def dlext : OS → Str
  | .windows => s% "dll"
  | .apple => s% "dylib"
  | .other => s% "so"

/-- `_this_os_name()` for `parse_dl_name_version`'s default. -/
def thisOsName : OS → Str
  | .windows => s% "windows"
  | .apple => s% "macos"
  | .other => s% "other"

def isInfix (needle hay : Str) : Bool :=
  (List.range (hay.length + 1)).any fun i => (hay.drop i).take needle.length == needle

/-- `is_library_file(name, file)`, lines 251-267. `parse_dl_name_version` throws
`ArgumentError` for a name that is no shared library; other errors propagate. -/
def isLibraryFile (os : OS) (name file : Str) : Jl Bool :=
  if name.getLast? = some '*' then
    let pre := name.dropLast
    pure (file.take pre.length == pre && isInfix ('.' :: dlext os) file)
  else
    match parseDlNameVersion file (thisOsName os) with
    | .error (.argumentError _) => pure false
    | .error e => .error e
    | .ok (parsed, _) =>
      if parsed == name then pure true
      else if os = .apple then pure false
      else do
        let (p2, _) ← parseDlNameVersion (parsed ++ s% ".dylib") (s% "macos")
        pure (p2 == name)

/-- `library_listings()`, lines 270-271. -/
def libraryListings (sys : Sys) : List (Str × List Str) :=
  (libraryDirs sys).filter sys.isdir |>.map fun d => (d, sys.readdir d)

/-- The files of `name` in one directory's listing. -/
def matchingFiles (sys : Sys) (dir : Str) (name : Str) : List Str → Jl (List Str)
  | [] => pure []
  | f :: fs => do
    let ok ← isLibraryFile sys.os name f
    let rest ← matchingFiles sys dir name fs
    pure (if ok then sys.joinpath dir f :: rest else rest)

/-- `library_files!(paths, name, listings)`, lines 274-286: the files of `name` in the first
directory that has any, appended to `paths`, and whether any were found. -/
def libraryFilesBang (sys : Sys) (paths : List Str) (name : Str) : List (Str × List Str) → Jl (List Str × Bool)
  | [] => pure (paths, false)
  | (dir, files) :: rest => do
    let found ← matchingFiles sys dir name files
    if found.isEmpty then libraryFilesBang sys paths name rest else pure (paths ++ found, true)

/-- `unique!` on a vector of strings: first occurrences in order. -/
def uniq : List Str → List Str
  | [] => []
  | x :: xs => x :: (uniq xs).filter (· != x)

/-- `library_files(names)`, lines 296-303. -/
def libraryFiles (sys : Sys) (names : List Str) : Jl (List Str) := do
  let listings := libraryListings sys
  let paths ← names.foldlM (fun paths n => do pure (← libraryFilesBang sys paths n listings).1) []
  pure (uniq paths)

/-- `library_files(name::AbstractString) = library_files((name,))`, line 304. -/
def libraryFiles1 (sys : Sys) (name : Str) : Jl (List Str) := libraryFiles sys [name]

/-- The loop `for component in optional_components ... end` of lines 307-311. -/
def checkComponents : List String → DJ Unit
  | [] => pure ()
  | c :: cs => if !COMPONENTS.contains c then .error (.argumentError "unknown optional component")
    else checkComponents cs

/-- `runtime_library_names(optional_components)`, lines 306-326. -/
def runtimeLibraryNames (sys : Sys) (optional : List String) : DJ (List Str × List Str) := do
  checkComponents optional
  let debug := if sys.isdebugbuild then s% "-debug" else []
  let required := (if sys.darwinFramework then [] else [s% "libjulia" ++ debug]) ++ [s% "libjulia-internal" ++ debug]
  if optional.contains "codegen" then
    pure (required ++ [s% "libjulia-codegen" ++ debug], sys.runtimeLibraryNames ++ sys.codegenLibraryNames)
  else pure (required, sys.runtimeLibraryNames)

/-- A `JlError` as a `DErr`: the exception types `parse_dl_name_version` throws. -/
def liftErr : JlError → DErr
  | .argumentError m => .argumentError m
  | .overflowError m => .overflowError m
  | .inexactError _ => .inexactError
  | .boundsError => .boundsError
  | .eofError => .eofError
  | _ => .errorException "error"

/-- `resolve_libraries(required, optional, listings)`, lines 347-363. -/
def resolveLibraries (sys : Sys) (required optional : List Str) (listings : List (Str × List Str)) :
    DJ (List Str) := do
  let lift {α : Type} (r : Jl α) : DJ α := match r with
    | .ok a => pure a
    | .error e => .error (liftErr e)
  let (paths, absent) ← required.foldlM (fun (acc : List Str × List Str) n => do
    let (p, found) ← lift (libraryFilesBang sys acc.1 n listings)
    pure (p, if found then acc.2 else acc.2 ++ [n])) ([], [])
  if !absent.isEmpty then .error (.errorException "this Julia installation does not contain the shared library")
  let paths ← optional.foldlM (fun paths n => do pure (← lift (libraryFilesBang sys paths n listings)).1) paths
  pure (uniq paths)

/-- `runtime_libraries(; optional_components = DEFAULT_COMPONENTS)`, lines 342-345. -/
def runtimeLibraries (sys : Sys) (optional : List String := COMPONENTS) : DJ (List Str) := do
  let (required, opt) ← runtimeLibraryNames sys optional
  resolveLibraries sys required opt (libraryListings sys)

end JuliaLean.DocsSyntaxCov.Linking

end


/-!
# Model of `base/linking.jl`

Typed source-mirrored methods for linker setup, dynamic-library lookup, and runtime library
bundling at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Host values, environment and file
operations, command execution, and Julia dispatch are explicit interfaces. Path, command, dynamic
library, binary-platform, and regex calls reuse their Base models.
-/

namespace JuliaLean.base.linking

open JuliaLean

abbrev M := JuliaLean.base.io.M
abbrev LinkError := JuliaLean.base.io.Error
abbrev Path := JuliaLean.base.path.Path
abbrev Cmd (Vec Cpu : Type) := JuliaLean.base.cmd.Cmd Vec String Cpu
abbrev U32 := JInt .u32

inductive HostOS where
  | windows | apple | linux | bsd | other
  deriving DecidableEq, Repr

structure Host (Vec : Type) where
  os : HostOS
  architecture : String
  binaryPlatform : String
  bindir : String
  baseLibdir : String
  privateLibdir : String
  privateLibexecdir : String
  macOSProductVersion : String
  macOSPlatformVersion : String
  compressDebugSections : String
  darwinFramework : Bool
  debugBuild : Bool
  runtimeLibraryNames : Vec
  codegenLibraryNames : Vec

structure IteratorOps (World Collection Element State : Type) where
  iterate : Collection → Option State → M World (Option (Element × State))

structure OnceSystem (World Vec : Type) where
  StringOnce : Type
  VectorOnce : Type
  ReentrantLock : Type
  Task : Type
  Queue : Type
  Lock : Type
  Entry : Type
  Slot : Type
  Source : Type
  Token : Type
  LockState : Type
  TaskValue : Type
  runtime : JuliaLean.base.lock.Runtime LinkError World ReentrantLock Task Queue Lock Entry Slot
    Source Token LockState TaskValue
  stringOperations : JuliaLean.base.lock.ProcessOnceOps LinkError World StringOnce
    (Unit → M World String) String ReentrantLock
  vectorOperations : JuliaLean.base.lock.ProcessOnceOps LinkError World VectorOnce
    (Unit → M World Vec) Vec ReentrantLock

structure PathCaches {World Vec : Type} (system : OnceSystem World Vec) where
  lldPath : system.StringOnce
  dsymutilPath : system.StringOnce

structure LibraryCaches {World Vec : Type} (system : OnceSystem World Vec) where
  libraryDirs : system.VectorOnce
  libpath : system.StringOnce

def newStringOnce {World Vec : Type} (system : OnceSystem World Vec)
    (initializer : Unit → M World String) : M World system.StringOnce :=
  JuliaLean.base.lock.newOncePerProcess system.runtime system.stringOperations initializer

def forceStringOnce {World Vec : Type} (system : OnceSystem World Vec)
    (once : system.StringOnce) : M World String :=
  JuliaLean.base.lock.oncePerProcess system.runtime system.stringOperations once

def newVectorOnce {World Vec : Type} (system : OnceSystem World Vec)
    (initializer : Unit → M World Vec) : M World system.VectorOnce :=
  JuliaLean.base.lock.newOncePerProcess system.runtime system.vectorOperations initializer

def forceVectorOnce {World Vec : Type} (system : OnceSystem World Vec)
    (once : system.VectorOnce) : M World Vec :=
  JuliaLean.base.lock.oncePerProcess system.runtime system.vectorOperations once

variable
  {World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit
    StringCodeUnitType VectorState : Type}

structure Ops where
  host : Host Vec
  vectors : JuliaLean.base.cmd.Vectors World Vec String
  globalEnvironment : Env
  copyEnvironment : Env → M World Env
  getEnvironment : Env → String → String → M World String
  setEnvironment : Env → String → String → M World Unit
  expandUser : String → M World String
  byteEnvironment : Env → M World (Option Vec)
  sameStringReference : String → String → Bool
  cstr : String → M World String
  onceSystem : OnceSystem World Vec
  which : String → M World (Option String)
  pathKernel : String
  pathStringOps : JuliaLean.base.path.StringOps
  stringToPath : String → Path
  pathToString : Path → String
  pathFiles : JuliaLean.base.path.FileBindings World
  pathErrorToIO : JuliaLean.base.path.PathError → LinkError
  isFile : String → M World Bool
  isDir : String → M World Bool
  readdirSorted : String → M World (List String)
  vectorIterator : IteratorOps World Vec String VectorState
  copyVector : Vec → M World Vec
  uniqueVector : Vec → M World Vec
  boolEnvOps : JuliaLean.base.env.BoolEnvOps World
  dyldImageCount : M World JuliaLean.base.libdl.Cint
  dyldGetImageName : JuliaLean.base.libdl.Flags → M World Handle
  unsafeString : Handle → M World String
  jlDllist : Vec → M World JuliaLean.base.libdl.Cint
  regexOps : JuliaLean.base.regex.RegexOps Regex String Data Ptr LinkError
  stringOps : JuliaLean.base.strings.basic.StringOps String StringSlice StringChar StringCodeUnit
    StringCodeUnitType LinkError
  regexLiteral : String → Regex
  showRegex : Regex → String
  rangeErrorToIO : JuliaLean.base.range.Exc → LinkError
  stderr : IO
  stdout : IO
  devNull : M World IO
  runProcess : Cmd Vec Cpu → IO → IO → IO → M World Process

abbrev ModelOps
    (World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit
      StringCodeUnitType VectorState : Type) :=
  Ops (World := World) (Env := Env) (Vec := Vec) (Cpu := Cpu)
    (IO := IO) (Process := Process) (Handle := Handle) (Regex := Regex) (Data := Data)
    (Ptr := Ptr) (StringSlice := StringSlice) (StringChar := StringChar)
    (StringCodeUnit := StringCodeUnit) (StringCodeUnitType := StringCodeUnitType)
    (VectorState := VectorState)

structure StringCollectionOps (World Collection Value State : Type) where
  collection : Collection
  iterator : IteratorOps World Collection Value State
  inKnown : Value → Bool
  isCodegen : Value → Bool
  repr : Value → M World String

structure LibraryStringOps (World Name File : Type) where
  endsWithStar : Name → Bool
  dropLastCharacter : Name → Name
  startsWithFile : File → Name → Bool
  occursInFile : String → File → Bool
  fileString : File → M World String
  equalParsedName : Name → JuliaLean.Platforms.Str → Bool
  nameString : Name → M World String


inductive RuntimeComponent where
  | codegen
  deriving DecidableEq, Repr

structure Tuple1 (A : Type) where
  value : A
  deriving DecidableEq, Repr

def tuple1Iterator {World A : Type} : IteratorOps World (Tuple1 A) A Bool where
  iterate tuple state := match state with
    | none => pure (some (tuple.value, true))
    | some _ => pure none

/-- List-backed iteration for ordered snapshots used by the model. -/
def listIterator {World A : Type} : IteratorOps World (List A) A (List A) where
  iterate source state := do
    let remaining := state.getD source
    match remaining with
    | [] => pure none
    | item :: rest => pure (some (item, rest))

/-- The source `Cmd` constructor with an already-typed argument vector. -/
def identityFieldCast {World A : Type} : JuliaLean.base.cmd.FieldCast World A A A where
  existing := some
  convert value := pure value
  assertResult value := .ok value

def commandFromVector {World Vec Cpu : Type} (arguments : Vec) : M World (Cmd Vec Cpu) :=
  JuliaLean.base.cmd.cmdExec "" identityFieldCast arguments

def copyCommandExec (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (base : Cmd Vec Cpu) (arguments : Vec) :
    M World (Cmd Vec Cpu) := do
  let fresh ← commandFromVector arguments
  JuliaLean.base.cmd.cmdCopy identityFieldCast identityFieldCast identityFieldCast
    identityFieldCast identityFieldCast identityFieldCast ops.sameStringReference ops.cstr
    fresh base.ignorestatus base.flags base.env base.dir base.cpus base.uid base.gid

def appendStrings (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (vector : Vec) (values : List String) : M World Unit := do
  for value in values do
    ops.vectors.push vector value

def liftPathResult (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) {A : Type} (result : Except JuliaLean.base.path.PathError A) :
    M World A :=
  match result with
  | .ok value => pure value
  | .error error => throw (ops.pathErrorToIO error)

def liftPathAction (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    {A : Type} (action : JuliaLean.base.path.M World A) : M World A :=
  fun world => do
    let (result, world) ← action world
    match result with
    | .ok value => some (.ok (value, world))
    | .error error => some (.error (ops.pathErrorToIO error, world))

def joinPath (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (paths : List String) : M World String := do
  let os ← liftPathResult ops (JuliaLean.base.path.platformForKernel ops.pathKernel)
  let path ← liftPathResult ops
    (JuliaLean.base.path.joinpathStrings os ops.pathStringOps
      (paths.map ops.stringToPath))
  pure (ops.pathToString path)

def joinStrings (separator : String) : List String → String
  | [] => ""
  | [value] => value
  | value :: rest => value ++ separator ++ joinStrings separator rest

def vectorToList (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (vector : Vec) : M World (List String) := do
  let values ← JuliaLean.base.io.whileLoop (fun (state, reverseValues) => do
    match ← ops.vectorIterator.iterate vector state with
    | none => pure (.inl reverseValues)
    | some (value, next) => pure (.inr (some next, value :: reverseValues))) (none, [])
  pure values.reverse

def absolutePath (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (first : String) (rest : List String) : M World String := do
  let os ← liftPathResult ops (JuliaLean.base.path.platformForKernel ops.pathKernel)
  let path ← liftPathAction ops
    (JuliaLean.base.path.abspathMany ops.pathFiles.ops os ops.pathStringOps
      (ops.stringToPath first) (rest.map ops.stringToPath))
  pure (ops.pathToString path)

-- UNTRANSLATED
-- Source: base/linking.jl:1-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- module Linking
-- 
-- import Base: isdebugbuild
-- import Base.Libc: Libdl
-- /Source
-- Reason: Julia module imports and export registration are supplied by the Base load graph.

/--
Julia source: base/linking.jl:7-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# from LLD_jll
const lld_exe = Sys.iswindows() ? "lld.exe" : "lld"
const dsymutil_exe = Sys.iswindows() ? "dsymutil.exe" : "dsymutil"

if Sys.iswindows()
    const LIBPATH_env = "PATH"
    const LIBPATH_default = ""
    const pathsep = ';'
elseif Sys.isapple()
    const LIBPATH_env = "DYLD_FALLBACK_LIBRARY_PATH"
    const LIBPATH_default = "~/lib:/usr/local/lib:/lib:/usr/lib"
    const pathsep = ':'
else
    const LIBPATH_env = "LD_LIBRARY_PATH"
    const LIBPATH_default = ""
    const pathsep = ':'
end
```
-/

structure EnvironmentConstants where
  lldExe : String
  dsymutilExe : String
  libpathEnv : String
  libpathDefault : String
  pathsep : Char
  deriving Repr, DecidableEq

def environmentConstants {Vec : Type} (host : Host Vec) : EnvironmentConstants :=
  match host.os with
  | .windows => ⟨"lld.exe", "dsymutil.exe", "PATH", "", ';'⟩
  | .apple => ⟨"lld", "dsymutil", "DYLD_FALLBACK_LIBRARY_PATH",
      "~/lib:/usr/local/lib:/lib:/usr/lib", ':'⟩
  | _ => ⟨"lld", "dsymutil", "LD_LIBRARY_PATH", "", ':'⟩

/--
Julia source: base/linking.jl:25-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function adjust_ENV!(env::Dict, PATH::String, LIBPATH::String, adjust_PATH::Bool, adjust_LIBPATH::Bool)
    if adjust_LIBPATH
        LIBPATH_base = get(env, LIBPATH_env, expanduser(LIBPATH_default))
        if !isempty(LIBPATH_base)
            env[LIBPATH_env] = string(LIBPATH, pathsep, LIBPATH_base)
        else
            env[LIBPATH_env] = LIBPATH
        end
    end
    if adjust_PATH && (LIBPATH_env != "PATH" || !adjust_LIBPATH)
        if !isempty(get(env, "PATH", ""))
            env["PATH"] = string(PATH, pathsep, env["PATH"])
        else
            env["PATH"] = PATH
        end
    end
    return env
end
```
-/

def adjustEnv (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (env : Env) (path libpath : String)
    (adjustPath adjustLibpath : Bool) : M World Env := do
  let constants := environmentConstants ops.host
  if adjustLibpath then
    let default ← ops.expandUser constants.libpathDefault
    let existing ← ops.getEnvironment env constants.libpathEnv default
    let value := if existing.isEmpty then libpath
      else libpath ++ String.singleton constants.pathsep ++ existing
    ops.setEnvironment env constants.libpathEnv value
  if adjustPath && (constants.libpathEnv != "PATH" || !adjustLibpath) then
    let existing ← ops.getEnvironment env "PATH" ""
    let value := if existing.isEmpty then path
      else path ++ String.singleton constants.pathsep ++ existing
    ops.setEnvironment env "PATH" value
  pure env

/--
Julia source: base/linking.jl:44-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const lld_path = OncePerProcess{String}() do
    # Prefer our own bundled lld, but if we don't have one, pick it up off of the PATH
    # If this is an in-tree build, `lld` will live in `tools`.  Otherwise, it'll be in `private_libexecdir`
    for bundled_lld_path in (joinpath(Sys.BINDIR, Base.PRIVATE_LIBEXECDIR, lld_exe),
                             joinpath(Sys.BINDIR, "..", "tools", lld_exe),
                             joinpath(Sys.BINDIR, lld_exe))
        if isfile(bundled_lld_path)
            return abspath(bundled_lld_path)
        end
    end
    return something(Sys.which(lld_exe), lld_exe)
end

const dsymutil_path = OncePerProcess{String}() do
    # Same as with lld but for dsymutil
    for bundled_dsymutil_path in (joinpath(Sys.BINDIR, Base.PRIVATE_LIBEXECDIR, dsymutil_exe),
                             joinpath(Sys.BINDIR, "..", "tools", dsymutil_exe),
                             joinpath(Sys.BINDIR, dsymutil_exe))
        if isfile(bundled_dsymutil_path)
            return abspath(bundled_dsymutil_path)
        end
    end
    return something(Sys.which(dsymutil_exe), dsymutil_exe)
end
```
-/
def newPathCaches (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) :
    M World (PathCaches ops.onceSystem) := do
  let constants := environmentConstants ops.host
  let locateTool : String → M World String := fun executable => do
    let candidates := [[ops.host.bindir, ops.host.privateLibexecdir, executable],
      [ops.host.bindir, "..", "tools", executable], [ops.host.bindir, executable]]
    let found ← JuliaLean.base.io.whileLoop (fun remaining => do
      match remaining with
      | [] => pure (.inl none)
      | parts :: rest => do
          let path ← joinPath ops parts
          if ← ops.isFile path then
            pure (.inl (some (← absolutePath ops path [])))
          else pure (.inr rest)) candidates
    match found with
    | some path => pure path
    | none => pure ((← ops.which executable).getD executable)
  let lldPath ← newStringOnce ops.onceSystem (fun _ => locateTool constants.lldExe)
  let dsymutilPath ← newStringOnce ops.onceSystem (fun _ => locateTool constants.dsymutilExe)
  pure ⟨lldPath, dsymutilPath⟩


/--
Julia source: base/linking.jl:69-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PATH() = dirname(lld_path())
```
-/

def pathFunction (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (caches : PathCaches ops.onceSystem) : M World String := do
  let executable ← forceStringOnce ops.onceSystem caches.lldPath
  let os ← liftPathResult ops (JuliaLean.base.path.platformForKernel ops.pathKernel)
  pure (ops.pathToString (JuliaLean.base.path.dirname os ops.pathStringOps
    (ops.stringToPath executable)))

/--
Julia source: base/linking.jl:71-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This installation's shared library directories, in search order. On Windows the DLLs are
# in `Sys.BINDIR`. The two can be the same directory.
const library_dirs = OncePerProcess{Vector{String}}() do
    unique!(String[private_libdir(), shlibdir()])
end

const LIBPATH = OncePerProcess{String}() do
    join(library_dirs(), pathsep)
end
```
-/
def newLibraryCaches (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (privateLibdir shlibdir : Unit → M World String) :
    M World (LibraryCaches ops.onceSystem) := do
  let dirs ← newVectorOnce ops.onceSystem (fun _ => do
    let privateDir ← privateLibdir ()
    let sharedDir ← shlibdir ()
    let result ← ops.vectors.empty
    ops.vectors.push result privateDir
    ops.vectors.push result sharedDir
    ops.uniqueVector result)
  let path ← newStringOnce ops.onceSystem (fun _ => do
    let directories ← forceVectorOnce ops.onceSystem dirs
    let values ← vectorToList ops directories
    pure (joinStrings (String.singleton (environmentConstants ops.host).pathsep) values))
  pure ⟨dirs, path⟩


/--
Julia source: base/linking.jl:81-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lld(; adjust_PATH::Bool = true, adjust_LIBPATH::Bool = true)
    env = adjust_ENV!(copy(ENV), PATH(), LIBPATH(), adjust_PATH, adjust_LIBPATH)
    return Cmd(Cmd([lld_path()]); env)
end
```
-/

def lld (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (pathCaches : PathCaches ops.onceSystem) (libraryCaches : LibraryCaches ops.onceSystem)
    (adjustPath adjustLibpath : Bool := true) : M World (Cmd Vec Cpu) := do
  let env ← ops.copyEnvironment ops.globalEnvironment
  let path ← pathFunction ops pathCaches
  let libpath ← forceStringOnce ops.onceSystem libraryCaches.libpath
  let env ← adjustEnv ops env path libpath adjustPath adjustLibpath
  let arguments ← ops.vectors.singleton (← forceStringOnce ops.onceSystem pathCaches.lldPath)
  let command ← commandFromVector arguments
  JuliaLean.base.cmd.cmdKeyword ops.byteEnvironment identityFieldCast ops.sameStringReference
    ops.cstr command command.ignorestatus env command.dir command.cpus command.uid command.gid
    (JuliaLean.base.cmd.defaultDetach command) (JuliaLean.base.cmd.defaultVerbatim command)
    (JuliaLean.base.cmd.defaultHide command)

/--
Julia source: base/linking.jl:86-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function dsymutil(; adjust_PATH::Bool = true, adjust_LIBPATH::Bool = true)
    env = adjust_ENV!(copy(ENV), PATH(), LIBPATH(), adjust_PATH, adjust_LIBPATH)
    return Cmd(Cmd([dsymutil_path()]); env)
end
```
-/

def dsymutil (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (pathCaches : PathCaches ops.onceSystem) (libraryCaches : LibraryCaches ops.onceSystem)
    (adjustPath adjustLibpath : Bool := true) :
    M World (Cmd Vec Cpu) := do
  let env ← ops.copyEnvironment ops.globalEnvironment
  let path ← pathFunction ops pathCaches
  let libpath ← forceStringOnce ops.onceSystem libraryCaches.libpath
  let env ← adjustEnv ops env path libpath adjustPath adjustLibpath
  let arguments ← ops.vectors.singleton (← forceStringOnce ops.onceSystem pathCaches.dsymutilPath)
  let command ← commandFromVector arguments
  JuliaLean.base.cmd.cmdKeyword ops.byteEnvironment identityFieldCast ops.sameStringReference
    ops.cstr command command.ignorestatus env command.dir command.cpus command.uid command.gid
    (JuliaLean.base.cmd.defaultDetach command) (JuliaLean.base.cmd.defaultVerbatim command)
    (JuliaLean.base.cmd.defaultHide command)

/--
Julia source: base/linking.jl:91-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ld(; strict_definitions::Bool = false)
    default_args = ``
    @static if Sys.iswindows()
        # From`x86_64-w64-mingw32-gcc -shared -Wl,--verbose`
        flavor = "gnu"
        m = Sys.ARCH == :x86_64 ? "i386pep" : "i386pe"
        entry = Sys.ARCH == :x86_64 ? "DllMainCRTStartup" : "_DllMainCRTStartup"
        default_args = `-m $m -Bdynamic -e $entry --enable-auto-image-base --disable-auto-import --disable-runtime-pseudo-reloc`
        if !strict_definitions
            default_args = `$default_args --allow-multiple-definition`
        end
    elseif Sys.isapple()
        flavor = "darwin"
        arch = Sys.ARCH == :aarch64 ? :arm64 : Sys.ARCH
        default_args = `-arch $arch -platform_version macos $(Base.MACOS_PRODUCT_VERSION) $(Base.MACOS_PLATFORM_VERSION)`
        if !strict_definitions
            default_args = `$default_args -undefined dynamic_lookup`
        end
        # due to an lld bug: https://github.com/llvm/llvm-project/issues/193646
        # we must make sure the syslibroot does not point to the system or else
        # it will not respect the provided `libSystem.tbd` file
        default_args = `$default_args -syslibroot $(private_libdir())`
    else
        flavor = "gnu"
        # From `gcc -shared -Wl,--verbose`; `-z defs` added to enforce that all symbols
        # the pkgimage references are resolvable at link time (catches regressions early
        # instead of deferring to first-call crashes at runtime).
        # `--discard-locals` drops assembler-local `.L` labels, which RISC-V objects carry
        # in their symbol tables (every `auipc` pair has one) and which profilers would
        # otherwise report instead of the enclosing function.
        default_args = `--build-id --eh-frame-hdr --hash-style=gnu --as-needed -z relro -z defs --discard-locals`
        if !isempty(Base.COMPRESS_PKGIMAGE_DEBUG_SECTIONS)
            default_args = `$default_args --compress-debug-sections=$(Base.COMPRESS_PKGIMAGE_DEBUG_SECTIONS)`
        end
    end

    `$(lld()) -flavor $flavor $default_args`
end
```
-/

def ld (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (pathCaches : PathCaches ops.onceSystem) (libraryCaches : LibraryCaches ops.onceSystem)
    (privateLibdir : Unit → M World String)
    (strictDefinitions : Bool := false) : M World (Cmd Vec Cpu) := do
  let mut flavor := "gnu"
  let mut defaultArgs : List String := []
  match ops.host.os with
  | .windows =>
      let machine := if ops.host.architecture == "x86_64" then "i386pep" else "i386pe"
      let entry := if ops.host.architecture == "x86_64" then "DllMainCRTStartup"
        else "_DllMainCRTStartup"
      defaultArgs := ["-m", machine, "-Bdynamic", "-e", entry, "--enable-auto-image-base",
        "--disable-auto-import", "--disable-runtime-pseudo-reloc"]
      if !strictDefinitions then
        defaultArgs := defaultArgs ++ ["--allow-multiple-definition"]
  | .apple =>
      flavor := "darwin"
      let architecture := if ops.host.architecture == "aarch64" then "arm64"
        else ops.host.architecture
      defaultArgs := ["-arch", architecture, "-platform_version", "macos",
        ops.host.macOSProductVersion, ops.host.macOSPlatformVersion]
      if !strictDefinitions then
        defaultArgs := defaultArgs ++ ["-undefined", "dynamic_lookup"]
      let privateDirectory ← privateLibdir ()
      defaultArgs := defaultArgs ++ ["-syslibroot", privateDirectory]
  | _ =>
      defaultArgs := ["--build-id", "--eh-frame-hdr", "--hash-style=gnu", "--as-needed",
        "-z", "relro", "-z", "defs", "--discard-locals"]
      if !ops.host.compressDebugSections.isEmpty then
        defaultArgs := defaultArgs ++ ["--compress-debug-sections=" ++
          ops.host.compressDebugSections]
  let lldCommand ← lld ops pathCaches libraryCaches
  let arguments ← ops.vectors.empty
  ops.vectors.append arguments lldCommand.exec
  appendStrings ops arguments ["-flavor", flavor]
  appendStrings ops arguments defaultArgs
  copyCommandExec ops lldCommand arguments

/--
Julia source: base/linking.jl:130-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const WHOLE_ARCHIVE = if Sys.isapple()
    "-all_load"
else
    "--whole-archive"
end

const NO_WHOLE_ARCHIVE = if Sys.isapple()
    ""
else
    "--no-whole-archive"
end
```
-/

structure ArchiveFlags where
  wholeArchive : String
  noWholeArchive : String
  deriving Repr, DecidableEq

def archiveFlags {Vec : Type} (host : Host Vec) : ArchiveFlags :=
  if host.os == .apple then ⟨"-all_load", ""⟩
  else ⟨"--whole-archive", "--no-whole-archive"⟩

/--
Julia source: base/linking.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
whole_archive(paths::String; is_cc=false) = whole_archive([paths]; is_cc)
```
-/

def wholeArchiveString (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (vectorMethod : Vec → Bool → M World (Cmd Vec Cpu))
    (path : String) (isCc : Bool := false) : M World (Cmd Vec Cpu) := do
  vectorMethod (← ops.vectors.singleton path) isCc

/--
Julia source: base/linking.jl:144-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function whole_archive(paths::Vector{String}; is_cc=false)
    cc_arg(a) = is_cc ? "-Wl,$a" : a
    if Sys.isapple()
        Cmd(collect(Iterators.flatmap(p -> (cc_arg("-force_load"), p), paths)))
    else
        `$(cc_arg("--whole-archive")) $paths $(cc_arg("--no-whole-archive"))`
    end
end
```
-/

def wholeArchiveVector (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (paths : Vec) (isCc : Bool := false) :
    M World (Cmd Vec Cpu) := do
  let arguments ← ops.vectors.empty
  let ccArg := fun (argument : String) =>
    if isCc then "-Wl," ++ argument else argument
  if ops.host.os == .apple then
    let _ ← JuliaLean.base.io.whileLoop (fun state => do
      match ← ops.vectorIterator.iterate paths state with
      | none => pure (.inl ())
      | some (path, next) =>
          ops.vectors.push arguments (ccArg "-force_load")
          ops.vectors.push arguments path
          pure (.inr (some next))) none
  else
    let flags := archiveFlags ops.host
    ops.vectors.push arguments (ccArg flags.wholeArchive)
    ops.vectors.append arguments paths
    ops.vectors.push arguments (ccArg flags.noWholeArchive)
  commandFromVector arguments

/--
Julia source: base/linking.jl:153-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const SHARED = if Sys.isapple()
    "-dylib"
else
    "-shared"
end
```
-/

def sharedFlag {Vec : Type} (host : Host Vec) : String :=
  if host.os == .apple then "-dylib" else "-shared"

/--
Julia source: base/linking.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
libdir() = abspath(Sys.BINDIR, Base.LIBDIR)
```
-/

def libdir (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) : M World String :=
  absolutePath ops ops.host.bindir [ops.host.baseLibdir]

/--
Julia source: base/linking.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
private_libdir() = abspath(Sys.BINDIR, Base.PRIVATE_LIBDIR)
```
-/

def privateLibdir (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) : M World String :=
  absolutePath ops ops.host.bindir [ops.host.privateLibdir]

/--
Julia source: base/linking.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    shlibdir() = Sys.BINDIR
```
-/

def shlibdirWindows (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) : String := ops.host.bindir

/--
Julia source: base/linking.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    shlibdir() = libdir()
```
-/

def shlibdirOther (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) : M World String := libdir ops

/--
Julia source: base/linking.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
verbose_linking() = something(Base.get_bool_env("JULIA_VERBOSE_LINKING", false), false)
```
-/

def verboseLinking (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) : M World Bool := do
  return ((← JuliaLean.base.env.getBoolEnvDefault ops.boolEnvOps "JULIA_VERBOSE_LINKING" false)
    ).getD false

/--
Julia source: base/linking.jl:169-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _find_static(lib)
    if isfile(joinpath(private_libdir(), lib))
        return joinpath(private_libdir(), lib)
    else
        return joinpath(libdir(), lib)
    end
end
```
-/

def findStatic (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (lib : String) : M World String := do
  let privateCandidate ← joinPath ops [← privateLibdir ops, lib]
  if ← ops.isFile privateCandidate then
    joinPath ops [← privateLibdir ops, lib]
  else
    joinPath ops [← libdir ops, lib]

/--
Julia source: base/linking.jl:177-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _find_loaded(re::Regex)
    for p in Libdl.dllist()
        occursin(re, p) && return p
    end
    error("no loaded shared object matching $re")
end
```
-/

def findLoaded (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (regex : Regex) : M World String := do
  let libraries ← JuliaLean.base.libdl.dllist ops.vectors.empty ops.vectors.push
    (ops.host.os == .apple) (ops.host.os == .windows) (ops.host.os == .linux)
    (ops.host.os == .bsd) ops.dyldImageCount ops.dyldGetImageName ops.unsafeString ops.jlDllist
  let result ← JuliaLean.base.io.whileLoop (fun state => do
    match ← ops.vectorIterator.iterate libraries state with
    | none => pure (.inl none)
    | some (path, next) =>
        match JuliaLean.base.regex.findnextRegex ops.regexOps (fun error => .jl error)
            ops.rangeErrorToIO ops.stringOps.lastindex
            (fun value index => ops.stringOps.nextind value index (JuliaLean.base.strings.basic.int 1))
            (fun value index => ops.stringOps.prevind value index (JuliaLean.base.strings.basic.int 1))
            regex path (JuliaLean.base.strings.basic.int 1) with
        | .error error => throw error
        | .ok (some _) => pure (.inl (some path))
        | .ok none => pure (.inr (some next))) none
  match result with
  | some path => pure path
  | none => throw (.errorException ("no loaded shared object matching " ++ ops.showRegex regex))

/--
Julia source: base/linking.jl:184-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function link_image_cmd(path, out; is_sysimage::Bool = false)
    PRIVATE_LIBDIR = "-L$(private_libdir())"
    LIBDIR = "-L$(libdir())"
    SHLIBDIR = "-L$(shlibdir())"
    LIBS = String[]
    if isdebugbuild()
        push!(LIBS, "-ljulia-debug")
        push!(LIBS, "-ljulia-internal-debug")
    else
        push!(LIBS, "-ljulia")
        push!(LIBS, "-ljulia-internal")
    end
    crtbegin = String[]
    crtend = String[]
    @static if Sys.iswindows()
        # From `x86_64-w64-mingw32-gcc -shared -Wl,--verbose`.
        append!(LIBS,     String["-lopenlibm"])
        # libmsvcrt-os.a contains MinGW CRT objects that can refer back to
        # libmingw32.a/libmingwex.a; keep the selected CRT last.
        append!(LIBS,     String["-lmingw32", "-lgcc_s", "-lgcc", "-lmoldname", "-lmingwex", "-lmsvcrt-os", "-lmingw32", "-lmingwex", "-lmsvcrt-os", "-lkernel32"])
        append!(LIBS,     String["-lpthread", "-ladvapi32", "-lshell32", "-luser32"])
        append!(crtbegin, String[_find_static("dllcrt2.o"), _find_static("crtbegin.o")])
        append!(crtend,   String[_find_static("crtend.o")])
        isdebugbuild() && push!(LIBS, "-lssp")
        append!(LIBS,     String["-lmingwex", "-lmsvcrt-os", "-lmingw32", "-lmingwex", "-lmsvcrt-os"])
    elseif Sys.isapple()
        # From `clang -dynamiclib -Wl,-v`
        append!(LIBS,     String[_find_static("libclang_rt.osx.a"), _find_static("libSystem.tbd")])
    else
        # From `gcc -shared -Wl,--verbose`
        # but without repeated libraries (lld auto-resolves circular library references)
        # musl has no separate libc.so: its dynamic loader is also the C library
        libc           = _find_loaded(r"/(?:libc|ld-musl-[^/]+)\.so\.\d+$")     # system libc
        ld_linux       = _find_loaded(r"/ld-(?:linux|musl|elf)[^/]*\.so\.\d+$") # system ld
        libc_nonshared = _find_static("libc_nonshared.a")
        append!(LIBS,     String["-lgcc", "--as-needed", "-lgcc_s", "-latomic", "-lopenlibm", "--no-as-needed", libc])
        isfile(libc_nonshared) && push!(LIBS, libc_nonshared)
        append!(LIBS,     String["--as-needed", ld_linux, "--no-as-needed"])
        append!(crtbegin, String[_find_static("crti.o"), _find_static("crtbeginS.o")])
        append!(crtend,   String[_find_static("crtendS.o"), _find_static("crtn.o")])
    end

    V = verbose_linking() ? "--verbose" : ""
    `$(ld(; strict_definitions = is_sysimage)) $V $SHARED -o $out $crtbegin $(whole_archive(path)) $PRIVATE_LIBDIR $LIBDIR $SHLIBDIR $LIBS $crtend`
end
```
-/

def linkImageCommand {PathValue Output : Type} (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (pathCaches : PathCaches ops.onceSystem) (libraryCaches : LibraryCaches ops.onceSystem)
    (wholeArchive : PathValue → M World (Cmd Vec Cpu))
    (stringifyOutput : Output → M World String)
    (path : PathValue) (out : Output) (isSysimage : Bool := false) :
    M World (Cmd Vec Cpu) := do
  let privateDir ← privateLibdir ops
  let libraryDir ← libdir ops
  let sharedDir ← match ops.host.os with
    | .windows => pure (shlibdirWindows ops)
    | _ => shlibdirOther ops
  let privateFlag := "-L" ++ privateDir
  let libraryFlag := "-L" ++ libraryDir
  let sharedDirFlag := "-L" ++ sharedDir
  let libraries ← ops.vectors.empty
  if ops.host.debugBuild then
    appendStrings ops libraries ["-ljulia-debug", "-ljulia-internal-debug"]
  else
    appendStrings ops libraries ["-ljulia", "-ljulia-internal"]
  let crtbegin ← ops.vectors.empty
  let crtend ← ops.vectors.empty
  match ops.host.os with
  | .windows =>
      appendStrings ops libraries ["-lopenlibm"]
      appendStrings ops libraries ["-lmingw32", "-lgcc_s", "-lgcc", "-lmoldname", "-lmingwex",
        "-lmsvcrt-os", "-lmingw32", "-lmingwex", "-lmsvcrt-os", "-lkernel32"]
      appendStrings ops libraries ["-lpthread", "-ladvapi32", "-lshell32", "-luser32"]
      let dllcrt2 ← findStatic ops "dllcrt2.o"
      let crtbeginPath ← findStatic ops "crtbegin.o"
      appendStrings ops crtbegin [dllcrt2, crtbeginPath]
      let crtendPath ← findStatic ops "crtend.o"
      ops.vectors.push crtend crtendPath
      if ops.host.debugBuild then ops.vectors.push libraries "-lssp"
      appendStrings ops libraries ["-lmingwex", "-lmsvcrt-os", "-lmingw32", "-lmingwex", "-lmsvcrt-os"]
  | .apple =>
      let clangRuntime ← findStatic ops "libclang_rt.osx.a"
      let systemLib ← findStatic ops "libSystem.tbd"
      appendStrings ops libraries [clangRuntime, systemLib]
  | _ =>
      let libcRegex := ops.regexLiteral "/(?:libc|ld-musl-[^/]+)\\.so\\.\\d+$"
      let linkerRegex := ops.regexLiteral "/ld-(?:linux|musl|elf)[^/]*\\.so\\.\\d+$"
      let libc ← findLoaded ops libcRegex
      let ldLinux ← findLoaded ops linkerRegex
      let libcNonshared ← findStatic ops "libc_nonshared.a"
      appendStrings ops libraries ["-lgcc", "--as-needed", "-lgcc_s", "-latomic", "-lopenlibm",
        "--no-as-needed", libc]
      if ← ops.isFile libcNonshared then ops.vectors.push libraries libcNonshared
      appendStrings ops libraries ["--as-needed", ldLinux, "--no-as-needed"]
      let crti ← findStatic ops "crti.o"
      let crtbeginPath ← findStatic ops "crtbeginS.o"
      appendStrings ops crtbegin [crti, crtbeginPath]
      let crtendPath ← findStatic ops "crtendS.o"
      let crtn ← findStatic ops "crtn.o"
      appendStrings ops crtend [crtendPath, crtn]
  let verbose ← verboseLinking ops
  let linker ← ld ops pathCaches libraryCaches (fun _ => privateLibdir ops) isSysimage
  let output ← stringifyOutput out
  let whole ← wholeArchive path
  let arguments ← ops.vectors.empty
  ops.vectors.append arguments linker.exec
  ops.vectors.push arguments (if verbose then "--verbose" else "")
  ops.vectors.push arguments (sharedFlag ops.host)
  appendStrings ops arguments ["-o", output]
  ops.vectors.append arguments crtbegin
  ops.vectors.append arguments whole.exec
  appendStrings ops arguments [privateFlag, libraryFlag, sharedDirFlag]
  ops.vectors.append arguments libraries
  ops.vectors.append arguments crtend
  copyCommandExec ops linker arguments

/--
Julia source: base/linking.jl:230-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function link_image(path, out, internal_stderr::IO=stderr, internal_stdout::IO=stdout;
                    is_sysimage::Bool = false)
    run(link_image_cmd(path, out; is_sysimage), Base.DevNull(), internal_stderr, internal_stdout)
end
```
-/

def linkImage {PathValue Output : Type} (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (pathCaches : PathCaches ops.onceSystem) (libraryCaches : LibraryCaches ops.onceSystem)
    (wholeArchive : PathValue → M World (Cmd Vec Cpu))
    (stringifyOutput : Output → M World String)
    (path : PathValue) (out : Output)
    (internalStderr : IO := ops.stderr) (internalStdout : IO := ops.stdout)
    (isSysimage : Bool := false) : M World Process := do
  let command ← linkImageCommand ops pathCaches libraryCaches wholeArchive stringifyOutput path out isSysimage
  let null ← ops.devNull
  ops.runProcess command null internalStderr internalStdout

/--
Julia source: base/linking.jl:238-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Known components. Others are rejected, so a typo cannot drop libraries from a bundle.
const COMPONENTS = (:codegen,)
```
-/
def components : Tuple1 RuntimeComponent := ⟨.codegen⟩

/--
Julia source: base/linking.jl:241-247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Linking.DEFAULT_COMPONENTS

The optional runtime components whose libraries [`runtime_libraries`](@ref) includes by
default: all of them.
"""
const DEFAULT_COMPONENTS = COMPONENTS
```
-/
def defaultComponents : Tuple1 RuntimeComponent := components

def defaultComponentOps {World : Type} :
    StringCollectionOps World (Tuple1 RuntimeComponent) RuntimeComponent Bool where
  collection := defaultComponents
  iterator := tuple1Iterator
  inKnown component := component == .codegen
  isCodegen component := component == .codegen
  repr component := pure (match component with | .codegen => ":codegen")



/--
Julia source: base/linking.jl:251-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_library_file(name::AbstractString, file::AbstractString)
    if endswith(name, '*')
        prefix = SubString(name, 1, prevind(name, lastindex(name)))
        return startswith(file, prefix) && occursin(string('.', Libdl.dlext), file)
    end
    parsed = try
        first(Base.BinaryPlatforms.parse_dl_name_version(file))
    catch ex
        ex isa ArgumentError || rethrow()
        return false # not the name of a shared library file
    end
    parsed == name && return true
    # `libopenblas64_.0.3.33.so` puts the soversion before the extension, as macOS does
    Sys.isapple() && return false
    parsed = first(Base.BinaryPlatforms.parse_dl_name_version(parsed * ".dylib", "macos"))
    return parsed == name
end
```
-/

def isLibraryFile {Name File : Type} (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (stringOps : LibraryStringOps World Name File) (name : Name) (file : File) :
    M World Bool := do
  if stringOps.endsWithStar name then
    let namePrefix := stringOps.dropLastCharacter name
    let extension := "." ++ JuliaLean.base.libdl.dlext
      (ops.host.os == .apple) (ops.host.os == .windows)
    return stringOps.startsWithFile file namePrefix && stringOps.occursInFile extension file
  let fileString ← stringOps.fileString file
  match JuliaLean.base.binaryplatforms.parseDlNameVersion fileString.toList
      ops.host.binaryPlatform.toList with
  | .error (.argumentError _) => pure false
  | .error error => throw (.jl error)
  | .ok (parsed, _) =>
      if stringOps.equalParsedName name parsed then pure true
      else if ops.host.os == .apple then pure false
      else
        match JuliaLean.base.binaryplatforms.parseDlNameVersion (parsed ++ ".dylib".toList)
            "macos".toList with
        | .error error => throw (.jl error)
        | .ok (macName, _) => pure (stringOps.equalParsedName name macName)

/--
Julia source: base/linking.jl:270-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
library_listings() = Pair{String,Vector{String}}[dir => readdir(dir; sort=true)
                                                 for dir in library_dirs() if isdir(dir)]
```
-/

def libraryListings (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (caches : LibraryCaches ops.onceSystem) : M World (List (String × List String)) := do
  let dirs ← forceVectorOnce ops.onceSystem caches.libraryDirs
  let listings ← JuliaLean.base.io.whileLoop (fun (state, reverseListings) => do
    match ← ops.vectorIterator.iterate dirs state with
    | none => pure (.inl reverseListings)
    | some (dir, next) =>
        if ← ops.isDir dir then
          let files ← ops.readdirSorted dir
          pure (.inr (some next, (dir, files) :: reverseListings))
        else pure (.inr (some next, reverseListings))) (none, [])
  pure listings.reverse

/--
Julia source: base/linking.jl:274-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function library_files!(paths::Vector{String}, name::AbstractString, listings)
    for (dir, files) in listings
        found = false
        for file in files
            is_library_file(name, file) || continue
            push!(paths, joinpath(dir, file))
            found = true
        end
        # a library lives in only one of these directories
        found && return true
    end
    return false
end
```
-/

def libraryFilesAppend {Name File Listings ListingState Files FileState : Type}
    (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (stringOps : LibraryStringOps World Name File)
    (listingIterator : IteratorOps World Listings (String × Files) ListingState)
    (fileIterator : IteratorOps World Files File FileState)
    (paths : Vec) (name : Name) (listings : Listings) : M World Bool := do
  JuliaLean.base.io.whileLoop (fun listingState => do
    match ← listingIterator.iterate listings listingState with
    | none => pure (.inl false)
    | some ((dir, files), nextListingState) => do
        let found ← JuliaLean.base.io.whileLoop (fun (fileState, found) => do
          match ← fileIterator.iterate files fileState with
          | none => pure (.inl found)
          | some (file, nextFileState) =>
              if ← isLibraryFile ops stringOps name file then
                let filePath ← stringOps.fileString file
                ops.vectors.push paths (← joinPath ops [dir, filePath])
                pure (.inr (some nextFileState, true))
              else
                pure (.inr (some nextFileState, found))) (none, false)
        if found then pure (.inl true)
        else pure (.inr (some nextListingState))) none

/--
Julia source: base/linking.jl:288-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Linking.library_files(name::AbstractString) -> Vector{String}
    Base.Linking.library_files(names) -> Vector{String}

Paths of the shared library files, including version symlinks, that this Julia installation
ships for the unversioned library name `name` (e.g. `"libopenblas64_"`). Names it does not
ship contribute nothing. System directories are not searched.
"""
function library_files(names)
    listings = library_listings()
    paths = String[]
    for name in names
        library_files!(paths, name, listings)
    end
    return unique!(paths)
end
```
-/

def libraryFiles {Name Names NameState : Type}
    (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (caches : LibraryCaches ops.onceSystem) (stringOps : LibraryStringOps World Name String)
    (nameIterator : IteratorOps World Names Name NameState) (names : Names) :
    M World Vec := do
  let listings ← libraryListings ops caches
  let paths ← ops.vectors.empty
  let _ ← JuliaLean.base.io.whileLoop (fun nameState => do
    match ← nameIterator.iterate names nameState with
    | none => pure (.inl ())
    | some (name, nextNameState) => do
        let _ ← libraryFilesAppend ops stringOps listIterator listIterator paths name listings
        pure (.inr (some nextNameState))) none
  ops.uniqueVector paths

/--
Julia source: base/linking.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
library_files(name::AbstractString) = library_files((name,))
```
-/

def libraryFilesSingle {Name : Type}
    (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (caches : LibraryCaches ops.onceSystem) (stringOps : LibraryStringOps World Name String)
    (name : Name) : M World Vec :=
  libraryFiles ops caches stringOps listIterator [name]

def renderComponents {Components Component State : Type}
    (componentOps : StringCollectionOps World Components Component State) : M World String := do
  let names ← JuliaLean.base.io.whileLoop (fun (state, reverseNames) => do
    match ← componentOps.iterator.iterate componentOps.collection state with
    | none => pure (.inl reverseNames)
    | some (component, next) =>
        let name ← componentOps.repr component
        pure (.inr (some next, name :: reverseNames))) (none, [])
  pure (joinStrings ", " names.reverse)

def containsCodegen {Components Component State : Type}
    (componentOps : StringCollectionOps World Components Component State)
    (components : Components) : M World Bool :=
  JuliaLean.base.io.whileLoop (fun state => do
    match ← componentOps.iterator.iterate components state with
    | none => pure (.inl false)
    | some (component, next) =>
        if componentOps.isCodegen component then pure (.inl true)
        else pure (.inr (some next))) none


/--
Julia source: base/linking.jl:306-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function runtime_library_names(optional_components)
    for component in optional_components
        component in COMPONENTS || throw(ArgumentError(
            "unknown optional component $(repr(component)); the optional components are " *
            join(map(repr, COMPONENTS), ", ")))
    end
    debug = isdebugbuild() ? "-debug" : ""
    # Julia's own libraries are required (a framework's `libjulia` is its `Julia` binary)
    required = String[]
    Base.DARWIN_FRAMEWORK || push!(required, "libjulia$debug")
    push!(required, "libjulia-internal$debug")
    # The rest come from `JL_RUNTIME_LIBS` in Make.inc and are optional: a build may use a
    # system copy (`USE_SYSTEM_LIBUV`) or turn off a feature (MMTk, Tracy, sanitizers).
    optional = copy(Base.RUNTIME_LIBRARY_NAMES)
    if :codegen in optional_components
        push!(required, "libjulia-codegen$debug")
        # LLVM may come from the system or be linked statically
        append!(optional, Base.CODEGEN_LIBRARY_NAMES)
    end
    return required, optional
end
```
-/

def runtimeLibraryNames {Components Component ComponentState : Type}
    (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState) (componentOps : StringCollectionOps World Components Component ComponentState)
    (optionalComponents : Components) : M World (Vec × Vec) := do
  let _ ← JuliaLean.base.io.whileLoop (fun state => do
    match ← componentOps.iterator.iterate optionalComponents state with
    | none => pure (.inl ())
    | some (component, next) =>
        if componentOps.inKnown component then pure (.inr (some next))
        else do
          let componentName ← componentOps.repr component
          let knownComponents ← renderComponents componentOps
          throw (.jl (.argumentError ("unknown optional component " ++ componentName ++
            "; the optional components are " ++ knownComponents)))) none
  let debug := if ops.host.debugBuild then "-debug" else ""
  let required ← ops.vectors.empty
  if !ops.host.darwinFramework then
    ops.vectors.push required ("libjulia" ++ debug)
  ops.vectors.push required ("libjulia-internal" ++ debug)
  let optional ← ops.copyVector ops.host.runtimeLibraryNames
  if ← containsCodegen componentOps optionalComponents then
    ops.vectors.push required ("libjulia-codegen" ++ debug)
    ops.vectors.append optional ops.host.codegenLibraryNames
  pure (required, optional)

/--
Julia source: base/linking.jl:328-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.Linking.runtime_libraries(; optional_components = Base.Linking.DEFAULT_COMPONENTS) -> Vector{String}

Paths of the shared library files, including version symlinks, that this Julia installation
ships and a program embedding the runtime needs. A bundle should keep each at the same path
relative to `Sys.BINDIR`.

The only optional component is `:codegen` (`libjulia-codegen` and LLVM), which a program that
never compiles code at run time, such as one built with `--trim`, can leave out.

Only files in this installation are returned, and libraries of standard libraries are not
included; see [`library_files`](@ref) for those. Throws if the installation lacks a library
every build ships, such as `libjulia-internal`.
"""
function runtime_libraries(; optional_components = DEFAULT_COMPONENTS)
    required, optional = runtime_library_names(optional_components)
    return resolve_libraries(required, optional, library_listings())
end
```
-/

def runtimeLibraries {Components Component ComponentState : Type}
    (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (componentOps : StringCollectionOps World Components Component ComponentState)
    (libraryCaches : LibraryCaches ops.onceSystem)
    (resolve : LibraryCaches ops.onceSystem → Vec → Vec → List (String × List String) → M World Vec)
    (optionalComponents : Components := componentOps.collection) : M World Vec := do
  let (required, optional) ← runtimeLibraryNames ops componentOps optionalComponents
  resolve libraryCaches required optional (← libraryListings ops libraryCaches)

/--
Julia source: base/linking.jl:347-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resolve_libraries(required, optional, listings)
    paths = String[]
    absent = String[]
    for name in required
        library_files!(paths, name, listings) || push!(absent, name)
    end
    if !isempty(absent)
        error("this Julia installation does not contain the shared ",
              length(absent) == 1 ? "library " : "libraries ", join(absent, ", "),
              ", which every build of Julia ships; looked in ", join(library_dirs(), ", "),
              ". The installation is incomplete.")
    end
    for name in optional
        library_files!(paths, name, listings)
    end
    return unique!(paths)
end
```
-/

def resolveLibraries {Name Required RequiredState Optional OptionalState
    Listings ListingState Files FileState : Type}
    (ops : ModelOps World Env Vec Cpu IO Process Handle Regex Data Ptr StringSlice StringChar StringCodeUnit StringCodeUnitType VectorState)
    (libraryCaches : LibraryCaches ops.onceSystem) (stringOps : LibraryStringOps World Name File)
    (requiredIterator : IteratorOps World Required Name RequiredState)
    (optionalIterator : IteratorOps World Optional Name OptionalState)
    (listingIterator : IteratorOps World Listings (String × Files) ListingState)
    (fileIterator : IteratorOps World Files File FileState)
    (required : Required) (optional : Optional) (listings : Listings) : M World Vec := do
  let paths ← ops.vectors.empty
  let absent ← JuliaLean.base.io.whileLoop (fun (state, reverseAbsent) => do
    match ← requiredIterator.iterate required state with
    | none => pure (.inl reverseAbsent)
    | some (name, next) => do
        let found ← libraryFilesAppend ops stringOps listingIterator fileIterator paths name listings
        if found then pure (.inr (some next, reverseAbsent))
        else pure (.inr (some next, (← stringOps.nameString name) :: reverseAbsent))) (none, [])
  if !absent.isEmpty then
    let dirsVector ← forceVectorOnce ops.onceSystem libraryCaches.libraryDirs
    let dirs ← vectorToList ops dirsVector
    let names := absent.reverse
    let noun := if names.length == 1 then "library " else "libraries "
    throw (.errorException ("this Julia installation does not contain the shared " ++ noun ++
      joinStrings ", " names ++ ", which every build of Julia ships; looked in " ++
      joinStrings ", " dirs ++ ". The installation is incomplete."))
  let _ ← JuliaLean.base.io.whileLoop (fun state => do
    match ← optionalIterator.iterate optional state with
    | none => pure (.inl ())
    | some (name, next) => do
        let _ ← libraryFilesAppend ops stringOps listingIterator fileIterator paths name listings
        pure (.inr (some next))) none
  ops.uniqueVector paths


end JuliaLean.base.linking
