import JuliaLean.Platforms.DlName
import JuliaLean.Platforms.Lit
import JuliaLean.DocsSyntaxCov.Ast

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
