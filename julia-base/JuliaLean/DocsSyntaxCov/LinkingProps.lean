import JuliaLean.DocsSyntaxCov.Linking

/-!
# Properties of `base/linking.jl`
-/

namespace JuliaLean.DocsSyntaxCov.Linking

open JuliaLean JuliaLean.DocsSyntaxCov
open JuliaLean.Platforms (Str)

theorem eget_eset_same (env : List (Str × Str)) (k v : Str) : eget (eset env k v) k = some v := by
  unfold eget eset
  split
  · rename_i h
    induction env with
    | nil => simp at h
    | cons p ps ih =>
      by_cases hp : p.1 = k
      · simp [hp]
      · have h' : ps.any (·.1 == k) = true := by simpa [hp] using h
        simpa [hp] using ih h'
  · rename_i h
    have : List.find? (fun p => p.1 == k) env = none := by
      rw [List.find?_eq_none]
      intro x hx hk
      exact h (List.any_eq_true.mpr ⟨x, hx, hk⟩)
    simp [List.find?_append, this]

/-- `adjust_ENV!` prepends `LIBPATH` (with `pathsep`) to the library search variable (or the
platform default), prepends `PATH` to `PATH`, leaves the environment alone when neither is
requested, and on Windows, where the library variable is `PATH` itself, only prepends
`LIBPATH`. -/
def AdjustEnvForms : Prop :=
  ∀ (os : OS) (dflt : Str) (env : List (Str × Str)) (P L : Str),
    adjustEnv os dflt env P L false false = env ∧
    eget (adjustEnv os dflt env P L false true) (libpathEnv os) =
      some (let base := (eget env (libpathEnv os)).getD dflt
            if base.isEmpty then L else L ++ [pathsep os] ++ base) ∧
    (os ≠ .windows → eget (adjustEnv os dflt env P L true false) (s% "PATH") =
      some (let old := (eget env (s% "PATH")).getD []
            if old.isEmpty then P else P ++ [pathsep os] ++ old)) ∧
    adjustEnv .windows dflt env P L true true = adjustEnv .windows dflt env P L false true ∧
    libpathEnv .windows = s% "PATH" ∧ pathsep .windows = ';' ∧ pathsep .apple = ':' ∧
    libpathDefault .apple = s% "~/lib:/usr/local/lib:/lib:/usr/lib" ∧ libpathDefault .other = []

theorem adjustEnvForms : AdjustEnvForms := by
  intro os dflt env P L
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [adjustEnv, if_true, Bool.false_and, Bool.false_eq_true, if_false]
    split <;> simp_all [eget_eset_same, List.isEmpty_iff]
  · intro hw
    have hne : libpathEnv os ≠ s% "PATH" := by cases os <;> simp_all [libpathEnv] <;> decide
    have hb : (libpathEnv os != s% "PATH") = true := by simpa using hne
    simp only [adjustEnv, Bool.false_eq_true, if_false, Bool.true_and, hb, Bool.true_or, if_true]
    split <;> simp_all [eget_eset_same, List.isEmpty_iff]
  · simp [adjustEnv, libpathEnv]

/-- The bundled tool is the first of `libexec`, `../tools` and `bin` that exists (made
absolute), else the one on `PATH`, else the bare name; `lld()`/`dsymutil()` run it in the
adjusted environment, and `PATH()` is its directory. -/
def ToolPaths : Prop :=
  ∀ (sys : Sys) (dflt exe : Str),
    let c1 := sys.joinpath (sys.joinpath sys.bindir sys.privateLibexecdirRel) exe
    (sys.isfile c1 = true → toolPath sys exe = sys.abspath c1 []) ∧
    (∀ w, (∀ c ∈ [c1, sys.joinpath (sys.joinpath (sys.joinpath sys.bindir (s% "..")) (s% "tools")) exe,
        sys.joinpath sys.bindir exe], sys.isfile c = false) →
      sys.which exe = some w → toolPath sys exe = w) ∧
    ((∀ c ∈ [c1, sys.joinpath (sys.joinpath (sys.joinpath sys.bindir (s% "..")) (s% "tools")) exe,
        sys.joinpath sys.bindir exe], sys.isfile c = false) →
      sys.which exe = none → toolPath sys exe = exe) ∧
    lld sys dflt = ⟨[lldPath sys], some (adjustEnv sys.os dflt sys.env (PATH sys) (LIBPATH sys) true true)⟩ ∧
    dsymutil sys dflt = ⟨[dsymutilPath sys], some (adjustEnv sys.os dflt sys.env (PATH sys) (LIBPATH sys) true true)⟩ ∧
    PATH sys = sys.dirname (lldPath sys) ∧
    lldExe .windows = s% "lld.exe" ∧ lldExe .other = s% "lld" ∧ dsymutilExe .windows = s% "dsymutil.exe"

theorem toolPaths : ToolPaths := by
  intro sys dflt exe
  refine ⟨fun h => ?_, fun w hn hw => ?_, fun hn hw => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [toolPath, List.find?, h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hn
    simp [toolPath, List.find?, hn.1, hn.2.1, hn.2.2, hw]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hn
    simp [toolPath, List.find?, hn.1, hn.2.1, hn.2.2, hw]

/-- `ld()` runs `lld -flavor <f>` with the platform's default arguments: on Linux and BSD
`strict_definitions` changes nothing; on Windows and macOS the non-strict command adds
`--allow-multiple-definition` / `-undefined dynamic_lookup`; macOS always ends with
`-syslibroot <private_libdir>`. -/
def LdForms : Prop :=
  ∀ (sys : Sys) (dflt : Str) (strict : Bool),
    (ld sys dflt strict).exec = [lldPath sys, s% "-flavor", (ldArgs sys strict).1] ++ (ldArgs sys strict).2 ∧
    (ld sys dflt strict).env = (lld sys dflt).env ∧
    (sys.os = .other → ldArgs sys strict = ldArgs sys false) ∧
    (sys.os = .windows → (ldArgs sys false).2 = (ldArgs sys true).2 ++ [s% "--allow-multiple-definition"]) ∧
    (sys.os = .apple → (ldArgs sys strict).2.getLast? = some (privateLibdir sys) ∧
      ((ldArgs sys false).2.contains (s% "dynamic_lookup") = true))

theorem ldForms : LdForms := by
  intro sys dflt strict
  refine ⟨rfl, rfl, fun h => ?_, fun h => ?_, fun h => ⟨?_, ?_⟩⟩
  · simp [ldArgs, h]
  · simp [ldArgs, h]
  · cases strict <;> simp [ldArgs, h]
  · simp [ldArgs, h]

/-- `whole_archive(paths; is_cc)`: `-force_load p` for each path on macOS, otherwise the paths
between `--whole-archive` and `--no-whole-archive`, each flag prefixed with `-Wl,` for a C
compiler; `whole_archive(path)` is `whole_archive([path])`. -/
def WholeArchiveForms : Prop :=
  ∀ (os : OS) (paths : List Str) (isCc : Bool) (p : Str),
    (os = .apple → (wholeArchive os paths isCc).exec =
      paths.flatMap (fun q => [ccArg isCc (s% "-force_load"), q])) ∧
    (os ≠ .apple → (wholeArchive os paths isCc).exec =
      [ccArg isCc (s% "--whole-archive")] ++ paths ++ [ccArg isCc (s% "--no-whole-archive")]) ∧
    ccArg true p = s% "-Wl," ++ p ∧ ccArg false p = p ∧
    wholeArchive1 os p isCc = wholeArchive os [p] isCc

theorem wholeArchiveForms : WholeArchiveForms := by
  intro os paths isCc p
  refine ⟨fun h => by simp [wholeArchive, h], fun h => by simp [wholeArchive, h], rfl, rfl, rfl⟩

/-- The library directories: `libdir()` and `private_libdir()` are absolute, `shlibdir()` is
`Sys.BINDIR` on Windows and `libdir()` elsewhere; `library_dirs` lists `private_libdir()`
and `shlibdir()` without repeats and `LIBPATH` joins them with `pathsep`;
`verbose_linking()` is `false` unless `JULIA_VERBOSE_LINKING` is a true value;
`_find_static` prefers the private directory; `_find_loaded` returns the first loaded
library matching or throws. -/
def LibraryDirForms : Prop :=
  ∀ (sys : Sys) (lib : Str) (re : Str → Bool),
    libdir sys = sys.abspath sys.bindir sys.libdirRel ∧
    privateLibdir sys = sys.abspath sys.bindir sys.privateLibdirRel ∧
    (sys.os = .windows → shlibdir sys = sys.bindir) ∧
    (sys.os ≠ .windows → shlibdir sys = libdir sys) ∧
    libraryDirs sys = (if privateLibdir sys = shlibdir sys then [privateLibdir sys]
      else [privateLibdir sys, shlibdir sys]) ∧
    LIBPATH sys = joinSep (pathsep sys.os) (libraryDirs sys) ∧
    (sys.verboseEnv = none → verboseLinking sys = false) ∧
    (∀ b, sys.verboseEnv = some b → verboseLinking sys = b) ∧
    (sys.isfile (sys.joinpath (privateLibdir sys) lib) = true →
      findStatic sys lib = sys.joinpath (privateLibdir sys) lib) ∧
    (sys.isfile (sys.joinpath (privateLibdir sys) lib) = false →
      findStatic sys lib = sys.joinpath (libdir sys) lib) ∧
    (∀ p, sys.dllist.find? re = some p → findLoaded sys re = .ok p) ∧
    (sys.dllist.find? re = none → ∃ m, findLoaded sys re = .error (.errorException m))

theorem libraryDirForms : LibraryDirForms := by
  intro sys lib re
  refine ⟨rfl, rfl, fun h => by simp [shlibdir, h, shlibdirWindows], fun h => by simp [shlibdir, h, shlibdirOther],
    ?_, rfl, fun h => by simp [verboseLinking, h], fun b h => by simp [verboseLinking, h],
    fun h => by simp [findStatic, h], fun h => by simp [findStatic, h], fun p h => by simp [findLoaded, h],
    fun h => ⟨"no loaded shared object matching", by simp [findLoaded, h]⟩⟩
  simp only [libraryDirs]
  split <;> simp_all

/-- `link_image_cmd(path, out; is_sysimage)`: the `ld` command (strict for a system image),
then the verbosity flag, `-shared`/`-dylib`, `-o out`, the C runtime start objects, the
whole archive `path`, the three `-L` directories, the libraries and the end objects; on
Linux it throws when no C library or dynamic loader is loaded. `link_image` runs it. -/
def LinkImageCmdShape : Prop :=
  ∀ (sys : Sys) (dflt : Str) (libcRe ldRe : Str → Bool) (path out : Str) (isSys : Bool),
    (sys.os = .apple → linkImageCmd sys dflt libcRe ldRe path out isSys =
      .ok ⟨(ld sys dflt isSys).exec ++ [if verboseLinking sys then s% "--verbose" else [], s% "-dylib", s% "-o", out] ++
        [s% "-force_load", path] ++
        [s% "-L" ++ privateLibdir sys, s% "-L" ++ libdir sys, s% "-L" ++ shlibdir sys] ++
        (if sys.isdebugbuild then [s% "-ljulia-debug", s% "-ljulia-internal-debug"] else [s% "-ljulia", s% "-ljulia-internal"]) ++
        [findStatic sys (s% "libclang_rt.osx.a"), findStatic sys (s% "libSystem.tbd")], (ld sys dflt isSys).env⟩) ∧
    (sys.os = .other → sys.dllist.find? libcRe = none →
      ∃ m, linkImageCmd sys dflt libcRe ldRe path out isSys = .error (.errorException m)) ∧
    linkImage sys dflt libcRe ldRe path out isSys = linkImageCmd sys dflt libcRe ldRe path out isSys

theorem linkImageCmdShape : LinkImageCmdShape := by
  intro sys dflt libcRe ldRe path out isSys
  refine ⟨fun h => ?_, fun h hc => ⟨"no loaded shared object matching", ?_⟩, rfl⟩
  · simp [linkImageCmd, h, wholeArchive1, wholeArchive, ccArg]
  · simp [linkImageCmd, h, findLoaded, hc]

/-- `is_library_file(name, file)`: a trailing `*` makes `name` a prefix (of a file with the
platform's extension); otherwise the name `parse_dl_name_version` reads from the file must
be `name`, a file that is no library name is not one, and outside macOS a soversion before
the extension (`libfoo.1.2.so`) also counts. -/
def IsLibraryFileForms : Prop :=
  (∀ (os : OS) (name file : Str), name.getLast? = some '*' →
    isLibraryFile os name file = .ok (file.take name.dropLast.length == name.dropLast &&
      isInfix ('.' :: dlext os) file)) ∧
  isLibraryFile .other (s% "libfoo") (s% "libfoo.so") = .ok true ∧
  isLibraryFile .other (s% "libfoo") (s% "libfoo.so.1.2") = .ok true ∧
  isLibraryFile .other (s% "libfoo") (s% "libfoo.1.2.so") = .ok true ∧
  isLibraryFile .apple (s% "libfoo") (s% "libfoo.1.2.so") = .ok false ∧
  isLibraryFile .other (s% "libfoo") (s% "README") = .ok false ∧
  isLibraryFile .other (s% "libfoo") (s% "libfoobar.so") = .ok false

theorem isLibraryFileForms : IsLibraryFileForms := by
  refine ⟨fun os name file h => by simp [isLibraryFile, h], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `library_files!`, `library_files` and `library_listings`: the files of a name come from the
first listed directory that has any; `library_files(name)` is `library_files((name,))`;
listings are those of the existing library directories. -/
def LibraryFilesForms : Prop :=
  ∀ (sys : Sys) (name : Str),
    libraryFiles1 sys name = libraryFiles sys [name] ∧
    libraryListings sys = ((libraryDirs sys).filter sys.isdir).map (fun d => (d, sys.readdir d)) ∧
    ∀ (paths : List Str) (dir : Str) (files : List Str) (rest : List (Str × List Str)) (found : List Str),
      matchingFiles sys dir name files = .ok found →
      libraryFilesBang sys paths name ((dir, files) :: rest) =
        if found.isEmpty then libraryFilesBang sys paths name rest else .ok (paths ++ found, true)

theorem libraryFilesForms : LibraryFilesForms := by
  intro sys name
  refine ⟨rfl, rfl, fun paths dir files rest found h => ?_⟩
  simp only [libraryFilesBang, h, exc_bind_ok]
  split <;> simp_all

/-- A Linux process whose library directories hold `libbar.1.2.3.4.so`. -/
def sys4 : Sys :=
  { os := .other, arch := .x86_64, bindir := s% "/j/bin", libdirRel := s% "../lib",
    privateLibdirRel := s% "../lib/julia", privateLibexecdirRel := s% "../libexec/julia",
    joinpath := fun a b => a ++ ['/'] ++ b, abspath := fun a b => a ++ ['/'] ++ b, dirname := id,
    isfile := fun _ => true, isdir := fun _ => true, readdir := fun _ => [s% "libbar.1.2.3.4.so"],
    dllist := [], which := fun _ => none, env := [], verboseEnv := none, isdebugbuild := false,
    darwinFramework := false, runtimeLibraryNames := [], codegenLibraryNames := [],
    compressDebugSections := [], macosProductVersion := [], macosPlatformVersion := [] }

/-- `library_files`: "Names it does not ship contribute nothing." Looking up a name returns
normally whatever other files the directories hold. -/
def LibraryFilesNoThrow : Prop :=
  ∀ (sys : Sys) (paths : List Str) (name : Str) (listings : List (Str × List Str)),
    ∃ r, libraryFilesBang sys paths name listings = .ok r

theorem libbar_throws :
    libraryFilesBang sys4 [] (s% "libfoo") [(s% "/d", [s% "libbar.1.2.3.4.so", s% "libfoo.so"])] =
      .error (.argumentError "invalid version string") := by decide +kernel

theorem libraryFilesNoThrow_refuted : ¬ LibraryFilesNoThrow := by
  intro h
  obtain ⟨r, hr⟩ := h sys4 [] (s% "libfoo") [(s% "/d", [s% "libbar.1.2.3.4.so", s% "libfoo.so"])]
  rw [libbar_throws] at hr
  cases hr

/-- `runtime_library_names(components)` rejects unknown components with an `ArgumentError`;
the required names are `libjulia` (unless a macOS framework) and `libjulia-internal`, plus
`libjulia-codegen` with `:codegen`, which also adds the LLVM names to the optional ones.
`resolve_libraries` throws when a required library is absent and otherwise returns the
files of the required and optional names without repeats; `runtime_libraries()` resolves the
names of all components in the library listings. -/
def RuntimeLibraries : Prop :=
  ∀ (sys : Sys),
    (∀ c rest, ¬ COMPONENTS.contains c → ∃ m, runtimeLibraryNames sys (c :: rest) = .error (.argumentError m)) ∧
    runtimeLibraryNames { sys with darwinFramework := false, isdebugbuild := false } [] =
      .ok ([s% "libjulia", s% "libjulia-internal"], sys.runtimeLibraryNames) ∧
    runtimeLibraryNames { sys with darwinFramework := false, isdebugbuild := false } ["codegen"] =
      .ok ([s% "libjulia", s% "libjulia-internal", s% "libjulia-codegen"],
        sys.runtimeLibraryNames ++ sys.codegenLibraryNames) ∧
    (∀ name opt listings, libraryFilesBang sys [] name listings = .ok ([], false) →
      ∃ m, resolveLibraries sys [name] opt listings = .error (.errorException m)) ∧
    resolveLibraries sys [] [] [] = .ok [] ∧
    runtimeLibraries sys = (do let (r, o) ← runtimeLibraryNames sys COMPONENTS
                               resolveLibraries sys r o (libraryListings sys))

theorem runtimeLibraries_spec : RuntimeLibraries := by
  intro sys
  refine ⟨fun c rest hc => ⟨"unknown optional component", ?_⟩, rfl, rfl,
    fun name opt listings h => ⟨"this Julia installation does not contain the shared library", ?_⟩, rfl, rfl⟩
  · have hc' : COMPONENTS.contains c = false := by simpa using hc
    simp only [runtimeLibraryNames, checkComponents, hc', Bool.not_false, ↓reduceIte, exc_bind_error]
  · simp [resolveLibraries, h, List.foldlM]

end JuliaLean.DocsSyntaxCov.Linking
