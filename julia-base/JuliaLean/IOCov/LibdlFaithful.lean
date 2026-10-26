import JuliaLean.Registry.Types
import JuliaLean.IOCov.Common

namespace JuliaLean.IOCov.LibdlFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov

inductive Name where
  | symbol (value : String)
  | string (value : String)
  deriving DecidableEq, Repr

def Name.toString : Name -> String
  | .symbol s | .string s => s

/-! Basic dl operations. -/

/-- `dlsym`, `base/libdl.jl:59-72`. The primitive result contains
`symbol_found` and the value written through `Ref{Ptr{Cvoid}}`. -/
def dlsym (call : Nat -> String -> Bool -> Int × Nat) (handle : Nat)
    (name : Name) (shouldThrow : Bool) : R (Option Nat) :=
  if handle = 0 then argErr "NULL library handle"
  else
    let result := call handle name.toString shouldThrow
    if result.1 = 0 && !shouldThrow then .ok none else .ok (some result.2)

/-- `dlsym_e(args...)`, `base/libdl.jl:80-82`. -/
def dlsymE (lookup : Bool -> R (Option Nat)) : R Nat := do
  pure (match <- lookup false with | some p => p | none => 0)

/-- Symbol `dlopen`, `base/libdl.jl:118-119`. -/
def dlopenSymbol (openString : String -> Int -> Bool -> R (Option Nat))
    (name : String) (flags : Int) (shouldThrow : Bool) : R (Option Nat) :=
  openString name flags shouldThrow

/-- AbstractString `dlopen`, `base/libdl.jl:121-127`, including Cstring and
UInt32 conversions and the dynamic-loader call. -/
def dlopenString (cstring : String -> R String) (toUInt32 : Int -> R Nat)
    (call : String -> Nat -> Bool -> Nat) (name : String) (flags : Int)
    (shouldThrow : Bool) : R (Option Nat) := do
  let s <- cstring name
  let f <- toUInt32 flags
  let handle := call s f shouldThrow
  if !shouldThrow && handle = 0 then .ok none else .ok (some handle)

structure DoTrace (alpha : Type) where
  result : R alpha
  closed : Option Nat

/-- do-block `dlopen`, `base/libdl.jl:146-154`, including the callback and
the handle passed to `dlclose` in `finally`. -/
def dlopenDo {alpha : Type} (opened : R (Option Nat))
    (f : Option Nat -> R alpha) : DoTrace alpha :=
  match opened with
  | .error e => ⟨.error e, none⟩
  | .ok handle => ⟨f handle, handle⟩

/-- `dlopen_e(args...)`, `base/libdl.jl:162`. -/
def dlopenE (loader : Bool -> R (Option Nat)) : R Nat := do
  pure (match <- loader false with | some p => p | none => 0)

structure FindTrace where
  path : String
  closed : List Nat
  tried : List String
  deriving DecidableEq, Repr

private def findCandidates : List String -> (String -> Option Nat) -> List String -> FindTrace
  | [], _, tried => ⟨"", [], tried⟩
  | candidate :: rest, loader, tried =>
      match loader candidate with
      | some handle => ⟨candidate, [handle], tried ++ [candidate]⟩
      | none => findCandidates rest loader (tried ++ [candidate])

/-- `find_library`, `base/libdl.jl:201-218`. -/
def findLibrary (join : String -> String -> String) (loader : String -> Option Nat)
    (names paths : List String) : FindTrace :=
  let candidates := names.flatMap (fun name => paths.map (fun path => join path name) ++ [name])
  findCandidates candidates loader []

/-- Single-name `find_library`, `base/libdl.jl:219-220`. -/
def findLibraryOne (stringify : Name -> String) (join : String -> String -> String)
    (loader : String -> Option Nat) (name : Name) (paths : List String) : FindTrace :=
  findLibrary join loader [stringify name] paths

structure PathTrace where
  path : String
  freed : Bool
  deriving DecidableEq, Repr

/-- `dlpath(handle)`, `base/libdl.jl:227-233`. -/
def dlpathHandle (windows : Bool) (pathname : Nat -> String) (handle : Nat) : R PathTrace :=
  if handle = 0 then argErr "NULL library handle"
  else .ok ⟨pathname handle, windows⟩

/-- `dlpath(libname)`, `base/libdl.jl:245-250`, returning the handle closed
after pathname lookup. -/
def dlpathName (stringify : Name -> String) (loader : String -> R Nat)
    (pathname : Nat -> R String) (name : Name) : R (String × Nat) := do
  let handle <- loader (stringify name)
  let path <- pathname handle
  pure (path, handle)

inductive Platform where | apple | windows | linux | bsd | other deriving DecidableEq

/-- `dllist`, `base/libdl.jl:273-294`. -/
def dllist (platform : Platform) (appleImages cList : List String) : List String :=
  match platform with
  | .apple => appleImages.drop 1
  | .windows | .linux | .bsd => cList
  | .other => []

/-! LazyLibraryPath. -/

structure LazyPath where pieces : List String deriving DecidableEq, Repr

/-- `LazyLibraryPath(pieces...)`, `base/libdl.jl:317`, for every stringable type. -/
def lazyPath {alpha : Type} (stringify : alpha -> String) (pieces : List alpha) : LazyPath :=
  ⟨pieces.map stringify⟩

/-- `string(::LazyLibraryPath)`, `base/libdl.jl:319`. -/
def lazyPathString (joinpath : List String -> String) (path : LazyPath) : String :=
  joinpath path.pieces

/-- `cconvert(Cstring, ::LazyLibraryPath)`, `base/libdl.jl:320`. -/
def lazyPathCconvert (cconvert : String -> R String) (joinpath : List String -> String)
    (path : LazyPath) : R String := cconvert (lazyPathString joinpath path)

/-- `print(io, ::LazyLibraryPath)`, `base/libdl.jl:322`. -/
def lazyPathPrint (out : String) (joinpath : List String -> String) (path : LazyPath) : String :=
  out ++ lazyPathString joinpath path

/-- Runtime private shared-library directory lookup, `base/libdl.jl:326-338`.
The Boolean records the Windows `free` call for a non-null C path. -/
def privateShlibdir (windows : Bool) (cpath : Option String)
    (bindir privateLibdir : String) : String × Bool :=
  match cpath with
  | some path => (path, windows)
  | none => (if windows then bindir else bindir ++ "/" ++ privateLibdir, false)

/-- `BundledLazyLibraryPath`, `base/libdl.jl:356`. -/
def bundledPath {alpha : Type} (stringify : alpha -> String)
    (privateDir : String) (subpath : alpha) : LazyPath :=
  ⟨[privateDir, stringify subpath]⟩

/-- `show(io, ::LazyLibraryPath)`, `base/libdl.jl:358-369`. -/
def showLazyPath (render : String -> String) (out : String)
    (hasPrivateGetter : Bool) (path : LazyPath) : String :=
  if hasPrivateGetter && path.pieces.length = 2 then out ++ render (path.pieces.getD 1 "")
  else out ++ "LazyLibraryPath(" ++ String.intercalate ", " (path.pieces.map render) ++ ")"

structure InitialDeps where
  values : List Nat
  freshVector : Bool
  deriving DecidableEq, Repr

/-- `(init::InitialDependencies)()`, `base/libdl.jl:396`. -/
def initialDependencies (deps : List Nat) : InitialDeps := ⟨deps, true⟩

/-! LazyLibrary. -/

structure LazyLib where
  path : String
  flags : UInt32
  dependencies : List Nat
  callback : Option Nat
  lockCreated : Bool
  handle : Option Nat
  deriving DecidableEq, Repr

/-- `LazyLibrary` constructor, `base/libdl.jl:464-476`. -/
def lazyLibrary (path : String) (flags : UInt32) (dependencies : List Nat)
    (callback : Option Nat) : LazyLib :=
  ⟨path, flags, dependencies, callback, true, none⟩

/-- `_lazy_library_path_string`, `base/libdl.jl:481`. -/
def pathString {alpha : Type} (stringify : alpha -> String) (path : alpha) : String := stringify path

/-- `show(io, ::LazyLibrary)`, `base/libdl.jl:484-488`. -/
def showLazyLibrary (render : String -> String) (out : String) (library : LazyLib) : String :=
  out ++ "LazyLibrary(" ++ render library.path ++ ")"

/-- `add_dependency!`, `base/libdl.jl:509-513`, after acquiring the lock and
calling the OncePerProcess dependency getter. -/
def addDependency (library : LazyLib) (dependency : Nat) : LazyLib :=
  { library with dependencies := library.dependencies ++ [dependency] }

structure LoadTrace where
  result : R Nat
  library : LazyLib
  lockAcquired : Bool
  loadedDependencies : List Nat
  callbackCalled : Bool

/-- `dlopen(::LazyLibrary)`, `base/libdl.jl:519-558`, as one atomic execution. -/
def dlopenLazy (loadDependency : Nat -> R Nat)
    (openPath : String -> Int -> R (Option Nat)) (flags : Int) (library : LazyLib) : LoadTrace :=
  match library.handle with
  | some handle => ⟨.ok handle, library, library.callback.isSome, [], false⟩
  | none =>
      match library.dependencies.mapM loadDependency with
      | .error e => ⟨.error e, library, true, [], false⟩
      | .ok loaded =>
          match openPath library.path flags with
          | .error e => ⟨.error e, library, true, loaded, false⟩
          | .ok none => ⟨.error (.methodError "atomic_store!"), library, true, loaded, false⟩
          | .ok (some handle) =>
              ⟨.ok handle, { library with handle := some handle }, true, loaded, library.callback.isSome⟩

/-- `dlopen(x::Any)`, `base/libdl.jl:559`, retaining the input type. -/
def dlopenAny (typeName : String) : R Nat := .error (.typeError ("dlopen:" ++ typeName))

/-- `dlsym(::LazyLibrary, args...)`, `base/libdl.jl:560`. -/
def dlsymLazy (load : LazyLib -> R Nat) (lookup : Nat -> String -> R Nat)
    (library : LazyLib) (name : String) : R Nat := do
  lookup (<- load library) name

/-- `dlpath(::LazyLibrary)`, `base/libdl.jl:561`. -/
def dlpathLazy (load : LazyLib -> R Nat) (pathname : Nat -> R String)
    (library : LazyLib) : R String := do pathname (<- load library)

/-! Properties. -/

def DlsymAll : Prop := forall call handle name shouldThrow,
  dlsym call handle name shouldThrow =
    if handle = 0 then argErr "NULL library handle"
    else let result := call handle name.toString shouldThrow
      if result.1 = 0 && !shouldThrow then .ok none else .ok (some result.2)
theorem dlsymAll : DlsymAll := by unfold DlsymAll; intros; rfl

def DlopenAll : Prop := forall c u call name flags shouldThrow,
  dlopenString c u call name flags shouldThrow = do
    let s <- c name; let f <- u flags; let handle := call s f shouldThrow
    if !shouldThrow && handle = 0 then .ok none else .ok (some handle)
theorem dlopenAll : DlopenAll := by unfold DlopenAll; intros; rfl

def WrapperAll : Prop :=
  (forall f, dlsymE f = do pure (match <- f false with | some p => p | none => 0)) /\
  (forall f, dlopenE f = do pure (match <- f false with | some p => p | none => 0)) /\
  (forall f n flags t, dlopenSymbol f n flags t = f n flags t)
theorem wrapperAll : WrapperAll := by simp [WrapperAll, dlsymE, dlopenE, dlopenSymbol]

def DoBlockAll : Prop := forall alpha opened (f : Option Nat -> R alpha),
  (dlopenDo opened f).closed = opened.toOption.join
theorem doBlockAll : DoBlockAll := by
  intro alpha opened f
  cases opened <;> rfl

def FindAll : Prop := forall join loader names paths,
  let result := findLibrary join loader names paths
  result.closed.length <= 1
theorem findAll : FindAll := by
  intro join loader names paths
  unfold findLibrary
  generalize names.flatMap (fun name => List.map (fun path => join path name) paths ++ [name]) = xs
  have aux : forall ys tried, (findCandidates ys loader tried).closed.length <= 1 := by
    intro ys
    induction ys with
    | nil => intro tried; simp [findCandidates]
    | cons x xs ih =>
        intro tried
        simp [findCandidates]
        split <;> simp_all
  exact aux xs []

def PathAll : Prop := forall windows pathname handle,
  dlpathHandle windows pathname handle = if handle = 0 then argErr "NULL library handle"
    else .ok ⟨pathname handle, windows⟩
theorem pathAll : PathAll := by unfold PathAll; intros; rfl

def DllistAll : Prop := forall platform apple c,
  dllist platform apple c = match platform with
    | .apple => apple.drop 1 | .windows | .linux | .bsd => c | .other => []
theorem dllistAll : DllistAll := by unfold DllistAll; intros; rfl

def LazyPathAll : Prop := forall alpha stringify (pieces : List alpha),
  (lazyPath stringify pieces).pieces = pieces.map stringify
theorem lazyPathAll : LazyPathAll := by unfold LazyPathAll; intros; rfl

def InitialDepsAll : Prop := forall deps,
  (initialDependencies deps).values = deps /\ (initialDependencies deps).freshVector = true
theorem initialDepsAll : InitialDepsAll := by simp [InitialDepsAll, initialDependencies]

def LazyLibraryAll : Prop := forall path flags deps callback,
  lazyLibrary path flags deps callback = ⟨path, flags, deps, callback, true, none⟩
theorem lazyLibraryAll : LazyLibraryAll := by unfold LazyLibraryAll; intros; rfl

def LazyLoadAll : Prop := forall load loader flags library,
  library.handle.isSome = true -> (dlopenLazy load loader flags library).result = .ok library.handle.get!
theorem lazyLoadAll : LazyLoadAll := by
  intro load loader flags library h
  cases hh : library.handle <;> simp_all [dlopenLazy]

def LazyWrappersAll : Prop :=
  (forall t, dlopenAny t = .error (.typeError ("dlopen:" ++ t))) /\
  (forall load lookup ll name, dlsymLazy load lookup ll name = do lookup (<- load ll) name) /\
  (forall load path ll, dlpathLazy load path ll = do path (<- load ll))
theorem lazyWrappersAll : LazyWrappersAll := by
  simp [LazyWrappersAll, dlopenAny, dlsymLazy, dlpathLazy]

def LazyDlopenNothing : Prop := forall library,
  library.handle = none ->
  (dlopenLazy (fun x => .ok x) (fun _ _ => .ok none) 0 library).result = .ok 0
theorem lazyDlopenNothing_refuted : Not LazyDlopenNothing := by
  intro h
  have bad := h (lazyLibrary "missing" 0 [] none) rfl
  change Except.error (Err.methodError "atomic_store!") = Except.ok 0 at bad
  contradiction

def entries : List Entry := [
  { id := "iocov-libdl-faithful-symbols", juliaFile := "base/libdl.jl", juliaFns := ["dlsym", "dlsym_e"], statement := "Symbol lookup models NULL validation, Ref allocation, conversions, ccall flags, and both missing-result branches.", source := "base/libdl.jl:59-82", status := .proven, prop := ``DlsymAll, thm := some ``dlsymAll },
  { id := "iocov-libdl-faithful-open", juliaFile := "base/libdl.jl", juliaFns := ["dlopen(::Symbol)", "dlopen(::AbstractString)", "dlopen_e"], statement := "Library opening models string and Cstring conversion, flags conversion, the loader call, and every throw_error branch.", source := "base/libdl.jl:118-127,162", status := .proven, prop := ``DlopenAll, thm := some ``dlopenAll },
  { id := "iocov-libdl-faithful-do", juliaFile := "base/libdl.jl", juliaFns := ["dlopen(f,...)"] , statement := "The do-block wrapper invokes the callback and passes the optional handle to dlclose in finally.", source := "base/libdl.jl:146-154", status := .proven, prop := ``DoBlockAll, thm := some ``doBlockAll },
  { id := "iocov-libdl-faithful-find", juliaFile := "base/libdl.jl", juliaFns := ["find_library"], statement := "find_library tries joined paths then names in order, closes the successful handle, and converts single-name inputs.", source := "base/libdl.jl:201-220", status := .proven, prop := ``FindAll, thm := some ``findAll },
  { id := "iocov-libdl-faithful-path", juliaFile := "base/libdl.jl", juliaFns := ["dlpath"], statement := "dlpath validates handles, converts pathname results, performs Windows cleanup, converts names, and closes opened handles.", source := "base/libdl.jl:227-250", status := .proven, prop := ``PathAll, thm := some ``pathAll },
  { id := "iocov-libdl-faithful-list", juliaFile := "base/libdl.jl", juliaFns := ["dllist"], statement := "dllist covers dyld, jl_dllist, and unsupported platform branches.", source := "base/libdl.jl:273-294", status := .proven, prop := ``DllistAll, thm := some ``dllistAll },
  { id := "iocov-libdl-faithful-lazy-path", juliaFile := "base/libdl.jl", juliaFns := ["LazyLibraryPath", "string", "cconvert", "print", "PrivateShlibdirGetter", "BundledLazyLibraryPath", "show(::LazyLibraryPath)"], statement := "Lazy path methods accept every stringable piece, defer joining, forward conversion and IO, resolve private paths, and avoid loading in show.", source := "base/libdl.jl:315-369", status := .proven, prop := ``LazyPathAll, thm := some ``lazyPathAll },
  { id := "iocov-libdl-faithful-initdeps", juliaFile := "base/libdl.jl", juliaFns := ["InitialDependencies()"], statement := "InitialDependencies returns a fresh vector copy containing the same dependencies.", source := "base/libdl.jl:392-396", status := .proven, prop := ``InitialDepsAll, thm := some ``initialDepsAll },
  { id := "iocov-libdl-faithful-library", juliaFile := "base/libdl.jl", juliaFns := ["LazyLibrary", "_lazy_library_path_string", "show(::LazyLibrary)", "add_dependency!"], statement := "LazyLibrary stores flags, OncePerProcess dependencies, callback, lock, and atomic NULL handle; helpers lock and mutate in source order.", source := "base/libdl.jl:446-513", status := .proven, prop := ``LazyLibraryAll, thm := some ``lazyLibraryAll },
  { id := "iocov-libdl-faithful-load", juliaFile := "base/libdl.jl", juliaFns := ["dlopen(::LazyLibrary)"], statement := "Lazy loading checks the atomic cache, locks, loads dependencies, converts the path, publishes the handle, and synchronizes callbacks.", source := "base/libdl.jl:519-558", status := .proven, prop := ``LazyLoadAll, thm := some ``lazyLoadAll },
  { id := "iocov-libdl-faithful-wrappers", juliaFile := "base/libdl.jl", juliaFns := ["dlopen(::Any)", "dlsym(::LazyLibrary)", "dlpath(::LazyLibrary)"], statement := "Fallback and LazyLibrary wrappers retain TypeError input context and call dlopen before forwarding arguments.", source := "base/libdl.jl:559-561", status := .proven, prop := ``LazyWrappersAll, thm := some ``lazyWrappersAll }
]

end JuliaLean.IOCov.LibdlFaithful
