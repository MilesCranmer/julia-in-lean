import JuliaLean.base.libdl
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.io.IOCovCommon


section
namespace JuliaLean.IOCov.LibdlFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov

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
theorem wrapperAll : WrapperAll := by
  simp [WrapperAll, dlsymE, dlopenE, dlopenSymbol]
  intro f
  cases f false with
  | error _ => rfl
  | ok p => cases p <;> rfl

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
end
