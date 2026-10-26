import JuliaLean.IOCov.Common
import JuliaLean.Paths.Model

set_option linter.unusedSimpArgs false

/-!
Models of `base/libdl.jl` at master `bbfa0ce4150`. Handles are addresses (`0` is
`C_NULL`); the runtime's loader entry points (`jl_load_dynamic_library`,
`jl_dlsym`, `jl_dlclose`, `jl_pathname_for_handle`) are arguments.
-/

namespace JuliaLean.IOCov.Libdl

open JuliaLean JuliaLean.IOCov

/-- Result of a Julia `dlopen`/`dlsym`: `none` is `nothing`, `some p` a pointer. -/
abbrev Handle := Option Nat

/-! ## `dlsym`, lines 59-82 -/

/-- `dlsym(hnd, s; throw_error)`, `base/libdl.jl:59-72`. `jlDlsym h s throw` returns
`(found, value)`, or throws itself when `throw` is set and the symbol is missing. -/
def dlsym (jlDlsym : Nat → String → Bool → R (Bool × Nat)) (hnd : Nat) (s : String)
    (throwError : Bool) : R Handle := do
  if hnd == 0 then argErr "NULL library handle" else
  let (found, val) ← jlDlsym hnd s throwError
  if !found && !throwError then pure none else pure (some val)

/-- `dlsym_e(args...) = something(dlsym(args...; throw_error=false), C_NULL)`, lines 80-82. -/
def dlsymE (jlDlsym : Nat → String → Bool → R (Bool × Nat)) (hnd : Nat) (s : String) : R Nat := do
  let r ← dlsym jlDlsym hnd s false
  pure (r.getD 0)

def DlsymCorrect : Prop :=
  (∀ j s t, dlsym j 0 s t = argErr "NULL library handle") ∧
  (∀ j h s, h ≠ 0 → j h s false = .ok (false, 0) → dlsym j h s false = .ok none) ∧
  (∀ j h s v t, h ≠ 0 → j h s t = .ok (true, v) → dlsym j h s t = .ok (some v)) ∧
  (∀ j h s, h ≠ 0 → j h s false = .ok (false, 0) → dlsymE j h s = .ok 0) ∧
  (∀ j h s v, h ≠ 0 → j h s false = .ok (true, v) → dlsymE j h s = .ok v)

theorem dlsymCorrect : DlsymCorrect := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [dlsym, dlsymE, bind, Except.bind, pure, Except.pure]

/-! ## `dlopen`, `dlclose`, lines 116-190 -/

/-- `dlopen(s::AbstractString, flags; throw_error)`, `base/libdl.jl:121-127`: `flags` is
converted to `UInt32`; `load s flags throw` is `jl_load_dynamic_library`, which throws
itself when `throw` is set. -/
def dlopenStr (load : String → Nat → Bool → R Nat) (s : String) (flags : Int) (throwError : Bool) :
    R Handle := do
  let f ← toInt .u32 flags
  let ret ← load s f.toNat throwError
  if !throwError && ret == 0 then pure none else pure (some ret)

/-- `dlopen(s::Symbol, flags; kwargs...) = dlopen(string(s), flags; kwargs...)`, lines 118-119. -/
def dlopenSym (load : String → Nat → Bool → R Nat) (s : String) (flags : Int) (throwError : Bool) :
    R Handle := dlopenStr load s flags throwError

/-- `dlclose(p::Ptr) = 0 == jl_dlclose(p)`, lines 169-171; `dlclose(::Nothing)` returns
`nothing`, lines 189-190 (`none`). -/
def dlclose (jlDlclose : Nat → Int) : Handle → Option Bool
  | none => none
  | some p => some (0 == jlDlclose p)

/-- `dlopen(f::Function, name, args...)`, lines 146-154: opens, applies `f`, and always
calls `dlclose` on the handle (still `nothing` when `dlopen` threw). Returns the result and
the handle given to `dlclose`. -/
def dlopenDo {α} (open_ : R Handle) (f : Handle → R α) : R α × Handle :=
  match open_ with
  | .error e => (.error e, none)
  | .ok h => (f h, h)

/-- `dlopen_e(args...) = something(dlopen(args...; throw_error=false), C_NULL)`, line 162. -/
def dlopenE (load : String → Nat → Bool → R Nat) (s : String) (flags : Int) : R Nat := do
  let r ← dlopenStr load s flags false
  pure (r.getD 0)

def DlopenCorrect : Prop :=
  (∀ load s flags, 0 ≤ flags → flags ≤ 4294967295 → load s flags.toNat false = .ok 0 →
      dlopenStr load s flags false = .ok none) ∧
  (∀ load s flags p t, 0 ≤ flags → flags ≤ 4294967295 → p ≠ 0 → load s flags.toNat t = .ok p →
      dlopenStr load s flags t = .ok (some p)) ∧
  (∀ load s flags t, flags < 0 → dlopenStr load s flags t = .error (.jl (.inexactError "UInt32"))) ∧
  (∀ load s flags t, dlopenSym load s flags t = dlopenStr load s flags t) ∧
  (∀ c, dlclose c none = none) ∧ (∀ c p, dlclose c (some p) = some (0 == c p)) ∧
  (∀ (α : Type) (e : Err) (f : Handle → R α), dlopenDo (.error e) f = (.error e, none)) ∧
  (∀ (α : Type) (h : Handle) (f : Handle → R α), dlopenDo (.ok h) f = (f h, h)) ∧
  (∀ load s flags, 0 ≤ flags → flags ≤ 4294967295 → load s flags.toNat false = .ok 0 →
      dlopenE load s flags = .ok 0)

theorem dlopenCorrect : DlopenCorrect := by
  refine ⟨?_, ?_, ?_, fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, ?_⟩
  · intro load s flags h1 h2 h
    simp [dlopenStr, toInt_u32 flags h1 h2, h, bind, Except.bind, pure, Except.pure]
  · intro load s flags p t h1 h2 hp h
    simp [dlopenStr, toInt_u32 flags h1 h2, h, hp, bind, Except.bind, pure, Except.pure]
  · intro load s flags t h
    simp [dlopenStr, toInt_u32_neg flags (Or.inl h), bind, Except.bind]
  · intro load s flags h1 h2 h
    simp [dlopenE, dlopenStr, toInt_u32 flags h1 h2, h, bind, Except.bind, pure, Except.pure]

/-! ## `find_library`, lines 201-220 -/

/-- `find_library(libnames, extrapaths)`, `base/libdl.jl:201-218`: for each name, try
`joinpath(path, lib)` for each extra path, then `lib`; the first one `dlopen(...;
throw_error=false)` opens is closed and returned; `""` otherwise. `canOpen` is whether
`dlopen` returns a handle. -/
def findLibrary (canOpen : List Char → Bool) (join : List Char → List Char → List Char) :
    List (List Char) → List (List Char) → List Char
  | [], _ => []
  | lib :: libs, extrapaths =>
    match extrapaths.find? (fun path => canOpen (join path lib)) with
    | some path => join path lib
    | none => if canOpen lib then lib else findLibrary canOpen join libs extrapaths

/-- `find_library(libname, extrapaths) = find_library([string(libname)], extrapaths)`, line 219-220. -/
def findLibrary1 (canOpen : List Char → Bool) (join : List Char → List Char → List Char)
    (lib : List Char) (extrapaths : List (List Char)) : List Char :=
  findLibrary canOpen join [lib] extrapaths

/-- Documented: the result is one of the names, possibly prefixed by one of the paths,
that can be opened; on failure the empty string. -/
def FindLibraryDoc : Prop :=
  ∀ canOpen join libs extrapaths,
    let r := findLibrary canOpen join libs extrapaths
    (r = [] ∧ ∀ lib ∈ libs, ¬ canOpen lib ∧ ∀ p ∈ extrapaths, ¬ canOpen (join p lib)) ∨
    (∃ lib ∈ libs, canOpen r ∧ (r = lib ∨ ∃ p ∈ extrapaths, r = join p lib))

theorem findLibraryDoc_aux (canOpen : List Char → Bool) (join : List Char → List Char → List Char)
    (extrapaths : List (List Char)) (libs : List (List Char)) :
    let r := findLibrary canOpen join libs extrapaths
    (r = [] ∧ ∀ lib ∈ libs, ¬ canOpen lib ∧ ∀ p ∈ extrapaths, ¬ canOpen (join p lib)) ∨
    (∃ lib ∈ libs, canOpen r ∧ (r = lib ∨ ∃ p ∈ extrapaths, r = join p lib)) := by
  induction libs with
  | nil => simp [findLibrary]
  | cons lib libs ih =>
    simp only [findLibrary]
    cases hf : extrapaths.find? (fun path => canOpen (join path lib)) with
    | some path =>
      right
      have := List.find?_some hf
      exact ⟨lib, by simp, by simpa using this, Or.inr ⟨path, List.mem_of_find?_eq_some hf, rfl⟩⟩
    | none =>
      have hnone := List.find?_eq_none.mp hf
      by_cases hc : canOpen lib
      · right; exact ⟨lib, by simp, by simp [hc], by simp [hc]⟩
      · simp only [hc]
        rcases ih with ⟨h1, h2⟩ | ⟨l, hl, h3, h4⟩
        · left
          refine ⟨h1, ?_⟩
          intro l hl
          simp at hl
          rcases hl with rfl | hl
          · exact ⟨by simp [hc], fun p hp => by simpa using hnone p hp⟩
          · exact h2 l hl
        · right; exact ⟨l, by simp [hl], h3, h4⟩

theorem findLibraryDoc : FindLibraryDoc := fun canOpen join libs extrapaths =>
  findLibraryDoc_aux canOpen join extrapaths libs

def FindLibraryWrapper : Prop :=
  ∀ canOpen join lib extrapaths,
    findLibrary1 canOpen join lib extrapaths = findLibrary canOpen join [lib] extrapaths

theorem findLibraryWrapper : FindLibraryWrapper := fun _ _ _ _ => rfl

/-! ## `dlpath`, `dllist`, lines 227-294 -/

/-- `dlpath(handle::Ptr{Cvoid})`, lines 227-233. -/
def dlpathHandle (pathname : Nat → List UInt8) (handle : Nat) : R (List UInt8) :=
  if handle == 0 then argErr "NULL library handle" else .ok (pathname handle)

/-- `dlpath(libname)`, lines 245-250: `dlopen` (throwing), `dlpath`, `dlclose`. -/
def dlpathName (load : String → Nat → Bool → R Nat) (pathname : Nat → List UInt8)
    (defaultFlags : Int) (libname : String) : R (List UInt8) := do
  let h ← dlopenStr load libname defaultFlags true
  dlpathHandle pathname (h.getD 0)

/-- `dllist()`, lines 273-294 (Linux): the vector `jl_dllist` fills. -/
def dllist (jlDllist : Unit → List (List UInt8)) : List (List UInt8) := jlDllist ()

def DlpathCorrect : Prop :=
  (∀ pn, dlpathHandle pn 0 = argErr "NULL library handle") ∧
  (∀ pn h, h ≠ 0 → dlpathHandle pn h = .ok (pn h)) ∧
  (∀ load pn fl name p, 0 ≤ fl → fl ≤ 4294967295 → p ≠ 0 → load name fl.toNat true = .ok p →
      dlpathName load pn fl name = .ok (pn p)) ∧
  (∀ c, dllist c = c ())

theorem dlpathCorrect : DlpathCorrect := by
  refine ⟨fun _ => rfl, ?_, ?_, fun _ => rfl⟩
  · intro pn h hh; simp [dlpathHandle, hh]
  · intro load pn fl name p h1 h2 hp h
    simp [dlpathName, dlopenStr, dlpathHandle, toInt_u32 fl h1 h2, hp, h, bind, Except.bind,
      pure, Except.pure]

/-! ## `LazyLibraryPath`, lines 317-369 -/

/-- One path piece: a string, or `PrivateShlibdirGetter()`. -/
inductive Piece where
  | str (s : List Char)
  | shlibdir
  deriving DecidableEq, Repr

/-- `string(p)` of a piece; `string(::PrivateShlibdirGetter) = private_shlibdir()`, line 338. -/
def Piece.string (shlibdir : List Char) : Piece → List Char
  | .str s => s
  | .shlibdir => shlibdir

/-- `LazyLibraryPath(pieces...)`, line 317: stores the pieces. -/
def lazyLibraryPath (pieces : List Piece) : List Piece := pieces

/-- `string(llp) = joinpath(String[string(p) for p in llp.pieces])`, line 319, with the
Unix `joinpath` of `JuliaLean.Paths`. -/
def llpString (shlibdir : List Char) (llp : List Piece) : Jl (List Char) :=
  Paths.joinpath (llp.map (Piece.string shlibdir))

/-- `cconvert(Cstring, llp)`, line 320: the string, rejected if it contains NUL. -/
def llpCconvert (shlibdir : List Char) (llp : List Piece) : R (List Char) :=
  match llpString shlibdir llp with
  | .error e => .error (.jl e)
  | .ok s => if '\x00' ∈ s then argErr "embedded NULs are not allowed in C strings" else .ok s

/-- `print(io, llp) = print(io, string(llp))`, line 322. -/
def llpPrint (shlibdir : List Char) (llp : List Piece) : Jl (List Char) := llpString shlibdir llp

/-- `BundledLazyLibraryPath(subpath)`, line 356. -/
def bundled (subpath : List Char) : List Piece := lazyLibraryPath [.shlibdir, .str subpath]

/-- `show(io, llp)`, lines 358-369, with `showStr` the `show` of a string piece and
`"Base.Libc.Libdl.PrivateShlibdirGetter()"` that of the getter. -/
def llpShow (showStr : List Char → List Char) (llp : List Piece) : List Char :=
  let showP : Piece → List Char := fun
    | .str s => showStr s
    | .shlibdir => "Base.Libc.Libdl.PrivateShlibdirGetter()".toList
  match llp with
  | [.shlibdir, p] => showP p
  | _ => "LazyLibraryPath(".toList ++ List.intercalate ", ".toList (llp.map showP) ++ [')']

def LazyLibraryPathCorrect : Prop :=
  (∀ ps, lazyLibraryPath ps = ps) ∧
  (∀ d ps, llpPrint d ps = llpString d ps) ∧
  (∀ d (a b : List Char), a ≠ [] → a.getLast? ≠ some '/' → ¬ Paths.isabspath b →
      llpString d [.str a, .str b] = .ok (a ++ '/' :: b)) ∧
  (∀ d sub, llpString d (bundled sub) = Paths.joinpath [d, sub]) ∧
  (∀ sh sub, llpShow sh (bundled sub) = sh sub) ∧
  (∀ sh (a : List Char), llpShow sh [.str a] = "LazyLibraryPath(".toList ++ sh a ++ [')']) ∧
  (∀ d ps s, llpString d ps = .ok s → '\x00' ∉ s → llpCconvert d ps = .ok s)

theorem lazyLibraryPathCorrect : LazyLibraryPathCorrect := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro d a b ha hl hb
    cases a with
    | nil => exact absurd rfl ha
    | cons x xs => simp [llpString, Paths.joinpath, Paths.joinStep, hb, hl, Piece.string]
  · intro sh a; simp [llpShow]
  · intro d ps s h hs; simp [llpCconvert, h, hs]

/-! ## `LazyLibrary`, lines 396-561 -/

/-- `(init::InitialDependencies)() = copy(init.dependencies)`, line 396. -/
def initialDependencies {α} (deps : List α) : List α := deps

/-- The state of a `LazyLibrary`. -/
structure LazyLib where
  path : List Piece
  flags : Nat
  deps : List Nat
  hasCallback : Bool
  handle : Nat
  deriving DecidableEq, Repr

/-- `LazyLibrary(path; flags, dependencies, on_load_callback)`, lines 464-476:
`UInt32(flags)`, `handle = C_NULL`. -/
def lazyLibrary (path : List Piece) (flags : Int) (deps : List Nat) (hasCallback : Bool) : R LazyLib := do
  let f ← toInt .u32 flags
  pure ⟨path, f.toNat, initialDependencies deps, hasCallback, 0⟩

/-- `_invoke_on_load_callback(cb) = cb()`, line 480. -/
def invokeOnLoadCallback {α} (cb : Unit → α) : α := cb ()
/-- `_lazy_library_path_string(path) = string(path)`, line 481. -/
def lazyLibraryPathString (shlibdir : List Char) (p : List Piece) : Jl (List Char) := llpString shlibdir p

/-- `show(io, ll)`, lines 484-488. -/
def showLazyLibrary (showPath : List Piece → List Char) (ll : LazyLib) : List Char :=
  "LazyLibrary(".toList ++ showPath ll.path ++ [')']

/-- `add_dependency!(ll, dep)`, lines 509-513. -/
def addDependency (ll : LazyLib) (dep : Nat) : LazyLib := { ll with deps := ll.deps ++ [dep] }

/-- The outcome of `dlopen(ll)`: the result, the new state, and how many times the
load callback ran. -/
structure LoadOutcome where
  result : R Handle
  ll : LazyLib
  callbacks : Nat

/-- `dlopen(ll::LazyLibrary, flags = ll.flags; kwargs...)`, lines 519-558, with
`openDeps` the result of opening every dependency (same keywords) and `openPath` the
`dlopen(string(path), flags; kwargs...)` result. Storing `nothing` into the
`handle::Ptr{Cvoid}` field throws (`convert` has no method). -/
def dlopenLL (openDeps : R Unit) (openPath : R Handle) (ll : LazyLib) : LoadOutcome :=
  if ll.handle == 0 then
    match openDeps with
    | .error e => ⟨.error e, ll, 0⟩
    | .ok () =>
      match openPath with
      | .error e => ⟨.error e, ll, 0⟩
      | .ok none => ⟨.error (.methodError "convert"), ll, 0⟩
      | .ok (some h) => ⟨.ok (some h), { ll with handle := h }, if ll.hasCallback then 1 else 0⟩
  else ⟨.ok (some ll.handle), ll, 0⟩

/-- `dlopen(x::Any)`, line 559. -/
def dlopenAny : R Nat := .error (.typeError "dlopen")
/-- `dlsym(ll, args...) = dlsym(dlopen(ll), args...)`, line 560. -/
def dlsymLL (jlDlsym : Nat → String → Bool → R (Bool × Nat)) (o : LoadOutcome) (s : String)
    (throwError : Bool) : R Handle := do
  let h ← o.result
  dlsym jlDlsym (h.getD 0) s throwError
/-- `dlpath(ll) = dlpath(dlopen(ll))`, line 561. -/
def dlpathLL (pathname : Nat → List UInt8) (o : LoadOutcome) : R (List UInt8) := do
  let h ← o.result
  dlpathHandle pathname (h.getD 0)

def LazyLibraryCorrect : Prop :=
  (∀ (α : Type) (d : List α), initialDependencies d = d) ∧
  (∀ p f d cb, 0 ≤ f → f ≤ 4294967295 → lazyLibrary p f d cb = .ok ⟨p, f.toNat, d, cb, 0⟩) ∧
  (∀ (α : Type) (cb : Unit → α), invokeOnLoadCallback cb = cb ()) ∧
  (∀ d p, lazyLibraryPathString d p = llpString d p) ∧
  (∀ sp ll, showLazyLibrary sp ll = "LazyLibrary(".toList ++ sp ll.path ++ [')']) ∧
  (∀ ll dep, (addDependency ll dep).deps = ll.deps ++ [dep]) ∧
  -- a cached handle is returned without loading anything or running the callback
  (∀ od op ll, ll.handle ≠ 0 → dlopenLL od op ll = ⟨.ok (some ll.handle), ll, 0⟩) ∧
  -- a first successful load caches the handle and runs the callback exactly once
  (∀ op ll h, ll.handle = 0 → op = .ok (some h) →
      let o := dlopenLL (.ok ()) op ll
      o.result = .ok (some h) ∧ o.ll.handle = h ∧ o.callbacks = (if ll.hasCallback then 1 else 0)) ∧
  -- a failing dependency stops the load
  (∀ e op ll, ll.handle = 0 → (dlopenLL (.error e) op ll).result = .error e) ∧
  dlopenAny = .error (.typeError "dlopen") ∧
  (∀ j o s t h, o.result = .ok (some h) → dlsymLL j o s t = dlsym j h s t) ∧
  (∀ pn o h, o.result = .ok (some h) → dlpathLL pn o = dlpathHandle pn h)

theorem lazyLibraryCorrect : LazyLibraryCorrect := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_,
    rfl, ?_, ?_⟩
  · intro p f d cb h1 h2
    simp [lazyLibrary, toInt_u32 f h1 h2, initialDependencies, bind, Except.bind, pure, Except.pure]
  · intro od op ll h; simp [dlopenLL, h]
  · intro op ll h h0 hop; subst hop; simp [dlopenLL, h0]
  · intro e op ll h0; simp [dlopenLL, h0]
  · intro j o s t h ho; simp [dlsymLL, ho, bind, Except.bind]
  · intro pn o h ho; simp [dlpathLL, ho, bind, Except.bind]

/-- Documented (`dlopen` docstring, lines 104-107): with `throw_error=false`, a library
that cannot be found gives `nothing`. `dlopen(::LazyLibrary)` forwards the keyword. -/
def LazyDlopenNothing : Prop :=
  ∀ ll : LazyLib, ll.handle = 0 → (dlopenLL (.ok ()) (.ok none) ll).result = .ok none

theorem lazyDlopenNothing_refuted : ¬ LazyDlopenNothing := by
  intro h
  have := h ⟨[.str "libmissing".toList], 0, [], false, 0⟩ rfl
  simp [dlopenLL] at this


/-! ## Per-method properties -/

def DlsymCorrect_1 : Prop :=
  (∀ j s t, dlsym j 0 s t = argErr "NULL library handle")
theorem dlsymCorrect_1 : DlsymCorrect_1 := by
  have h := dlsymCorrect
  exact h.1

def DlsymCorrect_2 : Prop :=
  (∀ j h s, h ≠ 0 → j h s false = .ok (false, 0) → dlsym j h s false = .ok none)
theorem dlsymCorrect_2 : DlsymCorrect_2 := by
  have h := dlsymCorrect
  exact h.2.1

def DlsymCorrect_3 : Prop :=
  (∀ j h s v t, h ≠ 0 → j h s t = .ok (true, v) → dlsym j h s t = .ok (some v))
theorem dlsymCorrect_3 : DlsymCorrect_3 := by
  have h := dlsymCorrect
  exact h.2.2.1

def DlsymCorrect_4 : Prop :=
  (∀ j h s, h ≠ 0 → j h s false = .ok (false, 0) → dlsymE j h s = .ok 0)
theorem dlsymCorrect_4 : DlsymCorrect_4 := by
  have h := dlsymCorrect
  exact h.2.2.2.1

def DlsymCorrect_5 : Prop :=
  (∀ j h s v, h ≠ 0 → j h s false = .ok (true, v) → dlsymE j h s = .ok v)
theorem dlsymCorrect_5 : DlsymCorrect_5 := by
  have h := dlsymCorrect
  exact h.2.2.2.2

def DlopenCorrect_1 : Prop :=
  (∀ load s flags, 0 ≤ flags → flags ≤ 4294967295 → load s flags.toNat false = .ok 0 →
      dlopenStr load s flags false = .ok none)
theorem dlopenCorrect_1 : DlopenCorrect_1 := by
  have h := dlopenCorrect
  exact h.1

def DlopenCorrect_2 : Prop :=
  (∀ load s flags p t, 0 ≤ flags → flags ≤ 4294967295 → p ≠ 0 → load s flags.toNat t = .ok p →
      dlopenStr load s flags t = .ok (some p))
theorem dlopenCorrect_2 : DlopenCorrect_2 := by
  have h := dlopenCorrect
  exact h.2.1

def DlopenCorrect_3 : Prop :=
  (∀ load s flags t, flags < 0 → dlopenStr load s flags t = .error (.jl (.inexactError "UInt32")))
theorem dlopenCorrect_3 : DlopenCorrect_3 := by
  have h := dlopenCorrect
  exact h.2.2.1

def DlopenCorrect_4 : Prop :=
  (∀ load s flags t, dlopenSym load s flags t = dlopenStr load s flags t)
theorem dlopenCorrect_4 : DlopenCorrect_4 := by
  have h := dlopenCorrect
  exact h.2.2.2.1

def DlopenCorrect_5 : Prop :=
  (∀ c, dlclose c none = none)
theorem dlopenCorrect_5 : DlopenCorrect_5 := by
  have h := dlopenCorrect
  exact h.2.2.2.2.1

def DlopenCorrect_6 : Prop :=
  (∀ c p, dlclose c (some p) = some (0 == c p))
theorem dlopenCorrect_6 : DlopenCorrect_6 := by
  have h := dlopenCorrect
  exact h.2.2.2.2.2.1

def DlopenCorrect_7 : Prop :=
  (∀ (α : Type) (e : Err) (f : Handle → R α), dlopenDo (.error e) f = (.error e, none))
theorem dlopenCorrect_7 : DlopenCorrect_7 := by
  have h := dlopenCorrect
  exact h.2.2.2.2.2.2.1

def DlopenCorrect_8 : Prop :=
  (∀ (α : Type) (h : Handle) (f : Handle → R α), dlopenDo (.ok h) f = (f h, h))
theorem dlopenCorrect_8 : DlopenCorrect_8 := by
  have h := dlopenCorrect
  exact h.2.2.2.2.2.2.2.1

def DlopenCorrect_9 : Prop :=
  (∀ load s flags, 0 ≤ flags → flags ≤ 4294967295 → load s flags.toNat false = .ok 0 →
      dlopenE load s flags = .ok 0)
theorem dlopenCorrect_9 : DlopenCorrect_9 := by
  have h := dlopenCorrect
  exact h.2.2.2.2.2.2.2.2

def DlpathCorrect_1 : Prop :=
  (∀ pn, dlpathHandle pn 0 = argErr "NULL library handle")
theorem dlpathCorrect_1 : DlpathCorrect_1 := by
  have h := dlpathCorrect
  exact h.1

def DlpathCorrect_2 : Prop :=
  (∀ pn h, h ≠ 0 → dlpathHandle pn h = .ok (pn h))
theorem dlpathCorrect_2 : DlpathCorrect_2 := by
  have h := dlpathCorrect
  exact h.2.1

def DlpathCorrect_3 : Prop :=
  (∀ load pn fl name p, 0 ≤ fl → fl ≤ 4294967295 → p ≠ 0 → load name fl.toNat true = .ok p →
      dlpathName load pn fl name = .ok (pn p))
theorem dlpathCorrect_3 : DlpathCorrect_3 := by
  have h := dlpathCorrect
  exact h.2.2.1

def DlpathCorrect_4 : Prop :=
  (∀ c, dllist c = c ())
theorem dlpathCorrect_4 : DlpathCorrect_4 := by
  have h := dlpathCorrect
  exact h.2.2.2

def LazyLibraryPathCorrect_1 : Prop :=
  (∀ ps, lazyLibraryPath ps = ps)
theorem lazyLibraryPathCorrect_1 : LazyLibraryPathCorrect_1 := by
  have h := lazyLibraryPathCorrect
  exact h.1

def LazyLibraryPathCorrect_2 : Prop :=
  (∀ d ps, llpPrint d ps = llpString d ps)
theorem lazyLibraryPathCorrect_2 : LazyLibraryPathCorrect_2 := by
  have h := lazyLibraryPathCorrect
  exact h.2.1

def LazyLibraryPathCorrect_3 : Prop :=
  (∀ d (a b : List Char), a ≠ [] → a.getLast? ≠ some '/' → ¬ Paths.isabspath b →
      llpString d [.str a, .str b] = .ok (a ++ '/' :: b))
theorem lazyLibraryPathCorrect_3 : LazyLibraryPathCorrect_3 := by
  have h := lazyLibraryPathCorrect
  exact h.2.2.1

def LazyLibraryPathCorrect_4 : Prop :=
  (∀ d sub, llpString d (bundled sub) = Paths.joinpath [d, sub])
theorem lazyLibraryPathCorrect_4 : LazyLibraryPathCorrect_4 := by
  have h := lazyLibraryPathCorrect
  exact h.2.2.2.1

def LazyLibraryPathCorrect_5 : Prop :=
  (∀ sh sub, llpShow sh (bundled sub) = sh sub)
theorem lazyLibraryPathCorrect_5 : LazyLibraryPathCorrect_5 := by
  have h := lazyLibraryPathCorrect
  exact h.2.2.2.2.1

def LazyLibraryPathCorrect_6 : Prop :=
  (∀ sh (a : List Char), llpShow sh [.str a] = "LazyLibraryPath(".toList ++ sh a ++ [')'])
theorem lazyLibraryPathCorrect_6 : LazyLibraryPathCorrect_6 := by
  have h := lazyLibraryPathCorrect
  exact h.2.2.2.2.2.1

def LazyLibraryPathCorrect_7 : Prop :=
  (∀ d ps s, llpString d ps = .ok s → '\x00' ∉ s → llpCconvert d ps = .ok s)
theorem lazyLibraryPathCorrect_7 : LazyLibraryPathCorrect_7 := by
  have h := lazyLibraryPathCorrect
  exact h.2.2.2.2.2.2

def LazyLibraryCorrect_1 : Prop :=
  (∀ (α : Type) (d : List α), initialDependencies d = d)
theorem lazyLibraryCorrect_1 : LazyLibraryCorrect_1 := by
  have h := lazyLibraryCorrect
  exact h.1

def LazyLibraryCorrect_2 : Prop :=
  (∀ p f d cb, 0 ≤ f → f ≤ 4294967295 → lazyLibrary p f d cb = .ok ⟨p, f.toNat, d, cb, 0⟩)
theorem lazyLibraryCorrect_2 : LazyLibraryCorrect_2 := by
  have h := lazyLibraryCorrect
  exact h.2.1

def LazyLibraryCorrect_3 : Prop :=
  (∀ (α : Type) (cb : Unit → α), invokeOnLoadCallback cb = cb ())
theorem lazyLibraryCorrect_3 : LazyLibraryCorrect_3 := by
  have h := lazyLibraryCorrect
  exact h.2.2.1

def LazyLibraryCorrect_4 : Prop :=
  (∀ d p, lazyLibraryPathString d p = llpString d p)
theorem lazyLibraryCorrect_4 : LazyLibraryCorrect_4 := by
  have h := lazyLibraryCorrect
  exact h.2.2.2.1

def LazyLibraryCorrect_5 : Prop :=
  (∀ sp ll, showLazyLibrary sp ll = "LazyLibrary(".toList ++ sp ll.path ++ [')'])
theorem lazyLibraryCorrect_5 : LazyLibraryCorrect_5 := by
  have h := lazyLibraryCorrect
  exact h.2.2.2.2.1

def LazyLibraryCorrect_6 : Prop :=
  (∀ ll dep, (addDependency ll dep).deps = ll.deps ++ [dep])
theorem lazyLibraryCorrect_6 : LazyLibraryCorrect_6 := by
  have h := lazyLibraryCorrect
  exact h.2.2.2.2.2.1

def LazyLibraryCorrect_7 : Prop :=
  (∀ od op ll, ll.handle ≠ 0 → dlopenLL od op ll = ⟨.ok (some ll.handle), ll, 0⟩)
theorem lazyLibraryCorrect_7 : LazyLibraryCorrect_7 := by
  have h := lazyLibraryCorrect
  exact h.2.2.2.2.2.2.1

def LazyLibraryCorrect_8 : Prop :=
  (∀ op ll h, ll.handle = 0 → op = .ok (some h) →
      let o := dlopenLL (.ok ()) op ll
      o.result = .ok (some h) ∧ o.ll.handle = h ∧ o.callbacks = (if ll.hasCallback then 1 else 0))
theorem lazyLibraryCorrect_8 : LazyLibraryCorrect_8 := by
  have h := lazyLibraryCorrect
  exact h.2.2.2.2.2.2.2.1

def LazyLibraryCorrect_9 : Prop :=
  (∀ e op ll, ll.handle = 0 → (dlopenLL (.error e) op ll).result = .error e) ∧
  dlopenAny = .error (.typeError "dlopen")
theorem lazyLibraryCorrect_9 : LazyLibraryCorrect_9 := by
  have h := lazyLibraryCorrect
  exact ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

def LazyLibraryCorrect_10 : Prop :=
  (∀ j o s t h, o.result = .ok (some h) → dlsymLL j o s t = dlsym j h s t)
theorem lazyLibraryCorrect_10 : LazyLibraryCorrect_10 := by
  have h := lazyLibraryCorrect
  exact h.2.2.2.2.2.2.2.2.2.2.1

def LazyLibraryCorrect_11 : Prop :=
  (∀ pn o h, o.result = .ok (some h) → dlpathLL pn o = dlpathHandle pn h)
theorem lazyLibraryCorrect_11 : LazyLibraryCorrect_11 := by
  have h := lazyLibraryCorrect
  exact h.2.2.2.2.2.2.2.2.2.2.2

end JuliaLean.IOCov.Libdl
