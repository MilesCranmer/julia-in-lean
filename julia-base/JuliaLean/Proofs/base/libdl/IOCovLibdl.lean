import JuliaLean.base.libdl
import JuliaLean.Proofs.base.io.IOCovCommon
import JuliaLean.base.path


section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Libdl

open JuliaLean JuliaLean.IOCov

def DlsymCorrect : Prop :=
  (∀ j s t, dlsym j 0 s t = argErr "NULL library handle") ∧
  (∀ j h s, h ≠ 0 → j h s false = .ok (false, 0) → dlsym j h s false = .ok none) ∧
  (∀ j h s v t, h ≠ 0 → j h s t = .ok (true, v) → dlsym j h s t = .ok (some v)) ∧
  (∀ j h s, h ≠ 0 → j h s false = .ok (false, 0) → dlsymE j h s = .ok 0) ∧
  (∀ j h s v, h ≠ 0 → j h s false = .ok (true, v) → dlsymE j h s = .ok v)

theorem dlsymCorrect : DlsymCorrect := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [dlsym, dlsymE, bind, Except.bind, pure, Except.pure]

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
end
