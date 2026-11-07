import JuliaLean.base.initdefs
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.InitDefs

open JuliaLean.RuntimeCov

/-! ## Properties -/

theorem splitOn_no_sep (c : Char) : ∀ s : Str, c ∉ s → splitOn c s = [s]
  | [] , _ => rfl
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    have hxs : c ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hx, splitOn_no_sep c xs hxs]

theorem splitOn_append_sep (c : Char) (t : Str) : ∀ s : Str, c ∉ s →
    splitOn c (s ++ c :: t) = s :: splitOn c t
  | [], _ => by simp [splitOn]
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    have hxs : c ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitOn, hx, splitOn_append_sep c t xs hxs]

/-- The documented `JULIA_DEPOT_PATH` expansion (manual, "JULIA_DEPOT_PATH"):
unset gives the user depot then the bundled depots; the empty string gives no
depot; `"/foo:"` replaces the user depot; `":/foo"` appends after the full
default list; `":"` is the full default list. -/
def DepotPathDocumented : Prop :=
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 : Str), u ≠ b1 → u ≠ b2 → b1 ≠ b2 →
      initDepotPath none sep eu u b1 b2 = [u, b1, b2]) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 : Str), initDepotPath (some []) sep eu u b1 b2 = []) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 foo : Str), foo ≠ [] → sep ∉ foo →
      eu foo ≠ b1 → eu foo ≠ b2 → b1 ≠ b2 →
      initDepotPath (some (foo ++ [sep])) sep eu u b1 b2 = [eu foo, b1, b2]) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 foo : Str), foo ≠ [] → sep ∉ foo →
      eu foo ≠ b1 → eu foo ≠ b2 → b1 ≠ b2 →
      initDepotPath (some (sep :: foo)) sep eu u b1 b2 = [u, b1, b2, eu foo]) ∧
  (∀ (sep : Char) (eu : Str → Str) (u b1 b2 : Str), b1 ≠ b2 →
      initDepotPath (some [sep]) sep eu u b1 b2 = [u, b1, b2])

theorem depotPathDocumented_proven : DepotPathDocumented := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sep eu u b1 b2 h1 h2 h3
    simp [initDepotPath, appendBundled, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · intro sep eu u b1 b2; simp [initDepotPath]
  · intro sep eu u b1 b2 foo hf hs h1 h2 h3
    have hsplit : splitOn sep (foo ++ [sep]) = [foo, []] := by
      rw [splitOn_append_sep sep [] foo hs]; rfl
    have hne : (foo ++ [sep]).isEmpty = false := by cases foo <;> simp_all
    have hfe : foo.isEmpty = false := by cases foo <;> simp_all
    simp only [initDepotPath, hne, hsplit, Bool.false_eq_true, ↓reduceIte]
    simp [depotLoop, hfe, appendBundled, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · intro sep eu u b1 b2 foo hf hs h1 h2 h3
    have hsplit : splitOn sep (sep :: foo) = [[], foo] := by
      simp [splitOn, splitOn_no_sep sep foo hs]
    have hfe : foo.isEmpty = false := by cases foo <;> simp_all
    simp only [initDepotPath, hsplit, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    simp [depotLoop, hfe, appendBundled, h1, h2, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · intro sep eu u b1 b2 h3
    have hsplit : splitOn sep [sep] = [[], []] := by simp [splitOn]
    simp only [initDepotPath, hsplit, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    simp [depotLoop, appendBundled, Ne.symm h3]

/-- Invariant: `init_depot_path` never lists a depot twice (every push is
guarded by `path in DEPOT_PATH`). -/
def DepotPathNoDuplicates : Prop :=
  ∀ (env : Option Str) (sep : Char) (eu : Str → Str) (u b1 b2 : Str),
    (initDepotPath env sep eu u b1 b2).Nodup

/-- `JULIA_DEPOT_PATH=":$HOME/.julia"` lists the user depot twice. -/
theorem depotPathNoDuplicates_refuted : ¬ DepotPathNoDuplicates := by
  intro h
  have := h (some [':', 'u']) ':' id ['u'] ['a'] ['b']
  revert this; decide

/-- The documented `JULIA_LOAD_PATH` expansion (manual, "JULIA_LOAD_PATH"):
the empty string gives an empty `LOAD_PATH`; `":"` gives the default load path;
`"/foo/bar:"` prepends `/foo/bar` to the defaults; unset gives the defaults. -/
def LoadPathDocumented : Prop :=
  (∀ sep cp (eu : Str → Str), parseLoadPath sep cp eu [] = []) ∧
  (∀ sep cp (eu : Str → Str), parseLoadPath sep cp eu [sep] = defaultLoadPath) ∧
  (∀ sep cp (eu : Str → Str) (foo : Str), foo ≠ [] → sep ∉ foo → foo ≠ ['@', '.'] →
      eu foo ∉ defaultLoadPath →
      parseLoadPath sep cp eu (foo ++ [sep]) = eu foo :: defaultLoadPath) ∧
  (∀ sep cp (eu : Str → Str), initLoadPath sep cp eu none = defaultLoadPath) ∧
  (∀ sep cp (eu : Str → Str) s, initLoadPath sep cp eu (some s) = parseLoadPath sep cp eu s)

theorem loadPathDocumented_proven : LoadPathDocumented := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sep cp eu; simp [parseLoadPath]
  · intro sep cp eu
    have hsplit : splitOn sep [sep] = [[], []] := by simp [splitOn]
    simp only [parseLoadPath, hsplit, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true,
      ↓reduceIte, List.foldl_cons, List.foldl_nil]
    decide
  · intro sep cp eu foo hf hs hd hn
    have hsplit : splitOn sep (foo ++ [sep]) = [foo, []] := by
      rw [splitOn_append_sep sep [] foo hs]; rfl
    have hne : (foo ++ [sep]).isEmpty = false := by cases foo <;> simp_all
    have hfe : foo.isEmpty = false := by cases foo <;> simp_all
    simp only [parseLoadPath, hne, hsplit, Bool.false_eq_true, ↓reduceIte, List.foldl_cons,
      List.foldl_nil, hfe, hd]
    simp only [defaultLoadPath] at hn ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨h1, h2, h3⟩ := hn
    have g1 : ¬ ['@'] = eu foo := fun e => h1 e.symm
    have g2 : ¬ ['@', 'v', '#', '.', '#'] = eu foo := fun e => h2 e.symm
    have g3 : ¬ ['@', 's', 't', 'd', 'l', 'i', 'b'] = eu foo := fun e => h3 e.symm
    simp [h1, h2, h3, g1, g2, g3]
  · intro sep cp eu; rfl
  · intro sep cp eu s; rfl

/-- The `LOAD_PATH` docstring: `@name` (other than the special `@`, `@.`,
`@temp`, `@stdlib` and `@script[/path]` forms) refers to the named environment
`name` in the depots. -/
def LoadPathNamedEnv : Prop :=
  ∀ (e : ExpandEnv) (name : Str),
    name ∉ [[], ['.'], ['t', 'e', 'm', 'p'], ['s', 't', 'd', 'l', 'i', 'b'], ['s', 'c', 'r', 'i', 'p', 't']] →
    ¬ (['s', 'c', 'r', 'i', 'p', 't', '/'].isPrefixOf name) → '#' ∉ name →
    loadPathExpand e ('@' :: name) = namedSearch e name

/-- `@scripts` is taken for `@script` followed by the relative path `s`. -/
theorem loadPathNamedEnv_refuted : ¬ LoadPathNamedEnv := by
  intro h
  have := h scriptsEnv ['s', 'c', 'r', 'i', 'p', 't', 's'] (by decide) (by decide) (by decide)
  revert this; decide

/-- Further documented behaviour of `base/initdefs.jl`. -/
def InitDefsBodies : Prop :=
  -- exit codes must fit in `Int32`
  (∀ n : Int, exit n = .ok n ↔ (-2147483648 ≤ n ∧ n ≤ 2147483647)) ∧
  exit0 = .ok 0 ∧
  (∀ (τ : Type) (s : Option τ), foregroundTask s = s) ∧
  -- the foreground task is `current_task()` inside and restored afterwards
  (∀ (τ : Type) (prev : Option τ) (c : τ), asForegroundTask prev c = (some c, prev)) ∧
  (∀ b, isinteractive b = b) ∧
  -- bundled depots are appended once, after the existing entries
  (∀ (b1 b2 : Str) (dp : List Str), dp.Nodup → b1 ≠ b2 → (appendBundled b1 b2 dp).Nodup) ∧
  (∀ (b1 b2 : Str) (dp : List Str), dp.IsPrefix (appendBundled b1 b2 dp)) ∧
  -- `current_project` only returns an existing project file in the walk
  (∀ names join isf dn home fuel dir p, currentProjectAt names join isf dn home fuel dir = some p →
      isf p = true) ∧
  (∀ s, currentProject none s = none) ∧
  (∀ c : Char, cmdSuppressesProgram c = true ↔ c = 'e' ∨ c = 'E') ∧
  -- `load_path_expand` special forms
  (∀ e : ExpandEnv, loadPathExpand e kAt = e.activeProjectNoSearch) ∧
  (∀ e : ExpandEnv, loadPathExpand e kDot = e.currentProject) ∧
  (∀ e : ExpandEnv, loadPathExpand e kTemp = some e.tempdir) ∧
  (∀ e : ExpandEnv, loadPathExpand e kStdlib = some e.stdlib) ∧
  (∀ e : ExpandEnv, e.programFile = none → loadPathExpand e kScript = none) ∧
  (∀ (e : ExpandEnv) (pf : Str), e.programFile = some pf →
      loadPathExpand e kScript = e.currentProjectAt (e.dirname pf)) ∧
  -- a named environment found in a depot is a project file there
  (∀ (e : ExpandEnv) (name p : Str), e.depots ≠ [] → namedSearch e name = some p →
      (∃ d ∈ e.depots, ∃ q ∈ e.projectNames, p = e.absJoin (e.envDir d name) q ∧
        e.isfileCS p = true) ∨
      (∃ d ds, e.depots = d :: ds ∧ e.initNamedEnv (e.newNamedEnvPath d name) = some p)) ∧
  (∀ e : ExpandEnv, e.depots = [] → ∀ name, namedSearch e name = none) ∧
  loadPathExpandNothing = none ∧
  (∀ ex au, initActiveProject none none ex au = none) ∧
  (∀ env ex au, initActiveProject (some []) env ex au = none) ∧
  (∀ w p, initNamedEnv w p = some p ↔ w = true) ∧
  (∀ ex isf isp isn wp lp, activeProject none ex isf isp isn wp lp false = none) ∧
  (∀ p cbs, (setActiveProject p cbs).1 = p ∧ (setActiveProject p cbs).2 = cbs) ∧
  (∀ a m, activeManifest none a m = (a.bind m)) ∧
  (∀ p a m, activeManifest (some p) a m = m p) ∧
  (∀ ex lp, (loadPath ex lp).Nodup) ∧
  -- atexit hooks run last-registered first, then registration fails
  (∀ s f s', atexit s f = .ok s' → s'.hooks = f :: s.hooks) ∧
  (∀ s f, s.finished = true → ∃ e, atexit s f = .error e) ∧
  (∀ hm c s, (runAtexitHooks hm c s).1.map Prod.fst = s.hooks ∧ (runAtexitHooks hm c s).2.finished = true) ∧
  (∀ hm c f1 f2 s1 s2, atexit ⟨[], false⟩ f1 = .ok s1 → atexit s1 f2 = .ok s2 →
      (runAtexitHooks hm c s2).1.map Prod.fst = [f2, f1]) ∧
  (∀ hm c s, atexitImpl hm c s = runAtexitHooks hm c s) ∧
  (∀ hs f, postoutput hs f = f :: hs) ∧
  (∀ hs, runPostoutput hs = (hs, [])) ∧
  (∀ hs f, atDisableLibraryThreading true hs f = (hs ++ [f], [])) ∧
  (∀ hs f, (atDisableLibraryThreading false hs f).2 = f :: hs.reverse)

theorem nodup_append_single (x : Str) : ∀ l : List Str, l.Nodup → x ∉ l → (l ++ [x]).Nodup
  | [], _, _ => by simp
  | a :: l, h, hx => by
    rw [List.nodup_cons] at h
    simp only [List.cons_append, List.nodup_cons]
    refine ⟨?_, nodup_append_single x l h.2 (fun m => hx (List.mem_cons_of_mem _ m))⟩
    intro hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact h.1 hm
    · simp at hm; subst hm; exact hx (by simp)

theorem pushUnique_nodup (x : Str) (l : List Str) (h : l.Nodup) :
    (if x ∈ l then l else l ++ [x]).Nodup := by
  split
  · exact h
  · rename_i hm; exact nodup_append_single x l h hm

theorem appendBundled_nodup (b1 b2 : Str) (dp : List Str) (h : dp.Nodup) (_hb : b1 ≠ b2) :
    (appendBundled b1 b2 dp).Nodup :=
  pushUnique_nodup b2 _ (pushUnique_nodup b1 dp h)

theorem appendBundled_prefix (b1 b2 : Str) (dp : List Str) : dp.IsPrefix (appendBundled b1 b2 dp) := by
  unfold appendBundled
  simp only
  split <;> split <;> simp

theorem currentProjectAt_file (names : List Str) (join : Str → Str → Str) (isf : Str → Bool)
    (dn : Str → Str) (home : Str) : ∀ (fuel : Nat) (dir p : Str),
    currentProjectAt names join isf dn home fuel dir = some p → isf p = true
  | 0, _, _, h => by simp [currentProjectAt] at h
  | fuel + 1, dir, p, h => by
    simp only [currentProjectAt] at h
    split at h
    · rename_i q hq
      simp at h; subst h
      have := List.find?_some hq; simpa using this
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact currentProjectAt_file names join isf dn home fuel _ p h

theorem namedSearch_go (e : ExpandEnv) (name p : Str) : ∀ ds : List Str,
    namedSearch.go e name ds = some p →
    (∃ d ∈ ds, ∃ q ∈ e.projectNames, p = e.absJoin (e.envDir d name) q ∧ e.isfileCS p = true) ∨
    (match e.depots with | [] => none | d :: _ => e.initNamedEnv (e.newNamedEnvPath d name)) = some p
  | [], h => by
    right
    cases hdepots : e.depots <;> simpa [namedSearch.go, hdepots] using h
  | d :: ds, h => by
    simp only [namedSearch.go] at h
    split at h
    · rcases namedSearch_go e name p ds h with ⟨d', hd, q, hq, h1⟩ | h2
      · exact Or.inl ⟨d', List.mem_cons_of_mem _ hd, q, hq, h1⟩
      · exact Or.inr h2
    · split at h
      · rename_i q hq
        simp at h; subst h
        have hfq := List.find?_some hq
        exact Or.inl ⟨d, by simp, q, List.mem_of_find?_eq_some hq, rfl, by simpa using hfq⟩
      · rcases namedSearch_go e name p ds h with ⟨d', hd, q, hq, h1⟩ | h2
        · exact Or.inl ⟨d', List.mem_cons_of_mem _ hd, q, hq, h1⟩
        · exact Or.inr h2

theorem loadPath_nodup (ex : Str → Option Str) (lp : List Str) : (loadPath ex lp).Nodup := by
  unfold loadPath
  suffices ∀ (acc : List Str), acc.Nodup → (lp.foldl (fun paths env => match ex env with
      | some p => if p ∈ paths then paths else paths ++ [p]
      | none => paths) acc).Nodup from this [] List.nodup_nil
  induction lp with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    split
    · split
      · exact h
      · rename_i p _ hm
        exact nodup_append_single p _ h hm
    · exact h

theorem initDefsBodies_proven : InitDefsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [exit, JuliaLean.IntTy.min, JuliaLean.IntTy.max, JuliaLean.IntTy.signed,
      JuliaLean.IntTy.bits]
    split <;> simp_all <;> omega
  · rfl
  · intro _ _; rfl
  · intro _ _ _; rfl
  · intro _; rfl
  · intro b1 b2 dp h hb; exact appendBundled_nodup b1 b2 dp h hb
  · intro b1 b2 dp; exact appendBundled_prefix b1 b2 dp
  · intro names join isf dn home fuel dir p h; exact currentProjectAt_file names join isf dn home fuel dir p h
  · intro _; rfl
  · intro c; simp [cmdSuppressesProgram]
  · intro e; simp [loadPathExpand, kAt]
  · intro e; simp [loadPathExpand, kAt, kDot]
  · intro e; simp [loadPathExpand, kAt, kDot, kTemp]
  · intro e; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib]
  · intro e h; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib, kScript, h]
  · intro e pf h; simp [loadPathExpand, kAt, kDot, kTemp, kStdlib, kScript, h]
  · intro e name p hd h
    rcases namedSearch_go e name p e.depots h with h1 | h2
    · exact Or.inl h1
    · right
      cases hds : e.depots with
      | nil => exact absurd hds hd
      | cons d ds => rw [hds] at h2; exact ⟨d, ds, rfl, h2⟩
  · intro e hd name
    simp only [namedSearch]
    rw [hd]; simp [namedSearch.go, hd]
  · rfl
  · intro _ _; rfl
  · intro env ex au; cases env <;> simp [initActiveProject]
  · intro w p; cases w <;> simp [initNamedEnv]
  · intro ex isf isp isn wp lp; simp [activeProject]
  · intro p cbs; exact ⟨rfl, rfl⟩
  · intro a m; cases a <;> rfl
  · intro p a m; rfl
  · intro ex lp; exact loadPath_nodup ex lp
  · intro s f s' h
    unfold atexit at h
    split at h
    · simp at h
    · simp at h; subst h; rfl
  · intro s f h; simp [atexit, h]
  · intro hm c s; simp [runAtexitHooks, Function.comp_def]
  · intro hm c f1 f2 s1 s2 h1 h2
    simp [atexit] at h1
    subst h1
    simp [atexit] at h2
    subst h2
    rfl
  · intro _ _ _; rfl
  · intro _ _; rfl
  · intro _; rfl
  · intro _ _; rfl
  · intro hs f; simp [atDisableLibraryThreading, disableLibraryThreading]
end JuliaLean.RuntimeCov.InitDefs
end
