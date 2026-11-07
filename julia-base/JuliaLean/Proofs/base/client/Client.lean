import JuliaLean.base.client
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.Client

open JuliaLean.RuntimeCov

/-! ## Properties -/

def ClientBodies : Prop :=
  -- `repl_color` returns the environment's color if it names one, else the default
  (∀ env tp hk d, hk (replColor env tp hk d) = true ∨ replColor env tp hk d = d) ∧
  (∀ env tp hk d, tp env = none → hk (.sym env) = true → replColor env tp hk d = .sym env) ∧
  (∀ env tp hk d n, tp env = some n → hk (.int n) = true → replColor env tp hk d = .int n) ∧
  (∀ env tp hk s, namedColor env tp hk s = replColor (env s.1) tp hk s.2) ∧
  (∀ tc env tp hk s, colorCode tc env tp hk s = tc (namedColor env tp hk s)) ∧
  colorSettings.length = 8 ∧
  -- shell mode: `cd` with no argument goes home, `cd -` needs OLDPWD,
  -- more than one argument is an error, other commands run through the shell
  (∀ w o home pwd sh esc, replCmd (.cmd ["cd"]) w o home pwd sh esc = .ok (.cd home pwd)) ∧
  (∀ w home pwd sh esc, ∃ e, replCmd (.cmd ["cd", "-"]) w none home pwd sh esc = .error e) ∧
  (∀ w o home pwd sh esc, replCmd (.cmd ["cd", "-"]) w (some o) home pwd sh esc = .ok (.cd o pwd)) ∧
  (∀ w o home pwd sh esc rest, 1 < rest.length →
      ∃ e, replCmd (.cmd ("cd" :: rest)) w o home pwd sh esc = .error e) ∧
  (∀ w o home pwd sh esc, ∃ e, replCmd (.cmd []) w o home pwd sh esc = .error e) ∧
  (∀ w o home pwd sh esc, ∃ e, replCmd .notACmd w o home pwd sh esc = .error e) ∧
  (∀ o home pwd sh esc x rest, x ≠ "cd" →
      replCmd (.cmd (x :: rest)) false o home pwd sh esc = .ok (.runShell (sh ++ ["-c", esc (x :: rest)]))) ∧
  -- frames from C or unknown stop the search
  (∀ fr rest f, (fr.unknown || fr.fromC) = true → ipMatchesFunc (fr :: rest) f = false) ∧
  (∀ fs f, ipMatchesFunc fs f = true → ∃ fr ∈ fs, fr.func = f) ∧
  (∀ f, isDriverEntry f = true → f.fromC = false) ∧
  (∀ f, isDriverMachinery f = true → f.modBaseOrCore = true) ∧
  -- scrubbing keeps a prefix of the backtrace
  (∀ bt, (scrubBacktrace bt).IsPrefix bt) ∧
  (∀ bt, findLastEntry bt = none → scrubBacktrace bt = bt) ∧
  (∀ (ε : Type) (st : List (ε × List Frame)), (scrubStack st).map Prod.fst = st.map Prod.fst) ∧
  (∀ bt, istrivialerror [(true, bt)] = false) ∧
  (∀ s, ∃ r, displayError s = "ERROR: " ++ r) ∧
  (∀ (α β : Type) (f : α → β) x, entryDelegate f x = f x) ∧
  -- a parse error at the end of a multi-statement input is returned alone
  (∀ cs, parseInputLineCore (.toplevel (cs ++ [.error])) = .error) ∧
  (∀ cs, parseInputLineCore (.toplevel (cs ++ [.incomplete])) = .incomplete) ∧
  (∀ p d s, parseInputLine p d s = parseInputLineCore (p s)) ∧
  (∀ ds, evalUserInput .ok ds = 0) ∧
  (∀ ds, evalUserInput .throws ds ≤ 3) ∧
  -- `exec_options`: `-e`/`-E` suppress the program and the REPL; a program
  -- file is the first argument; no arguments and no `-e` start a REPL
  (∀ args cmds s, ('e', s) ∈ cmds → (∀ c ∈ cmds, c.1 ≠ 'B') → (execOptions args cmds).repl = false) ∧
  (∀ a rest, execOptions (a :: rest) [] = ⟨a, rest, false, false⟩) ∧
  (execOptions [] []).repl = true ∧
  (∀ args s, (execOptions args [('B', s)]).bugReport = true) ∧
  -- startup files
  (∀ e p1 p2 isf p, globalStartupFile e p1 p2 isf = some p → isf p = true) ∧
  (∀ ds si isf p, localStartupFile ds si isf = some p → isf p = true) ∧
  (∀ si isf, localStartupFile [] si isf = none) ∧
  (∀ g l, loadJuliaStartup g l = g.toList ++ l.toList) ∧
  (∀ hs f, atreplinit hs f = f :: hs) ∧
  (∀ hs, runReplHooks hs = hs) ∧
  (∀ r, loadInteractiveUtils true r = some ()) ∧
  (∀ r, loadREPL r = some () ↔ r = true) ∧
  (∀ q, runMainRepl false true q true = .std) ∧
  (∀ i q r, runMainRepl true i q r = .fallback false) ∧
  (∀ cs, fallbackStatements (.toplevel cs) = cs) ∧
  (∀ p acc ls, (accumulateLines p acc ls).2.length ≤ ls.length) ∧
  (∀ t prev this, (runStdRepl t prev this).2.2 = prev) ∧
  (∀ (α β : Type) (p : α → β) x, internalParse p x = p x) ∧
  (∀ o, shouldUseMainEntrypoint false o = false) ∧
  (∀ s fresh, (sessionCancelSource (some s) fresh).1 = s) ∧
  (∀ fresh, sessionCancelSource none fresh = (fresh, some fresh)) ∧
  (∀ cur fresh child, (newEvaluationCancelSource cur fresh child).1.2 = (sessionCancelSource cur fresh).1) ∧
  (∀ cur, (cancelSessionWork cur).2.2 = none ∧ ((cancelSessionWork cur).1 = true ↔ cur.isSome)) ∧
  (∀ u, initFrontend u = !u) ∧
  (∀ r c, start true r c = 1) ∧
  (∀ c, start false none c = (c 0).getD 1) ∧
  (∀ i, replBanner 0 i = .no ∧ replBanner 1 i = .yes ∧ replBanner 2 i = .short) ∧
  (replBanner (-1) true = .yes ∧ replBanner (-1) false = .no) ∧
  (∀ args, ∃ e, mainMacro true true args = .error e) ∧
  (∀ args, mainMacro false false args = .ok (true, if args.isEmpty then none else some args))

theorem accumulateLines_len (p : String → Parsed) : ∀ (acc : String) (ls : List String),
    (accumulateLines p acc ls).2.length ≤ ls.length
  | _, [] => by simp [accumulateLines]
  | acc, l :: ls => by
    simp only [accumulateLines]
    split
    · exact Nat.le_succ_of_le (accumulateLines_len p _ ls)
    · simp

theorem ipMatchesFunc_mem : ∀ (fs : List Frame) (f : String), ipMatchesFunc fs f = true →
    ∃ fr ∈ fs, fr.func = f
  | [], _, h => by simp [ipMatchesFunc] at h
  | fr :: rest, f, h => by
    simp only [ipMatchesFunc] at h
    split at h
    · simp at h
    · split at h
      · rename_i he; exact ⟨fr, by simp, he⟩
      · obtain ⟨g, hg, he⟩ := ipMatchesFunc_mem rest f h
        exact ⟨g, List.mem_cons_of_mem _ hg, he⟩

theorem execScan_e (cmds : List (Char × String)) : ∀ (s : String) (p r : Bool),
    ('e', s) ∈ cmds → (∀ c ∈ cmds, c.1 ≠ 'B') →
    ∃ p', execOptions.scan cmds p r = some (p', false) := by
  induction cmds with
  | nil => intro s p r h; simp at h
  | cons c cs ih =>
    intro s p r hm hb
    obtain ⟨ch, arg⟩ := c
    have hb' : ∀ c ∈ cs, c.1 ≠ 'B' := fun c hc => hb c (List.mem_cons_of_mem _ hc)
    have hch : ch ≠ 'B' := hb (ch, arg) (by simp)
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [execOptions.scan]
    by_cases he : (ch = 'e' || ch = 'E') = true
    · simp only [he, ↓reduceIte]
      -- after an `-e` the REPL flag stays false through the rest of the scan
      clear hm ih
      suffices ∀ (l : List (Char × String)) (p : Bool), (∀ c ∈ l, c.1 ≠ 'B') →
          ∃ p', execOptions.scan l p false = some (p', false) from this cs false hb'
      intro l
      induction l with
      | nil => intro p _; exact ⟨p, rfl⟩
      | cons d ds ihd =>
        intro p hd
        obtain ⟨dh, da⟩ := d
        have hdB : dh ≠ 'B' := hd (dh, da) (by simp)
        have hds : ∀ c ∈ ds, c.1 ≠ 'B' := fun c hc => hd c (List.mem_cons_of_mem _ hc)
        simp only [execOptions.scan]
        by_cases hde : (dh = 'e' || dh = 'E') = true
        · simp only [hde, ↓reduceIte]; exact ihd false hds
        · simp only [hde, Bool.false_eq_true, ↓reduceIte, hdB]
          exact ihd p hds
    · simp only [he, Bool.false_eq_true, ↓reduceIte, hch]
      rcases hm with ⟨h1, _⟩ | hm
      · subst h1; simp at he
      · exact ih s p r hm hb'

theorem clientBodies_proven : ClientBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro env tp hk d
    unfold replColor
    by_cases h : hk (parseColor env tp) = true <;> simp [h]
  · intro env tp hk d h1 h2; simp [replColor, parseColor, h1, h2]
  · intro env tp hk d n h1 h2; simp [replColor, parseColor, h1, h2]
  · intro _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · rfl
  · intro w o home pwd sh esc; simp [replCmd]
  · intro w home pwd sh esc; simp [replCmd]
  · intro w o home pwd sh esc; simp [replCmd]
  · intro w o home pwd sh esc rest h; simp [replCmd, h]
  · intro w o home pwd sh esc; simp [replCmd]
  · intro w o home pwd sh esc; simp [replCmd]
  · intro o home pwd sh esc x rest hx; simp [replCmd, hx]
  · intro fr rest f h; simp [ipMatchesFunc, h]
  · intro fs f h; exact ipMatchesFunc_mem fs f h
  · intro f h; simp [isDriverEntry] at h; exact h.1
  · intro f h; simp [isDriverMachinery] at h; exact h.1.2
  · intro bt
    unfold scrubBacktrace
    split
    · exact List.prefix_refl bt
    · rename_i i _
      have h1 : (popMachinery (bt.take i)).IsPrefix (bt.take i) := by
        unfold popMachinery
        have := List.dropWhile_suffix isDriverMachinery (l := (bt.take i).reverse)
        have h2 := List.reverse_prefix.mpr this
        simpa using h2
      exact h1.trans (List.take_prefix i bt)
  · intro bt h; simp [scrubBacktrace, h]
  · intro ε st; simp [scrubStack]
  · intro bt; simp [istrivialerror]
  · intro s; exact ⟨s ++ "\n", by simp [displayError, String.append_assoc]⟩
  · intro _ _ _ _; rfl
  · intro cs; simp [parseInputLineCore, Parsed.isBad]
  · intro cs; simp [parseInputLineCore, Parsed.isBad]
  · intro _ _ _; rfl
  · intro ds; rfl
  · intro ds; exact Nat.min_le_left _ _
  · intro args cmds s hm hb
    obtain ⟨p', hp⟩ := execScan_e cmds s (!args.isEmpty) (!(!args.isEmpty)) hm hb
    simp only [execOptions, hp]
    split <;> rfl
  · intro a rest; rfl
  · rfl
  · intro args s; simp [execOptions, execOptions.scan]
  · intro e p1 p2 isf p h
    unfold globalStartupFile at h
    split at h
    · rename_i hc; simp at h hc; subst h; exact hc.2
    · split at h
      · simp at h
      · split at h
        · simp at h; subst h; assumption
        · simp at h
  · intro ds si isf p h
    unfold localStartupFile at h
    split at h
    · simp at h
    · split at h
      · simp at h; subst h; assumption
      · simp at h
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _; rfl
  · intro r; simp [loadInteractiveUtils]
  · intro r; cases r <;> simp [loadREPL]
  · intro q; rfl
  · intro i q r; simp [runMainRepl]
  · intro _; rfl
  · intro p acc ls; exact accumulateLines_len p acc ls
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro o; simp [shouldUseMainEntrypoint]
  · intro _ _; rfl
  · intro _; rfl
  · intro cur fresh child; rfl
  · intro cur; cases cur <;> simp [cancelSessionWork]
  · intro _; rfl
  · intro _ _; rfl
  · intro _; rfl
  · intro i; cases i <;> simp [replBanner]
  · simp [replBanner]
  · intro args; exact ⟨_, rfl⟩
  · intro args; rfl
end JuliaLean.RuntimeCov.Client
end
