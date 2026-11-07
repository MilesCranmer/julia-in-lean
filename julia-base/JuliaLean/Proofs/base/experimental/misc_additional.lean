import JuliaLean.base.experimental

/-!
# `base/experimental.jl`, second part (master `bbfa0ce4150`)

`sync_end`/`@sync`, error hints, `@overlay`, `@MethodTable`, `make_io_thread`,
`entrypoint`, `disable_new_worlds`, task metrics, `wait_with_timeout`, `@reexport`,
`set_syntax_version` and `@VERSION`. Runtime services the methods call (`take!`,
`ccall`s, the scheduler) are inputs of the models.
-/

namespace JuliaLean.MiscCov.Experimental

/-- The `Experimental.@sync` docstring (`base/experimental.jl:109-124`): `sync_end`
returns once every registered waitable has completed, spawning one watcher per
waitable, and the first exception is rethrown immediately with the block's source
cancelled; a block that registered nothing returns at once. -/
def SyncContract : Prop :=
  (∀ hasSrc es, syncEnd false hasSrc es = .ok 0) ∧
  (∀ (hasSrc : Bool) (k : Nat) (rest : List Event), 1 ≤ k →
    syncEnd true hasSrc (List.replicate k .task ++ List.replicate k .completion ++ rest) = .ok k) ∧
  (∀ (hasSrc : Bool) (k : Nat) (c : Bool) (rest : List Event),
    syncEnd true hasSrc (List.replicate k .task ++ .fail c :: rest) = .rethrown hasSrc k)

theorem syncLoop_tasks (hasSrc : Bool) : ∀ (k : Nat) (n : Int) (w : Nat) (es : List Event),
    syncLoop hasSrc n w (List.replicate k .task ++ es) = syncLoop hasSrc (n + k) (w + k) es := by
  intro k
  induction k with
  | zero => intro n w es; simp
  | succ k ih =>
    intro n w es
    rw [List.replicate_succ, List.cons_append, syncLoop, ih]
    congr 1 <;> omega

theorem syncLoop_completions (hasSrc : Bool) : ∀ (k : Nat) (w : Nat) (rest : List Event),
    syncLoop hasSrc ((k : Int) + 1) w (List.replicate (k + 1) .completion ++ rest) = .ok w := by
  intro k
  induction k with
  | zero => intro w rest; simp [syncLoop]
  | succ k ih =>
    intro w rest
    rw [List.replicate_succ, List.cons_append, syncLoop]
    rw [if_neg (by omega)]
    have : ((k + 1 : Nat) : Int) + 1 - 1 = (k : Int) + 1 := by omega
    rw [this]
    exact ih w rest

theorem syncContract_proven : SyncContract := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro hasSrc k rest hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [syncEnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [syncLoop_tasks]
    have := syncLoop_completions hasSrc j (0 + (j + 1)) rest
    have e : (0 : Int) + ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    rw [e, this]
    simp
  · intro hasSrc k c rest
    simp only [syncEnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [syncLoop_tasks]
    simp [syncLoop]

/-- The expansion runs the escaped block before `sync_end` and returns its value `v`. -/
def SyncMacroShape : Prop :=
  ∀ block : Ex, ∃ binds blk,
    syncMacro block = .expr "let" [binds, .expr "block" [.expr "=" [.sym "v", blk],
      .expr "call" [.sym "sync_end", Ex.esc (.sym "##sync#48"), .sym "#sync_src#"], .sym "v"]] ∧
    blk.args?.map (·.head?) = some (some (Ex.esc block))

theorem syncMacroShape_proven : SyncMacroShape := fun block => ⟨_, _, rfl, rfl⟩

/-- The docstrings: a registered handler is invoked for an exception of its type or
a subtype, after the handlers registered before it for the same `TypeName` and
after those of more specific types; a throwing handler does not stop the others; and
nothing runs while hints are disabled. -/
def HintsContract : Prop :=
  (∀ r isaT chain, showErrorHints true r isaT chain = []) ∧
  (∀ (r : HintTable) (tn n : Nat) (h : Handler), registerErrorHint r tn h tn = r tn ++ [h] ∧
    (n ≠ tn → registerErrorHint r tn h n = r n)) ∧
  (∀ (isaT : Nat → Bool) (hs : List Handler) (h : Handler) (out : List String),
    isaT h.exct = true → h.run = .ok out → runHandlers isaT (hs ++ [h]) = runHandlers isaT hs ++ out) ∧
  (∀ (isaT : Nat → Bool) (h : Handler) (hs : List Handler) (msg : String),
    isaT h.exct = true → h.run = .error msg →
      runHandlers isaT (h :: hs) = "@error Hint-handler caused an error" :: runHandlers isaT hs) ∧
  (∀ r isaT (chain : List Nat), showErrorHints false r isaT chain = chain.flatMap (fun tn => runHandlers isaT (r tn)))

theorem runHandlers_append (isaT : Nat → Bool) : ∀ (a b : List Handler),
    runHandlers isaT (a ++ b) = runHandlers isaT a ++ runHandlers isaT b := by
  intro a b
  induction a with
  | nil => rfl
  | cons h hs ih => simp [runHandlers, ih, List.append_assoc]

theorem hintsContract_proven : HintsContract := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_, fun _ _ _ => rfl⟩
  · intro r tn n h
    exact ⟨by simp [registerErrorHint], fun hn => by simp [registerErrorHint, hn]⟩
  · intro isaT hs h out hi hr
    rw [runHandlers_append]
    simp [runHandlers, hi, hr]
  · intro isaT h hs msg hi hr
    simp [runHandlers, hi, hr]

/-! ## `@overlay`, `@consistent_overlay`, `overlay_def!`, `base/experimental.jl:410-499` -/

/-- `@overlay` rewrites the signature of a definition to `Expr(:overlay, mt, f)(args...)`,
through return-type annotations and `where` clauses and inside docstring macros,
rewrites every definition of a block, and rejects anything else. -/
def OverlayContract : Prop :=
  ∀ (mt f body T : Ex) (args : List Ex),
    overlay mt (.expr "=" [.expr "call" (f :: args), body]) =
      .ok (Ex.esc (.expr "=" [.expr "call" (.expr "overlay" [mt, f] :: args), body])) ∧
    overlay mt (.expr "function" [.expr "::" [.expr "call" (f :: args), T], body]) =
      .ok (Ex.esc (.expr "function" [.expr "::" [.expr "call" (.expr "overlay" [mt, f] :: args), T], body])) ∧
    overlay mt (.expr "=" [.expr "where" [.expr "call" (f :: args), T], body]) =
      .ok (Ex.esc (.expr "=" [.expr "where" [.expr "call" (.expr "overlay" [mt, f] :: args), T], body])) ∧
    overlay mt (.expr "block" [.lnn, .expr "=" [.expr "call" (f :: args), body]]) =
      .ok (Ex.esc (.expr "block" [.lnn, .expr "=" [.expr "call" (.expr "overlay" [mt, f] :: args), body]])) ∧
    overlay mt (.expr "macrocall" [.sym "@doc", .lnn, .str "doc", .expr "=" [.expr "call" (f :: args), body]]) =
      .ok (Ex.esc (.expr "macrocall" [.sym "@doc", .lnn, .str "doc",
        .expr "=" [.expr "call" (.expr "overlay" [mt, f] :: args), body]])) ∧
    overlay mt (.expr "call" (f :: args)) = .error (.errorException "@overlay requires a function definition") ∧
    consistentOverlay mt (.expr "=" [.expr "call" (f :: args), body]) =
      .ok (Ex.esc (.expr "pushmeta" [.expr "=" [.expr "call" (.expr "overlay" [mt, f] :: args), body],
        .val "purity(consistent_overlay=true)"]))

theorem overlayContract_proven : OverlayContract := by
  intro mt f body T args
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [overlay, consistentOverlay, unwrapMacrocalls, mapUnwrapped, overlayOne, isFunctionDef, isShortSig,
      overlayDef, Ex.isExpr, Ex.isLnn, Ex.args?, bind, Except.bind, pure, Except.pure, List.mapM, List.mapM.loop]

def MethodTableContract : Prop :=
  (∀ (name mod : String), methodTableMacro name mod =
    Ex.esc (.expr "const" [.expr "=" [.sym name, .expr "call" [.val "new_mt", .qn (.sym name), .val mod]]])) ∧
  (∀ (name mod : String), newMt (.ok ()) name mod = .ok (name, mod)) ∧
  (∀ (e : Err) (name mod : String), newMt (.error e) name mod = .error e)

theorem methodTableContract_proven : MethodTableContract := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The docstrings: `make_io_thread` throws exactly when the thread cannot be created;
`entrypoint` records the signature only while generating output; the flags are set;
`task_running_time_ns` is `nothing` without metrics, the recorded total for another
task and that total plus the time since it last started for the current task;
`task_wall_time_ns` is `nothing` without metrics, 0 before the first enqueue, and
the time from the first enqueue to completion or to now. -/
def RuntimeContract : Prop :=
  (∀ c d : Int, (makeIoThread c d).toOption.isNone ↔ c ≠ 0) ∧
  (∀ s argt, entrypointT true s argt = { s with entrypoints := s.entrypoints ++ [argt] } ∧
    entrypointT false s argt = s) ∧
  (∀ g s f ats, entrypointF g s f ats = entrypointT g s ("Tuple{" ++ String.intercalate ", " (f :: ats) ++ "}")) ∧
  (∀ s, (disableNewWorlds s).newWorldsDisabled = true) ∧
  (∀ s b, (taskMetrics s b).metricsEnabled = b) ∧
  (∀ (t c : TaskM) (now : Nat), t.metricsEnabled = false →
    taskRunningTimeNs t c now = none ∧ taskWallTimeNs t now = none) ∧
  (∀ (t c : TaskM) (now : Nat), t.metricsEnabled = true → t.id ≠ c.id →
    taskRunningTimeNs t c now = some t.runningTimeNs) ∧
  (∀ (t : TaskM) (now : Nat), t.metricsEnabled = true → t.lastStartedRunningAt ≤ now →
    now < 2 ^ 64 → t.runningTimeNs + (now - t.lastStartedRunningAt) < 2 ^ 64 →
    taskRunningTimeNs t t now = some (t.runningTimeNs + (now - t.lastStartedRunningAt))) ∧
  (∀ (t : TaskM) (now : Nat), t.metricsEnabled = true → 0 < t.firstEnqueuedAt →
    t.firstEnqueuedAt ≤ t.finishedAt → t.finishedAt < 2 ^ 64 →
    taskWallTimeNs t now = some (t.finishedAt - t.firstEnqueuedAt)) ∧
  (∀ (t : TaskM) (now : Nat), t.metricsEnabled = true → 0 < t.firstEnqueuedAt → t.finishedAt = 0 →
    t.firstEnqueuedAt ≤ now → now < 2 ^ 64 →
    taskWallTimeNs t now = some (now - t.firstEnqueuedAt)) ∧
  (∀ (t : TaskM) (now : Nat), t.metricsEnabled = true → t.firstEnqueuedAt = 0 → taskWallTimeNs t now = some 0)

theorem runtimeContract_proven : RuntimeContract := by
  refine ⟨?_, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d
    by_cases h : c = 0 <;> simp [makeIoThread, h, Except.toOption]
  · intro t c now h; simp [taskRunningTimeNs, taskWallTimeNs, h]
  · intro t c now h1 h2; simp [taskRunningTimeNs, h1, h2]
  · intro t now h1 h2 h3 h4
    simp only [taskRunningTimeNs, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, addW, subW, Option.some.injEq]
    have hl : t.lastStartedRunningAt % 2 ^ 64 = t.lastStartedRunningAt := Nat.mod_eq_of_lt (by omega)
    rw [hl]
    omega
  · intro t now h1 h2 h3 h4
    simp only [taskWallTimeNs, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, subW]
    rw [if_neg (by omega), if_neg (by omega), Option.some.injEq]
    have hl : t.firstEnqueuedAt % 2 ^ 64 = t.firstEnqueuedAt := Nat.mod_eq_of_lt (by omega)
    rw [hl]
    omega
  · intro t now h1 h2 h3 h4 h5
    simp only [taskWallTimeNs, h1, h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, subW]
    rw [if_neg (by omega), Option.some.injEq]
    have hl : t.firstEnqueuedAt % 2 ^ 64 = t.firstEnqueuedAt := Nat.mod_eq_of_lt (by omega)
    rw [hl]
    omega
  · intro t now h1 h2; simp [taskWallTimeNs, h1, h2]

/-- `wait_with_timeout` parks on the condition, on the governing source if any, and on a
deadline exactly when `timeout > 0`; the condition's lock is released during the wait
and re-acquired on both the normal and the exceptional exit; a normal return withdraws
the entry with the value (closing the timer) and returns the waited value. -/
def WaitContract : Prop :=
  ∀ {V : Type} (timeout : Int) (hasSrc cancelled : Bool) (wait : Except Err V),
    ((waitWithTimeout timeout hasSrc true cancelled wait).1.head? = some (.park
      ((if timeout > 0 then [Waitable.cond] ++ (if hasSrc then [.source] else []) ++ [.timeout]
        else [Waitable.cond] ++ (if hasSrc then [.source] else []))))) ∧
    ((waitWithTimeout timeout hasSrc true cancelled wait).1.count .unlock =
      (waitWithTimeout timeout hasSrc true cancelled wait).1.count .relock) ∧
    (∀ v, wait = .ok v → ∃ steps, waitWithTimeout timeout hasSrc true cancelled wait = (steps, .value v) ∧
      steps.getLast? = some .withdrawValue) ∧
    ((waitWithTimeout timeout hasSrc false cancelled wait).1.count .unlock = 0)

theorem waitContract_proven : WaitContract := by
  intro V timeout hasSrc cancelled wait
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases wait <;> by_cases ht : timeout > 0 <;> cases hasSrc <;> simp [waitWithTimeout, ht]
  · cases wait <;> simp [waitWithTimeout]
  · intro v hv; subst hv; exact ⟨_, rfl, rfl⟩
  · simp [waitWithTimeout]

/-- `@reexport using A, B` evaluates one reexporting `using` per module path then a world
age update; other forms are rejected; `set_syntax_version` declares the parser of the
edition `(major, minor)`; `@set_syntax_version` calls it with the macro's module; and
`(@VERSION).syntax` is the parser's syntax version, 1.13 for a plain `LineNumberNode`. -/
def SyntaxContract : Prop :=
  (∀ mod (p : Ex) (ps : List Ex), (p :: ps).all (fun x => !x.isExpr ":") →
    reexport mod (.expr "using" (p :: ps)) = .ok (Ex.esc (.expr "block" (((p :: ps).map fun q =>
      .expr "call" [.val "Core._eval_using", .val mod, .qn q, .val "JL_MODULE_USING_REEXPORT"]) ++
      [.expr "latestworld" [], .sym "nothing"])))) ∧
  (∀ mod, reexport mod (.expr "using" []) = .error (.errorException "@reexport must be used with a `using` statement")) ∧
  (∀ mod hd args, hd ≠ "using" → reexport mod (.expr hd args) = .error (.errorException "@reexport must be used with a `using` statement")) ∧
  (∀ mod p q, reexport mod (.expr "using" [p, .expr ":" q]) =
    .error (.errorException "@reexport does not support `using Module: names` syntax")) ∧
  (∀ m major minor patch, setSyntaxVersionV m major minor patch = m ++ [("#_internal_julia_parse", (major, minor))]) ∧
  (∀ mod ver, setSyntaxVersionMacro mod ver = .expr "call" [.gref "Base" "set_syntax_version", .val mod, Ex.esc ver]) ∧
  (∀ v, versionMacro (some v) = .expr "tuple" [.expr "parameters" [.expr "kw" [.sym "syntax", .val v],
      .expr "kw" [.sym "runtime", .sym "VERSION"]]]) ∧
  (versionMacro none = .expr "tuple" [.expr "parameters" [.expr "kw" [.sym "syntax", .val "v\"1.13\""],
      .expr "kw" [.sym "runtime", .sym "VERSION"]]])

theorem syntaxContract_proven : SyntaxContract := by
  refine ⟨?_, fun _ => rfl, ?_, ?_, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  · intro mod p ps h
    have h' : (p :: ps).any (·.isExpr ":") = false := by
      simp only [List.all_eq_true, Bool.not_eq_true'] at h
      simp only [List.any_eq_false]
      intro x hx; simp [h x hx]
    simp only [reexport, h', Bool.false_eq_true, ↓reduceIte]
  · intro mod hd args h
    unfold reexport
    split
    · rename_i a as heq; cases heq; exact absurd rfl h
    · rfl
  · intro mod p q
    simp [reexport, Ex.isExpr]

end JuliaLean.MiscCov.Experimental
