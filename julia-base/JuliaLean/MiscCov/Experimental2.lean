import JuliaLean.MiscCov.Basic

/-!
# `base/experimental.jl`, second part (master `bbfa0ce4150`)

`sync_end`/`@sync`, error hints, `@overlay`, `@MethodTable`, `make_io_thread`,
`entrypoint`, `disable_new_worlds`, task metrics, `wait_with_timeout`, `@reexport`,
`set_syntax_version` and `@VERSION`. Runtime services the methods call (`take!`,
`ccall`s, the scheduler) are inputs of the models.
-/

namespace JuliaLean.MiscCov.Experimental

/-! ## `sync_end`, `base/experimental.jl:63-107` -/

/-- What `take!(c)` returns or throws: a waitable registered by `@async`/`@spawn`, the
`:__completion__` token a watcher puts after its waitable finished, or an exception
(a child failure delivered by `close(c, e)`, or a cancellation of the scope). -/
inductive Event where
  | task
  | completion
  | fail (cancellation : Bool)
  deriving DecidableEq, Repr

/-- The outcome of `sync_end`: normal return after spawning `watchers` watcher tasks,
the exception rethrown (with whether the block's source was cancelled), or still
blocked in `take!` when the events run out. -/
inductive SyncResult where
  | ok (watchers : Nat)
  | rethrown (srcCancelled : Bool) (watchers : Nat)
  | blocked
  deriving DecidableEq, Repr

/-- The `while true` loop of `sync_end`, on the sequence of `take!` results. -/
def syncLoop (hasSrc : Bool) : Int → Nat → List Event → SyncResult
  | _, _, [] => .blocked
  | n, w, .task :: es => syncLoop hasSrc (n + 1) (w + 1) es
  | n, w, .completion :: es => if n - 1 = 0 then .ok w else syncLoop hasSrc (n - 1) w es
  | _, w, .fail _ :: _ => .rethrown hasSrc w

/-- `sync_end(c, src)`: an empty channel is closed at once; otherwise the loop. -/
def syncEnd (ready : Bool) (hasSrc : Bool) (events : List Event) : SyncResult :=
  if !ready then .ok 0 else syncLoop hasSrc 0 0 events

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

/-- `Experimental.@sync block`, `base/experimental.jl:126-143`: a `let` that creates the
cancellation source and the channel, runs the block in a scope carrying the source's
token, then calls `sync_end` and returns the block's value. -/
def syncMacro (block : Ex) : Ex :=
  let var := Ex.esc (.sym "##sync#48")
  let blk := .expr "tryfinally" [Ex.esc block, .nothing,
    .expr "call" [.gref "Base" "Scope", .val "current_scope", .val "CANCEL_TOKEN => token(#sync_src#)"]]
  .expr "let" [.expr "block" [.expr "=" [.sym "#sync_src#", .val "CancellationTokenSource(default_cancel_token())"],
      .expr "=" [var, .val "Channel(Inf)"]],
    .expr "block" [.expr "=" [.sym "v", blk],
      .expr "call" [.sym "sync_end", var, .sym "#sync_src#"], .sym "v"]]

/-- The expansion runs the escaped block before `sync_end` and returns its value `v`. -/
def SyncMacroShape : Prop :=
  ∀ block : Ex, ∃ binds blk,
    syncMacro block = .expr "let" [binds, .expr "block" [.expr "=" [.sym "v", blk],
      .expr "call" [.sym "sync_end", Ex.esc (.sym "##sync#48"), .sym "#sync_src#"], .sym "v"]] ∧
    blk.args?.map (·.head?) = some (some (Ex.esc block))

theorem syncMacroShape_proven : SyncMacroShape := fun block => ⟨_, _, rfl, rfl⟩

/-! ## Error hints, `base/experimental.jl:331-374` -/

/-- A Julia type for the hint machinery: its `TypeName` and supertype (`none` for `Any`). -/
structure HTy where
  name : Nat
  super : Option Nat
  deriving DecidableEq, Repr

/-- A registered handler: the exception type it was registered for and what it writes
(or throws). -/
structure Handler where
  exct : Nat
  run : Except String (List String)

/-- `_hint_handlers`: the handlers of each `TypeName`, in registration order (an absent
key has none). -/
abbrev HintTable := Nat → List Handler

/-- `register_error_hint(handler, exct)`: `push!(get!(Vector{Any}, _hint_handlers,
typename(exct)), (exct, handler))`. `tn` is `Core.typename(exct)`. -/
def registerErrorHint (r : HintTable) (tn : Nat) (h : Handler) : HintTable :=
  fun n => if n = tn then r n ++ [h] else r n

/-- Run the handlers of one `TypeName` whose `exct` the exception is an instance of
(`isa` given as `isaT`); a throwing handler is logged and the loop continues. -/
def runHandlers (isaT : Nat → Bool) : List Handler → List String
  | [] => []
  | h :: hs =>
    (if isaT h.exct then
      match h.run with
      | .ok out => out
      | .error _ => ["@error Hint-handler caused an error"]
    else []) ++ runHandlers isaT hs

/-- `show_error_hints(io, ex, args...)`: nothing while `_hints_disabled[]`; otherwise the
handlers of `typeof(ex)` and of each supertype below `Any`, most specific first.
`chain` lists the `TypeName`s from `typeof(ex)` up to (excluding) `Any`. -/
def showErrorHints (disabled : Bool) (r : HintTable) (isaT : Nat → Bool) (chain : List Nat) : List String :=
  if disabled then [] else chain.flatMap (fun tn => runHandlers isaT (r tn))

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

/-- `Base.unwrap_macrocalls(ex)`: the last argument of nested macro calls. -/
def unwrapMacrocalls : Nat → Ex → Ex
  | 0, ex => ex
  | n + 1, .expr "macrocall" args =>
    match args.getLast? with
    | some a => unwrapMacrocalls n a
    | none => .expr "macrocall" args
  | _, ex => ex

/-- `Meta.is_function_def(ex)` (`base/expr.jl`): `function`, `->`, or a short definition
`f(...) = ...` (possibly through `::` and `where`). -/
def isShortSig : Nat → Ex → Bool
  | 0, _ => false
  | n + 1, .expr "call" _ => true
  | n + 1, .expr "::" (a :: _) => isShortSig n a
  | n + 1, .expr "where" (a :: _) => isShortSig n a
  | _, _ => false

def isFunctionDef (ex : Ex) : Bool :=
  match ex with
  | .expr "function" _ => true
  | .expr "->" _ => true
  | .expr "=" (lhs :: _) => isShortSig 100 lhs
  | _ => false

/-- `overlay_def!(mt, ex)`: in the first argument of `ex`, replace the called function of
the signature `f(args...)` by `Expr(:overlay, mt, f)`, looking through `::` and `where`. -/
def overlayDef (mt : Ex) : Nat → Ex → M Ex
  | 0, _ => .error (.other "fuel")
  | n + 1, .expr hd (arg1 :: rest) =>
    match arg1 with
    | .expr "call" (f :: cargs) => .ok (.expr hd (.expr "call" (.expr "overlay" [mt, f] :: cargs) :: rest))
    | .expr "::" _ | .expr "where" _ => do
      let a ← overlayDef mt n arg1
      pure (.expr hd (a :: rest))
    | _ => .error (.errorException "@overlay requires a function definition")
  | _, _ => .error .boundsError

/-- Apply `f` to the definition inside nested macro calls, rebuilding them. -/
def mapUnwrapped (f : Ex → M Ex) : Nat → Ex → M Ex
  | 0, ex => f ex
  | n + 1, .expr "macrocall" args =>
    match args.getLast? with
    | some a => do
      let a' ← mapUnwrapped f n a
      pure (.expr "macrocall" (args.dropLast ++ [a']))
    | none => f (.expr "macrocall" args)
  | _, ex => f ex

def overlayOne (mt : Ex) (ex : Ex) : M Ex :=
  if isFunctionDef ex then overlayDef mt 100 ex
  else .error (.errorException "@overlay requires a function definition")

/-- `@overlay mt def`, `base/experimental.jl:410-425`. -/
def overlay (mt def_ : Ex) : M Ex := do
  let inner := unwrapMacrocalls 100 def_
  if inner.isExpr "block" then
    let args := inner.args?.getD []
    let args' ← args.mapM (fun arg =>
      if arg.isLnn then pure arg else mapUnwrapped (overlayOne mt) 100 arg)
    let rebuilt ← mapUnwrapped (fun _ => pure (.expr "block" args')) 100 def_
    pure (Ex.esc rebuilt)
  else do
    let d ← mapUnwrapped (overlayOne mt) 100 def_
    pure (Ex.esc d)

/-- `@consistent_overlay mt def`, `base/experimental.jl:478-485`: one definition, plus
the `:consistent_overlay` purity `:meta` pushed into its body. -/
def consistentOverlay (mt def_ : Ex) : M Ex := do
  let d ← mapUnwrapped (overlayOne mt) 100 def_
  pure (Ex.esc (.expr "pushmeta" [d, .val "purity(consistent_overlay=true)"]))

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

/-! ## `@MethodTable`, `base/experimental.jl:501-509` -/

/-- `new_mt(name, mod)`: `jl_check_top_level_effect` (which may throw), then a fresh
method table named `name` owned by `mod`. -/
def newMt (checkTopLevel : M Unit) (name mod : String) : M (String × String) := do
  checkTopLevel
  pure (name, mod)

/-- `@MethodTable name` expands to `const name = new_mt(:name, __module__)`. -/
def methodTableMacro (name mod : String) : Ex :=
  Ex.esc (.expr "const" [.expr "=" [.sym name, .expr "call" [.val "new_mt", .qn (.sym name), .val mod]]])

def MethodTableContract : Prop :=
  (∀ (name mod : String), methodTableMacro name mod =
    Ex.esc (.expr "const" [.expr "=" [.sym name, .expr "call" [.val "new_mt", .qn (.sym name), .val mod]]])) ∧
  (∀ (name mod : String), newMt (.ok ()) name mod = .ok (name, mod)) ∧
  (∀ (e : Err) (name mod : String), newMt (.error e) name mod = .error e)

theorem methodTableContract_proven : MethodTableContract := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-! ## `make_io_thread`, `entrypoint`, `disable_new_worlds`, `task_metrics` -/

/-- `make_io_thread()`, `base/experimental.jl:548-562`: `createErr` and `detachErr` are
the return codes of `uv_thread_create` and `uv_thread_detach`. The check after the
detach call tests `err`, which still holds the create result. -/
def makeIoThread (createErr detachErr : Int) : M Unit :=
  if createErr ≠ 0 then .error (.other "IOError: uv_thread_create")
  else
    let _ := detachErr
    if createErr ≠ 0 then .error (.other "IOError: uv_thread_detach") else .ok ()

/-- Runtime flags touched by `entrypoint`, `disable_new_worlds` and `task_metrics`. -/
structure RtFlags where
  entrypoints : List String
  newWorldsDisabled : Bool
  metricsEnabled : Bool
  deriving DecidableEq, Repr

/-- `entrypoint(argt::Type)`, `base/experimental.jl:573-579`. -/
def entrypointT (generatingOutput : Bool) (s : RtFlags) (argt : String) : RtFlags :=
  if generatingOutput then { s with entrypoints := s.entrypoints ++ [argt] } else s

/-- `entrypoint(f, argtypes::Tuple) = entrypoint(Tuple{Core.Typeof(f), argtypes...})`,
`base/experimental.jl:569-571`. -/
def entrypointF (generatingOutput : Bool) (s : RtFlags) (typeofF : String) (argtypes : List String) : RtFlags :=
  entrypointT generatingOutput s ("Tuple{" ++ String.intercalate ", " (typeofF :: argtypes) ++ "}")

/-- `disable_new_worlds()`, `base/experimental.jl:588`. -/
def disableNewWorlds (s : RtFlags) : RtFlags := { s with newWorldsDisabled := true }

/-- `task_metrics(b::Bool)`, `base/experimental.jl:603-610`. -/
def taskMetrics (s : RtFlags) (b : Bool) : RtFlags := { s with metricsEnabled := b }

/-- A `Task`'s metric fields (`UInt64` nanoseconds). -/
structure TaskM where
  id : Nat
  metricsEnabled : Bool
  runningTimeNs : Nat
  lastStartedRunningAt : Nat
  firstEnqueuedAt : Nat
  finishedAt : Nat

/-- `x -% y` and `x +% y` on `UInt64`. -/
def subW (x y : Nat) : Nat := (x + 2 ^ 64 - y % 2 ^ 64) % 2 ^ 64
def addW (x y : Nat) : Nat := (x + y) % 2 ^ 64

/-- `task_running_time_ns(t)`, `base/experimental.jl:630-639`; `current` is
`current_task()` and `now` is `time_ns()`. -/
def taskRunningTimeNs (t current : TaskM) (now : Nat) : Option Nat :=
  if !t.metricsEnabled then none
  else if t.id = current.id then some (addW t.runningTimeNs (subW now t.lastStartedRunningAt))
  else some t.runningTimeNs

/-- `task_wall_time_ns(t)`, `base/experimental.jl:655-662`. -/
def taskWallTimeNs (t : TaskM) (now : Nat) : Option Nat :=
  if !t.metricsEnabled then none
  else if t.firstEnqueuedAt = 0 then some 0
  else if t.finishedAt = 0 then some (subW now t.firstEnqueuedAt)
  else some (subW t.finishedAt t.firstEnqueuedAt)

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

/-! ## `wait_with_timeout`, `base/experimental.jl:690-719` -/

/-- The waitables `wait_with_timeout` parks on. -/
inductive Waitable where
  | cond | source | timeout
  deriving DecidableEq, Repr

/-- Observable steps: park, withdraw with a wake reason, lock depth changes, and the
outcome. -/
inductive Step where
  | park (ws : List Waitable)
  | withdrawFired
  | withdrawValue
  | unlock
  | relock
  deriving DecidableEq, Repr

inductive WaitOutcome (V : Type) where
  | value (v : V)
  | throws (e : Err)

/-- `wait_with_timeout(c; first, timeout, cancel)`: `parked` is the result of `park!`,
`cancelled` whether `checkcancel(src)` throws, and `wait` the result of
`wait_safe_interrupt`. -/
def waitWithTimeout {V : Type} (timeout : Int) (hasSrc parked cancelled : Bool) (wait : Except Err V) :
    List Step × WaitOutcome V :=
  let ws := if timeout > 0 then (if hasSrc then [.cond, .source, .timeout] else [.cond, .timeout])
    else (if hasSrc then [.cond, .source] else [.cond])
  if !parked then
    ([.park ws, .withdrawFired],
      if hasSrc && cancelled then .throws (.other "CancellationRequest")
      else .throws (.errorException "park fired without a cancelled source"))
  else
    match wait with
    | .error e => ([.park ws, .unlock, .relock], .throws e)
    | .ok v => ([.park ws, .unlock, .relock, .withdrawValue], .value v)

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

/-! ## `@reexport`, `set_syntax_version`, `@VERSION` -/

/-- `@reexport ex`, `base/experimental.jl:751-770`. -/
def reexport (mod : String) (ex : Ex) : M Ex :=
  match ex with
  | .expr "using" (a :: as) =>
    if (a :: as).any (·.isExpr ":") then .error (.errorException "@reexport does not support `using Module: names` syntax")
    else .ok (Ex.esc (.expr "block" (((a :: as).map fun p =>
      .expr "call" [.val "Core._eval_using", .val mod, .qn p, .val "JL_MODULE_USING_REEXPORT"]) ++
      [.expr "latestworld" [], .sym "nothing"])))
  | _ => .error (.errorException "@reexport must be used with a `using` statement")

/-- `Base.set_syntax_version(m, edition::Tuple{Int,Int})` declares the constant
`#_internal_julia_parse` of `m` as `VersionedParse(edition)`, `base/experimental.jl:772-776`;
`set_syntax_version(mod, e::VersionNumber)` uses `EditionNumber(e)`, the major and
minor version (`:777-778`). The module is the list of its declared constants. -/
def setSyntaxVersion (m : List (String × (Int × Int))) (edition : Int × Int) : List (String × (Int × Int)) :=
  m ++ [("#_internal_julia_parse", edition)]

def setSyntaxVersionV (m : List (String × (Int × Int))) (major minor patch : Int) : List (String × (Int × Int)) :=
  let _ := patch
  setSyntaxVersion m (major, minor)

/-- `@set_syntax_version ver`, `base/experimental.jl:811-813`. -/
def setSyntaxVersionMacro (mod : String) (ver : Ex) : Ex :=
  .expr "call" [.gref "Base" "set_syntax_version", .val mod, Ex.esc ver]

/-- `@VERSION`, `base/experimental.jl:828-836`: the parser puts the syntax version into a
`MacroSource`; a plain `LineNumberNode` means 1.13. -/
def versionMacro (source : Option String) : Ex :=
  match source with
  | none => .expr "tuple" [.expr "parameters" [.expr "kw" [.sym "syntax", .val "v\"1.13\""],
      .expr "kw" [.sym "runtime", .sym "VERSION"]]]
  | some v => .expr "tuple" [.expr "parameters" [.expr "kw" [.sym "syntax", .val v],
      .expr "kw" [.sym "runtime", .sym "VERSION"]]]

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
