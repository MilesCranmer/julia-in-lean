import JuliaLean.RuntimeCov.Common

/-!
`base/client.jl`: REPL colors, shell-mode commands, backtrace scrubbing and
error display, input parsing and evaluation, command-line option processing,
startup files, REPL hooks and drivers, the session cancellation tree, `_start`,
`repl_main` and `@main`.  Terminal, process, parser and evaluator effects are
inputs; each model returns the observable decision the Julia code makes.
-/

namespace JuliaLean.RuntimeCov.Client

open JuliaLean.RuntimeCov

/-! ## Colors -/

/-- A key of `Base.text_colors`: an integer or a symbol. -/
inductive ColorKey where
  | int (n : Int)
  | sym (s : Sym)
  deriving DecidableEq, Repr

/-- `repl_color(key, default)`, base/client.jl:16-21: `env` is
`get(ENV, key, "")`, `tryparse` is `tryparse(Int, _)`, `haskey` tests
`text_colors`. -/
def parseColor (env : String) (tryparse : String → Option Int) : ColorKey :=
  match tryparse env with | some n => ColorKey.int n | none => ColorKey.sym env

def replColor (env : String) (tryparse : String → Option Int) (haskey : ColorKey → Bool)
    (default : ColorKey) : ColorKey :=
  let c := parseColor env tryparse
  if haskey c then c else default

/-- The named color queries, base/client.jl:23-32: environment variable and default. -/
def colorSettings : List (String × ColorKey) :=
  [("JULIA_ERROR_COLOR", .sym "light_red"), ("JULIA_WARN_COLOR", .sym "yellow"),
   ("JULIA_INFO_COLOR", .sym "cyan"), ("JULIA_DEBUG_COLOR", .sym "blue"),
   ("JULIA_INPUT_COLOR", .sym "normal"), ("JULIA_ANSWER_COLOR", .sym "normal"),
   ("JULIA_STACKFRAME_LINEINFO_COLOR", .sym "bold"), ("JULIA_STACKFRAME_FUNCTION_COLOR", .sym "bold")]

/-- `error_color()` … `stackframe_function_color()`: `repl_color` of the
setting's variable and default; `input_color`/`answer_color` index
`text_colors` with the result. -/
def namedColor (env : String → String) (tryparse : String → Option Int) (haskey : ColorKey → Bool)
    (setting : String × ColorKey) : ColorKey :=
  replColor (env setting.1) tryparse haskey setting.2
def colorCode (textColors : ColorKey → String) (env : String → String) (tryparse : String → Option Int)
    (haskey : ColorKey → Bool) (setting : String × ColorKey) : String :=
  textColors (namedColor env tryparse haskey setting)

/-! ## Shell mode -/

/-- What `repl_cmd` does. -/
inductive ShellAction where
  | runDirect
  | cd (dir : String) (oldpwd : Option String)
  | runShell (argv : List String)
  deriving DecidableEq, Repr

/-- The command handed to `repl_cmd`. -/
inductive CmdArg where
  | cmd (exec : List String)
  | pipeline
  | notACmd

/-- `repl_cmd(cmd, out)`, base/client.jl:34-91: `oldpwdEnv` is `ENV["OLDPWD"]`,
`pwd` the current directory (`none` if `pwd()` throws `IOError`), `shell` the
split `JULIA_SHELL`/`SHELL` command, `escape` `shell_escape_posixly`. -/
def replCmd (c : CmdArg) (iswindows : Bool) (oldpwdEnv : Option String) (home : String)
    (pwd : Option String) (shell : List String) (escape : List String → String) : Rt ShellAction :=
  match c with
  | .notACmd => .error (.argumentError "repl_cmd: expected an `AbstractCmd`")
  | .pipeline => .ok .runDirect
  | .cmd [] => .error (.argumentError "no cmd to execute")
  | .cmd (x :: rest) =>
    if x = "cd" then
      if rest.length > 1 then .error (.argumentError "cd method only takes one argument")
      else
        let dir : Rt String := match rest with
          | [d] => if d = "-" then (match oldpwdEnv with
              | none => .error (.errorException "cd: OLDPWD not set")
              | some o => .ok o) else .ok d
          | _ => .ok home
        match dir with
        | .error e => .error e
        | .ok d => .ok (.cd d pwd)
    else if iswindows then .ok .runDirect
    else .ok (.runShell (shell ++ ["-c", escape (x :: rest)]))

/-! ## Backtraces -/

/-- A stack frame as the scrubbing code sees it. -/
structure Frame where
  func : String
  fromC : Bool
  unknown : Bool
  modBaseOrCore : Bool
  deriving DecidableEq, Repr

/-- `ip_matches_func(ip, func)`, base/client.jl:94-102, over the frames of `ip`. -/
def ipMatchesFunc (frames : List Frame) (func : String) : Bool :=
  match frames with
  | [] => false
  | fr :: rest => if fr.unknown || fr.fromC then false else if fr.func = func then true
                  else ipMatchesFunc rest func

/-- `is_driver_entry(frame)`, base/client.jl:109-111. -/
def isDriverEntry (f : Frame) : Bool :=
  !f.fromC && ("__repl_entry".isPrefixOf f.func || "__script_entry".isPrefixOf f.func)

/-- `is_driver_machinery(frame)`, base/client.jl:115-120. -/
def isDriverMachinery (f : Frame) : Bool :=
  !f.fromC && f.modBaseOrCore &&
    f.func ∈ ["eval", "include_string", "_include", "include", "fl_toplevel_eval"]

/-- Pop machinery frames from the end (`while ... pop!`). -/
def popMachinery (bt : List Frame) : List Frame :=
  (bt.reverse.dropWhile isDriverMachinery).reverse

/-- Index of the last driver-entry frame (`findlast`). -/
def findLastEntry (bt : List Frame) : Option Nat :=
  ((List.range bt.length).filter (fun i => isDriverEntry (bt.getD i ⟨"", false, false, false⟩))).getLast?

/-- `scrub_repl_backtrace(bt)`, base/client.jl:122-135. -/
def scrubBacktrace (bt : List Frame) : List Frame :=
  match findLastEntry bt with
  | none => bt
  | some i => popMachinery (bt.take i)

/-- `scrub_repl_backtrace(stack::ExceptionStack)`, base/client.jl:136-137. -/
def scrubStack {ε : Type} (stack : List (ε × List Frame)) : List (ε × List Frame) :=
  stack.map fun p => (p.1, scrubBacktrace p.2)

/-- `istrivialerror(stack)`, base/client.jl:139-140. -/
def istrivialerror (stack : List (Bool × List Frame)) : Bool :=
  match stack with
  | [(isMethodError, bt)] => bt.length ≤ 1 && !isMethodError
  | _ => false

/-- `display_error(io, stack)` and the other `display_error` methods,
base/client.jl:143-156: `"ERROR: "` then the shown exceptions, then a newline. -/
def displayError (shown : String) : String := "ERROR: " ++ shown ++ "\n"

/-- `__script_entry_include`, `__script_entry_include_string`,
`__script_entry_eval`, `__repl_entry_client_eval`, base/client.jl:104-107,159:
delegate to `_include`/`include_string`/`Core.eval` unchanged. -/
def entryDelegate {α β : Type} (f : α → β) (x : α) : β := f x

/-! ## Parsing and evaluation -/

/-- A parse result: a top-level block of statements, or a single node. -/
inductive Parsed where
  | toplevel (children : List Parsed)
  | error
  | incomplete
  | node (n : Nat)
  deriving Repr

def Parsed.isIncomplete : Parsed → Bool
  | .incomplete => true
  | _ => false

def Parsed.isBad : Parsed → Bool
  | .error | .incomplete => true
  | _ => false

/-- `_parse_input_line_core`, base/client.jl:215-231. -/
def parseInputLineCore (ex : Parsed) : Parsed :=
  match ex with
  | .toplevel cs => match cs.getLast? with
    | some last => if last.isBad then last else ex
    | none => ex
  | _ => ex

/-- `parse_input_line(s; depwarn)`, base/client.jl:233-244: the logger choice
does not change the result. -/
def parseInputLine (parse : String → Parsed) (_depwarn : Bool) (s : String) : Parsed :=
  parseInputLineCore (parse s)

/-- Outcome of evaluating or displaying in `eval_user_input`. -/
inductive Outcome where
  | ok
  | throws
  deriving DecidableEq, Repr

/-- `eval_user_input(errio, ast, show_value)`, base/client.jl:161-213: returns
the number of error-display attempts made. The first try evaluates; every
later try displays the last error; it gives up after three failures. -/
def evalUserInput (evalOutcome : Outcome) (displayOutcomes : List Outcome) : Nat :=
  match evalOutcome with
  | .ok => 0
  | .throws =>
    let rec go : Nat → List Outcome → Nat
      | errcount, [] => errcount
      | errcount, o :: os => if errcount > 2 then errcount
        else match o with | .ok => errcount | .throws => go (errcount + 1) os
    min 3 (go 1 displayOutcomes)

/-! ## Command-line processing -/

/-- The decisions of `exec_options(opts)`, base/client.jl:246-361. -/
structure ExecPlan where
  programFile : String
  argsLeft : List String
  repl : Bool
  bugReport : Bool
  deriving DecidableEq, Repr

/-- The pre-processing loop of `exec_options`: `cmds` are the `-e`, `-E`,
`-L`, `-m`, `-B` options. -/
def execOptions (args : List String) (cmds : List (Char × String)) : ExecPlan :=
  let isProgram0 := !args.isEmpty
  let rec scan : List (Char × String) → Bool → Bool → Option (Bool × Bool)
    | [], p, r => some (p, r)
    | (c, _) :: cs, p, r =>
      if c = 'e' || c = 'E' then scan cs false false
      else if c = 'B' then none
      else scan cs p r
  match scan cmds isProgram0 (!isProgram0) with
  | none => ⟨"", args, false, true⟩
  | some (isProgram, repl) =>
    match isProgram, args with
    | true, a :: rest => ⟨a, rest, repl, false⟩
    | _, _ => ⟨"", args, repl, false⟩

/-- `_global_julia_startup_file()`, base/client.jl:363-377. -/
def globalStartupFile (sysconfdirEmpty : Bool) (p1 p2 : String) (isfile : String → Bool) : Option String :=
  if !sysconfdirEmpty && isfile p1 then some p1
  else if !sysconfdirEmpty && p1 = p2 then none
  else if isfile p2 then some p2 else none

/-- `_local_julia_startup_file()`, base/client.jl:379-385: `config/startup.jl`
in `DEPOT_PATH[1]`. -/
def localStartupFile (depots : List String) (startupIn : String → String) (isfile : String → Bool) :
    Option String :=
  match depots with
  | [] => none
  | d :: _ => if isfile (startupIn d) then some (startupIn d) else none

/-- `load_julia_startup()`, base/client.jl:387-393: the files included, global first. -/
def loadJuliaStartup (g l : Option String) : List String := g.toList ++ l.toList

/-! ## REPL hooks and drivers -/

/-- `atreplinit(f)`, base/client.jl:405. -/
def atreplinit (hooks : List Nat) (f : Nat) : List Nat := f :: hooks
/-- `__atreplinit(repl)` and `_atreplinit`, base/client.jl:407-417: calls in list order. -/
def runReplHooks (hooks : List Nat) : List Nat := hooks

/-- `load_InteractiveUtils(mod)`, base/client.jl:419-433: `none` when the
stdlib cannot be required (a warning is logged). -/
def loadInteractiveUtils (already : Bool) (requireOk : Bool) : Option Unit :=
  if already || requireOk then some () else none
/-- `load_REPL()`, base/client.jl:435-443. -/
def loadREPL (requireOk : Bool) : Option Unit := if requireOk then some () else none

/-- Which driver `run_main_repl` uses, base/client.jl:527-546, and whether it warns. -/
inductive Driver where
  | std
  | fallback (warned : Bool)
  deriving DecidableEq, Repr

def runMainRepl (fallbackEnv interactive quiet replAvailable : Bool) : Driver :=
  if !fallbackEnv && interactive && replAvailable then .std
  else .fallback (!fallbackEnv && interactive && !quiet)

/-- `run_fallback_repl(interactive)`, base/client.jl:448-494: a file input is
parsed whole and each top-level statement evaluated in order; otherwise lines
are accumulated until the parse is complete. -/
def fallbackStatements (whole : Parsed) : List Parsed :=
  match whole with
  | .toplevel cs => cs
  | ex => [ex]

def accumulateLines (parse : String → Parsed) : String → List String → String × List String
  | acc, [] => (acc, [])
  | acc, l :: ls =>
    let acc := acc ++ l
    if (parse acc).isIncomplete then accumulateLines parse acc ls else (acc, ls)

/-- `run_std_repl(REPL, quiet, banner, history_file)`, base/client.jl:496-524:
the basic REPL for a dumb terminal, the line editor otherwise; the previously
active REPL is restored afterwards. -/
def runStdRepl (term : String) (prev : Option Nat) (this : Nat) : Bool × Option Nat × Option Nat :=
  (term = "dumb", some this, prev)

/-- `var"#_internal_julia_parse"(args...)`, base/client.jl:568-570: calls the
parser held by `main_parser`. -/
def internalParse {α β : Type} (parser : α → β) (args : α) : β := parser args

/-- `should_use_main_entrypoint()`, base/client.jl:580-585. -/
def shouldUseMainEntrypoint (mainDefined : Bool) (ownerFlag : Option Bool) : Bool :=
  mainDefined && ownerFlag = some true

/-! ## Session cancellation -/

/-- `session_cancel_source!()`, base/client.jl:603-615: reuse or create. -/
def sessionCancelSource (cur : Option Nat) (fresh : Nat) : Nat × Option Nat :=
  match cur with
  | some s => (s, some s)
  | none => (fresh, some fresh)

/-- `new_evaluation_cancel_source!()`, base/client.jl:619-620: a child of the session source. -/
def newEvaluationCancelSource (cur : Option Nat) (fresh child : Nat) : (Nat × Nat) × Option Nat :=
  let (ses, st) := sessionCancelSource cur fresh
  ((child, ses), st)

/-- `cancel_session_work!()`, base/client.jl:630-642: the source cancelled and
the new state. -/
def cancelSessionWork (cur : Option Nat) : Bool × Option Nat × Option Nat :=
  match cur with
  | none => (false, none, none)
  | some s => (true, some s, none)

/-- `init_frontend()`, base/client.jl:644-651: the lowering choice. -/
def initFrontend (useFlisp : Bool) : Bool := !useFlisp

/-! ## `_start`, `repl_main`, `@main` -/

/-- `_start()`, base/client.jl:653-719: the exit code. `mainRet` is the
result of `main(ARGS)` or the REPL (`none` = `nothing`), `conv` the
conversion to `Cint`; a thrown error gives 1. -/
def start (threw : Bool) (mainRet : Option Int) (conv : Int → Option Int) : Int :=
  if threw then 1 else
  let r := mainRet.getD 0
  (conv r).getD 1

/-- `repl_main(_)`, base/client.jl:721-733: the banner choice. -/
inductive Banner where
  | no
  | yes
  | short
  deriving DecidableEq, Repr

def replBanner (b : Int) (interactiveInput : Bool) : Banner :=
  let auto := b == -1
  if b == 0 || (auto && !interactiveInput) then .no
  else if b == 1 || (auto && interactiveInput) then .yes
  else .short

/-- `@main(args...)`, base/client.jl:786-802: errors when `main` is an
imported binding; otherwise marks the entrypoint and returns `main` or the call. -/
def mainMacro (mainDefined importedMain : Bool) (args : List Nat) : Rt (Bool × Option (List Nat)) :=
  if mainDefined && importedMain then
    .error (.errorException "Symbol `main` is already a resolved import in module. `@main` must be used in the defining module.")
  else .ok (true, if args.isEmpty then none else some args)

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
