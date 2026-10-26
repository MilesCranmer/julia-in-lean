import JuliaLean.MiscCov.Basic

/-!
# The deprecation machinery of `base/deprecated.jl` (master `bbfa0ce4150`)

Macros are functions on syntax (`Ex`). Two printing functions are inputs of the
models: `show` is `sprint(show_unquoted, ex)` and `str` is `string(x)` of a macro
argument. `remove_linenums!` and `replace_linenums!` are modelled on `Ex`
(`base/expr.jl`). The runtime state used by `depwarn` is explicit: the
`--depwarn` option, the backtrace and the log records written.
-/

namespace JuliaLean.MiscCov.Deprecated

open JuliaLean.MiscCov

/-! ## `__has_internal_change`, `base/deprecated.jl:110-113` -/

/-- `__has_internal_change(version_or, change_name)`: `vgt` is `VERSION > version_or`. -/
def hasInternalChange (vgt : Bool) (changes : List String) (name : String) : Bool :=
  if vgt then true else changes.contains name

def HasInternalChange : Prop :=
  (∀ changes name, hasInternalChange true changes name = true) ∧
  (∀ changes name, hasInternalChange false changes name = true ↔ name ∈ changes)

theorem hasInternalChange_proven : HasInternalChange :=
  ⟨fun _ _ => rfl, fun changes name => by simp [hasInternalChange]⟩

/-! ## Line numbers, `base/expr.jl` -/

/-- `remove_linenums!(ex)`: drop `LineNumberNode`s from every `Expr`'s arguments. -/
def removeLinenums : Ex → Ex
  | .expr h as => .expr h ((as.filter (fun a => !a.isLnn)).attach.map (fun ⟨a, _⟩ => removeLinenums a))
  | e => e
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem (List.mem_filter.mp ‹_›).1
  simp_wf; omega

/-- `replace_linenums!(ex, lnn)`: every `LineNumberNode` becomes the macro's source. -/
def replaceLinenums : Ex → Ex
  | .expr h as => .expr h (as.attach.map (fun ⟨a, _⟩ => replaceLinenums a))
  | .lnn => .lnn
  | e => e
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem ‹_›
  simp_wf; omega

/-! ## `@deprecate`, `base/deprecated.jl:179-231` -/

/-- The error of `cannot_export_nonsymbol()`, `base/deprecated.jl:180-188`. -/
def cannotExportMsg : String :=
  "if the third `export_old` argument is not specified or `true`, the first argument must be of form (1) `f(...)` where `f` is a symbol, (2) `T{...}(...)` where `T` is a symbol, or (3) a symbol."

def cannotExportNonsymbol {α : Type} : M α := .error (.errorException cannotExportMsg)

/-- `Core.Typeof($(esc(f))).name.singletonname`. -/
def singletonName (f : Ex) : Ex :=
  .expr "." [.expr "." [.expr "call" [.gref "Core" "Typeof", Ex.esc f], .qn (.sym "name")], .qn (.sym "singletonname")]

/-- `@deprecate old new export_old`, `base/deprecated.jl:179-231`. -/
def deprecate (shw : Ex → String) (old new : Ex) (exportOld : Bool) : M Ex := do
  let metaEx := Ex.expr "meta" [.sym "noinline"]
  match old with
  | .expr h oargs =>
    if h = "call" ∨ h = "where" then do
      let new := removeLinenums new
      let oldcall := shw old
      let newcall := shw new
      let callexpr ← (if h = "call" then pure old else
        match oargs with
        | c :: _ => pure c
        | [] => .error .boundsError : M Ex)
      match callexpr with
      | .expr "call" (fn0 :: _) =>
        let fnexpr := match fn0 with
          | .expr "curly" (t :: _) => t
          | _ => fn0
        let maybeExport ← (if exportOld then
            match fnexpr with
            | .sym _ => pure (Ex.expr "export" [Ex.esc fnexpr])
            | _ => cannotExportNonsymbol
          else pure .nothing : M Ex)
        let ex := Ex.expr "=" [Ex.esc old, .expr "block" [metaEx,
          .expr "call" [.sym "depwarn", .str ("`" ++ oldcall ++ "` is deprecated, use `" ++ newcall ++ "` instead."),
            singletonName fnexpr], Ex.esc new]]
        pure (.expr "toplevel" [maybeExport, replaceLinenums ex])
      | .expr "call" [] => .error .boundsError
      | .expr _ _ => .error (.errorException "invalid usage of @deprecate")
      | _ => .error .fieldError
    else deprecateOther shw old new exportOld metaEx
  | _ => deprecateOther shw old new exportOld metaEx
where
  /-- The `else` branch, `base/deprecated.jl:219-229`, and the generated method
  `$(esc(old))(args...; kwargs...)` (`base/deprecated.jl:222-226`). -/
  deprecateOther (shw : Ex → String) (old new : Ex) (exportOld : Bool) (metaEx : Ex) : M Ex :=
    if exportOld && !(match old with | .sym _ => true | _ => false) then cannotExportNonsymbol
    else
      let ex := Ex.expr "function" [.expr "call" [Ex.esc old, .expr "parameters" [.expr "..." [.sym "kwargs"]],
          .expr "..." [.sym "args"]],
        .expr "block" [metaEx,
          .expr "call" [.sym "depwarn", .str ("`" ++ shw old ++ "` is deprecated, use `" ++ shw new ++ "` instead."),
            singletonName old],
          .expr "call" [Ex.esc new, .expr "parameters" [.expr "..." [.sym "kwargs"]], .expr "..." [.sym "args"]]]]
      .ok (.expr "toplevel" [if exportOld then .expr "export" [Ex.esc old] else .nothing, replaceLinenums ex])

/-- The `@deprecate` docstring: `@deprecate f(args) g(args)` defines `f(args)` that warns
"`f(args)` is deprecated, use `g(args)` instead." and evaluates `g(args)`, exporting `f`
unless `export_old` is false; `T{...}(...)` and `where` signatures name the function
`T` and the `:call` inside the `where`; a non-symbol function with `export_old` and an
`old` that is neither a call, a `where` nor (when exported) a symbol are rejected; a
symbol `old` defines a method forwarding all positional and keyword arguments. -/
def DeprecateContract : Prop :=
  (∀ shw (f : String) (xs : List Ex) (new : Ex),
    deprecate shw (.expr "call" (.sym f :: xs)) new true =
      .ok (.expr "toplevel" [.expr "export" [Ex.esc (.sym f)],
        replaceLinenums (.expr "=" [Ex.esc (.expr "call" (.sym f :: xs)), .expr "block" [.expr "meta" [.sym "noinline"],
          .expr "call" [.sym "depwarn", .str ("`" ++ shw (.expr "call" (.sym f :: xs)) ++ "` is deprecated, use `" ++
            shw (removeLinenums new) ++ "` instead."), singletonName (.sym f)], Ex.esc (removeLinenums new)]])])) ∧
  (∀ shw (f : String) (xs : List Ex) (new : Ex) (b : Bool) (r : Ex),
    deprecate shw (.expr "call" (.sym f :: xs)) new b = .ok r →
    ∃ ys, deprecate shw (.expr "call" (.expr "curly" (.sym f :: ys) :: xs)) new b ≠ .error (.errorException cannotExportMsg)) ∧
  (∀ shw (fn : Ex) (xs : List Ex) (new : Ex),
    (match fn with | .sym _ => false | .expr "curly" (.sym _ :: _) => false | _ => true) = true →
    deprecate shw (.expr "call" (fn :: xs)) new true = .error (.errorException cannotExportMsg)) ∧
  (∀ shw (c : Ex) (ws : List Ex) (new : Ex) (b : Bool),
    (match c with | .expr "call" _ => false | .expr _ _ => true | _ => false) = true →
    deprecate shw (.expr "where" (c :: ws)) new b = .error (.errorException "invalid usage of @deprecate")) ∧
  (∀ shw (ws : List Ex) (new : Ex) (b : Bool),
    deprecate shw (.expr "where" (.expr "call" [] :: ws)) new b = .error .boundsError) ∧
  (∀ shw (f : String) (new : Ex) (b : Bool),
    deprecate shw (.sym f) new b = .ok (.expr "toplevel" [if b then .expr "export" [Ex.esc (.sym f)] else .nothing,
      replaceLinenums (.expr "function" [.expr "call" [Ex.esc (.sym f), .expr "parameters" [.expr "..." [.sym "kwargs"]],
          .expr "..." [.sym "args"]],
        .expr "block" [.expr "meta" [.sym "noinline"],
          .expr "call" [.sym "depwarn", .str ("`" ++ shw (.sym f) ++ "` is deprecated, use `" ++ shw new ++ "` instead."),
            singletonName (.sym f)],
          .expr "call" [Ex.esc new, .expr "parameters" [.expr "..." [.sym "kwargs"]], .expr "..." [.sym "args"]]]])])) ∧
  (∀ shw (old new : Ex), (match old with | .sym _ => false | .expr "call" _ => false | .expr "where" _ => false | _ => true) = true →
    deprecate shw old new true = .error (.errorException cannotExportMsg))

theorem deprecateContract_proven : DeprecateContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro shw f xs new
    simp [deprecate, bind, Except.bind, pure, Except.pure]
  · intro shw f xs new b r _
    refine ⟨[], ?_⟩
    cases b <;> simp [deprecate, bind, Except.bind, pure, Except.pure, cannotExportNonsymbol]
  · intro shw fn xs new h
    cases fn with
    | expr hd as =>
      by_cases hc : hd = "curly"
      · subst hc
        match as with
        | [] => simp [deprecate, bind, Except.bind, pure, Except.pure, cannotExportNonsymbol]
        | t :: ts =>
          cases t <;> simp_all [deprecate, bind, Except.bind, pure, Except.pure, cannotExportNonsymbol]
      · simp [deprecate, hc, bind, Except.bind, pure, Except.pure, cannotExportNonsymbol]
    | _ => simp_all [deprecate, bind, Except.bind, pure, Except.pure, cannotExportNonsymbol]
  · intro shw c ws new b h
    cases c with
    | expr hd as =>
      by_cases hc : hd = "call"
      · subst hc
        cases as with
        | nil => simp at h
        | cons a as => simp_all
      · simp [deprecate, hc, bind, Except.bind, pure, Except.pure]
    | _ => simp at h
  · intro shw ws new b
    simp [deprecate, bind, Except.bind, pure, Except.pure]
  · intro shw f new b
    cases b <;> rfl
  · intro shw old new h
    cases old with
    | expr hd as =>
      by_cases h1 : hd = "call"
      · subst h1; simp at h
      · by_cases h2 : hd = "where"
        · subst h2; simp at h
        · simp [deprecate, deprecate.deprecateOther, h1, h2, cannotExportNonsymbol]
    | sym s => simp at h
    | _ => rfl

/-! ## `depwarn`, `base/deprecated.jl:253-317` -/

/-- One `StackTraces.lookup` result: the function name, whether it is a C frame or
`StackTraces.UNKNOWN`, and the name of the method of its `MethodInstance` if any. -/
structure Frame where
  func : String
  fromC : Bool
  unknown : Bool
  methodName : Option String
  deriving DecidableEq, Repr

/-- A backtrace: each instruction pointer with its inlined frames. -/
abbrev Backtrace := List (Nat × List Frame)

/-- The result of `firstcaller`: the instruction pointer and the frame, `none` for
`StackTraces.UNKNOWN`. -/
abbrev Caller := Nat × Option Frame

/-- The search of `firstcaller(bt, funcsyms)`, `base/deprecated.jl:293-317`: `found`
carries over from one frame to the next. -/
def firstcallerLoop (funcsyms : List String) : Bool → Backtrace → Caller
  | _, [] => (0, none)
  | found, (ip, lkups) :: bt =>
    let rec inner : Bool → List Frame → Sum Caller Bool
      | found, [] => .inr found
      | found, l :: ls =>
        if l.unknown || l.fromC then inner found ls
        else if found then .inl (ip, some l)
        else
          let found := funcsyms.contains l.func ||
            (match l.methodName with | some n => funcsyms.contains n | none => false)
          inner found ls
    match inner found lkups with
    | .inl c => c
    | .inr found => firstcallerLoop funcsyms found bt

/-- `firstcaller(bt, funcsyms)`, `base/deprecated.jl:293-317`. -/
def firstcallerTuple (bt : Backtrace) (funcsyms : List String) : Caller := firstcallerLoop funcsyms false bt

/-- `firstcaller(bt, ::Nothing)`, `base/deprecated.jl:291`. -/
def firstcallerNothing (_bt : Backtrace) : Caller := (0, none)

/-- `firstcaller(bt, funcsym::Symbol)`, `base/deprecated.jl:292`. -/
def firstcallerSym (bt : Backtrace) (funcsym : String) : Caller := firstcallerTuple bt [funcsym]

/-- A log record written by `@logmsg`: level (`true` is `Warn`, `false` is
`BelowMinLevel`), message, `_id = (frame, funcsym)`, `_group = :depwarn` and `maxlog`. -/
structure LogRec where
  warn : Bool
  msg : String
  id : Nat × Option String
  caller : Option Frame
  maxlog : Option Nat
  deriving DecidableEq, Repr

/-- `_depwarn(msg, funcsym, force)`, `base/deprecated.jl:260-289`. `level` is
`JLOptions().depwarn`. -/
def depwarnImpl (level : Nat) (bt : Backtrace) (msg : String) (funcsym : Option String) (force : Bool) :
    M (Option LogRec) :=
  if level = 2 then .error (.errorException msg)
  else
    let warn := force || level == 1
    let (frame, caller) := match funcsym with
      | none => firstcallerNothing bt
      | some f => firstcallerSym bt f
    .ok (some ⟨warn, msg, (frame, funcsym), caller, if funcsym.isNone then none else some 1⟩)

/-- `depwarn(msg, funcsym; force=false)`, `base/deprecated.jl:253-259`: `_depwarn` called
through `@invokelatest`. -/
def depwarn (level : Nat) (bt : Backtrace) (msg : String) (funcsym : Option String) (force : Bool := false) :
    M (Option LogRec) :=
  depwarnImpl level bt msg funcsym force

/-- The `depwarn` docstring and `--depwarn`: with `--depwarn=error` the message is thrown
as an `ErrorException`; otherwise it is logged at `Warn` when `force` or
`--depwarn=yes` (and below every level otherwise), once per call place: the record's id
is the calling frame with `funcsym` and `maxlog = 1`. The calling frame is the first
Julia frame after the innermost frame of `funcsym`. -/
def DepwarnContract : Prop :=
  (∀ bt msg fs force, depwarn 2 bt msg fs force = .error (.errorException msg)) ∧
  (∀ level bt msg f force, level ≠ 2 → ∃ r, depwarn level bt msg (some f) force = .ok (some r) ∧
    r.warn = (force || level == 1) ∧ r.msg = msg ∧ r.maxlog = some 1 ∧ r.id = ((firstcallerSym bt f).1, some f)) ∧
  (∀ level bt msg force, level ≠ 2 → ∃ r, depwarn level bt msg none force = .ok (some r) ∧
    r.maxlog = none ∧ r.id = (0, none) ∧ r.caller = none) ∧
  (∀ bt, firstcallerNothing bt = (0, none)) ∧
  (∀ (f : String) (ip ip' : Nat) (fr fr' : Frame) (rest : Backtrace),
    fr.func = f → fr.fromC = false → fr.unknown = false → fr'.fromC = false → fr'.unknown = false →
    firstcallerSym ((ip, [fr]) :: (ip', [fr']) :: rest) f = (ip', some fr')) ∧
  (∀ (f : String) (ip : Nat) (fr fr' : Frame) (rest : Backtrace),
    fr.func = f → fr.fromC = false → fr.unknown = false → fr'.fromC = false → fr'.unknown = false →
    firstcallerSym ((ip, [fr, fr']) :: rest) f = (ip, some fr')) ∧
  (∀ (fs : List String) (bt : Backtrace), (∀ p ∈ bt, ∀ l ∈ p.2, l.unknown = true) → firstcallerTuple bt fs = (0, none))

theorem firstcaller_unknown (fs : List String) : ∀ (found : Bool) (bt : Backtrace),
    (∀ p ∈ bt, ∀ l ∈ p.2, l.unknown = true) → firstcallerLoop fs found bt = (0, none) := by
  intro found bt
  induction bt generalizing found with
  | nil => intro _; rfl
  | cons p bt ih =>
    intro h
    obtain ⟨ip, lk⟩ := p
    have hin : ∀ found, firstcallerLoop.inner fs ip found lk = .inr found := by
      have hl : ∀ l ∈ lk, l.unknown = true := h (ip, lk) (List.mem_cons_self ..)
      clear h ih
      induction lk with
      | nil => intro; rfl
      | cons l ls ihl =>
        intro found
        simp only [firstcallerLoop.inner, hl l (List.mem_cons_self ..), Bool.true_or, ↓reduceIte]
        exact ihl (fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')) found
    simp only [firstcallerLoop, hin]
    exact ih _ (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem depwarnContract_proven : DepwarnContract := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_, fun _ => rfl, ?_, ?_, fun fs bt h => firstcaller_unknown fs false bt h⟩
  · intro level bt msg f force h
    refine ⟨⟨force || level == 1, msg, ((firstcallerSym bt f).1, some f),
      (firstcallerSym bt f).2, some 1⟩, ?_, rfl, rfl, rfl, rfl⟩
    simp [depwarn, depwarnImpl, h]
  · intro level bt msg force h
    refine ⟨⟨force || level == 1, msg, ((firstcallerNothing bt).1, none),
      (firstcallerNothing bt).2, none⟩, ?_, rfl, rfl, rfl⟩
    simp [depwarn, depwarnImpl, h]
  · intro f ip ip' fr fr' rest h1 h2 h3 h4 h5
    simp [firstcallerSym, firstcallerTuple, firstcallerLoop, firstcallerLoop.inner, h1, h2, h3, h4, h5]
  · intro f ip fr fr' rest h1 h2 h3 h4 h5
    simp [firstcallerSym, firstcallerTuple, firstcallerLoop, firstcallerLoop.inner, h1, h2, h3, h4, h5]

/-! ## Binding deprecations, `base/deprecated.jl:319-376` -/

/-- `deprecate(m, s, flag)`, `base/deprecated.jl:319`: `jl_deprecate_binding` sets the
deprecation flag of binding `m.s`. The table maps bindings to flags. -/
def deprecateBinding (tab : List ((String × String) × Nat)) (m s : String) (flag : Nat := 1) :
    List ((String × String) × Nat) :=
  ((m, s), flag) :: tab.filter (fun e => e.1 != (m, s))

/-- The flag of a binding (`0`: not deprecated). -/
def flagOf (tab : List ((String × String) × Nat)) (m s : String) : Nat :=
  ((tab.find? (fun e => e.1 == (m, s))).map (·.2)).getD 0

/-- `@deprecate_binding old new export_old dep_message constant`,
`base/deprecated.jl:346-353`; `dep_message = none` is `:nothing`. -/
def deprecateBindingMacro (str : Ex → String) (mod : String) (old new : Ex) (exportOld : Bool := true)
    (depMessage : Option Ex := none) (constant : Bool := true) : Ex :=
  let depMessage := depMessage.getD (.str (", use " ++ str new ++ " instead."))
  .expr "toplevel" [if exportOld then .expr "export" [Ex.esc old] else .nothing,
    .expr "const" [.expr "=" [Ex.esc (.sym ("_dep_message_" ++ str old)), Ex.esc depMessage]],
    if constant then .expr "const" [.expr "=" [Ex.esc old, Ex.esc new]] else .expr "=" [Ex.esc old, Ex.esc new],
    .expr "call" [.sym "deprecate", .val mod, .expr "quote" [old]]]

/-- `@deprecate_stdlib old mod export_old newname`, `base/deprecated.jl:355-365`.
`root` is `Base.root_module(Base, mod)`, which throws for a module not loaded. -/
def deprecateStdlib (str : Ex → String) (root : Ex → M String) (cur : String) (old mod : Ex)
    (exportOld : Bool := true) (newname : Ex := old) : M Ex := do
  let rename := if str old = str newname then "" else " as `" ++ str newname ++ "`"
  let depMessage := ": it has been moved to the standard library package `" ++ str mod ++ "`" ++ rename ++
    ".\nAdd `using " ++ str mod ++ "` to your imports."
  let m ← root mod
  let new := Ex.gref m (str newname)
  pure (.expr "toplevel" [if exportOld then .expr "export" [Ex.esc old] else .nothing,
    .expr "const" [.expr "=" [Ex.esc (.sym ("_dep_message_" ++ str old)), Ex.esc (.str depMessage)]],
    .expr "const" [.expr "=" [Ex.esc old, Ex.esc new]],
    .expr "call" [.sym "deprecate", .val cur, .expr "quote" [old]]])

/-- `@deprecate_moved old new export_old`, `base/deprecated.jl:367-376`, including the
generated `$eold(args...; kwargs...) = error($emsg)` (`:373`). -/
def deprecateMoved (str : Ex → String) (cur : String) (old new : Ex) (exportOld : Bool := true) : Ex :=
  let emsg := str old ++ " has been moved to the package " ++ str new ++ ".jl.\n" ++
    "Run `Pkg.add(\"" ++ str new ++ "\")` to install it, restart Julia,\n" ++
    "and then run `using " ++ str new ++ "` to load it."
  .expr "toplevel" [
    replaceLinenums (.expr "=" [.expr "call" [Ex.esc old, .expr "parameters" [.expr "..." [.sym "kwargs"]],
      .expr "..." [.sym "args"]], .expr "call" [.sym "error", .str emsg]]),
    if exportOld then .expr "export" [Ex.esc old] else .nothing,
    .expr "call" [.sym "deprecate", .val cur, .expr "quote" [old], .int 2]]

/-- The docstrings: `deprecate(m, s, flag)` sets the flag of exactly that binding;
`@deprecate_binding old new` makes `old` a constant alias of `new` (a plain global when
`constant` is false), exported unless `export_old` is false, with the message ", use
new instead." unless one is given, and marks it deprecated; `@deprecate_stdlib` points
`old` at the binding in the standard library with a message naming it;
`@deprecate_moved` defines `old` to throw a message naming the package and marks the
binding with flag 2. -/
def BindingContract : Prop :=
  (∀ tab m s flag, flagOf (deprecateBinding tab m s flag) m s = flag) ∧
  (∀ tab m s m' s' flag, (m', s') ≠ (m, s) → flagOf (deprecateBinding tab m s flag) m' s' = flagOf tab m' s') ∧
  (∀ str mod old new, deprecateBindingMacro str mod old new =
    .expr "toplevel" [.expr "export" [Ex.esc old],
      .expr "const" [.expr "=" [Ex.esc (.sym ("_dep_message_" ++ str old)), Ex.esc (.str (", use " ++ str new ++ " instead."))]],
      .expr "const" [.expr "=" [Ex.esc old, Ex.esc new]],
      .expr "call" [.sym "deprecate", .val mod, .expr "quote" [old]]]) ∧
  (∀ str mod old new msg, (deprecateBindingMacro str mod old new false (some msg) false) =
    .expr "toplevel" [.nothing, .expr "const" [.expr "=" [Ex.esc (.sym ("_dep_message_" ++ str old)), Ex.esc msg]],
      .expr "=" [Ex.esc old, Ex.esc new], .expr "call" [.sym "deprecate", .val mod, .expr "quote" [old]]]) ∧
  (∀ str root cur old mod m, root mod = .ok m →
    ∃ r, deprecateStdlib str root cur old mod = .ok r ∧
      r = .expr "toplevel" [.expr "export" [Ex.esc old],
        .expr "const" [.expr "=" [Ex.esc (.sym ("_dep_message_" ++ str old)),
          Ex.esc (.str (": it has been moved to the standard library package `" ++ str mod ++ "`" ++
            ".\nAdd `using " ++ str mod ++ "` to your imports."))]],
        .expr "const" [.expr "=" [Ex.esc old, Ex.esc (.gref m (str old))]],
        .expr "call" [.sym "deprecate", .val cur, .expr "quote" [old]]]) ∧
  (∀ str root cur old mod e, root mod = .error e → deprecateStdlib str root cur old mod = .error e) ∧
  (∀ str cur old new b, ∃ body, deprecateMoved str cur old new b =
    .expr "toplevel" [body, if b then .expr "export" [Ex.esc old] else .nothing,
      .expr "call" [.sym "deprecate", .val cur, .expr "quote" [old], .int 2]])

theorem bindingContract_proven : BindingContract := by
  refine ⟨?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_, ?_, fun _ _ _ _ _ => ⟨_, rfl⟩⟩
  · intro tab m s flag; simp [flagOf, deprecateBinding]
  · intro tab m s m' s' flag hne
    simp only [flagOf, deprecateBinding, List.find?_cons]
    have hb : ((m, s) == (m', s')) = false := beq_eq_false_iff_ne.mpr (fun h => hne h.symm)
    rw [hb]
    simp only
    congr 2
    induction tab with
    | nil => rfl
    | cons e es ih =>
      by_cases he : e.1 = (m, s)
      · have h2 : (e.1 == (m', s')) = false := by rw [he]; exact hb
        rw [List.filter_cons_of_neg (by simp [he]), ih, List.find?_cons_of_neg (by simp [h2])]
      · rw [List.filter_cons_of_pos (by simp [he]), List.find?_cons, List.find?_cons, ih]
  · intro str root cur old mod m h
    exact ⟨_, by simp [deprecateStdlib, h, bind, Except.bind, pure, Except.pure], rfl⟩
  · intro str root cur old mod e h
    simp [deprecateStdlib, h, bind, Except.bind]

end JuliaLean.MiscCov.Deprecated
