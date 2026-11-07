import JuliaLean.base.c

/-!
# `base/c.jl` (master `bbfa0ce4150`)

Macros are functions on their argument syntax (`Ex`). The runtime state the C
interface functions touch is explicit: the `defer_signal` counter of the current
thread (`jl_sigatomic_begin`/`jl_sigatomic_end`, `src/jlapi.c:536-553`), the SIGINT
policy (`jl_exit_on_sigint`, `src/signal-handling.c:374-377`), the list of
`jl_extern_c` registrations, and the deprecation warnings written.
-/

namespace JuliaLean.MiscCov.CInterface

open JuliaLean.MiscCov

/-- `unsafe_convert` returns the stored pointer; `@cfunction` requires a literal tuple of
argument types, turns it into `Core.svec(types...)`, and produces a `Ptr{Cvoid}` for a
plain callable and a `CFunction` closure for `$callable`. -/
def CfunctionContract : Prop :=
  (∀ cf : CFunction, unsafeConvert cf = cf.ptr) ∧
  (∀ f rt ats, ats.isExpr "tuple" = false →
    cfunction f rt ats = .error (.argumentError "@cfunction argument types must be a literal tuple")) ∧
  (∀ f rt as, f.isExpr "$" = false →
    cfunction f rt (.expr "tuple" as) =
      .ok (Ex.esc (.expr "cfunction" [.val "Ptr{Cvoid}", .qn f, rt, .expr "call" (.gref "Core" "svec" :: as),
        .qn (.sym "ccall")]))) ∧
  (∀ g gs rt as, cfunction (.expr "$" (g :: gs)) rt (.expr "tuple" as) =
      .ok (Ex.esc (.expr "cfunction" [.gref "Base" "CFunction", g, rt, .expr "call" (.gref "Core" "svec" :: as),
        .qn (.sym "ccall")])))

theorem cfunctionContract_proven : CfunctionContract := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro f rt ats h
    simp [cfunction, h]
  · intro f rt as h
    cases f <;> simp_all [cfunction, Ex.isExpr, argsOf, bind, Except.bind, pure, Except.pure]
  · intro g gs rt as
    simp [cfunction, Ex.isExpr, argsOf, arg, bind, Except.bind, pure, Except.pure]

/-- A thunk that leaves `defer_signal` balanced: it returns with the counter it was
called with. -/
def Balanced {α : Type} (f : Thunk α) : Prop :=
  ∀ r v r', f r = .ok (v, r') → r'.defer = r.defer

/-- The docstrings: `disable_sigint(f)` returns `f()` and leaves the sigatomic depth as
it was, running `f` one level deeper (and writes its deprecation warning when enabled);
`reenable_sigint(f)` inside such a region runs `f` one level shallower and restores the
depth; exceptions of `f` propagate; `exit_on_sigint` sets the policy. -/
def SigintContract : Prop :=
  (∀ (α : Type) (warn : Bool) (f : Thunk α) (r : RT), Balanced f →
    ∀ v r', disableSigint warn f r = .ok (v, r') →
      r'.defer = r.defer ∧ ∃ r1, f (sigatomicBegin (warnState warn r)) = .ok (v, r1)) ∧
  (∀ (α : Type) (warn : Bool) (f : Thunk α) (r : RT) (e : Err),
    f (sigatomicBegin (warnState warn r)) = .error e →
    disableSigint warn f r = .error e) ∧
  (∀ (α : Type) (f : Thunk α) (r : RT), 0 < r.defer → Balanced f →
    ∀ v r', reenableSigint f r = .ok (v, r') → r'.defer = r.defer) ∧
  (∀ (α : Type) (f : Thunk α) (r : RT), r.defer = 0 →
    reenableSigint f r = .error (.errorException "sigatomic_end called in non-sigatomic region")) ∧
  (∀ on r, (exitOnSigint on r).exitOnSigint = on ∧ (exitOnSigint on r).defer = r.defer) ∧
  (∀ r, ∃ r', sigatomicEnd (sigatomicBegin r) = .ok r' ∧ r' = r)

theorem sigintContract_proven : SigintContract := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  · intro α warn f r hb v r' h
    have hw : (warnState warn r).defer = r.defer := by cases warn <;> rfl
    cases hf : f (sigatomicBegin (warnState warn r)) with
    | error e => simp [disableSigint, hf, bind, Except.bind] at h
    | ok p =>
      obtain ⟨res, r1⟩ := p
      have hd := hb _ _ _ hf
      simp only [sigatomicBegin] at hd
      by_cases h0 : r1.defer = 0
      · simp [disableSigint, hf, bind, Except.bind, sigatomicEnd, h0] at h
      · simp [disableSigint, hf, bind, Except.bind, sigatomicEnd, h0, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp; omega, r1, rfl⟩
  · intro α warn f r e h
    simp [disableSigint, bind, Except.bind, h]
  · intro α f r hpos hb v r' h
    have hne : r.defer ≠ 0 := by omega
    cases hf : f { r with defer := r.defer - 1 } with
    | error e => simp [reenableSigint, sigatomicEnd, hne, hf, bind, Except.bind] at h
    | ok p =>
      obtain ⟨res, r1⟩ := p
      have hd := hb _ _ _ hf
      simp [reenableSigint, sigatomicEnd, hne, hf, bind, Except.bind, pure, Except.pure, sigatomicBegin] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hd ⊢
      omega
  · intro α f r h
    simp [reenableSigint, sigatomicEnd, h, bind, Except.bind]
  · intro r
    refine ⟨r, ?_, rfl⟩
    simp [sigatomicEnd, sigatomicBegin]


/-- The `@ccallable` docstring and `base/c.jl:233`: every argument that is not a method
definition (`f(...) = ...` or `function f(...) ... end`) is rejected with
`ErrorException("expected method definition in @ccallable")`. -/
def CcallableErrors : Prop :=
  ∀ (rt def_ : Ex), (∀ sig body, def_ ≠ .expr "function" [sig, body] ∧ def_ ≠ .expr "=" [sig, body]) →
    (match ccallable2 rt def_ with
     | .error (.errorException m) => m = "expected method definition in @ccallable" ∨ m = "@ccallable requires a return type"
     | _ => False)

theorem ccallableErrors_refuted : ¬ CcallableErrors := by
  intro h
  have := h (.sym "Int") (.expr "function" [.sym "f"]) (fun sig body => ⟨by simp, by simp⟩)
  simp [ccallable2, expandCcallable, headOf, bind, Except.bind] at this

/-- The `@ccallable` docstring: for `function f(x::A, y::B)::R ... end` (or the short form)
the expansion evaluates the definition and registers it with `_ccallable(name, R,
Tuple{typeof(f), A, B})`, an unannotated argument having type `Any`; a string first
argument is the C name, any other first argument the return type; a definition with
neither return type is rejected. -/
def CcallableExpand : Prop :=
  (∀ (h : String) (f R body : Ex) (xs : List Ex), (h = "function" ∨ h = "=") →
    (match f with | .expr "::" _ => false | _ => true) = true →
    ccallable1 (.expr h [.expr "::" [.expr "call" (f :: xs), R], body]) =
      .ok (.expr "block" [.expr "macrocall" [.sym "@__doc__", .lnn, Ex.esc (.expr h [.expr "::" [.expr "call" (f :: xs), R], body])],
        .expr "call" [.sym "_ccallable", .nothing, Ex.esc R,
          .expr "curly" (.sym "Tuple" :: Ex.esc (.expr "call" [.sym "typeof", f]) :: (xs.map argType).map Ex.esc)]])) ∧
  (∀ (h : String) (s : String) (f R body : Ex) (xs : List Ex), (h = "function" ∨ h = "=") →
    ccallable2 (.str s) (.expr h [.expr "::" [.expr "call" (f :: xs), R], body]) =
      (match ccallable1 (.expr h [.expr "::" [.expr "call" (f :: xs), R], body]) with
       | .ok (.expr "block" [d, .expr "call" [c, _, r, t]]) => .ok (.expr "block" [d, .expr "call" [c, .str s, r, t]])
       | other => other)) ∧
  (∀ (h : String) (f body : Ex) (xs : List Ex), (h = "function" ∨ h = "=") →
    ccallable1 (.expr h [.expr "call" (f :: xs), body]) = .error (.errorException "@ccallable requires a return type")) ∧
  (∀ a T, argType (.expr "::" [a, T]) = T ∧ argType (.sym "x") = .sym "Any") ∧
  (∀ regs name rt sigt, ccallableRt regs name rt sigt = regs ++ [(name, rt, sigt)])

theorem ccallableExpand_proven : CcallableExpand := by
  refine ⟨?_, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl⟩
  · intro h f R body xs hh hf
    have hh' : (h = "=" ∨ h = "function") := hh.symm
    match f with
    | .expr hd as =>
      by_cases h1 : hd = "::"
      · subst h1; simp at hf
      · simp_all [ccallable1, expandCcallable, headOf, arg, argsOf, nameEx, bind, Except.bind, pure, Except.pure] <;>
          (try split) <;> simp_all
    | .sym _ | .str _ | .int _ | .bool _ | .nothing | .qn _ | .gref _ _ | .lnn | .val _ =>
      simp_all [ccallable1, expandCcallable, headOf, arg, argsOf, nameEx, bind, Except.bind, pure, Except.pure]
  · intro h s f R body xs hh
    have hh' : (h = "=" ∨ h = "function") := hh.symm
    cases f <;> simp_all [ccallable1, ccallable2, expandCcallable, headOf, arg, argsOf, nameEx, bind, Except.bind, pure,
      Except.pure]
  · intro h f body xs hh
    have hh' : (h = "=" ∨ h = "function") := hh.symm
    simp_all [ccallable1, expandCcallable, headOf, bind, Except.bind, pure, Except.pure]

/-- A typed argument `x::T`. -/
def typed (x : Ex × Ex) : Ex := .expr "::" [x.1, x.2]

/-- The `ccall_macro_parse` docstring (`base/c.jl:255-266`): it returns
`(function_name, return_type, arg_types, args)`; for `name(args...)::rt` with a plain
function name, the first component is that name. -/
def CcallMacroParseDoc : Prop :=
  ∀ (f : String) (rt : Ex) (xs : List (Ex × Ex)),
    ∃ p, ccallMacroParse (.single (.expr "::" [.expr "call" (.sym f :: xs.map typed), rt])) = .ok p ∧
      p.func = .sym f ∧ p.rettype = rt ∧ p.types = xs.map (·.2) ∧ p.args = xs.map (·.1)

theorem ccallMacroParseDoc_refuted : ¬ CcallMacroParseDoc := by
  intro h
  obtain ⟨p, hp, hf, _⟩ := h "printf" (.sym "Cvoid") [(.str "%d", .sym "Cstring"), (.sym "value", .sym "Cuint")]
  simp [ccallMacroParse, Ex.isExpr, arg, argsOf, pushargs, pusharg, typed, bind, Except.bind, pure, Except.pure] at hp
  subst hp
  simp at hf

theorem pushargs_typed (acc : List Ex × List Ex) (xs : List (Ex × Ex)) :
    pushargs acc (xs.map typed) = .ok (acc.1 ++ xs.map (·.1), acc.2 ++ xs.map (·.2)) := by
  induction xs generalizing acc with
  | nil => simp [pushargs]
  | cons x xs ih =>
    simp only [List.map_cons, pushargs, pusharg, typed, Ex.isExpr, arg, bind, Except.bind, pure, Except.pure]
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Nat.reduceSub]
    rw [ih]
    simp

/-- What `ccall_macro_parse` does return (`base/c.jl:268-369`) for every typed call:
`((:f,), rt, types, args, gc_safe, cancel, 0)`, with the leading options applied; a
`;` splits off variadic arguments and sets `nreq` to the number of required ones
(at least one); untyped arguments, a missing return type and a non-call are
`ArgumentError`s. -/
def CcallMacroParse : Prop :=
  (∀ (f : String) (rt : Ex) (xs : List (Ex × Ex)),
    (match xs with | [] => true | x :: _ => !(typed x).isExpr "parameters") = true →
    ccallMacroParse (.many [.expr "::" [.expr "call" (.sym f :: xs.map typed), rt]]) =
      .ok ⟨.expr "tuple" [.qn (.sym f)], rt, xs.map (·.2), xs.map (·.1), false, none, 0⟩) ∧
  (∀ (f : String) (rt : Ex) (xs : List (Ex × Ex)) (b : Bool),
    (match xs with | [] => true | x :: _ => !(typed x).isExpr "parameters") = true →
    ccallMacroParse (.many [.expr "=" [.sym "gc_safe", .bool b], .expr "::" [.expr "call" (.sym f :: xs.map typed), rt]]) =
      .ok ⟨.expr "tuple" [.qn (.sym f)], rt, xs.map (·.2), xs.map (·.1), b, none, 0⟩) ∧
  (∀ (f : String) (rt : Ex) (x : Ex × Ex) (xs vs : List (Ex × Ex)),
    ccallMacroParse (.single (.expr "::" [.expr "call" (.sym f :: .expr "parameters" (vs.map typed) :: (x :: xs).map typed), rt])) =
      .ok ⟨.expr "tuple" [.qn (.sym f)], rt, (x :: xs ++ vs).map (·.2), (x :: xs ++ vs).map (·.1), false, none, xs.length + 1⟩) ∧
  (∀ (f : String) (rt : Ex) (vs : List (Ex × Ex)),
    ccallMacroParse (.single (.expr "::" [.expr "call" [.sym f, .expr "parameters" (vs.map typed)], rt])) =
      .error (.argumentError "C ABI prohibits vararg without one required argument")) ∧
  (∀ (c : Ex), (match c with | .expr "::" _ => false | _ => true) = true →
    ccallMacroParse (.single c) = .error (.argumentError "@ccall needs a function signature with a return type")) ∧
  (∀ (f : String) (rt x : Ex), (match x with | .expr "::" _ => false | .expr "parameters" _ => false | _ => true) = true →
    ccallMacroParse (.single (.expr "::" [.expr "call" [.sym f, x], rt])) =
      .error (.argumentError "args in @ccall need type annotations."))

theorem ccallMacroParse_proven : CcallMacroParse := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f rt xs hx
    have hp := pushargs_typed ([], []) xs
    simp only [typed, List.nil_append] at hp
    match xs with
    | [] => simp [ccallMacroParse, options, Ex.isExpr, arg, argsOf, pushargs, bind, Except.bind, pure, Except.pure]
    | x :: xs =>
      simp only [List.map_cons, typed, List.nil_append] at hp ⊢
      simp only [typed, Ex.isExpr] at hx
      simp [ccallMacroParse, options, Ex.isExpr, arg, argsOf, bind, Except.bind, pure, Except.pure, typed, hp]
  · intro f rt xs b hx
    have hp := pushargs_typed ([], []) xs
    cases b <;>
    match xs with
    | [] => simp [ccallMacroParse, options, Ex.isExpr, Ex.isSym, arg, argsOf, pushargs, bind, Except.bind, pure, Except.pure]
    | x :: xs =>
      simp only [List.map_cons, typed, List.nil_append] at hp ⊢
      simp [ccallMacroParse, options, Ex.isExpr, Ex.isSym, arg, argsOf, bind, Except.bind, pure, Except.pure, typed, hp]
  · intro f rt x xs vs
    have hp := pushargs_typed ([], []) (x :: xs)
    have hv := pushargs_typed ((x :: xs).map (·.1), (x :: xs).map (·.2)) vs
    simp only [List.map_cons, typed, List.nil_append] at hp hv ⊢
    simp [ccallMacroParse, Ex.isExpr, arg, argsOf, bind, Except.bind, pure, Except.pure, typed, hp, hv]
  · intro f rt vs
    simp [ccallMacroParse, Ex.isExpr, arg, argsOf, pushargs, bind, Except.bind, pure, Except.pure]
  · intro c hc
    cases c <;> simp_all [ccallMacroParse, Ex.isExpr, bind, Except.bind, pure, Except.pure]
    split at hc <;> simp_all
  · intro f rt x hx
    match x with
    | .expr hd as =>
      by_cases h1 : hd = "::"
      · subst h1; simp at hx
      · by_cases h2 : hd = "parameters"
        · subst h2; simp at hx
        · simp_all [ccallMacroParse, Ex.isExpr, arg, argsOf, pushargs, pusharg, bind, Except.bind, pure, Except.pure] <;>
            (try split) <;> simp_all
    | .sym _ | .str _ | .int _ | .bool _ | .nothing | .qn _ | .gref _ _ | .lnn | .val _ =>
      simp_all [ccallMacroParse, Ex.isExpr, arg, argsOf, pushargs, pusharg, bind, Except.bind, pure, Except.pure]

/-- `ccall_macro_lower` (`base/c.jl:372-401`) and the two macros: the call is
`ccall(esc(func), cconv, esc(rettype), (esc(types)...,), esc(args)...)` with the
convention, effects word without the reset bit, `gc_safe` and `nreq`; with a cancel
handler two `Ptr{Cvoid}` argument types and the handler and state arguments come first
and a nonzero `nreq` grows by two; `@ccall` and `@ccall_effects` lower what
`ccall_macro_parse` returns. -/
def CcallLower : Prop :=
  (∀ p : Parsed, p.cancel = none →
    ccallMacroLower .plain p = .expr "call" ([.sym "ccall", Ex.esc p.func,
      .expr "cconv" [.expr "tuple" [.sym "ccall", .int 0, .bool p.gcSafe], .int p.nreq], Ex.esc p.rettype,
      .expr "tuple" (p.types.map Ex.esc)] ++ p.args.map Ex.esc)) ∧
  (∀ (p : Parsed) (fex sex : Ex), p.cancel = some (fex, sex) →
    ccallMacroLower .plain p = .expr "call" ([.sym "ccall", Ex.esc p.func,
      .expr "cconv" [.expr "tuple" [.sym "ccall", .int 0, .bool p.gcSafe, .bool true],
        .int (if p.nreq > 0 then p.nreq + 2 else 0)], Ex.esc p.rettype,
      .expr "tuple" ([.val "Ptr{Cvoid}", .val "Ptr{Cvoid}"] ++ p.types.map Ex.esc), Ex.esc fex, Ex.esc sex] ++
      p.args.map Ex.esc)) ∧
  (∀ (p : Parsed) (b : Nat), p.cancel = none → b &&& resetSafeBit ≠ 0 →
    ccallMacroLower (.effects b) p = .expr "call" ([.sym "ccall", Ex.esc p.func,
      .expr "cconv" [.expr "tuple" [.sym "ccall", .int (b &&& (0xFFFF ^^^ resetSafeBit)), .bool p.gcSafe,
        .bool false, .bool true], .int p.nreq], Ex.esc p.rettype,
      .expr "tuple" (p.types.map Ex.esc)] ++ p.args.map Ex.esc)) ∧
  (∀ exprs, ccallMacro exprs = (ccallMacroParse (.many exprs)).map (ccallMacroLower .plain)) ∧
  (∀ b exprs, ccallEffects b exprs = (ccallMacroParse (.many exprs)).map (ccallMacroLower (.effects b)))

theorem ccallLower_proven : CcallLower := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p h; simp [ccallMacroLower, h]
  · intro p fex sex h
    simp only [ccallMacroLower, h]
    by_cases hn : p.nreq > 0 <;> simp [hn] <;> omega
  · intro p b h hb; simp [ccallMacroLower, h, hb]
  · intro exprs; simp only [ccallMacro]; cases ccallMacroParse (.many exprs) <;> rfl
  · intro b exprs; simp only [ccallEffects]; cases ccallMacroParse (.many exprs) <;> rfl

end JuliaLean.MiscCov.CInterface
