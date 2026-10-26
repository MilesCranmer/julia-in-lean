import JuliaLean.BootCov.Macros

/-!
Properties of the macros and doc helpers of `base/boot.jl` and `base/essentials.jl`.
-/

namespace JuliaLean.BootCov.Macros

open JuliaLean
open JuliaLean.BootCov

/-- Close `assumeEffects` under the implication `terminates_globally → terminates_locally`. -/
def implied (f : EffectFlags) : EffectFlags :=
  { f with terminatesLocally := f.terminatesLocally || f.terminatesGlobally }

/-- The `Base` effect macros with the `@assume_effects` settings their comments name
(`base/essentials.jl:195-374`). -/
def baseEffectTable : List (EffectFlags × List String) :=
  [(baseTotalMeta, ["total"]), (baseFoldableMeta, ["foldable"]),
   (baseTerminatesLocallyMeta, ["terminates_locally"]),
   (baseTerminatesGloballyMeta, ["terminates_globally"]),
   (baseTerminatesGloballyNotaskstateMeta, ["terminates_globally", "notaskstate"]),
   (baseTerminatesGloballyNoubMeta, ["terminates_globally", "noub"]),
   (baseEffectFreeTerminatesLocallyMeta, ["effect_free", "terminates_locally"]),
   (baseNothrowNoubMeta, ["nothrow", "noub"]), (baseNothrowMeta, ["nothrow"]),
   (baseNoubMeta, ["noub"]), (baseNotaskstateMeta, ["notaskstate"]),
   (baseNoubIfNoinboundsMeta, ["noub_if_noinbounds"])]

/-- Each `Base` effect macro "can be used in place of" its `@assume_effects` settings, as
its comment says: inside `Base` or `Compiler` it asserts exactly those effects (up to
`terminates_globally` implying `terminates_locally`), and elsewhere it expands to `false`. -/
def BaseEffectMetasMatchAssume : Prop :=
  ∀ p ∈ baseEffectTable, ∀ (baseRelative : String → String) (m : String),
    effectMeta (baseIsInternal baseRelative m) p.1 =
      (if baseIsInternal baseRelative m then .expr "meta" [.expr "purity" p.1.toList]
       else .bool false) ∧
    implied p.1 = implied (assumeEffects p.2)

theorem baseEffectMetasMatchAssume_refuted : ¬ BaseEffectMetasMatchAssume := by
  intro h
  have := (h (baseFoldableMeta, ["foldable"]) (by simp [baseEffectTable]) id "Base").2
  revert this
  decide

/-- `Core.@_total_meta` and `Core.@_foldable_meta` (`base/boot.jl:331-361`) expand to the
purity expression only inside `Core` and to `false` in every other module; the `:total`
form asserts exactly the effects of `@assume_effects :total`. -/
def CoreEffectMetas : Prop :=
  (∀ m, coreIsInternal m = true ↔ m = "Core") ∧
  (∀ m f, m ≠ "Core" → effectMeta (coreIsInternal m) f = .bool false) ∧
  (∀ f, effectMeta (coreIsInternal "Core") f = .expr "meta" [.expr "purity" f.toList]) ∧
  coreTotalMeta = assumeEffects ["total"] ∧
  coreFoldableMeta = { assumeEffects ["foldable"] with notaskstate := true, inaccessiblememonly := true }

theorem coreEffectMetas : CoreEffectMetas := by
  refine ⟨?_, ?_, fun _ => rfl, by decide, by decide⟩
  · intro m; simp [coreIsInternal]
  · intro m f h; simp [effectMeta, coreIsInternal, h]

/-- The marker macros of `Core` (`base/boot.jl:324-367`) expand to the documented
expressions, and `Expr(head, args...)` (line 327) requires a `Symbol` head and at least one
argument. -/
def CoreMarkerMacros : Prop :=
  (∀ x, coreNospecialize x = .expr "escape" [.expr "meta" [.sym "nospecialize", x]]) ∧
  latestworld = .expr "latestworld" [] ∧ inlineMacro = .expr "meta" [.sym "inline"] ∧
  noinlineMacro = .expr "meta" [.sym "noinline"] ∧
  nospecializeinferMacro = .expr "meta" [.sym "nospecializeinfer"] ∧
  boundscheckMarker = .expr "boundscheck" [] ∧
  (∀ h args, exprCtor (.sym h :: args) = .ok (.expr h args)) ∧
  (∀ h args, (∀ s, h ≠ .sym s) → exprCtor (h :: args) = .error (.typeError "Expr")) ∧
  (∃ msg, exprCtor [] = .error (.argument msg))

theorem coreMarkerMacros : CoreMarkerMacros := by
  refine ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_, ⟨_, rfl⟩⟩
  intro h args hh
  cases h with
  | sym s => exact absurd rfl (hh s)
  | _ => rfl

/-- The marker macros of `Base` (`base/essentials.jl:46-186`, 377-382, 488-501, 893,
939-977, 1020-1060, 1568-1570, 1646-1660) expand to the documented expressions:
`@nospecialize x=v` becomes a `:kw` argument only for a single argument; `@label _` and
`@label _ body` are rejected; a labelled `for` or `while` loop has its body wrapped in a
`name#cont` block; and `@world` accepts exactly a symbol, a `GlobalRef` or `a.b`. -/
def BaseMarkerMacros : Prop :=
  (∀ x v, nospecialize [.expr "=" [x, v]] =
    .expr "escape" [.expr "meta" [.sym "nospecialize", .expr "kw" [x, v]]]) ∧
  (∀ x v, specialize [.expr "=" [x, v]] =
    .expr "escape" [.expr "meta" [.sym "specialize", .expr "kw" [x, v]]]) ∧
  (∀ a b rest, nospecialize (a :: b :: rest) =
    .expr "escape" [.expr "meta" (.sym "nospecialize" :: a :: b :: rest)] ∧
    specialize (a :: b :: rest) = .expr "escape" [.expr "meta" (.sym "specialize" :: a :: b :: rest)]) ∧
  (∀ s, isdefinedMacro s = .expr "escape" [.expr "isdefined" [.sym s]]) ∧
  (∀ a, gcPreserveBegin a = .expr "gc_preserve_begin" [esc a] ∧
    gcPreserveEnd a = .expr "gc_preserve_end" [esc a]) ∧
  (∀ e, esc e = .expr "escape" [e]) ∧
  propagateInboundsMeta = .expr "meta" [.sym "inline", .sym "propagate_inbounds"] ∧
  nospecializeinferMeta = .expr "meta" [.sym "nospecializeinfer"] ∧
  (∀ m e, evalMacro1 m e = evalMacro2 (.module_ m) e) ∧
  (∀ md e, evalMacro2 md e = .expr "let" [.expr "=" [.sym "eval_local_result",
      .expr "escape" [.expr "call" [.globalRef "Core" "eval", md, .expr "quote" [e]]]],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ b, boundscheckMacro b = .expr "if" [.expr "boundscheck" [], esc b]) ∧
  (∀ b, inboundsMacro b = .expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", esc b]], .expr "inbounds" [.sym "pop"], .sym "val"]) ∧
  (∃ msg, label1 "_" = .error (.error msg)) ∧
  (∀ n, n ≠ "_" → label1 n = .ok (esc (.expr "symboliclabel" [.sym n]))) ∧
  (∀ b, ∃ msg, label2 "_" b = .error (.error msg)) ∧
  (∀ n it body rest, n ≠ "_" → label2 n (.expr "for" (it :: body :: rest)) =
    .ok (esc (.expr "symbolicblock" [.sym n,
      .expr "for" [it, .expr "symbolicblock" [.sym (n ++ "#cont"), body]]]))) ∧
  (∀ n c body rest, n ≠ "_" → label2 n (.expr "while" (c :: body :: rest)) =
    .ok (esc (.expr "symbolicblock" [.sym n,
      .expr "while" [c, .expr "symbolicblock" [.sym (n ++ "#cont"), body]]]))) ∧
  (∀ b, label0 b = esc (.expr "symbolicblock" [.sym "loop-exit", b])) ∧
  (∀ n, gotoMacro n = esc (.expr "symbolicgoto" [.sym n])) ∧
  (∀ l f, lineMacro (.lineNode l f) = .ok (.int l)) ∧
  (∀ m s w, (∀ t, w ≠ .sym t) → worldMacro m (.sym s) w =
    .ok (.expr "call" [.opaque 1, esc w, .quoteNode (.globalRef m s)])) ∧
  (∀ m w n, ∃ msg, worldMacro m (.int n) w = .error (.error msg))

theorem baseMarkerMacros : BaseMarkerMacros := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ => rfl,
    fun _ => ⟨rfl, rfl⟩, fun _ => rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ => rfl, ⟨_, rfl⟩, ?_, fun _ => ⟨_, rfl⟩, ?_, ?_, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, ?_, fun _ _ _ => ⟨_, rfl⟩⟩
  · intro n hn; simp [label1, hn]
  · intro n it body rest hn; simp [label2, hn]
  · intro n c body rest hn; simp [label2, hn]
  · intro m s w hw
    cases w with
    | sym t => exact absurd rfl (hw t)
    | _ => rfl

/-- The `Core` doc-system helpers (`base/boot.jl:941-960`): `isbasicdoc` accepts exactly
`a.b` expressions, `QuoteNode`s and `Symbol`s; `iscallexpr` sees through `where` to a
`:call` head; `ignoredoc` drops basic and call documentation targets and keeps every other
expression; `@doc` returns an `:escape` result of the hook unchanged and wraps any other
result in a hygienic scope; `@__doc__ x` marks `x` with `Expr(:meta, :doc)`; `atdoc!`
installs and returns the new hook. -/
def DocHelpers : Prop :=
  (∀ args, isbasicdoc (.expr "." args) = true) ∧
  (∀ v, isbasicdoc (.quoteNode v) = true) ∧ (∀ s, isbasicdoc (.sym s) = true) ∧
  (∀ n args, n ≠ "." → isbasicdoc (.expr n args) = false) ∧
  (∀ a args, firstarg a args = a) ∧
  (∀ args, iscallexpr (.expr "call" args) = .ok true) ∧
  (∀ a rest, iscallexpr (.expr "where" (a :: rest)) = iscallexpr a) ∧
  (∀ v, (∀ h args, v ≠ .expr h args) → iscallexpr v = .ok false) ∧
  (∀ e, isbasicdoc e = true → ignoredoc e = (iscallexpr e).map fun _ => .expr "escape" [.nothing]) ∧
  (∀ e, isbasicdoc e = false → iscallexpr e = .ok false → ignoredoc e = .ok (.expr "escape" [e])) ∧
  (∀ (atdoc : JVal → String → List JVal → JVal) src m x args,
    atdoc src m x = .expr "escape" args → docMacro atdoc src m x = .expr "escape" args) ∧
  (∀ (atdoc : JVal → String → List JVal → JVal) src m x,
    (∀ args, atdoc src m x ≠ .expr "escape" args) →
    docMacro atdoc src m x = .expr "escape" [.expr "hygienic-scope" [atdoc src m x, .module_ "Core", src]]) ∧
  (∀ x, docMarker x = .expr "escape" [.expr "block" [.expr "meta" [.sym "doc"], x]]) ∧
  (∀ {α : Type} (old new : α), atdocBang old new = (new, new))

theorem docHelpers : DocHelpers := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, fun _ => rfl, fun _ _ => rfl⟩
  · intro n args hn
    simp only [isbasicdoc]
    split <;> simp_all
  · intro v hv
    cases v with
    | expr h args => exact absurd rfl (hv h args)
    | _ => rfl
  · intro e he
    cases h : iscallexpr e <;>
      simp [ignoredoc, he, h, bind, Except.bind, pure, Except.pure, Except.map]
  · intro e he hc
    simp [ignoredoc, he, hc, bind, Except.bind, pure, Except.pure]
  · intro atdoc src m x args h
    simp [docMacro, h]
  · intro atdoc src m x h
    simp only [docMacro]

end JuliaLean.BootCov.Macros
