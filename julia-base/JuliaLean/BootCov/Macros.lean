import JuliaLean.BootCov.Basic

/-!
Macros of `base/boot.jl` and `base/essentials.jl` (master `bbfa0ce4150`) as
functions from their arguments (and `__module__`, `__source__`) to the `Expr`
they return, plus the small doc-system helpers of `Core`.
-/

namespace JuliaLean.BootCov.Macros

open JuliaLean
open JuliaLean.BootCov

/-- The eleven flags of `Expr(:purity, ...)`, in source order. -/
structure EffectFlags where
  consistent : Bool
  effectFree : Bool
  nothrow : Bool
  terminatesGlobally : Bool
  terminatesLocally : Bool
  notaskstate : Bool
  inaccessiblememonly : Bool
  noub : Bool
  noubIfNoinbounds : Bool
  consistentOverlay : Bool
  nortcall : Bool
  deriving Repr, DecidableEq

def EffectFlags.toList (f : EffectFlags) : List JVal :=
  [f.consistent, f.effectFree, f.nothrow, f.terminatesGlobally, f.terminatesLocally,
    f.notaskstate, f.inaccessiblememonly, f.noub, f.noubIfNoinbounds, f.consistentOverlay,
    f.nortcall].map JVal.bool

/-- `@_total_meta()`, `base/boot.jl:333-346`. -/
def coreTotalMeta : EffectFlags := ⟨true, true, true, true, false, true, true, true, false, false, true⟩
/-- `@_foldable_meta()`, `base/boot.jl:348-361`. -/
def coreFoldableMeta : EffectFlags := ⟨true, true, false, true, false, true, true, true, false, false, true⟩
/-- `@_total_meta()`, `base/essentials.jl:196-209`. -/
def baseTotalMeta : EffectFlags := ⟨true, true, true, true, false, true, true, true, false, false, true⟩
/-- `@_foldable_meta()`, `base/essentials.jl:211-224`. -/
def baseFoldableMeta : EffectFlags := ⟨true, true, false, true, false, true, true, true, false, false, true⟩
/-- `@_terminates_locally_meta()`, `base/essentials.jl:226-239`. -/
def baseTerminatesLocallyMeta : EffectFlags := ⟨false, false, false, false, true, false, false, false, false, false, false⟩
/-- `@_terminates_globally_meta()`, `base/essentials.jl:241-254`. -/
def baseTerminatesGloballyMeta : EffectFlags := ⟨false, false, false, true, true, false, false, false, false, false, false⟩
/-- `@_terminates_globally_notaskstate_meta()`, `base/essentials.jl:256-269`. -/
def baseTerminatesGloballyNotaskstateMeta : EffectFlags := ⟨false, false, false, true, true, true, false, false, false, false, false⟩
/-- `@_terminates_globally_noub_meta()`, `base/essentials.jl:271-284`. -/
def baseTerminatesGloballyNoubMeta : EffectFlags := ⟨false, false, false, true, true, false, false, true, false, false, false⟩
/-- `@_effect_free_terminates_locally_meta()`, `base/essentials.jl:286-299`. -/
def baseEffectFreeTerminatesLocallyMeta : EffectFlags := ⟨false, true, false, false, true, false, false, false, false, false, false⟩
/-- `@_nothrow_noub_meta()`, `base/essentials.jl:301-314`. -/
def baseNothrowNoubMeta : EffectFlags := ⟨false, false, true, false, false, false, false, true, false, false, false⟩
/-- `@_nothrow_meta()`, `base/essentials.jl:316-329`. -/
def baseNothrowMeta : EffectFlags := ⟨false, false, true, false, false, false, false, false, false, false, false⟩
/-- `@_noub_meta()`, `base/essentials.jl:331-344`. -/
def baseNoubMeta : EffectFlags := ⟨false, false, false, false, false, false, false, true, false, false, false⟩
/-- `@_notaskstate_meta()`, `base/essentials.jl:346-359`. -/
def baseNotaskstateMeta : EffectFlags := ⟨false, false, false, false, false, true, false, false, false, false, false⟩
/-- `@_noub_if_noinbounds_meta()`, `base/essentials.jl:361-374`. -/
def baseNoubIfNoinboundsMeta : EffectFlags := ⟨false, false, false, false, false, false, false, false, true, false, false⟩

/-- The expansion of an effect macro: `_is_internal(__module__) && Expr(:meta, Expr(:purity, ...))`. -/
def effectMeta (internal : Bool) (f : EffectFlags) : JVal :=
  if internal then .expr "meta" [.expr "purity" f.toList] else .bool false

/-- `Core._is_internal(m) = m === Core`, `base/boot.jl:331`. -/
def coreIsInternal (m : String) : Bool := m == "Core"

/-- `Base._nameof(m)` (`jl_module_name`), `base/essentials.jl:188`, and `Base.nameof(m::Module)`
(line 419); a module is identified by its name here. -/
def nameofModule (m : String) : String := m

/-- `Base._is_internal(m)`, `base/essentials.jl:190-193`; `baseRelative m` is
`jl_base_relative_to(m)`. -/
def baseIsInternal (baseRelative : String → String) (m : String) : Bool :=
  nameofModule m == "Base" || nameofModule (baseRelative m) == "Compiler"

/-- The `EffectsOverride` that `@assume_effects` builds for a list of settings
(`compute_assumed_setting`, `base/expr.jl:995-1031`), starting from no assumptions. -/
def none_ : EffectFlags := ⟨false, false, false, false, false, false, false, false, false, false, false⟩
def assumeSetting (o : EffectFlags) : String → EffectFlags
  | "consistent" => { o with consistent := true }
  | "effect_free" => { o with effectFree := true }
  | "nothrow" => { o with nothrow := true }
  | "terminates_globally" => { o with terminatesGlobally := true }
  | "terminates_locally" => { o with terminatesLocally := true }
  | "notaskstate" => { o with notaskstate := true }
  | "inaccessiblememonly" => { o with inaccessiblememonly := true }
  | "noub" => { o with noub := true }
  | "noub_if_noinbounds" => { o with noubIfNoinbounds := true }
  | "foldable" =>
    { o with consistent := true, effectFree := true, terminatesGlobally := true, noub := true, nortcall := true }
  | "total" =>
    { o with consistent := true, effectFree := true, nothrow := true, terminatesGlobally := true, notaskstate := true, inaccessiblememonly := true, noub := true, nortcall := true }
  | _ => o
def assumeEffects (settings : List String) : EffectFlags := settings.foldl assumeSetting none_

/-- `@nospecialize(x)` in `Core`, `base/boot.jl:324-326`. -/
def coreNospecialize (x : JVal) : JVal := .expr "escape" [.expr "meta" [.sym "nospecialize", x]]
/-- `@latestworld`, `@inline`, `@noinline`, `@nospecializeinfer`, `@_boundscheck`,
`base/boot.jl:329`, 363-367. -/
def latestworld : JVal := .expr "latestworld" []
def inlineMacro : JVal := .expr "meta" [.sym "inline"]
def noinlineMacro : JVal := .expr "meta" [.sym "noinline"]
def nospecializeinferMacro : JVal := .expr "meta" [.sym "nospecializeinfer"]
def boundscheckMarker : JVal := .expr "boundscheck" []

/-- `Expr(args...) = _expr(args...)`, `base/boot.jl:327`: the head must be a `Symbol`. -/
def exprCtor : List JVal → R JVal
  | [] => .error (.argument "too few arguments")
  | .sym h :: args => .ok (.expr h args)
  | _ :: _ => .error (.typeError "Expr")

/-- `@nospecialize(vars...)` and `@specialize(vars...)`, `base/essentials.jl:125-151`:
a single `x = v` argument becomes `Expr(:kw, x, v)`. -/
def kwOf : JVal → JVal
  | .expr "=" args => .expr "kw" args
  | v => v
def fixKw : List JVal → List JVal
  | [v] => [kwOf v]
  | vars => vars
def nospecialize (vars : List JVal) : JVal :=
  .expr "escape" [.expr "meta" (.sym "nospecialize" :: fixKw vars)]
def specialize (vars : List JVal) : JVal :=
  .expr "escape" [.expr "meta" (.sym "specialize" :: fixKw vars)]

/-- `@isdefined(s::Symbol)`, `base/essentials.jl:184-186`. -/
def isdefinedMacro (s : String) : JVal := .expr "escape" [.expr "isdefined" [.sym s]]

/-- `@_gc_preserve_begin(arg1)` and `@_gc_preserve_end(token)`, `base/essentials.jl:46-52`. -/
def gcPreserveBegin (a : JVal) : JVal := .expr "gc_preserve_begin" [esc a]
def gcPreserveEnd (t : JVal) : JVal := .expr "gc_preserve_end" [esc t]

/-- `@_propagate_inbounds_meta` and `@_nospecializeinfer_meta`, `base/essentials.jl:377-382`. -/
def propagateInboundsMeta : JVal := .expr "meta" [.sym "inline", .sym "propagate_inbounds"]
def nospecializeinferMeta : JVal := .expr "meta" [.sym "nospecializeinfer"]

/-- `@eval(ex)` and `@eval(mod, ex)`, `base/essentials.jl:488-501`. -/
def evalMacro2 (mod ex : JVal) : JVal :=
  .expr "let" [.expr "=" [.sym "eval_local_result",
      .expr "escape" [.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]]]],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]
def evalMacro1 (module_ : String) (ex : JVal) : JVal := evalMacro2 (.module_ module_) ex

/-- `@boundscheck(blk)` and `@inbounds(blk)`, `base/essentials.jl:939-977`. -/
def boundscheckMacro (blk : JVal) : JVal := .expr "if" [.expr "boundscheck" [], esc blk]
def inboundsMacro (blk : JVal) : JVal :=
  .expr "block" [.expr "inbounds" [.bool true], .expr "local" [.expr "=" [.sym "val", esc blk]],
    .expr "inbounds" [.sym "pop"], .sym "val"]

/-- `@label(name::Symbol)`, `base/essentials.jl:1020-1023`. -/
def label1 (name : String) : R JVal :=
  if name = "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _` is not allowed")
  else .ok (esc (.expr "symboliclabel" [.sym name]))

/-- `@label(name::Symbol, body)`, `base/essentials.jl:1025-1042`: the body of a `for` or
`while` loop is wrapped in a `name#cont` block so `continue name` can target it. -/
def label2 (name : String) (body : JVal) : R JVal :=
  if name = "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (a1 :: a2 :: _) =>
        .expr "for" [a1, .expr "symbolicblock" [.sym (name ++ "#cont"), a2]]
      | .expr "while" (a1 :: a2 :: _) =>
        .expr "while" [a1, .expr "symbolicblock" [.sym (name ++ "#cont"), a2]]
      | b => b
    .ok (esc (.expr "symbolicblock" [.sym name, body]))

/-- `@label(body)`, `base/essentials.jl:1044-1048`. -/
def label0 (body : JVal) : JVal := esc (.expr "symbolicblock" [.sym "loop-exit", body])

/-- `@goto(name)`, `base/essentials.jl:1058-1060`. -/
def gotoMacro (name : String) : JVal := esc (.expr "symbolicgoto" [.sym name])

/-- `@__LINE__`, `base/essentials.jl:1568-1570`: the line of `__source__`. -/
def lineMacro (source : JVal) : R JVal :=
  match source with
  | .lineNode l _ => .ok (.int l)
  | _ => .error (.method "getproperty")

/-- `@world(sym, world)`, `base/essentials.jl:1646-1660`. -/
def worldMacro (module_ : String) (sym world : JVal) : R JVal :=
  let world := if (match world with | .sym "∞" => true | _ => false)
    then JVal.expr "call" [.opaque 0] else world
  match sym with
  | .sym s => .ok (.expr "call" [.opaque 1, esc world, .quoteNode (.globalRef module_ s)])
  | .globalRef m n => .ok (.expr "call" [.opaque 1, esc world, .quoteNode (.globalRef m n)])
  | .expr "." [a, .quoteNode (.sym n)] =>
    .ok (.expr "call" [.opaque 1, esc world, .expr "call" [.opaque 2, esc a, .quoteNode (.sym n)]])
  | _ => .error (.error "`@world` requires a symbol or GlobalRef")

/-! ## Doc-system basics in `Core`, `base/boot.jl:940-960` -/

/-- `@doc(x...)`, lines 941-945; `atdoc` is the current `Core.atdoc` hook. -/
def docMacro (atdoc : JVal → String → List JVal → JVal) (source : JVal) (module_ : String)
    (x : List JVal) : JVal :=
  let docex := atdoc source module_ x
  match docex with
  | .expr "escape" _ => docex
  | _ => .expr "escape" [.expr "hygienic-scope" [docex, .module_ "Core", source]]

/-- `@__doc__(x)`, lines 946-948. -/
def docMarker (x : JVal) : JVal := .expr "escape" [.expr "block" [.expr "meta" [.sym "doc"], x]]

/-- `isbasicdoc(x)`, line 950. -/
def isbasicdoc : JVal → Bool
  | .expr "." _ => true
  | .quoteNode _ => true
  | .sym _ => true
  | _ => false

/-- `firstarg(arg1, args...) = arg1`, line 951. -/
def firstarg (arg1 : JVal) (_ : List JVal) : JVal := arg1

/-- `iscallexpr(ex::Expr)` and `iscallexpr(ex) = false`, lines 952-953. -/
def iscallexpr : JVal → R Bool
  | .expr "where" (a :: _) => iscallexpr a  -- `firstarg(ex.args...)` is `a`
  | .expr "where" [] => .error (.method "firstarg")
  | .expr "call" _ => .ok true
  | _ => .ok false

/-- `ignoredoc(source, mod, str, expr)`, lines 954-957. -/
def ignoredoc (expr : JVal) : R JVal := do
  let c ← iscallexpr expr
  if isbasicdoc expr || c then pure (.expr "escape" [.nothing]) else pure (.expr "escape" [expr])

/-- `atdoc!(λ) = global atdoc = λ`, line 960: returns `λ` and installs it. -/
def atdocBang {α : Type} (_old : α) (lam : α) : α × α := (lam, lam)

end JuliaLean.BootCov.Macros
