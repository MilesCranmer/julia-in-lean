import JuliaLean.base.expr
import JuliaLean.Proofs.base.expr.LegacyProofs

namespace JuliaLean.ExprReflect

open JuliaLean

def ExprSymbolBodies : Prop :=
  (∀ counter, gensymTag none counter = "##" ++ toString counter) ∧
  (∀ tag counter, gensymTag (some tag) counter = "##" ++ tag ++ "#" ++ toString counter) ∧
  (∀ tags counter, (gensymMany tags counter).length = tags.length) ∧
  (∀ names, (gensymMacro names).map (·.1) = names)

theorem exprSymbolBodies_proven : ExprSymbolBodies := by
  constructor
  · intro counter; rfl
  constructor
  · intros; rfl
  constructor
  · intro tags counter; simp [gensymMany]
  · intro names
    induction names <;> simp [gensymMacro, *]

def ExprIRBodies : Prop := ∀ object fresh,
  (copyIRObject fresh object).kind = object.kind ∧
  (copyIRObject fresh object).immutable = object.immutable ∧
  (isequalIRArg object object = true) ∧
  (isequalIRArg object (copyIRObject fresh object) =
    (object.mutableIds == (copyIRObject fresh object).mutableIds)) ∧
  (∀ codeInfo, (copyCodeInfoFields fresh codeInfo).slotnames = codeInfo.slotnames ∧
    (copyCodeInfoFields fresh codeInfo).code.length = codeInfo.code.length)

theorem exprIRBodies_proven : ExprIRBodies := by
  intro object fresh
  rcases object with ⟨kind, immutable, mutableIds⟩
  cases kind <;> simp [copyIRObject, isequalIRArg]
  all_goals intro codeInfo; cases codeInfo <;> simp [copyCodeInfoFields]

/-! ## base/expr.jl: macro expansion wrappers -/

def ExprMacroexpandBodies : Prop := ∀ recursive legacy,
  macroexpandFlags recursive legacy = ⟨recursive, false, legacy⟩ ∧
  macroexpandBangFlags recursive legacy = ⟨recursive, true, legacy⟩ ∧
  macroexpandMacroFlags.recursive = true ∧ macroexpand1MacroFlags.recursive = false

theorem exprMacroexpandBodies_proven : ExprMacroexpandBodies := by
  unfold ExprMacroexpandBodies
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## base/expr.jl: annotations and effect words -/

def ExprEffectBodies : Prop :=
  (∀ override, decodeEffectBits (effectBits override) = override) ∧
  (∀ setting value, (effectBits (applyEffectSetting default setting value)).length = 11) ∧
  (∀ target, !(assumeEffectsShape target).isEmpty) ∧
  constpropTag .aggressive = .ok "aggressive_constprop" ∧
  constpropTag .none = .ok "no_constprop" ∧
  (∀ tag, annotationTag tag true = "pushmeta:" ++ tag)

theorem exprEffectBodies_proven : ExprEffectBodies := by
  constructor
  · intro override
    rcases override with ⟨a,b,c,d,e,f,g,h,i,j,k⟩
    simp [effectBits, decodeEffectBits]
  constructor
  · intro setting value
    cases setting <;> rfl
  constructor
  · intro target
    cases target <;> decide
  exact ⟨rfl, rfl, fun _ => rfl⟩

def ExprMetaBodies : Prop :=
  (∀ depth expression, unwrapMacroDepth depth expression = expression) ∧
  (∀ args tag, (metaGet args tag false).2 = args) ∧
  (∀ head, isFunctionHead head = (head == "function" || head == "=" || head == "->")) ∧
  generatedMarker = .expr "generated" [] ∧
  (∀ line file, CoverageAst.removeLineNums (.line line file) = .line line file) ∧
  (∀ replacement arguments, CoverageAst.replaceLineNums replacement (.expr "escape" arguments) =
    .expr "escape" arguments) ∧
  (∀ arguments, CoverageAst.isFunctionDef (.expr "function" arguments) = true)

theorem exprMetaBodies_proven : ExprMetaBodies := by
  constructor
  · intro depth expression
    induction depth <;> simp [unwrapMacroDepth, *]
  constructor
  · intro args tag
    simp [metaGet]
  constructor
  · intro head; rfl
  constructor
  · rfl
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  · intros; rfl

/-! ## base/expr.jl: atomic macro lowering -/

def ExprAtomicBodies : Prop := ∀ operation target,
  !(atomicPrimitive operation target).isEmpty ∧
  (atomicOrderCount operation = 1 ∨ atomicOrderCount operation = 2) ∧
  (operation = .fetch → target = .field → atomicPrimitive operation target = "getproperty") ∧
  (operation = .replace → target = .index → atomicPrimitive operation target = "replaceindex_atomic!")

theorem exprAtomicBodies_proven : ExprAtomicBodies := by
  intro operation target
  cases operation <;> cases target <;> decide

/-! ## base/expr.jl: AST classification and generated-function lowering -/

def ExprGeneratedBodies : Prop :=
  (∀ kind, isaAstNode kind = false ↔ kind = .other) ∧
  (∀ kind, quotedShape kind = if kind = .other then "self" else "QuoteNode") ∧
  generatedBodyResult .codeInfo = .ok "CodeInfo:isva+binding-edges" ∧
  generatedBodyResult .syntaxError = .error (.argumentError "syntax") ∧
  generatedBodyResult .impure = .error (.argumentError "generated body is not pure")

theorem exprGeneratedBodies_proven : ExprGeneratedBodies := by
  constructor
  · intro kind; cases kind <;> simp [isaAstNode]
  constructor
  · intro kind; cases kind <;> rfl
  exact ⟨rfl, rfl, rfl⟩

end JuliaLean.ExprReflect
