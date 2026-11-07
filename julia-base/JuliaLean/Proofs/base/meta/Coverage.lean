import JuliaLean.base.meta
import JuliaLean.Proofs.base.meta.LegacyProofs

namespace JuliaLean.ExprReflect

open JuliaLean

def MetaIdentifierBodies : Prop := ∀ oracle first rest,
  isIdentifierModel oracle (first :: rest) =
    (String.ofList (first :: rest) != "true" && String.ofList (first :: rest) != "false" &&
      oracle.start first && rest.all oracle.rest) ∧
  (∀ symbol, isBinaryOperatorModel oracle symbol =
    (oracle.operator symbol && (!oracle.unary symbol || oracle.unaryAndBinary symbol) && symbol != "'")) ∧
  isPostfixOperatorModel oracle ('\'' :: rest) = rest.all oracle.suffix

theorem metaIdentifierBodies_proven : MetaIdentifierBodies := by
  unfold MetaIdentifierBodies
  intros
  exact ⟨rfl, fun _ => rfl, rfl⟩

/-! ## base/meta.jl: AST IO/lowering wrappers and parser interface -/

def MetaAstBodies : Prop :=
  (∀ location children, replaceSourceRoot location (.macrocall 0 children) = .macrocall location children) ∧
  (∀ location children, replaceSourceLoc location (.node "block" children) =
    .node "block" (children.map (replaceSourceLoc location))) ∧
  (∀ request, !(lowerModel request).isEmpty) ∧
  (∀ expression, quot expression = .expr "quote" [expression]) ∧
  (∀ expression, dumpMacroShape expression = "dump(QuoteNode(" ++ expression ++ "))")

theorem metaAstBodies_proven : MetaAstBodies := by
  constructor
  · intros; rfl
  constructor
  · intros; simp [replaceSourceLoc]
  constructor
  · intro request; cases request <;> simp [lowerModel]
  constructor
  · intro expression; rfl
  · intro expression; rfl

def MetaParserBodies : Prop :=
  (∀ length greedy raise oracle, parseAtModel length 0 greedy raise oracle = .error .boundsError) ∧
  (∀ length reply, reply.offset ≤ length → parseWholeModel length false reply =
    if reply.node == .parseError || reply.node == .incomplete then .ok reply.node else .ok .parseError) ∧
  parseMode true = .statement ∧ parseMode false = .atom ∧
  parserSource true = "module:#_internal_julia_parse" ∧
  parserSource false = "Base.VersionedParse"

theorem metaParserBodies_proven : MetaParserBodies := by
  constructor
  · intros; simp [parseAtModel]
  constructor
  · intro length reply hoffset
    simp [parseWholeModel, hoffset]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## base/meta.jl: partial inlining and hygiene helpers -/

def MetaInlineBodies : Prop := ∀ id slotCount slotOffset statementOffset off,
  partiallyInlineNode (.ssa id) slotCount slotOffset statementOffset off = .ssa (id + statementOffset) ∧
  partiallyInlineNode (.goto id) slotCount slotOffset statementOffset off = .goto (id + statementOffset) ∧
  partiallyInlineNode (.enter 0) slotCount slotOffset statementOffset off = .enter 0 ∧
  partiallyInlineNode .boundscheck slotCount slotOffset statementOffset true = .other 0

theorem metaInlineBodies_proven : MetaInlineBodies := by
  unfold MetaInlineBodies
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩

def MetaHygieneBodies : Prop :=
  (∀ frames payload, unescapeFrames (reescapeFrames frames payload) = payload) ∧
  (∀ count, unblockCount count = (count == 1)) ∧
  (∀ head original, uncurlyHead true head original = head)

theorem metaHygieneBodies_proven : MetaHygieneBodies := by
  exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end JuliaLean.ExprReflect
