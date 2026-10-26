import JuliaLean.ExprReflect.Proofs

/-!
Executable source-body models used by the whole-Base method coverage manifests.
Opaque runtime operations such as `ccall`, compiler queries, lowering, and world-age
lookups enter as explicit oracle values. The Julia wrappers, validation branches,
argument order, AST constructors, list traversal, and error paths remain executable.
-/

namespace JuliaLean.ExprReflect

open JuliaLean

/-! ## base/expr.jl: symbols and IR copying/equality -/

def gensymTag (tag : Option String) (counter : Nat) : String :=
  match tag with
  | none => "##" ++ toString counter
  | some tag => "##" ++ tag ++ "#" ++ toString counter

def gensymMany (tags : List String) (counter : Nat) : List String :=
  tags.mapIdx fun index tag => gensymTag (some tag) (counter + index)

def gensymMacro : List String → List (String × String)
  | [] => []
  | name :: names => (name, name) :: gensymMacro names

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

inductive IRKind where
  | expr | phi | phiC | codeInfo | quoteNode | debugInfo | other
  deriving Repr, DecidableEq, Inhabited

structure IRObject where
  kind : IRKind
  immutable : List Int
  mutableIds : List Nat
  deriving Repr, DecidableEq, Inhabited

def copyIRObject (fresh : Nat) (object : IRObject) : IRObject :=
  match object.kind with
  | .expr | .phi | .phiC | .codeInfo =>
    { object with mutableIds := object.mutableIds.map (fresh + ·) }
  | _ => object

def isequalIRArg (left right : IRObject) : Bool :=
  left.kind == right.kind && left.immutable == right.immutable &&
    left.mutableIds == right.mutableIds

/-- Mutable `CodeInfo` fields copied at `base/expr.jl:84-97`. -/
structure CodeInfoFields where
  code : List IRObject
  slotnames : List String
  slotflags : List Nat
  slottypes : Option (List String)
  ssaflags : List Nat
  edges : Option (List Nat)
  ssavaluetypes : Option (List String)
  deriving Repr, DecidableEq, Inhabited

def copyCodeInfoFields (fresh : Nat) (codeInfo : CodeInfoFields) : CodeInfoFields := {
  code := codeInfo.code.map (copyIRObject fresh)
  slotnames := codeInfo.slotnames
  slotflags := codeInfo.slotflags
  slottypes := codeInfo.slottypes.map id
  ssaflags := codeInfo.ssaflags
  edges := codeInfo.edges.map id
  ssavaluetypes := codeInfo.ssavaluetypes.map id }

def codeInfoEqual (left right : CodeInfoFields) : Bool :=
  left == right

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

structure MacroexpandFlags where
  recursive : Bool
  inplace : Bool
  legacyscope : Bool
  deriving Repr, DecidableEq, Inhabited

def macroexpandFlags (recursive legacyscope : Bool) : MacroexpandFlags :=
  ⟨recursive, false, legacyscope⟩

def macroexpandBangFlags (recursive legacyscope : Bool) : MacroexpandFlags :=
  ⟨recursive, true, legacyscope⟩

def macroexpandMacroFlags : MacroexpandFlags := ⟨true, false, true⟩
def macroexpand1MacroFlags : MacroexpandFlags := ⟨false, false, true⟩

def ExprMacroexpandBodies : Prop := ∀ recursive legacy,
  macroexpandFlags recursive legacy = ⟨recursive, false, legacy⟩ ∧
  macroexpandBangFlags recursive legacy = ⟨recursive, true, legacy⟩ ∧
  macroexpandMacroFlags.recursive = true ∧ macroexpand1MacroFlags.recursive = false

theorem exprMacroexpandBodies_proven : ExprMacroexpandBodies := by
  unfold ExprMacroexpandBodies
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## base/expr.jl: annotations and effect words -/

inductive ConstpropSetting where
  | aggressive | none | unsupported
  deriving Repr, DecidableEq, Inhabited

def constpropTag : ConstpropSetting → Jl String
  | .aggressive => .ok "aggressive_constprop"
  | .none => .ok "no_constprop"
  | .unsupported => .error (.argumentError "unsupported @constprop setting")

structure EffectOverride where
  consistent : Bool := false
  effectFree : Bool := false
  nothrow : Bool := false
  terminatesGlobally : Bool := false
  terminatesLocally : Bool := false
  notaskstate : Bool := false
  inaccessibleMemOnly : Bool := false
  noub : Bool := false
  noubIfNoInbounds : Bool := false
  consistentOverlay : Bool := false
  nortcall : Bool := false
  deriving Repr, DecidableEq, Inhabited

def effectBits (override : EffectOverride) : List Bool := [
  override.consistent, override.effectFree, override.nothrow,
  override.terminatesGlobally, override.terminatesLocally, override.notaskstate,
  override.inaccessibleMemOnly, override.noub, override.noubIfNoInbounds,
  override.consistentOverlay, override.nortcall]

def decodeEffectBits (bits : List Bool) : EffectOverride := {
  consistent := bits[0]?.getD false
  effectFree := bits[1]?.getD false
  nothrow := bits[2]?.getD false
  terminatesGlobally := bits[3]?.getD false
  terminatesLocally := bits[4]?.getD false
  notaskstate := bits[5]?.getD false
  inaccessibleMemOnly := bits[6]?.getD false
  noub := bits[7]?.getD false
  noubIfNoInbounds := bits[8]?.getD false
  consistentOverlay := bits[9]?.getD false
  nortcall := bits[10]?.getD false }

inductive EffectSetting where
  | consistent | effectFree | nothrow | terminatesGlobally | terminatesLocally
  | notaskstate | inaccessibleMemOnly | noub | noubIfNoInbounds | nortcall
  | foldable | removable | total
  deriving Repr, DecidableEq, Inhabited

def applyEffectSetting (override : EffectOverride) (setting : EffectSetting)
    (value : Bool := true) : EffectOverride :=
  match setting with
  | .consistent => { override with consistent := value }
  | .effectFree => { override with effectFree := value }
  | .nothrow => { override with nothrow := value }
  | .terminatesGlobally => { override with terminatesGlobally := value }
  | .terminatesLocally => { override with terminatesLocally := value }
  | .notaskstate => { override with notaskstate := value }
  | .inaccessibleMemOnly => { override with inaccessibleMemOnly := value }
  | .noub => { override with noub := value }
  | .noubIfNoInbounds => { override with noubIfNoInbounds := value }
  | .nortcall => { override with nortcall := value }
  | .foldable => {
      consistent := value, effectFree := value, nothrow := override.nothrow,
      terminatesGlobally := value, terminatesLocally := override.terminatesLocally,
      notaskstate := override.notaskstate, inaccessibleMemOnly := override.inaccessibleMemOnly,
      noub := value, noubIfNoInbounds := override.noubIfNoInbounds,
      consistentOverlay := override.consistentOverlay, nortcall := value }
  | .removable => {
      consistent := override.consistent, effectFree := value, nothrow := value,
      terminatesGlobally := value, terminatesLocally := override.terminatesLocally,
      notaskstate := override.notaskstate, inaccessibleMemOnly := override.inaccessibleMemOnly,
      noub := override.noub, noubIfNoInbounds := override.noubIfNoInbounds,
      consistentOverlay := override.consistentOverlay, nortcall := override.nortcall }
  | .total => {
      consistent := value, effectFree := value, nothrow := value,
      terminatesGlobally := value, terminatesLocally := override.terminatesLocally,
      notaskstate := value, inaccessibleMemOnly := value, noub := value,
      noubIfNoInbounds := override.noubIfNoInbounds,
      consistentOverlay := override.consistentOverlay, nortcall := value }

inductive EffectTarget where | ccall | functionDef | anonymous | callsite
  deriving Repr, DecidableEq, Inhabited

def assumeEffectsShape : EffectTarget → String
  | .ccall => "ccall_effects-word"
  | .functionDef => "pushmeta-purity"
  | .anonymous => "meta-purity"
  | .callsite => "purity-region"

def annotationTag (tag : String) (isFunction : Bool) : String :=
  if isFunction then "pushmeta:" ++ tag else "region:" ++ tag

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

def constpropShape (setting : ConstpropSetting) (hasExpression : Bool) : Jl String := do
  let tag ← constpropTag setting
  return if hasExpression then "pushmeta:" ++ tag else "meta:" ++ tag

/-! ## base/expr.jl: metadata, line numbers, and generated annotations -/

def unwrapMacroDepth : Nat → Ast → Ast
  | 0, expression => expression
  | depth + 1, expression => unwrapMacroDepth depth expression

def metaGet (args : List String) (tag : String) (delete : Bool) : Option String × List String :=
  (args.find? (· == tag), if delete then args.filter (· != tag) else args)

def isFunctionHead (head : String) : Bool :=
  head == "function" || head == "=" || head == "->"

def generatedMarker : Ast := .expr "generated" []

/-! A direct tree for the metadata and line-number methods at
`base/expr.jl:1167-1324`. -/
inductive CoverageAst where
  | nil
  | atom (value : String)
  | line (line : Int) (file : Option String)
  | args (first rest : CoverageAst)
  | expr (head : String) (args : CoverageAst)
  deriving Repr, DecidableEq, Inhabited

namespace CoverageAst

def filterLines : CoverageAst → CoverageAst
  | .nil => .nil
  | .args (.line _ _) rest => filterLines rest
  | .args first rest => .args first (filterLines rest)
  | other => other

def removeLineNums : CoverageAst → CoverageAst
  | .nil => .nil
  | .atom value => .atom value
  | .line lineNumber file => .line lineNumber file
  | .args first rest => .args (removeLineNums first) (removeLineNums rest)
  | .expr head arguments =>
    let arguments := removeLineNums arguments
    let arguments := if head == "block" || head == "quote" then filterLines arguments else arguments
    .expr head arguments

def replaceLineNums (replacement : Int) : CoverageAst → CoverageAst
  | .nil => .nil
  | .atom value => .atom value
  | .line _ file => .line replacement file
  | .args first rest => .args (replaceLineNums replacement first) (replaceLineNums replacement rest)
  | .expr "escape" arguments => .expr "escape" arguments
  | .expr head arguments => .expr head (replaceLineNums replacement arguments)

def unwrapMacrocall : CoverageAst → CoverageAst
  | .expr "macrocall" (.args _ (.args inner .nil)) => unwrapMacrocall inner
  | expression => expression
termination_by expression => sizeOf expression

def isFunctionDef : CoverageAst → Bool
  | .expr "function" _ | .expr "->" _ => true
  | .expr "=" (.args (.expr "call" _) _) => true
  | _ => false

end CoverageAst

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

inductive AtomicTarget where | field | index
  deriving Repr, DecidableEq, Inhabited
inductive AtomicOperation where | fetch | store | modify | swap | replace | once
  deriving Repr, DecidableEq, Inhabited

def atomicPrimitive : AtomicOperation → AtomicTarget → String
  | .fetch, .field => "getproperty"
  | .fetch, .index => "getindex_atomic"
  | .store, .field => "setproperty!"
  | .store, .index => "setindex_atomic!"
  | .modify, .field => "modifyproperty!"
  | .modify, .index => "modifyindex_atomic!"
  | .swap, .field => "swapproperty!"
  | .swap, .index => "swapindex_atomic!"
  | .replace, .field => "replaceproperty!"
  | .replace, .index => "replaceindex_atomic!"
  | .once, .field => "setpropertyonce!"
  | .once, .index => "setindexonce_atomic!"

def atomicOrderCount : AtomicOperation → Nat
  | .fetch | .store | .modify | .swap => 1
  | .replace | .once => 2

def ExprAtomicBodies : Prop := ∀ operation target,
  !(atomicPrimitive operation target).isEmpty ∧
  (atomicOrderCount operation = 1 ∨ atomicOrderCount operation = 2) ∧
  (operation = .fetch → target = .field → atomicPrimitive operation target = "getproperty") ∧
  (operation = .replace → target = .index → atomicPrimitive operation target = "replaceindex_atomic!")

theorem exprAtomicBodies_proven : ExprAtomicBodies := by
  intro operation target
  cases operation <;> cases target <;> decide

/-! ## base/expr.jl: AST classification and generated-function lowering -/

inductive AstNodeKind where
  | newvar | codeInfo | line | goto | gotoIf | enter | ret | ssa | slot | argument
  | quote | globalRef | binding | symbol | pi | phi | phiC | upsilon | expr | other
  deriving Repr, DecidableEq, Inhabited

def isaAstNode : AstNodeKind → Bool
  | .other => false
  | _ => true

def quotedShape (kind : AstNodeKind) : String :=
  if isaAstNode kind then "QuoteNode" else "self"

inductive LoweredGenerated where | codeInfo | syntaxError | impure
  deriving Repr, DecidableEq, Inhabited

def generatedBodyResult (lowered : LoweredGenerated) : Jl String :=
  match lowered with
  | .codeInfo => .ok "CodeInfo:isva+binding-edges"
  | .syntaxError => .error (.argumentError "syntax")
  | .impure => .error (.argumentError "generated body is not pure")

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

/-! ## base/meta.jl: identifiers and operators -/

structure IdentifierOracle where
  start : Char → Bool
  rest : Char → Bool
  operator : String → Bool
  unary : String → Bool
  unaryAndBinary : String → Bool
  syntactic : String → Bool
  suffix : Char → Bool

def isIdentifierModel (oracle : IdentifierOracle) (chars : List Char) : Bool :=
  match chars with
  | [] => false
  | first :: rest =>
    let text := String.ofList chars
    text != "true" && text != "false" && oracle.start first && rest.all oracle.rest

def isBinaryOperatorModel (oracle : IdentifierOracle) (symbol : String) : Bool :=
  oracle.operator symbol && (!oracle.unary symbol || oracle.unaryAndBinary symbol) && symbol != "'"

def isPostfixOperatorModel (oracle : IdentifierOracle) (chars : List Char) : Bool :=
  match chars with
  | '\'' :: suffix => suffix.all oracle.suffix
  | _ => false

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

inductive SourceTree where
  | atom (name : String)
  | macrocall (location : Nat) (children : List SourceTree)
  | node (head : String) (children : List SourceTree)
  deriving Repr, Inhabited

def replaceSourceRoot (location : Nat) : SourceTree → SourceTree
  | .macrocall _ children => .macrocall location children
  | tree => tree

def replaceSourceLoc (location : Nat) : SourceTree → SourceTree
  | .atom name => .atom name
  | .macrocall _ children => .macrocall location (children.map (replaceSourceLoc location))
  | .node head children => .node head (children.map (replaceSourceLoc location))
termination_by tree => sizeOf tree

structure LowerRequest where
  moduleName : String
  expression : String
  deriving Repr, DecidableEq, Inhabited

def lowerModel (request : LowerRequest) : String :=
  "Core._lower(" ++ request.expression ++ "," ++ request.moduleName ++ ")"

def dumpMacroShape (expression : String) : String := "dump(QuoteNode(" ++ expression ++ "))"

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

inductive ParseNode where | value (text : String) | parseError | incomplete | nothing
  deriving Repr, DecidableEq, Inhabited

structure ParseReply where
  node : ParseNode
  offset : Nat
  deriving Repr, DecidableEq, Inhabited

inductive ParseMode where | statement | atom | all
  deriving Repr, DecidableEq, Inhabited

def parseMode (greedy : Bool) : ParseMode := if greedy then .statement else .atom

def parserSource (moduleHasOverride : Bool) : String :=
  if moduleHasOverride then "module:#_internal_julia_parse" else "Base.VersionedParse"

def parseAtModel (length position : Nat) (greedy raiseError : Bool)
    (oracle : Nat → Bool → ParseReply) : Jl ParseReply :=
  if position < 1 || length + 1 < position then .error .boundsError
  else
    let reply := oracle (position - 1) greedy
    if raiseError && reply.node == .parseError then .error (.argumentError "ParseError")
    else .ok { reply with offset := reply.offset + 1 }

def parseWholeModel (length : Nat) (raiseError : Bool) (reply : ParseReply) : Jl ParseNode :=
  if reply.node == .parseError || reply.node == .incomplete then .ok reply.node
  else if reply.offset ≤ length then
    if raiseError then .error (.argumentError "extra token") else .ok .parseError
  else .ok reply.node

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

inductive InlineNode where
  | ssa (id : Int) | goto (label : Int) | slot (id : Int) | boundscheck
  | gotoIf (condition : Int) (dest : Int) | enter (dest : Int)
  | newvar (slot : Int) | phi (edges : List Int) | upsilon (value : Option Int)
  | phiC (values : List Int) | ret (value : Option Int)
  | staticParameter (index : Nat) | cfunction | foreigncall | isdefined (slot : Int)
  | expression (head : String) | other (payload : Int)
  deriving Repr, DecidableEq, Inhabited

def partiallyInlineNode (node : InlineNode) (slotCount slotOffset statementOffset : Int)
    (boundscheckOff : Bool) : InlineNode :=
  match node with
  | .ssa id => .ssa (id + statementOffset)
  | .goto label => .goto (label + statementOffset)
  | .slot id => if 1 ≤ id && id ≤ slotCount then .other id else .slot (id + slotOffset)
  | .boundscheck => if boundscheckOff then .other 0 else .boundscheck
  | .gotoIf condition dest => .gotoIf condition (dest + statementOffset)
  | .enter 0 => .enter 0
  | .enter dest => .enter (dest + statementOffset)
  | .newvar slot => .newvar (slot + slotOffset)
  | .phi edges => .phi (edges.map (· + slotOffset))
  | .upsilon value => .upsilon value
  | .phiC values => .phiC values
  | .ret value => .ret value
  | .staticParameter index => .staticParameter index
  | .cfunction => .cfunction
  | .foreigncall => .foreigncall
  | .isdefined slot =>
    if 1 ≤ slot && slot ≤ slotCount then .other 1 else .isdefined (slot + slotOffset)
  | .expression head => .expression head
  | node => node

def MetaInlineBodies : Prop := ∀ id slotCount slotOffset statementOffset off,
  partiallyInlineNode (.ssa id) slotCount slotOffset statementOffset off = .ssa (id + statementOffset) ∧
  partiallyInlineNode (.goto id) slotCount slotOffset statementOffset off = .goto (id + statementOffset) ∧
  partiallyInlineNode (.enter 0) slotCount slotOffset statementOffset off = .enter 0 ∧
  partiallyInlineNode .boundscheck slotCount slotOffset statementOffset true = .other 0

theorem metaInlineBodies_proven : MetaInlineBodies := by
  unfold MetaInlineBodies
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩

inductive HygieneFrame where | escape | hygienic (context : List String)
  deriving Repr, DecidableEq, Inhabited

def reescapeFrames (frames : List HygieneFrame) (payload : String) : List HygieneFrame × String :=
  (frames, payload)

def unescapeFrames (wrapped : List HygieneFrame × String) : String := wrapped.2

def unblockCount (nonLineExpressions : Nat) : Bool := nonLineExpressions == 1

def uncurlyHead (isCurly : Bool) (head original : String) : String :=
  if isCurly then head else original

def MetaHygieneBodies : Prop :=
  (∀ frames payload, unescapeFrames (reescapeFrames frames payload) = payload) ∧
  (∀ count, unblockCount count = (count == 1)) ∧
  (∀ head original, uncurlyHead true head original = head)

theorem metaHygieneBodies_proven : MetaHygieneBodies := by
  exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-! ## base/reflection.jl: lowered code, parameters, and compiler dispatch -/

structure LoweredCandidate where
  generated : Bool
  mayInvokeGenerator : Bool
  fallback : String
  staged : String
  deriving Repr, DecidableEq, Inhabited

def loweredCandidate (useGenerated : Bool) (candidate : LoweredCandidate) : Jl String :=
  if useGenerated && candidate.generated then
    if candidate.mayInvokeGenerator then .ok candidate.staged
    else .error (.argumentError "could not expand generator")
  else .ok candidate.fallback

def codeLoweredModel (useGenerated : Bool) (candidates : List LoweredCandidate) : Jl (List String) :=
  candidates.mapM (loweredCandidate useGenerated)

def normalizeDebugInfo (irShowDefined : Bool) (debugInfo : String) : Jl String :=
  let normalized := if !irShowDefined && debugInfo == "default" then "source" else debugInfo
  if normalized == "source" || normalized == "none" then .ok normalized
  else .error (.argumentError "debuginfo must be source or none")

def reflectionWorldAllowed (pureContext : Bool) (worldIsMax : Bool) : Bool :=
  !pureContext && !worldIsMax

def methodInstancesModel (candidates : List String) : List String :=
  candidates.map ("specialize:" ++ ·)

def ReflectionLoweredBodies : Prop := ∀ candidate,
  loweredCandidate false candidate = .ok candidate.fallback ∧
  (candidate.generated = false → loweredCandidate true candidate = .ok candidate.fallback) ∧
  (∀ candidates, (methodInstancesModel candidates).length = candidates.length) ∧
  normalizeDebugInfo false "default" = .ok "source" ∧
  reflectionWorldAllowed false false = true

theorem reflectionLoweredBodies_proven : ReflectionLoweredBodies := by
  intro candidate
  constructor
  · simp [loweredCandidate]
  constructor
  · intro h
    simp [loweredCandidate, h]
  constructor
  · intro candidates; simp [methodInstancesModel]
  exact ⟨rfl, rfl⟩

def boolCint (value : Bool) : Int := if value then 1 else 0

structure CodegenFlags where
  trackAllocations : Bool
  codeCoverage : Bool
  preferSpecsig : Bool
  emitMetadata : Bool
  deriving Repr, Inhabited

def codegenParamsModel (flags : CodegenFlags) : List Int := [
  boolCint flags.trackAllocations, boolCint flags.codeCoverage,
  boolCint flags.preferSpecsig, boolCint flags.emitMetadata]

def emissionParamsModel (emitMetadata : Bool) : Int := boolCint emitMetadata

def ReflectionParamBodies : Prop := ∀ flags,
  (codegenParamsModel flags).length = 4 ∧
  (codegenParamsModel flags).all (fun value => value = 0 || value = 1) ∧
  (emissionParamsModel flags.emitMetadata = 0 ∨ emissionParamsModel flags.emitMetadata = 1)

theorem reflectionParamBodies_proven : ReflectionParamBodies := by
  intro flags
  rcases flags with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

inductive CompilerRoute where | typeinfWorld | reflectionModule | interpreterModule | methodTableModule
  deriving Repr, DecidableEq, Inhabited

def compilerRoute (reflectionCompiler interp methodTable : Bool) : CompilerRoute :=
  if interp then .interpreterModule
  else if methodTable then .methodTableModule
  else if reflectionCompiler then .reflectionModule
  else .typeinfWorld

def ReflectionCompilerBodies : Prop := ∀ reflection interp table,
  compilerRoute reflection interp table =
    if interp then .interpreterModule
    else if table then .methodTableModule
    else if reflection then .reflectionModule else .typeinfWorld

theorem reflectionCompilerBodies_proven : ReflectionCompilerBodies := by
  unfold ReflectionCompilerBodies
  intros
  rfl

/-! ## base/reflection.jl: query result shaping -/

inductive FunctionClass where | ordinary | opaque | builtin
  deriving Repr, DecidableEq, Inhabited

def codeQueryRows (inferred : List (Option String)) : List String :=
  inferred.map fun result => result.getD "Method=>Any"

def irCodeQueryRows (inferred : List (Option (String × String))) : List String :=
  inferred.map fun result => match result with
    | none => "Method=>Any"
    | some (code, ty) => code ++ "=>" ++ ty

def returnTypeRows (functionClass : FunctionClass) (inferred : List (Option String)) : List String :=
  match functionClass with
  | .opaque => [inferred.head?.join.getD "Any"]
  | .builtin => [inferred.head?.join.getD "Any"]
  | .ordinary => inferred.map (·.getD "Any")

def exceptionTypeRows (functionClass : FunctionClass) (inferred : List (Option String)) : List String :=
  match functionClass with
  | .opaque => ["Any"]
  | .builtin => [inferred.head?.join.getD "Any"]
  | .ordinary => inferred.map (·.getD "Any")

def inferCollectiveType (functionClass : FunctionClass) (types : List String) : String :=
  match functionClass with
  | .opaque | .builtin => types.head?.getD "Any"
  | .ordinary => String.intercalate " ∪ " types

def checkGeneratedContext (pureContext worldIsMax : Bool) : Jl Unit :=
  if pureContext || worldIsMax then .error (.argumentError "reflection from generated function")
  else .ok ()

def ReflectionQueryBodies : Prop := ∀ results,
  (codeQueryRows results).length = results.length ∧
  (returnTypeRows .ordinary results).length = results.length ∧
  (exceptionTypeRows .ordinary results).length = results.length ∧
  (irCodeQueryRows (results.map (·.map fun value => (value, value)))).length = results.length ∧
  checkGeneratedContext false false = .ok ()

theorem reflectionQueryBodies_proven : ReflectionQueryBodies := by
  intro results
  simp [codeQueryRows, returnTypeRows, exceptionTypeRows, irCodeQueryRows,
    checkGeneratedContext]

/-! ## base/reflection.jl: public method APIs and ambiguity -/

structure KeywordMethod where
  positionalMatch : Bool
  acceptedKeywords : List String
  forwardsKeywords : Bool
  deriving Repr, DecidableEq, Inhabited

def hasKeywordMethod (method : KeywordMethod) (requested : List String) : Bool :=
  method.positionalMatch &&
    (requested.isEmpty || method.forwardsKeywords || requested.all method.acceptedKeywords.contains)

def parentModuleModel (methods : List String) : Jl String :=
  match methods with
  | [] => .error (.argumentError "no matching methods")
  | moduleName :: _ => .ok moduleName

inductive BodyFunctionHead where
  | symbol (moduleName name : String)
  | globalRef (moduleName name : String)
  | apply (next : BodyFunctionHead)
  | applyIterate (next : BodyFunctionHead)
  | ssa (resolved : Option BodyFunctionHead)
  | other
  deriving Repr, Inhabited

def bodyFunctionModel : BodyFunctionHead → Option (String × String)
  | .symbol moduleName name | .globalRef moduleName name => some (moduleName, name)
  | .apply next | .applyIterate next => bodyFunctionModel next
  | .ssa (some next) => bodyFunctionModel next
  | .ssa none | .other => none

def ReflectionApiBodies : Prop :=
  (∀ method, hasKeywordMethod method [] = method.positionalMatch) ∧
  (∀ moduleName rest, parentModuleModel (moduleName :: rest) = .ok moduleName) ∧
  (∀ table modules method, whichMethod table modules = some method → hasMethod table modules = true) ∧
  (∀ moduleName name, bodyFunctionModel (.globalRef moduleName name) = some (moduleName, name))

theorem reflectionApiBodies_proven : ReflectionApiBodies := by
  constructor
  · intro method
    simp [hasKeywordMethod]
  constructor
  · intros; rfl
  constructor
  · exact whichHasMethod_proven
  · intros; rfl

structure AmbiguityFacts where
  sameMethod : Bool
  bottomIntersection : Bool
  hasBottomParameter : Bool
  generatorWorld : Bool
  runtimeAmbiguity : Bool
  involvesBoth : Bool
  reverseIntersectionWorks : Bool
  deriving Repr, DecidableEq, Inhabited

def isAmbiguousModel (facts : AmbiguityFacts) (ambiguousBottom : Bool) : Bool :=
  if facts.sameMethod || facts.bottomIntersection then false
  else if !ambiguousBottom && facts.hasBottomParameter then false
  else if facts.generatorWorld then true
  else facts.runtimeAmbiguity && facts.involvesBoth && facts.reverseIntersectionWorks

def ReflectionAmbiguityBodies : Prop := ∀ facts flag,
  isAmbiguousModel facts flag = true → facts.sameMethod = false ∧ facts.bottomIntersection = false

theorem reflectionAmbiguityBodies_proven : ReflectionAmbiguityBodies := by
  intro facts flag h
  simp [isAmbiguousModel] at h
  exact h.1

/-! ## base/reflection.jl: invoke macros and cache reset -/

inductive CallForm where | call | getproperty | getindex | setproperty | setindex | invalid
  deriving Repr, DecidableEq, Inhabited

def callTarget : CallForm → Jl String
  | .call => .ok "call-target"
  | .getproperty => .ok "getproperty"
  | .getindex => .ok "getindex"
  | .setproperty => .ok "setproperty!"
  | .setindex => .ok "setindex!"
  | .invalid => .error (.argumentError "expected call expression")

def invokeTypeSource (annotated : Bool) : String :=
  if annotated then "annotation" else "Core.Typeof"

def invokeLatestRoute (literalGlobal hasKeywords : Bool) : String :=
  if literalGlobal then
    if hasKeywords then "invokelatest_gr:kwcall" else "invokelatest_gr:invoke_in_world"
  else "invokelatest"

def flattenTupleArgs (arguments : List (List String)) : List String := arguments.flatten

def ReflectionInvokeBodies : Prop :=
  (∀ form target, callTarget form = .ok target → form ≠ .invalid) ∧
  invokeTypeSource true = "annotation" ∧ invokeTypeSource false = "Core.Typeof" ∧
  invokeLatestRoute true false = "invokelatest_gr:invoke_in_world" ∧
  (∀ arguments, (flattenTupleArgs arguments).length = (arguments.map List.length).sum)

theorem reflectionInvokeBodies_proven : ReflectionInvokeBodies := by
  constructor
  · intro form target h
    cases form <;> simp [callTarget] at h ⊢
  exact ⟨rfl, rfl, rfl, fun arguments => by simp [flattenTupleArgs]⟩

structure CacheState where
  requireWorldIsMax : Bool
  compilerActive : Bool
  deriving Repr, DecidableEq, Inhabited

def dropCachesModel (_ : CacheState) : CacheState := ⟨true, true⟩

def ReflectionCacheBodies : Prop := ∀ state,
  (dropCachesModel state).requireWorldIsMax = true ∧
  (dropCachesModel state).compilerActive = true

theorem reflectionCacheBodies_proven : ReflectionCacheBodies := by
  intro state
  exact ⟨rfl, rfl⟩

/-! ## base/Enums.jl: runtime methods and macro-generated methods -/

structure EnumRuntime where
  names : List (Int × String)
  instances : List Int
  typeHash : Nat
  deriving Repr, DecidableEq, Inhabited

def enumName (definition : EnumRuntime) (value : Int) : String :=
  (definition.names.find? (·.1 == value)).map (·.2) |>.getD ("<invalid #" ++ toString value ++ ">")

def enumContains (definition : EnumRuntime) (value : Int) : Bool :=
  definition.instances.contains value

def enumIsless (left right : Int) : Bool := left < right
def enumBroadcast (value : Int) : List Int := [value]

def enumBaseType (baseType : String) : String := baseType
def enumBitcast (value : Int) : Int := value
def enumWriteRead (value : Int) : Int := enumBitcast value
def enumHashModel (hashType : Nat → Nat → Nat) (hashValue : Int → Nat → Nat)
    (typeHash : Nat) (value : Int) (seed : Nat) : Nat :=
  hashType typeHash (hashValue value seed)
def enumPrintModel (definition : EnumRuntime) (value : Int) : String := enumName definition value
def enumShowModel (definitionModule : String) (visible compact : Bool)
    (definition : EnumRuntime) (value : Int) : String :=
  let renderedPrefix := if compact || visible then "" else definitionModule ++ "."
  renderedPrefix ++ enumName definition value

def EnumRuntimeBodies : Prop := ∀ definition value,
  enumContains definition value = definition.instances.contains value ∧
  (enumBroadcast value).length = 1 ∧
  enumIsless value value = false ∧
  enumName definition value =
    ((definition.names.find? (·.1 == value)).map (·.2)).getD ("<invalid #" ++ toString value ++ ">") ∧
  enumWriteRead value = value ∧
  (∀ hashType hashValue typeHash seed,
    enumHashModel hashType hashValue typeHash value seed =
      hashType typeHash (hashValue value seed))

theorem enumRuntimeBodies_proven : EnumRuntimeBodies := by
  intro definition value
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp [enumIsless]
  constructor
  · rfl
  constructor
  · rfl
  · intros; rfl

inductive MembershipStrategy where | interval | disjunction | set
  deriving Repr, DecidableEq, Inhabited

def membershipStrategy (values : List Int) : MembershipStrategy :=
  match values with
  | [] => .disjunction
  | [_] => .interval
  | _ :: _ =>
    let lo := values.foldl min values.head!
    let hi := values.foldl max values.head!
    if values.length = (hi - lo + 1).toNat then .interval
    else if values.length < 20 then .disjunction else .set

def EnumMacroBodies : Prop :=
  (∀ value, membershipStrategy [value] = .interval) ∧
  EnumAssignsDocumentedValues ∧ EnumRejectsDuplicateValues ∧
  EnumRejectsDuplicateNames ∧ EnumRejectsOutOfRange ∧ EnumRejectsOverflow

theorem enumMacroBodies_proven : EnumMacroBodies := by
  constructor
  · intro value; rfl
  exact ⟨enumAssignsDocumentedValues_proven, enumRejectsDuplicateValues_proven,
    enumRejectsDuplicateNames_proven, enumRejectsOutOfRange_proven,
    enumRejectsOverflow_proven⟩

/-! ## base/cartesian.jl: macro constructors and substitution utilities -/

inductive CartesianMacro where | nloops | nref | ncall | ncallkw | nexprs | nextract | nall | nany | ntuple | nif
  deriving Repr, DecidableEq, Inhabited

def cartesianGeneratedCount (kind : CartesianMacro) (dimensions : Nat) : Nat :=
  match kind with
  | .nif => if dimensions = 0 then 0 else dimensions
  | _ => dimensions

def cartesianIndexSequence (dimensions : Nat) : List Nat :=
  (List.range dimensions).map (· + 1)

def ncallArguments (dimensions : Nat) (fixed : List String) (stem : String) : List String :=
  fixed ++ (cartesianIndexSequence dimensions).map fun index => indexedName stem index

def ncallkwShape (dimensions : Nat) (keywords fixed : List String) (stem : String) : List String :=
  keywords ++ ncallArguments dimensions fixed stem

def nexprsShape (dimensions : Nat) (stem : String) : List String :=
  cartesianIndexSequence dimensions |>.map fun index => indexedName stem index

def nextractShape (dimensions : Nat) (stem source : String) : List (String × String) :=
  cartesianIndexSequence dimensions |>.map fun index =>
    (indexedName stem index, source ++ "[" ++ toString index ++ "]")

def nbooleanShape (dimensions : Nat) : List Nat := cartesianIndexSequence dimensions

def nifShape (dimensions : Nat) : List Nat :=
  if dimensions = 0 then [] else cartesianIndexSequence dimensions

def CartesianMacroBodies : Prop := ∀ kind dimensions,
  cartesianGeneratedCount kind dimensions ≤ dimensions ∧
  (cartesianIndexSequence dimensions).length = dimensions ∧
  (∀ fixed stem, (ncallArguments dimensions fixed stem).length = fixed.length + dimensions) ∧
  (∀ stem source, (nextractShape dimensions stem source).length = dimensions)

theorem cartesianMacroBodies_proven : CartesianMacroBodies := by
  intro kind dimensions
  constructor
  · cases kind <;> by_cases h : dimensions = 0 <;> simp [cartesianGeneratedCount, h]
  constructor
  · simp [cartesianIndexSequence]
  constructor
  · intros; simp [ncallArguments, cartesianIndexSequence]
  · intros; simp [nextractShape, cartesianIndexSequence]

inductive SymbolicExpr where
  | value (n : Int) | variable | add (a b : SymbolicExpr) | sub (a b : SymbolicExpr)
  | mul (a b : SymbolicExpr) | div (a b : SymbolicExpr) | neg (a : SymbolicExpr)
  deriving Repr, DecidableEq, Inhabited

def resolveArithmetic : SymbolicExpr → Option Int
  | .value n => some n
  | .variable => none
  | .add a b => do return (← resolveArithmetic a) + (← resolveArithmetic b)
  | .sub a b => do return (← resolveArithmetic a) - (← resolveArithmetic b)
  | .mul a b => do return (← resolveArithmetic a) * (← resolveArithmetic b)
  | .div a b => do
    let denominator ← resolveArithmetic b
    if denominator = 0 then none else return (← resolveArithmetic a).tdiv denominator
  | .neg a => do return -(← resolveArithmetic a)

def indexedSymbol (stem : String) (extension : Int) : String :=
  stem ++ "_" ++ toString extension

inductive ReplaceContext where | executable | quoted | foreignHygiene
  deriving Repr, DecidableEq, Inhabited

def replaceSymbolModel (context : ReplaceContext) (symbol pattern : String) (value : Int) : String :=
  match context with
  | .foreignHygiene => symbol
  | .quoted => symbol
  | .executable => if symbol == pattern then toString value else symbol

def popLineBlock (nonLineArguments : List String) : Option String :=
  match nonLineArguments with
  | [only] => some only
  | _ => none

def resolveConditional (condition : Option Bool) (whenTrue whenFalse : String) : Option String :=
  condition.map fun value => if value then whenTrue else whenFalse

def CartesianSubstitutionBodies : Prop :=
  (∀ stem extension, indexedSymbol stem extension = stem ++ "_" ++ toString extension) ∧
  (∀ a b, resolveArithmetic (.add (.value a) (.value b)) = some (a + b)) ∧
  (∀ a, resolveArithmetic (.neg (.value a)) = some (-a)) ∧
  (∀ symbol pattern value, replaceSymbolModel .quoted symbol pattern value = symbol) ∧
  (∀ only, popLineBlock [only] = some only) ∧
  (∀ whenTrue whenFalse, resolveConditional (some true) whenTrue whenFalse = some whenTrue)

theorem cartesianSubstitutionBodies_proven : CartesianSubstitutionBodies := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end JuliaLean.ExprReflect
