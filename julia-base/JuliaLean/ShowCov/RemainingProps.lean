import JuliaLean.ShowCov.Remaining

/-!
Behavioral properties for the remaining `base/show.jl` method models.  Each
property quantifies over the runtime observations used by its source methods.
-/

namespace JuliaLean.ShowCov

open JuliaLean.Show
open Remaining

def FunctionDisplaySpec : Prop :=
  (∀ x : SelfInput, isSelf x =
    if x.typeNameIsSingleton then false
    else if x.backdatedConstant then x.restrictionTypeIsSelf
    else x.globalDefined && x.globalTypeIsSelf) ∧
  (∀ compact compactText f, showFunctionPlain compact compactText f =
    if compact then compactText
    else match f.kind with
      | .intrinsic id => f.name ++ " (intrinsic function #" ++ toString id ++ ")"
      | .builtin => f.name ++ " (built-in function)"
      | .generic =>
        let n := f.methodCount
        let methodWord := if n = 1 then "method" else "methods"
        let shownName := if isSelf f.self || f.name.contains '#' then f.name else "(::" ++ f.typeText ++ ")"
        let what := if shownName.startsWith "@" then "macro" else "generic function"
        shownName ++ " (" ++ what ++ " with " ++ toString n ++ " " ++ methodWord ++ ")") ∧
  (∀ pure active, activeModule pure active =
    if pure then .error (.errorException "active_module() should not be called from a pure context")
    else match active with | .absent => .ok "Main" | .present m => .ok m) ∧
  (∀ f fallback, showFunction f fallback =
    if f.nameIsSingleton then fallback
    else if f.compact then f.singletonName
    else if f.globallyBound then
      (if f.visible || f.sameModule then "" else f.moduleName ++ ".") ++ f.singletonName
    else fallback) ∧
  (∀ compact name, showIntrinsic compact name =
    (if compact then "" else "Core.Intrinsics.") ++ name) ∧
  (∀ name, printIntrinsic name = name)

theorem functionDisplaySpec_proven : FunctionDisplaySpec := by
  simp [FunctionDisplaySpec, isSelf, showFunctionPlain, activeModule, showFunction,
    showIntrinsic, printIntrinsic]
  repeat' apply And.intro <;> intros <;> rfl

def ContainerDisplaySpec : Prop :=
  (∀ summary forward label entries compact limit rows,
    showKeyValueIter summary forward label entries compact limit rows =
      if entries.isEmpty && compact then forward
      else if entries.isEmpty then summary
      else if limit && rows < 2 then summary ++ ". " ++ label ++ ": …"
      else
        let room := if limit then rows - 1 else entries.length
        let shown := entries.take room
        let lines := shown.map (fun e => "\n  " ++ if limit then e.limited else e.full)
        let ellipsis := if limit && room < entries.length then ["\n  ⋮"] else []
        summary ++ ". " ++ label ++ ":" ++ String.join (lines ++ ellipsis)) ∧
  (∀ summary forward entries hasLength circular limit rows ellipsisKey,
    showDictPlain summary forward entries hasLength circular limit rows ellipsisKey =
      if entries.isEmpty || !hasLength then forward
      else if circular then summary ++ ":"
      else if limit && rows < 2 then summary ++ ": …"
      else
        let room := if limit then rows - 1 else entries.length
        let shown := entries.take room
        let lines := shown.map fun e =>
          "\n  " ++ (if limit then e.alignedLimitedKey else e.key) ++ " => " ++
            (if limit then e.limitedValue else e.value)
        let ellipsis := if limit && room < entries.length then
          ["\n  " ++ ellipsisKey ++ " => ⋮"] else []
        summary ++ ":" ++ String.join (lines ++ ellipsis)) ∧
  (∀ summary forward entries circular limit rows,
    showSetPlain summary forward entries circular limit rows =
      if entries.isEmpty then forward
      else if circular then summary ++ ":"
      else if limit && rows < 2 then summary ++ ": …"
      else
        let room := if limit then rows - 1 else entries.length
        let shown := entries.take room
        let lines := shown.map (fun e => "\n  " ++ if limit then e.limited else e.full)
        let ellipsis := if limit && room < entries.length then ["\n  ⋮ "] else []
        summary ++ ":" ++ String.join (lines ++ ellipsis))

theorem containerDisplaySpec_proven : ContainerDisplaySpec := by
  simp [ContainerDisplaySpec, showKeyValueIter, showDictPlain, showSetPlain]

def TypeAnalysisSpec : Prop :=
  (∀ a b, printWithoutParams a b = (a && b)) ∧
  (∀ bindings name, ioHasTvarName bindings name =
    bindings.any fun b => b.unionallKey && b.isTypeVar && b.name == name && b.occurs) ∧
  (∀ name, ioHasTvarNamePlain name = false) ∧
  (∀ ub, modulesOf (.typeVar ub) = modulesOf ub) ∧
  (∀ p, modulesOf (.typeEq (some p)) = modulesOf p) ∧
  (∀ p, modulesOf (.typeEgal p) = modulesOf p) ∧
  (∀ a b, modulesOf (.union a b) = (modulesOf a ++ modulesOf b).eraseDups) ∧
  (∀ free before, hasOtherFreeTypevars free before =
    free.any fun v => !before.contains v) ∧
  (∀ alias, unboundedTypealias alias = match alias with
    | .atom text => .atom text
    | .unionall name _ body => .unionall name true (unboundedTypealias body)) ∧
  (∀ context bindings x, reapplyUnionallEnv context bindings x =
    if context then bindings.foldl
      (fun acc b => if b.1 then "(" ++ acc ++ " where " ++ b.2 ++ ")" else acc) x
    else x) ∧
  (∀ any tuple candidates, makeTypealias any tuple candidates =
    if any || tuple then none
    else
      let valid := candidates.filter validTypeAliasCandidate
      let names := valid.map (·.name)
      let best := if valid.length > 1 then
        valid.filter fun c => !(c.strictSubtypes.any fun n => names.contains n)
      else valid
      match best with | [c] => some (c.name, c.env) | _ => none)

theorem typeAnalysisSpec_proven : TypeAnalysisSpec := by
  simp [TypeAnalysisSpec, printWithoutParams, ioHasTvarName, ioHasTvarNamePlain,
    modulesOf, hasOtherFreeTypevars, reapplyUnionallEnv,
    makeTypealias]
  constructor
  · intro alias
    cases alias with
    | atom => rfl
    | unionall name unbounded body => cases unbounded <;> rfl
  · intro; rfl

def TypeParamsSpec : Prop :=
  (∀ name, isGensym name = name.contains '#') ∧
  (∀ selected elide later env, showCanElide selected elide later env =
    (elide != 0 && selected && !(later.any id) && !(env.any id))) ∧
  (∀ other upper lower, egalVar other upper lower = (other && upper && lower)) ∧
  (∀ params keep elide, (showTypeparams params keep elide).2 = elide) ∧
  (∀ params elide, showTypeparams params 0 elide = ("", elide))

theorem typeParamsSpec_proven : TypeParamsSpec := by
  simp [TypeParamsSpec, isGensym, showCanElide, egalVar, showTypeparams]

def TypeAliasPrintSpec : Prop :=
  (∀ compact visible mod name, showTypealiasName compact visible mod name =
    (if !compact && !visible then mod ++ "." else "") ++ name) ∧
  (∀ name params empty, showTypealias name params empty = name ++ if empty then "" else params) ∧
  (∀ context outer env, makeWheres context outer env =
    let seen := context.eraseDups
    let outerNew := outer.filter fun x => !seen.contains x
    let seen' := (seen ++ outerNew).eraseDups
    let inner := env.reverse.filter fun x => !seen'.contains x
    inner.reverse ++ outerNew) ∧
  (∀ wheres, showWheres wheres = match wheres with
    | [] => "" | [w] => " where " ++ w | ws => " where {" ++ ", ".intercalate ws ++ "}") ∧
  (showTypealiasLookup none = (false, "")) ∧
  (∀ text, showTypealiasLookup (some text) = (true, text)) ∧
  (∀ candidates, makeTypealiases true false candidates = []) ∧
  (∀ pieces, showUnionaliases pieces [] = (false, "")) ∧
  (∀ normal p a c g s, showTypePlain normal p a c g s =
    if !p && a then normal ++ if c then "" else " (alias for " ++ normal ++ ")"
    else normal ++ if !c && g then
      " (singleton type of function " ++ s ++ ", subtype of Function)" else "")

theorem typeAliasPrintSpec_proven : TypeAliasPrintSpec := by
  simp [TypeAliasPrintSpec, showTypealiasName, showTypealias, makeWheres,
    showWheres, showTypealiasLookup, makeTypealiases, showUnionaliases,
    showTypePlain]
  intro; rfl

def TypeDispatchSpec : Prop :=
  (∀ p, showTypeEgal p = "Core.TypeEgal{" ++ p ++ "}") ∧
  (showAnyType .bottom = "Union{}") ∧
  (∀ p, showAnyType (.typeEgal p) = showTypeEgal p) ∧
  (∀ p, showAnyType (.typeEq p) = "Type{" ++ p ++ "}") ∧
  (∀ compact p, showTypeEq compact p =
    (if compact then "Type{" else "TypeEq{") ++ p ++ "}") ∧
  (∀ compact p, showType compact (.typeEgal p) = showTypeEgal p) ∧
  (∀ compact, showType compact .bottom = "Union{}") ∧
  (∀ compact body wheres, showType compact (.unionall body wheres) = body ++ showWheres wheres)

theorem typeDispatchSpec_proven : TypeDispatchSpec := by
  simp [TypeDispatchSpec, showTypeEgal, showAnyType, showTypeEq, showType]

def TypeNamesSpec : Prop :=
  (∀ v, isVisible v =
    if v.deprecated || !v.fromDefined || !v.parentDefined then false
    else if v.sameBinding || v.importedChainReachesParent then true
    else v.bothDefinedConst && v.sameRestriction) ∧
  (∀ v, isGlobalFunction v =
    (v.hasName && v.concreteWrapper && !v.isDataTypeName && !v.containsHash && !v.containsAt &&
      v.hasModule && v.defined && v.constant && v.valueHasWrapperType)) ∧
  (checkWorldBounded [] = none) ∧
  (∀ p ps m, p.definedConst = true → p.valueIsSubtype = true → p.maxWorld = some m →
    checkWorldBounded (p :: ps) = some (p.minWorld, m)) ∧
  (∀ v, v.unionAllName = true → showTypeName v = "UnionAll") ∧
  (∀ v, maybeKwsNt v =
    if v.pairsName && v.fourParameters && v.firstSymbol && v.fourthNamedTuple &&
      v.fourthHasTwoParameters && v.typesDataType && v.secondMatchesEltype &&
      v.symbolsTuple && v.thirdNothing then some v.result else none) ∧
  (∀ v, v.tuple = true → showDatatype v = renderTupleType v.tupleParams v.homogeneousTail v.varargKind) ∧
  (∀ types, showSupertypes types = " <: ".intercalate types) ∧
  (∀ expressions, (showMacro expressions).1 = expressions.map fun e => e.1 ++ " = " ++ e.2) ∧
  (∀ name, showTypeNameObject name = "typename(" ++ name ++ ")")

theorem typeNamesSpec_proven : TypeNamesSpec := by
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro; rfl
  · intro; rfl
  · intro p ps m hc hv hm
    simp [checkWorldBounded, hc, hv, hm]
  · intro v h; simp [showTypeName, h]
  · intro v; rfl
  · intro v h; simp [showDatatype, h]
  · intro; rfl
  · intro; rfl
  · intro; rfl

def SourceInfoSpec : Prop :=
  (∀ names, (sourceinfoSlotnames names).length = names.length) ∧
  (∀ fromStack m, showMethodInstance fromStack (.generator m) = "MethodInstance generator for " ++ m) ∧
  (∀ fromStack c, showMethodInstance fromStack (.method c) = "MethodInstance for " ++ c) ∧
  (∀ mi abi foreign, showCodeInstance mi abi foreign =
    "CodeInstance for " ++ mi ++ (if abi then " (ABI Overridden)" else "") ++
      (if foreign then " (foreign)" else ""))

theorem sourceinfoSlotnames_length (names : List String) :
    (sourceinfoSlotnames names).length = names.length := by
  simp [sourceinfoSlotnames]

theorem sourceInfoSpec_proven : SourceInfoSpec := by
  exact ⟨sourceinfoSlotnames_length, by intros; rfl, by intros; rfl, by intros; rfl⟩

def ExprWrappersSpec : Prop :=
  (∀ d o ex, printExprNode d o ex =
    showUnquoted d o (16 * ex.size + 16) false false ex 0 (-1) 0) ∧
  (∀ d o ex, showExprNode d o ex =
    showQuoteExpr d o (16 * ex.size + 16) true false ex 0 (-1)) ∧
  (∀ d o ex, showUnquoted0 d o ex =
    showUnquoted d o (16 * ex.size + 16) false false ex 0 0 0) ∧
  (∀ d o ex indent, showUnquotedIndent d o ex indent =
    showUnquoted d o (16 * ex.size + 16) false false ex indent 0 0) ∧
  (∀ rendered, showUnquotedFallback rendered = rendered) ∧
  (∀ d o ex indent prec, showUnquotedQuoteLevel d o ex indent prec =
    showUnquoted d o (16 * ex.size + 16) false false ex indent prec 0) ∧
  (∀ runtime symbol, operatorPrecedenceSymbol runtime symbol = runtime symbol) ∧
  operatorPrecedenceAny = 0 ∧
  isQuotedOther = false ∧ isQuotedQuoteNode = true ∧
  (∀ h n, isQuotedExpr h n = ((h == "quote" || h == "inert") && n = 1)) ∧
  (∀ v, unquotedValue v = v) ∧
  (∀ args, unquotedExpr args = args.head?)

theorem exprWrappersSpec_proven : ExprWrappersSpec := by
  simp [ExprWrappersSpec, printExprNode, showExprNode, showUnquoted0,
    showUnquotedIndent, showUnquotedFallback, showUnquotedQuoteLevel, operatorPrecedenceSymbol,
    operatorPrecedenceAny, isQuotedOther, isQuotedQuoteNode, isQuotedExpr,
    unquotedValue, unquotedExpr]

def AstFormattingSpec : Prop :=
  (∀ p arrow assignment control pair power comparison unaryOnly rightSpelling neutralSpelling,
    operatorAssociativity p arrow assignment control pair power comparison
      unaryOnly rightSpelling neutralSpelling =
    if p ∈ [arrow, assignment, control, pair, power] || unaryOnly || rightSpelling then .right
    else if p ∈ [0, comparison] || neutralSpelling then .none else .left) ∧
  (∀ color text col, emphasize color text col =
    if color then ("styled", text ++ ":" ++ col, true) else ("plain", text.toUpper, false)) ∧
  (∀ line, showLineNumber line none = "#= line " ++ toString line ++ " =#") ∧
  (∀ line file, showLineNumber line (some file) = "#= " ++ file ++ ":" ++ toString line ++ " =#") ∧
  (∀ head args body indent moduleHead, showBlockText head args body indent moduleHead =
    let argsText := if args.isEmpty then "" else " " ++
      (if head == "elseif" then " " else ", ").intercalate args
    let bodyIndent := if moduleHead then indent else indent + 4
    head ++ argsText ++ String.join (body.map fun ex =>
      "\n" ++ String.ofList (List.replicate bodyIndent ' ') ++ ex) ++
      "\n" ++ String.ofList (List.replicate indent ' ')) ∧
  (∀ op cl sep items, showEnclosedListText op cl sep items = op ++ sep.intercalate items ++ cl)

theorem astFormattingSpec_proven : AstFormattingSpec := by
  simp [AstFormattingSpec, operatorAssociativity, emphasize, showLineNumber,
    showBlockText, showEnclosedListText]

def IrNodeSpec : Prop :=
  (∀ id cls, showSSAValue id cls = match cls with
    | .invalid => ("%" ++ toString id, "red", false)
    | .strong => ("%" ++ toString id, "light_red", true)
    | .mild => ("%" ++ toString id, "warn", true)
    | .normal => ("%" ++ toString id, "plain", false)) ∧
  (∀ shown, showSymbolNode shown = shown) ∧
  (∀ line file, showLineNode line file = showLineNumber line file) ∧
  (∀ label, showGotoNode label = "goto %" ++ toString label) ∧
  (∀ shown, showGlobalRefNode shown = shown) ∧
  (∀ owner, showBindingPartitionNode owner = owner) ∧
  (∀ mod sym ident startsAt op quoted, showGlobalRef mod sym ident startsAt op quoted =
    let q := !ident && !startsAt
    let parens := q && (!op || quoted)
    mod ++ "." ++ (if q then ":" else "") ++ (if parens then "(" else "") ++ sym ++
      (if parens then ")" else "")) ∧
  (∀ id names, showSlotNumber id names = match names with
    | some ns => if id > 0 && id ≤ ns.length then ns[id - 1]! else "_" ++ toString id
    | none => "_" ++ toString id) ∧
  (∀ symbol shown, showQuoteNode symbol shown = match symbol with
    | some s => s | none => "$(QuoteNode(" ++ shown ++ "))") ∧
  (∀ body ranges, showGenerator body ranges =
    body ++ String.join (ranges.map fun r => " for " ++ ", ".intercalate r)) ∧
  (∀ parts, validImportPath (.path parts) false = !parts.isEmpty) ∧
  (∀ ex, showImportPath ex = match ex with
    | .symbol name => name
    | .path parts => ".".intercalate (parts.map fun p => if p == ".." then "(..)" else p)
    | .colon base names => showImportPath base ++ ": " ++ ", ".intercalate (names.map showImportPath)
    | .as path alias => showImportPath path ++ " as " ++ showImportPath alias
    | .other shown => shown) ∧
  (∀ s g q shown, allowMacroname s g q shown =
    if s || g || q then "macroname(" ++ shown ++ ")" else shown) ∧
  (∀ core name macroName, isCoreMacroGlobal core name macroName = (core && name == macroName)) ∧
  (∀ macroName, isCoreMacroOther macroName = false) ∧
  (∀ head args, showExprFallback head args =
    "$(Expr(" ++ head ++ String.join (args.map (", " ++ ·)) ++ "))")

theorem irNodeSpec_proven : IrNodeSpec := by
  simp [IrNodeSpec, showSSAValue, showSymbolNode, showGotoNode,
    showLineNode, showGlobalRefNode, showBindingPartitionNode, showGlobalRef, showSlotNumber,
    showQuoteNode, showGenerator, validImportPath, allowMacroname,
    isCoreMacroGlobal, isCoreMacroOther, showExprFallback]
  constructor
  · intros; rfl
  · constructor
    · intros; rfl
    · constructor
      · intros; rfl
      · intro ex; cases ex <;> simp [showImportPath]

def StacktraceSpec : Prop :=
  (∀ name, demangleFunctionName name = match name.splitOn "#" with
    | first :: _ :: _ => if first.isEmpty then name else first | _ => name) ∧
  (∀ q n mod name, showSignatureFunction (.globalFunction q n mod name) =
    (if q && n then mod ++ "." else "") ++ name) ∧
  (∀ back text color bold, printWithinStacktrace back text color bold =
    if back then (text, color, bold) else (text, "plain", false)) ∧
  (∀ f args kwargs wheres, showTupleAsCall f args kwargs wheres =
    let positional := args.map fun a => a.name.getD "" ++ "::" ++ a.typeText
    let kwtext := match kwargs with
      | none => ""
      | some ks => "; " ++ ", ".intercalate (ks.map fun k => k.name ++ if k.splat then "..." else "::" ++ k.typeText)
    f ++ "(" ++ ", ".intercalate positional ++ kwtext ++ ")" ++ wheres) ∧
  (∀ flag original limited, typeLimitedStringFromContext flag original limited =
    if flag then (limited, decide (limited.utf8ByteSize < original.utf8ByteSize)) else (original, false))

theorem stacktraceSpec_proven : StacktraceSpec := by
  simp [StacktraceSpec, demangleFunctionName, showSignatureFunction,
    printWithinStacktrace, showTupleAsCall, typeLimitedStringFromContext]
  constructor <;> intros <;> rfl

def TypeBindingSpec : Prop :=
  (∀ str i ell useColor, printTypeBicolor str i ell useColor =
    if !useColor then [(str, "plain")]
    else match i with
      | none => [(str, "outer")]
      | some n =>
        let outer := str.toList.take n
        let inner := str.toList.drop n
        if ell && inner.length ≥ 3 then
          [(String.ofList outer, "outer"),
            (String.ofList (inner.dropLast.dropLast.dropLast), "inner"), ("...", "outer")]
        else [(String.ofList outer, "outer"), (String.ofList inner, "inner")]) ∧
  (∀ text, resolveBinding (.value text) = some text) ∧
  (∀ value, resolveBinding (.quote value) = some value) ∧
  (∀ name, resolveBinding (.symbol name) = some name) ∧
  (∀ a b c, isModuleCall a b c = (a && b && c)) ∧
  (∀ name lb ub env bottom any lp up, showTypeVar name lb ub env bottom any lp up =
    let lower := (if lp then "(" else "") ++ lb ++ (if lp then ")" else "")
    let upper := (if up then "(" else "") ++ ub ++ (if up then ")" else "")
    let first := if !env && !bottom then if any then name ++ ">:" ++ lower else lower ++ "<:" ++ name else name
    first ++ if !env && !any then "<:" ++ upper else "") ∧
  (showVararg none none = "Vararg") ∧
  (∀ t n, showVararg (some t) n = "Vararg{" ++ t ++ (n.map (", " ++ ·)).getD "" ++ "}")

theorem typeBindingSpec_proven : TypeBindingSpec := by
  simp [TypeBindingSpec, printTypeBicolor, resolveBinding, isModuleCall,
    showTypeVar, showVararg]
  intro str i; constructor <;> rfl

def CodeIrSpec : Prop :=
  (∀ ir, showCodeInfo ir = "CodeInfo(\n" ++ ir ++ ")") ∧
  (∀ slot names, showArgument slot names = showSlotNumber slot names) ∧
  (∀ edges values prefixText, showPhiNode edges values prefixText =
    let pairs := List.zipWith
      (fun e v => prefixText ++ toString e ++ " => " ++ v.getD "#undef") edges values
    "φ (" ++ ", ".intercalate pairs ++ ")") ∧
  (∀ values, showPhiCNode values = "φᶜ (" ++ ", ".intercalate values ++ ")") ∧
  (∀ value typ, showPiNode value typ = "π (" ++ value ++ ", " ++ typ ++ ")") ∧
  (∀ value, showUpsilonNode value = "ϒ (" ++ value.getD "#undef" ++ ")") ∧
  (showReturnNode none = "unreachable") ∧
  (∀ value, showReturnNode (some value) = "return " ++ value) ∧
  (∀ dest cond prefixText, showGotoIfNot dest cond prefixText =
    "goto " ++ prefixText ++ toString dest ++ " if not " ++ cond)

theorem codeIrSpec_proven : CodeIrSpec := by
  simp [CodeIrSpec, showCodeInfo, showArgument, showPhiNode, showPhiCNode, showPiNode,
    showUpsilonNode, showReturnNode, showGotoIfNot]

def OpaqueBindingSpec : Prop :=
  (∀ args result, showOpaqueClosure args result = args ++ "->◌::" ++ result) ∧
  (∀ p, printPartition p =
    toString p.minWorld ++ ":" ++ (p.maxWorld.map toString).getD "∞" ++
      (if p.flags.isEmpty then "" else " [" ++ ",".intercalate p.flags ++ "]") ++
      " - " ++ partitionKindText p.kind) ∧
  (∀ owner p, showPartition owner p false =
    "BindingPartition(for " ++ owner ++ ": " ++ printPartition p ++ ")") ∧
  (∀ owner p, showPartition owner p true =
    "BindingPartition for " ++ owner ++ "\n   " ++ printPartition p) ∧
  (∀ globalRef, showBinding globalRef none = "Binding " ++ globalRef ++ " - No partitions") ∧
  (∀ globalRef ps, showBinding globalRef (some ps) =
    "Binding " ++ globalRef ++ String.join (ps.map fun p => "\n   " ++ printPartition p))

theorem opaqueBindingSpec_proven : OpaqueBindingSpec := by
  simp [OpaqueBindingSpec, showOpaqueClosure, printPartition, showPartition,
    showBinding]

end JuliaLean.ShowCov
