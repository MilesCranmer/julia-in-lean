import JuliaLean.DocsSyntaxCov.Syntax

/-!
# Properties of `base/syntax.jl`

Each proposition is quantified over the method inputs and exposes the corresponding model
function.  Equational properties state the branch structure directly; behavioral properties
state the documented tree, context, source and conversion invariants.
-/

namespace JuliaLean.DocsSyntaxCov.Syntax

open JuliaLean.DocsSyntaxCov

def SyntaxConstructors : Prop :=
  (∀ id h cs v src ctx jl md mod flags,
    syntax9 id h cs v src ctx jl md mod flags = .mk id h cs v src ctx jl md mod flags) ∧
  (∀ mod ed, syntaxContext2 mod ed = ⟨some ⟨mod, []⟩, none, ed, false⟩) ∧
  ∀ id h cs v src ctx,
    syntax5 id h cs v src ctx = .mk id h cs v src ctx none [] none 0

theorem syntaxConstructors : SyntaxConstructors := ⟨fun _ _ _ _ _ _ _ _ _ _ => rfl,
  fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

def SyntaxAccessors : Prop := ∀ ex : Node,
  head ex = ex.head ∧
  isLeaf ex = ex.children?.isNone ∧
  numchildren ex = (ex.children?.map List.length).getD 0 ∧
  children ex = ex.children?.getD [] ∧
  (∀ i, getindex ex i = match ex.children? with
    | none => .error .typeError
    | some cs => match cs[i - 1]? with | some c => .ok c | none => .error .boundsError) ∧
  (∀ first length, getrange ex first length = match ex.children? with
    | none => .error .typeError
    | some cs => if first = 0 ∨ first - 1 + length > cs.length then .error .boundsError
      else .ok ((cs.drop (first - 1)).take length)) ∧
  firstindex ex = 1 ∧ lastindex ex = numchildren ex

theorem syntaxAccessors : SyntaxAccessors := by
  intro ex
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl, rfl, rfl⟩

def NodeStringBehavior : Prop :=
  (∀ repr ex, nodeString repr 0 ex = "(head=" ++ ex.head ++ ")") ∧
  ∀ repr depth ex, nodeString repr (depth + 1) ex =
    let valuePart := match ex.value with | .none => "" | v => ", value=" ++ repr v
    let childPart := if isLeaf ex then ", leaf" else if depth = 0 then "" else
      ", children=[" ++ String.join ((children ex).map (fun c => "\n" ++ nodeString repr depth c)) ++ "]"
    "(head=" ++ ex.head ++ valuePart ++ childPart ++ ")"

theorem nodeStringBehavior : NodeStringBehavior := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

def SyntaxValidation : Prop :=
  (∀ st, assertSyntaxNode st =
    if isLeaf st then
      if st.head = "globalref" && st.mod.isNone then some (st, "leaf globalref requires module in .mod")
      else match leafNeeds st.head with
        | some accepts => if accepts st.value then none else some (st, "needs value")
        | none => if ["placeholder", "nothing", "tombstone", "error", "sourcelocation",
            "latestworld", "latestworld_if_toplevel"].contains st.head then none
          else match st.source with | .text (.ref _) => none | _ => some (st, "unrecognized leaf")
    else if leafOnly.contains st.head then some (st, "Found leaf-only kind with children") else none) ∧
  (∀ st, assertSyntaxRec 0 st [] = some (st, "out of fuel")) ∧
  (∀ fuel recursive st, assertSyntax fuel recursive st =
    match (if recursive then assertSyntaxRec fuel st [] else assertSyntaxNode st) with
    | some _ => .error (.errorException "assert_syntax failed") | none => .ok ()) ∧
  (∀ check x, debugCheckAttrs check x = do let _ ← check x; pure x) ∧
  ∀ ex name value, setproperty ex name value = .error (.errorException "Syntax: this can't be mutated")

theorem syntaxValidation : SyntaxValidation := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

def MknodeBehavior : Prop :=
  (∀ debug old attrs line, mknode false debug old attrs line =
    .error (.argumentError "usage: @mknode(old; attr=val...)")) ∧
  (∀ debug old attrs line, mknode true debug old attrs line = .ok
    (.mk old.id (attrs.head.getD old.head) (attrs.children.getD old.children?)
      (attrs.value.getD old.value) (attrs.source.getD (.syntax old.id))
      (attrs.context.getD old.context)
      (attrs.jlSource.getD (if debug then some line else old.jlSource))
      (attrs.metadata.getD old.metadata) (attrs.mod.getD old.mod)
      (attrs.syntaxFlags.getD old.syntaxFlags))) ∧
  (∀ x, mknode1 false x = .expr "macrocall" [.sym "@mknode", .val "__source__", .nothing, x]) ∧
  ∀ x, mknode1 true x = .expr "macrocall" [.sym "@mknode", .val "__source__", x, .val "_DEFAULT_NODE"]

theorem mknodeBehavior : MknodeBehavior := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

def MapchildrenBehavior : Prop := ∀ eqNode f ex,
  (isLeaf ex = true → mapchildren eqNode f ex = ex) ∧
  (isLeaf ex = false →
    let mapped := (children ex).map f
    mapchildren eqNode f ex = if (List.zip mapped (children ex)).all (fun p => eqNode p.1 p.2)
      then ex else ex.withChildren (some mapped))

theorem mapchildrenBehavior : MapchildrenBehavior := by
  intro eqNode f ex
  constructor
  · intro h; simp [mapchildren, h]
  · intro h; simp [mapchildren, h]

def ContextLayers : Prop :=
  (∀ sc, isBaseLayer sc = match sc.layer with
    | none => .error .typeError | some l => .ok l.escaped.isEmpty) ∧
  (∀ sc, baseLayer 0 sc = .error (.errorException "out of fuel")) ∧
  (∀ sc, syntaxModuleContext sc = match sc.layer with | some l => .ok l.mod | none => .error .typeError) ∧
  (∀ st, syntaxModule st = match st.mod with | some m => .ok m | none => syntaxModuleContext st.context) ∧
  (∀ st, syntaxName st = match st.value with | .str x => .ok x | _ => .error .typeError) ∧
  (∀ st, edition st = st.context.edition) ∧
  (∀ v, editionOther v = (1, 14)) ∧
  ∀ st sc, withContext st sc = st.withContextSource sc st.source

theorem contextLayers : ContextLayers :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ _ => rfl⟩

def ScopeTransforms : Prop :=
  (∀ fuel reference st,
    adoptReference fuel reference st = (adoptScope fuel reference.context st.context.unexpanded st []).1) ∧
  (∀ fuel macrocall st,
    adoptMacro fuel macrocall st = (adoptScope fuel macrocall.context (some macrocall.id) st []).1) ∧
  (∀ fuel macrocall reference st,
    adoptMacroReference fuel macrocall reference st =
      (adoptScope fuel reference.context (some macrocall.id) st []).1) ∧
  (∀ st sc, fillContext 0 st sc = st) ∧
  (∀ fuel st, removeScope1 fuel st = (removeScope fuel st []).1) ∧
  ∀ heap fuel trim st, trimProvenance1 heap fuel trim st = do
    let (st, _) ← trimProvenance heap fuel trim st []
    pure st

theorem scopeTransforms : ScopeTransforms :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ => rfl⟩

def ScopeDisplay : Prop :=
  (∀ objectId l, showLayerCompact (showLayer objectId) l = showLayer objectId l) ∧
  (∀ showLayerFn heap sc, showContext showLayerFn heap sc =
    "[" ++ (if sc.edition = (1, 15) then "" else "old,") ++
      (if sc.internal then "internal," else "") ++ showLayerFn sc.layer ++ "," ++
      (match sc.unexpanded.bind heap with
       | none => ""
       | some u => if u.head = "macrocall" then (children u).head?.map Node.head |>.getD "" else u.head) ++ "]") ∧
  ∀ f c, showContextCompact f c = f c

theorem scopeDisplay : ScopeDisplay := ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

def ProvenanceBehavior : Prop :=
  (∀ heap st, provenance heap 0 st = []) ∧
  (∀ heap fuel st, provenance heap (fuel + 1) st = match st.source with
    | .text _ => [] | .syntax id => match heap id with
      | none => [] | some s => s :: provenance heap fuel s) ∧
  (∀ heap st, prov heap st = match st.source with
    | .syntax id => (heap id).getD st | .text _ => st) ∧
  (∀ heap st, provEnd heap 0 st = st) ∧
  (∀ heap st, macroProv heap st = st.context.unexpanded.bind heap) ∧
  (∀ heap st, macroProvEnd heap 0 st = none) ∧
  (∀ heap fuel st, unexpandedSourceref heap fuel st = match macroProvEnd heap fuel st with
    | none => sourceref heap fuel st | some mp => sourceref heap fuel mp) ∧
  (∀ heap fuel st out,
    flattenedProvenanceInto heap fuel st out = out ++ flattenedProvenance heap fuel st)

theorem provenanceBehavior : ProvenanceBehavior :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def SourceLocationBehavior : Prop :=
  (∀ src b, sourceLine src b = src.firstLine - 1 + countLe (b - src.byteOffset) src.lineStarts) ∧
  (∀ r, firstLineNodeRef r = ⟨sourceLine r.code r.firstByte, some r.code.filename⟩) ∧
  (∀ l, firstLineNodeLine l = l) ∧
  (∀ heap fuel s, filename heap fuel s = do
    let sr ← sourceref heap fuel s
    pure (match sr with | .line l => l.file.getD "" | .ref r => r.code.filename)) ∧
  ∀ heap fuel s, firstLineNodeSyntax heap fuel s = do
    let sr ← sourceref heap fuel s
    match sr with | .line l => pure l | .ref r => pure ⟨sourceLine r.code r.firstByte, some r.code.filename⟩

theorem sourceLocationBehavior : SourceLocationBehavior :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def ExprLineBehavior : Prop :=
  (∀ e, firstLineInExpr 0 e = none) ∧
  (∀ fuel h args, firstLineInExpr (fuel + 1) (.expr h args) =
    if ["macrocall", "quote", "inert"].contains h then none
    else args.foldl (fun found a => found.orElse fun _ => match a with
      | .lnn line file => some ⟨line, some file⟩
      | x@(.expr _ _) => firstLineInExpr fuel x | _ => none) none) ∧
  (∀ fuel e, firstLineExpr fuel e = (firstLineInExpr fuel e).getD ⟨0, some ""⟩) ∧
  (∀ fuel line file, unescapeLnn (fuel + 1) (.lnn line file) = some ⟨line, some file⟩) ∧
  ∀ fuel e dflt, getInnerLnn fuel e dflt = match e with
    | .expr h args =>
      if h = "struct" || h = "macrocall" then (firstLineInExpr fuel e).getD dflt
      else if h = "quote" || h = "inert" then match args.head? with
        | some x@(.expr _ _) => (firstLineInExpr fuel x).getD dflt | _ => dflt
      else if ["function", "macro", "module", "=", "->"].contains h then match args.getLast? with
        | some (.expr "block" (x :: _)) => (unescapeLnn fuel x).getD dflt | _ => dflt
      else dflt
    | _ => dflt

theorem exprLineBehavior : ExprLineBehavior :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def ExprSyntaxBehavior : Prop :=
  (∀ s, isLoweringAstNode (.sym s) = true) ∧
  (∀ fuel id s ctx src q,
    exprToSyntax (fuel + 1) id (.sym s) ctx src q = .ok (syntax5 id "identifier" none (.str s) src ctx, src)) ∧
  (∀ fuel id ctx src q,
    exprToSyntax (fuel + 1) id (.expr "identifier" []) ctx src q =
      .error (.errorException "reserved Expr head")) ∧
  (∀ fuel id e src ctx, exprToSyntaxText fuel id e src ctx = do
    let (s, _) ← exprToSyntax fuel id e ctx (.text src) false
    pure s) ∧
  ∀ fuel id e src, exprToSyntaxFromNode fuel id e src = do
    let (s, _) ← exprToSyntax fuel id e src.context (.syntax src.id) false
    pure s

theorem exprSyntaxBehavior : ExprSyntaxBehavior := by
  exact ⟨fun _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def MetaCallBehavior : Prop :=
  (∀ s, isMetaDocBlock s =
    (s.head = "block" && numchildren s = 2 && match (children s).head? with
      | some s1 => s1.head = "meta" && numchildren s1 = 1 && match (children s1).head? with
        | some s11 => s11.head = "identifier" && valueIsDoc s11.value | none => false
      | none => false)) ∧
  (∀ e, isEventuallyCall 0 e = false) ∧
  (∀ fuel h args, isEventuallyCall (fuel + 1) (.expr h args) =
    (h = "call" || (["escape", "where", "::"].contains h && match args.head? with
      | some x => isEventuallyCall fuel x | none => false)))

theorem metaCallBehavior : MetaCallBehavior := ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

def SyntaxExprBehavior : Prop :=
  (∀ ex lno first, pushLno ex lno first = match ex with
    | .expr h args => if lno.file != some "" || lno.line != 0 then
        .expr h (if first then .lnn lno.line (lno.file.getD "") :: args
          else args ++ [.lnn lno.line (lno.file.getD "")]) else ex
    | _ => ex) ∧
  (∀ lineOf s suppress, syntaxToExpr lineOf 0 s suppress = .error (.errorException "out of fuel")) ∧
  (∀ lineOf fuel s suppress n, s.head = "identifier" → s.value = .str n →
    syntaxToExpr lineOf (fuel + 1) s suppress =
      .ok (match s.mod with | some m => .expr "GlobalRef" [.val m, .sym n] | none => .sym n))

theorem syntaxExprBehavior : SyntaxExprBehavior := by
  refine ⟨fun _ _ _ => rfl, fun lineOf s suppress => by simp [syntaxToExpr], ?_⟩
  intro lineOf fuel s suppress n hh hv
  simp [syntaxToExpr, hh, hv]
  rfl

def ParserEvalWrappers : Prop :=
  (∀ unsafeString parseString ptr len filename lineno,
    cParseallExpr unsafeString parseString ptr len filename lineno =
      let str := unsafeString ptr len
      let (ex, offset) := parseString str filename lineno
      .expr "svec" [ex, .int (offset - 1)]) ∧
  (∀ eval lineOf mod e, flToplevelEval eval lineOf mod (.inr e) = .ok (eval mod e))

theorem parserEvalWrappers : ParserEvalWrappers := ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def PrintingHelpers : Prop :=
  (∀ render name value, attrsummary render name value = match value with
    | .number n => name ++ "=" ++ n | .line l => name ++ "=L" ++ toString l.line
    | .module m => name ++ "=" ++ m | _ => name) ∧
  (∀ s, subscriptStr s = String.mk (s.toList.map subscriptChar)) ∧
  (∀ repr heap ex, valueString repr heap ex =
    let base := match ex.head with
      | "identifier" | "placeholder" => match ex.value with | .str s => s | _ => ""
      | "ssavalue" => "%" | "bindingid" => "#" | "label" => "label"
      | "nothing" => "core.nothing" | "core" => "core." ++ (match ex.value with | .str s => s | _ => "")
      | "top" => "top." ++ (match ex.value with | .str s => s | _ => "")
      | "symbol" => ":" ++ (match ex.value with | .str s => s | _ => "")
      | "globalref" => ex.mod.getD "" ++ "." ++ (match ex.value with | .str s => s | _ => "")
      | "slot" => "slot" | "slots" => "Slots" | "lambdabindings" => "LambdaBindings"
      | "latestworld" => "latestworld" | "static_parameter" => "static_parameter"
      | "symboliclabel" => "label:" ++ (match ex.value with | .str s => s | _ => "")
      | "symbolicgoto" => "goto:" ++ (match ex.value with | .str s => s | _ => "")
      | _ => if valueIsNone ex.value then "::" ++ ex.head else repr ex.value
    if ["bindingid", "slot", "ssavalue", "static_parameter", "label"].contains ex.head then
      base ++ match ex.value with | .int i => subscriptStr (toString i) | _ => "" else base)

theorem printingHelpers : PrintingHelpers := ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

def SyntaxTreePrinting : Prop :=
  (∀ valueStr ex indent kinds, showSyntaxTree valueStr 0 ex indent kinds = "") ∧
  (∀ valueStr ex, showSexpr 0 valueStr ex = "") ∧
  (∀ check valueStr ex kinds, showSyntaxPlain check valueStr ex kinds = do
    let _ ← check ex
    pure (showSyntaxTree valueStr (numchildren ex * 4 + 8) ex "" kinds)) ∧
  ∀ check valueStr ex, showSyntaxSexpr check valueStr ex = do
    let _ ← check ex
    pure (showSexpr (numchildren ex * 4 + 8) valueStr ex)

theorem syntaxTreePrinting : SyntaxTreePrinting :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end JuliaLean.DocsSyntaxCov.Syntax
