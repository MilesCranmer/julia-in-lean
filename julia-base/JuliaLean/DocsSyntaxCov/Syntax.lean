import JuliaLean.DocsSyntaxCov.Ast

/-!
# Model of `base/syntax.jl`

The Julia structures are represented by finite trees.  Julia object identity is an explicit
`Nat`; references in `.source` and `SyntaxContext.unexpanded` use those identities and a heap
lookup supplied to the provenance functions.  External operations (`repr`, parsing and
top-level evaluation) are parameters, so the Base wrappers preserve their call order without
axiomatizing those operations.
-/

namespace JuliaLean.DocsSyntaxCov.Syntax

open JuliaLean.DocsSyntaxCov

structure LineNode where
  line : Int
  file : Option String
  deriving DecidableEq, Repr

structure SourceCode where
  text : String
  byteOffset : Int
  filename : String
  firstLine : Int
  lineStarts : List Int
  deriving DecidableEq, Repr

structure SourceRef where
  code : SourceCode
  firstByte : Nat
  lastByte : Nat
  deriving DecidableEq, Repr

inductive TextSource where
  | line (l : LineNode)
  | ref (r : SourceRef)
  deriving DecidableEq, Repr

structure ScopeLayer where
  mod : String
  /-- Modules of successively escaped layers, nearest first. -/
  escaped : List String
  deriving DecidableEq, Repr

structure SyntaxContext where
  layer : Option ScopeLayer
  unexpanded : Option Nat
  edition : Int × Int
  internal : Bool
  deriving DecidableEq, Repr

inductive SValue where
  | none
  | str (s : String)
  | int (i : Int)
  | number (s : String)
  | module (m : String)
  | line (l : LineNode)
  | ref (r : SourceRef)
  | context (c : SyntaxContext)
  | other (v : JV)
  deriving Repr

inductive Source where
  | syntax (id : Nat)
  | text (s : TextSource)
  deriving DecidableEq, Repr

inductive Node where
  | mk (id : Nat) (head : String) (children : Option (List Node)) (value : SValue)
      (source : Source) (context : SyntaxContext) (jlSource : Option LineNode)
      (metadata : List (String × SValue)) (mod : Option String) (syntaxFlags : Nat)
  deriving Repr

namespace Node

def id : Node → Nat | .mk id .. => id
def head : Node → String | .mk _ h .. => h
def children? : Node → Option (List Node) | .mk _ _ cs .. => cs
def value : Node → SValue | .mk _ _ _ v .. => v
def source : Node → Source | .mk _ _ _ _ s .. => s
def context : Node → SyntaxContext | .mk _ _ _ _ _ c .. => c
def jlSource : Node → Option LineNode | .mk _ _ _ _ _ _ s .. => s
def metadata : Node → List (String × SValue) | .mk _ _ _ _ _ _ _ m .. => m
def mod : Node → Option String | .mk _ _ _ _ _ _ _ _ m .. => m
def syntaxFlags : Node → Nat | .mk _ _ _ _ _ _ _ _ _ f => f

def withChildren (n : Node) (cs : Option (List Node)) : Node :=
  .mk n.id n.head cs n.value n.source n.context n.jlSource n.metadata n.mod n.syntaxFlags

def withContext (n : Node) (c : SyntaxContext) : Node :=
  .mk n.id n.head n.children? n.value n.source c n.jlSource n.metadata n.mod n.syntaxFlags

def withSource (n : Node) (s : Source) : Node :=
  .mk n.id n.head n.children? n.value s n.context n.jlSource n.metadata n.mod n.syntaxFlags

def withContextSource (n : Node) (c : SyntaxContext) (s : Source) : Node :=
  .mk n.id n.head n.children? n.value s c n.jlSource n.metadata n.mod n.syntaxFlags

end Node

abbrev Heap := Nat → Option Node

/-- The nine-field inner constructor, `base/syntax.jl:57-59`. -/
def syntax9 (id : Nat) (head : String) (children : Option (List Node)) (value : SValue)
    (source : Source) (context : SyntaxContext) (jlSource : Option LineNode)
    (metadata : List (String × SValue)) (mod : Option String) (syntaxFlags : Nat) : Node :=
  .mk id head children value source context jlSource metadata mod syntaxFlags

/-- `SyntaxContext(mod, edition)`, lines 70-72. -/
def syntaxContext2 (mod : String) (edition : Int × Int) : SyntaxContext :=
  ⟨some ⟨mod, []⟩, none, edition, false⟩

/-- The five-argument `Syntax` constructor, lines 77-80. -/
def syntax5 (id : Nat) (head : String) (children : Option (List Node)) (value : SValue)
    (source : Source) (context : SyntaxContext) : Node :=
  syntax9 id head children value source context none [] none 0

def head (ex : Node) : String := ex.head
def isLeaf (ex : Node) : Bool := ex.children?.isNone
def numchildren (ex : Node) : Nat := ex.children?.map List.length |>.getD 0
def noChildren : List Node := []
def children (ex : Node) : List Node := ex.children?.getD noChildren

/-- The two `getindex` bodies; failure is an explicit bounds or type error. -/
def getindex (ex : Node) (i : Nat) : DJ Node :=
  match ex.children? with
  | none => .error .typeError
  | some cs => match cs[i - 1]? with | some c => .ok c | none => .error .boundsError

def getrange (ex : Node) (first length : Nat) : DJ (List Node) :=
  match ex.children? with
  | none => .error .typeError
  | some cs => if first = 0 ∨ first - 1 + length > cs.length then .error .boundsError
    else .ok ((cs.drop (first - 1)).take length)

def firstindex (_ : Node) : Nat := 1
def lastindex (ex : Node) : Nat := numchildren ex

/-- `node_string`, lines 115-142, with Julia's `repr` supplied by the caller. -/
def nodeString (reprValue : SValue → String) : Nat → Node → String
  | 0, ex => "(head=" ++ ex.head ++ ")"
  | depth + 1, ex =>
    let valuePart := match ex.value with
      | .none => ""
      | v => ", value=" ++ reprValue v
    let childPart := if isLeaf ex then ", leaf"
      else if depth = 0 then ""
      else ", children=[" ++ String.join ((children ex).map (fun c => "\n" ++ nodeString reprValue depth c)) ++ "]"
    "(head=" ++ ex.head ++ valuePart ++ childPart ++ ")"

def stringValue : SValue → Bool | .str _ => true | _ => false
def intValue : SValue → Bool | .int _ => true | _ => false
def vectorValue : SValue → Bool | .other (.expr "vector" _) => true | _ => false
def versionValue : SValue → Bool | .other (.expr "version" _) => true | _ => false

def leafNeeds : String → Option (SValue → Bool)
  | "identifier" | "core" | "top" | "symbol" | "globalref" | "symboliclabel"
  | "symbolicgoto" | "strmacroname" | "cmdmacroname" => some stringValue
  | "bindingid" | "label" | "slot" | "static_parameter" | "ssavalue" => some intValue
  | "slots" => some vectorValue
  | "version" => some versionValue
  | "value" | "lambdabindings" => some (fun _ => true)
  | "placeholder" | "nothing" | "tombstone" | "error" | "sourcelocation"
  | "latestworld" | "latestworld_if_toplevel" => none
  | _ => none

def leafOnly : List String :=
  ["identifier", "value", "placeholder", "bindingid", "label", "symbol", "nothing",
   "tombstone", "sourcelocation", "lambdabindings", "slots"]

/-- `_assert_syntax_node`, lines 160-208. -/
def assertSyntaxNode (st : Node) : Option (Node × String) :=
  if isLeaf st then
    if st.head = "globalref" && st.mod.isNone then some (st, "leaf globalref requires module in .mod")
    else match leafNeeds st.head with
      | some accepts => if accepts st.value then none else some (st, "needs value")
      | none =>
        if ["placeholder", "nothing", "tombstone", "error", "sourcelocation", "latestworld",
            "latestworld_if_toplevel"].contains st.head then none
        else match st.source with
          | .text (.ref _) => none
          | _ => some (st, "unrecognized leaf")
  else if leafOnly.contains st.head then some (st, "Found leaf-only kind with children") else none

/-- `_assert_syntax`, lines 213-231, with fuel for the recursive traversal. -/
def assertSyntaxRec : Nat → Node → List Nat → Option (Node × String)
  | 0, st, _ => some (st, "out of fuel")
  | fuel + 1, st, parents =>
    if parents.contains st.id then some (st, "cycle detected")
    else match assertSyntaxNode st with
      | some e => some e
      | none => (children st).foldl
        (fun found c => found.orElse fun _ => assertSyntaxRec fuel c (parents ++ [st.id])) none

/-- `assert_syntax`, lines 147-158. -/
def assertSyntax (fuel : Nat) (recursive : Bool) (st : Node) : DJ Unit :=
  let vr := if recursive then assertSyntaxRec fuel st [] else assertSyntaxNode st
  match vr with | some _ => .error (.errorException "assert_syntax failed") | none => .ok ()

structure Attrs where
  head : Option String := none
  children : Option (Option (List Node)) := none
  value : Option SValue := none
  source : Option Source := none
  context : Option SyntaxContext := none
  jlSource : Option (Option LineNode) := none
  metadata : Option (List (String × SValue)) := none
  mod : Option (Option String) := none
  syntaxFlags : Option Nat := none

/-- The semantic result of `@mknode`: copy each field, replace supplied attributes, use the
old node as provenance unless `source` is supplied, and use the macro line as `jl_source` in
debug mode.  The macro's argument and duplicate-name checks are represented by `valid`. -/
def mknode (valid debug : Bool) (old : Node) (attrs : Attrs) (macroLine : LineNode) : DJ Node :=
  if !valid then .error (.argumentError "usage: @mknode(old; attr=val...)")
  else .ok (.mk old.id (attrs.head.getD old.head) (attrs.children.getD old.children?)
    (attrs.value.getD old.value) (attrs.source.getD (.syntax old.id))
    (attrs.context.getD old.context)
    (attrs.jlSource.getD (if debug then some macroLine else old.jlSource))
    (attrs.metadata.getD old.metadata) (attrs.mod.getD old.mod) (attrs.syntaxFlags.getD old.syntaxFlags))

/-- The one-argument macro delegates to the two-argument macro after splitting parameters. -/
def mknode1 (isParameters : Bool) (x : JV) : JV :=
  let old := if isParameters then .val "_DEFAULT_NODE" else x
  let attrs := if isParameters then x else .nothing
  .expr "macrocall" [.sym "@mknode", .val "__source__", attrs, old]

def debugCheckAttrs (check : Node → DJ Unit) (x : Node) : DJ Node := do
  let _ ← check x
  pure x

def setproperty (_ : Node) (_ : String) (_ : SValue) : DJ Node :=
  .error (.errorException "Syntax: this can't be mutated")

/-- `mapchildren`, lines 296-320.  The first changed child allocates the copy; unchanged trees
return the original node. -/
def mapchildren (eqNode : Node → Node → Bool) (f : Node → Node) (ex : Node) : Node :=
  if isLeaf ex then ex
  else
    let orig := children ex
    let mapped := orig.map f
    if (List.zip mapped orig).all (fun p => eqNode p.1 p.2) then ex
    else ex.withChildren (some mapped)

def isBaseLayer (sc : SyntaxContext) : DJ Bool :=
  match sc.layer with | none => .error .typeError | some l => .ok l.escaped.isEmpty

def baseLayer : Nat → SyntaxContext → DJ ScopeLayer
  | 0, _ => .error (.errorException "out of fuel")
  | fuel + 1, sc => match sc.layer with
    | none => .error .typeError
    | some l => match l.escaped with
      | [] => .ok l
      | escaped :: rest => baseLayer fuel { sc with layer := some ⟨escaped, rest⟩ }

def escapeLayer (fuel : Nat) (sc : SyntaxContext) (recursive : Bool) : DJ SyntaxContext := do
  let l2 ← if recursive then (baseLayer fuel sc).map some else match sc.layer with
    | none => .error .typeError
    | some l => match l.escaped with | [] => .ok none | m :: rest => .ok (some ⟨m, rest⟩)
  pure ⟨l2, sc.unexpanded, sc.edition, sc.internal⟩

def syntaxModuleContext (sc : SyntaxContext) : DJ String := match sc.layer with
  | some l => .ok l.mod
  | none => .error .typeError

def syntaxModule (st : Node) : DJ String := match st.mod with
  | some m => .ok m
  | none => syntaxModuleContext st.context

def syntaxName (s : Node) : DJ String := match s.value with | .str x => .ok x | _ => .error .typeError
def edition (st : Node) : Int × Int := st.context.edition
def editionOther (_ : SValue) : Int × Int := (1, 14)
def withContext (st : Node) (sc : SyntaxContext) : Node := st.withContextSource sc st.source

abbrev ContextMap := List (SyntaxContext × SyntaxContext)
def contextGet (m : ContextMap) (k : SyntaxContext) : Option SyntaxContext :=
  (m.find? (fun p => decide (p.1 = k))).map Prod.snd
def contextSet (m : ContextMap) (k v : SyntaxContext) : ContextMap :=
  if m.any (fun p => decide (p.1 = k)) then m.map (fun p => if p.1 = k then (k, v) else p)
  else m ++ [(k, v)]

def mapChildrenState (f : Node → ContextMap → Node × ContextMap) :
    List Node → ContextMap → List Node × ContextMap
  | [], m => ([], m)
  | x :: xs, m =>
    let (x', m) := f x m
    let (xs', m) := mapChildrenState f xs m
    (x' :: xs', m)

/-- `adopt_scope`, lines 359-377, as a state-passing model of `scmap`. -/
def adoptScope (fuel : Nat) (scIn : SyntaxContext) (unexpandedIn : Option Nat) :
    Node → ContextMap → Node × ContextMap
  | st, scmap =>
    if fuel = 0 then (st, scmap) else
    let stSc := st.context
    let sc2 := (contextGet scmap stSc).getD
      (if stSc.layer = scIn.layer then stSc else
        ⟨scIn.layer, if stSc.layer.isNone then unexpandedIn else stSc.unexpanded,
          stSc.edition, stSc.internal⟩)
    let scmap := contextSet scmap stSc sc2
    let st2 := if stSc = sc2 then st else withContext st sc2
    if isLeaf st || numchildren st = 0 then (st2, scmap)
    else
      let (cs, scmap) := mapChildrenState (adoptScope (fuel - 1) scIn unexpandedIn) (children st2) scmap
      (st2.withChildren (some cs), scmap)

def adoptReference (fuel : Nat) (reference st : Node) : Node :=
  (adoptScope fuel reference.context st.context.unexpanded st []).1
def adoptMacro (fuel : Nat) (macrocall st : Node) : Node :=
  (adoptScope fuel macrocall.context (some macrocall.id) st []).1
def adoptMacroReference (fuel : Nat) (macrocall reference st : Node) : Node :=
  (adoptScope fuel reference.context (some macrocall.id) st []).1

def fillContext : Nat → Node → SyntaxContext → Node
  | 0, st, _ => st
  | fuel + 1, st, sc =>
    let st := if st.context = sc then st else withContext st sc
    st.withChildren (st.children?.map fun cs => cs.map (fun c => fillContext fuel c sc))

/-- `remove_scope`, lines 395-410. -/
def removeScope (fuel : Nat) : Node → ContextMap → Node × ContextMap
  | st, scmap =>
    if fuel = 0 then (st, scmap) else
    let stSc := st.context
    let sc2 := (contextGet scmap stSc).getD
      (if stSc.layer.isNone then stSc else ⟨none, stSc.unexpanded, stSc.edition, stSc.internal⟩)
    let scmap := contextSet scmap stSc sc2
    let st2 := if stSc = sc2 then st else withContext st sc2
    if isLeaf st || numchildren st = 0 then (st2, scmap)
    else
      let (cs, scmap) := mapChildrenState (removeScope (fuel - 1)) (children st2) scmap
      (st2.withChildren (some cs), scmap)

def removeScope1 (fuel : Nat) (st : Node) : Node := (removeScope fuel st []).1

def showLayer (objectId : ScopeLayer → String) (l : ScopeLayer) : String :=
  let rec go (mod : String) : List String → String
    | [] => "SL(" ++ mod ++ ",," ++ objectId ⟨mod, []⟩ ++ ")"
    | m :: rest => "SL(" ++ mod ++ "," ++ go m rest ++ "," ++ objectId ⟨mod, m :: rest⟩ ++ ")"
  go l.mod l.escaped

def showContext (showLayerFn : Option ScopeLayer → String) (heap : Heap) (sc : SyntaxContext) : String :=
  "[" ++ (if sc.edition = (1, 15) then "" else "old,") ++
    (if sc.internal then "internal," else "") ++ showLayerFn sc.layer ++ "," ++
    (match sc.unexpanded.bind heap with
     | none => ""
     | some u => if u.head = "macrocall" then (children u).head?.map Node.head |>.getD "" else u.head) ++ "]"

def showLayerCompact (f : ScopeLayer → String) (l : ScopeLayer) : String := f l
def showContextCompact (f : SyntaxContext → String) (c : SyntaxContext) : String := f c

/-- `provenance`, lines 489-497, with fuel for malformed source cycles. -/
def provenance (heap : Heap) : Nat → Node → List Node
  | 0, _ => []
  | fuel + 1, st => match st.source with
    | .text _ => []
    | .syntax id => match heap id with | none => [] | some s => s :: provenance heap fuel s

def prov (heap : Heap) (st : Node) : Node := match st.source with
  | .syntax id => (heap id).getD st
  | .text _ => st

def provEnd (heap : Heap) : Nat → Node → Node
  | 0, st => st
  | fuel + 1, st => match st.source with
    | .syntax id => provEnd heap fuel ((heap id).getD st)
    | .text _ => st

def sourceref (heap : Heap) (fuel : Nat) (st : Node) : DJ TextSource :=
  match (provEnd heap fuel st).source with | .text s => .ok s | .syntax _ => .error .typeError

def macroProv (heap : Heap) (st : Node) : Option Node := st.context.unexpanded.bind heap

def macroProvEnd (heap : Heap) : Nat → Node → Option Node
  | 0, _ => none
  | fuel + 1, st => match macroProv heap st with
    | none => none
    | some mp => (macroProvEnd heap fuel mp).orElse fun _ => some mp

def unexpandedSourceref (heap : Heap) (fuel : Nat) (st : Node) : DJ TextSource :=
  match macroProvEnd heap fuel st with | none => sourceref heap fuel st | some mp => sourceref heap fuel mp

/-- `_trim_provenance`, lines 417-435.  The context cache is explicit; the model keeps the
identity of an unexpanded node when it is retained and replaces every `.source` chain by its
terminal text reference. -/
def trimProvenance (heap : Heap) (fuel : Nat) (trimUnexpanded : Bool) :
    Node → ContextMap → DJ (Node × ContextMap)
  | st, scmap =>
    if fuel = 0 then .error (.errorException "out of fuel") else do
      let stSc := st.context
      let sc2 := (contextGet scmap stSc).getD
        ⟨stSc.layer, if stSc.unexpanded.isNone || trimUnexpanded then none else stSc.unexpanded,
          stSc.edition, stSc.internal⟩
      let scmap := contextSet scmap stSc sc2
      let src ← sourceref heap fuel st
      let st2 := st.withContextSource sc2 (.text src)
      if isLeaf st || numchildren st = 0 then pure (st2, scmap)
      else
        let results ← (children st).mapM fun c =>
          trimProvenance heap (fuel - 1) trimUnexpanded c scmap
        let cs := results.map Prod.fst
        let scmap := (results.getLast?).map Prod.snd |>.getD scmap
        pure (st2.withChildren (some cs), scmap)

def trimProvenance1 (heap : Heap) (fuel : Nat) (trimUnexpanded : Bool) (st : Node) : DJ Node := do
  let (st, _) ← trimProvenance heap fuel trimUnexpanded st []
  pure st

def flattenedProvenance (heap : Heap) (fuel : Nat) (st : Node) : List Node :=
  let rec go : Nat → Node → List Node → List Node
    | 0, _, out => out
    | n + 1, x, out =>
      let out := match macroProv heap x with
        | some m => if m.id = (prov heap x).id then out else go n m out
        | none => out
      out ++ [provEnd heap n x]
  go fuel st []

def flattenedProvenanceInto (heap : Heap) (fuel : Nat) (st : Node) (out : List Node) : List Node :=
  out ++ flattenedProvenance heap fuel st

def filename (heap : Heap) (fuel : Nat) (s : Node) : DJ String := do
  let sr ← sourceref heap fuel s
  pure (match sr with | .line l => l.file.getD "" | .ref r => r.code.filename)

def countLe (x : Int) : List Int → Nat
  | [] => 0
  | y :: ys => if y ≤ x then 1 + countLe x ys else 0

def sourceLine (src : SourceCode) (b : Int) : Int :=
  src.firstLine - 1 + countLe (b - src.byteOffset) src.lineStarts

def firstLineNodeSyntax (heap : Heap) (fuel : Nat) (s : Node) : DJ LineNode := do
  let sr ← sourceref heap fuel s
  match sr with
  | .line l => pure l
  | .ref r => pure ⟨sourceLine r.code r.firstByte, some r.code.filename⟩

def firstLineNodeRef (r : SourceRef) : LineNode :=
  ⟨sourceLine r.code r.firstByte, some r.code.filename⟩

def firstLineNodeLine (l : LineNode) : LineNode := l

/-- `_first_linenode`, lines 597-606, on the shared `JV` expression model. -/
def firstLineInExpr : Nat → JV → Option LineNode
  | 0, _ => none
  | fuel + 1, .expr h args =>
    if ["macrocall", "quote", "inert"].contains h then none
    else args.foldl (fun found a => found.orElse fun _ => match a with
      | .lnn line file => some ⟨line, some file⟩
      | e@(.expr _ _) => firstLineInExpr fuel e
      | _ => none) none
  | _, _ => none

def firstLineExpr (fuel : Nat) (e : JV) : LineNode := (firstLineInExpr fuel e).getD ⟨0, some ""⟩

def unescapeLnn : Nat → JV → Option LineNode
  | 0, _ => none
  | _, .lnn line file => some ⟨line, some file⟩
  | fuel + 1, .expr h (x :: _) => if h = "escape" || h = "hygienic-scope" then unescapeLnn fuel x else none
  | _, _ => none

def getInnerLnn (fuel : Nat) (e : JV) (dflt : LineNode) : LineNode :=
  match e with
  | .expr h args =>
    if h = "struct" || h = "macrocall" then (firstLineInExpr fuel e).getD dflt
    else if (h = "quote" || h = "inert") then
      match args.head? with | some x@(.expr _ _) => (firstLineInExpr fuel x).getD dflt | _ => dflt
    else if ["function", "macro", "module", "=", "->"].contains h then
      match args.getLast? with
      | some (.expr "block" (x :: _)) => (unescapeLnn fuel x).getD dflt
      | _ => dflt
    else dflt
  | _ => dflt

def isLoweringAstNode : JV → Bool
  | .sym _ | .qn _ | .expr _ _ | .val "GlobalRef" => true
  | _ => false

/-- A compact, branch-faithful Expr-to-Syntax conversion, lines 651-699. -/
def exprToSyntax : Nat → Nat → JV → SyntaxContext → Source → Bool → DJ (Node × Source)
  | 0, _, _, _, _, _ => .error (.errorException "out of fuel")
  | fuel + 1, nextId, e, context, src, quoted =>
    match e with
    | .sym s => .ok (syntax5 nextId "identifier" none (.str s) src context, src)
    | .qn v => do
      let (child, src) ← exprToSyntax fuel (nextId + 1) v context src true
      pure (syntax5 nextId "inert" (some [child]) .none src context, src)
    | .expr h args =>
      if h = "value" || h = "identifier" then .error (.errorException "reserved Expr head")
      else
        let quoted := quoted || h = "quote" || h = "inert"
        let rec convert : Nat → List JV → Source → DJ (List Node × Source)
          | _, [], src => .ok ([], src)
          | id, a :: rest, src => do
            let (n, src) ← exprToSyntax fuel id a context src quoted
            let (ns, src) ← convert (id + 1) rest src
            pure (n :: ns, src)
        do
          let (cs, src') ← convert (nextId + 1) args src
          pure (syntax5 nextId h (some cs) .none src context, src')
    | .val "SSAValue" | .val "SlotNumber" =>
      if quoted then .ok (syntax5 nextId "value" none (.other e) src context, src)
      else .error (.errorException "SSAValue and SlotNumber objects should not occur in an AST")
    | .val "GlobalRef" => .ok (syntax9 nextId "identifier" none (.str "GlobalRef") src context none [] (some "GlobalRef") 0, src)
    | .lnn line file =>
      let src' := match src with | .text (.line _) => .text (.line ⟨line, some file⟩) | _ => src
      .ok (syntax5 nextId "value" none (.line ⟨line, some file⟩) src' context, src')
    | _ => .ok (syntax5 nextId "value" none (.other e) src context, src)

def exprToSyntaxText (fuel nextId : Nat) (e : JV) (src : TextSource) (context : SyntaxContext) : DJ Node := do
  let (s, _) ← exprToSyntax fuel nextId e context (.text src) false
  pure s

def exprToSyntaxFromNode (fuel nextId : Nat) (e : JV) (src : Node) : DJ Node := do
  let (s, _) ← exprToSyntax fuel nextId e src.context (.syntax src.id) false
  pure s

def valueIsDoc : SValue → Bool | .str s => s = "doc" | _ => false

def isMetaDocBlock (s : Node) : Bool :=
  s.head = "block" && numchildren s = 2 &&
    match (children s).head? with
    | some s1 => s1.head = "meta" && numchildren s1 = 1 &&
      match (children s1).head? with
      | some s11 => s11.head = "identifier" && valueIsDoc s11.value
      | none => false
    | none => false

def isEventuallyCall : Nat → JV → Bool
  | 0, _ => false
  | fuel + 1, .expr h args => h = "call" ||
      (["escape", "where", "::"].contains h && match args.head? with
        | some x => isEventuallyCall fuel x | none => false)
  | _, _ => false

def pushLno (ex : JV) (lno : LineNode) (first : Bool := false) : JV := match ex with
  | .expr h args =>
    if lno.file != some "" || lno.line != 0 then
      .expr h (if first then .lnn lno.line (lno.file.getD "") :: args else args ++ [.lnn lno.line (lno.file.getD "")])
    else ex
  | _ => ex

/-- `syntax_to_expr`, lines 718-788.  It includes the identifier, value, inert and general
node branches; optional line-node insertion is represented by `lineOf`. -/
def syntaxToExpr (lineOf : Node → LineNode) : Nat → Node → Bool → DJ JV
  | 0, _, _ => .error (.errorException "out of fuel")
  | fuel + 1, s, suppress =>
    if s.head = "identifier" then match s.value with
      | .str n => .ok (match s.mod with | some m => .expr "GlobalRef" [.val m, .sym n] | none => .sym n)
      | _ => .error .typeError
    else if s.head = "value" then match s.value with
      | .other v => .ok (if isLoweringAstNode v then .qn v else v)
      | .line l => .ok (.lnn l.line (l.file.getD ""))
      | .str x => .ok (.str x)
      | .int x => .ok (.int x)
      | _ => .ok .nothing
    else if s.head = "inert" then match (children s).head? with
      | none => .error .boundsError
      | some c => do pure (.qn (← syntaxToExpr lineOf fuel c false))
    else if isLeaf s then .error .assertionError
    else
      let rec convert : Nat → List Node → DJ (List JV)
        | _, [] => .ok []
        | i, c :: cs => do
          let suppressChild := (i = 1 && (s.head = "for" || s.head = "let")) || (i = 2 && s.head = "do")
          let x ← syntaxToExpr lineOf fuel c suppressChild
          let xs ← convert (i + 1) cs
          let x := if (s.head = "block" || s.head = "toplevel") && !suppress && !isMetaDocBlock s
            then match pushLno (.expr "block" [x]) (lineOf c) with | .expr _ ys => ys | _ => [x]
            else [x]
          pure (x ++ xs)
      do
        let args ← convert 1 (children s)
        let out := .expr s.head args
        pure (if !suppress && s.head = "block" && args.isEmpty then pushLno out (lineOf s) else out)

/-- `_c_parseall_expr`, lines 791-798. -/
def cParseallExpr (unsafeString : Nat → Nat → String)
    (parseString : String → String → Int → JV × Int)
    (ptr len : Nat) (filename : String) (lineno : Int) : JV :=
  let str := unsafeString ptr len
  let (ex, offset) := parseString str filename lineno
  .expr "svec" [ex, .int (offset - 1)]

def flToplevelEval (eval : String → JV → JV) (lineOf : Node → LineNode)
    (mod : String) (x : Sum Node JV) : DJ JV := match x with
  | .inr e => .ok (eval mod e)
  | .inl s => do
    let e ← syntaxToExpr lineOf (numchildren s * 4 + 8) s false
    pure (eval mod (.expr "toplevel" [.lnn (lineOf s).line ((lineOf s).file.getD ""), e]))

def attrsummary (_show : SValue → String) (name : String) (value : SValue) : String := match value with
  | .number n => name ++ "=" ++ n
  | .line l => name ++ "=L" ++ toString l.line
  | .module m => name ++ "=" ++ m
  | _ => name

def subscriptChar : Char → Char
  | '0' => '₀' | '1' => '₁' | '2' => '₂' | '3' => '₃' | '4' => '₄'
  | '5' => '₅' | '6' => '₆' | '7' => '₇' | '8' => '₈' | '9' => '₉' | c => c

def subscriptStr (s : String) : String := String.mk (s.toList.map subscriptChar)

def valueIsNone : SValue → Bool | .none => true | _ => false

def valueString (reprValue : SValue → String) (heap : Heap) (ex : Node) : String :=
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
    | _ => if valueIsNone ex.value then "::" ++ ex.head else reprValue ex.value
  if ["bindingid", "slot", "ssavalue", "static_parameter", "label"].contains ex.head then
    base ++ match ex.value with | .int i => subscriptStr (toString i) | _ => ""
  else base

def showSyntaxTree (valueStr : Node → String) : Nat → Node → String → Bool → String
  | 0, _, _, _ => ""
  | fuel + 1, ex, indent, showKinds =>
    let node := if isLeaf ex then valueStr ex else "[" ++ ex.head ++ "]"
    let line := indent ++ node ++ (if showKinds && isLeaf ex then " :: " ++ ex.head else "") ++ "\n"
    line ++ String.join ((children ex).map fun c => showSyntaxTree valueStr fuel c (indent ++ "  ") showKinds)

def showSyntaxPlain (check : Node → DJ Unit) (valueStr : Node → String)
    (ex : Node) (showKinds : Bool := true) : DJ String := do
  let _ ← check ex
  pure (showSyntaxTree valueStr (numchildren ex * 4 + 8) ex "" showKinds)

def showSexpr : Nat → (Node → String) → Node → String
  | 0, _, _ => ""
  | fuel + 1, valueStr, ex => if isLeaf ex then valueStr ex
    else "(" ++ ex.head ++ String.join ((children ex).map fun n => " " ++ showSexpr fuel valueStr n) ++ ")"

def showSyntaxSexpr (check : Node → DJ Unit) (valueStr : Node → String) (ex : Node) : DJ String := do
  let _ ← check ex
  pure (showSexpr (numchildren ex * 4 + 8) valueStr ex)

end JuliaLean.DocsSyntaxCov.Syntax
