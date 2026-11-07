import JuliaLean.base.docs.Docs
import JuliaLean.Core
import JuliaLean.base.expr
import JuliaLean.base.boot


section

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

end


/-!
# Model of `base/syntax.jl`

The `Syntax` trees of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` used by macro expansion
and lowering: scope layers, syntax contexts, source references, the `@mknode` macro, provenance
queries, the `Expr` ↔ `Syntax` conversions, the frontend helpers `_c_parseall_expr` and
`fl_toplevel_eval`, and the printing of `Syntax` trees.

Values, the runtime world and the builtins are those of the installed `base/boot.jl` model
(`JuliaLean.base.boot`: `CoreM`, `CoreOps`); `Expr` values and `Meta.isexpr`/`remove_linenums!`
are the installed `base/expr.jl` model, and the `Core` constructors called here (`Expr`,
`QuoteNode`, `LineNumberNode`, `Symbol`, `GlobalRef`, `UInt16`) are the `boot.jl` ones. Instances
of the structs of this file are `SObj` records, all fields kept as values; the mutable ones
(`ScopeLayer`, `SyntaxContext`, `SourceCode`, `Syntax`) are allocated with a fresh identity by
`SyntaxOps.alloc`, and `SyntaxOps.syn` reads the record of a value. A field read `x.f` is the
record field for these structs and the builtin `getfield` otherwise. Calls of other Base generic
functions (`length`, `push!`, `string`, `*`, `get`, `setindex!`, `repr`, `print`, `printstyled`,
`sort!`, `searchsortedlast`, ...) are `CoreOps.call` of the function `Base.name`, dispatched when
they run; the elements of a collection are read by `SyntaxOps.elems`. Closures passed to
`mapchildren` are Lean functions of their argument.

`@mknode` is modelled twice: as the macro (a function of its arguments returning the expansion,
as in `base/expr.jl`), and, at each use in a method, as the call its expansion makes:
`_debug_check_attrs(Syntax(fields...))` with the fields taken from `old` in field order and
overridden by the attributes. The macro puts `__source__`, a `LineNumberNode`, in the `jl_source`
argument position of that call, where it evaluates to `nothing` (nodes built by `@mknode` without
a `jl_source` attribute have `jl_source === nothing` on nightly). Recursion is a
`partial_fixpoint`, where `none` is divergence.
-/

namespace JuliaLean.base.syntax

open JuliaLean
open JuliaLean.base.expr (Value Sym)
open JuliaLean.base.boot (CoreM CoreOps I64)

/-- The fields of a `ScopeLayer`. -/
structure LayerR (L : Type) where
  mod : Value L
  escaped : Value L

/-- The fields of a `SyntaxContext`. -/
structure ContextR (L : Type) where
  layer : Value L
  unexpanded : Value L
  edition : Value L
  internal : Value L

/-- The fields of a `SourceCode`. -/
structure CodeR (L : Type) where
  text : Value L
  byte_offset : Value L
  filename : Value L
  first_line : Value L
  line_starts : Value L

/-- The fields of a `SourceRef`. -/
structure RefR (L : Type) where
  code : Value L
  first_byte : Value L
  last_byte : Value L

/-- The fields of a `Syntax`. -/
structure SyntaxR (L : Type) where
  head : Value L
  children : Value L
  value : Value L
  source : Value L
  context : Value L
  jl_source : Value L
  meta_ : Value L
  mod : Value L
  syntax_flags : Value L

/-- An instance of a struct of this file. -/
inductive SObj (L : Type) where
  | layer (r : LayerR L)
  | context (r : ContextR L)
  | code (r : CodeR L)
  | ref (r : RefR L)
  | syntax (r : SyntaxR L)
  | macroContext (macrocall : Value L)

/-- The operations of this file beyond the `Core` ones. -/
structure SyntaxOps (W L : Type) extends CoreOps W L where
  /-- The value of the binding `Base.name` (a function, a type or a constant). -/
  baseFn : String → L
  /-- The instance of a struct of this file that a value is, if it is one. -/
  syn : L → Option (SObj L)
  /-- `new` of a mutable struct of this file: an object with a fresh identity. -/
  alloc : SObj L → CoreM W L (Value L)
  /-- `new` of an immutable struct of this file. -/
  imm : SObj L → L
  /-- The elements of a collection, in iteration order. -/
  elems : Value L → CoreM W L (List (Value L))
  /-- A `CodeInfo` with its line numbers removed (`base/expr.jl`'s `remove_linenums!`). -/
  codeInfoNoLines : L → L
  /-- `jl_toplevel_eval(mod, ex)`. -/
  toplevelEvalC : Value L → Value L → CoreM W L (Value L)
  /-- A `Char` value. -/
  char : Char → L

section
variable {W L : Type} (ops : SyntaxOps W L)

/-- `Base.name` as a value. -/
def bV (name : String) : Value L := .leaf (ops.baseFn name)

/-- A call `Base.name(args...)`. -/
def callB (name : String) (args : List (Value L)) : CoreM W L (Value L) :=
  ops.call (bV ops name) args

/-- A `String` value. -/
def sV (s : String) : Value L := .leaf (ops.str s)

/-- An `Int` value. -/
def iV (n : Int) : Value L := .leaf (ops.ofInt (JInt.lit .i64 n))

/-- `nothing`. -/
def nothingS : Value L := .leaf ops.nothing

/-- `x === nothing` (`isnothing(x)`). -/
def isNothing (x : Value L) : Bool := ops.same x (nothingS ops)

/-- A `Bool` value. -/
def bS (b : Bool) : Value L := .leaf (ops.ofBool b)

/-- `x === :s`. -/
def isSym (x : Value L) (s : String) : Bool :=
  match x with
  | .symbol n => n == s
  | _ => false

/-- The instance of a struct of this file that `x` is. -/
def synOf (x : Value L) : Option (SObj L) :=
  match x with
  | .leaf l => ops.syn l
  | _ => none

/-- The fields of `x` if it is a `Syntax`. -/
def asSyntax (x : Value L) : Option (SyntaxR L) :=
  match synOf ops x with
  | some (.syntax r) => some r
  | _ => none

/-- `x isa Syntax`. -/
def isSyntax (x : Value L) : Bool := (asSyntax ops x).isSome

/-- `x isa SourceRef`. -/
def isSourceRef (x : Value L) : Bool :=
  match synOf ops x with
  | some (.ref _) => true
  | _ => false

/-- `x isa ScopeLayer`. -/
def isLayer (x : Value L) : Bool :=
  match synOf ops x with
  | some (.layer _) => true
  | _ => false

/-- `x isa LineNumberNode`. -/
def isLnn (x : Value L) : Bool :=
  match x with
  | .lineNumberNode .. => true
  | _ => false

/-- `x.name`: the record field for the structs of this file, `getfield` otherwise. -/
def getprop (x : Value L) (name : String) : CoreM W L (Value L) :=
  let field : Option (Value L) := match synOf ops x, name with
    | some (.layer r), "mod" => some r.mod
    | some (.layer r), "escaped" => some r.escaped
    | some (.context r), "layer" => some r.layer
    | some (.context r), "unexpanded" => some r.unexpanded
    | some (.context r), "edition" => some r.edition
    | some (.context r), "internal" => some r.internal
    | some (.code r), "text" => some r.text
    | some (.code r), "byte_offset" => some r.byte_offset
    | some (.code r), "filename" => some r.filename
    | some (.code r), "first_line" => some r.first_line
    | some (.code r), "line_starts" => some r.line_starts
    | some (.ref r), "code" => some r.code
    | some (.ref r), "first_byte" => some r.first_byte
    | some (.ref r), "last_byte" => some r.last_byte
    | some (.syntax r), "head" => some r.head
    | some (.syntax r), "children" => some r.children
    | some (.syntax r), "value" => some r.value
    | some (.syntax r), "source" => some r.source
    | some (.syntax r), "context" => some r.context
    | some (.syntax r), "jl_source" => some r.jl_source
    | some (.syntax r), "meta" => some r.meta_
    | some (.syntax r), "mod" => some r.mod
    | some (.syntax r), "syntax_flags" => some r.syntax_flags
    | some (.macroContext m), "macrocall" => some m
    | _, _ => none
  match field with
  | some v => pure v
  | none => ops.getfield x (.symbol name)

/-- `x::T` for the type `Base.T` and a test `ok` of `x isa T`. -/
def assertKind (ok : Bool) (x : Value L) (T : String) : CoreM W L (Value L) :=
  if ok then pure x
  else JuliaLean.base.boot.throwTypeError ops.toCoreOps "typeassert" "" (bV ops T) x

/-- The value lowering of `new` stores in the typed field `field` of the struct `Base.S`. -/
def cfS (S : String) (field : Sym) (x : Value L) : CoreM W L (Value L) :=
  JuliaLean.base.boot.convertField ops.toCoreOps (bV ops S) field x

/-- The argument conversion of a default constructor called with arguments not all of the field
types: `convert(fieldtype(S, f), x)::fieldtype(S, f)` for each field. -/
def convertArg (S : String) (field : Sym) (x : Value L) : CoreM W L (Value L) := do
  let T ← ops.fieldtype (bV ops S) field
  JuliaLean.base.boot.typeassert ops.toCoreOps (← ops.call (.leaf (ops.core "convert")) [T, x]) T

/-- `isa(x, fieldtype(S, f))` for every argument of a default constructor call. -/
def fieldTypesMatch (S : String) : List (Sym × Value L) → CoreM W L Bool
  | [] => pure true
  | (f, x) :: rest => do
    let T ← ops.fieldtype (bV ops S) f
    if ops.isa x T then fieldTypesMatch S rest else pure false

/-- `Meta.name`. -/
def metaFn (name : String) : CoreM W L (Value L) :=
  ops.getfield (bV ops "Meta") (.symbol name)

/-- The condition of `if`, `&&`, `||` or `?:`: a `Bool`, otherwise the runtime's
`TypeError(:if, "", Bool, x)`. -/
def cond (x : Value L) : CoreM W L Bool :=
  match x with
  | .leaf l => match ops.asBool l with
    | some b => pure b
    | none => JuliaLean.base.boot.throwTypeError ops.toCoreOps "if" "" (.leaf (ops.core "Bool")) x
  | _ => JuliaLean.base.boot.throwTypeError ops.toCoreOps "if" "" (.leaf (ops.core "Bool")) x

/-- `throw(ArgumentError(msg))`. -/
def throwArg {α : Type} (msg : Value L) : CoreM W L α := do
  throw (← JuliaLean.base.boot.ArgumentError ops.toCoreOps msg)

/-- `a, b = v`: the first two elements of the iteration of `v`; `BoundsError(v, i)` when the
iteration ends before element `i`. -/
def destructure2 (v : Value L) : CoreM W L (Value L × Value L) := do
  match ← ops.elems v with
  | a :: b :: _ => pure (a, b)
  | [_] => throw (JuliaLean.base.boot.BoundsError2 ops.toCoreOps v (iV ops 2))
  | [] => throw (JuliaLean.base.boot.BoundsError2 ops.toCoreOps v (iV ops 1))

/-- The tuple `(xs...)` as a value. -/
def tup (xs : List (Value L)) : Value L := .leaf (ops.tuple xs)

/-- The field names of `Syntax`, in order (`fieldnames(Syntax)`). -/
def syntaxFields : List Sym :=
  ["head", "children", "value", "source", "context", "jl_source", "meta", "mod", "syntax_flags"]

/-- A keyword call `f(args...; k=v, ...)`: `Core.kwcall((; k=v, ...), f, args...)`. -/
def callKw (f : String) (kwargs : List (Sym × Value L)) (args : List (Value L)) :
    CoreM W L (Value L) := do
  let nt ← JuliaLean.base.boot.NamedTuple_names ops.toCoreOps
    (tup ops (kwargs.map fun kv => .symbol kv.1)) (tup ops (kwargs.map (·.2)))
  ops.call (.leaf (ops.core "kwcall")) (nt :: bV ops f :: args)

/-- `Dict{SyntaxContext, SyntaxContext}()`. -/
def newContextDict : CoreM W L (Value L) := do
  ops.call (← ops.applyType (bV ops "Dict") [bV ops "SyntaxContext", bV ops "SyntaxContext"]) []

/-- A field of the node an `@mknode(old; attrs...)` expansion builds: the attribute if given,
otherwise `old` for `source`, `nothing` for `jl_source` and `old`'s field for the others. -/
def mknodeField (old : Value L) (attrs : List (Sym × Value L)) (f : Sym) : CoreM W L (Value L) :=
  match attrs.lookup f with
  | some v => pure v
  | none =>
    if f == "source" then pure old
    else if f == "jl_source" then pure (nothingS ops)
    else getprop ops old f

/-- The value `MIME"s"()`. -/
def mimeV (s : String) : CoreM W L (Value L) := do
  ops.call (← ops.applyType (bV ops "MIME") [.symbol s]) []

-- Reason: A comment.
-- UNTRANSLATED
-- Source: base/syntax.jl:1-2 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Data structures used by macro-expansion and lowering
-- 
-- /Source

/--
Julia source: base/syntax.jl:3-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct ScopeLayer
    const mod::Module
    const escaped::Union{Nothing, ScopeLayer}
end

```
-/
def ScopeLayer_new (mod escaped : Value L) : CoreM W L (Value L) := do
  let mod ← cfS ops "ScopeLayer" "mod" mod
  let escaped ← cfS ops "ScopeLayer" "escaped" escaped
  ops.alloc (.layer ⟨mod, escaped⟩)
/-- The call `ScopeLayer(mod, escaped)`: the typed default constructor for arguments of the field
types, otherwise the converting one. -/
def ScopeLayer (mod escaped : Value L) : CoreM W L (Value L) := do
  if ← fieldTypesMatch ops "ScopeLayer" [("mod", mod), ("escaped", escaped)] then
    ScopeLayer_new ops mod escaped
  else
    let mod ← convertArg ops "ScopeLayer" "mod" mod
    let escaped ← convertArg ops "ScopeLayer" "escaped" escaped
    ScopeLayer_new ops mod escaped

/--
Julia source: base/syntax.jl:8-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
Each node has a SyntaxContext describing its macro expansion and edition.
`SyntaxContext` is shared between all nodes of a single macro expansion, and is
one-to-one with ScopeLayer, with a few exceptions (contexts sharing same layer):
- `escape` and adopt_scope
- Desugaring creates internal contexts in its better version of `gensym`

We may want to move layer out of this struct for easier adopt_scope and
rebase_layer operations, but assuming mostly hygienic macros and few
scope-changing functions, this is most compact.
"""
mutable struct SyntaxContext
    const layer::Union{Nothing, ScopeLayer}
    # For provenance; is not affected by escaping
    const unexpanded::Any # Union{Syntax, Nothing}
    const edition::Tuple{Int, Int}
    const internal::Bool
end

```
-/
def SyntaxContext_new (layer unexpanded edition internal : Value L) : CoreM W L (Value L) := do
  let layer ← cfS ops "SyntaxContext" "layer" layer
  let edition ← cfS ops "SyntaxContext" "edition" edition
  let internal ← cfS ops "SyntaxContext" "internal" internal
  ops.alloc (.context ⟨layer, unexpanded, edition, internal⟩)
/-- The call `SyntaxContext(layer, unexpanded, edition, internal)` of a default constructor. -/
def SyntaxContext4 (layer unexpanded edition internal : Value L) : CoreM W L (Value L) := do
  if ← fieldTypesMatch ops "SyntaxContext"
      [("layer", layer), ("unexpanded", unexpanded), ("edition", edition), ("internal", internal)] then
    SyntaxContext_new ops layer unexpanded edition internal
  else
    let layer ← convertArg ops "SyntaxContext" "layer" layer
    let edition ← convertArg ops "SyntaxContext" "edition" edition
    let internal ← convertArg ops "SyntaxContext" "internal" internal
    SyntaxContext_new ops layer unexpanded edition internal

/--
Julia source: base/syntax.jl:27-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Similar to JuliaSyntax.SourceFile
mutable struct SourceCode
    const text::SubString{String}
    const byte_offset::Int
    const filename::Symbol
    const first_line::Int
    const line_starts::Vector{Int}
end

```
-/
def SourceCode_new (text byte_offset filename first_line line_starts : Value L) :
    CoreM W L (Value L) := do
  let text ← cfS ops "SourceCode" "text" text
  let byte_offset ← cfS ops "SourceCode" "byte_offset" byte_offset
  let filename ← cfS ops "SourceCode" "filename" filename
  let first_line ← cfS ops "SourceCode" "first_line" first_line
  let line_starts ← cfS ops "SourceCode" "line_starts" line_starts
  ops.alloc (.code ⟨text, byte_offset, filename, first_line, line_starts⟩)
/-- The call `SourceCode(text, byte_offset, filename, first_line, line_starts)`. -/
def SourceCode (text byte_offset filename first_line line_starts : Value L) :
    CoreM W L (Value L) := do
  if ← fieldTypesMatch ops "SourceCode" [("text", text), ("byte_offset", byte_offset),
      ("filename", filename), ("first_line", first_line), ("line_starts", line_starts)] then
    SourceCode_new ops text byte_offset filename first_line line_starts
  else
    let text ← convertArg ops "SourceCode" "text" text
    let byte_offset ← convertArg ops "SourceCode" "byte_offset" byte_offset
    let filename ← convertArg ops "SourceCode" "filename" filename
    let first_line ← convertArg ops "SourceCode" "first_line" first_line
    let line_starts ← convertArg ops "SourceCode" "line_starts" line_starts
    SourceCode_new ops text byte_offset filename first_line line_starts

/--
Julia source: base/syntax.jl:36-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Reference to bytes within a source file
struct SourceRef
    code::SourceCode
    first_byte::UInt32
    last_byte::UInt32
end

```
-/
def SourceRef_new (code first_byte last_byte : Value L) : CoreM W L (Value L) := do
  let code ← cfS ops "SourceRef" "code" code
  let first_byte ← cfS ops "SourceRef" "first_byte" first_byte
  let last_byte ← cfS ops "SourceRef" "last_byte" last_byte
  pure (.leaf (ops.imm (.ref ⟨code, first_byte, last_byte⟩)))
/-- The call `SourceRef(code, first_byte, last_byte)`. -/
def SourceRef (code first_byte last_byte : Value L) : CoreM W L (Value L) := do
  if ← fieldTypesMatch ops "SourceRef"
      [("code", code), ("first_byte", first_byte), ("last_byte", last_byte)] then
    SourceRef_new ops code first_byte last_byte
  else
    let code ← convertArg ops "SourceRef" "code" code
    let first_byte ← convertArg ops "SourceRef" "first_byte" first_byte
    let last_byte ← convertArg ops "SourceRef" "last_byte" last_byte
    SourceRef_new ops code first_byte last_byte

/--
Julia source: base/syntax.jl:43-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct Syntax
    const head::Symbol
    # Should be considered immutable
    const children::Union{Nothing, Vector{Syntax}}
    const value::Any
    const source::Union{Syntax,SourceRef,LineNumberNode}
    const context::SyntaxContext
    const jl_source::Union{Nothing, LineNumberNode}
    meta::Union{Nothing, Base.ImmutableDict{Symbol,Any}}
    # TODO: this is rarely used, and should just be part of context
    const mod::Union{Nothing, Module}
    # TODO: this is almost never populated and semantically irrelevant after
    # parsing
    const syntax_flags::UInt16
    function Syntax(head, children, @nospecialize(value), source, context, jl_source, meta, mod, syntax_flags)
        new(head, children, value, source, context, jl_source, meta, mod, syntax_flags)
    end
end
```
-/
def Syntax9 (head children value source context jl_source meta_ mod syntax_flags : Value L) :
    CoreM W L (Value L) := do
  let head ← cfS ops "Syntax" "head" head
  let children ← cfS ops "Syntax" "children" children
  let source ← cfS ops "Syntax" "source" source
  let context ← cfS ops "Syntax" "context" context
  let jl_source ← cfS ops "Syntax" "jl_source" jl_source
  let meta_ ← cfS ops "Syntax" "meta" meta_
  let mod ← cfS ops "Syntax" "mod" mod
  let syntax_flags ← cfS ops "Syntax" "syntax_flags" syntax_flags
  ops.alloc (.syntax ⟨head, children, value, source, context, jl_source, meta_, mod, syntax_flags⟩)

-- Reason: The type alias `SourceAttrType` defines no method.
-- UNTRANSLATED
-- Source: base/syntax.jl:61-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const SourceAttrType = Union{Syntax,SourceRef,LineNumberNode}
-- 
-- /Source

/--
Julia source: base/syntax.jl:63-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Passed to the user as an implicit new-macro argument, like __module__ in old
# macros
struct MacroContext
    macrocall::Syntax
end

```
-/
def MacroContext_new (macrocall : Value L) : CoreM W L (Value L) := do
  pure (.leaf (ops.imm (.macroContext (← cfS ops "MacroContext" "macrocall" macrocall))))
/-- The call `MacroContext(macrocall)`. -/
def MacroContext (macrocall : Value L) : CoreM W L (Value L) := do
  if ← fieldTypesMatch ops "MacroContext" [("macrocall", macrocall)] then
    MacroContext_new ops macrocall
  else MacroContext_new ops (← convertArg ops "MacroContext" "macrocall" macrocall)

/--
Julia source: base/syntax.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A default context corresponding to no expansion
function SyntaxContext(mod::Module, edition::Tuple{Int, Int})
    SyntaxContext(ScopeLayer(mod, nothing), nothing, edition, false)
end

```
-/
def SyntaxContext2 (mod edition : Value L) : CoreM W L (Value L) := do
  SyntaxContext4 ops (← ScopeLayer ops mod (nothingS ops)) (nothingS ops) edition (bS ops false)

/--
Julia source: base/syntax.jl:74-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const JL_NEW_EDITION = (1, 15)
const JL_OLD_EDITION = (1, 14)

```
-/
def JL_NEW_EDITION : Value L := .leaf (ops.tuple [iV ops 1, iV ops 15])
def JL_OLD_EDITION : Value L := .leaf (ops.tuple [iV ops 1, iV ops 14])

/--
Julia source: base/syntax.jl:77-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Syntax(head::Symbol, children, @nospecialize(value), source, context)
    Syntax(head, children, value, source, context,
               nothing, nothing, nothing, UInt16(0))
end

```
-/
def Syntax5 (head : Sym) (children value source context : Value L) : CoreM W L (Value L) := do
  let flags ← JuliaLean.base.boot.UInt16_ ops.toCoreOps (.int .i64 (JInt.lit .i64 0))
  Syntax9 ops (.symbol head) children value source context (nothingS ops) (nothingS ops)
    (nothingS ops) (.leaf (ops.int flags))

/--
Julia source: base/syntax.jl:82-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
head(ex::Syntax) = ex.head

```
-/
def head (ex : Value L) : CoreM W L (Value L) := getprop ops ex "head"

/--
Julia source: base/syntax.jl:84-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_leaf(ex::Syntax) = ex.children === nothing

```
-/
def is_leaf (ex : Value L) : CoreM W L Bool := do
  pure (isNothing ops (← getprop ops ex "children"))

/--
Julia source: base/syntax.jl:86-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function numchildren(ex::Syntax)
    cs = ex.children
    isnothing(cs) ? 0 : length(cs)
end

```
-/
def numchildren (ex : Value L) : CoreM W L (Value L) := do
  let cs ← getprop ops ex "children"
  if isNothing ops cs then pure (iV ops 0) else callB ops "length" [cs]

/--
Julia source: base/syntax.jl:91-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# TODO: Better to make this an error, since it can cause nodes that were
# intended to be leaves `Syntax(head, children(old), ...)` to be non-leaves
const NO_CHILDREN = Syntax[]

```
-/
-- The vector bound to the constant at load time, `Syntax[]`.
def NO_CHILDREN_init : CoreM W L (Value L) := callB ops "getindex" [bV ops "Syntax"]
/-- The value of the constant `NO_CHILDREN` read by the methods below. -/
def NO_CHILDREN : Value L := bV ops "NO_CHILDREN"

/--
Julia source: base/syntax.jl:95-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function children(ex::Syntax)
    cs = ex.children
    cs === nothing ? NO_CHILDREN : cs
end

```
-/
def children (ex : Value L) : CoreM W L (Value L) := do
  let cs ← getprop ops ex "children"
  pure (if isNothing ops cs then NO_CHILDREN ops else cs)

/--
Julia source: base/syntax.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.getindex(ex::Syntax, i::Integer)
    ex.children[i]
end

```
-/
def getindex_Integer (ex i : Value L) : CoreM W L (Value L) := do
  callB ops "getindex" [← getprop ops ex "children", i]

/--
Julia source: base/syntax.jl:104-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.getindex(ex::Syntax, r::UnitRange)
    @view ex.children[r]
end

```
-/
def getindex_UnitRange (ex r : Value L) : CoreM W L (Value L) := do
  callB ops "view" [← getprop ops ex "children", r]

/--
Julia source: base/syntax.jl:108-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.firstindex(::Syntax) = 1
Base.lastindex(ex::Syntax) = numchildren(ex)

```
-/
def firstindex (_ex : Value L) : Value L := iV ops 1
def lastindex (ex : Value L) : CoreM W L (Value L) := numchildren ops ex

/--
Julia source: base/syntax.jl:111-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#-------------------------------------------------------------------------------
# AST creation utilities

# fallback printing.  `invokelatest` so new `show` methods don't invalidate callers
function node_string(ex::Syntax, depth=2)
    out = "(head="*string(head(ex))
    for n in sort!(collect(fieldnames(typeof(ex))))
        val = getproperty(ex, n)
        if !isnothing(val) && n !== :head
            val_str = if val isa Syntax && depth > 1
                node_string(val, depth-1)
            elseif isbits(val) || val isa
                Union{AbstractString, Symbol, Module, LineNumberNode}
                invokelatest(repr, val)::String
            else
                invokelatest(repr, typeof(val))::String
            end
            out *= ", "*string(n)*"="*val_str
        end
    end
    if is_leaf(ex)
        out *= ", leaf"
    elseif depth > 1
        out *= ", children=["
        for c in children(ex)
            out *= "\n"*node_string(c, depth-1)
        end
        out *= "]"
    end
    out *= ")"
    return out
end
```
-/
-- `val isa Union{AbstractString, Symbol, Module, LineNumberNode}`.
def isPrintable (val : Value L) : Bool :=
  ops.isa val (bV ops "AbstractString") || ops.isa val (bV ops "Symbol") ||
    ops.isa val (bV ops "Module") || ops.isa val (bV ops "LineNumberNode")

def node_string (ex depth : Value L) : CoreM W L (Value L) := do
  let mut out ← callB ops "*" [sV ops "(head=", ← callB ops "string" [← head ops ex]]
  let names ← ops.elems (← callB ops "sort!"
    [← callB ops "collect" [← callB ops "fieldnames" [.leaf (ops.typeOf ex)]]])
  for n in names do
    let val ← callB ops "getproperty" [ex, n]
    if !isNothing ops val && !isSym n "head" then
      let deep ← if isSyntax ops val then callB ops ">" [depth, iV ops 1] else pure (bS ops false)
      let val_str ←
        if isSyntax ops val && ops.same deep (bS ops true) then
          node_string val (← callB ops "-" [depth, iV ops 1])
        else
          let bits ← callB ops "isbits" [val]
          if ops.same bits (bS ops true) || isPrintable ops val then do
            JuliaLean.base.boot.typeassert ops.toCoreOps
              (← callB ops "invokelatest" [bV ops "repr", val]) (bV ops "String")
          else do
            JuliaLean.base.boot.typeassert ops.toCoreOps
              (← callB ops "invokelatest" [bV ops "repr", .leaf (ops.typeOf val)]) (bV ops "String")
      out ← callB ops "*" [out, ← callB ops "*" [sV ops ", ", ← callB ops "string" [n], sV ops "=", val_str]]
  if ← is_leaf ops ex then
    out ← callB ops "*" [out, sV ops ", leaf"]
  else if ops.same (← callB ops ">" [depth, iV ops 1]) (bS ops true) then
    out ← callB ops "*" [out, sV ops ", children=["]
    for c in ← ops.elems (← children ops ex) do
      out ← callB ops "*" [out, ← callB ops "*" [sV ops "\n", ← node_string c (← callB ops "-" [depth, iV ops 1])]]
    out ← callB ops "*" [out, sV ops "]"]
  out ← callB ops "*" [out, sV ops ")"]
  return out
partial_fixpoint

def node_string1 (ex : Value L) : CoreM W L (Value L) := node_string ops ex (iV ops 2)

/--
Julia source: base/syntax.jl:160-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _assert_syntax_node(st::Syntax)
    h = head(st)
    if is_leaf(st)
        if h === :globalref && st.mod === nothing
            return (st, "leaf globalref requires module in .mod")
        end
        (needs_val, valtype) =
            h === :identifier ? (true, String) :
            h === :value ? (true, Any) :
            h === :core ? (true, String) :
            h === :top ? (true, String) :
            h === :symbol ? (true, String) :
            h === :globalref ? (true, String) :
            h === :placeholder ? (false, Any) :
            h === :bindingid ? (true, Int) :
            h === :label ? (true, Int) :
            h === :symboliclabel ? (true, String) :
            h === :symbolicgoto ? (true, String) :
            h === :slot ? (true, Int) :
            h === :static_parameter ? (true, Int) :
            h === :ssavalue ? (true, Int) :
            h === :nothing ? (false, Any) :
            h === :tombstone ? (false, Any) :
            h === :error ? (false, Any) :
            h === :sourcelocation ? (false, Any) :
            h === :latestworld ? (false, Any) :
            h === :latestworld_if_toplevel ? (false, Any) :
            h === :strmacroname ? (true, String) :
            h === :cmdmacroname ? (true, String) :
            h === :lambdabindings ? (true, Any) : # JL.LambdaBindings
            h === :slots ? (true, Vector) : # Vector{JL.Slot}
            h === :version ? (true, VersionNumber) :
            # too lenient, but the green tree includes unspecified leaf nodes.
            # we hit this when JuliaSyntax.is_trivia(node) with some operators.
            st.source isa SourceRef ? (false, Any) :
                (return (st, "unrecognized leaf $(h)"))
        if needs_val && !(st.value isa valtype)
            return (st, LazyString("needs value ::", valtype))
        end
    else
        # Note some kinds can show up as non-leaves too (mostly from Expr)
        if h in (:identifier, :value, :placeholder, :bindingid, :label, :symbol,
                 :nothing, :tombstone, :sourcelocation,
                 :lambdabindings, :slots)
            return (st, "Found leaf-only kind with children")
        end
    end
    nothing
end

```
-/
def leafValueTypes : List (String × Bool × String) :=
  [("identifier", true, "String"), ("value", true, "Any"), ("core", true, "String"),
   ("top", true, "String"), ("symbol", true, "String"), ("globalref", true, "String"),
   ("placeholder", false, "Any"), ("bindingid", true, "Int"), ("label", true, "Int"),
   ("symboliclabel", true, "String"), ("symbolicgoto", true, "String"), ("slot", true, "Int"),
   ("static_parameter", true, "Int"), ("ssavalue", true, "Int"), ("nothing", false, "Any"),
   ("tombstone", false, "Any"), ("error", false, "Any"), ("sourcelocation", false, "Any"),
   ("latestworld", false, "Any"), ("latestworld_if_toplevel", false, "Any"),
   ("strmacroname", true, "String"), ("cmdmacroname", true, "String"),
   ("lambdabindings", true, "Any"), ("slots", true, "Vector"), ("version", true, "VersionNumber")]

def leafOnlyKinds : List String :=
  ["identifier", "value", "placeholder", "bindingid", "label", "symbol", "nothing", "tombstone",
   "sourcelocation", "lambdabindings", "slots"]

def _assert_syntax_node (st : Value L) : CoreM W L (Value L) := do
  let h ← head ops st
  if ← is_leaf ops st then
    if isSym h "globalref" && isNothing ops (← getprop ops st "mod") then
      return tup ops [st, sV ops "leaf globalref requires module in .mod"]
    let entry := leafValueTypes.find? (fun e => isSym h e.1)
    let (needs_val, valtype) ← match entry with
      | some (_, nv, T) => pure (nv, T)
      | none =>
        if isSourceRef ops (← getprop ops st "source") then pure (false, "Any")
        else return tup ops [st, ← callB ops "string" [sV ops "unrecognized leaf ", h]]
    if needs_val && !ops.isa (← getprop ops st "value") (bV ops valtype) then
      return tup ops [st, ← callB ops "LazyString" [sV ops "needs value ::", bV ops valtype]]
  else
    if leafOnlyKinds.any (isSym h) then
      return tup ops [st, sV ops "Found leaf-only kind with children"]
  return nothingS ops

/--
Julia source: base/syntax.jl:210-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Cyclic references are still possible with children (as they are stored in a
# mutable vector), but other cycles (e.g. source) should be impossible by
# construction
function _assert_syntax(st::Syntax, parents::Vector{Syntax})
    if st in parents
        err = "cycle detected: ["
        for p in parents
            err *= "\n" * node_string(p)
        end
        return (st, err*"]")
    end
    vr = _assert_syntax_node(st)
    isnothing(vr) || return vr

    push!(parents, st)
    is_leaf(st) || for c in children(st)
        vr = _assert_syntax(c, parents)
        isnothing(vr) || return vr
    end
    pop!(parents)
    nothing
end

```
-/
def _assert_syntax (st parents : Value L) : CoreM W L (Value L) := do
  if ← cond ops (← callB ops "in" [st, parents]) then
    let mut err := sV ops "cycle detected: ["
    for p in ← ops.elems parents do
      err ← callB ops "*" [err, ← callB ops "*" [sV ops "\n", ← node_string1 ops p]]
    return tup ops [st, ← callB ops "*" [err, sV ops "]"]]
  let vr ← _assert_syntax_node ops st
  if !isNothing ops vr then return vr
  let _ ← callB ops "push!" [parents, st]
  if !(← is_leaf ops st) then
    for c in ← ops.elems (← children ops st) do
      let vr ← _assert_syntax c parents
      if !isNothing ops vr then return vr
  let _ ← callB ops "pop!" [parents]
  return nothingS ops
partial_fixpoint

/--
Julia source: base/syntax.jl:143-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Tree invariants assumed everywhere, including `show`, so fallback printing
# should be used on failure.  (These checks really belong in the type system.)
# Failure should only be possible working on internals.
function assert_syntax(st::Syntax, recursive=true)
    vr = recursive ? _assert_syntax(st, Syntax[]) :
        _assert_syntax_node(st)
    if vr !== nothing
        err_st, err = vr
        msg = string("assert_syntax failed: ", node_string(st),
                     "\n  failing node: ", node_string(err_st),
                     "\n  reason: ", err)
        error(msg)
    end
    nothing
end

```
-/
def assert_syntax (st recursive : Value L) : CoreM W L (Value L) := do
  let vr ← if ← cond ops recursive then do
      _assert_syntax ops st (← callB ops "getindex" [bV ops "Syntax"])
    else _assert_syntax_node ops st
  if !isNothing ops vr then
    let (err_st, err) ← destructure2 ops vr
    let msg ← callB ops "string" [sV ops "assert_syntax failed: ", ← node_string1 ops st,
      sV ops "\n  failing node: ", ← node_string1 ops err_st, sV ops "\n  reason: ", err]
    let _ ← callB ops "error" [msg]
  return nothingS ops
def assert_syntax1 (st : Value L) : CoreM W L (Value L) := assert_syntax ops st (bS ops true)

/--
Julia source: base/syntax.jl:233-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _DEFAULT_NODE = Syntax(
    :none, nothing, nothing, LineNumberNode(0), SyntaxContext(Core, (0, 0)))

```
-/
-- The node bound to the constant at load time; the methods read the constant itself.
def _DEFAULT_NODE_init : CoreM W L (Value L) := do
  Syntax5 ops "none" (nothingS ops) (nothingS ops)
    (JuliaLean.base.boot.LineNumberNode1 ops.toCoreOps (JInt.lit .i64 0))
    (← SyntaxContext2 ops (.leaf (ops.core "Core")) (tup ops [iV ops 0, iV ops 0]))
/-- The value of the constant `_DEFAULT_NODE`. -/
def _DEFAULT_NODE : Value L := bV ops "_DEFAULT_NODE"

/--
Julia source: base/syntax.jl:236-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const DEBUG_LOWERING = true

```
-/
def DEBUG_LOWERING : Bool := true

/--
Julia source: base/syntax.jl:238-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @mknode(old; attr=val...)

Create a node `new` that is an immutable update of `old`, but setting `old` as
its provenance, and setting jl_source to macrocall's location.  `attrs` may
override `old`'s fields (so if `old` is not provided, some attrs are required.)

This is the main operation used by syntax transformations in lowering.
"""
macro mknode(attrs, old)
    Base.remove_linenums!(old)
    Base.remove_linenums!(attrs)
    old_gs = gensym()
    if !(isnothing(attrs) || attrs isa Expr && Meta.isexpr(attrs, :parameters))
        throw(ArgumentError("usage: @mknode(old; attr=val...)"))
    end
    out_args = Vector(undef, fieldcount(Syntax))
    for (i, n) in enumerate(fieldnames(Syntax))
        out_args[i] = (DEBUG_LOWERING && n === :jl_source) ? __source__ :
            n === :source ? old_gs :
            Expr(:(.), old_gs, QuoteNode(n))
    end
    seen_attrs = Set{Symbol}()
    attrs isa Expr && for a in attrs.args
        (aname, aval) = if Meta.isexpr(a, :(kw), 2) && a.args[1] isa Symbol
            (a.args[1]::Symbol, a.args[2])
        elseif a isa Symbol
            (a, a)
        else
            throw(ArgumentError("usage: @mknode(old; attr=val...)"))
        end
        aname in seen_attrs && throw(ArgumentError("duplicate attr provided $__source__"))
        push!(seen_attrs, aname)
        out_args[Base.fieldindex(Syntax, aname)] = aval
    end
    old === _DEFAULT_NODE && !((:head, :source, :context) ⊆ seen_attrs) &&
        throw(ArgumentError("brand-new node from @mknode requires more attrs $__source__"))

    out = Expr(:let,
               Expr(:block, Expr(:(=), old_gs, old)),
               Expr(:block, Expr(:call, Syntax, out_args...)))
    DEBUG_LOWERING && (out.args[end] = Expr(:call, _debug_check_attrs, out.args[end]))
    esc(out)
end
```
-/
-- `source` is `__source__`; `attrs` and `old` are the macro arguments.
def macro_mknode2 (source attrs old : Value L) : CoreM W L (Value L) := do
  let old := JuliaLean.base.expr.remove_linenums! ops.codeInfoNoLines old
  let attrs := JuliaLean.base.expr.remove_linenums! ops.codeInfoNoLines attrs
  let old_gs ← callB ops "gensym" []
  if !(isNothing ops attrs || JuliaLean.base.expr.isexpr attrs "parameters") then
    throwArg ops (sV ops "usage: @mknode(old; attr=val...)")
  let mut out_args : List (Value L) := syntaxFields.map fun n =>
    if DEBUG_LOWERING && n == "jl_source" then source
    else if n == "source" then old_gs
    else .expr "." [old_gs, .quoteNode (.symbol n)]
  let mut seen_attrs : List Sym := []
  match attrs with
  | .expr _ args =>
    for a in args do
      let (aname, aval) ← match a with
        | .expr "kw" [.symbol n, v] => pure (n, v)
        | .symbol n => pure (n, a)
        | _ => throwArg ops (sV ops "usage: @mknode(old; attr=val...)")
      if seen_attrs.contains aname then
        throwArg ops (← callB ops "string" [sV ops "duplicate attr provided ", source])
      seen_attrs := seen_attrs ++ [aname]
      match syntaxFields.idxOf? aname with
      | some i => out_args := out_args.set i aval
      | none => let _ ← callB ops "fieldindex" [bV ops "Syntax", .symbol aname]
  | _ => pure ()
  if ops.same old (_DEFAULT_NODE ops) &&
      !(["head", "source", "context"].all seen_attrs.contains) then
    throwArg ops (← callB ops "string"
      [sV ops "brand-new node from @mknode requires more attrs ", source])
  let call : Value L := .expr "call" (bV ops "Syntax" :: out_args)
  let out : Value L := .expr "let" [.expr "block" [.expr "=" [old_gs, old]],
    if DEBUG_LOWERING then .expr "call" [bV ops "_debug_check_attrs", .expr "block" [call]]
    else .expr "block" [call]]
  pure (.expr "escape" [out])


/--
Julia source: base/syntax.jl:282-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro mknode(x)
    (old, attrs) = Meta.isexpr(x, :parameters) ? (_DEFAULT_NODE, x) : (x, nothing)
    esc(Expr(:macrocall, var"@mknode", __source__, attrs, old))
end

function _debug_check_attrs(x)
    assert_syntax(x, false)
    x
end

```
-/
def _debug_check_attrs (x : Value L) : CoreM W L (Value L) := do
  let _ ← assert_syntax ops x (bS ops false)
  pure x

/-- `@mknode(x)`. -/
def macro_mknode1 (source x : Value L) : Value L :=
  let (old, attrs) := if JuliaLean.base.expr.isexpr x "parameters" then (_DEFAULT_NODE ops, x)
    else (x, nothingS ops)
  .expr "escape" [.expr "macrocall" [bV ops "@mknode", source, attrs, old]]

/-- The call of an `@mknode` expansion: `_debug_check_attrs(Syntax(fields...))`, with
`jl_source` `nothing` unless given. -/
def mknode (head children value source context jl_source meta_ mod syntax_flags : Value L) :
    CoreM W L (Value L) := do
  _debug_check_attrs ops (← Syntax9 ops head children value source context jl_source meta_ mod
    syntax_flags)

/-- `@mknode(old; attrs...)` at a use in a method: the call its expansion makes. -/
def mknodeFrom (old : Value L) (attrs : List (Sym × Value L)) : CoreM W L (Value L) := do
  let fld := mknodeField ops old attrs
  mknode ops (← fld "head") (← fld "children") (← fld "value") (← fld "source") (← fld "context")
    (← fld "jl_source") (← fld "meta") (← fld "mod") (← fld "syntax_flags")

/--
Julia source: base/syntax.jl:292-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.setproperty!(ex::Syntax, name::Symbol, @nospecialize(val)) =
    error("Syntax: this can't be mutated")

```
-/
def setproperty! (_ex _name _val : Value L) : CoreM W L (Value L) :=
  callB ops "error" [sV ops "Syntax: this can't be mutated"]

/--
Julia source: base/syntax.jl:295-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This function should be allocation-free if no children were changed
function mapchildren(f::Function, ex::Syntax)
    if is_leaf(ex)
        return ex
    end
    orig_children = children(ex)
    cs = nothing
    for (i,e) in enumerate(orig_children)
        newchild = f(e)::Syntax
        if isnothing(cs)
            if newchild == e
                continue
            else
                cs = Vector{Syntax}(undef, length(orig_children))
                copyto!(cs, orig_children[1:i-1])
            end
        end
        cs[i] = newchild
    end
    if isnothing(cs)
        return ex
    end
    cs::Vector{Syntax}
    ex2 = @mknode(ex; children=cs)
    return ex2
end

```
-/
-- `f` is the function, given by its call.
-- The `for` loop over `enumerate(orig_children)`: `cs` and the index `i` of the last element.
def mapchildren_loop (f : Value L → CoreM W L (Value L)) (orig_children : Value L) :
    Value L → Int → List (Value L) → CoreM W L (Value L)
  | cs, _, [] => pure cs
  | cs, i, e :: es => do
    let i := i + 1
    let v ← f e
    let newchild ← assertKind ops (isSyntax ops v) v "Syntax"
    if isNothing ops cs then
      if ← cond ops (← callB ops "==" [newchild, e]) then
        mapchildren_loop f orig_children cs i es
      else
        let cs ← ops.call (← ops.applyType (bV ops "Vector") [bV ops "Syntax"])
          [.leaf (ops.core "undef"), ← callB ops "length" [orig_children]]
        let _ ← callB ops "copyto!" [cs, ← callB ops "getindex"
          [orig_children, ← callB ops ":" [iV ops 1, ← callB ops "-" [iV ops i, iV ops 1]]]]
        let _ ← callB ops "setindex!" [cs, newchild, iV ops i]
        mapchildren_loop f orig_children cs i es
    else
      let _ ← callB ops "setindex!" [cs, newchild, iV ops i]
      mapchildren_loop f orig_children cs i es

def mapchildren (f : Value L → CoreM W L (Value L)) (ex : Value L) : CoreM W L (Value L) := do
  if ← is_leaf ops ex then
    return ex
  let orig_children ← children ops ex
  let cs ← mapchildren_loop ops f orig_children (nothingS ops) 0 (← ops.elems orig_children)
  if isNothing ops cs then
    return ex
  let cs2 ← JuliaLean.base.boot.typeassert ops.toCoreOps cs
    (← ops.applyType (bV ops "Vector") [bV ops "Syntax"])
  mknodeFrom ops ex [("children", cs2)]

/-- Monotonicity of a `CoreM` body built from binds and conditionals, given tactics `hyp` for the
recursive or argument calls. -/
macro "core_mono" hyp:tacticSeq : tactic => `(tactic|
  repeat (any_goals (first
    | exact Lean.Order.monotone_const _
    | ($hyp)
    | (apply Lean.Order.monotone_bind
       case' hmono₂ => apply Lean.Order.monotone_of_monotone_apply; intro _)
    | apply Lean.Order.monotone_ite)))

theorem monotone_mapchildren_loop {γ : Sort _} [Lean.Order.PartialOrder γ]
    (f : γ → Value L → CoreM W L (Value L)) (hf : Lean.Order.monotone f) (orig_children : Value L) :
    ∀ (es : List (Value L)) (cs : Value L) (i : Int),
      Lean.Order.monotone (fun x => mapchildren_loop ops (f x) orig_children cs i es) := by
  intro es
  induction es with
  | nil => intro cs i; exact Lean.Order.monotone_const _
  | cons e es ih =>
    intro cs i
    simp only [mapchildren_loop]
    core_mono (first | exact ih _ _ | (apply Lean.Order.monotone_apply; exact hf))

@[partial_fixpoint_monotone]
theorem monotone_mapchildren {γ : Sort _} [Lean.Order.PartialOrder γ]
    (f : γ → Value L → CoreM W L (Value L)) (hf : Lean.Order.monotone f) (ex : Value L) :
    Lean.Order.monotone (fun x => mapchildren ops (f x) ex) := by
  unfold mapchildren
  core_mono (exact monotone_mapchildren_loop ops f hf _ _ _ _)

-- Reason: A section comment and a string of notes on provenance, which defines no method.
-- UNTRANSLATED
-- Source: base/syntax.jl:471-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #-------------------------------------------------------------------------------
-- # Provenance
-- 
-- """
-- Provenance notes: A Syntax `st` has `.source` equal to one of:
-- - Syntax (of the Syntax `st` was transformed from)
-- - a reference to source text (either SourceRef or LineNumberNode).
-- 
-- Let "textref" refer to a Syntax with non-Syntax `.source`.  Every Syntax
-- is either a textref or has one at the end of its `.source` chain.
-- 
-- All invariants noted in this section are awaiting the design of the "new macro"
-- API.  As of writing this, the user has more freedom than they should have.
-- """
-- 
-- /Source

/--
Julia source: base/syntax.jl:486-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
Returns [st.source, st.source.source, ..., textref]
"""
function provenance(st::Syntax)
    prov = Syntax[]
    s = st.source
    while s isa Syntax
        push!(prov, s)
        s = s.source
    end
    return prov
end

```
-/
def provenance_loop (s prov : Value L) : CoreM W L (Value L) := do
  if isSyntax ops s then
    let _ ← callB ops "push!" [prov, s]
    provenance_loop (← getprop ops s "source") prov
  else pure prov
partial_fixpoint

def provenance (st : Value L) : CoreM W L (Value L) := do
  let prov ← callB ops "getindex" [bV ops "Syntax"]
  provenance_loop ops (← getprop ops st "source") prov

/--
Julia source: base/syntax.jl:499-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"`provenance(st)[1]`, or `st` if that's empty"
function prov(st::Syntax)
    source = st.source
    source isa Syntax ? source : st
end

```
-/
def prov (st : Value L) : CoreM W L (Value L) := do
  let source ← getprop ops st "source"
  pure (if isSyntax ops source then source else st)

/--
Julia source: base/syntax.jl:505-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"textref of st (possibly == st)"
function prov_end(st::Syntax)
    out = st
    while out.source isa Syntax
        out = prov(out)
    end
    return out
end

```
-/
def prov_end_loop (out : Value L) : CoreM W L (Value L) := do
  if isSyntax ops (← getprop ops out "source") then prov_end_loop (← prov ops out) else pure out
partial_fixpoint

def prov_end (st : Value L) : CoreM W L (Value L) := prov_end_loop ops st

/--
Julia source: base/syntax.jl:514-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"`st`'s textref's `.source`, ignoring all expansions"
function sourceref(st::Syntax)
    src = prov_end(st)
    src.source::Union{LineNumberNode, SourceRef}
end

```
-/
def sourceref (st : Value L) : CoreM W L (Value L) := do
  let src ← prov_end ops st
  let T ← ops.applyType (.leaf (ops.core "Union")) [bV ops "LineNumberNode", bV ops "SourceRef"]
  JuliaLean.base.boot.typeassert ops.toCoreOps (← getprop ops src "source") T

/--
Julia source: base/syntax.jl:520-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"The last macro expansion `st` was involved in, or nothing"
function macro_prov(st::Syntax)
    msrc = st.context.unexpanded
    isnothing(msrc) ? nothing : msrc::typeof(st)
end

```
-/
def macro_prov (st : Value L) : CoreM W L (Value L) := do
  let msrc ← getprop ops (← getprop ops st "context") "unexpanded"
  if isNothing ops msrc then pure (nothingS ops)
  else JuliaLean.base.boot.typeassert ops.toCoreOps msrc (.leaf (ops.typeOf st))

/--
Julia source: base/syntax.jl:526-534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"The first macro expansion `st` was involved in (chronologically), or nothing"
function macro_prov_end(st::Syntax)
    lastmp = mp = macro_prov(st)
    while !isnothing(mp)
        lastmp, mp = mp, macro_prov(mp)
    end
    return lastmp
end

```
-/
def macro_prov_end_loop (lastmp mp : Value L) : CoreM W L (Value L) := do
  if isNothing ops mp then pure lastmp
  else macro_prov_end_loop mp (← macro_prov ops mp)
partial_fixpoint

def macro_prov_end (st : Value L) : CoreM W L (Value L) := do
  let mp ← macro_prov ops st
  macro_prov_end_loop ops mp mp

/--
Julia source: base/syntax.jl:535-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"The top-level location of `st`"
function unexpanded_sourceref(st::Syntax)
    mp = macro_prov_end(st)
    isnothing(mp) ? sourceref(st) : sourceref(mp)
end

```
-/
def unexpanded_sourceref (st : Value L) : CoreM W L (Value L) := do
  let mp ← macro_prov_end ops st
  if isNothing ops mp then sourceref ops st else sourceref ops mp

/--
Julia source: base/syntax.jl:560-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Only recurse on the first macro source in any source chain
function _flattened_provenance(st::Syntax, out)
    msrc = macro_prov(st)
    # macro source === source means `st` is from the `msrc` macro body
    !isnothing(msrc) && msrc != prov(st) &&
        _flattened_provenance(msrc, out)
    push!(out, prov_end(st))
    out
end

```
-/
def _flattened_provenance (st out : Value L) : CoreM W L (Value L) := do
  let msrc ← macro_prov ops st
  if !isNothing ops msrc then
    if ← cond ops (← callB ops "!=" [msrc, ← prov ops st]) then
      let _ ← _flattened_provenance msrc out
  let _ ← callB ops "push!" [out, ← prov_end ops st]
  pure out
partial_fixpoint

/--
Julia source: base/syntax.jl:541-559 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
A list of textrefs associated with `st`.  The number of returned trees should
equal one plus the number of macro expansions `st` "went through":

- For new macros, this is the number of macro expansions `st` was both an input
  and output of, so if `st` was created in a macro body, `flattened_provenance`
  returns a list of length 1.

- For old macros, we can't determine whether expanded syntax is from the
  macrocall args or macro body (it will have LineNumberNode .source), so all
  expanded syntax counts as having "went through" the macrocall.

The resulting list should be in the order
`[outermost_macrocall, innermost_macrocall, ..., expression_textref]`.
"""
function flattened_provenance(st::Syntax)
    _flattened_provenance(st, Syntax[])
end

```
-/
def flattened_provenance (st : Value L) : CoreM W L (Value L) := do
  _flattened_provenance ops st (← callB ops "getindex" [bV ops "Syntax"])

/--
Julia source: base/syntax.jl:570-576 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# TODO: We want a bigger API (probably like Compiler.source_location),
# but avoid duplication with JuliaSyntax for now
function filename(s::Syntax)
    sr = sourceref(s)
    n = sr isa LineNumberNode ? sr.file : sr.code.filename
    n === nothing ? :var"" : n
end
```
-/
def filename (s : Value L) : CoreM W L (Value L) := do
  let sr ← sourceref ops s
  let n ← if isLnn sr then getprop ops sr "file"
    else do getprop ops (← getprop ops sr "code") "filename"
  pure (if isNothing ops n then .symbol "" else n)

/--
Julia source: base/syntax.jl:577-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function source_line(src::SourceCode, b)
    src.first_line - 1 +
        searchsortedlast(src.line_starts, b - src.byte_offset)
end
```
-/
def source_line (src b : Value L) : CoreM W L (Value L) := do
  let base ← callB ops "-" [← getprop ops src "first_line", iV ops 1]
  callB ops "+" [base, ← callB ops "searchsortedlast"
    [← getprop ops src "line_starts", ← callB ops "-" [b, ← getprop ops src "byte_offset"]]]

/--
Julia source: base/syntax.jl:581-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
first_linenode(s::Syntax) = first_linenode(sourceref(s))
first_linenode(sr::SourceRef) =
    LineNumberNode(source_line(sr.code, sr.first_byte), sr.code.filename)
first_linenode(lnn::LineNumberNode) = lnn

```
-/
def first_linenode_Syntax (s : Value L) : CoreM W L (Value L) := do
  callB ops "first_linenode" [← sourceref ops s]
def first_linenode_SourceRef (sr : Value L) : CoreM W L (Value L) := do
  let code ← getprop ops sr "code"
  callB ops "LineNumberNode"
    [← source_line ops code (← getprop ops sr "first_byte"), ← getprop ops code "filename"]
def first_linenode_LineNumberNode (lnn : Value L) : Value L := lnn

-- Reason: A section comment.
-- UNTRANSLATED
-- Source: base/syntax.jl:322-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #-------------------------------------------------------------------------------
-- # Context and layers
-- 
-- /Source

/--
Julia source: base/syntax.jl:325-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_base_layer(sc::SyntaxContext) = (sc.layer::ScopeLayer).escaped === nothing

```
-/
-- `x::ScopeLayer`.
def asLayer (x : Value L) : CoreM W L (Value L) := assertKind ops (isLayer ops x) x "ScopeLayer"

def is_base_layer (sc : Value L) : CoreM W L Bool := do
  pure (isNothing ops (← getprop ops (← asLayer ops (← getprop ops sc "layer")) "escaped"))

/--
Julia source: base/syntax.jl:327-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The scope corresponding to no macro expansion.  Use with caution: macros may
# expand to top-level forms, so "base layer" !== "this top-level thunk's
# pre-expansion context" (usually ctx.syntax_context).  Throws with no layer.
function base_layer(sc::SyntaxContext)
    l = sc.layer::ScopeLayer
    while l.escaped !== nothing
        l = l.escaped
    end
    return l
end

```
-/
def base_layer_loop (l : Value L) : CoreM W L (Value L) := do
  let e ← getprop ops l "escaped"
  if isNothing ops e then pure l else base_layer_loop e
partial_fixpoint

def base_layer (sc : Value L) : CoreM W L (Value L) := do
  base_layer_loop ops (← asLayer ops (← getprop ops sc "layer"))

/--
Julia source: base/syntax.jl:338-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function escape_layer(sc::SyntaxContext, recursive::Bool)
    l2 = recursive ? base_layer(sc) : (sc.layer::ScopeLayer).escaped
    SyntaxContext(l2, sc.unexpanded, sc.edition, sc.internal)
end

```
-/
def escape_layer (sc recursive : Value L) : CoreM W L (Value L) := do
  let l2 ← if ← cond ops recursive then base_layer ops sc
    else do getprop ops (← asLayer ops (← getprop ops sc "layer")) "escaped"
  callB ops "SyntaxContext" [l2, ← getprop ops sc "unexpanded", ← getprop ops sc "edition",
    ← getprop ops sc "internal"]

/--
Julia source: base/syntax.jl:343-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
syntax_module(sc::SyntaxContext) = (sc.layer::ScopeLayer).mod
function syntax_module(st::Syntax)
    st_mod = st.mod
    st_mod === nothing || return st_mod::Module
    syntax_module(st.context)
end
syntax_name(s::Syntax) = s.value::String

```
-/
def syntax_module_SyntaxContext (sc : Value L) : CoreM W L (Value L) := do
  getprop ops (← asLayer ops (← getprop ops sc "layer")) "mod"
def syntax_module_Syntax (st : Value L) : CoreM W L (Value L) := do
  let st_mod ← getprop ops st "mod"
  if !isNothing ops st_mod then
    return ← JuliaLean.base.boot.typeassert ops.toCoreOps st_mod (bV ops "Module")
  callB ops "syntax_module" [← getprop ops st "context"]
def syntax_name (s : Value L) : CoreM W L (Value L) := do
  JuliaLean.base.boot.typeassert ops.toCoreOps (← getprop ops s "value") (bV ops "String")

/--
Julia source: base/syntax.jl:351-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
edition(st::Syntax) = st.context.edition
edition(@nospecialize(st)) = JL_OLD_EDITION

```
-/
def edition_Syntax (st : Value L) : CoreM W L (Value L) := do
  getprop ops (← getprop ops st "context") "edition"
def edition_Any (_st : Value L) : Value L := JL_OLD_EDITION ops

/--
Julia source: base/syntax.jl:354-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_with_context(st, sc) =
    @mknode(st; context=sc, source=st.source, jl_source=st.jl_source)

```
-/
def _with_context (st sc : Value L) : CoreM W L (Value L) := do
  let source ← getprop ops st "source"
  let jl_source ← getprop ops st "jl_source"
  mknodeFrom ops st [("context", sc), ("source", source), ("jl_source", jl_source)]

/--
Julia source: base/syntax.jl:357-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Unconditional; tramples existing scope, and includes quoted forms.  Only
# changes layer where it needs changing.
function adopt_scope(sc_in::SyntaxContext, st::Syntax, unexpanded_in, scmap)
    st_sc = st.context
    sc2 = get(scmap, st_sc, nothing)
    if isnothing(sc2)
        sc2 = scmap[st_sc] = st_sc.layer === sc_in.layer ? st_sc :
            SyntaxContext(
                sc_in.layer,
                # If the layer is foreign, update macro provenance
                (st_sc.layer === nothing || base_layer(st_sc) !== base_layer(sc_in) ?
                    unexpanded_in : st_sc.unexpanded),
                st_sc.edition, st_sc.internal)
    end
    if is_leaf(st) || numchildren(st) == 0
        sc2 === st_sc ? st : _with_context(st, sc2)
    else
        mapchildren(c->adopt_scope(sc_in, c, unexpanded_in, scmap),
                    sc2 === st_sc ? st : _with_context(st, sc2))
    end
end
adopt_scope(reference::Syntax, st::Syntax) =
    adopt_scope(reference.context, st, st.context.unexpanded,
                Dict{SyntaxContext, SyntaxContext}())
# MacroContext methods are for use in new-macro bodies.  These extend the
# provenance tree as JuliaLowering expects.
adopt_scope(ctx::MacroContext, st::Syntax) =
    adopt_scope(ctx.macrocall.context, st, ctx.macrocall,
                Dict{SyntaxContext, SyntaxContext}())
adopt_scope(ctx::MacroContext, reference::Syntax, st::Syntax) =
    adopt_scope(reference.context, st, ctx.macrocall,
                Dict{SyntaxContext, SyntaxContext}())

```
-/
def adopt_scope (sc_in st unexpanded_in scmap : Value L) : CoreM W L (Value L) := do
  let st_sc ← getprop ops st "context"
  let mut sc2 ← callB ops "get" [scmap, st_sc, nothingS ops]
  if isNothing ops sc2 then
    let v ← if ops.same (← getprop ops st_sc "layer") (← getprop ops sc_in "layer") then pure st_sc
      else do
        let st_layer ← getprop ops st_sc "layer"
        let foreign ← if isNothing ops st_layer then pure true
          else do pure !(ops.same (← base_layer ops st_sc) (← base_layer ops sc_in))
        callB ops "SyntaxContext" [← getprop ops sc_in "layer",
          ← if foreign then pure unexpanded_in else getprop ops st_sc "unexpanded",
          ← getprop ops st_sc "edition", ← getprop ops st_sc "internal"]
    let _ ← callB ops "setindex!" [scmap, v, st_sc]
    sc2 := v
  let leafy ← if ← is_leaf ops st then pure true
    else do cond ops (← callB ops "==" [← numchildren ops st, iV ops 0])
  let st2 ← if ops.same sc2 st_sc then pure st else _with_context ops st sc2
  if leafy then pure st2
  else mapchildren ops (fun c => adopt_scope sc_in c unexpanded_in scmap) st2
partial_fixpoint

def adopt_scope_Syntax (reference st : Value L) : CoreM W L (Value L) := do
  adopt_scope ops (← getprop ops reference "context") st
    (← getprop ops (← getprop ops st "context") "unexpanded") (← newContextDict ops)
def adopt_scope_MacroContext (ctx st : Value L) : CoreM W L (Value L) := do
  let macrocall ← getprop ops ctx "macrocall"
  adopt_scope ops (← getprop ops macrocall "context") st macrocall (← newContextDict ops)
def adopt_scope_MacroContext3 (ctx reference st : Value L) : CoreM W L (Value L) := do
  adopt_scope ops (← getprop ops reference "context") st (← getprop ops ctx "macrocall")
    (← newContextDict ops)

/--
Julia source: base/syntax.jl:390-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill_context(st::Syntax, sc::SyntaxContext)
    mapchildren(c->fill_context(c, sc),
                sc === st.context ? st : _with_context(st, sc))
end

```
-/
def fill_context (st sc : Value L) : CoreM W L (Value L) := do
  let st2 ← if ops.same sc (← getprop ops st "context") then pure st else _with_context ops st sc
  mapchildren ops (fun c => fill_context c sc) st2
partial_fixpoint

/--
Julia source: base/syntax.jl:395-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function remove_scope(st::Syntax, scmap)
    st_sc = st.context
    sc2 = get(scmap, st.context, nothing)
    if isnothing(sc2)
        sc2 = scmap[st_sc] = st_sc.layer === nothing ? st_sc :
            SyntaxContext(nothing, st_sc.unexpanded, st_sc.edition, st_sc.internal)
    end
    if is_leaf(st) || numchildren(st) == 0
        sc2 === st_sc ? st : _with_context(st, sc2)
    else
        mapchildren(c->remove_scope(c, scmap),
                    sc2 === st_sc ? st : _with_context(st, sc2))
    end
end
remove_scope(st::Syntax) =
    remove_scope(st, Dict{SyntaxContext, SyntaxContext}())

```
-/
def remove_scope (st scmap : Value L) : CoreM W L (Value L) := do
  let st_sc ← getprop ops st "context"
  let mut sc2 ← callB ops "get" [scmap, ← getprop ops st "context", nothingS ops]
  if isNothing ops sc2 then
    let v ← if isNothing ops (← getprop ops st_sc "layer") then pure st_sc
      else do callB ops "SyntaxContext" [nothingS ops, ← getprop ops st_sc "unexpanded",
        ← getprop ops st_sc "edition", ← getprop ops st_sc "internal"]
    let _ ← callB ops "setindex!" [scmap, v, st_sc]
    sc2 := v
  let leafy ← if ← is_leaf ops st then pure true
    else do cond ops (← callB ops "==" [← numchildren ops st, iV ops 0])
  let st2 ← if ops.same sc2 st_sc then pure st else _with_context ops st sc2
  if leafy then pure st2
  else mapchildren ops (fun c => remove_scope c scmap) st2
partial_fixpoint

def remove_scope1 (st : Value L) : CoreM W L (Value L) := do
  remove_scope ops st (← newContextDict ops)

/--
Julia source: base/syntax.jl:412-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# premature optimization: If a large piece of parsed code contains macrocalls
# that embed syntax into IR, size (of the source text, but mostly the green
# tree) becomes an issue.  Ideally we would store the big stuff in a known place
# once and refer to it from all lowered code, but for now haphazardly delete
# information.  Keep sourceref, and sourceref of unexpanded if !trim_unexpanded
function _trim_provenance(st::Syntax, trim_unexpanded, scmap)
    st_sc = st.context
    sc2 = get(scmap, st_sc, nothing)
    if isnothing(sc2)
        ux = st_sc.unexpanded === nothing || trim_unexpanded ?
            nothing : _trim_provenance(st_sc.unexpanded, false, scmap)
        sc2 = scmap[st_sc] = st_sc.unexpanded === ux ? st_sc :
            SyntaxContext(st_sc.layer, ux, st_sc.edition, st_sc.internal)
    end
    if is_leaf(st) || numchildren(st) == 0
        source = sourceref(st)
        sc2 === st_sc && !(st.source isa Syntax) ? st :
            @mknode(st; context=sc2, source, jl_source=st.jl_source)
    else
        @mknode(st; context=sc2, source=sourceref(st), jl_source=st.jl_source,
                children=Syntax[_trim_provenance(
                    c, trim_unexpanded, scmap) for c in children(st)])
    end
end
trim_provenance(st::Syntax, trim_unexpanded) =
    _trim_provenance(st, trim_unexpanded, Dict{SyntaxContext, SyntaxContext}())

```
-/
-- `Syntax[f(c) for c in cs]` is `collect(Syntax, generator)`: the results in order, in a new
-- `Vector{Syntax}`.
def _trim_provenance (st trim_unexpanded scmap : Value L) : CoreM W L (Value L) := do
  let st_sc ← getprop ops st "context"
  let mut sc2 ← callB ops "get" [scmap, st_sc, nothingS ops]
  if isNothing ops sc2 then
    let unexpanded ← getprop ops st_sc "unexpanded"
    let ux ← if isNothing ops unexpanded then pure (nothingS ops)
      else do
        if ← cond ops trim_unexpanded then pure (nothingS ops)
        else _trim_provenance unexpanded (bS ops false) scmap
    let v ← if ops.same (← getprop ops st_sc "unexpanded") ux then pure st_sc
      else do callB ops "SyntaxContext" [← getprop ops st_sc "layer", ux,
        ← getprop ops st_sc "edition", ← getprop ops st_sc "internal"]
    let _ ← callB ops "setindex!" [scmap, v, st_sc]
    sc2 := v
  let leafy ← if ← is_leaf ops st then pure true
    else do cond ops (← callB ops "==" [← numchildren ops st, iV ops 0])
  if leafy then
    let source ← sourceref ops st
    if ops.same sc2 st_sc && !isSyntax ops (← getprop ops st "source") then pure st
    else
      let jl_source ← getprop ops st "jl_source"
      mknodeFrom ops st [("context", sc2), ("source", source), ("jl_source", jl_source)]
  else
    let source ← sourceref ops st
    let jl_source ← getprop ops st "jl_source"
    let mut cs : List (Value L) := []
    for c in ← ops.elems (← children ops st) do
      cs := cs ++ [← _trim_provenance c trim_unexpanded scmap]
    let csv ← callB ops "collect"
      [bV ops "Syntax", tup ops cs]
    mknodeFrom ops st [("context", sc2), ("source", source), ("jl_source", jl_source),
      ("children", csv)]
partial_fixpoint

def trim_provenance (st trim_unexpanded : Value L) : CoreM W L (Value L) := do
  _trim_provenance ops st trim_unexpanded (← newContextDict ops)

/--
Julia source: base/syntax.jl:439-450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, ::MIME"text/plain", sl::ScopeLayer)
    color = isnothing(sl.escaped) ? :normal : :cyan
    printstyled(io, "SL("; color)
    print(io, string(sl.mod))
    print(io, ",")
    !isnothing(sl.escaped) && print(io, sl.escaped)
    print(io, ",")
    printstyled(io, string(objectid(sl);base=62); color)
    printstyled(io, ")"; color)
end
Base.show(io::IO, sl::ScopeLayer) = Base.show(io::IO, MIME"text/plain"(), sl)

```
-/
def show_ScopeLayer_mime (io _mime sl : Value L) : CoreM W L (Value L) := do
  let escaped ← getprop ops sl "escaped"
  let color : Value L := if isNothing ops escaped then .symbol "normal" else .symbol "cyan"
  let _ ← callKw ops "printstyled" [("color", color)] [io, sV ops "SL("]
  let _ ← callB ops "print" [io, ← callB ops "string" [← getprop ops sl "mod"]]
  let _ ← callB ops "print" [io, sV ops ","]
  if !isNothing ops (← getprop ops sl "escaped") then
    let _ ← callB ops "print" [io, ← getprop ops sl "escaped"]
  let _ ← callB ops "print" [io, sV ops ","]
  let _ ← callKw ops "printstyled"  [("color", color)]
    [io, ← callKw ops "string" [("base", iV ops 62)] [← callB ops "objectid" [sl]]]
  callKw ops "printstyled" [("color", color)] [io, sV ops ")"]
def show_ScopeLayer (io sl : Value L) : CoreM W L (Value L) := do
  callB ops "show" [io, ← mimeV ops "text/plain", sl]

/--
Julia source: base/syntax.jl:451-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, ::MIME"text/plain", sc::SyntaxContext)
    color = sc.internal ? :light_black :
        sc.edition == JL_NEW_EDITION ? :normal : :blue
    printstyled(io, "["; color)
    if sc.edition != JL_NEW_EDITION
        printstyled(io, "old,"; color)
    end
    if sc.internal
        printstyled(io, "internal,"; color)
    end
    print(io, sc.layer)
    print(io, ",")
    if sc.unexpanded isa Syntax
        k = head(sc.unexpanded)
        k === :macrocall ? print(io, sc.unexpanded[1]) : print(io, k)
    end
    printstyled(io, "]"; color)
end
Base.show(io::IO, sc::SyntaxContext) = Base.show(io::IO, MIME"text/plain"(), sc)

```
-/
def show_SyntaxContext_mime (io _mime sc : Value L) : CoreM W L (Value L) := do
  let color : Value L ←
    if ← cond ops (← getprop ops sc "internal") then pure (.symbol "light_black")
    else do
      if ← cond ops (← callB ops "==" [← getprop ops sc "edition", JL_NEW_EDITION ops]) then
        pure (.symbol "normal")
      else pure (.symbol "blue")
  let _ ← callKw ops "printstyled" [("color", color)] [io, sV ops "["]
  if ← cond ops (← callB ops "!=" [← getprop ops sc "edition", JL_NEW_EDITION ops]) then
    let _ ← callKw ops "printstyled" [("color", color)] [io, sV ops "old,"]
  if ← cond ops (← getprop ops sc "internal") then
    let _ ← callKw ops "printstyled" [("color", color)] [io, sV ops "internal,"]
  let _ ← callB ops "print" [io, ← getprop ops sc "layer"]
  let _ ← callB ops "print" [io, sV ops ","]
  let u ← getprop ops sc "unexpanded"
  if isSyntax ops u then
    let k ← head ops u
    if isSym k "macrocall" then
      let _ ← callB ops "print" [io, ← callB ops "getindex" [u, iV ops 1]]
    else
      let _ ← callB ops "print" [io, k]
  callKw ops "printstyled" [("color", color)] [io, sV ops "]"]
def show_SyntaxContext (io sc : Value L) : CoreM W L (Value L) := do
  callB ops "show" [io, ← mimeV ops "text/plain", sc]

-- Reason: A section comment.
-- UNTRANSLATED
-- Source: base/syntax.jl:586-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #-------------------------------------------------------------------------------
-- # Expr <-> Syntax
-- #
-- # Adding more cases to these functions is almost certainly wrong, since these
-- # operates on arbitrary heads and arguments throughout macro expansion, not
-- # well-formed syntax after expansion is done.  Most of the complexity here is
-- # LineNumberNode absorption logic: linenodes are always considered provenance if
-- # unquoted, then removed in certain forms.  If `src` is not an linenode, it is
-- # assumed to be a better provenance source, so linenodes in `e` are not used for
-- # provenance (but still removed).
-- 
-- /Source

mutual
/--
Julia source: base/syntax.jl:597-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _first_linenode(e::Expr)
    e.head in (:macrocall, :quote, :inert) || for a in e.args
        a isa LineNumberNode && return a
        if a isa Expr
            a_out = _first_linenode(a)
            a_out isa LineNumberNode && return a_out
        end
    end
    return nothing
end
first_linenode(e::Expr) = something(_first_linenode(e), LineNumberNode(0, :var""))

```
-/
def _first_linenode : Value L → Value L
  | .expr h args =>
    if h == "macrocall" || h == "quote" || h == "inert" then nothingS ops
    else _first_linenode_args args
  | _ => nothingS ops
/-- The `for a in e.args` loop of `_first_linenode`. -/
def _first_linenode_args : List (Value L) → Value L
  | [] => nothingS ops
  | a :: as =>
    match a with
    | .lineNumberNode .. => a
    | .expr .. =>
      let a_out := _first_linenode a
      if isLnn a_out then a_out else _first_linenode_args as
    | _ => _first_linenode_args as
end

/-- `LineNumberNode(0, :var"")`. -/
def noLnn : Value L := .lineNumberNode (JInt.lit .i64 0) (.symbol "")

def first_linenode_Expr (e : Value L) : Value L :=
  let l := _first_linenode ops e
  if isNothing ops l then noLnn else l

/--
Julia source: base/syntax.jl:609-614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unescape_lnn(@nospecialize(e)) =
    e isa LineNumberNode ? e :
    (e isa Expr &&
    (e.head === :escape || e.head === Symbol("hygienic-scope")) &&
    length(e.args) > 0) ? _unescape_lnn(e.args[1]) : nothing

```
-/
def _unescape_lnn : Value L → Value L
  | e@(.lineNumberNode ..) => e
  | .expr h (a :: _) =>
    if h == "escape" || h == "hygienic-scope" then _unescape_lnn a else nothingS ops
  | _ => nothingS ops

/--
Julia source: base/syntax.jl:615-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Linenodes usually apply to the following form, but some forms contain the
# relevant line node as an argument.
function _get_inner_lnn(e::Expr, default::LineNumberNode)
    if e.head === :struct || e.head === :macrocall
        something(_first_linenode(e), default)
    elseif (e.head === :quote || e.head === :inert) &&
            length(e.args) > 0 && e.args[1] isa Expr
        something(_first_linenode(e.args[1]), default)
    elseif e.head in (:function, :macro, :module, :(=), :->)
        length(e.args) >= 2 || return default
        b = e.args[end]
        b isa Expr || return default
        b.head === :block || return default
        length(b.args) >= 1 || return default
        b_lnn = _unescape_lnn(b.args[1])
        return b_lnn isa LineNumberNode ? b_lnn : default
    else
        default
    end
end

```
-/
def _get_inner_lnn (e default : Value L) : Value L :=
  match e with
  | .expr h args =>
    let something (x : Value L) : Value L := if isNothing ops x then default else x
    if h == "struct" || h == "macrocall" then something (_first_linenode ops e)
    else if (h == "quote" || h == "inert") && (match args with | .expr .. :: _ => true | _ => false)
    then something (_first_linenode ops (args.headD default))
    else if ["function", "macro", "module", "=", "->"].contains h then
      if args.length < 2 then default
      else match args.getLast? with
        | some (.expr "block" (b1 :: _)) =>
          let b_lnn := _unescape_lnn ops b1
          if isLnn b_lnn then b_lnn else default
        | _ => default
    else default
  | _ => default

/--
Julia source: base/syntax.jl:636-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# List of Expr-AST forms that are always converted to some Syntax form and
# never inserted as an opaque `:value`. Note no LineNumberNode, which appears
# unwrapped in a macrocall (possibly generated functions too, TODO check)
isa_lowering_ast_node(@nospecialize(e)) =
    e isa Symbol || e isa QuoteNode || e isa Expr || e isa GlobalRef

```
-/
def isa_lowering_ast_node : Value L → Bool
  | .symbol _ | .quoteNode _ | .expr .. | .globalRef .. => true
  | _ => false

/--
Julia source: base/syntax.jl:651-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _expr_to_syntax(@nospecialize(e), context::SyntaxContext,
                         src::SourceAttrType, quoted::Bool)
    s = if e isa Symbol
        @mknode(;head=:identifier, value=String(e), source=src, context)
    elseif e isa QuoteNode
        v = e.value
        src = src isa LineNumberNode && v isa Expr ?
            something(first_linenode(v), src) : src
        cid, _ = _expr_to_syntax(v, context, src, true)
        @mknode(;head=:inert, source=src, children=Syntax[cid], context)
    elseif e isa Expr
        h = e.head
        if h === :value || h === :identifier
            error("expr heads :value and :identifier are reserved")
        end
        src = old_src = src isa LineNumberNode ? _get_inner_lnn(e, src) : src
        cs = Syntax[]
        rm_linenodes = h in (:block, :toplevel)
        quoted |= h in (:quote, :inert)
        for arg in e.args
            if rm_linenodes && (lnn = quoted ? arg : _unescape_lnn(arg);
                                lnn isa LineNumberNode)
                src isa LineNumberNode && (src = lnn)
            else
                cid, src = _expr_to_syntax(arg, context, src, quoted)
                push!(cs, cid)
            end
        end
        @mknode(;head=h, source=old_src, children=cs, context)
    elseif (e isa Core.SSAValue || e isa Core.SlotNumber) && !quoted
        error("SSAValue and SlotNumber objects should not occur in an AST")
    elseif e isa GlobalRef
        # Represent globalref as :identifier with :mod attribute
        @mknode(;head=:identifier, source=src, value=string(e.name),
                mod=e.mod, context)
    else
        # We may want additional special cases for other types where
        # `Base.isa_ast_node(e)`, but `:value` should be fine for most, since
        # most are produced in or after lowering
        if e isa LineNumberNode && src isa LineNumberNode
            # linenode outside of block or toplevel
            src = e
        end
        @mknode(;head=:value, value=e, source=src, context)
    end
    @assert isa_lowering_ast_node(e) || head(s) === :value s

    return s, src
end
```
-/
def _expr_to_syntax (e context src : Value L) (quoted : Bool) :
    CoreM W L (Value L × Value L) := do
  let (s, src) ← match e with
    | .symbol n => do
      let s ← mknodeFrom ops (_DEFAULT_NODE ops) [("head", .symbol "identifier"),
        ("value", ← callB ops "String" [.symbol n]), ("source", src), ("context", context)]
      pure (s, src)
    | .quoteNode v => do
      let src := if isLnn src && (match v with | .expr .. => true | _ => false) then
        first_linenode_Expr ops v else src
      let (cid, _) ← _expr_to_syntax v context src true
      let s ← mknodeFrom ops (_DEFAULT_NODE ops) [("head", .symbol "inert"), ("source", src),
        ("children", ← callB ops "getindex" [bV ops "Syntax", cid]), ("context", context)]
      pure (s, src)
    | .expr h args => do
      if h == "value" || h == "identifier" then
        let _ ← callB ops "error" [sV ops "expr heads :value and :identifier are reserved"]
      let old_src := if isLnn src then _get_inner_lnn ops e src else src
      let mut src := old_src
      let cs ← callB ops "getindex" [bV ops "Syntax"]
      let rm_linenodes := h == "block" || h == "toplevel"
      let quoted := quoted || h == "quote" || h == "inert"
      for arg in args do
        if rm_linenodes && isLnn (if quoted then arg else _unescape_lnn ops arg) then
          if isLnn src then src := (if quoted then arg else _unescape_lnn ops arg)
        else
          let (cid, src') ← _expr_to_syntax arg context src quoted
          src := src'
          let _ ← callB ops "push!" [cs, cid]
      let s ← mknodeFrom ops (_DEFAULT_NODE ops) [("head", .symbol h), ("source", old_src),
        ("children", cs), ("context", context)]
      pure (s, src)
    | .globalRef mod name => do
      let s ← mknodeFrom ops (_DEFAULT_NODE ops) [("head", .symbol "identifier"), ("source", src),
        ("value", ← callB ops "string" [.symbol name]), ("mod", .leaf mod), ("context", context)]
      pure (s, src)
    | _ => do
      let ssaOrSlot := match e with | .ssaValue _ | .slotNumber _ => true | _ => false
      if ssaOrSlot && !quoted then
        let _ ← callB ops "error"
          [sV ops "SSAValue and SlotNumber objects should not occur in an AST"]
      let src := if isLnn e && isLnn src then e else src
      let s ← mknodeFrom ops (_DEFAULT_NODE ops) [("head", .symbol "value"), ("value", e),
        ("source", src), ("context", context)]
      pure (s, src)
  if !(isa_lowering_ast_node e || isSym (← head ops s) "value") then
    throw (← callB ops "AssertionError" [← callB ops "string" [s]])
  return (s, src)
partial_fixpoint

/--
Julia source: base/syntax.jl:642-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expr_to_syntax(@nospecialize(e),
                        src::Union{LineNumberNode, SourceRef}=
                            e isa Expr ? first_linenode(e) : LineNumberNode(0, :var""),
                        context=SyntaxContext(nothing, nothing, JL_OLD_EDITION, false))
    _expr_to_syntax(e, context, src, false)[1]
end
function expr_to_syntax(@nospecialize(e), src::Syntax)
    _expr_to_syntax(e, src.context, src, false)[1]
end
```
-/
def expr_to_syntax3 (e src context : Value L) : CoreM W L (Value L) := do
  pure (← _expr_to_syntax ops e context src false).1
def expr_to_syntax2 (e src : Value L) : CoreM W L (Value L) := do
  expr_to_syntax3 ops e src
    (← SyntaxContext4 ops (nothingS ops) (nothingS ops) (JL_OLD_EDITION ops) (bS ops false))
def expr_to_syntax1 (e : Value L) : CoreM W L (Value L) := do
  let src := match e with
    | .expr .. => first_linenode_Expr ops e
    | _ => noLnn
  expr_to_syntax2 ops e src
def expr_to_syntax_Syntax (e src : Value L) : CoreM W L (Value L) := do
  pure (← _expr_to_syntax ops e (← getprop ops src "context") src false).1

/--
Julia source: base/syntax.jl:700-709 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# @__doc__ is brittle
function _is_meta_doc_block(s::Syntax)
    head(s) === :block && numchildren(s) == 2 && let s1 = s[1]
        head(s1) === :meta && numchildren(s1) == 1 && let s11 = s1[1]
            head(s11) === :identifier && s11.value === "doc"
        end
    end
end

```
-/
def _is_meta_doc_block (s : Value L) : CoreM W L Bool := do
  if !isSym (← head ops s) "block" then return false
  if !(← cond ops (← callB ops "==" [← numchildren ops s, iV ops 2])) then return false
  let s1 ← callB ops "getindex" [s, iV ops 1]
  if !isSym (← head ops s1) "meta" then return false
  if !(← cond ops (← callB ops "==" [← numchildren ops s1, iV ops 1])) then return false
  let s11 ← callB ops "getindex" [s1, iV ops 1]
  if !isSym (← head ops s11) "identifier" then return false
  pure (ops.same (← getprop ops s11 "value") (sV ops "doc"))

/--
Julia source: base/syntax.jl:710-714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_eventually_call(e)
    return e isa Expr && (e.head === :call ||
        e.head in (:escape, :where, :(::)) && is_eventually_call(e.args[1]))
end

```
-/
-- `e.args[1]`: `getindex` of the argument vector, which throws `BoundsError` when it is empty.
def firstArg (e : Value L) : CoreM W L (Value L) :=
  match e with
  | .expr _ (a :: _) => pure a
  | _ => do callB ops "getindex" [← ops.getfield e (.symbol "args"), iV ops 1]

def is_eventually_call (e : Value L) : CoreM W L Bool := do
  match e with
  | .expr "call" _ => pure true
  | .expr h _ =>
    if h == "escape" || h == "where" || h == "::" then do is_eventually_call (← firstArg ops e)
    else pure false
  | _ => pure false
partial_fixpoint

/--
Julia source: base/syntax.jl:715-788 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `suppress_linenodes` is true if `st`'s parent knows `st` is an exception to
# normal linenode rules.  It only applies to `st`, and not transitively to its
# children.
function syntax_to_expr(s::Syntax, suppress_linenodes=false)
    push_lno!(ex::Expr, lno::LineNumberNode, first::Bool=false) =
        if lno.file !== :var"" || lno.line != 0
            first ? pushfirst!(ex.args, lno) : push!(ex.args, lno)
        end
    h = head(s)
    if h === :identifier
        # @assert scope layer is base
        n = Symbol(s.value::String)
        mod = s.mod
        !isnothing(mod) ? GlobalRef(mod, n) : n
    elseif h === :value
        v = s.value
        # Let `s.value isa Symbol` (or other AST node).  Since we enforce that
        # this is never produced by the reverse Expr->Syntax transformation,
        # there is no lonely Expr for which `s` is the only Syntax
        # representation.  This means we can pick some other expr this
        # represents, namely Expr(`(inert ,s.value)) rather than
        # Expr(s.value).
        isa_lowering_ast_node(v) ? QuoteNode(v) : v
    elseif h === :inert
        QuoteNode(syntax_to_expr(s[1]))
    else
        # TODO: should handle post-lowering forms as well
        @assert !is_leaf(s) (s, "syntax_to_expr should only be used pre-desugaring")
        out = Expr(h)

        # (Move the following assumptions to the docs if they turn out accurate)
        # The only mandatory LineNumberNode is the second macrocall argument.
        # Other than that, optional linenodes may show up anywhere within:
        # - `block`, unless the block is the first child of `for` or `let`
        # - `toplevel`
        # Macro authors are responsible for handling any linenodes that follow
        # the rules above (but the presence of optional linenodes can't be
        # counted upon).
        need_lnns = h in (:block, :toplevel) && !suppress_linenodes &&
            !_is_meta_doc_block(s)
        for (i, c) in enumerate(children(s))
            need_lnns && push_lno!(out, first_linenode(c))
            let suppress_c = i == 1 && (h == :for || h == :let) || i == 2 && h == :do
                push!(out.args, syntax_to_expr(c, suppress_c))
            end
        end
        # Add extra linenodes to some blocks for better provenance
        if !suppress_linenodes && h === :block && length(out.args) == 0
            push_lno!(out, first_linenode(s))
        elseif h in (:module, :function, :macro) && length(out.args) > 0
            let b = out.args[end]
                b isa Expr && b.head === :block &&
                    push_lno!(b, first_linenode(s), true)
            end
        elseif length(out.args) == 2 && ((h === :-> && !suppress_linenodes) ||
            (h === :(=) && is_eventually_call(out.args[1])))
            let b = out.args[end]
                b isa Expr && b.head === :block && !isempty(b.args) &&
                    b.args[1] isa LineNumberNode && first_linenode(s) != b.args[1] &&
                    push_lno!(b, first_linenode(s), true)
            end
        elseif h in (:for, :while) && length(out.args) > 0
            let b = out.args[end]
                b isa Expr && b.head === :block && let sr = sourceref(s)
                    last_lno = sr isa LineNumberNode ? sr :
                        LineNumberNode(source_line(sr.code, sr.last_byte),
                                       filename(s))
                    push_lno!(b, last_lno)
                end
            end
        end
        out
    end
end
```
-/
-- `Expr` values are their contents: `push!(ex.args, x)` on an `Expr` is the `Expr` with `x`
-- appended, and a change to `b = out.args[end]` is a change to the last argument of `out`.
-- `push_lno!(ex, lno, first)` on the arguments `args` of `ex`.
def push_lno! (args : List (Value L)) (lno : Value L) (first : Bool) :
    CoreM W L (List (Value L)) := do
  let file_set := !ops.same (← getprop ops lno "file") (.symbol "")
  let push ← if file_set then pure true
    else do cond ops (← callB ops "!=" [← getprop ops lno "line", iV ops 0])
  pure (if push then (if first then lno :: args else args ++ [lno]) else args)

/-- The head of an `Expr(h)`: `TypeError` unless `h` is a `Symbol`. -/
def exprHead (h : Value L) : CoreM W L Sym :=
  match h with
  | .symbol n => pure n
  | _ => JuliaLean.base.boot.throwTypeError ops.toCoreOps "Expr" "" (.leaf (ops.core "Symbol")) h

def syntax_to_expr (s : Value L) (suppress_linenodes : Bool) : CoreM W L (Value L) := do
  let h ← head ops s
  if isSym h "identifier" then
    let v ← JuliaLean.base.boot.typeassert ops.toCoreOps (← getprop ops s "value") (bV ops "String")
    let n ← callB ops "Symbol" [v]
    let mod ← getprop ops s "mod"
    if !isNothing ops mod then callB ops "GlobalRef" [mod, n] else pure n
  else if isSym h "value" then
    let v ← getprop ops s "value"
    pure (if isa_lowering_ast_node v then .quoteNode v else v)
  else if isSym h "inert" then
    pure (.quoteNode (← syntax_to_expr (← callB ops "getindex" [s, iV ops 1]) false))
  else
    if ← is_leaf ops s then
      throw (← callB ops "AssertionError" [← callB ops "string"
        [tup ops [s, sV ops "syntax_to_expr should only be used pre-desugaring"]]])
    let hn ← exprHead ops h
    let mut args : List (Value L) := []
    let need_lnns ← if (hn == "block" || hn == "toplevel") && !suppress_linenodes then do
        pure !(← _is_meta_doc_block ops s)
      else pure false
    let mut i : Nat := 0
    for c in ← ops.elems (← children ops s) do
      i := i + 1
      if need_lnns then
        args ← push_lno! ops args (← callB ops "first_linenode" [c]) false
      let suppress_c := i == 1 && (hn == "for" || hn == "let") || i == 2 && hn == "do"
      args := args ++ [← syntax_to_expr c suppress_c]
    if !suppress_linenodes && hn == "block" && args.length == 0 then
      args ← push_lno! ops args (← callB ops "first_linenode" [s]) false
    else if ["module", "function", "macro"].contains hn && args.length > 0 then
      match args.getLast? with
      | some (.expr "block" bargs) =>
        let bargs ← push_lno! ops bargs (← callB ops "first_linenode" [s]) true
        args := args.dropLast ++ [.expr "block" bargs]
      | _ => pure ()
    else
      let assign_call ← if args.length == 2 then
          if hn == "->" && !suppress_linenodes then pure true
          else if hn == "=" then is_eventually_call ops (args.headD (nothingS ops))
          else pure false
        else pure false
      if assign_call then
        match args.getLast? with
        | some (.expr "block" (b1 :: brest)) =>
          if isLnn b1 then
            if ← cond ops (← callB ops "!=" [← callB ops "first_linenode" [s], b1]) then
              let bargs ← push_lno! ops (b1 :: brest) (← callB ops "first_linenode" [s]) true
              args := args.dropLast ++ [.expr "block" bargs]
        | _ => pure ()
      else if (hn == "for" || hn == "while") && args.length > 0 then
        match args.getLast? with
        | some (.expr "block" bargs) =>
          let sr ← sourceref ops s
          let last_lno ← if isLnn sr then pure sr else do
            let code ← getprop ops sr "code"
            callB ops "LineNumberNode"
              [← source_line ops code (← getprop ops sr "last_byte"), ← filename ops s]
          let bargs ← push_lno! ops bargs last_lno false
          args := args.dropLast ++ [.expr "block" bargs]
        | _ => pure ()
    pure (.expr hn args)
partial_fixpoint

def syntax_to_expr1 (s : Value L) : CoreM W L (Value L) := syntax_to_expr ops s false

/--
Julia source: base/syntax.jl:789-798 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# convenience function for `jl_parse`
function _c_parseall_expr(code::Core.SimpleVector, filename::String,
                          lineno::Int, mod::Union{Module, Nothing})
    (ptr, len) = code
    str = unsafe_string(ptr, len)
    pfm = Meta.parser_for_module(mod)
    ex, offset = Meta._parse_string(str, filename, lineno, 1, :all, Expr, pfm)
    return Core.svec(ex, offset-1)
end
```
-/
def _c_parseall_expr (code filename lineno mod : Value L) : CoreM W L (Value L) := do
  let (ptr, len) ← destructure2 ops code
  let str ← callB ops "unsafe_string" [ptr, len]
  let pfm ← ops.call (← metaFn ops "parser_for_module") [mod]
  let (ex, offset) ← destructure2 ops (← ops.call (← metaFn ops "_parse_string")
    [str, filename, lineno, iV ops 1, .symbol "all", .leaf (ops.core "Expr"), pfm])
  ops.call (.leaf (ops.core "svec")) [ex, ← callB ops "-" [offset, iV ops 1]]

/--
Julia source: base/syntax.jl:799-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function fl_toplevel_eval(mod::Module, @nospecialize(x))
    ex = if x isa Syntax
        Expr(:toplevel, first_linenode(x), syntax_to_expr(x))
    else
        x
    end
    ccall(:jl_toplevel_eval, Any, (Any, Any), mod, ex)
end

```
-/
def fl_toplevel_eval (mod x : Value L) : CoreM W L (Value L) := do
  let ex ← if isSyntax ops x then do
      pure (.expr "toplevel" [← callB ops "first_linenode" [x], ← syntax_to_expr1 ops x])
    else pure x
  ops.toplevelEvalC mod ex

-- Reason: A section comment.
-- UNTRANSLATED
-- Source: base/syntax.jl:809-811 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #-------------------------------------------------------------------------------
-- # Printing
-- 
-- /Source

/--
Julia source: base/syntax.jl:812-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
attrsummary(name, _value) = string(name)
attrsummary(name, value::Number) = "$name=$value"
attrsummary(name, value::LineNumberNode) = "$name=L$(value.line)"
attrsummary(name, value::Module) = "$name=$value"

```
-/
def attrsummary_Any (name _value : Value L) : CoreM W L (Value L) := callB ops "string" [name]
def attrsummary_Number (name value : Value L) : CoreM W L (Value L) :=
  callB ops "string" [name, sV ops "=", value]
def attrsummary_LineNumberNode (name value : Value L) : CoreM W L (Value L) := do
  callB ops "string" [name, sV ops "=L", ← getprop ops value "line"]
def attrsummary_Module (name value : Value L) : CoreM W L (Value L) :=
  callB ops "string" [name, sV ops "=", value]

/--
Julia source: base/syntax.jl:817-822 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function subscript_str(i)
     replace(string(i),
             "0"=>"₀", "1"=>"₁", "2"=>"₂", "3"=>"₃", "4"=>"₄",
             "5"=>"₅", "6"=>"₆", "7"=>"₇", "8"=>"₈", "9"=>"₉")
end

```
-/
def subscript_str (i : Value L) : CoreM W L (Value L) := do
  let mut pairs : List (Value L) := []
  for (d, s) in [("0", "₀"), ("1", "₁"), ("2", "₂"), ("3", "₃"), ("4", "₄"), ("5", "₅"),
      ("6", "₆"), ("7", "₇"), ("8", "₈"), ("9", "₉")] do
    pairs := pairs ++ [← callB ops "=>" [sV ops d, sV ops s]]
  callB ops "replace" ((← callB ops "string" [i]) :: pairs)

/--
Julia source: base/syntax.jl:823-864 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _value_string(ex)
    k = head(ex)
    str = k == :identifier  ? syntax_name(ex)           :
          k == :placeholder ? syntax_name(ex)           :
          k == :ssavalue    ? "%"                   :
          k == :bindingid   ? "#"                   :
          k == :label       ? "label"               :
          k == :nothing     ? "core.nothing"        :
          k == :core        ? "core.$(syntax_name(ex))" :
          k == :top         ? "top.$(syntax_name(ex))"  :
          k == :symbol      ? ":$(syntax_name(ex))" :
          k == :globalref   ? "$(ex.mod).$(syntax_name(ex))" :
          k == :slot        ? "slot" :
          k == :slots       ? "Slots" :
          k == :lambdabindings ? "LambdaBindings" :
          k == :latestworld ? "latestworld" :
          k == :static_parameter ? "static_parameter" :
          k == :symboliclabel ? "label:$(syntax_name(ex))" :
          k == :symbolicgoto ? "goto:$(syntax_name(ex))" :
          k == :sourcelocation ?
              "SourceLocation:$(first_linenode(ex).line)" :
              k == :value ?
              (ex.value isa SourceRef ?
              "SourceRef:$(first_linenode(ex).line)" :
              ex.value isa SyntaxContext ? "SyntaxContext(#=omitted=#)" : repr(ex.value)) :
              ex.value !== nothing ? repr(ex.value) : "::$k"

    if head(ex) in (:bindingid, :slot, :ssavalue, :static_parameter, :label)
        idstr = subscript_str(ex.value::Int)
        str = "$(str)$idstr"
    end
    if k == :slot || k == :bindingid
        for p in provenance(ex)
            if head(p) == :identifier
                str = "$(str)/$(syntax_name(p))"
                break
            end
        end
    end
    return str
end

```
-/
def _value_string (ex : Value L) : CoreM W L (Value L) := do
  let k ← head ops ex
  let named (pre : String) : CoreM W L (Value L) := do
    callB ops "string" [sV ops pre, ← syntax_name ops ex]
  let mut str ←
    if isSym k "identifier" then syntax_name ops ex
    else if isSym k "placeholder" then syntax_name ops ex
    else if isSym k "ssavalue" then pure (sV ops "%")
    else if isSym k "bindingid" then pure (sV ops "#")
    else if isSym k "label" then pure (sV ops "label")
    else if isSym k "nothing" then pure (sV ops "core.nothing")
    else if isSym k "core" then named "core."
    else if isSym k "top" then named "top."
    else if isSym k "symbol" then named ":"
    else if isSym k "globalref" then do
      callB ops "string" [← getprop ops ex "mod", sV ops ".", ← syntax_name ops ex]
    else if isSym k "slot" then pure (sV ops "slot")
    else if isSym k "slots" then pure (sV ops "Slots")
    else if isSym k "lambdabindings" then pure (sV ops "LambdaBindings")
    else if isSym k "latestworld" then pure (sV ops "latestworld")
    else if isSym k "static_parameter" then pure (sV ops "static_parameter")
    else if isSym k "symboliclabel" then named "label:"
    else if isSym k "symbolicgoto" then named "goto:"
    else if isSym k "sourcelocation" then do
      callB ops "string" [sV ops "SourceLocation:",
        ← getprop ops (← callB ops "first_linenode" [ex]) "line"]
    else if isSym k "value" then do
      let v ← getprop ops ex "value"
      if isSourceRef ops v then
        callB ops "string" [sV ops "SourceRef:",
          ← getprop ops (← callB ops "first_linenode" [ex]) "line"]
      else if (match synOf ops v with | some (.context _) => true | _ => false) then
        pure (sV ops "SyntaxContext(#=omitted=#)")
      else callB ops "repr" [v]
    else do
      let v ← getprop ops ex "value"
      if !isNothing ops v then callB ops "repr" [v] else callB ops "string" [sV ops "::", k]
  let h ← head ops ex
  if ["bindingid", "slot", "ssavalue", "static_parameter", "label"].any (isSym h) then
    let idstr ← subscript_str ops
      (← JuliaLean.base.boot.typeassert ops.toCoreOps (← getprop ops ex "value") (bV ops "Int"))
    str ← callB ops "string" [str, idstr]
  if isSym k "slot" || isSym k "bindingid" then
    for p in ← ops.elems (← provenance ops ex) do
      if isSym (← head ops p) "identifier" then
        str ← callB ops "string" [str, sV ops "/", ← syntax_name ops p]
        break
  return str

/--
Julia source: base/syntax.jl:865-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_syntax_tree(io, ex, indent, show_kinds, @nospecialize(parent_sc))
    nodestr = !is_leaf(ex) ? "[$(string(head(ex)))]" : _value_string(ex)

    treestr = rpad(string(indent, nodestr), 40)
    if show_kinds && is_leaf(ex)
        treestr = treestr*" :: "*string(head(ex))
    end

    std_attrs = Set([:value,:head,:syntax_flags,:source,:context])
    attrstr = join([attrsummary(n, getproperty(ex, n))
                    for n in fieldnames(typeof(ex)) if n ∉ std_attrs &&
                        getproperty(ex, n) !== nothing], ",")
    print(io, rpad(treestr, 60))
    print(io, " | ")
    sc = ex.context
    if sc !== parent_sc
        print(io, sc)
        print(io, ",")
    end
    print(io, attrstr)
    println(io)

    if !is_leaf(ex)
        new_indent = indent*"  "
        for n in children(ex)
            _show_syntax_tree(io, n, new_indent, show_kinds, sc)
        end
    end
end

```
-/
def _show_syntax_tree (io ex indent show_kinds parent_sc : Value L) : CoreM W L (Value L) := do
  let nodestr ← if !(← is_leaf ops ex) then do
      callB ops "string" [sV ops "[", ← callB ops "string" [← head ops ex], sV ops "]"]
    else _value_string ops ex
  let mut treestr ← callB ops "rpad" [← callB ops "string" [indent, nodestr], iV ops 40]
  if ← cond ops show_kinds then
    if ← is_leaf ops ex then
      treestr ← callB ops "*" [treestr, sV ops " :: ", ← callB ops "string" [← head ops ex]]
  let std_attrs ← callB ops "Set" [← callB ops "vect" [.symbol "value", .symbol "head",
    .symbol "syntax_flags", .symbol "source", .symbol "context"]]
  let mut summaries : List (Value L) := []
  for n in ← ops.elems (← callB ops "fieldnames" [.leaf (ops.typeOf ex)]) do
    if ← cond ops (← callB ops "∉" [n, std_attrs]) then
      if !isNothing ops (← callB ops "getproperty" [ex, n]) then
        summaries := summaries ++
          [← callB ops "attrsummary" [n, ← callB ops "getproperty" [ex, n]]]
  let attrstr ← callB ops "join" [← callB ops "vect" summaries, sV ops ","]
  let _ ← callB ops "print" [io, ← callB ops "rpad" [treestr, iV ops 60]]
  let _ ← callB ops "print" [io, sV ops " | "]
  let sc ← getprop ops ex "context"
  if !ops.same sc parent_sc then
    let _ ← callB ops "print" [io, sc]
    let _ ← callB ops "print" [io, sV ops ","]
  let _ ← callB ops "print" [io, attrstr]
  let _ ← callB ops "println" [io]
  if !(← is_leaf ops ex) then
    let new_indent ← callB ops "*" [indent, sV ops "  "]
    for n in ← ops.elems (← children ops ex) do
      let _ ← _show_syntax_tree io n new_indent show_kinds sc
  return nothingS ops
partial_fixpoint

/--
Julia source: base/syntax.jl:895-898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, ::MIME"text/plain", ex::Syntax, show_kinds=true)
    assert_syntax(ex)
    _show_syntax_tree(io, ex, "", show_kinds, nothing)
end
```
-/
def show_Syntax_plain (io _mime ex show_kinds : Value L) : CoreM W L (Value L) := do
  let _ ← assert_syntax1 ops ex
  _show_syntax_tree ops io ex (sV ops "") show_kinds (nothingS ops)
def show_Syntax_plain3 (io mime ex : Value L) : CoreM W L (Value L) :=
  show_Syntax_plain ops io mime ex (bS ops true)

/--
Julia source: base/syntax.jl:899-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_syntax_tree_sexpr(io, ex)
    if is_leaf(ex)
        print(io, _value_string(ex))
    else
        print(io, "(", string(head(ex)))
        for n in children(ex)
            print(io, ' ')
            _show_syntax_tree_sexpr(io, n)
        end
        print(io, ')')
    end
end

```
-/
def _show_syntax_tree_sexpr (io ex : Value L) : CoreM W L (Value L) := do
  if ← is_leaf ops ex then
    callB ops "print" [io, ← _value_string ops ex]
  else
    let _ ← callB ops "print" [io, sV ops "(", ← callB ops "string" [← head ops ex]]
    for n in ← ops.elems (← children ops ex) do
      let _ ← callB ops "print" [io, .leaf (ops.char ' ')]
      let _ ← _show_syntax_tree_sexpr io n
    callB ops "print" [io, .leaf (ops.char ')')]
partial_fixpoint

/--
Julia source: base/syntax.jl:912-916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, ::MIME"text/x.sexpression", node::Syntax)
    assert_syntax(node)
    _show_syntax_tree_sexpr(io, node)
end

```
-/
def show_Syntax_sexpression (io _mime node : Value L) : CoreM W L (Value L) := do
  let _ ← assert_syntax1 ops node
  _show_syntax_tree_sexpr ops io node

/--
Julia source: base/syntax.jl:917-920 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.show(io::IO, node::Syntax)
    assert_syntax(node)
    _show_syntax_tree_sexpr(io, node)
end
```
-/
def show_Syntax (io node : Value L) : CoreM W L (Value L) := do
  let _ ← assert_syntax1 ops node
  _show_syntax_tree_sexpr ops io node

end

end JuliaLean.base.syntax

