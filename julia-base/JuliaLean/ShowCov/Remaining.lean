import JuliaLean.ShowCov.Basic
import JuliaLean.Show.ExprPrint

/-!
Models for the remaining method bodies in `base/show.jl`.  Runtime reflection,
printing of an already-rendered Julia value, and calls into the parser are
explicit inputs.  The surrounding branch order and output construction mirror
the pinned Julia source.
-/

namespace JuliaLean.ShowCov.Remaining

open JuliaLean.Show

abbrev Trace := List String

def traceText (xs : Trace) : String := String.join xs

/-! ## Function and container display -/

structure SelfInput where
  typeNameIsSingleton : Bool
  backdatedConstant : Bool
  restrictionTypeIsSelf : Bool
  globalDefined : Bool
  globalTypeIsSelf : Bool
  deriving Repr, DecidableEq

/-- Mirrors `_isself` at `base/show.jl:41-53`. -/
def isSelf (x : SelfInput) : Bool :=
  if x.typeNameIsSingleton then false
  else if x.backdatedConstant then x.restrictionTypeIsSelf
  else x.globalDefined && x.globalTypeIsSelf

inductive FunctionKind where
  | intrinsic (id : Int)
  | builtin
  | generic
  deriving Repr, DecidableEq

structure FunctionView where
  kind : FunctionKind
  name : String
  typeText : String
  methodCount : Nat
  self : SelfInput
  deriving Repr, DecidableEq

/-- Mirrors `show(::MIME"text/plain", ::Function)` at `base/show.jl:55-73`.
`compactText` is the result of the compact `show(io, f)` call. -/
def showFunctionPlain (compact : Bool) (compactText : String) (f : FunctionView) : String :=
  if compact then compactText
  else match f.kind with
    | .intrinsic id => f.name ++ " (intrinsic function #" ++ toString id ++ ")"
    | .builtin => f.name ++ " (built-in function)"
    | .generic =>
      let n := f.methodCount
      let methodWord := if n = 1 then "method" else "methods"
      let shownName := if isSelf f.self || f.name.contains '#' then f.name else "(::" ++ f.typeText ++ ")"
      let what := if shownName.startsWith "@" then "macro" else "generic function"
      shownName ++ " (" ++ what ++ " with " ++ toString n ++ " " ++ methodWord ++ ")"

structure IterEntry where
  full : String
  limited : String
  deriving Repr, DecidableEq

/-- Body-level model of the KeySet/ValueIterator text display at
`base/show.jl:137-166`. -/
def showKeyValueIter (summary forward label : String) (entries : List IterEntry)
    (compact limit : Bool) (rows : Nat) : String :=
  if entries.isEmpty && compact then forward
  else if entries.isEmpty then summary
  else if limit && rows < 2 then summary ++ ". " ++ label ++ ": …"
  else
    let room := if limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if limit then e.limited else e.full)
    let ellipsis := if limit && room < entries.length then ["\n  ⋮"] else []
    summary ++ ". " ++ label ++ ":" ++ String.join (lines ++ ellipsis)

structure DictEntry where
  key : String
  value : String
  alignedLimitedKey : String
  limitedValue : String
  deriving Repr, DecidableEq

/-- Body-level model of `show(::MIME"text/plain", ::AbstractDict)` at
`base/show.jl:168-233`.  The four strings are the results of the source's
`sprint` and truncation calls. -/
def showDictPlain (summary forward : String) (entries : List DictEntry)
    (hasLength circular limit : Bool) (rows : Nat) (ellipsisKey : String := "⋮") : String :=
  if entries.isEmpty || !hasLength then forward
  else if circular then summary ++ ":"
  else if limit && rows < 2 then summary ++ ": …"
  else
    let room := if limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map fun e =>
      "\n  " ++ (if limit then e.alignedLimitedKey else e.key) ++ " => " ++
        (if limit then e.limitedValue else e.value)
    let ellipsis := if limit && room < entries.length then ["\n  " ++ ellipsisKey ++ " => ⋮"] else []
    summary ++ ":" ++ String.join (lines ++ ellipsis)

/-- Body-level model of `show(::MIME"text/plain", ::AbstractSet)` at
`base/show.jl:241-276`. -/
def showSetPlain (summary forward : String) (entries : List IterEntry)
    (circular limit : Bool) (rows : Nat) : String :=
  if entries.isEmpty then forward
  else if circular then summary ++ ":"
  else if limit && rows < 2 then summary ++ ": …"
  else
    let room := if limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if limit then e.limited else e.full)
    let ellipsis := if limit && room < entries.length then ["\n  ⋮ "] else []
    summary ++ ":" ++ String.join (lines ++ ellipsis)

inductive ActiveRepl where
  | absent
  | present (moduleName : String)
  deriving Repr, DecidableEq

/-- Mirrors `active_module()` at `base/show.jl:570-578`. -/
def activeModule (pure : Bool) (active : ActiveRepl) : R String :=
  if pure then .error (.errorException "active_module() should not be called from a pure context")
  else match active with
    | .absent => .ok "Main"
    | .present m => .ok m

structure FunctionNameView where
  nameIsSingleton : Bool
  singletonName : String
  moduleName : String
  compact : Bool
  globallyBound : Bool
  visible : Bool
  sameModule : Bool
  deriving Repr, DecidableEq

/-- Mirrors `show_function` at `base/show.jl:583-601`; `fallback` is the
rendered result of the chosen fallback function. -/
def showFunction (f : FunctionNameView) (fallback : String) : String :=
  if f.nameIsSingleton then fallback
  else if f.compact then f.singletonName
  else if f.globallyBound then
    (if f.visible || f.sameModule then "" else f.moduleName ++ ".") ++ f.singletonName
  else fallback

/-- Mirrors `show(::Core.IntrinsicFunction)` at `base/show.jl:606-611`. -/
def showIntrinsic (compact : Bool) (name : String) : String :=
  (if compact then "" else "Core.Intrinsics.") ++ name

/-- Mirrors `print(::Core.IntrinsicFunction)` at `base/show.jl:613`. -/
def printIntrinsic (name : String) : String := name

/-! ## Type analysis and printing -/

/-- Mirrors `print_without_params` at `base/show.jl:617-620`. -/
def printWithoutParams (unwrappedIsData wrapperIsOriginal : Bool) : Bool :=
  unwrappedIsData && wrapperIsOriginal

structure TVarBinding where
  unionallKey : Bool
  isTypeVar : Bool
  name : String
  occurs : Bool
  deriving Repr, DecidableEq

/-- Mirrors the IOContext overload of `io_has_tvar_name` at
`base/show.jl:622-629`. -/
def ioHasTvarName (bindings : List TVarBinding) (name : String) : Bool :=
  bindings.any fun b => b.unionallKey && b.isTypeVar && b.name == name && b.occurs

/-- Mirrors the plain-IO overload at `base/show.jl:630`. -/
def ioHasTvarNamePlain (_name : String) : Bool := false

inductive TypeShape where
  | data (moduleName : String)
  | typeVar (upper : TypeShape)
  | typeEq (parameter : Option TypeShape)
  | typeEgal (parameter : TypeShape)
  | union (left right : TypeShape)
  | other
  deriving Repr

/-- Mirrors the four `modulesof!` methods at `base/show.jl:632-652`. -/
def modulesOf : TypeShape → List String
  | .data m => [m]
  | .typeVar ub => modulesOf ub
  | .typeEq (some p) => modulesOf p
  | .typeEq none => []
  | .typeEgal p => modulesOf p
  | .union a b => (modulesOf a ++ modulesOf b).eraseDups
  | .other => []

/-- Mirrors `has_other_free_typevars` at `base/show.jl:654-667`. -/
def hasOtherFreeTypevars (free before : List Nat) : Bool :=
  free.any fun v => !before.contains v

inductive AliasShape where
  | atom (text : String)
  | unionall (name : String) (unbounded : Bool) (body : AliasShape)
  deriving Repr

/-- Mirrors the recursive binder walk in `unbounded_typealias` at
`base/show.jl:674-684`. -/
def unboundedTypealias : AliasShape → AliasShape
  | a@(.atom _) => a
  | .unionall name true body => .unionall name true (unboundedTypealias body)
  | .unionall name false body => .unionall name true (unboundedTypealias body)

/-- Mirrors `reapply_unionall_env` at `base/show.jl:692-701`. -/
def reapplyUnionallEnv (isContext : Bool) (bindings : List (Bool × String)) (x : String) : String :=
  if isContext then bindings.foldl (fun acc b => if b.1 then "(" ++ acc ++ " where " ++ b.2 ++ ")" else acc) x
  else x

structure AliasCandidate where
  name : String
  env : List String
  defined : Bool
  deprecated : Bool
  constant : Bool
  isType : Bool
  hasFree : Bool
  printsWithoutParams : Bool
  properSubtype : Bool
  unionall : Bool
  applicationSucceeded : Bool
  hasOtherFree : Bool
  appliedEqualsInput : Bool
  exactInput : Bool
  strictSubtypes : List String
  deriving Repr, DecidableEq

def validTypeAliasCandidate (c : AliasCandidate) : Bool :=
  c.defined && !c.deprecated && c.constant && c.isType && !c.hasFree &&
    !c.printsWithoutParams && c.properSubtype &&
    (if c.unionall then c.applicationSucceeded && !c.hasOtherFree && c.appliedEqualsInput else c.exactInput)

/-- Mirrors candidate collection, strict-subtype filtering, and the unique
result rule in `make_typealias` at `base/show.jl:703-767`. -/
def makeTypealias (isAny isTuple : Bool) (candidates : List AliasCandidate) : Option (String × List String) :=
  if isAny || isTuple then none
  else
    let valid := candidates.filter validTypeAliasCandidate
    let names := valid.map (·.name)
    let best := if valid.length > 1 then
      valid.filter fun c => !(c.strictSubtypes.any fun n => names.contains n)
    else valid
    match best with
    | [c] => some (c.name, c.env)
    | _ => none

/-- Mirrors `isgensym` at `base/show.jl:769`. -/
def isGensym (name : String) : Bool := name.contains '#'

/-- Mirrors `show_can_elide` at `base/show.jl:771-784`.  The two lists contain
the later where-binders and the other environment slots that refer to `p`. -/
def showCanElide (isSelected : Bool) (elide : Nat) (laterRefs otherEnvRefs : List Bool) : Bool :=
  elide != 0 && isSelected && !(laterRefs.any id) && !(otherEnvRefs.any id)

/-- Mirrors the nested `egal_var` method at `base/show.jl:789-793`. -/
def egalVar (otherIsTypeVar upperEquivalent lowerEquivalent : Bool) : Bool :=
  otherIsTypeVar && upperEquivalent && lowerEquivalent

inductive ParamRender where
  | plain (text : String)
  | typevar (text lower upper : String) (lowerBottom upperAny : Bool)
      (whereIndex : Nat)
  deriving Repr, DecidableEq

def renderParam (p : ParamRender) (elide : Nat) : String := match p with
  | .plain text => text
  | .typevar text lower upper lowerBottom upperAny whereIndex =>
    if lowerBottom && whereIndex > elide then "<:" ++ upper
    else if upperAny && whereIndex > elide then ">:" ++ lower
    else text

/-- Mirrors the final rendering and where-vector resize performed by
`show_typeparams` at `base/show.jl:786-830`; the source loop's decisions are
represented by `keep` and `elide`. -/
def showTypeparams (params : List ParamRender) (keep elide : Nat) : String × Nat :=
  let visible := (params.take keep).map fun p => renderParam p elide
  (if visible.isEmpty then "" else "{" ++ ", ".intercalate visible ++ "}", elide)

/-- Mirrors `show_typealias_name` at `base/show.jl:832-845`. -/
def showTypealiasName (compact visible : Bool) (moduleName name : String) : String :=
  (if !compact && !visible then moduleName ++ "." else "") ++ name

/-- Mirrors `show_typealias(::GlobalRef, env, wheres)` at
`base/show.jl:847-862`. -/
def showTypealias (name renderedParams : String) (envEmpty : Bool) : String :=
  name ++ if envEmpty then "" else renderedParams

/-- Mirrors `make_wheres` at `base/show.jl:864-892`. -/
def makeWheres (context outer env : List Nat) : List Nat :=
  let seen := context.eraseDups
  let outerNew := outer.filter fun x => !seen.contains x
  let seen' := (seen ++ outerNew).eraseDups
  let inner := env.reverse.filter fun x => !seen'.contains x
  inner.reverse ++ outerNew

/-- Mirrors `show_wheres` at `base/show.jl:894-906`. -/
def showWheres (wheres : List String) : String := match wheres with
  | [] => ""
  | [w] => " where " ++ w
  | ws => " where {" ++ ", ".intercalate ws ++ "}"

/-- Mirrors the boolean wrapper `show_typealias(io, x)` at
`base/show.jl:908-915`. -/
def showTypealiasLookup (alias : Option String) : Bool × String := match alias with
  | none => (false, "")
  | some text => (true, text)

structure UnionAliasCandidate where
  text : String
  score : Nat × Int
  subsumedByEarlier : Bool
  deriving Repr, DecidableEq

/-- Mirrors the empty handling, score ordering, and subsumption keep pass in
`make_typealiases` at `base/show.jl:917-1000`. -/
def makeTypealiases (isAny isTuple : Bool) (candidates : List UnionAliasCandidate) : List String :=
  if isAny || isTuple then []
  else
    (candidates.mergeSort fun a b => a.score.1 > b.score.1 ||
      (a.score.1 = b.score.1 && a.score.2 > b.score.2)).filterMap fun c =>
        if c.subsumedByEarlier then none else some c.text

structure UnionPiece where
  text : String
  isTypeVar : Bool
  covered : Bool
  deriving Repr, DecidableEq

/-- Mirrors `show_unionaliases` at `base/show.jl:1002-1044`. -/
def showUnionaliases (pieces : List UnionPiece) (aliases : List String) : Bool × String :=
  if aliases.isEmpty then (false, "")
  else
    let ordinary := pieces.filter fun p => !p.isTypeVar && !p.covered
    let tvars := pieces.filter fun p => p.isTypeVar
    if ordinary.isEmpty && tvars.isEmpty && aliases.length = 1 then (true, aliases.head!)
    else (true, "Union{" ++ ", ".intercalate ((ordinary.map (·.text)) ++ aliases ++ (tvars.map (·.text))) ++ "}")

/-- Mirrors the alias annotation and singleton-function hint in
`show(::MIME"text/plain", ::Type)` at `base/show.jl:1046-1069`. -/
def showTypePlain (normal : String) (printNoParams hasAlias compact globalFunction : Bool)
    (symbol : String) : String :=
  if !printNoParams && hasAlias then
    normal ++ if compact then "" else " (alias for " ++ normal ++ ")"
  else normal ++ if !compact && globalFunction then
    " (singleton type of function " ++ symbol ++ ", subtype of Function)" else ""

/-- Mirrors `show_typeegal` at `base/show.jl:1071-1075`. -/
def showTypeEgal (parameter : String) : String := "Core.TypeEgal{" ++ parameter ++ "}"

inductive AnyTypeView where
  | bottom
  | typeEgal (parameter : String)
  | typeEq (parameter : String)
  | other (rendered : String)
  deriving Repr, DecidableEq

/-- Mirrors `show(::Core.AnyType)` at `base/show.jl:1076-1086`. -/
def showAnyType : AnyTypeView → String
  | .bottom => "Union{}"
  | .typeEgal p => showTypeEgal p
  | .typeEq p => "Type{" ++ p ++ "}"
  | .other s => s

/-- Mirrors `show_typeeq` at `base/show.jl:1091-1095`. -/
def showTypeEq (compact : Bool) (parameter : String) : String :=
  (if compact then "Type{" else "TypeEq{") ++ parameter ++ "}"

inductive ShowTypeBranch where
  | typeEgal (parameter : String)
  | withoutParams (name : String)
  | alias (text : String)
  | typeEq (parameter : String)
  | datatype (text : String)
  | union (aliasesWorked : Bool) (text : String)
  | bottom
  | unionall (body : String) (wheres : List String)
  deriving Repr, DecidableEq

/-- Mirrors the dispatch order of `_show_type` at `base/show.jl:1096-1152`. -/
def showType (compact : Bool) : ShowTypeBranch → String
  | .typeEgal p => showTypeEgal p
  | .withoutParams n => n
  | .alias s => if compact then s else s
  | .typeEq p => showTypeEq compact p
  | .datatype s => s
  | .union worked s => if compact && worked then s else "Union" ++ s
  | .bottom => "Union{}"
  | .unionall body wheres => body ++ showWheres wheres

structure VisibilityView where
  deprecated : Bool
  fromDefined : Bool
  parentDefined : Bool
  sameBinding : Bool
  importedChainReachesParent : Bool
  bothDefinedConst : Bool
  sameRestriction : Bool
  deriving Repr, DecidableEq

/-- Mirrors `isvisible` at `base/show.jl:1159-1177`. -/
def isVisible (v : VisibilityView) : Bool :=
  if v.deprecated || !v.fromDefined || !v.parentDefined then false
  else if v.sameBinding || v.importedChainReachesParent then true
  else v.bothDefinedConst && v.sameRestriction

structure GlobalFunctionView where
  hasName : Bool
  concreteWrapper : Bool
  isDataTypeName : Bool
  containsHash : Bool
  containsAt : Bool
  hasModule : Bool
  defined : Bool
  constant : Bool
  valueHasWrapperType : Bool
  deriving Repr, DecidableEq

/-- Mirrors `is_global_function` at `base/show.jl:1179-1189`. -/
def isGlobalFunction (v : GlobalFunctionView) : Bool :=
  v.hasName && v.concreteWrapper && !v.isDataTypeName && !v.containsHash && !v.containsAt &&
    v.hasModule && v.defined && v.constant && v.valueHasWrapperType

structure WorldPartition where
  definedConst : Bool
  valueIsSubtype : Bool
  minWorld : Int
  maxWorld : Option Int
  deriving Repr, DecidableEq

/-- Mirrors the partition walk in `check_world_bounded` at
`base/show.jl:1191-1209`; `none` for `maxWorld` represents `typemax(UInt)`. -/
def checkWorldBounded : List WorldPartition → Option (Int × Int)
  | [] => none
  | p :: ps => if p.definedConst && p.valueIsSubtype then
      match p.maxWorld with | none => none | some m => some (p.minWorld, m)
    else checkWorldBounded ps

structure TypeNameView where
  unionAllName : Bool
  globalFunction : Bool
  compact : Bool
  prefixModule : Bool
  moduleText : String
  symbolText : String
  symbolStartsIdentifier : Bool
  quotedSymbol : Bool
  world : Option (Int × Int)
  deriving Repr, DecidableEq

/-- Mirrors `show_type_name` at `base/show.jl:1211-1246`. -/
def showTypeName (v : TypeNameView) : String :=
  if v.unionAllName then "UnionAll"
  else
    let prefixText := if v.globalFunction then "typeof(" else ""
    let worldOpen := if v.world.isSome then "@world(" else ""
    let modulePrefix := if !v.compact && v.prefixModule then
      v.moduleText ++ "." ++ if v.globalFunction && !v.symbolStartsIdentifier then
        if v.quotedSymbol then ":(" else ":" else "" else ""
    let worldClose := match v.world with | none => "" | some w => ", " ++ toString w.1 ++ ":" ++ toString w.2 ++ ")"
    let quoteClose := if !v.compact && v.prefixModule && v.globalFunction &&
      !v.symbolStartsIdentifier && v.quotedSymbol then ")" else ""
    prefixText ++ worldOpen ++ modulePrefix ++ v.symbolText ++ worldClose ++ quoteClose ++
      (if v.globalFunction then ")" else "")

structure KwargsView where
  pairsName : Bool
  fourParameters : Bool
  firstSymbol : Bool
  fourthNamedTuple : Bool
  fourthHasTwoParameters : Bool
  typesDataType : Bool
  secondMatchesEltype : Bool
  symbolsTuple : Bool
  thirdNothing : Bool
  result : String
  deriving Repr, DecidableEq

/-- Mirrors `maybe_kws_nt` at `base/show.jl:1248-1264`. -/
def maybeKwsNt (v : KwargsView) : Option String :=
  if v.pairsName && v.fourParameters && v.firstSymbol && v.fourthNamedTuple &&
      v.fourthHasTwoParameters && v.typesDataType && v.secondMatchesEltype &&
      v.symbolsTuple && v.thirdNothing then some v.result else none

inductive VarargKind where | none | fixed (n : Nat) | bound (n : String) | unbound
  deriving Repr, DecidableEq

structure DatatypeView where
  tuple : Bool
  namedTuple : Bool
  tupleParams : List String
  homogeneousTail : Nat
  varargKind : VarargKind
  namedTupleValid : Bool
  namedTupleText : String
  backtrace : Bool
  kwargsText : Option String
  ordinaryText : String
  deriving Repr, DecidableEq

def renderTupleType (params : List String) (tail : Nat) (kind : VarargKind) : String :=
  if params.isEmpty then "Tuple{}"
  else
    let fulln := match kind with | .fixed n => params.length + n - 1 | _ => params.length
    let last := params.getLast!
    let useNTuple := match kind with
      | .bound _ => params.length = 1 && tail = 1
      | .fixed _ => tail = fulln && 3 < tail
      | .none => tail = fulln && 3 < tail
      | .unbound => false
    if useNTuple then
      let ntext := match kind with | .bound n => n | _ => toString fulln
      "NTuple{" ++ ntext ++ ", " ++ last ++ "}"
    else
      let headlen := if 3 < tail then fulln - tail else fulln
      let shownHead := (List.range headlen).map fun i =>
        if let .fixed _ := kind then if params.length ≤ i then last else params[i]!
        else params[i]!
      let tailText := if headlen < fulln then
        (if headlen > 0 then ["Vararg{" ++ last ++ ", " ++ toString (fulln - headlen) ++ "}"]
         else ["Vararg{" ++ last ++ ", " ++ toString fulln ++ "}"])
        else []
      "Tuple{" ++ ", ".intercalate (shownHead ++ tailText) ++ "}"

/-- Mirrors `show_datatype` at `base/show.jl:1266-1360`. -/
def showDatatype (v : DatatypeView) : String :=
  if v.tuple then renderTupleType v.tupleParams v.homogeneousTail v.varargKind
  else if v.namedTuple && v.namedTupleValid then "@NamedTuple{" ++ v.namedTupleText ++ "}"
  else if v.backtrace && v.kwargsText.isSome then "@Kwargs{" ++ v.kwargsText.get! ++ "}"
  else v.ordinaryText

/-- Mirrors both `show_supertypes` methods at `base/show.jl:1378-1386`. -/
def showSupertypes (types : List String) : String := " <: ".intercalate types

/-- Models the expansion produced by `@show` at `base/show.jl:1406-1414`.
Each pair is the source expression text and its evaluated `repr`. -/
def showMacro (expressions : List (String × String)) : List String × Option String :=
  (expressions.map fun e => e.1 ++ " = " ++ e.2, expressions.getLast?.map (·.2))

/-- Mirrors `show(::Core.TypeName)` at `base/show.jl:1416-1420`. -/
def showTypeNameObject (name : String) : String := "typename(" ++ name ++ ")"

/-! ## Source information and AST helpers -/

def duplicateCounts (names : List String) : List (String × Nat) :=
  names.foldl (fun counts name =>
    let n := (counts.find? (·.1 == name)).map (·.2) |>.getD 0
    (name, n + 1) :: counts.filter (·.1 != name)) []

/-- Mirrors `sourceinfo_slotnames` at `base/show.jl:1495-1516`. -/
def sourceinfoSlotnames (slotnames : List String) : List String :=
  let counts := duplicateCounts slotnames
  slotnames.mapIdx fun i name =>
    if name == "#unused#" then "_"
    else if name.isEmpty || (counts.find? (·.1 == name)).any (fun p => p.2 > 1) then
      name ++ "@_" ++ toString (i + 1)
    else name

inductive MethodInstanceView where
  | generator (methodText : String)
  | method (callText : String)
  | thunk (detail : Option (String × String))
  deriving Repr, DecidableEq

/-- Mirrors `show_mi` at `base/show.jl:1533-1560`. -/
def showMethodInstance (fromStackframe : Bool) : MethodInstanceView → String
  | .generator m => "MethodInstance generator for " ++ m
  | .method c => "MethodInstance for " ++ c
  | .thunk detail => "Toplevel MethodInstance thunk" ++ match detail with
      | some (definition, line) =>
        if fromStackframe then "" else " from " ++ definition ++ " starting at " ++ line
      | none => ""

/-- Mirrors `show(::CodeInstance)` at `base/show.jl:1519-1531`. -/
def showCodeInstance (mi : String) (abiOverridden foreign : Bool) : String :=
  "CodeInstance for " ++ mi ++ (if abiOverridden then " (ABI Overridden)" else "") ++
    (if foreign then " (foreign)" else "")

/-- Mirrors the simple `ExprNode` and `show_unquoted` forwarding methods at
`base/show.jl:1666-1671`. -/
def printExprNode (d : UData) (o : OpData) (ex : JE) : PO :=
  showUnquoted d o (16 * ex.size + 16) false false ex 0 (-1) 0
def showExprNode (d : UData) (o : OpData) (ex : JE) : PO :=
  showQuoteExpr d o (16 * ex.size + 16) true false ex 0 (-1)
def showUnquoted0 (d : UData) (o : OpData) (ex : JE) : PO :=
  showUnquoted d o (16 * ex.size + 16) false false ex 0 0 0
def showUnquotedIndent (d : UData) (o : OpData) (ex : JE) (indent : Nat) : PO :=
  showUnquoted d o (16 * ex.size + 16) false false ex indent 0 0
def showUnquotedFallback (rendered : String) : String := rendered
def showUnquotedQuoteLevel (d : UData) (o : OpData) (ex : JE) (indent : Nat) (prec : Int) : PO :=
  showUnquoted d o (16 * ex.size + 16) false false ex indent prec 0

/-- Mirrors the two `operator_precedence` methods at `base/show.jl:1713-1714`. -/
def operatorPrecedenceSymbol (runtime : String → Int) (symbol : String) : Int := runtime symbol
def operatorPrecedenceAny : Int := 0

inductive Associativity where | left | right | none
  deriving Repr, DecidableEq

/-- Mirrors `operator_associativity` at `base/show.jl:1739-1748`. -/
def operatorAssociativity (precedence arrow assignment control pair power comparison : Int)
    (unaryOnly rightSpelling neutralSpelling : Bool) : Associativity :=
  if precedence ∈ [arrow, assignment, control, pair, power] || unaryOnly || rightSpelling then .right
  else if precedence ∈ [0, comparison] || neutralSpelling then .none
  else .left

/-- Mirrors the three `is_quoted` methods at `base/show.jl:1750-1752`. -/
def isQuotedOther : Bool := false
def isQuotedQuoteNode : Bool := true
def isQuotedExpr (head : String) (nargs : Nat) : Bool := (head == "quote" || head == "inert") && nargs = 1

/-- Mirrors the `unquoted` methods at `base/show.jl:1754-1755`. -/
def unquotedValue (value : String) : String := value
def unquotedExpr (args : List String) : Option String := args.head?

/-- Mirrors `emphasize` at `base/show.jl:1762-1764`; the result records the
selected printer, text, color, and bold flag. -/
def emphasize (colorEnabled : Bool) (text color : String) : String × String × Bool :=
  if colorEnabled then ("styled", text ++ ":" ++ color, true)
  else ("plain", text.toUpper, false)

/-- Mirrors the three `show_linenumber` methods at `base/show.jl:1766-1768`. -/
def showLineNumber (line : Int) (file : Option String := none) : String := match file with
  | none => "#= line " ++ toString line ++ " =#"
  | some f => "#= " ++ f ++ ":" ++ toString line ++ " =#"

/-- Mirrors the three `show_block` methods at `base/show.jl:1771-1797` at the
level of already-rendered arguments and body statements. -/
def showBlockText (head : String) (args body : List String) (indent : Nat) (moduleHead : Bool) : String :=
  let argsText := if args.isEmpty then "" else " " ++ (if head == "elseif" then " " else ", ").intercalate args
  let bodyIndent := if moduleHead then indent else indent + 4
  head ++ argsText ++ String.join (body.map fun ex => "\n" ++ String.ofList (List.replicate bodyIndent ' ') ++ ex) ++
    "\n" ++ String.ofList (List.replicate indent ' ')

/-- Mirrors `show_enclosed_list` at `base/show.jl:1828-1832`. -/
def showEnclosedListText (op cl sep : String) (items : List String) : String :=
  op ++ sep.intercalate items ++ cl

inductive WarnClass where | invalid | strong | mild | normal
  deriving Repr, DecidableEq

/-- Mirrors `show_unquoted(::SSAValue)` at `base/show.jl:1880-1894`. -/
def showSSAValue (id : Int) (cls : WarnClass) : String × String × Bool :=
  let text := "%" ++ toString id
  match cls with
  | .invalid => (text, "red", false)
  | .strong => (text, "light_red", true)
  | .mild => (text, "warn", true)
  | .normal => (text, "plain", false)

/-- Mirrors the one-line IR-node methods at `base/show.jl:1895-1900`. -/
def showSymbolNode (shown : String) : String := shown
def showLineNode (line : Int) (file : Option String) : String := showLineNumber line file
def showGotoNode (label : Int) : String := "goto %" ++ toString label
def showGlobalRefNode (shown : String) : String := shown
def showBindingPartitionNode (ownerGlobalRef : String) : String := ownerGlobalRef

/-- Mirrors `show_globalref` at `base/show.jl:1902-1912`. -/
def showGlobalRef (moduleName symbolShown : String) (identifier startsAt operator quoted : Bool) : String :=
  let needsQuote := !identifier && !startsAt
  let parens := needsQuote && (!operator || quoted)
  moduleName ++ "." ++ (if needsQuote then ":" else "") ++
    (if parens then "(" else "") ++ symbolShown ++ (if parens then ")" else "")

/-- Mirrors `show_unquoted(::SlotNumber)` at `base/show.jl:1914-1922`. -/
def showSlotNumber (id : Nat) (slotnames : Option (List String)) : String := match slotnames with
  | some names => if id > 0 && id ≤ names.length then names[id - 1]! else "_" ++ toString id
  | none => "_" ++ toString id

/-- Mirrors `show_unquoted(::QuoteNode)` at `base/show.jl:1924-1935`. -/
def showQuoteNode (symbol : Option String) (shownValue : String) : String := match symbol with
  | some s => s
  | none => "$(QuoteNode(" ++ shownValue ++ "))"

/-- Mirrors the loop structure of `show_generator` at `base/show.jl:1962-1981`.
`ranges` is in the order collected from nested `:flatten` nodes. -/
def showGenerator (body : String) (ranges : List (List String)) : String :=
  body ++ String.join (ranges.map fun r => " for " ++ ", ".intercalate r)

inductive ImportExpr where
  | symbol (name : String)
  | path (parts : List String)
  | colon (base : ImportExpr) (names : List ImportExpr)
  | as (path alias : ImportExpr)
  | other (shown : String)
  deriving Repr

/-- Mirrors `valid_import_path` at `base/show.jl:1983-1988`. -/
def validImportPath : ImportExpr → Bool → Bool
  | .as path _, true => validImportPath path false
  | .path parts, _ => !parts.isEmpty
  | _, _ => false

/-- Mirrors `show_import_path` at `base/show.jl:1990-2020`. -/
def showImportPath : ImportExpr → String
  | .symbol name => name
  | .path parts => ".".intercalate (parts.map fun p => if p == ".." then "(..)" else p)
  | .colon base names => showImportPath base ++ ": " ++ ", ".intercalate (names.map showImportPath)
  | .as path alias => showImportPath path ++ " as " ++ showImportPath alias
  | .other shown => shown

/-- Mirrors `allow_macroname` at `base/show.jl:2023-2032`. -/
def allowMacroname (symbolStartsAt globalRef quotedDot : Bool) (shown : String) : String :=
  if symbolStartsAt || globalRef || quotedDot then "macroname(" ++ shown ++ ")" else shown

/-- Mirrors the four `is_core_macro` methods at `base/show.jl:2034-2037`. -/
def isCoreMacroGlobal (isCore : Bool) (name macroName : String) : Bool := isCore && name == macroName
def isCoreMacroOther (_macroName : String) : Bool := false

/-- Mirrors `show_unquoted_expr_fallback` at `base/show.jl:2043-2051`. -/
def showExprFallback (head : String) (args : List String) : String :=
  "$(Expr(" ++ head ++ String.join (args.map (", " ++ ·)) ++ "))"

/-! ## Stacktrace and IR display -/

/-- Mirrors both `demangle_function_name` methods at `base/show.jl:2608-2616`. -/
def demangleFunctionName (name : String) : String :=
  match name.splitOn "#" with
  | first :: _ :: _ => if first.isEmpty then name else first
  | _ => name

inductive SignatureFunctionView where
  | globalFunction (qualified needsModule : Bool) (moduleName name : String)
  | typeObject (needsParens : Bool) (text : String)
  | other (typeText argName : String) (html : Bool)
  deriving Repr, DecidableEq

/-- Mirrors `show_signature_function` at `base/show.jl:2620-2643`. -/
def showSignatureFunction : SignatureFunctionView → String
  | .globalFunction qualified needsModule mod name =>
      (if qualified && needsModule then mod ++ "." else "") ++ name
  | .typeObject parens text => (if parens then "(" else "") ++ text ++ (if parens then ")" else "")
  | .other typ arg html => if html then "(" ++ arg ++ "::<b>" ++ typ ++ "</b>)"
      else "(" ++ arg ++ "::" ++ typ ++ ")"

/-- Mirrors `print_within_stacktrace` at `base/show.jl:2645-2651`. -/
def printWithinStacktrace (backtrace : Bool) (text color : String) (bold : Bool) : String × String × Bool :=
  if backtrace then (text, color, bold) else (text, "plain", false)

structure CallArg where
  name : Option String
  typeText : String
  deriving Repr, DecidableEq

structure KwArg where
  name : String
  typeText : String
  splat : Bool
  deriving Repr, DecidableEq

/-- Mirrors the output construction in `show_tuple_as_call` at
`base/show.jl:2653-2710`. -/
def showTupleAsCall (functionText : String) (args : List CallArg) (kwargs : Option (List KwArg))
    (whereText : String) : String :=
  let positional := args.map fun a => a.name.getD "" ++ "::" ++ a.typeText
  let kwtext := match kwargs with
    | none => ""
    | some ks => "; " ++ ", ".intercalate (ks.map fun k => k.name ++ if k.splat then "..." else "::" ++ k.typeText)
  functionText ++ "(" ++ ", ".intercalate positional ++ kwtext ++ ")" ++ whereText

/-- Mirrors `type_limited_string_from_context` at `base/show.jl:2712-2723`.
`limited` is the result of the separately modelled `type_depth_limit` call. -/
def typeLimitedStringFromContext (flagPresent : Bool) (original limited : String) : String × Bool :=
  if flagPresent then (limited, limited.utf8ByteSize < original.utf8ByteSize) else (original, false)

/-- Mirrors the two `print_type_bicolor` methods at `base/show.jl:2818-2838`.
The tuple records the outer, inner, and final ellipsis pieces. -/
def printTypeBicolor (str : String) (braceIndex : Option Nat) (endsEllipsis useColor : Bool) : List (String × String) :=
  if !useColor then [(str, "plain")]
  else match braceIndex with
    | none => [(str, "outer")]
    | some i =>
      let outer := str.toList.take i
      let inner := str.toList.drop i
      if endsEllipsis && inner.length ≥ 3 then
        [(String.ofList outer, "outer"), (String.ofList (inner.dropLast.dropLast.dropLast), "inner"), ("...", "outer")]
      else [(String.ofList outer, "outer"), (String.ofList inner, "inner")]

inductive BindingExpr where
  | value (text : String)
  | quote (value : String)
  | symbol (name : String)
  | dot (parent : BindingExpr) (name : String)
  | global (defined constant isModule : Bool) (moduleName name : String)
  deriving Repr, DecidableEq

/-- Mirrors the five `resolvebinding` methods at `base/show.jl:2840-2858`. -/
def resolveBinding : BindingExpr → Option String
  | .value text => some text
  | .quote value => some value
  | .symbol name => some name
  | .dot parent name => (resolveBinding parent).map (· ++ "." ++ name)
  | .global defined constant isModule mod name =>
      if defined && constant && isModule then some (mod ++ "." ++ name) else none

/-- Mirrors `ismodulecall` at `base/show.jl:2860-2864`. -/
def isModuleCall (callHead getfieldFunction resolvedModule : Bool) : Bool :=
  callHead && getfieldFunction && resolvedModule

/-- Mirrors `show(::TypeVar)` and its nested `show_bound` at
`base/show.jl:2866-2899`. -/
def showTypeVar (name lower upper : String) (inEnv lowerBottom upperAny lowerParens upperParens : Bool) : String :=
  let lb := (if lowerParens then "(" else "") ++ lower ++ (if lowerParens then ")" else "")
  let ub := (if upperParens then "(" else "") ++ upper ++ (if upperParens then ")" else "")
  let first := if !inEnv && !lowerBottom then
    if upperAny then name ++ ">:" ++ lb else lb ++ "<:" ++ name
    else name
  first ++ if !inEnv && !upperAny then "<:" ++ ub else ""

/-- Mirrors `show(::Core.TypeofVararg)` at `base/show.jl:2901-2912`. -/
def showVararg (typeText : Option String) (lengthText : Option String) : String := match typeText with
  | none => "Vararg"
  | some t => "Vararg{" ++ t ++ (lengthText.map (", " ++ ·)).getD "" ++ "}"

/-- Mirrors `show(::CodeInfo)` at `base/show.jl:2916-2929`. -/
def showCodeInfo (ir : String) : String := "CodeInfo(\n" ++ ir ++ ")"

/-- Mirrors the Argument wrapper at `base/show.jl:2931`. -/
def showArgument (slot : Nat) (names : Option (List String)) : String := showSlotNumber slot names

/-- Mirrors `show_unquoted_phinode` at `base/show.jl:2933-2947`. -/
def showPhiNode (edges : List Int) (values : List (Option String)) (prefixText : String := "%") : String :=
  let pairs := List.zipWith (fun e v => prefixText ++ toString e ++ " => " ++ v.getD "#undef") edges values
  "φ (" ++ ", ".intercalate pairs ++ ")"

/-- Mirrors `show_unquoted(::PhiCNode)` at `base/show.jl:2949-2957`. -/
def showPhiCNode (values : List String) : String := "φᶜ (" ++ ", ".intercalate values ++ ")"

/-- Mirrors `show_unquoted(::PiNode)` at `base/show.jl:2959-2965`. -/
def showPiNode (value typeText : String) : String := "π (" ++ value ++ ", " ++ typeText ++ ")"

/-- Mirrors `show_unquoted(::UpsilonNode)` at `base/show.jl:2967-2973`. -/
def showUpsilonNode (value : Option String) : String := "ϒ (" ++ value.getD "#undef" ++ ")"

/-- Mirrors `show_unquoted(::ReturnNode)` at `base/show.jl:2975-2982`. -/
def showReturnNode (value : Option String) : String := match value with
  | none => "unreachable"
  | some v => "return " ++ v

/-- Mirrors both GotoIfNot methods at `base/show.jl:2984-2988`. -/
def showGotoIfNot (dest : Int) (condition : String) (prefixText : String := "%") : String :=
  "goto " ++ prefixText ++ toString dest ++ " if not " ++ condition

/-! ## Opaque closures, bindings, and partitions -/

/-- Mirrors both OpaqueClosure show methods at `base/show.jl:3443-3452`. -/
def showOpaqueClosure (arguments result : String) : String := arguments ++ "->◌::" ++ result

inductive PartitionKind where
  | backdatedConst | const | constImport | undefConst | guard | failed | declared
  | implicitGlobal (target : String) | implicitConst | explicitUsing (target : String)
  | imported (target : String) | globalVar (typeText : String)
  deriving Repr, DecidableEq

structure PartitionView where
  minWorld : Nat
  maxWorld : Option Nat
  flags : List String
  kind : PartitionKind
  deriving Repr, DecidableEq

def partitionKindText : PartitionKind → String
  | .backdatedConst => "backdated constant binding"
  | .const => "constant binding"
  | .constImport => "constant binding (declared with `import`)"
  | .undefConst => "undefined const binding"
  | .guard => "undefined binding - guard entry"
  | .failed => "ambiguous binding - guard entry"
  | .declared => "weak global binding declared using `global` (implicit type Any)"
  | .implicitGlobal target => "implicit `using` resolved to global " ++ target
  | .implicitConst => "implicit `using` resolved to constant"
  | .explicitUsing target => "explicit `using` from " ++ target
  | .imported target => "explicit `import` from " ++ target
  | .globalVar typ => "global variable with type " ++ typ

/-- Mirrors `print_partition` at `base/show.jl:3455-3505`. -/
def printPartition (p : PartitionView) : String :=
  toString p.minWorld ++ ":" ++ (p.maxWorld.map toString).getD "∞" ++
    (if p.flags.isEmpty then "" else " [" ++ ",".intercalate p.flags ++ "]") ++
    " - " ++ partitionKindText p.kind

/-- Mirrors the two BindingPartition show methods at `base/show.jl:3507-3517`. -/
def showPartition (owner : String) (p : PartitionView) (plain : Bool) : String :=
  if plain then "BindingPartition for " ++ owner ++ "\n   " ++ printPartition p
  else "BindingPartition(for " ++ owner ++ ": " ++ printPartition p ++ ")"

/-- Mirrors `show(::MIME"text/plain", ::Binding)` at
`base/show.jl:3519-3536`. -/
def showBinding (globalRef : String) (partitions : Option (List PartitionView)) : String := match partitions with
  | none => "Binding " ++ globalRef ++ " - No partitions"
  | some ps => "Binding " ++ globalRef ++ String.join (ps.map fun p => "\n   " ++ printPartition p)

end JuliaLean.ShowCov.Remaining
