import JuliaLean.ShowCov.MethodSupport
import JuliaLean.ShowCov.Truncate
import JuliaLean.ShowCov.IOContext
import JuliaLean.ShowCov.Values
import JuliaLean.ShowCov.Containers
import JuliaLean.ShowCov.Remaining
import JuliaLean.Show.ExprPrint
import JuliaLean.Show.Symbol

namespace JuliaLean.ShowCov.Methods.ShowFile

set_option linter.unusedVariables false

open JuliaLean.Registry
open JuliaLean.ShowCov.Methods
open JuliaLean.ShowCov
open JuliaLean.Show
open JuliaLean.Strings

structure Capture where
  matchText : List Char
  nextIndex : Nat
  deriving DecidableEq, Repr

def captureIter : List Capture → Option (Capture × (Nat × List Capture))
  | [] => none
  | capture :: rest => some (capture, (capture.nextIndex, rest))

def ansiIterStep (captures : List Capture) (i : Nat) :
    Option ((Nat × Truncate.Tok) ×
      (Nat × Option (Capture × (Nat × List Capture)))) :=
  match captureIter captures with
  | none => none
  | some (capture, (j, newState)) =>
    let token := if (capture.matchText.map Char.utf8Size).sum = 1 then
      match capture.matchText with
      | [c] => Truncate.Tok.ch c
      | _ => Truncate.Tok.ansi capture.matchText
    else Truncate.Tok.ansi capture.matchText
    some ((i, token), (j, captureIter newState))

structure RangeValue where
  id : Nat
  deriving DecidableEq, Repr

structure RangeRuntime where
  render : RangeValue → String
  summary : RangeValue → String
  printLinRange : RangeValue → String
  printLogRange : RangeValue → String
  isempty : RangeValue → Bool

structure WrapperValue where
  id : Nat
  deriving DecidableEq, Repr

structure WrapperRuntime where
  render : WrapperValue → String

structure TypeNameValue where
  id : Nat
  name : String
  singletonName : String
  moduleName : String
  moduleFieldDefined : Bool
  moduleGlobalDefined : Bool
  moduleBindingConst : Bool
  globalValueId : Nat
  deriving DecidableEq, Repr

structure DataTypeValue where
  id : Nat
  typeName : TypeNameValue
  deriving DecidableEq, Repr

structure BindingPartitionValue where
  kind : Nat
  restriction : Nat
  deriving DecidableEq, Repr

structure SelfRuntime where
  worldAge : Nat
  parentModule : DataTypeValue → String
  lookupBindingPartition : Nat → String → String → BindingPartitionValue
  bindingKind : BindingPartitionValue → Nat
  backdatedConstKind : Nat
  typeOf : Nat → Nat
  isDefinedGlobal : String → String → Bool
  getGlobal : String → String → Nat

def isSelfBody (runtime : SelfRuntime) (ft : DataTypeValue) : Bool :=
  let ftname := ft.typeName
  let name := ftname.singletonName
  if ftname.name == name then false
  else
    let mod := runtime.parentModule ft
    let bpart := runtime.lookupBindingPartition runtime.worldAge mod name
    if runtime.bindingKind bpart = runtime.backdatedConstKind then
      ft.id = runtime.typeOf bpart.restriction
    else runtime.isDefinedGlobal mod name &&
      ft.id = runtime.typeOf (runtime.getGlobal mod name)

inductive DisplayFunctionKind where
  | intrinsic
  | builtin
  | generic
  deriving DecidableEq, Repr

structure FunctionValue where
  id : Nat
  datatype : DataTypeValue
  kind : DisplayFunctionKind
  methods : List Nat
  deriving DecidableEq, Repr

structure FunctionRuntime where
  selfRuntime : SelfRuntime
  render : FunctionValue → String
  renderType : DataTypeValue → String
  bitcastInt32 : FunctionValue → Int
  visibleFrom : String → String → String → Bool
  fallbackDefault : FunctionValue → String
  fallbackShow : FunctionValue → String

def showFunctionBody (runtime : FunctionRuntime) (compact : Bool)
    (f : FunctionValue) : String :=
  if compact then runtime.render f
  else
    let ft := f.datatype
    let name := ft.typeName.singletonName
    match f.kind with
    | .intrinsic =>
      runtime.render f ++ " (intrinsic function #" ++
        toString (runtime.bitcastInt32 f) ++ ")"
    | .builtin => name ++ " (built-in function)"
    | .generic =>
      let n := f.methods.length
      let methodWord := if n = 1 then "method" else "methods"
      let stringName := name
      let shownName := if isSelfBody runtime.selfRuntime ft || stringName.contains '#' then
        stringName else "(::" ++ runtime.renderType ft ++ ")"
      let what := if shownName.startsWith "@" then "macro" else "generic function"
      shownName ++ " (" ++ what ++ " with " ++ toString n ++ " " ++ methodWord ++ ")"

inductive FunctionFallback where
  | showDefault
  | show
  deriving DecidableEq, Repr

structure FunctionIO where
  moduleName : String
  compact : Bool
  deriving DecidableEq, Repr

def functionFallback (runtime : FunctionRuntime) : FunctionFallback → FunctionValue → String
  | .showDefault, function => runtime.fallbackDefault function
  | .show, function => runtime.fallbackShow function

def showFunctionCore (runtime : FunctionRuntime) (io : FunctionIO)
    (function : FunctionValue) (compact : Bool) (fallback : FunctionFallback) : String :=
  let fname := function.datatype.typeName
  if fname.name == fname.singletonName then functionFallback runtime fallback function
  else if compact then fname.singletonName
  else if fname.moduleFieldDefined && fname.moduleGlobalDefined &&
      fname.moduleBindingConst && fname.globalValueId = function.id then
    let qualifier := if runtime.visibleFrom fname.singletonName fname.moduleName io.moduleName ||
        fname.moduleName = io.moduleName then "" else fname.moduleName ++ "."
    qualifier ++ fname.singletonName
  else functionFallback runtime fallback function

structure ActiveReplValue where
  id : Nat
  deriving DecidableEq, Repr

structure ActiveModuleRuntime where
  isPureContext : Unit → Bool
  activeReplDefined : Unit → Bool
  activeRepl : Option ActiveReplValue
  invokeLatest : ActiveReplValue → String

def activeModuleBody (runtime : ActiveModuleRuntime) : R String :=
  if runtime.isPureContext () then
    .error (.errorException "active_module() should not be called from a pure context")
  else match runtime.activeReplDefined (), runtime.activeRepl with
    | false, _ => .ok "Main"
    | true, none => .ok "Main"
    | true, some repl => .ok (runtime.invokeLatest repl)

structure TypeObject where
  id : Nat
  deriving DecidableEq, Repr

inductive UnwrappedType where
  | dataType (wrapperId : Nat)
  | other
  deriving DecidableEq, Repr

structure TypeRuntime where
  unwrapUnionall : TypeObject → UnwrappedType

def printWithoutParamsBody (runtime : TypeRuntime) (value : TypeObject) : Bool :=
  match runtime.unwrapUnionall value with
  | .dataType wrapperId => wrapperId = value.id
  | .other => false

structure TypeVarValue where
  id : Nat
  name : String
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

inductive TypeBindingValue where
  | typeVar (value : TypeVarValue)
  | other (id : Nat)
  deriving DecidableEq, Repr

structure TypeVarContext where
  dict : List (String × TypeBindingValue)
  deriving DecidableEq, Repr

structure TypeVarRuntime where
  hasTypevar : TypeObject → TypeVarValue → Bool

def ioHasTypevarBody (runtime : TypeVarRuntime) (io : TypeVarContext)
    (name : String) (value : TypeObject) : Bool :=
  io.dict.any fun binding =>
    binding.1 == "unionall_env" && match binding.2 with
    | .typeVar typevar => typevar.name == name && runtime.hasTypevar value typevar
    | .other _ => false

inductive TypeParameterValue where
  | anyType (shape : Remaining.TypeShape)
  | typeVar (shape : Remaining.TypeShape)
  | nonType (id : Nat)

structure ParameterizedTypeValue where
  id : Nat
  deriving DecidableEq, Repr

structure ParameterRuntime where
  typeParameter : ParameterizedTypeValue → TypeParameterValue

def modulesTypeEqBody (runtime : ParameterRuntime) (value : ParameterizedTypeValue) : List String :=
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []

structure FreeTypevarRuntime where
  hasFreeTypevars : TypeObject → Bool
  findFreeTypevars : TypeObject → List TypeVarValue

def hasOtherFreeTypevarsBody (runtime : FreeTypevarRuntime) (value : TypeObject)
    (freeBefore : List TypeVarValue) : Bool :=
  if !runtime.hasFreeTypevars value then false
  else (runtime.findFreeTypevars value).any fun freeVar =>
    !(freeBefore.any fun previous => previous.id == freeVar.id)

inductive TypeExpr where
  | atom (id : Nat)
  | unionAll (freeVar : TypeVarValue) (body : TypeExpr)
  deriving DecidableEq, Repr

def reapplyUnionallBody (context : Option TypeVarContext) (value : TypeExpr) : TypeExpr :=
  match context with
  | none => value
  | some io => io.dict.foldl (fun result binding =>
      if binding.1 == "unionall_env" then match binding.2 with
        | .typeVar freeVar => .unionAll freeVar result
        | .other _ => result
      else result) value

structure SymbolValue where
  id : Nat
  deriving DecidableEq, Repr

structure SymbolRuntime where
  string : SymbolValue → String

inductive TypeSlot where
  | typeVar (value : TypeVarValue)
  | other (value : TypeObject)
  deriving DecidableEq, Repr

structure TypeRelationRuntime where
  hasTypevar : Nat → TypeVarValue → Bool
  structurallyEquivalent : Nat → Nat → Bool

def showCanElideBody (runtime : TypeRelationRuntime) (parameter : TypeVarValue)
    (wheres : List TypeVarValue) (elide : Nat) (env : List TypeSlot) (skip : Nat) : Bool :=
  if elide = 0 then false
  else match wheres[elide - 1]? with
  | none => false
  | some selected =>
    if selected.id != parameter.id then false
    else
      let laterOk := (wheres.drop elide).all fun value =>
        !runtime.hasTypevar value.lower parameter && !runtime.hasTypevar value.upper parameter
      let envOk := env.zipIdx.all fun (value, index) =>
        index + 1 = skip || match value with
        | .typeVar typevar =>
          !runtime.hasTypevar typevar.lower parameter &&
            !runtime.hasTypevar typevar.upper parameter
        | .other other => !runtime.hasTypevar other.id parameter
      laterOk && envOk

def egalVarBody (runtime : TypeRelationRuntime) (parameter : TypeVarValue) : TypeSlot → Bool
  | .other _ => false
  | .typeVar other =>
    runtime.structurallyEquivalent parameter.upper other.upper &&
      runtime.structurallyEquivalent parameter.lower other.lower

structure GlobalRefValue where
  moduleName : String
  name : String
  deriving DecidableEq, Repr

structure AliasNameRuntime where
  compact : Bool
  fromModule : Option String
  visible : String → String → String → Bool
  renderModule : String → String

def showAliasNameBody (runtime : AliasNameRuntime) (reference : GlobalRefValue) : Out :=
  let qualifier := if runtime.compact then [] else match runtime.fromModule with
    | none => [runtime.renderModule reference.moduleName, "."]
    | some origin => if runtime.visible reference.name reference.moduleName origin then []
      else [runtime.renderModule reference.moduleName, "."]
  qualifier ++ [reference.name]

structure WheresRuntime where
  render : List TypeVarValue → TypeVarValue → String

def showWheresLoop (runtime : WheresRuntime) (all : List TypeVarValue) :
    List TypeVarValue → Nat → Out
  | [], _ => []
  | parameter :: rest, index =>
    [if all.length = 1 then " where " else if index = 1 then " where {" else ", ",
      runtime.render (all.take (index - 1)) parameter] ++
    showWheresLoop runtime all rest (index + 1)

def showWheresBody (runtime : WheresRuntime) (wheres : List TypeVarValue) : Out :=
  showWheresLoop runtime wheres wheres 1 ++ if wheres.length > 1 then ["}"] else []

structure TypeParamsRuntime where
  relation : TypeRelationRuntime
  bottomId : Nat
  anyId : Nat
  render : List TypeVarValue → TypeSlot → String

def elideParamStep (runtime : TypeParamsRuntime) (env orig : List TypeSlot)
    (wheres : List TypeVarValue) (state : Nat × Nat) (index : Nat) : Nat × Nat :=
  let (n, elide) := state
  match env[index]? with
  | none | some (.other _) => state
  | some (.typeVar parameter) =>
    let can := showCanElideBody runtime.relation parameter wheres elide env (index + 1)
    let sameOrig := match orig[index]? with
      | some other => egalVarBody runtime.relation parameter other
      | none => false
    if index + 1 = n && sameOrig && can then (n - 1, elide - 1)
    else if parameter.lower = runtime.bottomId && parameter.name.contains '#' && can then
      (n, elide - 1)
    else if parameter.upper = runtime.anyId && parameter.name.contains '#' && can then
      (n, elide - 1)
    else state

def wherePosition (wheres : List TypeVarValue) (parameter : TypeVarValue) : Nat :=
  match wheres.findIdx? (fun value => value.id == parameter.id) with
  | none => 0
  | some index => index + 1

def renderTypeParam (runtime : TypeParamsRuntime) (wheres : List TypeVarValue)
    (elide : Nat) : TypeSlot → String
  | slot@(.other _) => runtime.render wheres slot
  | slot@(.typeVar parameter) =>
    if parameter.lower = runtime.bottomId && wherePosition wheres parameter > elide then
      "<:" ++ runtime.render wheres (.other ⟨parameter.upper⟩)
    else if parameter.upper = runtime.anyId && wherePosition wheres parameter > elide then
      ">:" ++ runtime.render wheres (.other ⟨parameter.lower⟩)
    else runtime.render wheres slot

def showTypeparamsBody (runtime : TypeParamsRuntime) (env orig : List TypeSlot)
    (wheres : List TypeVarValue) : Out × List TypeVarValue :=
  let initial := (env.length, wheres.length)
  let (n, elide) := (List.range env.length).reverse.foldl
    (elideParamStep runtime env orig wheres) initial
  let params := env.take n
  let output := if n = 0 then [] else ["{"] ++
    params.zipIdx.flatMap (fun (parameter, index) =>
      [renderTypeParam runtime wheres elide parameter] ++
        if index + 1 < n then [", "] else []) ++ ["}"]
  (output, wheres.take elide)

structure TypeAliasValue where
  reference : GlobalRefValue
  binders : List TypeVarValue
  deriving DecidableEq, Repr

structure TypeAliasRuntime where
  nameRuntime : AliasNameRuntime
  paramsRuntime : TypeParamsRuntime

def showTypealiasBody (runtime : TypeAliasRuntime) (alias : TypeAliasValue)
    (env : List TypeSlot) (wheres : List TypeVarValue) : Out × List TypeVarValue :=
  let name := showAliasNameBody runtime.nameRuntime alias.reference
  if env.isEmpty then (name, wheres)
  else
    let params := showTypeparamsBody runtime.paramsRuntime env
      (alias.binders.map TypeSlot.typeVar) wheres
    (name ++ params.1, params.2)

structure MakeWheresRuntime where
  hasTypevar : TypeExpr → TypeVarValue → Bool

def addSeen (seen : List Nat) (typevar : TypeVarValue) : List Nat :=
  if seen.contains typevar.id then seen else typevar.id :: seen

def outerWheres : TypeExpr → List Nat → List TypeVarValue →
    List Nat × List TypeVarValue
  | .atom _, seen, wheres => (seen, wheres)
  | .unionAll typevar body, seen, wheres =>
    if seen.contains typevar.id then outerWheres body seen wheres
    else outerWheres body (typevar.id :: seen) (wheres ++ [typevar])

def makeWheresBody (runtime : MakeWheresRuntime) (context : Option TypeVarContext)
    (env : List TypeSlot) (value : TypeExpr) : List TypeVarValue :=
  let contextVars := match context with
    | none => []
    | some io => io.dict.filterMap fun (binding : String × TypeBindingValue) =>
      if binding.1 == "unionall_env" then match binding.2 with
        | TypeBindingValue.typeVar typevar =>
          if runtime.hasTypevar value typevar then some typevar else none
        | TypeBindingValue.other _ => none
      else none
  let seen := contextVars.foldl addSeen []
  let (seen, wheres) := outerWheres value seen []
  (env.reverse.foldl (fun (seen, wheres) slot => match slot with
    | .other _ => (seen, wheres)
    | .typeVar typevar => if seen.contains typevar.id then (seen, wheres)
      else (typevar.id :: seen, typevar :: wheres)) (seen, wheres)).2

structure AliasDispatchRuntime where
  makeAlias : TypeExpr → Option (TypeAliasValue × List TypeSlot)
  makeWheres : List TypeSlot → TypeExpr → List TypeVarValue
  showAlias : TypeAliasValue → List TypeSlot → List TypeVarValue → Out
  showWheres : List TypeVarValue → Out

def showTypealiasDispatchBody (runtime : AliasDispatchRuntime) (value : TypeExpr) : Bool × Out :=
  match runtime.makeAlias value with
  | none => (false, [])
  | some (alias, env) =>
    let wheres := runtime.makeWheres env value
    (true, runtime.showAlias alias env wheres ++ runtime.showWheres wheres)

structure AliasObject where
  id : Nat
  isUnionAll : Bool
  deriving DecidableEq, Repr

structure FoundAlias where
  reference : GlobalRefValue
  object : AliasObject
  env : List TypeSlot
  deriving DecidableEq, Repr

structure MakeAliasRuntime where
  anyId : Nat
  isTupleSubtype : TypeObject → Bool
  modulesOf : TypeObject → List String
  normalizeModule : String → String
  names : String → List String
  isDefinedGlobal : String → String → Bool
  isDeprecated : String → String → Bool
  isConst : String → String → Bool
  getGlobal : String → String → AliasObject
  isType : AliasObject → Bool
  hasFreeTypevars : AliasObject → Bool
  printWithoutParams : AliasObject → Bool
  isSubtype : TypeObject → AliasObject → Bool
  reapplyContext : Option TypeVarContext → TypeObject → TypeObject
  findFreeTypevars : TypeObject → List TypeVarValue
  unbounded : AliasObject → AliasObject
  intersectEnv : TypeObject → AliasObject → List TypeSlot
  applyAlias : AliasObject → List TypeSlot → Option TypeObject
  rewrapFree : TypeObject → List TypeVarValue → TypeObject
  hasOtherFree : TypeObject → List TypeVarValue → Bool
  sameType : TypeObject → TypeObject → Bool
  aliasSubtype : AliasObject → AliasObject → Bool

def aliasMatch (runtime : MakeAliasRuntime) (input proper : TypeObject)
    (reference : GlobalRefValue) (alias : AliasObject) : Option FoundAlias :=
  if !runtime.isType alias || runtime.hasFreeTypevars alias ||
      runtime.printWithoutParams alias || !runtime.isSubtype proper alias then none
  else if alias.isUnionAll then
    let freeBefore := runtime.findFreeTypevars input
    let env := runtime.intersectEnv input (runtime.unbounded alias)
    match runtime.applyAlias alias env with
    | none => none
    | some applied =>
      let applied := runtime.rewrapFree applied freeBefore
      if runtime.hasOtherFree applied freeBefore || !runtime.sameType applied input then none
      else some ⟨reference, alias, env⟩
  else if alias.id = input.id then some ⟨reference, alias, []⟩ else none

def collectAliases (runtime : MakeAliasRuntime) (input proper : TypeObject) : List FoundAlias :=
  (runtime.modulesOf input).map runtime.normalizeModule |>.flatMap fun moduleName =>
    (runtime.names moduleName).filterMap fun name =>
      if runtime.isDefinedGlobal moduleName name && !runtime.isDeprecated moduleName name &&
          runtime.isConst moduleName name then
        let alias := runtime.getGlobal moduleName name
        aliasMatch runtime input proper ⟨moduleName, name⟩ alias
      else none

def chooseAlias (runtime : MakeAliasRuntime) (aliases : List FoundAlias) : Option FoundAlias :=
  let best := if aliases.length > 1 then aliases.filter fun candidate =>
    !(aliases.any fun other =>
      runtime.aliasSubtype other.object candidate.object &&
        !runtime.aliasSubtype candidate.object other.object)
  else aliases
  match best with | [candidate] => some candidate | _ => none

def makeTypealiasBody (runtime : MakeAliasRuntime) (context : Option TypeVarContext)
    (input : TypeObject) : Option FoundAlias :=
  if input.id = runtime.anyId || runtime.isTupleSubtype input then none
  else chooseAlias runtime (collectAliases runtime input (runtime.reapplyContext context input))

structure TypeId where
  id : Nat
  deriving DecidableEq, Repr

structure ScalarIO where
  typeinfo : TypeId
  hexUnsigned : Bool
  deriving DecidableEq, Repr

structure SignedValue where
  value : Int
  deriving DecidableEq, Repr

structure UnsignedValue where
  value : Nat
  typeId : TypeId
  deriving DecidableEq, Repr

structure ScalarRuntime where
  anyType : TypeId
  nothingType : TypeId
  boolType : TypeId
  nonnothingType : TypeId → TypeId
  nonmissingType : TypeId → TypeId
  stringSigned : SignedValue → String
  stringUnsignedDecimal : UnsignedValue → String
  stringUnsignedHex : UnsignedValue → Nat → String
  bitSize : UnsignedValue → Nat
  typeOfUnsigned : UnsignedValue → TypeId
  renderType : TypeId → String

def nonnothingNonmissingBody (runtime : ScalarRuntime) (io : ScalarIO) : TypeId :=
  runtime.nonmissingType (runtime.nonnothingType io.typeinfo)

def showBoolBody (runtime : ScalarRuntime) (io : ScalarIO) (value : Bool) : Out :=
  [if nonnothingNonmissingBody runtime io = runtime.boolType then
    if value then "1" else "0"
   else if value then "true" else "false"]

def showUnsignedBody (runtime : ScalarRuntime) (io : ScalarIO)
    (value : UnsignedValue) : Out :=
  if io.hexUnsigned then
    ["0x", runtime.stringUnsignedHex value ((runtime.bitSize value + 3) / 4)]
  else if io.typeinfo = runtime.typeOfUnsigned value then
    [runtime.stringUnsignedDecimal value]
  else [runtime.renderType (runtime.typeOfUnsigned value), "(",
    runtime.stringUnsignedDecimal value, ")"]

structure PairElement where
  id : Nat
  deriving DecidableEq, Repr

structure PairValue where
  first : PairElement
  second : PairElement
  pairType : TypeId
  firstParameter : TypeId
  secondParameter : TypeId
  deriving DecidableEq, Repr

structure PairIO where
  typeinfo : TypeId
  compact : Bool
  deriving DecidableEq, Repr

structure PairRuntime where
  anyType : TypeId
  pairSupertype : TypeId
  typeOfValue : PairElement → TypeId
  typeOfPair : PairValue → TypeId
  pairIsa : PairValue → TypeId → Bool
  subtype : TypeId → TypeId → Bool
  fieldType : TypeId → Nat → TypeId
  isDelimited : PairIO → PairElement → Bool
  renderValue : PairIO → PairElement → String
  renderType : TypeId → String
  renderTuple : PairElement → PairElement → String
  symbolOfFunction : FunctionValue → SymbolValue
  isOperator : SymbolValue → Bool

def hasTightTypeBody (runtime : PairRuntime) (pair : PairValue) : Bool :=
  runtime.typeOfValue pair.first = pair.firstParameter &&
    runtime.typeOfValue pair.second = pair.secondParameter

def pairDelimitedBody (runtime : PairRuntime) (io : PairIO) (pair : PairValue) : Bool :=
  !(hasTightTypeBody runtime pair || io.typeinfo = runtime.typeOfPair pair)

def pairTypeinfosBody (runtime : PairRuntime) (io : PairIO) (pair : PairValue) : TypeId × TypeId :=
  if runtime.pairIsa pair io.typeinfo && runtime.subtype io.typeinfo runtime.pairSupertype then
    (runtime.fieldType io.typeinfo 1, runtime.fieldType io.typeinfo 2)
  else (runtime.anyType, runtime.anyType)

def showPairBody (runtime : PairRuntime) (io : PairIO) (pair : PairValue) : Out :=
  if pairDelimitedBody runtime io pair then
    [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second]
  else
    let typeinfos := pairTypeinfosBody runtime io pair
    let io1 : PairIO := ⟨typeinfos.1, io.compact⟩
    let io2 : PairIO := ⟨typeinfos.2, io.compact⟩
    let firstDelimited := runtime.isDelimited io1 pair.first
    let secondDelimited := runtime.isDelimited io2 pair.second
    (if firstDelimited then [] else ["("]) ++ [runtime.renderValue io1 pair.first] ++
    (if firstDelimited then [] else [")"]) ++ [if io.compact then "=>" else " => "] ++
    (if secondDelimited then [] else ["("]) ++ [runtime.renderValue io2 pair.second] ++
    (if secondDelimited then [] else [")"])

structure ModuleValue where
  id : Nat
  name : String
  parentId : Nat
  deriving DecidableEq, Repr

structure ModuleRuntime where
  moduleCount : Nat
  lookup : Nat → ModuleValue
  lookupSelf : ∀ module, lookup module.id = module
  isRootModule : ModuleValue → Bool
  showSymbol : String → String

def printFullnameBody (runtime : ModuleRuntime) : Nat → ModuleValue → Out
  | 0, module => [runtime.showSymbol module.name]
  | fuel + 1, module =>
    let parent := runtime.lookup module.parentId
    if parent.id = module.id then [runtime.showSymbol module.name]
    else printFullnameBody runtime fuel parent ++ [".", runtime.showSymbol module.name]

def showModuleBody (runtime : ModuleRuntime) (module : ModuleValue) : Out :=
  if runtime.isRootModule module then [module.name]
  else printFullnameBody runtime runtime.moduleCount module

structure CodeInfoValue where
  slotnames : List SymbolValue
  deriving DecidableEq, Repr

structure SlotRuntime where
  symbolRuntime : SymbolRuntime
  unusedSymbol : SymbolValue

def slotStrings (runtime : SlotRuntime) (slotnames : List SymbolValue) : List String :=
  slotnames.map fun symbol =>
    if symbol.id = runtime.unusedSymbol.id then "#unused#"
    else runtime.symbolRuntime.string symbol

def sourceSlotnamesBody (runtime : SlotRuntime) (slotnames : List SymbolValue) : List String :=
  Remaining.sourceinfoSlotnames (slotStrings runtime slotnames)

structure MethodValue where
  id : Nat
  name : String
  generatorId : Option Nat
  deriving DecidableEq, Repr

structure DebugInfoValue where
  file : String
  line : Int
  deriving DecidableEq, Repr

structure MethodCacheValue where
  ownerUninferred : Bool
  debugInfo : DebugInfoValue
  deriving DecidableEq, Repr

inductive MethodDefValue where
  | method (value : MethodValue)
  | toplevel (id : Nat)
  deriving DecidableEq, Repr

structure MethodInstanceValue where
  id : Nat
  definition : MethodDefValue
  specTypes : TypeExpr
  cache : Option MethodCacheValue
  deriving DecidableEq, Repr

inductive CodeInstanceDef where
  | methodInstance (value : MethodInstanceValue)
  | abiOverride (value : MethodInstanceValue)
  deriving DecidableEq, Repr

structure CodeInstanceValue where
  definition : CodeInstanceDef
  owner : Option Nat
  deriving DecidableEq, Repr

structure MethodRuntime where
  renderMethod : MethodValue → String
  showTupleAsCall : String → TypeExpr → Bool → String
  renderToplevelDef : Nat → String

def showMethodInstanceBody (runtime : MethodRuntime) (miValue : MethodInstanceValue)
    (fromStackframe : Bool) : String :=
  match miValue.definition with
  | .method method =>
    if method.generatorId = some miValue.id then
      "MethodInstance generator for " ++ runtime.renderMethod method
    else "MethodInstance for " ++ runtime.showTupleAsCall method.name miValue.specTypes true
  | .toplevel definition =>
    let base := "Toplevel MethodInstance thunk"
    if fromStackframe then base else match miValue.cache with
    | some cache => if cache.ownerUninferred then
        let location := if cache.debugInfo.file.isEmpty || cache.debugInfo.line < 0 then
          "<unknown>" else cache.debugInfo.file ++ ":" ++ toString cache.debugInfo.line
        base ++ " from " ++ runtime.renderToplevelDef definition ++ " starting at " ++ location
      else base
    | none => base

def showCodeInstanceBody (runtime : MethodRuntime) (codeValue : CodeInstanceValue) : String :=
  let (methodInstance, abi) := match codeValue.definition with
    | .methodInstance value => (value, false)
    | .abiOverride value => (value, true)
  "CodeInstance for " ++ showMethodInstanceBody runtime methodInstance false ++
    (if abi then " (ABI Overridden)" else "") ++
    (if codeValue.owner.isSome then " (foreign)" else "")

structure DelimElement where
  id : Nat
  deriving DecidableEq, Repr

structure DelimArrayValue where
  id : Nat
  slots : List (Option DelimElement)
  deriving DecidableEq, Repr

structure DelimArrayRuntime where
  showCircular : DelimArrayValue → Option String
  render : DelimElement → String

def delimArrayElement (runtime : DelimArrayRuntime) (array : DelimArrayValue)
    (index : Int) : Option String :=
  if index < 1 then none else match array.slots[index.toNat - 1]? with
  | none | some none => none
  | some (some value) => some (runtime.render value)

structure IteratorValue where
  id : Nat
  fuel : Nat
  deriving DecidableEq, Repr

structure IteratorState where
  value : DelimElement
  stateId : Nat
  deriving DecidableEq, Repr

structure DelimIteratorRuntime where
  showCircular : IteratorValue → Option String
  iterateStart : IteratorValue → Option IteratorState
  iterateNext : IteratorValue → Nat → Option IteratorState
  render : DelimElement → String

def skipIterator (runtime : DelimIteratorRuntime) (iterator : IteratorValue) :
    Nat → Nat → Option IteratorState → Option IteratorState
  | 0, _, state => state
  | fuel + 1, count, state =>
    if count ≤ 1 then state else match state with
    | none => none
    | some current => skipIterator runtime iterator fuel (count - 1)
      (runtime.iterateNext iterator current.stateId)

def delimIteratorLoop (runtime : DelimIteratorRuntime) (iterator : IteratorValue)
    (delim : String) (delimOne : Bool) (n : Int) :
    Nat → Int → Bool → Option IteratorState → Out
  | 0, _, _, _ => []
  | _, _, _, none => []
  | fuel + 1, count, first, some current =>
    let shown := runtime.render current.value
    let next := runtime.iterateNext iterator current.stateId
    let count := count + 1
    if next.isNone || count > n then [shown] ++ (if delimOne && first then [delim] else [])
    else [shown, delim, " "] ++
      delimIteratorLoop runtime iterator delim delimOne n fuel count false next

def showDelimIteratorBody (runtime : DelimIteratorRuntime) (iterator : IteratorValue)
    (op delim close : String) (delimOne : Bool) (first : Nat) (n : Int) : Out :=
  [op] ++ (match runtime.showCircular iterator with
  | some marker => [marker]
  | none =>
    let state := skipIterator runtime iterator iterator.fuel first
      (runtime.iterateStart iterator)
    delimIteratorLoop runtime iterator delim delimOne n iterator.fuel
      (Int.ofNat (min first 1) - 1) true state) ++ [close]

structure OperatorRuntime where
  precedence : SymbolValue → Int
  isUnary : SymbolValue → Bool
  isUnaryAndBinary : SymbolValue → Bool
  arrow : Int
  assignment : Int
  controlFlow : Int
  pair : Int
  power : Int
  comparison : Int
  leftPipeId : Nat
  shortCircuitOrId : Nat
  questionId : Nat
  plusId : Nat
  plusPlusId : Nat
  multiplyId : Nat

inductive AssociativityValue where
  | left | right | none
  deriving DecidableEq, Repr

def operatorAssociativityBody (runtime : OperatorRuntime) (symbol : SymbolValue) : AssociativityValue :=
  let precedence := runtime.precedence symbol
  if precedence ∈ [runtime.arrow, runtime.assignment, runtime.controlFlow,
      runtime.pair, runtime.power] ||
      (runtime.isUnary symbol && !runtime.isUnaryAndBinary symbol) ||
      symbol.id = runtime.leftPipeId || symbol.id = runtime.shortCircuitOrId ||
      symbol.id = runtime.questionId then .right
  else if precedence ∈ [0, runtime.comparison] || symbol.id = runtime.plusId ||
      symbol.id = runtime.plusPlusId || symbol.id = runtime.multiplyId then .none
  else .left

structure QuoteNodeValue where
  value : DelimElement
  deriving DecidableEq, Repr

structure ExprValue where
  head : String
  args : List DelimElement
  deriving DecidableEq, Repr

structure ExprContext where
  unquoteFallback : Bool
  deriving DecidableEq, Repr

structure ExprRuntime where
  showQuoteSymbol : ExprContext → JStr → Int → Int → PO
  showQuoteExpr : ExprContext → JE → Int → Int → PO
  showUnquoted : ExprContext → JE → Int → Int → PO
  showFallback : ExprContext → DelimElement → String

structure StyledIO where
  id : Nat
  deriving DecidableEq, Repr

inductive WriteEvent where
  | plain (text : String)
  | styled (text color : String) (bold : Bool)
  deriving DecidableEq, Repr

structure StyleRuntime where
  colorEnabled : StyledIO → Bool
  uppercase : String → String
  renderLine : DelimElement → String
  renderFile : DelimElement → String

structure SymbolPrintRuntime where
  string : SymbolValue → String
  symbolFromString : String → SymbolValue
  isValidIdentifier : SymbolValue → Bool
  isIdentifier : SymbolValue → Bool
  isOperator : SymbolValue → Bool
  escapeRaw : String → String
  quotedSymbolIds : List Nat

def showSymPlain (runtime : SymbolPrintRuntime) (symbol : SymbolValue) : String :=
  if runtime.isValidIdentifier symbol then runtime.string symbol
  else "var\"" ++ runtime.escapeRaw (runtime.string symbol) ++ "\""

def showSymBody (runtime : SymbolPrintRuntime) (symbol : SymbolValue)
    (allowMacroname : Bool) : String :=
  if runtime.isValidIdentifier symbol then runtime.string symbol
  else
    let name := runtime.string symbol
    if allowMacroname && name.startsWith "@" then
      "@" ++ showSymPlain runtime (runtime.symbolFromString (name.drop 1).toString)
    else "var\"" ++ runtime.escapeRaw name ++ "\""

structure SSAValueModel where
  id : Int
  deriving DecidableEq, Repr

inductive SSAWarnClass where
  | strong | mild | none
  deriving DecidableEq, Repr

structure SSARuntime where
  maxId : StyledIO → Int
  warnClass : StyledIO → Int → SSAWarnClass
  warnColor : Unit → String

def showSSABody (runtime : SSARuntime) (io : StyledIO)
    (value : SSAValueModel) : List WriteEvent :=
  let text := "%" ++ toString value.id
  if runtime.maxId io < value.id then [.styled text "red" false]
  else match runtime.warnClass io value.id with
  | .strong => [.styled text "light_red" true]
  | .mild => [.styled text (runtime.warnColor ()) true]
  | .none => [.plain text]

structure GlobalRefModel where
  moduleValue : ModuleValue
  name : SymbolValue
  deriving DecidableEq, Repr

structure GlobalRefRuntime where
  symbolRuntime : SymbolPrintRuntime
  renderModule : ModuleValue → String

def showGlobalRefBody (runtime : GlobalRefRuntime) (reference : GlobalRefModel)
    (allowMacroname : Bool) : String :=
  let name := runtime.symbolRuntime.string reference.name
  let quoted := !runtime.symbolRuntime.isIdentifier reference.name && !name.startsWith "@"
  let parens := quoted && (!runtime.symbolRuntime.isOperator reference.name ||
    runtime.symbolRuntime.quotedSymbolIds.contains reference.name.id)
  runtime.renderModule reference.moduleValue ++ "." ++
    (if quoted then ":" else "") ++ (if parens then "(" else "") ++
    showSymBody runtime.symbolRuntime reference.name allowMacroname ++
    (if parens then ")" else "")

structure BindingPartitionModel where
  owner : GlobalRefModel
  deriving DecidableEq, Repr

structure SlotNumberModel where
  id : Nat
  deriving DecidableEq, Repr

structure SlotIO where
  sourceSlotnames : Option (List String)
  deriving DecidableEq, Repr

def showSlotBody (io : SlotIO) (slot : SlotNumberModel) : R String :=
  match io.sourceSlotnames with
  | some names => if slot.id ≤ names.length then
      if slot.id = 0 then .error .boundsError else match names[slot.id - 1]? with
      | some name => .ok name
      | none => .error .boundsError
    else .ok ("_" ++ toString slot.id)
  | none => .ok ("_" ++ toString slot.id)

structure LineNodeModel where
  line : DelimElement
  file : Option DelimElement
  deriving DecidableEq, Repr

inductive QuoteContent where
  | symbol (value : SymbolValue)
  | block (value : ExprValue)
  | other (value : DelimElement)
  deriving DecidableEq, Repr

structure QuoteNodeModel where
  value : QuoteContent
  deriving DecidableEq, Repr

structure QuoteRuntime where
  symbols : SymbolPrintRuntime
  quotedIds : List Nat
  renderStringRepr : String → String
  showBlock : ExprContext → String → ExprValue → Int → Int → String
  showUnquotedOther : ExprContext → DelimElement → Int → Int → String
  showOther : ExprContext → DelimElement → String
  showExpr : ExprContext → ExprValue → String

def showQuotedBody (runtime : QuoteRuntime) (io : ExprContext) (value : QuoteContent)
    (indent quoteLevel : Int) : String :=
  match value with
  | .symbol symbol =>
    let name := runtime.symbols.string symbol
    if runtime.quotedIds.contains symbol.id then ":(" ++ name ++ ")"
    else if runtime.symbols.isIdentifier symbol ||
        (runtime.symbols.isOperator symbol && name ≠ "'") then ":" ++ name
    else "Symbol(" ++ runtime.renderStringRepr name ++ ")"
  | .block expression =>
    runtime.showBlock ⟨false⟩ "quote" expression indent quoteLevel ++ "end"
  | .other other => ":(" ++ runtime.showUnquotedOther io other (indent + 2) (-1) ++ ")"

def showQuoteNodeBody (runtime : QuoteRuntime) (io : ExprContext)
    (node : QuoteNodeModel) (indent : Int) : String :=
  match node.value with
  | .symbol symbol => showQuotedBody runtime io (.symbol symbol) indent 0
  | .block expression => "$(QuoteNode(" ++
      runtime.showExpr io expression ++ "))"
  | .other other => "$(QuoteNode(" ++ runtime.showOther io other ++ "))"

inductive ImportNode where
  | symbol (value : SymbolValue)
  | globalRef (value : GlobalRefModel)
  | expr (head : String) (args : List ImportNode)
  | other (id : Nat)
  deriving Repr

def validImportPathBody (node : ImportNode) (allowAs : Bool) : Bool :=
  let node := match node with
    | .expr "as" [path, _] => if allowAs then path else node
    | _ => node
  match node with
  | .expr "." args => !args.isEmpty && args.all fun arg => match arg with
    | .symbol _ => true
    | _ => false
  | _ => false

structure ImportRuntime where
  symbols : SymbolPrintRuntime
  renderUnquoted : ImportNode → Int → Int → Int → String

def showImportPathBody (runtime : ImportRuntime) : ImportNode → Int → R String
  | node@(.symbol _), _ => .ok (runtime.renderUnquoted node 0 0 0)
  | node@(.globalRef _), _ => .ok (runtime.renderUnquoted node 0 0 0)
  | node@(.other _), _ => .ok (runtime.renderUnquoted node 0 0 0)
  | .expr ":" [], quoteLevel => .ok (runtime.renderUnquoted (.expr ":" []) 0 0 quoteLevel)
  | .expr ":" (first :: rest), quoteLevel => do
    let firstText ← showImportPathBody runtime first quoteLevel
    let restText ← rest.mapM (showImportPathBody runtime · quoteLevel)
    .ok (firstText ++ ": " ++ ", ".intercalate restText)
  | .expr "." args, _ => do
    let pieces ← args.zipIdx.mapM fun (arg, index) => match arg with
      | .symbol symbol =>
        let name := runtime.symbols.string symbol
        let shown := if name = "." then "." else if name = ".." then "(..)"
          else showSymBody runtime.symbols symbol (index + 1 = args.length)
        .ok (shown ++ if index + 1 < args.length && name ≠ "." then "." else "")
      | _ => .error .typeError
    .ok (String.join pieces)
  | node@(.expr _ _), quoteLevel => .ok (runtime.renderUnquoted node 0 0 quoteLevel)

def allowMacronameBody (runtime : SymbolPrintRuntime) (node : ImportNode) : ImportNode :=
  let shouldWrap := match node with
    | .symbol symbol => (runtime.string symbol).startsWith "@"
    | .globalRef _ => true
    | .expr "." [_, .expr "quote" _] => true
    | .expr "." [_, _] => false
    | _ => false
  if shouldWrap then .expr "macroname" [node] else node

def isCoreMacroBody (reference : GlobalRefModel) (macroName : SymbolValue) : Bool :=
  reference.moduleValue.name = "Core" && reference.name.id = macroName.id

structure ExprFallbackValue where
  head : DelimElement
  args : List DelimElement
  deriving DecidableEq, Repr

structure ExprFallbackRuntime where
  render : DelimElement → String

def showExprFallbackBody (runtime : ExprFallbackRuntime) (expression : ExprFallbackValue) : String :=
  "$(Expr(" ++ runtime.render expression.head ++
    String.join (expression.args.map fun arg => ", " ++ runtime.render arg) ++ "))"

inductive GeneratorExpr where
  | base (body : DelimElement) (ranges : List DelimElement)
  | flatten (inner : GeneratorExpr) (ranges : List DelimElement)
  deriving Repr

structure GeneratorRuntime where
  showUnquoted : DelimElement → Int → Int → Int → String
  showList : List DelimElement → String → Int → Int → Int → String

def collectGenerator : GeneratorExpr → DelimElement × List (List DelimElement)
  | .base body ranges => (body, [ranges])
  | .flatten inner ranges =>
    let result := collectGenerator inner
    (result.1, ranges :: result.2)

def showGeneratorBody (runtime : GeneratorRuntime) (expression : GeneratorExpr)
    (indent quoteLevel : Int) : String :=
  let (body, ranges) := collectGenerator expression
  runtime.showUnquoted body indent 0 quoteLevel ++
    String.join (ranges.map fun range => " for " ++
      runtime.showList range ", " indent 0 quoteLevel)

inductive AstValue where
  | symbol (value : SymbolValue)
  | real (value : Int)
  | string (value : String)
  | bool (value : Bool)
  | expr (head : String) (args : List AstValue)
  | globalRef (value : GlobalRefModel)
  | binding (value : BindingPartitionModel)
  | quoteNode (value : DelimElement)
  | other (id : Nat)
  deriving Repr

structure AstRuntime where
  renderUnquoted : AstValue → Int → Int → Int → String
  renderFallback : AstValue → String
  isOperator : SymbolValue → Bool
  isValidIdentifier : SymbolValue → Bool
  unaryOperatorIds : List Nat
  callDelimiters : String → String × String

def astIsQuoted : AstValue → Bool
  | .quoteNode _ => true
  | .expr head args => (head = "quote" || head = "inert") && args.length = 1
  | _ => false

def astListItem (runtime : AstRuntime) (item : AstValue) (first : Bool)
    (indent prec quoteLevel : Int) (encloseOperators keyword : Bool) : String :=
  let unaryCall := match item with
    | .expr "call" (.symbol callee :: _) => runtime.unaryOperatorIds.contains callee.id
    | _ => false
  let negativeReal := match item with | .real value => value < 0 | _ => false
  let operatorSymbol := match item with
    | .symbol symbol => runtime.isOperator symbol && runtime.isValidIdentifier symbol
    | _ => false
  let parens := !astIsQuoted item &&
    ((first && prec ≥ 14 && (unaryCall || negativeReal)) ||
      (encloseOperators && operatorSymbol))
  let shown := match item with
    | .expr "kw" [lhs, rhs] => if keyword then
        runtime.renderUnquoted (.expr "=" [lhs, rhs]) indent (if parens then 0 else prec) quoteLevel
      else runtime.renderUnquoted item indent (if parens then 0 else prec) quoteLevel
    | .expr "=" [_, _] => if keyword then runtime.renderFallback item
      else runtime.renderUnquoted item indent (if parens then 0 else prec) quoteLevel
    | _ => runtime.renderUnquoted item indent (if parens then 0 else prec) quoteLevel
  (if parens then "(" else "") ++ shown ++ if parens then ")" else ""

def showAstListBody (runtime : AstRuntime) (items : List AstValue) (separator : String)
    (indent prec quoteLevel : Int) (encloseOperators keyword : Bool) : String :=
  String.join (items.zipIdx.map fun (item, index) =>
    (if index = 0 then "" else separator) ++
      astListItem runtime item (index = 0) (indent + 4) prec quoteLevel encloseOperators keyword)

def showAstBlockBody (runtime : AstRuntime) (head : String) (arguments : List AstValue)
    (body : AstValue) (indent quoteLevel : Int) : String :=
  let argsText := if arguments.isEmpty then "" else " " ++
    showAstListBody runtime arguments (if head = "elseif" then " " else ", ") indent 0 quoteLevel false false
  let bodyIndent := if head = "module" || head = "baremodule" then indent else indent + 4
  let expressions := match body with
    | .expr "block" args | .expr "quote" args => args
    | _ => [body]
  head ++ argsText ++ String.join (expressions.map fun expression =>
    "\n" ++ String.ofList (List.replicate bodyIndent.toNat ' ') ++
      runtime.renderUnquoted expression bodyIndent (-1) quoteLevel) ++
    "\n" ++ String.ofList (List.replicate indent.toNat ' ')

def showAstCallBody (runtime : AstRuntime) (head : String) (function : AstValue)
    (arguments : List AstValue) (indent quoteLevel : Int) (keyword : Bool) : String :=
  let (openToken, closeToken) := runtime.callDelimiters head
  let direct := match function with
    | .symbol symbol =>
      (symbol.id ≠ 0 && !(head = "." && runtime.isOperator symbol)) ||
        !runtime.isValidIdentifier symbol
    | .expr exprHead _ => exprHead = "." || exprHead = "curly" || exprHead = "macroname"
    | .globalRef _ | .binding _ => true
    | _ => false
  let functionText := runtime.renderUnquoted function indent 0 quoteLevel
  let functionText := if direct then functionText else "(" ++ functionText ++ ")"
  let functionText := functionText ++ if head = "." then "." else ""
  match arguments with
  | .expr "parameters" parameters :: positional =>
    functionText ++ openToken ++
      showAstListBody runtime positional ", " indent 0 quoteLevel false keyword ++ "; " ++
      showAstListBody runtime parameters ", " indent 0 quoteLevel false keyword ++ closeToken
  | _ => functionText ++ openToken ++
      showAstListBody runtime arguments ", " indent 0 quoteLevel false keyword ++ closeToken

def astIsExpr (value : AstValue) (head : String) : Bool := match value with
  | .expr actual _ => actual = head
  | _ => false

def astSymbol? : AstValue → Option SymbolValue
  | .symbol symbol => some symbol
  | .globalRef reference => some reference.name
  | _ => none

structure FullExprRuntime where
  ast : AstRuntime
  operators : OperatorRuntime
  symbols : SymbolPrintRuntime
  infixHeads : List String
  wideInfixHeads : List String
  parenHeads : List (String × (String × String))
  callHeads : List String
  isPostfix : SymbolValue → Bool
  showGenerator : AstValue → Int → Int → String
  showImport : AstValue → Int → String
  validImport : AstValue → Bool → Bool
  allowMacroname : AstValue → AstValue
  isCoreMacro : AstValue → String → Bool
  showQuoted : AstValue → Int → Int → String
  showLine : List AstValue → String
  escapeString : String → String
  fallback : AstValue → String

def showExprFullBody (runtime : FullExprRuntime) (unquoteFallback beginsym : Bool)
    (expression : AstValue) (indent prec quoteLevel : Int) : String :=
  match expression with
  | nonexpr@(.symbol _) | nonexpr@(.real _) | nonexpr@(.string _) |
      nonexpr@(.bool _) | nonexpr@(.globalRef _) | nonexpr@(.binding _) |
      nonexpr@(.quoteNode _) | nonexpr@(.other _) =>
    runtime.ast.renderUnquoted nonexpr indent prec quoteLevel
  | expr@(.expr head args) =>
    let nargs := args.length
    let render (value : AstValue) (p : Int := 0) :=
      runtime.ast.renderUnquoted value indent p quoteLevel
    let list (values : List AstValue) (separator : String) (p : Int := 0)
        (enclose : Bool := false) (keyword : Bool := false) :=
      showAstListBody runtime.ast values separator indent p quoteLevel enclose keyword
    if head = "." && (nargs ≠ 2 || !astIsExpr (args.getD 1 (.other 0)) "tuple") then
      match args with
      | [.symbol symbol] => if runtime.symbols.isOperator symbol then
          "(." ++ runtime.symbols.string symbol ++ ")" else runtime.fallback expr
      | [item, field] => if astIsQuoted field then
          let itemText := render item
          let itemParens := !astIsQuoted item && match item with
            | .symbol symbol => !runtime.symbols.isIdentifier symbol
            | .expr "." _ => false
            | _ => true
          let fieldText := render field
          (if itemParens then "(" else "") ++ itemText ++ (if itemParens then ")" else "") ++
            "." ++ fieldText
        else runtime.fallback expr
      | _ => runtime.fallback expr
    else if runtime.infixHeads.contains head && nargs = 2 then
      let precedence := runtime.operators.precedence (runtime.symbols.symbolFromString head)
      let separator := if runtime.wideInfixHeads.contains head then " " ++ head ++ " " else head
      let shown := list args separator precedence true
      if precedence ≤ prec then "(" ++ shown ++ ")" else shown
    else if head = "tuple" then
      match args with
      | .expr "parameters" parameters :: positional =>
        "(" ++ list positional ", " ++ (if positional.length = 1 then "," else "") ++ ";" ++
          (if parameters.isEmpty then "" else " " ++ list parameters ", " 0 false true) ++ ")"
      | _ => "(" ++ list args ", " ++ (if nargs = 1 then "," else "") ++ ")"
    else if runtime.parenHeads.any (fun pair => pair.1 = head) ||
        ["typed_vcat", "typed_hcat", "typed_ncat"].contains head then
      let typed := head.startsWith "typed_"
      let normalized := if head = "typed_vcat" then "vcat" else if head = "typed_hcat" then "hcat"
        else if head = "typed_ncat" then "ncat" else head
      let values := if typed then args.drop 1 else args
      let typePrefix := if typed then match args with | first :: _ => render first | _ => "" else ""
      let delimiters := (runtime.parenHeads.find? (fun pair => pair.1 = normalized)).map (·.2) |>.getD ("[", "]")
      let separator := if ["vcat", "bracescat"].contains normalized then "; "
        else if ["hcat", "row"].contains normalized then " " else ", "
      typePrefix ++ delimiters.1 ++ list values separator ++ delimiters.2
    else if (head = "'" && nargs = 1) || (head = "call" && nargs = 2 &&
        match args[0]? with
        | some (AstValue.symbol symbol) => runtime.isPostfix symbol && runtime.symbols.string symbol != "'"
        | _ => false) then
      let (operatorText, operand) := if head = "'" then ("'", args.getD 0 (.other 0)) else
        match args with
        | .symbol symbol :: operand :: _ => (runtime.symbols.string symbol, operand)
        | _ => ("", .other 0)
      let enclosed := match operand with
        | .expr _ _ => true
        | .symbol symbol => runtime.symbols.isOperator symbol
        | _ => false
      (if enclosed then "(" else "") ++ render operand ++
        (if enclosed then ")" else "") ++ operatorText
    else if head = "call" && nargs ≥ 1 then
      match args with
      | function :: arguments =>
        let symbol := astSymbol? function
        let precedence := match symbol with | some value => runtime.operators.precedence value | none => 0
        let keyword := arguments.any (astIsExpr · "kw") ||
          match arguments with | first :: _ => astIsExpr first "parameters" | [] => false
        if keyword then showAstCallBody runtime.ast head function arguments indent quoteLevel true
        else if match symbol with | some value => runtime.symbols.string value == "*" | none => false then
          match arguments with
          | [.real coefficient, .symbol symbolValue] =>
            let first := (runtime.symbols.string symbolValue).toList.headD 'a'
            let forbidden := ['e', 'E', 'f'] ++ if coefficient = 0 then ['b', 'o', 'x'] else []
            if !forbidden.contains first then toString coefficient ++ runtime.symbols.string symbolValue
            else showAstCallBody runtime.ast head function arguments indent quoteLevel true
          | _ => showAstCallBody runtime.ast head function arguments indent quoteLevel true
        else if match symbol with
          | some value => arguments.length = 1 && runtime.operators.isUnary value
          | none => false then
          render function ++ render (arguments.headD (.other 0)) precedence
        else if precedence > 0 && arguments.length = 2 then
          let separator := match symbol with | some value => " " ++ runtime.symbols.string value ++ " " | none => " "
          let shown := list arguments separator precedence true
          if precedence ≤ prec then "(" ++ shown ++ ")" else shown
        else showAstCallBody runtime.ast head function arguments indent quoteLevel true
      | [] => runtime.fallback expr
    else if ["new", "splatnew"].contains head then
      "%" ++ head ++ "(" ++ list args ", " ++ ")"
    else if runtime.callHeads.contains head && nargs ≥ 1 then
      let function := args.getD 0 (.other 0)
      let callArguments := if head = "." then match args[1]? with
        | some (AstValue.expr _ values) => values
        | _ => []
        else args.drop 1
      showAstCallBody runtime.ast head function callArguments indent quoteLevel (head != "curly")
    else if head = "typed_comprehension" && nargs = 2 then
      render (args.getD 0 (.other 0)) ++ "[" ++
        runtime.showGenerator (args.getD 1 (.other 0)) indent quoteLevel ++ "]"
    else if head = "comprehension" && nargs = 1 then
      "[" ++ runtime.showGenerator (args.getD 0 (.other 0)) indent quoteLevel ++ "]"
    else if (head = "generator" && nargs ≥ 2) || (head = "flatten" && nargs = 1) then
      "(" ++ runtime.showGenerator expr indent quoteLevel ++ ")"
    else if head = "filter" && nargs = 2 then
      render (args.getD 1 (.other 0)) ++ " if " ++ render (args.getD 0 (.other 0))
    else if head = "comparison" && nargs ≥ 3 && nargs % 2 = 1 then
      list args " "
    else if ["for", "while", "function", "macro", "if", "elseif", "let"].contains head &&
        (nargs = 1 || nargs = 2 || ((head = "if" || head = "elseif") && nargs = 3)) then
      let arguments := if nargs ≥ 2 then [args.getD 0 (.other 0)] else []
      let body := args.getD (nargs - 1) (.expr "block" [])
      showAstBlockBody runtime.ast head arguments body indent quoteLevel ++ "end"
    else if head = "do" && nargs = 2 then
      render (args.getD 0 (.other 0)) (-1) ++ " do" ++
        render (args.getD 1 (.other 0)) ++ "\n" ++
        String.ofList (List.replicate indent.toNat ' ') ++ "end"
    else if head = "module" && (nargs = 3 || nargs = 4) then
      let bare := match args with
        | _ :: .bool flag :: _ => !flag
        | .bool flag :: _ => !flag
        | _ => false
      let name := args.getD (nargs - 2) (.other 0)
      let body := args.getD (nargs - 1) (.expr "block" [])
      showAstBlockBody runtime.ast (if bare then "baremodule" else "module") [name]
        body indent quoteLevel ++ "end"
    else if head = "struct" && nargs = 3 then
      let mutable := match args[0]? with | some (.bool value) => value | _ => false
      showAstBlockBody runtime.ast (if mutable then "mutable struct" else "struct")
        [args.getD 1 (.other 0)] (args.getD 2 (.expr "block" [])) indent quoteLevel ++ "end"
    else if head = "primitive" && nargs = 2 then "primitive type " ++ list args " " ++ " end"
    else if head = "abstract" && nargs = 1 then "abstract type " ++ list args " " ++ " end"
    else if head = "return" && nargs = 1 && match args[0]? with
      | some (AstValue.other 0) => true
      | _ => false then
      "return"
    else if ["::", "<:", ">:"].contains head && nargs = 1 then head ++ render (args.getD 0 (.other 0))
    else if head = "..." && nargs = 1 then render (args.getD 0 (.other 0)) ++ "..."
    else if nargs = 0 && ["break", "continue"].contains head then head
    else if (nargs = 1 && ["return", "const"].contains head) || ["local", "global"].contains head then
      head ++ " " ++ list args ", "
    else if ["export", "public"].contains head then
      head ++ " " ++ list (args.map runtime.allowMacroname) ", "
    else if head = "macrocall" && nargs ≥ 2 then
      if runtime.isCoreMacro (args.getD 0 (.other 0)) "@cmd" then
        "`" ++ render (args.getD 2 (.other 0)) ++ "`"
      else if ["@int128_str", "@uint128_str", "@big_str"].any
          (runtime.isCoreMacro (args.getD 0 (.other 0))) then render (args.getD 2 (.other 0))
      else match args with
        | .symbol macroName :: _ :: .string text :: suffix =>
          let name := runtime.symbols.string macroName
          if name.startsWith "@" && name.endsWith "_str" then
            let literalName := String.ofList (name.toList.drop 1 |>.dropLast.dropLast.dropLast.dropLast)
            literalName ++ "\"" ++ runtime.escapeString text ++ "\"" ++
              match suffix with | [value] => render value | _ => ""
          else showAstCallBody runtime.ast "call" (runtime.allowMacroname (args.getD 0 (.other 0)))
            (args.drop 2) indent quoteLevel false
        | _ => showAstCallBody runtime.ast "call" (runtime.allowMacroname (args.getD 0 (.other 0)))
          (args.drop 2) indent quoteLevel false
    else if head = "macroname" && nargs = 1 then render (args.getD 0 (.other 0))
    else if head = "line" && 1 ≤ nargs && nargs ≤ 2 then runtime.showLine args
    else if head = "try" && 3 ≤ nargs && nargs ≤ 5 then
      showAstBlockBody runtime.ast "try" [] (args.getD 0 (.other 0)) indent quoteLevel ++ "end"
    else if head = "block" then
      if beginsym then "(" ++ list args ";\n" ++ (if args.isEmpty then ";;)" else ";)")
      else showAstBlockBody runtime.ast "begin" [] expr indent quoteLevel ++ "end"
    else if head = "quote" && nargs = 1 then runtime.showQuoted (args.getD 0 (.other 0)) indent (quoteLevel + 1)
    else if head = "gotoifnot" && nargs = 2 then
      "unless " ++ render (args.getD 0 (.other 0)) ++ " goto %" ++ render (args.getD 1 (.other 0))
    else if head = "string" && nargs = 1 then match args[0]? with
      | some (AstValue.string text) => "\"" ++ runtime.escapeString text ++ "\""
      | _ => runtime.fallback expr
    else if head = "null" then "nothing"
    else if head = "string" then "\"" ++ String.join (args.map fun value => match value with
      | .string text => runtime.escapeString text
      | _ => "$(" ++ render value ++ ")") ++ "\""
    else if (head = "&" || head = "$") && nargs = 1 then
      if head = "$" && unquoteFallback then runtime.fallback expr
      else head ++ render (args.getD 0 (.other 0))
    else if head = "where" && nargs > 1 then
      let tail := if nargs = 2 then render (args.getD 1 (.other 0))
        else "{" ++ list (args.drop 1) ", " ++ "}"
      (if prec ≥ 1 then "(" else "") ++ render (args.getD 0 (.other 0)) ++
        " where " ++ tail ++ if prec ≥ 1 then ")" else ""
    else if (head = "import" || head = "using") && args.all (runtime.validImport · true) then
      head ++ " " ++ ", ".intercalate (args.map (runtime.showImport · quoteLevel))
    else if head = "as" && nargs = 2 && runtime.validImport (args.getD 0 (.other 0)) false then
      runtime.showImport (args.getD 0 (.other 0)) quoteLevel ++ " as " ++ render (args.getD 1 (.other 0))
    else if head = "meta" && nargs ≥ 1 then "# meta: " ++ list args " "
    else runtime.fallback expr

def demangleFunctionBody (name : String) : String :=
  let pieces := name.splitOn "#"
  match pieces with
  | first :: _ :: _ => if first.isEmpty then name else first
  | _ => name

structure StacktraceIO where
  backtrace : Bool
  displaysize : Int × Int
  deriving DecidableEq, Repr

def printWithinStacktraceBody (io : StacktraceIO) (pieces : List String)
    (color : String) (bold : Bool) : List WriteEvent :=
  let text := String.join pieces
  if io.backtrace then [.styled text color bold] else [.plain text]

structure TypeLimitContext where
  limitedFlag : Option Bool
  displaysize : Int × Int
  deriving DecidableEq, Repr

structure TypeLimitRuntime where
  depthLimit : String → Int → String
  byteSize : String → Nat

def typeLimitedBody (runtime : TypeLimitRuntime) (context : TypeLimitContext)
    (text : String) : String × Option Bool :=
  match context.limitedFlag with
  | none => (text, none)
  | some current =>
    let limited := runtime.depthLimit text (max context.displaysize.2 120)
    (limited, some (current || runtime.byteSize limited < runtime.byteSize text))

structure SignatureRuntime where
  unwrapUnionall : TypeObject → TypeObject
  subtypeFunction : TypeObject → Bool
  asDataType : TypeObject → Option DataTypeValue
  parametersEmpty : DataTypeValue → Bool
  isSelf : DataTypeValue → Bool
  parentModule : DataTypeValue → String
  isExported : String → String → Bool
  mainModule : String
  renderModule : String → String
  renderSymbol : String → String
  isType : TypeObject → Bool
  typeParameter : TypeObject → Option TypeObject
  isTypeVar : TypeObject → Bool
  isUnionAll : TypeObject → Bool
  wrapperIsSelf : TypeObject → Bool
  renderType : TypeObject → String

def showSignatureFunctionBody (runtime : SignatureRuntime) (input : TypeObject)
    (demangle : Bool) (argumentName : String) (html qualified : Bool) : String :=
  let unwrapped := runtime.unwrapUnionall input
  match runtime.asDataType unwrapped with
  | some datatype =>
    if runtime.subtypeFunction input && runtime.parametersEmpty datatype && runtime.isSelf datatype then
      let moduleName := runtime.parentModule datatype
      let qualifier := if qualified && !runtime.isExported moduleName datatype.typeName.singletonName &&
          moduleName ≠ runtime.mainModule then runtime.renderModule moduleName ++ "." else ""
      let name := if demangle then demangleFunctionBody datatype.typeName.singletonName
        else datatype.typeName.singletonName
      qualifier ++ runtime.renderSymbol name
    else if runtime.isType input then match runtime.typeParameter input with
      | some parameter => if runtime.isTypeVar parameter then
          if html then "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
          else "(" ++ argumentName ++ "::" ++ runtime.renderType input ++ ")"
        else
          let parens := runtime.isUnionAll parameter && !runtime.wrapperIsSelf parameter
          (if parens then "(" else "") ++ runtime.renderType parameter ++
            (if parens then ")" else "")
      | none => runtime.renderType input
    else if html then "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
    else "(" ++ argumentName ++ "::" ++ runtime.renderType input ++ ")"
  | none => if runtime.isType input then match runtime.typeParameter input with
      | some parameter => runtime.renderType parameter
      | none => runtime.renderType input
    else if html then "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
    else "(" ++ argumentName ++ "::" ++ runtime.renderType input ++ ")"

inductive SignatureType where
  | tupleRoot
  | datatype (parameters : List TypeObject)
  | unionAll (binder : TypeVarValue) (body : SignatureType)
  deriving Repr

structure TupleCallRuntime where
  symbols : SymbolPrintRuntime
  signature : SignatureRuntime
  renderType : TypeObject → Bool → String
  isSplatKeyword : TypeObject → Bool
  renderMethodParams : List TypeVarValue → String
  limit : String → String

def unwrapSignature : SignatureType → List TypeVarValue × List TypeObject
  | .tupleRoot => ([], [])
  | .datatype parameters => ([], parameters)
  | .unionAll binder body =>
    let result := unwrapSignature body
    (binder :: result.1, result.2)

def showTupleCallBody (runtime : TupleCallRuntime) (name : SymbolValue)
    (signature : SignatureType) (demangle : Bool)
    (kwargs : Option (List (SymbolValue × TypeObject)))
    (argumentNames : Option (List SymbolValue)) (qualified hasFirst : Bool) : String :=
  match signature with
  | .tupleRoot => runtime.symbols.string
      (if demangle then runtime.symbols.symbolFromString
        (demangleFunctionBody (runtime.symbols.string name)) else name) ++ "(...)"
  | _ =>
    let (binders, parameters) := unwrapSignature signature
    let start := if hasFirst then 1 else 0
    let functionText := if hasFirst then match parameters with
      | first :: _ => showSignatureFunctionBody runtime.signature first demangle "" false qualified
      | [] => ""
      else ""
    let showNames := match argumentNames with
      | some names => names.length == parameters.length
      | none => false
    let arguments := (parameters.drop start).zipIdx.map fun (parameter, offset) =>
      let index := offset + start
      let argName := if showNames then match argumentNames with
        | some names => match names[index]? with | some symbol => runtime.symbols.string symbol | none => ""
        | none => "" else ""
      (if argName.isEmpty then "" else argName) ++ "::" ++ runtime.renderType parameter true
    let keywords := match kwargs with
      | none => ""
      | some pairs => "; " ++ ", ".intercalate (pairs.map fun pair =>
        runtime.symbols.string pair.1 ++ if runtime.isSplatKeyword pair.2 then "..."
          else "::" ++ runtime.renderType pair.2 true)
    runtime.limit (functionText ++ "(" ++ ", ".intercalate arguments ++ keywords ++ ")" ++
      runtime.renderMethodParams binders)

structure TypeColorRuntime where
  renderType : TypeObject → StacktraceIO → String

def firstBrace (text : String) : Option Nat := text.toList.findIdx? (fun char => char = '{')

def printTypeBicolorText (text color innerColor : String) (useColor : Bool) : List WriteEvent :=
  if !useColor then [.plain text]
  else match firstBrace text with
  | none => [.styled text color false]
  | some index =>
    let chars := text.toList
    let outer := String.ofList (chars.take index)
    if text.endsWith "..." then
      let inner := String.ofList ((chars.drop index).dropLast.dropLast.dropLast)
      [.styled outer color false, .styled inner innerColor false, .styled "..." color false]
    else [.styled outer color false, .styled (String.ofList (chars.drop index)) innerColor false]

inductive BindingNode where
  | other (id : Nat)
  | quote (value : BindingNode)
  | symbol (value : SymbolValue)
  | globalRef (value : GlobalRefModel)
  | expr (head : String) (args : List BindingNode)
  deriving Repr

inductive BindingResult where
  | value (node : BindingNode)
  | module (value : ModuleValue)
  | nothing
  deriving Repr

structure BindingRuntime where
  mainModule : ModuleValue
  baseModuleId : Nat
  coreModuleId : Nat
  getfieldSymbolId : Nat
  isDefined : GlobalRefModel → Bool
  isConst : GlobalRefModel → Bool
  getModule : GlobalRefModel → Option ModuleValue

def resolveGlobalBody (runtime : BindingRuntime) (reference : GlobalRefModel) : BindingResult :=
  if !runtime.isDefined reference || !runtime.isConst reference then .nothing
  else match runtime.getModule reference with
  | some module => .module module
  | none => .nothing

def resolveBindingBody (runtime : BindingRuntime) : Nat → BindingNode → BindingResult
  | 0, node => .value node
  | _, .other id => .value (.other id)
  | _, .quote value => .value value
  | fuel + 1, .symbol symbol =>
    resolveGlobalBody runtime ⟨runtime.mainModule, symbol⟩
  | _, .globalRef reference => resolveGlobalBody runtime reference
  | fuel + 1, .expr "." [parent, .symbol name] =>
    match resolveBindingBody runtime fuel parent with
    | .module module => resolveGlobalBody runtime ⟨module, name⟩
    | _ => .nothing
  | _, .expr _ _ => .nothing

def isModuleCallBody (runtime : BindingRuntime) (expression : BindingNode) : Bool :=
  match expression with
  | .expr "call" (BindingNode.globalRef callee :: target :: _) =>
    let getfield := callee.name.id = runtime.getfieldSymbolId &&
      (callee.moduleValue.id = runtime.baseModuleId || callee.moduleValue.id = runtime.coreModuleId)
    getfield && match resolveBindingBody runtime 32 target with
      | .module _ => true
      | _ => false
  | _ => false

structure TypeVarShowRuntime where
  bottomId : Nat
  anyId : Nat
  renderName : String → String
  isUnionAll : TypeObject → Bool
  printWithoutParams : TypeObject → Bool
  renderBound : TypeObject → String

def typevarInEnv (context : TypeVarContext) (typevar : TypeVarValue) : Bool :=
  context.dict.any fun binding => binding.1 == "unionall_env" && match binding.2 with
    | .typeVar value => value.id == typevar.id
    | .other _ => false

def showBoundBody (runtime : TypeVarShowRuntime) (bound : TypeObject) : String :=
  let parens := runtime.isUnionAll bound && !runtime.printWithoutParams bound
  (if parens then "(" else "") ++ runtime.renderBound bound ++ if parens then ")" else ""

def showTypevarBody (runtime : TypeVarShowRuntime) (context : TypeVarContext)
    (typevar : TypeVarValue) : String :=
  let inEnv := typevarInEnv context typevar
  let lower : TypeObject := ⟨typevar.lower⟩
  let upper : TypeObject := ⟨typevar.upper⟩
  let name := runtime.renderName typevar.name
  let lowerText := if !inEnv && typevar.lower ≠ runtime.bottomId then
    if typevar.upper = runtime.anyId then name ++ ">:" ++ showBoundBody runtime lower
    else showBoundBody runtime lower ++ "<:" ++ name
    else name
  lowerText ++ if !inEnv && typevar.upper ≠ runtime.anyId then
    "<:" ++ showBoundBody runtime upper else ""

structure VarargValue where
  typeField : Option TypeObject
  lengthField : Option DelimElement
  deriving Repr

structure VarargRuntime where
  renderType : TypeObject → String
  renderLength : DelimElement → String

def showVarargBody (runtime : VarargRuntime) (value : VarargValue) : String :=
  "Vararg" ++ match value.typeField with
  | none => ""
  | some type => "{" ++ runtime.renderType type ++ match value.lengthField with
    | none => "}"
    | some length => ", " ++ runtime.renderLength length ++ "}"

structure CodeInfoModel where
  id : Nat
  slotnames : Option (List SymbolValue)
  deriving DecidableEq, Repr

structure CodeInfoRuntime where
  slotRuntime : SlotRuntime
  debugInfoConfig : String → CodeInfoModel → String
  showIR : CodeInfoModel → Option (List String) → String → String

def showCodeInfoBody (runtime : CodeInfoRuntime) (source : CodeInfoModel)
    (debugInfo : String) : String :=
  let normalized := source.slotnames.map (sourceSlotnamesBody runtime.slotRuntime)
  let config := runtime.debugInfoConfig debugInfo source
  "CodeInfo(\n" ++ runtime.showIR source normalized config ++ ")"

structure IRNodeRuntime where
  renderUnquoted : DelimElement → Int → String
  renderType : TypeObject → String

structure ArgumentNode where
  n : Nat
  deriving DecidableEq, Repr

structure PhiNodeValue where
  edges : List Int
  values : List (Option DelimElement)
  deriving DecidableEq, Repr

structure PhiCNodeValue where
  values : List DelimElement
  deriving DecidableEq, Repr

structure PiNodeValue where
  value : DelimElement
  type : TypeObject
  deriving DecidableEq, Repr

structure OptionalNodeValue where
  value : Option DelimElement
  deriving DecidableEq, Repr

structure GotoIfNotValue where
  destination : Int
  condition : DelimElement
  deriving DecidableEq, Repr

def showPhiBody (runtime : IRNodeRuntime) (node : PhiNodeValue)
    (indent : Int) (labelPrefix : String) : String :=
  let arguments := node.edges.zipIdx.map fun (edge, index) =>
    let value := match node.values[index]? with
      | some (some assigned) => runtime.renderUnquoted assigned indent
      | _ => "#undef"
    labelPrefix ++ toString edge ++ " => " ++ value
  "φ (" ++ ", ".intercalate arguments ++ ")"

def showPhiCBody (runtime : IRNodeRuntime) (node : PhiCNodeValue) (indent : Int) : String :=
  "φᶜ (" ++ ", ".intercalate (node.values.map (runtime.renderUnquoted · indent)) ++ ")"

def showGotoIfNotBody (runtime : IRNodeRuntime) (node : GotoIfNotValue)
    (indent : Int) (labelPrefix : String) : String :=
  "goto " ++ labelPrefix ++ toString node.destination ++ " if not " ++
    runtime.renderUnquoted node.condition indent

structure AlignmentIO where
  color : Bool
  compact : Bool
  deriving DecidableEq, Repr

structure AlignmentValue where
  id : Nat
  deriving DecidableEq, Repr

structure AlignmentRuntime where
  render : AlignmentIO → AlignmentValue → String
  renderPlainString : AlignmentIO → AlignmentValue → String
  charWidth : Char → Nat

def noColorIO (io : AlignmentIO) : AlignmentIO := {io with color := false}

def alignmentFromShowBody (runtime : AlignmentRuntime) (io : AlignmentIO)
    (value : AlignmentValue) : Nat :=
  Truncate.textwidth runtime.charWidth (runtime.render (noColorIO io) value).toList

def alignmentFromPlainStringBody (runtime : AlignmentRuntime) (io : AlignmentIO)
    (value : AlignmentValue) : Nat :=
  Truncate.textwidth runtime.charWidth (runtime.renderPlainString (noColorIO io) value).toList

structure PairAlignmentRuntime where
  pairRuntime : PairRuntime
  renderPair : PairIO → PairValue → String
  renderElement : PairIO → PairElement → String
  charWidth : Char → Nat

def stringWidth (charWidth : Char → Nat) (text : String) : Int :=
  Int.ofNat (Truncate.textwidth charWidth text.toList)

def alignmentPairBody (runtime : PairAlignmentRuntime) (io : PairIO)
    (pair : PairValue) : Int × Int :=
  let fullWidth := stringWidth runtime.charWidth (runtime.renderPair io pair)
  if !pairDelimitedBody runtime.pairRuntime io pair then
    let typeinfos := pairTypeinfosBody runtime.pairRuntime io pair
    let context : PairIO := ⟨typeinfos.1, io.compact⟩
    let baseLeft := stringWidth runtime.charWidth (runtime.renderElement context pair.first)
    let parenWidth := if runtime.pairRuntime.isDelimited context pair.first then 0 else 2
    let spaceWidth := if io.compact then 0 else 1
    let left := baseLeft + parenWidth + spaceWidth
    (left + 1, fullWidth - left - 1)
  else (0, fullWidth)

structure BitIO where
  id : Nat
  deriving DecidableEq, Repr

structure BitWrite where
  io : BitIO
  text : String
  deriving DecidableEq, Repr

structure BitArrayValue where
  chunks : List Nat
  length : Nat
  deriving DecidableEq, Repr

def printBitChunkBody (io : BitIO) (chunk length : Nat) : List BitWrite :=
  (Containers.printBitChunk chunk length).map fun char => ⟨io, String.singleton char⟩

def bitshowBody (io : BitIO) (array : BitArrayValue) : List BitWrite :=
  if array.length = 0 then [] else
  let preceding := array.chunks.dropLast.flatMap fun chunk =>
    printBitChunkBody io chunk 64 ++ [⟨io, ": "⟩]
  let lastLength := (array.length - 1) % 64 + 1
  preceding ++ printBitChunkBody io (array.chunks.getLastD 0) lastLength

structure OpaqueClosureValue where
  argumentType : SignatureType
  resultType : TypeObject
  deriving Repr

structure OpaqueRuntime where
  tupleRuntime : TupleCallRuntime
  renderResultType : TypeObject → String

def showOpaqueBody (runtime : OpaqueRuntime) (closure : OpaqueClosureValue) : String :=
  showTupleCallBody runtime.tupleRuntime ⟨0⟩ closure.argumentType false none none false false ++
    "->◌::" ++ runtime.renderResultType closure.resultType

structure PartitionValue where
  id : Nat
  minWorld : Nat
  maxWorld : Nat
  kindBits : Nat
  restriction : BindingNode
  deriving Repr

structure PartitionRuntime where
  maxWorldValue : Nat
  flagMask : Nat
  exportedFlag : Nat
  implicitlyExportedFlag : Nat
  deprecatedFlag : Nat
  depwarnFlag : Nat
  implicitlyDeprecatedFlag : Nat
  bindingKind : PartitionValue → Nat
  backdatedConstKind : Nat
  constKind : Nat
  constImportKind : Nat
  undefConstKind : Nat
  guardKind : Nat
  failedKind : Nat
  declaredKind : Nat
  implicitGlobalKind : Nat
  implicitConstKind : Nat
  explicitKind : Nat
  importedKind : Nat
  globalKind : Nat
  renderRestriction : BindingNode → String
  restrictionGlobalRef : BindingNode → GlobalRefModel
  renderGlobalRef : GlobalRefModel → String
  owner : PartitionValue → GlobalRefModel
  lookupPartition : Nat → PartitionValue
  nextPartition : PartitionValue → Option Nat

def partitionFlags (runtime : PartitionRuntime) (partition : PartitionValue) : List String :=
  [(runtime.exportedFlag, "exported"),
   (runtime.implicitlyExportedFlag, "re-exported"),
   (runtime.deprecatedFlag, "deprecated"),
   (runtime.depwarnFlag, "depwarn"),
   (runtime.implicitlyDeprecatedFlag, "implicitly-deprecated")].filterMap fun pair =>
    if (partition.kindBits &&& pair.1) != 0 then some pair.2 else none

def partitionKindText (runtime : PartitionRuntime) (partition : PartitionValue) : String :=
  let kind := runtime.bindingKind partition
  if kind = runtime.backdatedConstKind then "backdated constant binding"
  else if kind = runtime.constKind then "constant binding"
  else if kind = runtime.constImportKind then "constant binding (declared with `import`)"
  else if kind = runtime.undefConstKind then "undefined const binding"
  else if kind = runtime.guardKind then "undefined binding - guard entry"
  else if kind = runtime.failedKind then "ambiguous binding - guard entry"
  else if kind = runtime.declaredKind then "weak global binding declared using `global` (implicit type Any)"
  else if kind = runtime.implicitGlobalKind then "implicit `using` resolved to global " ++
    runtime.renderGlobalRef (runtime.restrictionGlobalRef partition.restriction)
  else if kind = runtime.implicitConstKind then "implicit `using` resolved to constant"
  else if kind = runtime.explicitKind then "explicit `using` from " ++
    runtime.renderGlobalRef (runtime.restrictionGlobalRef partition.restriction)
  else if kind = runtime.importedKind then "explicit `import` from " ++
    runtime.renderGlobalRef (runtime.restrictionGlobalRef partition.restriction)
  else "global variable with type " ++ runtime.renderRestriction partition.restriction

def printPartitionBody (runtime : PartitionRuntime) (partition : PartitionValue) : String :=
  toString partition.minWorld ++ ":" ++
    (if partition.maxWorld = runtime.maxWorldValue then "∞" else toString partition.maxWorld) ++
    (if (partition.kindBits &&& runtime.flagMask) != 0 then
      " [" ++ ",".intercalate (partitionFlags runtime partition) ++ "]" else "") ++
    " - " ++ partitionKindText runtime partition

def bindingPartitionsBody (runtime : PartitionRuntime) : Nat → Option Nat → List String
  | 0, _ => []
  | _, none => []
  | fuel + 1, some id =>
    let partition := runtime.lookupPartition id
    ("\n   " ++ printPartitionBody runtime partition) ::
      bindingPartitionsBody runtime fuel (runtime.nextPartition partition)

structure BindingValue where
  globalRef : GlobalRefModel
  partitionsDefined : Bool
  firstPartition : Option Nat
  fuel : Nat
  deriving Repr

structure IntoValue where
  id : Nat
  moduleValue : ModuleValue
  deriving DecidableEq, Repr

structure IntoRuntime where
  getGlobal : ModuleValue → String → Nat
  renderModule : ModuleValue → String
  showDefault : IntoValue → String

def showIntoBody (runtime : IntoRuntime) (value : IntoValue) (field : String) : String :=
  if runtime.getGlobal value.moduleValue field = value.id then
    runtime.renderModule value.moduleValue ++ "." ++ field
  else runtime.showDefault value

structure AxisModel where
  value : DelimElement
  indices : Option DelimElement
  length : Nat
  oneTo : Bool
  deriving DecidableEq, Repr

structure SummaryValue where
  id : Nat
  typeId : TypeObject
  axes : List AxisModel
  eltype : TypeObject
  deriving Repr

structure MemoryRefValue where
  id : Nat
  memoryLength : Int
  offset : Int
  typeId : TypeObject
  deriving Repr

structure SummaryRuntime where
  renderType : TypeObject → String
  renderValue : DelimElement → String
  showarg : SummaryValue → Bool → String
  showargMemory : MemoryRefValue → Bool → String
  axes : SummaryValue → List AxisModel
  showPlainFunction : SummaryValue → String

def dimsText (dimensions : List Nat) : String :=
  if dimensions.isEmpty then "0-dimensional"
  else if dimensions.length = 1 then toString (dimensions.headD 0) ++ "-element"
  else "×".intercalate (dimensions.map toString)

def axisText (runtime : SummaryRuntime) (axis : AxisModel) : String :=
  runtime.renderValue (axis.indices.getD axis.value)

def axesText (runtime : SummaryRuntime) (axes : List AxisModel) : String :=
  "×".intercalate (axes.map (axisText runtime))

def arraySummaryBody (runtime : SummaryRuntime) (array : SummaryValue)
    (axes : List AxisModel) (includeIndices : Bool) : String :=
  dimsText (axes.map (·.length)) ++ " " ++ runtime.showarg array true ++
    if includeIndices then " with indices " ++ axesText runtime axes else ""

structure SubArrayValue where
  parent : SummaryValue
  indices : List AxisModel
  eltype : TypeObject
  deriving Repr

structure ReshapedValue where
  parent : SummaryValue
  dimensions : List Int
  eltype : TypeObject
  deriving Repr

structure ReinterpretValue where
  parent : SummaryValue
  targetType : TypeObject
  eltype : TypeObject
  deriving Repr

structure IteratorWrapperValue where
  iterator : DelimElement
  deriving DecidableEq, Repr

structure ContainerRuntime where
  summary : SummaryRuntime
  showParent : SummaryValue → Bool → String
  showIterator : DelimElement → String

def showIndicesBody (runtime : SummaryRuntime) : List AxisModel → String
  | [] => ""
  | axis :: rest => (if axis.indices.isSome then ", :" else ", " ++ axisText runtime axis) ++
    showIndicesBody runtime rest

inductive AnyTypeKind where
  | bottom | typeEgal | typeEq | other
  deriving DecidableEq, Repr

structure AnyTypeValueModel where
  object : TypeObject
  kind : AnyTypeKind
  deriving DecidableEq, Repr

structure AnyTypeRuntime where
  compact : Bool
  typeParameter : AnyTypeValueModel → TypeObject
  renderType : TypeObject → String
  showOtherType : AnyTypeValueModel → String

def showTypeEgalBody (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) : String :=
  "Core.TypeEgal{" ++ runtime.renderType (runtime.typeParameter value) ++ "}"

def showTypeEqBody (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) : String :=
  (if runtime.compact then "Type{" else "TypeEq{") ++
    runtime.renderType (runtime.typeParameter value) ++ "}"

def showAnyTypeBody (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) : String :=
  match value.kind with
  | .bottom => "Union{}"
  | .typeEgal => showTypeEgalBody runtime value
  | .typeEq => showTypeEqBody runtime value
  | .other => runtime.showOtherType value

structure TypeDispatchRuntime where
  compact : Bool
  isTypeEgal : TypeObject → Bool
  showTypeEgal : TypeObject → String
  printWithoutParams : TypeObject → Bool
  showTypeName : TypeObject → String
  showAlias : TypeObject → Option String
  isTypeEq : TypeObject → Bool
  showTypeEq : TypeObject → String
  asDataType : TypeObject → Bool
  showDatatype : TypeObject → List TypeVarValue → String
  unionTypes : TypeObject → Option (List TypeObject)
  showUnionAliases : TypeObject → Option String
  bottomId : Nat
  unwrapUnionAll : TypeObject → List TypeVarValue × TypeObject
  ioHasTypevarName : String → TypeObject → Bool
  freshTypevar : TypeVarValue → Nat → TypeVarValue
  instantiate : TypeObject → TypeVarValue → TypeVarValue → TypeObject
  renderType : TypeObject → String
  showWheres : List TypeVarValue → String

def uniqueBinder (runtime : TypeDispatchRuntime) (whole : TypeObject)
    (body : TypeObject) (binder : TypeVarValue) : TypeVarValue × TypeObject :=
  if binder.name = "_" || runtime.ioHasTypevarName binder.name whole then
    let rec find : Nat → TypeVarValue × TypeObject
      | 0 => (binder, body)
      | fuel + 1 =>
        let fresh := runtime.freshTypevar binder (fuel + 1)
        if runtime.ioHasTypevarName fresh.name whole then find fuel
        else (fresh, runtime.instantiate body binder fresh)
    find 64
  else (binder, body)

def showTypeDispatchBody (runtime : TypeDispatchRuntime) (input : TypeObject) : String :=
  if runtime.isTypeEgal input then runtime.showTypeEgal input
  else if runtime.printWithoutParams input then runtime.showTypeName input
  else if runtime.compact then match runtime.showAlias input with
    | some alias => alias
    | none =>
      if runtime.isTypeEq input then runtime.showTypeEq input
      else if runtime.asDataType input then runtime.showDatatype input []
      else match runtime.unionTypes input with
        | some types => match runtime.showUnionAliases input with
          | some aliases => aliases
          | none => "Union{" ++ ",".intercalate (types.map runtime.renderType) ++ "}"
        | none => if input.id = runtime.bottomId then "Union{}" else
          let (binders, initialBody) := runtime.unwrapUnionAll input
          let (wheres, body) := binders.foldl (fun (wheres, body) binder =>
            let result := uniqueBinder runtime input body binder
            (wheres ++ [result.1], result.2)) ([], initialBody)
          (if runtime.asDataType body then runtime.showDatatype body wheres
           else runtime.renderType body) ++ runtime.showWheres wheres
  else if runtime.isTypeEq input then runtime.showTypeEq input
  else if runtime.asDataType input then runtime.showDatatype input []
  else match runtime.unionTypes input with
    | some types => "Union{" ++ ",".intercalate (types.map runtime.renderType) ++ "}"
    | none => if input.id = runtime.bottomId then "Union{}" else
      let (binders, initialBody) := runtime.unwrapUnionAll input
      let (wheres, body) := binders.foldl (fun (wheres, body) binder =>
        let result := uniqueBinder runtime input body binder
        (wheres ++ [result.1], result.2)) ([], initialBody)
      (if runtime.asDataType body then runtime.showDatatype body wheres
       else runtime.renderType body) ++ runtime.showWheres wheres

structure VisibilityBinding where
  id : Nat
  deriving DecidableEq, Repr

structure VisibilityPartition where
  kind : Nat
  restrictionId : Nat
  deriving DecidableEq, Repr

structure VisibilityRuntime where
  isDeprecated : ModuleValue → SymbolValue → Bool
  isDefinedGlobal : ModuleValue → SymbolValue → Bool
  binding : ModuleValue → SymbolValue → VisibilityBinding
  worldAge : Nat
  lookupPartition : Nat → VisibilityBinding → VisibilityPartition
  explicitlyImported : Nat → Bool
  restrictionBinding : VisibilityPartition → VisibilityBinding
  definedConst : Nat → Bool

def followImports (runtime : VisibilityRuntime) (parent : VisibilityBinding) :
    Nat → VisibilityBinding → VisibilityBinding × Bool
  | 0, current => (current, current.id = parent.id)
  | fuel + 1, current =>
    if current.id = parent.id then (current, true)
    else
      let partition := runtime.lookupPartition runtime.worldAge current
      if runtime.explicitlyImported partition.kind then
        followImports runtime parent fuel (runtime.restrictionBinding partition)
      else (current, false)

def isVisibleBody (runtime : VisibilityRuntime) (symbol : SymbolValue)
    (parent origin : ModuleValue) : Bool :=
  if runtime.isDeprecated parent symbol || !runtime.isDefinedGlobal origin symbol ||
      !runtime.isDefinedGlobal parent symbol then false
  else
    let parentBinding := runtime.binding parent symbol
    let originBinding := runtime.binding origin symbol
    let followed := followImports runtime parentBinding 64 originBinding
    if followed.2 then true else
    let parentPartition := runtime.lookupPartition runtime.worldAge parentBinding
    let originPartition := runtime.lookupPartition runtime.worldAge followed.1
    runtime.definedConst parentPartition.kind && runtime.definedConst originPartition.kind &&
      parentPartition.restrictionId = originPartition.restrictionId

structure GlobalFunctionRuntime where
  dataTypeNameId : Nat
  concrete : TypeNameValue → Bool
  moduleDefined : TypeNameValue → Bool
  isDefinedGlobal : String → String → Bool
  isConst : String → String → Bool
  globalIsaWrapper : String → String → TypeNameValue → Bool

def isGlobalFunctionBody (runtime : GlobalFunctionRuntime) (typeName : TypeNameValue)
    (globalName : Option String) : Bool :=
  match globalName with
  | none => false
  | some name => runtime.concrete typeName && typeName.id ≠ runtime.dataTypeNameId &&
    !name.contains '#' && !name.contains '@' && runtime.moduleDefined typeName &&
    runtime.isDefinedGlobal typeName.moduleName name && runtime.isConst typeName.moduleName name &&
    runtime.globalIsaWrapper typeName.moduleName name typeName

structure WorldRuntime where
  bindingDefined : TypeNameValue → Bool
  firstPartition : TypeNameValue → Option Nat
  lookup : Nat → PartitionValue
  next : PartitionValue → Option Nat
  definedConst : Nat → Bool
  restrictionIsTypeSubtype : BindingNode → TypeNameValue → Bool
  maxWorld : Nat

def checkWorldBody (runtime : WorldRuntime) (typeName : TypeNameValue) : Option (Int × Int) :=
  if !runtime.bindingDefined typeName then none else
  let rec search : Nat → Option Nat → Option (Int × Int)
    | 0, _ => none
    | _, none => none
    | fuel + 1, some id =>
      let partition := runtime.lookup id
      if runtime.definedConst partition.kindBits &&
          runtime.restrictionIsTypeSubtype partition.restriction typeName then
        if partition.maxWorld = runtime.maxWorld then none
        else some (Int.ofNat partition.minWorld, Int.ofNat partition.maxWorld)
      else search fuel (runtime.next partition)
  search 64 (runtime.firstPartition typeName)

structure ShowTypeNameRuntime where
  unionAllNameId : Nat
  compact : Bool
  originModule : Option ModuleValue
  globalFunctionRuntime : GlobalFunctionRuntime
  visibilityRuntime : VisibilityRuntime
  worldRuntime : WorldRuntime
  symbolFromName : String → SymbolValue
  moduleFromName : String → ModuleValue
  renderModule : ModuleValue → String
  showSymbol : SymbolValue → String
  idStart : Char → Bool
  quotedSymbolIds : List Nat

def showTypeNameBody (runtime : ShowTypeNameRuntime) (typeName : TypeNameValue) : String :=
  if typeName.id = runtime.unionAllNameId then "UnionAll" else
  let globalName := typeName.singletonName
  let globalFunction := isGlobalFunctionBody runtime.globalFunctionRuntime typeName (some globalName)
  let symbol := runtime.symbolFromName (if globalFunction then globalName else typeName.name)
  let world := checkWorldBody runtime.worldRuntime typeName
  let module := runtime.moduleFromName typeName.moduleName
  let qualify := !runtime.compact && typeName.moduleFieldDefined && match runtime.originModule with
    | none => true
    | some origin => !isVisibleBody runtime.visibilityRuntime symbol module origin
  let symbolText := runtime.showSymbol symbol
  let firstChar := symbolText.toList.headD 'a'
  let needsQuote := globalFunction && !runtime.idStart firstChar
  let parens := needsQuote && runtime.quotedSymbolIds.contains symbol.id
  (if globalFunction then "typeof(" else "") ++
    (if world.isSome then "@world(" else "") ++
    (if qualify then runtime.renderModule module ++ "." else "") ++
    (if qualify && needsQuote then ":" else "") ++
    (if qualify && parens then "(" else "") ++ symbolText ++
    (match world with | some (lo, hi) => ", " ++ toString lo ++ ":" ++ toString hi ++ ")" | none => "") ++
    (if qualify && parens then ")" else "") ++ (if globalFunction then ")" else "")

inductive NestedParameter where
  | type (value : TypeObject)
  | symbols (values : List SymbolValue)
  | other (id : Nat)
  deriving Repr

structure NestedDatatype where
  id : Nat
  name : TypeNameValue
  parameters : List NestedParameter
  deriving Repr

inductive DatatypeParameter where
  | type (value : TypeObject)
  | typevar (value : TypeVarValue)
  | vararg (type : TypeObject) (length : Option Nat)
  | symbols (values : List SymbolValue)
  | datatype (value : NestedDatatype)
  | other (id : Nat)
  deriving Repr

structure DatatypeModel where
  id : Nat
  name : TypeNameValue
  parameters : List DatatypeParameter
  deriving Repr

structure KwargsRuntime where
  pairsTypeNameId : Nat
  namedTupleTypeNameId : Nat
  isSymbolType : DatatypeParameter → Bool
  isNothingType : DatatypeParameter → Bool
  eltype : NestedDatatype → DatatypeParameter
  sameParameter : DatatypeParameter → DatatypeParameter → Bool

def maybeKwargsBody (runtime : KwargsRuntime) (datatype : DatatypeModel) : Option NestedDatatype :=
  if datatype.name.id ≠ runtime.pairsTypeNameId || datatype.parameters.length ≠ 4 then none
  else match datatype.parameters with
  | first :: second :: third :: .datatype fourth :: [] =>
    if !runtime.isSymbolType first || fourth.name.id ≠ runtime.namedTupleTypeNameId ||
        fourth.parameters.length ≠ 2 || !runtime.sameParameter second (runtime.eltype fourth) ||
        !runtime.isNothingType third then none
    else match fourth.parameters with
      | .symbols _ :: .type _ :: [] => some fourth
      | _ => none
  | _ => none

structure DatatypeRuntime where
  tupleNameId : Nat
  namedTupleNameId : Nat
  anyTypeId : Nat
  backtrace : Bool
  kwargsRuntime : KwargsRuntime
  sameParameter : DatatypeParameter → DatatypeParameter → Bool
  renderParameter : DatatypeParameter → String
  renderSymbol : SymbolValue → String
  renderTypeName : TypeNameValue → String
  showTypeparams : List DatatypeParameter → List TypeVarValue → String

def nestedTypes (datatype : NestedDatatype) : List TypeObject :=
  datatype.parameters.filterMap fun parameter => match parameter with
  | .type value => some value
  | _ => none

def showNamedTupleFields (runtime : DatatypeRuntime) (symbols : List SymbolValue)
    (types : List TypeObject) : String :=
  ", ".intercalate (symbols.zipIdx.map fun (symbol, index) =>
    let typeText := match types[index]? with
      | some type => if type.id = runtime.anyTypeId then "" else "::" ++
        runtime.renderParameter (.type type)
      | none => ""
    runtime.renderSymbol symbol ++ typeText)

def showDatatypeBody (runtime : DatatypeRuntime) (datatype : DatatypeModel)
    (wheres : List TypeVarValue) : String :=
  let parameters := datatype.parameters
  if datatype.name.id = runtime.tupleNameId then
    if parameters.isEmpty then "Tuple{}" else
    let last := parameters.getLastD (.other 0)
    let (element, varargLength, varargKind) := match last with
      | .vararg type (some length) => (.type type, length, 1)
      | .vararg type none => (.type type, 0, 2)
      | other => (other, 1, 0)
    let fullLength := if varargKind = 1 then parameters.length + varargLength - 1
      else parameters.length
    let tailLength := if varargKind = 2 then 1 else
      (parameters.dropLast.reverse.takeWhile (runtime.sameParameter · element)).length + 1
    if (varargKind = 2 && parameters.length = 1) ||
        ((varargKind = 0 || varargKind = 1) && tailLength = fullLength && fullLength > 3) then
      "NTuple{" ++ (if varargKind = 2 then "N" else toString fullLength) ++ ", " ++
        runtime.renderParameter element ++ "}"
    else
      let headLength := if tailLength > 3 then fullLength - tailLength else fullLength
      let heads := (List.range headLength).map fun index =>
        runtime.renderParameter (if varargKind = 1 && index ≥ parameters.length - 1 then
          element else parameters.getD index element)
      let tail := if headLength < fullLength then
        (if heads.isEmpty then "" else ", ") ++ "Vararg{" ++ runtime.renderParameter element ++
          ", " ++ toString (fullLength - headLength) ++ "}" else ""
      "Tuple{" ++ ", ".intercalate heads ++ tail ++ "}"
  else if datatype.name.id = runtime.namedTupleNameId then
    match parameters with
    | .symbols symbols :: .datatype types :: [] =>
      let typeValues := nestedTypes types
      if typeValues.length = symbols.length then
        "@NamedTuple{" ++ showNamedTupleFields runtime symbols typeValues ++ "}"
      else runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
    | _ => runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
  else if runtime.backtrace then match maybeKwargsBody runtime.kwargsRuntime datatype with
    | some kwargs => match kwargs.parameters with
      | .symbols symbols :: .type _ :: [] =>
        "@Kwargs{" ++ showNamedTupleFields runtime symbols (nestedTypes kwargs) ++ "}"
      | _ => runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
    | none => runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres
  else runtime.renderTypeName datatype.name ++ runtime.showTypeparams parameters wheres

structure SupertypeRuntime where
  anyTypeId : Nat
  supertype : TypeObject → TypeObject
  render : TypeObject → String

def showSupertypesBody (runtime : SupertypeRuntime) : Nat → TypeObject → String
  | 0, type => runtime.render type
  | fuel + 1, type =>
    if type.id = runtime.anyTypeId then runtime.render type else
    let parent := runtime.supertype type
    runtime.render type ++ " <: " ++ showSupertypesBody runtime fuel parent

structure ShowMacroRuntime where
  showUnquoted : AstValue → String
  escape : AstValue → AstValue
  evaluate : AstValue → DelimElement
  repr : DelimElement → String

structure ShowMacroExpansion where
  lines : List String
  returnValue : Option DelimElement
  deriving DecidableEq, Repr

def showMacroBody (runtime : ShowMacroRuntime) (expressions : List AstValue) : ShowMacroExpansion :=
  let lines := expressions.map fun expression =>
    runtime.showUnquoted expression ++ " = " ++ runtime.repr (runtime.evaluate (runtime.escape expression))
  ⟨lines, (expressions.getLast?).map (runtime.evaluate ∘ runtime.escape)⟩

structure ModulesRuntime where
  unwrapUnionall : TypeObject → TypeObject
  dataModule : TypeObject → Option String
  typeEqParameter : TypeObject → Option TypeObject
  typeEgalParameter : TypeObject → Option TypeObject
  unionParts : TypeObject → Option (TypeObject × TypeObject)

def modulesOfTypeBody (runtime : ModulesRuntime) : Nat → TypeObject → List String
  | 0, _ => []
  | fuel + 1, input =>
    let value := runtime.unwrapUnionall input
    match runtime.dataModule value with
    | some moduleName => [moduleName]
    | none => match runtime.typeEqParameter value with
      | some parameter => modulesOfTypeBody runtime fuel parameter
      | none => match runtime.typeEgalParameter value with
        | some parameter => modulesOfTypeBody runtime fuel parameter
        | none => match runtime.unionParts value with
          | some (left, right) =>
            (modulesOfTypeBody runtime fuel left ++ modulesOfTypeBody runtime fuel right).eraseDups
          | none => []

structure UnionAliasValue where
  found : FoundAlias
  applied : TypeObject
  unionLength : Nat
  scoreEnv : Int
  deriving Repr

structure UnionAliasRuntime where
  base : MakeAliasRuntime
  emptyUnion : TypeObject
  unionTypes : TypeObject → List TypeObject
  rewrapUnionall : TypeObject → TypeObject → TypeObject
  unionLength : TypeObject → Nat
  subtype : TypeObject → TypeObject → Bool
  union : TypeObject → TypeObject → TypeObject
  printWithoutParams : TypeObject → Bool

def unionAliasCandidate (runtime : UnionAliasRuntime) (input : TypeObject)
    (components : List TypeObject) (reference : GlobalRefValue)
    (alias : AliasObject) : Option UnionAliasValue :=
  if !runtime.base.isType alias || runtime.base.hasFreeTypevars alias ||
      runtime.base.printWithoutParams alias || runtime.base.isTupleSubtype ⟨alias.id⟩ then none
  else
    let env := runtime.base.intersectEnv input (runtime.base.unbounded alias)
    match runtime.base.applyAlias alias env with
    | none => none
    | some applied0 =>
      let applied := runtime.base.rewrapFree applied0 (runtime.base.findFreeTypevars input)
      if runtime.base.hasOtherFree applied (runtime.base.findFreeTypevars input) ||
          !runtime.subtype applied input then none
      else if !(components.any fun component => runtime.subtype component applied) then none
      else some ⟨⟨reference, alias, if runtime.printWithoutParams input then [] else env⟩,
        applied, runtime.unionLength applied, -Int.ofNat env.length⟩

def insertUnionAlias (value : UnionAliasValue) : List UnionAliasValue → List UnionAliasValue
  | [] => [value]
  | head :: tail =>
    if value.unionLength > head.unionLength ||
        (value.unionLength = head.unionLength && value.scoreEnv > head.scoreEnv) then
      value :: head :: tail else head :: insertUnionAlias value tail

def sortUnionAliases (values : List UnionAliasValue) : List UnionAliasValue :=
  values.foldr insertUnionAlias []

def makeTypealiasesBody (runtime : UnionAliasRuntime) (input : TypeObject) :
    List UnionAliasValue × TypeObject :=
  if input.id = runtime.base.anyId || runtime.base.isTupleSubtype input then ([], runtime.emptyUnion)
  else
    let components := runtime.unionTypes input |>.map (runtime.rewrapUnionall · input)
    let aliases := (runtime.base.modulesOf input).map runtime.base.normalizeModule |>.flatMap fun moduleName =>
      (runtime.base.names moduleName).filterMap fun name =>
        if runtime.base.isDefinedGlobal moduleName name && !runtime.base.isDeprecated moduleName name &&
            runtime.base.isConst moduleName name then
          let alias := runtime.base.getGlobal moduleName name
          unionAliasCandidate runtime input components ⟨moduleName, name⟩ alias
        else none
    let sorted := sortUnionAliases aliases
    let (_, applied, kept) := sorted.foldl (fun (previous, applied, kept) alias =>
      let score := (alias.unionLength, alias.scoreEnv)
      if alias.unionLength < 2 then
        if runtime.subtype alias.applied applied then (previous, applied, kept)
        else (previous, runtime.union applied alias.applied, kept ++ [alias])
      else if score = previous || !runtime.subtype alias.applied applied then
        (score, runtime.union applied alias.applied, kept ++ [alias])
      else (previous, applied, kept)) ((0, 0), runtime.emptyUnion, [])
    (kept, applied)

structure ShowUnionRuntime where
  aliases : UnionAliasRuntime
  renderType : TypeObject → String
  makeWheres : FoundAlias → TypeObject → List TypeVarValue
  renderAlias : FoundAlias → List TypeVarValue → String
  renderWheres : List TypeVarValue → String
  isTypeVar : TypeObject → Bool

def showUnionAliasesBody (runtime : ShowUnionRuntime) (input : TypeObject) : Bool × String :=
  let (aliases, applied) := makeTypealiasesBody runtime.aliases input
  if aliases.isEmpty then (false, "") else
  let components := runtime.aliases.unionTypes input
  let remaining := components.filter fun type =>
    !runtime.isTypeVar type && !runtime.aliases.subtype type applied
  let typevars := components.filter runtime.isTypeVar
  let aliasTexts := aliases.map fun alias =>
    let wheres := runtime.makeWheres alias.found alias.applied
    runtime.renderAlias alias.found wheres ++ runtime.renderWheres wheres
  let pieces := remaining.map runtime.renderType ++ aliasTexts ++ typevars.map runtime.renderType
  (true, if remaining.isEmpty && typevars.isEmpty && aliases.length = 1 then
    aliasTexts.headD "" else "Union{" ++ ", ".intercalate pieces ++ "}")

structure TypePlainRuntime where
  printWithoutParams : TypeObject → Bool
  makeAlias : TypeObject → Option FoundAlias
  unwrapIsUnion : TypeObject → Bool
  unionAliasesApplied : TypeObject → TypeObject
  subtype : TypeObject → TypeObject → Bool
  renderCompact : TypeObject → String
  renderNormal : TypeObject → String
  compactContext : Bool
  asDataTypeName : TypeObject → Option TypeNameValue
  unionAllTypeId : Nat
  isGlobalFunction : TypeNameValue → String → Bool
  renderSymbol : String → String

def showTypePlainBody (runtime : TypePlainRuntime) (input : TypeObject) : List WriteEvent :=
  let aliasWorks := (runtime.makeAlias input).isSome ||
    (runtime.unwrapIsUnion input && runtime.subtype input (runtime.unionAliasesApplied input))
  if !runtime.printWithoutParams input && aliasWorks then
    [.plain (runtime.renderCompact input)] ++
    (if runtime.compactContext then [] else
      [.styled " (alias for " "light_black" false,
       .styled (runtime.renderNormal input) "light_black" false,
       .styled ")" "light_black" false])
  else
    let normal := [.plain (runtime.renderNormal input)]
    if runtime.compactContext || input.id = runtime.unionAllTypeId then normal
    else match runtime.asDataTypeName input with
    | some typeName => if runtime.isGlobalFunction typeName typeName.singletonName then
        normal ++ [.plain (" (singleton type of function " ++
          runtime.renderSymbol typeName.singletonName ++ ", subtype of Function)")]
      else normal
    | none => normal

structure DumpDatatype where
  typeId : TypeObject
  isStruct : Bool
  isMutable : Bool
  isTuple : Bool
  isPrimitive : Bool
  isAbstract : Bool
  isAny : Bool
  supertype : TypeObject
  unknownNamedTuple : Bool
  fields : List (String × Bool × Option TypeObject)
  deriving Repr

inductive DumpValue where
  | bottom
  | module (value : ModuleValue)
  | string (value : String)
  | symbol (value : SymbolValue)
  | unionType (value : TypeObject)
  | pointer (address : Nat)
  | function (value : FunctionValue)
  | simpleVector (slots : List (Option DumpValue))
  | array (elementType : TypeObject) (shape : String) (numeric : Bool)
      (slots : List (Option DumpValue))
  | datatype (value : DumpDatatype)
  | object (typeId : TypeObject) (fields : List (String × Option DumpValue))
  | leaf (typeId : TypeObject) (id : Nat)
  deriving Repr

structure DumpRuntime where
  renderBottom : String
  renderModule : ModuleValue → String
  renderString : String → String
  renderSymbol : SymbolValue → String
  renderType : TypeObject → String
  renderPointer : Nat → String
  renderFunction : FunctionValue → String
  renderLeaf : Nat → String
  renderValue : DumpValue → String
  circular : DumpValue → Bool

def dumpIndent (indent : String) := indent ++ "  "

def dumpBody (runtime : DumpRuntime) (limit : Bool) : Nat → String → DumpValue → String
  | _, _, .bottom => runtime.renderBottom
  | _, _, .module value => "Module " ++ runtime.renderModule value
  | _, _, .string value => "String " ++ runtime.renderString value
  | _, _, .symbol value => "Symbol " ++ runtime.renderSymbol value
  | _, _, .unionType value => runtime.renderType value
  | _, _, .pointer address => runtime.renderPointer address
  | _, _, .function value => runtime.renderFunction value ++ " (function of type " ++
      runtime.renderType ⟨value.datatype.id⟩ ++ ")"
  | _, _, .simpleVector [] => "empty SimpleVector"
  | 0, _, .simpleVector _ => "SimpleVector"
  | depth + 1, indent, .simpleVector slots =>
    "SimpleVector" ++ String.join (slots.zipIdx.map fun (slot, index) =>
      "\n" ++ indent ++ "  " ++ toString (index + 1) ++ ": " ++ match slot with
      | none => "#undef"
      | some value => dumpBody runtime limit depth (dumpIndent indent) value)
  | _, _, .array elementType shape true slots =>
    "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ") " ++
      runtime.renderValue (.array elementType shape true slots)
  | 0, _, .array elementType shape false _ =>
    "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ")"
  | depth + 1, indent, value@(.array elementType shape false slots) =>
    let header := "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ")"
    if slots.isEmpty || runtime.circular value then header else
    let indices := if limit && slots.length > 10 then
      [0, 1, 2, 3, 4] ++ [slots.length - 5, slots.length - 4,
        slots.length - 3, slots.length - 2, slots.length - 1]
      else List.range slots.length
    header ++ "\n" ++ String.join (indices.zipIdx.map fun (index, shownIndex) =>
      (if limit && slots.length > 10 && shownIndex = 5 then indent ++ "  ...\n" else "") ++
      indent ++ "  " ++ toString (index + 1) ++ ": " ++ match slots[index]? with
      | some (some child) => dumpBody runtime limit depth (dumpIndent indent) child
      | _ => "#undef" ++ if shownIndex + 1 < indices.length then "\n" else "")
  | depth, indent, .datatype datatype =>
    let header := (if datatype.isMutable && datatype.isStruct then "mutable " else "") ++
      (if datatype.isStruct && !datatype.isTuple then "struct " else "") ++
      (if datatype.isPrimitive then "primitive type " else "") ++
      (if datatype.isAbstract then "abstract type " else "") ++ runtime.renderType datatype.typeId ++
      (if datatype.isAny then "" else " <: " ++ runtime.renderType datatype.supertype)
    if depth = 0 || datatype.isTuple || datatype.isAbstract || datatype.unknownNamedTuple then header else
      header ++ String.join (datatype.fields.map fun (name, constant, fieldType) =>
        "\n" ++ indent ++ "  " ++ (if datatype.isMutable && constant then "const " else "") ++
        name ++ match fieldType with | none => "" | some type => "::" ++ runtime.renderType type)
  | 0, _, .object typeId _ => runtime.renderType typeId
  | depth + 1, indent, value@(.object typeId fields) =>
    let header := runtime.renderType typeId
    if fields.isEmpty then header ++ " " ++ runtime.renderValue value
    else if runtime.circular value then header else header ++ String.join (fields.map fun (name, field) =>
      "\n" ++ indent ++ "  " ++ name ++ ": " ++ match field with
      | none => "#undef"
      | some child => dumpBody runtime limit depth (dumpIndent indent) child)
  | _, _, .leaf typeId id => runtime.renderType typeId ++ " " ++ runtime.renderLeaf id

def dumpElementsBody (runtime : DumpRuntime) (depth : Nat) (indent : String)
    (slots : List (Option DumpValue)) (first last : Nat) : String :=
  String.join ((List.range (last + 1 - first)).map fun offset =>
    let index := first + offset
    indent ++ "  " ++ toString index ++ ": " ++
      (match slots[index - 1]? with
       | some (some value) => dumpBody runtime false (depth - 1) (dumpIndent indent) value
       | _ => "#undef") ++ if index < last then "\n" else "")

def emphasizeBody (runtime : StyleRuntime) (io : StyledIO) (text color : String) : List WriteEvent :=
  if runtime.colorEnabled io then [.styled text color true]
  else [.plain (runtime.uppercase text)]

def showLineBody (runtime : StyleRuntime) (line : DelimElement)
    (file : Option DelimElement) : List WriteEvent :=
  let text := match file with
    | none => "#= line " ++ runtime.renderLine line ++ " =#"
    | some path => "#= " ++ runtime.renderFile path ++ ":" ++ runtime.renderLine line ++ " =#"
  [.styled text "light_black" false]

structure AliasVarValue where
  id : Nat
  name : String
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

inductive AliasExpr where
  | atom (id : Nat)
  | unionAll (binder : AliasVarValue) (body : AliasExpr)
  deriving DecidableEq, Repr

structure AliasRuntime where
  bottomId : Nat
  anyId : Nat
  newTypeVar : String → AliasVarValue
  newTypeVarLower : ∀ name, (newTypeVar name).lower = bottomId
  newTypeVarUpper : ∀ name, (newTypeVar name).upper = anyId
  instantiate : AliasVarValue → AliasExpr → AliasVarValue → AliasExpr

def unboundedAlias (runtime : AliasRuntime) : AliasExpr → AliasExpr
  | .atom id => .atom id
  | .unionAll binder body =>
    let rewritten := unboundedAlias runtime body
    if binder.lower = runtime.bottomId ∧ binder.upper = runtime.anyId then
      if rewritten = body then .unionAll binder body else .unionAll binder rewritten
    else
      let fresh := runtime.newTypeVar binder.name
      .unionAll fresh (runtime.instantiate binder rewritten fresh)

def outerBinderUnbounded (runtime : AliasRuntime) : AliasExpr → Bool
  | .atom _ => true
  | .unionAll binder _ =>
    binder.lower == runtime.bottomId && binder.upper == runtime.anyId

structure IterValue where
  elements : List Nat
  isKeySet : Bool
  deriving DecidableEq, Repr

structure IterRuntime where
  compact : Bool
  limit : Bool
  color : Bool
  displaysize : Int × Int
  renderIter : IterValue → String
  summary : IterValue → String
  renderValue : Nat → String
  sprintShow : Nat → String
  truncate : Bool → String → Nat → String

def showKeyValueBody (runtime : IterRuntime) (iter : IterValue) : String :=
  let entries := iter.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value)
        (max 4 (runtime.displaysize.2 - 2)).toNat : Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  Remaining.showKeyValueIter (runtime.summary iter) (runtime.renderIter iter)
    (if iter.isKeySet then "Keys" else "Values") entries runtime.compact runtime.limit rows

structure SetValue where
  elements : List Nat
  deriving DecidableEq, Repr

structure SetRuntime where
  limit : Bool
  color : Bool
  displaysize : Int × Int
  renderSet : SetValue → String
  summary : SetValue → String
  circular : SetValue → Bool
  renderValue : Nat → String
  sprintShow : Nat → String
  truncate : Bool → String → Nat → String
  showarg : SetValue → Bool → String

def showSetBody (runtime : SetRuntime) (set : SetValue) : String :=
  let cols := max 4 (runtime.displaysize.2 - 2)
  let entries := set.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value) cols.toNat :
        Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  Remaining.showSetPlain (runtime.summary set) (runtime.renderSet set) entries
    (runtime.circular set) runtime.limit rows

structure DictValue where
  pairs : List (Nat × Nat)
  hasLength : Bool
  deriving DecidableEq, Repr

structure DictRuntime where
  limit : Bool
  color : Bool
  hasCompactKey : Bool
  displaysize : Int × Int
  renderDict : DictValue → String
  summary : DictValue → String
  circular : DictValue → Bool
  sprintKey : Nat → String
  sprintValue : Nat → String
  renderValue : Nat → String
  textWidth : Bool → String → Nat
  truncate : Bool → String → Nat → Bool → String

def widthStep (runtime : DictRuntime) (cols : Nat) (current : Nat)
    (text : String) : Nat := min cols (max current (runtime.textWidth runtime.color text))

def showDictBody (runtime : DictRuntime) (dict : DictValue) : String :=
  if dict.pairs.isEmpty || !dict.hasLength then runtime.renderDict dict
  else
    let summary := runtime.summary dict
    if runtime.circular dict then summary ++ ":"
    else if runtime.limit && runtime.displaysize.1 - 3 < 2 then summary ++ ": …"
    else
      let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else dict.pairs.length
      let cols := if runtime.limit then (max 12 runtime.displaysize.2 - 6).toNat else 0
      let shownPairs := dict.pairs.take rows
      let keyStrings := shownPairs.map (runtime.sprintKey ·.1)
      let valueStrings := shownPairs.map (runtime.sprintValue ·.2)
      let initialKeyWidth := keyStrings.foldl (widthStep runtime cols) 0
      let valueWidth := valueStrings.foldl (widthStep runtime cols) 0
      let keyWidth := if runtime.limit &&
          initialKeyWidth > max (cols / 2) (cols - valueWidth) then
        max ((cols + 2) / 3) (cols - valueWidth) else initialKeyWidth
      let entries := dict.pairs.map fun pair =>
        { key := runtime.sprintKey pair.1
          value := runtime.renderValue pair.2
          alignedLimitedKey := runtime.truncate runtime.color
            (runtime.sprintKey pair.1) keyWidth true
          limitedValue := runtime.truncate runtime.color
            (runtime.sprintValue pair.2) (cols - keyWidth) false : Remaining.DictEntry }
      Remaining.showDictPlain summary (runtime.renderDict dict) entries dict.hasLength
        false runtime.limit rows

inductive OptionValue where
  | ordinary (id : Nat)
  | ptrUInt8 (address : Option Nat)
  | ptrPtrUInt8 (address : Nat)
  | string (text : String)
  deriving DecidableEq, Repr

structure JLOptionsValue where
  fields : List (String × OptionValue)
  deriving DecidableEq, Repr

structure JLOptionsRuntime where
  unsafeString : Nat → String
  unsafeLoadCommands : Nat → OptionValue
  repr : OptionValue → String

def normalizeOptionValue (runtime : JLOptionsRuntime) : OptionValue → OptionValue
  | .ptrUInt8 none => .string ""
  | .ptrUInt8 (some address) => .string (runtime.unsafeString address)
  | .ptrPtrUInt8 address => runtime.unsafeLoadCommands address
  | value => value

def showJLOptionsBody (runtime : JLOptionsRuntime) (opt : JLOptionsValue) : Out :=
  let nfields := opt.fields.length
  ["JLOptions(", "\n"] ++ (opt.fields.zipIdx.flatMap fun ((field, value), index) =>
    let value := normalizeOptionValue runtime value
    ["  ", field, " = ", runtime.repr value,
      if index + 1 < nfields then "," else "", "\n"]) ++ [")"]

structure TaskValue where
  id : Nat
  deriving DecidableEq, Repr

structure TaskRuntime where
  render : TaskValue → String
  isFailed : TaskValue → Bool
  showException : TaskValue → Bool → String

def showTaskBody (runtime : TaskRuntime) (task : TaskValue) : Out :=
  [runtime.render task] ++
    if runtime.isFailed task then ["\n", runtime.showException task false] else []

structure CancellationValue where
  id : Nat
  nparents : Nat
  deriving DecidableEq, Repr

structure SeverityValue where
  request : UInt8
  deriving DecidableEq, Repr

structure CancellationRuntime where
  cancelSeverity : CancellationValue → Option SeverityValue
  repr : UInt8 → String

def showCancellationBody (runtime : CancellationRuntime)
    (source : CancellationValue) : Out :=
  ["CancellationTokenSource("] ++
  [match runtime.cancelSeverity source with
   | none => "active"
   | some severity =>
     let request := severity.request
     if request = 0x1 then "cancelled"
     else if request = 0x3 then "cancelled, abandon external"
     else if request = 0x4 then "cancelled, abandon all"
     else "cancelled, severity " ++ runtime.repr request] ++
  (if source.nparents > 0 then
    [", ", toString source.nparents,
      if source.nparents = 1 then " parent" else " parents"] else []) ++ [")"]

structure IOContextRuntime where
  getColor : IOCtx.BaseIO → Bool
  renderBase : IOCtx.BaseIO → String

inductive LockEffect where
  | lock
  | unlock
  deriving DecidableEq, Repr

def lockEffect (effect : LockEffect) (io : IOCtx.JIO) : IOCtx.BaseIO × LockEffect :=
  match IOCtx.unwrapcontext io with
  | .plain base => (base, effect)
  | .ctx base _ => (base, effect)

structure GenericValue where
  id : Nat
  deriving DecidableEq, Repr

structure GenericShowRuntime where
  stdout : IOCtx.BaseIO
  showDefault : IOCtx.BaseIO → GenericValue → Out
  showOn : IOCtx.BaseIO → GenericValue → Out
  inferenceBarrier : GenericValue → GenericValue
  showDefaultInner : IOCtx.BaseIO → GenericValue → Out

structure DefaultValue where
  typeId : Nat
  fields : List (Option GenericValue)
  bytes : List UInt8
  byteSize : Nat
  bitSize : Nat
  deriving DecidableEq, Repr

structure DefaultRuntime where
  renderType : Nat → String
  showCircular : IOCtx.BaseIO → DefaultValue → Option String
  showField : IOCtx.BaseIO → GenericValue → String

def defaultFields (runtime : DefaultRuntime) (io : IOCtx.BaseIO)
    (x : DefaultValue) : List Values.Field :=
  x.fields.map fun field => match field with
  | none => .undef
  | some value => .val (runtime.showField io value)

def showDefaultBody (runtime : DefaultRuntime) (io : IOCtx.BaseIO)
    (x : DefaultValue) : Out :=
  let fields := defaultFields runtime io x
  let bits := if !x.fields.isEmpty || x.byteSize = 0 then none
    else some (x.bytes, x.bitSize)
  Values.showDefault (runtime.renderType x.typeId)
    (runtime.showCircular io x) fields bits

def showAtNamedTuple (fields : List (String × Option String)) : Out :=
  fields.zipIdx.flatMap fun ((name, typ), i) =>
    (if i = 0 then [] else [", "]) ++ [name] ++ match typ with | none => [] | some t => ["::", t]

def stateIs (q : Truncate.QState) (bit : Nat) : Bool :=
  if bit = 1 then q.backslash else if bit = 2 then q.squote else if bit = 4 then q.dquote else false
def stateEnter (q : Truncate.QState) (bit : Nat) : Truncate.QState :=
  if bit = 1 then {q with backslash := true} else if bit = 2 then {q with squote := true}
  else if bit = 4 then {q with dquote := true} else q
def stateLeave (q : Truncate.QState) (bit : Nat) : Truncate.QState :=
  if bit = 1 then {q with backslash := false} else if bit = 2 then {q with squote := false}
  else if bit = 4 then {q with dquote := false} else q

def showBound (text : String) (parens : Bool) : String := if parens then "(" ++ text ++ ")" else text

/-- `show(io::IO, ::MIME"text/plain", u::UndefInitializer)`, `base/show.jl:6-10`. -/
def m6 (compact : Bool) := Values.showUndefPlain compact
def P6 : Prop := ∀ (compact : Bool), (m6 compact) = Values.showUndefPlain compact
theorem p6 : P6 := fun compact => rfl

/-- `show(io::IO, ::MIME"text/plain", r::AbstractRange)`, `base/show.jl:14-14`. -/
def m14 (runtime : RangeRuntime) (r : RangeValue) : Out := [runtime.render r]
def P14 : Prop := ∀ runtime r, m14 runtime r = [runtime.render r]
theorem p14 : P14 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", r::UnitRange)`, `base/show.jl:16-21`. -/
def m16 (runtime : RangeRuntime) (compact : Bool) (r : RangeValue) : Out :=
  [runtime.render r] ++
    (if !compact && runtime.isempty r then [" (empty range)"] else [])
def P16 : Prop := ∀ runtime compact r, m16 runtime compact r =
  [runtime.render r] ++ (if !compact && runtime.isempty r then [" (empty range)"] else [])
theorem p16 : P16 := fun _ _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", r::LinRange)`, `base/show.jl:23-32`. -/
def m23 (runtime : RangeRuntime) (r : RangeValue) : Out :=
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLinRange r]
def P23 : Prop := ∀ runtime r, m23 runtime r =
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLinRange r]
theorem p23 : P23 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", r::LogRange)`, `base/show.jl:34-39`. -/
def m34 (runtime : RangeRuntime) (r : RangeValue) : Out :=
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLogRange r]
def P34 : Prop := ∀ runtime r, m34 runtime r =
  if runtime.isempty r then [runtime.render r]
  else [runtime.summary r, ":", "\n", runtime.printLogRange r]
theorem p34 : P34 := fun _ _ => rfl

/-- `_isself(ft::DataType)`, `base/show.jl:41-53`. -/
def m41 (runtime : SelfRuntime) (ft : DataTypeValue) := isSelfBody runtime ft
def P41 : Prop := ∀ runtime ft, m41 runtime ft =
  let ftname := ft.typeName
  let name := ftname.singletonName
  if ftname.name == name then false
  else
    let mod := runtime.parentModule ft
    let bpart := runtime.lookupBindingPartition runtime.worldAge mod name
    if runtime.bindingKind bpart = runtime.backdatedConstKind then
      ft.id = runtime.typeOf bpart.restriction
    else runtime.isDefinedGlobal mod name &&
      ft.id = runtime.typeOf (runtime.getGlobal mod name)
theorem p41 : P41 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", f::Function)`, `base/show.jl:55-73`. -/
def m55 (runtime : FunctionRuntime) (compact : Bool) (f : FunctionValue) :=
  showFunctionBody runtime compact f
def P55 : Prop := ∀ runtime compact f, m55 runtime compact f =
  if compact then runtime.render f
  else
    let ft := f.datatype
    let name := ft.typeName.singletonName
    match f.kind with
    | .intrinsic => runtime.render f ++ " (intrinsic function #" ++
        toString (runtime.bitcastInt32 f) ++ ")"
    | .builtin => name ++ " (built-in function)"
    | .generic =>
      let n := f.methods.length
      let methodWord := if n = 1 then "method" else "methods"
      let stringName := name
      let shownName := if isSelfBody runtime.selfRuntime ft || stringName.contains '#' then
        stringName else "(::" ++ runtime.renderType ft ++ ")"
      let what := if shownName.startsWith "@" then "macro" else "generic function"
      shownName ++ " (" ++ what ++ " with " ++ toString n ++ " " ++ methodWord ++ ")"
theorem p55 : P55 := fun _ _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", c::ComposedFunction)`, `base/show.jl:75-75`. -/
def m75 (runtime : WrapperRuntime) (c : WrapperValue) : Out := [runtime.render c]
def P75 : Prop := ∀ runtime c, m75 runtime c = [runtime.render c]
theorem p75 : P75 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", c::Returns)`, `base/show.jl:76-76`. -/
def m76 (runtime : WrapperRuntime) (c : WrapperValue) : Out := [runtime.render c]
def P76 : Prop := ∀ runtime c, m76 runtime c = [runtime.render c]
theorem p76 : P76 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", s::Splat)`, `base/show.jl:77-77`. -/
def m77 (runtime : WrapperRuntime) (s : WrapperValue) : Out := [runtime.render s]
def P77 : Prop := ∀ runtime s, m77 runtime s = [runtime.render s]
theorem p77 : P77 := fun _ _ => rfl

/-- `ncodeunits(c::ANSIDelimiter)`, `base/show.jl:85-85`. -/
def m85 (tok : Truncate.Tok) := Truncate.Tok.ncu tok
def P85 : Prop := ∀ (tok : Truncate.Tok), (m85 tok) = Truncate.Tok.ncu tok
theorem p85 : P85 := fun tok => rfl

/-- `textwidth(::ANSIDelimiter)`, `base/show.jl:86-86`. -/
def m86 (tw : Char → Nat) (tok : Truncate.Tok) := Truncate.Tok.width tw tok
def P86 : Prop := ∀ (tw : Char → Nat) (tok : Truncate.Tok), (m86 tw tok) = Truncate.Tok.width tw tok
theorem p86 : P86 := fun tw tok => rfl

/-- `ANSIIterator(s::AbstractString)`, `base/show.jl:92-92`. -/
def m92 (s : List Char) := Truncate.ansiTokens s
def P92 : Prop := ∀ (s : List Char), (m92 s) = Truncate.ansiTokens s
theorem p92 : P92 := fun s => rfl

/-- `IteratorSize(::Type{<:ANSIIterator})`, `base/show.jl:94-94`. -/
def m94 (_iteratorType : String) := Truncate.iteratorSizeANSI
def P94 : Prop := ∀ iteratorType : String, m94 iteratorType = Truncate.iteratorSizeANSI
theorem p94 : P94 := fun _ => rfl

/-- `eltype(::Type{<:ANSIIterator})`, `base/show.jl:95-95`. -/
def m95 (_iteratorType : String) := Truncate.eltypeANSI
def P95 : Prop := ∀ iteratorType : String, m95 iteratorType = Truncate.eltypeANSI
theorem p95 : P95 := fun _ => rfl

/-- `iterate(I::ANSIIterator, (i, m_st)=(1, iterate(I.captures)))`, `base/show.jl:96-101`. -/
def m96 (captures : List Capture) (i : Nat) := ansiIterStep captures i
def P96 : Prop := ∀ captures i, m96 captures i =
  match captureIter captures with
  | none => none
  | some (capture, (j, newState)) =>
    let token := if (capture.matchText.map Char.utf8Size).sum = 1 then
      match capture.matchText with
      | [c] => Truncate.Tok.ch c
      | _ => Truncate.Tok.ansi capture.matchText
    else Truncate.Tok.ansi capture.matchText
    some ((i, token), (j, captureIter newState))
theorem p96 : P96 := fun _ _ => rfl

/-- `textwidth(I::ANSIIterator)`, `base/show.jl:102-102`. -/
def m102 (tw : Char → Nat) (s : List Char) := Truncate.ansiWidth tw s
def P102 : Prop := ∀ (tw : Char → Nat) (s : List Char), (m102 tw s) = Truncate.ansiWidth tw s
theorem p102 : P102 := fun tw s => rfl

/-- `_truncate_at_width_or_chars(ignore_ANSI::Bool, str::AbstractString, width::Int, rpad::Bool=false, chars="\r\n", truncmark="…")`, `base/show.jl:104-135`. -/
def m104 (tw : Char → Nat) (ignore : Bool) (s : List Char) (width : Int) (rpad : Bool) (chars mark : List Char) := Truncate.truncateAt tw ignore s width rpad chars mark
def P104 : Prop := ∀ (tw : Char → Nat) (ignore : Bool) (s : List Char) (width : Int) (rpad : Bool) (chars mark : List Char), (m104 tw ignore s width rpad chars mark) = Truncate.truncateAt tw ignore s width rpad chars mark
theorem p104 : P104 := fun tw ignore s width rpad chars mark => rfl

/-- `show(io::IO, ::MIME"text/plain", iter::Union{KeySet,ValueIterator})`, `base/show.jl:137-166`. -/
def m137 (runtime : IterRuntime) (iter : IterValue) := showKeyValueBody runtime iter
def P137 : Prop := ∀ runtime iter, m137 runtime iter =
  let entries := iter.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value)
        (max 4 (runtime.displaysize.2 - 2)).toNat : Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  if entries.isEmpty && runtime.compact then runtime.renderIter iter
  else if entries.isEmpty then runtime.summary iter
  else if runtime.limit && rows < 2 then runtime.summary iter ++ ". " ++
    (if iter.isKeySet then "Keys" else "Values") ++ ": …"
  else
    let room := if runtime.limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if runtime.limit then e.limited else e.full)
    let ellipsis := if runtime.limit && room < entries.length then ["\n  ⋮"] else []
    runtime.summary iter ++ ". " ++ (if iter.isKeySet then "Keys" else "Values") ++
      ":" ++ String.join (lines ++ ellipsis)
theorem p137 : P137 := by unfold P137; intros; rfl

/-- `show(io::IO, ::MIME"text/plain", t::AbstractDict{K,V}) where {K,V}`, `base/show.jl:168-233`. -/
def m168 (runtime : DictRuntime) (dict : DictValue) := showDictBody runtime dict
def P168 : Prop := ∀ runtime dict,
  HasResult (m168 runtime dict) ∧
  (dict.pairs.isEmpty || !dict.hasLength → m168 runtime dict = runtime.renderDict dict) ∧
  (!dict.pairs.isEmpty → dict.hasLength → runtime.circular dict →
    m168 runtime dict = runtime.summary dict ++ ":")
theorem p168 : P168 := by
  intro runtime dict
  refine ⟨hasResult _, ?_, ?_⟩
  · intro h
    simp only [m168, showDictBody]
    split <;> simp_all
  · intro hne hlen hcirc
    cases h : dict.pairs with
    | nil => simp [h] at hne
    | cons head tail => simp [m168, showDictBody, h, hlen, hcirc]

/-- `summary(io::IO, t::AbstractSet)`, `base/show.jl:235-239`. -/
def m235 (runtime : SetRuntime) (set : SetValue) : Out :=
  [runtime.showarg set true, " with ", toString set.elements.length,
    if set.elements.length = 1 then " element" else " elements"]
def P235 : Prop := ∀ runtime set, m235 runtime set =
  [runtime.showarg set true, " with ", toString set.elements.length,
    if set.elements.length = 1 then " element" else " elements"]
theorem p235 : P235 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", t::AbstractSet{T}) where T`, `base/show.jl:241-276`. -/
def m241 (runtime : SetRuntime) (set : SetValue) := showSetBody runtime set
def P241 : Prop := ∀ runtime set, m241 runtime set =
  let cols := max 4 (runtime.displaysize.2 - 2)
  let entries := set.elements.map fun value =>
    { full := runtime.renderValue value
      limited := runtime.truncate runtime.color (runtime.sprintShow value) cols.toNat :
        Remaining.IterEntry }
  let rows := if runtime.limit then (runtime.displaysize.1 - 4).toNat else entries.length
  if entries.isEmpty then runtime.renderSet set
  else if runtime.circular set then runtime.summary set ++ ":"
  else if runtime.limit && rows < 2 then runtime.summary set ++ ": …"
  else
    let room := if runtime.limit then rows - 1 else entries.length
    let shown := entries.take room
    let lines := shown.map (fun e => "\n  " ++ if runtime.limit then e.limited else e.full)
    let ellipsis := if runtime.limit && room < entries.length then ["\n  ⋮ "] else []
    runtime.summary set ++ ":" ++ String.join (lines ++ ellipsis)
theorem p241 : P241 := by unfold P241; intros; rfl

/-- `show(io::IO, ::MIME"text/plain", opt::JLOptions)`, `base/show.jl:278-292`. -/
def m278 (runtime : JLOptionsRuntime) (opt : JLOptionsValue) :=
  showJLOptionsBody runtime opt
def P278 : Prop := ∀ runtime opt, m278 runtime opt =
  let nfields := opt.fields.length
  ["JLOptions(", "\n"] ++ opt.fields.zipIdx.flatMap (fun ((field, value), index) =>
    let value := normalizeOptionValue runtime value
    ["  ", field, " = ", runtime.repr value,
      if index + 1 < nfields then "," else "", "\n"]) ++ [")"]
theorem p278 : P278 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", t::Task)`, `base/show.jl:294-300`. -/
def m294 (runtime : TaskRuntime) (task : TaskValue) := showTaskBody runtime task
def P294 : Prop := ∀ runtime task, m294 runtime task =
  [runtime.render task] ++
    if runtime.isFailed task then ["\n", runtime.showException task false] else []
theorem p294 : P294 := fun _ _ => rfl

/-- `show(io::IO, src::Core.CancellationTokenSource)`, `base/show.jl:304-319`. -/
def m304 (runtime : CancellationRuntime) (source : CancellationValue) :=
  showCancellationBody runtime source
def P304 : Prop := ∀ runtime source, m304 runtime source =
  ["CancellationTokenSource("] ++
  [match runtime.cancelSeverity source with
   | none => "active"
   | some severity =>
     let request := severity.request
     if request = 0x1 then "cancelled"
     else if request = 0x3 then "cancelled, abandon external"
     else if request = 0x4 then "cancelled, abandon all"
     else "cancelled, severity " ++ runtime.repr request] ++
  (if source.nparents > 0 then [", ", toString source.nparents,
    if source.nparents = 1 then " parent" else " parents"] else []) ++ [")"]
theorem p304 : P304 := fun _ _ => rfl

/-- `print(io::IO, s::Symbol)`, `base/show.jl:322-322`. -/
def m322 (name : String) := Values.printSymbol name
def P322 : Prop := ∀ name, m322 name = name
theorem p322 : P322 := fun _ => rfl

/-- `IOContext{IO_t}(io::IO_t, dict::ImmutableDict{Symbol, Any}) where IO_t<:IO`, `base/show.jl:336-339`. -/
def m336 (io : IOCtx.JIO) (dict : IOCtx.IDict) := IOCtx.mkCtx io dict
def P336 : Prop := ∀ (io : IOCtx.JIO) (dict : IOCtx.IDict), (m336 io dict) = IOCtx.mkCtx io dict
theorem p336 : P336 := fun io dict => rfl

/-- `ioproperties(io::IO)`, `base/show.jl:343-343`. -/
def m343 (runtime : IOContextRuntime) (io : IOCtx.BaseIO) : IOCtx.IDict :=
  if runtime.getColor io then [("color", .bool true)] else []
def P343 : Prop := ∀ runtime io, m343 runtime io =
  if runtime.getColor io then [("color", .bool true)] else []
theorem p343 : P343 := fun _ _ => rfl

/-- `ioproperties(io::IOContext)`, `base/show.jl:344-344`. -/
def m344 (io : IOCtx.JIO) := IOCtx.ioproperties io
def P344 : Prop := ∀ (io : IOCtx.JIO), (m344 io) = IOCtx.ioproperties io
theorem p344 : P344 := fun io => rfl

/-- `unwrapcontext(io::IO)`, `base/show.jl:346-346`. -/
def m346 (io : IOCtx.JIO) := IOCtx.unwrapcontext io
def P346 : Prop := ∀ (io : IOCtx.JIO), (m346 io) = IOCtx.unwrapcontext io
theorem p346 : P346 := fun io => rfl

/-- `unwrapcontext(io::IOContext)`, `base/show.jl:347-347`. -/
def m347 (io : IOCtx.JIO) := IOCtx.unwrapcontext io
def P347 : Prop := ∀ (io : IOCtx.JIO), (m347 io) = IOCtx.unwrapcontext io
theorem p347 : P347 := fun io => rfl

/-- `IOContext(io::IO, dict::ImmutableDict{Symbol, Any})`, `base/show.jl:349-351`. -/
def m349 (io : IOCtx.JIO) (dict : IOCtx.IDict) := IOCtx.ioContextDict io dict
def P349 : Prop := ∀ (io : IOCtx.JIO) (dict : IOCtx.IDict), (m349 io dict) = IOCtx.ioContextDict io dict
theorem p349 : P349 := fun io dict => rfl

/-- `IOContext(io::IOContext, dict::ImmutableDict{Symbol, Any})`, `base/show.jl:353-355`. -/
def m353 (io : IOCtx.JIO) (dict : IOCtx.IDict) := IOCtx.ioContextDict io dict
def P353 : Prop := ∀ (io : IOCtx.JIO) (dict : IOCtx.IDict), (m353 io dict) = IOCtx.ioContextDict io dict
theorem p353 : P353 := fun io dict => rfl

/-- `convert(::Type{IOContext}, io::IOContext)`, `base/show.jl:358-358`. -/
def m358 (io : IOCtx.JIO) := IOCtx.convertCtx io
def P358 : Prop := ∀ (io : IOCtx.JIO), (m358 io) = IOCtx.convertCtx io
theorem p358 : P358 := fun io => rfl

/-- `convert(::Type{IOContext}, io::IO)`, `base/show.jl:359-359`. -/
def m359 (io : IOCtx.JIO) := IOCtx.convertCtx io
def P359 : Prop := ∀ (io : IOCtx.JIO), (m359 io) = IOCtx.convertCtx io
theorem p359 : P359 := fun io => rfl

/-- `convert(::Type{IOContext{IO_t}}, io::IOContext{IO_t}) where {IO_t}`, `base/show.jl:360-360`. -/
def m360 (io : IOCtx.JIO) := IOCtx.convertCtx io
def P360 : Prop := ∀ (io : IOCtx.JIO), (m360 io) = IOCtx.convertCtx io
theorem p360 : P360 := fun io => rfl

/-- `convert(::Type{IOContext{IO_t}}, io::IO) where {IO_t}`, `base/show.jl:361-361`. -/
def m361 (io : IOCtx.JIO) := IOCtx.convertCtx io
def P361 : Prop := ∀ (io : IOCtx.JIO), (m361 io) = IOCtx.convertCtx io
theorem p361 : P361 := fun io => rfl

/-- `IOContext(io::IO)`, `base/show.jl:363-363`. -/
def m363 (io : IOCtx.JIO) := IOCtx.ioContext1 io
def P363 : Prop := ∀ (io : IOCtx.JIO), (m363 io) = IOCtx.ioContext1 io
theorem p363 : P363 := fun io => rfl

/-- `IOContext{IO_t}(io::IO) where {IO_t}`, `base/show.jl:364-364`. -/
def m364 (io : IOCtx.JIO) := IOCtx.ioContext1 io
def P364 : Prop := ∀ (io : IOCtx.JIO), (m364 io) = IOCtx.ioContext1 io
theorem p364 : P364 := fun io => rfl

/-- `IOContext(io::IO, KV::Pair)`, `base/show.jl:366-369`. -/
def m366 (io : IOCtx.JIO) (kv : String × IOCtx.PV) := IOCtx.ioContextPair io kv
def P366 : Prop := ∀ (io : IOCtx.JIO) (kv : String × IOCtx.PV), (m366 io kv) = IOCtx.ioContextPair io kv
theorem p366 : P366 := fun io kv => rfl

/-- `IOContext(io::IO, context::IO)`, `base/show.jl:381-381`. -/
def m381 (io context : IOCtx.JIO) := IOCtx.ioContextIO io context
def P381 : Prop := ∀ (io context : IOCtx.JIO), (m381 io context) = IOCtx.ioContextIO io context
theorem p381 : P381 := fun io context => rfl

/-- `IOContext(io::IO, KV::Pair, KVs::Pair...)`, `base/show.jl:456-456`. -/
def m456 (io : IOCtx.JIO) (kvs : List (String × IOCtx.PV)) := IOCtx.ioContextPairs io kvs
def P456 : Prop := ∀ (io : IOCtx.JIO) (kvs : List (String × IOCtx.PV)), (m456 io kvs) = IOCtx.ioContextPairs io kvs
theorem p456 : P456 := fun io kvs => rfl

/-- `show(io::IO, ctx::IOContext)`, `base/show.jl:458-458`. -/
def m458 (runtime : IOContextRuntime) (ctx : IOCtx.JIO) : Out :=
  match IOCtx.unwrapcontext ctx with
  | .plain base => ["IOContext(", runtime.renderBase base, ")"]
  | .ctx base _ => ["IOContext(", runtime.renderBase base, ")"]
def P458 : Prop := ∀ runtime ctx, m458 runtime ctx =
  match IOCtx.unwrapcontext ctx with
  | .plain base => ["IOContext(", runtime.renderBase base, ")"]
  | .ctx base _ => ["IOContext(", runtime.renderBase base, ")"]
theorem p458 : P458 := fun _ _ => rfl

/-- `pipe_reader(io::IOContext)`, `base/show.jl:460-460`. -/
def m460 (io : IOCtx.JIO) := IOCtx.pipeReader io
def P460 : Prop := ∀ (io : IOCtx.JIO), (m460 io) = IOCtx.pipeReader io
theorem p460 : P460 := fun io => rfl

/-- `pipe_writer(io::IOContext)`, `base/show.jl:461-461`. -/
def m461 (io : IOCtx.JIO) := IOCtx.pipeWriter io
def P461 : Prop := ∀ (io : IOCtx.JIO), (m461 io) = IOCtx.pipeWriter io
theorem p461 : P461 := fun io => rfl

/-- `lock(io::IOContext)`, `base/show.jl:462-462`. -/
def m462 (io : IOCtx.JIO) := lockEffect .lock io
def P462 : Prop := ∀ io, (m462 io).2 = .lock
theorem p462 : P462 := by intro io; cases io <;> rfl

/-- `unlock(io::IOContext)`, `base/show.jl:463-463`. -/
def m463 (io : IOCtx.JIO) := lockEffect .unlock io
def P463 : Prop := ∀ io, (m463 io).2 = .unlock
theorem p463 : P463 := by intro io; cases io <;> rfl

/-- `in(key_value::Pair, io::IOContext)`, `base/show.jl:465-465`. -/
def m465 (kv : String × IOCtx.PV) (io : IOCtx.JIO) := IOCtx.inCtx kv io
def P465 : Prop := ∀ kv io, m465 kv io = IOCtx.inWith IOCtx.sameIdentity kv io
theorem p465 : P465 := fun _ _ => rfl

/-- `in(key_value::Pair, io::IO)`, `base/show.jl:466-466`. -/
def m466 (kv : String × IOCtx.PV) (base : IOCtx.BaseIO) := IOCtx.inCtx kv (.plain base)
def P466 : Prop := ∀ (kv : String × IOCtx.PV) (base : IOCtx.BaseIO), (m466 kv base) = IOCtx.inCtx kv (.plain base)
theorem p466 : P466 := fun kv base => rfl

/-- `haskey(io::IOContext, key)`, `base/show.jl:467-467`. -/
def m467 (io : IOCtx.JIO) (key : String) := IOCtx.haskeyCtx key io
def P467 : Prop := ∀ (io : IOCtx.JIO) (key : String), (m467 io key) = IOCtx.haskeyCtx key io
theorem p467 : P467 := fun io key => rfl

/-- `haskey(io::IO, key)`, `base/show.jl:468-468`. -/
def m468 (base : IOCtx.BaseIO) (key : String) := IOCtx.haskeyCtx key (.plain base)
def P468 : Prop := ∀ (base : IOCtx.BaseIO) (key : String), (m468 base key) = IOCtx.haskeyCtx key (.plain base)
theorem p468 : P468 := fun base key => rfl

/-- `getindex(io::IOContext, key)`, `base/show.jl:469-469`. -/
def m469 (io : IOCtx.JIO) (key : String) := IOCtx.getindexCtx key io
def P469 : Prop := ∀ (io : IOCtx.JIO) (key : String), (m469 io key) = IOCtx.getindexCtx key io
theorem p469 : P469 := fun io key => rfl

/-- `getindex(io::IO, key)`, `base/show.jl:470-470`. -/
def m470 (base : IOCtx.BaseIO) (key : String) := IOCtx.getindexCtx key (.plain base)
def P470 : Prop := ∀ (base : IOCtx.BaseIO) (key : String), (m470 base key) = IOCtx.getindexCtx key (.plain base)
theorem p470 : P470 := fun base key => rfl

/-- `get(io::IOContext, key, default)`, `base/show.jl:471-471`. -/
def m471 (io : IOCtx.JIO) (key : String) (default : IOCtx.PV) := IOCtx.getCtx key default io
def P471 : Prop := ∀ (io : IOCtx.JIO) (key : String) (default : IOCtx.PV), (m471 io key default) = IOCtx.getCtx key default io
theorem p471 : P471 := fun io key default => rfl

/-- `get(io::IO, key, default)`, `base/show.jl:472-472`. -/
def m472 (base : IOCtx.BaseIO) (key : String) (default : IOCtx.PV) := IOCtx.getCtx key default (.plain base)
def P472 : Prop := ∀ (base : IOCtx.BaseIO) (key : String) (default : IOCtx.PV), (m472 base key default) = IOCtx.getCtx key default (.plain base)
theorem p472 : P472 := fun base key default => rfl

/-- `keys(io::IOContext)`, `base/show.jl:473-473`. -/
def m473 (io : IOCtx.JIO) := IOCtx.keysCtx io
def P473 : Prop := ∀ (io : IOCtx.JIO), (m473 io) = IOCtx.keysCtx io
theorem p473 : P473 := fun io => rfl

/-- `keys(io::IO)`, `base/show.jl:474-474`. -/
def m474 (base : IOCtx.BaseIO) := IOCtx.keysCtx (.plain base)
def P474 : Prop := ∀ (base : IOCtx.BaseIO), (m474 base) = IOCtx.keysCtx (.plain base)
theorem p474 : P474 := fun base => rfl

/-- `displaysize(io::IOContext)`, `base/show.jl:476-476`. -/
def m476 (io : IOCtx.JIO) := IOCtx.displaysizeCtx io
def P476 : Prop := ∀ (io : IOCtx.JIO), (m476 io) = IOCtx.displaysizeCtx io
theorem p476 : P476 := fun io => rfl

/-- `show_circular(io::IO, @nospecialize(x))`, `base/show.jl:478-478`. -/
def m478 (x : IOCtx.PV) (base : IOCtx.BaseIO) := IOCtx.showCircular x (.plain base)
def P478 : Prop := ∀ (x : IOCtx.PV) (base : IOCtx.BaseIO), (m478 x base) = IOCtx.showCircular x (.plain base)
theorem p478 : P478 := fun x base => rfl

/-- `show_circular(io::IOContext, @nospecialize(x))`, `base/show.jl:479-491`. -/
def m479 (x : IOCtx.PV) (io : IOCtx.JIO) := IOCtx.showCircular x io
def P479 : Prop := ∀ (x : IOCtx.PV) (io : IOCtx.JIO), (m479 x io) = IOCtx.showCircular x io
theorem p479 : P479 := fun x io => rfl

/-- `show(io::IO, @nospecialize(x))`, `base/show.jl:520-520`. -/
def m520 (runtime : GenericShowRuntime) (io : IOCtx.BaseIO) (x : GenericValue) :=
  runtime.showDefault io x
def P520 : Prop := ∀ runtime io x, m520 runtime io x = runtime.showDefault io x
theorem p520 : P520 := fun _ _ _ => rfl

/-- `show(x)`, `base/show.jl:522-522`. -/
def m522 (runtime : GenericShowRuntime) (x : GenericValue) :=
  runtime.showOn runtime.stdout x
def P522 : Prop := ∀ runtime x, m522 runtime x = runtime.showOn runtime.stdout x
theorem p522 : P522 := fun _ _ => rfl

/-- `show_default(io::IO, @nospecialize(x))`, `base/show.jl:525-525`. -/
def m525 (runtime : GenericShowRuntime) (io : IOCtx.BaseIO) (x : GenericValue) :=
  runtime.showDefaultInner io (runtime.inferenceBarrier x)
def P525 : Prop := ∀ runtime io x, m525 runtime io x =
  runtime.showDefaultInner io (runtime.inferenceBarrier x)
theorem p525 : P525 := fun _ _ _ => rfl

/-- `_show_default(io::IO, @nospecialize(x))`, `base/show.jl:527-568`. -/
def m527 (runtime : DefaultRuntime) (io : IOCtx.BaseIO) (x : DefaultValue) :=
  showDefaultBody runtime io x
def P527 : Prop := ∀ runtime io x, m527 runtime io x =
  let fields := defaultFields runtime io x
  let bits := if !x.fields.isEmpty || x.byteSize = 0 then none
    else some (x.bytes, x.bitSize)
  [runtime.renderType x.typeId, "("] ++
  (match bits with
   | none =>
     if let some marker := runtime.showCircular io x then [marker] else
     let shown := fields.map fun field => match field with
       | .undef => "#undef"
       | .val text => text
     shown.zipIdx.flatMap fun (text, index) =>
       [text] ++ if index + 1 < fields.length then [", "] else []
   | some (bytes, nbits) =>
     let nbytes := (nbits + 7) / 8
     ["0x"] ++ (List.range nbytes).reverse.map (fun index =>
       let byte := (bytes.getD index 0).toNat
       if index = nbytes - 1 ∧ nbits % 8 ≠ 0 then
         Values.hexPad (byte % 2 ^ (nbits % 8)) ((nbits % 8 + 3) / 4)
       else Values.hexPad byte 2)) ++ [")"]
theorem p527 : P527 := fun _ _ _ => rfl

/-- `active_module()`, `base/show.jl:570-578`. -/
def m570 (runtime : ActiveModuleRuntime) := activeModuleBody runtime
def P570 : Prop := ∀ runtime, m570 runtime =
  if runtime.isPureContext () then
    .error (.errorException "active_module() should not be called from a pure context")
  else match runtime.activeReplDefined (), runtime.activeRepl with
    | false, _ => .ok "Main"
    | true, none => .ok "Main"
    | true, some repl => .ok (runtime.invokeLatest repl)
theorem p570 : P570 := fun _ => rfl

/-- `show_function(io::IO, f::Function, compact::Bool, fallback::Function)`, `base/show.jl:583-601`. -/
def m583 (runtime : FunctionRuntime) (io : FunctionIO) (function : FunctionValue)
    (compact : Bool) (fallback : FunctionFallback) :=
  showFunctionCore runtime io function compact fallback
def P583 : Prop := ∀ runtime io function compact fallback,
  HasResult (m583 runtime io function compact fallback) ∧
  (function.datatype.typeName.name = function.datatype.typeName.singletonName →
    m583 runtime io function compact fallback = functionFallback runtime fallback function) ∧
  (function.datatype.typeName.name ≠ function.datatype.typeName.singletonName → compact = true →
    m583 runtime io function compact fallback = function.datatype.typeName.singletonName)
theorem p583 : P583 := by
  intro runtime io function compact fallback
  refine ⟨hasResult _, ?_, ?_⟩
  · intro h; simp [m583, showFunctionCore, h]
  · intro h hc; simp [m583, showFunctionCore, h, hc]

/-- `show(io::IO, f::Function)`, `base/show.jl:603-603`. -/
def m603 (runtime : FunctionRuntime) (io : FunctionIO) (function : FunctionValue) :=
  showFunctionCore runtime io function io.compact .showDefault
def P603 : Prop := ∀ runtime io function,
  m603 runtime io function = showFunctionCore runtime io function io.compact .showDefault
theorem p603 : P603 := fun _ _ _ => rfl

/-- `print(io::IO, f::Function)`, `base/show.jl:604-604`. -/
def m604 (runtime : FunctionRuntime) (io : FunctionIO) (function : FunctionValue) :=
  showFunctionCore runtime io function true .show
def P604 : Prop := ∀ runtime io function,
  m604 runtime io function = showFunctionCore runtime io function true .show
theorem p604 : P604 := fun _ _ _ => rfl

/-- `show(io::IO, f::Core.IntrinsicFunction)`, `base/show.jl:606-611`. -/
def m606 (io : FunctionIO) (function : FunctionValue) : String :=
  (if io.compact then "" else "Core.Intrinsics.") ++ function.datatype.typeName.singletonName
def P606 : Prop := ∀ io function, m606 io function =
  (if io.compact then "" else "Core.Intrinsics.") ++ function.datatype.typeName.singletonName
theorem p606 : P606 := fun _ _ => rfl

/-- `print(io::IO, f::Core.IntrinsicFunction)`, `base/show.jl:613-613`. -/
def m613 (function : FunctionValue) : String := function.datatype.typeName.singletonName
def P613 : Prop := ∀ function, m613 function = function.datatype.typeName.singletonName
theorem p613 : P613 := fun _ => rfl

/-- `show(io::IO, ::MIME"text/plain", ::Core.TypeofBottom)`, `base/show.jl:615-615`. -/
def m615 (_io : AlignmentIO) : Out := ["Union{}"]
def P615 : Prop := ∀ io, m615 io = ["Union{}"]
theorem p615 : P615 := fun _ => rfl

/-- `print_without_params(@nospecialize(x))`, `base/show.jl:617-620`. -/
def m617 (runtime : TypeRuntime) (value : TypeObject) :=
  printWithoutParamsBody runtime value
def P617 : Prop := ∀ runtime value, m617 runtime value =
  match runtime.unwrapUnionall value with
  | .dataType wrapperId => wrapperId = value.id
  | .other => false
theorem p617 : P617 := fun _ _ => rfl

/-- `io_has_tvar_name(io::IOContext, name::Symbol, @nospecialize(x))`, `base/show.jl:622-629`. -/
def m622 (runtime : TypeVarRuntime) (io : TypeVarContext) (name : String)
    (value : TypeObject) := ioHasTypevarBody runtime io name value
def P622 : Prop := ∀ runtime io name value, m622 runtime io name value =
  io.dict.any fun binding =>
    binding.1 == "unionall_env" && match binding.2 with
    | .typeVar typevar => typevar.name == name && runtime.hasTypevar value typevar
    | .other _ => false
theorem p622 : P622 := fun _ _ _ _ => rfl

/-- `io_has_tvar_name(io::IO, name::Symbol, @nospecialize(x))`, `base/show.jl:630-630`. -/
def m630 (name : String) := Remaining.ioHasTvarNamePlain name
def P630 : Prop := ∀ name, m630 name = false
theorem p630 : P630 := fun _ => rfl

/-- `modulesof!(s::Set{Module}, x::TypeVar)`, `base/show.jl:632-632`. -/
def m632 (upper : Remaining.TypeShape) := Remaining.modulesOf (.typeVar upper)
def P632 : Prop := ∀ upper, m632 upper = Remaining.modulesOf upper
theorem p632 : P632 := fun _ => rfl

/-- `modulesof!(s::Set{Module}, x::TypeEq)`, `base/show.jl:633-637`. -/
def m633 (runtime : ParameterRuntime) (value : ParameterizedTypeValue) :=
  modulesTypeEqBody runtime value
def P633 : Prop := ∀ runtime value, m633 runtime value =
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []
theorem p633 : P633 := fun _ _ => rfl

/-- `modulesof!(s::Set{Module}, x::Core.TypeEgal)`, `base/show.jl:638-638`. -/
def m638 (runtime : ParameterRuntime) (value : ParameterizedTypeValue) :=
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []
def P638 : Prop := ∀ runtime value, m638 runtime value =
  match runtime.typeParameter value with
  | .anyType shape | .typeVar shape => Remaining.modulesOf shape
  | .nonType _ => []
theorem p638 : P638 := fun _ _ => rfl

/-- `modulesof!(s::Set{Module}, x::Type)`, `base/show.jl:639-652`. -/
def m639 (runtime : ModulesRuntime) (input : TypeObject) :=
  modulesOfTypeBody runtime 64 input
def P639 : Prop := ∀ runtime input moduleName,
  runtime.dataModule (runtime.unwrapUnionall input) = some moduleName →
    m639 runtime input = [moduleName]
theorem p639 : P639 := by
  intro runtime input moduleName h
  simp [m639, modulesOfTypeBody, h]

/-- `has_other_free_typevars(@nospecialize(x), free_before)`, `base/show.jl:654-667`. -/
def m654 (runtime : FreeTypevarRuntime) (value : TypeObject)
    (freeBefore : List TypeVarValue) := hasOtherFreeTypevarsBody runtime value freeBefore
def P654 : Prop := ∀ runtime value freeBefore, m654 runtime value freeBefore =
  if !runtime.hasFreeTypevars value then false
  else (runtime.findFreeTypevars value).any fun freeVar =>
    !(freeBefore.any fun previous => previous.id == freeVar.id)
theorem p654 : P654 := fun _ _ _ => rfl

/-- `unbounded_typealias(@nospecialize(alias))`, `base/show.jl:674-684`. -/
def m674 (runtime : AliasRuntime) (alias : AliasExpr) := unboundedAlias runtime alias
def P674 : Prop := ∀ runtime alias,
  HasResult (m674 runtime alias) ∧
  (match alias with
   | .atom id => m674 runtime alias = .atom id
   | .unionAll binder body =>
     if binder.lower = runtime.bottomId ∧ binder.upper = runtime.anyId then
       m674 runtime alias = .unionAll binder (unboundedAlias runtime body)
     else outerBinderUnbounded runtime (m674 runtime alias) = true)
theorem p674 : P674 := by
  intro runtime alias
  refine ⟨hasResult _, ?_⟩
  cases alias with
  | atom id => rfl
  | unionAll binder body =>
    by_cases h : binder.lower = runtime.bottomId ∧ binder.upper = runtime.anyId
    · by_cases hb : unboundedAlias runtime body = body
      · simp only [h, if_true]
        unfold m674
        rw [unboundedAlias, if_pos h, if_pos hb]
        exact congrArg (AliasExpr.unionAll binder) hb.symm
      · simp only [h, if_true]
        unfold m674
        rw [unboundedAlias, if_pos h, if_neg hb]
        simp
    · simp only [h, if_false]
      unfold m674
      rw [unboundedAlias, if_neg h]
      simp only [outerBinderUnbounded, runtime.newTypeVarLower,
        runtime.newTypeVarUpper, beq_self_eq_true, Bool.and_self]

/-- `reapply_unionall_env(io::Union{IO,Nothing}, @nospecialize(x))`, `base/show.jl:692-701`. -/
def m692 (context : Option TypeVarContext) (value : TypeExpr) :=
  reapplyUnionallBody context value
def P692 : Prop := ∀ context value, m692 context value =
  match context with
  | none => value
  | some io => io.dict.foldl (fun result binding =>
      if binding.1 == "unionall_env" then match binding.2 with
        | .typeVar freeVar => .unionAll freeVar result
        | .other _ => result
      else result) value
theorem p692 : P692 := fun _ _ => rfl

/-- `make_typealias(@nospecialize(x::Type), io::Union{IO,Nothing}=nothing)`, `base/show.jl:703-767`. -/
def m703 (runtime : MakeAliasRuntime) (context : Option TypeVarContext)
    (input : TypeObject) := makeTypealiasBody runtime context input
def P703 : Prop := ∀ runtime context input,
  HasResult (m703 runtime context input) ∧
  (input.id = runtime.anyId → m703 runtime context input = none) ∧
  (runtime.isTupleSubtype input = true → m703 runtime context input = none)
theorem p703 : P703 := by
  intro runtime context input
  refine ⟨hasResult _, ?_, ?_⟩
  · intro h; simp [m703, makeTypealiasBody, h]
  · intro h; simp [m703, makeTypealiasBody, h]

/-- `isgensym(s::Symbol)`, `base/show.jl:769-769`. -/
def m769 (runtime : SymbolRuntime) (symbol : SymbolValue) :=
  (runtime.string symbol).contains '#'
def P769 : Prop := ∀ runtime symbol,
  m769 runtime symbol = (runtime.string symbol).contains '#'
theorem p769 : P769 := fun _ _ => rfl

/-- `show_can_elide(p::TypeVar, wheres::Vector, elide::Int, env::SimpleVector, skip::Int)`, `base/show.jl:771-784`. -/
def m771 (runtime : TypeRelationRuntime) (parameter : TypeVarValue)
    (wheres : List TypeVarValue) (elide : Nat) (env : List TypeSlot) (skip : Nat) :=
  showCanElideBody runtime parameter wheres elide env skip
def P771 : Prop := ∀ runtime parameter wheres elide env skip,
  HasResult (m771 runtime parameter wheres elide env skip) ∧
  (elide = 0 → m771 runtime parameter wheres elide env skip = false)
theorem p771 : P771 := by
  intro runtime parameter wheres elide env skip
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m771, showCanElideBody, h]

/-- `show_typeparams(io::IO, env::SimpleVector, orig::SimpleVector, wheres::Vector)`, `base/show.jl:786-830`. -/
def m786 (runtime : TypeParamsRuntime) (env orig : List TypeSlot)
    (wheres : List TypeVarValue) := showTypeparamsBody runtime env orig wheres
def P786 : Prop := ∀ runtime env orig wheres, (m786 runtime env orig wheres).2.IsPrefix wheres
theorem p786 : P786 := by
  intro runtime env orig wheres
  simp only [m786, showTypeparamsBody]
  exact List.take_prefix _ _

/-- `egal_var(p::TypeVar, @nospecialize o)`, `base/show.jl:789-793`. -/
def m789 (runtime : TypeRelationRuntime) (parameter : TypeVarValue) (other : TypeSlot) :=
  egalVarBody runtime parameter other
def P789 : Prop := ∀ runtime parameter other, m789 runtime parameter other =
  match other with
  | .other _ => false
  | .typeVar value =>
    runtime.structurallyEquivalent parameter.upper value.upper &&
      runtime.structurallyEquivalent parameter.lower value.lower
theorem p789 : P789 := fun _ _ _ => rfl

/-- `show_typealias_name(io::IO, name::GlobalRef)`, `base/show.jl:832-845`. -/
def m832 (runtime : AliasNameRuntime) (reference : GlobalRefValue) :=
  showAliasNameBody runtime reference
def P832 : Prop := ∀ runtime reference, m832 runtime reference =
  (if runtime.compact then [] else match runtime.fromModule with
   | none => [runtime.renderModule reference.moduleName, "."]
   | some origin => if runtime.visible reference.name reference.moduleName origin then []
     else [runtime.renderModule reference.moduleName, "."]) ++ [reference.name]
theorem p832 : P832 := fun _ _ => rfl

/-- `show_typealias(io::IO, name::GlobalRef, env::SimpleVector, wheres::Vector)`, `base/show.jl:847-862`. -/
def m847 (runtime : TypeAliasRuntime) (alias : TypeAliasValue)
    (env : List TypeSlot) (wheres : List TypeVarValue) :=
  showTypealiasBody runtime alias env wheres
def P847 : Prop := ∀ runtime alias env wheres,
  (m847 runtime alias env wheres).2.IsPrefix wheres
theorem p847 : P847 := by
  intro runtime alias env wheres
  simp only [m847, showTypealiasBody]
  split
  · exact List.prefix_refl _
  · exact List.take_prefix _ _

/-- `make_wheres(io::IO, env::SimpleVector, @nospecialize(x::Type))`, `base/show.jl:864-892`. -/
def m864 (runtime : MakeWheresRuntime) (context : Option TypeVarContext)
    (env : List TypeSlot) (value : TypeExpr) := makeWheresBody runtime context env value
def P864 : Prop := ∀ runtime context env value,
  HasResult (m864 runtime context env value) ∧
  (context = none → env = [] → (∀ id, value = .atom id → m864 runtime context env value = []))
theorem p864 : P864 := by
  intro runtime context env value
  refine ⟨hasResult _, ?_⟩
  intro hc he id hv
  subst context; subst env; subst value
  simp [m864, makeWheresBody, outerWheres]

/-- `show_wheres(io::IO, wheres::Vector{TypeVar})`, `base/show.jl:894-906`. -/
def m894 (runtime : WheresRuntime) (wheres : List TypeVarValue) :=
  showWheresBody runtime wheres
def P894 : Prop := ∀ runtime wheres,
  HasResult (m894 runtime wheres) ∧ (wheres = [] → m894 runtime wheres = [])
theorem p894 : P894 := by
  intro runtime wheres
  refine ⟨hasResult _, ?_⟩
  intro h; subst h; rfl

/-- `show_typealias(io::IO, @nospecialize(x::Type))`, `base/show.jl:908-915`. -/
def m908 (runtime : AliasDispatchRuntime) (value : TypeExpr) :=
  showTypealiasDispatchBody runtime value
def P908 : Prop := ∀ runtime value,
  (m908 runtime value).1 = (runtime.makeAlias value).isSome
theorem p908 : P908 := by
  intro runtime value
  cases h : runtime.makeAlias value <;> simp [m908, showTypealiasDispatchBody, h]

/-- `make_typealiases(@nospecialize(x::Type))`, `base/show.jl:917-1000`. -/
def m917 (runtime : UnionAliasRuntime) (input : TypeObject) :=
  makeTypealiasesBody runtime input
def P917 : Prop := ∀ runtime input,
  HasResult (m917 runtime input) ∧
  (input.id = runtime.base.anyId → m917 runtime input = ([], runtime.emptyUnion))
theorem p917 : P917 := by
  intro runtime input
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m917, makeTypealiasesBody, h]

/-- `show_unionaliases(io::IO, x::Union)`, `base/show.jl:1002-1044`. -/
def m1002 (runtime : ShowUnionRuntime) (input : TypeObject) :=
  showUnionAliasesBody runtime input
def P1002 : Prop := ∀ runtime input,
  (m1002 runtime input).1 = !(makeTypealiasesBody runtime.aliases input).1.isEmpty
theorem p1002 : P1002 := by
  intro runtime input
  generalize h : makeTypealiasesBody runtime.aliases input = result
  rcases result with ⟨aliases, applied⟩
  cases aliases <;> simp [m1002, showUnionAliasesBody, h]

/-- `show(io::IO, ::MIME"text/plain", @nospecialize(x::Type))`, `base/show.jl:1046-1069`. -/
def m1046 (runtime : TypePlainRuntime) (input : TypeObject) :=
  showTypePlainBody runtime input
def P1046 : Prop := ∀ runtime input,
  runtime.printWithoutParams input = false → (runtime.makeAlias input).isSome = true →
    (m1046 runtime input).head? = some (.plain (runtime.renderCompact input))
theorem p1046 : P1046 := by
  intro runtime input hp ha
  simp [m1046, showTypePlainBody, hp, ha]

/-- `show_typeegal(io::IO, @nospecialize(x::Core.TypeEgal))`, `base/show.jl:1071-1075`. -/
def m1071 (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) :=
  showTypeEgalBody runtime value
def P1071 : Prop := ∀ runtime value, m1071 runtime value =
  "Core.TypeEgal{" ++ runtime.renderType (runtime.typeParameter value) ++ "}"
theorem p1071 : P1071 := fun _ _ => rfl

/-- `show(io::IO, @nospecialize(x::Core.AnyType))`, `base/show.jl:1076-1086`. -/
def m1076 (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) :=
  showAnyTypeBody runtime value
def P1076 : Prop := ∀ runtime value,
  value.kind = .bottom → m1076 runtime value = "Union{}"
theorem p1076 : P1076 := by
  intro runtime value h
  cases value with
  | mk object kind => cases kind <;> simp_all [m1076, showAnyTypeBody]

/-- `show_typeeq(io::IO, @nospecialize(x::TypeEq))`, `base/show.jl:1091-1095`. -/
def m1091 (runtime : AnyTypeRuntime) (value : AnyTypeValueModel) :=
  showTypeEqBody runtime value
def P1091 : Prop := ∀ runtime value, m1091 runtime value =
  (if runtime.compact then "Type{" else "TypeEq{") ++
    runtime.renderType (runtime.typeParameter value) ++ "}"
theorem p1091 : P1091 := fun _ _ => rfl

/-- `_show_type(io::IO, @nospecialize(x::Type))`, `base/show.jl:1096-1152`. -/
def m1096 (runtime : TypeDispatchRuntime) (input : TypeObject) :=
  showTypeDispatchBody runtime input
def P1096 : Prop := ∀ runtime input,
  HasResult (m1096 runtime input) ∧
  (runtime.isTypeEgal input = true → m1096 runtime input = runtime.showTypeEgal input)
theorem p1096 : P1096 := by
  intro runtime input
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1096, showTypeDispatchBody, h]

/-- `isvisible(sym::Symbol, parent::Module, from::Module)`, `base/show.jl:1159-1177`. -/
def m1159 (runtime : VisibilityRuntime) (symbol : SymbolValue)
    (parent origin : ModuleValue) := isVisibleBody runtime symbol parent origin
def P1159 : Prop := ∀ runtime symbol parent origin,
  HasResult (m1159 runtime symbol parent origin) ∧
  (runtime.isDeprecated parent symbol = true → m1159 runtime symbol parent origin = false)
theorem p1159 : P1159 := by
  intro runtime symbol parent origin
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1159, isVisibleBody, h]

/-- `is_global_function(tn::Core.TypeName, globname::Union{Symbol,Nothing})`, `base/show.jl:1179-1189`. -/
def m1179 (runtime : GlobalFunctionRuntime) (typeName : TypeNameValue)
    (globalName : Option String) := isGlobalFunctionBody runtime typeName globalName
def P1179 : Prop := ∀ runtime typeName globalName,
  HasResult (m1179 runtime typeName globalName) ∧
  (globalName = none → m1179 runtime typeName globalName = false)
theorem p1179 : P1179 := by
  intro runtime typeName globalName
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1179, isGlobalFunctionBody, h]

/-- `check_world_bounded(tn::Core.TypeName)`, `base/show.jl:1191-1209`. -/
def m1191 (runtime : WorldRuntime) (typeName : TypeNameValue) :=
  checkWorldBody runtime typeName
def P1191 : Prop := ∀ runtime typeName,
  HasResult (m1191 runtime typeName) ∧
  (runtime.bindingDefined typeName = false → m1191 runtime typeName = none)
theorem p1191 : P1191 := by
  intro runtime typeName
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1191, checkWorldBody, h]

/-- `show_type_name(io::IO, tn::Core.TypeName)`, `base/show.jl:1211-1246`. -/
def m1211 (runtime : ShowTypeNameRuntime) (typeName : TypeNameValue) :=
  showTypeNameBody runtime typeName
def P1211 : Prop := ∀ runtime typeName,
  HasResult (m1211 runtime typeName) ∧
  (typeName.id = runtime.unionAllNameId → m1211 runtime typeName = "UnionAll")
theorem p1211 : P1211 := by
  intro runtime typeName
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1211, showTypeNameBody, h]

/-- `maybe_kws_nt(x::DataType)`, `base/show.jl:1248-1264`. -/
def m1248 (runtime : KwargsRuntime) (datatype : DatatypeModel) :=
  maybeKwargsBody runtime datatype
def P1248 : Prop := ∀ runtime datatype,
  HasResult (m1248 runtime datatype) ∧
  (datatype.name.id ≠ runtime.pairsTypeNameId → m1248 runtime datatype = none)
theorem p1248 : P1248 := by
  intro runtime datatype
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1248, maybeKwargsBody, h]

/-- `show_datatype(io::IO, x::DataType, wheres::Vector{TypeVar}=TypeVar[])`, `base/show.jl:1266-1360`. -/
def m1266 (runtime : DatatypeRuntime) (datatype : DatatypeModel)
    (wheres : List TypeVarValue) := showDatatypeBody runtime datatype wheres
def P1266 : Prop := ∀ runtime datatype wheres,
  datatype.name.id = runtime.tupleNameId → datatype.parameters = [] →
    m1266 runtime datatype wheres = "Tuple{}"
theorem p1266 : P1266 := by
  intro runtime datatype wheres hn hp
  simp [m1266, showDatatypeBody, hn, hp]

/-- `show_at_namedtuple(io::IO, syms::Tuple, types::DataType)`, `base/show.jl:1362-1376`. -/
def m1362 (runtime : DatatypeRuntime) (symbols : List SymbolValue)
    (types : List TypeObject) := showNamedTupleFields runtime symbols types
def P1362 : Prop := ∀ runtime types,
  m1362 runtime [] types = ""
theorem p1362 : P1362 := by unfold P1362; intros; rfl

/-- `show_supertypes(io::IO, typ::DataType)`, `base/show.jl:1378-1384`. -/
def m1378 (runtime : SupertypeRuntime) (type : TypeObject) :=
  showSupertypesBody runtime 64 type
def P1378 : Prop := ∀ runtime type,
  type.id = runtime.anyTypeId → m1378 runtime type = runtime.render type
theorem p1378 : P1378 := by
  intro runtime type h
  simp [m1378, showSupertypesBody, h]

/-- `show_supertypes(typ::DataType)`, `base/show.jl:1386-1386`. -/
def m1386 (runtime : SupertypeRuntime) (type : TypeObject) := m1378 runtime type
def P1386 : Prop := ∀ runtime type, m1386 runtime type = m1378 runtime type
theorem p1386 : P1386 := fun _ _ => rfl

/-- `show(exs...)`, `base/show.jl:1406-1414`. -/
def m1406 (runtime : ShowMacroRuntime) (expressions : List AstValue) :=
  showMacroBody runtime expressions
def P1406 : Prop := ∀ runtime expressions,
  (m1406 runtime expressions).lines.length = expressions.length
theorem p1406 : P1406 := by
  intro runtime expressions
  simp [m1406, showMacroBody]

/-- `show(io::IO, tn::Core.TypeName)`, `base/show.jl:1416-1420`. -/
def m1416 (runtime : ShowTypeNameRuntime) (name : TypeNameValue) :=
  "typename(" ++ m1211 runtime name ++ ")"
def P1416 : Prop := ∀ runtime name,
  m1416 runtime name = "typename(" ++ m1211 runtime name ++ ")"
theorem p1416 : P1416 := fun _ _ => rfl

/-- `nonnothing_nonmissing_typeinfo(io::IO)`, `base/show.jl:1422-1422`. -/
def m1422 (runtime : ScalarRuntime) (io : ScalarIO) :=
  nonnothingNonmissingBody runtime io
def P1422 : Prop := ∀ runtime io, m1422 runtime io =
  runtime.nonmissingType (runtime.nonnothingType io.typeinfo)
theorem p1422 : P1422 := fun _ _ => rfl

/-- `show(io::IO, b::Bool)`, `base/show.jl:1423-1423`. -/
def m1423 (runtime : ScalarRuntime) (io : ScalarIO) (value : Bool) :=
  showBoolBody runtime io value
def P1423 : Prop := ∀ runtime io value, m1423 runtime io value =
  [if runtime.nonmissingType (runtime.nonnothingType io.typeinfo) = runtime.boolType then
    if value then "1" else "0" else if value then "true" else "false"]
theorem p1423 : P1423 := fun _ _ _ => rfl

/-- `show(io::IO, ::Nothing)`, `base/show.jl:1424-1424`. -/
def m1424 (_io : ScalarIO) : Out := ["nothing"]
def P1424 : Prop := ∀ io, m1424 io = ["nothing"]
theorem p1424 : P1424 := fun _ => rfl

/-- `show(io::IO, n::Signed)`, `base/show.jl:1425-1425`. -/
def m1425 (runtime : ScalarRuntime) (value : SignedValue) : Out :=
  [runtime.stringSigned value]
def P1425 : Prop := ∀ runtime value, m1425 runtime value = [runtime.stringSigned value]
theorem p1425 : P1425 := fun _ _ => rfl

/-- `show(io::IO, n::Unsigned)`, `base/show.jl:1426-1436`. -/
def m1426 (runtime : ScalarRuntime) (io : ScalarIO) (value : UnsignedValue) :=
  showUnsignedBody runtime io value
def P1426 : Prop := ∀ runtime io value, m1426 runtime io value =
  if io.hexUnsigned then ["0x", runtime.stringUnsignedHex value ((runtime.bitSize value + 3) / 4)]
  else if io.typeinfo = runtime.typeOfUnsigned value then [runtime.stringUnsignedDecimal value]
  else [runtime.renderType (runtime.typeOfUnsigned value), "(", runtime.stringUnsignedDecimal value, ")"]
theorem p1426 : P1426 := fun _ _ _ => rfl

/-- `print(io::IO, n::Unsigned)`, `base/show.jl:1437-1437`. -/
def m1437 (runtime : ScalarRuntime) (value : UnsignedValue) : Out :=
  [runtime.stringUnsignedDecimal value]
def P1437 : Prop := ∀ runtime value, m1437 runtime value = [runtime.stringUnsignedDecimal value]
theorem p1437 : P1437 := fun _ _ => rfl

/-- `has_tight_type(p::Pair)`, `base/show.jl:1439-1441`. -/
def m1439 (runtime : PairRuntime) (pair : PairValue) := hasTightTypeBody runtime pair
def P1439 : Prop := ∀ runtime pair, m1439 runtime pair =
  (runtime.typeOfValue pair.first = pair.firstParameter &&
    runtime.typeOfValue pair.second = pair.secondParameter)
theorem p1439 : P1439 := fun _ _ => rfl

/-- `isdelimited(io::IO, x)`, `base/show.jl:1443-1443`. -/
def m1443 (_io x : String) := Values.isdelimitedAny
def P1443 : Prop := ∀ io x : String, m1443 io x = true
theorem p1443 : P1443 := fun _ _ => rfl

/-- `isdelimited(io::IO, x::Function)`, `base/show.jl:1444-1444`. -/
def m1444 (runtime : PairRuntime) (function : FunctionValue) :=
  !runtime.isOperator (runtime.symbolOfFunction function)
def P1444 : Prop := ∀ runtime function, m1444 runtime function =
  !runtime.isOperator (runtime.symbolOfFunction function)
theorem p1444 : P1444 := fun _ _ => rfl

/-- `isdelimited(io::IO, p::Pair)`, `base/show.jl:1448-1448`. -/
def m1448 (runtime : PairRuntime) (io : PairIO) (pair : PairValue) :=
  pairDelimitedBody runtime io pair
def P1448 : Prop := ∀ runtime io pair, m1448 runtime io pair =
  !(hasTightTypeBody runtime pair || io.typeinfo = runtime.typeOfPair pair)
theorem p1448 : P1448 := fun _ _ _ => rfl

/-- `gettypeinfos(io::IO, p::Pair)`, `base/show.jl:1450-1455`. -/
def m1450 (runtime : PairRuntime) (io : PairIO) (pair : PairValue) :=
  pairTypeinfosBody runtime io pair
def P1450 : Prop := ∀ runtime io pair, m1450 runtime io pair =
  if runtime.pairIsa pair io.typeinfo && runtime.subtype io.typeinfo runtime.pairSupertype then
    (runtime.fieldType io.typeinfo 1, runtime.fieldType io.typeinfo 2)
  else (runtime.anyType, runtime.anyType)
theorem p1450 : P1450 := fun _ _ _ => rfl

/-- `show(io::IO, p::Pair)`, `base/show.jl:1457-1467`. -/
def m1457 (runtime : PairRuntime) (io : PairIO) (pair : PairValue) :=
  showPairBody runtime io pair
def P1457 : Prop := ∀ runtime io pair,
  HasResult (m1457 runtime io pair) ∧
  (pairDelimitedBody runtime io pair = true → m1457 runtime io pair =
    [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second])
theorem p1457 : P1457 := by
  intro runtime io pair
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1457, showPairBody, h]

/-- `show_pairtyped(io::IO, p::Pair{K,V}) where {K,V}`, `base/show.jl:1469-1472`. -/
def m1469 (runtime : PairRuntime) (pair : PairValue) : Out :=
  [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second]
def P1469 : Prop := ∀ runtime pair, m1469 runtime pair =
  [runtime.renderType (runtime.typeOfPair pair), runtime.renderTuple pair.first pair.second]
theorem p1469 : P1469 := fun _ _ => rfl

/-- `show(io::IO, m::Module)`, `base/show.jl:1474-1480`. -/
def m1474 (runtime : ModuleRuntime) (module : ModuleValue) := showModuleBody runtime module
def P1474 : Prop := ∀ runtime module,
  HasResult (m1474 runtime module) ∧
  (runtime.isRootModule module = true → m1474 runtime module = [module.name])
theorem p1474 : P1474 := by
  intro runtime module
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1474, showModuleBody, h]

/-- `print_fullname(io::IO, m::Module)`, `base/show.jl:1484-1493`. -/
def m1484 (runtime : ModuleRuntime) (module : ModuleValue) :=
  printFullnameBody runtime runtime.moduleCount module
def P1484 : Prop := ∀ runtime module,
  HasResult (m1484 runtime module) ∧
  (module.parentId = module.id → runtime.moduleCount > 0 →
    m1484 runtime module = [runtime.showSymbol module.name])
theorem p1484 : P1484 := by
  intro runtime module
  refine ⟨hasResult _, ?_⟩
  intro hp hf
  cases h : runtime.moduleCount with
  | zero => omega
  | succ fuel =>
    simp only [m1484, h, printFullnameBody]
    rw [hp, runtime.lookupSelf]
    simp

/-- `sourceinfo_slotnames(src::CodeInfo)`, `base/show.jl:1495-1495`. -/
def m1495 (runtime : SlotRuntime) (source : CodeInfoValue) :=
  sourceSlotnamesBody runtime source.slotnames
def P1495 : Prop := ∀ runtime source,
  m1495 runtime source = sourceSlotnamesBody runtime source.slotnames
theorem p1495 : P1495 := fun _ _ => rfl

/-- `sourceinfo_slotnames(slotnames::Vector{Symbol})`, `base/show.jl:1496-1516`. -/
def m1496 (runtime : SlotRuntime) (slotnames : List SymbolValue) :=
  sourceSlotnamesBody runtime slotnames
def P1496 : Prop := ∀ runtime slotnames,
  HasResult (m1496 runtime slotnames) ∧ (slotnames = [] → m1496 runtime slotnames = [])
theorem p1496 : P1496 := by
  intro runtime slotnames
  refine ⟨hasResult _, ?_⟩
  intro h; subst h; rfl

/-- `show(io::IO, mi::Core.MethodInstance)`, `base/show.jl:1518-1518`. -/
def m1518 (runtime : MethodRuntime) (miValue : MethodInstanceValue) :=
  showMethodInstanceBody runtime miValue false
def P1518 : Prop := ∀ runtime miValue,
  m1518 runtime miValue = showMethodInstanceBody runtime miValue false
theorem p1518 : P1518 := fun _ _ => rfl

/-- `show(io::IO, codeinst::Core.CodeInstance)`, `base/show.jl:1519-1531`. -/
def m1519 (runtime : MethodRuntime) (codeValue : CodeInstanceValue) :=
  showCodeInstanceBody runtime codeValue
def P1519 : Prop := ∀ runtime codeValue,
  HasResult (m1519 runtime codeValue) ∧
  (codeValue.owner.isSome = true → ∃ stem, m1519 runtime codeValue = stem ++ " (foreign)")
theorem p1519 : P1519 := by
  intro runtime codeValue
  refine ⟨hasResult _, ?_⟩
  intro h
  cases ho : codeValue.owner with
  | none => simp [ho] at h
  | some owner =>
    cases hd : codeValue.definition with
    | methodInstance mi =>
      exact ⟨"CodeInstance for " ++ showMethodInstanceBody runtime mi false,
        by simp [m1519, showCodeInstanceBody, ho, hd]⟩
    | abiOverride mi =>
      exact ⟨"CodeInstance for " ++ showMethodInstanceBody runtime mi false ++
        " (ABI Overridden)", by simp [m1519, showCodeInstanceBody, ho, hd]⟩

/-- `show_mi(io::IO, mi::Core.MethodInstance, from_stackframe::Bool=false)`, `base/show.jl:1533-1560`. -/
def m1533 (runtime : MethodRuntime) (miValue : MethodInstanceValue)
    (fromStackframe : Bool) := showMethodInstanceBody runtime miValue fromStackframe
def P1533 : Prop := ∀ runtime miValue fromStackframe,
  HasResult (m1533 runtime miValue fromStackframe) ∧
  (fromStackframe = true → match miValue.definition with
    | .toplevel _ => m1533 runtime miValue fromStackframe = "Toplevel MethodInstance thunk"
    | .method _ => True)
theorem p1533 : P1533 := by
  intro runtime miValue fromStackframe
  refine ⟨hasResult _, ?_⟩
  intro h; subst h
  cases miValue with
  | mk id definition specTypes cache =>
    cases definition <;> simp [m1533, showMethodInstanceBody]

/-- `show_delim_array(io::IO, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1=first(LinearIndices(itr)), l=last(LinearIndices(itr)))`, `base/show.jl:1562-1589`. -/
def m1562 (runtime : DelimArrayRuntime) (array : DelimArrayValue)
    (op delim close : String) (delimOne : Bool) (first last : Int) :=
  Containers.showDelimArray (delimArrayElement runtime array) op delim close delimOne
    (runtime.showCircular array) first last
def P1562 : Prop := ∀ runtime array op delim close delimOne first last,
  HasResult (m1562 runtime array op delim close delimOne first last) ∧
  (∀ marker, runtime.showCircular array = some marker →
    m1562 runtime array op delim close delimOne first last = [op, marker, close])
theorem p1562 : P1562 := by
  intro runtime array op delim close delimOne first last
  refine ⟨hasResult _, ?_⟩
  intro marker h
  simp [m1562, Containers.showDelimArray, h]

/-- `show_delim_array(io::IO, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int))`, `base/show.jl:1591-1623`. -/
def m1591 (runtime : DelimIteratorRuntime) (iterator : IteratorValue)
    (op delim close : String) (delimOne : Bool) (first : Nat) (count : Int) :=
  showDelimIteratorBody runtime iterator op delim close delimOne first count
def P1591 : Prop := ∀ runtime iterator op delim close delimOne first count,
  HasResult (m1591 runtime iterator op delim close delimOne first count) ∧
  (∀ marker, runtime.showCircular iterator = some marker →
    m1591 runtime iterator op delim close delimOne first count = [op, marker, close])
theorem p1591 : P1591 := by
  intro runtime iterator op delim close delimOne first count
  refine ⟨hasResult _, ?_⟩
  intro marker h
  simp [m1591, showDelimIteratorBody, h]

/-- `show(io::IO, t::Tuple)`, `base/show.jl:1625-1625`. -/
def m1625 (runtime : DelimArrayRuntime) (tuple : DelimArrayValue) :=
  m1562 runtime tuple "(" "," ")" true 1 tuple.slots.length
def P1625 : Prop := ∀ runtime tuple,
  m1625 runtime tuple = m1562 runtime tuple "(" "," ")" true 1 tuple.slots.length
theorem p1625 : P1625 := fun _ _ => rfl

/-- `show(io::IO, v::SimpleVector)`, `base/show.jl:1626-1626`. -/
def m1626 (runtime : DelimArrayRuntime) (vector : DelimArrayValue) :=
  m1562 runtime vector "svec(" "," ")" false 1 vector.slots.length
def P1626 : Prop := ∀ runtime vector,
  m1626 runtime vector = m1562 runtime vector "svec(" "," ")" false 1 vector.slots.length
theorem p1626 : P1626 := fun _ _ => rfl

/-- `show(io::IO, s::Symbol)`, `base/show.jl:1628-1628`. -/
def m1628 (runtime : ExprRuntime) (io : ExprContext) (symbol : JStr) :=
  runtime.showQuoteSymbol io symbol 0 0
def P1628 : Prop := ∀ runtime io symbol,
  m1628 runtime io symbol = runtime.showQuoteSymbol io symbol 0 0
theorem p1628 : P1628 := fun _ _ _ => rfl

/-- `print( io::IO, ex::ExprNode)`, `base/show.jl:1666-1666`. -/
def m1666 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) :=
  runtime.showUnquoted ⟨false⟩ expression 0 (-1)
def P1666 : Prop := ∀ runtime io expression,
  m1666 runtime io expression = runtime.showUnquoted ⟨false⟩ expression 0 (-1)
theorem p1666 : P1666 := fun _ _ _ => rfl

/-- `show( io::IO, ex::ExprNode)`, `base/show.jl:1667-1667`. -/
def m1667 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) :=
  runtime.showQuoteExpr ⟨true⟩ expression 0 (-1)
def P1667 : Prop := ∀ runtime io expression,
  m1667 runtime io expression = runtime.showQuoteExpr ⟨true⟩ expression 0 (-1)
theorem p1667 : P1667 := fun _ _ _ => rfl

/-- `show_unquoted(io::IO, ex)`, `base/show.jl:1668-1668`. -/
def m1668 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) :=
  runtime.showUnquoted io expression 0 0
def P1668 : Prop := ∀ runtime io expression,
  m1668 runtime io expression = runtime.showUnquoted io expression 0 0
theorem p1668 : P1668 := fun _ _ _ => rfl

/-- `show_unquoted(io::IO, ex, indent::Int)`, `base/show.jl:1669-1669`. -/
def m1669 (runtime : ExprRuntime) (io : ExprContext) (expression : JE) (indent : Int) :=
  runtime.showUnquoted io expression indent 0
def P1669 : Prop := ∀ runtime io expression indent,
  m1669 runtime io expression indent = runtime.showUnquoted io expression indent 0
theorem p1669 : P1669 := fun _ _ _ _ => rfl

/-- `show_unquoted(io::IO, ex, ::Int,::Int)`, `base/show.jl:1670-1670`. -/
def m1670 (runtime : ExprRuntime) (io : ExprContext) (value : DelimElement) :=
  runtime.showFallback io value
def P1670 : Prop := ∀ runtime io value,
  m1670 runtime io value = runtime.showFallback io value
theorem p1670 : P1670 := fun _ _ _ => rfl

/-- `show_unquoted(io::IO, ex, indent::Int, prec::Int, ::Int)`, `base/show.jl:1671-1671`. -/
def m1671 (runtime : ExprRuntime) (io : ExprContext) (expression : JE)
    (indent prec _quoteLevel : Int) := runtime.showUnquoted io expression indent prec
def P1671 : Prop := ∀ runtime io expression indent prec quoteLevel,
  m1671 runtime io expression indent prec quoteLevel =
    runtime.showUnquoted io expression indent prec
theorem p1671 : P1671 := fun _ _ _ _ _ _ => rfl

/-- `operator_precedence(s::Symbol)`, `base/show.jl:1713-1713`. -/
def m1713 (runtime : OperatorRuntime) (symbol : SymbolValue) := runtime.precedence symbol
def P1713 : Prop := ∀ runtime symbol, m1713 runtime symbol = runtime.precedence symbol
theorem p1713 : P1713 := fun _ _ => rfl

/-- `operator_precedence(x::Any)`, `base/show.jl:1714-1714`. -/
def m1714 (_x : String) := Remaining.operatorPrecedenceAny
def P1714 : Prop := ∀ x : String, m1714 x = 0
theorem p1714 : P1714 := fun _ => rfl

/-- `operator_associativity(s::Symbol)`, `base/show.jl:1739-1748`. -/
def m1739 (runtime : OperatorRuntime) (symbol : SymbolValue) :=
  operatorAssociativityBody runtime symbol
def P1739 : Prop := ∀ runtime symbol,
  runtime.precedence symbol ∈ [runtime.arrow, runtime.assignment, runtime.controlFlow,
    runtime.pair, runtime.power] → m1739 runtime symbol = .right
theorem p1739 : P1739 := by
  intro runtime symbol h
  simp [m1739, operatorAssociativityBody, h]

/-- `is_quoted(ex)`, `base/show.jl:1750-1750`. -/
def m1750 (_ex : DelimElement) := false
def P1750 : Prop := ∀ ex : DelimElement, m1750 ex = false
theorem p1750 : P1750 := fun _ => rfl

/-- `is_quoted(ex::QuoteNode)`, `base/show.jl:1751-1751`. -/
def m1751 (_node : QuoteNodeValue) := true
def P1751 : Prop := ∀ node : QuoteNodeValue, m1751 node = true
theorem p1751 : P1751 := fun _ => rfl

/-- `is_quoted(ex::Expr)`, `base/show.jl:1752-1752`. -/
def m1752 (expression : ExprValue) :=
  (expression.head = "quote" || expression.head = "inert") && expression.args.length = 1
def P1752 : Prop := ∀ expression, m1752 expression =
  ((expression.head = "quote" || expression.head = "inert") && expression.args.length = 1)
theorem p1752 : P1752 := fun _ => rfl

/-- `unquoted(ex::QuoteNode)`, `base/show.jl:1754-1754`. -/
def m1754 (node : QuoteNodeValue) := node.value
def P1754 : Prop := ∀ node, m1754 node = node.value
theorem p1754 : P1754 := fun _ => rfl

/-- `unquoted(ex::Expr)`, `base/show.jl:1755-1755`. -/
def m1755 (expression : ExprValue) : R DelimElement :=
  match expression.args with | value :: _ => .ok value | [] => .error .boundsError
def P1755 : Prop := ∀ expression, m1755 expression =
  match expression.args with | value :: _ => .ok value | [] => .error .boundsError
theorem p1755 : P1755 := fun _ => rfl

/-- `emphasize(io, str::AbstractString, col = Base.error_color())`, `base/show.jl:1762-1764`. -/
def m1762 (runtime : StyleRuntime) (io : StyledIO) (text color : String) :=
  emphasizeBody runtime io text color
def P1762 : Prop := ∀ runtime io text color, m1762 runtime io text color =
  if runtime.colorEnabled io then [.styled text color true]
  else [.plain (runtime.uppercase text)]
theorem p1762 : P1762 := fun _ _ _ _ => rfl

/-- `show_linenumber(io::IO, line)`, `base/show.jl:1766-1766`. -/
def m1766 (runtime : StyleRuntime) (line : DelimElement) := showLineBody runtime line none
def P1766 : Prop := ∀ runtime line, m1766 runtime line =
  [.styled ("#= line " ++ runtime.renderLine line ++ " =#") "light_black" false]
theorem p1766 : P1766 := fun _ _ => rfl

/-- `show_linenumber(io::IO, line, file)`, `base/show.jl:1767-1767`. -/
def m1767 (runtime : StyleRuntime) (line file : DelimElement) :=
  showLineBody runtime line (some file)
def P1767 : Prop := ∀ runtime line file, m1767 runtime line file =
  [.styled ("#= " ++ runtime.renderFile file ++ ":" ++ runtime.renderLine line ++ " =#")
    "light_black" false]
theorem p1767 : P1767 := fun _ _ _ => rfl

/-- `show_linenumber(io::IO, line, file::Nothing)`, `base/show.jl:1768-1768`. -/
def m1768 (runtime : StyleRuntime) (line : DelimElement) := m1766 runtime line
def P1768 : Prop := ∀ runtime line, m1768 runtime line = m1766 runtime line
theorem p1768 : P1768 := fun _ _ => rfl

/-- `show_block(io::IO, head, args::Vector, body, indent::Int, quote_level::Int)`, `base/show.jl:1771-1789`. -/
def m1771 (runtime : AstRuntime) (head : String) (arguments : List AstValue)
    (body : AstValue) (indent quoteLevel : Int) :=
  showAstBlockBody runtime head arguments body indent quoteLevel
def P1771 : Prop := ∀ runtime head indent quoteLevel,
  m1771 runtime head [] (.expr "block" []) indent quoteLevel =
    head ++ "\n" ++ String.ofList (List.replicate indent.toNat ' ')
theorem p1771 : P1771 := by
  intro runtime head indent quoteLevel
  simp [m1771, showAstBlockBody]

/-- `show_block(io::IO,head, block,i::Int, quote_level::Int)`, `base/show.jl:1790-1790`. -/
def m1790 (runtime : AstRuntime) (head : String) (body : AstValue)
    (indent quoteLevel : Int) := m1771 runtime head [] body indent quoteLevel
def P1790 : Prop := ∀ runtime head body indent quoteLevel,
  m1790 runtime head body indent quoteLevel = m1771 runtime head [] body indent quoteLevel
theorem p1790 : P1790 := fun _ _ _ _ _ => rfl

/-- `show_block(io::IO, head, arg, block, i::Int, quote_level::Int)`, `base/show.jl:1791-1797`. -/
def m1791 (runtime : AstRuntime) (head : String) (argument body : AstValue)
    (indent quoteLevel : Int) :=
  let arguments := match argument with
    | .expr "block" args | .expr "quote" args => args
    | _ => [argument]
  m1771 runtime head arguments body indent quoteLevel
def P1791 : Prop := ∀ runtime head arguments body indent quoteLevel,
  m1791 runtime head (.expr "block" arguments) body indent quoteLevel =
    m1771 runtime head arguments body indent quoteLevel
theorem p1791 : P1791 := by unfold P1791; intros; rfl

/-- `show_list(io::IO, items, sep, indent::Int, prec::Int=0, quote_level::Int=0, enclose_operators::Bool=false, kw::Bool=false)`, `base/show.jl:1800-1826`. -/
def m1800 (runtime : AstRuntime) (items : List AstValue) (separator : String)
    (indent prec quoteLevel : Int) (encloseOperators keyword : Bool) :=
  showAstListBody runtime items separator indent prec quoteLevel encloseOperators keyword
def P1800 : Prop := ∀ runtime separator indent prec quoteLevel encloseOperators keyword,
  m1800 runtime [] separator indent prec quoteLevel encloseOperators keyword = ""
theorem p1800 : P1800 := by unfold P1800; intros; rfl

/-- `show_enclosed_list(io::IO, op, items, sep, cl, indent, prec=0, quote_level=0, encl_ops=false, kw::Bool=false)`, `base/show.jl:1828-1832`. -/
def m1828 (runtime : AstRuntime) (openToken : String) (items : List AstValue)
    (separator closeToken : String) (indent prec quoteLevel : Int)
    (encloseOperators keyword : Bool) := openToken ++
  m1800 runtime items separator indent prec quoteLevel encloseOperators keyword ++ closeToken
def P1828 : Prop := ∀ runtime openToken items separator closeToken indent prec quoteLevel encloseOperators keyword,
  m1828 runtime openToken items separator closeToken indent prec quoteLevel encloseOperators keyword =
    openToken ++ m1800 runtime items separator indent prec quoteLevel encloseOperators keyword ++ closeToken
theorem p1828 : P1828 := fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- `show_call(io::IO, head, func, func_args, indent, quote_level, kw::Bool)`, `base/show.jl:1837-1862`. -/
def m1837 (runtime : AstRuntime) (head : String) (function : AstValue)
    (arguments : List AstValue) (indent quoteLevel : Int) (keyword : Bool) :=
  showAstCallBody runtime head function arguments indent quoteLevel keyword
def P1837 : Prop := ∀ runtime head reference indent quoteLevel keyword,
  head ≠ "." →
  runtime.callDelimiters head = ("(", ")") →
  m1837 runtime head (.globalRef reference) [] indent quoteLevel keyword =
    runtime.renderUnquoted (.globalRef reference) indent 0 quoteLevel ++ "()"
theorem p1837 : P1837 := by
  intro runtime head reference indent quoteLevel keyword hdot h
  simp [m1837, showAstCallBody, showAstListBody, h, hdot, String.append_assoc]

/-- `show_sym(io::IO, sym::Symbol; allow_macroname=false)`, `base/show.jl:1867-1876`. -/
def m1867 (runtime : SymbolPrintRuntime) (symbol : SymbolValue) (allowMacroname : Bool) :=
  showSymBody runtime symbol allowMacroname
def P1867 : Prop := ∀ runtime symbol allowMacroname,
  HasResult (m1867 runtime symbol allowMacroname) ∧
  (runtime.isValidIdentifier symbol = true →
    m1867 runtime symbol allowMacroname = runtime.string symbol)
theorem p1867 : P1867 := by
  intro runtime symbol allowMacroname
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1867, showSymBody, h]

/-- `show_unquoted(io::IO, val::SSAValue, ::Int, ::Int)`, `base/show.jl:1880-1894`. -/
def m1880 (runtime : SSARuntime) (io : StyledIO) (value : SSAValueModel) :=
  showSSABody runtime io value
def P1880 : Prop := ∀ runtime io value,
  HasResult (m1880 runtime io value) ∧
  (runtime.maxId io < value.id →
    m1880 runtime io value = [.styled ("%" ++ toString value.id) "red" false])
theorem p1880 : P1880 := by
  intro runtime io value
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m1880, showSSABody, h]

/-- `show_unquoted(io::IO, sym::Symbol, ::Int, ::Int)`, `base/show.jl:1895-1895`. -/
def m1895 (runtime : SymbolPrintRuntime) (symbol : SymbolValue) :=
  showSymBody runtime symbol false
def P1895 : Prop := ∀ runtime symbol, m1895 runtime symbol = showSymBody runtime symbol false
theorem p1895 : P1895 := fun _ _ => rfl

/-- `show_unquoted(io::IO, ex::LineNumberNode, ::Int, ::Int)`, `base/show.jl:1896-1896`. -/
def m1896 (runtime : StyleRuntime) (node : LineNodeModel) :=
  showLineBody runtime node.line node.file
def P1896 : Prop := ∀ runtime node,
  m1896 runtime node = showLineBody runtime node.line node.file
theorem p1896 : P1896 := fun _ _ => rfl

/-- `show_unquoted(io::IO, ex::GotoNode, ::Int, ::Int)`, `base/show.jl:1897-1897`. -/
def m1897 (label : Int) := Remaining.showGotoNode label
def P1897 : Prop := ∀ label, m1897 label = "goto %" ++ toString label
theorem p1897 : P1897 := fun label => rfl

/-- `show_unquoted(io::IO, ex::GlobalRef, ::Int, ::Int)`, `base/show.jl:1898-1898`. -/
def m1898 (runtime : GlobalRefRuntime) (reference : GlobalRefModel) :=
  showGlobalRefBody runtime reference false
def P1898 : Prop := ∀ runtime reference,
  m1898 runtime reference = showGlobalRefBody runtime reference false
theorem p1898 : P1898 := fun _ _ => rfl

/-- `show_unquoted(io::IO, bpart::Core.BindingPartition, ::Int, ::Int)`, `base/show.jl:1899-1900`. -/
def m1899 (runtime : GlobalRefRuntime) (partition : BindingPartitionModel) :=
  showGlobalRefBody runtime partition.owner false
def P1899 : Prop := ∀ runtime partition,
  m1899 runtime partition = showGlobalRefBody runtime partition.owner false
theorem p1899 : P1899 := fun _ _ => rfl

/-- `show_globalref(io::IO, ex::GlobalRef; allow_macroname=false)`, `base/show.jl:1902-1912`. -/
def m1902 (runtime : GlobalRefRuntime) (reference : GlobalRefModel)
    (allowMacroname : Bool) := showGlobalRefBody runtime reference allowMacroname
def P1902 : Prop := ∀ runtime reference allowMacroname,
  m1902 runtime reference allowMacroname = showGlobalRefBody runtime reference allowMacroname
theorem p1902 : P1902 := fun _ _ _ => rfl

/-- `show_unquoted(io::IO, ex::SlotNumber, ::Int, ::Int)`, `base/show.jl:1914-1922`. -/
def m1914 (io : SlotIO) (slot : SlotNumberModel) := showSlotBody io slot
def P1914 : Prop := ∀ io slot,
  (io.sourceSlotnames.isSome = true → slot.id = 0 → m1914 io slot = .error .boundsError) ∧
  HasResult (m1914 io slot)
theorem p1914 : P1914 := by
  intro io slot
  refine ⟨?_, hasResult _⟩
  intro hs hid
  cases slot with
  | mk id =>
    simp only at hid
    subst id
    cases h : io.sourceSlotnames with
    | none => simp [h] at hs
    | some names => simp [m1914, showSlotBody, h]

/-- `show_unquoted(io::IO, ex::QuoteNode, indent::Int, _prec::Int)`, `base/show.jl:1924-1935`. -/
def m1924 (runtime : QuoteRuntime) (io : ExprContext) (node : QuoteNodeModel)
    (indent : Int) := showQuoteNodeBody runtime io node indent
def P1924 : Prop := ∀ runtime io node indent,
  HasResult (m1924 runtime io node indent) ∧
  (∀ symbol, node.value = .symbol symbol →
    m1924 runtime io node indent = showQuotedBody runtime io (.symbol symbol) indent 0)
theorem p1924 : P1924 := by
  intro runtime io node indent
  refine ⟨hasResult _, ?_⟩
  intro symbol h
  cases node with
  | mk value => simp only at h; subst value; rfl

/-- `show_unquoted_quote_expr(io::IO, @nospecialize(value), indent::Int, quote_level::Int)`, `base/show.jl:1937-1960`. -/
def m1937 (runtime : QuoteRuntime) (io : ExprContext) (value : QuoteContent)
    (indent quoteLevel : Int) := showQuotedBody runtime io value indent quoteLevel
def P1937 : Prop := ∀ runtime io symbol indent quoteLevel,
  runtime.quotedIds.contains symbol.id = true →
  m1937 runtime io (.symbol symbol) indent quoteLevel =
    ":(" ++ runtime.symbols.string symbol ++ ")"
theorem p1937 : P1937 := by
  intro runtime io symbol indent quoteLevel h
  have hm : symbol.id ∈ runtime.quotedIds := by
    rw [← List.contains_iff_mem]
    exact h
  simp [m1937, showQuotedBody, hm]

/-- `show_generator(io, ex::Expr, indent, quote_level)`, `base/show.jl:1962-1981`. -/
def m1962 (runtime : GeneratorRuntime) (expression : GeneratorExpr)
    (indent quoteLevel : Int) := showGeneratorBody runtime expression indent quoteLevel
def P1962 : Prop := ∀ runtime expression indent quoteLevel,
  let collected := collectGenerator expression
  m1962 runtime expression indent quoteLevel =
    runtime.showUnquoted collected.1 indent 0 quoteLevel ++
      String.join (collected.2.map fun range => " for " ++
        runtime.showList range ", " indent 0 quoteLevel)
theorem p1962 : P1962 := fun _ _ _ _ => rfl

/-- `valid_import_path(@nospecialize(ex), allow_as = true)`, `base/show.jl:1983-1988`. -/
def m1983 (node : ImportNode) (allowAs : Bool) := validImportPathBody node allowAs
def P1983 : Prop := ∀ node allowAs, m1983 node allowAs = validImportPathBody node allowAs
theorem p1983 : P1983 := fun _ _ => rfl

/-- `show_import_path(io::IO, ex, quote_level)`, `base/show.jl:1990-2020`. -/
def m1990 (runtime : ImportRuntime) (node : ImportNode) (quoteLevel : Int) :=
  showImportPathBody runtime node quoteLevel
def P1990 : Prop := ∀ runtime symbol quoteLevel,
  m1990 runtime (.symbol symbol) quoteLevel =
    .ok (runtime.renderUnquoted (.symbol symbol) 0 0 0)
theorem p1990 : P1990 := by
  unfold P1990 m1990 showImportPathBody
  intros
  rfl

/-- `allow_macroname(ex)`, `base/show.jl:2023-2032`. -/
def m2023 (runtime : SymbolPrintRuntime) (node : ImportNode) := allowMacronameBody runtime node
def P2023 : Prop := ∀ runtime reference,
  m2023 runtime (.globalRef reference) = .expr "macroname" [.globalRef reference]
theorem p2023 : P2023 := by unfold P2023; intros; rfl

/-- `is_core_macro(arg::GlobalRef, macro_name::AbstractString)`, `base/show.jl:2034-2034`. -/
def m2034 (runtime : SymbolPrintRuntime) (reference : GlobalRefModel) (macroName : String) :=
  isCoreMacroBody reference (runtime.symbolFromString macroName)
def P2034 : Prop := ∀ runtime reference macroName,
  m2034 runtime reference macroName =
    isCoreMacroBody reference (runtime.symbolFromString macroName)
theorem p2034 : P2034 := fun _ _ _ => rfl

/-- `is_core_macro(arg::GlobalRef, macro_name::Symbol)`, `base/show.jl:2035-2035`. -/
def m2035 (reference : GlobalRefModel) (macroName : SymbolValue) :=
  isCoreMacroBody reference macroName
def P2035 : Prop := ∀ reference macroName, m2035 reference macroName =
  (reference.moduleValue.name = "Core" && reference.name.id = macroName.id)
theorem p2035 : P2035 := fun _ _ => rfl

/-- `is_core_macro(@nospecialize(arg), macro_name::AbstractString)`, `base/show.jl:2036-2036`. -/
def m2036 (_arg : DelimElement) (_macroName : String) := false
def P2036 : Prop := ∀ arg macroName, m2036 arg macroName = false
theorem p2036 : P2036 := fun _ _ => rfl

/-- `is_core_macro(@nospecialize(arg), macro_name::Symbol)`, `base/show.jl:2037-2037`. -/
def m2037 (_arg : DelimElement) (_macroName : SymbolValue) := false
def P2037 : Prop := ∀ arg macroName, m2037 arg macroName = false
theorem p2037 : P2037 := fun _ _ => rfl

/-- `show_unquoted_expr_fallback(io::IO, ex::Expr)`, `base/show.jl:2043-2051`. -/
def m2043 (runtime : ExprFallbackRuntime) (expression : ExprFallbackValue) :=
  showExprFallbackBody runtime expression
def P2043 : Prop := ∀ runtime expression,
  m2043 runtime expression = "$(Expr(" ++ runtime.render expression.head ++
    String.join (expression.args.map fun arg => ", " ++ runtime.render arg) ++ "))"
theorem p2043 : P2043 := fun _ _ => rfl

/-- `show_unquoted(io::IO, ex::Expr, indent::Int, prec::Int, quote_level::Int = 0)`, `base/show.jl:2054-2606`. -/
def m2054 (runtime : FullExprRuntime) (unquoteFallback beginsym : Bool)
    (expression : AstValue) (indent prec quoteLevel : Int) :=
  showExprFullBody runtime unquoteFallback beginsym expression indent prec quoteLevel
def P2054 : Prop := ∀ runtime unquoteFallback beginsym expression indent prec quoteLevel,
  (∀ id, expression = .other id →
    m2054 runtime unquoteFallback beginsym expression indent prec quoteLevel =
      runtime.ast.renderUnquoted (.other id) indent prec quoteLevel)
theorem p2054 : P2054 := by
  intro runtime unquoteFallback beginsym expression indent prec quoteLevel id h
  subst expression; rfl

/-- `demangle_function_name(name::Symbol)`, `base/show.jl:2608-2608`. -/
def m2608 (runtime : SymbolPrintRuntime) (name : SymbolValue) :=
  runtime.symbolFromString (demangleFunctionBody (runtime.string name))
def P2608 : Prop := ∀ runtime name, m2608 runtime name =
  runtime.symbolFromString (demangleFunctionBody (runtime.string name))
theorem p2608 : P2608 := fun _ _ => rfl

/-- `demangle_function_name(name::AbstractString)`, `base/show.jl:2609-2616`. -/
def m2609 (name : String) := demangleFunctionBody name
def P2609 : Prop := ∀ name, m2609 name =
  let pieces := name.splitOn "#"
  match pieces with
  | first :: _ :: _ => if first.isEmpty then name else first
  | _ => name
theorem p2609 : P2609 := fun _ => rfl

/-- `show_signature_function(io::IO, @nospecialize(ft), demangle=false, fargname="", html=false, qualified=false)`, `base/show.jl:2620-2643`. -/
def m2620 (runtime : SignatureRuntime) (input : TypeObject) (demangle : Bool)
    (argumentName : String) (html qualified : Bool) :=
  showSignatureFunctionBody runtime input demangle argumentName html qualified
def P2620 : Prop := ∀ runtime input demangle argumentName html qualified,
  runtime.asDataType (runtime.unwrapUnionall input) = none →
  runtime.isType input = false → html = true →
  m2620 runtime input demangle argumentName html qualified =
    "(" ++ argumentName ++ "::<b>" ++ runtime.renderType input ++ "</b>)"
theorem p2620 : P2620 := by
  intro runtime input demangle argumentName html qualified hd ht hh
  simp [m2620, showSignatureFunctionBody, hd, ht, hh]

/-- `print_within_stacktrace(io, s...; color=:normal, bold=false)`, `base/show.jl:2645-2651`. -/
def m2645 (io : StacktraceIO) (pieces : List String) (color : String) (bold : Bool) :=
  printWithinStacktraceBody io pieces color bold
def P2645 : Prop := ∀ io pieces color bold, m2645 io pieces color bold =
  if io.backtrace then [.styled (String.join pieces) color bold]
  else [.plain (String.join pieces)]
theorem p2645 : P2645 := fun _ _ _ _ => rfl

/-- `show_tuple_as_call(out::IO, name::Symbol, sig::Type; demangle=false, kwargs=nothing, argnames=nothing, qualified=false, hasfirst=true)`, `base/show.jl:2653-2710`. -/
def m2653 (runtime : TupleCallRuntime) (name : SymbolValue) (signature : SignatureType)
    (demangle : Bool) (kwargs : Option (List (SymbolValue × TypeObject)))
    (argumentNames : Option (List SymbolValue)) (qualified hasFirst : Bool) :=
  showTupleCallBody runtime name signature demangle kwargs argumentNames qualified hasFirst
def P2653 : Prop := ∀ runtime name signature demangle kwargs argumentNames qualified hasFirst,
  signature = .tupleRoot → m2653 runtime name signature demangle kwargs argumentNames qualified hasFirst =
    runtime.symbols.string (if demangle then runtime.symbols.symbolFromString
      (demangleFunctionBody (runtime.symbols.string name)) else name) ++ "(...)"
theorem p2653 : P2653 := by
  intro runtime name signature demangle kwargs argumentNames qualified hasFirst h
  subst signature; rfl

/-- `type_limited_string_from_context(out::IO, str::String)`, `base/show.jl:2712-2723`. -/
def m2712 (runtime : TypeLimitRuntime) (context : TypeLimitContext) (text : String) :=
  typeLimitedBody runtime context text
def P2712 : Prop := ∀ runtime context text,
  HasResult (m2712 runtime context text) ∧
  (context.limitedFlag = none → m2712 runtime context text = (text, none))
theorem p2712 : P2712 := by
  intro runtime context text
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m2712, typeLimitedBody, h]

/-- `type_depth_limit(str::String, n::Int; maxdepth = nothing)`, `base/show.jl:2726-2816`. -/
def m2726 (tw : Char → Nat) (s : List Char) (width : Int) (maxDepth : Option Int) := Truncate.typeDepthLimit tw s width maxDepth
def P2726 : Prop := ∀ (tw : Char → Nat) (s : List Char) (width : Int) (maxDepth : Option Int), (m2726 tw s width maxDepth) = Truncate.typeDepthLimit tw s width maxDepth
theorem p2726 : P2726 := fun tw s width maxDepth => rfl

/-- `stateis(s)`, `base/show.jl:2734-2734`. -/
def m2734 (state bit : Nat) := (state &&& bit) != 0
def P2734 : Prop := ∀ state bit, m2734 state bit = ((state &&& bit) != 0)
theorem p2734 : P2734 := fun _ _ => rfl

/-- `quoted()`, `base/show.jl:2735-2735`. -/
def m2735 (state : Nat) := m2734 state 2 || m2734 state 4
def P2735 : Prop := ∀ state, m2735 state =
  ((state &&& 2) != 0 || (state &&& 4) != 0)
theorem p2735 : P2735 := fun _ => rfl

/-- `enter(s)`, `base/show.jl:2736-2736`. -/
def m2736 (state bit : Nat) := state ||| bit
def P2736 : Prop := ∀ state bit, m2736 state bit = (state ||| bit)
theorem p2736 : P2736 := fun _ _ => rfl

/-- `leave(s)`, `base/show.jl:2737-2737`. -/
def m2737 (state bit : Nat) := state - (state &&& bit)
def P2737 : Prop := ∀ state bit, m2737 state bit = state - (state &&& bit)
theorem p2737 : P2737 := fun _ _ => rfl

/-- `print_type_bicolor(io, type; kwargs...)`, `base/show.jl:2818-2821`. -/
def m2818 (runtime : TypeColorRuntime) (io : StacktraceIO) (type : TypeObject)
    (color innerColor : String) (useColor : Bool) :=
  printTypeBicolorText (runtime.renderType type io) color innerColor useColor
def P2818 : Prop := ∀ runtime io type color innerColor useColor,
  m2818 runtime io type color innerColor useColor =
    printTypeBicolorText (runtime.renderType type io) color innerColor useColor
theorem p2818 : P2818 := fun _ _ _ _ _ _ => rfl

/-- `print_type_bicolor(io, str::String; color=:normal, inner_color=:light_black, use_color::Bool=true)`, `base/show.jl:2823-2838`. -/
def m2823 (text color innerColor : String) (useColor : Bool) :=
  printTypeBicolorText text color innerColor useColor
def P2823 : Prop := ∀ text color innerColor useColor,
  HasResult (m2823 text color innerColor useColor) ∧
  (useColor = false → m2823 text color innerColor useColor = [.plain text])
theorem p2823 : P2823 := by
  intro text color innerColor useColor
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m2823, printTypeBicolorText, h]

/-- `resolvebinding(@nospecialize(ex))`, `base/show.jl:2840-2840`. -/
def m2840 (node : BindingNode) := BindingResult.value node
def P2840 : Prop := ∀ node, m2840 node = .value node
theorem p2840 : P2840 := fun _ => rfl

/-- `resolvebinding(ex::QuoteNode)`, `base/show.jl:2841-2841`. -/
def m2841 (value : BindingNode) := BindingResult.value value
def P2841 : Prop := ∀ value, m2841 value = .value value
theorem p2841 : P2841 := fun _ => rfl

/-- `resolvebinding(ex::Symbol)`, `base/show.jl:2842-2842`. -/
def m2842 (runtime : BindingRuntime) (symbol : SymbolValue) :=
  resolveGlobalBody runtime ⟨runtime.mainModule, symbol⟩
def P2842 : Prop := ∀ runtime symbol, m2842 runtime symbol =
  resolveGlobalBody runtime ⟨runtime.mainModule, symbol⟩
theorem p2842 : P2842 := fun _ _ => rfl

/-- `resolvebinding(ex::Expr)`, `base/show.jl:2843-2851`. -/
def m2843 (runtime : BindingRuntime) (expression : BindingNode) :=
  resolveBindingBody runtime 32 expression
def P2843 : Prop := ∀ runtime id,
  m2843 runtime (.other id) = .value (.other id)
theorem p2843 : P2843 := by unfold P2843; intros; rfl

/-- `resolvebinding(ex::GlobalRef)`, `base/show.jl:2852-2858`. -/
def m2852 (runtime : BindingRuntime) (reference : GlobalRefModel) :=
  resolveGlobalBody runtime reference
def P2852 : Prop := ∀ runtime reference,
  (runtime.isDefined reference = false → m2852 runtime reference = .nothing) ∧
  HasResult (m2852 runtime reference)
theorem p2852 : P2852 := by
  intro runtime reference
  refine ⟨?_, hasResult _⟩
  intro h; simp [m2852, resolveGlobalBody, h]

/-- `ismodulecall(ex::Expr)`, `base/show.jl:2860-2864`. -/
def m2860 (runtime : BindingRuntime) (expression : BindingNode) :=
  isModuleCallBody runtime expression
def P2860 : Prop := ∀ runtime expression, m2860 runtime expression =
  isModuleCallBody runtime expression
theorem p2860 : P2860 := fun _ _ => rfl

/-- `show(io::IO, tv::TypeVar)`, `base/show.jl:2866-2899`. -/
def m2866 (runtime : TypeVarShowRuntime) (context : TypeVarContext)
    (typevar : TypeVarValue) := showTypevarBody runtime context typevar
def P2866 : Prop := ∀ runtime context typevar,
  typevarInEnv context typevar = true →
    m2866 runtime context typevar = runtime.renderName typevar.name
theorem p2866 : P2866 := by
  intro runtime context typevar h
  simp [m2866, showTypevarBody, h]

/-- `show_bound(io::IO, @nospecialize(b))`, `base/show.jl:2873-2879`. -/
def m2873 (runtime : TypeVarShowRuntime) (bound : TypeObject) := showBoundBody runtime bound
def P2873 : Prop := ∀ runtime bound, m2873 runtime bound =
  (if runtime.isUnionAll bound && !runtime.printWithoutParams bound then "(" else "") ++
    runtime.renderBound bound ++
    if runtime.isUnionAll bound && !runtime.printWithoutParams bound then ")" else ""
theorem p2873 : P2873 := fun _ _ => rfl

/-- `show(io::IO, vm::Core.TypeofVararg)`, `base/show.jl:2901-2912`. -/
def m2901 (runtime : VarargRuntime) (value : VarargValue) := showVarargBody runtime value
def P2901 : Prop := ∀ runtime value,
  HasResult (m2901 runtime value) ∧
  (value.typeField = none → m2901 runtime value = "Vararg")
theorem p2901 : P2901 := by
  intro runtime value
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m2901, showVarargBody, h]

/-- `show(io::IO, src::CodeInfo; debuginfo::Symbol=:source)`, `base/show.jl:2916-2929`. -/
def m2916 (runtime : CodeInfoRuntime) (source : CodeInfoModel) (debugInfo : String) :=
  showCodeInfoBody runtime source debugInfo
def P2916 : Prop := ∀ runtime source debugInfo, m2916 runtime source debugInfo =
  "CodeInfo(\n" ++ runtime.showIR source
    (source.slotnames.map (sourceSlotnamesBody runtime.slotRuntime))
    (runtime.debugInfoConfig debugInfo source) ++ ")"
theorem p2916 : P2916 := fun _ _ _ => rfl

/-- `show_unquoted(io::IO, val::Argument, indent::Int, prec::Int)`, `base/show.jl:2931-2931`. -/
def m2931 (io : SlotIO) (argument : ArgumentNode) := m1914 io ⟨argument.n⟩
def P2931 : Prop := ∀ io argument, m2931 io argument = m1914 io ⟨argument.n⟩
theorem p2931 : P2931 := fun _ _ => rfl

/-- `show_unquoted(io::IO, stmt::PhiNode, indent::Int, ::Int)`, `base/show.jl:2933-2933`. -/
def m2933 (runtime : IRNodeRuntime) (node : PhiNodeValue) (indent : Int) :=
  showPhiBody runtime node indent "%"
def P2933 : Prop := ∀ runtime node indent,
  m2933 runtime node indent = showPhiBody runtime node indent "%"
theorem p2933 : P2933 := fun _ _ _ => rfl

/-- `show_unquoted_phinode(io::IO, stmt::PhiNode, indent::Int, prefix::String)`, `base/show.jl:2934-2947`. -/
def m2934 (runtime : IRNodeRuntime) (node : PhiNodeValue) (indent : Int)
    (labelPrefix : String) := showPhiBody runtime node indent labelPrefix
def P2934 : Prop := ∀ runtime values indent labelPrefix,
  m2934 runtime ⟨[], values⟩ indent labelPrefix = "φ ()"
theorem p2934 : P2934 := by unfold P2934; intros; rfl

/-- `show_unquoted(io::IO, stmt::PhiCNode, indent::Int, ::Int)`, `base/show.jl:2949-2957`. -/
def m2949 (runtime : IRNodeRuntime) (node : PhiCNodeValue) (indent : Int) :=
  showPhiCBody runtime node indent
def P2949 : Prop := ∀ runtime node indent,
  m2949 runtime node indent = showPhiCBody runtime node indent
theorem p2949 : P2949 := fun _ _ _ => rfl

/-- `show_unquoted(io::IO, stmt::PiNode, indent::Int, ::Int)`, `base/show.jl:2959-2965`. -/
def m2959 (runtime : IRNodeRuntime) (node : PiNodeValue) (indent : Int) : List WriteEvent :=
  [.plain ("π (" ++ runtime.renderUnquoted node.value indent ++ ", "),
    .styled (runtime.renderType node.type) "cyan" false, .plain ")"]
def P2959 : Prop := ∀ runtime node indent, m2959 runtime node indent =
  [.plain ("π (" ++ runtime.renderUnquoted node.value indent ++ ", "),
    .styled (runtime.renderType node.type) "cyan" false, .plain ")"]
theorem p2959 : P2959 := fun _ _ _ => rfl

/-- `show_unquoted(io::IO, stmt::UpsilonNode, indent::Int, ::Int)`, `base/show.jl:2967-2973`. -/
def m2967 (runtime : IRNodeRuntime) (node : OptionalNodeValue) (indent : Int) :=
  "ϒ (" ++ (match node.value with
    | some value => runtime.renderUnquoted value indent
    | none => "#undef") ++ ")"
def P2967 : Prop := ∀ runtime indent,
  m2967 runtime ⟨none⟩ indent = "ϒ (#undef)"
theorem p2967 : P2967 := by unfold P2967; intros; rfl

/-- `show_unquoted(io::IO, stmt::ReturnNode, indent::Int, ::Int)`, `base/show.jl:2975-2982`. -/
def m2975 (runtime : IRNodeRuntime) (node : OptionalNodeValue) (indent : Int) :=
  match node.value with
  | none => "unreachable"
  | some value => "return " ++ runtime.renderUnquoted value indent
def P2975 : Prop := ∀ runtime indent,
  m2975 runtime ⟨none⟩ indent = "unreachable"
theorem p2975 : P2975 := by unfold P2975; intros; rfl

/-- `show_unquoted(io::IO, stmt::GotoIfNot, indent::Int, ::Int)`, `base/show.jl:2984-2984`. -/
def m2984 (runtime : IRNodeRuntime) (node : GotoIfNotValue) (indent : Int) :=
  showGotoIfNotBody runtime node indent "%"
def P2984 : Prop := ∀ runtime node indent,
  m2984 runtime node indent = showGotoIfNotBody runtime node indent "%"
theorem p2984 : P2984 := fun _ _ _ => rfl

/-- `show_unquoted_gotoifnot(io::IO, stmt::GotoIfNot, indent::Int, prefix::String)`, `base/show.jl:2985-2988`. -/
def m2985 (runtime : IRNodeRuntime) (node : GotoIfNotValue) (indent : Int)
    (labelPrefix : String) := showGotoIfNotBody runtime node indent labelPrefix
def P2985 : Prop := ∀ runtime node indent labelPrefix,
  m2985 runtime node indent labelPrefix = showGotoIfNotBody runtime node indent labelPrefix
theorem p2985 : P2985 := fun _ _ _ _ => rfl

/-- `dump(io::IOContext, x::SimpleVector, n::Int, indent)`, `base/show.jl:2990-3008`. -/
def m2990 (runtime : DumpRuntime) (limit : Bool) (depth : Nat)
    (indent : String) (value : DumpValue) := dumpBody runtime limit depth indent value
def P2990 : Prop := ∀ runtime limit depth indent value,
  value = .simpleVector [] → m2990 runtime limit depth indent value = "empty SimpleVector"
theorem p2990 : P2990 := by
  intro runtime limit depth indent value h
  subst value; cases depth <;> simp [m2990, dumpBody]

/-- `dump(io::IOContext, @nospecialize(x), n::Int, indent)`, `base/show.jl:3010-3041`. -/
def m3010 (runtime : DumpRuntime) (limit : Bool) (depth : Nat)
    (indent : String) (value : DumpValue) := dumpBody runtime limit depth indent value
def P3010 : Prop := ∀ runtime limit depth indent value,
  value = .bottom → m3010 runtime limit depth indent value = runtime.renderBottom
theorem p3010 : P3010 := by
  intro runtime limit depth indent value h
  subst value; cases depth <;> simp [m3010, dumpBody]

/-- `dump(io::IOContext, x::Module, n::Int, indent)`, `base/show.jl:3043-3043`. -/
def m3043 (runtime : DumpRuntime) (module : ModuleValue) :=
  dumpBody runtime false 0 "" (.module module)
def P3043 : Prop := ∀ runtime module,
  m3043 runtime module = "Module " ++ runtime.renderModule module
theorem p3043 : P3043 := fun _ _ => rfl

/-- `dump(io::IOContext, x::String, n::Int, indent)`, `base/show.jl:3044-3044`. -/
def m3044 (runtime : DumpRuntime) (value : String) :=
  dumpBody runtime false 0 "" (.string value)
def P3044 : Prop := ∀ runtime value,
  m3044 runtime value = "String " ++ runtime.renderString value
theorem p3044 : P3044 := fun _ _ => rfl

/-- `dump(io::IOContext, x::Symbol, n::Int, indent)`, `base/show.jl:3045-3045`. -/
def m3045 (runtime : DumpRuntime) (symbol : SymbolValue) :=
  dumpBody runtime false 0 "" (.symbol symbol)
def P3045 : Prop := ∀ runtime symbol,
  m3045 runtime symbol = "Symbol " ++ runtime.renderSymbol symbol
theorem p3045 : P3045 := fun _ _ => rfl

/-- `dump(io::IOContext, x::Union, n::Int, indent)`, `base/show.jl:3046-3046`. -/
def m3046 (runtime : DumpRuntime) (type : TypeObject) :=
  dumpBody runtime false 0 "" (.unionType type)
def P3046 : Prop := ∀ runtime type, m3046 runtime type = runtime.renderType type
theorem p3046 : P3046 := fun _ _ => rfl

/-- `dump(io::IOContext, x::Ptr, n::Int, indent)`, `base/show.jl:3047-3047`. -/
def m3047 (runtime : DumpRuntime) (address : Nat) :=
  dumpBody runtime false 0 "" (.pointer address)
def P3047 : Prop := ∀ runtime address, m3047 runtime address = runtime.renderPointer address
theorem p3047 : P3047 := fun _ _ => rfl

/-- `dump_elts(io::IOContext, x::Array, n::Int, indent, i0, i1)`, `base/show.jl:3049-3059`. -/
def m3049 (runtime : DumpRuntime) (depth : Nat) (indent : String)
    (slots : List (Option DumpValue)) (first last : Nat) :=
  dumpElementsBody runtime depth indent slots first last
def P3049 : Prop := ∀ runtime depth indent slots first,
  first > 0 → m3049 runtime depth indent slots first (first - 1) = ""
theorem p3049 : P3049 := by
  intro runtime depth indent slots first h
  simp [m3049, dumpElementsBody, Nat.sub_add_cancel (by omega : 1 ≤ first)]

/-- `dump(io::IOContext, x::Array, n::Int, indent)`, `base/show.jl:3061-3084`. -/
def m3061 (runtime : DumpRuntime) (limit : Bool) (depth : Nat) (indent : String)
    (array : DumpValue) := dumpBody runtime limit depth indent array
def P3061 : Prop := ∀ runtime limit depth indent array,
  (∀ elementType shape slots, array = .array elementType shape true slots →
    m3061 runtime limit depth indent array =
      "Array{" ++ runtime.renderType elementType ++ "}(" ++ shape ++ ") " ++
        runtime.renderValue (.array elementType shape true slots))
theorem p3061 : P3061 := by
  intro runtime limit depth indent array elementType shape slots h
  subst array; simp [m3061, dumpBody]

/-- `dump(io::IOContext, x::DataType, n::Int, indent)`, `base/show.jl:3087-3126`. -/
def m3087 (runtime : DumpRuntime) (depth : Nat) (indent : String)
    (datatype : DumpDatatype) := dumpBody runtime false depth indent (.datatype datatype)
def P3087 : Prop := ∀ runtime depth indent datatype,
  datatype.isAny = true → depth = 0 →
    m3087 runtime depth indent datatype =
      (if datatype.isMutable && datatype.isStruct then "mutable " else "") ++
      (if datatype.isStruct && !datatype.isTuple then "struct " else "") ++
      (if datatype.isPrimitive then "primitive type " else "") ++
      (if datatype.isAbstract then "abstract type " else "") ++
      runtime.renderType datatype.typeId
theorem p3087 : P3087 := by
  intro runtime depth indent datatype ha hd
  subst depth
  simp [m3087, dumpBody, ha]

/-- `dump(io::IO, @nospecialize(x); maxdepth=DUMP_DEFAULT_MAXDEPTH)`, `base/show.jl:3130-3133`. -/
def m3130 (runtime : DumpRuntime) (limit : Bool) (maxDepth : Nat) (value : DumpValue) :=
  dumpBody runtime limit maxDepth "" value ++ "\n"
def P3130 : Prop := ∀ runtime limit maxDepth value,
  m3130 runtime limit maxDepth value = dumpBody runtime limit maxDepth "" value ++ "\n"
theorem p3130 : P3130 := fun _ _ _ _ => rfl

/-- `dump(arg; maxdepth=DUMP_DEFAULT_MAXDEPTH)`, `base/show.jl:3163-3167`. -/
def m3163 (runtime : DumpRuntime) (maxDepth : Nat) (value : DumpValue) :=
  m3130 runtime true maxDepth value
def P3163 : Prop := ∀ runtime maxDepth value,
  m3163 runtime maxDepth value = m3130 runtime true maxDepth value
theorem p3163 : P3163 := fun _ _ _ => rfl

/-- `nocolor(io::IO)`, `base/show.jl:3169-3169`. -/
def m3169 (io : AlignmentIO) := noColorIO io
def P3169 : Prop := ∀ io, (m3169 io).color = false
theorem p3169 : P3169 := fun _ => rfl

/-- `alignment_from_show(io::IO, x::Any)`, `base/show.jl:3170-3171`. -/
def m3170 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  alignmentFromShowBody runtime io value
def P3170 : Prop := ∀ runtime io value, m3170 runtime io value =
  Truncate.textwidth runtime.charWidth (runtime.render (noColorIO io) value).toList
theorem p3170 : P3170 := fun _ _ _ => rfl

/-- `alignment_from_show(io::IO, x::AbstractString)`, `base/show.jl:3172-3173`. -/
def m3172 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  alignmentFromPlainStringBody runtime io value
def P3172 : Prop := ∀ runtime io value, m3172 runtime io value =
  Truncate.textwidth runtime.charWidth
    (runtime.renderPlainString (noColorIO io) value).toList
theorem p3172 : P3172 := fun _ _ _ => rfl

/-- `alignment(io::IO, x::Any)`, `base/show.jl:3191-3191`. -/
def m3191 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  (0, m3170 runtime io value)
def P3191 : Prop := ∀ runtime io value, m3191 runtime io value =
  (0, m3170 runtime io value)
theorem p3191 : P3191 := fun _ _ _ => rfl

/-- `alignment(io::IO, x::Number)`, `base/show.jl:3192-3192`. -/
def m3192 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  (m3170 runtime io value, 0)
def P3192 : Prop := ∀ runtime io value, m3192 runtime io value =
  (m3170 runtime io value, 0)
theorem p3192 : P3192 := fun _ _ _ => rfl

/-- `alignment(io::IO, x::Integer)`, `base/show.jl:3193-3193`. -/
def m3193 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  (m3170 runtime io value, 0)
def P3193 : Prop := ∀ runtime io value, m3193 runtime io value =
  (m3170 runtime io value, 0)
theorem p3193 : P3193 := fun _ _ _ => rfl

/-- `alignment(io::IO, x::Real)`, `base/show.jl:3194-3199`. -/
def m3194 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  Containers.alignmentReal runtime.charWidth (runtime.render (noColorIO io) value).toList
def P3194 : Prop := ∀ runtime io value,
  runtime.render (noColorIO io) value = "" → m3194 runtime io value = (0, 0)
theorem p3194 : P3194 := by
  intro runtime io value h
  simp [m3194, h, Containers.alignmentReal, Containers.splitRealAt]

/-- `alignment(io::IO, x::Complex)`, `base/show.jl:3200-3205`. -/
def m3200 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  Containers.alignmentComplex runtime.charWidth (runtime.render (noColorIO io) value).toList
def P3200 : Prop := ∀ runtime io value,
  runtime.render (noColorIO io) value = "" → m3200 runtime io value = (0, 0)
theorem p3200 : P3200 := by
  intro runtime io value h
  simp [m3200, h, Containers.alignmentComplex, Containers.splitComplex,
    Containers.alignmentAny]

/-- `alignment(io::IO, x::Rational)`, `base/show.jl:3206-3211`. -/
def m3206 (runtime : AlignmentRuntime) (io : AlignmentIO) (value : AlignmentValue) :=
  Containers.alignmentRational runtime.charWidth (runtime.render (noColorIO io) value).toList
def P3206 : Prop := ∀ runtime io value,
  runtime.render (noColorIO io) value = "" → m3206 runtime io value = (0, 0)
theorem p3206 : P3206 := by
  intro runtime io value h
  simp [m3206, h, Containers.alignmentRational, Containers.splitRational,
    Containers.alignmentAny]

/-- `alignment(io::IO, x::Pair)`, `base/show.jl:3213-3224`. -/
def m3213 (runtime : PairAlignmentRuntime) (io : PairIO) (pair : PairValue) :=
  alignmentPairBody runtime io pair
def P3213 : Prop := ∀ runtime io pair,
  pairDelimitedBody runtime.pairRuntime io pair = true →
  m3213 runtime io pair =
    (0, stringWidth runtime.charWidth (runtime.renderPair io pair))
theorem p3213 : P3213 := by
  intro runtime io pair h
  simp [m3213, alignmentPairBody, h]

/-- `show(io::IO, ::UndefInitializer)`, `base/show.jl:3228-3228`. -/
def m3228 (_io : AlignmentIO) : Out := ["UndefInitializer()"]
def P3228 : Prop := ∀ io, m3228 io = ["UndefInitializer()"]
theorem p3228 : P3228 := fun _ => rfl

/-- `summary(io::IO, x)`, `base/show.jl:3249-3249`. -/
def m3249 (runtime : SummaryRuntime) (value : SummaryValue) :=
  runtime.renderType value.typeId
def P3249 : Prop := ∀ runtime value, m3249 runtime value = runtime.renderType value.typeId
theorem p3249 : P3249 := fun _ _ => rfl

/-- `summary(x)`, `base/show.jl:3250-3254`. -/
def m3250 (runtime : SummaryRuntime) (value : SummaryValue) := m3249 runtime value
def P3250 : Prop := ∀ runtime value, m3250 runtime value = m3249 runtime value
theorem p3250 : P3250 := fun _ _ => rfl

/-- `dims2string(d)`, `base/show.jl:3258-3260`. -/
def m3258 (dimensions : List Nat) := dimsText dimensions
def P3258 : Prop := m3258 [] = "0-dimensional" ∧
  ∀ length, m3258 [length] = toString length ++ "-element"
theorem p3258 : P3258 := by
  constructor
  · rfl
  · intro length; rfl

/-- `inds2string(inds)`, `base/show.jl:3262-3262`. -/
def m3262 (runtime : SummaryRuntime) (axes : List AxisModel) := axesText runtime axes
def P3262 : Prop := ∀ runtime axes, m3262 runtime axes =
  "×".intercalate (axes.map (axisText runtime))
theorem p3262 : P3262 := fun _ _ => rfl

/-- `_indsstring(i)`, `base/show.jl:3263-3263`. -/
def m3263 (runtime : SummaryRuntime) (axis : AxisModel) := runtime.renderValue axis.value
def P3263 : Prop := ∀ runtime axis, m3263 runtime axis = runtime.renderValue axis.value
theorem p3263 : P3263 := fun _ _ => rfl

/-- `_indsstring(i::Union{IdentityUnitRange, Slice})`, `base/show.jl:3264-3264`. -/
def m3264 (runtime : SummaryRuntime) (axis : AxisModel) :=
  runtime.renderValue (axis.indices.getD axis.value)
def P3264 : Prop := ∀ runtime axis, m3264 runtime axis =
  runtime.renderValue (axis.indices.getD axis.value)
theorem p3264 : P3264 := fun _ _ => rfl

/-- `summary(io::IO, a::AbstractArray)`, `base/show.jl:3267-3267`. -/
def m3267 (runtime : SummaryRuntime) (array : SummaryValue) :=
  let axes := runtime.axes array
  arraySummaryBody runtime array axes (!(axes.all (·.oneTo)))
def P3267 : Prop := ∀ runtime array,
  (runtime.axes array).all (·.oneTo) = true →
  m3267 runtime array = arraySummaryBody runtime array (runtime.axes array) false
theorem p3267 : P3267 := by
  intro runtime array h
  unfold m3267
  simp [h]

/-- `array_summary(io::IO, a, inds::Tuple{Vararg{OneTo}})`, `base/show.jl:3268-3271`. -/
def m3268 (runtime : SummaryRuntime) (array : SummaryValue) (axes : List AxisModel) :=
  arraySummaryBody runtime array axes false
def P3268 : Prop := ∀ runtime array axes,
  m3268 runtime array axes = dimsText (axes.map (·.length)) ++ " " ++ runtime.showarg array true
theorem p3268 : P3268 := by
  intro runtime array axes
  simp [m3268, arraySummaryBody]

/-- `array_summary(io::IO, a, inds)`, `base/show.jl:3272-3276`. -/
def m3272 (runtime : SummaryRuntime) (array : SummaryValue) (axes : List AxisModel) :=
  arraySummaryBody runtime array axes true
def P3272 : Prop := ∀ runtime array axes,
  m3272 runtime array axes = dimsText (axes.map (·.length)) ++ " " ++
    runtime.showarg array true ++ " with indices " ++ axesText runtime axes
theorem p3272 : P3272 := by
  intro runtime array axes
  simp [m3272, arraySummaryBody, String.append_assoc]

/-- `summary(io::IO, mref::GenericMemoryRef)`, `base/show.jl:3279-3284`. -/
def m3279 (runtime : SummaryRuntime) (reference : MemoryRefValue) :=
  toString (reference.memoryLength - reference.offset + 1) ++ "-element " ++
    runtime.showargMemory reference true
def P3279 : Prop := ∀ runtime reference, m3279 runtime reference =
  toString (reference.memoryLength - reference.offset + 1) ++ "-element " ++
    runtime.showargMemory reference true
theorem p3279 : P3279 := fun _ _ => rfl

/-- `summary(io::IO, f::Function)`, `base/show.jl:3287-3287`. -/
def m3287 (runtime : SummaryRuntime) (function : SummaryValue) :=
  runtime.showPlainFunction function
def P3287 : Prop := ∀ runtime function,
  m3287 runtime function = runtime.showPlainFunction function
theorem p3287 : P3287 := fun _ _ => rfl

/-- `showarg(io::IO, @nospecialize(x), toplevel)`, `base/show.jl:3335-3338`. -/
def m3335 (runtime : SummaryRuntime) (value : SummaryValue) (top : Bool) :=
  (if top then "" else "::") ++ runtime.renderType value.typeId
def P3335 : Prop := ∀ runtime value top, m3335 runtime value top =
  (if top then "" else "::") ++ runtime.renderType value.typeId
theorem p3335 : P3335 := fun _ _ _ => rfl

/-- `showarg(io::IO, T::Type, toplevel)`, `base/show.jl:3339-3342`. -/
def m3339 (runtime : SummaryRuntime) (type : TypeObject) (top : Bool) :=
  (if top then "" else "::") ++ "Type{" ++ runtime.renderType type ++ "}"
def P3339 : Prop := ∀ runtime type top, m3339 runtime type top =
  (if top then "" else "::") ++ "Type{" ++ runtime.renderType type ++ "}"
theorem p3339 : P3339 := fun _ _ _ => rfl

/-- `showarg(io::IO, a::Array{Union{}}, toplevel)`, `base/show.jl:3344-3347`. -/
def m3344 (runtime : SummaryRuntime) (array : SummaryValue) (top : Bool) :=
  m3335 runtime array top
def P3344 : Prop := ∀ runtime array top, m3344 runtime array top = m3335 runtime array top
theorem p3344 : P3344 := fun _ _ _ => rfl

/-- `showarg(io::IO, v::SubArray, toplevel)`, `base/show.jl:3350-3357`. -/
def m3350 (runtime : ContainerRuntime) (view : SubArrayValue) (top : Bool) :=
  "view(" ++ runtime.showParent view.parent false ++
    showIndicesBody runtime.summary view.indices ++ ")" ++
    (if top then " with eltype " ++ runtime.summary.renderType view.eltype else "")
def P3350 : Prop := ∀ runtime view,
  m3350 runtime view false = "view(" ++ runtime.showParent view.parent false ++
    showIndicesBody runtime.summary view.indices ++ ")"
theorem p3350 : P3350 := by
  unfold P3350
  intros
  simp [m3350, String.append_assoc]

/-- `showindices(io, ::Slice, inds...)`, `base/show.jl:3358-3359`. -/
def m3358 (runtime : SummaryRuntime) (rest : List AxisModel) :=
  ", :" ++ showIndicesBody runtime rest
def P3358 : Prop := ∀ runtime rest,
  m3358 runtime rest = ", :" ++ showIndicesBody runtime rest
theorem p3358 : P3358 := fun _ _ => rfl

/-- `showindices(io, ind1, inds...)`, `base/show.jl:3360-3361`. -/
def m3360 (runtime : SummaryRuntime) (first : AxisModel) (rest : List AxisModel) :=
  ", " ++ axisText runtime first ++ showIndicesBody runtime rest
def P3360 : Prop := ∀ runtime first rest,
  m3360 runtime first rest = ", " ++ axisText runtime first ++ showIndicesBody runtime rest
theorem p3360 : P3360 := fun _ _ _ => rfl

/-- `showindices(io)`, `base/show.jl:3362-3362`. -/
def m3362 (_io : SummaryRuntime) := ""
def P3362 : Prop := ∀ io, m3362 io = ""
theorem p3362 : P3362 := fun _ => rfl

/-- `showarg(io::IO, r::ReshapedArray, toplevel)`, `base/show.jl:3364-3373`. -/
def m3364 (runtime : ContainerRuntime) (array : ReshapedValue) (top : Bool) :=
  "reshape(" ++ runtime.showParent array.parent false ++
    (if array.dimensions.isEmpty then "" else ", " ++ ", ".intercalate (array.dimensions.map toString)) ++
    ")" ++ if top then " with eltype " ++ runtime.summary.renderType array.eltype else ""
def P3364 : Prop := ∀ runtime array,
  m3364 runtime array false = "reshape(" ++ runtime.showParent array.parent false ++
    (if array.dimensions.isEmpty then "" else ", " ++ ", ".intercalate (array.dimensions.map toString)) ++ ")"
theorem p3364 : P3364 := by
  unfold P3364
  intros
  simp [m3364, String.append_assoc]

/-- `showarg(io::IO, r::NonReshapedReinterpretArray{T}, toplevel) where {T}`, `base/show.jl:3375-3379`. -/
def m3375 (runtime : ContainerRuntime) (array : ReinterpretValue) :=
  "reinterpret(" ++ runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")"
def P3375 : Prop := ∀ runtime array, m3375 runtime array =
  "reinterpret(" ++ runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")"
theorem p3375 : P3375 := fun _ _ => rfl

/-- `showarg(io::IO, r::ReshapedReinterpretArray{T}, toplevel) where {T}`, `base/show.jl:3381-3387`. -/
def m3381 (runtime : ContainerRuntime) (array : ReinterpretValue) (top : Bool) :=
  "reinterpret(reshape, " ++ runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")" ++
    if top then " with eltype " ++ runtime.summary.renderType array.eltype else ""
def P3381 : Prop := ∀ runtime array,
  m3381 runtime array false = "reinterpret(reshape, " ++
    runtime.summary.renderType array.targetType ++ ", " ++
    runtime.showParent array.parent false ++ ")"
theorem p3381 : P3381 := by
  unfold P3381
  intros
  simp [m3381, String.append_assoc]

/-- `show(io::IO, e::Iterators.Enumerate)`, `base/show.jl:3391-3395`. -/
def m3391 (runtime : ContainerRuntime) (wrapper : IteratorWrapperValue) :=
  "enumerate(" ++ runtime.showIterator wrapper.iterator ++ ")"
def P3391 : Prop := ∀ runtime wrapper, m3391 runtime wrapper =
  "enumerate(" ++ runtime.showIterator wrapper.iterator ++ ")"
theorem p3391 : P3391 := fun _ _ => rfl

/-- `show(io::IO, z::Iterators.Zip)`, `base/show.jl:3396-3396`. -/
def m3396 (runtime : DelimArrayRuntime) (items : DelimArrayValue) :=
  m1562 runtime items "zip(" "," ")" false 1 items.slots.length
def P3396 : Prop := ∀ runtime items,
  m3396 runtime items = m1562 runtime items "zip(" "," ")" false 1 items.slots.length
theorem p3396 : P3396 := fun _ _ => rfl

/-- `Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T<:AbstractArray`, `base/show.jl:3399-3401`. -/
def m3399 (runtime : SummaryRuntime) (arrayType : TypeObject) :=
  "pairs(IndexLinear(), ::" ++ runtime.renderType arrayType ++ ")"
def P3399 : Prop := ∀ runtime arrayType, m3399 runtime arrayType =
  "pairs(IndexLinear(), ::" ++ runtime.renderType arrayType ++ ")"
theorem p3399 : P3399 := fun _ _ => rfl

/-- `Base.showarg(io::IO, r::Iterators.Pairs{Symbol, <:Any, Nothing, T}, toplevel) where {T <: NamedTuple}`, `base/show.jl:3403-3405`. -/
def m3403 (_values : List DelimElement) (_toplevel : Bool) := "pairs(::NamedTuple)"
def P3403 : Prop := ∀ values : List DelimElement, ∀ toplevel : Bool,
  m3403 values toplevel = "pairs(::NamedTuple)"
theorem p3403 : P3403 := fun _ _ => rfl

/-- `Base.showarg(io::IO, r::Iterators.Pairs{<:Any, <:Any, I, D}, toplevel) where {D, I}`, `base/show.jl:3407-3409`. -/
def m3407 (runtime : SummaryRuntime) (dictType indexType : TypeObject) :=
  "Iterators.Pairs(::" ++ runtime.renderType dictType ++ ", ::" ++
    runtime.renderType indexType ++ ")"
def P3407 : Prop := ∀ runtime dictType indexType, m3407 runtime dictType indexType =
  "Iterators.Pairs(::" ++ runtime.renderType dictType ++ ", ::" ++
    runtime.renderType indexType ++ ")"
theorem p3407 : P3407 := fun _ _ _ => rfl

/-- `print_bit_chunk(io::IO, c::UInt64, l::Integer = 64)`, `base/show.jl:3415-3423`. -/
def m3415 (io : BitIO) (chunk length : Nat) := printBitChunkBody io chunk length
def P3415 : Prop := ∀ io chunk length, m3415 io chunk length =
  (Containers.printBitChunk chunk length).map fun char => ⟨io, String.singleton char⟩
theorem p3415 : P3415 := fun _ _ _ => rfl

/-- `print_bit_chunk(c::UInt64, l::Integer)`, `base/show.jl:3425-3425`. -/
def m3425 (stdout : BitIO) (chunk length : Nat) := m3415 stdout chunk length
def P3425 : Prop := ∀ stdout chunk length,
  m3425 stdout chunk length = m3415 stdout chunk length
theorem p3425 : P3425 := fun _ _ _ => rfl

/-- `print_bit_chunk(c::UInt64)`, `base/show.jl:3426-3426`. -/
def m3426 (stdout : BitIO) (chunk : Nat) := m3415 stdout chunk 64
def P3426 : Prop := ∀ stdout chunk, m3426 stdout chunk = m3415 stdout chunk 64
theorem p3426 : P3426 := fun _ _ => rfl

/-- `bitshow(io::IO, B::BitArray)`, `base/show.jl:3428-3437`. -/
def m3428 (io : BitIO) (array : BitArrayValue) := bitshowBody io array
def P3428 : Prop := ∀ io array,
  HasResult (m3428 io array) ∧ (array.length = 0 → m3428 io array = [])
theorem p3428 : P3428 := by
  intro io array
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m3428, bitshowBody, h]

/-- `bitshow(B::BitArray)`, `base/show.jl:3438-3438`. -/
def m3438 (stdout : BitIO) (array : BitArrayValue) := m3428 stdout array
def P3438 : Prop := ∀ stdout array, m3438 stdout array = m3428 stdout array
theorem p3438 : P3438 := fun _ _ => rfl

/-- `bitstring(B::BitArray)`, `base/show.jl:3440-3440`. -/
def m3440 (array : BitArrayValue) :=
  String.join ((bitshowBody ⟨0⟩ array).map (·.text))
def P3440 : Prop := ∀ array, m3440 array =
  String.join ((bitshowBody ⟨0⟩ array).map (·.text))
theorem p3440 : P3440 := fun _ => rfl

/-- `show(io::IO, oc::Core.OpaqueClosure)`, `base/show.jl:3443-3448`. -/
def m3443 (runtime : OpaqueRuntime) (closure : OpaqueClosureValue) :=
  showOpaqueBody runtime closure
def P3443 : Prop := ∀ runtime closure, m3443 runtime closure =
  showTupleCallBody runtime.tupleRuntime ⟨0⟩ closure.argumentType false none none false false ++
    "->◌::" ++ runtime.renderResultType closure.resultType
theorem p3443 : P3443 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", oc::Core.OpaqueClosure{A, R}) where {A, R}`, `base/show.jl:3450-3452`. -/
def m3450 (runtime : OpaqueRuntime) (closure : OpaqueClosureValue) :=
  m3443 runtime closure
def P3450 : Prop := ∀ runtime closure, m3450 runtime closure = m3443 runtime closure
theorem p3450 : P3450 := fun _ _ => rfl

/-- `print_partition(io::IO, partition::Core.BindingPartition)`, `base/show.jl:3455-3505`. -/
def m3455 (runtime : PartitionRuntime) (partition : PartitionValue) :=
  printPartitionBody runtime partition
def P3455 : Prop := ∀ runtime partition,
  partition.maxWorld = runtime.maxWorldValue →
  (m3455 runtime partition).contains '∞' = true
theorem p3455 : P3455 := by
  intro runtime partition h
  simp [m3455, printPartitionBody, h]

/-- `show(io::IO, partition::Core.BindingPartition)`, `base/show.jl:3507-3511`. -/
def m3507 (runtime : PartitionRuntime) (partition : PartitionValue) :=
  "BindingPartition(for " ++ runtime.renderGlobalRef (runtime.owner partition) ++ ": " ++
    printPartitionBody runtime partition ++ ")"
def P3507 : Prop := ∀ runtime partition, m3507 runtime partition =
  "BindingPartition(for " ++ runtime.renderGlobalRef (runtime.owner partition) ++ ": " ++
    printPartitionBody runtime partition ++ ")"
theorem p3507 : P3507 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", partition::Core.BindingPartition)`, `base/show.jl:3513-3517`. -/
def m3513 (runtime : PartitionRuntime) (partition : PartitionValue) :=
  "BindingPartition for " ++ runtime.renderGlobalRef (runtime.owner partition) ++
    "\n   " ++ printPartitionBody runtime partition
def P3513 : Prop := ∀ runtime partition, m3513 runtime partition =
  "BindingPartition for " ++ runtime.renderGlobalRef (runtime.owner partition) ++
    "\n   " ++ printPartitionBody runtime partition
theorem p3513 : P3513 := fun _ _ => rfl

/-- `show(io::IO, ::MIME"text/plain", bnd::Core.Binding)`, `base/show.jl:3519-3536`. -/
def m3519 (runtime : PartitionRuntime) (binding : BindingValue) :=
  "Binding " ++ runtime.renderGlobalRef binding.globalRef ++
    if !binding.partitionsDefined then " - No partitions"
    else String.join (bindingPartitionsBody runtime binding.fuel binding.firstPartition)
def P3519 : Prop := ∀ runtime binding,
  HasResult (m3519 runtime binding) ∧
  (binding.partitionsDefined = false →
    m3519 runtime binding = "Binding " ++ runtime.renderGlobalRef binding.globalRef ++
      " - No partitions")
theorem p3519 : P3519 := by
  intro runtime binding
  refine ⟨hasResult _, ?_⟩
  intro h; simp [m3519, h]

/-- `show(io::IO, ii::IncludeInto)`, `base/show.jl:3539-3546`. -/
def m3539 (runtime : IntoRuntime) (value : IntoValue) :=
  showIntoBody runtime value "include"
def P3539 : Prop := ∀ runtime value,
  runtime.getGlobal value.moduleValue "include" = value.id →
    m3539 runtime value = runtime.renderModule value.moduleValue ++ ".include"
theorem p3539 : P3539 := by
  intro runtime value h
  simp [m3539, showIntoBody, h, String.append_assoc]

/-- `show(io::IO, ei::Core.EvalInto)`, `base/show.jl:3548-3555`. -/
def m3548 (runtime : IntoRuntime) (value : IntoValue) :=
  showIntoBody runtime value "eval"
def P3548 : Prop := ∀ runtime value,
  runtime.getGlobal value.moduleValue "eval" = value.id →
    m3548 runtime value = runtime.renderModule value.moduleValue ++ ".eval"
theorem p3548 : P3548 := by
  intro runtime value h
  simp [m3548, showIntoBody, h, String.append_assoc]

def entries : List Entry := [
  entry "showcov-show-l6" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", u::UndefInitializer)" "The source-order model of show(io::IO, ::MIME\"text/plain\", u::UndefInitializer) has a result for every allowed input." ``P6 ``p6,
  entry "showcov-show-l14" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::AbstractRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::AbstractRange) has a result for every allowed input." ``P14 ``p14,
  entry "showcov-show-l16" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::UnitRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::UnitRange) has a result for every allowed input." ``P16 ``p16,
  entry "showcov-show-l23" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::LinRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::LinRange) has a result for every allowed input." ``P23 ``p23,
  entry "showcov-show-l34" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", r::LogRange)" "The source-order model of show(io::IO, ::MIME\"text/plain\", r::LogRange) has a result for every allowed input." ``P34 ``p34,
  entry "showcov-show-l41" "base/show.jl" "_isself(ft::DataType)" "The source-order model of _isself(ft::DataType) has a result for every allowed input." ``P41 ``p41,
  entry "showcov-show-l55" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", f::Function)" "The source-order model of show(io::IO, ::MIME\"text/plain\", f::Function) has a result for every allowed input." ``P55 ``p55,
  entry "showcov-show-l75" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", c::ComposedFunction)" "The source-order model of show(io::IO, ::MIME\"text/plain\", c::ComposedFunction) has a result for every allowed input." ``P75 ``p75,
  entry "showcov-show-l76" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", c::Returns)" "The source-order model of show(io::IO, ::MIME\"text/plain\", c::Returns) has a result for every allowed input." ``P76 ``p76,
  entry "showcov-show-l77" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", s::Splat)" "The source-order model of show(io::IO, ::MIME\"text/plain\", s::Splat) has a result for every allowed input." ``P77 ``p77,
  entry "showcov-show-l85" "base/show.jl" "ncodeunits(c::ANSIDelimiter)" "The source-order model of ncodeunits(c::ANSIDelimiter) has a result for every allowed input." ``P85 ``p85,
  entry "showcov-show-l86" "base/show.jl" "textwidth(::ANSIDelimiter)" "The source-order model of textwidth(::ANSIDelimiter) has a result for every allowed input." ``P86 ``p86,
  entry "showcov-show-l92" "base/show.jl" "ANSIIterator(s::AbstractString)" "The source-order model of ANSIIterator(s::AbstractString) has a result for every allowed input." ``P92 ``p92,
  entry "showcov-show-l94" "base/show.jl" "IteratorSize(::Type{<:ANSIIterator})" "The source-order model of IteratorSize(::Type{<:ANSIIterator}) has a result for every allowed input." ``P94 ``p94,
  entry "showcov-show-l95" "base/show.jl" "eltype(::Type{<:ANSIIterator})" "The source-order model of eltype(::Type{<:ANSIIterator}) has a result for every allowed input." ``P95 ``p95,
  entry "showcov-show-l96" "base/show.jl" "iterate(I::ANSIIterator, (i, m_st)=(1, iterate(I.captures)))" "The source-order model of iterate(I::ANSIIterator, (i, m_st)=(1, iterate(I.captures))) has a result for every allowed input." ``P96 ``p96,
  entry "showcov-show-l102" "base/show.jl" "textwidth(I::ANSIIterator)" "The source-order model of textwidth(I::ANSIIterator) has a result for every allowed input." ``P102 ``p102,
  entry "showcov-show-l104" "base/show.jl" "_truncate_at_width_or_chars(ignore_ANSI::Bool, str::AbstractString, width::Int, rpad::Bool=false, chars=\"\\r\\n\", truncmark=\"…\")" "The source-order model of _truncate_at_width_or_chars(ignore_ANSI::Bool, str::AbstractString, width::Int, rpad::Bool=false, chars=\"\\r\\n\", truncmark=\"…\") has a result for every allowed input." ``P104 ``p104,
  entry "showcov-show-l137" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", iter::Union{KeySet,ValueIterator})" "The source-order model of show(io::IO, ::MIME\"text/plain\", iter::Union{KeySet,ValueIterator}) has a result for every allowed input." ``P137 ``p137,
  entry "showcov-show-l168" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", t::AbstractDict{K,V}) where {K,V}" "The source-order model of show(io::IO, ::MIME\"text/plain\", t::AbstractDict{K,V}) where {K,V} has a result for every allowed input." ``P168 ``p168,
  entry "showcov-show-l235" "base/show.jl" "summary(io::IO, t::AbstractSet)" "The source-order model of summary(io::IO, t::AbstractSet) has a result for every allowed input." ``P235 ``p235,
  entry "showcov-show-l241" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", t::AbstractSet{T}) where T" "The source-order model of show(io::IO, ::MIME\"text/plain\", t::AbstractSet{T}) where T has a result for every allowed input." ``P241 ``p241,
  entry "showcov-show-l278" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", opt::JLOptions)" "The source-order model of show(io::IO, ::MIME\"text/plain\", opt::JLOptions) has a result for every allowed input." ``P278 ``p278,
  entry "showcov-show-l294" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", t::Task)" "The source-order model of show(io::IO, ::MIME\"text/plain\", t::Task) has a result for every allowed input." ``P294 ``p294,
  entry "showcov-show-l304" "base/show.jl" "show(io::IO, src::Core.CancellationTokenSource)" "The source-order model of show(io::IO, src::Core.CancellationTokenSource) has a result for every allowed input." ``P304 ``p304,
  entry "showcov-show-l322" "base/show.jl" "print(io::IO, s::Symbol)" "The source-order model of print(io::IO, s::Symbol) has a result for every allowed input." ``P322 ``p322,
  entry "showcov-show-l336" "base/show.jl" "IOContext{IO_t}(io::IO_t, dict::ImmutableDict{Symbol, Any}) where IO_t<:IO" "The source-order model of IOContext{IO_t}(io::IO_t, dict::ImmutableDict{Symbol, Any}) where IO_t<:IO has a result for every allowed input." ``P336 ``p336,
  entry "showcov-show-l343" "base/show.jl" "ioproperties(io::IO)" "The source-order model of ioproperties(io::IO) has a result for every allowed input." ``P343 ``p343,
  entry "showcov-show-l344" "base/show.jl" "ioproperties(io::IOContext)" "The source-order model of ioproperties(io::IOContext) has a result for every allowed input." ``P344 ``p344,
  entry "showcov-show-l346" "base/show.jl" "unwrapcontext(io::IO)" "The source-order model of unwrapcontext(io::IO) has a result for every allowed input." ``P346 ``p346,
  entry "showcov-show-l347" "base/show.jl" "unwrapcontext(io::IOContext)" "The source-order model of unwrapcontext(io::IOContext) has a result for every allowed input." ``P347 ``p347,
  entry "showcov-show-l349" "base/show.jl" "IOContext(io::IO, dict::ImmutableDict{Symbol, Any})" "The source-order model of IOContext(io::IO, dict::ImmutableDict{Symbol, Any}) has a result for every allowed input." ``P349 ``p349,
  entry "showcov-show-l353" "base/show.jl" "IOContext(io::IOContext, dict::ImmutableDict{Symbol, Any})" "The source-order model of IOContext(io::IOContext, dict::ImmutableDict{Symbol, Any}) has a result for every allowed input." ``P353 ``p353,
  entry "showcov-show-l358" "base/show.jl" "convert(::Type{IOContext}, io::IOContext)" "The source-order model of convert(::Type{IOContext}, io::IOContext) has a result for every allowed input." ``P358 ``p358,
  entry "showcov-show-l359" "base/show.jl" "convert(::Type{IOContext}, io::IO)" "The source-order model of convert(::Type{IOContext}, io::IO) has a result for every allowed input." ``P359 ``p359,
  entry "showcov-show-l360" "base/show.jl" "convert(::Type{IOContext{IO_t}}, io::IOContext{IO_t}) where {IO_t}" "The source-order model of convert(::Type{IOContext{IO_t}}, io::IOContext{IO_t}) where {IO_t} has a result for every allowed input." ``P360 ``p360,
  entry "showcov-show-l361" "base/show.jl" "convert(::Type{IOContext{IO_t}}, io::IO) where {IO_t}" "The source-order model of convert(::Type{IOContext{IO_t}}, io::IO) where {IO_t} has a result for every allowed input." ``P361 ``p361,
  entry "showcov-show-l363" "base/show.jl" "IOContext(io::IO)" "The source-order model of IOContext(io::IO) has a result for every allowed input." ``P363 ``p363,
  entry "showcov-show-l364" "base/show.jl" "IOContext{IO_t}(io::IO) where {IO_t}" "The source-order model of IOContext{IO_t}(io::IO) where {IO_t} has a result for every allowed input." ``P364 ``p364,
  entry "showcov-show-l366" "base/show.jl" "IOContext(io::IO, KV::Pair)" "The source-order model of IOContext(io::IO, KV::Pair) has a result for every allowed input." ``P366 ``p366,
  entry "showcov-show-l381" "base/show.jl" "IOContext(io::IO, context::IO)" "The source-order model of IOContext(io::IO, context::IO) has a result for every allowed input." ``P381 ``p381,
  entry "showcov-show-l456" "base/show.jl" "IOContext(io::IO, KV::Pair, KVs::Pair...)" "The source-order model of IOContext(io::IO, KV::Pair, KVs::Pair...) has a result for every allowed input." ``P456 ``p456,
  entry "showcov-show-l458" "base/show.jl" "show(io::IO, ctx::IOContext)" "The source-order model of show(io::IO, ctx::IOContext) has a result for every allowed input." ``P458 ``p458,
  entry "showcov-show-l460" "base/show.jl" "pipe_reader(io::IOContext)" "The source-order model of pipe_reader(io::IOContext) has a result for every allowed input." ``P460 ``p460,
  entry "showcov-show-l461" "base/show.jl" "pipe_writer(io::IOContext)" "The source-order model of pipe_writer(io::IOContext) has a result for every allowed input." ``P461 ``p461,
  entry "showcov-show-l462" "base/show.jl" "lock(io::IOContext)" "The source-order model of lock(io::IOContext) has a result for every allowed input." ``P462 ``p462,
  entry "showcov-show-l463" "base/show.jl" "unlock(io::IOContext)" "The source-order model of unlock(io::IOContext) has a result for every allowed input." ``P463 ``p463,
  entry "showcov-show-l465" "base/show.jl" "in(key_value::Pair, io::IOContext)" "The source-order model of in(key_value::Pair, io::IOContext) has a result for every allowed input." ``P465 ``p465,
  entry "showcov-show-l466" "base/show.jl" "in(key_value::Pair, io::IO)" "The source-order model of in(key_value::Pair, io::IO) has a result for every allowed input." ``P466 ``p466,
  entry "showcov-show-l467" "base/show.jl" "haskey(io::IOContext, key)" "The source-order model of haskey(io::IOContext, key) has a result for every allowed input." ``P467 ``p467,
  entry "showcov-show-l468" "base/show.jl" "haskey(io::IO, key)" "The source-order model of haskey(io::IO, key) has a result for every allowed input." ``P468 ``p468,
  entry "showcov-show-l469" "base/show.jl" "getindex(io::IOContext, key)" "The source-order model of getindex(io::IOContext, key) has a result for every allowed input." ``P469 ``p469,
  entry "showcov-show-l470" "base/show.jl" "getindex(io::IO, key)" "The source-order model of getindex(io::IO, key) has a result for every allowed input." ``P470 ``p470,
  entry "showcov-show-l471" "base/show.jl" "get(io::IOContext, key, default)" "The source-order model of get(io::IOContext, key, default) has a result for every allowed input." ``P471 ``p471,
  entry "showcov-show-l472" "base/show.jl" "get(io::IO, key, default)" "The source-order model of get(io::IO, key, default) has a result for every allowed input." ``P472 ``p472,
  entry "showcov-show-l473" "base/show.jl" "keys(io::IOContext)" "The source-order model of keys(io::IOContext) has a result for every allowed input." ``P473 ``p473,
  entry "showcov-show-l474" "base/show.jl" "keys(io::IO)" "The source-order model of keys(io::IO) has a result for every allowed input." ``P474 ``p474,
  entry "showcov-show-l476" "base/show.jl" "displaysize(io::IOContext)" "The source-order model of displaysize(io::IOContext) has a result for every allowed input." ``P476 ``p476,
  entry "showcov-show-l478" "base/show.jl" "show_circular(io::IO, @nospecialize(x))" "The source-order model of show_circular(io::IO, @nospecialize(x)) has a result for every allowed input." ``P478 ``p478,
  entry "showcov-show-l479" "base/show.jl" "show_circular(io::IOContext, @nospecialize(x))" "The source-order model of show_circular(io::IOContext, @nospecialize(x)) has a result for every allowed input." ``P479 ``p479,
  entry "showcov-show-l520" "base/show.jl" "show(io::IO, @nospecialize(x))" "The source-order model of show(io::IO, @nospecialize(x)) has a result for every allowed input." ``P520 ``p520,
  entry "showcov-show-l522" "base/show.jl" "show(x)" "The source-order model of show(x) has a result for every allowed input." ``P522 ``p522,
  entry "showcov-show-l525" "base/show.jl" "show_default(io::IO, @nospecialize(x))" "The source-order model of show_default(io::IO, @nospecialize(x)) has a result for every allowed input." ``P525 ``p525,
  entry "showcov-show-l527" "base/show.jl" "_show_default(io::IO, @nospecialize(x))" "The source-order model of _show_default(io::IO, @nospecialize(x)) has a result for every allowed input." ``P527 ``p527,
  entry "showcov-show-l570" "base/show.jl" "active_module()" "The source-order model of active_module() has a result for every allowed input." ``P570 ``p570,
  entry "showcov-show-l583" "base/show.jl" "show_function(io::IO, f::Function, compact::Bool, fallback::Function)" "The source-order model of show_function(io::IO, f::Function, compact::Bool, fallback::Function) has a result for every allowed input." ``P583 ``p583,
  entry "showcov-show-l603" "base/show.jl" "show(io::IO, f::Function)" "The source-order model of show(io::IO, f::Function) has a result for every allowed input." ``P603 ``p603,
  entry "showcov-show-l604" "base/show.jl" "print(io::IO, f::Function)" "The source-order model of print(io::IO, f::Function) has a result for every allowed input." ``P604 ``p604,
  entry "showcov-show-l606" "base/show.jl" "show(io::IO, f::Core.IntrinsicFunction)" "The source-order model of show(io::IO, f::Core.IntrinsicFunction) has a result for every allowed input." ``P606 ``p606,
  entry "showcov-show-l613" "base/show.jl" "print(io::IO, f::Core.IntrinsicFunction)" "The source-order model of print(io::IO, f::Core.IntrinsicFunction) has a result for every allowed input." ``P613 ``p613,
  entry "showcov-show-l615" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", ::Core.TypeofBottom)" "The source-order model of show(io::IO, ::MIME\"text/plain\", ::Core.TypeofBottom) has a result for every allowed input." ``P615 ``p615,
  entry "showcov-show-l617" "base/show.jl" "print_without_params(@nospecialize(x))" "The source-order model of print_without_params(@nospecialize(x)) has a result for every allowed input." ``P617 ``p617,
  entry "showcov-show-l622" "base/show.jl" "io_has_tvar_name(io::IOContext, name::Symbol, @nospecialize(x))" "The source-order model of io_has_tvar_name(io::IOContext, name::Symbol, @nospecialize(x)) has a result for every allowed input." ``P622 ``p622,
  entry "showcov-show-l630" "base/show.jl" "io_has_tvar_name(io::IO, name::Symbol, @nospecialize(x))" "The source-order model of io_has_tvar_name(io::IO, name::Symbol, @nospecialize(x)) has a result for every allowed input." ``P630 ``p630,
  entry "showcov-show-l632" "base/show.jl" "modulesof!(s::Set{Module}, x::TypeVar)" "The source-order model of modulesof!(s::Set{Module}, x::TypeVar) has a result for every allowed input." ``P632 ``p632,
  entry "showcov-show-l633" "base/show.jl" "modulesof!(s::Set{Module}, x::TypeEq)" "The source-order model of modulesof!(s::Set{Module}, x::TypeEq) has a result for every allowed input." ``P633 ``p633,
  entry "showcov-show-l638" "base/show.jl" "modulesof!(s::Set{Module}, x::Core.TypeEgal)" "The source-order model of modulesof!(s::Set{Module}, x::Core.TypeEgal) has a result for every allowed input." ``P638 ``p638,
  entry "showcov-show-l639" "base/show.jl" "modulesof!(s::Set{Module}, x::Type)" "The source-order model of modulesof!(s::Set{Module}, x::Type) has a result for every allowed input." ``P639 ``p639,
  entry "showcov-show-l654" "base/show.jl" "has_other_free_typevars(@nospecialize(x), free_before)" "The source-order model of has_other_free_typevars(@nospecialize(x), free_before) has a result for every allowed input." ``P654 ``p654,
  entry "showcov-show-l674" "base/show.jl" "unbounded_typealias(@nospecialize(alias))" "The source-order model of unbounded_typealias(@nospecialize(alias)) has a result for every allowed input." ``P674 ``p674,
  entry "showcov-show-l692" "base/show.jl" "reapply_unionall_env(io::Union{IO,Nothing}, @nospecialize(x))" "The source-order model of reapply_unionall_env(io::Union{IO,Nothing}, @nospecialize(x)) has a result for every allowed input." ``P692 ``p692,
  entry "showcov-show-l703" "base/show.jl" "make_typealias(@nospecialize(x::Type), io::Union{IO,Nothing}=nothing)" "The source-order model of make_typealias(@nospecialize(x::Type), io::Union{IO,Nothing}=nothing) has a result for every allowed input." ``P703 ``p703,
  entry "showcov-show-l769" "base/show.jl" "isgensym(s::Symbol)" "The source-order model of isgensym(s::Symbol) has a result for every allowed input." ``P769 ``p769,
  entry "showcov-show-l771" "base/show.jl" "show_can_elide(p::TypeVar, wheres::Vector, elide::Int, env::SimpleVector, skip::Int)" "The source-order model of show_can_elide(p::TypeVar, wheres::Vector, elide::Int, env::SimpleVector, skip::Int) has a result for every allowed input." ``P771 ``p771,
  entry "showcov-show-l786" "base/show.jl" "show_typeparams(io::IO, env::SimpleVector, orig::SimpleVector, wheres::Vector)" "The source-order model of show_typeparams(io::IO, env::SimpleVector, orig::SimpleVector, wheres::Vector) has a result for every allowed input." ``P786 ``p786,
  entry "showcov-show-l789" "base/show.jl" "egal_var(p::TypeVar, @nospecialize o)" "The source-order model of egal_var(p::TypeVar, @nospecialize o) has a result for every allowed input." ``P789 ``p789,
  entry "showcov-show-l832" "base/show.jl" "show_typealias_name(io::IO, name::GlobalRef)" "The source-order model of show_typealias_name(io::IO, name::GlobalRef) has a result for every allowed input." ``P832 ``p832,
  entry "showcov-show-l847" "base/show.jl" "show_typealias(io::IO, name::GlobalRef, env::SimpleVector, wheres::Vector)" "The source-order model of show_typealias(io::IO, name::GlobalRef, env::SimpleVector, wheres::Vector) has a result for every allowed input." ``P847 ``p847,
  entry "showcov-show-l864" "base/show.jl" "make_wheres(io::IO, env::SimpleVector, @nospecialize(x::Type))" "The source-order model of make_wheres(io::IO, env::SimpleVector, @nospecialize(x::Type)) has a result for every allowed input." ``P864 ``p864,
  entry "showcov-show-l894" "base/show.jl" "show_wheres(io::IO, wheres::Vector{TypeVar})" "The source-order model of show_wheres(io::IO, wheres::Vector{TypeVar}) has a result for every allowed input." ``P894 ``p894,
  entry "showcov-show-l908" "base/show.jl" "show_typealias(io::IO, @nospecialize(x::Type))" "The source-order model of show_typealias(io::IO, @nospecialize(x::Type)) has a result for every allowed input." ``P908 ``p908,
  entry "showcov-show-l917" "base/show.jl" "make_typealiases(@nospecialize(x::Type))" "The source-order model of make_typealiases(@nospecialize(x::Type)) has a result for every allowed input." ``P917 ``p917,
  entry "showcov-show-l1002" "base/show.jl" "show_unionaliases(io::IO, x::Union)" "The source-order model of show_unionaliases(io::IO, x::Union) has a result for every allowed input." ``P1002 ``p1002,
  entry "showcov-show-l1046" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", @nospecialize(x::Type))" "The source-order model of show(io::IO, ::MIME\"text/plain\", @nospecialize(x::Type)) has a result for every allowed input." ``P1046 ``p1046,
  entry "showcov-show-l1071" "base/show.jl" "show_typeegal(io::IO, @nospecialize(x::Core.TypeEgal))" "The source-order model of show_typeegal(io::IO, @nospecialize(x::Core.TypeEgal)) has a result for every allowed input." ``P1071 ``p1071,
  entry "showcov-show-l1076" "base/show.jl" "show(io::IO, @nospecialize(x::Core.AnyType))" "The source-order model of show(io::IO, @nospecialize(x::Core.AnyType)) has a result for every allowed input." ``P1076 ``p1076,
  entry "showcov-show-l1091" "base/show.jl" "show_typeeq(io::IO, @nospecialize(x::TypeEq))" "The source-order model of show_typeeq(io::IO, @nospecialize(x::TypeEq)) has a result for every allowed input." ``P1091 ``p1091,
  entry "showcov-show-l1096" "base/show.jl" "_show_type(io::IO, @nospecialize(x::Type))" "The source-order model of _show_type(io::IO, @nospecialize(x::Type)) has a result for every allowed input." ``P1096 ``p1096,
  entry "showcov-show-l1159" "base/show.jl" "isvisible(sym::Symbol, parent::Module, from::Module)" "The source-order model of isvisible(sym::Symbol, parent::Module, from::Module) has a result for every allowed input." ``P1159 ``p1159,
  entry "showcov-show-l1179" "base/show.jl" "is_global_function(tn::Core.TypeName, globname::Union{Symbol,Nothing})" "The source-order model of is_global_function(tn::Core.TypeName, globname::Union{Symbol,Nothing}) has a result for every allowed input." ``P1179 ``p1179,
  entry "showcov-show-l1191" "base/show.jl" "check_world_bounded(tn::Core.TypeName)" "The source-order model of check_world_bounded(tn::Core.TypeName) has a result for every allowed input." ``P1191 ``p1191,
  entry "showcov-show-l1211" "base/show.jl" "show_type_name(io::IO, tn::Core.TypeName)" "The source-order model of show_type_name(io::IO, tn::Core.TypeName) has a result for every allowed input." ``P1211 ``p1211,
  entry "showcov-show-l1248" "base/show.jl" "maybe_kws_nt(x::DataType)" "The source-order model of maybe_kws_nt(x::DataType) has a result for every allowed input." ``P1248 ``p1248,
  entry "showcov-show-l1266" "base/show.jl" "show_datatype(io::IO, x::DataType, wheres::Vector{TypeVar}=TypeVar[])" "The source-order model of show_datatype(io::IO, x::DataType, wheres::Vector{TypeVar}=TypeVar[]) has a result for every allowed input." ``P1266 ``p1266,
  entry "showcov-show-l1362" "base/show.jl" "show_at_namedtuple(io::IO, syms::Tuple, types::DataType)" "The source-order model of show_at_namedtuple(io::IO, syms::Tuple, types::DataType) has a result for every allowed input." ``P1362 ``p1362,
  entry "showcov-show-l1378" "base/show.jl" "show_supertypes(io::IO, typ::DataType)" "The source-order model of show_supertypes(io::IO, typ::DataType) has a result for every allowed input." ``P1378 ``p1378,
  entry "showcov-show-l1386" "base/show.jl" "show_supertypes(typ::DataType)" "The source-order model of show_supertypes(typ::DataType) has a result for every allowed input." ``P1386 ``p1386,
  entry "showcov-show-l1406" "base/show.jl" "show(exs...)" "The source-order model of show(exs...) has a result for every allowed input." ``P1406 ``p1406,
  entry "showcov-show-l1416" "base/show.jl" "show(io::IO, tn::Core.TypeName)" "The source-order model of show(io::IO, tn::Core.TypeName) has a result for every allowed input." ``P1416 ``p1416,
  entry "showcov-show-l1422" "base/show.jl" "nonnothing_nonmissing_typeinfo(io::IO)" "The source-order model of nonnothing_nonmissing_typeinfo(io::IO) has a result for every allowed input." ``P1422 ``p1422,
  entry "showcov-show-l1423" "base/show.jl" "show(io::IO, b::Bool)" "The source-order model of show(io::IO, b::Bool) has a result for every allowed input." ``P1423 ``p1423,
  entry "showcov-show-l1424" "base/show.jl" "show(io::IO, ::Nothing)" "The source-order model of show(io::IO, ::Nothing) has a result for every allowed input." ``P1424 ``p1424,
  entry "showcov-show-l1425" "base/show.jl" "show(io::IO, n::Signed)" "The source-order model of show(io::IO, n::Signed) has a result for every allowed input." ``P1425 ``p1425,
  entry "showcov-show-l1426" "base/show.jl" "show(io::IO, n::Unsigned)" "The source-order model of show(io::IO, n::Unsigned) has a result for every allowed input." ``P1426 ``p1426,
  entry "showcov-show-l1437" "base/show.jl" "print(io::IO, n::Unsigned)" "The source-order model of print(io::IO, n::Unsigned) has a result for every allowed input." ``P1437 ``p1437,
  entry "showcov-show-l1439" "base/show.jl" "has_tight_type(p::Pair)" "The source-order model of has_tight_type(p::Pair) has a result for every allowed input." ``P1439 ``p1439,
  entry "showcov-show-l1443" "base/show.jl" "isdelimited(io::IO, x)" "The source-order model of isdelimited(io::IO, x) has a result for every allowed input." ``P1443 ``p1443,
  entry "showcov-show-l1444" "base/show.jl" "isdelimited(io::IO, x::Function)" "The source-order model of isdelimited(io::IO, x::Function) has a result for every allowed input." ``P1444 ``p1444,
  entry "showcov-show-l1448" "base/show.jl" "isdelimited(io::IO, p::Pair)" "The source-order model of isdelimited(io::IO, p::Pair) has a result for every allowed input." ``P1448 ``p1448,
  entry "showcov-show-l1450" "base/show.jl" "gettypeinfos(io::IO, p::Pair)" "The source-order model of gettypeinfos(io::IO, p::Pair) has a result for every allowed input." ``P1450 ``p1450,
  entry "showcov-show-l1457" "base/show.jl" "show(io::IO, p::Pair)" "The source-order model of show(io::IO, p::Pair) has a result for every allowed input." ``P1457 ``p1457,
  entry "showcov-show-l1469" "base/show.jl" "show_pairtyped(io::IO, p::Pair{K,V}) where {K,V}" "The source-order model of show_pairtyped(io::IO, p::Pair{K,V}) where {K,V} has a result for every allowed input." ``P1469 ``p1469,
  entry "showcov-show-l1474" "base/show.jl" "show(io::IO, m::Module)" "The source-order model of show(io::IO, m::Module) has a result for every allowed input." ``P1474 ``p1474,
  entry "showcov-show-l1484" "base/show.jl" "print_fullname(io::IO, m::Module)" "The source-order model of print_fullname(io::IO, m::Module) has a result for every allowed input." ``P1484 ``p1484,
  entry "showcov-show-l1495" "base/show.jl" "sourceinfo_slotnames(src::CodeInfo)" "The source-order model of sourceinfo_slotnames(src::CodeInfo) has a result for every allowed input." ``P1495 ``p1495,
  entry "showcov-show-l1496" "base/show.jl" "sourceinfo_slotnames(slotnames::Vector{Symbol})" "The source-order model of sourceinfo_slotnames(slotnames::Vector{Symbol}) has a result for every allowed input." ``P1496 ``p1496,
  entry "showcov-show-l1518" "base/show.jl" "show(io::IO, mi::Core.MethodInstance)" "The source-order model of show(io::IO, mi::Core.MethodInstance) has a result for every allowed input." ``P1518 ``p1518,
  entry "showcov-show-l1519" "base/show.jl" "show(io::IO, codeinst::Core.CodeInstance)" "The source-order model of show(io::IO, codeinst::Core.CodeInstance) has a result for every allowed input." ``P1519 ``p1519,
  entry "showcov-show-l1533" "base/show.jl" "show_mi(io::IO, mi::Core.MethodInstance, from_stackframe::Bool=false)" "The source-order model of show_mi(io::IO, mi::Core.MethodInstance, from_stackframe::Bool=false) has a result for every allowed input." ``P1533 ``p1533,
  entry "showcov-show-l1562" "base/show.jl" "show_delim_array(io::IO, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1=first(LinearIndices(itr)), l=last(LinearIndices(itr)))" "The source-order model of show_delim_array(io::IO, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1=first(LinearIndices(itr)), l=last(LinearIndices(itr))) has a result for every allowed input." ``P1562 ``p1562,
  entry "showcov-show-l1591" "base/show.jl" "show_delim_array(io::IO, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int))" "The source-order model of show_delim_array(io::IO, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int)) has a result for every allowed input." ``P1591 ``p1591,
  entry "showcov-show-l1625" "base/show.jl" "show(io::IO, t::Tuple)" "The source-order model of show(io::IO, t::Tuple) has a result for every allowed input." ``P1625 ``p1625,
  entry "showcov-show-l1626" "base/show.jl" "show(io::IO, v::SimpleVector)" "The source-order model of show(io::IO, v::SimpleVector) has a result for every allowed input." ``P1626 ``p1626,
  entry "showcov-show-l1628" "base/show.jl" "show(io::IO, s::Symbol)" "The source-order model of show(io::IO, s::Symbol) has a result for every allowed input." ``P1628 ``p1628,
  entry "showcov-show-l1666" "base/show.jl" "print( io::IO, ex::ExprNode)" "The source-order model of print( io::IO, ex::ExprNode) has a result for every allowed input." ``P1666 ``p1666,
  entry "showcov-show-l1667" "base/show.jl" "show( io::IO, ex::ExprNode)" "The source-order model of show( io::IO, ex::ExprNode) has a result for every allowed input." ``P1667 ``p1667,
  entry "showcov-show-l1668" "base/show.jl" "show_unquoted(io::IO, ex)" "The source-order model of show_unquoted(io::IO, ex) has a result for every allowed input." ``P1668 ``p1668,
  entry "showcov-show-l1669" "base/show.jl" "show_unquoted(io::IO, ex, indent::Int)" "The source-order model of show_unquoted(io::IO, ex, indent::Int) has a result for every allowed input." ``P1669 ``p1669,
  entry "showcov-show-l1670" "base/show.jl" "show_unquoted(io::IO, ex, ::Int,::Int)" "The source-order model of show_unquoted(io::IO, ex, ::Int,::Int) has a result for every allowed input." ``P1670 ``p1670,
  entry "showcov-show-l1671" "base/show.jl" "show_unquoted(io::IO, ex, indent::Int, prec::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex, indent::Int, prec::Int, ::Int) has a result for every allowed input." ``P1671 ``p1671,
  entry "showcov-show-l1713" "base/show.jl" "operator_precedence(s::Symbol)" "The source-order model of operator_precedence(s::Symbol) has a result for every allowed input." ``P1713 ``p1713,
  entry "showcov-show-l1714" "base/show.jl" "operator_precedence(x::Any)" "The source-order model of operator_precedence(x::Any) has a result for every allowed input." ``P1714 ``p1714,
  entry "showcov-show-l1739" "base/show.jl" "operator_associativity(s::Symbol)" "The source-order model of operator_associativity(s::Symbol) has a result for every allowed input." ``P1739 ``p1739,
  entry "showcov-show-l1750" "base/show.jl" "is_quoted(ex)" "The source-order model of is_quoted(ex) has a result for every allowed input." ``P1750 ``p1750,
  entry "showcov-show-l1751" "base/show.jl" "is_quoted(ex::QuoteNode)" "The source-order model of is_quoted(ex::QuoteNode) has a result for every allowed input." ``P1751 ``p1751,
  entry "showcov-show-l1752" "base/show.jl" "is_quoted(ex::Expr)" "The source-order model of is_quoted(ex::Expr) has a result for every allowed input." ``P1752 ``p1752,
  entry "showcov-show-l1754" "base/show.jl" "unquoted(ex::QuoteNode)" "The source-order model of unquoted(ex::QuoteNode) has a result for every allowed input." ``P1754 ``p1754,
  entry "showcov-show-l1755" "base/show.jl" "unquoted(ex::Expr)" "The source-order model of unquoted(ex::Expr) has a result for every allowed input." ``P1755 ``p1755,
  entry "showcov-show-l1762" "base/show.jl" "emphasize(io, str::AbstractString, col = Base.error_color())" "The source-order model of emphasize(io, str::AbstractString, col = Base.error_color()) has a result for every allowed input." ``P1762 ``p1762,
  entry "showcov-show-l1766" "base/show.jl" "show_linenumber(io::IO, line)" "The source-order model of show_linenumber(io::IO, line) has a result for every allowed input." ``P1766 ``p1766,
  entry "showcov-show-l1767" "base/show.jl" "show_linenumber(io::IO, line, file)" "The source-order model of show_linenumber(io::IO, line, file) has a result for every allowed input." ``P1767 ``p1767,
  entry "showcov-show-l1768" "base/show.jl" "show_linenumber(io::IO, line, file::Nothing)" "The source-order model of show_linenumber(io::IO, line, file::Nothing) has a result for every allowed input." ``P1768 ``p1768,
  entry "showcov-show-l1771" "base/show.jl" "show_block(io::IO, head, args::Vector, body, indent::Int, quote_level::Int)" "The source-order model of show_block(io::IO, head, args::Vector, body, indent::Int, quote_level::Int) has a result for every allowed input." ``P1771 ``p1771,
  entry "showcov-show-l1790" "base/show.jl" "show_block(io::IO,head, block,i::Int, quote_level::Int)" "The source-order model of show_block(io::IO,head, block,i::Int, quote_level::Int) has a result for every allowed input." ``P1790 ``p1790,
  entry "showcov-show-l1791" "base/show.jl" "show_block(io::IO, head, arg, block, i::Int, quote_level::Int)" "The source-order model of show_block(io::IO, head, arg, block, i::Int, quote_level::Int) has a result for every allowed input." ``P1791 ``p1791,
  entry "showcov-show-l1800" "base/show.jl" "show_list(io::IO, items, sep, indent::Int, prec::Int=0, quote_level::Int=0, enclose_operators::Bool=false, kw::Bool=false)" "The source-order model of show_list(io::IO, items, sep, indent::Int, prec::Int=0, quote_level::Int=0, enclose_operators::Bool=false, kw::Bool=false) has a result for every allowed input." ``P1800 ``p1800,
  entry "showcov-show-l1828" "base/show.jl" "show_enclosed_list(io::IO, op, items, sep, cl, indent, prec=0, quote_level=0, encl_ops=false, kw::Bool=false)" "The source-order model of show_enclosed_list(io::IO, op, items, sep, cl, indent, prec=0, quote_level=0, encl_ops=false, kw::Bool=false) has a result for every allowed input." ``P1828 ``p1828,
  entry "showcov-show-l1837" "base/show.jl" "show_call(io::IO, head, func, func_args, indent, quote_level, kw::Bool)" "The source-order model of show_call(io::IO, head, func, func_args, indent, quote_level, kw::Bool) has a result for every allowed input." ``P1837 ``p1837,
  entry "showcov-show-l1867" "base/show.jl" "show_sym(io::IO, sym::Symbol; allow_macroname=false)" "The source-order model of show_sym(io::IO, sym::Symbol; allow_macroname=false) has a result for every allowed input." ``P1867 ``p1867,
  entry "showcov-show-l1880" "base/show.jl" "show_unquoted(io::IO, val::SSAValue, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, val::SSAValue, ::Int, ::Int) has a result for every allowed input." ``P1880 ``p1880,
  entry "showcov-show-l1895" "base/show.jl" "show_unquoted(io::IO, sym::Symbol, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, sym::Symbol, ::Int, ::Int) has a result for every allowed input." ``P1895 ``p1895,
  entry "showcov-show-l1896" "base/show.jl" "show_unquoted(io::IO, ex::LineNumberNode, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::LineNumberNode, ::Int, ::Int) has a result for every allowed input." ``P1896 ``p1896,
  entry "showcov-show-l1897" "base/show.jl" "show_unquoted(io::IO, ex::GotoNode, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::GotoNode, ::Int, ::Int) has a result for every allowed input." ``P1897 ``p1897,
  entry "showcov-show-l1898" "base/show.jl" "show_unquoted(io::IO, ex::GlobalRef, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::GlobalRef, ::Int, ::Int) has a result for every allowed input." ``P1898 ``p1898,
  entry "showcov-show-l1899" "base/show.jl" "show_unquoted(io::IO, bpart::Core.BindingPartition, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, bpart::Core.BindingPartition, ::Int, ::Int) has a result for every allowed input." ``P1899 ``p1899,
  entry "showcov-show-l1902" "base/show.jl" "show_globalref(io::IO, ex::GlobalRef; allow_macroname=false)" "The source-order model of show_globalref(io::IO, ex::GlobalRef; allow_macroname=false) has a result for every allowed input." ``P1902 ``p1902,
  entry "showcov-show-l1914" "base/show.jl" "show_unquoted(io::IO, ex::SlotNumber, ::Int, ::Int)" "The source-order model of show_unquoted(io::IO, ex::SlotNumber, ::Int, ::Int) has a result for every allowed input." ``P1914 ``p1914,
  entry "showcov-show-l1924" "base/show.jl" "show_unquoted(io::IO, ex::QuoteNode, indent::Int, _prec::Int)" "The source-order model of show_unquoted(io::IO, ex::QuoteNode, indent::Int, _prec::Int) has a result for every allowed input." ``P1924 ``p1924,
  entry "showcov-show-l1937" "base/show.jl" "show_unquoted_quote_expr(io::IO, @nospecialize(value), indent::Int, quote_level::Int)" "The source-order model of show_unquoted_quote_expr(io::IO, @nospecialize(value), indent::Int, quote_level::Int) has a result for every allowed input." ``P1937 ``p1937,
  entry "showcov-show-l1962" "base/show.jl" "show_generator(io, ex::Expr, indent, quote_level)" "The source-order model of show_generator(io, ex::Expr, indent, quote_level) has a result for every allowed input." ``P1962 ``p1962,
  entry "showcov-show-l1983" "base/show.jl" "valid_import_path(@nospecialize(ex), allow_as = true)" "The source-order model of valid_import_path(@nospecialize(ex), allow_as = true) has a result for every allowed input." ``P1983 ``p1983,
  entry "showcov-show-l1990" "base/show.jl" "show_import_path(io::IO, ex, quote_level)" "The source-order model of show_import_path(io::IO, ex, quote_level) has a result for every allowed input." ``P1990 ``p1990,
  entry "showcov-show-l2023" "base/show.jl" "allow_macroname(ex)" "The source-order model of allow_macroname(ex) has a result for every allowed input." ``P2023 ``p2023,
  entry "showcov-show-l2034" "base/show.jl" "is_core_macro(arg::GlobalRef, macro_name::AbstractString)" "The source-order model of is_core_macro(arg::GlobalRef, macro_name::AbstractString) has a result for every allowed input." ``P2034 ``p2034,
  entry "showcov-show-l2035" "base/show.jl" "is_core_macro(arg::GlobalRef, macro_name::Symbol)" "The source-order model of is_core_macro(arg::GlobalRef, macro_name::Symbol) has a result for every allowed input." ``P2035 ``p2035,
  entry "showcov-show-l2036" "base/show.jl" "is_core_macro(@nospecialize(arg), macro_name::AbstractString)" "The source-order model of is_core_macro(@nospecialize(arg), macro_name::AbstractString) has a result for every allowed input." ``P2036 ``p2036,
  entry "showcov-show-l2037" "base/show.jl" "is_core_macro(@nospecialize(arg), macro_name::Symbol)" "The source-order model of is_core_macro(@nospecialize(arg), macro_name::Symbol) has a result for every allowed input." ``P2037 ``p2037,
  entry "showcov-show-l2043" "base/show.jl" "show_unquoted_expr_fallback(io::IO, ex::Expr)" "The source-order model of show_unquoted_expr_fallback(io::IO, ex::Expr) has a result for every allowed input." ``P2043 ``p2043,
  entry "showcov-show-l2054" "base/show.jl" "show_unquoted(io::IO, ex::Expr, indent::Int, prec::Int, quote_level::Int = 0)" "The source-order model of show_unquoted(io::IO, ex::Expr, indent::Int, prec::Int, quote_level::Int = 0) has a result for every allowed input." ``P2054 ``p2054,
  entry "showcov-show-l2608" "base/show.jl" "demangle_function_name(name::Symbol)" "The source-order model of demangle_function_name(name::Symbol) has a result for every allowed input." ``P2608 ``p2608,
  entry "showcov-show-l2609" "base/show.jl" "demangle_function_name(name::AbstractString)" "The source-order model of demangle_function_name(name::AbstractString) has a result for every allowed input." ``P2609 ``p2609,
  entry "showcov-show-l2620" "base/show.jl" "show_signature_function(io::IO, @nospecialize(ft), demangle=false, fargname=\"\", html=false, qualified=false)" "The source-order model of show_signature_function(io::IO, @nospecialize(ft), demangle=false, fargname=\"\", html=false, qualified=false) has a result for every allowed input." ``P2620 ``p2620,
  entry "showcov-show-l2645" "base/show.jl" "print_within_stacktrace(io, s...; color=:normal, bold=false)" "The source-order model of print_within_stacktrace(io, s...; color=:normal, bold=false) has a result for every allowed input." ``P2645 ``p2645,
  entry "showcov-show-l2653" "base/show.jl" "show_tuple_as_call(out::IO, name::Symbol, sig::Type; demangle=false, kwargs=nothing, argnames=nothing, qualified=false, hasfirst=true)" "The source-order model of show_tuple_as_call(out::IO, name::Symbol, sig::Type; demangle=false, kwargs=nothing, argnames=nothing, qualified=false, hasfirst=true) has a result for every allowed input." ``P2653 ``p2653,
  entry "showcov-show-l2712" "base/show.jl" "type_limited_string_from_context(out::IO, str::String)" "The source-order model of type_limited_string_from_context(out::IO, str::String) has a result for every allowed input." ``P2712 ``p2712,
  entry "showcov-show-l2726" "base/show.jl" "type_depth_limit(str::String, n::Int; maxdepth = nothing)" "The source-order model of type_depth_limit(str::String, n::Int; maxdepth = nothing) has a result for every allowed input." ``P2726 ``p2726,
  entry "showcov-show-l2734" "base/show.jl" "stateis(s)" "The source-order model of stateis(s) has a result for every allowed input." ``P2734 ``p2734,
  entry "showcov-show-l2735" "base/show.jl" "quoted()" "The source-order model of quoted() has a result for every allowed input." ``P2735 ``p2735,
  entry "showcov-show-l2736" "base/show.jl" "enter(s)" "The source-order model of enter(s) has a result for every allowed input." ``P2736 ``p2736,
  entry "showcov-show-l2737" "base/show.jl" "leave(s)" "The source-order model of leave(s) has a result for every allowed input." ``P2737 ``p2737,
  entry "showcov-show-l2818" "base/show.jl" "print_type_bicolor(io, type; kwargs...)" "The source-order model of print_type_bicolor(io, type; kwargs...) has a result for every allowed input." ``P2818 ``p2818,
  entry "showcov-show-l2823" "base/show.jl" "print_type_bicolor(io, str::String; color=:normal, inner_color=:light_black, use_color::Bool=true)" "The source-order model of print_type_bicolor(io, str::String; color=:normal, inner_color=:light_black, use_color::Bool=true) has a result for every allowed input." ``P2823 ``p2823,
  entry "showcov-show-l2840" "base/show.jl" "resolvebinding(@nospecialize(ex))" "The source-order model of resolvebinding(@nospecialize(ex)) has a result for every allowed input." ``P2840 ``p2840,
  entry "showcov-show-l2841" "base/show.jl" "resolvebinding(ex::QuoteNode)" "The source-order model of resolvebinding(ex::QuoteNode) has a result for every allowed input." ``P2841 ``p2841,
  entry "showcov-show-l2842" "base/show.jl" "resolvebinding(ex::Symbol)" "The source-order model of resolvebinding(ex::Symbol) has a result for every allowed input." ``P2842 ``p2842,
  entry "showcov-show-l2843" "base/show.jl" "resolvebinding(ex::Expr)" "The source-order model of resolvebinding(ex::Expr) has a result for every allowed input." ``P2843 ``p2843,
  entry "showcov-show-l2852" "base/show.jl" "resolvebinding(ex::GlobalRef)" "The source-order model of resolvebinding(ex::GlobalRef) has a result for every allowed input." ``P2852 ``p2852,
  entry "showcov-show-l2860" "base/show.jl" "ismodulecall(ex::Expr)" "The source-order model of ismodulecall(ex::Expr) has a result for every allowed input." ``P2860 ``p2860,
  entry "showcov-show-l2866" "base/show.jl" "show(io::IO, tv::TypeVar)" "The source-order model of show(io::IO, tv::TypeVar) has a result for every allowed input." ``P2866 ``p2866,
  entry "showcov-show-l2873" "base/show.jl" "show_bound(io::IO, @nospecialize(b))" "The source-order model of show_bound(io::IO, @nospecialize(b)) has a result for every allowed input." ``P2873 ``p2873,
  entry "showcov-show-l2901" "base/show.jl" "show(io::IO, vm::Core.TypeofVararg)" "The source-order model of show(io::IO, vm::Core.TypeofVararg) has a result for every allowed input." ``P2901 ``p2901,
  entry "showcov-show-l2916" "base/show.jl" "show(io::IO, src::CodeInfo; debuginfo::Symbol=:source)" "The source-order model of show(io::IO, src::CodeInfo; debuginfo::Symbol=:source) has a result for every allowed input." ``P2916 ``p2916,
  entry "showcov-show-l2931" "base/show.jl" "show_unquoted(io::IO, val::Argument, indent::Int, prec::Int)" "The source-order model of show_unquoted(io::IO, val::Argument, indent::Int, prec::Int) has a result for every allowed input." ``P2931 ``p2931,
  entry "showcov-show-l2933" "base/show.jl" "show_unquoted(io::IO, stmt::PhiNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::PhiNode, indent::Int, ::Int) has a result for every allowed input." ``P2933 ``p2933,
  entry "showcov-show-l2934" "base/show.jl" "show_unquoted_phinode(io::IO, stmt::PhiNode, indent::Int, prefix::String)" "The source-order model of show_unquoted_phinode(io::IO, stmt::PhiNode, indent::Int, prefix::String) has a result for every allowed input." ``P2934 ``p2934,
  entry "showcov-show-l2949" "base/show.jl" "show_unquoted(io::IO, stmt::PhiCNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::PhiCNode, indent::Int, ::Int) has a result for every allowed input." ``P2949 ``p2949,
  entry "showcov-show-l2959" "base/show.jl" "show_unquoted(io::IO, stmt::PiNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::PiNode, indent::Int, ::Int) has a result for every allowed input." ``P2959 ``p2959,
  entry "showcov-show-l2967" "base/show.jl" "show_unquoted(io::IO, stmt::UpsilonNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::UpsilonNode, indent::Int, ::Int) has a result for every allowed input." ``P2967 ``p2967,
  entry "showcov-show-l2975" "base/show.jl" "show_unquoted(io::IO, stmt::ReturnNode, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::ReturnNode, indent::Int, ::Int) has a result for every allowed input." ``P2975 ``p2975,
  entry "showcov-show-l2984" "base/show.jl" "show_unquoted(io::IO, stmt::GotoIfNot, indent::Int, ::Int)" "The source-order model of show_unquoted(io::IO, stmt::GotoIfNot, indent::Int, ::Int) has a result for every allowed input." ``P2984 ``p2984,
  entry "showcov-show-l2985" "base/show.jl" "show_unquoted_gotoifnot(io::IO, stmt::GotoIfNot, indent::Int, prefix::String)" "The source-order model of show_unquoted_gotoifnot(io::IO, stmt::GotoIfNot, indent::Int, prefix::String) has a result for every allowed input." ``P2985 ``p2985,
  entry "showcov-show-l2990" "base/show.jl" "dump(io::IOContext, x::SimpleVector, n::Int, indent)" "The source-order model of dump(io::IOContext, x::SimpleVector, n::Int, indent) has a result for every allowed input." ``P2990 ``p2990,
  entry "showcov-show-l3010" "base/show.jl" "dump(io::IOContext, @nospecialize(x), n::Int, indent)" "The source-order model of dump(io::IOContext, @nospecialize(x), n::Int, indent) has a result for every allowed input." ``P3010 ``p3010,
  entry "showcov-show-l3043" "base/show.jl" "dump(io::IOContext, x::Module, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Module, n::Int, indent) has a result for every allowed input." ``P3043 ``p3043,
  entry "showcov-show-l3044" "base/show.jl" "dump(io::IOContext, x::String, n::Int, indent)" "The source-order model of dump(io::IOContext, x::String, n::Int, indent) has a result for every allowed input." ``P3044 ``p3044,
  entry "showcov-show-l3045" "base/show.jl" "dump(io::IOContext, x::Symbol, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Symbol, n::Int, indent) has a result for every allowed input." ``P3045 ``p3045,
  entry "showcov-show-l3046" "base/show.jl" "dump(io::IOContext, x::Union, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Union, n::Int, indent) has a result for every allowed input." ``P3046 ``p3046,
  entry "showcov-show-l3047" "base/show.jl" "dump(io::IOContext, x::Ptr, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Ptr, n::Int, indent) has a result for every allowed input." ``P3047 ``p3047,
  entry "showcov-show-l3049" "base/show.jl" "dump_elts(io::IOContext, x::Array, n::Int, indent, i0, i1)" "The source-order model of dump_elts(io::IOContext, x::Array, n::Int, indent, i0, i1) has a result for every allowed input." ``P3049 ``p3049,
  entry "showcov-show-l3061" "base/show.jl" "dump(io::IOContext, x::Array, n::Int, indent)" "The source-order model of dump(io::IOContext, x::Array, n::Int, indent) has a result for every allowed input." ``P3061 ``p3061,
  entry "showcov-show-l3087" "base/show.jl" "dump(io::IOContext, x::DataType, n::Int, indent)" "The source-order model of dump(io::IOContext, x::DataType, n::Int, indent) has a result for every allowed input." ``P3087 ``p3087,
  entry "showcov-show-l3130" "base/show.jl" "dump(io::IO, @nospecialize(x); maxdepth=DUMP_DEFAULT_MAXDEPTH)" "The source-order model of dump(io::IO, @nospecialize(x); maxdepth=DUMP_DEFAULT_MAXDEPTH) has a result for every allowed input." ``P3130 ``p3130,
  entry "showcov-show-l3163" "base/show.jl" "dump(arg; maxdepth=DUMP_DEFAULT_MAXDEPTH)" "The source-order model of dump(arg; maxdepth=DUMP_DEFAULT_MAXDEPTH) has a result for every allowed input." ``P3163 ``p3163,
  entry "showcov-show-l3169" "base/show.jl" "nocolor(io::IO)" "The source-order model of nocolor(io::IO) has a result for every allowed input." ``P3169 ``p3169,
  entry "showcov-show-l3170" "base/show.jl" "alignment_from_show(io::IO, x::Any)" "The source-order model of alignment_from_show(io::IO, x::Any) has a result for every allowed input." ``P3170 ``p3170,
  entry "showcov-show-l3172" "base/show.jl" "alignment_from_show(io::IO, x::AbstractString)" "The source-order model of alignment_from_show(io::IO, x::AbstractString) has a result for every allowed input." ``P3172 ``p3172,
  entry "showcov-show-l3191" "base/show.jl" "alignment(io::IO, x::Any)" "The source-order model of alignment(io::IO, x::Any) has a result for every allowed input." ``P3191 ``p3191,
  entry "showcov-show-l3192" "base/show.jl" "alignment(io::IO, x::Number)" "The source-order model of alignment(io::IO, x::Number) has a result for every allowed input." ``P3192 ``p3192,
  entry "showcov-show-l3193" "base/show.jl" "alignment(io::IO, x::Integer)" "The source-order model of alignment(io::IO, x::Integer) has a result for every allowed input." ``P3193 ``p3193,
  entry "showcov-show-l3194" "base/show.jl" "alignment(io::IO, x::Real)" "The source-order model of alignment(io::IO, x::Real) has a result for every allowed input." ``P3194 ``p3194,
  entry "showcov-show-l3200" "base/show.jl" "alignment(io::IO, x::Complex)" "The source-order model of alignment(io::IO, x::Complex) has a result for every allowed input." ``P3200 ``p3200,
  entry "showcov-show-l3206" "base/show.jl" "alignment(io::IO, x::Rational)" "The source-order model of alignment(io::IO, x::Rational) has a result for every allowed input." ``P3206 ``p3206,
  entry "showcov-show-l3213" "base/show.jl" "alignment(io::IO, x::Pair)" "The source-order model of alignment(io::IO, x::Pair) has a result for every allowed input." ``P3213 ``p3213,
  entry "showcov-show-l3228" "base/show.jl" "show(io::IO, ::UndefInitializer)" "The source-order model of show(io::IO, ::UndefInitializer) has a result for every allowed input." ``P3228 ``p3228,
  entry "showcov-show-l3249" "base/show.jl" "summary(io::IO, x)" "The source-order model of summary(io::IO, x) has a result for every allowed input." ``P3249 ``p3249,
  entry "showcov-show-l3250" "base/show.jl" "summary(x)" "The source-order model of summary(x) has a result for every allowed input." ``P3250 ``p3250,
  entry "showcov-show-l3258" "base/show.jl" "dims2string(d)" "The source-order model of dims2string(d) has a result for every allowed input." ``P3258 ``p3258,
  entry "showcov-show-l3262" "base/show.jl" "inds2string(inds)" "The source-order model of inds2string(inds) has a result for every allowed input." ``P3262 ``p3262,
  entry "showcov-show-l3263" "base/show.jl" "_indsstring(i)" "The source-order model of _indsstring(i) has a result for every allowed input." ``P3263 ``p3263,
  entry "showcov-show-l3264" "base/show.jl" "_indsstring(i::Union{IdentityUnitRange, Slice})" "The source-order model of _indsstring(i::Union{IdentityUnitRange, Slice}) has a result for every allowed input." ``P3264 ``p3264,
  entry "showcov-show-l3267" "base/show.jl" "summary(io::IO, a::AbstractArray)" "The source-order model of summary(io::IO, a::AbstractArray) has a result for every allowed input." ``P3267 ``p3267,
  entry "showcov-show-l3268" "base/show.jl" "array_summary(io::IO, a, inds::Tuple{Vararg{OneTo}})" "The source-order model of array_summary(io::IO, a, inds::Tuple{Vararg{OneTo}}) has a result for every allowed input." ``P3268 ``p3268,
  entry "showcov-show-l3272" "base/show.jl" "array_summary(io::IO, a, inds)" "The source-order model of array_summary(io::IO, a, inds) has a result for every allowed input." ``P3272 ``p3272,
  entry "showcov-show-l3279" "base/show.jl" "summary(io::IO, mref::GenericMemoryRef)" "The source-order model of summary(io::IO, mref::GenericMemoryRef) has a result for every allowed input." ``P3279 ``p3279,
  entry "showcov-show-l3287" "base/show.jl" "summary(io::IO, f::Function)" "The source-order model of summary(io::IO, f::Function) has a result for every allowed input." ``P3287 ``p3287,
  entry "showcov-show-l3335" "base/show.jl" "showarg(io::IO, @nospecialize(x), toplevel)" "The source-order model of showarg(io::IO, @nospecialize(x), toplevel) has a result for every allowed input." ``P3335 ``p3335,
  entry "showcov-show-l3339" "base/show.jl" "showarg(io::IO, T::Type, toplevel)" "The source-order model of showarg(io::IO, T::Type, toplevel) has a result for every allowed input." ``P3339 ``p3339,
  entry "showcov-show-l3344" "base/show.jl" "showarg(io::IO, a::Array{Union{}}, toplevel)" "The source-order model of showarg(io::IO, a::Array{Union{}}, toplevel) has a result for every allowed input." ``P3344 ``p3344,
  entry "showcov-show-l3350" "base/show.jl" "showarg(io::IO, v::SubArray, toplevel)" "The source-order model of showarg(io::IO, v::SubArray, toplevel) has a result for every allowed input." ``P3350 ``p3350,
  entry "showcov-show-l3358" "base/show.jl" "showindices(io, ::Slice, inds...)" "The source-order model of showindices(io, ::Slice, inds...) has a result for every allowed input." ``P3358 ``p3358,
  entry "showcov-show-l3360" "base/show.jl" "showindices(io, ind1, inds...)" "The source-order model of showindices(io, ind1, inds...) has a result for every allowed input." ``P3360 ``p3360,
  entry "showcov-show-l3362" "base/show.jl" "showindices(io)" "The source-order model of showindices(io) has a result for every allowed input." ``P3362 ``p3362,
  entry "showcov-show-l3364" "base/show.jl" "showarg(io::IO, r::ReshapedArray, toplevel)" "The source-order model of showarg(io::IO, r::ReshapedArray, toplevel) has a result for every allowed input." ``P3364 ``p3364,
  entry "showcov-show-l3375" "base/show.jl" "showarg(io::IO, r::NonReshapedReinterpretArray{T}, toplevel) where {T}" "The source-order model of showarg(io::IO, r::NonReshapedReinterpretArray{T}, toplevel) where {T} has a result for every allowed input." ``P3375 ``p3375,
  entry "showcov-show-l3381" "base/show.jl" "showarg(io::IO, r::ReshapedReinterpretArray{T}, toplevel) where {T}" "The source-order model of showarg(io::IO, r::ReshapedReinterpretArray{T}, toplevel) where {T} has a result for every allowed input." ``P3381 ``p3381,
  entry "showcov-show-l3391" "base/show.jl" "show(io::IO, e::Iterators.Enumerate)" "The source-order model of show(io::IO, e::Iterators.Enumerate) has a result for every allowed input." ``P3391 ``p3391,
  entry "showcov-show-l3396" "base/show.jl" "show(io::IO, z::Iterators.Zip)" "The source-order model of show(io::IO, z::Iterators.Zip) has a result for every allowed input." ``P3396 ``p3396,
  entry "showcov-show-l3399" "base/show.jl" "Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T<:AbstractArray" "The source-order model of Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T<:AbstractArray has a result for every allowed input." ``P3399 ``p3399,
  entry "showcov-show-l3403" "base/show.jl" "Base.showarg(io::IO, r::Iterators.Pairs{Symbol, <:Any, Nothing, T}, toplevel) where {T <: NamedTuple}" "The source-order model of Base.showarg(io::IO, r::Iterators.Pairs{Symbol, <:Any, Nothing, T}, toplevel) where {T <: NamedTuple} has a result for every allowed input." ``P3403 ``p3403,
  entry "showcov-show-l3407" "base/show.jl" "Base.showarg(io::IO, r::Iterators.Pairs{<:Any, <:Any, I, D}, toplevel) where {D, I}" "The source-order model of Base.showarg(io::IO, r::Iterators.Pairs{<:Any, <:Any, I, D}, toplevel) where {D, I} has a result for every allowed input." ``P3407 ``p3407,
  entry "showcov-show-l3415" "base/show.jl" "print_bit_chunk(io::IO, c::UInt64, l::Integer = 64)" "The source-order model of print_bit_chunk(io::IO, c::UInt64, l::Integer = 64) has a result for every allowed input." ``P3415 ``p3415,
  entry "showcov-show-l3425" "base/show.jl" "print_bit_chunk(c::UInt64, l::Integer)" "The source-order model of print_bit_chunk(c::UInt64, l::Integer) has a result for every allowed input." ``P3425 ``p3425,
  entry "showcov-show-l3426" "base/show.jl" "print_bit_chunk(c::UInt64)" "The source-order model of print_bit_chunk(c::UInt64) has a result for every allowed input." ``P3426 ``p3426,
  entry "showcov-show-l3428" "base/show.jl" "bitshow(io::IO, B::BitArray)" "The source-order model of bitshow(io::IO, B::BitArray) has a result for every allowed input." ``P3428 ``p3428,
  entry "showcov-show-l3438" "base/show.jl" "bitshow(B::BitArray)" "The source-order model of bitshow(B::BitArray) has a result for every allowed input." ``P3438 ``p3438,
  entry "showcov-show-l3440" "base/show.jl" "bitstring(B::BitArray)" "The source-order model of bitstring(B::BitArray) has a result for every allowed input." ``P3440 ``p3440,
  entry "showcov-show-l3443" "base/show.jl" "show(io::IO, oc::Core.OpaqueClosure)" "The source-order model of show(io::IO, oc::Core.OpaqueClosure) has a result for every allowed input." ``P3443 ``p3443,
  entry "showcov-show-l3450" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", oc::Core.OpaqueClosure{A, R}) where {A, R}" "The source-order model of show(io::IO, ::MIME\"text/plain\", oc::Core.OpaqueClosure{A, R}) where {A, R} has a result for every allowed input." ``P3450 ``p3450,
  entry "showcov-show-l3455" "base/show.jl" "print_partition(io::IO, partition::Core.BindingPartition)" "The source-order model of print_partition(io::IO, partition::Core.BindingPartition) has a result for every allowed input." ``P3455 ``p3455,
  entry "showcov-show-l3507" "base/show.jl" "show(io::IO, partition::Core.BindingPartition)" "The source-order model of show(io::IO, partition::Core.BindingPartition) has a result for every allowed input." ``P3507 ``p3507,
  entry "showcov-show-l3513" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", partition::Core.BindingPartition)" "The source-order model of show(io::IO, ::MIME\"text/plain\", partition::Core.BindingPartition) has a result for every allowed input." ``P3513 ``p3513,
  entry "showcov-show-l3519" "base/show.jl" "show(io::IO, ::MIME\"text/plain\", bnd::Core.Binding)" "The source-order model of show(io::IO, ::MIME\"text/plain\", bnd::Core.Binding) has a result for every allowed input." ``P3519 ``p3519,
  entry "showcov-show-l3539" "base/show.jl" "show(io::IO, ii::IncludeInto)" "The source-order model of show(io::IO, ii::IncludeInto) has a result for every allowed input." ``P3539 ``p3539,
  entry "showcov-show-l3548" "base/show.jl" "show(io::IO, ei::Core.EvalInto)" "The source-order model of show(io::IO, ei::Core.EvalInto) has a result for every allowed input." ``P3548 ``p3548
]

end JuliaLean.ShowCov.Methods.ShowFile
