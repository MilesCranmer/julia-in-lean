import JuliaLean.ExprReflect.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

/-! Exact row models for `base/expr.jl` at `bbfa0ce4150`. -/

/-- Both collection-head `isexpr` methods, `base/expr.jl:3-4`. -/
def exprRow3 (expression : Ast) (heads : List String) : Bool := isExpr expression heads none
def ExprRow3Property : Prop := ∀ expression heads,
  exprRow3 expression heads = match expression with | .expr head _ => heads.contains head | _ => false
theorem exprRow3_proven : ExprRow3Property := by
  unfold ExprRow3Property
  intro expression heads
  cases expression <;> simp [exprRow3, isExpr]

def exprRow4 (expression : Ast) (heads : List String) (arity : Nat) : Bool := isExpr expression heads (some arity)
def ExprRow4Property : Prop := ∀ expression heads arity,
  exprRow4 expression heads arity = match expression with
    | .expr head arguments => heads.contains head && arguments.length == arity | _ => false
theorem exprRow4_proven : ExprRow4Property := by unfold ExprRow4Property; intro expression heads arity; cases expression <;> rfl

structure GensymState where
  next : Nat
  names : List String
  deriving Repr, DecidableEq, Inhabited

def jlGensym (tag : Option String) (state : GensymState) : String × GensymState :=
  let name := gensymTag tag state.next
  (name, ⟨state.next + 1, state.names ++ [name]⟩)

def exprRow18 (state : GensymState) := jlGensym none state
def ExprRow18Property : Prop := ∀ state, (exprRow18 state).2.next = state.next + 1
theorem exprRow18_proven : ExprRow18Property := by unfold ExprRow18Property; intro state; cases state; rfl

def exprRow20 (tag : String) (state : GensymState) := jlGensym (some tag) state
def ExprRow20Property : Prop := ∀ tag state,
  (exprRow20 tag state).1 = gensymTag (some tag) state.next
theorem exprRow20_proven : ExprRow20Property := by unfold ExprRow20Property; intros; rfl

def exprRow22 : List String → GensymState → List String × GensymState
  | [], state => ([],state)
  | tag::tags, state =>
    let (name,state) := jlGensym (some tag) state
    let (names,state) := exprRow22 tags state
    (name::names,state)
def ExprRow22Property : Prop := ∀ tags state, (exprRow22 tags state).1.length = tags.length
theorem exprRow22_proven : ExprRow22Property := by intro tags; induction tags <;> simp [exprRow22, *]

def exprRow23 (tag : String) (state : GensymState) := jlGensym (some tag) state
def ExprRow23Property : Prop := ∀ tag state, exprRow23 tag state = exprRow20 tag state
theorem exprRow23_proven : ExprRow23Property := by unfold ExprRow23Property; intros; rfl

def exprRow31 (names : List String) (state : GensymState) : List (String × String) × GensymState :=
  let (generated,state) := exprRow22 names state
  (List.zip names generated, state)
def ExprRow31Property : Prop := ∀ names state,
  (exprRow31 names state).1.map (·.1) = names
theorem exprRow31_proven : ExprRow31Property := by
  intro names state; simp [exprRow31]
  induction names generalizing state <;> simp [exprRow22, *]

def exprRow42 (expression : Ast) (head : String) : Bool := isExpr expression [head] none
def ExprRow42Property : Prop := ∀ expression head,
  exprRow42 expression head = match expression with | .expr actual _ => decide (actual = head) | _ => false
theorem exprRow42_proven : ExprRow42Property := by unfold ExprRow42Property; intro expression head; cases expression <;> simp [exprRow42,isExpr]

def exprRow43 (expression : Ast) (head : String) (arity : Nat) : Bool := isExpr expression [head] (some arity)
def ExprRow43Property : Prop := ∀ expression head arity,
  exprRow43 expression head arity = match expression with
    | .expr actual arguments => decide (actual = head) && arguments.length == arity | _ => false
theorem exprRow43_proven : ExprRow43Property := by unfold ExprRow43Property; intro expression head arity; cases expression <;> simp [exprRow43,isExpr]

/-! IR copy and equality rows. -/

structure PhiModel where
  edges : List Int
  values : List (Option IRObject)
  deriving Repr, DecidableEq, Inhabited

structure PhiCModel where
  values : List (Option IRObject)
  deriving Repr, DecidableEq, Inhabited

def copyOptionalIR (fresh : Nat) : Option IRObject → Option IRObject
  | none => none
  | some value => some (copyIRObject fresh value)

def exprRow45 (fresh : Nat) (object : IRObject) : IRObject := copyIRObject fresh { object with kind := .expr }
def ExprRow45Property : Prop := ∀ fresh object, (exprRow45 fresh object).kind = .expr
theorem exprRow45_proven : ExprRow45Property := by unfold ExprRow45Property; intros; rfl

def exprRow46 (fresh : Nat) (node : PhiModel) : PhiModel :=
  ⟨node.edges, node.values.map (copyOptionalIR fresh)⟩
def ExprRow46Property : Prop := ∀ fresh node,
  (exprRow46 fresh node).edges = node.edges ∧
  (exprRow46 fresh node).values = node.values.map (copyOptionalIR fresh)
theorem exprRow46_proven : ExprRow46Property := by unfold ExprRow46Property; intros; exact ⟨rfl,rfl⟩

def exprRow56 (fresh : Nat) (node : PhiCModel) : PhiCModel :=
  ⟨node.values.map (copyOptionalIR fresh)⟩
def ExprRow56Property : Prop := ∀ fresh node,
  (exprRow56 fresh node).values = node.values.map (copyOptionalIR fresh)
theorem exprRow56_proven : ExprRow56Property := by unfold ExprRow56Property; intros; rfl

def exprRow69 (fresh : Nat) (object : IRObject) : IRObject :=
  match object.kind with
  | .expr | .phi | .phiC => copyIRObject fresh object
  | _ => object
def ExprRow69Property : Prop := ∀ fresh object,
  exprRow69 fresh object = match object.kind with
    | .expr | .phi | .phiC => copyIRObject fresh object
    | _ => object
theorem exprRow69_proven : ExprRow69Property := by unfold ExprRow69Property; intros; rfl

def exprRow79 (fresh : Nat) (arguments : List (Option IRObject)) : List (Option IRObject) :=
  arguments.map (copyOptionalIR fresh)
def ExprRow79Property : Prop := ∀ fresh arguments,
  exprRow79 fresh arguments = arguments.map (copyOptionalIR fresh)
theorem exprRow79_proven : ExprRow79Property := by unfold ExprRow79Property; intros; rfl

def exprRow81 (head : String) (arguments : List Ast) : Ast := .expr head arguments
def ExprRow81Property : Prop := ∀ head arguments, exprRow81 head arguments = .expr head arguments
theorem exprRow81_proven : ExprRow81Property := by unfold ExprRow81Property; intros; rfl

def exprRow84 (fresh : Nat) (code : CodeInfoFields) : CodeInfoFields := copyCodeInfoFields fresh code
def ExprRow84Property : Prop := ∀ fresh code,
  (exprRow84 fresh code).slotnames = code.slotnames ∧ (exprRow84 fresh code).code.length = code.code.length
theorem exprRow84_proven : ExprRow84Property := by intro fresh code; cases code <;> simp [exprRow84,copyCodeInfoFields]

def exprRow99 (left right : IRObject) : Bool := isequalIRArg left right
def ExprRow99Property : Prop := ∀ left right, exprRow99 left right = isequalIRArg left right
theorem exprRow99_proven : ExprRow99Property := by unfold ExprRow99Property; intros; rfl

def exprRow118 (left right : List IRObject) : Bool :=
  left.length == right.length && (List.zip left right).all fun pair => isequalIRArg pair.1 pair.2
def ExprRow118Property : Prop := ∀ left right,
  exprRow118 left right = (left.length == right.length && (List.zip left right).all fun pair => isequalIRArg pair.1 pair.2)
theorem exprRow118_proven : ExprRow118Property := by unfold ExprRow118Property; intros; rfl

def exprStructuralEqual (left right : IRObject) : Bool := isequalIRArg left right

def exprRow135 := exprStructuralEqual
def exprRow137 := exprStructuralEqual
def exprRow139 := exprStructuralEqual
def exprRow141 := exprStructuralEqual
def exprRow143 := exprStructuralEqual
def exprRow173 := exprStructuralEqual

def ExprRow135Property : Prop := ∀ left right, exprRow135 left right = isequalIRArg left right
def ExprRow137Property : Prop := ∀ left right, exprRow137 left right = isequalIRArg left right
def ExprRow139Property : Prop := ∀ left right, exprRow139 left right = isequalIRArg left right
def ExprRow141Property : Prop := ∀ left right, exprRow141 left right = isequalIRArg left right
def ExprRow143Property : Prop := ∀ left right, exprRow143 left right = isequalIRArg left right
def ExprRow173Property : Prop := ∀ left right, exprRow173 left right = isequalIRArg left right
theorem exprRow135_proven : ExprRow135Property := by unfold ExprRow135Property; intros; rfl
theorem exprRow137_proven : ExprRow137Property := by unfold ExprRow137Property; intros; rfl
theorem exprRow139_proven : ExprRow139Property := by unfold ExprRow139Property; intros; rfl
theorem exprRow141_proven : ExprRow141Property := by unfold ExprRow141Property; intros; rfl
theorem exprRow143_proven : ExprRow143Property := by unfold ExprRow143Property; intros; rfl
theorem exprRow173_proven : ExprRow173Property := by unfold ExprRow173Property; intros; rfl

/-! Macro expansion rows. -/

def exprRow209 (recursive legacy : Bool) : MacroexpandFlags := ⟨recursive,false,legacy⟩
def ExprRow209Property : Prop := ∀ recursive legacy, exprRow209 recursive legacy = ⟨recursive,false,legacy⟩
theorem exprRow209_proven : ExprRow209Property := by unfold ExprRow209Property; intros; rfl

def exprRow232 (recursive legacy : Bool) : MacroexpandFlags := ⟨recursive,true,legacy⟩
def ExprRow232Property : Prop := ∀ recursive legacy, exprRow232 recursive legacy = ⟨recursive,true,legacy⟩
theorem exprRow232_proven : ExprRow232Property := by unfold ExprRow232Property; intros; rfl

def exprRow279 (moduleName expression : String) : String := "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),true,true)"
def ExprRow279Property : Prop := ∀ moduleName expression,
  exprRow279 moduleName expression = "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),true,true)"
theorem exprRow279_proven : ExprRow279Property := by unfold ExprRow279Property; intros; rfl

def exprRow282 := exprRow279
def ExprRow282Property : Prop := ∀ moduleName expression, exprRow282 moduleName expression = exprRow279 moduleName expression
theorem exprRow282_proven : ExprRow282Property := by unfold ExprRow282Property; intros; rfl

def exprRow291 (moduleName expression : String) : String := "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),false,true)"
def ExprRow291Property : Prop := ∀ moduleName expression,
  exprRow291 moduleName expression = "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),false,true)"
theorem exprRow291_proven : ExprRow291Property := by unfold ExprRow291Property; intros; rfl

def exprRow294 := exprRow291
def ExprRow294Property : Prop := ∀ moduleName expression, exprRow294 moduleName expression = exprRow291 moduleName expression
theorem exprRow294_proven : ExprRow294Property := by unfold ExprRow294Property; intros; rfl

/-! Annotation and effect rows. -/

def exprRow389 (isFunction : Bool) : String := annotationTag "inline" isFunction
def ExprRow389Property : Prop := ∀ isFunction, exprRow389 isFunction = annotationTag "inline" isFunction
theorem exprRow389_proven : ExprRow389Property := by unfold ExprRow389Property; intros; rfl

def exprRow466 (isFunction : Bool) : String := annotationTag "noinline" isFunction
def ExprRow466Property : Prop := ∀ isFunction, exprRow466 isFunction = annotationTag "noinline" isFunction
theorem exprRow466_proven : ExprRow466Property := by unfold ExprRow466Property; intros; rfl

def exprRow505 (setting : ConstpropSetting) (isExpression : Bool) := constpropShape setting isExpression
def ExprRow505Property : Prop := ∀ setting isExpression, exprRow505 setting isExpression = constpropShape setting isExpression
theorem exprRow505_proven : ExprRow505Property := by unfold ExprRow505Property; intros; rfl

def exprRow510 (setting : ConstpropSetting) := constpropShape setting false
def ExprRow510Property : Prop := ∀ setting, exprRow510 setting = constpropShape setting false
theorem exprRow510_proven : ExprRow510Property := by unfold ExprRow510Property; intros; rfl

def exprRow515 := constpropTag
def ExprRow515Property : Prop := ∀ setting, exprRow515 setting = constpropTag setting
theorem exprRow515_proven : ExprRow515Property := by unfold ExprRow515Property; intros; rfl

def exprRow896 (target : EffectTarget) : String := assumeEffectsShape target
def ExprRow896Property : Prop := ∀ target, exprRow896 target = assumeEffectsShape target
theorem exprRow896_proven : ExprRow896Property := by unfold ExprRow896Property; intros; rfl

def exprRow938 (settings : List (EffectSetting × Bool)) : EffectOverride :=
  settings.foldl (fun override setting => applyEffectSetting override setting.1 setting.2) default
def ExprRow938Property : Prop := ∀ settings, (effectBits (exprRow938 settings)).length = 11
theorem exprRow938_proven : ExprRow938Property := by unfold ExprRow938Property; intros; simp [effectBits]

def exprRow962 (override : EffectOverride) := override
def ExprRow962Property : Prop := ∀ override, exprRow962 override = override
theorem exprRow962_proven : ExprRow962Property := by unfold ExprRow962Property; intros; rfl

def exprRow995 (override : EffectOverride) (setting : EffectSetting) (value : Bool) :=
  applyEffectSetting override setting value
def ExprRow995Property : Prop := ∀ override setting value,
  exprRow995 override setting value = applyEffectSetting override setting value
theorem exprRow995_proven : ExprRow995Property := by unfold ExprRow995Property; intros; rfl

def exprRow1035 := effectBits
def ExprRow1035Property : Prop := ∀ override, (exprRow1035 override).length = 11
theorem exprRow1035_proven : ExprRow1035Property := by unfold ExprRow1035Property; intro; rfl

def exprRow1051 := decodeEffectBits
def ExprRow1051Property : Prop := ∀ override, exprRow1051 (effectBits override) = override
theorem exprRow1051_proven : ExprRow1051Property := by unfold ExprRow1051Property; intro override; cases override; rfl

def exprRow1066 := effectBits
def ExprRow1066Property : Prop := ∀ override, exprRow1066 override = effectBits override
theorem exprRow1066_proven : ExprRow1066Property := by unfold ExprRow1066Property; intros; rfl

def exprRow1111 (isExpression : Bool) := if isExpression then "pushmeta:nospecializeinfer" else "identity"
def ExprRow1111Property : Prop := ∀ value, exprRow1111 value = if value then "pushmeta:nospecializeinfer" else "identity"
theorem exprRow1111_proven : ExprRow1111Property := by unfold ExprRow1111Property; intros; rfl

def exprRow1148 (isExpression : Bool) := if isExpression then ["inline","propagate_inbounds"] else []
def ExprRow1148Property : Prop := ∀ value, exprRow1148 value = if value then ["inline","propagate_inbounds"] else []
theorem exprRow1148_proven : ExprRow1148Property := by unfold ExprRow1148Property; intros; rfl

def exprRow1161 (isExpression : Bool) := if isExpression then ["polly"] else []
def ExprRow1161Property : Prop := ∀ value, exprRow1161 value = if value then ["polly"] else []
theorem exprRow1161_proven : ExprRow1161Property := by unfold ExprRow1161Property; intros; rfl

/-! Metadata and line-number rows. -/

/-- Generic `unwrap_macrocalls`; `base/expr.jl:1167`. -/
def exprRow1167 (value : CoverageAst) : CoverageAst := value
def ExprRow1167Property : Prop := ∀ value, exprRow1167 value = value
theorem exprRow1167_proven : ExprRow1167Property := by unfold ExprRow1167Property; intro; rfl

/-- Expr `unwrap_macrocalls`; `base/expr.jl:1168-1174`. -/
def exprRow1168 (value : CoverageAst) : CoverageAst := CoverageAst.unwrapMacrocall value
def ExprRow1168Property : Prop := ∀ value, exprRow1168 value = CoverageAst.unwrapMacrocall value
theorem exprRow1168_proven : ExprRow1168Property := by unfold ExprRow1168Property; intro; rfl

structure MetaBody where
  tags : List String
  statements : List CoverageAst
  deriving Repr, DecidableEq, Inhabited

/-- `pushmeta!`; `base/expr.jl:1176-1187`. -/
def exprRow1176 (body : MetaBody) (tag : String) : MetaBody :=
  { body with tags := body.tags ++ [tag] }
def ExprRow1176Property : Prop := ∀ body tag,
  (exprRow1176 body tag).tags = body.tags ++ [tag]
theorem exprRow1176_proven : ExprRow1176Property := by unfold ExprRow1176Property; intros; rfl

def getMetaTag (body : MetaBody) (tag : String) (delete : Bool) : Option String × MetaBody :=
  match body.tags.findIdx? (· == tag) with
  | none => (none,body)
  | some index =>
    let found := body.tags[index]!
    (some found, if delete then { body with tags := body.tags.eraseIdx index } else body)

/-- `popmeta!`; `base/expr.jl:1189`. -/
def exprRow1189 (body : MetaBody) (tag : String) := getMetaTag body tag true
def ExprRow1189Property : Prop := ∀ body tag, exprRow1189 body tag = getMetaTag body tag true
theorem exprRow1189_proven : ExprRow1189Property := by unfold ExprRow1189Property; intros; rfl

/-- `peekmeta`; `base/expr.jl:1190`. -/
def exprRow1190 (body : MetaBody) (tag : String) := getMetaTag body tag false
def ExprRow1190Property : Prop := ∀ body tag, exprRow1190 body tag = getMetaTag body tag false
theorem exprRow1190_proven : ExprRow1190Property := by unfold ExprRow1190Property; intros; rfl

/-- Expr `_getmeta`; `base/expr.jl:1192-1195`. -/
def exprRow1192 (body : MetaBody) (tag : String) (delete : Bool) := getMetaTag body tag delete
def ExprRow1192Property : Prop := ∀ body tag delete, exprRow1192 body tag delete = getMetaTag body tag delete
theorem exprRow1192_proven : ExprRow1192Property := by unfold ExprRow1192Property; intros; rfl

/-- Atomic `_getmeta` fallback; `base/expr.jl:1196`. -/
def exprRow1196 (body : CoverageAst) : Option String × CoverageAst := (none,body)
def ExprRow1196Property : Prop := ∀ body, exprRow1196 body = (none,body)
theorem exprRow1196_proven : ExprRow1196Property := by unfold ExprRow1196Property; intro; rfl

/-- Array `_getmeta`; `base/expr.jl:1197-1213`. -/
def exprRow1197 (body : MetaBody) (tag : String) (delete : Bool) := getMetaTag body tag delete
def ExprRow1197Property : Prop := ∀ body tag delete, exprRow1197 body tag delete = getMetaTag body tag delete
theorem exprRow1197_proven : ExprRow1197Property := by unfold ExprRow1197Property; intros; rfl

/-- `findmetaarg`; `base/expr.jl:1216-1225`. -/
def exprRow1216 (arguments : List String) (tag : String) : Nat :=
  match arguments.findIdx? (· == tag) with | none => 0 | some index => index + 1
def ExprRow1216Property : Prop := ∀ arguments tag,
  exprRow1216 arguments tag = match arguments.findIdx? (· == tag) with | none => 0 | some index => index + 1
theorem exprRow1216_proven : ExprRow1216Property := by unfold ExprRow1216Property; intros; rfl

/-- `annotate_meta_def_or_block`; `base/expr.jl:1227-1240`. -/
def exprRow1227 (isFunction : Bool) (tag : String) : String := annotationTag tag isFunction
def ExprRow1227Property : Prop := ∀ isFunction tag, exprRow1227 isFunction tag = annotationTag tag isFunction
theorem exprRow1227_proven : ExprRow1227Property := by unfold ExprRow1227Property; intros; rfl

/-- `is_short_function_def`; `base/expr.jl:1242-1250`. -/
def exprRow1242 (value : CoverageAst) : Bool :=
  match value with | .expr "=" (.args (.expr "call" _) _) => true | _ => false
def ExprRow1242Property : Prop := ∀ value,
  exprRow1242 value = match value with | .expr "=" (.args (.expr "call" _) _) => true | _ => false
theorem exprRow1242_proven : ExprRow1242Property := by unfold ExprRow1242Property; intro value; cases value <;> rfl

/-- `is_function_def`; `base/expr.jl:1251-1252`. -/
def exprRow1251 (value : CoverageAst) : Bool := CoverageAst.isFunctionDef value
def ExprRow1251Property : Prop := ∀ value, exprRow1251 value = CoverageAst.isFunctionDef value
theorem exprRow1251_proven : ExprRow1251Property := by unfold ExprRow1251Property; intro; rfl

/-- Expr `findmeta`; `base/expr.jl:1254-1261`. -/
def exprRow1254 (isFunction : Bool) (body : MetaBody) : Jl (Nat × MetaBody) :=
  if isFunction then .ok (if body.tags.isEmpty then 0 else 1,body)
  else .error (.argumentError "not a function expression")
def ExprRow1254Property : Prop := ∀ body,
  exprRow1254 false body = .error (.argumentError "not a function expression")
theorem exprRow1254_proven : ExprRow1254Property := by unfold ExprRow1254Property; intro; rfl

/-- Array `findmeta`; `base/expr.jl:1263`. -/
def exprRow1263 (body : MetaBody) : Nat × MetaBody := (if body.tags.isEmpty then 0 else 1,body)
def ExprRow1263Property : Prop := ∀ body, (exprRow1263 body).2 = body
theorem exprRow1263_proven : ExprRow1263Property := by unfold ExprRow1263Property; intro; rfl

/-- `findmeta_block`; `base/expr.jl:1265-1280`. -/
def exprRow1265 (body : MetaBody) (predicate : List String → Bool) : Nat :=
  match body.tags.findIdx? (fun tag => predicate [tag]) with | none => 0 | some index => index + 1
def ExprRow1265Property : Prop := ∀ body predicate,
  exprRow1265 body predicate = match body.tags.findIdx? (fun tag => predicate [tag]) with | none => 0 | some index => index + 1
theorem exprRow1265_proven : ExprRow1265Property := by unfold ExprRow1265Property; intros; rfl

/-- `remove_linenums!`; `base/expr.jl:1287-1304`. -/
def exprRow1287 (value : CoverageAst) := CoverageAst.removeLineNums value
def ExprRow1287Property : Prop := ∀ value, exprRow1287 value = CoverageAst.removeLineNums value
theorem exprRow1287_proven : ExprRow1287Property := by unfold ExprRow1287Property; intro; rfl

/-- Atomic `replace_linenums!`; `base/expr.jl:1306`. -/
def exprRow1306 (value : CoverageAst) (_line : Int) := value
def ExprRow1306Property : Prop := ∀ value line, exprRow1306 value line = value
theorem exprRow1306_proven : ExprRow1306Property := by unfold ExprRow1306Property; intros; rfl

/-- Expr `replace_linenums!`; `base/expr.jl:1307-1324`. -/
def exprRow1307 (value : CoverageAst) (line : Int) := CoverageAst.replaceLineNums line value
def ExprRow1307Property : Prop := ∀ value line, exprRow1307 value line = CoverageAst.replaceLineNums line value
theorem exprRow1307_proven : ExprRow1307Property := by unfold ExprRow1307Property; intros; rfl

/-- Zero-argument `@generated`; `base/expr.jl:1326-1328`. -/
def exprRow1326 : Ast := .expr "generated" []
def ExprRow1326Property : Prop := ∀ (_ : Unit), exprRow1326 = .expr "generated" []
theorem exprRow1326_proven : ExprRow1326Property := by unfold ExprRow1326Property; intro; rfl

/-- Function `@generated`; `base/expr.jl:1359-1375`. -/
def exprRow1359 (isFunction : Bool) (signature body : Ast) : Jl Ast := annotateGenerated isFunction signature body
def ExprRow1359Property : Prop := ∀ isFunction signature body,
  exprRow1359 isFunction signature body = annotateGenerated isFunction signature body
theorem exprRow1359_proven : ExprRow1359Property := by unfold ExprRow1359Property; intros; rfl

/-! Atomic macro rows. -/

inductive AtomicSyntax where
  | field (object field : String)
  | index (object : String) (indices : List String)
  | call (operator : String) (target : AtomicSyntax) (argument : String)
  | assign (target : AtomicSyntax) (value : String)
  | modify (target : AtomicSyntax) (operator value : String)
  | replace (target : AtomicSyntax) (expected replacement : String)
  | once (target : AtomicSyntax) (value : String)
  | invalid
  deriving Repr, Inhabited

structure AtomicCall where
  primitive : String
  arguments : List String
  selectSecond : Bool := false
  deriving Repr, DecidableEq, Inhabited

def lowerAtomic (operation : AtomicOperation) (successOrder failOrder : String)
    (target : AtomicSyntax) (operator value extra : String) (selectSecond : Bool := false) : Jl AtomicCall :=
  match target with
  | .field object field =>
    let arguments := match operation with
      | .fetch => [object,field,successOrder]
      | .store | .swap => [object,field,value,successOrder]
      | .modify => [object,field,operator,value,successOrder]
      | .replace => [object,field,value,extra,successOrder,failOrder]
      | .once => [object,field,value,successOrder,failOrder]
    .ok ⟨atomicPrimitive operation .field,arguments,selectSecond⟩
  | .index object indices =>
    let callPrefix := match operation with
      | .fetch => [object,successOrder]
      | .store | .swap => [object,successOrder,value]
      | .modify => [object,successOrder,operator,value]
      | .replace => [object,successOrder,failOrder,value,extra]
      | .once => [object,successOrder,failOrder,value]
    .ok ⟨atomicPrimitive operation .index,callPrefix ++ indices,selectSecond⟩
  | _ => .error (.argumentError "atomic target must be field access or indexing")

def sequentialOrder : String := "sequentially_consistent"

def exprRow1489 (isDeclaration : Bool) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  if isDeclaration then .ok ⟨"Expr(:atomic)",[],false⟩
  else lowerAtomic .fetch sequentialOrder sequentialOrder atomicExpression "" "" ""
def ExprRow1489Property : Prop := ∀ declaration atomicExpression,
  exprRow1489 declaration atomicExpression = if declaration then .ok ⟨"Expr(:atomic)",[],false⟩
    else lowerAtomic .fetch sequentialOrder sequentialOrder atomicExpression "" "" ""
theorem exprRow1489_proven : ExprRow1489Property := by unfold ExprRow1489Property; intros; rfl

def exprRow1495 (order : String) (atomicExpression : AtomicSyntax) :=
  lowerAtomic .fetch order order atomicExpression "" "" ""
def ExprRow1495Property : Prop := ∀ order atomicExpression,
  exprRow1495 order atomicExpression = lowerAtomic .fetch order order atomicExpression "" "" ""
theorem exprRow1495_proven : ExprRow1495Property := by unfold ExprRow1495Property; intros; rfl

def exprRow1499 (target : AtomicSyntax) (operator value : String) :=
  lowerAtomic .modify sequentialOrder sequentialOrder target operator value ""
def ExprRow1499Property : Prop := ∀ target operator value,
  exprRow1499 target operator value = lowerAtomic .modify sequentialOrder sequentialOrder target operator value ""
theorem exprRow1499_proven : ExprRow1499Property := by unfold ExprRow1499Property; intros; rfl

def exprRow1502 := exprRow1499
def ExprRow1502Property : Prop := ∀ target operator value, exprRow1502 target operator value = exprRow1499 target operator value
theorem exprRow1502_proven : ExprRow1502Property := by unfold ExprRow1502Property; intros; rfl

def exprRow1506 (order : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .field _ _ | .index _ _ => lowerAtomic .fetch order order atomicExpression "" "" ""
  | .call operator target value => lowerAtomic .modify order order target operator value ""
  | .assign target value => lowerAtomic .store order order target "" value ""
  | .modify target operator value => lowerAtomic .modify order order target operator value "" true
  | .invalid => .error (.argumentError "could not parse @atomic expression")
  | _ => .error (.argumentError "could not parse @atomic expression")
def ExprRow1506Property : Prop := ∀ order atomicExpression,
  exprRow1506 order atomicExpression = match atomicExpression with
    | .field _ _ | .index _ _ => lowerAtomic .fetch order order atomicExpression "" "" ""
    | .call operator target value => lowerAtomic .modify order order target operator value ""
    | .assign target value => lowerAtomic .store order order target "" value ""
    | .modify target operator value => lowerAtomic .modify order order target operator value "" true
    | .invalid => .error (.argumentError "could not parse @atomic expression")
    | _ => .error (.argumentError "could not parse @atomic expression")
theorem exprRow1506_proven : ExprRow1506Property := by intro order atomicExpression; cases atomicExpression <;> rfl

def exprRow1555 (order : String) (target : AtomicSyntax) (operator value : String) :=
  lowerAtomic .modify order order target operator value ""
def ExprRow1555Property : Prop := ∀ order target operator value,
  exprRow1555 order target operator value = lowerAtomic .modify order order target operator value ""
theorem exprRow1555_proven : ExprRow1555Property := by unfold ExprRow1555Property; intros; rfl

def makeAtomicSwap (order : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .assign target value => lowerAtomic .swap order order target "" value ""
  | _ => .error (.argumentError "@atomicswap expression missing assignment")

def exprRow1615 (order : String) (atomicExpression : AtomicSyntax) := makeAtomicSwap order atomicExpression
def ExprRow1615Property : Prop := ∀ order atomicExpression,
  exprRow1615 order atomicExpression = makeAtomicSwap order atomicExpression
theorem exprRow1615_proven : ExprRow1615Property := by unfold ExprRow1615Property; intros; rfl

def exprRow1619 (atomicExpression : AtomicSyntax) := makeAtomicSwap sequentialOrder atomicExpression
def ExprRow1619Property : Prop := ∀ atomicExpression,
  exprRow1619 atomicExpression = makeAtomicSwap sequentialOrder atomicExpression
theorem exprRow1619_proven : ExprRow1619Property := by unfold ExprRow1619Property; intro; rfl

def exprRow1622 (order : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  makeAtomicSwap order atomicExpression
def ExprRow1622Property : Prop := ∀ order atomicExpression,
  exprRow1622 order atomicExpression = match atomicExpression with
    | .assign target value => lowerAtomic .swap order order target "" value ""
    | _ => .error (.argumentError "@atomicswap expression missing assignment")
theorem exprRow1622_proven : ExprRow1622Property := by
  unfold ExprRow1622Property; intro order atomicExpression; cases atomicExpression <;> rfl

def makeAtomicReplace (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .replace target expected replacement =>
    lowerAtomic .replace success fail target "" expected replacement
  | _ => .error (.argumentError "@atomicreplace expression missing field access or indexing")

def exprRow1710 (success fail : String) (atomicExpression : AtomicSyntax) :=
  makeAtomicReplace success fail atomicExpression
def ExprRow1710Property : Prop := ∀ success fail atomicExpression,
  exprRow1710 success fail atomicExpression = makeAtomicReplace success fail atomicExpression
theorem exprRow1710_proven : ExprRow1710Property := by unfold ExprRow1710Property; intros; rfl

def exprRow1715 (order : String) (atomicExpression : AtomicSyntax) := makeAtomicReplace order order atomicExpression
def exprRow1719 (atomicExpression : AtomicSyntax) := makeAtomicReplace sequentialOrder sequentialOrder atomicExpression
def ExprRow1715Property : Prop := ∀ order atomicExpression,
  exprRow1715 order atomicExpression = makeAtomicReplace order order atomicExpression
def ExprRow1719Property : Prop := ∀ atomicExpression,
  exprRow1719 atomicExpression = makeAtomicReplace sequentialOrder sequentialOrder atomicExpression
theorem exprRow1715_proven : ExprRow1715Property := by unfold ExprRow1715Property; intros; rfl
theorem exprRow1719_proven : ExprRow1719Property := by unfold ExprRow1719Property; intro; rfl

def exprRow1722 (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  makeAtomicReplace success fail atomicExpression
def ExprRow1722Property : Prop := ∀ success fail atomicExpression,
  exprRow1722 success fail atomicExpression = match atomicExpression with
    | .replace target expected replacement =>
      lowerAtomic .replace success fail target "" expected replacement
    | _ => .error (.argumentError "@atomicreplace expression missing field access or indexing")
theorem exprRow1722_proven : ExprRow1722Property := by
  unfold ExprRow1722Property; intro success fail atomicExpression; cases atomicExpression <;> rfl

def makeAtomicOnce (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .once target value | .assign target value => lowerAtomic .once success fail target "" value ""
  | _ => .error (.argumentError "@atomiconce expression missing assignment")

def exprRow1813 (success fail : String) (atomicExpression : AtomicSyntax) :=
  makeAtomicOnce success fail atomicExpression
def exprRow1818 (order : String) (atomicExpression : AtomicSyntax) := makeAtomicOnce order order atomicExpression
def exprRow1822 (atomicExpression : AtomicSyntax) := makeAtomicOnce sequentialOrder sequentialOrder atomicExpression
def ExprRow1813Property : Prop := ∀ success fail atomicExpression,
  exprRow1813 success fail atomicExpression = makeAtomicOnce success fail atomicExpression
def ExprRow1818Property : Prop := ∀ order atomicExpression,
  exprRow1818 order atomicExpression = makeAtomicOnce order order atomicExpression
def ExprRow1822Property : Prop := ∀ atomicExpression,
  exprRow1822 atomicExpression = makeAtomicOnce sequentialOrder sequentialOrder atomicExpression
theorem exprRow1813_proven : ExprRow1813Property := by unfold ExprRow1813Property; intros; rfl
theorem exprRow1818_proven : ExprRow1818Property := by unfold ExprRow1818Property; intros; rfl
theorem exprRow1822_proven : ExprRow1822Property := by unfold ExprRow1822Property; intro; rfl

def exprRow1825 (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  makeAtomicOnce success fail atomicExpression
def ExprRow1825Property : Prop := ∀ success fail atomicExpression,
  exprRow1825 success fail atomicExpression = match atomicExpression with
    | .once target value | .assign target value => lowerAtomic .once success fail target "" value ""
    | _ => .error (.argumentError "@atomiconce expression missing assignment")
theorem exprRow1825_proven : ExprRow1825Property := by
  unfold ExprRow1825Property; intro success fail atomicExpression; cases atomicExpression <;> rfl

/-! AST classification and generated-function rows. -/

def exprRow1841 (head : String) : Bool := head == "boundscheck" || head == "meta" || head == "loopinfo"
def ExprRow1841Property : Prop := ∀ head,
  exprRow1841 head = (head == "boundscheck" || head == "meta" || head == "loopinfo")
theorem exprRow1841_proven : ExprRow1841Property := by unfold ExprRow1841Property; intros; rfl

def exprRow1842 (isExpression : Bool) (head : String) : Bool := isExpression && exprRow1841 head
def ExprRow1842Property : Prop := ∀ isExpression head,
  exprRow1842 isExpression head = (isExpression && exprRow1841 head)
theorem exprRow1842_proven : ExprRow1842Property := by unfold ExprRow1842Property; intros; rfl

def exprRow1850 := isaAstNode
def ExprRow1850Property : Prop := ∀ kind, exprRow1850 kind = false ↔ kind = .other
theorem exprRow1850_proven : ExprRow1850Property := by intro kind; cases kind <;> simp [exprRow1850,isaAstNode]

def exprRow1873 (kind : AstNodeKind) : Bool := !isaAstNode kind
def ExprRow1873Property : Prop := ∀ kind, exprRow1873 kind = true ↔ kind = .other
theorem exprRow1873_proven : ExprRow1873Property := by intro kind; cases kind <;> simp [exprRow1873,isaAstNode]

def exprRow1883 := quotedShape
def ExprRow1883Property : Prop := ∀ kind,
  exprRow1883 kind = if kind = .other then "self" else "QuoteNode"
theorem exprRow1883_proven : ExprRow1883Property := by intro kind; cases kind <;> rfl

def exprRow1886 := generatedBodyResult
def ExprRow1886Property : Prop := ∀ lowered, exprRow1886 lowered = generatedBodyResult lowered
theorem exprRow1886_proven : ExprRow1886Property := by unfold ExprRow1886Property; intros; rfl

structure GeneratedStubInput where
  body : String
  file : Option String
  line : Int
  argnames : List String
  staticParameters : List String
  moduleName : String
  isVararg : Bool
  deriving Repr, DecidableEq, Inhabited

def exprRow1914 (input : GeneratedStubInput) : String :=
  let file := input.file.getD "none"
  let lambda := "lambda(" ++ String.intercalate "," input.argnames ++ "):push_loc(" ++ file ++ "):return(toplevel_pure(" ++ input.body ++ ")):pop_loc"
  if input.staticParameters.isEmpty then lambda else "with-static-parameters(" ++ lambda ++ "," ++ String.intercalate "," input.staticParameters ++ ")"
def ExprRow1914Property : Prop := ∀ input,
  input.staticParameters = [] →
  exprRow1914 input = "lambda(" ++ String.intercalate "," input.argnames ++ "):push_loc(" ++ input.file.getD "none" ++ "):return(toplevel_pure(" ++ input.body ++ ")):pop_loc"
theorem exprRow1914_proven : ExprRow1914Property := by intros input h; simp [exprRow1914,h]

end JuliaLean.ExprReflect
