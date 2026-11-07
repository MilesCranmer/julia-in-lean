import JuliaLean.base.expr
import JuliaLean.Proofs.base.expr.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

def ExprRow3Property : Prop := ∀ expression heads,
  exprRow3 expression heads = match expression with | .expr head _ => heads.contains head | _ => false

theorem exprRow3_proven : ExprRow3Property := by
  unfold ExprRow3Property
  intro expression heads
  cases expression <;> simp [exprRow3, isExpr]

def ExprRow4Property : Prop := ∀ expression heads arity,
  exprRow4 expression heads arity = match expression with
    | .expr head arguments => heads.contains head && arguments.length == arity | _ => false

theorem exprRow4_proven : ExprRow4Property := by unfold ExprRow4Property; intro expression heads arity; cases expression <;> rfl

def ExprRow18Property : Prop := ∀ state, (exprRow18 state).2.next = state.next + 1

theorem exprRow18_proven : ExprRow18Property := by unfold ExprRow18Property; intro state; cases state; rfl

def ExprRow20Property : Prop := ∀ tag state,
  (exprRow20 tag state).1 = gensymTag (some tag) state.next

theorem exprRow20_proven : ExprRow20Property := by unfold ExprRow20Property; intros; rfl

def ExprRow22Property : Prop := ∀ tags state, (exprRow22 tags state).1.length = tags.length

theorem exprRow22_proven : ExprRow22Property := by intro tags; induction tags <;> simp [exprRow22, *]

def ExprRow23Property : Prop := ∀ tag state, exprRow23 tag state = exprRow20 tag state

theorem exprRow23_proven : ExprRow23Property := by unfold ExprRow23Property; intros; rfl

def ExprRow31Property : Prop := ∀ names state,
  (exprRow31 names state).1.map (·.1) = names

theorem exprRow31_proven : ExprRow31Property := by
  intro names state; simp [exprRow31]
  induction names generalizing state <;> simp [exprRow22, *]

def ExprRow42Property : Prop := ∀ expression head,
  exprRow42 expression head = match expression with | .expr actual _ => decide (actual = head) | _ => false

theorem exprRow42_proven : ExprRow42Property := by unfold ExprRow42Property; intro expression head; cases expression <;> simp [exprRow42,isExpr]

def ExprRow43Property : Prop := ∀ expression head arity,
  exprRow43 expression head arity = match expression with
    | .expr actual arguments => decide (actual = head) && arguments.length == arity | _ => false

theorem exprRow43_proven : ExprRow43Property := by unfold ExprRow43Property; intro expression head arity; cases expression <;> simp [exprRow43,isExpr]

/-! IR copy and equality rows. -/

def ExprRow45Property : Prop := ∀ fresh object, (exprRow45 fresh object).kind = .expr

theorem exprRow45_proven : ExprRow45Property := by unfold ExprRow45Property; intros; rfl

def ExprRow46Property : Prop := ∀ fresh node,
  (exprRow46 fresh node).edges = node.edges ∧
  (exprRow46 fresh node).values = node.values.map (copyOptionalIR fresh)

theorem exprRow46_proven : ExprRow46Property := by unfold ExprRow46Property; intros; exact ⟨rfl,rfl⟩

def ExprRow56Property : Prop := ∀ fresh node,
  (exprRow56 fresh node).values = node.values.map (copyOptionalIR fresh)

theorem exprRow56_proven : ExprRow56Property := by unfold ExprRow56Property; intros; rfl

def ExprRow69Property : Prop := ∀ fresh object,
  exprRow69 fresh object = match object.kind with
    | .expr | .phi | .phiC => copyIRObject fresh object
    | _ => object

theorem exprRow69_proven : ExprRow69Property := by unfold ExprRow69Property; intros; rfl

def ExprRow79Property : Prop := ∀ fresh arguments,
  exprRow79 fresh arguments = arguments.map (copyOptionalIR fresh)

theorem exprRow79_proven : ExprRow79Property := by unfold ExprRow79Property; intros; rfl

def ExprRow81Property : Prop := ∀ head arguments, exprRow81 head arguments = .expr head arguments

theorem exprRow81_proven : ExprRow81Property := by unfold ExprRow81Property; intros; rfl

def ExprRow84Property : Prop := ∀ fresh code,
  (exprRow84 fresh code).slotnames = code.slotnames ∧ (exprRow84 fresh code).code.length = code.code.length

theorem exprRow84_proven : ExprRow84Property := by intro fresh code; cases code <;> simp [exprRow84,copyCodeInfoFields]

def ExprRow99Property : Prop := ∀ left right, exprRow99 left right = isequalIRArg left right

theorem exprRow99_proven : ExprRow99Property := by unfold ExprRow99Property; intros; rfl

def ExprRow118Property : Prop := ∀ left right,
  exprRow118 left right = (left.length == right.length && (List.zip left right).all fun pair => isequalIRArg pair.1 pair.2)

theorem exprRow118_proven : ExprRow118Property := by unfold ExprRow118Property; intros; rfl

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

def ExprRow209Property : Prop := ∀ recursive legacy, exprRow209 recursive legacy = ⟨recursive,false,legacy⟩

theorem exprRow209_proven : ExprRow209Property := by unfold ExprRow209Property; intros; rfl

def ExprRow232Property : Prop := ∀ recursive legacy, exprRow232 recursive legacy = ⟨recursive,true,legacy⟩

theorem exprRow232_proven : ExprRow232Property := by unfold ExprRow232Property; intros; rfl

def ExprRow279Property : Prop := ∀ moduleName expression,
  exprRow279 moduleName expression = "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),true,true)"

theorem exprRow279_proven : ExprRow279Property := by unfold ExprRow279Property; intros; rfl

def ExprRow282Property : Prop := ∀ moduleName expression, exprRow282 moduleName expression = exprRow279 moduleName expression

theorem exprRow282_proven : ExprRow282Property := by unfold ExprRow282Property; intros; rfl

def ExprRow291Property : Prop := ∀ moduleName expression,
  exprRow291 moduleName expression = "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),false,true)"

theorem exprRow291_proven : ExprRow291Property := by unfold ExprRow291Property; intros; rfl

def ExprRow294Property : Prop := ∀ moduleName expression, exprRow294 moduleName expression = exprRow291 moduleName expression

theorem exprRow294_proven : ExprRow294Property := by unfold ExprRow294Property; intros; rfl

/-! Annotation and effect rows. -/

def ExprRow389Property : Prop := ∀ isFunction, exprRow389 isFunction = annotationTag "inline" isFunction

theorem exprRow389_proven : ExprRow389Property := by unfold ExprRow389Property; intros; rfl

def ExprRow466Property : Prop := ∀ isFunction, exprRow466 isFunction = annotationTag "noinline" isFunction

theorem exprRow466_proven : ExprRow466Property := by unfold ExprRow466Property; intros; rfl

def ExprRow505Property : Prop := ∀ setting isExpression, exprRow505 setting isExpression = constpropShape setting isExpression

theorem exprRow505_proven : ExprRow505Property := by unfold ExprRow505Property; intros; rfl

def ExprRow510Property : Prop := ∀ setting, exprRow510 setting = constpropShape setting false

theorem exprRow510_proven : ExprRow510Property := by unfold ExprRow510Property; intros; rfl

def ExprRow515Property : Prop := ∀ setting, exprRow515 setting = constpropTag setting

theorem exprRow515_proven : ExprRow515Property := by unfold ExprRow515Property; intros; rfl

def ExprRow896Property : Prop := ∀ target, exprRow896 target = assumeEffectsShape target

theorem exprRow896_proven : ExprRow896Property := by unfold ExprRow896Property; intros; rfl

def ExprRow938Property : Prop := ∀ settings, (effectBits (exprRow938 settings)).length = 11

theorem exprRow938_proven : ExprRow938Property := by unfold ExprRow938Property; intros; simp [effectBits]

def ExprRow962Property : Prop := ∀ override, exprRow962 override = override

theorem exprRow962_proven : ExprRow962Property := by unfold ExprRow962Property; intros; rfl

def ExprRow995Property : Prop := ∀ override setting value,
  exprRow995 override setting value = applyEffectSetting override setting value

theorem exprRow995_proven : ExprRow995Property := by unfold ExprRow995Property; intros; rfl

def ExprRow1035Property : Prop := ∀ override, (exprRow1035 override).length = 11

theorem exprRow1035_proven : ExprRow1035Property := by unfold ExprRow1035Property; intro; rfl

def ExprRow1051Property : Prop := ∀ override, exprRow1051 (effectBits override) = override

theorem exprRow1051_proven : ExprRow1051Property := by unfold ExprRow1051Property; intro override; cases override; rfl

def ExprRow1066Property : Prop := ∀ override, exprRow1066 override = effectBits override

theorem exprRow1066_proven : ExprRow1066Property := by unfold ExprRow1066Property; intros; rfl

def ExprRow1111Property : Prop := ∀ value, exprRow1111 value = if value then "pushmeta:nospecializeinfer" else "identity"

theorem exprRow1111_proven : ExprRow1111Property := by unfold ExprRow1111Property; intros; rfl

def ExprRow1148Property : Prop := ∀ value, exprRow1148 value = if value then ["inline","propagate_inbounds"] else []

theorem exprRow1148_proven : ExprRow1148Property := by unfold ExprRow1148Property; intros; rfl

def ExprRow1161Property : Prop := ∀ value, exprRow1161 value = if value then ["polly"] else []

theorem exprRow1161_proven : ExprRow1161Property := by unfold ExprRow1161Property; intros; rfl

/-! Metadata and line-number rows. -/

/-- Generic `unwrap_macrocalls`; `base/expr.jl:1167`. -/

def ExprRow1167Property : Prop := ∀ value, exprRow1167 value = value

theorem exprRow1167_proven : ExprRow1167Property := by unfold ExprRow1167Property; intro; rfl

/-- Expr `unwrap_macrocalls`; `base/expr.jl:1168-1174`. -/

def ExprRow1168Property : Prop := ∀ value, exprRow1168 value = CoverageAst.unwrapMacrocall value

theorem exprRow1168_proven : ExprRow1168Property := by unfold ExprRow1168Property; intro; rfl

def ExprRow1176Property : Prop := ∀ body tag,
  (exprRow1176 body tag).tags = body.tags ++ [tag]

theorem exprRow1176_proven : ExprRow1176Property := by unfold ExprRow1176Property; intros; rfl

def ExprRow1189Property : Prop := ∀ body tag, exprRow1189 body tag = getMetaTag body tag true

theorem exprRow1189_proven : ExprRow1189Property := by unfold ExprRow1189Property; intros; rfl

/-- `peekmeta`; `base/expr.jl:1190`. -/

def ExprRow1190Property : Prop := ∀ body tag, exprRow1190 body tag = getMetaTag body tag false

theorem exprRow1190_proven : ExprRow1190Property := by unfold ExprRow1190Property; intros; rfl

/-- Expr `_getmeta`; `base/expr.jl:1192-1195`. -/

def ExprRow1192Property : Prop := ∀ body tag delete, exprRow1192 body tag delete = getMetaTag body tag delete

theorem exprRow1192_proven : ExprRow1192Property := by unfold ExprRow1192Property; intros; rfl

/-- Atomic `_getmeta` fallback; `base/expr.jl:1196`. -/

def ExprRow1196Property : Prop := ∀ body, exprRow1196 body = (none,body)

theorem exprRow1196_proven : ExprRow1196Property := by unfold ExprRow1196Property; intro; rfl

/-- Array `_getmeta`; `base/expr.jl:1197-1213`. -/

def ExprRow1197Property : Prop := ∀ body tag delete, exprRow1197 body tag delete = getMetaTag body tag delete

theorem exprRow1197_proven : ExprRow1197Property := by unfold ExprRow1197Property; intros; rfl

/-- `findmetaarg`; `base/expr.jl:1216-1225`. -/

def ExprRow1216Property : Prop := ∀ arguments tag,
  exprRow1216 arguments tag = match arguments.findIdx? (· == tag) with | none => 0 | some index => index + 1

theorem exprRow1216_proven : ExprRow1216Property := by unfold ExprRow1216Property; intros; rfl

/-- `annotate_meta_def_or_block`; `base/expr.jl:1227-1240`. -/

def ExprRow1227Property : Prop := ∀ isFunction tag, exprRow1227 isFunction tag = annotationTag tag isFunction

theorem exprRow1227_proven : ExprRow1227Property := by unfold ExprRow1227Property; intros; rfl

/-- `is_short_function_def`; `base/expr.jl:1242-1250`. -/

def ExprRow1242Property : Prop := ∀ value,
  exprRow1242 value = match value with | .expr "=" (.args (.expr "call" _) _) => true | _ => false

theorem exprRow1242_proven : ExprRow1242Property := by unfold ExprRow1242Property; intro value; cases value <;> rfl

/-- `is_function_def`; `base/expr.jl:1251-1252`. -/

def ExprRow1251Property : Prop := ∀ value, exprRow1251 value = CoverageAst.isFunctionDef value

theorem exprRow1251_proven : ExprRow1251Property := by unfold ExprRow1251Property; intro; rfl

/-- Expr `findmeta`; `base/expr.jl:1254-1261`. -/

def ExprRow1254Property : Prop := ∀ body,
  exprRow1254 false body = .error (.argumentError "not a function expression")

theorem exprRow1254_proven : ExprRow1254Property := by unfold ExprRow1254Property; intro; rfl

/-- Array `findmeta`; `base/expr.jl:1263`. -/

def ExprRow1263Property : Prop := ∀ body, (exprRow1263 body).2 = body

theorem exprRow1263_proven : ExprRow1263Property := by unfold ExprRow1263Property; intro; rfl

/-- `findmeta_block`; `base/expr.jl:1265-1280`. -/

def ExprRow1265Property : Prop := ∀ body predicate,
  exprRow1265 body predicate = match body.tags.findIdx? (fun tag => predicate [tag]) with | none => 0 | some index => index + 1

theorem exprRow1265_proven : ExprRow1265Property := by unfold ExprRow1265Property; intros; rfl

/-- `remove_linenums!`; `base/expr.jl:1287-1304`. -/

def ExprRow1287Property : Prop := ∀ value, exprRow1287 value = CoverageAst.removeLineNums value

theorem exprRow1287_proven : ExprRow1287Property := by unfold ExprRow1287Property; intro; rfl

/-- Atomic `replace_linenums!`; `base/expr.jl:1306`. -/

def ExprRow1306Property : Prop := ∀ value line, exprRow1306 value line = value

theorem exprRow1306_proven : ExprRow1306Property := by unfold ExprRow1306Property; intros; rfl

/-- Expr `replace_linenums!`; `base/expr.jl:1307-1324`. -/

def ExprRow1307Property : Prop := ∀ value line, exprRow1307 value line = CoverageAst.replaceLineNums line value

theorem exprRow1307_proven : ExprRow1307Property := by unfold ExprRow1307Property; intros; rfl

/-- Zero-argument `@generated`; `base/expr.jl:1326-1328`. -/

def ExprRow1326Property : Prop := ∀ (_ : Unit), exprRow1326 = .expr "generated" []

theorem exprRow1326_proven : ExprRow1326Property := by unfold ExprRow1326Property; intro; rfl

/-- Function `@generated`; `base/expr.jl:1359-1375`. -/

def ExprRow1359Property : Prop := ∀ isFunction signature body,
  exprRow1359 isFunction signature body = annotateGenerated isFunction signature body

theorem exprRow1359_proven : ExprRow1359Property := by unfold ExprRow1359Property; intros; rfl

/-! Atomic macro rows. -/

def ExprRow1489Property : Prop := ∀ declaration atomicExpression,
  exprRow1489 declaration atomicExpression = if declaration then .ok ⟨"Expr(:atomic)",[],false⟩
    else lowerAtomic .fetch sequentialOrder sequentialOrder atomicExpression "" "" ""

theorem exprRow1489_proven : ExprRow1489Property := by unfold ExprRow1489Property; intros; rfl

def ExprRow1495Property : Prop := ∀ order atomicExpression,
  exprRow1495 order atomicExpression = lowerAtomic .fetch order order atomicExpression "" "" ""

theorem exprRow1495_proven : ExprRow1495Property := by unfold ExprRow1495Property; intros; rfl

def ExprRow1499Property : Prop := ∀ target operator value,
  exprRow1499 target operator value = lowerAtomic .modify sequentialOrder sequentialOrder target operator value ""

theorem exprRow1499_proven : ExprRow1499Property := by unfold ExprRow1499Property; intros; rfl

def ExprRow1502Property : Prop := ∀ target operator value, exprRow1502 target operator value = exprRow1499 target operator value

theorem exprRow1502_proven : ExprRow1502Property := by unfold ExprRow1502Property; intros; rfl

def ExprRow1506Property : Prop := ∀ order atomicExpression,
  exprRow1506 order atomicExpression = match atomicExpression with
    | .field _ _ | .index _ _ => lowerAtomic .fetch order order atomicExpression "" "" ""
    | .call operator target value => lowerAtomic .modify order order target operator value ""
    | .assign target value => lowerAtomic .store order order target "" value ""
    | .modify target operator value => lowerAtomic .modify order order target operator value "" true
    | .invalid => .error (.argumentError "could not parse @atomic expression")
    | _ => .error (.argumentError "could not parse @atomic expression")

theorem exprRow1506_proven : ExprRow1506Property := by intro order atomicExpression; cases atomicExpression <;> rfl

def ExprRow1555Property : Prop := ∀ order target operator value,
  exprRow1555 order target operator value = lowerAtomic .modify order order target operator value ""

theorem exprRow1555_proven : ExprRow1555Property := by unfold ExprRow1555Property; intros; rfl

def ExprRow1615Property : Prop := ∀ order atomicExpression,
  exprRow1615 order atomicExpression = makeAtomicSwap order atomicExpression

theorem exprRow1615_proven : ExprRow1615Property := by unfold ExprRow1615Property; intros; rfl

def ExprRow1619Property : Prop := ∀ atomicExpression,
  exprRow1619 atomicExpression = makeAtomicSwap sequentialOrder atomicExpression

theorem exprRow1619_proven : ExprRow1619Property := by unfold ExprRow1619Property; intro; rfl

def ExprRow1622Property : Prop := ∀ order atomicExpression,
  exprRow1622 order atomicExpression = match atomicExpression with
    | .assign target value => lowerAtomic .swap order order target "" value ""
    | _ => .error (.argumentError "@atomicswap expression missing assignment")

theorem exprRow1622_proven : ExprRow1622Property := by
  unfold ExprRow1622Property; intro order atomicExpression; cases atomicExpression <;> rfl

def ExprRow1710Property : Prop := ∀ success fail atomicExpression,
  exprRow1710 success fail atomicExpression = makeAtomicReplace success fail atomicExpression

theorem exprRow1710_proven : ExprRow1710Property := by unfold ExprRow1710Property; intros; rfl

def ExprRow1715Property : Prop := ∀ order atomicExpression,
  exprRow1715 order atomicExpression = makeAtomicReplace order order atomicExpression

def ExprRow1719Property : Prop := ∀ atomicExpression,
  exprRow1719 atomicExpression = makeAtomicReplace sequentialOrder sequentialOrder atomicExpression

theorem exprRow1715_proven : ExprRow1715Property := by unfold ExprRow1715Property; intros; rfl

theorem exprRow1719_proven : ExprRow1719Property := by unfold ExprRow1719Property; intro; rfl

def ExprRow1722Property : Prop := ∀ success fail atomicExpression,
  exprRow1722 success fail atomicExpression = match atomicExpression with
    | .replace target expected replacement =>
      lowerAtomic .replace success fail target "" expected replacement
    | _ => .error (.argumentError "@atomicreplace expression missing field access or indexing")

theorem exprRow1722_proven : ExprRow1722Property := by
  unfold ExprRow1722Property; intro success fail atomicExpression; cases atomicExpression <;> rfl

def ExprRow1813Property : Prop := ∀ success fail atomicExpression,
  exprRow1813 success fail atomicExpression = makeAtomicOnce success fail atomicExpression

def ExprRow1818Property : Prop := ∀ order atomicExpression,
  exprRow1818 order atomicExpression = makeAtomicOnce order order atomicExpression

def ExprRow1822Property : Prop := ∀ atomicExpression,
  exprRow1822 atomicExpression = makeAtomicOnce sequentialOrder sequentialOrder atomicExpression

theorem exprRow1813_proven : ExprRow1813Property := by unfold ExprRow1813Property; intros; rfl

theorem exprRow1818_proven : ExprRow1818Property := by unfold ExprRow1818Property; intros; rfl

theorem exprRow1822_proven : ExprRow1822Property := by unfold ExprRow1822Property; intro; rfl

def ExprRow1825Property : Prop := ∀ success fail atomicExpression,
  exprRow1825 success fail atomicExpression = match atomicExpression with
    | .once target value | .assign target value => lowerAtomic .once success fail target "" value ""
    | _ => .error (.argumentError "@atomiconce expression missing assignment")

theorem exprRow1825_proven : ExprRow1825Property := by
  unfold ExprRow1825Property; intro success fail atomicExpression; cases atomicExpression <;> rfl

/-! AST classification and generated-function rows. -/

def ExprRow1841Property : Prop := ∀ head,
  exprRow1841 head = (head == "boundscheck" || head == "meta" || head == "loopinfo")

theorem exprRow1841_proven : ExprRow1841Property := by unfold ExprRow1841Property; intros; rfl

def ExprRow1842Property : Prop := ∀ isExpression head,
  exprRow1842 isExpression head = (isExpression && exprRow1841 head)

theorem exprRow1842_proven : ExprRow1842Property := by unfold ExprRow1842Property; intros; rfl

def ExprRow1850Property : Prop := ∀ kind, exprRow1850 kind = false ↔ kind = .other

theorem exprRow1850_proven : ExprRow1850Property := by intro kind; cases kind <;> simp [exprRow1850,isaAstNode]

def ExprRow1873Property : Prop := ∀ kind, exprRow1873 kind = true ↔ kind = .other

theorem exprRow1873_proven : ExprRow1873Property := by intro kind; cases kind <;> simp [exprRow1873,isaAstNode]

def ExprRow1883Property : Prop := ∀ kind,
  exprRow1883 kind = if kind = .other then "self" else "QuoteNode"

theorem exprRow1883_proven : ExprRow1883Property := by intro kind; cases kind <;> rfl

def ExprRow1886Property : Prop := ∀ lowered, exprRow1886 lowered = generatedBodyResult lowered

theorem exprRow1886_proven : ExprRow1886Property := by unfold ExprRow1886Property; intros; rfl

def ExprRow1914Property : Prop := ∀ input,
  input.staticParameters = [] →
  exprRow1914 input = "lambda(" ++ String.intercalate "," input.argnames ++ "):push_loc(" ++ input.file.getD "none" ++ "):return(toplevel_pure(" ++ input.body ++ ")):pop_loc"

theorem exprRow1914_proven : ExprRow1914Property := by intros input h; simp [exprRow1914,h]

end JuliaLean.ExprReflect
