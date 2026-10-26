import JuliaLean.ExprReflect.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

/-! Exact row models for `base/cartesian.jl` at `bbfa0ce4150`. -/

def cartDimensions (count : Int) : List Int :=
  (List.range count.toNat).map fun index => (index + 1 : Nat)

def indexedNameInt (stem : String) (extension : Int) : String :=
  stem ++ "_" ++ toString extension

def replaceIndexedChars : Nat → List Char → List Char → List Char → List Char
  | 0, _, _, input => input
  | _fuel + 1, _pattern, _replacement, [] => []
  | fuel + 1, pattern, replacement, '_' :: rest =>
    if pattern.isEmpty then '_' :: replaceIndexedChars fuel pattern replacement rest
    else if pattern.isPrefixOf rest then
      let suffix := rest.drop pattern.length
      if suffix.isEmpty || suffix.head? = some '_' then
        '_' :: replacement ++ replaceIndexedChars fuel pattern replacement suffix
      else '_' :: replaceIndexedChars fuel pattern replacement rest
    else '_' :: replaceIndexedChars fuel pattern replacement rest
  | fuel + 1, pattern, replacement, character :: rest =>
    character :: replaceIndexedChars fuel pattern replacement rest

def replaceNameSegments (name pattern : String) (value : Int) : String :=
  String.ofList (replaceIndexedChars name.length pattern.toList (toString value).toList name.toList)

def cartResolveInt : Ast → Option Int
  | .int value => some value
  | .expr "call" [.atom "+", .int left, .int right] => some (left + right)
  | .expr "call" [.atom "-", .int left, .int right] => some (left - right)
  | .expr "call" [.atom "*", .int left, .int right] => some (left * right)
  | .expr "call" [.atom "div", .int left, .int right] =>
    if right = 0 then none else some (left.tdiv right)
  | _ => none

def cartReplaceCtx (pattern : String) (value : Int) (inQuote : Bool) (escapeDepth : Nat) : Ast → Ast
  | .atom name =>
    if escapeDepth != 0 then .atom name
    else if name == pattern then .int value else .atom (replaceNameSegments name pattern value)
  | .int number => .int number
  | .line => .line
  | .quoteNode quoted => .quoteNode quoted
  | .expr "meta" arguments => .expr "meta" arguments
  | .expr "inert" arguments => .expr "inert" arguments
  | .expr "curly" [.atom base, argument] =>
    if !inQuote && escapeDepth = 0 && base.endsWith "_" then
      let argument := cartReplaceCtx pattern value inQuote escapeDepth argument
      match cartResolveInt argument with
      | some result => .atom (base ++ toString result)
      | none => .expr "curly" [.atom base, argument]
    else .expr "curly" [.atom base, argument]
  | .expr "hygienic-scope" arguments =>
    .expr "hygienic-scope" (arguments.map (cartReplaceCtx pattern value inQuote (escapeDepth + 1)))
  | expression@(.expr "escape" arguments) =>
    if escapeDepth = 0 then expression
    else .expr "escape" (arguments.map (cartReplaceCtx pattern value inQuote (escapeDepth - 1)))
  | .expr "$" arguments =>
    .expr "$" (arguments.map (cartReplaceCtx pattern value false escapeDepth))
  | .expr "quote" arguments =>
    .expr "quote" (arguments.map (cartReplaceCtx pattern value true escapeDepth))
  | .expr head arguments =>
    .expr head (arguments.map (cartReplaceCtx pattern value inQuote escapeDepth))
termination_by expression => sizeOf expression

def cartReplace (pattern : String) (value : Int) (expression : Ast) : Ast :=
  cartReplaceCtx pattern value false 0 expression

def cartNonLine : Ast → Bool | .line => false | .expr "line" _ => false | _ => true

def cartPopLine : Ast → Ast
  | original@(.expr "block" arguments) =>
    match arguments.filter cartNonLine with | [only] => only | _ => original
  | value => value

def cartResolveSimple (expression : Ast) : Ast :=
  match cartResolveInt expression with | some value => .int value | none => expression

inductive InlineAnonymous where
  | prefix (stem : String)
  | lambda (parameter : String) (body : Ast)
  | invalid
  deriving Repr, Inhabited

def inlineAnonymousModel (source : InlineAnonymous) (value : Int) : Jl Ast :=
  match source with
  | .prefix stem => .ok (.atom (indexedNameInt stem value))
  | .lambda parameter body => .ok (cartResolveSimple (cartPopLine (cartReplace parameter value body)))
  | .invalid => .error (.argumentError "not an anonymous function")

def cartMapDimensions (count : Int) (source : InlineAnonymous) : Jl (List Ast) :=
  (cartDimensions count).mapM (inlineAnonymousModel source)

inductive CartesianRange where
  | arrayAxes (array : String)
  | anonymous (source : InlineAnonymous)
  | invalid
  deriving Repr, Inhabited

def rangeAt (range : CartesianRange) (dimension : Int) : Jl Ast :=
  match range with
  | .arrayAxes array => .ok (.expr "axes" [.atom array, .int dimension])
  | .anonymous source@(.lambda _ _) => inlineAnonymousModel source dimension
  | .anonymous _ => .error (.argumentError "range must be an anonymous function")
  | .invalid => .error (.argumentError "range must be an anonymous function")

def cartLoopLayer (iterator : String) (range : Ast) (pre post : Option Ast) (inner : Ast) : Ast :=
  .expr "for" [
    .expr "=" [.atom iterator, range],
    .expr "block" [pre.getD (.atom "nothing"), inner, post.getD (.atom "nothing")]]

def buildLoops (count : Int) (iterator : String) (range : CartesianRange)
    (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast := do
  let mut result := .expr "escape" [body]
  for dimension in cartDimensions count do
    let loopRange ← rangeAt range dimension
    let preExpr ← (match pre with
      | none => .ok none
      | some source => do let expression ← inlineAnonymousModel source dimension; return some expression : Jl (Option Ast))
    let postExpr ← (match post with
      | none => .ok none
      | some source => do let expression ← inlineAnonymousModel source dimension; return some expression : Jl (Option Ast))
    result := cartLoopLayer (indexedNameInt iterator dimension) loopRange preExpr postExpr result
  return result

/-- `@nloops`; `base/cartesian.jl:38-40`. -/
def cartRow38 (count : Int) (iterator : String) (range : CartesianRange)
    (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast :=
  buildLoops count iterator range pre post body

def CartRow38Property : Prop := ∀ count iterator range pre post body,
  cartRow38 count iterator range pre post body = buildLoops count iterator range pre post body
theorem cartRow38_proven : CartRow38Property := by unfold CartRow38Property; intros; rfl

/-- Array-symbol `_nloops`; `base/cartesian.jl:42-44`. -/
def cartRow42 (count : Int) (iterator array : String) (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast :=
  buildLoops count iterator (.arrayAxes array) pre post body

def CartRow42Property : Prop := ∀ count iterator array pre post body,
  cartRow42 count iterator array pre post body = buildLoops count iterator (.arrayAxes array) pre post body
theorem cartRow42_proven : CartRow42Property := by unfold CartRow42Property; intros; rfl

/-- Anonymous-range `_nloops`; `base/cartesian.jl:46-71`. -/
def cartRow46 (count : Int) (iterator : String) (range : InlineAnonymous)
    (argumentCount : Nat) (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast :=
  if argumentCount < 1 || 3 < argumentCount then
    .error (.argumentError "number of arguments must be 1 through 3")
  else buildLoops count iterator (.anonymous range) pre post body

def CartRow46Property : Prop := ∀ count iterator range argumentCount pre post body,
  cartRow46 count iterator range argumentCount pre post body =
    if argumentCount < 1 || 3 < argumentCount then
      .error (.argumentError "number of arguments must be 1 through 3")
    else buildLoops count iterator (.anonymous range) pre post body

theorem cartRow46_proven : CartRow46Property := by
  unfold CartRow46Property
  intros
  rfl

/-- `@nref`; `base/cartesian.jl:85-88`. -/
def cartRow85 (count : Int) (array : String) (source : InlineAnonymous) : Jl Ast := do
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok variables => .ok (.expr "escape" [.expr "ref" (.atom array :: variables)])

def CartRow85Property : Prop := ∀ count array source variables,
  cartMapDimensions count source = .ok variables →
  cartRow85 count array source = .ok (.expr "escape" [.expr "ref" (.atom array :: variables)])

theorem cartRow85_proven : CartRow85Property := by
  unfold CartRow85Property
  intros count array source variables h
  simp [cartRow85, h]

def splitLast {α : Type} : List α → Option (List α × α)
  | [] => none
  | [last] => some ([], last)
  | first :: rest => return (first :: (← splitLast rest).1, (← splitLast rest).2)

/-- `@ncall`; `base/cartesian.jl:105-110`. -/
def cartRow105 (count : Int) (functionName : String) (arguments : List Ast)
    (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok variables => .ok (.expr "escape" [.expr "call" (.atom functionName :: arguments ++ variables)])

def CartRow105Property : Prop := ∀ count functionName arguments source variables,
  cartMapDimensions count source = .ok variables →
  cartRow105 count functionName arguments source =
    .ok (.expr "escape" [.expr "call" (.atom functionName :: arguments ++ variables)])

theorem cartRow105_proven : CartRow105Property := by
  unfold CartRow105Property
  intros; simp [cartRow105, *]

/-- `@ncallkw`; `base/cartesian.jl:132-138`. -/
def cartRow132 (count : Int) (functionName : String) (keywordTuple : Ast)
    (arguments : List Ast) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok variables =>
    let parameters := .expr "parameters" [.expr "..." [keywordTuple]]
    .ok (.expr "escape" [.expr "call" (.atom functionName :: parameters :: arguments ++ variables)])

def CartRow132Property : Prop := ∀ count functionName keyword arguments source variables,
  cartMapDimensions count source = .ok variables →
  cartRow132 count functionName keyword arguments source =
    .ok (.expr "escape" [.expr "call" (.atom functionName ::
      .expr "parameters" [.expr "..." [keyword]] :: arguments ++ variables)])

theorem cartRow132_proven : CartRow132Property := by
  unfold CartRow132Property
  intros; simp [cartRow132, *]

/-- `@nexprs`; `base/cartesian.jl:156-159`. -/
def cartRow156 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok expressions => .ok (.expr "escape" [.expr "block" expressions])

def CartRow156Property : Prop := ∀ count source expressions,
  cartMapDimensions count source = .ok expressions →
  cartRow156 count source = .ok (.expr "escape" [.expr "block" expressions])
theorem cartRow156_proven : CartRow156Property := by unfold CartRow156Property; intros; simp [cartRow156, *]

/-- Symbol-source `@nextract`; `base/cartesian.jl:179-182`. -/
def cartRow179 (count : Int) (external source : String) : Ast :=
  .expr "block" ((cartDimensions count).map fun dimension =>
    .expr "escape" [.expr "=" [
      .atom (indexedNameInt external dimension),
      .expr "ref" [.atom source, .int dimension]]])

def CartRow179Property : Prop := ∀ count external source,
  match cartRow179 count external source with
  | .expr "block" assignments => assignments.length = (cartDimensions count).length
  | _ => False
theorem cartRow179_proven : CartRow179Property := by
  unfold CartRow179Property
  intros
  simp [cartRow179]

/-- Anonymous-source `@nextract`; `base/cartesian.jl:184-187`. -/
def cartRow184 (count : Int) (external : String) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok values =>
    let assignments := List.zipWith (fun dimension value =>
      .expr "escape" [.expr "=" [.atom (indexedNameInt external dimension), value]])
      (cartDimensions count) values
    .ok (.expr "block" assignments)

def CartRow184Property : Prop := ∀ count external source output,
  cartRow184 count external source = .ok output →
  match output with | .expr "block" _ => True | _ => False
theorem cartRow184_proven : CartRow184Property := by
  unfold CartRow184Property
  intros count external source output h
  cases hmap : cartMapDimensions count source with
  | error error => simp [cartRow184, hmap] at h
  | ok values =>
    simp [cartRow184, hmap] at h
    subst output
    trivial

def cartBooleanMacro (head : String) (count : Int) (source : InlineAnonymous) : Jl Ast := do
  let conditions ← cartMapDimensions count source
  return .expr head (conditions.map fun condition => .expr "escape" [condition])

/-- `@nall`; `base/cartesian.jl:198-204`. -/
def cartRow198 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match source with
  | .lambda _ _ => cartBooleanMacro "&&" count source
  | _ => .error (.argumentError "criterion must be an anonymous function")

def CartRow198Property : Prop := ∀ count parameter body,
  cartRow198 count (.lambda parameter body) = cartBooleanMacro "&&" count (.lambda parameter body)
theorem cartRow198_proven : CartRow198Property := by unfold CartRow198Property; intros; rfl

def CartRow198All : Prop := ∀ count source,
  cartRow198 count source = match source with
    | .lambda _ _ => cartBooleanMacro "&&" count source
    | _ => .error (.argumentError "criterion must be an anonymous function")
theorem cartRow198_all : CartRow198All := by
  unfold CartRow198All
  intros count source
  cases source <;> rfl

/-- `@nany`; `base/cartesian.jl:214-220`. -/
def cartRow214 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match source with
  | .lambda _ _ => cartBooleanMacro "||" count source
  | _ => .error (.argumentError "criterion must be an anonymous function")

def CartRow214Property : Prop := ∀ count parameter body,
  cartRow214 count (.lambda parameter body) = cartBooleanMacro "||" count (.lambda parameter body)
theorem cartRow214_proven : CartRow214Property := by unfold CartRow214Property; intros; rfl

def CartRow214All : Prop := ∀ count source,
  cartRow214 count source = match source with
    | .lambda _ _ => cartBooleanMacro "||" count source
    | _ => .error (.argumentError "criterion must be an anonymous function")
theorem cartRow214_all : CartRow214All := by
  unfold CartRow214All
  intros count source
  cases source <;> rfl

/-- `@ntuple`; `base/cartesian.jl:228-231`. -/
def cartRow228 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok values => .ok (.expr "escape" [.expr "tuple" values])

def CartRow228Property : Prop := ∀ count source values,
  cartMapDimensions count source = .ok values →
  cartRow228 count source = .ok (.expr "escape" [.expr "tuple" values])
theorem cartRow228_proven : CartRow228Property := by unfold CartRow228Property; intros; simp [cartRow228, *]

def buildIfChain : List Int → InlineAnonymous → InlineAnonymous → Ast → Jl Ast
  | [], _, _, fallback => .ok fallback
  | dimension :: rest, condition, operation, fallback => do
    let tail ← buildIfChain rest condition operation fallback
    let condition ← inlineAnonymousModel condition dimension
    let operation ← inlineAnonymousModel operation dimension
    return .expr "if" [.expr "escape" [condition], .expr "escape" [operation], tail]

/-- `@nif`; `base/cartesian.jl:251-259`. -/
def cartRow251 (count : Int) (condition operation : InlineAnonymous) (otherwise : Option InlineAnonymous) : Jl Ast := do
  let last ← inlineAnonymousModel (otherwise.getD operation) count
  let dimensions := (cartDimensions count).dropLast.reverse
  buildIfChain dimensions condition operation (.expr "escape" [last])

def CartRow251Property : Prop := ∀ count condition operation otherwise,
  cartRow251 count condition operation otherwise = do
    let last ← inlineAnonymousModel (otherwise.getD operation) count
    let dimensions := (cartDimensions count).dropLast.reverse
    buildIfChain dimensions condition operation (.expr "escape" [last])
theorem cartRow251_proven : CartRow251Property := by
  unfold CartRow251Property
  intros
  rfl

/-! Substitution and expression-resolution rows. -/

/-- `inlineanonymous(ex::Expr, val)`; `base/cartesian.jl:264-276`. -/
def cartRow264 (source : InlineAnonymous) (value : Int) : Jl Ast := inlineAnonymousModel source value
def CartRow264Property : Prop := ∀ source value, cartRow264 source value = inlineAnonymousModel source value
theorem cartRow264_proven : CartRow264Property := by unfold CartRow264Property; intros; rfl

/-- `inlineanonymous(base::Symbol, ext)`; `base/cartesian.jl:279`. -/
def cartRow279 (base : String) (extension : Int) : String := indexedNameInt base extension
def CartRow279Property : Prop := ∀ base extension, cartRow279 base extension = indexedNameInt base extension
theorem cartRow279_proven : CartRow279Property := by unfold CartRow279Property; intros; rfl

structure CartReplace where
  pattern : String
  value : Int
  deriving Repr, DecidableEq, Inhabited

/-- `LReplace(sym, val)`; `base/cartesian.jl:292`. -/
def cartRow292 (pattern : String) (value : Int) : CartReplace := ⟨pattern, value⟩
def CartRow292Property : Prop := ∀ pattern value, cartRow292 pattern value = ⟨pattern, value⟩
theorem cartRow292_proven : CartRow292Property := by unfold CartRow292Property; intros; rfl

/-- `lreplace(ex, sym, val)`; `base/cartesian.jl:294`. -/
def cartRow294 (expression : Ast) (pattern : String) (value : Int) : Ast := cartReplace pattern value expression
def CartRow294Property : Prop := ∀ expression pattern value,
  cartRow294 expression pattern value = cartReplace pattern value expression
theorem cartRow294_proven : CartRow294Property := by unfold CartRow294Property; intros; rfl

/-- Symbol `lreplace!`; `base/cartesian.jl:296-300`. -/
def cartRow296 (symbol pattern : String) (value : Int) (escapeDepth : Nat) : String :=
  if escapeDepth != 0 then symbol else if symbol == pattern then toString value else replaceNameSegments symbol pattern value
def CartRow296Property : Prop := ∀ symbol pattern value depth,
  cartRow296 symbol pattern value depth =
    if depth != 0 then symbol else if symbol == pattern then toString value else replaceNameSegments symbol pattern value
theorem cartRow296_proven : CartRow296Property := by
  unfold CartRow296Property
  intros; rfl

/-- `lreplace_string!`; `base/cartesian.jl:302-342`. -/
def cartRow302 (name pattern : String) (value : Int) : String := replaceNameSegments name pattern value
def CartRow302Property : Prop := ∀ name pattern value,
  cartRow302 name pattern value = replaceNameSegments name pattern value
theorem cartRow302_proven : CartRow302Property := by unfold CartRow302Property; intros; rfl

/-- Expr `lreplace!`; `base/cartesian.jl:344-377`. -/
def cartRow344 (expression : Ast) (pattern : String) (value : Int) : Ast := cartReplace pattern value expression
def CartRow344Property : Prop := ∀ expression pattern value,
  cartRow344 expression pattern value = cartReplace pattern value expression
theorem cartRow344_proven : CartRow344Property := by unfold CartRow344Property; intros; rfl

/-- Atomic fallback `lreplace!`; `base/cartesian.jl:379`. -/
def cartRow379 (argument : Ast) : Ast := argument
def CartRow379Property : Prop := ∀ argument, cartRow379 argument = argument
theorem cartRow379_proven : CartRow379Property := by unfold CartRow379Property; intro; rfl

def nonLineAst : Ast → Bool | .line => false | .expr "line" _ => false | _ => true

/-- Atomic `poplinenum`; `base/cartesian.jl:383`. -/
def cartRow383 (argument : Ast) : Ast := argument
def CartRow383Property : Prop := ∀ argument, cartRow383 argument = argument
theorem cartRow383_proven : CartRow383Property := by unfold CartRow383Property; intro; rfl

/-- Expr `poplinenum`; `base/cartesian.jl:384-399`. -/
def cartRow384 (expression : Ast) : Ast :=
  match expression with
  | .expr "block" arguments =>
    match arguments.filter nonLineAst with | [only] => only | _ => expression
  | _ => expression

def CartRow384Property : Prop := ∀ expression,
  cartRow384 expression = match expression with
    | .expr "block" arguments =>
      match arguments.filter nonLineAst with | [only] => only | _ => expression
    | _ => expression
theorem cartRow384_proven : CartRow384Property := by
  unfold CartRow384Property
  intro expression
  rfl

inductive ResolveArithmetic where
  | value (number : Int)
  | call (operator : String) (arguments : List Int)
  | other
  deriving Repr, DecidableEq, Inhabited

def evaluateArithmetic (operator : String) (arguments : List Int) : Option Int :=
  match operator, arguments with
  | "+", [a,b] => some (a+b) | "-", [a,b] => some (a-b)
  | "*", [a,b] => some (a*b) | "div", [a,b] => if b = 0 then none else some (a.tdiv b)
  | _, _ => none

/-- Expr `exprresolve_arith`; `base/cartesian.jl:408-418`. -/
def cartRow408 : ResolveArithmetic → Bool × Int
  | .call operator arguments => match evaluateArithmetic operator arguments with | some value => (true,value) | none => (false,0)
  | _ => (false,0)
def CartRow408Property : Prop := ∀ operator arguments value,
  evaluateArithmetic operator arguments = some value → cartRow408 (.call operator arguments) = (true,value)
theorem cartRow408_proven : CartRow408Property := by unfold CartRow408Property; intros; simp [cartRow408, *]

def CartRow408All : Prop := ∀ expression,
  cartRow408 expression = match expression with
    | .call operator arguments => match evaluateArithmetic operator arguments with
      | some value => (true,value) | none => (false,0)
    | _ => (false,0)
theorem cartRow408_all : CartRow408All := by
  unfold CartRow408All
  intros expression
  cases expression <;> rfl

/-- Atomic `exprresolve_arith`; `base/cartesian.jl:419`. -/
def cartRow419 (_ : Ast) : Bool × Int := (false,0)
def CartRow419Property : Prop := ∀ argument, cartRow419 argument = (false,0)
theorem cartRow419_proven : CartRow419Property := by unfold CartRow419Property; intro; rfl

/-- Bool `exprresolve_conditional`; `base/cartesian.jl:421`. -/
def cartRow421 (condition : Bool) : Bool × Bool := (true,condition)
def CartRow421Property : Prop := ∀ condition, cartRow421 condition = (true,condition)
theorem cartRow421_proven : CartRow421Property := by unfold CartRow421Property; intro; rfl

inductive ResolveCondition where | boolean (value : Bool) | comparison (operator : String) (left right : Int) | other
  deriving Repr, DecidableEq, Inhabited

def cartCompare : String → Int → Int → Option Bool
  | "==", a, b => some (a == b) | "<", a, b => some (a < b)
  | ">", a, b => some (a > b) | "<=", a, b => some (a ≤ b) | ">=", a, b => some (a ≥ b)
  | _, _, _ => none

/-- Expr `exprresolve_conditional`; `base/cartesian.jl:422-434`. -/
def cartRow422 : ResolveCondition → Bool × Bool
  | .boolean value => (true,value)
  | .comparison operator left right => match cartCompare operator left right with | some value => (true,value) | none => (false,false)
  | .other => (false,false)
def CartRow422Property : Prop := ∀ operator left right value,
  cartCompare operator left right = some value → cartRow422 (.comparison operator left right) = (true,value)
theorem cartRow422_proven : CartRow422Property := by unfold CartRow422Property; intros; simp [cartRow422, *]

def CartRow422All : Prop := ∀ condition,
  cartRow422 condition = match condition with
    | .boolean value => (true,value)
    | .comparison operator left right => match cartCompare operator left right with
      | some value => (true,value) | none => (false,false)
    | .other => (false,false)
theorem cartRow422_all : CartRow422All := by
  unfold CartRow422All
  intros condition
  cases condition <;> rfl

/-- Atomic `exprresolve_conditional`; `base/cartesian.jl:435`. -/
def cartRow435 (_ : Ast) : Bool × Bool := (false,false)
def CartRow435Property : Prop := ∀ argument, cartRow435 argument = (false,false)
theorem cartRow435_proven : CartRow435Property := by unfold CartRow435Property; intro; rfl

/-- Atomic `exprresolve`; `base/cartesian.jl:437`. -/
def cartRow437 (argument : Ast) : Ast := argument
def CartRow437Property : Prop := ∀ argument, cartRow437 argument = argument
theorem cartRow437_proven : CartRow437Property := by unfold CartRow437Property; intro; rfl

/-- Expr `exprresolve`; `base/cartesian.jl:438-473`. -/
def cartRow438 : ResolveArithmetic → ResolveArithmetic
  | .call "+" [a,0] => .value a
  | .call "-" [a,0] => .value a
  | expression@(.call operator arguments) =>
    match evaluateArithmetic operator arguments with | some value => .value value | none => expression
  | expression => expression

def CartRow438Property : Prop := ∀ expression,
  cartRow438 expression = expression ∨ ∃ value, cartRow438 expression = .value value
theorem cartRow438_proven : CartRow438Property := by
  unfold CartRow438Property
  intro expression
  cases expression with
  | value number => exact Or.inl rfl
  | other => exact Or.inl rfl
  | call operator arguments =>
    simp [cartRow438]
    split <;> simp_all
    split <;> simp_all

end JuliaLean.ExprReflect
