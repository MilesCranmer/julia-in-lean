import JuliaLean.base.cartesian
import JuliaLean.Proofs.base.cartesian.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

def CartRow38Property : Prop := ∀ count iterator range pre post body,
  cartRow38 count iterator range pre post body = buildLoops count iterator range pre post body

theorem cartRow38_proven : CartRow38Property := by unfold CartRow38Property; intros; rfl

/-- Array-symbol `_nloops`; `base/cartesian.jl:42-44`. -/

def CartRow42Property : Prop := ∀ count iterator array pre post body,
  cartRow42 count iterator array pre post body = buildLoops count iterator (.arrayAxes array) pre post body

theorem cartRow42_proven : CartRow42Property := by unfold CartRow42Property; intros; rfl

/-- Anonymous-range `_nloops`; `base/cartesian.jl:46-71`. -/

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

def CartRow85Property : Prop := ∀ count array source variables,
  cartMapDimensions count source = .ok variables →
  cartRow85 count array source = .ok (.expr "escape" [.expr "ref" (.atom array :: variables)])

theorem cartRow85_proven : CartRow85Property := by
  unfold CartRow85Property
  intros count array source variables h
  simp [cartRow85, h]

def CartRow105Property : Prop := ∀ count functionName arguments source variables,
  cartMapDimensions count source = .ok variables →
  cartRow105 count functionName arguments source =
    .ok (.expr "escape" [.expr "call" (.atom functionName :: arguments ++ variables)])

theorem cartRow105_proven : CartRow105Property := by
  unfold CartRow105Property
  intros; simp [cartRow105, *]

/-- `@ncallkw`; `base/cartesian.jl:132-138`. -/

def CartRow132Property : Prop := ∀ count functionName keyword arguments source variables,
  cartMapDimensions count source = .ok variables →
  cartRow132 count functionName keyword arguments source =
    .ok (.expr "escape" [.expr "call" (.atom functionName ::
      .expr "parameters" [.expr "..." [keyword]] :: arguments ++ variables)])

theorem cartRow132_proven : CartRow132Property := by
  unfold CartRow132Property
  intros; simp [cartRow132, *]

/-- `@nexprs`; `base/cartesian.jl:156-159`. -/

def CartRow156Property : Prop := ∀ count source expressions,
  cartMapDimensions count source = .ok expressions →
  cartRow156 count source = .ok (.expr "escape" [.expr "block" expressions])

theorem cartRow156_proven : CartRow156Property := by unfold CartRow156Property; intros; simp [cartRow156, *]

/-- Symbol-source `@nextract`; `base/cartesian.jl:179-182`. -/

def CartRow179Property : Prop := ∀ count external source,
  match cartRow179 count external source with
  | .expr "block" assignments => assignments.length = (cartDimensions count).length
  | _ => False

theorem cartRow179_proven : CartRow179Property := by
  unfold CartRow179Property
  intros
  simp [cartRow179]

/-- Anonymous-source `@nextract`; `base/cartesian.jl:184-187`. -/

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

def CartRow228Property : Prop := ∀ count source values,
  cartMapDimensions count source = .ok values →
  cartRow228 count source = .ok (.expr "escape" [.expr "tuple" values])

theorem cartRow228_proven : CartRow228Property := by unfold CartRow228Property; intros; simp [cartRow228, *]

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

def CartRow264Property : Prop := ∀ source value, cartRow264 source value = inlineAnonymousModel source value

theorem cartRow264_proven : CartRow264Property := by unfold CartRow264Property; intros; rfl

/-- `inlineanonymous(base::Symbol, ext)`; `base/cartesian.jl:279`. -/

def CartRow279Property : Prop := ∀ base extension, cartRow279 base extension = indexedNameInt base extension

theorem cartRow279_proven : CartRow279Property := by unfold CartRow279Property; intros; rfl

def CartRow292Property : Prop := ∀ pattern value, cartRow292 pattern value = ⟨pattern, value⟩

theorem cartRow292_proven : CartRow292Property := by unfold CartRow292Property; intros; rfl

/-- `lreplace(ex, sym, val)`; `base/cartesian.jl:294`. -/

def CartRow294Property : Prop := ∀ expression pattern value,
  cartRow294 expression pattern value = cartReplace pattern value expression

theorem cartRow294_proven : CartRow294Property := by unfold CartRow294Property; intros; rfl

/-- Symbol `lreplace!`; `base/cartesian.jl:296-300`. -/

def CartRow296Property : Prop := ∀ symbol pattern value depth,
  cartRow296 symbol pattern value depth =
    if depth != 0 then symbol else if symbol == pattern then toString value else replaceNameSegments symbol pattern value

theorem cartRow296_proven : CartRow296Property := by
  unfold CartRow296Property
  intros; rfl

/-- `lreplace_string!`; `base/cartesian.jl:302-342`. -/

def CartRow302Property : Prop := ∀ name pattern value,
  cartRow302 name pattern value = replaceNameSegments name pattern value

theorem cartRow302_proven : CartRow302Property := by unfold CartRow302Property; intros; rfl

/-- Expr `lreplace!`; `base/cartesian.jl:344-377`. -/

def CartRow344Property : Prop := ∀ expression pattern value,
  cartRow344 expression pattern value = cartReplace pattern value expression

theorem cartRow344_proven : CartRow344Property := by unfold CartRow344Property; intros; rfl

/-- Atomic fallback `lreplace!`; `base/cartesian.jl:379`. -/

def CartRow379Property : Prop := ∀ argument, cartRow379 argument = argument

theorem cartRow379_proven : CartRow379Property := by unfold CartRow379Property; intro; rfl

def CartRow383Property : Prop := ∀ argument, cartRow383 argument = argument

theorem cartRow383_proven : CartRow383Property := by unfold CartRow383Property; intro; rfl

/-- Expr `poplinenum`; `base/cartesian.jl:384-399`. -/

def CartRow384Property : Prop := ∀ expression,
  cartRow384 expression = match expression with
    | .expr "block" arguments =>
      match arguments.filter nonLineAst with | [only] => only | _ => expression
    | _ => expression

theorem cartRow384_proven : CartRow384Property := by
  unfold CartRow384Property
  intro expression
  rfl

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

def CartRow419Property : Prop := ∀ argument, cartRow419 argument = (false,0)

theorem cartRow419_proven : CartRow419Property := by unfold CartRow419Property; intro; rfl

/-- Bool `exprresolve_conditional`; `base/cartesian.jl:421`. -/

def CartRow421Property : Prop := ∀ condition, cartRow421 condition = (true,condition)

theorem cartRow421_proven : CartRow421Property := by unfold CartRow421Property; intro; rfl

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

def CartRow435Property : Prop := ∀ argument, cartRow435 argument = (false,false)

theorem cartRow435_proven : CartRow435Property := by unfold CartRow435Property; intro; rfl

/-- Atomic `exprresolve`; `base/cartesian.jl:437`. -/

def CartRow437Property : Prop := ∀ argument, cartRow437 argument = argument

theorem cartRow437_proven : CartRow437Property := by unfold CartRow437Property; intro; rfl

/-- Expr `exprresolve`; `base/cartesian.jl:438-473`. -/

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
