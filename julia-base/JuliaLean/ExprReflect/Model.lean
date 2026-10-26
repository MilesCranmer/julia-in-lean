import JuliaLean.Core

/-!
Small executable models for expression utilities, enum construction, reflection,
and `Base.Cartesian` on Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.ExprReflect

open JuliaLean

/-! ### Expression utilities -/

/-- Julia AST values needed by the modelled metaprogramming functions. -/
inductive Ast where
  | atom (name : String)
  | int (value : Int)
  | line
  | expr (head : String) (args : List Ast)
  | quoteNode (value : Ast)
  deriving Repr, Inhabited

/-- `isexpr(ex, heads[, n])`; `base/expr.jl:3-4,42-43`. -/
def isExpr (ex : Ast) (heads : List String) (arity : Option Nat := none) : Bool :=
  match ex with
  | .expr head args => heads.contains head && arity.all (args.length == ·)
  | _ => false

/-- `Meta.quot(ex)`; `base/meta.jl:158`. -/
def quot (ex : Ast) : Ast := .expr "quote" [ex]

/-- Structural content printed by `Meta.show_sexpr`; `base/meta.jl:231-256`.
Indentation and punctuation are presentation details, while this tree records the
head and recursive argument order exactly. -/
inductive SExpr where
  | atom (text : String)
  | form (head : String) (args : List SExpr)
  | quoteNode (value : SExpr)
  deriving Repr, Inhabited

def toSExpr : Ast → SExpr
  | .atom name => .atom name
  | .int value => .atom (toString value)
  | .line => .atom "#line"
  | .expr head args => .form head (args.map toSExpr)
  | .quoteNode value => .quoteNode (toSExpr value)
termination_by ex => sizeOf ex

/-!
`copy(::Expr)` recursively copies direct `Expr` arguments but does not descend
through `QuoteNode`. Natural numbers stand for mutable Expr identities.
`base/expr.jl:45,67-81`.
-/
inductive CopyVal where
  | nil
  | atom (name : String)
  | args (first rest : CopyVal)
  | expr (id : Nat) (head : String) (args : CopyVal)
  | quoteNode (value : CopyVal)
  deriving Repr, DecidableEq, Inhabited

def copyExprs (fresh : Nat) : CopyVal → CopyVal
  | .nil => .nil
  | .atom name => .atom name
  | .args first rest => .args (copyExprs fresh first) (copyExprs fresh rest)
  | .expr id head args => .expr (fresh + id) head (copyExprs fresh args)
  | .quoteNode value => .quoteNode value

def eraseCopyIds : CopyVal → CopyVal
  | .nil => .nil
  | .atom name => .atom name
  | .args first rest => .args (eraseCopyIds first) (eraseCopyIds rest)
  | .expr _ head args => .expr 0 head (eraseCopyIds args)
  | .quoteNode value => .quoteNode (eraseCopyIds value)

def copyIds : CopyVal → List Nat
  | .nil => []
  | .atom _ => []
  | .args first rest => copyIds first ++ copyIds rest
  | .expr id _ args => id :: copyIds args
  | .quoteNode value => copyIds value

def allIdsBelow (value : CopyVal) (fresh : Nat) : Bool :=
  (copyIds value).all (· < fresh)

def idsDisjoint (left right : List Nat) : Bool :=
  left.all fun id => !right.contains id

/-! ### Annotation macros -/

/-- Normalized effect of `annotate_meta_def_or_block`; `base/expr.jl:1227-1239`.
The Bool records the preceding `is_function_def` result. -/
def annotateInline (isFunction : Bool) (ex : Ast) : Ast :=
  if isFunction then
    .expr "escape" [.expr "pushmeta" [.atom "inline", ex]]
  else
    .expr "block" [
      .expr "inline" [.atom "true"],
      .expr "local" [.expr "=" [.atom "val", .expr "escape" [ex]]],
      .expr "inline" [.atom "false"],
      .atom "val"]

/-- Normalized `@generated` transformation; `base/expr.jl:1359-1374`. -/
def annotateGenerated (isFunction : Bool) (signature body : Ast) : Jl Ast :=
  if isFunction then
    .ok (.expr "escape" [.expr "function" [signature,
      .expr "if" [.expr "generated" [], body,
        .expr "block" [.expr "meta" [.atom "generated_only"],
          .expr "return" [.atom "nothing"]]]]])
  else
    .error (.argumentError "invalid syntax; @generated must be used with a function definition")

/-! ### Reflection -/

/-- Definite layout metadata used by `fieldnames`, `fieldcount`, and `fieldoffset`. -/
structure TypeLayout where
  names : List String
  offsets : List Nat
  definite : Bool
  deriving Repr, DecidableEq, Inhabited

/-- `fieldcount`; `base/runtime_internals.jl:1456-1487`. -/
def fieldCount (layout : TypeLayout) : Jl Nat :=
  if layout.definite then .ok layout.names.length
  else .error (.argumentError "type does not have a definite number of fields")

/-- `fieldnames`; `base/runtime_internals.jl:413-442`. -/
def fieldNames (layout : TypeLayout) : Jl (List String) := do
  if layout.definite then .ok layout.names
  else .error (.argumentError "type does not have a definite number of fields")

/-- One-based `fieldoffset(type, i)`. The public `Integer` index is converted to
`Cint` before `jl_get_field_offset`; `base/runtime_internals.jl:1228-1275`. -/
def fieldOffset (layout : TypeLayout) (index : Int) : Jl Nat := do
  if index < -2147483648 || 2147483647 < index then
    .error (.inexactError "Cint")
  else if !layout.definite then
    .error (.argumentError "type does not have a definite number of fields")
  else if index < 1 || layout.names.length < index.toNat then
    .error .boundsError
  else match layout.offsets[index.toNat - 1]? with
    | some offset => .ok offset
    | none => .error .boundsError

/-- Abstract method record. Input order is Julia's most-to-least-specific order. -/
structure MethodInfo where
  name : String
  moduleName : String
  signatureMatches : Bool
  deriving Repr, DecidableEq, Inhabited

/-- `matches_to_methods`; `base/runtime_internals.jl:1723-1731`. -/
def methods (table : List MethodInfo) (modules : Option (List String)) : List MethodInfo :=
  table.filter fun method =>
    method.signatureMatches && modules.all (·.contains method.moduleName)

/-- `which`, abstracting the runtime's unique most-specific match; `base/reflection.jl:968-1013`. -/
def whichMethod (table : List MethodInfo) (modules : Option (List String)) : Option MethodInfo :=
  (methods table modules).head?

/-- `hasmethod`; `base/reflection.jl:1077-1139`. -/
def hasMethod (table : List MethodInfo) (modules : Option (List String)) : Bool :=
  !(methods table modules).isEmpty

/-- `nameof(f::Function)`; `base/reflection.jl:1029-1043`. -/
def nameOf (functionName : String) : String := functionName

/-! ### `@enum` -/

/-- Bounds of a primitive enum base type. -/
structure EnumBounds where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq, Inhabited

structure EnumMember where
  name : String
  value : Option Int
  deriving Repr, DecidableEq, Inhabited

structure EnumState where
  next : Int
  names : List String
  values : List Int
  lo : Int
  hi : Int
  hasExplicit : Bool
  deriving Repr, DecidableEq, Inhabited

structure EnumResult where
  names : List String
  instances : List Int
  typeminValue : Int
  typemaxValue : Int
  deriving Repr, DecidableEq, Inhabited

def enumConvert (bounds : EnumBounds) (value : Int) : Jl Int :=
  if bounds.lo ≤ value && value ≤ bounds.hi then .ok value
  else .error (.inexactError "@enum")

def enumNext (bounds : EnumBounds) (value : Int) : Int :=
  if value = bounds.hi then bounds.lo else value + 1

/-- The validation and state update after a member's value is known. -/
def enumFinish (bounds : EnumBounds) (state : EnumState) (member : EnumMember)
    (value : Int) (explicit : Bool) : Jl EnumState :=
  let hasExplicit := state.hasExplicit || explicit
  if hasExplicit && state.values.contains value then
    .error (.argumentError "values must be unique")
  else
    let values := state.values ++ [value]
    if state.names.contains member.name then
      .error (.argumentError "name is not unique")
    else
      let first := state.values.isEmpty
      .ok {
        next := enumNext bounds value
        names := state.names ++ [member.name]
        values
        lo := if first then value else state.lo
        hi := if first then value else max state.hi value
        hasExplicit }

/-- One iteration of `@enum`; `base/Enums.jl:170-217`. -/
def enumStep (bounds : EnumBounds) (state : EnumState) (member : EnumMember) : Jl EnumState :=
  match member.value with
  | some raw =>
    match enumConvert bounds raw with
    | .error error => .error error
    | .ok value => enumFinish bounds state member value true
  | none =>
    if state.next = bounds.lo && !state.values.isEmpty then
      .error (.argumentError "overflow in value")
    else enumFinish bounds state member state.next false

def enumLoop (bounds : EnumBounds) : EnumState → List EnumMember → Jl EnumState
  | state, [] => .ok state
  | state, member :: rest =>
    match enumStep bounds state member with
    | .error error => .error error
    | .ok state => enumLoop bounds state rest

/-- `@enum` member assignment and generated extrema/instances;
`base/Enums.jl:144-251`. Identifier validation and `Core.eval` are preconditions
of this integer/member-list model. -/
def enumBuild (bounds : EnumBounds) (members : List EnumMember) : Jl EnumResult :=
  if members.isEmpty then
    .error (.argumentError "no arguments given for Enum")
  else
    match enumLoop bounds {
        next := 0, names := [], values := [], lo := 0, hi := 0, hasExplicit := false } members with
    | .error error => .error error
    | .ok state => .ok {
        names := state.names
        instances := state.values
        typeminValue := state.lo
        typemaxValue := state.hi }

/-! ### `Base.Cartesian` -/

def indexedName (stem : String) (dimension : Nat) : String :=
  stem ++ "_" ++ toString dimension

/-- `@nref`; `base/cartesian.jl:73-88`. -/
def nref (dimensions : Nat) (array stem : String) : Ast :=
  .expr "escape" [.expr "ref" (.atom array ::
    (List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

/-- `@ntuple`; `base/cartesian.jl:222-231`. -/
def ntuple (dimensions : Nat) (stem : String) : Ast :=
  .expr "escape" [.expr "tuple"
    ((List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

def loopLayer (iterator array : String) (dimension : Nat) (body : Ast) : Ast :=
  .expr "for" [
    .expr "=" [.atom (indexedName iterator dimension),
      .expr "axes" [.atom array, .int dimension]],
    body]

/-- The documented normalized nest, built inner dimension first so dimension `N`
is outermost; `base/cartesian.jl:25-33,53-70`. -/
def documentedLoops (dimensions : Nat) (iterator array : String) (body : Ast) : Ast :=
  (List.range dimensions).foldl
    (fun nested index => loopLayer iterator array (index + 1) nested)
    (.expr "escape" [body])

def isCompound : Ast → Bool
  | .expr _ _ => true
  | _ => false

/-- Actual `@nloops` dispatch: `args::Expr...` rejects atomic bodies before the
loop builder runs; `base/cartesian.jl:38-70`. -/
def nloops (dimensions : Nat) (iterator array : String) (body : Ast) : Jl Ast :=
  if isCompound body then .ok (documentedLoops dimensions iterator array body)
  else .error (.methodError "Base.Cartesian._nloops")

end JuliaLean.ExprReflect
