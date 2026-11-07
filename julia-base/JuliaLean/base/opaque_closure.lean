import JuliaLean.Core
import JuliaLean.base.expr

/-!
# Model of `base/opaque_closure.jl`

The macros build their `:opaque_closure` syntax from the typed AST in
`JuliaLean.base.expr`. `opaque2` returns the expansion and updated type AST, so
its `filter!` mutation remains explicit. `GenerateKwargs` records forwarded
keywords; the runtime constructor remains a typed primitive.
-/

namespace JuliaLean.base.opaque_closure

open JuliaLean
open JuliaLean.base.expr

abbrev I := JInt .i64
abbrev CInt := JInt .i32

inductive OpaqueError (RuntimeError : Type) where
  | expression (error : ExprError)
  | runtime (error : RuntimeError)
  | errorException (message : String)
structure MacroOutcome (L Error : Type) where
  result : Except Error (Value L)
  typeAfter : Value L



structure GenerateOptions (Module : Type) where
  mod : Module
  lineno : I
  file : Option Sym
  doCompile : Bool
  isinferred : Bool
structure GenerateKwargs (Module : Type) where
  mod : Option Module
  lineno : Option I
  file : Option (Option Sym)
  doCompile : Option Bool
  isinferred : Option Bool

private def defaultGenerateKwargs {Module : Type} : GenerateKwargs Module :=
  ⟨none, none, none, none, none⟩


structure OpaqueClosureOps (L Module Source Closure RuntimeError : Type) where
  leaves : LeafOps L
  exprArgs : Value L → Except (OpaqueError RuntimeError) (List (Value L))
  destructureArrow : List (Value L) → Except (OpaqueError RuntimeError) (Value L × Value L)
  unionEmpty : Value L
  baseModule : Module
  toCint : I → Except (OpaqueError RuntimeError) CInt
  boolToCint : Bool → CInt
  newOpaqueClosureFromCodeInfo : Value L → Value L → Value L → Module → Source →
    CInt → Option Sym → CInt → CInt → List (Value L) → CInt → CInt →
    Except (OpaqueError RuntimeError) Closure

private def nothingValue {L Module Source Closure RuntimeError : Type}
    (ops : OpaqueClosureOps L Module Source Closure RuntimeError) : Value L :=
  .leaf ops.leaves.nothing

private def trueValue {L Module Source Closure RuntimeError : Type}
    (ops : OpaqueClosureOps L Module Source Closure RuntimeError) : Value L :=
  .leaf (ops.leaves.ofBool true)

private def isUnderscore {L : Type} : Value L → Bool
  | .symbol "_" => true
  | _ => false

private def isLineNumberNode {L : Type} : Value L → Bool
  | .lineNumberNode _ _ => true
  | _ => false

/--
Julia source: base/opaque_closure.jl:20-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro opaque(ex)
    esc(Expr(:opaque_closure, nothing, nothing, nothing, #= allow_partial =# true, ex))
end
```
-/
def opaque1 {L Module Source Closure RuntimeError : Type}
    (ops : OpaqueClosureOps L Module Source Closure RuntimeError) (ex : Value L) : Value L :=
  esc (.expr "opaque_closure"
    [nothingValue ops, nothingValue ops, nothingValue ops, trueValue ops, ex])

/--
Julia source: base/opaque_closure.jl:24-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro opaque(ty, ex)
    if Base.isexpr(ty, :->)
        (AT, body) = ty.args
        filter!((n)->!isa(n, LineNumberNode), body.args)
        if !Base.isexpr(body, :block) || length(body.args) != 1
            error("Opaque closure type must be specified in the form Tuple{T,U...}->RT")
        end
        RT = only(body.args)
    else
        error("Opaque closure type must be specified in the form Tuple{T,U...}->RT")
    end
    AT = (AT !== :_) ? AT : nothing
    RT = (RT !== :_) ? RT : nothing
    return esc(Expr(:opaque_closure, AT, RT, RT, #= allow_partial =# true, ex))
end
```
-/
def opaque2 {L Module Source Closure RuntimeError : Type}
    (ops : OpaqueClosureOps L Module Source Closure RuntimeError)
    (ty ex : Value L) : MacroOutcome L (OpaqueError RuntimeError) :=
  let badSignature :=
    OpaqueError.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT"
  if !isexpr ty "->" then ⟨.error badSignature, ty⟩
  else
    match ops.exprArgs ty with
    | .error error => ⟨.error error, ty⟩
    | .ok tyArgs =>
      match ops.destructureArrow tyArgs with
      | .error error => ⟨.error error, ty⟩
      | .ok (argType, body) =>
        match ops.exprArgs body with
        | .error error => ⟨.error error, ty⟩
        | .ok rawBodyArgs =>
          let bodyArgs := rawBodyArgs.filter (fun node => !isLineNumberNode node)
          let bodyAfter := match body with
            | .expr head _ => Value.expr head bodyArgs
            | other => other
          let tyAfter := Value.expr "->" [argType, bodyAfter]
          if !isexpr body "block" || bodyArgs.length != 1 then
            ⟨.error badSignature, tyAfter⟩
          else
            match bodyArgs with
            | [returnType] =>
              let argType := if isUnderscore argType then nothingValue ops else argType
              let returnType := if isUnderscore returnType then nothingValue ops else returnType
              ⟨.ok (esc (.expr "opaque_closure"
                [argType, returnType, returnType, trueValue ops, ex])), tyAfter⟩
            | _ => ⟨.error badSignature, tyAfter⟩

private def defaultGenerateOptions {L Module Source Closure RuntimeError : Type}
    (ops : OpaqueClosureOps L Module Source Closure RuntimeError) : GenerateOptions Module :=
  ⟨ops.baseModule, JInt.wrap .i64 0, none, true, true⟩

/--
Julia source: base/opaque_closure.jl:47-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function generate_opaque_closure(@nospecialize(sig), @nospecialize(rt_lb), @nospecialize(rt_ub),
                                 src::CodeInfo, nargs::Int, isva::Bool, @nospecialize env...;
                                 mod::Module=@__MODULE__,
                                 lineno::Int=0,
                                 file::Union{Nothing,Symbol}=nothing,
                                 do_compile::Bool=true,
                                 isinferred::Bool=true)
    return ccall(:jl_new_opaque_closure_from_code_info, Any, (Any, Any, Any, Any, Any, Cint, Any, Cint, Cint, Any, Cint, Cint),
        sig, rt_lb, rt_ub, mod, src, lineno, file, nargs, isva, env, do_compile, isinferred)
end
```
-/
def generateOpaqueClosure {L Module Source Closure RuntimeError : Type}
    (ops : OpaqueClosureOps L Module Source Closure RuntimeError)
    (sig rtLower rtUpper : Value L) (src : Source) (nargs : I) (isva : Bool)
    (env : List (Value L)) (options : GenerateOptions Module := defaultGenerateOptions ops) :
    Except (OpaqueError RuntimeError) Closure := do
  let lineno ← ops.toCint options.lineno
  let nargs ← ops.toCint nargs
  let isva := ops.boolToCint isva
  let doCompile := ops.boolToCint options.doCompile
  let isinferred := ops.boolToCint options.isinferred
  ops.newOpaqueClosureFromCodeInfo sig rtLower rtUpper options.mod src lineno options.file
    nargs isva env doCompile isinferred

/--
Julia source: base/opaque_closure.jl:43-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Core.OpaqueClosure(src::CodeInfo, @nospecialize env...; rettype, sig, nargs, isva=false, kwargs...)
    return generate_opaque_closure(sig, Union{}, rettype, src, nargs, isva, env...; kwargs...)
end
```
-/
def ofCodeInfo {L Module Source Closure RuntimeError : Type}
    (ops : OpaqueClosureOps L Module Source Closure RuntimeError)
    (src : Source) (env : List (Value L)) (rettype sig : Value L) (nargs : I)
    (isva : Bool := false) (kwargs : GenerateKwargs Module := defaultGenerateKwargs) :
    Except (OpaqueError RuntimeError) Closure := do
  let options : GenerateOptions Module :=
    ⟨kwargs.mod.getD ops.baseModule, kwargs.lineno.getD (JInt.wrap .i64 0),
      kwargs.file.getD none, kwargs.doCompile.getD true, kwargs.isinferred.getD true⟩
  generateOpaqueClosure ops sig ops.unionEmpty rettype src nargs isva env options

end JuliaLean.base.opaque_closure

namespace JuliaLean.MiscCov.OpaqueClosure

/-- `@opaque ex`, `base/opaque_closure.jl:20-22`. -/
def opaque1 (ex : Ex) : Ex :=
  Ex.esc (.expr "opaque_closure" [.nothing, .nothing, .nothing, .bool true, ex])

/-- `@opaque ty ex`, `base/opaque_closure.jl:24-38`: `ty` must be `AT -> RT` whose body,
without line numbers, is a block of one expression; `_` stands for `nothing`. -/
def opaque2 (ty ex : Ex) : M Ex :=
  match ty with
  | .expr "->" [AT, body] =>
    let bargs := (body.args?.getD []).filter (fun x => !x.isLnn)
    if !(body.isExpr "block") || bargs.length != 1 then
      .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")
    else
      let RT := bargs.head!
      let AT := if !AT.isSym "_" then AT else .nothing
      let RT := if !RT.isSym "_" then RT else .nothing
      .ok (Ex.esc (.expr "opaque_closure" [AT, RT, RT, .bool true, ex]))
  | _ => .error (.errorException "Opaque closure type must be specified in the form Tuple{T,U...}->RT")

/-- The argument record of `jl_new_opaque_closure_from_code_info`. -/
structure NewOC where
  sig : String
  rtLb : String
  rtUb : String
  mod : String
  lineno : Int
  file : Option String
  nargs : Int
  isva : Bool
  env : List String
  doCompile : Bool
  isinferred : Bool
  deriving DecidableEq, Repr

/-- `generate_opaque_closure(sig, rt_lb, rt_ub, src, nargs, isva, env...; mod=@__MODULE__,
lineno=0, file=nothing, do_compile=true, isinferred=true)`, `base/opaque_closure.jl:47-56`;
`@__MODULE__` there is `Base`. -/
def generate (sig rtLb rtUb : String) (nargs : Int) (isva : Bool) (env : List String)
    (mod : String := "Base") (lineno : Int := 0) (file : Option String := none)
    (doCompile : Bool := true) (isinferred : Bool := true) : NewOC :=
  ⟨sig, rtLb, rtUb, mod, lineno, file, nargs, isva, env, doCompile, isinferred⟩

/-- `Core.OpaqueClosure(src, env...; rettype, sig, nargs, isva=false, kwargs...)`,
`base/opaque_closure.jl:43-45`. -/
def ofCodeInfo (env : List String) (rettype sig : String) (nargs : Int) (isva : Bool := false) : NewOC :=
  generate sig "Union{}" rettype nargs isva env

end JuliaLean.MiscCov.OpaqueClosure
