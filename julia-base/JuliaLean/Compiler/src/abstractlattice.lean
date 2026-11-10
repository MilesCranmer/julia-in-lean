import JuliaLean.Compiler.Prelude
import JuliaLean.Compiler.src.typeutils

/-!
`Compiler/src/abstractlattice.jl`: the lattice layers and the operations that do not call the
layered `⊑`.

The lattice structs themselves are `Lattice` in `JuliaLean/Compiler/Prelude.lean`. The generic
operations that call `⊑` (`⊏`, `⋤`, `is_lattice_equal`, the `fallback_lattice` methods and
`widenlattice(𝕃, t)`) are in `JuliaLean/Compiler/src/typelattice.lean`, after the layered `⊑` and
`widenconst` they call, and cite this file.
-/

namespace JuliaLean.Compiler

open JuliaLean.C

/-- `widenlattice(𝕃)`

Julia source: Compiler/src/abstractlattice.jl:12,21,32,43,54,65,76,95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widenlattice(::JLTypeLattice) = error("Type lattice is the least-precise lattice available")
widenlattice(::ConstsLattice) = JLTypeLattice()
widenlattice(𝕃::PartialsLattice) = 𝕃.parent
widenlattice(𝕃::ConditionalsLattice) = 𝕃.parent
widenlattice(𝕃::InterConditionalsLattice) = 𝕃.parent
widenlattice(𝕃::MustAliasesLattice) = 𝕃.parent
widenlattice(𝕃::InterMustAliasesLattice) = 𝕃.parent
widenlattice(𝕃::InferenceLattice) = 𝕃.parent
```
-/
def widenlattice : Lattice → CM Lattice
  | .jlType => jlThrow "ErrorException" "Type lattice is the least-precise lattice available"
  | .consts => pure .jlType
  | .partials p | .conditionals p | .interConditionals p | .mustAliases p
  | .interMustAliases p | .inference p => pure p

/-- The parent layer, total (`widenlattice` of every layer but `JLTypeLattice`). -/
def Lattice.parent : Lattice → Lattice
  | .jlType | .consts => .jlType
  | .partials p | .conditionals p | .interConditionals p | .mustAliases p
  | .interMustAliases p | .inference p => p

/-- `is_valid_lattice_norec(𝕃, elem)`

Julia source: Compiler/src/abstractlattice.jl:13,22,33,44,55,66,77,96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_valid_lattice_norec(::JLTypeLattice, @nospecialize(elem)) = isa(elem, Type)
is_valid_lattice_norec(::ConstsLattice, @nospecialize(elem)) = isa(elem, Const) || isa(elem, PartialTypeVar)
is_valid_lattice_norec(::PartialsLattice, @nospecialize(elem)) = isa(elem, PartialStruct) || isa(elem, PartialOpaque) || isa(elem, PartialTask)
is_valid_lattice_norec(::ConditionalsLattice, @nospecialize(elem)) = isa(elem, Conditional)
is_valid_lattice_norec(::InterConditionalsLattice, @nospecialize(elem)) = isa(elem, InterConditional)
is_valid_lattice_norec(::MustAliasesLattice, @nospecialize(elem)) = isa(elem, MustAlias)
is_valid_lattice_norec(::InterMustAliasesLattice, @nospecialize(elem)) = isa(elem, InterMustAlias)
is_valid_lattice_norec(::InferenceLattice, @nospecialize(elem)) = isa(elem, LimitedAccuracy)
```
-/
def isValidLatticeNorec : Lattice → LElt → Bool
  | .jlType, e => e.isTypeElt
  | .consts, e => e.isConst || e.isPartialTypeVar
  | .partials _, e => e.isPartialStruct || e.isPartialOpaque || e.isPartialTask
  | .conditionals _, e => e.isConditional
  | .interConditionals _, e => e.isInterConditional
  | .mustAliases _, e => e.isMustAlias
  | .interMustAliases _, e => e.isInterMustAlias
  | .inference _, e => e.isLimited

/-- `tmeet(::JLTypeLattice, a::AnyType, b::AnyType)`

Julia source: Compiler/src/abstractlattice.jl:110-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tmeet(::JLTypeLattice, @nospecialize(a::AnyType), @nospecialize(b::AnyType))
    ti = typeintersect(a, b)
    valid_as_lattice(ti, true) || return Bottom
    return ti
end
```
-/
def tmeetJLType (n : Nat) (E : CEnv) (a : LElt) (b : Val) : CM LElt := do
  let .ty a := a | jlThrow "MethodError" "tmeet(::JLTypeLattice, ...)"
  if !a.isType || !b.isType then jlThrow "MethodError" "tmeet(::JLTypeLattice, ...)"
  let ti ← typeintersect n E a b
  if !(← validAsLattice n E ti true) then return .ty .bottom
  return .ty ti

/-- `tmerge_field(𝕃, a, b)`: `nothing` for every layer of the default lattices.

In this file, a call on `widenlattice(ConstsLattice())` is written as the `JLTypeLattice` result,
so that the recursion on the layer is structural.

Julia source: Compiler/src/abstractlattice.jl:139-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tmerge_field(𝕃::AbstractLattice, @nospecialize(a), @nospecialize(b))
    return tmerge_field(widenlattice(𝕃), a, b)
end
tmerge_field(::JLTypeLattice, @nospecialize(a), @nospecialize(b)) = nothing
```
-/
def tmergeField : Lattice → LElt → LElt → CM (Option LElt)
  | .jlType, _, _ => pure none
  | .consts, _, _ => pure none
  | .partials p, a, b | .conditionals p, a, b | .interConditionals p, a, b
  | .mustAliases p, a, b | .interMustAliases p, a, b | .inference p, a, b => tmergeField p a b

/-- `⊑(::JLTypeLattice, a::AnyType, b::AnyType)`

Julia source: Compiler/src/abstractlattice.jl:153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer ⊑(::JLTypeLattice, @nospecialize(a::AnyType), @nospecialize(b::AnyType)) = a <: b
```
-/
def sqsubJLType (n : Nat) (E : CEnv) (a b : LElt) : CM Bool :=
  match a, b with
  | .ty a, .ty b => if a.isType && b.isType then issub n E a b
                    else jlThrow "MethodError" "⊑(::JLTypeLattice, ...)"
  | _, _ => jlThrow "MethodError" "⊑(::JLTypeLattice, ...)"

/-- `has_nontrivial_extended_info(𝕃, t)`

Julia source: Compiler/src/abstractlattice.jl:189-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer has_nontrivial_extended_info(𝕃::AbstractLattice, @nospecialize t) =
    has_nontrivial_extended_info(widenlattice(𝕃), t)
@nospecializeinfer function has_nontrivial_extended_info(𝕃::PartialsLattice, @nospecialize t)
    isa(t, PartialStruct) && return true
    isa(t, PartialOpaque) && return true
    isa(t, PartialTask) && return true
    return has_nontrivial_extended_info(widenlattice(𝕃), t)
end
@nospecializeinfer function has_nontrivial_extended_info(𝕃::ConstsLattice, @nospecialize t)
    isa(t, PartialTypeVar) && return true
    if isa(t, Const)
        val = t.val
        # a type-valued `Const` may pin `=== val` beyond its widening (which for
        # an open `val` is only the `==`-class `Type{val}`)
        return !issingletontype(typeof(val))
    end
    return has_nontrivial_extended_info(widenlattice(𝕃), t)
end
@nospecializeinfer has_nontrivial_extended_info(::JLTypeLattice, @nospecialize(t)) = false
```
-/
def hasNontrivialExtendedInfo (n : Nat) (E : CEnv) : Lattice → LElt → CM Bool
  | .jlType, _ => pure false
  | .consts, t => do
    if t.isPartialTypeVar then return true
    if let .const val := t then
      return !(← issingletontype n E (typeOf val))
    pure false
  | .partials p, t => do
    if t.isPartialStruct then return true
    if t.isPartialOpaque then return true
    if t.isPartialTask then return true
    hasNontrivialExtendedInfo n E p t
  | .conditionals p, t | .interConditionals p, t | .mustAliases p, t
  | .interMustAliases p, t | .inference p, t => hasNontrivialExtendedInfo n E p t

/-- `Core.Method`, `Core.CodeInstance`. -/
def methodType : Val := .datatype "Core.Method" []
def codeInstanceType : Val := .datatype "Core.CodeInstance" []

/-- `is_const_prop_profitable_arg(𝕃, t)`

Julia source: Compiler/src/abstractlattice.jl:215-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer is_const_prop_profitable_arg(𝕃::AbstractLattice, @nospecialize t) =
    is_const_prop_profitable_arg(widenlattice(𝕃), t)
@nospecializeinfer function is_const_prop_profitable_arg(𝕃::PartialsLattice, @nospecialize t)
    if isa(t, PartialStruct)
        return true # might be a bit aggressive, may want to enable some check like follows:
        ...
    end
    isa(t, PartialOpaque) && return true
    isa(t, PartialTask) && return true
    return is_const_prop_profitable_arg(widenlattice(𝕃), t)
end
@nospecializeinfer function is_const_prop_profitable_arg(𝕃::ConstsLattice, @nospecialize t)
    if isa(t, Const)
        # don't consider mutable values useful constants unless they have const fields
        val = t.val
        return isa(val, Symbol) || isa(val, Type) || isa(val, Method) || isa(val, CodeInstance) ||
                    !ismutable(val) || (typeof(val).name.constfields != C_NULL)
    end
    isa(t, PartialTypeVar) && return false # this isn't forwardable
    return is_const_prop_profitable_arg(widenlattice(𝕃), t)
end
@nospecializeinfer is_const_prop_profitable_arg(::JLTypeLattice, @nospecialize t) = false
```
`Method` and `CodeInstance` are concrete types with no subtypes, so `isa(val, Method)` is
`typeof(val) === Method`; their objects are mutable references (`Val.mutableRef`). -/
def isConstPropProfitableArg (E : CEnv) : Lattice → LElt → CM Bool
  | .jlType, _ => pure false
  | .consts, t => do
    if let .const val := t then
      if val.isSymbol || val.isType || typeOf val == methodType || typeOf val == codeInstanceType then
        return true
      if !(← ismutable E val) then return true
      return hasConstfields E val
    if t.isPartialTypeVar then return false
    pure false
  | .partials p, t => do
    if t.isPartialStruct then return true
    if t.isPartialOpaque then return true
    if t.isPartialTask then return true
    isConstPropProfitableArg E p t
  | .conditionals p, t | .interConditionals p, t | .mustAliases p, t
  | .interMustAliases p, t | .inference p, t => isConstPropProfitableArg E p t

/-- `is_forwardable_argtype(𝕃, x)`

Julia source: Compiler/src/abstractlattice.jl:244-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer is_forwardable_argtype(𝕃::AbstractLattice, @nospecialize(x)) =
    is_forwardable_argtype(widenlattice(𝕃), x)
@nospecializeinfer function is_forwardable_argtype(𝕃::ConditionalsLattice, @nospecialize x)
    isa(x, Conditional) && return true
    return is_forwardable_argtype(widenlattice(𝕃), x)
end
@nospecializeinfer function is_forwardable_argtype(𝕃::PartialsLattice, @nospecialize x)
    isa(x, PartialStruct) && return true
    isa(x, PartialOpaque) && return true
    isa(x, PartialTask) && return true
    return is_forwardable_argtype(widenlattice(𝕃), x)
end
@nospecializeinfer function is_forwardable_argtype(𝕃::ConstsLattice, @nospecialize x)
    isa(x, Const) && return true
    return is_forwardable_argtype(widenlattice(𝕃), x)
end
@nospecializeinfer function is_forwardable_argtype(𝕃::MustAliasesLattice, @nospecialize x)
    isa(x, MustAlias) && return true
    return is_forwardable_argtype(widenlattice(𝕃), x)
end
@nospecializeinfer is_forwardable_argtype(::JLTypeLattice, @nospecialize x) = false
```
-/
def isForwardableArgtype : Lattice → LElt → Bool
  | .jlType, _ => false
  | .consts, x => x.isConst || false
  | .partials p, x =>
    x.isPartialStruct || x.isPartialOpaque || x.isPartialTask || isForwardableArgtype p x
  | .conditionals p, x => x.isConditional || isForwardableArgtype p x
  | .mustAliases p, x => x.isMustAlias || isForwardableArgtype p x
  | .interConditionals p, x | .interMustAliases p, x | .inference p, x => isForwardableArgtype p x

/-- `is_valid_lattice(𝕃, elem)`

Julia source: Compiler/src/abstractlattice.jl:281-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@nospecializeinfer is_valid_lattice(𝕃::AbstractLattice, @nospecialize(elem)) =
    is_valid_lattice_norec(𝕃, elem) && is_valid_lattice(widenlattice(𝕃), elem)
@nospecializeinfer is_valid_lattice(𝕃::JLTypeLattice, @nospecialize(elem)) = is_valid_lattice_norec(𝕃, elem)
```
For every element, `is_valid_lattice_norec` holds for at most one layer, so this is false for any
lattice above `JLTypeLattice`. -/
def isValidLattice : Lattice → LElt → Bool
  | .jlType, e => isValidLatticeNorec .jlType e
  | .consts, e => isValidLatticeNorec .consts e && isValidLatticeNorec .jlType e
  | .partials p, e => isValidLatticeNorec (.partials p) e && isValidLattice p e
  | .conditionals p, e => isValidLatticeNorec (.conditionals p) e && isValidLattice p e
  | .interConditionals p, e => isValidLatticeNorec (.interConditionals p) e && isValidLattice p e
  | .mustAliases p, e => isValidLatticeNorec (.mustAliases p) e && isValidLattice p e
  | .interMustAliases p, e => isValidLatticeNorec (.interMustAliases p) e && isValidLattice p e
  | .inference p, e => isValidLatticeNorec (.inference p) e && isValidLattice p e

/-- `has_conditional`, `has_mustalias`, `has_extended_unionsplit`

Julia source: Compiler/src/abstractlattice.jl:285-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_conditional(𝕃::AbstractLattice) = has_conditional(widenlattice(𝕃))
has_conditional(::AnyConditionalsLattice) = true
has_conditional(::JLTypeLattice) = false

has_mustalias(𝕃::AbstractLattice) = has_mustalias(widenlattice(𝕃))
has_mustalias(::AnyMustAliasesLattice) = true
has_mustalias(::JLTypeLattice) = false

has_extended_unionsplit(𝕃::AbstractLattice) = has_extended_unionsplit(widenlattice(𝕃))
has_extended_unionsplit(::AnyMustAliasesLattice) = true
has_extended_unionsplit(::JLTypeLattice) = false
```
-/
def hasConditional : Lattice → Bool
  | .jlType => false
  | .conditionals _ | .interConditionals _ => true
  | .consts => false
  | .partials p | .mustAliases p | .interMustAliases p | .inference p => hasConditional p

def hasMustalias : Lattice → Bool
  | .jlType => false
  | .mustAliases _ | .interMustAliases _ => true
  | .consts => false
  | .partials p | .conditionals p | .interConditionals p | .inference p => hasMustalias p

def hasExtendedUnionsplit : Lattice → Bool
  | .jlType => false
  | .mustAliases _ | .interMustAliases _ => true
  | .consts => false
  | .partials p | .conditionals p | .interConditionals p | .inference p => hasExtendedUnionsplit p

end JuliaLean.Compiler
