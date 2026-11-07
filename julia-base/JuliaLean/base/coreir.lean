import JuliaLean.Core
import JuliaLean.base.io

/-!
# Model of `base/coreir.jl`

Typed models of the Core IR constructors and `PartialStruct` helpers in Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Core type reflection, vector allocation and field
access, and equality on `Any` values are explicit typed interfaces. The `PartialStruct` model keeps
the original vector objects so reads, writes, and aliases remain visible.
-/

namespace JuliaLean.base.coreir

open JuliaLean

abbrev M := JuliaLean.base.io.M
abbrev I64 := JInt64

inductive CoreIRError where
  | boundsError
  | assertionError (message : String)
  | errorException (message : String)
  | externalError (message : String)
  deriving DecidableEq, Repr

structure PhiNodeOps (World Int32Vector AnyVector PhiNode : Type) where
  emptyInt32Vector : M World Int32Vector
  emptyAnyVector : M World AnyVector
  construct : Int32Vector → AnyVector → M World PhiNode

-- UNTRANSLATED
-- Source: base/coreir.jl:1-1 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- /Source
-- Reason: The Julia license line has no executable behavior.

/--
Julia source: base/coreir.jl:3-3 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Core.PhiNode() = Core.PhiNode(Int32[], Any[])
```
-/
def emptyPhiNode {World Int32Vector AnyVector PhiNode : Type}
    (ops : PhiNodeOps World Int32Vector AnyVector PhiNode) : M World PhiNode := do
  let edges ← ops.emptyInt32Vector
  let values ← ops.emptyAnyVector
  ops.construct edges values

/--
Julia source: base/coreir.jl:5-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    struct Const
        val
    end

The type representing a constant value.
"""
Core.Const
```
-/
structure Const (Value : Type) where
  val : Value

/--
Julia source: base/coreir.jl:14-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    struct PartialStruct
        typ
        undefs::Vector{Union{Nothing,Bool}} # represents whether a given field may be undefined
        fields::Vector{Any} # i-th element describes the lattice element for the i-th defined field
    end

This extended lattice element is introduced when we have information about an object's
fields beyond what can be obtained from the object type. E.g. it represents a tuple where
some elements are known to be constants or a struct whose `Any`-typed field is initialized
with value whose type is concrete.

- `typ` indicates the type of the object
- `undefs` records defined-ness of each field
- `fields` holds the lattice elements corresponding to each field of the object

`fields` corresponds to the fields that `typ` can have.
If `typ` is a struct that can have `n` fields, then `length(fields) == n`.
A special case: if `typ` is a variable-length `Tuple`,
then `length(fields) == datatype_min_ninitialized(typ) + 1`.
The last element represents the `Vararg` element.

`undefs` is a `Vector{Union{Nothing,Bool}}` with the same length as `fields`, encoding
the following information about field defined-ness:
- `undefs[i] === nothing` indicates the corresponding element in `fields` may be undefined
- `undefs[i] === false` indicates the corresponding element in `fields` is guaranteed to be defined
- `undefs[i] === true` indicates the corresponding element in `fields` is guaranteed to be undefined
If `field[i]` is of type `Union{}`, it means the `i`-th field will never be initialized and
thus never be defined. In this case, `undefs[i]` should always be `true`.

The same applies if `typ` is a `Tuple`, and because of how `Tuple` elements are initialized,
`undefs[i] === false` holds except that `undefs[end]` may be `nothing` when the last element
is `Vararg`.
"""
Core.PartialStruct
```
-/
structure PartialStruct (TypeValue UndefVector FieldsVector : Type) where
  typ : TypeValue
  undefs : UndefVector
  fields : FieldsVector

structure PartialStructTypeOps (World TypeValue Field UndefVector FieldsVector : Type) where
  fieldCountNoError : TypeValue → Option Nat
  isTupleSubtype : TypeValue → Bool
  isVarargType : Field → Bool
  datatypeMinNinitialized : TypeValue → Nat
  isUnionBottom : Field → Bool
  fieldsLength : FieldsVector → Nat
  fieldAt : FieldsVector → Nat → M World Field
  undefsLength : UndefVector → Nat
  undefAt : UndefVector → Nat → M World (Option Bool)
  newUndefs : Nat → M World UndefVector
  setUndef : UndefVector → Nat → Option Bool → M World Unit

def coreAssertion {World : Type} (condition : Bool) (message : String) : M World Unit :=
  if condition then pure () else throw (JuliaLean.base.io.Error.foreignError "AssertionError" message)

/--
Julia source: base/coreir.jl:50-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Core.PartialStruct(typ::Type, undefs::Vector{Union{Nothing,Bool}}, fields::Vector{Any})
    fldcnt = fieldcount_noerror(typ)
    if fldcnt !== nothing
        @assert fldcnt == length(fields)
    else
        @assert typ <: Tuple && isvarargtype(fields[end])
        @assert datatype_min_ninitialized(typ) == length(fields) - 1
        @assert undefs[end] === nothing
    end
    @assert length(fields) == length(undefs)
    for i = 1:length(fields)
        if fields[i] === Union{}
            @assert undefs[i] === true "`Union{}` typed field should be strictly undefined"
        end
    end
    return Core._PartialStruct(typ, undefs, fields)
end
```
-/
def partialStructConstructor {World TypeValue Field UndefVector FieldsVector : Type}
    (ops : PartialStructTypeOps World TypeValue Field UndefVector FieldsVector)
    (typ : TypeValue) (undefs : UndefVector) (fields : FieldsVector) :
    M World (PartialStruct TypeValue UndefVector FieldsVector) := do
  let fieldCount := ops.fieldCountNoError typ
  if let some count := fieldCount then
    coreAssertion (count == ops.fieldsLength fields) "fldcnt == length(fields)"
  else do
    if !(ops.isTupleSubtype typ) then
      throw (JuliaLean.base.io.Error.foreignError "AssertionError" "typ <: Tuple && isvarargtype(fields[end])")
    let lastField ← ops.fieldAt fields (ops.fieldsLength fields)
    if !(ops.isVarargType lastField) then
      throw (JuliaLean.base.io.Error.foreignError "AssertionError" "typ <: Tuple && isvarargtype(fields[end])")
    let minimumInitialized := ops.datatypeMinNinitialized typ
    if minimumInitialized != ops.fieldsLength fields - 1 then
      throw (JuliaLean.base.io.Error.foreignError "AssertionError" "datatype_min_ninitialized(typ) == length(fields) - 1")
    let lastUndef ← ops.undefAt undefs (ops.undefsLength undefs)
    if lastUndef != none then
      throw (JuliaLean.base.io.Error.foreignError "AssertionError" "undefs[end] === nothing")
  if ops.fieldsLength fields != ops.undefsLength undefs then
    throw (JuliaLean.base.io.Error.foreignError "AssertionError" "length(fields) == length(undefs)")
  let _ ← JuliaLean.base.io.whileLoop (fun index => do
    if index > ops.fieldsLength fields then
      pure (.inl ())
    else
      let field ← ops.fieldAt fields index
      if ops.isUnionBottom field then
        let undef ← ops.undefAt undefs index
        if undef != some true then
          throw (JuliaLean.base.io.Error.foreignError "AssertionError" "`Union{}` typed field should be strictly undefined")
      pure (.inr (index + 1))) 1
  pure ⟨typ, undefs, fields⟩

/--
Julia source: base/coreir.jl:68-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Legacy constructor
function Core.PartialStruct(@nospecialize(typ), fields::Vector{Any})
    undefs = partialstruct_init_undefs(typ, fields)
    undefs === nothing && error("This object never exists at runtime")
    return Core.PartialStruct(typ, undefs, fields)
end
```
-/
def partialStructLegacy {World TypeValue Field UndefVector FieldsVector : Type}
    (ops : PartialStructTypeOps World TypeValue Field UndefVector FieldsVector)
    (initUndefs : PartialStructTypeOps World TypeValue Field UndefVector FieldsVector →
      TypeValue → FieldsVector → M World (Option UndefVector))
    (typ : TypeValue) (fields : FieldsVector) : M World (PartialStruct TypeValue UndefVector FieldsVector) := do
  match ← initUndefs ops typ fields with
  | none => throw (.errorException "This object never exists at runtime")
  | some undefs => partialStructConstructor ops typ undefs fields

def hasBottomPrefix {World TypeValue Field UndefVector FieldsVector : Type}
    (ops : PartialStructTypeOps World TypeValue Field UndefVector FieldsVector)
    (fields : FieldsVector) : Nat → Nat → M World Bool
  | 0, _ => pure false
  | remaining + 1, index => do
      let field ← ops.fieldAt fields index
      if ops.isUnionBottom field then pure true
      else hasBottomPrefix ops fields remaining (index + 1)

def setFalsePrefix {World TypeValue Field UndefVector FieldsVector : Type}
    (ops : PartialStructTypeOps World TypeValue Field UndefVector FieldsVector)
    (undefs : UndefVector) : Nat → Nat → M World Unit
  | 0, _ => pure ()
  | remaining + 1, index => do
      ops.setUndef undefs index (some false)
      setFalsePrefix ops undefs remaining (index + 1)

def setUndefinedTail {World TypeValue Field UndefVector FieldsVector : Type}
    (ops : PartialStructTypeOps World TypeValue Field UndefVector FieldsVector)
    (fields : FieldsVector) (start : Nat) : List Nat → UndefVector → M World UndefVector
  | [], undefs => pure undefs
  | offset :: rest, undefs => do
      let index := start + offset
      let field ← ops.fieldAt fields index
      if ops.isUnionBottom field then ops.setUndef undefs index (some true)
      setUndefinedTail ops fields start rest undefs

/--
Julia source: base/coreir.jl:75-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function partialstruct_init_undefs(@nospecialize(typ), fields::Vector{Any})
    nf = length(fields)
    minf = datatype_min_ninitialized(typ)
    for i = 1:minf
        if fields[i] === Union{}
            return nothing # disallow runtime-invalid `PartialStruct`
        end
    end
    undefs = Union{Nothing,Bool}[nothing for _ in 1:nf]
    for i in 1:minf
        undefs[i] = false
    end
    for i = minf+1:nf
        if fields[i] === Union{}
            undefs[i] = true
        end
    end
    return undefs
end
```
-/
def partialStructInitUndefs {World TypeValue Field UndefVector FieldsVector : Type}
    (ops : PartialStructTypeOps World TypeValue Field UndefVector FieldsVector)
    (typ : TypeValue) (fields : FieldsVector) : M World (Option UndefVector) := do
  let fieldCount := ops.fieldsLength fields
  let minimumInitialized := ops.datatypeMinNinitialized typ
  if ← hasBottomPrefix ops fields minimumInitialized 1 then
    pure none
  else do
    let undefs ← ops.newUndefs fieldCount
    let _ ← setFalsePrefix ops undefs minimumInitialized 1
    let undefs ← setUndefinedTail ops fields (minimumInitialized + 1)
      (List.range (fieldCount - minimumInitialized)) undefs
    pure (some undefs)

structure PartialStructEqualityOps (World TypeValue UndefVector FieldsVector Field : Type) where
  sameTypeIdentity : TypeValue → TypeValue → Bool
  equalUndefs : UndefVector → UndefVector → M World Bool
  equalFields : FieldsVector → FieldsVector → M World Bool

/--
Julia source: base/coreir.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
a::PartialStruct == b::PartialStruct = a.typ === b.typ && a.undefs == b.undefs && a.fields == b.fields
```
-/
def partialStructEqual {World TypeValue UndefVector FieldsVector Field : Type}
    (ops : PartialStructEqualityOps World TypeValue UndefVector FieldsVector Field)
    (a b : PartialStruct TypeValue UndefVector FieldsVector) : M World Bool := do
  if !ops.sameTypeIdentity a.typ b.typ then
    pure false
  else if !(← ops.equalUndefs a.undefs b.undefs) then
    pure false
  else
    ops.equalFields a.fields b.fields

inductive PartialStructProperty (UndefVector Value : Type) where
  | undefs (value : UndefVector)
  | other (value : Value)

structure PartialStructGetOps (World PartialStructValue UndefVector Value : Type) where
  getfield : PartialStructValue → String → M World Value
  assertUndefs : Value → M World UndefVector

/--
Julia source: base/coreir.jl:97-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.getproperty(pstruct::Core.PartialStruct, name::Symbol)
    name === :undefs && return getfield(pstruct, :undefs)::Vector{Union{Nothing,Bool}}
    return getfield(pstruct, name)
end
```
-/
def partialStructGetProperty {World PartialStructValue UndefVector Value : Type}
    (ops : PartialStructGetOps World PartialStructValue UndefVector Value)
    (pstruct : PartialStructValue) (name : String) :
    M World (PartialStructProperty UndefVector Value) := do
  let field ← ops.getfield pstruct name
  if name == "undefs" then
    pure (.undefs (← ops.assertUndefs field))
  else
    pure (.other field)

/--
Julia source: base/coreir.jl:102-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    struct InterConditional
        slot::Int
        thentype
        elsetype
    end

Similar to `Conditional`, but conveys inter-procedural constraints imposed on call arguments.
This is separate from `Conditional` to catch logic errors: the lattice element name is `InterConditional`
while processing a call, then `Conditional` everywhere else.
"""
Core.InterConditional
```
-/
structure InterConditional (ThenType ElseType : Type) where
  slot : I64
  thentype : ThenType
  elsetype : ElseType

-- UNTRANSLATED
-- Source: base/coreir.jl:115-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     alias::InterMustAlias
-- 
-- This lattice element is used in a very similar way as `InterConditional`, but corresponds to `MustAlias`.
-- """
-- Core.InterMustAlias
-- /Source
-- Reason: Core.InterMustAlias is compiler-owned; this file only documents and names the built-in type.

end JuliaLean.base.coreir

namespace JuliaLean.MiscCov.CoreIR

/-- A lattice element of `fields`: we only need whether it is `Union{}` and whether it
is a `Vararg`. -/
structure Lat where
  tag : Nat
  isBottom : Bool
  isVararg : Bool
  deriving DecidableEq, Repr

/-- What `PartialStruct` checks of `typ`: `fieldcount_noerror(typ)` (`none` for a
variable-length tuple), `typ <: Tuple`, and `datatype_min_ninitialized(typ)`. -/
structure TypInfo where
  id : Nat
  fldcnt : Option Nat
  isTuple : Bool
  minInit : Nat
  deriving DecidableEq, Repr

/-- `undefs` entries: `nothing`, `false`, `true`. -/
abbrev Undef := Option Bool

structure PartialStruct where
  typ : TypInfo
  undefs : List Undef
  fields : List Lat
  deriving DecidableEq, Repr

/-- `Core.PhiNode() = Core.PhiNode(Int32[], Any[])`, `base/coreir.jl:3`: the edges and
values of the node. -/
def phiNode : List Int × List Lat := ([], [])

/-- The conditions asserted by `Core.PartialStruct(typ::Type, undefs, fields)`,
`base/coreir.jl:50-64`, in order; `none` is a `BoundsError` from `fields[end]` on an
empty vector. -/
def mk3Checks (typ : TypInfo) (undefs : List Undef) (fields : List Lat) : Option Bool :=
  match typ.fldcnt with
  | some n => some ((n == fields.length) && fields.length == undefs.length && loopOk)
  | none =>
    match fields.getLast? with
    | none => none
    | some f => some (typ.isTuple && f.isVararg && typ.minInit == fields.length - 1 &&
        undefs.getLast? == some none && fields.length == undefs.length && loopOk)
where
  /-- `for i = 1:length(fields); fields[i] === Union{} && @assert undefs[i] === true; end` -/
  loopOk : Bool := (List.range fields.length).all fun i =>
    !(fields.getD i ⟨0, false, false⟩).isBottom || undefs.getD i none == some true

/-- `Core.PartialStruct(typ::Type, undefs, fields)`, `base/coreir.jl:50-66`: every failed
`@assert` throws `AssertionError`. -/
def mk3 (typ : TypInfo) (undefs : List Undef) (fields : List Lat) : M PartialStruct :=
  match mk3Checks typ undefs fields with
  | none => .error .boundsError
  | some true => .ok ⟨typ, undefs, fields⟩
  | some false => .error .assertionError

/-- `partialstruct_init_undefs(typ, fields)`, `base/coreir.jl:75-93`; `none` is the
returned `nothing`. Indices are 1-based in Julia. -/
def initUndefs (typ : TypInfo) (fields : List Lat) : Option (List Undef) :=
  let nf := fields.length
  let minf := typ.minInit
  if (fields.take minf).any (·.isBottom) then none
  else some ((List.range nf).map fun i =>
    if i < minf then some false
    else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none)

/-- `Core.PartialStruct(typ, fields::Vector{Any})`, `base/coreir.jl:69-73`. -/
def mk2 (typ : TypInfo) (fields : List Lat) : M PartialStruct :=
  match initUndefs typ fields with
  | none => .error (.errorException "This object never exists at runtime")
  | some undefs => mk3 typ undefs fields

/-- `a::PartialStruct == b::PartialStruct`, `base/coreir.jl:95`. -/
def eq (a b : PartialStruct) : Bool := a.typ == b.typ && a.undefs == b.undefs && a.fields == b.fields

/-- `getproperty(pstruct::PartialStruct, name)`, `base/coreir.jl:97-100`. -/
inductive Field | typ | undefs | fields
def getproperty (p : PartialStruct) : Field → (TypInfo ⊕ List Undef ⊕ List Lat)
  | .undefs => .inr (.inl p.undefs)
  | .typ => .inl p.typ
  | .fields => .inr (.inr p.fields)

end JuliaLean.MiscCov.CoreIR
