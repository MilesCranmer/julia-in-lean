import JuliaLean.base.runtime_internals
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.runtime_internals.LegacyRuntime
open JuliaLean JuliaLean.base.runtime_internals JuliaLean.Registry
open JuliaLean.base.io (M Error)

section dispatch
variable {World V D N Mod P Sym : Type} (ops : TypeOps World V D N Mod P Sym)

theorem fieldindexDispatch_datatype (t : V) (dt : D) (name : Sym) (error : Bool)
    (kind : ops.asDatatype t = some dt) :
    fieldindexDispatch ops t name error = fieldindexDataType ops dt name error := by
  simp [fieldindexDispatch, kind]

theorem fieldindexDispatch_union (t : V) (a b : V) (name : Sym) (error : Bool)
    (datatype : ops.asDatatype t = none) (kind : ops.asUnion t = some (a, b)) :
    fieldindexDispatch ops t name error = fieldindexUnion ops t name error := by
  simp [fieldindexDispatch, datatype, kind]

theorem fieldindexDispatch_unionall (t : V) (name : Sym) (error : Bool)
    (datatype : ops.asDatatype t = none) (union : ops.asUnion t = none)
    (kind : ops.egal (ops.unwrap t) t = false) :
    fieldindexDispatch ops t name error = fieldindexUnionall ops t name error := by
  simp [fieldindexDispatch, datatype, union, kind]

theorem fieldindexDispatch_missing (t : V) (name : Sym) (error : Bool)
    (datatype : ops.asDatatype t = none) (union : ops.asUnion t = none)
    (kind : ops.egal (ops.unwrap t) t = true) :
    fieldindexDispatch ops t name error = throw (.jl (.methodError "fieldindex")) := by
  simp [fieldindexDispatch, datatype, union, kind]

end dispatch

/-- The advertised return type applies to every Type input, including the empty type. -/
def HasfieldTotal : Prop :=
  ∀ (World V D N Mod P Sym : Type) (ops : TypeOps World V D N Mod P Sym)
    (t : V) (name : Sym) (world : World),
    ∃ result after, hasfield (fun t name error => fieldindexDispatch ops t name error) t name world =
      some (.ok (result, after))


/-- `iskindtype` claims all accepted kinds are concrete. -/
def KindsConcrete : Prop :=
  ∀ (World V D N Mod P Sym : Type) (ops : TypeOps World V D N Mod P Sym) t,
    iskindtype ops t = true → isconcretetype ops t = true

/-- The predicates read AnyType's runtime identity and abstract flags.
The empty type has no DataType or nonempty-Union descriptor. -/
def anyTypeOps : TypeOps Unit String String String Unit Unit String where
  unwrap := id
  asDatatype := fun name => if name == "Union{}" then none else some name
  datatypeValue := id
  asUnion := fun _ => none
  isTypeEq := fun _ => false
  isTypeEgal := fun _ => false
  isAType := fun _ => true
  isTypeVar := fun _ => false
  typeParameter := fun t => pure t
  typeof := fun _ => "DataType"
  coreTypeof := fun _ => pure "DataType"
  egal := (· == ·)
  egalName := (· == ·)
  bottom := "Union{}"
  any := "Any"
  typeOfBottomType := "Core.TypeofBottom"
  coreTypeofBottom := "Core.TypeofBottom"
  kindTypes := ["Core.AnyType", "DataType", "UnionAll", "Union", "TypeEq", "Core.TypeEgal", "Core.TypeofBottom"]
  tupleName := "Tuple"
  namedTupleName := "NamedTuple"
  nameOf := id
  name := id
  module := fun _ => ()
  nameFlags := fun name => JInt.lit .u8 (if name == "Core.AnyType" then 1 else 0)
  dataFlags := fun name => JInt.lit .u16 (if name == "Core.AnyType" then 0 else 2)
  names := fun _ => []
  wrapper := id
  parameter := fun t _ => pure t
  parameters := fun _ => pure []
  symbolTuple := fun _ => none
  fieldtypes := fun _ => pure []
  isTuple := fun _ => false
  isVaTuple := fun _ => false
  isVararg := fun _ => false
  unwrapVararg := id
  tupleType := fun _ => pure "Tuple"
  asTypeCollection := fun _ => none
  rewrapUnionall := fun body _ => pure body
  hasInstance := fun _ => pure false
  layout := fun _ => ()
  isNull := fun _ => true
  loadLayout := fun _ => throw (.foreignError "UndefRefError" "null datatype layout")
  constFields := fun _ => ()
  atomicFields := fun _ => ()
  loadUInt32 := fun _ _ => pure (JInt.lit .u32 0)
  nativeFieldIndex := fun _ _ _ => pure (JInt.lit .i32 0)
  nfields := fun _ => pure (i 0)
  coreSizeof := fun _ => pure (i 0)
  applicable := fun _ _ => pure false
  isdefined := fun _ _ => pure false
  assertType := pure
  typeintersect := fun _ _ => pure "Union{}"
  morespecific := fun _ _ => pure (JInt.lit .i32 0)

theorem hasfieldTotal_refuted : ¬ HasfieldTotal := by
  intro promised
  obtain ⟨result, after, run⟩ :=
    promised Unit String String String Unit Unit String anyTypeOps "Union{}" "name" ()
  change (some (Except.error (Error.jl (.methodError "fieldindex"), ())) :
    Option (Except (Error × Unit) (Bool × Unit))) = some (Except.ok (result, after)) at run
  cases Option.some.inj run

theorem kindsConcrete_refuted : ¬ KindsConcrete := by
  intro promised
  have bad := promised Unit String String String Unit Unit String anyTypeOps "Core.AnyType" rfl
  change false = true at bad
  contradiction

def entries : List Entry := [
  { id := "runtimecov-hasfield-kind-types", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["hasfield(::Type, ::Symbol)", "fieldindex"]
    statement := "hasfield(T, name) returns a Bool for every type T."
    source := "base/runtime_internals.jl hasfield docstring", status := .refuted
    prop := ``HasfieldTotal, thm := some ``hasfieldTotal_refuted
    issue := "none found (queries: hasfield Union{}; hasfield MethodError; fieldindex TypeEq)" },
  { id := "runtimecov-iskindtype-abstract-kind", juliaFile := "base/runtime_internals.jl"
    juliaFns := ["iskindtype"]
    statement := "Every type iskindtype accepts is concrete, as its docstring states."
    source := "base/runtime_internals.jl:1041-1048 (iskindtype docstring)", status := .refuted
    prop := ``KindsConcrete, thm := some ``kindsConcrete_refuted
    issue := "none found (queries: iskindtype; AnyType abstract kind; related PRs #61915 and #58774)" }
]

end JuliaLean.Proofs.base.runtime_internals.LegacyRuntime
