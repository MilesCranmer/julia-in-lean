import JuliaLean.RuntimeCov.Common

/-!
`base/runtime_internals.jl`: field reflection on types: `_fieldnames`,
`fieldname`, `fieldnames`, `hasfield`, `nameof`/`parentmodule` of types,
field `isconst`/`isfieldatomic`, `fieldoffset`, `fieldindex` and its helpers,
`fieldcount`, `fieldtypes`, `propertynames` and `hasproperty`.

A type is a `DataType` record, a `Union`, a `UnionAll` (its body), `Union{}`,
or one of master's type kinds (`TypeEq` for `Type{T}` values, `Core.TypeEgal`
carrying the `DataType` that is `typeof(T)`).  Runtime queries
(`jl_field_index`, field offsets and types, the type-name wrapper) are inputs.
-/

namespace JuliaLean.RuntimeCov.Fields

open JuliaLean.RuntimeCov

/-- A `Core.TypeName`: the fields the reflection code reads. -/
structure TName where
  name : Sym
  module : String
  names : List Sym
  isNamedTuple : Bool
  isTuple : Bool
  mutable : Bool
  abstract : Bool
  /-- `constfields`/`atomicfields` bitmaps as 0-based field indices; `none` is `C_NULL`. -/
  constfields : Option (List Nat)
  atomicfields : Option (List Nat)
  deriving DecidableEq, Repr

/-- A `DataType`. For `NamedTuple` types, `ntNames` is `parameters[1]` when it
is a tuple and `ntTypesCount` is `datatype_fieldcount(parameters[2])` when that
is a `Tuple` `DataType`. -/
structure DTy where
  tn : TName
  ntNames : Option (List Sym)
  ntTypesCount : Option Nat
  isvatuple : Bool
  ntypes : Nat
  deriving DecidableEq, Repr

inductive Ty where
  | dt (d : DTy)
  | union (a b : Ty)
  | unionAll (body : Ty)
  | bottom
  | typeEq
  | typeEgal (kind : DTy)
  | other
  deriving DecidableEq, Repr

/-- `unwrap_unionall(t)`. -/
def unwrap : Ty → Ty
  | .unionAll b => unwrap b
  | t => t

/-- `t isa Type{<:Tuple}` (`t <: Tuple`): the dispatch test for the tuple methods. -/
def isTupleType : Ty → Bool
  | .dt d => d.tn.isTuple
  | .union a b => isTupleType a && isTupleType b
  | .unionAll b => isTupleType b
  | .bottom => true
  | _ => false

/-! ## Names -/

/-- `_fieldnames(t)`, base/runtime_internals.jl:237-246. -/
def fieldnamesRaw (d : DTy) : Rt (List Sym) :=
  if d.tn.isNamedTuple then
    match d.ntNames with
    | some ns => .ok ns
    | none => .error (.argumentError "type does not have definite field names")
  else .ok d.tn.names

/-- `datatype_fieldcount(t)`, lines 1376-1396. -/
def datatypeFieldcount (d : DTy) : Option Nat :=
  if d.tn.isNamedTuple then
    match d.ntNames with
    | some ns => some ns.length
    | none => d.ntTypesCount
  else if d.tn.abstract then none
  else if d.tn.isTuple then (if d.isvatuple then none else some d.ntypes)
  else some d.tn.names.length

/-- `_typename_noerror(t)`, lines 1398-1409. -/
def typenameNoerror : Ty → Option TName
  | .unionAll b => typenameNoerror b
  | .dt d => some d.tn
  | .union a b =>
    match typenameNoerror a with
    | none => none
    | some an => if typenameNoerror b = some an then some an else none
  | _ => none

/-- `_fieldcount_noerror(t)`, lines 1440-1454. -/
def fieldcountNoerror : Ty → Option Nat
  | .bottom => some 0
  | .unionAll b => fieldcountNoerror b
  | .union a b =>
    if typenameNoerror (.union a b) = none then none
    else match fieldcountNoerror a with
      | none => none
      | some ac => if fieldcountNoerror b = some ac then some ac else none
  | .dt d => datatypeFieldcount d
  | _ => none

/-- `fieldcount_noerror(t)`, lines 1489-1491. -/
def fieldcountNoerrorPub (t : Ty) : Option Nat := fieldcountNoerror t

/-- `fieldcount(t)`, lines 1462-1487. -/
def fieldcount (t : Ty) : Rt Nat :=
  match t with
  | .bottom => .error (.argumentError "The empty type does not have a well-defined number of fields since it does not have instances.")
  | .typeEgal k => match datatypeFieldcount k with
    | some n => .ok n
    | none => .error (.argumentError "type does not have a definite number of fields")
  | _ =>
    match unwrap t with
    | .union a b => match fieldcountNoerror (.union a b) with
      | some n => .ok n
      | none => .error (.argumentError "type does not have a definite number of fields")
    | .typeEq => .error (.argumentError "type does not have a definite number of fields")
    | .dt d => match datatypeFieldcount d with
      | some n => .ok n
      | none => .error (.argumentError "type does not have a definite number of fields")
    | _ => .error .typeError

/-- `fieldname(t::DataType, i)`, lines 391-405, with its local helpers
`throw_not_def_field`, `throw_field_access`, `throw_need_pos_int` (392-397). -/
def fieldnameDT (d : DTy) (i : Int) : Rt Sym :=
  if d.tn.abstract then .error (.argumentError "type does not have definite field names")
  else do
    let names ← fieldnamesRaw d
    let n := names.length
    if i > n then .error (.argumentError ("Cannot access field " ++ toString i ++ " since type only has " ++ toString n ++ (if n == 1 then " field." else " fields.")))
    else if i < 1 then .error (.argumentError ("Field numbers must be positive integers. " ++ toString i ++ " is invalid."))
    else .ok (names.getD (i - 1).toNat "")

/-- The field "name" returned by `fieldname`: a `Symbol` or, for tuples, the index. -/
inductive FieldName where
  | sym (s : Sym)
  | idx (i : Int)
  deriving DecidableEq, Repr

/-- `fieldname(t, i)` over all methods, lines 391-411: the tuple method
(`Type{<:Tuple}`) is the most specific, then `DataType`, `UnionAll` (unwrap),
`Core.TypeEgal` (the kind of the parameter) and `TypeEq` (error). -/
def fieldname (t : Ty) (i : Int) : Rt FieldName :=
  if isTupleType t then do
    let n ← fieldcount t
    if i < 1 ∨ i > n then .error .boundsError else .ok (.idx i)
  else match t with
    | .dt d => FieldName.sym <$> fieldnameDT d i
    | .unionAll _ => match unwrap t with
      | .dt d => FieldName.sym <$> fieldnameDT d i
      | _ => .error .methodError
    | .typeEgal k => FieldName.sym <$> fieldnameDT k i
    | .typeEq => .error (.argumentError "type does not have definite field names")
    | _ => .error .methodError

/-- `fieldnames(t)` over all methods, lines 435-442. -/
def fieldnames (t : Ty) : Rt (List FieldName) :=
  match t with
  | .bottom => .error (.argumentError "The empty type does not have field names since it does not have instances.")
  | _ =>
    if isTupleType t then do
      let n ← fieldcount t
      pure ((List.range n).map fun (k : Nat) => .idx ((k : Int) + 1))
    else match t with
      | .typeEq => .error (.argumentError "type does not have a definite number of fields")
      | .typeEgal k => do let _ ← fieldcount (.dt k); let ns ← fieldnamesRaw k; pure (ns.map .sym)
      | _ => match unwrap t with
        | .dt d => do let _ ← fieldcount (.dt d); let ns ← fieldnamesRaw d; pure (ns.map .sym)
        | _ => .error .methodError

/-! ## Indices -/

/-- `jl_field_index(T, name, err)` for a `DataType`: the 0-based position in
its field names, `-1` if absent (an error when `err`). -/
def jlFieldIndex (d : DTy) (name : Sym) (err : Bool) : Rt Int :=
  match fieldnamesRaw d with
  | .error e => .error e
  | .ok ns =>
    match ns.idxOf? name with
    | some k => .ok k
    | none => if err then .error .fieldError else .ok (-1)

/-- `_fieldindex_maythrow` and `_fieldindex_nothrow`, lines 1330-1340, and
`fieldindex(T::DataType, name, err)`, lines 1326-1328. -/
def fieldindexDT (d : DTy) (name : Sym) (err : Bool) : Rt Int := do
  let k ← jlFieldIndex d name err
  pure (k + 1)

/-- `_fieldindex_noerror(t, name)`, lines 1426-1438. -/
def fieldindexNoerror (name : Sym) : Ty → Option Int
  | .unionAll b => fieldindexNoerror name b
  | .union a b =>
    if typenameNoerror (.union a b) = none then none
    else match fieldindexNoerror name a with
      | none => none
      | some ai => if fieldindexNoerror name b = some ai then some ai else none
  | .dt d => match fieldindexDT d name false with
    | .ok k => some k
    | .error _ => none
  | _ => none

/-- `_fieldindex_error_type(t)`, lines 1411-1424; `wrapper` is the type-name's
unwrapped `wrapper` when it is a `DataType`. -/
def fieldindexErrorType (wrapper : TName → Option DTy) (t : Ty) : Option DTy :=
  match unwrap t with
  | .dt d => if fieldcountNoerror (.dt d) = none then none else some d
  | .union a b => match typenameNoerror (.union a b) with
    | none => none
    | some tn => wrapper tn
  | _ => none

/-- `_fieldindex(t, name, err)`, lines 1350-1362. -/
def fieldindexGeneric (wrapper : TName → Option DTy) (t : Ty) (name : Sym) (err : Bool) : Rt Int :=
  match fieldindexNoerror name t with
  | none => if err then .error (.argumentError "type does not have definite fields") else .ok 0
  | some idx =>
    if idx = 0 ∧ err then
      match fieldindexErrorType wrapper t with
      | none => .error (.argumentError "type does not have definite fields")
      | some d => fieldindexDT d name true
    else .ok idx

/-- `fieldindex(t, name, err)` over all methods (lines 1326, 1342, 1346): only
`DataType`, `UnionAll` and `Union` have methods. -/
def fieldindex (wrapper : TName → Option DTy) (t : Ty) (name : Sym) (err : Bool) : Rt Int :=
  match t with
  | .dt d => fieldindexDT d name err
  | .unionAll _ | .union _ _ => fieldindexGeneric wrapper t name err
  | _ => .error .methodError

/-- `hasfield(T, name)`, line 467. -/
def hasfield (wrapper : TName → Option DTy) (t : Ty) (name : Sym) : Rt Bool := do
  let k ← fieldindex wrapper t name false
  pure (k > 0)

/-- `argument_datatype(t)` and `argument_datatypename(t)`, lines 1364-1374: the
runtime's answer. -/
def argumentDatatype {α : Type} (rt : Ty → Option α) (t : Ty) : Option α := rt t

/-! ## Names and modules of types -/

/-- `nameof(t::DataType)`, `nameof(t::UnionAll)`, lines 487-488. -/
def nameof (t : Ty) : Rt Sym :=
  match unwrap t with
  | .dt d => .ok d.tn.name
  | _ => .error .methodError

/-- `parentmodule(t::DataType)`, `parentmodule(t::UnionAll)`, lines 509-510. -/
def parentmoduleT (t : Ty) : Rt String :=
  match unwrap t with
  | .dt d => .ok d.tn.module
  | _ => .error .methodError

/-! ## Field constness and atomicity -/

/-- `isconst(t::Type, s::Int)`, lines 544-555. -/
def isconstIdx (t : Ty) (s : Int) : Bool :=
  match unwrap t with
  | .dt d =>
    if !d.tn.mutable then true
    else if ¬ (1 ≤ s ∧ s ≤ d.tn.names.length) then true
    else match d.tn.constfields with
      | none => false
      | some cs => (s - 1).toNat ∈ cs
  | _ => false

/-- `isconst(t::Type, s::Symbol)`, lines 538-543. -/
def isconstSym (t : Ty) (s : Sym) : Rt Bool :=
  match unwrap t with
  | .dt d => do let k ← fieldindexDT d s false; pure (isconstIdx (.dt d) k)
  | _ => .ok false

/-- `isfieldatomic(t::Type, s::Int)`, lines 568-579. -/
def isfieldatomicIdx (t : Ty) (s : Int) : Bool :=
  match unwrap t with
  | .dt d =>
    if !d.tn.mutable then false
    else if ¬ (1 ≤ s ∧ s ≤ d.tn.names.length) then false
    else match d.tn.atomicfields with
      | none => false
      | some cs => (s - 1).toNat ∈ cs
  | _ => false

/-- `isfieldatomic(t::Type, s::Symbol)`, lines 562-567. -/
def isfieldatomicSym (t : Ty) (s : Sym) : Rt Bool :=
  match unwrap t with
  | .dt d => do let k ← fieldindexDT d s false; pure (isfieldatomicIdx (.dt d) k)
  | _ => .ok false

/-! ## Offsets and field types -/

/-- `fieldoffset(x::DataType, idx)`, line 1273: the runtime's offset. -/
def fieldoffsetIdx (offset : DTy → Int → Nat) (d : DTy) (i : Int) : Nat := offset d i
/-- `fieldoffset(x::DataType, name)`, line 1274. -/
def fieldoffsetName (offset : DTy → Int → Nat) (d : DTy) (name : Sym) : Rt Nat := do
  let k ← fieldindexDT d name true
  pure (offset d k)
/-- `fieldoffset(x::Core.TypeEgal, idx)`, line 1275: the offset in `typeof(T)`. -/
def fieldoffsetEgal (offset : DTy → Int → Nat) (kind : DTy) (i : Int) : Nat := offset kind i

/-- `fieldtypes(T)`, lines 1513-1514: `fieldtype(T, i)` for `i in 1:fieldcount(T)`. -/
def fieldtypes {τ : Type} (fieldtype : Ty → Nat → τ) (t : Ty) : Rt (List τ) := do
  let n ← fieldcount t
  pure ((List.range n).map fun k => fieldtype t (k + 1))

/-! ## Properties of values -/

/-- What `propertynames` dispatches on, lines 1679-1682. -/
inductive Val where
  | module (names : List Sym)
  | array
  | other (t : Ty)

/-- `propertynames(x)`, `propertynames(m::Module)`, `propertynames(x::Array)`,
and `propertynames(x, private)` (which ignores the flag). -/
def propertynames (x : Val) : Rt (List FieldName) :=
  match x with
  | .module ns => .ok (ns.map .sym)
  | .array => .ok []
  | .other t => fieldnames t
def propertynamesPrivate (x : Val) (_private : Bool) : Rt (List FieldName) := propertynames x

/-- `hasproperty(x, s)`, line 1694. -/
def hasproperty (x : Val) (s : Sym) : Rt Bool := do
  let ps ← propertynames x
  pure (ps.contains (.sym s))

/-! ## Refuted: `hasfield` always returns a boolean -/

/-- The `hasfield` docstring (lines 444-466): "Return a boolean indicating
whether `T` has `name` as one of its own fields", for any `T::Type`. -/
def HasfieldTotal : Prop :=
  ∀ (wrapper : TName → Option DTy) (t : Ty) (name : Sym), ∃ b, hasfield wrapper t name = .ok b

/-- `Union{}` (and, on master, the `TypeEq` kind of `Type{Int}`) have no
`fieldindex` method. -/
theorem hasfieldTotal_refuted : ¬ HasfieldTotal := by
  intro h
  obtain ⟨b, hb⟩ := h (fun _ => none) .bottom "name"
  simp [hasfield, fieldindex, bind, Except.bind] at hb

/-! ## Proven properties -/

def sampleTN (names : List Sym) (mutable : Bool) (cf af : Option (List Nat)) : TName :=
  ⟨"T", "Main", names, false, false, mutable, false, cf, af⟩

def FieldsBodies : Prop :=
  -- a concrete non-tuple struct: `fieldname` returns the i-th name and rejects
  -- indices outside `1:nfields` with `ArgumentError`
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.abstract = false → d.tn.isTuple = false →
      ∀ i : Int, 1 ≤ i → i ≤ d.tn.names.length →
      fieldname (.dt d) i = .ok (.sym (d.tn.names.getD (i - 1).toNat ""))) ∧
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.abstract = false → d.tn.isTuple = false →
      ∀ i : Int, (i < 1 ∨ d.tn.names.length < i) → ∃ m, fieldname (.dt d) i = .error (.argumentError m)) ∧
  (∀ d : DTy, d.tn.abstract = true → d.tn.isTuple = false →
      ∀ i, ∃ m, fieldname (.dt d) i = .error (.argumentError m)) ∧
  -- tuple types: names are indices, out of range is a `BoundsError`
  (∀ d : DTy, d.tn.isTuple = true → d.tn.isNamedTuple = false → d.tn.abstract = false →
      d.isvatuple = false → ∀ i : Int, 1 ≤ i → i ≤ d.ntypes → fieldname (.dt d) i = .ok (.idx i)) ∧
  (∀ d : DTy, d.tn.isTuple = true → d.tn.isNamedTuple = false → d.tn.abstract = false →
      d.isvatuple = false → ∀ i : Int, (i < 1 ∨ d.ntypes < i) → fieldname (.dt d) i = .error .boundsError) ∧
  (∀ i, fieldname .typeEq i = .error (.argumentError "type does not have definite field names")) ∧
  -- `fieldname(t::UnionAll, i)` delegates to the unwrapped `DataType`
  (∀ b i d, isTupleType b = false → unwrap b = .dt d →
      fieldname (.unionAll b) i = FieldName.sym <$> fieldnameDT d i) ∧
  -- `fieldnames` of a struct has exactly `fieldcount` entries
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.abstract = false → d.tn.isTuple = false →
      fieldnames (.dt d) = .ok (d.tn.names.map .sym) ∧ fieldcount (.dt d) = .ok d.tn.names.length) ∧
  fieldnames .bottom = .error (.argumentError "The empty type does not have field names since it does not have instances.") ∧
  (∃ m, fieldcount .bottom = .error (.argumentError m)) ∧
  -- `fieldcount` of a union of one type name agrees with its members
  (∀ a b n, typenameNoerror (.union a b) ≠ none → fieldcountNoerror a = some n →
      fieldcountNoerror b = some n → (unwrap (.union a b) = .union a b) →
      fieldcount (.union a b) = .ok n) ∧
  (∀ t, fieldcountNoerrorPub t = fieldcountNoerror t) ∧
  -- `fieldindex(T, name, false)` of a struct is its 1-based position or 0
  (∀ d : DTy, d.tn.isNamedTuple = false → ∀ name,
      fieldindexDT d name false = .ok (match d.tn.names.idxOf? name with
        | some k => (k : Int) + 1 | none => 0)) ∧
  (∀ d : DTy, d.tn.isNamedTuple = false → ∀ name, name ∉ d.tn.names →
      fieldindexDT d name true = .error .fieldError) ∧
  -- `hasfield` on a struct: exactly its own field names
  (∀ w (d : DTy), d.tn.isNamedTuple = false → ∀ name,
      hasfield w (.dt d) name = .ok (decide (name ∈ d.tn.names))) ∧
  -- the non-throwing union query never throws
  (∀ w t name, (∃ a b, t = .union a b) ∨ (∃ b, t = .unionAll b) →
      ∃ k, fieldindex w t name false = .ok k) ∧
  (∀ (α : Type) (rt : Ty → Option α) t, argumentDatatype rt t = rt t) ∧
  (∀ b, nameof (.unionAll b) = nameof b) ∧
  (∀ d, nameof (.dt d) = .ok d.tn.name ∧ parentmoduleT (.dt d) = .ok d.tn.module) ∧
  (∀ b, parentmoduleT (.unionAll b) = parentmoduleT b) ∧
  -- field constness: immutable structs and out-of-bounds fields are const;
  -- atomic fields only exist in mutable structs, within bounds
  (∀ d : DTy, d.tn.mutable = false → ∀ s, isconstIdx (.dt d) s = true) ∧
  (∀ d : DTy, ∀ s : Int, (s < 1 ∨ d.tn.names.length < s) → isconstIdx (.dt d) s = true) ∧
  (∀ t s, isfieldatomicIdx t s = true → ∃ d, unwrap t = .dt d ∧ d.tn.mutable = true ∧
      1 ≤ s ∧ s ≤ d.tn.names.length) ∧
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.mutable = true → ∀ s, s ∉ d.tn.names →
      isconstSym (.dt d) s = .ok true) ∧
  (∀ t s, (∀ d, unwrap t ≠ .dt d) → isconstSym t s = .ok false ∧ isfieldatomicSym t s = .ok false) ∧
  (∀ off d i, fieldoffsetIdx off d i = off d i) ∧
  (∀ off d name, d.tn.isNamedTuple = false → name ∉ d.tn.names →
      fieldoffsetName off d name = .error .fieldError) ∧
  (∀ off k i, fieldoffsetEgal off k i = off k i) ∧
  (∀ (τ : Type) (ft : Ty → Nat → τ) t n, fieldcount t = .ok n → (fieldtypes ft t).map List.length = .ok n) ∧
  propertynames .array = .ok [] ∧
  (∀ x p, propertynamesPrivate x p = propertynames x) ∧
  (∀ ns s, hasproperty (.module ns) s = .ok (decide (s ∈ ns)))

theorem idxOf?_none_iff {name : Sym} {ns : List Sym} : ns.idxOf? name = none ↔ name ∉ ns := by
  simp [List.idxOf?_eq_none_iff]

theorem fieldsBodies_proven : FieldsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d h1 h2 h3 i hi1 hi2
    have h5 : ¬ (d.tn.names.length : Int) < i := by omega
    have h6 : ¬ i < 1 := by omega
    simp [fieldname, isTupleType, h3, fieldnameDT, fieldnamesRaw, h1, h2, bind, Except.bind, h5, h6,
      Functor.map, Except.map]
  · intro d h1 h2 h3 i hi
    rcases hi with hi | hi
    · have : ¬ i > (d.tn.names.length : Int) := by omega
      simp [fieldname, isTupleType, h3, fieldnameDT, fieldnamesRaw, h1, h2, bind, Except.bind, this, hi,
        Functor.map, Except.map]
    · simp [fieldname, isTupleType, h3, fieldnameDT, fieldnamesRaw, h1, h2, bind, Except.bind, hi,
        Functor.map, Except.map]
  · intro d h1 h3 i
    simp [fieldname, isTupleType, h3, fieldnameDT, h1, Functor.map, Except.map]
  · intro d h1 h2 h3 h4 i hi1 hi2
    have : ¬ (i < 1 ∨ i > (d.ntypes : Int)) := by omega
    simp [fieldname, isTupleType, h1, fieldcount, unwrap, datatypeFieldcount, h2, h3, h4, bind,
      Except.bind, this]
  · intro d h1 h2 h3 h4 i hi
    have : (i < 1 ∨ i > (d.ntypes : Int)) := by omega
    simp [fieldname, isTupleType, h1, fieldcount, unwrap, datatypeFieldcount, h2, h3, h4, bind,
      Except.bind, this]
  · intro i; simp [fieldname, isTupleType]
  · intro b i d hb hu
    have : unwrap (.unionAll b) = .dt d := hu
    simp only [fieldname, isTupleType, hb, Bool.false_eq_true, ↓reduceIte, this]
  · intro d h1 h2 h3
    simp [fieldnames, isTupleType, h3, unwrap, fieldcount, datatypeFieldcount, h1, h2, fieldnamesRaw,
      bind, Except.bind, pure, Except.pure]
  · rfl
  · exact ⟨_, rfl⟩
  · intro a b n htn ha hb hu
    simp only [fieldcount, hu, fieldcountNoerror]
    simp [htn, ha, hb]
  · intro _; rfl
  · intro d h name
    simp only [fieldindexDT, jlFieldIndex, fieldnamesRaw, h, Bool.false_eq_true, ↓reduceIte]
    cases hk : d.tn.names.idxOf? name <;> simp [bind, Except.bind, pure, Except.pure]
  · intro d h name hn
    have : d.tn.names.idxOf? name = none := idxOf?_none_iff.mpr hn
    simp [fieldindexDT, jlFieldIndex, fieldnamesRaw, h, this, bind, Except.bind]
  · intro w d h name
    simp only [hasfield, fieldindex, fieldindexDT, jlFieldIndex, fieldnamesRaw, h, Bool.false_eq_true,
      ↓reduceIte]
    cases hk : d.tn.names.idxOf? name with
    | none =>
      have := idxOf?_none_iff.mp hk
      simp [bind, Except.bind, pure, Except.pure, this]
    | some k =>
      have hm : name ∈ d.tn.names := by
        by_cases hc : name ∈ d.tn.names
        · exact hc
        · rw [idxOf?_none_iff.mpr hc] at hk; cases hk
      simp [bind, Except.bind, pure, Except.pure, hm] <;> omega
  · intro w t name ht
    rcases ht with ⟨a, b, rfl⟩ | ⟨b, rfl⟩
    · simp only [fieldindex, fieldindexGeneric]
      cases fieldindexNoerror name (.union a b) with
      | none => exact ⟨0, rfl⟩
      | some idx => exact ⟨idx, by simp⟩
    · simp only [fieldindex, fieldindexGeneric]
      cases fieldindexNoerror name (.unionAll b) with
      | none => exact ⟨0, rfl⟩
      | some idx => exact ⟨idx, by simp⟩
  · intro _ _ _; rfl
  · intro b; rfl
  · intro d; exact ⟨rfl, rfl⟩
  · intro b; rfl
  · intro d h s; simp [isconstIdx, unwrap, h]
  · intro d s hs
    have : ¬ (1 ≤ s ∧ s ≤ (d.tn.names.length : Int)) := by omega
    simp [isconstIdx, unwrap, this]
  · intro t s h
    unfold isfieldatomicIdx at h
    split at h
    · rename_i d hd
      refine ⟨d, hd, ?_⟩
      split at h
      · simp at h
      · rename_i hm
        split at h
        · simp at h
        · rename_i hb
          simp at hm
          exact ⟨hm, by omega, by omega⟩
    · simp at h
  · intro d h1 h2 s hs
    have : d.tn.names.idxOf? s = none := idxOf?_none_iff.mpr hs
    simp [isconstSym, unwrap, fieldindexDT, jlFieldIndex, fieldnamesRaw, h1, this, bind, Except.bind,
      pure, Except.pure, isconstIdx, h2]
  · intro t s h
    constructor
    · unfold isconstSym; split
      · rename_i d hd; exact absurd hd (h d)
      · rfl
    · unfold isfieldatomicSym; split
      · rename_i d hd; exact absurd hd (h d)
      · rfl
  · intro _ _ _; rfl
  · intro off d name h hn
    have : d.tn.names.idxOf? name = none := idxOf?_none_iff.mpr hn
    simp [fieldoffsetName, fieldindexDT, jlFieldIndex, fieldnamesRaw, h, this, bind, Except.bind]
  · intro _ _ _; rfl
  · intro τ ft t n h; simp [fieldtypes, h, bind, Except.bind, pure, Except.pure, Except.map]
  · rfl
  · intro _ _; rfl
  · intro ns s; simp [hasproperty, propertynames, bind, Except.bind, pure, Except.pure]

end JuliaLean.RuntimeCov.Fields
