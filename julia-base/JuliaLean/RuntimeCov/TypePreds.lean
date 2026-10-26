import JuliaLean.RuntimeCov.Common

/-!
`base/runtime_internals.jl:620-623, 815-1226, 1532-1634, 1778-1789, 1999`:
the type predicates read from `DataType` and `TypeName` flag words
(`ismutable`, `isstructtype`, `isconcretetype`, `isdispatchtuple`, ...), the
kind tests (`iskindtype`, `isType`, `isdispatchelem`), `type_parameter`,
`has_bottom_parameter`, `rewrap_free_typevars`, `to_tuple_type`,
`signature_type`, union flattening, and the subtyping-runtime wrappers
(`typeintersect`, `morespecific`, `hasintersect`).

A type is a `DataType` (its flag words and parameters), a `Union`, a
`UnionAll`, a `TypeVar`, `Union{}`, one of master's `Type{T}` kinds (`TypeEq`,
`Core.TypeEgal`), a `Vararg`, or a non-type value.  Runtime answers (subtyping,
intersection, `typeof`, free type variables) are parameters.
-/

namespace JuliaLean.RuntimeCov.TypePreds

open JuliaLean.RuntimeCov

/-- The seven kind objects that `iskindtype` names (line 1049). -/
inductive Kind where
  | anyType | dataType | unionAll | union | typeEq | typeEgal | typeofBottom
  deriving DecidableEq, Repr

/-- A `DataType`: `flags` is `dt.flags`, `nameFlags` is `dt.name.flags`, and
`kind` says whether this object is one of the kind types. -/
structure DT where
  flags : Nat
  nameFlags : Nat
  kind : Option Kind
  hasInstance : Bool
  deriving DecidableEq, Repr

inductive Ty where
  | dt (d : DT) (params : List Ty)
  | union (a b : Ty)
  | unionAll (v : Sym) (lb ub : Ty) (body : Ty)
  | tvar (v : Sym) (lb ub : Ty)
  | bottom
  | typeEq (T : Ty)
  | typeEgal (T : Ty)
  | vararg (T : Ty)
  | value (id : Nat)
  deriving Repr

/-- `unwrap_unionall(t)`. -/
def unwrap : Ty → Ty
  | .unionAll _ _ _ b => unwrap b
  | t => t

/-- `isa(t, Type)` (equivalently `isa(t, Core.AnyType)`). -/
def isTypeVal : Ty → Bool
  | .dt _ _ | .union _ _ | .unionAll _ _ _ _ | .bottom | .typeEq _ | .typeEgal _ => true
  | _ => false

def bit (w m : Nat) : Bool := w &&& m == m

/-! ## Flag predicates -/

/-- `ismutabletypename(tn)`, line 861. -/
def ismutabletypename (nameFlags : Nat) : Bool := bit nameFlags 0x2

/-- `ismutable(x)`, line 840: `typeofV x` is `typeof(x)`. -/
def ismutable (typeofV : Ty → DT) (x : Ty) : Bool := bit (typeofV x).nameFlags 0x2

/-- `ismutabletype(t)`, lines 854-859. -/
def ismutabletype (t : Ty) : Bool :=
  match unwrap t with
  | .dt d _ => ismutabletypename d.nameFlags
  | _ => false

/-- `isTypeEq`, `isTypeEgal`, `isType`, lines 1095-1109. -/
def isTypeEq : Ty → Bool | .typeEq _ => true | _ => false
def isTypeEgal : Ty → Bool | .typeEgal _ => true | _ => false
def isType (t : Ty) : Bool := isTypeEq t || isTypeEgal t

/-- `type_parameter(t::TypeEq)`, `type_parameter(t::Core.TypeEgal)`, lines 1111-1112. -/
def typeParameter : Ty → Rt Ty
  | .typeEq T => .ok T
  | .typeEgal T => .ok T
  | _ => .error .methodError

/-- `isprimitivetype(t)`, lines 885-891. -/
def isprimitivetype (t : Ty) : Bool :=
  match unwrap t with
  | .dt d _ => bit d.flags 0x0080
  | _ => false

/-- `isabstracttype(t)`, lines 1186-1192. -/
def isabstracttype (t : Ty) : Bool :=
  let t := unwrap t
  if isType t then true
  else match t with
    | .dt d _ => bit d.nameFlags 0x1
    | _ => false

/-- `isstructtype(t)`, lines 870-876. -/
def isstructtype (t : Ty) : Bool :=
  match unwrap t with
  | .dt d ps => !isprimitivetype (.dt d ps) && !isabstracttype (.dt d ps)
  | _ => false

/-- `isbitstype(t)`, line 917, and `isbits(x)`, line 924. -/
def isbitstype : Ty → Bool
  | .dt d _ => bit d.flags 0x0008
  | _ => false
def isbits (typeofV : Ty → DT) (x : Ty) : Bool := isbitstype (.dt (typeofV x) [])

/-- `objectid(x)`, lines 936-939: `jl_object_id`. -/
def objectid (oid : Ty → Nat) (x : Ty) : Nat := oid x

/-- `isdispatchtuple(t)`, line 990, and `isconcretetype(t)`, line 1161. -/
def isdispatchtuple : Ty → Bool
  | .dt d _ => bit d.flags 0x0004
  | _ => false
def isconcretetype : Ty → Bool
  | .dt d _ => bit d.flags 0x0002
  | _ => false

/-- `datatype_ismutationfree`, `datatype_isidentityfree`, lines 992, 1017. -/
def datatypeIsmutationfree (d : DT) : Bool := bit d.flags 0x0100
def datatypeIsidentityfree (d : DT) : Bool := bit d.flags 0x0200

/-- `ismutationfree(t)`, lines 1003-1015: the `t = unwrap_unionall(t)` step is the
`UnionAll` clause; `kindOf T` is `typeof(T)`, a `DataType`, on which the
function reads `datatype_ismutationfree`. -/
def ismutationfree (kindOf : Ty → DT) : Ty → Bool
  | .unionAll _ _ _ b => ismutationfree kindOf b
  | .dt d _ => datatypeIsmutationfree d
  | .typeEq T | .typeEgal T => isTypeVal T && datatypeIsmutationfree (kindOf T)
  | .union a b => ismutationfree kindOf a && ismutationfree kindOf b
  | _ => false

/-- `isidentityfree(t)`, lines 1026-1038. -/
def isidentityfree (kindOf : Ty → DT) : Ty → Bool
  | .unionAll _ _ _ b => isidentityfree kindOf b
  | .dt d _ => datatypeIsidentityfree d
  | .typeEq T | .typeEgal T => isTypeVal T && datatypeIsidentityfree (kindOf T)
  | .union a b => isidentityfree kindOf a && isidentityfree kindOf b
  | _ => false

/-- `iskindtype(t)`, line 1049: `t` is one of the seven kind objects. -/
def iskindtype : Ty → Bool
  | .dt d _ => d.kind.isSome
  | _ => false

/-- `isconcretedispatch(t)`, line 1074. -/
def isconcretedispatch (t : Ty) : Bool := isconcretetype t && !iskindtype t

/-- `v === Union{}`. -/
def isBottom : Ty → Bool | .bottom => true | _ => false

def isTypeofBottom : Ty → Bool
  | .dt d _ => d.kind == some .typeofBottom
  | _ => false

/-- `isdispatchelem(v)`, lines 1080-1083. -/
def isdispatchelem (v : Ty) : Bool :=
  isBottom v || isTypeofBottom v || isconcretedispatch v || isTypeEgal v ||
    (isTypeEq v && (match typeParameter v with | .ok T => isBottom T | .error _ => false))

/-! ## The kind objects -/

/-- The kind `DataType`s as the runtime creates them (src/jltypes.c):
`Core.AnyType` comes from `jl_new_abstracttype`; the other six are concrete
struct types (`DataType` is mutable). -/
def kindDT : Kind → DT
  | .anyType => ⟨0x0, 0x1, some .anyType, false⟩
  | .dataType => ⟨0x2, 0x2, some .dataType, false⟩
  | k => ⟨0x2, 0x0, some k, false⟩

def kindType (k : Kind) : Ty := .dt (kindDT k) []

/-! ## Structure of types -/

mutual
/-- `has_bottom_parameter(t::Core.AnyType)`, `(t::TypeVar)`, `(::Any)`,
lines 1576-1593.  The `UnionAll` clause recurses through `unwrap_unionall`. -/
def hasBottomParameter : Ty → Bool
  | .bottom => true
  | .dt _ ps => hasBottomParams ps
  | .typeEq T => hasBottomParameter T
  | .typeEgal T => hasBottomParameter T
  | .unionAll _ _ _ b => hasBottomParameter b
  | .union a b => hasBottomParameter a && hasBottomParameter b
  | .tvar _ _ ub => hasBottomParameter ub
  | _ => false
/-- The `for p in getfield(t, :parameters)` loop. -/
def hasBottomParams : List Ty → Bool
  | [] => false
  | p :: ps => hasBottomParameter p || hasBottomParams ps
end

/-- `unionlen(x)`, line 1778. -/
def unionlen : Ty → Nat
  | .union a b => unionlen a + unionlen b
  | _ => 1

/-- `_uniontypes(x, ts)`, lines 1780-1788, and `uniontypes(x)`, line 1789. -/
def uniontypesAcc : Ty → List Ty → List Ty
  | .union a b, ts => uniontypesAcc b (uniontypesAcc a ts)
  | x, ts => ts ++ [x]
def uniontypes (x : Ty) : List Ty := uniontypesAcc x []

/-- `find_free_typevars(t)`, lines 1595-1597: the runtime's list. -/
def findFreeTypevars (rt : Ty → List (Sym × Ty × Ty)) (t : Ty) : List (Sym × Ty × Ty) := rt t

def isvarargtype : Ty → Bool | .vararg _ => true | _ => false

/-- `rewrap_free_typevars(t, pre)`, lines 1612-1629: the loop runs from the last
free variable to the first, wrapping each one not in `pre`. -/
def rewrapFreeTypevars (hasFree : Ty → Bool) (ffv : Ty → List (Sym × Ty × Ty)) (t : Ty)
    (pre : List Sym) : Ty :=
  if !hasFree t then t
  else if isvarargtype t then t
  else
    (findFreeTypevars ffv t).reverse.foldl
      (fun acc (v : Sym × Ty × Ty) => if pre.contains v.1 then acc else .unionAll v.1 v.2.1 v.2.2 acc) t

/-- `typeintersect(a, b)`, line 1223: both arguments must be types. -/
def typeintersect (rt : Ty → Ty → Ty) (a b : Ty) : Rt Ty :=
  if isTypeVal a && isTypeVal b then .ok (rt a b) else .error .typeError

/-- `morespecific(a, b)` on types and on methods, lines 1225-1226. -/
def morespecific (rt : Ty → Ty → Int) (a b : Ty) : Rt Bool :=
  if isTypeVal a && isTypeVal b then .ok (rt a b != 0) else .error .typeError
def morespecificMethod (rt : Nat → Nat → Int) (a b : Nat) : Bool := rt a b != 0

/-- `hasintersect(a, b)`, line 1999. -/
def hasintersect (rt : Ty → Ty → Ty) (a b : Ty) : Rt Bool := do
  let ti ← typeintersect rt a b
  pure (!isBottom ti)

/-- `typeintersect_env(a, b)`, lines 1631-1634: the runtime's `(ti, env)` pair. -/
def typeintersectEnv {ε : Type} (rt : Ty → Ty → Ty × ε) (a b : Ty) : Ty × ε := rt a b

/-- `datatype_fieldtypes(x)`, line 622, and `get_methodtable(m)`, lines 1563-1569:
runtime answers. -/
def datatypeFieldtypes (rt : DT → List Ty) (d : DT) : List Ty := rt d
def getMethodtable {μ : Type} (rt : Nat → Option μ) (m : Nat) : Option μ := rt m

/-! ## Argument tuples -/

/-- What `to_tuple_type` receives: a `Tuple`, `AbstractArray` or `SimpleVector`
of elements (spliced into `Tuple{t...}`), or any other value. -/
inductive TTArg where
  | coll (elems : List Ty)
  | val (t : Ty)

def unwrapva : Ty → Ty | .vararg T => T | t => t
def isTVar : Ty → Bool | .tvar _ _ _ => true | _ => false

/-- `to_tuple_type(t)`, lines 1534-1552: `tupleDT` is the `Tuple` type
constructor's `DataType`; `subTuple t` is `t <: Tuple`. -/
def toTupleType (tupleDT : DT) (subTuple : Ty → Bool) (a : TTArg) : Rt Ty :=
  let t := match a with | .coll es => Ty.dt tupleDT es | .val t => t
  if isTypeVal t && subTuple t then
    match unwrap t with
    | .dt _ ps =>
      if ps.all (fun p => let p := unwrapva p; isTypeVal p || isTVar p) then .ok t
      else .error (.errorException "argument tuple type must contain only types")
    | _ => .error .typeError
  else .error (.errorException "expected tuple type")

/-- `rewrap_unionall(body, t)`: re-wrap `body` in `t`'s `UnionAll` binders. -/
def rewrapUnionall (body : Ty) : Ty → Ty
  | .unionAll v lb ub b => .unionAll v lb ub (rewrapUnionall body b)
  | _ => body

/-- `signature_type(f, argtypes)`, lines 1554-1561: `ft` is `Core.Typeof(f)`. -/
def signatureType (tupleDT : DT) (subTuple : Ty → Bool) (ft : Ty) (a : TTArg) : Rt Ty := do
  let argtypes ← toTupleType tupleDT subTuple a
  match unwrap argtypes with
  | .dt _ ps => pure (rewrapUnionall (.dt tupleDT (ft :: ps)) argtypes)
  | _ => .error .typeError

/-! ## Refuted: every kind is concrete -/

/-- The `iskindtype` docstring (lines 1041-1048): "All kinds are concrete because
types are Julia values." -/
def KindsConcrete : Prop := ∀ k, iskindtype (kindType k) = true → isconcretetype (kindType k) = true

/-- `Core.AnyType` is one of the kinds `iskindtype` accepts, and it is abstract. -/
theorem kindsConcrete_refuted : ¬ KindsConcrete := by
  intro h
  have := h .anyType rfl
  simp [kindType, kindDT, isconcretetype, bit] at this

/-! ## Proven properties -/

theorem uniontypesAcc_prefix : ∀ x ts, ∃ r, uniontypesAcc x ts = ts ++ r ∧ r.length = unionlen x ∧
    ∀ y ∈ r, ∀ a b, y ≠ .union a b
  | .union a b, ts => by
    obtain ⟨ra, ha, hla, hya⟩ := uniontypesAcc_prefix a ts
    obtain ⟨rb, hb, hlb, hyb⟩ := uniontypesAcc_prefix b (ts ++ ra)
    refine ⟨ra ++ rb, ?_, ?_, ?_⟩
    · simp [uniontypesAcc, ha, hb]
    · simp [unionlen, hla, hlb]
    · intro y hy; simp only [List.mem_append] at hy
      rcases hy with hy | hy
      · exact hya y hy
      · exact hyb y hy
  | .dt d ps, ts => ⟨[.dt d ps], rfl, rfl, by simp⟩
  | .unionAll v l u b, ts => ⟨[.unionAll v l u b], rfl, rfl, by simp⟩
  | .tvar v l u, ts => ⟨[.tvar v l u], rfl, rfl, by simp⟩
  | .bottom, ts => ⟨[.bottom], rfl, rfl, by simp⟩
  | .typeEq T, ts => ⟨[.typeEq T], rfl, rfl, by simp⟩
  | .typeEgal T, ts => ⟨[.typeEgal T], rfl, rfl, by simp⟩
  | .vararg T, ts => ⟨[.vararg T], rfl, rfl, by simp⟩
  | .value n, ts => ⟨[.value n], rfl, rfl, by simp⟩

theorem rewrap_foldl (pre : List Sym) : ∀ (fv : List (Sym × Ty × Ty)) (t : Ty),
    fv.reverse.foldl (fun acc (v : Sym × Ty × Ty) => if pre.contains v.1 then acc else .unionAll v.1 v.2.1 v.2.2 acc) t =
    (fv.filter (fun v => !pre.contains v.1)).foldr (fun v acc => Ty.unionAll v.1 v.2.1 v.2.2 acc) t
  | [], t => rfl
  | v :: vs, t => by
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, rewrap_foldl pre vs]
    by_cases h : v.1 ∈ pre
    · simp [h, List.filter_cons]
    · simp [h, List.filter_cons]

def TypePredsBodies : Prop :=
  -- the kinds
  (∀ k, iskindtype (kindType k) = true) ∧
  (∀ k, k ≠ .anyType → isconcretetype (kindType k) = true) ∧
  isabstracttype (kindType .anyType) = true ∧
  (∀ t, isconcretedispatch t = true → isconcretetype t = true ∧ iskindtype t = false) ∧
  (∀ k, isconcretedispatch (kindType k) = false) ∧
  -- a struct type is neither primitive nor abstract
  (∀ t, isstructtype t = true → isprimitivetype t = false ∧ isabstracttype t = false) ∧
  -- "If T is not a type, then return false"
  (∀ t, isTypeVal t = false → ismutabletype t = false ∧ isstructtype t = false ∧
      isprimitivetype t = false ∧ isbitstype t = false ∧ isconcretetype t = false ∧
      isabstracttype t = false ∧ isdispatchtuple t = false ∧ iskindtype t = false) ∧
  (∀ k t, isTypeVal t = false → (∀ v l u b, t ≠ .unionAll v l u b) →
      ismutationfree k t = false ∧ isidentityfree k t = false) ∧
  -- `Type{T}` kinds are abstract, never concrete or structs
  (∀ T, isabstracttype (.typeEq T) = true ∧ isabstracttype (.typeEgal T) = true ∧
      isconcretetype (.typeEq T) = false ∧ isstructtype (.typeEq T) = false) ∧
  (∀ T, isType (.typeEq T) = true ∧ isType (.typeEgal T) = true ∧
      typeParameter (.typeEq T) = .ok T ∧ typeParameter (.typeEgal T) = .ok T) ∧
  (∀ t, isType t = false → typeParameter t = .error .methodError) ∧
  -- `UnionAll` wrappers are transparent to the declared-kind predicates
  (∀ v l u b, ismutabletype (.unionAll v l u b) = ismutabletype b ∧
      isprimitivetype (.unionAll v l u b) = isprimitivetype b ∧
      isabstracttype (.unionAll v l u b) = isabstracttype b ∧
      isstructtype (.unionAll v l u b) = isstructtype b) ∧
  (∀ k v l u b, ismutationfree k (.unionAll v l u b) = ismutationfree k b) ∧
  (∀ k a b, ismutationfree k (.union a b) = (ismutationfree k a && ismutationfree k b) ∧
      isidentityfree k (.union a b) = (isidentityfree k a && isidentityfree k b)) ∧
  (∀ k d ps, ismutationfree k (.dt d ps) = datatypeIsmutationfree d ∧
      isidentityfree k (.dt d ps) = datatypeIsidentityfree d) ∧
  (∀ tf x, isbits tf x = bit (tf x).flags 0x8) ∧
  (∀ tf x, ismutable tf x = ismutabletypename (tf x).nameFlags) ∧
  (∀ oid x y, x = y → objectid oid x = objectid oid y) ∧
  -- `isdispatchelem`: `Union{}`, its type, concrete non-kinds, egality kinds,
  -- and `Type{Union{}}`
  isdispatchelem .bottom = true ∧
  (∀ T, isdispatchelem (.typeEgal T) = true) ∧
  isdispatchelem (.typeEq .bottom) = true ∧
  (∀ T, isBottom T = false → isdispatchelem (.typeEq T) = false) ∧
  (∀ t, isconcretedispatch t = true → isdispatchelem t = true) ∧
  -- `has_bottom_parameter`
  hasBottomParameter .bottom = true ∧
  (∀ d ps, Ty.bottom ∈ ps → hasBottomParameter (.dt d ps) = true) ∧
  (∀ a b, hasBottomParameter (.union a b) = (hasBottomParameter a && hasBottomParameter b)) ∧
  (∀ n, hasBottomParameter (.value n) = false) ∧
  (∀ T, hasBottomParameter (.typeEq T) = hasBottomParameter T) ∧
  (∀ t, hasBottomParameter (unwrap t) = hasBottomParameter t) ∧
  -- `unionlen` counts exactly the non-union members `uniontypes` lists
  (∀ x, (uniontypes x).length = unionlen x ∧ ∀ y ∈ uniontypes x, ∀ a b, y ≠ .union a b) ∧
  (∀ x, (∀ a b, x ≠ .union a b) → uniontypes x = [x]) ∧
  (∀ rt t, findFreeTypevars rt t = rt t) ∧
  -- `rewrap_free_typevars` wraps each free variable not in `pre`, the first
  -- one outermost
  (∀ hf ffv t pre, hf t = false → rewrapFreeTypevars hf ffv t pre = t) ∧
  (∀ hf ffv T pre, rewrapFreeTypevars hf ffv (.vararg T) pre = .vararg T) ∧
  (∀ hf ffv t pre, hf t = true → isvarargtype t = false →
      rewrapFreeTypevars hf ffv t pre =
        ((ffv t).filter (fun v => !pre.contains v.1)).foldr (fun v acc => Ty.unionAll v.1 v.2.1 v.2.2 acc) t) ∧
  -- runtime subtyping wrappers type-check their arguments
  (∀ rt a b, isTypeVal a = true → isTypeVal b = true → typeintersect rt a b = .ok (rt a b)) ∧
  (∀ rt a b, isTypeVal a = false → typeintersect rt a b = .error .typeError) ∧
  (∀ rt a b, isTypeVal a = true → isTypeVal b = true → morespecific rt a b = .ok (rt a b != 0)) ∧
  (∀ rt a b, morespecificMethod rt a b = (rt a b != 0)) ∧
  (∀ rt a b, isTypeVal a = true → isTypeVal b = true →
      hasintersect rt a b = .ok (!isBottom (rt a b))) ∧
  (∀ (ε : Type) (rt : Ty → Ty → Ty × ε) a b, typeintersectEnv rt a b = rt a b) ∧
  (∀ rt d, datatypeFieldtypes rt d = rt d) ∧
  (∀ (μ : Type) (rt : Nat → Option μ) m, getMethodtable rt m = rt m) ∧
  -- `to_tuple_type`
  (∀ tdt st es, st (.dt tdt es) = true → (∀ p ∈ es, isTypeVal (unwrapva p) = true) →
      toTupleType tdt st (.coll es) = .ok (.dt tdt es)) ∧
  (∀ tdt st es, st (.dt tdt es) = true → (∃ p ∈ es, isTypeVal (unwrapva p) = false ∧ isTVar (unwrapva p) = false) →
      toTupleType tdt st (.coll es) = .error (.errorException "argument tuple type must contain only types")) ∧
  (∀ tdt st t, st t = false → toTupleType tdt st (.val t) = .error (.errorException "expected tuple type")) ∧
  (∀ tdt st t, isTypeVal t = false → toTupleType tdt st (.val t) = .error (.errorException "expected tuple type")) ∧
  -- `signature_type` prepends `Core.Typeof(f)` to the argument types
  (∀ tdt st ft es, toTupleType tdt st (.coll es) = .ok (.dt tdt es) →
      signatureType tdt st ft (.coll es) = .ok (.dt tdt (ft :: es)))

theorem hasBottom_unwrap : ∀ t, hasBottomParameter (unwrap t) = hasBottomParameter t
  | .unionAll v l u b => by
    simp only [unwrap, hasBottom_unwrap b]
    simp [hasBottomParameter]
  | .dt _ _ | .union _ _ | .tvar _ _ _ | .bottom | .typeEq _ | .typeEgal _ | .vararg _ | .value _ => rfl

theorem hasBottomParams_of_mem : ∀ ps : List Ty, Ty.bottom ∈ ps → hasBottomParams ps = true
  | [], h => by simp at h
  | p :: ps, h => by
    simp only [hasBottomParams, Bool.or_eq_true]
    rcases List.mem_cons.mp h with h | h
    · left; subst h; simp [hasBottomParameter]
    · right; exact hasBottomParams_of_mem ps h

theorem unwrap_idem : ∀ t, unwrap (unwrap t) = unwrap t
  | .unionAll _ _ _ b => unwrap_idem b
  | .dt _ _ | .union _ _ | .tvar _ _ _ | .bottom | .typeEq _ | .typeEgal _ | .vararg _ | .value _ => rfl

theorem isprimitivetype_unwrap (t : Ty) : isprimitivetype (unwrap t) = isprimitivetype t := by
  simp only [isprimitivetype, unwrap_idem]

theorem isabstracttype_unwrap (t : Ty) : isabstracttype (unwrap t) = isabstracttype t := by
  simp only [isabstracttype, unwrap_idem]

theorem typePredsBodies_proven : TypePredsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro k; cases k <;> rfl
  · intro k hk; cases k <;> first | exact absurd rfl hk | decide
  · decide
  · intro t h; simp only [isconcretedispatch, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h
  · intro k; cases k <;> decide
  · intro t h
    unfold isstructtype at h
    split at h
    · rename_i d ps hu
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [← isprimitivetype_unwrap, hu]; exact h1
      · rw [← isabstracttype_unwrap, hu]; exact h2
    · simp at h
  · intro t h
    cases t <;> simp_all [isTypeVal, ismutabletype, isstructtype, isprimitivetype, isbitstype, isconcretetype,
      isabstracttype, isdispatchtuple, iskindtype, unwrap, isType, isTypeEq, isTypeEgal]
  · intro k t h hu
    cases t <;> simp_all [isTypeVal, ismutationfree, isidentityfree]
  · intro T
    simp [isabstracttype, unwrap, isType, isTypeEq, isTypeEgal, isconcretetype, isstructtype]
  · intro T; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro t h
    cases t <;> simp_all [isType, isTypeEq, isTypeEgal, typeParameter]
  · intro v l u b
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro _ _ _ _ _; rfl
  · intro _ _ _; exact ⟨rfl, rfl⟩
  · intro _ _ _; exact ⟨rfl, rfl⟩
  · intro _ _; rfl
  · intro _ _; rfl
  · intro oid x y h; subst h; rfl
  · rfl
  · intro T; simp [isdispatchelem, isTypeEgal]
  · simp [isdispatchelem, isTypeEq, typeParameter, isBottom]
  · intro T hT
    have h0 : isBottom (Ty.typeEq T) = false := rfl
    simp only [isdispatchelem, h0, isTypeofBottom, isconcretedispatch, isconcretetype, isTypeEgal,
      isTypeEq, typeParameter, hT]
    all_goals rfl
  · intro t h; simp [isdispatchelem, h]
  · rfl
  · intro d ps h; simp only [hasBottomParameter]; exact hasBottomParams_of_mem ps h
  · intro _ _; rfl
  · intro _; rfl
  · intro _; rfl
  · exact hasBottom_unwrap
  · intro x
    obtain ⟨r, hr, hl, hy⟩ := uniontypesAcc_prefix x []
    simp only [uniontypes, hr, List.nil_append]
    exact ⟨hl, hy⟩
  · intro x hx
    cases x with
    | union a b => exact absurd rfl (hx a b)
    | _ => rfl
  · intro _ _; rfl
  · intro hf ffv t pre h; simp [rewrapFreeTypevars, h]
  · intro hf ffv T pre
    unfold rewrapFreeTypevars
    cases hf (.vararg T) <;> rfl
  · intro hf ffv t pre h1 h2
    simp only [rewrapFreeTypevars, h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, findFreeTypevars]
    exact rewrap_foldl pre (ffv t) t
  · intro rt a b ha hb; simp [typeintersect, ha, hb]
  · intro rt a b ha; simp [typeintersect, ha]
  · intro rt a b ha hb; simp [morespecific, ha, hb]
  · intro _ _ _; rfl
  · intro rt a b ha hb
    simp [hasintersect, typeintersect, ha, hb, bind, Except.bind, pure, Except.pure]
  · intro _ _ _ _; rfl
  · intro _ _; rfl
  · intro _ _ _; rfl
  · intro tdt st es hs hp
    have hall : es.all (fun p => let p := unwrapva p; isTypeVal p || isTVar p) = true := by
      simp only [List.all_eq_true]
      intro p hpm; simp [hp p hpm]
    have ht : isTypeVal (.dt tdt es) = true := rfl
    simp [toTupleType, ht, hs, unwrap, hall]
  · intro tdt st es hs hp
    have hall : es.all (fun p => let p := unwrapva p; isTypeVal p || isTVar p) = false := by
      obtain ⟨p, hpm, h1, h2⟩ := hp
      simp only [List.all_eq_false]
      exact ⟨p, hpm, by simp [h1, h2]⟩
    have ht : isTypeVal (.dt tdt es) = true := rfl
    simp [toTupleType, ht, hs, unwrap, hall]
  · intro tdt st t h; simp [toTupleType, h]
  · intro tdt st t h; simp [toTupleType, h]
  · intro tdt st ft es h
    simp [signatureType, h, bind, Except.bind, unwrap, rewrapUnionall, pure, Except.pure]

end JuliaLean.RuntimeCov.TypePreds
