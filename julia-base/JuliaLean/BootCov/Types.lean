import JuliaLean.BootCov.Basic

/-!
Type-object functions of `base/boot.jl` and `base/essentials.jl` (master
`bbfa0ce4150`): `Typeof`, `TypeVar`, `UnionAll`, `typename`, the
`unwrap_unionall` family, `Vararg` helpers, `datatype_min_ninitialized`,
`has_typevar` and the `TypeApp` machinery.
-/

namespace JuliaLean.BootCov.Types

open JuliaLean
open JuliaLean.BootCov

mutual
/-- Typevar ids free in a type (`jl_has_free_typevars` / `jl_has_typevar`). -/
def freeVars : JType → List Nat
  | .dt _ _ ps => freeVarsList ps
  | .union a b => freeVars a ++ freeVars b
  | .bottom => []
  | .tvar id _ _ _ => [id]
  | .unionAll v body => freeVarsBound v ++ (freeVars body).filter (· ≠ varId v)
  | .vararg T N => freeVarsOpt T ++ freeVarsOpt N
  | .typeApp h p => freeVars h ++ freeVars p
  | .intParam _ => []
  | .names _ => []
  | .other _ => []
def freeVarsList : List JType → List Nat
  | [] => []
  | t :: ts => freeVars t ++ freeVarsList ts
def freeVarsOpt : Option JType → List Nat
  | none => []
  | some t => freeVars t
/-- Free variables of the bounds of a `UnionAll` variable. -/
def freeVarsBound : JType → List Nat
  | .tvar _ _ lb ub => freeVars lb ++ freeVars ub
  | _ => []
/-- The id of a `UnionAll` variable. -/
def varId : JType → Nat
  | .tvar id _ _ _ => id
  | _ => 0
end

/-- `jl_has_typevar(t, v)`, `base/essentials.jl:1288`. -/
def hasTypevar (t v : JType) : Bool := (freeVars t).contains (varId v)

/-- `jl_has_free_typevars(t)`. -/
def hasFreeTypevars (t : JType) : Bool := !(freeVars t).isEmpty

/-- `isa(x, Type)`: a type object (not a `Vararg`, not a plain parameter). -/
def isType : JType → Bool
  | .vararg _ _ => false
  | .intParam _ => false
  | .names _ => false
  | .other _ => false
  | .typeApp _ _ => false
  | .tvar _ _ _ _ => false
  | _ => true

/-- `Type{x}` and `Core.TypeEgal{x}`. -/
def typeKind (x : JType) : JType := .dt "Type" true [x]
def typeEgalKind (x : JType) : JType := .dt "TypeEgal" true [x]

/-- `(f::typeof(Typeof))(x)`, `base/boot.jl:300-307`; `typeof` is the runtime `typeof`. -/
def typeof_ (typeof : JVal → JType) (x : JVal) : JType :=
  match x with
  | .ty t => if isType t then (if hasFreeTypevars t then typeKind t else typeEgalKind t)
             else typeof x
  | _ => typeof x

/-- `(f::typeof(TypeEqOf))(x)`, `base/boot.jl:316-319`. -/
def typeEqOf (typeof : JVal → JType) (x : JVal) : JType :=
  match x with
  | .ty t => if isType t then typeKind t else typeof x
  | _ => typeof x

/-- `_typeof_captured_variable(t)`, `base/boot.jl:387`. -/
def typeofCapturedVariable (typeof : JVal → JType) (t : JVal) : JType :=
  match t with
  | .ty T => if isType T && hasFreeTypevars T then typeof t else typeof_ typeof t
  | _ => typeof_ typeof t

/-- A bound accepted by `jl_new_typevar`: a type or a typevar. -/
def isBound : JType → Bool
  | .vararg _ _ => false
  | .intParam _ => false
  | .names _ => false
  | .other _ => false
  | _ => true

/-- `_typevar(n::Symbol, lb, ub)` (`jl_new_typevar`) with object identity `fresh`;
`TypeVar(n)`, `TypeVar(n, ub)`, `TypeVar(n, lb, ub)`, `base/boot.jl:370-372`. -/
def typevar3 (fresh : Nat) (n : JVal) (lb ub : JType) : R JType :=
  match n with
  | .sym s =>
    if !isBound lb then .error (.typeError "TypeVar")
    else if !isBound ub then .error (.typeError "TypeVar")
    else .ok (.tvar fresh s lb ub)
  | _ => .error (.typeError "typeassert")
def typevar1 (fresh : Nat) (n : JVal) : R JType := typevar3 fresh n .bottom (.dt "Any" true [])
def typevar2 (fresh : Nat) (n : JVal) (ub : JType) : R JType := typevar3 fresh n .bottom ub

/-- `jl_type_unionall(v, body)` (`src/jltypes.c:1054-1099`). -/
def typeUnionall (v body : JType) : R JType :=
  match body with
  | .vararg T N =>
    let tHas := match T with | some t => hasTypevar t v | none => false
    let nHas := match N with | some n => hasTypevar n v | none => false
    if !tHas && !nHas then .ok body
    else if tHas && nHas then .error (.error "Wrapping `Vararg` directly in UnionAll is disallowed")
    else if tHas then
      match T with
      | some t => .ok (.vararg (some (if hasTypevar t v then .unionAll v t else t)) N)
      | none => .ok body
    else .ok (.vararg T none)
  | .intParam _ | .names _ | .other _ => .error (.typeError "UnionAll")
  | _ =>
    match body, v with
    | .tvar i _ _ _, .tvar j _ _ ub => if i = j then .ok ub
        else if hasTypevar body v then .ok (.unionAll v body) else .ok body
    | _, _ => if hasTypevar body v then .ok (.unionAll v body) else .ok body

/-- `UnionAll(v, t) = ccall(:jl_type_unionall, Any, (Any, Any), v::TypeVar, t)`,
`base/boot.jl:373`. -/
def unionAllCtor (v t : JType) : R JType :=
  match v with
  | .tvar _ _ _ _ => typeUnionall v t
  | _ => .error (.typeError "typeassert")

/-- `unwrap_unionall(a)`, `base/essentials.jl:544-550`. -/
def unwrapUnionall : JType → JType
  | .unionAll _ b => unwrapUnionall b
  | t => t

/-- `rewrap_unionall(t, u)`, `base/essentials.jl:552-558`. -/
def rewrapUnionall (t : JType) : JType → R JType
  | .unionAll v b => do
    let inner ← rewrapUnionall t b
    unionAllCtor v inner
  | _ => .ok t

/-- `!isdefined(t, :N) || t.N === u.var` for a `Vararg` length `N`. -/
def lengthIsVar : Option JType → JType → Bool
  | none, _ => true
  | some (.tvar i _ _ _), v => i == varId v
  | some _, _ => false

/-- `rewrap_unionall(t::Core.TypeofVararg, u)`, `base/essentials.jl:560-571`. -/
def rewrapUnionallVararg (T N : Option JType) (u : JType) : R JType :=
  match T, u with
  | none, _ => .ok (.vararg T N)
  | some t, .unionAll v b =>
    match rewrapUnionall t (.unionAll v b) with
    | .error e => .error e
    | .ok T' => if lengthIsVar N v then .ok (.vararg (some T') none) else .ok (.vararg (some T') N)
  | some _, _ => .ok (.vararg T N)

mutual
/-- Substitute typevar `id` by `r` (the instantiation `u{r}`). -/
def subst (id : Nat) (r : JType) : JType → JType
  | .dt n a ps => .dt n a (substList id r ps)
  | .union a b => .union (subst id r a) (subst id r b)
  | .bottom => .bottom
  | .tvar i n lb ub => if i = id then r else .tvar i n (subst id r lb) (subst id r ub)
  | .unionAll v b => .unionAll (subst id r v) (subst id r b)
  | .vararg T N => .vararg (substOpt id r T) (substOpt id r N)
  | .typeApp h p => .typeApp (subst id r h) (subst id r p)
  | .intParam n => .intParam n
  | .names s => .names s
  | .other s => .other s
def substList (id : Nat) (r : JType) : List JType → List JType
  | [] => []
  | t :: ts => subst id r t :: substList id r ts
def substOpt (id : Nat) (r : JType) : Option JType → Option JType
  | none => none
  | some t => some (subst id r t)
end

/-- `body{nv}`: instantiate the outermost variable of a `UnionAll`. -/
def instantiate (u r : JType) : R JType :=
  match u with
  | .unionAll v b => .ok (subst (varId v) r b)
  | _ => .error (.typeError "Type{...} expression")

/-- `rename_unionall(u)`, `base/essentials.jl:574-582`; fresh typevar ids start at `next`. -/
def renameUnionall (next : Nat) : JType → R (JType × Nat)
  | .unionAll v b => do
    match v with
    | .tvar _ name lb ub =>
      let (b', next') ← renameUnionall next b
      let body ← unionAllCtor v b'
      let nv := JType.tvar next' name lb ub
      let inst ← instantiate body nv
      let r ← unionAllCtor nv inst
      pure (r, next' + 1)
    | _ => .error (.typeError "typeassert")
  | u => .ok (u, next)

/-- `widen_diagonal(t, troot)` (`jl_widen_diagonal`), `base/essentials.jl:585-587`. -/
def widenDiagonal (widen : JType → JType → JType) (t troot : JType) : JType := widen t troot

/-- `isvarargtype(t)`, `base/essentials.jl:589-591`. -/
def isvarargtype : JType → Bool
  | .vararg _ _ => true
  | _ => false

/-- `isvatuple(t)`, `base/essentials.jl:593-601`. -/
def isvatuple (t : JType) : Bool :=
  match unwrapUnionall t with
  | .dt _ _ ps => decide (ps.length > 0) && (match ps.getLast? with
      | some p => isvarargtype p | none => false)
  | _ => false

/-- `unwrapva(t)`, `base/essentials.jl:603-606`. -/
def unwrapva : JType → JType
  | .vararg (some T) _ => T
  | .vararg none _ => .dt "Any" true []
  | t => t

/-- `unconstrain_vararg_length(va) = Vararg{unwrapva(va)}`, `base/essentials.jl:608-613`. -/
def unconstrainVarargLength (va : JType) : JType := .vararg (some (unwrapva va)) none

/-- The `Tuple` branch of `datatype_min_ninitialized`, `base/essentials.jl:630-644`. -/
def tupleMinFields (ps : List JType) : Int :=
  let n : Int := ps.length
  if n = 0 then 0
  else match ps.getLast? with
    | some (.vararg _ N) =>
      let n := n - 1
      match N with
      | some (.intParam k) => n + k
      | _ => n
    | _ => n

/-- `datatype_min_ninitialized(t0)`, `base/essentials.jl:617-646`; `nfields name` is
`length(t.name.names)` and `nuninit name` is `t.name.n_uninitialized`. -/
def datatypeMinNinitialized (nfields nuninit : String → Nat) (t0 : JType) : Int :=
  match unwrapUnionall t0 with
  | .dt name abs ps =>
    if abs then 0
    else if name = "NamedTuple" then
      match ps with
      | .names syms :: _ => syms.length
      | _ :: types :: _ =>
        match unwrapUnionall types with
        | .dt "Tuple" _ tps => tupleMinFields tps
        | _ => 0
      | _ => 0
    else if name = "Tuple" then tupleMinFields ps
    else (nfields name : Int) - nuninit name
  | _ => 0

/-- `typename(a)`, `base/boot.jl:1310-1318`: the type name of a `DataType`, of a `Union`
whose members share it, and of a `UnionAll` body; `TypeNameError` otherwise. -/
def typename : JType → R String
  | .dt name _ _ => .ok name
  | .union a b => do
    let ta ← typename a
    let tb ← typename b
    if ta = tb then pure tb else .error .typeName
  | .unionAll _ body => typename body
  | _ => .error .typeName

/-- `(>:)(a, b) = (b <: a)` and `(!==)(a, b) = !(a === b)`, `base/boot.jl:1322-1323`. -/
def supertypeOf {α : Type} (sub : α → α → Bool) (a b : α) : Bool := sub b a
def notEgal {α : Type} (egal : α → α → Bool) (a b : α) : Bool := !egal a b

/-- `TypeApp(head, param) = new(head, param)`, `base/boot.jl:420-422`. -/
def typeAppCtor (head param : JType) : JType := .typeApp head param

/-- `_contains_typeapp(x)`, `base/boot.jl:426-434`. -/
def containsTypeapp : JType → Bool
  | .typeApp _ _ => true
  | .unionAll _ body => containsTypeapp body
  | _ => false

/-- The nested chain `TypeApp(TypeApp(tc, p1), p2), ...` built by the loops of
`apply_type_or_typeapp`. -/
def typeAppChain (tc : JType) (params : List JType) : JType :=
  params.foldl typeAppCtor tc

/-- `apply_type_or_typeapp(tc, params...)`, `base/boot.jl:436-467`; `applyType` is the
`apply_type` builtin. -/
def applyTypeOrTypeapp (applyType : JType → List JType → R JType) (tc : JType)
    (params : List JType) : R JType :=
  match tc with
  | .tvar _ _ _ _ | .typeApp _ _ => .ok (typeAppChain tc params)
  | _ => if params.any containsTypeapp then .ok (typeAppChain tc params)
         else applyType tc params

/-- `resolve_typegroup(mod, typevars, struct_infos, old_types)`, `base/boot.jl:403-409`:
an empty typegroup returns `()`, otherwise the runtime resolves it. -/
def resolveTypegroup (resolve : List JVal → List JVal → List JVal → JVal)
    (typevars structInfos oldTypes : List JVal) : JVal :=
  if typevars.length = 0 then .tuple [] else resolve typevars structInfos oldTypes

end JuliaLean.BootCov.Types
