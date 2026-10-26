import JuliaLean.BootCov.Types

/-!
Properties of the type-object functions of `base/boot.jl` and `base/essentials.jl`.
-/

namespace JuliaLean.BootCov.Types

open JuliaLean
open JuliaLean.BootCov

/-- `Typeof(x)` (`base/boot.jl:300-307`) is `Type{x}` for a type with free typevars,
`Core.TypeEgal{x}` for any other type, and `typeof(x)` for a non-type; `TypeEqOf(x)`
(lines 316-319) is `Type{x}` for every type; `_typeof_captured_variable(t)` (line 387) is
`typeof(t)` for a type with free typevars and `Typeof(t)` otherwise. -/
def TypeofKinds : Prop :=
  (∀ (typeof : JVal → JType) (t : JType), isType t = true →
    typeof_ typeof (.ty t) = (if hasFreeTypevars t then typeKind t else typeEgalKind t) ∧
    typeEqOf typeof (.ty t) = typeKind t) ∧
  (∀ (typeof : JVal → JType) (x : JVal), (∀ t, x ≠ .ty t) →
    typeof_ typeof x = typeof x ∧ typeEqOf typeof x = typeof x) ∧
  (∀ (typeof : JVal → JType) (t : JType), isType t = true → hasFreeTypevars t = true →
    typeofCapturedVariable typeof (.ty t) = typeof (.ty t)) ∧
  (∀ (typeof : JVal → JType) (t : JType), hasFreeTypevars t = false →
    typeofCapturedVariable typeof (.ty t) = typeof_ typeof (.ty t))

theorem typeofKinds : TypeofKinds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro typeof t h
    simp [typeof_, typeEqOf, h]
  · intro typeof x h
    cases x with
    | ty t => exact absurd rfl (h t)
    | _ => exact ⟨rfl, rfl⟩
  · intro typeof t h1 h2
    simp [typeofCapturedVariable, h1, h2]
  · intro typeof t h
    simp [typeofCapturedVariable, h]

/-- `TypeVar(n)`, `TypeVar(n, ub)` and `TypeVar(n, lb, ub)` (`base/boot.jl:370-372`) build a
fresh typevar named `n` with bounds `Union{}`/`Any` by default, throw `TypeError` when `n`
is not a `Symbol` or a bound is not a type; `UnionAll(v, t)` (line 373) throws `TypeError`
unless `v` is a `TypeVar`, returns `v.ub` for `t === v`, returns `t` when `v` does not occur
in `t`, and otherwise wraps `t`. -/
def TypeVarUnionAll : Prop :=
  (∀ (f : Nat) (n : String) (lb ub : JType), isBound lb = true → isBound ub = true →
    typevar3 f (.sym n) lb ub = .ok (.tvar f n lb ub)) ∧
  (∀ (f : Nat) (n : JVal) (lb ub : JType), (∀ s, n ≠ .sym s) →
    typevar3 f n lb ub = .error (.typeError "typeassert")) ∧
  (∀ (f : Nat) (n : JVal), typevar1 f n = typevar3 f n .bottom (.dt "Any" true [])) ∧
  (∀ (f : Nat) (n : JVal) (ub : JType), typevar2 f n ub = typevar3 f n .bottom ub) ∧
  (∀ (f : Nat) (n : String) (lb ub : JType), isBound ub = false →
    typevar3 f (.sym n) lb ub = .error (.typeError "TypeVar")) ∧
  (∀ (v t : JType), (∀ i n lb ub, v ≠ .tvar i n lb ub) →
    unionAllCtor v t = .error (.typeError "typeassert")) ∧
  (∀ (i : Nat) (n : String) (lb ub : JType),
    unionAllCtor (.tvar i n lb ub) (.tvar i n lb ub) = .ok ub) ∧
  (∀ (i : Nat) (n : String) (lb ub : JType) (name : String) (abs : Bool) (ps : List JType),
    unionAllCtor (.tvar i n lb ub) (.dt name abs ps) =
      .ok (if hasTypevar (.dt name abs ps) (.tvar i n lb ub) then
        .unionAll (.tvar i n lb ub) (.dt name abs ps) else .dt name abs ps))

theorem typeVarUnionAll : TypeVarUnionAll := by
  refine ⟨?_, ?_, fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro f n lb ub h1 h2
    simp [typevar3, h1, h2]
  · intro f n lb ub h
    cases n with
    | sym s => exact absurd rfl (h s)
    | _ => rfl
  · intro f n lb ub h
    simp only [typevar3, h]
    split <;> rfl
  · intro v t h
    cases v with
    | tvar i n lb ub => exact absurd rfl (h i n lb ub)
    | _ => rfl
  · intro i n lb ub
    simp [unionAllCtor, typeUnionall]
  · intro i n lb ub name abs ps
    simp only [unionAllCtor, typeUnionall]
    split <;> rfl

/-- A `UnionAll` as Julia builds it: the variable is a `TypeVar` that occurs in the body
and the body is a type other than that variable. -/
def NormalSpine : JType → Prop
  | .unionAll v b =>
    (∃ i n lb ub, v = .tvar i n lb ub ∧ hasTypevar b v = true ∧
      (∀ n' lb' ub', b ≠ .tvar i n' lb' ub') ∧
      (∀ T N, b ≠ .vararg T N) ∧ (∀ k, b ≠ .intParam k) ∧ (∀ s, b ≠ .names s) ∧
      (∀ s, b ≠ .other s)) ∧ NormalSpine b
  | _ => True

theorem unionAllCtor_normal (v b : JType)
    (h : ∃ i n lb ub, v = .tvar i n lb ub ∧ hasTypevar b v = true ∧
      (∀ n' lb' ub', b ≠ .tvar i n' lb' ub') ∧
      (∀ T N, b ≠ .vararg T N) ∧ (∀ k, b ≠ .intParam k) ∧ (∀ s, b ≠ .names s) ∧
      (∀ s, b ≠ .other s)) :
    unionAllCtor v b = .ok (.unionAll v b) := by
  obtain ⟨i, n, lb, ub, rfl, hv, hne, hva, hk, hs, ho⟩ := h
  simp only [unionAllCtor, typeUnionall]
  cases b with
  | vararg T N => exact absurd rfl (hva T N)
  | intParam k => exact absurd rfl (hk k)
  | names s => exact absurd rfl (hs s)
  | other s => exact absurd rfl (ho s)
  | tvar j n' lb' ub' =>
    have : j ≠ i := fun e => hne n' lb' ub' (by rw [e])
    simp [this, hv]
  | _ => simp [hv]

/-- `unwrap_unionall` (`base/essentials.jl:544-550`) strips every `where`, and
`rewrap_unionall(unwrap_unionall(u), u)` (lines 552-558) rebuilds `u` exactly for every
`UnionAll` Julia can construct; `rewrap_unionall(t, u)` is `t` when `u` is not a
`UnionAll`, and the `Vararg` method (lines 560-571) returns a `Vararg` without an element
type unchanged. -/
def UnwrapRewrap : Prop :=
  (∀ u : JType, ∀ v b, unwrapUnionall u ≠ .unionAll v b) ∧
  (∀ u : JType, NormalSpine u → rewrapUnionall (unwrapUnionall u) u = .ok u) ∧
  (∀ t u : JType, (∀ v b, u ≠ .unionAll v b) → rewrapUnionall t u = .ok t) ∧
  (∀ (N : Option JType) (u : JType), rewrapUnionallVararg none N u = .ok (.vararg none N)) ∧
  (∀ (T : JType) (N : Option JType) (u : JType), (∀ v b, u ≠ .unionAll v b) →
    rewrapUnionallVararg (some T) N u = .ok (.vararg (some T) N))

theorem unwrap_not_unionAll : (u : JType) → ∀ v b, unwrapUnionall u ≠ .unionAll v b
  | .unionAll _ b', v, b => by simp only [unwrapUnionall]; exact unwrap_not_unionAll b' v b
  | .dt _ _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .union _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .bottom, v, b => by intro h; simp [unwrapUnionall] at h
  | .tvar _ _ _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .vararg _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .typeApp _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .intParam _, v, b => by intro h; simp [unwrapUnionall] at h
  | .names _, v, b => by intro h; simp [unwrapUnionall] at h
  | .other _, v, b => by intro h; simp [unwrapUnionall] at h

theorem rewrap_unwrap : (u : JType) → NormalSpine u → rewrapUnionall (unwrapUnionall u) u = .ok u
  | .unionAll v b, h => by
    simp only [NormalSpine] at h
    simp only [unwrapUnionall, rewrapUnionall, rewrap_unwrap b h.2, bind, Except.bind]
    exact unionAllCtor_normal v b h.1
  | .dt _ _ _, _ => by rfl
  | .union _ _, _ => by rfl
  | .bottom, _ => by rfl
  | .tvar _ _ _ _, _ => by rfl
  | .vararg _ _, _ => by rfl
  | .typeApp _ _, _ => by rfl
  | .intParam _, _ => by rfl
  | .names _, _ => by rfl
  | .other _, _ => by rfl

theorem unwrapRewrap : UnwrapRewrap := by
  refine ⟨unwrap_not_unionAll, rewrap_unwrap, ?_, fun _ _ => rfl, ?_⟩
  · intro t u h
    cases u with
    | unionAll v b => exact absurd rfl (h v b)
    | _ => rfl
  · intro T N u h
    cases u with
    | unionAll v b => exact absurd rfl (h v b)
    | _ => rfl

/-- `typename` (`base/boot.jl:1310-1318`) sees through `where`: `typename(u)` equals
`typename(unwrap_unionall(u))` for every type; a `Union` has a type name exactly when
both members have the same one; values that are not `DataType`, `Union` or `UnionAll`
(including `Union{}`) throw `TypeNameError`. -/
def TypenameBehaviour : Prop :=
  (∀ u : JType, typename u = typename (unwrapUnionall u)) ∧
  (∀ (a b : JType) (na nb : String), typename a = .ok na → typename b = .ok nb →
    typename (.union a b) = (if na = nb then .ok nb else .error .typeName)) ∧
  (∀ (a b : JType) e, typename a = .error e → typename (.union a b) = .error e) ∧
  (∀ (n : String) (abs : Bool) (ps : List JType), typename (.dt n abs ps) = .ok n) ∧
  typename .bottom = .error .typeName ∧
  (∀ T N, typename (.vararg T N) = .error .typeName)

theorem typename_unwrap : (u : JType) → typename u = typename (unwrapUnionall u)
  | .unionAll _ b => by simp only [typename, unwrapUnionall]; exact typename_unwrap b
  | .dt _ _ _ => by rfl
  | .union _ _ => by rfl
  | .bottom => by rfl
  | .tvar _ _ _ _ => by rfl
  | .vararg _ _ => by rfl
  | .typeApp _ _ => by rfl
  | .intParam _ => by rfl
  | .names _ => by rfl
  | .other _ => by rfl

theorem typenameBehaviour : TypenameBehaviour := by
  refine ⟨typename_unwrap, ?_, ?_, fun _ _ _ => rfl, rfl, fun _ _ => rfl⟩
  · intro a b na nb ha hb
    simp only [typename, ha, hb, bind, Except.bind]
    split <;> rfl
  · intro a b e ha
    simp [typename, ha, bind, Except.bind]

/-- The `Vararg` helpers (`base/essentials.jl:589-613`): `isvarargtype` recognises exactly
`Vararg`; `unwrapva(Vararg{T,N})` is `T`, `unwrapva(Vararg)` is `Any` and other types are
unchanged; `unconstrain_vararg_length(va)` is `Vararg{unwrapva(va)}` without a length; and
`isvatuple(t)` holds exactly when `unwrap_unionall(t)` is a `DataType` whose last
parameter is a `Vararg`. -/
def VarargHelpers : Prop :=
  (∀ t : JType, isvarargtype t = true ↔ ∃ T N, t = .vararg T N) ∧
  (∀ (T : JType) (N : Option JType), unwrapva (.vararg (some T) N) = T) ∧
  (∀ N : Option JType, unwrapva (.vararg none N) = .dt "Any" true []) ∧
  (∀ t : JType, isvarargtype t = false → unwrapva t = t) ∧
  (∀ va : JType, unconstrainVarargLength va = .vararg (some (unwrapva va)) none) ∧
  (∀ t : JType, isvatuple t = true ↔
    ∃ n abs ps T N, unwrapUnionall t = .dt n abs ps ∧ ps.getLast? = some (.vararg T N))

theorem varargHelpers : VarargHelpers := by
  refine ⟨?_, fun _ _ => rfl, fun _ => rfl, ?_, fun _ => rfl, ?_⟩
  · intro t
    cases t <;> simp [isvarargtype]
  · intro t h
    cases t with
    | vararg T N => simp [isvarargtype] at h
    | _ => rfl
  · intro t
    simp only [isvatuple]
    cases hu : unwrapUnionall t with
    | dt n abs ps =>
      constructor
      · intro h
        cases hl : ps.getLast? with
        | none => simp [hl] at h
        | some p =>
          simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h
          cases p with
          | vararg T N => exact ⟨n, abs, ps, T, N, rfl, hl⟩
          | _ => simp [isvarargtype] at h
      · rintro ⟨n', abs', ps', T, N, he, hl⟩
        simp only [JType.dt.injEq] at he
        obtain ⟨_, _, h3⟩ := he
        subst h3
        cases ps with
        | nil => simp at hl
        | cons a l => simp [hl, isvarargtype]
    | _ => simp

/-- `datatype_min_ninitialized(t)` (`base/essentials.jl:617-646`) counts the fields every
instance defines: an abstract type has none; a tuple type `Tuple{P1,...,Pn}` has `n`, minus
one for a trailing unbounded `Vararg`, plus `k - 1` for a trailing `Vararg{T,k}`; a
`NamedTuple` with known names has one per name; a `NamedTuple{names,Tuple{...}}` with
unknown names counts like its tuple; any other struct has its field count minus its
possibly-undefined fields. -/
def MinNinitialized : Prop :=
  (∀ nf nu n ps, datatypeMinNinitialized nf nu (.dt n true ps) = 0) ∧
  (∀ nf nu ps, (∀ T N, ps.getLast? ≠ some (.vararg T N)) →
    datatypeMinNinitialized nf nu (.dt "Tuple" false ps) = ps.length) ∧
  (∀ nf nu ps T, datatypeMinNinitialized nf nu (.dt "Tuple" false (ps ++ [.vararg T none])) =
    ps.length) ∧
  (∀ nf nu ps T (k : Int), datatypeMinNinitialized nf nu
      (.dt "Tuple" false (ps ++ [.vararg T (some (.intParam k))])) = ps.length + k) ∧
  (∀ nf nu syms rest, datatypeMinNinitialized nf nu (.dt "NamedTuple" false (.names syms :: rest)) =
    syms.length) ∧
  (∀ nf nu v tps rest, (∀ s, v ≠ .names s) →
    datatypeMinNinitialized nf nu (.dt "NamedTuple" false (v :: .dt "Tuple" false tps :: rest)) =
      tupleMinFields tps) ∧
  (∀ nf nu n ps, n ≠ "Tuple" → n ≠ "NamedTuple" →
    datatypeMinNinitialized nf nu (.dt n false ps) = (nf n : Int) - nu n) ∧
  (∀ nf nu (u : JType), datatypeMinNinitialized nf nu u =
    datatypeMinNinitialized nf nu (unwrapUnionall u))

theorem unwrap_idem : (u : JType) → unwrapUnionall (unwrapUnionall u) = unwrapUnionall u
  | .unionAll _ b => by simp only [unwrapUnionall]; exact unwrap_idem b
  | .dt _ _ _ => by rfl
  | .union _ _ => by rfl
  | .bottom => by rfl
  | .tvar _ _ _ _ => by rfl
  | .vararg _ _ => by rfl
  | .typeApp _ _ => by rfl
  | .intParam _ => by rfl
  | .names _ => by rfl
  | .other _ => by rfl

theorem tupleMinFields_plain (ps : List JType) (h : ∀ T N, ps.getLast? ≠ some (.vararg T N)) :
    tupleMinFields ps = ps.length := by
  simp only [tupleMinFields]
  split
  · omega
  · cases hl : ps.getLast? with
    | none => rfl
    | some p =>
      cases p with
      | vararg T N => exact absurd hl (h T N)
      | _ => rfl

theorem tupleMinFields_va (ps : List JType) (T : Option JType) :
    tupleMinFields (ps ++ [.vararg T none]) = ps.length := by
  simp only [tupleMinFields, List.getLast?_concat, List.length_append, List.length_cons,
    List.length_nil]
  split <;> omega

theorem tupleMinFields_vaN (ps : List JType) (T : Option JType) (k : Int) :
    tupleMinFields (ps ++ [.vararg T (some (.intParam k))]) = ps.length + k := by
  simp only [tupleMinFields, List.getLast?_concat, List.length_append, List.length_cons,
    List.length_nil]
  split <;> omega

theorem minNinitialized : MinNinitialized := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro nf nu n ps; simp [datatypeMinNinitialized, unwrapUnionall]
  · intro nf nu ps h
    simp [datatypeMinNinitialized, unwrapUnionall, tupleMinFields_plain ps h]
  · intro nf nu ps T
    simp [datatypeMinNinitialized, unwrapUnionall, tupleMinFields_va]
  · intro nf nu ps T k
    simp [datatypeMinNinitialized, unwrapUnionall, tupleMinFields_vaN]
  · intro nf nu syms rest; simp [datatypeMinNinitialized, unwrapUnionall]
  · intro nf nu v tps rest h
    cases v with
    | names s => exact absurd rfl (h s)
    | _ => simp [datatypeMinNinitialized, unwrapUnionall]
  · intro nf nu n ps h1 h2; simp [datatypeMinNinitialized, unwrapUnionall, h1, h2]
  · intro nf nu u
    simp only [datatypeMinNinitialized, unwrap_idem]

/-- `has_typevar(t, v)` (`base/essentials.jl:1288`) finds `v` in its own body and in type
parameters, and a `where`-bound variable is not free in the `UnionAll` that binds it. -/
def HasTypevarBehaviour : Prop :=
  (∀ i n lb ub, hasTypevar (.tvar i n lb ub) (.tvar i n lb ub) = true) ∧
  (∀ i n lb ub name abs ps, hasTypevar (.dt name abs ps) (.tvar i n lb ub) =
    (freeVarsList ps).contains i) ∧
  (∀ i n lb ub b, i ∉ freeVars lb → i ∉ freeVars ub →
    hasTypevar (.unionAll (.tvar i n lb ub) b) (.tvar i n lb ub) = false)

theorem hasTypevarBehaviour : HasTypevarBehaviour := by
  refine ⟨?_, ?_, ?_⟩
  · intro i n lb ub; simp [hasTypevar, freeVars, varId]
  · intro i n lb ub name abs ps; simp [hasTypevar, freeVars, varId]
  · intro i n lb ub b h1 h2
    simp [hasTypevar, freeVars, freeVarsBound, varId, h1, h2]

/-- The `TypeApp` machinery (`base/boot.jl:420-467`): `_contains_typeapp` finds a
`TypeApp` itself or under `where`; `apply_type_or_typeapp(tc, params...)` builds the
left-nested `TypeApp` chain when the head is a `TypeVar` or `TypeApp` or some parameter
contains a `TypeApp`, and otherwise calls `apply_type(tc, params...)`; an empty typegroup
resolves to `()`. -/
def TypeAppBehaviour : Prop :=
  (∀ h p, containsTypeapp (typeAppCtor h p) = true) ∧
  (∀ v b, containsTypeapp (.unionAll v b) = containsTypeapp b) ∧
  (∀ tc p ps, typeAppChain tc (p :: ps) = typeAppChain (.typeApp tc p) ps) ∧
  (∀ (ap : JType → List JType → R JType) i n lb ub ps,
    applyTypeOrTypeapp ap (.tvar i n lb ub) ps = .ok (typeAppChain (.tvar i n lb ub) ps)) ∧
  (∀ (ap : JType → List JType → R JType) h p ps,
    applyTypeOrTypeapp ap (.typeApp h p) ps = .ok (typeAppChain (.typeApp h p) ps)) ∧
  (∀ (ap : JType → List JType → R JType) name abs qs ps, ps.any containsTypeapp = true →
    applyTypeOrTypeapp ap (.dt name abs qs) ps = .ok (typeAppChain (.dt name abs qs) ps)) ∧
  (∀ (ap : JType → List JType → R JType) name abs qs ps, ps.any containsTypeapp = false →
    applyTypeOrTypeapp ap (.dt name abs qs) ps = ap (.dt name abs qs) ps) ∧
  (∀ (res : List JVal → List JVal → List JVal → JVal) s o, resolveTypegroup res [] s o = .tuple []) ∧
  (∀ (res : List JVal → List JVal → List JVal → JVal) t ts s o,
    resolveTypegroup res (t :: ts) s o = res (t :: ts) s o)

theorem typeAppBehaviour : TypeAppBehaviour := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, ?_, ?_, fun _ _ _ => rfl, ?_⟩
  · intro ap name abs qs ps h; simp [applyTypeOrTypeapp, h]
  · intro ap name abs qs ps h; simp [applyTypeOrTypeapp, h]
  · intro res t ts s o; simp [resolveTypegroup]

/-- `(>:)(a, b)` is `b <: a` and `(!==)(a, b)` is `!(a === b)` (`base/boot.jl:1322-1323`). -/
def BootOperators : Prop :=
  (∀ {α : Type} (sub : α → α → Bool) a b, supertypeOf sub a b = sub b a) ∧
  (∀ {α : Type} (egal : α → α → Bool) a b, notEgal egal a b = !egal a b)

theorem bootOperators : BootOperators := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- `rename_unionall(u)` (`base/essentials.jl:574-582`) returns a non-`UnionAll` unchanged,
and renames the variable of `D{T} where T` to a fresh `TypeVar` with the same name and
bounds; `widen_diagonal` (lines 585-587) returns the runtime's answer. -/
def RenameUnionall : Prop :=
  (∀ next u, (∀ v b, u ≠ .unionAll v b) → renameUnionall next u = .ok (u, next)) ∧
  (∀ (next i : Nat) (n : String) (lb ub : JType) (name : String) (abs : Bool),
    renameUnionall next (.unionAll (.tvar i n lb ub) (.dt name abs [.tvar i n lb ub])) =
      .ok (.unionAll (.tvar next n lb ub) (.dt name abs [.tvar next n lb ub]), next + 1)) ∧
  (∀ (w : JType → JType → JType) t r, widenDiagonal w t r = w t r)

theorem renameUnionall_spec : RenameUnionall := by
  refine ⟨?_, ?_, fun _ _ _ => rfl⟩
  · intro next u h
    cases u with
    | unionAll v b => exact absurd rfl (h v b)
    | _ => rfl
  · intro next i n lb ub name abs
    simp [renameUnionall, bind, Except.bind, pure, Except.pure, unionAllCtor, typeUnionall,
      hasTypevar, freeVars, freeVarsList, varId, instantiate, subst, substList]

end JuliaLean.BootCov.Types
