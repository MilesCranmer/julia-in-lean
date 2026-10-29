import JuliaLean.src.julia_h
import JuliaLean.src.jltypes_c

/-!
TypeMaps and method-table signature indexing (`src/typemap.c`).

The full tree structure of `typemap.c` (`TypemapEntry` linked lists sorted into
`(leaf sigs..., simple sigs..., other sigs...)`, `mtcache` insertion-ordered
dictionaries, `MAX_METHLIST_COUNT = 6` list-to-level and `doublesplit`
conversions, and `Type{Union{}}` early-visit pruning via `typemap_bottom_search`)
is modelled faithfully because both the `exclude_typeofbottom` pruning in
`jl_typemap_intersection_visitor` and the candidate visit order in
`get_intersect_matches` and `ml_matches` depend on it.
-/

namespace JuliaLean.C

/-- `~(size_t)0`: unbounded upper world age sentinel. -/
def worldMax : Nat := (1 <<< 64) - 1

/-- `MAX_METHLIST_COUNT` (`src/typemap.c:12`). -/
def maxMethlistCount : Nat := 6

/-- Operations from `subtype.c` used by `typemap.c` and `gf.c` (extending `Ops` from `jltypes.c`). -/
structure GfOps extends Ops where
  /-- `jl_type_morespecific(a, b)` (`src/subtype.c:7697-7708`). -/
  typeMorespecific : Val → Val → CM Bool
  /-- `jl_type_intersection_env_s(a, b, penv, &issubty)` (`src/subtype.c:6628-6738`);
  `withEnv` is `penv != NULL`, returning `(ti, env, issubty)`. -/
  typeIntersectionEnvS : Val → Val → Bool → CM (Val × List Val × Bool)
  /-- `jl_subtype_matching(a, b, penv)` (`src/subtype.c:6761-6782`);
  `withEnv` is `penv != NULL`, returning `(matched, env)`. -/
  subtypeMatching : Val → Val → Bool → CM (Bool × List Val)
  /-- `jl_isa(x, t)` (`src/subtype.c:4253-4309`). -/
  isa : Val → Val → CM Bool
  /-- `jl_is_typeofbottom_param(t)` (`src/subtype.c:7414-7432`). -/
  isTypeofbottomParam : Val → CM Bool
  /-- `jl_obviously_unequal(a, b)` (`src/subtype.c:640-726`). -/
  obviouslyUnequal : Val → Val → CM Bool

/-- `jl_type_intersection_env(a, b, penv)` (`src/subtype.c:6740-6743`). -/
def GfOps.typeIntersectionEnv (ops : GfOps) (a b : Val) : CM (Val × List Val) := do
  let (ti, env, _) ← ops.typeIntersectionEnvS a b true
  return (ti, env)

/-- `jl_type_intersection(a, b)` (`src/subtype.c:6745-6748`). -/
def GfOps.typeIntersection (ops : GfOps) (a b : Val) : CM Val := do
  let (ti, _, _) ← ops.typeIntersectionEnvS a b false
  return ti

/-- Built-in `Core` `TypeName`s (`src/jltypes.c:3592-3803`), used as fallback when not listed in `T.names`. -/
def builtinTypeNames : List TypeName :=
  [ { name := "Core.Any", abstract := true, mutable := false, wrapper := anyType, super := none }
  , { name := "Core.AnyType", abstract := true, mutable := false, wrapper := anytypeType, super := some anyType }
  , { name := "Core.TypeofBottom", abstract := false, mutable := false, wrapper := typeofbottomType, super := some anytypeType }
  , { name := "Core.TypeEq", abstract := false, mutable := false, wrapper := typeeqType, super := some anytypeType }
  , { name := "Core.TypeEgal", abstract := false, mutable := false, wrapper := typeegalType, super := some anytypeType }
  , { name := "Core.DataType", abstract := false, mutable := true, wrapper := datatypeType, super := some anytypeType }
  , { name := "Core.Union", abstract := false, mutable := false, wrapper := uniontypeType, super := some anytypeType }
  , { name := "Core.UnionAll", abstract := false, mutable := false, wrapper := unionallType, super := some anytypeType }
  , { name := "Core.Intersect", abstract := false, mutable := false, wrapper := intersectType, super := some anytypeType }
  , { name := "Core.TypeVar", abstract := false, mutable := true, wrapper := tvarType, super := some anyType }
  , { name := "Core.TypeofVararg", abstract := false, mutable := false, wrapper := varargType, super := some anyType }
  , { name := "Core.Symbol", abstract := false, mutable := true, wrapper := symbolType, super := some anyType }
  , { name := "Core.Tuple", abstract := false, mutable := false, wrapper := anytupleType, super := some anyType }
  ]

/-- Built-in `Layout`s for the kind datatypes (`src/jltypes.c:3601-3795`). -/
def builtinLayouts : List Layout :=
  [ { dt := typeofbottomType, isbits := true, singleton := true, concreteSubtype := true }
  , { dt := datatypeType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := uniontypeType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := unionallType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := typeeqType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := typeegalType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := intersectType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := tvarType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := varargType, isbits := false, singleton := false, concreteSubtype := true }
  , { dt := symbolType, isbits := false, singleton := false, concreteSubtype := true }
  ]

/-- Augment `T` with fallback built-in `Core` type names and layouts. -/
def withBuiltinTypes (T : Types) : Types :=
  { names := T.names ++ builtinTypeNames, layouts := T.layouts ++ builtinLayouts }

/-- Look up a `TypeName` in `T`, falling back to built-in `Core` type names. -/
def typenameOf (T : Types) (name : String) : CM TypeName :=
  (withBuiltinTypes T).typename name

/-- `jl_type_type` (`Type{T} where T`, `src/jltypes.c:3770-3774`). -/
def mkTypeType : CM Val := do
  let id ← freshId
  return .unionall id "T" .bottom anyType (.typeeq (.typevar id "T" .bottom anyType))

/-- `jl_is_dispatch_tupletype` (`dt->isdispatchtuple`, `src/julia.h:2123-2126`, `src/jltypes.c:2096-2120`). -/
def isDispatchTupletype (T : Types) (v : Val) : CM Bool := do
  let T := withBuiltinTypes T
  match v with
  | .datatype name ps =>
    if name != tupleName then return false
    for p in ps do
      let ok ←
        if p.isDatatype then
          if !isKind p then
            if ← isConcreteType T p then pure true
            else pure (p == typeofbottomType)
          else
            pure (p == typeofbottomType)
        else if p.isTypeegal then
          pure true
        else if p.isTypeeq && p.someTypeT == .bottom then
          pure true
        else
          pure false
      if !ok then return false
    return true
  | _ => return false

/-- `jl_datatype_compute_super` (`src/jltypes.c:3407-3439`). -/
def datatypeComputeSuper (n : Nat) (T : Types) (ops : Ops) (ndt : Val) : CM (Option Val) := do
  let T := withBuiltinTypes T
  if ndt == anyType then return some anyType
  match ndt with
  | .datatype name ps =>
    if name == tupleName then return some anyType
    let tn ← T.typename name
    match tn.super with
    | none =>
      if name == "Core.Any" then return some anyType
      return none
    | some sup =>
      let vars := wrapperVars tn.wrapper
      let env : InstEnv := ((vars.filterMap Val.tvId).zip ps).reverse
      instTypeW n T ops sup env true 0
  | _ => return none

/-- A key in an `mtcache`: either a `jl_typename_t*` (by name) or a concrete `Val` (in a `doublesplit` cache). -/
inductive MtKey where
  | typename (name : String)
  | val (v : Val)
  deriving Repr, BEq, Inhabited

/-- `jl_typemap_entry_t` (`src/julia.h:1024-1041`). -/
structure TypemapEntry where
  sig : Val
  simplesig : Option Val := none
  guardsigs : List Val := []
  minWorld : Nat
  maxWorld : Nat
  /-- Method index (`func.method` in `mt->defs`). -/
  func : Nat
  isleafsig : Bool
  issimplesig : Bool
  va : Bool
  deriving Repr, BEq, Inhabited

/-- `jl_typemap_t` (`src/julia.h:293`, `src/julia.h:1044-1059`) and `mtcache` (`Memory{Any}`, `src/typemap.c:331-339`). -/
inductive Typemap where
  /-- A linked list of `jl_typemap_entry_t` (`jl_nothing` is `[]`). -/
  | entries (es : List TypemapEntry)
  /-- `jl_typemap_level_t`: splits on the argument at `offs`. -/
  | level (arg1 targ name1 tname : List (MtKey × Typemap))
          (linear : List TypemapEntry)
          (any : Typemap)
  /-- `jl_genericmemory_t` (`dblcache`): second-level `mtcache` produced by `doublesplit`. -/
  | memory (pairs : List (MtKey × Typemap))
  deriving Repr, Inhabited

/-- `struct jl_typemap_assoc` (`src/julia_internal.h:1975-1981`). -/
structure TypemapAssoc where
  types : Val
  world : Nat
  /-- `some env` when `search->env != NULL`, `none` when `search->env == NULL`. -/
  env : Option (List Val) := none
  deriving Repr, Inhabited

/-- `struct typemap_intersection_env` (`src/julia_internal.h:2010-2027`). -/
structure TypemapIntersectionEnv where
  type : Val
  va : Option Val
  searchBottom : Nat := 0
  minValid : Nat := 0
  maxValid : Nat := worldMax
  ti : Val := .bottom
  /-- `some env` when `closure->env != NULL`, `none` when `closure->env == NULL`. -/
  env : Option (List Val) := none
  issubty : Bool := false
  emptinessOnly : Bool := false
  deriving Repr, Inhabited

/-- `jl_is_any`: compute whether the specificity of this type is equivalent to `Any` in the sort order.

Julia source: src/typemap.c:19-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_is_any(jl_value_t *t1)
{
    while (jl_is_typevar(t1))
        t1 = ((jl_tvar_t*)t1)->ub;
    return t1 == (jl_value_t*)jl_any_type;
}
```
-/
def jlIsAny (n : Nat) (t1 : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t1 with
    | .typevar _ _ _ ub => jlIsAny n ub
    | _ => pure (t1 == anyType)

/-- `jl_type_extract_name`: returns the `TypeName` name string, or `none` for `NULL`.

Julia source: src/typemap.c:26-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *jl_type_extract_name(jl_value_t *t1 JL_PROPAGATES_ROOT, int invariant) JL_NOTSAFEPOINT
{
    if (jl_is_unionall(t1))
        t1 = jl_unwrap_unionall(t1);
    if (jl_is_vararg(t1)) {
        return jl_type_extract_name(jl_unwrap_vararg(t1), invariant);
    }
    else if (t1 == jl_bottom_type || (invariant && jl_is_typeofbottom_param(t1))) {
        // file all spellings to Type{Union{}} in the same bucket, then walk to the other type buckets from there
        return (jl_value_t*)jl_typeofbottom_type->name;
    }
    else if (jl_is_typevar(t1)) {
        return jl_type_extract_name(((jl_tvar_t*)t1)->ub, 0);
    }
    else if (jl_is_some_Type(t1)) {
        // invariantly this is the wrapper's own name; covariantly the key must lie on
        // both the `typeof(arg)` and the wrapper supertype chains, which meet at `AnyType`
        if (invariant)
            return jl_is_typeeq(t1) ? (jl_value_t*)jl_type_typename : (jl_value_t*)jl_typeegal_type->name;
        return (jl_value_t*)jl_anytype_type->name;
    }
    else if (jl_is_datatype(t1)) {
        jl_datatype_t *dt = (jl_datatype_t*)t1;
        if (jl_is_kind(t1) && !invariant)
            return (jl_value_t*)jl_anytype_type->name;
        // `AnyType == Type`, and every `TypeEq{...}` spelling of it is filed under its
        // subtype `TypeEq`, so give it that name invariantly
        if (dt == jl_anytype_type && invariant)
            return (jl_value_t*)jl_type_typename;
        return (jl_value_t*)dt->name;
    }
    else if (jl_is_uniontype(t1)) {
        jl_uniontype_t *u1 = (jl_uniontype_t*)t1;
        jl_value_t *tn1 = jl_type_extract_name(u1->a, invariant);
        jl_value_t *tn2 = jl_type_extract_name(u1->b, invariant);
        if (tn1 == tn2)
            return tn1;
        // TODO: if invariant is false, instead find the nearest common ancestor
        return NULL;
    }
    return NULL;
}
```
-/
def jlTypeExtractName (n : Nat) (ops : GfOps) (t1 : Val) (invariant : Bool) : CM (Option String) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let t1 := if t1.isUnionall then t1.unwrapUnionall else t1
    if t1.isVararg then
      jlTypeExtractName n ops t1.unwrapVararg invariant
    else
      let isBotParam ← if invariant then ops.isTypeofbottomParam t1 else pure false
      if t1 == .bottom || isBotParam then
        -- file all spellings to Type{Union{}} in the same bucket, then walk to the other type buckets from there
        return some "Core.TypeofBottom"
      else if let .typevar _ _ _ ub := t1 then
        jlTypeExtractName n ops ub false
      else if t1.isSomeType then
        -- invariantly this is the wrapper's own name; covariantly the key must lie on
        -- both the `typeof(arg)` and the wrapper supertype chains, which meet at `AnyType`
        if invariant then
          return some (if t1.isTypeeq then "Core.TypeEq" else "Core.TypeEgal")
        return some "Core.AnyType"
      else if let .datatype dtName _ := t1 then
        if isKind t1 && !invariant then
          return some "Core.AnyType"
        -- `AnyType == Type`, and every `TypeEq{...}` spelling of it is filed under its
        -- subtype `TypeEq`, so give it that name invariantly
        if t1 == anytypeType && invariant then
          return some "Core.TypeEq"
        return some dtName
      else if let .union u1a u1b := t1 then
        let tn1 ← jlTypeExtractName n ops u1a invariant
        let tn2 ← jlTypeExtractName n ops u1b invariant
        if tn1 == tn2 then
          return tn1
        return none
      else
        return none

/-- `jl_type_extract_name_precise`: return `false` if the name extracted above is an over-approximation
(such that intersection also needs to consider the subtypes).

Julia source: src/typemap.c:71-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_type_extract_name_precise(jl_value_t *t1, int invariant)
{
    if (jl_is_unionall(t1))
        t1 = jl_unwrap_unionall(t1);
    if (jl_is_vararg(t1)) {
        return jl_type_extract_name_precise(jl_unwrap_vararg(t1), invariant);
    }
    else if (invariant && jl_is_typeofbottom_param(t1)) {
        return 1; // the `TypeofBottom` name holds every spelling of `Type{typeof(Union{})}`
    }
    else if (jl_is_typevar(t1)) {
        jl_value_t *ub = ((jl_tvar_t*)t1)->ub;
        // as a `Type{T}` parameter, a `T` bounded by a kind or wrapper (whose name
        // `jl_type_extract_name` folds to `AnyType`) may also be a `Type{...}`, `TypeEgal{...}`
        // or kind object, which is filed under its own name rather than an ancestor's
        if (invariant && jl_type_extract_name(ub, 0) == (jl_value_t*)jl_anytype_type->name)
            return 0;
        return jl_type_extract_name_precise(ub, 0);
    }
    else if (jl_is_some_Type(t1)) {
        return 1;
    }
    else if (t1 == jl_bottom_type || t1 == (jl_value_t*)jl_typeofbottom_type) {
        return 1;
    }
    else if (jl_is_datatype(t1)) {
        jl_datatype_t *dt = (jl_datatype_t*)t1;
        if (invariant || !dt->name->abstract)
            return 1;
        return 0;
    }
    else if (jl_is_uniontype(t1)) {
        jl_uniontype_t *u1 = (jl_uniontype_t*)t1;
        if (!jl_type_extract_name_precise(u1->a, invariant))
            return 0;
        if (!jl_type_extract_name_precise(u1->b, invariant))
            return 0;
        jl_value_t *tn1 = jl_type_extract_name(u1->a, invariant);
        jl_value_t *tn2 = jl_type_extract_name(u1->b, invariant);
        if (tn1 == tn2)
            return 1;
        return 0;
    }
    return 1;
}
```
-/
def jlTypeExtractNamePrecise (n : Nat) (T : Types) (ops : GfOps) (t1 : Val) (invariant : Bool) :
    CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let t1 := if t1.isUnionall then t1.unwrapUnionall else t1
    if t1.isVararg then
      jlTypeExtractNamePrecise n T ops t1.unwrapVararg invariant
    else
      let isBotParam ← if invariant then ops.isTypeofbottomParam t1 else pure false
      if isBotParam then
        return true -- the `TypeofBottom` name holds every spelling of `Type{typeof(Union{})}`
      else if let .typevar _ _ _ ub := t1 then
        -- as a `Type{T}` parameter, a `T` bounded by a kind or wrapper (whose name
        -- `jl_type_extract_name` folds to `AnyType`) may also be a `Type{...}`, `TypeEgal{...}`
        -- or kind object, which is filed under its own name rather than an ancestor's
        if invariant then
          if (← jlTypeExtractName n ops ub false) == some "Core.AnyType" then
            return false
        jlTypeExtractNamePrecise n T ops ub false
      else if t1.isSomeType then
        return true
      else if t1 == .bottom || t1 == typeofbottomType then
        return true
      else if let .datatype dtName _ := t1 then
        if invariant then return true
        let tn ← typenameOf T dtName
        return !tn.abstract
      else if let .union u1a u1b := t1 then
        if !(← jlTypeExtractNamePrecise n T ops u1a invariant) then
          return false
        if !(← jlTypeExtractNamePrecise n T ops u1b invariant) then
          return false
        let tn1 ← jlTypeExtractName n ops u1a invariant
        let tn2 ← jlTypeExtractName n ops u1b invariant
        return tn1 == tn2
      else
        return true

/-- `jl_parameter_includes_bottom`: return whether `Type{Union{}}` is a subtype of `Type{t1}`
(which may have free typevars).

Julia source: src/typemap.c:118-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_parameter_includes_bottom(jl_value_t *t1)
{
    if (jl_is_typevar(t1) || t1 == jl_bottom_type)
        return 1;
    else if (jl_is_uniontype(t1)) {
        jl_uniontype_t *u1 = (jl_uniontype_t*)t1;
        return jl_parameter_includes_bottom(u1->a) && jl_parameter_includes_bottom(u1->b);
    }
    return 0;
}
```
-/
def jlParameterIncludesBottom (n : Nat) (t1 : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if t1.isTypevar || t1 == .bottom then
      return true
    else if let .union a b := t1 then
      if !(← jlParameterIncludesBottom n a) then return false
      jlParameterIncludesBottom n b
    else
      return false

/-- `sig_match_by_type_leaf`

Julia source: src/typemap.c:132-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int sig_match_by_type_leaf(jl_value_t **types, jl_tupletype_t *sig, size_t n) JL_CANSAFEPOINT
{
    size_t i;
    for (i = 0; i < n; i++) {
        jl_value_t *decl = jl_tparam(sig, i);
        jl_value_t *a = types[i];
        if (jl_is_some_Type(a)) // decl is not Type, because it wouldn't be leafsig
            a = jl_typeof(jl_some_Type_T(a));
        if (!jl_types_equal(a, decl))
            return 0;
    }
    return 1;
}
```
-/
def sigMatchByTypeLeaf (ops : GfOps) (types : List Val) (sig : Val) (len : Nat) : CM Bool := do
  let sigParams := sig.params
  for i in [0:len] do
    let decl := sigParams[i]!
    let a := types[i]!
    let a := if a.isSomeType then typeOf a.someTypeT else a
    if !(← ops.typesEqual a decl) then
      return false
  return true

/-- `jl_subtype_anytype`: returns `true` if every value of type `a` is itself a type (i.e., `a <: AnyType`).

Julia source: src/typemap.c:147-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_subtype_anytype(jl_value_t *a) JL_NOTSAFEPOINT
{
    while (1) {
        if (a == (jl_value_t*)jl_anytype_type || jl_is_kind(a) || jl_is_some_Type(a))
            return 1;
        else if (jl_is_unionall(a))
            a = jl_unwrap_unionall(a);
        else if (jl_is_uniontype(a)) {
            jl_uniontype_t *u = (jl_uniontype_t*)a;
            if (!jl_subtype_anytype(u->a))
                return 0;
            a = u->b;
        }
        else if (jl_is_typevar(a))
            a = ((jl_tvar_t*)a)->ub;
        else
            return 0;
    }
}
```
-/
def jlSubtypeAnytype (n : Nat) (a : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if a == anytypeType || isKind a || a.isSomeType then
      return true
    else if a.isUnionall then
      jlSubtypeAnytype n a.unwrapUnionall
    else if let .union ua ub := a then
      if !(← jlSubtypeAnytype n ua) then
        return false
      jlSubtypeAnytype n ub
    else if let .typevar _ _ _ ub := a then
      jlSubtypeAnytype n ub
    else
      return false

/-- `sig_match_by_type_simple`

Julia source: src/typemap.c:167-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int sig_match_by_type_simple(jl_value_t **types, size_t n, jl_tupletype_t *sig, size_t lensig, int va) JL_CANSAFEPOINT
{
    size_t i;
    if (va) lensig -= 1;
    for (i = 0; i < lensig; i++) {
        jl_value_t *decl = jl_tparam(sig, i);
        jl_value_t *a = types[i];
        if (jl_is_vararg(a))
            return 0;
        if (jl_is_typeeq(decl)) {
            jl_value_t *tp0 = jl_typeeq_T(decl);
            // either query wrapper matches by type equality (egal implies equal)
            if (jl_is_some_Type(a)) {
                if (!jl_types_equal(jl_some_Type_T(a), tp0))
                    return 0;
            }
            else {
                return 0;
            }
        }
        else if (jl_is_typeegal(decl)) {
            // an egality key matches only an `===`-equal egality key
            if (!(jl_is_typeegal(a) && jl_egal(jl_typeegal_T(a), jl_typeegal_T(decl))))
                return 0;
        }
        else if (decl == (jl_value_t*)jl_any_type) {
        }
        else if (decl == (jl_value_t*)jl_anytype_type) {
            if (!jl_subtype_anytype(a))
                return 0;
        }
        else {
            assert(jl_is_concrete_type(decl));
            if (jl_is_some_Type(a)) { // decl is not TypeEq/TypeEgal or AnyType, because it would be caught above, so it must be concrete
                a = jl_typeof(jl_some_Type_T(a));
            }
            if (!jl_types_equal(a, decl))
                return 0;
        }
    }
    if (va) {
        jl_value_t *decl = jl_tparam(sig, i);
        assert(jl_is_vararg(decl));
        if (jl_vararg_kind(decl) == JL_VARARG_INT) {
            if (n - i != jl_unbox_long(jl_tparam1(decl)))
                return 0;
        }
        jl_value_t *t = jl_unwrap_vararg(decl);
        if (jl_is_typevar(t))
            t = ((jl_tvar_t*)t)->ub;
        for (; i < n; i++) {
            jl_value_t *ti = types[i];
            if (i == n - 1 && jl_is_vararg(ti))
                ti = jl_unwrap_vararg(ti);
            if (!jl_subtype(ti, t))
                return 0;
        }
        return 1;
    }
    return 1;
}
```
-/
def sigMatchByTypeSimple (n : Nat) (T : Types) (ops : GfOps) (types : List Val) (ntypes : Nat)
    (sig : Val) (lensig : Nat) (va : Bool) : CM Bool := do
  let T := withBuiltinTypes T
  let sigParams := sig.params
  let checkLen := if va then lensig - 1 else lensig
  for i in [0:checkLen] do
    let decl := sigParams[i]!
    let a := types[i]!
    if a.isVararg then
      return false
    if let .typeeq tp0 := decl then
      -- either query wrapper matches by type equality (egal implies equal)
      if a.isSomeType then
        if !(← ops.typesEqual a.someTypeT tp0) then
          return false
      else
        return false
    else if let .typeegal dt0 := decl then
      -- an egality key matches only an `===`-equal egality key
      if !a.isTypeegal then
        return false
      if !(← egal n T a.someTypeT dt0) then
        return false
    else if decl == anyType then
      pure ()
    else if decl == anytypeType then
      if !(← jlSubtypeAnytype n a) then
        return false
    else
      let a := if a.isSomeType then typeOf a.someTypeT else a
      if !(← ops.typesEqual a decl) then
        return false
  if va then
    let decl := sigParams[checkLen]!
    if decl.varargKind == .int then
      if let some (.long k) := decl.varargN? then
        if Int.ofNat (ntypes - checkLen) != k then
          return false
    let t := decl.unwrapVararg
    let t := match t with | .typevar _ _ _ ub => ub | _ => t
    for i in [checkLen:ntypes] do
      let ti := types[i]!
      let ti := if i == ntypes - 1 && ti.isVararg then ti.unwrapVararg else ti
      if !(← ops.subtype ti t) then
        return false
    return true
  return true

/-- `is_cache_leaf`

Julia source: src/typemap.c:324-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_cache_leaf(jl_value_t *ty, int tparam)
{
    if (ty == jl_bottom_type)
        return 1;
    return (jl_is_concrete_type(ty) && (tparam || !jl_is_kind(ty)));
}
```
-/
def isCacheLeaf (T : Types) (ty : Val) (tparam : Bool) : CM Bool := do
  let T := withBuiltinTypes T
  if ty == .bottom then
    return true
  let conc ← isConcreteType T ty
  if !conc then
    return false
  return tparam || !isKind ty

/-- `mtcache_eq`

Julia source: src/typemap.c:348-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int mtcache_eq(size_t p, const void *key, jl_value_t *data, uint_t hv) JL_NOTSAFEPOINT
{
    size_t ki = MTCACHE_KEY_SLOT(p);
    if (ki >= ((jl_genericmemory_t*)data)->length)
        return 0; // OOB access, probably due to a data race
    jl_value_t *k = jl_genericmemory_ptr_ref(data, ki);
    return k != NULL && jl_egal(k, (jl_value_t*)key);
}
```
-/
def mtcacheEq (n : Nat) (T : Types) (k key : MtKey) : CM Bool :=
  match k, key with
  | .typename a, .typename b => pure (a == b)
  | .val a, .val b => egal n (withBuiltinTypes T) a b
  | _, _ => pure false

/-- `mtcache_hash_peek`: returns the index of `ty` in `cache`, or `none` (`-1`).

Julia source: src/typemap.c:357-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static ssize_t mtcache_hash_peek(jl_genericmemory_t *cache JL_PROPAGATES_ROOT, jl_value_t *ty) JL_NOTSAFEPOINT
{
    if (cache == (jl_genericmemory_t*)jl_an_empty_memory_any)
        return -1;
    jl_genericmemory_t *idxs = (jl_genericmemory_t*)jl_genericmemory_ptr_ref(cache, 0); // acquire
    JL_GC_PROMISE_ROOTED(idxs);
    // mtcache_eq does not safepoint, so this lookup is safe from JL_NOTSAFEPOINT callers
    ssize_t jl_smallintset_lookup(jl_genericmemory_t *cache, smallintset_eq eq JL_NOTSAFEPOINT, const void *key, jl_value_t *data, uint_t hv, int pop) JL_NOTSAFEPOINT;
    return jl_smallintset_lookup(idxs, mtcache_eq, ty, (jl_value_t*)cache, (uint_t)jl_object_id(ty), 0);
}
```
-/
def mtcacheHashPeek (n : Nat) (T : Types) (cache : List (MtKey × Typemap)) (ty : MtKey) :
    CM (Option Nat) := do
  let mut idx := 0
  for (k, _) in cache do
    if ← mtcacheEq n T k ty then
      return some idx
    idx := idx + 1
  return none

/-- `mtcache_hash_insert`

Julia source: src/typemap.c:378-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void mtcache_hash_insert(_Atomic(jl_genericmemory_t*) *pcache, jl_value_t *parent, jl_value_t *key, jl_typemap_t *val) JL_CANSAFEPOINT
{
    size_t p = jl_ordereddict_reserve(pcache, parent, 2); // reserve one key/value pair
    jl_genericmemory_t *a = jl_atomic_load_relaxed(pcache);
    jl_genericmemory_ptr_set(a, MTCACHE_KEY_SLOT(p), key); // release
    jl_genericmemory_ptr_set(a, MTCACHE_VAL_SLOT(p), (jl_value_t*)val); // release
    // publish the entry last, so a concurrent lookup that observes it in the
    // index also observes the key and value written above
    jl_smallintset_insert((_Atomic(jl_genericmemory_t*)*)a->ptr, (jl_value_t*)a, mtcache_hash, p, (jl_value_t*)a);
}
```
-/
def mtcacheHashInsert (cache : List (MtKey × Typemap)) (key : MtKey) (val : Typemap) :
    List (MtKey × Typemap) :=
  cache ++ [(key, val)]

/-- `mtcache_hash_lookup`

Julia source: src/typemap.c:389-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_typemap_t *mtcache_hash_lookup(jl_genericmemory_t *cache JL_PROPAGATES_ROOT, jl_value_t *ty) JL_NOTSAFEPOINT
{
    ssize_t p = mtcache_hash_peek(cache, ty);
    if (p == -1)
        return (jl_typemap_t*)jl_nothing;
    jl_typemap_t *ml = (jl_typemap_t*)jl_genericmemory_ptr_ref(cache, MTCACHE_VAL_SLOT(p));
    return ml == NULL ? (jl_typemap_t*)jl_nothing : ml;
}
```
-/
def mtcacheHashLookup (n : Nat) (T : Types) (cache : List (MtKey × Typemap)) (ty : MtKey) :
    CM Typemap := do
  match ← mtcacheHashPeek n T cache ty with
  | none => return .entries []
  | some p => return cache[p]!.2

mutual
/-- `jl_typemap_memory_visitor`

Julia source: src/typemap.c:400-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_typemap_memory_visitor(jl_genericmemory_t *a, jl_typemap_visitor_fptr fptr, void *closure) JL_CANSAFEPOINT
{
    size_t i, l = a->length;
    _Atomic(jl_typemap_t*) *data = (_Atomic(jl_typemap_t*)*) a->ptr;
    for (i = 2; i < l; i += 2) { // values live on even slots >= 2 (slot 0 is the index)
        jl_value_t *d = jl_atomic_load_relaxed(&data[i]);
        JL_GC_PROMISE_ROOTED(d);
        if (d == NULL)
            continue;
        if (jl_is_genericmemory(d)) {
            if (!jl_typemap_memory_visitor((jl_genericmemory_t*)d, fptr, closure))
                return 0;
        }
        else {
            if (!jl_typemap_visitor(d, fptr, closure))
                return 0;
        }
    }
    return 1;
}
```
-/
def jlTypemapMemoryVisitor {α : Type} (n : Nat) (a : List (MtKey × Typemap))
    (fptr : TypemapEntry → α → CM (Bool × α)) (st : α) : CM (Bool × α) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut st := st
    for (_, d) in a do
      match d with
      | .memory inner =>
        let (ok, st') ← jlTypemapMemoryVisitor n inner fptr st
        st := st'
        if !ok then return (false, st)
      | _ =>
        let (ok, st') ← jlTypemapVisitor n d fptr st
        st := st'
        if !ok then return (false, st)
    return (true, st)

/-- `jl_typemap_node_visitor`: calls `fptr` on each `TypemapEntry` in sort order, until `fptr` returns `false`.

Julia source: src/typemap.c:423-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_typemap_node_visitor(jl_typemap_entry_t *ml, jl_typemap_visitor_fptr fptr, void *closure) JL_CANSAFEPOINT
{
    while (ml != (void*)jl_nothing) {
        if (!fptr(ml, closure))
            return 0;
        ml = jl_atomic_load_relaxed(&ml->next);
    }
    return 1;
}
```
-/
def jlTypemapNodeVisitor {α : Type} (n : Nat) (ml : List TypemapEntry)
    (fptr : TypemapEntry → α → CM (Bool × α)) (st : α) : CM (Bool × α) :=
  match n with
  | 0 => outOfBudget
  | _ + 1 => do
    let mut st := st
    for entry in ml do
      let (ok, st') ← fptr entry st
      st := st'
      if !ok then return (false, st)
    return (true, st)

/-- `jl_typemap_visitor`

Julia source: src/typemap.c:433-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_typemap_visitor(jl_typemap_t *cache, jl_typemap_visitor_fptr fptr, void *closure)
{
    if (jl_typeof(cache) == (jl_value_t*)jl_typemap_level_type) {
        jl_typemap_level_t *node = (jl_typemap_level_t*)cache;
        jl_genericmemory_t *a = NULL;
        JL_GC_PUSH1(&a);
        a = jl_atomic_load_relaxed(&node->targ);
        if (a != (jl_genericmemory_t*)jl_an_empty_memory_any)
            if (!jl_typemap_memory_visitor(a, fptr, closure))
                goto exit;
        a = jl_atomic_load_relaxed(&node->arg1);
        if (a != (jl_genericmemory_t*)jl_an_empty_memory_any)
            if (!jl_typemap_memory_visitor(a, fptr, closure))
                goto exit;
        a = jl_atomic_load_relaxed(&node->tname);
        if (a != (jl_genericmemory_t*)jl_an_empty_memory_any)
            if (!jl_typemap_memory_visitor(a, fptr, closure))
                goto exit;
        a = jl_atomic_load_relaxed(&node->name1);
        if (a != (jl_genericmemory_t*)jl_an_empty_memory_any)
            if (!jl_typemap_memory_visitor(a, fptr, closure))
                goto exit;
        if (!jl_typemap_node_visitor(jl_atomic_load_relaxed(&node->linear), fptr, closure))
            goto exit;
        if (!jl_typemap_visitor(jl_atomic_load_relaxed(&node->any), fptr, closure))
            goto exit;
        JL_GC_POP();
        return 1;
exit:
        JL_GC_POP();
        return 0;
    }
    else {
        return jl_typemap_node_visitor((jl_typemap_entry_t*)cache, fptr, closure);
    }
}
```
-/
def jlTypemapVisitor {α : Type} (n : Nat) (cache : Typemap)
    (fptr : TypemapEntry → α → CM (Bool × α)) (st : α) : CM (Bool × α) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match cache with
    | .level arg1 targ name1 tname linear any =>
      let mut st := st
      if !targ.isEmpty then
        let (ok, st') ← jlTypemapMemoryVisitor n targ fptr st
        st := st'
        if !ok then return (false, st)
      if !arg1.isEmpty then
        let (ok, st') ← jlTypemapMemoryVisitor n arg1 fptr st
        st := st'
        if !ok then return (false, st)
      if !tname.isEmpty then
        let (ok, st') ← jlTypemapMemoryVisitor n tname fptr st
        st := st'
        if !ok then return (false, st)
      if !name1.isEmpty then
        let (ok, st') ← jlTypemapMemoryVisitor n name1 fptr st
        st := st'
        if !ok then return (false, st)
      let (ok, st') ← jlTypemapNodeVisitor n linear fptr st
      st := st'
      if !ok then return (false, st)
      jlTypemapVisitor n any fptr st
    | .entries ml =>
      jlTypemapNodeVisitor n ml fptr st
    | .memory pairs =>
      jlTypemapMemoryVisitor n pairs fptr st
end

/-- `jl_supertype_height`

Julia source: src/typemap.c:470-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static unsigned jl_supertype_height(jl_datatype_t *dt) JL_CANSAFEPOINT
{
    unsigned height = 1;
    while (dt != NULL && dt != jl_any_type) {
        height++;
        dt = jl_datatype_compute_super(dt);
    }
    return height;
}
```
-/
def jlSupertypeHeight (n : Nat) (T : Types) (ops : Ops) (dt : Val) : CM Nat :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if dt == anyType then return 1
    match ← datatypeComputeSuper n T ops dt with
    | none => return 2
    | some sup => return 1 + (← jlSupertypeHeight n T ops sup)

/-- `tname_intersection_dt`: return `true` if `a` and `b` might intersect in the type domain
(taken over just `b`'s type-name): whether the supertype chains of `a` and `b.wrapper` meet.

Julia source: src/typemap.c:482-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int tname_intersection_dt(jl_datatype_t *a, jl_typename_t *bname, unsigned ha) JL_CANSAFEPOINT
{
    if (a == jl_any_type)
        return 1;
    jl_datatype_t *b = (jl_datatype_t*)jl_unwrap_unionall(bname->wrapper);
    // Additionally, a `TypeEq` meets every kind name (`TypeEq{R} <: Union{DataType, UnionAll, ...}`),
    // and every kind meets both wrapper names (`TypeEgal{X} <: typeof(X)`, `TypeEq{Vector} intersects UnionAll`).
    if ((a == jl_typeeq_type && jl_is_kind((jl_value_t*)b)) ||
        (jl_is_kind((jl_value_t*)a) && (b == jl_typeeq_type || b == jl_typeegal_type)))
        return 1;
    unsigned hb = 1;
    while (b != NULL && b != jl_any_type) {
        if (a->name == b->name)
            return 1;
        hb++;
        b = jl_datatype_compute_super(b);
    }
    while (ha > hb) {
        a = jl_datatype_compute_super(a);
        ha--;
        if (a == NULL)
            return 1; // definition in progress: conservatively may intersect
    }
    return a->name == bname;
}
```
-/
def tnameIntersectionDt (n : Nat) (T : Types) (ops : Ops) (a : Val) (bname : String) (ha : Nat) :
    CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if a == anyType then
      return true
    let btn ← typenameOf T bname
    let b := btn.wrapper.unwrapUnionall
    -- Additionally, a `TypeEq` meets every kind name (`TypeEq{R} <: Union{DataType, UnionAll, ...}`),
    -- and every kind meets both wrapper names (`TypeEgal{X} <: typeof(X)`, `TypeEq{Vector} intersects UnionAll`).
    if (a == typeeqType && isKind b) || (isKind a && (b == typeeqType || b == typeegalType)) then
      return true
    let mut hb : Nat := 1
    let mut bcur : Option Val := some b
    let mut steps := n
    while bcur.isSome && bcur != some anyType do
      if steps == 0 then outOfBudget
      steps := steps - 1
      let some bv := bcur | break
      if a.name? == bv.name? then
        return true
      hb := hb + 1
      bcur ← datatypeComputeSuper n T ops bv
    let mut acur := a
    let mut ha := ha
    while ha > hb do
      if steps == 0 then outOfBudget
      steps := steps - 1
      ha := ha - 1
      match ← datatypeComputeSuper n T ops acur with
      | none => return true -- definition in progress: conservatively may intersect
      | some sup => acur := sup
    return acur.name? == some bname

/-- `tname_super`: the bucket after `super` in a `tname` walk that ends at `Any` (or `none`).

Julia source: src/typemap.c:510-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_datatype_t *tname_super(jl_datatype_t *super JL_PROPAGATES_ROOT) JL_CANSAFEPOINT
{
    if (super == jl_any_type)
        return NULL;
    if (super == jl_typeofbottom_type)
        return jl_typeeq_type;
    return jl_datatype_compute_super(super); // NULL if the definition is in progress
}
```
-/
def tnameSuper (n : Nat) (T : Types) (ops : Ops) (super : Val) : CM (Option Val) := do
  if super == anyType then
    return none
  if super == typeofbottomType then
    return some typeeqType
  datatypeComputeSuper n T ops super

/-- `tname_intersection`: return `true` if `a` might intersect a type named `bname` (`tparam = false`),
or `Type{X}` or `TypeEgal{X}` for some `X` named `bname` (`tparam = true`), over just the type-names.

Julia source: src/typemap.c:523-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int tname_intersection(jl_value_t *a, jl_typename_t *bname, int8_t tparam) JL_CANSAFEPOINT
{
    if (a == (jl_value_t*)jl_any_type)
        return 1;
    a = jl_unwrap_unionall(a);
    assert(!jl_is_vararg(a));
    if (jl_is_uniontype(a))
        return tname_intersection(((jl_uniontype_t*)a)->a, bname, tparam) ||
               tname_intersection(((jl_uniontype_t*)a)->b, bname, tparam);
    if (jl_is_typevar(a))
        return tname_intersection(((jl_tvar_t*)a)->ub, bname, tparam);
    if (tparam) {
        if (jl_is_kind(a) || a == (jl_value_t*)jl_anytype_type)
            return 1; // a kind contains the `X` of any `Type{X}`
        if (!jl_is_some_Type(a))
            return 0;
        a = jl_unwrap_unionall(jl_some_Type_T(a));
        if (a == jl_bottom_type || jl_is_typeofbottom_param(a))
            a = (jl_value_t*)jl_typeofbottom_type; // filed under the `TypeofBottom` name, as `jl_type_extract_name`
        else if (!jl_is_datatype(a))
            return tname_intersection(a, bname, 0);
    }
    // a wrapper is not a datatype, so it has no supertype chain of its own: replace it with
    // the kind of its instances, `typeof(X)` for the single instance of a `TypeEgal{X}`, and
    // `TypeEq` for a `Type{X}`, whose spellings may be of several kinds (which
    // `tname_intersection_dt` then meets with every kind name)
    else if (jl_is_typeegal(a))
        a = jl_typeof(jl_typeegal_T(a));
    else if (jl_is_typeeq(a))
        a = (jl_value_t*)jl_typeeq_type;
    if (jl_is_datatype(a))
        return tname_intersection_dt((jl_datatype_t*)a, bname, jl_supertype_height((jl_datatype_t*)a));
    return 0;
}
```
-/
def tnameIntersection (n : Nat) (T : Types) (ops : GfOps) (a : Val) (bname : String)
    (tparam : Bool) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if a == anyType then
      return true
    let a := a.unwrapUnionall
    if let .union ua ub := a then
      if ← tnameIntersection n T ops ua bname tparam then
        return true
      return ← tnameIntersection n T ops ub bname tparam
    if let .typevar _ _ _ ub := a then
      return ← tnameIntersection n T ops ub bname tparam
    let mut a := a
    if tparam then
      if isKind a || a == anytypeType then
        return true -- a kind contains the `X` of any `Type{X}`
      if !a.isSomeType then
        return false
      a := a.someTypeT.unwrapUnionall
      let isBot ← if a == .bottom then pure true else ops.isTypeofbottomParam a
      if isBot then
        a := typeofbottomType -- filed under the `TypeofBottom` name, as `jl_type_extract_name`
      else if !a.isDatatype then
        return ← tnameIntersection n T ops a bname false
    else if a.isTypeegal then
      a := typeOf a.someTypeT
    else if a.isTypeeq then
      a := typeeqType
    if a.isDatatype then
      let h ← jlSupertypeHeight n T ops.toOps a
      return ← tnameIntersectionDt n T ops.toOps a bname h
    return false

/-- `typemap_type_components`: classify how `t` can match a type object, returning `(byIdentity, byKind)`.

Julia source: src/typemap.c:569-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void typemap_type_components(jl_value_t *t, int *by_identity, int *by_kind) JL_NOTSAFEPOINT
{
    while (1) {
        t = jl_unwrap_unionall(t);
        if (jl_is_typevar(t)) {
            t = ((jl_tvar_t*)t)->ub;
        }
        else if (jl_is_uniontype(t)) {
            typemap_type_components(((jl_uniontype_t*)t)->a, by_identity, by_kind);
            t = ((jl_uniontype_t*)t)->b;
        }
        else {
            break;
        }
    }
    assert(!jl_is_vararg(t));
    if (t == (jl_value_t*)jl_any_type || jl_is_kind(t) || t == (jl_value_t*)jl_anytype_type) {
        *by_kind = 1;
    }
    else if (jl_is_some_Type(t)) {
        *by_identity = 1;
    }
}
```
-/
def typemapTypeComponents (n : Nat) (t : Val) (byIdentity byKind : Bool) : CM (Bool × Bool) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let t := t.unwrapUnionall
    match t with
    | .typevar _ _ _ ub =>
      typemapTypeComponents n ub byIdentity byKind
    | .union ua ub =>
      let (byId, byK) ← typemapTypeComponents n ua byIdentity byKind
      typemapTypeComponents n ub byId byK
    | _ =>
      if t == anyType || isKind t || t == anytypeType then
        return (byIdentity, true)
      else if t.isSomeType then
        return (true, byKind)
      else
        return (byIdentity, byKind)

/-- `concrete_intersects`

Julia source: src/typemap.c:593-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int concrete_intersects(jl_value_t *t, jl_value_t *ty, int8_t tparam) JL_CANSAFEPOINT
{
    if (ty == (jl_value_t*)jl_any_type) // easy case: Any always matches
        return 1;
    if (tparam & 1)
        return jl_isa(t, ty); // (Type{t} <: ty), where is_leaf_type(t) => isa(t, ty)
    else
        return t == ty || jl_subtype(t, ty);
}
```
-/
def concreteIntersects (ops : GfOps) (t ty : Val) (tparam : Nat) : CM Bool := do
  if ty == anyType then
    return true
  if (tparam &&& 1) != 0 then
    ops.isa t ty -- (Type{t} <: ty), where is_leaf_type(t) => isa(t, ty)
  else
    if t == ty then return true
    ops.subtype t ty

/-- `has_covariant_var`: if `TypeVar` `tv` is used covariantly, it cannot be `Union{}`.

Julia source: src/typemap.c:729-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_covariant_var(jl_datatype_t *ttypes, jl_tvar_t *tv)
{
    size_t i, l = jl_nparams(ttypes);
    for (i = 0; i < l; i++)
        if (jl_tparam(ttypes, i) == (jl_value_t*)tv)
            return 1;
    return 0;
}
```
-/
def hasCovariantVar (ttypes tv : Val) : Bool :=
  ttypes.params.any (· == tv)

/-- `rewrap_unionall_bottom`: wrap `t` in the unionalls surrounding `u`, as `jl_rewrap_unionall`,
except that `tv` is instantiated as `Union{}` at the `where` that binds it.

Julia source: src/typemap.c:742-759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *rewrap_unionall_bottom(jl_value_t *t, jl_value_t *u, jl_tvar_t *tv) JL_CANSAFEPOINT
{
    if (!jl_is_unionall(u))
        return t;
    jl_unionall_t *ua = (jl_unionall_t*)u;
    t = rewrap_unionall_bottom(t, ua->body, tv);
    if (t == NULL)
        return NULL;
    JL_GC_PUSH1(&t);
    if (ua->var == tv)
        t = jl_substitute_var_nothrow(t, tv, jl_bottom_type, 1);
    else if (t == ua->body)
        t = u;
    else
        t = jl_type_unionall(ua->var, t);
    JL_GC_POP();
    return t;
}
```
-/
def rewrapUnionallBottom (n : Nat) (T : Types) (ops : Ops) (t u tv : Val) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let T := withBuiltinTypes T
    match u with
    | .unionall id nm lb ub body =>
      let some t ← rewrapUnionallBottom n T ops t body tv | return none
      let var := Val.typevar id nm lb ub
      if var == tv then
        substituteVarNothrow n T ops t tv .bottom 1
      else if t == body then
        return some u
      else
        return some (← typeUnionall n T ops var t)
    | _ => return some t

/-- `typemap_bottom_calls`: handles calls that subtype `closure.type` whose argument at `offs` is `Union{}`.

Julia source: src/typemap.c:767-832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *typemap_bottom_calls(struct typemap_intersection_env *closure, size_t offs) JL_CANSAFEPOINT
{
    jl_value_t *ttypes = jl_unwrap_unionall(closure->type);
    size_t l = jl_nparams(ttypes);
    int unroll = closure->va && l <= offs + 1;
    jl_value_t *ty = unroll ? closure->va : jl_tparam(ttypes, offs);
    jl_tvar_t *tv = NULL;
    if (jl_is_typeeq(ty) && jl_is_typevar(jl_typeeq_T(ty))) {
        // `T` must be `Union{}`, so instantiate it as that at its `where` to form a tighter
        // bound in case `T` got used elsewhere too, which is exact (up to its own bound, when
        // that is open). If that is not a valid instantiation (e.g. `T` is also a `Vararg`
        // count, or a parameter of `B{X>:Int}`), there are no such calls, and so any method
        // "covers" them.
        tv = (jl_tvar_t*)jl_typeeq_T(ty);
        if (tv->lb != jl_bottom_type && !jl_has_free_typevars(tv->lb)) {
            // `T >: lb` with a closed, non-empty `lb` cannot be `Union{}`: there are no such calls
            return jl_bottom_type;
        }
        if (!unroll) {
            jl_value_t *bottom_calls = rewrap_unionall_bottom(ttypes, closure->type, tv);
            return bottom_calls ? bottom_calls : jl_bottom_type; // NULL will pass the subtype query trivially (and would be a valid optimization even without the special bottom method)
        }
    }
    // Otherwise rebuild the tuple, unrolled through `offs` if needed, with this slot rewritten
    // to `Type{Union{}}` directly (which is also what substituting `T` would make it)
    jl_value_t *bottom_calls = NULL;
    jl_svec_t *params = NULL;
    jl_value_t *count = NULL;
    JL_GC_PUSH3(&bottom_calls, &params, &count);
    if (unroll) {
        // `offs` is in the trailing `Vararg`: unroll it through `offs`. That only adds
        // covariant copies of its element, and keeps the `Vararg` (so any typevar in it is
        // already diagonal), so the argument at `offs` is a new copy that is safe to replace
        // (it avoids the hole above).
        jl_value_t *n = jl_unwrap_vararg_num(jl_tparam(ttypes, l - 1));
        ssize_t rest = -1;
        if (n && jl_is_long(n)) {
            rest = jl_unbox_long(n) - (ssize_t)(offs + 2 - l);
            if (rest < 0) {
                // there are no calls with an argument at `offs`
                JL_GC_POP();
                return jl_bottom_type;
            }
        }
        params = jl_alloc_svec(rest == 0 ? offs + 1 : offs + 2);
        for (size_t i = 0; i <= offs; i++)
            jl_svecset(params, i, i < l - 1 ? jl_tparam(ttypes, i) : closure->va);
        if (rest != 0) {
            if (rest > 0)
                count = jl_box_long(rest);
            jl_svecset(params, offs + 1, jl_wrap_vararg(closure->va, count, 1, 0));
        }
    }
    else {
        assert(offs < l);
        params = jl_svec_copy(((jl_datatype_t*)ttypes)->parameters);
    }
    jl_svecset(params, offs, jl_wrap_Type(jl_bottom_type));
    bottom_calls = (jl_value_t*)jl_apply_tuple_type(params, 1);
    if (tv == NULL)
        bottom_calls = jl_rewrap_unionall(bottom_calls, closure->type);
    else
        bottom_calls = rewrap_unionall_bottom(bottom_calls, closure->type, tv);
    JL_GC_POP();
    return bottom_calls ? bottom_calls : jl_bottom_type;
}
```
-/
def typemapBottomCalls (n : Nat) (T : Types) (ops : GfOps) (closure : TypemapIntersectionEnv)
    (offs : Nat) : CM Val := do
  let T := withBuiltinTypes T
  let ttypes := closure.type.unwrapUnionall
  let l := ttypes.nparams
  let unroll := closure.va.isSome && l ≤ offs + 1
  let ty := if unroll then closure.va.getD anyType else ttypes.params[offs]!
  let mut tv : Option Val := none
  if ty.isTypeeq && ty.someTypeT.isTypevar then
    let tvVal := ty.someTypeT
    tv := some tvVal
    if tvVal.tvLb != .bottom && !tvVal.tvLb.hasFreeTypevars then
      -- `T >: lb` with a closed, non-empty `lb` cannot be `Union{}`: there are no such calls
      return .bottom
    if !unroll then
      let bottomCalls ← rewrapUnionallBottom n T ops.toOps ttypes closure.type tvVal
      return bottomCalls.getD .bottom
  let mut params : Array Val := #[]
  if unroll then
    let vaParam := ttypes.params[l - 1]!
    let nVal := vaParam.varargN?
    let mut rest : Int := -1
    if let some (.long nv) := nVal then
      rest := nv - (Int.ofNat (offs + 2) - Int.ofNat l)
      if rest < 0 then
        return .bottom
    for i in [0:offs + 1] do
      let p := if i < l - 1 then ttypes.params[i]! else closure.va.getD anyType
      params := params.push p
    if rest != 0 then
      let count : Option Val := if rest > 0 then some (.long rest) else none
      let some va ← wrapVararg n T ops.toOps closure.va count true 0
        | throw "unreachable: wrapVararg failed in typemap_bottom_calls"
      params := params.push va
  else
    params := ttypes.params.toArray
  let botType ← wrapType n T ops.toOps .bottom
  params := params.set! offs botType
  let bottomCalls? ← instDatatypeInner n T ops.toOps tupleName params.toList true 0
  let bottomCalls? ← match bottomCalls?, tv with
    | none, _ => pure none
    | some bc, none => pure (some (rewrapUnionall bc closure.type))
    | some bc, some tvVal => rewrapUnionallBottom n T ops.toOps bc closure.type tvVal
  return bottomCalls?.getD .bottom

/-- `typemap_bottom_search`: records whether `ml` is the dispatch target of every call in `closure.type`
whose argument at `closure.searchBottom - 1` is `Union{}`.

Julia source: src/typemap.c:840-851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void typemap_bottom_search(jl_typemap_entry_t *ml, struct typemap_intersection_env *closure) JL_CANSAFEPOINT
{
    if (closure->search_bottom == 0)
        return;
    jl_value_t *bottom_calls = typemap_bottom_calls(closure, closure->search_bottom - 1);
    JL_GC_PUSH1(&bottom_calls);
    if (jl_subtype(bottom_calls, (jl_value_t*)ml->sig)) {
        // instruct typemap it can set exclude_typeofbottom on this parameter
        closure->search_bottom = 0;
    }
    JL_GC_POP();
}
```
-/
def typemapBottomSearch (n : Nat) (T : Types) (ops : GfOps) (ml : TypemapEntry)
    (closure : TypemapIntersectionEnv) : CM TypemapIntersectionEnv := do
  if closure.searchBottom == 0 then
    return closure
  let bottomCalls ← typemapBottomCalls n T ops closure (closure.searchBottom - 1)
  if ← ops.subtype bottomCalls ml.sig then
    -- instruct typemap it can set exclude_typeofbottom on this parameter
    return { closure with searchBottom := 0 }
  return closure

mutual
/-- `jl_typemap_intersection_memory_visitor`

Julia source: src/typemap.c:605-677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_typemap_intersection_memory_visitor(jl_genericmemory_t *a, jl_value_t *ty, int8_t tparam,
                                                 int8_t offs, struct typemap_intersection_env *closure) JL_CANSAFEPOINT
{
    JL_GC_PUSH1(&a);
    size_t i, l = a->length;
    _Atomic(jl_typemap_t*) *data = (_Atomic(jl_typemap_t*)*) a->ptr;
    unsigned height = 0;
    jl_datatype_t *tydt = jl_any_type;
    if (tparam & 2) {
        // try to extract a description of ty for intersections, but since we
        jl_value_t *ttype = jl_unwrap_unionall(ty);
        if (tparam & 1)
            // extract T from Type{T} (if possible)
            ttype = jl_is_some_Type(ttype) ? jl_some_Type_T(ttype) : NULL;
        if (ttype && jl_is_datatype(ttype)) {
            tydt = (jl_datatype_t*)ttype;
        }
        else if (ttype) {
            ttype = jl_type_extract_name(ttype, tparam & 1);
            tydt = ttype ? (jl_datatype_t*)jl_unwrap_unionall(((jl_typename_t*)ttype)->wrapper) : NULL;
        }
        if (tydt == jl_any_type)
            ty = (jl_value_t*)jl_any_type;
        else if (tydt == NULL)
            tydt = jl_any_type;
        else
            height = jl_supertype_height(tydt);
    }
    for (i = 1; i < l; i += 2) { // key on odd slot i, value on even slot i+1 (slot 0 is the index)
        jl_value_t *t = jl_atomic_load_relaxed(&data[i]);
        JL_GC_PROMISE_ROOTED(t);
        if (t == jl_nothing || t == NULL)
            continue;
        if (tparam & 2) {
            jl_typemap_t *ml = jl_atomic_load_relaxed(&data[i + 1]);
            JL_GC_PROMISE_ROOTED(ml);
            // the value is published (release) after its key, so ml may be NULL if
            // we're racing with the thread inserting this entry; skip incomplete entries
            if (ml == NULL)
                continue;
            if (tydt == jl_any_type ?
                    tname_intersection(ty, (jl_typename_t*)t, tparam & 1) :
                    tname_intersection_dt(tydt, (jl_typename_t*)t, height)) {
                if ((tparam & 4) && t == (jl_value_t*)jl_typeofbottom_type->name) // skip Type{Union{}} and Type{typeof(Union{})}, since the caller already handled those
                    continue;
                if (jl_is_genericmemory(ml)) {
                    if (!jl_typemap_intersection_memory_visitor((jl_genericmemory_t*)ml, ty, tparam & ~2, offs, closure))
                        goto exit;
                }
                else {
                    if (!jl_typemap_intersection_visitor(ml, offs + 1, closure))
                        goto exit;
                }
            }
        }
        else {
            // `t` is a leaftype, so intersection test becomes subtype (after excluding kinds)
            if (concrete_intersects(t, ty, tparam)) {
                jl_typemap_t *ml = jl_atomic_load_relaxed(&data[i + 1]);
                JL_GC_PROMISE_ROOTED(ml);
                // NOTE: ml might be NULL if we're racing with the thread that's inserting the item
                if (ml != NULL && !jl_typemap_intersection_visitor(ml, offs + 1, closure))
                    goto exit;
            }
        }
    }
    JL_GC_POP();
    return 1;

exit:
    JL_GC_POP();
    return 0;
}
```
-/
def jlTypemapIntersectionMemoryVisitor {α : Type} (n : Nat) (T : Types) (ops : GfOps)
    (a : List (MtKey × Typemap)) (ty : Val) (tparam : Nat) (offs : Nat)
    (closure : TypemapIntersectionEnv) (st : α)
    (fptr : TypemapEntry → TypemapIntersectionEnv → α → CM (Bool × TypemapIntersectionEnv × α))
    (entryFilter : Option (TypemapEntry → TypemapIntersectionEnv → α → Bool) := none) :
    CM (Bool × TypemapIntersectionEnv × α) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut ty := ty
    let mut height : Nat := 0
    let mut tydt : Option Val := some anyType
    if (tparam &&& 2) != 0 then
      let ttype0 := ty.unwrapUnionall
      let ttype? : Option Val :=
        if (tparam &&& 1) != 0 then
          if ttype0.isSomeType then some ttype0.someTypeT else none
        else
          some ttype0
      match ttype? with
      | some ttype =>
        if ttype.isDatatype then
          tydt := some ttype
        else
          match ← jlTypeExtractName n ops ttype ((tparam &&& 1) != 0) with
          | some tnName =>
            let tn ← typenameOf T tnName
            tydt := some tn.wrapper.unwrapUnionall
          | none =>
            tydt := none
      | none =>
        tydt := some anyType
      if tydt == some anyType then
        ty := anyType
      else if tydt.isNone then
        tydt := some anyType
      else if let some dt := tydt then
        height ← jlSupertypeHeight n T ops.toOps dt
    let tydtVal := tydt.getD anyType
    let mut closure := closure
    let mut st := st
    for (k, ml) in a do
      if (tparam &&& 2) != 0 then
        let .typename tName := k | continue
        let hit ←
          if tydtVal == anyType then
            tnameIntersection n T ops ty tName ((tparam &&& 1) != 0)
          else
            tnameIntersectionDt n T ops.toOps tydtVal tName height
        if hit then
          if (tparam &&& 4) != 0 && tName == "Core.TypeofBottom" then
            continue
          match ml with
          | .memory inner =>
            let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops inner ty (tparam - (tparam &&& 2)) offs closure st fptr entryFilter
            closure := c'
            st := st'
            if !ok then return (false, closure, st)
          | _ =>
            let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
            closure := c'
            st := st'
            if !ok then return (false, closure, st)
      else
        let .val t := k | continue
        if ← concreteIntersects ops t ty tparam then
          let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
          closure := c'
          st := st'
          if !ok then return (false, closure, st)
    return (true, closure, st)

/-- `jl_typemap_intersection_node_visitor`: calls `fptr` on each `TypemapEntry` in `ml` in sort order
for which `type ∩ ml.sig != Union{}`, until `fptr` returns `false`.

Julia source: src/typemap.c:682-726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_typemap_intersection_node_visitor(jl_typemap_entry_t *ml, struct typemap_intersection_env *closure) JL_CANSAFEPOINT
{
    // slow-path scan everything in ml
    // mark this `register` because (for branch prediction)
    // that can be absolutely critical for speed
    register jl_typemap_intersection_visitor_fptr fptr = closure->fptr;
    for (;  ml != (void*)jl_nothing; ml = jl_atomic_load_relaxed(&ml->next)) {
        if (closure->max_valid < jl_atomic_load_relaxed(&ml->min_world))
            continue;
        if (closure->min_valid > jl_atomic_load_relaxed(&ml->max_world))
            continue;
        if (closure->entry_filter && !closure->entry_filter(ml, closure))
            continue;
        int nonempty;
        if (closure->emptiness_only) {
            // The callback consumes only the match verdict and `issubty`; skip
            // materializing the intersection type and the typevar environment.
            // (`issubty` matches the full path: jl_type_intersection_env_s
            // reports `type <: ml->sig`; the emptiness verdict is the same
            // conservative one the full intersection would give.)
            closure->issubty = jl_subtype(closure->type, (jl_value_t*)ml->sig);
            nonempty = closure->issubty || !jl_has_empty_intersection(closure->type, (jl_value_t*)ml->sig);
            closure->ti = nonempty ? (jl_value_t*)jl_any_type : jl_bottom_type;
        }
        else {
            jl_svec_t **penv = NULL;
            if (closure->env) {
                closure->env = jl_emptysvec;
                penv = &closure->env;
            }
            closure->ti = jl_type_intersection_env_s(closure->type, (jl_value_t*)ml->sig, penv, &closure->issubty);
            nonempty = closure->ti != (jl_value_t*)jl_bottom_type;
        }
        if (nonempty) {
            // In some corner cases type intersection is conservative and returns something
            // for intersect(A, B) even though A is a dispatch tuple and !(A <: B).
            // For dispatch purposes in such a case we know there's no match. This check
            // fixes issue #30394.
            if (closure->issubty || !jl_is_dispatch_tupletype(closure->type))
                if (!fptr(ml, closure))
                    return 0;
        }
    }
    return 1;
}
```
-/
def jlTypemapIntersectionNodeVisitor {α : Type} (n : Nat) (T : Types) (ops : GfOps)
    (ml : List TypemapEntry) (closure : TypemapIntersectionEnv) (st : α)
    (fptr : TypemapEntry → TypemapIntersectionEnv → α → CM (Bool × TypemapIntersectionEnv × α))
    (entryFilter : Option (TypemapEntry → TypemapIntersectionEnv → α → Bool) := none) :
    CM (Bool × TypemapIntersectionEnv × α) :=
  match n with
  | 0 => outOfBudget
  | _ + 1 => do
    let mut closure := closure
    let mut st := st
    for entry in ml do
      if closure.maxValid < entry.minWorld then
        continue
      if closure.minValid > entry.maxWorld then
        continue
      if let some filt := entryFilter then
        if !filt entry closure st then
          continue
      let mut nonempty := false
      let (nonempty', closure') ←
        if closure.emptinessOnly then do
          let issub ← ops.subtype closure.type entry.sig
          let ne ← if issub then pure true else pure (!(← ops.hasEmptyIntersection closure.type entry.sig))
          let ti := if ne then anyType else .bottom
          pure (ne, { closure with issubty := issub, ti := ti })
        else do
          let withEnv := closure.env.isSome
          let (ti, envList, issub) ← ops.typeIntersectionEnvS closure.type entry.sig withEnv
          let envOpt := if withEnv then some envList else none
          pure (ti != .bottom, { closure with ti := ti, env := envOpt, issubty := issub })
      nonempty := nonempty'
      closure := closure'
      if nonempty then
        -- In some corner cases type intersection is conservative and returns something
        -- for intersect(A, B) even though A is a dispatch tuple and !(A <: B).
        -- For dispatch purposes in such a case we know there's no match. This check
        -- fixes issue #30394.
        let okDispatch ←
          if closure.issubty then pure true
          else pure (!(← isDispatchTupletype T closure.type))
        if okDispatch then
          let (ok, c', st') ← fptr entry closure st
          closure := c'
          st := st'
          if !ok then return (false, closure, st)
    return (true, closure, st)

/-- `jl_typemap_intersection_visitor`

Julia source: src/typemap.c:853-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_typemap_intersection_visitor(jl_typemap_t *map, int offs,
                                    struct typemap_intersection_env *closure)
{
    jl_value_t *ttypes = jl_unwrap_unionall(closure->type);
    assert(jl_is_datatype(ttypes));
    //TODO: fast-path for leaf-type tuples?
    //if (ttypes->isdispatchtuple) {
    //    register jl_typemap_intersection_visitor_fptr fptr = closure->fptr;
    //    struct jl_typemap_assoc search = {(jl_value_t*)closure->type, world, closure->env, 0, ~(size_t)0};
    //    jl_typemap_entry_t *ml = jl_typemap_assoc_by_type(map, search, offs, /*subtype*/1);
    //    if (ml) {
    //        closure->env = search->env;
    //        if (!fptr(ml, closure))
    //            return 0;
    //    }
    //    return 1;
    //}
    if (jl_typeof(map) == (jl_value_t *)jl_typemap_level_type) {
        jl_typemap_level_t *cache = (jl_typemap_level_t*)map;
        jl_value_t *ty;
        size_t l = jl_nparams(ttypes);
        if (closure->va && l <= offs + 1) {
            ty = closure->va;
        }
        else if (l > offs) {
            ty = jl_tparam(ttypes, offs);
        }
        else {
            ty = NULL;
        }
        if (ty) {
            while (jl_is_typevar(ty))
                ty = ((jl_tvar_t*)ty)->ub;
            // approxify the tparam until we have a valid type
            if (jl_has_free_typevars(ty))
                ty = jl_rewrap_unionall(ty, closure->type);
            JL_GC_PUSH1(&ty);
            jl_genericmemory_t *targ = jl_atomic_load_relaxed(&cache->targ);
            jl_genericmemory_t *tname = jl_atomic_load_relaxed(&cache->tname);
            int maybe_type = 0;
            int maybe_kind = 0;
            int exclude_typeofbottom = 0;
            jl_value_t *typetype = NULL;
            jl_value_t *name = NULL;
            // pre-check: optimized pre-intersection test to see if `ty` could intersect with any Type or Kind
            if (targ != (jl_genericmemory_t*)jl_an_empty_memory_any || tname != (jl_genericmemory_t*)jl_an_empty_memory_any) {
                int by_identity = 0;
                typemap_type_components(ty, &by_identity, &maybe_kind);
                maybe_type = by_identity || maybe_kind;
                if (maybe_type && !maybe_kind) { // a kind query keeps the `TypeofBottom` bucket
                    typetype = jl_unwrap_unionall(ty);
                    typetype = jl_is_some_Type(typetype) ? jl_some_Type_T(typetype) : NULL;
                    name = typetype ? jl_type_extract_name(typetype, 1) : NULL;
                    if (!typetype)
                        exclude_typeofbottom = !jl_subtype((jl_value_t*)jl_typeofbottom_type, ty);
                    else if (jl_is_typevar(typetype))
                        exclude_typeofbottom = has_covariant_var((jl_datatype_t*)ttypes, (jl_tvar_t*)typetype);
                    else
                        exclude_typeofbottom = !jl_parameter_includes_bottom(typetype);
                }
            }
            // Decide whether to visit the `Type{Union{}}` buckets, before either is
            // searched: they hold the methods that can dominate the query for intersections
            // at `Type{Union{}}`, so a covering method found in one lets all the rest of
            // the `TypeEq{...}` buckets be skipped. Note that `Type{typeof(Union{})}` is
            // filed under the same name, so a query by that name visits them too, and a
            // query that may be it under another spelling (a union, or a typevar that cannot
            // be `Union{}`) has no precise name, so its scan below includes them instead.
            int visit_bottom = !exclude_typeofbottom || name == (jl_value_t*)jl_typeofbottom_type->name;
            int8_t scan_tparam = visit_bottom ? 3 | 4 : 3; // bit 4: skip those buckets, already visited
            // First check for intersections with methods defined on Type{T}, where T was a concrete type
            if (targ != (jl_genericmemory_t*)jl_an_empty_memory_any && maybe_type) {
                if (visit_bottom) {
                    // detect Type{Union{}}, Type{Type{Union{}}}, and Type{typeof(Union{}} and do those early here
                    // otherwise the possibility of encountering `Type{Union{}}` in this intersection may
                    // be forcing us to do some extra work here whenever we see a typevar, even though
                    // the likelihood of that value actually occurring is frequently likely to be
                    // zero (or result in an ambiguous match)
                    targ = jl_atomic_load_relaxed(&cache->targ); // may be GC'd during type-intersection
                    jl_value_t *ml = mtcache_hash_lookup(targ, (jl_value_t*)jl_typeofbottom_type->name);
                    if (ml != jl_nothing) {
                        size_t search_bottom = closure->search_bottom;
                        closure->search_bottom = offs + 1;
                        if (!jl_typemap_intersection_visitor((jl_typemap_t*)ml, offs+1, closure)) {
                            closure->search_bottom = search_bottom;
                            JL_GC_POP();
                            return 0;
                        }
                        if (closure->search_bottom == 0)
                            exclude_typeofbottom = 1;
                        closure->search_bottom = search_bottom;
                    }
                }
                if (name != (jl_value_t*)jl_typeofbottom_type->name &&
                        (!typetype || jl_has_free_typevars(typetype) || is_cache_leaf(typetype, 1))) { // otherwise cannot contain this particular kind, so don't bother with checking
                    targ = jl_atomic_load_relaxed(&cache->targ); // may be GC'd earlier
                    if (exclude_typeofbottom && name && jl_type_extract_name_precise(typetype, 1)) {
                        // attempt semi-direct lookup of types via their names
                        // consider the type name first
                        jl_value_t *ml = mtcache_hash_lookup(targ, (jl_value_t*)name);
                        if (jl_is_genericmemory(ml)) {
                            if (typetype && !jl_has_free_typevars(typetype)) {
                                // direct lookup of leaf types
                                if (is_cache_leaf(typetype, 1)) {
                                    ml = mtcache_hash_lookup((jl_genericmemory_t*)ml, typetype);
                                    if (ml != jl_nothing) {
                                        if (!jl_typemap_intersection_visitor((jl_typemap_t*)ml, offs+1, closure)) { JL_GC_POP(); return 0; }
                                    }
                                }
                            }
                            else {
                                if (!jl_typemap_intersection_memory_visitor((jl_genericmemory_t*)ml, ty, 1, offs, closure)) { JL_GC_POP(); return 0; }
                            }
                        }
                        else if (ml != jl_nothing) {
                            if (!jl_typemap_intersection_visitor((jl_typemap_t*)ml, offs+1, closure)) { JL_GC_POP(); return 0; }
                        }
                    }
                    else {
                        // else a scan is required to consider all the possible subtypes
                        if (!jl_typemap_intersection_memory_visitor(targ, exclude_typeofbottom ? ty : (jl_value_t*)jl_any_type, scan_tparam, offs, closure)) { JL_GC_POP(); return 0; }
                    }
                }
            }
            jl_genericmemory_t *cachearg1 = jl_atomic_load_relaxed(&cache->arg1);
            if (cachearg1 != (jl_genericmemory_t*)jl_an_empty_memory_any) {
                if (is_cache_leaf(ty, 0)) {
                    jl_typename_t *name = ty == jl_bottom_type ? jl_typeofbottom_type->name : ((jl_datatype_t*)ty)->name;
                    // direct lookup of leaf types
                    jl_value_t *ml = mtcache_hash_lookup(cachearg1, (jl_value_t*)name);
                    if (jl_is_genericmemory(ml))
                        ml = mtcache_hash_lookup((jl_genericmemory_t*)ml, ty);
                    if (ml != jl_nothing) {
                        if (!jl_typemap_intersection_visitor(ml, offs+1, closure)) { JL_GC_POP(); return 0; }
                    }
                }
                else {
                    jl_value_t *name = jl_type_extract_name(ty, 0);
                    if (name && jl_type_extract_name_precise(ty, 0)) {
                        // direct lookup of leaf types
                        jl_value_t *ml = mtcache_hash_lookup(cachearg1, name);
                        if (jl_is_genericmemory(ml)) {
                            if (!jl_typemap_intersection_memory_visitor((jl_genericmemory_t*)ml, ty, 0, offs, closure)) { JL_GC_POP(); return 0; }
                        }
                        else {
                            if (!jl_typemap_intersection_visitor((jl_typemap_t*)ml, offs+1, closure)) { JL_GC_POP(); return 0; }
                        }
                    }
                    else {
                        // else a scan is required to check subtypes
                        if (!jl_typemap_intersection_memory_visitor(cachearg1, ty, 2, offs, closure)) { JL_GC_POP(); return 0; }
                    }
                }
            }
            // Next check for intersections with methods defined on Type{T}, where T was not concrete (it might even have been a TypeVar), but had an extractable TypeName
            if (tname != (jl_genericmemory_t*)jl_an_empty_memory_any && maybe_type) {
                if (visit_bottom) {
                    // Detect Type{Union{}}, Type{Type{Union{}}}, and Type{typeof(Union{}} and do those early here
                    // otherwise the possibility of encountering `Type{Union{}}` in this intersection may
                    // be forcing us to do some extra work here whenever we see a typevar, even though
                    // the likelihood of that value actually occurring is frequently likely to be
                    // zero (or result in an ambiguous match).
                    tname = jl_atomic_load_relaxed(&cache->tname);  // may be GC'd earlier
                    jl_value_t *ml = mtcache_hash_lookup(tname, (jl_value_t*)jl_typeofbottom_type->name);
                    if (ml != jl_nothing) {
                        size_t search_bottom = closure->search_bottom;
                        closure->search_bottom = offs + 1;
                        if (!jl_typemap_intersection_visitor((jl_typemap_t*)ml, offs+1, closure)) {
                            closure->search_bottom = search_bottom;
                            JL_GC_POP();
                            return 0;
                        }
                        if (closure->search_bottom == 0)
                            exclude_typeofbottom = 1;
                        closure->search_bottom = search_bottom;
                    }
                }
                if (exclude_typeofbottom && name && jl_type_extract_name_precise(typetype, 1)) {
                    // semi-direct lookup of types
                    // just consider the type and its direct super types
                    jl_datatype_t *start = (jl_datatype_t*)jl_unwrap_unionall(((jl_typename_t*)name)->wrapper);
                    jl_datatype_t *super = start;
                    if (start == jl_typeofbottom_type)
                        super = tname_super(start); // the `TypeofBottom` bucket was already visited above
                    while (super != NULL) {
                        tname = jl_atomic_load_relaxed(&cache->tname); // reload after callback
                        jl_typemap_t *ml = mtcache_hash_lookup(tname, (jl_value_t*)super->name);
                        if (ml != jl_nothing) {
                            if (!jl_typemap_intersection_visitor(ml, offs+1, closure)) { JL_GC_POP(); return 0; }
                        }
                        super = tname_super(super);
                    }
                }
                else {
                    // else a scan is required to check subtypes of typetype too
                    tname = jl_atomic_load_relaxed(&cache->tname);  // may be GC'd earlier
                    if (!jl_typemap_intersection_memory_visitor(tname, exclude_typeofbottom ? ty : (jl_value_t*)jl_any_type, scan_tparam, offs, closure)) { JL_GC_POP(); return 0; }
                }
            }
            jl_genericmemory_t *name1 = jl_atomic_load_relaxed(&cache->name1);
            if (name1 != (jl_genericmemory_t*)jl_an_empty_memory_any) {
                jl_value_t *name = jl_type_extract_name(ty, 0);
                if (name && jl_type_extract_name_precise(ty, 0)) {
                    jl_datatype_t *super = (jl_datatype_t*)jl_unwrap_unionall(((jl_typename_t*)name)->wrapper);
                    // direct lookup of concrete types
                    while (1) {
                        name1 = jl_atomic_load_relaxed(&cache->name1); // reload after callback
                        jl_typemap_t *ml = mtcache_hash_lookup(name1, (jl_value_t*)super->name);
                        if (ml != jl_nothing) {
                            if (!jl_typemap_intersection_visitor(ml, offs+1, closure)) { JL_GC_POP(); return 0; }
                        }
                        if (super == jl_any_type)
                            break;
                        super = jl_datatype_compute_super(super);
                        if (super == NULL)
                            break; // definition in progress
                    }
                }
                else {
                    // else a scan is required to check subtypes
                    if (!jl_typemap_intersection_memory_visitor(name1, ty, 2, offs, closure)) { JL_GC_POP(); return 0; }
                }
            }
            JL_GC_POP();
        }
        if (!jl_typemap_intersection_node_visitor(jl_atomic_load_relaxed(&cache->linear), closure))
            return 0;
        return jl_typemap_intersection_visitor(jl_atomic_load_relaxed(&cache->any), offs+1, closure);
    }
    else {
        return jl_typemap_intersection_node_visitor(
            (jl_typemap_entry_t*)map, closure);
    }
}
```
-/
def jlTypemapIntersectionVisitor {α : Type} (n : Nat) (T : Types) (ops : GfOps)
    (map : Typemap) (offs : Nat) (closure : TypemapIntersectionEnv) (st : α)
    (fptr : TypemapEntry → TypemapIntersectionEnv → α → CM (Bool × TypemapIntersectionEnv × α))
    (entryFilter : Option (TypemapEntry → TypemapIntersectionEnv → α → Bool) := none) :
    CM (Bool × TypemapIntersectionEnv × α) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let ttypes := closure.type.unwrapUnionall
    match map with
    | .level cachearg1 targ name1 tname linear any =>
      let mut closure := closure
      let mut st := st
      let l := ttypes.nparams
      let ty? : Option Val :=
        if closure.va.isSome && l ≤ offs + 1 then
          closure.va
        else if l > offs then
          some ttypes.params[offs]!
        else
          none
      if let some ty0 := ty? then
        let mut ty := ty0
        let mut tvSteps := n
        while ty.isTypevar do
          if tvSteps == 0 then outOfBudget
          tvSteps := tvSteps - 1
          ty := ty.tvUb
        -- approxify the tparam until we have a valid type
        if ty.hasFreeTypevars then
          ty := rewrapUnionall ty closure.type
        let mut maybeType := false
        let mut maybeKind := false
        let mut excludeTypeofbottom := false
        let mut typetype : Option Val := none
        let mut name : Option String := none
        -- pre-check: optimized pre-intersection test to see if `ty` could intersect with any Type or Kind
        if !targ.isEmpty || !tname.isEmpty then
          let (byIdentity, mk) ← typemapTypeComponents n ty false false
          maybeKind := mk
          maybeType := byIdentity || maybeKind
          if maybeType && !maybeKind then -- a kind query keeps the `TypeofBottom` bucket
            let tt := ty.unwrapUnionall
            typetype := if tt.isSomeType then some tt.someTypeT else none
            name ← match typetype with
              | some tp => jlTypeExtractName n ops tp true
              | none => pure none
            excludeTypeofbottom ← match typetype with
              | none => pure (!(← ops.subtype typeofbottomType ty))
              | some tp =>
                if tp.isTypevar then
                  pure (hasCovariantVar ttypes tp)
                else
                  pure (!(← jlParameterIncludesBottom n tp))
        let visitBottom := !excludeTypeofbottom || name == some "Core.TypeofBottom"
        let scanTparam : Nat := if visitBottom then (3 ||| 4) else 3
        -- First check for intersections with methods defined on Type{T}, where T was a concrete type
        if !targ.isEmpty && maybeType then
          if visitBottom then
            let ml ← mtcacheHashLookup n T targ (.typename "Core.TypeofBottom")
            if !(match ml with | .entries [] => true | _ => false) then
              let searchBottom := closure.searchBottom
              closure := { closure with searchBottom := offs + 1 }
              let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
              closure := c'
              st := st'
              if !ok then
                return (false, { closure with searchBottom := searchBottom }, st)
              if closure.searchBottom == 0 then
                excludeTypeofbottom := true
              closure := { closure with searchBottom := searchBottom }
          let condTarg ←
            if name == some "Core.TypeofBottom" then
              pure false
            else
              match typetype with
              | none => pure true
              | some tp =>
                if tp.hasFreeTypevars then pure true
                else isCacheLeaf T tp true
          if condTarg then
            let directPrecise ← match excludeTypeofbottom, name, typetype with
              | true, some _, some tp => jlTypeExtractNamePrecise n T ops tp true
              | _, _, _ => pure false
            if directPrecise then
              let nm := name.getD ""
              let ml ← mtcacheHashLookup n T targ (.typename nm)
              match ml with
              | .memory inner =>
                match typetype with
                | some tp =>
                  if !tp.hasFreeTypevars then
                    if ← isCacheLeaf T tp true then
                      let ml2 ← mtcacheHashLookup n T inner (.val tp)
                      if !(match ml2 with | .entries [] => true | _ => false) then
                        let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml2 (offs + 1) closure st fptr entryFilter
                        closure := c'
                        st := st'
                        if !ok then return (false, closure, st)
                  else
                    let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops inner ty 1 offs closure st fptr entryFilter
                    closure := c'
                    st := st'
                    if !ok then return (false, closure, st)
                | none =>
                  let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops inner ty 1 offs closure st fptr entryFilter
                  closure := c'
                  st := st'
                  if !ok then return (false, closure, st)
              | .entries [] => pure ()
              | _ =>
                let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
                closure := c'
                st := st'
                if !ok then return (false, closure, st)
            else
              let scanTy := if excludeTypeofbottom then ty else anyType
              let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops targ scanTy scanTparam offs closure st fptr entryFilter
              closure := c'
              st := st'
              if !ok then return (false, closure, st)
        -- Next check cache->arg1
        if !cachearg1.isEmpty then
          if ← isCacheLeaf T ty false then
            let nm := if ty == .bottom then "Core.TypeofBottom" else ty.name?.getD ""
            let mut ml ← mtcacheHashLookup n T cachearg1 (.typename nm)
            if let .memory inner := ml then
              ml ← mtcacheHashLookup n T inner (.val ty)
            if !(match ml with | .entries [] => true | _ => false) then
              let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
              closure := c'
              st := st'
              if !ok then return (false, closure, st)
          else
            let nm? ← jlTypeExtractName n ops ty false
            let precise ← if nm?.isSome then jlTypeExtractNamePrecise n T ops ty false else pure false
            if let (some nm, true) := (nm?, precise) then
              let ml ← mtcacheHashLookup n T cachearg1 (.typename nm)
              match ml with
              | .memory inner =>
                let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops inner ty 0 offs closure st fptr entryFilter
                closure := c'
                st := st'
                if !ok then return (false, closure, st)
              | _ =>
                let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
                closure := c'
                st := st'
                if !ok then return (false, closure, st)
            else
              let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops cachearg1 ty 2 offs closure st fptr entryFilter
              closure := c'
              st := st'
              if !ok then return (false, closure, st)
        -- Next check intersections with methods defined on Type{T} in cache->tname
        if !tname.isEmpty && maybeType then
          if visitBottom then
            let ml ← mtcacheHashLookup n T tname (.typename "Core.TypeofBottom")
            if !(match ml with | .entries [] => true | _ => false) then
              let searchBottom := closure.searchBottom
              closure := { closure with searchBottom := offs + 1 }
              let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
              closure := c'
              st := st'
              if !ok then
                return (false, { closure with searchBottom := searchBottom }, st)
              if closure.searchBottom == 0 then
                excludeTypeofbottom := true
              closure := { closure with searchBottom := searchBottom }
          let directPrecise ← match excludeTypeofbottom, name, typetype with
            | true, some _, some tp => jlTypeExtractNamePrecise n T ops tp true
            | _, _, _ => pure false
          if directPrecise then
            let nm := name.getD ""
            let tn ← typenameOf T nm
            let start := tn.wrapper.unwrapUnionall
            let mut super? : Option Val ←
              if start == typeofbottomType then
                tnameSuper n T ops.toOps start
              else
                pure (some start)
            let mut supSteps := n
            while super?.isSome do
              if supSteps == 0 then outOfBudget
              supSteps := supSteps - 1
              let some sup := super? | break
              let supName := sup.name?.getD ""
              let ml ← mtcacheHashLookup n T tname (.typename supName)
              if !(match ml with | .entries [] => true | _ => false) then
                let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
                closure := c'
                st := st'
                if !ok then return (false, closure, st)
              super? ← tnameSuper n T ops.toOps sup
          else
            let scanTy := if excludeTypeofbottom then ty else anyType
            let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops tname scanTy scanTparam offs closure st fptr entryFilter
            closure := c'
            st := st'
            if !ok then return (false, closure, st)
        -- Next check cache->name1
        if !name1.isEmpty then
          let nm? ← jlTypeExtractName n ops ty false
          let precise ← if nm?.isSome then jlTypeExtractNamePrecise n T ops ty false else pure false
          if let (some nm, true) := (nm?, precise) then
            let tn ← typenameOf T nm
            let mut super? : Option Val := some tn.wrapper.unwrapUnionall
            let mut supSteps := n
            while super?.isSome do
              if supSteps == 0 then outOfBudget
              supSteps := supSteps - 1
              let some sup := super? | break
              let supName := sup.name?.getD ""
              let ml ← mtcacheHashLookup n T name1 (.typename supName)
              if !(match ml with | .entries [] => true | _ => false) then
                let (ok, c', st') ← jlTypemapIntersectionVisitor n T ops ml (offs + 1) closure st fptr entryFilter
                closure := c'
                st := st'
                if !ok then return (false, closure, st)
              if sup == anyType then
                break
              super? ← datatypeComputeSuper n T ops.toOps sup
          else
            let (ok, c', st') ← jlTypemapIntersectionMemoryVisitor n T ops name1 ty 2 offs closure st fptr entryFilter
            closure := c'
            st := st'
            if !ok then return (false, closure, st)
      let (ok, c', st') ← jlTypemapIntersectionNodeVisitor n T ops linear closure st fptr entryFilter
      closure := c'
      st := st'
      if !ok then return (false, closure, st)
      jlTypemapIntersectionVisitor n T ops any (offs + 1) closure st fptr entryFilter
    | .entries ml =>
      jlTypemapIntersectionNodeVisitor n T ops ml closure st fptr entryFilter
    | .memory pairs =>
      jlTypemapIntersectionMemoryVisitor n T ops pairs anyType 2 offs closure st fptr entryFilter
end

/-- `jl_typemap_entry_assoc_by_type`

Julia source: src/typemap.c:1099-1156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_typemap_entry_t *jl_typemap_entry_assoc_by_type(
        jl_typemap_entry_t *ml,
        struct jl_typemap_assoc *search) JL_CANSAFEPOINT
{
    jl_value_t *types = search->types;
    JL_GC_PROMISE_ROOTED(types);
    jl_value_t *unw = jl_unwrap_unionall((jl_value_t*)types);
    int isua = jl_is_unionall(types);
    size_t n = jl_nparams(unw);
    int typesisva = n == 0 ? 0 : jl_is_vararg(jl_tparam(unw, n-1));
    for (; ml != (void*)jl_nothing; ml = jl_atomic_load_relaxed(&ml->next)) {
        if (search->world < jl_atomic_load_relaxed(&ml->min_world) || search->world > jl_atomic_load_relaxed(&ml->max_world))
            continue;
        size_t lensig = jl_nparams(jl_unwrap_unionall((jl_value_t*)ml->sig));
        if (lensig == n || (ml->va && lensig <= n+1)) {
            int resetenv = 0, ismatch = 1;
            if (ml->simplesig != (void*)jl_nothing && !isua) {
                size_t lensimplesig = jl_nparams(ml->simplesig);
                int isva = lensimplesig > 0 && jl_is_vararg(jl_tparam(ml->simplesig, lensimplesig - 1));
                if (lensig == n || (isva && lensimplesig <= n + 1))
                    ismatch = sig_match_by_type_simple(jl_svec_data(((jl_datatype_t*)types)->parameters), n,
                                                       ml->simplesig, lensimplesig, isva);
                else
                    ismatch = 0;
            }

            if (ismatch == 0)
                ; // nothing
            else if (ml->isleafsig && !typesisva && !isua)
                ismatch = sig_match_by_type_leaf(jl_svec_data(((jl_datatype_t*)types)->parameters),
                                                 ml->sig, lensig);
            else if (ml->issimplesig && !typesisva && !isua)
                ismatch = sig_match_by_type_simple(jl_svec_data(((jl_datatype_t*)types)->parameters), n,
                                                   ml->sig, lensig, ml->va);
            else {
                ismatch = jl_subtype_matching(types, (jl_value_t*)ml->sig, search->env ? &search->env : NULL);
                if (ismatch && search->env)
                    resetenv = 1;
            }
            if (ismatch) {
                size_t i, l;
                for (i = 0, l = jl_svec_len(ml->guardsigs); i < l; i++) {
                    // see corresponding code in jl_typemap_entry_assoc_exact
                    if (jl_subtype(types, jl_svecref(ml->guardsigs, i))) {
                        ismatch = 0;
                        break;
                    }
                }
                if (ismatch) {
                    return ml;
                }
            }
            if (resetenv)
                search->env = jl_emptysvec;
        }
    }
    return NULL;
}
```
-/
def jlTypemapEntryAssocByType (n : Nat) (T : Types) (ops : GfOps) (ml : List TypemapEntry)
    (search : TypemapAssoc) : CM (Option TypemapEntry × TypemapAssoc) := do
  let types := search.types
  let unw := types.unwrapUnionall
  let isua := types.isUnionall
  let nparams := unw.nparams
  let typesisva := if nparams == 0 then false else unw.params[nparams - 1]!.isVararg
  let mut search := search
  for entry in ml do
    if search.world < entry.minWorld || search.world > entry.maxWorld then
      continue
    let lensig := entry.sig.unwrapUnionall.nparams
    if lensig == nparams || (entry.va && lensig ≤ nparams + 1) then
      let mut resetenv := false
      let mut ismatch := true
      if let some simplesig := entry.simplesig then
        if !isua then
          let lensimplesig := simplesig.nparams
          let isva := lensimplesig > 0 && simplesig.params[lensimplesig - 1]!.isVararg
          if lensig == nparams || (isva && lensimplesig ≤ nparams + 1) then
            ismatch ← sigMatchByTypeSimple n T ops types.params nparams simplesig lensimplesig isva
          else
            ismatch := false
      if !ismatch then
        pure ()
      else if entry.isleafsig && !typesisva && !isua then
        ismatch ← sigMatchByTypeLeaf ops types.params entry.sig lensig
      else if entry.issimplesig && !typesisva && !isua then
        ismatch ← sigMatchByTypeSimple n T ops types.params nparams entry.sig lensig entry.va
      else
        let withEnv := search.env.isSome
        let (matched, envOut) ← ops.subtypeMatching types entry.sig withEnv
        ismatch := matched
        if ismatch && withEnv then
          search := { search with env := some envOut }
          resetenv := true
      if ismatch then
        for g in entry.guardsigs do
          if ← ops.subtype types g then
            ismatch := false
            break
        if ismatch then
          return (some entry, search)
      if resetenv then
        search := { search with env := some [] }
  return (none, search)

/-- `jl_typemap_entry_lookup_by_type`

Julia source: src/typemap.c:1158-1193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_typemap_entry_t *jl_typemap_entry_lookup_by_type(
        jl_typemap_entry_t *ml, struct jl_typemap_assoc *search) JL_CANSAFEPOINT
{
    for (; ml != (void*)jl_nothing; ml = jl_atomic_load_relaxed(&ml->next)) {
        if (search->world < jl_atomic_load_relaxed(&ml->min_world) || search->world > jl_atomic_load_relaxed(&ml->max_world))
            continue;
        // unroll the first few cases here, to the extent that is possible to do fast and easily
        jl_value_t *types = search->types;
        JL_GC_PROMISE_ROOTED(types);
        jl_value_t *a = jl_unwrap_unionall(types);
        jl_value_t *b = jl_unwrap_unionall((jl_value_t*)ml->sig);
        size_t na = jl_nparams(a);
        size_t nb = jl_nparams(b);
        int va_a = na > 0 && jl_is_vararg(jl_tparam(a, na - 1));
        int va_b = nb > 0 && jl_is_vararg(jl_tparam(b, nb - 1));
        if (!va_a && !va_b) {
            if (na != nb)
                continue;
        }
        if (na - va_a > 0 && nb - va_b > 0) {
            if (jl_obviously_unequal(jl_tparam(a, 0), jl_tparam(b, 0)))
                continue;
            if (na - va_a > 1 && nb - va_b > 1) {
                if (jl_obviously_unequal(jl_tparam(a, 1), jl_tparam(b, 1)))
                    continue;
                if (na - va_a > 2 && nb - va_b > 2) {
                    if (jl_obviously_unequal(jl_tparam(a, 2), jl_tparam(b, 2)))
                        continue;
                }
            }
        }
        if (jl_types_equal(types, (jl_value_t*)ml->sig))
            return ml;
    }
    return NULL;
}
```
-/
def jlTypemapEntryLookupByType (ops : GfOps) (ml : List TypemapEntry) (search : TypemapAssoc) :
    CM (Option TypemapEntry) := do
  for entry in ml do
    if search.world < entry.minWorld || search.world > entry.maxWorld then
      continue
    let types := search.types
    let a := types.unwrapUnionall
    let b := entry.sig.unwrapUnionall
    let na := a.nparams
    let nb := b.nparams
    let vaA := if na > 0 && a.params[na - 1]!.isVararg then 1 else 0
    let vaB := if nb > 0 && b.params[nb - 1]!.isVararg then 1 else 0
    if vaA == 0 && vaB == 0 then
      if na != nb then
        continue
    if na - vaA > 0 && nb - vaB > 0 then
      if ← ops.obviouslyUnequal a.params[0]! b.params[0]! then
        continue
      if na - vaA > 1 && nb - vaB > 1 then
        if ← ops.obviouslyUnequal a.params[1]! b.params[1]! then
          continue
        if na - vaA > 2 && nb - vaB > 2 then
          if ← ops.obviouslyUnequal a.params[2]! b.params[2]! then
            continue
    if ← ops.typesEqual types entry.sig then
      return some entry
  return none

/-- `jl_typemap_assoc_by_type`: general entry point for looking up a type in the cache as a
subtype (`subtype = true`) or with `types_equal` (`subtype = false`).

Julia source: src/typemap.c:1198-1367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_typemap_entry_t *jl_typemap_assoc_by_type(
        jl_typemap_t *ml_or_cache,
        struct jl_typemap_assoc *search,
        int8_t offs, uint8_t subtype)
{
    if (jl_typeof(ml_or_cache) == (jl_value_t *)jl_typemap_level_type) {
        jl_typemap_level_t *cache = (jl_typemap_level_t*)ml_or_cache;
        // called object is the primary key for constructors, otherwise first argument
        jl_value_t *ty;
        jl_value_t *ttypes = jl_unwrap_unionall((jl_value_t*)search->types);
        JL_GC_PROMISE_ROOTED(ttypes);
        assert(jl_is_datatype(ttypes));
        size_t l = jl_nparams(ttypes);
        int isva = 0;
        // compute the type at offset `offs` into `types`, which may be a Vararg
        if (l <= offs + 1) {
            ty = jl_tparam(ttypes, l - 1);
            if (jl_is_vararg(ty)) {
                ty = jl_unwrap_vararg(ty);
                isva = 1;
            }
            else if (l <= offs) {
                ty = NULL;
            }
        }
        else if (l > offs) {
            ty = jl_tparam(ttypes, offs);
        }
        else {
            ty = NULL;
        }
        // If there is a type at offs, look in the optimized leaf type caches
        if (ty && !subtype) {
            if (jl_is_any(ty))
                return jl_typemap_assoc_by_type(jl_atomic_load_relaxed(&cache->any), search, offs + 1, subtype);
            if (isva) // in lookup mode, want to match Vararg exactly, not as a subtype
                ty = NULL;
        }
        if (ty) {
            // now look at the optimized leaftype caches
            if (jl_is_some_Type(ty)) {
                jl_value_t *a0 = jl_some_Type_T(ty);
                if (is_cache_leaf(a0, 1)) {
                    jl_genericmemory_t *targ = jl_atomic_load_relaxed(&cache->targ);
                    if (targ != (jl_genericmemory_t*)jl_an_empty_memory_any) {
                        jl_typename_t *name = a0 == jl_bottom_type ? jl_typeofbottom_type->name : ((jl_datatype_t*)a0)->name;
                        jl_value_t *ml = mtcache_hash_lookup(targ, (jl_value_t*)name);
                        if (jl_is_genericmemory(ml))
                            ml = mtcache_hash_lookup((jl_genericmemory_t*)ml, a0);
                        if (ml != jl_nothing) {
                            jl_typemap_entry_t *li = jl_typemap_assoc_by_type((jl_typemap_t*)ml, search, offs + 1, subtype);
                            if (li) return li;
                        }
                    }
                    if (!subtype) return NULL;
                }
            }
            if (is_cache_leaf(ty, 0)) {
                jl_genericmemory_t *cachearg1 = jl_atomic_load_relaxed(&cache->arg1);
                if (cachearg1 != (jl_genericmemory_t*)jl_an_empty_memory_any) {
                    jl_typename_t *name = ty == jl_bottom_type ? jl_typeofbottom_type->name : ((jl_datatype_t*)ty)->name;
                    jl_value_t *ml = mtcache_hash_lookup(cachearg1, (jl_value_t*)name);
                    if (jl_is_genericmemory(ml))
                        ml = mtcache_hash_lookup((jl_genericmemory_t*)ml, ty);
                    if (ml != jl_nothing) {
                        jl_typemap_entry_t *li = jl_typemap_assoc_by_type((jl_typemap_t*)ml, search, offs + 1, subtype);
                        if (li) return li;
                    }
                }
                if (!subtype) return NULL;
            }
        }
        if (ty || subtype) {
            // now look at the optimized TypeName caches
            jl_genericmemory_t *tname = jl_atomic_load_relaxed(&cache->tname);
            if (tname != (jl_genericmemory_t*)jl_an_empty_memory_any) {
                jl_value_t *a0 = ty && jl_is_some_Type(ty) ? jl_type_extract_name(jl_some_Type_T(ty), 1) : NULL;
                if (a0) { // TODO: if we start analyzing Union types in jl_type_extract_name, then a0 might be over-approximated here, leading us to miss possible subtypes
                    jl_datatype_t *super = (jl_datatype_t*)jl_unwrap_unionall(((jl_typename_t*)a0)->wrapper);
                    while (super != NULL) {
                        tname = jl_atomic_load_relaxed(&cache->tname); // reload after tree descent (which may hit safepoints)
                        jl_typemap_t *ml = mtcache_hash_lookup(tname, (jl_value_t*)super->name);
                        if (ml != (void*)jl_nothing) {
                            jl_typemap_entry_t *li = jl_typemap_assoc_by_type(ml, search, offs + 1, subtype);
                            if (li) return li;
                        }
                        if (!subtype)
                            break;
                        super = tname_super(super);
                    }
                }
                else {
                    if (!ty || !jl_has_empty_intersection((jl_value_t*)jl_type_type, ty)) {
                        jl_genericmemory_t *tname = jl_atomic_load_relaxed(&cache->tname); // reload after type-intersect
                        // couldn't figure out unique `a0` initial point, so scan all for matches
                        size_t i, l = tname->length;
                        _Atomic(jl_typemap_t*) *data = (_Atomic(jl_typemap_t*)*) jl_genericmemory_ptr_data(tname);
                        JL_GC_PUSH1(&tname);
                        for (i = 2; i < l; i += 2) { // values live on even slots >= 2 (slot 0 is the index)
                            jl_typemap_t *ml = jl_atomic_load_relaxed(&data[i]);
                            if (ml == NULL || ml == jl_nothing)
                                continue;
                            jl_typemap_entry_t *li = jl_typemap_assoc_by_type(ml, search, offs + 1, subtype);
                            if (li) {
                                JL_GC_POP();
                                return li;
                            }
                        }
                        JL_GC_POP();
                    }
                }
            }
            jl_genericmemory_t *name1 = jl_atomic_load_relaxed(&cache->name1);
            if (name1 != (jl_genericmemory_t*)jl_an_empty_memory_any) {
                if (ty) {
                    jl_value_t *a0 = jl_type_extract_name(ty, 0);
                    if (a0) { // TODO: if we start analyzing Union types in jl_type_extract_name, then a0 might be over-approximated here, leading us to miss possible subtypes
                        jl_datatype_t *super = (jl_datatype_t*)jl_unwrap_unionall(((jl_typename_t*)a0)->wrapper);
                        while (1) {
                            name1 = jl_atomic_load_relaxed(&cache->name1); // reload after tree descent (which may hit safepoints)
                            jl_typemap_t *ml = mtcache_hash_lookup(name1, (jl_value_t*)super->name);
                            if (ml != (void*)jl_nothing) {
                                jl_typemap_entry_t *li =
                                    jl_typemap_assoc_by_type(ml, search, offs + 1, subtype);
                                if (li) return li;
                            }
                            if (super == jl_any_type || !subtype)
                                break;
                            super = jl_datatype_compute_super(super);
                            if (super == NULL)
                                break; // definition in progress
                        }
                    }
                }
                else {
                    // doing subtype, but couldn't figure out unique `ty`, so scan all for supertypes
                    size_t i, l = name1->length;
                    _Atomic(jl_typemap_t*) *data = (_Atomic(jl_typemap_t*)*) jl_genericmemory_ptr_data(name1);
                    JL_GC_PUSH1(&name1);
                    for (i = 2; i < l; i += 2) { // values live on even slots >= 2 (slot 0 is the index)
                        jl_typemap_t *ml = jl_atomic_load_relaxed(&data[i]);
                        if (ml == NULL || ml == jl_nothing)
                            continue;
                        jl_typemap_entry_t *li = jl_typemap_assoc_by_type(ml, search, offs + 1, subtype);
                        if (li) {
                            JL_GC_POP();
                            return li;
                        }
                    }
                    JL_GC_POP();
                }
            }
        }
        // Always check the list (since offs doesn't always start at 0)
        if (subtype) {
            jl_typemap_entry_t *li = jl_typemap_entry_assoc_by_type(jl_atomic_load_relaxed(&cache->linear), search);
            if (li) return li;
            return jl_typemap_assoc_by_type(jl_atomic_load_relaxed(&cache->any), search, offs + 1, subtype);
        }
        else {
            return jl_typemap_entry_lookup_by_type(jl_atomic_load_relaxed(&cache->linear), search);
        }
    }
    else {
        jl_typemap_entry_t *leaf = (jl_typemap_entry_t*)ml_or_cache;
        return subtype ?
            jl_typemap_entry_assoc_by_type(leaf, search) :
            jl_typemap_entry_lookup_by_type(leaf, search);
    }
}
```
-/
def jlTypemapAssocByType (n : Nat) (T : Types) (ops : GfOps) (mlOrCache : Typemap)
    (search : TypemapAssoc) (offs : Nat) (subtype : Bool) :
    CM (Option TypemapEntry × TypemapAssoc) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match mlOrCache with
    | .level cachearg1 targ name1 tname linear any =>
      let mut search := search
      let ttypes := search.types.unwrapUnionall
      let l := ttypes.nparams
      let mut isva := false
      let mut ty? : Option Val := none
      if l ≤ offs + 1 then
        if l > 0 then
          let last := ttypes.params[l - 1]!
          if last.isVararg then
            ty? := some last.unwrapVararg
            isva := true
          else if l ≤ offs then
            ty? := none
          else
            ty? := some last
      else if l > offs then
        ty? := some ttypes.params[offs]!
      if !subtype then
        if let some ty := ty? then
          if ← jlIsAny n ty then
            return ← jlTypemapAssocByType n T ops any search (offs + 1) subtype
          if isva then
            ty? := none
      if let some ty := ty? then
        if ty.isSomeType then
          let a0 := ty.someTypeT
          if ← isCacheLeaf T a0 true then
            if !targ.isEmpty then
              let nm := if a0 == .bottom then "Core.TypeofBottom" else a0.name?.getD ""
              let mut ml ← mtcacheHashLookup n T targ (.typename nm)
              if let .memory inner := ml then
                ml ← mtcacheHashLookup n T inner (.val a0)
              if !(match ml with | .entries [] => true | _ => false) then
                let (li, s') ← jlTypemapAssocByType n T ops ml search (offs + 1) subtype
                search := s'
                if li.isSome then return (li, search)
            if !subtype then return (none, search)
        if ← isCacheLeaf T ty false then
          if !cachearg1.isEmpty then
            let nm := if ty == .bottom then "Core.TypeofBottom" else ty.name?.getD ""
            let mut ml ← mtcacheHashLookup n T cachearg1 (.typename nm)
            if let .memory inner := ml then
              ml ← mtcacheHashLookup n T inner (.val ty)
            if !(match ml with | .entries [] => true | _ => false) then
              let (li, s') ← jlTypemapAssocByType n T ops ml search (offs + 1) subtype
              search := s'
              if li.isSome then return (li, search)
          if !subtype then return (none, search)
      if ty?.isSome || subtype then
        if !tname.isEmpty then
          let a0? ← match ty? with
            | some ty =>
              if ty.isSomeType then jlTypeExtractName n ops ty.someTypeT true else pure none
            | none => pure none
          if let some a0 := a0? then
            let tn ← typenameOf T a0
            let mut super? : Option Val := some tn.wrapper.unwrapUnionall
            let mut steps := n
            while super?.isSome do
              if steps == 0 then outOfBudget
              steps := steps - 1
              let some sup := super? | break
              let ml ← mtcacheHashLookup n T tname (.typename (sup.name?.getD ""))
              if !(match ml with | .entries [] => true | _ => false) then
                let (li, s') ← jlTypemapAssocByType n T ops ml search (offs + 1) subtype
                search := s'
                if li.isSome then return (li, search)
              if !subtype then break
              super? ← tnameSuper n T ops.toOps sup
          else
            let checkTname ← match ty? with
              | none => pure true
              | some ty =>
                let tt ← mkTypeType
                pure (!(← ops.hasEmptyIntersection tt ty))
            if checkTname then
              for (_, ml) in tname do
                if !(match ml with | .entries [] => true | _ => false) then
                  let (li, s') ← jlTypemapAssocByType n T ops ml search (offs + 1) subtype
                  search := s'
                  if li.isSome then return (li, search)
        if !name1.isEmpty then
          if let some ty := ty? then
            if let some a0 ← jlTypeExtractName n ops ty false then
              let tn ← typenameOf T a0
              let mut super? : Option Val := some tn.wrapper.unwrapUnionall
              let mut steps := n
              while super?.isSome do
                if steps == 0 then outOfBudget
                steps := steps - 1
                let some sup := super? | break
                let ml ← mtcacheHashLookup n T name1 (.typename (sup.name?.getD ""))
                if !(match ml with | .entries [] => true | _ => false) then
                  let (li, s') ← jlTypemapAssocByType n T ops ml search (offs + 1) subtype
                  search := s'
                  if li.isSome then return (li, search)
                if sup == anyType || !subtype then break
                super? ← datatypeComputeSuper n T ops.toOps sup
          else
            for (_, ml) in name1 do
              if !(match ml with | .entries [] => true | _ => false) then
                let (li, s') ← jlTypemapAssocByType n T ops ml search (offs + 1) subtype
                search := s'
                if li.isSome then return (li, search)
      if subtype then
        let (li, s') ← jlTypemapEntryAssocByType n T ops linear search
        search := s'
        if li.isSome then return (li, search)
        jlTypemapAssocByType n T ops any search (offs + 1) subtype
      else
        let li ← jlTypemapEntryLookupByType ops linear search
        return (li, search)
    | .entries leaf =>
      if subtype then
        jlTypemapEntryAssocByType n T ops leaf search
      else do
        let li ← jlTypemapEntryLookupByType ops leaf search
        return (li, search)
    | .memory pairs =>
      let mut search := search
      for (_, ml) in pairs do
        let (li, s') ← jlTypemapAssocByType n T ops ml search (offs + 1) subtype
        search := s'
        if li.isSome then return (li, search)
      return (none, search)

/-- `jl_typemap_list_count_locked`

Julia source: src/typemap.c:1532-1540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static unsigned jl_typemap_list_count_locked(jl_typemap_entry_t *ml) JL_NOTSAFEPOINT
{
    unsigned count = 0;
    while (ml != (void*)jl_nothing) {
        count++;
        ml = jl_atomic_load_relaxed(&ml->next);
    }
    return count;
}
```
-/
def jlTypemapListCountLocked (ml : List TypemapEntry) : Nat :=
  ml.length

/-- `jl_new_typemap_level`

Julia source: src/typemap.c:1544-1557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_typemap_level_t *jl_new_typemap_level(void) JL_CANSAFEPOINT
{
    jl_task_t *ct = jl_current_task;
    jl_typemap_level_t *cache =
        (jl_typemap_level_t*)jl_gc_alloc(ct->ptls, sizeof(jl_typemap_level_t),
                                         jl_typemap_level_type);
    jl_atomic_store_relaxed(&cache->arg1, (jl_genericmemory_t*)jl_an_empty_memory_any);
    jl_atomic_store_relaxed(&cache->targ, (jl_genericmemory_t*)jl_an_empty_memory_any);
    jl_atomic_store_relaxed(&cache->name1, (jl_genericmemory_t*)jl_an_empty_memory_any);
    jl_atomic_store_relaxed(&cache->tname, (jl_genericmemory_t*)jl_an_empty_memory_any);
    jl_atomic_store_relaxed(&cache->linear, (jl_typemap_entry_t*)jl_nothing);
    jl_atomic_store_relaxed(&cache->any, jl_nothing);
    return cache;
}
```
-/
def jlNewTypemapLevel : Typemap :=
  .level [] [] [] [] [] (.entries [])

/-- `jl_typemap_list_insert_`: pick the first insertion point that guarantees the list ordering
will be `(leaf sigs..., simple sigs..., other sigs...)`.

Julia source: src/typemap.c:1598-1617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void jl_typemap_list_insert_(
        jl_typemap_t *map, _Atomic(jl_typemap_entry_t*) *pml, jl_value_t *parent,
        jl_typemap_entry_t *newrec)
{
    jl_typemap_entry_t *l = jl_atomic_load_relaxed(pml);

    // Pick the first intersection point that guarantees that the list ordering
    // will be (leaf sigs..., simple sigs..., other sigs...)
    while ((jl_value_t*)l != jl_nothing) {
        if (newrec->isleafsig || !l->isleafsig)
            if (newrec->issimplesig || !l->issimplesig)
                break;
        pml = &l->next;
        parent = (jl_value_t*)l;
        l = jl_atomic_load_relaxed(&l->next);
    }

    jl_gc_write_atomic(newrec, newrec->next, jl_typemap_entry_t, l, relaxed);
    jl_gc_write_atomic(parent, *pml, jl_typemap_entry_t, newrec, release);
}
```
-/
def jlTypemapListInsert : List TypemapEntry → TypemapEntry → List TypemapEntry
  | [], newrec => [newrec]
  | l :: rest, newrec =>
    if (newrec.isleafsig || !l.isleafsig) && (newrec.issimplesig || !l.issimplesig) then
      newrec :: l :: rest
    else
      l :: jlTypemapListInsert rest newrec

mutual
/-- `jl_method_convert_list_to_cache`

Julia source: src/typemap.c:1563-1596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *jl_method_convert_list_to_cache(
        jl_typemap_t *map, jl_typemap_entry_t *ml, int8_t tparam, int8_t offs, int8_t doublesplit) JL_CANSAFEPOINT
{
    _Atomic(jl_genericmemory_t*) dblcache = (jl_genericmemory_t*)jl_an_empty_memory_any;
    jl_typemap_level_t *cache = doublesplit ? NULL : jl_new_typemap_level();
    jl_typemap_entry_t *next = NULL;
    JL_GC_PUSH4(&cache, &dblcache, &next, &ml);
    while (ml != (void*)jl_nothing) {
        next = jl_atomic_load_relaxed(&ml->next);
        jl_gc_write_atomic(ml, ml->next, jl_typemap_entry_t, (jl_typemap_entry_t*)jl_nothing, relaxed);
        // n.b. this is being done concurrently with lookups!
        // TODO: is it safe to be doing this concurrently with lookups?
        if (doublesplit) {
            jl_value_t *key = jl_unwrap_unionall((jl_value_t*)ml->sig);
            size_t len = jl_nparams(key);
            if (offs < len-1)
                key = jl_tparam(key, offs);
            else
                key = jl_tparam(key, len-1);
            if (jl_is_vararg(key))
                key = jl_unwrap_vararg(key);
            if (tparam) {
                assert(jl_is_some_Type(key));
                key = jl_some_Type_T(key);
            }
            jl_typemap_memory_insert_(map, &dblcache, key, ml, NULL, 0, offs, NULL);
        }
        else
            jl_typemap_level_insert_(map, cache, ml, offs);
        ml = next;
    }
    JL_GC_POP();
    return doublesplit ? (jl_value_t*)jl_atomic_load_relaxed(&dblcache) : (jl_value_t*)cache;
}
```
-/
def jlMethodConvertListToCache (n : Nat) (T : Types) (ops : GfOps) (ml : List TypemapEntry)
    (tparam : Bool) (offs : Nat) (doublesplit : Bool) : CM Typemap :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if doublesplit then
      let mut dblcache : List (MtKey × Typemap) := []
      for entry in ml do
        let key0 := entry.sig.unwrapUnionall
        let len := key0.nparams
        let key1 := if offs < len - 1 then key0.params[offs]! else key0.params[len - 1]!
        let key2 := if key1.isVararg then key1.unwrapVararg else key1
        let key3 := if tparam then key2.someTypeT else key2
        dblcache ← jlTypemapMemoryInsert n T ops dblcache (.val key3) entry false offs none
      return .memory dblcache
    else
      let mut cache := jlNewTypemapLevel
      for entry in ml do
        cache ← jlTypemapLevelInsert n T ops cache entry offs
      return cache

/-- `jl_typemap_insert_generic`

Julia source: src/typemap.c:1620-1651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void jl_typemap_insert_generic(
        jl_typemap_t *map, _Atomic(jl_value_t*) *pml, jl_value_t *parent,
        jl_typemap_entry_t *newrec, int8_t tparam, int8_t offs, jl_value_t *doublesplit) JL_CANSAFEPOINT
{
    jl_value_t *ml = jl_atomic_load_relaxed(pml);
    if (jl_is_genericmemory(ml)) {
        assert(doublesplit);
        jl_typemap_memory_insert_(map, (_Atomic(jl_genericmemory_t*)*)pml, doublesplit, newrec, parent, 0, offs, NULL);
        return;
    }

    if (jl_typeof(ml) == (jl_value_t*)jl_typemap_level_type) {
        assert(!doublesplit);
        jl_typemap_level_insert_(map, (jl_typemap_level_t*)ml, newrec, offs);
        return;
    }

    unsigned count = jl_typemap_list_count_locked((jl_typemap_entry_t*)ml);
    if (count > MAX_METHLIST_COUNT) {
        ml = jl_method_convert_list_to_cache(
            map, (jl_typemap_entry_t*)ml, tparam, offs, doublesplit != NULL);
        jl_gc_write_atomic(parent, *pml, jl_value_t, ml, release);
        if (doublesplit)
            jl_typemap_memory_insert_(map, (_Atomic(jl_genericmemory_t*)*)pml, doublesplit, newrec, parent, 0, offs, NULL);
        else
            jl_typemap_level_insert_(map, (jl_typemap_level_t*)ml, newrec, offs);
        return;
    }

    jl_typemap_list_insert_(map, (_Atomic(jl_typemap_entry_t*)*)pml,
        parent, newrec);
}
```
-/
def jlTypemapInsertGeneric (n : Nat) (T : Types) (ops : GfOps) (ml : Typemap)
    (newrec : TypemapEntry) (tparam : Bool) (offs : Nat) (doublesplit : Option Val) :
    CM Typemap :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match ml with
    | .memory pairs =>
      let some ds := doublesplit | throw "unreachable: memory without doublesplit"
      let pairs' ← jlTypemapMemoryInsert n T ops pairs (.val ds) newrec false offs none
      return .memory pairs'
    | .level .. =>
      jlTypemapLevelInsert n T ops ml newrec offs
    | .entries es =>
      let count := jlTypemapListCountLocked es
      if count > maxMethlistCount then
        let converted ← jlMethodConvertListToCache n T ops es tparam offs doublesplit.isSome
        match doublesplit, converted with
        | some ds, .memory pairs =>
          let pairs' ← jlTypemapMemoryInsert n T ops pairs (.val ds) newrec false offs none
          return .memory pairs'
        | none, _ =>
          jlTypemapLevelInsert n T ops converted newrec offs
        | _, _ => throw "unreachable: jlMethodConvertListToCache mismatch"
      else
        return .entries (jlTypemapListInsert es newrec)

/-- `jl_typemap_memory_insert_`

Julia source: src/typemap.c:1653-1663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void jl_typemap_memory_insert_(
        jl_typemap_t *map, _Atomic(jl_genericmemory_t*) *pcache, jl_value_t *key, jl_typemap_entry_t *newrec,
        jl_value_t *parent, int8_t tparam, int8_t offs, jl_value_t *doublesplit)
{
    jl_genericmemory_t *cache = jl_atomic_load_relaxed(pcache);
    _Atomic(jl_value_t*) *pml = mtcache_hash_lookup_bp(cache, key);
    if (pml == NULL)
        mtcache_hash_insert(pcache, parent, key, (jl_typemap_t*)newrec);
    else
        jl_typemap_insert_generic(map, pml, (jl_value_t*) cache, newrec, tparam, offs + (doublesplit ? 0 : 1), doublesplit);
}
```
-/
def jlTypemapMemoryInsert (n : Nat) (T : Types) (ops : GfOps) (cache : List (MtKey × Typemap))
    (key : MtKey) (newrec : TypemapEntry) (tparam : Bool) (offs : Nat)
    (doublesplit : Option Val) : CM (List (MtKey × Typemap)) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match ← mtcacheHashPeek n T cache key with
    | none =>
      return mtcacheHashInsert cache key (.entries [newrec])
    | some idx =>
      let (k, oldVal) := cache[idx]!
      let nextOffs := offs + (if doublesplit.isSome then 0 else 1)
      let newVal ← jlTypemapInsertGeneric n T ops oldVal newrec tparam nextOffs doublesplit
      return cache.set idx (k, newVal)

/-- `jl_typemap_level_insert_`

Julia source: src/typemap.c:1665-1738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void jl_typemap_level_insert_(
        jl_typemap_t *map, jl_typemap_level_t *cache, jl_typemap_entry_t *newrec, int8_t offs)
{
    jl_value_t *ttypes = jl_unwrap_unionall((jl_value_t*)newrec->sig);
    size_t l = jl_nparams(ttypes);
    // compute the type at offset `offs` into `sig`, which may be a Vararg
    jl_value_t *t1;
    int isva = 0;
    if (l <= offs + 1) {
        t1 = jl_tparam(ttypes, l - 1);
        if (jl_is_vararg(t1)) {
            isva = 1;
            t1 = jl_unwrap_vararg(t1);
        }
        else if (l <= offs) {
            t1 = NULL;
        }
    }
    else if (l > offs) {
        t1 = jl_tparam(ttypes, offs);
    }
    else {
        t1 = NULL;
    }
    // If the type at `offs` is Any, put it in the Any list
    if (t1 && jl_is_any(t1)) {
        jl_typemap_insert_generic(map, &cache->any, (jl_value_t*)cache, newrec, 0, offs+1, NULL);
        return;
    }
    // Don't put Varargs in the optimized caches (too hard to handle in lookup and bp)
    if (t1 && !isva) {
        // try to put in leaf type caches
        if (jl_is_some_Type(t1)) {
            // if the argument is Type{...}, this method has specializations for singleton kinds
            // and we use the table indexed for that purpose.
            jl_value_t *a0 = jl_some_Type_T(t1);
            if (is_cache_leaf(a0, 1)) {
                jl_typename_t *name = a0 == jl_bottom_type ? jl_typeofbottom_type->name : ((jl_datatype_t*)a0)->name;
                jl_typemap_memory_insert_(map, &cache->targ, (jl_value_t*)name, newrec, (jl_value_t*)cache, 1, offs, jl_is_datatype(name->wrapper) ? NULL : a0);
                return;
            }
        }
        if (is_cache_leaf(t1, 0)) {
            jl_typename_t *name = t1 == jl_bottom_type ? jl_typeofbottom_type->name : ((jl_datatype_t*)t1)->name;
            jl_typemap_memory_insert_(map, &cache->arg1, (jl_value_t*)name, newrec, (jl_value_t*)cache, 0, offs, jl_is_datatype(name->wrapper) ? NULL : t1);
            return;
        }

        // try to put in TypeName caches
        jl_value_t *a0;
        t1 = jl_unwrap_unionall(t1);
        if (jl_is_some_Type(t1)) {
            jl_value_t *tp0 = jl_some_Type_T(t1);
            a0 = jl_type_extract_name(tp0, 1);
            jl_datatype_t *super = a0 ? (jl_datatype_t*)jl_unwrap_unionall(((jl_typename_t*)a0)->wrapper) : jl_any_type;
            jl_typename_t *name = super->name;
            jl_typemap_memory_insert_(map, &cache->tname, (jl_value_t*)name, newrec, (jl_value_t*)cache, 1, offs, NULL);
            return;
        }
        if (jl_is_typeofbottom_param(t1)) {
            // A parameter that admits only `Union{}`, such as `T<:Type{Union{}}`,
            // ranks above every other in specificity, and must not get skipped by the filter
            // logic, even if the above code didn't notice it shares that specificity rule.
            jl_typemap_memory_insert_(map, &cache->tname, (jl_value_t*)jl_typeofbottom_type->name, newrec, (jl_value_t*)cache, 1, offs, NULL);
            return;
        }
        a0 = jl_type_extract_name(t1, 0);
        if (a0 && a0 != (jl_value_t*)jl_any_type->name) {
            jl_typemap_memory_insert_(map, &cache->name1, a0, newrec, (jl_value_t*)cache, 0, offs, NULL);
            return;
        }
    }
    jl_typemap_list_insert_(map, &cache->linear, (jl_value_t*)cache, newrec);
}
```
-/
def jlTypemapLevelInsert (n : Nat) (T : Types) (ops : GfOps) (cache : Typemap)
    (newrec : TypemapEntry) (offs : Nat) : CM Typemap :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let .level arg1 targ name1 tname linear any := cache
      | throw "jlTypemapLevelInsert: expected Typemap.level"
    let ttypes := newrec.sig.unwrapUnionall
    let l := ttypes.nparams
    let mut t1? : Option Val := none
    let mut isva := false
    if l ≤ offs + 1 then
      if l > 0 then
        let last := ttypes.params[l - 1]!
        if last.isVararg then
          isva := true
          t1? := some last.unwrapVararg
        else if l ≤ offs then
          t1? := none
        else
          t1? := some last
    else if l > offs then
      t1? := some ttypes.params[offs]!
    -- If the type at `offs` is Any, put it in the Any list
    if let some t1 := t1? then
      if ← jlIsAny n t1 then
        let any' ← jlTypemapInsertGeneric n T ops any newrec false (offs + 1) none
        return .level arg1 targ name1 tname linear any'
    -- Don't put Varargs in the optimized caches (too hard to handle in lookup and bp)
    if let some t1 := t1? then
      if !isva then
        -- try to put in leaf type caches
        if t1.isSomeType then
          let a0 := t1.someTypeT
          if ← isCacheLeaf T a0 true then
            let name := if a0 == .bottom then "Core.TypeofBottom" else a0.name?.getD ""
            let tn ← typenameOf T name
            let ds := if tn.wrapper.isDatatype then none else some a0
            let targ' ← jlTypemapMemoryInsert n T ops targ (.typename name) newrec true offs ds
            return .level arg1 targ' name1 tname linear any
        if ← isCacheLeaf T t1 false then
          let name := if t1 == .bottom then "Core.TypeofBottom" else t1.name?.getD ""
          let tn ← typenameOf T name
          let ds := if tn.wrapper.isDatatype then none else some t1
          let arg1' ← jlTypemapMemoryInsert n T ops arg1 (.typename name) newrec false offs ds
          return .level arg1' targ name1 tname linear any
        -- try to put in TypeName caches
        let t1u := t1.unwrapUnionall
        if t1u.isSomeType then
          let tp0 := t1u.someTypeT
          let a0? ← jlTypeExtractName n ops tp0 true
          let name := a0?.getD "Core.Any"
          let tname' ← jlTypemapMemoryInsert n T ops tname (.typename name) newrec true offs none
          return .level arg1 targ name1 tname' linear any
        if ← ops.isTypeofbottomParam t1u then
          let tname' ← jlTypemapMemoryInsert n T ops tname (.typename "Core.TypeofBottom") newrec true offs none
          return .level arg1 targ name1 tname' linear any
        let a0? ← jlTypeExtractName n ops t1u false
        if let some a0 := a0? then
          if a0 != "Core.Any" then
            let name1' ← jlTypemapMemoryInsert n T ops name1 (.typename a0) newrec false offs none
            return .level arg1 targ name1' tname linear any
    let linear' := jlTypemapListInsert linear newrec
    return .level arg1 targ name1 tname linear' any
end

/-- `jl_typemap_alloc`

Julia source: src/typemap.c:1740-1784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_typemap_entry_t *jl_typemap_alloc(
        jl_tupletype_t *type, jl_tupletype_t *simpletype, jl_svec_t *guardsigs,
        jl_value_t *newvalue, size_t min_world, size_t max_world)
{
    jl_task_t *ct = jl_current_task;
    assert(min_world > 0 && max_world > 0);
    if (!simpletype)
        simpletype = (jl_tupletype_t*)jl_nothing;
    jl_value_t *ttype = jl_unwrap_unionall((jl_value_t*)type);
    assert(jl_is_tuple_type(ttype));
    // compute the complexity of this type signature
    int isva = jl_is_va_tuple((jl_datatype_t*)ttype);
    int issimplesig = !jl_is_unionall(type); // a TypeVar environment needs a complex matching test
    int isleafsig = issimplesig && !isva; // entirely leaf types don't need to be sorted
    size_t i, l;
    for (i = 0, l = jl_nparams(ttype); i < l && issimplesig; i++) {
        jl_value_t *decl = jl_tparam(ttype, i);
        if (jl_is_kind(decl) || decl == (jl_value_t*)jl_anytype_type)
            isleafsig = 0; // Type{} may have a higher priority than a kind; both are
                           // still simple for sig_match_simple
        else if (jl_is_some_Type(decl))
            isleafsig = 0; // Type{}/TypeEgal{} may need special processing to compute the match
        else if (jl_is_vararg(decl))
            isleafsig = 0; // makes iteration easier when the endpoints are the same
        else if (decl == (jl_value_t*)jl_any_type)
            isleafsig = 0; // Any needs to go in the general cache
        else if (!jl_is_concrete_type(decl)) // anything else needs to go through the general subtyping test
            isleafsig = issimplesig = 0;
    }

    jl_typemap_entry_t *newrec =
        (jl_typemap_entry_t*)jl_gc_alloc(ct->ptls, sizeof(jl_typemap_entry_t),
                                         jl_typemap_entry_type);
    newrec->sig = type;
    newrec->simplesig = simpletype;
    newrec->func.value = newvalue;
    newrec->guardsigs = guardsigs;
    jl_atomic_store_relaxed(&newrec->next, (jl_typemap_entry_t*)jl_nothing);
    jl_atomic_store_relaxed(&newrec->min_world, min_world);
    jl_atomic_store_relaxed(&newrec->max_world, max_world);
    newrec->va = isva;
    newrec->issimplesig = issimplesig;
    newrec->isleafsig = isleafsig;
    return newrec;
}
```
-/
def jlTypemapAlloc (T : Types) (type : Val) (simpletype : Option Val) (guardsigs : List Val)
    (newvalue : Nat) (minWorld maxWorld : Nat) : CM TypemapEntry := do
  let T := withBuiltinTypes T
  let ttype := type.unwrapUnionall
  let isva := ttype.isVaTuple
  let mut issimplesig := !type.isUnionall
  let mut isleafsig := issimplesig && !isva
  for decl in ttype.params do
    if !issimplesig then break
    if isKind decl || decl == anytypeType then
      isleafsig := false
    else if decl.isSomeType then
      isleafsig := false
    else if decl.isVararg then
      isleafsig := false
    else if decl == anyType then
      isleafsig := false
    else if !(← isConcreteType T decl) then
      isleafsig := false
      issimplesig := false
  return {
    sig := type
    simplesig := simpletype
    guardsigs := guardsigs
    func := newvalue
    minWorld := minWorld
    maxWorld := maxWorld
    va := isva
    issimplesig := issimplesig
    isleafsig := isleafsig
  }

/-- `jl_typemap_insert`

Julia source: src/typemap.c:1786-1791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void jl_typemap_insert(_Atomic(jl_typemap_t *) *pcache, jl_value_t *parent,
        jl_typemap_entry_t *newrec, int8_t offs)
{
    jl_typemap_t *cache = jl_atomic_load_relaxed(pcache);
    jl_typemap_insert_generic(cache, pcache, parent, newrec, 0, offs, NULL);
}
```
-/
def jlTypemapInsert (n : Nat) (T : Types) (ops : GfOps) (cache : Typemap) (newrec : TypemapEntry)
    (offs : Nat) : CM Typemap :=
  jlTypemapInsertGeneric n T ops cache newrec false offs none

end JuliaLean.C
