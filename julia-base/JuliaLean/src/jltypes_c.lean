import JuliaLean.src.julia_h

/-!
Type properties and constructors used by subtyping (`src/jltypes.c`).
-/

namespace JuliaLean.C

/-- A `jl_typeenv_t` entry: a type variable and the value it is bound to (`NULL` = unbound). -/
structure TypeEnvEntry where
  var : Nat
  val : Option Val
  deriving Repr, BEq, Inhabited

/-- `jl_typeenv_t`, innermost binding first. -/
abbrev TypeEnv := List TypeEnvEntry

/--
Julia source: src/jltypes.c:38-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeenv_has(jl_typeenv_t *env, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    while (env != NULL) {
        if (env->var == v)
            return 1;
        env = env->prev;
    }
    return 0;
}
```
-/
def typeenvHas (env : TypeEnv) (v : Nat) : Bool :=
  env.any (·.var == v)

/--
Julia source: src/jltypes.c:48-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeenv_has_ne(jl_typeenv_t *env, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    while (env != NULL) {
        if (env->var == v)
            return env->val != (jl_value_t*)v; // consider it actually not present if it is bound to itself unchanging
        env = env->prev;
    }
    return 0;
}
```
-/
def typeenvHasNe (env : TypeEnv) (v : Val) : Bool :=
  match v.tvId with
  | none => false
  | some id =>
    match env.find? (·.var == id) with
    | some e => e.val != some v
    | none => false

mutual
/--
Julia source: src/jltypes.c:126-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_free_typevars(jl_value_t *v, jl_typeenv_t *env) JL_NOTSAFEPOINT
{
    while (1) {
        if (jl_is_datatype(v) && (env == NULL || !((jl_datatype_t*)v)->hasfreetypevars))
            return ((jl_datatype_t*)v)->hasfreetypevars;
        if (jl_is_typevar(v)) {
            return !typeenv_has(env, (jl_tvar_t*)v);
        }
        if (jl_is_typeapp(v))
            return 1;
        while (jl_is_unionall(v)) {
            jl_unionall_t *ua = (jl_unionall_t*)v;
            if (ua->var->lb != jl_bottom_type && has_free_typevars(ua->var->lb, env))
                return 1;
            if (ua->var->ub != (jl_value_t*)jl_any_type && has_free_typevars(ua->var->ub, env))
                return 1;
            jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
            newenv->var = ua->var;
            newenv->val = NULL;
            newenv->prev = env;
            env = newenv;
            v = ua->body;
        }
        // After unwrapping UnionAll, body might be TypeApp or TypeVar;
        // restart the loop so those checks at the top fire.
        if (jl_is_typeapp(v) || jl_is_typevar(v))
            continue;
        if (jl_is_datatype(v)) {
            int expect = ((jl_datatype_t*)v)->hasfreetypevars;
            if (expect == 0 || env == NULL)
                return expect;
            size_t i;
            for (i = 0; i < jl_nparams(v); i++) {
                if (has_free_typevars(jl_tparam(v, i), env))
                    return 1;
            }
            return 0;
        }
        else if (jl_is_uniontype(v) || jl_is_intersecttype(v)) {
            if (has_free_typevars(((jl_uniontype_t*)v)->a, env))
                return 1;
           v = ((jl_uniontype_t*)v)->b;
        }
        else if (jl_is_some_Type(v)) {
            v = jl_some_Type_T(v);
        }
        else if (jl_is_vararg(v)) {
            jl_vararg_t *vm = (jl_vararg_t*)v;
            if (!vm->T)
                return 0;
            if (vm->N) {
                if (has_free_typevars(vm->N, env))
                    return 1;
            }
            v = vm->T;
        }
        else {
            return 0;
        }
    }
}
```
-/
def hasFreeTypevars (v : Val) (env : TypeEnv) : Bool :=
  match v with
  | .datatype _ ps =>
    -- `hasfreetypevars` is computed from the parameters when the DataType is constructed.
    let expect := hasFreeTypevarsList ps []
    if env.isEmpty || !expect then expect else hasFreeTypevarsList ps env
  | .typevar id _ _ _ => !typeenvHas env id
  | .typeapp .. => true
  | .unionall id _ lb ub body =>
    if lb != .bottom && hasFreeTypevars lb env then true
    else if ub != anyType && hasFreeTypevars ub env then true
    else hasFreeTypevars body ({ var := id, val := none } :: env)
  | .union a b | .intersect a b => hasFreeTypevars a env || hasFreeTypevars b env
  | .typeeq T | .typeegal T => hasFreeTypevars T env
  | .vararg none _ => false
  | .vararg (some T) N =>
    (match N with | some n => hasFreeTypevars n env | none => false) || hasFreeTypevars T env
  | _ => false

def hasFreeTypevarsList (ps : List Val) (env : TypeEnv) : Bool :=
  match ps with
  | [] => false
  | p :: rest => hasFreeTypevars p env || hasFreeTypevarsList rest env
end

/-- `jl_has_free_typevars`

Julia source: src/jltypes.c:188-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_has_free_typevars(jl_value_t *v) JL_NOTSAFEPOINT
{
    return has_free_typevars(v, NULL);
}
```
-/
def Val.hasFreeTypevars (v : Val) : Bool := JuliaLean.C.hasFreeTypevars v []

/-- `((jl_datatype_t*)v)->hasfreetypevars`, set when the DataType is constructed. -/
def Val.dtHasFreeTypevars (v : Val) : Bool := hasFreeTypevarsList v.params []

mutual
/--
Julia source: src/jltypes.c:270-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// test whether a type has vars bound by the given environment
int jl_has_bound_typevars(jl_value_t *v, jl_typeenv_t *env) JL_NOTSAFEPOINT
{
    while (1) {
        if (jl_is_datatype(v) && !((jl_datatype_t*)v)->hasfreetypevars)
            return 0;
        if (jl_is_typevar(v)) {
            return typeenv_has_ne(env, (jl_tvar_t*)v);
        }
        if (jl_is_typeapp(v)) {
            jl_typeapp_t *ta = (jl_typeapp_t*)v;
            if (jl_has_bound_typevars(ta->head, env))
                return 1;
            v = ta->param;
            continue;
        }
        while (jl_is_unionall(v)) {
            jl_unionall_t *ua = (jl_unionall_t*)v;
            if (ua->var->lb != jl_bottom_type && jl_has_bound_typevars(ua->var->lb, env))
                return 1;
            if (ua->var->ub != (jl_value_t*)jl_any_type && jl_has_bound_typevars(ua->var->ub, env))
                return 1;
            // Temporarily remove this var from env if necessary
            // Note that te might be bound more than once in the env, so
            // we remove it by setting it to itself in a new env.
            if (typeenv_has_ne(env, ua->var)) {
                jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
                newenv->var = ua->var;
                newenv->val = (jl_value_t*)ua->var;
                newenv->prev = env;
                env = newenv;
            }
            v = ua->body;
        }
        // After unwrapping UnionAll, body might be TypeApp or TypeVar;
        // restart the loop so those checks at the top fire.
        if (jl_is_typeapp(v) || jl_is_typevar(v))
            continue;
        if (jl_is_datatype(v)) {
            if (!((jl_datatype_t*)v)->hasfreetypevars)
                return 0;
            size_t i;
            for (i = 0; i < jl_nparams(v); i++) {
                if (jl_has_bound_typevars(jl_tparam(v, i), env))
                    return 1;
            }
            return 0;
        }
        else if (jl_is_uniontype(v) || jl_is_intersecttype(v)) {
            if (jl_has_bound_typevars(((jl_uniontype_t*)v)->a, env))
                return 1;
           v = ((jl_uniontype_t*)v)->b;
        }
        else if (jl_is_some_Type(v)) {
            v = jl_some_Type_T(v);
        }
        else if (jl_is_vararg(v)) {
            jl_vararg_t *vm = (jl_vararg_t *)v;
            if (!vm->T)
                return 0;
            if (vm->N) {
                if (jl_has_bound_typevars(vm->N, env))
                    return 1;
            }
            v = vm->T;
        }
        else {
            return 0;
        }
    }
}
```
-/
def hasBoundTypevars (v : Val) (env : TypeEnv) : Bool :=
  match v with
  | .datatype _ ps => if !hasFreeTypevarsList ps [] then false else hasBoundTypevarsList ps env
  | .typevar .. => typeenvHasNe env v
  | .typeapp head param => hasBoundTypevars head env || hasBoundTypevars param env
  | .unionall id n lb ub body =>
    if lb != .bottom && hasBoundTypevars lb env then true
    else if ub != anyType && hasBoundTypevars ub env then true
    else
      let var := Val.typevar id n lb ub
      -- Temporarily remove this var from env: bind it to itself in a new entry.
      let env := if typeenvHasNe env var then { var := id, val := some var } :: env else env
      hasBoundTypevars body env
  | .union a b | .intersect a b => hasBoundTypevars a env || hasBoundTypevars b env
  | .typeeq T | .typeegal T => hasBoundTypevars T env
  | .vararg none _ => false
  | .vararg (some T) N =>
    (match N with | some n => hasBoundTypevars n env | none => false) || hasBoundTypevars T env
  | _ => false

def hasBoundTypevarsList (ps : List Val) (env : TypeEnv) : Bool :=
  match ps with
  | [] => false
  | p :: rest => hasBoundTypevars p env || hasBoundTypevarsList rest env
end

/-- `jl_has_typevar(t, v)`

Julia source: src/jltypes.c:342-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_has_typevar(jl_value_t *t, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    jl_typeenv_t env = { v, NULL, NULL };
    return jl_has_bound_typevars(t, &env);
}
```
-/
def Val.hasTypevar (t v : Val) : Bool :=
  match v.tvId with
  | some id => hasBoundTypevars t [{ var := id, val := none }]
  | none => false


/-! ## DataType properties fixed at construction -/

mutual
/-- `dt->isconcretetype`, as `jl_precompute_memoized_dt` computes it; `jl_is_concrete_type`.

Julia source: src/jltypes.c:2090-2137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void jl_precompute_memoized_dt(jl_datatype_t *dt, int cacheable)
{
    int istuple = (dt->name == jl_tuple_typename);
    dt->hasfreetypevars = 0;
    dt->maybe_subtype_of_cache = 1;
    dt->isconcretetype = !dt->name->abstract;
    dt->isdispatchtuple = istuple;
    size_t i, l = jl_nparams(dt);
    for (i = 0; i < l; i++) {
        jl_value_t *p = jl_tparam(dt, i);
        if (!dt->hasfreetypevars) {
            dt->hasfreetypevars = jl_has_free_typevars(p);
            if (dt->hasfreetypevars)
                dt->isconcretetype = 0;
        }
        if (istuple) {
            if (dt->isconcretetype)
                dt->isconcretetype = (jl_is_datatype(p) && ((jl_datatype_t*)p)->isconcretetype) ||
                    p == jl_bottom_type;
            if (dt->isdispatchtuple) {
                // a type-valued slot is a dispatch slot only in the egality form
                // `TypeEgal{T}` that `jl_inst_arg_tuple_type` produces; an equality
                // `Type{T}` slot also admits `==`-equal but non-egal arguments --
                // except `Type{Union{}}`, whose sole instance is the unique bottom
                // object (and which aliases the dispatch slot `typeof(Union{})`)
                dt->isdispatchtuple =
                    (jl_is_datatype(p) && ((!jl_is_kind(p) && ((jl_datatype_t*)p)->isconcretetype) ||
                     (p == (jl_value_t*)jl_typeofbottom_type))) ||
                    jl_is_typeegal(p) ||
                    (jl_is_typeeq(p) && jl_typeeq_T(p) == jl_bottom_type);
            }
        }
        if (jl_is_vararg(p))
            p = ((jl_vararg_t*)p)->T;
        if (istuple && dt->has_concrete_subtype) {
            // tuple types like Tuple{:x} and Tuple{Union{}} cannot have instances
            if (p && !jl_is_type(p) && !jl_is_typevar(p))
                dt->has_concrete_subtype = 0;
            if (p == jl_bottom_type)
                dt->has_concrete_subtype = 0;
        }
        if (dt->maybe_subtype_of_cache) {
            dt->maybe_subtype_of_cache = !p || maybe_subtype_of_cache(p, istuple) || !jl_has_free_typevars(p);
        }
    }
    assert(dt->isconcretetype || dt->isdispatchtuple ? dt->maybe_subtype_of_cache : 1);
    dt->hash = typekey_hash(dt->name, jl_svec_data(dt->parameters), l, cacheable);
}
```
-/
def isConcreteType (T : Types) : Val → CM Bool
  | .datatype name ps => do
    let tn ← T.typename name
    if tn.abstract || hasFreeTypevarsList ps [] then return false
    if name != tupleName then return true
    allConcreteOrBottom T ps
  | _ => pure false

def allConcreteOrBottom (T : Types) : List Val → CM Bool
  | [] => pure true
  | p :: ps => do
    let ok ← if p == .bottom then pure true else isConcreteType T p
    if ok then allConcreteOrBottom T ps else pure false
end

/-- `jl_is_tuple_type` -/
def Val.isTupleType (v : Val) : Bool := v.name? == some tupleName

/-- `jl_is_abstracttype` -/
def isAbstractType (T : Types) (v : Val) : CM Bool :=
  match v with
  | .datatype name _ => return (← T.typename name).abstract
  | _ => pure false

/-! ## Egality (`===`) of type objects (`src/builtins.c`) -/

mutual
/-- `egal_types(a, b, env, tvar_names)`; `env` maps a variable of `a` (by id) to the
corresponding variable object of `b`.

Julia source: src/builtins.c:195-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int egal_types(const jl_value_t *a, const jl_value_t *b, jl_typeenv_t *env, int tvar_names) JL_NOTSAFEPOINT
{
    if (a == b)
        return 1;
    uintptr_t dtag = jl_typetagof(a);
    if (dtag != jl_typetagof(b))
        return 0;
    if (dtag == jl_datatype_tag << 4) {
        jl_datatype_t *dta = (jl_datatype_t*)a;
        jl_datatype_t *dtb = (jl_datatype_t*)b;
        if (dta->name != dtb->name)
            return 0;
        size_t i, l = jl_nparams(dta);
        if (jl_nparams(dtb) != l)
            return 0;
        for (i = 0; i < l; i++) {
            if (!egal_types(jl_tparam(dta, i), jl_tparam(dtb, i), env, tvar_names))
                return 0;
        }
        return 1;
    }
    if (dtag == jl_tvar_tag << 4) {
        jl_typeenv_t *pe = env;
        while (pe != NULL) {
            if (pe->var == (jl_tvar_t*)a)
                return pe->val == b;
            pe = pe->prev;
        }
        return 0;
    }
    if (dtag == jl_unionall_tag << 4) {
        jl_unionall_t *ua = (jl_unionall_t*)a;
        jl_unionall_t *ub = (jl_unionall_t*)b;
        if (tvar_names && ua->var->name != ub->var->name)
            return 0;
        if (!(egal_types(ua->var->lb, ub->var->lb, env, tvar_names) && egal_types(ua->var->ub, ub->var->ub, env, tvar_names)))
            return 0;
        jl_typeenv_t e = { ua->var, (jl_value_t*)ub->var, env };
        return egal_types(ua->body, ub->body, &e, tvar_names);
    }
    if (dtag == jl_uniontype_tag << 4) {
        return egal_types(((jl_uniontype_t*)a)->a, ((jl_uniontype_t*)b)->a, env, tvar_names) &&
            egal_types(((jl_uniontype_t*)a)->b, ((jl_uniontype_t*)b)->b, env, tvar_names);
    }
    if (dtag == jl_typeegal_tag << 4) {
        // `TypeEgal` parameters are egality keys: alpha-renamed parameters are
        // `==` but not `===`, so their `TypeEgal`s are distinct types. The
        // name-insensitive mode (tvar_names==0) must therefore still compare
        // the parameter by name.
        return egal_types(((jl_typeeq_t*)a)->T, ((jl_typeeq_t*)b)->T, env, 1);
    }
    if (dtag == jl_typeeq_tag << 4)
        return egal_types(((jl_typeeq_t*)a)->T, ((jl_typeeq_t*)b)->T, env, tvar_names);
    if (dtag == jl_vararg_tag << 4) {
        jl_vararg_t *vma = (jl_vararg_t*)a;
        jl_vararg_t *vmb = (jl_vararg_t*)b;
        jl_value_t *vmaT = vma->T ? vma->T : (jl_value_t*)jl_any_type;
        jl_value_t *vmbT = vmb->T ? vmb->T : (jl_value_t*)jl_any_type;
        if (!egal_types(vmaT, vmbT, env, tvar_names))
            return 0;
        if (vma->N && vmb->N)
            return egal_types(vma->N, vmb->N, env, tvar_names);
        return !vma->N && !vmb->N;
    }
    assert(dtag == jl_symbol_tag << 4 || dtag == jl_module_tag << 4 || !((jl_datatype_t*)jl_typeof(a))->name->mutabl);
    return jl_egal__bitstag(a, b, dtag);
}
```
-/
def egalTypes (n : Nat) (T : Types) (a b : Val) (env : List (Nat × Val)) (names : Bool) :
    CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == b then pure true else
    match a, b with
    | .datatype na pa, .datatype nb pb =>
      if na != nb || pa.length != pb.length then pure false
      else (pa.zip pb).allM fun (x, y) => egalTypes n T x y env names
    | .typevar id _ _ _, _ =>
      pure (match env.lookup id with | some v => v == b | none => false)
    | .unionall ida na lba uba ba, .unionall idb nb lbb ubb bb => do
      if names && na != nb then return false
      if !(← egalTypes n T lba lbb env names) then return false
      if !(← egalTypes n T uba ubb env names) then return false
      egalTypes n T ba bb ((ida, .typevar idb nb lbb ubb) :: env) names
    | .union a1 a2, .union b1 b2 => do
      if !(← egalTypes n T a1 b1 env names) then return false
      egalTypes n T a2 b2 env names
    -- `TypeEgal` parameters are egality keys, compared by name even in the name-insensitive mode.
    | .typeegal x, .typeegal y => egalTypes n T x y env true
    | .typeeq x, .typeeq y => egalTypes n T x y env names
    | .vararg ta na, .vararg tb nb => do
      if !(← egalTypes n T (ta.getD anyType) (tb.getD anyType) env names) then return false
      match na, nb with
      | some x, some y => egalTypes n T x y env names
      | none, none => pure true
      | _, _ => pure false
    -- `jl_egal__bitstag` for the remaining tags; `Intersect` and `TypeApp` compare their fields.
    | .intersect a1 a2, .intersect b1 b2 | .typeapp a1 a2, .typeapp b1 b2 => do
      if !(← egal n T a1 b1) then return false
      egal n T a2 b2
    | _, _ => pure false

/-- `jl_egal` on type objects and type parameters.

Julia source: src/julia.h:2083-2102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
STATIC_INLINE int jl_egal__unboxed_(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED, uintptr_t dtag) JL_NOTSAFEPOINT
{
    if (dtag < jl_max_tags << 4) {
        if (dtag == jl_symbol_tag << 4 || dtag == jl_bool_tag << 4 || dtag == jl_nothing_tag << 4)
            return 0;
    }
    else if (((jl_datatype_t*)dtag)->name->mutabl)
        return 0;
    return jl_egal__bitstag(a, b, dtag);
}

STATIC_INLINE int jl_egal_(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED) JL_NOTSAFEPOINT
{
    if (a == b)
        return 1;
    uintptr_t dtag = jl_typetagof(a);
    if (dtag != jl_typetagof(b))
        return 0;
    return jl_egal__unboxed_(a, b, dtag);
}
```

Julia source: src/builtins.c:283-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_egal__bitstag(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED, uintptr_t dtag) JL_NOTSAFEPOINT
{
    if (dtag < jl_max_tags << 4) {
        switch ((enum jl_small_typeof_tags)(dtag >> 4)) {
        case jl_int8_tag:
        case jl_uint8_tag:
        case jl_addrspacecore_tag:
            return *(uint8_t*)a == *(uint8_t*)b;
        case jl_int16_tag:
        case jl_uint16_tag:
            return *(uint16_t*)a == *(uint16_t*)b;
        case jl_int32_tag:
        case jl_uint32_tag:
        case jl_char_tag:
        case jl_intrinsic_tag:
            return *(uint32_t*)a == *(uint32_t*)b;
        case jl_int64_tag:
        case jl_uint64_tag:
            return *(uint64_t*)a == *(uint64_t*)b;
        case jl_ssavalue_tag:
        case jl_slotnumber_tag:
        case jl_argument_tag:
            return *(size_t*)a == *(size_t*)b;
        case jl_gotoifnot_tag:
            return compare_fields(a, b, jl_gotoifnot_type);
        case jl_returnnode_tag:
            return compare_fields(a, b, jl_returnnode_type);
        case jl_enternode_tag:
            return compare_fields(a, b, jl_enternode_type);
        case jl_pinode_tag:
            return compare_fields(a, b, jl_pinode_type);
        case jl_phinode_tag:
            return compare_fields(a, b, jl_phinode_type);
        case jl_phicnode_tag:
            return compare_fields(a, b, jl_phicnode_type);
        case jl_upsilonnode_tag:
            return compare_fields(a, b, jl_upsilonnode_type);
        case jl_globalref_tag:
            return compare_fields(a, b, jl_globalref_type);
        case jl_gotonode_tag:
            return *(size_t*)a == *(size_t*)b;
        case jl_quotenode_tag:
            return compare_fields(a, b, jl_quotenode_type);
        case jl_unionall_tag:
            return egal_types(a, b, NULL, 1);
        case jl_uniontype_tag:
            return compare_fields(a, b, jl_uniontype_type);
        case jl_typeeq_tag:
        case jl_typeegal_tag:
            return egal_types(a, b, NULL, 1);
        case jl_vararg_tag:
            return compare_fields(a, b, jl_vararg_type);
        case jl_task_tag:
        case jl_tvar_tag:
        case jl_symbol_tag:
        case jl_module_tag:
        case jl_bool_tag:
        case jl_nothing_tag:
        case jl_cancel_source_tag: // mutable: identity (a == b checked above)
        case jl_wait_entry_tag:    // mutable: identity (a == b checked above)
            return 0;
        case jl_simplevector_tag:
            return compare_svec((jl_svec_t*)a, (jl_svec_t*)b);
        case jl_string_tag: {
                size_t l = jl_string_len(a);
                if (jl_string_len(b) != l)
                    return 0;
                return !memcmp(jl_string_data(a), jl_string_data(b), l);
            }
        case jl_datatype_tag: {
                jl_datatype_t *dta = (jl_datatype_t*)a;
                jl_datatype_t *dtb = (jl_datatype_t*)b;
                if (dta->name != dtb->name)
                    return 0;
                if (dta->name != jl_tuple_typename && (dta->isconcretetype || dtb->isconcretetype))
                    return 0;
                return compare_svec(dta->parameters, dtb->parameters);
            }
#ifndef NDEBUG
        default:
#endif
        case jl_max_tags:
        case jl_null_tag:
        case jl_typeofbottom_tag:
        case jl_tags_count:
            abort();
        }
    }
    return jl_egal__bits(a, b, (jl_datatype_t*)dtag);
}
```

Julia source: src/builtins.c:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int NOINLINE compare_svec(jl_svec_t *a, jl_svec_t *b) JL_NOTSAFEPOINT
{
    size_t i, l = jl_svec_len(a);
    if (l != jl_svec_len(b))
        return 0;
    for (i = 0; i < l; i++) {
        if (!jl_egal(jl_svecref(a, i), jl_svecref(b, i)))
            return 0;
    }
    return 1;
}
```
-/
def egal (n : Nat) (T : Types) (a b : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == b then pure true else
    if typeOf a != typeOf b then pure false else
    match a, b with
    | .unionall .., _ | .typeeq _, _ | .typeegal _, _ => egalTypes n T a b [] true
    | .union a1 a2, .union b1 b2 | .intersect a1 a2, .intersect b1 b2
    | .typeapp a1 a2, .typeapp b1 b2 => do
      if !(← egal n T a1 b1) then return false
      egal n T a2 b2
    | .vararg ta na, .vararg tb nb => do
      if !(← egalField n T ta tb) then return false
      egalField n T na nb
    | .datatype na pa, .datatype nb pb => do
      if na != nb then return false
      if na != tupleName && ((← isConcreteType T a) || (← isConcreteType T b)) then return false
      if pa.length != pb.length then return false
      (pa.zip pb).allM fun (x, y) => egal n T x y
    | _, _ => pure false

/-- One pointer field of `compare_fields`: equal pointers, or both set and `jl_egal`. -/
def egalField (n : Nat) (T : Types) : Option Val → Option Val → CM Bool
  | none, none => pure true
  | some x, some y => if x == y then pure true else egal n T x y
  | _, _ => pure false
end

/-- `jl_types_struct_equiv`

Julia source: src/builtins.c:263-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_types_struct_equiv(jl_value_t *a, jl_value_t *b)
{
    return egal_types(a, b, NULL, 0);
}
```
-/
def typesStructEquiv (n : Nat) (T : Types) (a b : Val) : CM Bool := egalTypes n T a b [] false

/-- `jl_compute_field_offsets` and `jl_is_datatype_make_singleton`, restricted to
the three properties in `Layout`. A concrete Tuple's fields are its parameters;
all other concrete types require recorded layout properties.

Julia source: src/datatype.c:645-887 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void jl_compute_field_offsets(jl_datatype_t *st)
{
    const uint64_t max_offset = (((uint64_t)1) << 32) - 1;
    const uint64_t max_size = max_offset >> 1;

    if (st->name->wrapper == NULL)
        return; // we got called too early--we'll be back
    jl_datatype_t *w = (jl_datatype_t*)jl_unwrap_unionall(st->name->wrapper);
    if (st == w && st->layout) {
        // this check allows us to force re-computation of the layout for some types during init
        st->layout = NULL;
        st->zeroinit = 0;
        st->has_concrete_subtype = 1;
    }
    if (st->name == jl_genericmemory_typename) {
        jl_get_genericmemory_layout(st);
        return;
    }
    int isbitstype = st->isconcretetype && st->name->mayinlinealloc;
    int ismutationfree = !w->layout || !jl_is_layout_opaque(w->layout);
    int isidentityfree = !st->name->mutabl;
    // If layout doesn't depend on type parameters, it's stored in st->name->wrapper
    // and reused by all subtypes.
    if (w->layout) {
        st->layout = w->layout;
        st->zeroinit = w->zeroinit;
        st->has_concrete_subtype = w->has_concrete_subtype;
        if (!jl_is_layout_opaque(st->layout)) { // e.g. jl_simplevector_type
            st->isbitstype = isbitstype && st->layout->npointers == 0;
            jl_maybe_allocate_singleton_instance(st);
        }
        return;
    }
    assert(st->types && w->types);
    size_t i, nfields = jl_svec_len(st->types);
    assert(st->name->n_uninitialized <= nfields);
    if (nfields == 0) {
        // if we have no fields, we can trivially skip the rest
        if (st == jl_symbol_type || st == jl_string_type) {
            // opaque layout - heap-allocated blob
            static const jl_datatype_layout_t opaque_byte_layout = {0, 0, 1, -1, 1, { .isbitsegal=1 }};
            st->layout = &opaque_byte_layout;
            return;
        }
        else if (st == jl_simplevector_type || st == jl_module_type) {
            static const jl_datatype_layout_t opaque_ptr_layout = {0, 0, 1, -1, sizeof(void*), { .isbitsegal=1 }};
            st->layout = &opaque_ptr_layout;
            return;
        }
        else {
            static const jl_datatype_layout_t singleton_layout = {0, 0, 0, -1, 1, { .isbitsegal=1 }};
            st->layout = &singleton_layout;
        }
    }
    else {
        // compute a conservative estimate of whether there could exist an instance of a subtype of this
        for (i = 0; st->has_concrete_subtype && i < nfields - st->name->n_uninitialized; i++) {
            jl_value_t *fld = jl_svecref(st->types, i);
            if (fld == jl_bottom_type)
                st->has_concrete_subtype = 0;
            else
                st->has_concrete_subtype = !jl_is_datatype(fld) || ((jl_datatype_t *)fld)->has_concrete_subtype;
        }
        // compute layout for the wrapper object if the field types have no free variables
        // During typegroup resolution, isconcretetype may be temporarily 0, but we should
        // still compute the layout if the type doesn't actually have free type vars.
        // jl_has_fixed_layout may return 0 due to conservative checks on Tuple fields.
        if (!st->isconcretetype && !jl_has_fixed_layout(st) && jl_has_free_typevars((jl_value_t*)st)) {
            assert(st == w); // otherwise caller should not have requested this layout
            return;
        }
    }

    for (i = 0; (isbitstype || isidentityfree || ismutationfree) && i < nfields; i++) {
        jl_value_t *fld = jl_field_type(st, i);
        if (isbitstype && jl_is_datatype(fld) && ((jl_datatype_t*)fld)->layout == NULL &&
            ((jl_datatype_t*)fld)->name->mayinlinealloc) {
            // The field's layout (and thus its isbitstype flag) may not have
            // been computed yet, e.g. for instantiations deferred during
            // typegroup resolution; compute it now so the flag is accurate.
            // The mayinlinealloc check breaks self-reference cycles: a type
            // whose layout recursion reaches itself is boxed and never isbits.
            jl_struct_try_layout((jl_datatype_t*)fld);
        }
        isbitstype &= jl_isbits(fld);
        ismutationfree &= (!st->name->mutabl || jl_field_isconst(st, i)) && is_type_mutationfree(fld);
        isidentityfree &= is_type_identityfree(fld);
    }

    // if we didn't reuse the layout above, compute it now
    if (st->layout == NULL) {
        size_t descsz = nfields * sizeof(jl_fielddesc32_t);
        jl_fielddesc32_t *desc;
        uint32_t *pointers;
        int should_malloc = descsz >= jl_page_size;
        if (should_malloc)
            desc = (jl_fielddesc32_t*)malloc_s(descsz);
        else
            desc = (jl_fielddesc32_t*)alloca(descsz);
        size_t sz = 0;
        size_t alignm = 1;
        int zeroinit = 0;
        int haspadding = 0;
        int isbitsegal = 1;
        int homogeneous = 1;
        int needlock = 0;
        uint32_t npointers = 0;
        jl_value_t *firstty = jl_field_type(st, 0);
        for (i = 0; i < nfields; i++) {
            jl_value_t *fld = jl_field_type(st, i);
            jl_value_t *layout_fld = normalize_typeofbottom_layout_alias(fld);
            int isatomic = jl_field_isatomic(st, i);
            size_t fsz = 0, al = 1;
            if (jl_islayout_inline(fld, &fsz, &al) && (!isatomic || jl_is_datatype(layout_fld))) { // aka jl_datatype_isinlinealloc
                if (__unlikely(fsz > max_size))
                    // Should never happen
                    throw_ovf(should_malloc, desc, st, fsz);
                desc[i].isptr = 0;

                if (jl_is_uniontype(fld)) {
                    fsz += 1; // selector byte
                    zeroinit = 1;
                    // TODO: Some unions could be bits comparable.
                    isbitsegal = 0;
                }
                else {
                    assert(jl_is_datatype(layout_fld));
                    if (fsz > jl_datatype_size(layout_fld)) {
                        // We have to pad the size to integer size class, but it means this has some padding
                        isbitsegal = 0;
                        haspadding = 1;
                    }
                    uint32_t fld_npointers = ((jl_datatype_t*)layout_fld)->layout->npointers;
                    if (((jl_datatype_t*)layout_fld)->layout->flags.haspadding)
                        haspadding = 1;
                    if (!((jl_datatype_t*)layout_fld)->layout->flags.isbitsegal)
                        isbitsegal = 0;
                    if (i >= nfields - st->name->n_uninitialized && fld_npointers &&
                        fld_npointers * sizeof(void*) != fsz) {
                        // For field types that contain pointers, we allow inlinealloc
                        // as long as the field type itself is always fully initialized.
                        // In such a case, we use the first pointer in the inlined field
                        // as the #undef marker (if it is zero, we treat the whole inline
                        // struct as #undef). However, we do not zero-initialize the whole
                        // struct, so the non-pointer parts of the inline allocation may
                        // be arbitrary, but still need to compare egal (because all #undef)
                        // representations are egal. Because of this, we cannot bitscompare
                        // them.
                        // TODO: Consider zero-initializing the whole struct.
                        isbitsegal = 0;
                    }
                    if (!zeroinit)
                        zeroinit = ((jl_datatype_t*)layout_fld)->zeroinit;
                    npointers += fld_npointers;
                }
            }
            else {
                fsz = sizeof(void*);
                al = fsz;
                if (al > MAX_ALIGN)
                    al = MAX_ALIGN;
                desc[i].isptr = 1;
                zeroinit = 1;
                npointers++;
                if (!jl_pointer_egal(fld)) {
                    isbitsegal = 0;
                }
            }
            if (isatomic && fsz > MAX_ATOMIC_SIZE)
                needlock = 1;
            if (isatomic && fsz <= MAX_ATOMIC_SIZE)
                al = fsz = next_power_of_two(fsz);
            if (al != 0) {
                size_t alsz = LLT_ALIGN(sz, al);
                if (alsz != sz)
                    haspadding = 1;
                sz = alsz;
                if (al > alignm)
                    alignm = al;
            }
            homogeneous &= firstty == fld;
            desc[i].offset = sz;
            desc[i].size = fsz;
            if (__unlikely(max_offset - sz < fsz))
                throw_ovf(should_malloc, desc, st, sz);
            sz += fsz;
        }
        if (needlock) {
            size_t offset = LLT_ALIGN(sizeof(jl_mutex_t), alignm);
            for (i = 0; i < nfields; i++) {
                desc[i].offset += offset;
            }
            if (__unlikely(max_offset - sz < offset))
                throw_ovf(should_malloc, desc, st, sz);
            sz += offset;
            haspadding = 1;
        }
        if (homogeneous && jl_is_tuple_type(st)) {
            // Some tuples become LLVM vectors with stronger alignment than what was calculated above.
            unsigned al = jl_special_vector_alignment(nfields, firstty);
            assert(al % alignm == 0);
            if (al > alignm)
                alignm = al;
        }
        if (LLT_ALIGN(sz, alignm) > sz) {
            haspadding = 1;
            sz = LLT_ALIGN(sz, alignm);
        }
        if (should_malloc && npointers)
            pointers = (uint32_t*)malloc_s(npointers * sizeof(uint32_t));
        else
            pointers = (uint32_t*)alloca(npointers * sizeof(uint32_t));
        size_t ptr_i = 0;
        for (i = 0; i < nfields; i++) {
            jl_value_t *fld = jl_field_type(st, i);
            jl_value_t *layout_fld = normalize_typeofbottom_layout_alias(fld);
            uint32_t offset = desc[i].offset / sizeof(jl_value_t**);
            if (desc[i].isptr)
                pointers[ptr_i++] = offset;
            else if (jl_is_datatype(layout_fld)) {
                int j, npointers = ((jl_datatype_t*)layout_fld)->layout->npointers;
                for (j = 0; j < npointers; j++) {
                    pointers[ptr_i++] = offset + jl_ptr_offset((jl_datatype_t*)layout_fld, j);
                }
            }
        }
        assert(ptr_i == npointers);
        st->layout = jl_get_layout(sz, nfields, npointers, alignm, haspadding, isbitsegal, 0, 0, desc, pointers);
        if (should_malloc) {
            free(desc);
            if (npointers)
                free(pointers);
        }
        st->zeroinit = zeroinit;
    }
    // now finish deciding if this instantiation qualifies for special properties
    assert(!isbitstype || st->layout->npointers == 0); // the definition of isbits
    st->isbitstype = isbitstype;
    st->ismutationfree = ismutationfree;
    st->isidentityfree = isidentityfree;
    jl_maybe_allocate_singleton_instance(st);
    return;
}
```

Julia source: src/datatype.c:355-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
STATIC_INLINE int jl_is_datatype_make_singleton(jl_datatype_t *d) JL_NOTSAFEPOINT
{
    // Check d->layout first to avoid NULL dereference (can be NULL during typegroup resolution)
    return d->layout && d->isconcretetype && jl_datatype_size(d) == 0 && d->layout->npointers == 0 && !d->name->mutabl; // implies jl_is_layout_opaque
}
```
-/
def layoutOf (n : Nat) (T : Types) (v : Val) : CM Layout :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match T.layouts.find? (·.dt == v) with
    | some l => return l
    | none =>
      for l in T.layouts do
        if ← egalTypes n T l.dt v [] true then return l
      if let .datatype name ps := v then
        if name == tupleName && (← isConcreteType T v) then
          let mut isbits := true
          let mut singleton := true
          let mut concreteSubtype := true
          for p in ps do
            if p == .bottom then
              isbits := false
              singleton := false
              concreteSubtype := false
            else
              let fld ← layoutOf n T p
              isbits := isbits && fld.isbits
              singleton := singleton && fld.singleton
              concreteSubtype := concreteSubtype && fld.concreteSubtype
          return ⟨v, isbits, singleton, concreteSubtype⟩
      throw s!"no recorded layout for concrete type {repr v}"

/-- `jl_is_datatype_singleton`: only concrete types have an instance.

Julia source: src/julia.h:1936-1939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
STATIC_INLINE int jl_is_datatype_singleton(jl_datatype_t *d) JL_NOTSAFEPOINT
{
    return d->instance != NULL && d->layout->size == 0 && d->layout->npointers == 0;
}
```
-/
def isDatatypeSingleton (n : Nat) (T : Types) (v : Val) : CM Bool := do
  if !(← isConcreteType T v) then return false
  return (← layoutOf n T v).singleton

/-- `jl_isbits`: `isbitstype` requires `isconcretetype`.

Julia source: src/julia.h:1931-1934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
STATIC_INLINE int jl_isbits(void *t) JL_NOTSAFEPOINT // corresponding to isbitstype() in julia
{
    return jl_is_datatype(t) && ((jl_datatype_t*)t)->isbitstype;
}
```
-/
def isBits (n : Nat) (T : Types) (v : Val) : CM Bool := do
  if !(← isConcreteType T v) then return false
  return (← layoutOf n T v).isbits

/-! ## Union construction -/

/-- `jl_rewrap_unionall(t, u)`: wrap `t` in the UnionAlls around `u`.

Julia source: src/jltypes.c:1769-1790 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// wrap `t` in the same unionalls that surround `u`
// where `t` is derived from `u`, so the error checks in jl_type_unionall are unnecessary
jl_value_t *jl_rewrap_unionall(jl_value_t *t, jl_value_t *u)
{
    if (!jl_is_unionall(u))
        return t;
    t = jl_rewrap_unionall(t, ((jl_unionall_t*)u)->body);
    jl_tvar_t *v = ((jl_unionall_t*)u)->var;
    // normalize `T where T<:S` => S
    if (t == (jl_value_t*)v)
        return v->ub;
    // where var doesn't occur in body just return body
    if (!jl_has_typevar(t, v))
        return t;
    JL_GC_PUSH1(&t);
    //if (v->lb == v->ub)  // TODO maybe
    //    t = jl_substitute_var(body, v, v->ub);
    //else
    t = jl_new_struct(jl_unionall_type, v, t);
    JL_GC_POP();
    return t;
}
```
-/
def rewrapUnionall (t : Val) : Val → Val
  | .unionall id nm lb ub body =>
    let t := rewrapUnionall t body
    let v := Val.typevar id nm lb ub
    if t == v then ub
    else if !t.hasTypevar v then t
    else .unionall id nm lb ub t
  | _ => t

/-- `jl_rewrap_unionall_`

Julia source: src/jltypes.c:1794-1803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_rewrap_unionall_(jl_value_t *t, jl_value_t *u)
{
    if (!jl_is_unionall(u))
        return t;
    t = jl_rewrap_unionall_(t, ((jl_unionall_t*)u)->body);
    JL_GC_PUSH1(&t);
    t = jl_new_struct(jl_unionall_type, ((jl_unionall_t*)u)->var, t);
    JL_GC_POP();
    return t;
}
```
-/
def rewrapUnionall_ (t : Val) : Val → Val
  | .unionall id nm lb ub body => .unionall id nm lb ub (rewrapUnionall_ t body)
  | _ => t

/-- `flatten_type_union` of one type; `count_union_components` is the length of the result.

Julia source: src/jltypes.c:634-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int count_union_components(jl_value_t **types, size_t n, int widen)
{
    size_t i, c = 0;
    for (i = 0; i < n; i++) {
        jl_value_t *e = types[i];
        while (jl_is_uniontype(e)) {
            jl_uniontype_t *u = (jl_uniontype_t*)e;
            c += count_union_components(&u->a, 1, widen);
            e = u->b;
        }
        if (widen && jl_is_unionall(e) && jl_is_uniontype(jl_unwrap_unionall(e))) {
            jl_uniontype_t *u = (jl_uniontype_t*)jl_unwrap_unionall(e);
            c += count_union_components(&u->a, 2, widen);
        }
        else {
            c++;
        }
    }
    return c;
}

static void flatten_type_union(jl_value_t **types, size_t n, jl_value_t **out, size_t *idx, int widen) JL_CANSAFEPOINT
{
    size_t i;
    for (i = 0; i < n; i++) {
        jl_value_t *e = types[i];
        while (jl_is_uniontype(e)) {
            jl_uniontype_t *u = (jl_uniontype_t*)e;
            flatten_type_union(&u->a, 1, out, idx, widen);
            e = u->b;
        }
        if (widen && jl_is_unionall(e) && jl_is_uniontype(jl_unwrap_unionall(e))) {
            // flatten this UnionAll into place by switching the union and unionall
            jl_uniontype_t *u = (jl_uniontype_t*)jl_unwrap_unionall(e);
            size_t old_idx = *idx;
            flatten_type_union(&u->a, 2, out, idx, widen);
            for (; old_idx < *idx; old_idx++)
                out[old_idx] = jl_rewrap_unionall(out[old_idx], e);
        }
        else {
            out[*idx] = e;
            (*idx)++;
        }
    }
}
```
-/
def flattenTypeUnion (n : Nat) (widen : Bool) (e : Val) : CM (List Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match e with
    | .union a b => return (← flattenTypeUnion n widen a) ++ (← flattenTypeUnion n widen b)
    | e =>
      match widen, e, e.unwrapUnionall with
      | true, .unionall .., .union a b => do
        -- flatten this UnionAll into place by switching the union and unionall
        let out := (← flattenTypeUnion n widen a) ++ (← flattenTypeUnion n widen b)
        return out.map (rewrapUnionall · e)
      | _, _, _ => return [e]

/-- `strcmp` sign: byte order of UTF-8 equals code point order. -/
def strCmp (a b : String) : Int := if a < b then -1 else if a == b then 0 else 1

/-- `cmp_` -/
def cmpNat (a b : Nat) : Int := if a < b then -1 else if a > b then 1 else 0

/-- The module and type name of a qualified type name: `Main.U.A` is type `A` in module `U`
(`datatype_module_name`, `jl_typename_str`). -/
def moduleAndName (s : String) : String × String :=
  match (s.splitOn ".").reverse with
  | name :: m :: _ => (m, name)
  | [name] => ("", name)
  | [] => ("", "")

/-- `is_value_param`

Julia source: src/jltypes.c:508-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
STATIC_INLINE int is_value_param(jl_value_t *p) JL_NOTSAFEPOINT
{
    return !jl_is_type(p) && !jl_is_typevar(p) && !jl_is_vararg(p);
}
```
-/
def isValueParam (p : Val) : Bool := !p.isType && !p.isTypevar && !p.isVararg

mutual
/-- `value_param_cmp`; the only plain values in this model are `Int` and `Symbol`.

Julia source: src/jltypes.c:515-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// order two value type parameters by their type, then by value; 0 if there is
// no deterministic order
static int value_param_cmp(jl_value_t *a, jl_value_t *b) JL_NOTSAFEPOINT
{
    jl_datatype_t *dt = (jl_datatype_t*)jl_typeof(a);
    if (dt != (jl_datatype_t*)jl_typeof(b))
        return datatype_name_cmp((jl_value_t*)dt, jl_typeof(b));
    if (dt == jl_long_type) {
        // numerically, so e.g. `Val{-1}` prints before `Val{1}`
        ssize_t x = jl_unbox_long(a), y = jl_unbox_long(b);
        return x < y ? -1 : x > y;
    }
    if (dt == jl_symbol_type)
        return strcmp(jl_symbol_name((jl_sym_t*)a), jl_symbol_name((jl_sym_t*)b));
    // padding bytes are undefined, so only padding-free bits values compare by bytes
    if (dt->isbitstype && !dt->layout->flags.haspadding)
        return memcmp(a, b, jl_datatype_size(dt));
    return 0;
}
```
-/
def valueParamCmp (n : Nat) (a b : Val) : CM Int :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if typeOf a != typeOf b then datatypeNameCmp n (typeOf a) (typeOf b) else
    match a, b with
    | .long x, .long y => pure (if x < y then -1 else if x > y then 1 else 0)
    | .symbol x, .symbol y => pure (strCmp x y)
    | _, _ => pure 0

/-- `datatype_name_cmp`

Julia source: src/jltypes.c:535-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// a/b are jl_datatype_t* & not NULL
static int datatype_name_cmp(jl_value_t *a, jl_value_t *b) JL_NOTSAFEPOINT
{
    if (!jl_is_datatype(a))
        return jl_is_datatype(b) ? 1 : 0;
    if (!jl_is_datatype(b))
        return -1;
    int cmp = strcmp(str_(datatype_module_name(a)), str_(datatype_module_name(b)));
    if (cmp != 0)
        return cmp;
    cmp = strcmp(str_(jl_typename_str(a)), str_(jl_typename_str(b)));
    if (cmp != 0)
        return cmp;
    cmp = cmp_(jl_nparams(a), jl_nparams(b));
    if (cmp != 0)
        return cmp;
    // compare up to 3 type parameters
    for (int i = 0; i < 3 && i < jl_nparams(a); i++) {
        jl_value_t *ap = jl_tparam(a, i);
        jl_value_t *bp = jl_tparam(b, i);
        if (ap == bp) {
            continue;
        }
        else if (jl_is_datatype(ap) && jl_is_datatype(bp)) {
            cmp = datatype_name_cmp(ap, bp);
            if (cmp != 0)
                return cmp;
        }
        else if (jl_is_unionall(ap) && jl_is_unionall(bp)) {
            cmp = datatype_name_cmp(jl_unwrap_unionall(ap), jl_unwrap_unionall(bp));
            if (cmp != 0)
                return cmp;
        }
        else if (is_value_param(ap) && is_value_param(bp)) {
            cmp = value_param_cmp(ap, bp);
            if (cmp != 0)
                return cmp;
        }
        else {
            // give up
            cmp = 0;
        }
    }
    return cmp;
}
```
-/
def datatypeNameCmp (n : Nat) (a b : Val) : CM Int :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match a, b with
    | .datatype na pa, .datatype nb pb => do
      let (ma, sa) := moduleAndName na
      let (mb, sb) := moduleAndName nb
      let c := strCmp ma mb
      if c != 0 then return c
      let c := strCmp sa sb
      if c != 0 then return c
      let c := cmpNat pa.length pb.length
      if c != 0 then return c
      -- compare up to 3 type parameters
      for (ap, bp) in (pa.zip pb).take 3 do
        let c ←
          if ap == bp then pure 0
          else if ap.isDatatype && bp.isDatatype then datatypeNameCmp n ap bp
          else if ap.isUnionall && bp.isUnionall then
            datatypeNameCmp n ap.unwrapUnionall bp.unwrapUnionall
          else if isValueParam ap && isValueParam bp then valueParamCmp n ap bp
          else pure 0
        if c != 0 then return c
      return 0
    | .datatype .., _ => pure (-1)
    | _, .datatype .. => pure 1
    | _, _ => pure 0
end

/-- `union_sort_cmp`; `none` is a removed (`NULL`) slot.

Julia source: src/jltypes.c:581-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// sort singletons first, then DataTypes, then UnionAlls,
// ties broken alphabetically including module name & type parameters
static int union_sort_cmp(jl_value_t *a, jl_value_t *b) JL_NOTSAFEPOINT
{
    if (a == NULL)
        return b == NULL ? 0 : 1;
    if (b == NULL)
        return -1;
    if (jl_is_datatype(a)) {
        if (!jl_is_datatype(b))
            return -1;
        if (jl_is_datatype_singleton((jl_datatype_t*)a)) {
            if (jl_is_datatype_singleton((jl_datatype_t*)b))
                return datatype_name_cmp(a, b);
            return -1;
        }
        else if (jl_is_datatype_singleton((jl_datatype_t*)b)) {
            return 1;
        }
        else if (jl_isbits(a)) {
            if (jl_isbits(b))
                return datatype_name_cmp(a, b);
            return -1;
        }
        else if (jl_isbits(b)) {
            return 1;
        }
        else {
            return datatype_name_cmp(a, b);
        }
    }
    else {
        if (jl_is_datatype(b))
            return 1;
        // `Type{T}`/`TypeEgal{T}` wrappers sort like the `Type` datatypes they
        // used to be: after other datatypes, but before typevars and unionalls,
        // so that e.g. `Union{T, Type{T}}` keeps its historical component order
        // (the subtype environment binds a variable from the first matching
        // branch, and `foo(::Union{T, Type{T}}) where T` must bind `T` from the
        // `Type{T}` component when both match, #62141)
        if (jl_is_some_Type(a)) {
            if (!jl_is_some_Type(b))
                return -1;
            // order two wrappers by their parameters, as the parameter
            // comparison loop used to
            return datatype_name_cmp(jl_some_Type_T(a), jl_some_Type_T(b));
        }
        if (jl_is_some_Type(b))
            return 1;
        return datatype_name_cmp(jl_unwrap_unionall(a), jl_unwrap_unionall(b));
    }
}
```
-/
def unionSortCmp (n : Nat) (T : Types) : Option Val → Option Val → CM Int
  | none, none => pure 0
  | none, some _ => pure 1
  | some _, none => pure (-1)
  | some a, some b => do
    if a.isDatatype then
      if !b.isDatatype then return -1
      if ← isDatatypeSingleton n T a then
        if ← isDatatypeSingleton n T b then return ← datatypeNameCmp n a b
        return -1
      if ← isDatatypeSingleton n T b then return 1
      if ← isBits n T a then
        if ← isBits n T b then return ← datatypeNameCmp n a b
        return -1
      if ← isBits n T b then return 1
      datatypeNameCmp n a b
    else
      if b.isDatatype then return 1
      if a.isSomeType then
        if !b.isSomeType then return -1
        return ← datatypeNameCmp n a.someTypeT b.someTypeT
      if b.isSomeType then return 1
      datatypeNameCmp n a.unwrapUnionall b.unwrapUnionall

/-- `isort_union`: insertion sort, each element moving left past every element it sorts
before.

Julia source: src/jltypes.c:681-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void isort_union(jl_value_t **a, size_t len) JL_NOTSAFEPOINT
{
    size_t i, j;
    for (i = 1; i < len; i++) {
        jl_value_t *x = a[i];
        for (j = i; j > 0; j--) {
            jl_value_t *y = a[j - 1];
            if (!(union_sort_cmp(x, y) < 0))
                break;
            a[j] = y;
        }
        a[j] = x;
    }
}
```
-/
def isortUnion (n : Nat) (T : Types) (xs : List (Option Val)) : CM (List (Option Val)) := do
  -- the sorted prefix, rightmost element first
  let mut rev : List (Option Val) := []
  for x in xs do
    rev ← insertRev x rev
  return rev.reverse
where
  insertRev (x : Option Val) : List (Option Val) → CM (List (Option Val))
    | [] => pure [x]
    | y :: ys => do
      if (← unionSortCmp n T x y) < 0 then return y :: (← insertRev x ys)
      return x :: y :: ys

/-! ## Type instantiation and union construction

Functions of `jltypes.c` call into `subtype.c` (`jl_subtype`, `jl_types_equal`, ...), which calls
back into `jltypes.c`. Lean modules cannot import each other, so these functions take the
`subtype.c` operations as a parameter `ops`; `subtype_c.lean` ties the knot.

Modelling notes.
* The type cache (`lookup_type`) is not modelled: a DataType is its name and parameters. Julia's
  cache can return an earlier `==`-equal instantiation, which depends on session history.
* A DataType's supertype is computed on demand (`superOf` in `subtype_c.lean`) rather than at
  construction, and its field types and layout are not computed (layouts are recorded input).
* "Changed" (`pi != elt` in C) is structural inequality.
* Recursive type groups (`jl_typestack_t`, deferred caches and supertypes) are outside the model.
-/

/-- Operations defined in `subtype.c` that the functions of `jltypes.c` call. -/
structure Ops where
  subtype : Val → Val → CM Bool
  typesEqual : Val → Val → CM Bool
  isLeafBound : Val → CM Bool
  hasEmptyIntersection : Val → Val → CM Bool
  obviouslyDisjoint : Val → Val → Bool → CM Bool

/-- A `jl_typeenv_t` chain for instantiation: variable id and value, innermost first. -/
abbrev InstEnv := List (Nat × Val)

def anytupleType : Val := .datatype tupleName [.vararg (some anyType) none]
def emptytupleType : Val := .datatype tupleName []

def Val.varargT? : Val → Option Val | .vararg t _ => t | _ => none
def Val.varargN? : Val → Option Val | .vararg _ n => n | _ => none
/-- `jl_unwrap_vararg` -/
def Val.unwrapVararg (v : Val) : Val := v.varargT?.getD anyType
/-- `jl_is_va_tuple` -/
def Val.isVaTuple (v : Val) : Bool := v.isTupleType && (v.params.getLast?.map Val.isVararg).getD false

/-- `jl_vararg_kind` -/
inductive VarargKind | none | unbound | int | bound
  deriving BEq, Repr

def Val.varargKind : Val → VarargKind
  | .vararg _ none => .unbound
  | .vararg _ (some (.long _)) => .int
  | .vararg _ (some _) => .bound
  | _ => .none

/-- The variables of a type name's wrapper, outermost first. -/
def wrapperVars : Val → List Val
  | .unionall id nm lb ub body => .typevar id nm lb ub :: wrapperVars body
  | _ => []

/-- `is_nestable_type_param`. A tuple type's parameters are types, never module objects, so
`jl_is_module(pi)` is false here.

Julia source: src/builtins.c:2022-2039 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_nestable_type_param(jl_value_t *t)
{
    if (jl_is_namedtuple_type(t))
        t = jl_tparam1(t);
    if (jl_is_tuple_type(t)) {
        // NOTE: tuples of symbols are not currently bits types, but have been
        // allowed as type parameters. this is a bit ugly.
        size_t i, l = jl_nparams(t);
        for (i = 0; i < l; i++) {
            jl_value_t *pi = jl_tparam(t, i);
            if (!(pi == (jl_value_t*)jl_symbol_type || jl_isbits(pi) || is_nestable_type_param(pi) ||
        jl_is_module(pi)))
                return 0;
        }
        return 1;
    }
    return 0;
}
```
-/
def isNestableTypeParam (n : Nat) (T : Types) (t : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let t ← match t with
      | .datatype "Core.NamedTuple" ps =>
        match ps with
        | [_, p] => pure p
        | _ => throw s!"malformed NamedTuple type {repr t}"
      | t => pure t
    let .datatype name ps := t | return false
    if name != tupleName then return false
    for pi in ps do
      if pi == symbolType then continue
      if ← isBits n T pi then continue
      if ← isNestableTypeParam n T pi then continue
      return false
    return true

/-- `jl_valid_type_param`.

Julia source: src/builtins.c:2041-2050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_valid_type_param(jl_value_t *v)
{
    if (jl_is_tuple(v) || jl_is_namedtuple(v))
        return is_nestable_type_param(jl_typeof(v));
    if (jl_is_vararg(v))
        return 0;
    // TODO: maybe more things
    return jl_is_type(v) || jl_is_typevar(v) || jl_is_symbol(v) || jl_isbits(jl_typeof(v)) ||
        jl_is_module(v);
}
```
-/
def validTypeParam (n : Nat) (T : Types) (v : Val) : CM Bool := do
  if let .datatype nm _ := typeOf v then
    if nm == tupleName || nm == "Core.NamedTuple" then
      return ← isNestableTypeParam n T (typeOf v)
  if v.isVararg then return false
  if v.isType || v.isTypevar || v.isSymbol then return true
  if ← isBits n T (typeOf v) then return true
  return v.isModule

/-- `jl_new_typevar`

Julia source: src/builtins.c:2210-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_tvar_t *jl_new_typevar(jl_sym_t *name, jl_value_t *lb, jl_value_t *ub)
{
    if (lb != jl_bottom_type && !jl_is_type(lb) && !jl_is_typevar(lb))
        jl_type_error_rt("TypeVar", "lower bound", (jl_value_t *)jl_type_type, lb);
    if (ub != (jl_value_t *)jl_any_type && !jl_is_type(ub) && !jl_is_typevar(ub))
        jl_type_error_rt("TypeVar", "upper bound", (jl_value_t *)jl_type_type, ub);
    jl_task_t *ct = jl_current_task;
    jl_tvar_t *tv = (jl_tvar_t *)jl_gc_alloc(ct->ptls, sizeof(jl_tvar_t), jl_tvar_type);
    jl_set_typetagof(tv, jl_tvar_tag, 0);
    tv->name = name;
    tv->lb = lb;
    tv->ub = ub;
    return tv;
}

```
-/
def newTypevar (name : String) (lb ub : Val) : CM Val := do
  if lb != .bottom && !lb.isType && !lb.isTypevar then
    throw s!"TypeError: in TypeVar, in lower bound, expected Type, got {repr lb}"
  if ub != anyType && !ub.isType && !ub.isTypevar then
    throw s!"TypeError: in TypeVar, in upper bound, expected Type, got {repr ub}"
  return .typevar (← freshId) name lb ub

/-- `within_typevar`

Julia source: src/jltypes.c:1527-1542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int within_typevar(jl_value_t *t, jl_value_t *vlb, jl_value_t *vub) JL_CANSAFEPOINT
{
    jl_value_t *lb = t, *ub = t;
    if (jl_is_typevar(t) || jl_has_free_typevars(t)) {
        // TODO: automatically restrict typevars in method definitions based on
        // types they are used in.
        return 1;
        //lb = ((jl_tvar_t*)t)->lb;
        //ub = ((jl_tvar_t*)t)->ub;
    }
    else if (!jl_is_type(t)) {
        return vlb == jl_bottom_type && vub == (jl_value_t*)jl_any_type;
    }
    return ((jl_has_free_typevars(vlb) || jl_subtype(vlb, lb)) &&
            (jl_has_free_typevars(vub) || jl_subtype(ub, vub)));
}
```
-/
def withinTypevar (ops : Ops) (t vlb vub : Val) : CM Bool := do
  if t.isTypevar || t.hasFreeTypevars then return true
  if !t.isType then return vlb == .bottom && vub == anyType
  if !vlb.hasFreeTypevars then
    if !(← ops.subtype vlb t) then return false
  if vub.hasFreeTypevars then return true
  ops.subtype t vub

/-- `extract_wrapper`

Julia source: src/jltypes.c:2192-2205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *extract_wrapper(jl_value_t *t JL_PROPAGATES_ROOT) JL_NOTSAFEPOINT JL_GLOBALLY_ROOTED
{
    t = jl_unwrap_unionall(t);
    if (jl_is_datatype(t))
        return ((jl_datatype_t*)t)->name->wrapper;
    if (jl_is_uniontype(t)) {
        jl_value_t *n1 = extract_wrapper(((jl_uniontype_t*)t)->a);
        if (n1 != NULL) return n1;
        return extract_wrapper(((jl_uniontype_t*)t)->b);
    }
    if (jl_is_typevar(t))
        return extract_wrapper(((jl_tvar_t*)t)->ub);
    return NULL;
}
```
-/
def extractWrapper (n : Nat) (T : Types) (t : Val) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t.unwrapUnionall with
    | .datatype name _ => return some (← T.typename name).wrapper
    | .union a b => do
      match ← extractWrapper n T a with
      | some w => return some w
      | none => extractWrapper n T b
    | .typevar _ _ _ ub => extractWrapper n T ub
    | _ => return none

mutual
/-- `_may_substitute_ub`, from the top of its `while (1)` loop; returns the result and the
updated `cov_count`.

Julia source: src/jltypes.c:2207-2264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int _may_substitute_ub(jl_value_t *v, jl_tvar_t *var, int inside_inv, int *cov_count) JL_NOTSAFEPOINT
{
    while (1) {
        if (v == (jl_value_t*)var) {
            if (inside_inv) {
                return 0;
            }
            else {
                (*cov_count)++;
                return *cov_count <= 1 || jl_is_concrete_type(var->ub);
            }
        }
        while (jl_is_unionall(v)) {
            jl_unionall_t *ua = (jl_unionall_t*)v;
            if (ua->var == var)
                return 1;
            if (ua->var->lb != jl_bottom_type && !_may_substitute_ub(ua->var->lb, var, inside_inv, cov_count))
                return 0;
            if (ua->var->ub != (jl_value_t*)jl_any_type && !_may_substitute_ub(ua->var->ub, var, inside_inv, cov_count))
                return 0;
            v = ua->body;
        }
        if (jl_is_datatype(v)) {
            int invar = inside_inv || !jl_is_tuple_type(v);
            for (size_t i = 0; i < jl_nparams(v); i++) {
                jl_value_t *p = jl_tparam(v, i);
                if (!_may_substitute_ub(p, var, invar, cov_count))
                    return 0;
            }
            return 1;
        }
        else if (jl_is_uniontype(v)) {
            // TODO: is !inside_inv, these don't have to share the changes to cov_count
            if (!_may_substitute_ub(((jl_uniontype_t*)v)->a, var, inside_inv, cov_count))
                return 0;
            v = ((jl_uniontype_t*)v)->b;
        }
        else if (jl_is_vararg(v)) {
            jl_vararg_t *va = (jl_vararg_t*)v;
            if (!va->T)
                return 1;
            if (va->N) {
                if (!_may_substitute_ub(va->N, var, 1, cov_count))
                    return 0;
            }
            if (!jl_is_concrete_type(var->ub))
                inside_inv = 1; // treat as invariant inside vararg, for the sake of this algorithm
            v = va->T;
        }
        else if (jl_is_some_Type(v)) {
            inside_inv = 1;
            v = jl_some_Type_T(v);
        }
        else {
            return 1;
        }
    }
}
```
-/
def maySubstituteUbTop (n : Nat) (T : Types) (var v : Val) (insideInv : Bool) (cov : Nat) :
    CM (Bool × Nat) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if v == var then
      if insideInv then return (false, cov)
      let cov := cov + 1
      if cov ≤ 1 then return (true, cov)
      return (← isConcreteType T var.tvUb, cov)
    maySubstituteUbBody n T var v insideInv cov

/-- The rest of one iteration of `_may_substitute_ub`'s loop, after the `v == var` test. -/
def maySubstituteUbBody (n : Nat) (T : Types) (var v : Val) (insideInv : Bool) (cov : Nat) :
    CM (Bool × Nat) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match v with
    | .unionall id _ lb ub body =>
      if some id == var.tvId then return (true, cov)
      let mut cov := cov
      if lb != .bottom then
        let (ok, c) ← maySubstituteUbTop n T var lb insideInv cov
        cov := c
        if !ok then return (false, cov)
      if ub != anyType then
        let (ok, c) ← maySubstituteUbTop n T var ub insideInv cov
        cov := c
        if !ok then return (false, cov)
      maySubstituteUbBody n T var body insideInv cov
    | .datatype name ps => do
      let invar := insideInv || name != tupleName
      let mut cov := cov
      for p in ps do
        let (ok, c) ← maySubstituteUbTop n T var p invar cov
        cov := c
        if !ok then return (false, cov)
      return (true, cov)
    | .union a b => do
      let (ok, cov) ← maySubstituteUbTop n T var a insideInv cov
      if !ok then return (false, cov)
      maySubstituteUbTop n T var b insideInv cov
    | .vararg none _ => return (true, cov)
    | .vararg (some t) N => do
      let mut cov := cov
      if let some N := N then
        let (ok, c) ← maySubstituteUbTop n T var N true cov
        cov := c
        if !ok then return (false, cov)
      -- treat as invariant inside vararg, for the sake of this algorithm
      let insideInv := if !(← isConcreteType T var.tvUb) then true else insideInv
      maySubstituteUbTop n T var t insideInv cov
    | .typeeq t | .typeegal t => maySubstituteUbTop n T var t true cov
    | _ => return (true, cov)
end

/-- `may_substitute_ub`

Julia source: src/jltypes.c:2266-2275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// Check whether `var` may be replaced with its upper bound `ub` in `v where var<:ub`
// Conditions:
//  * `var` does not appear in invariant position
//  * `var` appears at most once (in covariant position) and not in a `Vararg`
//    unless the upper bound is concrete (diagonal rule)
static int may_substitute_ub(jl_value_t *v, jl_tvar_t *var) JL_NOTSAFEPOINT
{
    int cov_count = 0;
    return _may_substitute_ub(v, var, 0, &cov_count);
}
```
-/
def maySubstituteUb (n : Nat) (T : Types) (v var : Val) : CM Bool := do
  return (← maySubstituteUbTop n T var v false 0).1

/-- `jl_wrap_Type`: `Type{t}`

Julia source: src/jltypes.c:3268-3292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_typeeq_t *jl_wrap_Type(jl_value_t *t)
{
    if (jl_is_typeeq(t) && jl_typeeq_T(t) == jl_bottom_type)
        t = (jl_value_t*)jl_typeofbottom_type;
    jl_value_t *tw = extract_wrapper(t);
    if (tw && tw != t && jl_typeof(t) == jl_typeof(tw) &&
            !jl_has_free_typevars(t) && jl_types_equal(t, tw)) {
        t = tw;
    }
    if (t == jl_bottom_type && jl_typeofbottom_type && jl_typeofbottom_type->name) {
        jl_value_t *cached = jl_atomic_load_relaxed(&jl_typeofbottom_type->name->Typeofwrapper);
        if (cached)
            return (jl_typeeq_t*)cached;
    }
    jl_task_t *ct = jl_current_task;
    JL_GC_PUSH1(&t);
    jl_typeeq_t *te = (jl_typeeq_t*)jl_gc_alloc(ct->ptls, sizeof(jl_typeeq_t), jl_typeeq_type);
    jl_set_typetagof(te, jl_typeeq_tag, 0);
    te->T = t;
    if (t == jl_bottom_type && jl_typeofbottom_type && jl_typeofbottom_type->name) {
        jl_gc_write_atomic(jl_typeofbottom_type->name, jl_typeofbottom_type->name->Typeofwrapper, jl_value_t, (jl_value_t*)te, relaxed);
    }
    JL_GC_POP();
    return te;
}
```
-/
def wrapType (n : Nat) (T : Types) (ops : Ops) (t : Val) : CM Val := do
  let t := if t.isTypeeq && t.someTypeT == .bottom then typeofbottomType else t
  let mut t := t
  if let some tw ← extractWrapper n T t then
    if tw != t && typeOf t == typeOf tw && !t.hasFreeTypevars then
      if ← ops.typesEqual t tw then t := tw
  return .typeeq t

/-- `jl_wrap_TypeEgal`

Julia source: src/jltypes.c:3294-3311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_wrap_TypeEgal(jl_value_t *t)
{
    // `TypeEgal` pins a type value by egality; non-type parameters and free
    // typevars are not valid.
    if (!jl_is_type(t) || jl_has_free_typevars(t))
        jl_type_error_rt("TypeEgal", "parameter", (jl_value_t*)jl_type_type, t);
    // `typeof(Union{})` already denotes exactly the single-instance set `{Union{}}`
    // (the bottom object is unique), so normalize to it
    if (t == jl_bottom_type)
        return (jl_value_t*)jl_typeofbottom_type;
    jl_task_t *ct = jl_current_task;
    JL_GC_PUSH1(&t);
    jl_value_t *te = jl_gc_alloc(ct->ptls, sizeof(jl_typeeq_t), jl_typeegal_type);
    jl_set_typetagof(te, jl_typeegal_tag, 0);
    ((jl_typeeq_t*)te)->T = t;
    JL_GC_POP();
    return te;
}
```
-/
def wrapTypeEgal (t : Val) : CM Val := do
  if !t.isType || t.hasFreeTypevars then
    throw s!"TypeError: in TypeEgal, in parameter, expected Type, got {repr t}"
  if t == .bottom then return typeofbottomType
  return .typeegal t

/-- The union of the remaining slots, built right to left (`jl_new_struct(jl_uniontype_type, ...)`). -/
def buildUnion (temp : List (Option Val)) : Val :=
  temp.foldr (fun x acc => match x with
    | none => acc
    | some x => if acc == .bottom then x else .union x acc) .bottom

mutual
/-- `inst_type_w_(t, env, NULL, check, nothrow)`; `none` is `NULL` (only when `nothrow`).

Julia source: src/jltypes.c:3040-3219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *inst_type_w_(jl_value_t *t, jl_typeenv_t *env, jl_typestack_t *stack, int check, int nothrow, jl_deferred_typecache_t *dcache)
{
    size_t i;
    if (jl_is_typeapp(t))
        return t;
    if (jl_is_typevar(t)) {
        jl_typeenv_t *e = env;
        while (e != NULL) {
            if (e->var == (jl_tvar_t*)t) {
                jl_value_t *val = e->val;
                return val;
            }
            e = e->prev;
        }
        return t;
    }
    if (jl_is_unionall(t)) {
        jl_unionall_t *ua = (jl_unionall_t*)t;
        jl_value_t *lb = NULL;
        jl_value_t *var = NULL;
        jl_value_t *newbody = NULL;
        JL_GC_PUSH3(&lb, &var, &newbody);
        // set nothrow <= 1 to ensure lb's accuracy.
        lb = inst_type_w_(ua->var->lb, env, stack, check, nothrow ? 1 : 0, dcache);
        if (lb == NULL) {
            assert(nothrow);
            t = NULL;
        }
        if (t != NULL) {
            var = inst_type_w_(ua->var->ub, env, stack, check, nothrow, dcache);
            if (var == NULL) {
                if (lb == jl_bottom_type)
                    var = jl_bottom_type;
                else
                    t = NULL;
            }
            else if (lb != ua->var->lb || var != ua->var->ub) {
                var = (jl_value_t*)jl_new_typevar(ua->var->name, lb, var);
            }
            else {
                var = (jl_value_t*)ua->var;
            }
        }
        if (t != NULL) {
            jl_typeenv_t newenv = { ua->var, var, env };
            newbody = inst_type_w_(ua->body, &newenv, stack, check, nothrow, dcache);
            if (newbody == NULL) {
                t = NULL;
            }
            else if (!jl_has_typevar(newbody, (jl_tvar_t *)var) && jl_has_typevar(ua->body, ua->var)) {
                // inner instantiation made a typevar disappear, e.g.
                // NTuple{0,T} => Tuple{}; drop the now-vacuous UnionAll
                // However, if the original body was degenerate and didn't have the typevar (special
                // case in method signature creation, then we don't normalize it here either to avoid
                // confusing subtyping).
                t = newbody;
            }
            else if (newbody != ua->body || var != (jl_value_t*)ua->var) {
                // if t's parameters are not bound in the environment, return it uncopied (#9378)
                t = jl_new_struct(jl_unionall_type, var, newbody);
            }
        }
        JL_GC_POP();
        return t;
    }
    if (jl_is_uniontype(t)) {
        jl_uniontype_t *u = (jl_uniontype_t*)t;
        jl_value_t *a = inst_type_w_(u->a, env, stack, check, nothrow, dcache);
        jl_value_t *b = NULL;
        JL_GC_PUSH2(&a, &b);
        b = inst_type_w_(u->b, env, stack, check, nothrow, dcache);
        if (nothrow) {
            // ensure jl_type_union nothrow.
            if (a && !(jl_is_typevar(a) || jl_is_type(a)))
                a = NULL;
            if (b && !(jl_is_typevar(b) || jl_is_type(b)))
                b = NULL;
        }
        if (a != u->a || b != u->b) {
            if (!check) {
                // fast path for `jl_rename_unionall`.
                t = jl_new_struct(jl_uniontype_type, a, b);
            }
            else if (a == NULL || b == NULL) {
                assert(nothrow);
                t = nothrow == 1 ? NULL : a == NULL ? b : a;
            }
            else {
                assert(a != NULL && b != NULL);
                jl_value_t *uargs[2] = {a, b};
                t = jl_type_union(uargs, 2);
            }
        }
        JL_GC_POP();
        return t;
    }
    if (jl_is_typeeq(t)) {
        jl_typeeq_t *te = (jl_typeeq_t*)t;
        jl_value_t *T = inst_type_w_(te->T, env, stack, check, nothrow ? 1 : 0, dcache);
        JL_GC_PUSH1(&T);
        if (T == NULL) {
            assert(nothrow);
            t = NULL;
        }
        else if (T != te->T) {
            t = (jl_value_t*)jl_wrap_Type(T);
        }
        JL_GC_POP();
        return t;
    }
    if (jl_is_typeegal(t)) {
        jl_typeeq_t *te = (jl_typeeq_t*)t;
        jl_value_t *T = inst_type_w_(te->T, env, stack, check, nothrow ? 1 : 0, dcache);
        JL_GC_PUSH1(&T);
        if (T == NULL) {
            assert(nothrow);
            t = NULL;
        }
        else if (T != te->T) {
            t = jl_wrap_TypeEgal(T);
        }
        JL_GC_POP();
        return t;
    }
    if (jl_is_vararg(t)) {
        jl_vararg_t *v = (jl_vararg_t*)t;
        jl_value_t *T = NULL;
        jl_value_t *N = NULL;
        JL_GC_PUSH2(&T, &N);
        if (v->T) {
            T = inst_type_w_(v->T, env, stack, check, nothrow, dcache);
            if (T == NULL) {
                if (nothrow == 2)
                    T = jl_bottom_type;
                else
                    t = NULL;
            }
            if (t && v->N) {
                // set nothrow <= 1 to ensure invariant parameter's accuracy.
                N = inst_type_w_(v->N, env, stack, check, nothrow ? 1 : 0, dcache);
                if (N == NULL)
                    t = NULL;
            }
        }
        if (t && (T != v->T || N != v->N))
            t = (jl_value_t*)jl_wrap_vararg(T, N, check, nothrow);
        JL_GC_POP();
        return t;
    }
    if (!jl_is_datatype(t))
        return t;
    jl_datatype_t *tt = (jl_datatype_t*)t;
    jl_svec_t *tp = tt->parameters;
    if (tp == jl_emptysvec)
        return t;
    jl_typename_t *tn = tt->name;
    if (tn == jl_tuple_typename)
        return inst_tuple_w_(t, env, stack, check, nothrow, dcache);
    size_t ntp = jl_svec_len(tp);
    jl_value_t **iparams;
    JL_GC_PUSHARGS(iparams, ntp);
    int bound = 0;
    for (i = 0; i < ntp; i++) {
        jl_value_t *elt = jl_svecref(tp, i);
        // set nothrow <= 1 to ensure invariant parameter's accuracy.
        jl_value_t *pi = inst_type_w_(elt, env, stack, check, nothrow ? 1 : 0, dcache);
        if (pi == NULL) {
            assert(nothrow);
            t = NULL;
            break;
        }
        iparams[i] = pi;
        bound |= (pi != elt);
    }
    // if t's parameters are not bound in the environment, return it uncopied (#9378)
    if (t != NULL && bound)
        t = inst_datatype_inner(tt, NULL, iparams, ntp, stack, env, check, nothrow, dcache);
    JL_GC_POP();
    return t;
}
```
-/
def instTypeW (n : Nat) (T : Types) (ops : Ops) (t : Val) (env : InstEnv) (check : Bool)
    (nothrow : Nat) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match t with
    | .typeapp .. => return some t
    | .typevar id .. => return some ((env.lookup id).getD t)
    | .unionall uid nm ulb uub body => do
      -- set nothrow <= 1 to ensure lb's accuracy.
      let some lb ← instTypeW n T ops ulb env check (if nothrow != 0 then 1 else 0)
        | return none
      let var ← match ← instTypeW n T ops uub env check nothrow with
        | none =>
          if lb == .bottom then
            throw "unrepresentable: UnionAll whose variable is replaced by Union{}"
          return none
        | some ub =>
          if lb != ulb || ub != uub then newTypevar nm lb ub
          else pure (Val.typevar uid nm ulb uub)
      let .typevar vid vnm vlb vub := var | throw "unreachable"
      let some newbody ← instTypeW n T ops body ((uid, var) :: env) check nothrow
        | return none
      if !newbody.hasTypevar var && body.hasTypevar (.typevar uid nm ulb uub) then
        -- inner instantiation made a typevar disappear, e.g. NTuple{0,T} => Tuple{}
        return some newbody
      if newbody != body || vid != uid || vlb != ulb || vub != uub then
        return some (.unionall vid vnm vlb vub newbody)
      return some t
    | .union ua ub => do
      let mut a ← instTypeW n T ops ua env check nothrow
      let mut b ← instTypeW n T ops ub env check nothrow
      if nothrow != 0 then
        -- ensure jl_type_union nothrow.
        if let some x := a then if !(x.isTypevar || x.isType) then a := none
        if let some x := b then if !(x.isTypevar || x.isType) then b := none
      if a == some ua && b == some ub then return some t
      if !check then
        -- fast path for `jl_rename_unionall`.
        match a, b with
        | some x, some y => return some (.union x y)
        | _, _ => throw "unrepresentable: Union with a NULL component"
      match a, b with
      | some x, some y => return some (← typeUnion n T ops [x, y])
      | none, y => return if nothrow == 1 then none else y
      | x, none => return if nothrow == 1 then none else x
    | .typeeq te => do
      let some x ← instTypeW n T ops te env check (if nothrow != 0 then 1 else 0) | return none
      if x != te then return some (← wrapType n T ops x)
      return some t
    | .typeegal te => do
      let some x ← instTypeW n T ops te env check (if nothrow != 0 then 1 else 0) | return none
      if x != te then return some (← wrapTypeEgal x)
      return some t
    | .vararg vT vN => do
      match vT with
      | none => return some t
      | some vt =>
        let x ← instTypeW n T ops vt env check nothrow
        let x ← match x with
          | some x => pure x
          | none => if nothrow == 2 then pure .bottom else return none
        let mut N := none
        if let some vn := vN then
          -- set nothrow <= 1 to ensure invariant parameter's accuracy.
          match ← instTypeW n T ops vn env check (if nothrow != 0 then 1 else 0) with
          | none => return none
          | some y => N := some y
        if some x != vT || N != vN then return ← wrapVararg n T ops (some x) N check nothrow
        return some t
    | .datatype _ [] => return some t
    | .datatype name ps => do
      if name == tupleName then return ← instTupleW n T ops t env check nothrow
      let mut iparams := #[]
      for elt in ps do
        -- set nothrow <= 1 to ensure invariant parameter's accuracy.
        let some pi ← instTypeW n T ops elt env check (if nothrow != 0 then 1 else 0)
          | return none
        iparams := iparams.push pi
      -- if t's parameters are not bound in the environment, return it uncopied (#9378)
      if iparams.toList == ps then return some t
      instDatatypeInner n T ops name iparams.toList check nothrow
    | _ => return some t

/-- `inst_tuple_w_`

Julia source: src/jltypes.c:2967-3034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *inst_tuple_w_(jl_value_t *t, jl_typeenv_t *env, jl_typestack_t *stack, int check, int nothrow, jl_deferred_typecache_t *dcache) JL_CANSAFEPOINT
{
    jl_datatype_t *tt = (jl_datatype_t*)t;
    jl_svec_t *tp = tt->parameters;
    size_t ntp = jl_svec_len(tp);
    // Instantiate Tuple{Vararg{T,N}} where T is fixed and N is known, such as Dims{3}
    // And avoiding allocating the intermediate steps
    // Note this does not instantiate Tuple{Vararg{Int,3}}; that's done in inst_datatype_inner
    // Note this does not instantiate NTuple{N,T}, since it is unnecessary and inefficient to expand that now
    if (jl_is_va_tuple(tt) && ntp == 1) {
        // If this is a Tuple{Vararg{T,N}} with known N and T, expand it to
        // a fixed-length tuple
        jl_value_t *T=NULL, *N=NULL;
        jl_value_t *va = jl_tparam0(tt);
        jl_value_t *ttT = jl_unwrap_vararg(va);
        jl_value_t *ttN = jl_unwrap_vararg_num(va);
        jl_typeenv_t *e = env;
        while (e != NULL) {
            if ((jl_value_t*)e->var == ttT)
                T = e->val;
            else if ((jl_value_t*)e->var == ttN)
                N = e->val;
            e = e->prev;
        }
        if (T != NULL && N != NULL && jl_is_long(N)) { // TODO: && !jl_has_free_typevars(T) to match inst_datatype_inner, or even && jl_is_concrete_type(T)
            // Since this is skipping jl_wrap_vararg, we inline the checks from it here
            ssize_t nt = jl_unbox_long(N);
            if (nt >= 0)
                return jl_tupletype_fill(nt, T, check, nothrow, dcache);
            if (nothrow)
                return NULL;
            jl_errorf("Vararg length is negative: %zd", nt);
        }
    }
    jl_value_t **iparams;
    int onstack = ntp < jl_page_size/sizeof(jl_value_t*);
    JL_GC_PUSHARGS(iparams, onstack ? ntp : 1);
    jl_svec_t *ip_heap = NULL;
    if (!onstack) {
        ip_heap = jl_alloc_svec(ntp);
        iparams[0] = (jl_value_t*)ip_heap;
        iparams = jl_svec_data(ip_heap);
    }
    int i, bound = 0;
    for (i = 0; i < ntp; i++) {
        jl_value_t *elt = jl_svecref(tp, i);
        jl_value_t *pi = inst_type_w_(elt, env, stack, check, nothrow, dcache);
        if (pi == NULL) {
            assert(nothrow);
            if (nothrow == 1 || (i == ntp-1 && jl_is_vararg(elt))) {
                t = NULL;
                break;
            }
            else {
                pi = jl_bottom_type;
            }
        }
        if (ip_heap)
            jl_gc_write(ip_heap, iparams[i], jl_value_t, pi);
        else
            iparams[i] = pi;
        bound |= (pi != elt);
    }
    if (t != NULL && bound)
        t = inst_datatype_inner(tt, ip_heap, iparams, ntp, stack, env, check, nothrow, dcache);
    JL_GC_POP();
    return t;
}
```
-/
def instTupleW (n : Nat) (T : Types) (ops : Ops) (t : Val) (env : InstEnv) (check : Bool)
    (nothrow : Nat) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let tp := t.params
    if t.isVaTuple && tp.length == 1 then
      -- If this is a Tuple{Vararg{T,N}} with known N and T, expand it to a fixed-length tuple.
      let va := tp.head!
      let ttT := va.unwrapVararg
      let ttN := va.varargN?
      let mut vT : Option Val := none
      let mut vN : Option Val := none
      for (var, val) in env do
        if ttT.tvId == some var then vT := some val
        else if (ttN.bind Val.tvId) == some var then vN := some val
      if let (some x, some (.long nt)) := (vT, vN) then
        if nt ≥ 0 then return ← tupletypeFill n T ops nt.toNat x check nothrow
        if nothrow != 0 then return none
        throw s!"Vararg length is negative: {nt}"
    let mut iparams := #[]
    let mut failed := false
    for h : i in [0:tp.length] do
      let elt := tp[i]
      let pi ← match ← instTypeW n T ops elt env check nothrow with
        | some pi => pure (some pi)
        | none =>
          if nothrow == 1 || (i == tp.length - 1 && elt.isVararg) then pure none
          else pure (some .bottom)
      match pi with
      | none => failed := true; break
      | some pi => iparams := iparams.push pi
    if failed then return none
    if iparams.toList == tp then return some t
    instDatatypeInner n T ops tupleName iparams.toList check nothrow

/-- `inst_datatype_inner(dt, p, iparams, ntp, NULL, env, check, nothrow)` for a DataType named
`name`; `none` is `NULL`.

Julia source: src/jltypes.c:2470-2883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *inst_datatype_inner(jl_datatype_t *dt, jl_svec_t *p, jl_value_t **iparams, size_t ntp,
                                       jl_typestack_t *stack, jl_typeenv_t *env, int check, int nothrow,
                                       jl_deferred_typecache_t *dcache)
{
    jl_typestack_t top;
    jl_typename_t *tn = dt->name;
    int istuple = (tn == jl_tuple_typename);
    int isnamedtuple = (tn == jl_namedtuple_typename);

    // check if type cache will be applicable
    // n.b. for deferred instantiations, `cacheable` still controls the cache
    // lookup, hash computation and eager field/layout instantiation; only the
    // write side (cache insertion, global-root interning) is redirected below
    int cacheable = 1;
    if (istuple) {
        size_t i;
        for (i = 0; i < ntp; i++) {
            jl_value_t *pi = iparams[i];
            if (jl_is_vararg(pi) && jl_unwrap_vararg(pi) == jl_bottom_type) {
                jl_value_t *va1 = jl_unwrap_vararg_num(pi);
                if (va1 && jl_is_long(va1)) {
                    ssize_t nt = jl_unbox_long(va1);
                    if (nt == 0)
                        va1 = NULL;
                    else
                        pi = jl_bottom_type; // trigger errorf below
                }
                // This imposes an implicit constraint that va1==0,
                // so we keep the Vararg if it has a TypeVar
                if (va1 == NULL) {
                    p = NULL;
                    ntp -= 1;
                    assert(i == ntp);
                    break;
                }
            }
            if (pi == jl_bottom_type) {
                if (nothrow)
                    return NULL;
                jl_errorf("Tuple field type cannot be Union{}");
            }
            if (cacheable && !jl_is_concrete_type(pi))
                cacheable = 0;
        }
    }
    else {
        size_t i;
        for (i = 0; cacheable && i < ntp; i++)
            if (jl_has_free_typevars(iparams[i]))
                cacheable = 0;
    }
    // if applicable, check the cache first for a match
    if (cacheable) {
        jl_value_t *lkup = (jl_value_t*)lookup_type(tn, iparams, ntp);
        if (lkup == NULL)
            lkup = lookup_deferred_type(dcache, tn, iparams, ntp);
        if (lkup != NULL)
            return lkup;
    }
    // if some normalization might be needed, do that now
    // it is probably okay to mutate iparams, and we only store globally rooted objects here
    if (check) {
        size_t i;
        for (i = 0; i < ntp; i++) {
            jl_value_t *pi = iparams[i];
            if (pi == jl_bottom_type)
                continue;
            if (jl_is_datatype(pi))
                continue;
            if (jl_is_vararg(pi))
                // This is already handled in jl_wrap_vararg instead
                continue;
            if (!cacheable && jl_has_free_typevars(pi))
                continue;
            // normalize types equal to wrappers
            jl_value_t *tw = extract_wrapper(pi);
            if (tw && tw != pi &&
                    !jl_has_free_typevars(pi) && jl_types_equal(pi, tw)) {
                if (p)
                    jl_gc_write(p, iparams[i], jl_value_t, tw);
                else
                    iparams[i] = tw;
            }
        }
    }
    // then check the cache again, if applicable
    if (cacheable) {
        jl_value_t *lkup = (jl_value_t*)lookup_type(tn, iparams, ntp);
        if (lkup != NULL)
            return lkup;
    }
    jl_value_t *stack_lkup = lookup_type_stack(stack, dt, ntp, iparams);
    if (stack_lkup)
        return stack_lkup;

    // check parameters against bounds in type definition
    // for whether this is even valid
    if (check && !istuple) {
        assert(ntp > 0);
        if (check_datatype_parameters(tn, iparams, ntp, nothrow))
            return NULL;
    }
    else if (ntp == 0 && jl_emptytuple_type != NULL) {
        // empty tuple type case
        assert(istuple);
        return (jl_value_t*)jl_emptytuple_type;
    }

    jl_datatype_t *ndt = NULL;
    JL_GC_PUSH2(&p, &ndt);

    jl_value_t *last = iparams[ntp - 1];
    if (istuple && ntp > 0 && jl_is_vararg(last)) {
        // normalize Tuple{..., Vararg{Int, 3}} to Tuple{..., Int, Int, Int}
        jl_value_t *va = jl_unwrap_unionall(last);
        jl_value_t *va0 = jl_unwrap_vararg(va), *va1 = jl_unwrap_vararg_num(va);
        // return same `Tuple` object for types equal to it
        if (ntp == 1 && va0 == (jl_value_t*)jl_any_type && !va1) {
            JL_GC_POP();
            return (jl_value_t*)jl_anytuple_type;
        }
        if (va1 && jl_is_long(va1)) {
            ssize_t nt = jl_unbox_long(va1);
            assert(nt >= 0);
            if (nt == 0 || !jl_has_free_typevars(va0)) {
                if (ntp == 1) {
                    JL_GC_POP();
                    return jl_tupletype_fill(nt, va0, 0, 0, dcache);
                }
                size_t i, l;
                p = jl_alloc_svec(ntp - 1 + nt);
                for (i = 0, l = ntp - 1; i < l; i++)
                    jl_svecset(p, i, iparams[i]);
                l = ntp - 1 + nt;
                for (; i < l; i++)
                    jl_svecset(p, i, va0);
                size_t np = jl_svec_len(p);
                jl_value_t **pp = jl_svec_data(p);
                jl_value_t *ndt = inst_datatype_inner(jl_anytuple_type, p, pp, np, NULL, NULL, check, nothrow, dcache);
                JL_GC_POP();
                return ndt;
            }
        }
    }

    if (p == NULL) {
        // slots in iparams are untracked by the GC static analyzer so it won't
        // complain, but this is used as rooting storage for normalized types
        // below so it must be rooted properly by the GC
        p = jl_alloc_svec_uninit(ntp);
        for (size_t i = 0; i < ntp; i++) {
            jl_gc_write_fresh(p, jl_svec_data(p)[i], jl_value_t, iparams[i]);
        }
        iparams = jl_svec_data(p);
    }
    assert(jl_is_svec(p) && iparams == jl_svec_data(p));

    // try to simplify some type parameters
    if (check) {
        int changed = 0;
        if (istuple) // normalization might change Tuple's, but not other types's, cacheable status
            cacheable = 1;
        size_t i;
        for (i = 0; i < ntp; i++) {
            jl_value_t *pi = iparams[i];
            jl_value_t *newp = normalize_unionalls(pi);
            if (newp != pi) {
                jl_gc_write(p, iparams[i], jl_value_t, newp);
                changed = 1;
            }
            if (istuple && cacheable && !jl_is_concrete_type(newp))
                cacheable = 0;
        }
        if (changed) {
            // If this changed something, we need to check the cache again, in
            // case we missed the match earlier before the normalizations
            //
            // e.g. return inst_datatype_inner(dt, p, iparams, ntp, stack, env, 0);
            if (cacheable) {
                jl_value_t *lkup = (jl_value_t*)lookup_type(tn, iparams, ntp);
                if (lkup == NULL)
                    lkup = lookup_deferred_type(dcache, tn, iparams, ntp);
                if (lkup != NULL) {
                    JL_GC_POP();
                    return lkup;
                }
            }
            jl_value_t *stack_lkup = lookup_type_stack(stack, dt, ntp, iparams);
            if (stack_lkup) {
                JL_GC_POP();
                return stack_lkup;
            }
        }
    }

    // Decide whether this instantiation must be deferred: instantiations
    // referencing the in-flight typegroup are canonicalized against `dcache`
    // and published only once the group is validated.
    int defer = 0;
    if (dcache != NULL && cacheable) {
        for (size_t i = 0; i < ntp; i++) {
            if (type_references_deferred(iparams[i], dcache)) {
                defer = 1;
                break;
            }
        }
    }

    // try to reduce duplication in objects (if the caller didn't already check) by
    // comparing them against a list of objects already known to be globally rooted and
    // swapping them as possible
    if (check && jl_global_roots_list != NULL) {
        for (size_t i = 0; i < ntp; i++) {
            jl_value_t *pi = iparams[i];
            if (cacheable || !jl_has_free_typevars(pi)) {
                pi = jl_as_global_root(pi, cacheable && !defer);
                if (pi != NULL) {
                    jl_gc_write(p, iparams[i], jl_value_t, pi);
                }
            }
        }
    }

    ndt = jl_new_uninitialized_datatype();

    // now that most allocations are done
    // acquire the write lock now that we know we need a new object
    // since we're going to immediately leak it globally via the instantiation stack
    if (cacheable && !defer) {
        JL_LOCK(&typecache_lock); // Might GC
        jl_value_t *lkup = (jl_value_t*)lookup_type(tn, iparams, ntp);
        if (lkup) {
            JL_UNLOCK(&typecache_lock); // Might GC
            JL_GC_POP();
            return lkup;
        }
    }

    // create and initialize new type
    ndt->isprimitivetype = dt->isprimitivetype;
    // Usually dt won't have ismutationfree set at this point, but it is
    // overridden for `Type`, which we handle here.
    ndt->ismutationfree = dt->ismutationfree;
    // associate these parameters with the new type on
    // the stack, in case one of its field types references it.
    top.tt = (jl_datatype_t*)ndt;
    top.prev = stack;
    stack = &top;
    jl_gc_write(ndt, ndt->name, jl_typename_t, tn);
    ndt->super = NULL;
    jl_gc_write(ndt, ndt->parameters, jl_svec_t, p);
    ndt->types = NULL; // to be filled in below
    int invalid = 0;
    if (istuple) {
        jl_gc_write(ndt, ndt->types, jl_svec_t, p); // TODO: this may need to filter out certain types
    }
    else if (isnamedtuple) {
        jl_value_t *names_tup = jl_svecref(p, 0);
        jl_value_t *values_tt = jl_svecref(p, 1);
        if (!jl_has_free_typevars(names_tup) && !jl_has_free_typevars(values_tt)) {
            if (!jl_is_tuple(names_tup)) {
                if (!nothrow)
                    jl_type_error_rt("NamedTuple", "names", (jl_value_t*)jl_anytuple_type, names_tup);
                invalid = 1;
            }
            size_t nf = jl_nfields(names_tup);
            for (size_t i = 0; i < nf; i++) {
                jl_value_t *ni = jl_fieldref(names_tup, i);
                if (!jl_is_symbol(ni)) {
                    if (!nothrow)
                        jl_type_error_rt("NamedTuple", "name", (jl_value_t*)jl_symbol_type, ni);
                    invalid = 1; break;
                }
                for (size_t j = 0; j < i; j++) {
                    if (ni == jl_fieldref_noalloc(names_tup, j)) {
                        if (!nothrow)
                            jl_errorf("duplicate field name in NamedTuple: \"%s\" is not unique", jl_symbol_name((jl_sym_t*)ni));
                        invalid = 1; break;
                    }
                }
                if (invalid) break;
            }
            if (values_tt == jl_bottom_type && nf > 0) {
                jl_gc_write(ndt, ndt->types, jl_svec_t, jl_svec_fill(nf, jl_bottom_type));
            }
            else {
                if (!jl_is_datatype(values_tt)) {
                    // reachable for `NamedTuple{(), Union{}}`, e.g. from type intersection
                    if (!nothrow)
                        jl_error("NamedTuple field type must be a tuple datatype");
                    invalid = 1;
                }
                else {
                    if (jl_is_va_tuple((jl_datatype_t*)values_tt) || jl_nparams(values_tt) != nf) {
                        if (!nothrow)
                            jl_error("NamedTuple names and field types must have matching lengths");
                        invalid = 1;
                    }
                    jl_gc_write(ndt, ndt->types, jl_svec_t, ((jl_datatype_t*)values_tt)->parameters);
                }
            }
        }
        else {
            ndt->types = jl_emptysvec; // XXX: this is essentially always incorrect
        }
    }
    else if (tn == jl_genericmemoryref_typename || tn == jl_genericmemory_typename) {
        jl_value_t *isatomic = jl_svecref(p, 0);
        if (!jl_is_typevar(isatomic) && !jl_is_symbol(isatomic)) {
            if (!nothrow)
                jl_type_error_rt("GenericMemory", "isatomic parameter", (jl_value_t*)jl_symbol_type, isatomic);
            invalid = 1;
        }
        jl_value_t *addrspace = jl_svecref(p, 2);
        if (!jl_is_typevar(addrspace) && !jl_is_addrspace(addrspace)) {
            if (!nothrow)
                jl_type_error_rt("GenericMemory", "addrspace parameter", (jl_value_t*)jl_addrspace_type, addrspace);
            invalid = 1;
        }
    }

    if (nothrow && invalid) {
        if (cacheable && !defer)
            JL_UNLOCK(&typecache_lock);
        JL_GC_POP();
        return NULL;
    }
    jl_datatype_t *primarydt = ((jl_datatype_t*)jl_unwrap_unionall(tn->wrapper));
    jl_precompute_memoized_dt(ndt, cacheable);
    // for deferred instantiations, the layout is computed at publication:
    // the group's types are still incomplete here, and computing it now
    // would bake in wrong assumptions (cf. #40050)
    if (primarydt->layout && !defer)
        jl_compute_field_offsets(ndt);

    // A definition whose supertype declaration recursively applies the type
    // being defined at structurally increasing parameters (issue #61347, e.g.
    // `struct S{T} <: A{S{Tuple{T}}} end`) has an infinite supertype graph:
    // eagerly instantiating each level's supertype creates the next level.
    // When another instantiation of this typename is already in flight above
    // this one (`stack` has `ndt` itself on top) and the supertype template
    // mentions the typename, defer the supertype and complete it lazily, one
    // level per demand (`jl_datatype_compute_super`). Same-parameter
    // self-references never get here (`lookup_type_stack` ties that knot),
    // so ordinary recursive types are unaffected. Field types stay eager: a
    // concrete type must publish with its layout, and only the supertype
    // declaration can force an infinite graph through abstract levels.
    int defer_super = check && !istuple && !isnamedtuple && dt->super != NULL &&
        typename_on_stack(top.prev, tn) &&
        typename_occurs_in((jl_value_t*)primarydt->super, tn);
    if (istuple || isnamedtuple) {
        ndt->super = jl_any_type;
    }
    else if (defer_super) {
        // deferred (see above)
    }
    else if (dt->super) {
        jl_value_t *super = inst_type_w_((jl_value_t*)dt->super, env, stack, check, nothrow, dcache);
        if (nothrow && super == NULL) {
            if (cacheable && !defer)
                JL_UNLOCK(&typecache_lock);
            JL_GC_POP();
            return NULL;
        }
        jl_gc_write(ndt, ndt->super, jl_datatype_t, (jl_datatype_t *)super);
    }
    jl_svec_t *ftypes = dt->types;
    if (ftypes == NULL)
        ftypes = primarydt->types;
    if (ftypes == NULL || dt->super == NULL) {
        // in the process of creating this type definition:
        // need to instantiate the super and types fields later
        if (tn->partial == NULL) {
            jl_gc_write(tn, tn->partial, jl_array_t, jl_alloc_vec_any(0));
        }
        jl_array_ptr_1d_push(tn->partial, (jl_value_t*)ndt);
    }
    else if (!isnamedtuple && !istuple) {
        assert(ftypes != jl_emptysvec || jl_field_names(ndt) == jl_emptysvec);
        assert(ftypes == jl_emptysvec || !ndt->name->abstract);
        if (ftypes == jl_emptysvec) {
            ndt->types = ftypes;
        }
        else if (cacheable) {
            // recursively instantiate the types of the fields
            if (dt->types == NULL)
                jl_gc_write(ndt, ndt->types, jl_svec_t, compute_fieldtypes_(ndt, stack, cacheable && !defer, dcache));
            else
                jl_gc_write(ndt, ndt->types, jl_svec_t, inst_ftypes(ftypes, env, stack, cacheable && !defer, dcache));
        }
    }

    // now publish the finished result
    // XXX: if the stack was used, this will publish in the wrong order,
    // leading to incorrect layouts and data races (#40050: the A{T} should be
    // an isbitstype singleton of size 0)
    if (cacheable) {
        if (defer) {
            // record for publication once the typegroup is validated; the
            // layout is computed at publication (see above)
            jl_array_ptr_1d_push(dcache->list, (jl_value_t*)ndt);
            ptrhash_put(&dcache->set, ndt, ndt);
        }
        else {
            if (ndt->layout == NULL && ndt->types != NULL && ndt->isconcretetype)
                jl_compute_field_offsets(ndt);
            jl_cache_type_(ndt);
            JL_UNLOCK(&typecache_lock); // Might GC
        }
    }

    JL_GC_POP();
    return (jl_value_t*)ndt;
}
```
-/
def instDatatypeInner (n : Nat) (T : Types) (ops : Ops) (name : String) (iparams : List Val)
    (check : Bool) (nothrow : Nat) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let istuple := name == tupleName
    let isnamedtuple := name == "Core.NamedTuple"
    let mut ps := iparams
    -- check if type cache will be applicable
    let mut cacheable := true
    if istuple then
      let mut kept := #[]
      for p0 in ps do
        let mut p := p0
        if p.isVararg && p.unwrapVararg == .bottom then
          let mut va1 := p.varargN?
          if let some (.long nt) := va1 then
            if nt == 0 then va1 := none else p := .bottom
          -- This imposes an implicit constraint that va1==0,
          -- so we keep the Vararg if it has a TypeVar
          if va1.isNone then break
        if p == .bottom then
          if nothrow != 0 then return none
          throw "Tuple field type cannot be Union{}"
        if cacheable && !(← isConcreteType T p) then cacheable := false
        kept := kept.push p0
      ps := kept.toList
    else
      cacheable := !ps.any Val.hasFreeTypevars
    -- if some normalization might be needed, do that now
    if check then
      let mut out := #[]
      for p in ps do
        let mut p := p
        if !(p == .bottom || p.isDatatype || p.isVararg || (!cacheable && p.hasFreeTypevars)) then
          -- normalize types equal to wrappers
          if let some tw ← extractWrapper n T p then
            if tw != p && !p.hasFreeTypevars then
              if ← ops.typesEqual p tw then p := tw
        out := out.push p
      ps := out.toList
    -- check parameters against bounds in type definition
    if check && !istuple then
      if !(← checkDatatypeParameters n T ops name ps nothrow) then return none
    else if ps.isEmpty then
      return some emptytupleType
    if istuple then
      if let some last := ps.getLast? then
        if last.isVararg then
          -- normalize Tuple{..., Vararg{Int, 3}} to Tuple{..., Int, Int, Int}
          let va0 := last.unwrapVararg
          let va1 := last.varargN?
          -- return same `Tuple` object for types equal to it
          if ps.length == 1 && va0 == anyType && va1.isNone then return some anytupleType
          if let some (.long nt) := va1 then
            if nt == 0 || !va0.hasFreeTypevars then
              if ps.length == 1 then return ← tupletypeFill n T ops nt.toNat va0 false 0
              return ← instDatatypeInner n T ops tupleName
                (ps.dropLast ++ List.replicate nt.toNat va0) check nothrow
    -- try to simplify some type parameters
    if check then
      ps ← ps.mapM (normalizeUnionalls n T ops)
    if isnamedtuple then
      let [namesTup, valuesTt] := ps | throw "NamedTuple: wrong number of parameters"
      if !namesTup.hasFreeTypevars && !valuesTt.hasFreeTypevars then
        let .imm namesTy names := namesTup | do
          if nothrow != 0 then return none
          throw s!"TypeError: in NamedTuple, in names, expected Tuple, got {repr namesTup}"
        if !namesTy.isTupleType then
          if nothrow != 0 then return none
          throw s!"TypeError: in NamedTuple, in names, expected Tuple, got {repr namesTup}"
        let mut seen : List Val := []
        for ni in names do
          if !ni.isSymbol then
            if nothrow != 0 then return none
            throw s!"TypeError: in NamedTuple, in name, expected Symbol, got {repr ni}"
          if seen.contains ni then
            if nothrow != 0 then return none
            let .symbol s := ni | throw "NamedTuple: expected Symbol"
            throw s!"duplicate field name in NamedTuple: \"{s}\" is not unique"
          seen := ni :: seen
        if valuesTt != .bottom || names.isEmpty then
          if !valuesTt.isDatatype then
            if nothrow != 0 then return none
            throw "NamedTuple field type must be a tuple datatype"
          if valuesTt.isVaTuple || valuesTt.nparams != names.length then
            if nothrow != 0 then return none
            throw "NamedTuple names and field types must have matching lengths"
    else if name == "Core.GenericMemoryRef" || name == "Core.GenericMemory" then
      let [isatomic, _, addrspace] := ps | throw s!"{name}: wrong number of parameters"
      if !isatomic.isTypevar && !isatomic.isSymbol then
        if nothrow != 0 then return none
        throw s!"TypeError: in GenericMemory, in isatomic parameter, expected Symbol, got {repr isatomic}"
      if !addrspace.isTypevar && (typeOf addrspace).name? != some "Core.AddrSpace" then
        if nothrow != 0 then return none
        throw s!"TypeError: in GenericMemory, in addrspace parameter, expected Core.AddrSpace, got {repr addrspace}"
    return some (.datatype name ps)

/-- `check_datatype_parameters`; `true` when the parameters are valid (C returns 0).

Julia source: src/jltypes.c:2139-2190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int check_datatype_parameters(jl_typename_t *tn, jl_value_t **params, size_t np, int nothrow) JL_CANSAFEPOINT
{
    jl_value_t *wrapper = tn->wrapper;
    jl_value_t **bounds;
    JL_GC_PUSHARGS(bounds, np*2);
    int i = 0;
    while (jl_is_unionall(wrapper)) {
        jl_tvar_t *tv = ((jl_unionall_t*)wrapper)->var;
        bounds[i++] = tv->lb;
        bounds[i++] = tv->ub;
        wrapper = ((jl_unionall_t*)wrapper)->body;
    }
    assert(i == np*2);
    wrapper = tn->wrapper;
    for (i = 0; i < np; i++) {
        assert(jl_is_unionall(wrapper));
        jl_tvar_t *tv = ((jl_unionall_t*)wrapper)->var;
        if (!within_typevar(params[i], bounds[2*i], bounds[2*i+1])) {
            if (nothrow) {
                JL_GC_POP();
                return 1;
            }
            if (tv->lb != bounds[2*i] || tv->ub != bounds[2*i+1])
                // pass a new version of `tv` containing the instantiated bounds
                tv = jl_new_typevar(tv->name, bounds[2*i], bounds[2*i+1]);
            JL_GC_PUSH1(&tv);
            jl_type_error_rt(jl_symbol_name(tn->name), jl_symbol_name(tv->name), (jl_value_t*)tv, params[i]);
        }
        int j;
        for (j = 2*i + 2; j < 2*np; j++) {
            jl_value_t *bj = bounds[j];
            if (bj != (jl_value_t*)jl_any_type && bj != jl_bottom_type) {
                int isub = j & 1;
                // use different nothrow level for lb and ub substitution.
                // TODO: This assuming the top instantiation could only start with
                // `nothrow == 2` or `nothrow == 0`. If `nothrow` is initially set to 1
                // then we might miss some inner error, perhaps the normal path should
                // also follow this rule？
                jl_value_t *nb = jl_substitute_var_nothrow(bj, tv, params[i], nothrow ? (isub ? 2 : 1) : 0 );
                if (nb == NULL) {
                    assert(nothrow);
                    JL_GC_POP();
                    return 1;
                }
                bounds[j] = nb;
            }
        }
        wrapper = ((jl_unionall_t*)wrapper)->body;
    }
    JL_GC_POP();
    return 0;
}
```
-/
def checkDatatypeParameters (n : Nat) (T : Types) (ops : Ops) (name : String)
    (params : List Val) (nothrow : Nat) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let vars := wrapperVars (← T.typename name).wrapper
    if vars.length != params.length then throw s!"{name}: wrong number of parameters"
    let mut bounds : Array Val := #[]
    for v in vars do
      bounds := (bounds.push v.tvLb).push v.tvUb
    for h : i in [0:params.length] do
      let tv := vars[i]!
      let p := params[i]
      if !(← withinTypevar ops p bounds[2*i]! bounds[2*i+1]!) then
        if nothrow != 0 then return false
        let .typevar _ tvname _ _ := tv | throw "check_datatype_parameters: expected TypeVar"
        let tv ← if tv.tvLb != bounds[2*i]! || tv.tvUb != bounds[2*i+1]! then
            newTypevar tvname bounds[2*i]! bounds[2*i+1]!
          else pure tv
        throw s!"TypeError: in {(moduleAndName name).2}, in {repr tv}, got {repr p}"
      for j in [2*i+2:2*params.length] do
        let bj := bounds[j]!
        if bj != anyType && bj != .bottom then
          -- use different nothrow level for lb and ub substitution.
          let isub := j % 2 == 1
          let lvl := if nothrow != 0 then (if isub then 2 else 1) else 0
          let some nb ← substituteVarNothrow n T ops bj tv p lvl | return false
          bounds := bounds.set! j nb
    return true

/-- `jl_substitute_var_nothrow`

Julia source: src/jltypes.c:1745-1752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_substitute_var_nothrow(jl_value_t *t, jl_tvar_t *var, jl_value_t *val, int nothrow)
{
    if (val == (jl_value_t*)var)
        return t;
    nothrow = jl_is_typevar(val) ? 0 : nothrow;
    jl_typeenv_t env = { var, val, NULL };
    return inst_type_w_(t, &env, NULL, 1, nothrow, 0);
}
```
-/
def substituteVarNothrow (n : Nat) (T : Types) (ops : Ops) (t var val : Val) (nothrow : Nat) :
    CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if val == var then return some t
    let nothrow := if val.isTypevar then 0 else nothrow
    let some id := var.tvId | throw "substitute_var: not a TypeVar"
    instTypeW n T ops t [(id, val)] true nothrow

/-- `normalize_unionalls`

Julia source: src/jltypes.c:2277-2326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *normalize_unionalls(jl_value_t *t) JL_CANSAFEPOINT
{
    if (jl_is_uniontype(t)) {
        jl_uniontype_t *u = (jl_uniontype_t*)t;
        jl_value_t *a = NULL;
        jl_value_t *b = NULL;
        JL_GC_PUSH2(&a, &b);
        a = normalize_unionalls(u->a);
        b = normalize_unionalls(u->b);
        if (a != u->a || b != u->b) {
            t = jl_new_struct(jl_uniontype_type, a, b);
        }
        JL_GC_POP();
    }
    else if (jl_is_typeeq(t)) {
        jl_typeeq_t *te = (jl_typeeq_t*)t;
        jl_value_t *T = normalize_unionalls(te->T);
        JL_GC_PUSH1(&T);
        if (T != te->T && jl_typeof(T) == jl_typeof(te->T))
            t = (jl_value_t*)jl_wrap_Type(T);
        JL_GC_POP();
    }
    else if (jl_is_typeegal(t)) {
        // `TypeEgal{T}` pins `T` by object identity: substituting a normalized
        // (`==`-equal but non-egal) rep would change which object the kind
        // claims its instance is
    }
    else if (jl_is_unionall(t)) {
        jl_unionall_t *u = (jl_unionall_t*)t;
        jl_value_t *body = normalize_unionalls(u->body);
        JL_GC_PUSH2(&body, &t);
        if (body != u->body) {
            t = jl_new_struct(jl_unionall_type, u->var, body);
            u = (jl_unionall_t*)t;
        }

        if (u->var->lb == u->var->ub || may_substitute_ub(body, u->var)) {
            body = (jl_value_t*)u;
            JL_TRY {
                t = jl_instantiate_unionall(u, u->var->ub);
            }
            JL_CATCH {
                // just skip normalization
                // (may happen for bounds inconsistent with the wrapper's bounds)
            }
        }
        JL_GC_POP();
    }
    return t;
}
```
-/
def normalizeUnionalls (n : Nat) (T : Types) (ops : Ops) (t : Val) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match t with
    | .union ua ub => do
      let a ← normalizeUnionalls n T ops ua
      let b ← normalizeUnionalls n T ops ub
      if a != ua || b != ub then return .union a b
      return t
    | .typeeq te => do
      let x ← normalizeUnionalls n T ops te
      if x != te && typeOf x == typeOf te then return ← wrapType n T ops x
      return t
    -- `TypeEgal{T}` pins `T` by object identity
    | .typeegal _ => return t
    | .unionall id nm lb ub body => do
      let nbody ← normalizeUnionalls n T ops body
      let u := if nbody != body then Val.unionall id nm lb ub nbody else t
      let var := Val.typevar id nm lb ub
      if lb == ub || (← maySubstituteUb n T nbody var) then
        -- a failure just skips normalization
        -- (may happen for bounds inconsistent with the wrapper's bounds)
        try
          return ← instantiateUnionall n T ops u ub
        catch _ =>
          return u
      return u
    | _ => return t

/-- `jl_instantiate_unionall(u, p)`

Julia source: src/jltypes.c:1722-1731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *instantiate_unionall_(jl_unionall_t *u, jl_value_t *p, jl_deferred_typecache_t *dcache)
{
    jl_typeenv_t env = { u->var, p, NULL };
    return inst_type_w_(u->body, &env, NULL, 1, 0, dcache);
}

JL_DLLEXPORT jl_value_t *jl_instantiate_unionall(jl_unionall_t *u, jl_value_t *p)
{
    return instantiate_unionall_(u, p, NULL);
}
```
-/
def instantiateUnionall (n : Nat) (T : Types) (ops : Ops) (u p : Val) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let .unionall id _ _ _ body := u | throw "instantiate_unionall: not a UnionAll"
    let some r ← instTypeW n T ops body [(id, p)] true 0 | throw "unreachable: NULL with nothrow 0"
    return r

/-- `jl_tupletype_fill`: `NTuple{n, t}`

Julia source: src/jltypes.c:2329-2356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *jl_tupletype_fill(size_t n, jl_value_t *t, int check, int nothrow, jl_deferred_typecache_t *dcache) JL_CANSAFEPOINT
{
    jl_value_t *p = NULL;
    JL_GC_PUSH1(&p);
    if (check) {
        // Since we are skipping making the Vararg and skipping checks later,
        // we inline the checks from jl_wrap_vararg here now
        if (!jl_valid_type_param(t)) {
            if (nothrow) {
                JL_GC_POP();
                return NULL;
            }
            jl_type_error_rt("Vararg", "type", (jl_value_t*)jl_type_type, t);
        }
        // jl_wrap_vararg sometimes simplifies the type, so we only do this 1 time, instead of for each n later
        t = normalize_unionalls(t);
        p = t;
        jl_value_t *tw = extract_wrapper(t);
        if (tw && t != tw && !jl_has_free_typevars(t) && jl_types_equal(t, tw))
            t = tw;
        p = t;
        check = 0; // remember that checks are already done now
    }
    p = (jl_value_t*)jl_svec_fill(n, t);
    p = jl_apply_tuple_type_v_(jl_svec_data((jl_svec_t*)p), n, (jl_svec_t*)p, check, dcache);
    JL_GC_POP();
    return p;
}
```
-/
def tupletypeFill (n : Nat) (T : Types) (ops : Ops) (len : Nat) (t : Val) (check : Bool)
    (nothrow : Nat) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut t := t
    let mut check := check
    if check then
      -- Since we are skipping making the Vararg and skipping checks later,
      -- we inline the checks from jl_wrap_vararg here now
      if !(← validTypeParam n T t) then
        if nothrow != 0 then return none
        throw s!"TypeError: in Vararg, in type, expected Type, got {repr t}"
      t ← normalizeUnionalls n T ops t
      if let some tw ← extractWrapper n T t then
        if t != tw && !t.hasFreeTypevars then
          if ← ops.typesEqual t tw then t := tw
      check := false
    instDatatypeInner n T ops tupleName (List.replicate len t) check 0

/-- `jl_wrap_vararg`; `none` is `NULL` (only when `nothrow`).

Julia source: src/jltypes.c:3313-3367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_vararg_t *jl_wrap_vararg(jl_value_t *t, jl_value_t *n, int check, int nothrow)
{
    int valid = 1;
    jl_vararg_t *vm = NULL;
    jl_task_t *ct = jl_current_task;
    JL_GC_PUSH1(&t);
    if (check) {
        if (n) {
            if (jl_is_typevar(n) || jl_is_uniontype(jl_unwrap_unionall(n))) {
                // TODO: this is disabled due to #39698; it is also inconsistent
                // with other similar checks, where we usually only check substituted
                // values and not the bounds of variables.
                /*
                jl_tvar_t *N = (jl_tvar_t*)n;
                if (valid && !(N->lb == jl_bottom_type && N->ub == (jl_value_t*)jl_any_type)) {
                    if (!nothrow)
                        jl_error("TypeVar in Vararg length must have bounds Union{} and Any");
                    invalid = 1;
                }
                */
            }
            else if (valid && !jl_is_long(n)) {
                if (!nothrow)
                    jl_type_error_rt("Vararg", "count", (jl_value_t*)jl_long_type, n);
                valid = 0;
            }
            else if (valid && jl_unbox_long(n) < 0) {
                if (!nothrow)
                    jl_errorf("Vararg length is negative: %zd", jl_unbox_long(n));
                valid = 0;
            }
        }
        if (t) {
            if (valid && !jl_valid_type_param(t)) {
                if (!nothrow)
                    jl_type_error_rt("Vararg", "type", (jl_value_t*)jl_type_type, t);
                valid = 0;
            }
            if (valid) {
                t = normalize_unionalls(t);
                jl_value_t *tw = extract_wrapper(t);
                if (tw && t != tw && !jl_has_free_typevars(t) && jl_types_equal(t, tw))
                    t = tw;
            }
        }
    }
    if (valid) {
        vm = (jl_vararg_t *)jl_gc_alloc(ct->ptls, sizeof(jl_vararg_t), jl_vararg_type);
        jl_set_typetagof(vm, jl_vararg_tag, 0);
        vm->T = t;
        vm->N = n;
    }
    JL_GC_POP();
    return vm;
}
```
-/
def wrapVararg (n : Nat) (T : Types) (ops : Ops) (t N : Option Val) (check : Bool)
    (nothrow : Nat) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut valid := true
    let mut t := t
    if check then
      if let some nv := N then
        if nv.isTypevar || nv.unwrapUnionall.isUnion then
          pure ()
        else if !nv.isLong then
          if nothrow == 0 then
            throw s!"TypeError: in Vararg, in count, expected Int64, got {repr nv}"
          valid := false
        else if let .long k := nv then
          if k < 0 then
            if nothrow == 0 then throw s!"Vararg length is negative: {k}"
            valid := false
      if let some tv := t then
        if valid && !(← validTypeParam n T tv) then
          if nothrow == 0 then
            throw s!"TypeError: in Vararg, in type, expected Type, got {repr tv}"
          valid := false
        if valid then
          let mut x ← normalizeUnionalls n T ops tv
          if let some tw ← extractWrapper n T x then
            if x != tw && !x.hasFreeTypevars then
              if ← ops.typesEqual x tw then x := tw
          t := some x
    if valid then return some (.vararg t N)
    return none

/-- `jl_type_union`

Julia source: src/jltypes.c:780-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_type_union(jl_value_t **ts, size_t n)
{
    if (n == 0)
        return (jl_value_t*)jl_bottom_type;
    size_t i;
    for (i = 0; i < n; i++) {
        jl_value_t *pi = ts[i];
        // reject the internal `Intersect` meet node (see #61917): it must not
        // be embedded into a user-visible `Union`.
        if (!(jl_is_type(pi) || jl_is_typevar(pi)))
            jl_type_error("Union", (jl_value_t*)jl_type_type, pi);
    }
    if (n == 1)
        return ts[0];

    size_t nt = count_union_components(ts, n, 1);
    jl_value_t **temp;
    JL_GC_PUSHARGS(temp, nt+1);
    size_t count = 0;
    flatten_type_union(ts, n, temp, &count, 1);
    assert(count == nt);
    size_t j;
    for (i = 0; i < nt; i++) {
        int has_free = temp[i] != NULL && jl_has_free_typevars(temp[i]);
        for (j = 0; j < nt; j++) {
            if (j != i && temp[i] && temp[j]) {
                int has_free2 = has_free | (jl_has_free_typevars(temp[j]) << 1);
                if (simple_subtype(temp[i], temp[j], has_free2, 1))
                    temp[i] = NULL;
            }
        }
    }
    isort_union(temp, nt);
    merge_vararg_unions(temp, nt);
    jl_value_t **ptu = &temp[nt];
    *ptu = jl_bottom_type;
    int k;
    for (k = (int)nt-1; k >= 0; --k) {
        if (temp[k] != NULL) {
            if (*ptu == jl_bottom_type)
                *ptu = temp[k];
            else
                *ptu = jl_new_struct(jl_uniontype_type, temp[k], *ptu);
        }
    }
    assert(*ptu != NULL);
    jl_value_t *tu = *ptu;
    JL_GC_POP();
    return tu;
}
```
-/
def typeUnion (n : Nat) (T : Types) (ops : Ops) (ts : List Val) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if ts.isEmpty then return .bottom
    for p in ts do
      -- reject the internal `Intersect` meet node (see #61917)
      if !(p.isType || p.isTypevar) then
        throw s!"TypeError: in Union, expected Type, got {repr p}"
    if let [t] := ts then return t
    let mut flat : List Val := []
    for t in ts do
      flat := flat ++ (← flattenTypeUnion n true t)
    let mut temp : Array (Option Val) := (flat.map some).toArray
    let nt := temp.size
    for i in [0:nt] do
      let hasFree := match temp[i]! with | some x => x.hasFreeTypevars | none => false
      for j in [0:nt] do
        if let (some ti, some tj) := (temp[i]!, temp[j]!) then
          if j != i then
            let hasFree2 := (if hasFree then 1 else 0) ||| (if tj.hasFreeTypevars then 2 else 0)
            if ← simpleSubtype n T ops ti tj hasFree2 true then temp := temp.set! i none
    let sorted ← isortUnion n T temp.toList
    let merged ← mergeVarargUnions n T ops sorted.toArray
    return buildUnion merged.toList

/-- `simple_subtype`; `hasfree` bit 0 is `a`, bit 1 is `b`.

Julia source: src/jltypes.c:696-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int simple_subtype(jl_value_t *a, jl_value_t *b, int hasfree, int isUnion)
{
    assert(hasfree == (jl_has_free_typevars(a) | (jl_has_free_typevars(b) << 1)));
    if (a == jl_bottom_type || b == (jl_value_t*)jl_any_type)
        return 1;
    if (jl_egal(a, b))
        return 1;
    if (hasfree == 0) {
        int mergeable = isUnion;
        if (!mergeable) // issue #24521: don't merge Type{T} where typeof(T) varies
            mergeable = !(jl_is_typeeq(a) && jl_is_typeeq(b) &&
             jl_typeof(jl_typeeq_T(a)) != jl_typeof(jl_typeeq_T(b)));
        return mergeable && jl_subtype(a, b);
    }
    if (jl_is_typevar(a)) {
        jl_value_t *na = ((jl_tvar_t*)a)->ub;
        hasfree &= (jl_has_free_typevars(na) | 2);
        return simple_subtype(na, b, hasfree, isUnion);
    }
    if (jl_is_typevar(b)) {
        jl_value_t *nb = ((jl_tvar_t*)b)->lb;
        // This branch is not valid if `b` obeys diagonal rule,
        // as it might normalize `Union` into a single `TypeVar`, e.g.
        // Tuple{Union{Int,T},T} where {T>:Int} != Tuple{T,T} where {T>:Int}
        if (is_leaf_bound(nb))
            return 0;
        hasfree &= ((jl_has_free_typevars(nb) << 1) | 1);
        return simple_subtype(a, nb, hasfree, isUnion);
    }
    if (b == (jl_value_t*)jl_typeofbottom_type) {
        // `Type{Union{}} == TypeofBottom` (the bottom object is unique). No
        // other `Type{T}` lies in a kind: its members include `UnionAll`
        // spellings of `T` (#33136).
        return jl_is_typeeq(a) && jl_typeeq_T(a) == jl_bottom_type;
    }
    return 0;
}
```
-/
def simpleSubtype (n : Nat) (T : Types) (ops : Ops) (a b : Val) (hasfree : Nat) (isUnion : Bool) :
    CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if a == .bottom || b == anyType then return true
    if ← egal n T a b then return true
    if hasfree == 0 then
      let mergeable := isUnion ||
        -- issue #24521: don't merge Type{T} where typeof(T) varies
        !(a.isTypeeq && b.isTypeeq && typeOf a.someTypeT != typeOf b.someTypeT)
      if !mergeable then return false
      return ← ops.subtype a b
    if let .typevar _ _ _ na := a then
      let hasfree := hasfree &&& ((if na.hasFreeTypevars then 1 else 0) ||| 2)
      return ← simpleSubtype n T ops na b hasfree isUnion
    if let .typevar _ _ nb _ := b then
      -- This branch is not valid if `b` obeys diagonal rule
      if ← ops.isLeafBound nb then return false
      let hasfree := hasfree &&& ((if nb.hasFreeTypevars then 2 else 0) ||| 1)
      return ← simpleSubtype n T ops a nb hasfree isUnion
    if b == typeofbottomType then
      -- `Type{Union{}} == TypeofBottom` (the bottom object is unique)
      return a.isTypeeq && a.someTypeT == .bottom
    return false

/-- `merge_vararg_unions`: merge `Union{Tuple{}, Tuple{T}, Tuple{T, T, Vararg{T}}}` into
`Tuple{Vararg{T}}`; `temp` is sorted.

Julia source: src/jltypes.c:734-778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// merge Union{Tuple{}, Tuple{T}, Tuple{T, T, Vararg{T}}} into Tuple{Vararg{T}}
// assumes temp is already sorted by number of type parameters
STATIC_INLINE void merge_vararg_unions(jl_value_t **temp, size_t nt) JL_CANSAFEPOINT
{
    for (size_t i = nt-1; i > 0; i--) {
        // match types of form Tuple{T, ..., Vararg{T}}
        jl_value_t *tt = temp[i];
        if (!(tt && jl_is_tuple_type(tt))) continue;
        size_t nfields = jl_nparams(tt);
        if (nfields <= 1) continue;
        jl_value_t *va = jl_tparam(tt, nfields-1);
        if (jl_vararg_kind(va) != JL_VARARG_UNBOUND) continue;
        jl_value_t *t = jl_unwrap_vararg(va);
        size_t min_elements = nfields-1;
        for (size_t j = 0; j < nfields-1; j++)
            if (!jl_egal(jl_tparam(tt, j), t)) goto outer_loop;

        // look for Tuple{T, T, ...} then Tuple{T, ...}, etc
        for (long j = i-1; j >= 0; j--) {
            jl_value_t *ttj = temp[j];
            if (!(ttj && jl_is_tuple_type(ttj))) break;
            size_t nfieldsj = jl_nparams(ttj);
            if (nfieldsj >= min_elements) continue;
            if (nfieldsj != min_elements-1) break;
            for (size_t k = 0; k < nfieldsj; k++)
                if (!jl_egal(jl_tparam(ttj, k), t)) goto inner_loop;

            temp[j] = NULL;
            min_elements--;
 inner_loop:
            continue;
        }

        if (min_elements == nfields-1) continue;
        jl_value_t** params;
        JL_GC_PUSHARGS(params, min_elements+1);
        for (size_t j = 0; j < min_elements; j++)
            params[j] = t;
        params[min_elements] = va;
        temp[i] = jl_apply_type((jl_value_t*)jl_tuple_type, params, min_elements+1);
        JL_GC_POP();
 outer_loop:
        continue;
    }
}
```
-/
def mergeVarargUnions (n : Nat) (T : Types) (ops : Ops) (temp : Array (Option Val)) :
    CM (Array (Option Val)) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut temp := temp
    let nt := temp.size
    for i' in (List.range (nt - 1)).reverse do
      let i := i' + 1
      -- match types of form Tuple{T, ..., Vararg{T}}
      let some tt := temp[i]! | continue
      if !tt.isTupleType then continue
      let ps := tt.params
      let nfields := ps.length
      if nfields ≤ 1 then continue
      let va := ps.getLast!
      if va.varargKind != .unbound then continue
      let t := va.unwrapVararg
      let mut minElements := nfields - 1
      let mut allSame := true
      for p in ps.dropLast do
        if !(← egal n T p t) then allSame := false; break
      if !allSame then continue
      -- look for Tuple{T, T, ...} then Tuple{T, ...}, etc
      for j in (List.range i).reverse do
        let some ttj := temp[j]! | break
        if !ttj.isTupleType then break
        let nfj := ttj.params.length
        if nfj ≥ minElements then continue
        if nfj + 1 != minElements then break
        let mut same := true
        for p in ttj.params do
          if !(← egal n T p t) then same := false; break
        if !same then continue
        temp := temp.set! j none
        minElements := minElements - 1
      if minElements == nfields - 1 then continue
      let params := List.replicate minElements t ++ [va]
      let some r ← instDatatypeInner n T ops tupleName params true 0 | throw "unreachable"
      temp := temp.set! i (some r)
    return temp
end

/-- `jl_rename_unionall`: the same UnionAll over a fresh variable.

Julia source: src/jltypes.c:1733-1743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_unionall_t *jl_rename_unionall(jl_unionall_t *u)
{
    jl_tvar_t *v = jl_new_typevar(u->var->name, u->var->lb, u->var->ub);
    jl_value_t *t = NULL;
    JL_GC_PUSH2(&v, &t);
    jl_typeenv_t env = { u->var, (jl_value_t *)v, NULL };
    t = inst_type_w_(u->body, &env, NULL, 0, 0, 0);
    t = jl_new_struct(jl_unionall_type, v, t);
    JL_GC_POP();
    return (jl_unionall_t*)t;
}
```
-/
def renameUnionall (n : Nat) (T : Types) (ops : Ops) (u : Val) : CM Val := do
  let .unionall uid nm lb ub body := u | throw "rename_unionall: not a UnionAll"
  let v ← newTypevar nm lb ub
  let .typevar vid .. := v | throw "unreachable"
  let some t ← instTypeW n T ops body [(uid, v)] false 0 | throw "unreachable: NULL with nothrow 0"
  return .unionall vid nm lb ub t

/-- `jl_substitute_var`

Julia source: src/jltypes.c:1754-1760 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_substitute_var(jl_value_t *t, jl_tvar_t *var, jl_value_t *val)
{
    if (val == (jl_value_t*)var)
        return t;
    jl_typeenv_t env = { var, val, NULL };
    return inst_type_w_(t, &env, NULL, 1, 0, 0);
}
```
-/
def substituteVar (n : Nat) (T : Types) (ops : Ops) (t var val : Val) : CM Val := do
  if val == var then return t
  let some id := var.tvId | throw "substitute_var: not a TypeVar"
  let some r ← instTypeW n T ops t [(id, val)] true 0 | throw "unreachable: NULL with nothrow 0"
  return r

/-- `jl_type_unionall(v, body)`, with deprecation warnings off (`--depwarn=no`, the default).

Julia source: src/jltypes.c:1054-1099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_type_unionall(jl_tvar_t *v, jl_value_t *body)
{
    if (jl_is_vararg(body)) {
        if (jl_options.depwarn) {
            if (jl_options.depwarn == JL_OPTIONS_DEPWARN_ERROR)
                jl_error("Wrapping `Vararg` directly in UnionAll is deprecated (wrap the tuple instead).\nYou may need to write `f(x::Vararg{T})` rather than `f(x::Vararg{<:T})` or `f(x::Vararg{T}) where T` instead of `f(x::Vararg{T} where T)`.");
            jl_printf(JL_STDERR, "WARNING: Wrapping `Vararg` directly in UnionAll is deprecated (wrap the tuple instead).\nYou may need to write `f(x::Vararg{T})` rather than `f(x::Vararg{<:T})` or `f(x::Vararg{T}) where T` instead of `f(x::Vararg{T} where T)`.\nTo make this warning an error, and hence obtain a stack trace, use `julia --depwarn=error`.\n");
        }
        jl_vararg_t *vm = (jl_vararg_t*)body;
        int T_has_tv = vm->T && jl_has_typevar(vm->T, v);
        int N_has_tv = vm->N && jl_has_typevar(vm->N, v);
        if (!T_has_tv && !N_has_tv) {
            return body;
        }
        if (T_has_tv && N_has_tv) {
            jl_error("Wrapping `Vararg` directly in UnionAll is disallowed if the typevar occurs in both `T` and `N`");
        }
        if (T_has_tv) {
            jl_value_t *wrapped = jl_type_unionall(v, vm->T);
            JL_GC_PUSH1(&wrapped);
            wrapped = (jl_value_t*)jl_wrap_vararg(wrapped, vm->N, 1, 0);
            JL_GC_POP();
            return wrapped;
        }
        else {
            assert(N_has_tv);
            assert(vm->N == (jl_value_t*)v);
            return (jl_value_t*)jl_wrap_vararg(vm->T, NULL, 1, 0);
        }
    }
    if (!jl_is_type(body) && !jl_is_typevar(body) && !jl_is_typeapp(body))
        jl_type_error("UnionAll", (jl_value_t*)jl_type_type, body);
    // normalize `T where T<:S` => S
    if (body == (jl_value_t*)v)
        return v->ub;
    // where var doesn't occur in body just return body
    if (jl_is_typeeq(body) && v->ub != (jl_value_t*)jl_any_type) {
        if (!jl_has_typevar(body, v))
            return body;
    }
    else if (!jl_has_typevar(body, v))
        return body;
    //if (v->lb == v->ub)  // TODO maybe
    //    return jl_substitute_var(body, v, v->ub);
    return jl_new_struct(jl_unionall_type, v, body);
}
```
-/
def typeUnionall (n : Nat) (T : Types) (ops : Ops) (v body : Val) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let .typevar vid vnm vlb vub := v | throw "type_unionall: not a TypeVar"
    if let .vararg vT vN := body then
      let tHasTv := match vT with | some t => t.hasTypevar v | none => false
      let nHasTv := match vN with | some x => x.hasTypevar v | none => false
      if !tHasTv && !nHasTv then return body
      if tHasTv && nHasTv then
        throw "Wrapping `Vararg` directly in UnionAll is disallowed if the typevar occurs in both `T` and `N`"
      if tHasTv then
        let wrapped ← typeUnionall n T ops v (vT.getD anyType)
        let some r ← wrapVararg n T ops (some wrapped) vN true 0 | throw "unreachable"
        return r
      let some r ← wrapVararg n T ops vT none true 0 | throw "unreachable"
      return r
    if !body.isType && !body.isTypevar && !body.isTypeapp then
      throw s!"TypeError: in UnionAll, expected Type, got {repr body}"
    -- normalize `T where T<:S` => S
    if body == v then return vub
    -- where var doesn't occur in body just return body
    if body.isTypeeq && vub != anyType then
      if !body.hasTypevar v then return body
    else if !body.hasTypevar v then return body
    return .unionall vid vnm vlb vub body

mutual
/-- `maybe_subtype_of_cache`

Julia source: src/jltypes.c:1440-1462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int maybe_subtype_of_cache(jl_value_t *kj, int covariant) JL_NOTSAFEPOINT
{
    jl_value_t *uw = jl_is_unionall(kj) ? jl_unwrap_unionall(kj) : kj;
    if (jl_is_datatype(uw)) {
        jl_datatype_t *dt = (jl_datatype_t*)uw;
        return dt->maybe_subtype_of_cache;
    }
    else if (jl_is_uniontype(uw)) {
        int ca = maybe_subtype_of_cache(((jl_uniontype_t*)uw)->a, covariant);
        int cb = maybe_subtype_of_cache(((jl_uniontype_t*)uw)->b, covariant);
        return ca && cb;
    }
    else if (uw == jl_bottom_type) {
        return 1;
    }
    else if (jl_is_typevar(uw) && !covariant) { // assume Tuple's bounds are always degenerate
        // TODO: improve this bound if we can prove that typeintersect(lb,ub) is a leaftype
        jl_tvar_t *tv = (jl_tvar_t*)uw;
        return tv->lb == tv->ub ||
               tv->lb != jl_bottom_type;
    }
    return 1;
}
```
-/
def maybeSubtypeOfCache (n : Nat) (kj : Val) (covariant : Bool) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let uw := if kj.isUnionall then kj.unwrapUnionall else kj
    match uw with
    | .datatype .. => dtMaybeSubtypeOfCache n uw
    | .union a b => do
      let ca ← maybeSubtypeOfCache n a covariant
      let cb ← maybeSubtypeOfCache n b covariant
      return ca && cb
    | .bottom => return true
    | .typevar _ _ lb ub =>
      -- assume Tuple's bounds are always degenerate
      if !covariant then return lb == ub || lb != .bottom
      return true
    | _ => return true

/-- `dt->maybe_subtype_of_cache` as `jl_precompute_memoized_dt` computes it; Julia sets it to 0
for `jl_anytuple_type` after construction.

Julia source: src/jltypes.c:2090-2137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void jl_precompute_memoized_dt(jl_datatype_t *dt, int cacheable)
{
    int istuple = (dt->name == jl_tuple_typename);
    dt->hasfreetypevars = 0;
    dt->maybe_subtype_of_cache = 1;
    dt->isconcretetype = !dt->name->abstract;
    dt->isdispatchtuple = istuple;
    size_t i, l = jl_nparams(dt);
    for (i = 0; i < l; i++) {
        jl_value_t *p = jl_tparam(dt, i);
        if (!dt->hasfreetypevars) {
            dt->hasfreetypevars = jl_has_free_typevars(p);
            if (dt->hasfreetypevars)
                dt->isconcretetype = 0;
        }
        if (istuple) {
            if (dt->isconcretetype)
                dt->isconcretetype = (jl_is_datatype(p) && ((jl_datatype_t*)p)->isconcretetype) ||
                    p == jl_bottom_type;
            if (dt->isdispatchtuple) {
                // a type-valued slot is a dispatch slot only in the egality form
                // `TypeEgal{T}` that `jl_inst_arg_tuple_type` produces; an equality
                // `Type{T}` slot also admits `==`-equal but non-egal arguments --
                // except `Type{Union{}}`, whose sole instance is the unique bottom
                // object (and which aliases the dispatch slot `typeof(Union{})`)
                dt->isdispatchtuple =
                    (jl_is_datatype(p) && ((!jl_is_kind(p) && ((jl_datatype_t*)p)->isconcretetype) ||
                     (p == (jl_value_t*)jl_typeofbottom_type))) ||
                    jl_is_typeegal(p) ||
                    (jl_is_typeeq(p) && jl_typeeq_T(p) == jl_bottom_type);
            }
        }
        if (jl_is_vararg(p))
            p = ((jl_vararg_t*)p)->T;
        if (istuple && dt->has_concrete_subtype) {
            // tuple types like Tuple{:x} and Tuple{Union{}} cannot have instances
            if (p && !jl_is_type(p) && !jl_is_typevar(p))
                dt->has_concrete_subtype = 0;
            if (p == jl_bottom_type)
                dt->has_concrete_subtype = 0;
        }
        if (dt->maybe_subtype_of_cache) {
            dt->maybe_subtype_of_cache = !p || maybe_subtype_of_cache(p, istuple) || !jl_has_free_typevars(p);
        }
    }
    assert(dt->isconcretetype || dt->isdispatchtuple ? dt->maybe_subtype_of_cache : 1);
    dt->hash = typekey_hash(dt->name, jl_svec_data(dt->parameters), l, cacheable);
}
```

Julia source: src/jltypes.c:3800-3803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    // fix some miscomputed values, since we didn't know this was going to be a Tuple in jl_precompute_memoized_dt
    jl_tuple_typename->wrapper = (jl_value_t*)jl_anytuple_type; // remove UnionAll wrappers
    jl_anytuple_type->isconcretetype = 0;
    jl_anytuple_type->maybe_subtype_of_cache = 0;
```
-/
def dtMaybeSubtypeOfCache (n : Nat) (dt : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if dt == anytupleType then return false
    let .datatype name ps := dt | return false
    let istuple := name == tupleName
    for p in ps do
      let p := if p.isVararg then p.varargT? else some p
      match p with
      | none => pure ()
      | some p =>
        if !(← maybeSubtypeOfCache n p istuple) && p.hasFreeTypevars then return false
    return true
end

/-- `has_concrete_supertype`

Julia source: src/jltypes.c:1464-1503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
// compute whether kj might have a supertype which is actually concrete
static int has_concrete_supertype(jl_value_t *kj) JL_NOTSAFEPOINT
{
    jl_value_t *uw = jl_is_unionall(kj) ? jl_unwrap_unionall(kj) : kj;
    if (jl_is_datatype(uw)) {
        jl_datatype_t *dt = (jl_datatype_t*)uw;
        if (dt->name->abstract)
            return 0;
        if (!dt->maybe_subtype_of_cache)
            return 0;
        if (dt->name == jl_tuple_typename) {
            // check tuple parameters recursively for has_concrete_supertype
            size_t i, n = jl_nparams(dt);
            for (i = 0; i < n; i++) {
                jl_value_t *p = jl_tparam(dt, i);
                if (jl_is_vararg(p))
                    p = jl_unwrap_vararg(p);
                if (!has_concrete_supertype(p))
                    return 0;
            }
        }
        return 1;
    }
    else if (jl_is_uniontype(uw)) {
        int ca = has_concrete_supertype(((jl_uniontype_t*)uw)->a);
        int cb = has_concrete_supertype(((jl_uniontype_t*)uw)->b);
        return ca && cb;
    }
    else if (jl_is_some_Type(uw)) {
        return 1;
    }
    else if (uw == jl_bottom_type) {
        return 1;
    }
    else if (jl_is_typevar(uw)) {
        jl_tvar_t *tv = (jl_tvar_t*)uw;
        return has_concrete_supertype(tv->ub);
    }
    return 0;
}
```
-/
def hasConcreteSupertype (n : Nat) (T : Types) (kj : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let uw := if kj.isUnionall then kj.unwrapUnionall else kj
    match uw with
    | .datatype name ps => do
      if (← T.typename name).abstract then return false
      if !(← dtMaybeSubtypeOfCache n uw) then return false
      if name == tupleName then
        -- check tuple parameters recursively for has_concrete_supertype
        for p in ps do
          let p := if p.isVararg then p.unwrapVararg else p
          if !(← hasConcreteSupertype n T p) then return false
      return true
    | .union a b => do
      let ca ← hasConcreteSupertype n T a
      let cb ← hasConcreteSupertype n T b
      return ca && cb
    | .typeeq _ | .typeegal _ => return true
    | .bottom => return true
    | .typevar _ _ _ ub => hasConcreteSupertype n T ub
    | _ => return false

/-- `dt->has_concrete_subtype`. A concrete DataType's value is final after its layout is
computed (`src/datatype.c:699-708`), so it is read from the recorded or derived layout. Otherwise only the
construction-time rule applies: a Tuple with a value or `Union{}` parameter has no instances.

Julia source: src/jltypes.c:2120-2130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            }
        }
        if (jl_is_vararg(p))
            p = ((jl_vararg_t*)p)->T;
        if (istuple && dt->has_concrete_subtype) {
            // tuple types like Tuple{:x} and Tuple{Union{}} cannot have instances
            if (p && !jl_is_type(p) && !jl_is_typevar(p))
                dt->has_concrete_subtype = 0;
            if (p == jl_bottom_type)
                dt->has_concrete_subtype = 0;
        }
```
-/
def hasConcreteSubtype (n : Nat) (T : Types) (dt : Val) : CM Bool := do
  let .datatype name ps := dt | return false
  if ← isConcreteType T dt then return (← layoutOf n T dt).concreteSubtype
  if name != tupleName then return true
  for p in ps do
    let p := if p.isVararg then p.varargT? else some p
    if let some p := p then
      -- tuple types like Tuple{:x} and Tuple{Union{}} cannot have instances
      if !p.isType && !p.isTypevar then return false
      if p == .bottom then return false
  return true

/-- `jl_type_equality_is_identity`

Julia source: src/jltypes.c:1505-1523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_type_equality_is_identity(jl_value_t *t1, jl_value_t *t2) JL_NOTSAFEPOINT
{
    int c1 = jl_is_concrete_type(t1);
    int c2 = jl_is_concrete_type(t2);
    if (c1 && c2) {
        if (((jl_datatype_t*)t1)->name != jl_tuple_typename)
            return 1;
        if (((jl_datatype_t*)t2)->name != jl_tuple_typename)
            return 1;
        if (((jl_datatype_t*)t1)->has_concrete_subtype && ((jl_datatype_t*)t2)->has_concrete_subtype)
            return 1;
        // e.g. Tuple{Union{}} and Tuple{Int} are both concrete!
    }
    if (c1 && !has_concrete_supertype(t2))
        return 1;
    if (c2 && !has_concrete_supertype(t1))
        return 1;
    return 0;
}
```
-/
def typeEqualityIsIdentity (n : Nat) (T : Types) (t1 t2 : Val) : CM Bool := do
  let c1 ← isConcreteType T t1
  let c2 ← isConcreteType T t2
  if c1 && c2 then
    if t1.name? != some tupleName then return true
    if t2.name? != some tupleName then return true
    if ← hasConcreteSubtype n T t1 then
      if ← hasConcreteSubtype n T t2 then return true
    -- e.g. Tuple{Union{}} and Tuple{Int} are both concrete!
  if c1 then
    if !(← hasConcreteSupertype n T t2) then return true
  if c2 then
    if !(← hasConcreteSupertype n T t1) then return true
  return false

/-- `simple_subtype2`: bit 0 is `a <: b`, bit 1 is `b <: a`.

Julia source: src/jltypes.c:831-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int simple_subtype2(jl_value_t *a, jl_value_t *b, int hasfree, int isUnion) JL_CANSAFEPOINT
{
    assert(hasfree == (jl_has_free_typevars(a) | (jl_has_free_typevars(b) << 1)));
    int subab = 0, subba = 0;
    if (jl_egal(a, b)) {
        subab = subba = 1;
    }
    else if (a == jl_bottom_type || b == (jl_value_t*)jl_any_type) {
        subab = 1;
    }
    else if (b == jl_bottom_type || a == (jl_value_t*)jl_any_type) {
        subba = 1;
    }
    else if (hasfree != 0) {
        subab = simple_subtype(a, b, hasfree, isUnion);
        subba = simple_subtype(b, a, ((hasfree & 2) >> 1) | ((hasfree & 1) << 1), isUnion);
    }
    else if (jl_is_typeeq(a) && jl_is_typeeq(b) &&
             jl_typeof(jl_typeeq_T(a)) != jl_typeof(jl_typeeq_T(b))) {
        // issue #24521: don't merge Type{T} where typeof(T) varies
    }
    else if (jl_typeof(a) == jl_typeof(b) && jl_types_struct_equiv(a, b)) {
        subab = subba = 1;
    }
    else {
        subab = jl_subtype(a, b);
        subba = jl_subtype(b, a);
    }
    return subab | (subba<<1);
}
```
-/
def simpleSubtype2 (n : Nat) (T : Types) (ops : Ops) (a b : Val) (hasfree : Nat)
    (isUnion : Bool) : CM Nat := do
  let mut subab := false
  let mut subba := false
  if ← egal n T a b then
    subab := true
    subba := true
  else if a == .bottom || b == anyType then
    subab := true
  else if b == .bottom || a == anyType then
    subba := true
  else if hasfree != 0 then
    subab ← simpleSubtype n T ops a b hasfree isUnion
    subba ← simpleSubtype n T ops b a (((hasfree &&& 2) >>> 1) ||| ((hasfree &&& 1) <<< 1)) isUnion
  else if a.isTypeeq && b.isTypeeq && typeOf a.someTypeT != typeOf b.someTypeT then
    -- issue #24521: don't merge Type{T} where typeof(T) varies
    pure ()
  else if typeOf a == typeOf b && (← typesStructEquiv n T a b) then
    subab := true
    subba := true
  else
    subab ← ops.subtype a b
    subba ← ops.subtype b a
  return (if subab then 1 else 0) ||| (if subba then 2 else 0)

/-- `simple_union`

Julia source: src/jltypes.c:862-934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *simple_union(jl_value_t *a, jl_value_t *b)
{
    size_t nta = count_union_components(&a, 1, 1);
    size_t ntb = count_union_components(&b, 1, 1);
    size_t nt = nta + ntb;
    jl_value_t **temp;
    JL_GC_PUSHARGS(temp, nt+1);
    size_t count = 0;
    flatten_type_union(&a, 1, temp, &count, 1);
    flatten_type_union(&b, 1, temp, &count, 1);
    assert(count == nt);
    size_t i, j;
    size_t ra = nta, rb = ntb;
    // first remove cross-redundancy and check if `a >: b` or `a <: b`.
    for (i = 0; i < nta; i++) {
        if (temp[i] == NULL) continue;
        int has_free = jl_has_free_typevars(temp[i]);
        for (j = nta; j < nt; j++) {
            if (temp[j] == NULL) continue;
            int has_free2 = has_free | (jl_has_free_typevars(temp[j]) << 1);
            int subs = simple_subtype2(temp[i], temp[j], has_free2, 0);
            int subab = subs & 1, subba = subs >> 1;
            if (subab) {
                temp[i] = NULL;
                if (!subba) ra = 0;
                count--;
                break;
            }
            else if (subba) {
                temp[j] = NULL;
                rb = 0;
                count--;
            }
        }
    }
    if (count == ra) {
        JL_GC_POP();
        return a;
    }
    if (count == rb) {
        JL_GC_POP();
        return b;
    }
    // then remove self-redundancy
    for (i = 0; i < nt; i++) {
        int has_free = temp[i] != NULL && jl_has_free_typevars(temp[i]);
        size_t jmin = i < nta ? 0 : nta;
        size_t jmax = i < nta ? nta : nt;
        for (j = jmin; j < jmax; j++) {
            if (j != i && temp[i] && temp[j]) {
                int has_free2 = has_free | (jl_has_free_typevars(temp[j]) << 1);
                if (simple_subtype(temp[i], temp[j], has_free2, 0))
                    temp[i] = NULL;
            }
        }
    }
    isort_union(temp, nt);
    merge_vararg_unions(temp, nt);
    temp[nt] = jl_bottom_type;
    size_t k;
    for (k = nt; k-- > 0; ) {
        if (temp[k] != NULL) {
            if (temp[nt] == jl_bottom_type)
                temp[nt] = temp[k];
            else
                temp[nt] = jl_new_struct(jl_uniontype_type, temp[k], temp[nt]);
        }
    }
    assert(temp[nt] != NULL);
    jl_value_t *tu = temp[nt];
    JL_GC_POP();
    return tu;
}
```
-/
def simpleUnion (n : Nat) (T : Types) (ops : Ops) (a b : Val) : CM Val := do
  let fa ← flattenTypeUnion n true a
  let fb ← flattenTypeUnion n true b
  let nta := fa.length
  let ntb := fb.length
  let nt := nta + ntb
  let mut temp : Array (Option Val) := ((fa ++ fb).map some).toArray
  let mut count := nt
  let mut ra := nta
  let mut rb := ntb
  -- first remove cross-redundancy and check if `a >: b` or `a <: b`.
  for i in [0:nta] do
    let some ti := temp[i]! | continue
    let hasFree := ti.hasFreeTypevars
    for j in [nta:nt] do
      let some tj := temp[j]! | continue
      let hasFree2 := (if hasFree then 1 else 0) ||| (if tj.hasFreeTypevars then 2 else 0)
      let subs ← simpleSubtype2 n T ops ti tj hasFree2 false
      let subab := subs &&& 1 != 0
      let subba := subs >>> 1 != 0
      if subab then
        temp := temp.set! i none
        if !subba then ra := 0
        count := count - 1
        break
      else if subba then
        temp := temp.set! j none
        rb := 0
        count := count - 1
  if count == ra then return a
  if count == rb then return b
  -- then remove self-redundancy
  for i in [0:nt] do
    let hasFree := match temp[i]! with | some x => x.hasFreeTypevars | none => false
    let (jmin, jmax) := if i < nta then (0, nta) else (nta, nt)
    for j in [jmin:jmax] do
      if let (some ti, some tj) := (temp[i]!, temp[j]!) then
        if j != i then
          let hasFree2 := (if hasFree then 1 else 0) ||| (if tj.hasFreeTypevars then 2 else 0)
          if ← simpleSubtype n T ops ti tj hasFree2 false then temp := temp.set! i none
  let sorted ← isortUnion n T temp.toList
  let merged ← mergeVarargUnions n T ops sorted.toArray
  return buildUnion merged.toList

/-- `simple_intersect(a, b, overesi)`

Julia source: src/jltypes.c:936-1050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *simple_intersect(jl_value_t *a, jl_value_t *b, int overesi)
{
    // Unlike `Union`, we don't unwrap `UnionAll` here to avoid possible widening.
    size_t nta = count_union_components(&a, 1, 0);
    size_t ntb = count_union_components(&b, 1, 0);
    size_t nt = nta + ntb;
    jl_value_t **temp;
    JL_GC_PUSHARGS(temp, nt+1);
    size_t count = 0;
    flatten_type_union(&a, 1, temp, &count, 0);
    flatten_type_union(&b, 1, temp, &count, 0);
    assert(count == nt);
    size_t i, j;
    int8_t *stemp = (int8_t *)alloca(count);
    // first remove disjoint elements.
    memset(stemp, 0, count);
    for (i = 0; i < nta; i++) {
        int hasfree = jl_has_free_typevars(temp[i]);
        for (j = nta; j < nt; j++) {
            if (!stemp[i] || !stemp[j]) {
                int intersect = !hasfree && !jl_has_free_typevars(temp[j]);
                if (!(intersect ? jl_has_empty_intersection(temp[i], temp[j]) : obviously_disjoint(temp[i], temp[j], 0)))
                    stemp[i] = stemp[j] = 1;
            }
        }
    }
    for (i = 0; i < nt; i++) {
        temp[i] = stemp[i] ? temp[i] : NULL;
    }
    // then check subtyping.
    // stemp[k] == -1 : ∃i temp[k] >:ₛ temp[i]
    // stemp[k] == 1 : ∃i temp[k] == temp[i]
    // stemp[k] == 2 : ∃i temp[k] <:ₛ temp[i]
    memset(stemp, 0, count);
    int all_disjoint = 1, subs[2] = {1, 1}, rs[2] = {1, 1};
    for (i = 0; i < nta; i++) {
        if (temp[i] == NULL) continue;
        all_disjoint = 0;
        int has_free = jl_has_free_typevars(temp[i]);
        for (j = nta; j < nt; j++) {
            if (temp[j] == NULL) continue;
            int has_free2 = has_free | (jl_has_free_typevars(temp[j]) << 1);
            int subs = simple_subtype2(temp[i], temp[j], has_free2, 0);
            int subab = subs & 1, subba = subs >> 1;
            if (subba && !subab) {
                stemp[i] = -1;
                if (stemp[j] >= 0) stemp[j] = 2;
            }
            else if (subab && !subba) {
                stemp[j] = -1;
                if (stemp[i] >= 0) stemp[i] = 2;
            }
            else if (subs) {
                if (stemp[i] == 0) stemp[i] = 1;
                if (stemp[j] == 0) stemp[j] = 1;
            }
        }
    }
    if (!all_disjoint) {
        for (i = 0; i < nt; i++) {
            subs[i >= nta] &= (temp[i] == NULL || stemp[i] > 0);
            rs[i >= nta] &= (temp[i] != NULL && stemp[i] > 0);
        }
        // return a(b) if a(b) <: b(a)
        if (rs[0]) {
            JL_GC_POP();
            return a;
        }
        if (rs[1]) {
            JL_GC_POP();
            return b;
        }
    }
    // return `Union{}` for `merge_env` if we can't prove `<:` or `>:`
    if (all_disjoint || (!overesi && !subs[0] && !subs[1])) {
        JL_GC_POP();
        return jl_bottom_type;
    }
    if (!subs[0] && !subs[1] && overesi == 1) {
        // Neither operand subsumes the other and they are not disjoint, so the
        // meet is not expressible as a single existing type. With `overesi==1`
        // (exact-meet mode, used on the subtype path) keep it as an internal
        // `Intersect{a, b}` node rather than over-approximating to one side,
        // which would silently drop the other. `overesi==2` falls through to
        // the legacy over-approximation below (used to widen an `Intersect`
        // before it could escape into a static parameter). See #61917.
        JL_GC_POP();
        return jl_new_struct(jl_intersect_type, a, b);
    }
    nt = subs[0] ? nta : subs[1] ? nt  : nt;
    i  = subs[0] ? 0   : subs[1] ? nta : 0;
    count = nt - i;
    if (!subs[0] && !subs[1]) {
        // over-approximate (`overesi==2`): keep only `a` components with strict
        // `<:` and all of `b`, then union them.
        for (j = 0; j < nt; j++)
            if (stemp[j] < (j < nta ? 2 : 0))
                temp[j] = NULL;
    }
    isort_union(&temp[i], count);
    temp[nt] = jl_bottom_type;
    size_t k;
    for (k = nt; k-- > i; ) {
        if (temp[k] != NULL) {
            if (temp[nt] == jl_bottom_type)
                temp[nt] = temp[k];
            else
                temp[nt] = jl_new_struct(jl_uniontype_type, temp[k], temp[nt]);
        }
    }
    assert(temp[nt] != NULL);
    jl_value_t *tu = temp[nt];
    JL_GC_POP();
    return tu;
}
```
-/
def simpleIntersect (n : Nat) (T : Types) (ops : Ops) (a b : Val) (overesi : Nat) : CM Val := do
  -- Unlike `Union`, we don't unwrap `UnionAll` here to avoid possible widening.
  let fa ← flattenTypeUnion n false a
  let fb ← flattenTypeUnion n false b
  let nta := fa.length
  let nt := nta + fb.length
  let mut temp : Array (Option Val) := ((fa ++ fb).map some).toArray
  -- first remove disjoint elements.
  let mut stemp : Array Int := Array.replicate nt 0
  for i in [0:nta] do
    let ti := temp[i]!.getD .bottom
    let hasfree := ti.hasFreeTypevars
    for j in [nta:nt] do
      if stemp[i]! == 0 || stemp[j]! == 0 then
        let tj := temp[j]!.getD .bottom
        let intersect := !hasfree && !tj.hasFreeTypevars
        let disjoint ← if intersect then ops.hasEmptyIntersection ti tj
          else ops.obviouslyDisjoint ti tj false
        if !disjoint then
          stemp := (stemp.set! i 1).set! j 1
  for i in [0:nt] do
    if stemp[i]! == 0 then temp := temp.set! i none
  -- then check subtyping.
  -- stemp[k] == -1 : ∃i temp[k] >:ₛ temp[i]
  -- stemp[k] == 1 : ∃i temp[k] == temp[i]
  -- stemp[k] == 2 : ∃i temp[k] <:ₛ temp[i]
  stemp := Array.replicate nt 0
  let mut allDisjoint := true
  let mut subs : Array Bool := #[true, true]
  let mut rs : Array Bool := #[true, true]
  for i in [0:nta] do
    let some ti := temp[i]! | continue
    allDisjoint := false
    let hasFree := ti.hasFreeTypevars
    for j in [nta:nt] do
      let some tj := temp[j]! | continue
      let hasFree2 := (if hasFree then 1 else 0) ||| (if tj.hasFreeTypevars then 2 else 0)
      let s ← simpleSubtype2 n T ops ti tj hasFree2 false
      let subab := s &&& 1 != 0
      let subba := s >>> 1 != 0
      if subba && !subab then
        stemp := stemp.set! i (-1)
        if stemp[j]! ≥ 0 then stemp := stemp.set! j 2
      else if subab && !subba then
        stemp := stemp.set! j (-1)
        if stemp[i]! ≥ 0 then stemp := stemp.set! i 2
      else if s != 0 then
        if stemp[i]! == 0 then stemp := stemp.set! i 1
        if stemp[j]! == 0 then stemp := stemp.set! j 1
  if !allDisjoint then
    for i in [0:nt] do
      let k := if i ≥ nta then 1 else 0
      subs := subs.set! k (subs[k]! && (temp[i]!.isNone || stemp[i]! > 0))
      rs := rs.set! k (rs[k]! && (temp[i]!.isSome && stemp[i]! > 0))
    -- return a(b) if a(b) <: b(a)
    if rs[0]! then return a
    if rs[1]! then return b
  -- return `Union{}` for `merge_env` if we can't prove `<:` or `>:`
  if allDisjoint || (overesi == 0 && !subs[0]! && !subs[1]!) then return .bottom
  if !subs[0]! && !subs[1]! && overesi == 1 then
    -- keep the exact meet as an internal `Intersect{a, b}` node (#61917)
    return .intersect a b
  let ntEnd := if subs[0]! then nta else nt
  let i0 := if subs[0]! then 0 else if subs[1]! then nta else 0
  if !subs[0]! && !subs[1]! then
    -- over-approximate (`overesi==2`): keep only `a` components with strict `<:` and all of `b`
    for j in [0:ntEnd] do
      if stemp[j]! < (if j < nta then 2 else 0) then temp := temp.set! j none
  let sorted ← isortUnion n T (temp.toList.drop i0 |>.take (ntEnd - i0))
  return buildUnion sorted

end JuliaLean.C
