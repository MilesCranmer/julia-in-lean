import JuliaLean.src.julia_h
import JuliaLean.src.jltypes_c
import JuliaLean.src.typemap_c
import JuliaLean.src.subtype_c

/-!
Generic functions, method table insertion, specificity sorting, and method lookup (`src/gf.c`).
-/

namespace JuliaLean.C

/-- `METHOD_SIG_LATEST_WHICH` (`src/julia_internal.h:827-829`). -/
def methodSigLatestWhich : Nat := 1
/-- `METHOD_SIG_LATEST_ONLY` -/
def methodSigLatestOnly : Nat := 2
/-- `METHOD_SIG_NO_LOSERS` -/
def methodSigNoLosers : Nat := 4

/-- `jl_method_t` (`src/julia.h:433-499`), keeping the fields read by method insertion and lookup. -/
structure Method where
  /-- Unique method identity (index in `MethodTable.methods`). -/
  uid : Nat := 0
  /-- Method label (`ret` in `generate.jl`'s `T table ret world sig` lines). -/
  ret : Int := 0
  /-- `m->sig`: method's type signature. -/
  sig : Val
  /-- `m->primary_world`: world age at which the method became active (`worldMax` before activation). -/
  primaryWorld : Nat := worldMax
  /-- Upper bound of the method's world range (`worldMax` while active; set to `world` by `jl_method_table_disable`). -/
  deletedWorld : Nat := worldMax
  /-- `m->dispatch_status`: bitmask of `METHOD_SIG_LATEST_WHICH` (1), `METHOD_SIG_LATEST_ONLY` (2), `METHOD_SIG_NO_LOSERS` (4). -/
  dispatchStatus : Nat := methodSigNoLosers
  /-- `m->interferences`: insertion-ordered set of intersecting methods (by `uid`) not more specific than this method. -/
  interferences : List Nat := []
  deriving Repr, BEq, Inhabited

/-- `jl_methtable_t` (`src/julia.h:1074-1083`) together with the global world counter. -/
structure MethodTable where
  defs : Typemap := .entries []
  methods : Array Method := #[]
  worldCounter : Nat := 1
  deriving Repr, Inhabited

/-- `jl_method_match_t` (`src/julia.h:1091-1099`). -/
structure MethodMatch where
  specTypes : Val
  sparams : List Val
  method : Method
  fullyCovers : Bool
  deriving Repr, BEq, Inhabited

/-- Outcome of a generic function call lookup. -/
inductive LookupResult where
  | method (ret : Int)
  | nomethod
  | ambiguous
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString LookupResult where
  toString
    | .method i => s!"method {i}"
    | .nomethod => "nomethod"
    | .ambiguous => "ambiguous"

/-- `jl_cachearg_offset`

Julia source: src/gf.c:138-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int8_t jl_cachearg_offset(void)
{
    return 0;
}
```
-/
def jlCacheargOffset : Nat := 0

/-- `jl_methtable_lookup`

Julia source: src/gf.c:347-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_methtable_lookup(jl_value_t *type, size_t world)
{
    // TODO: this is sort of an odd lookup strategy (and the only user of
    // jl_typemap_assoc_by_type with subtype=0), while normally jl_gf_invoke_lookup would be
    // expected to be used instead
    struct jl_typemap_assoc search = {type, world, NULL};
    jl_typemap_entry_t *sf = jl_typemap_assoc_by_type(jl_atomic_load_relaxed(&jl_method_table->defs), &search, 0, /*subtype*/0);
    if (!sf)
        return jl_nothing;
    return sf->func.value;
}
```
-/
def jlMethtableLookup (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable) (type : Val)
    (world : Nat) : CM (Option Method) := do
  let search : TypemapAssoc := { types := type, world := world, env := none }
  let (sf?, _) ← jlTypemapAssocByType n T ops mt.defs search 0 false
  match sf? with
  | none => return none
  | some sf => return mt.methods[sf.func]?

/-- `very_general_type`

Julia source: src/gf.c:1171-1174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int very_general_type(jl_value_t *t) JL_CANSAFEPOINT
{
    return (t == (jl_value_t*)jl_any_type || jl_types_equal(t, (jl_value_t*)jl_type_type));
}
```
-/
def veryGeneralType (ops : GfOps) (t : Val) : CM Bool := do
  if t == anyType then return true
  let tt ← mkTypeType
  ops.typesEqual t tt

/-- `jl_nth_slot_type`

Julia source: src/gf.c:1176-1186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_nth_slot_type(jl_value_t *sig, size_t i) JL_NOTSAFEPOINT
{
    sig = jl_unwrap_unionall(sig);
    size_t len = jl_nparams(sig);
    if (i < len-1)
        return jl_tparam(sig, i);
    jl_value_t *p = jl_tparam(sig, len-1);
    if (jl_is_vararg(p))
        p = jl_unwrap_vararg(p);
    return p;
}
```
-/
def jlNthSlotType (sig : Val) (i : Nat) : Val :=
  let sig := sig.unwrapUnionall
  let len := sig.nparams
  if i < len - 1 then
    sig.params[i]!
  else
    let p := sig.params[len - 1]!
    if p.isVararg then p.unwrapVararg else p

/-- `struct matches_env` (`src/gf.c:2347-2353`). -/
structure MatchesEnv where
  newentry : TypemapEntry
  shadowed : List Nat := []
  replaced : Option TypemapEntry := none
  deriving Repr, Inhabited

/-- `get_intersect_visitor`

Julia source: src/gf.c:2355-2375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int get_intersect_visitor(jl_typemap_entry_t *oldentry, struct typemap_intersection_env *closure0) JL_CANSAFEPOINT
{
    struct matches_env *closure = container_of(closure0, struct matches_env, match);
    jl_method_t *oldmethod = oldentry->func.method;
    assert(oldentry != closure->newentry && "entry already added");
    assert(jl_atomic_load_relaxed(&oldentry->min_world) <= jl_atomic_load_relaxed(&closure->newentry->min_world) && "old method cannot be newer than new method");
    //assert(jl_atomic_load_relaxed(&oldentry->max_world) != jl_atomic_load_relaxed(&closure->newentry->min_world) && "method cannot be added at the same time as method deleted");
    assert((jl_atomic_load_relaxed(&oldentry->max_world) == ~(size_t)0));
    // don't need to consider other similar methods if this oldentry will always fully intersect with them and dominates all of them
    if (closure->match.issubty // e.g. jl_subtype(closure->newentry.sig, oldentry->sig)
        && jl_subtype(oldmethod->sig, (jl_value_t*)closure->newentry->sig)) { // e.g. jl_type_equal(closure->newentry->sig, oldentry->sig)
        if (closure->replaced == NULL || jl_atomic_load_relaxed(&closure->replaced->min_world) < jl_atomic_load_relaxed(&oldentry->min_world))
            closure->replaced = oldentry; // must pick the newest insertion (both are still valid)
    }
    if (closure->shadowed == NULL)
        closure->shadowed = (jl_value_t*)jl_alloc_vec_any(0);
    // Record every intersecting method so the interference relation is complete.
    jl_array_ptr_1d_push((jl_array_t*)closure->shadowed, (jl_value_t*)oldmethod);
    typemap_bottom_search(oldentry, &closure->match);
    return 1;
}
```
-/
def getIntersectVisitor (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable)
    (oldentry : TypemapEntry) (closure0 : TypemapIntersectionEnv) (env : MatchesEnv) :
    CM (Bool × TypemapIntersectionEnv × MatchesEnv) := do
  let oldmethod := mt.methods[oldentry.func]!
  let mut replaced := env.replaced
  -- don't need to consider other similar methods if this oldentry will always fully intersect with them and dominates all of them
  if closure0.issubty then
    if ← ops.subtype oldmethod.sig env.newentry.sig then
      let take ← match replaced with
        | none => pure true
        | some rep => pure (rep.minWorld < oldentry.minWorld)
      if take then
        replaced := some oldentry -- must pick the newest insertion (both are still valid)
  -- Record every intersecting method so the interference relation is complete.
  let shadowed := env.shadowed ++ [oldmethod.uid]
  let closure1 ← typemapBottomSearch n T ops oldentry closure0
  return (true, closure1, { env with shadowed := shadowed, replaced := replaced })

/-- `get_intersect_matches`: the methods intersecting `newentry` in `world`, with the method of
equal signature it replaces in the second component.

Julia source: src/gf.c:2389-2416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *get_intersect_matches(jl_typemap_t *defs, jl_typemap_entry_t *newentry, jl_typemap_entry_t **replaced, size_t world, size_t image, jl_value_t *shadowed) JL_CANSAFEPOINT
{
    jl_tupletype_t *type = newentry->sig;
    jl_tupletype_t *ttypes = (jl_tupletype_t*)jl_unwrap_unionall((jl_value_t*)type);
    size_t l = jl_nparams(ttypes);
    jl_value_t *va = NULL;
    if (l > 0) {
        va = jl_tparam(ttypes, l - 1);
        if (jl_is_vararg(va))
            va = jl_unwrap_vararg(va);
        else
            va = NULL;
    }
    // search for all intersecting methods active in the previous world, to determine the changes needed to be made for the next world
    struct matches_env env = {{get_intersect_visitor, (jl_value_t*)type, va, /* .search_bottom = */ 0,
            /* .min_valid = */ world, /* .max_valid = */ world,
            /* .ti = */ NULL, /* .env = */ NULL, /* .issubty = */ 0,
            /* .emptiness_only = */ 1,
            /* .entry_filter = */ image == (size_t)-1 ? NULL : intersect_entry_uncovered},
        /* .newentry = */ newentry, /* .shadowed */ shadowed, /* .replaced */ NULL, image};
    JL_GC_PUSH3(&env.match.env, &env.match.ti, &env.shadowed);
    jl_typemap_intersection_visitor(defs, 0, &env.match);
    env.match.env = NULL;
    env.match.ti = NULL;
    *replaced = env.replaced;
    JL_GC_POP();
    return env.shadowed;
}
```
-/
def getIntersectMatches (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable)
    (newentry : TypemapEntry) (world : Nat) (shadowed : List Nat := []) :
    CM (List Nat × Option TypemapEntry) := do
  let type := newentry.sig
  let ttypes := type.unwrapUnionall
  let l := ttypes.nparams
  let va : Option Val :=
    if l > 0 then
      let last := ttypes.params[l - 1]!
      if last.isVararg then some last.unwrapVararg else none
    else
      none
  let matchEnv : TypemapIntersectionEnv := {
    type := type
    va := va
    searchBottom := 0
    minValid := world
    maxValid := world
    ti := .bottom
    env := none
    issubty := false
    emptinessOnly := true
  }
  let initEnv : MatchesEnv := {
    newentry := newentry
    shadowed := shadowed
    replaced := none
  }
  let (_, _, outEnv) ← jlTypemapIntersectionVisitor n T ops mt.defs 0 matchEnv initEnv
    (getIntersectVisitor n T ops mt) none
  return (outEnv.shadowed, outEnv.replaced)

/-- `jl_type_intersection2`: returns `(nonempty, isect, isect2?)`.

Julia source: src/gf.c:2594-2618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int jl_type_intersection2(jl_value_t *t1, jl_value_t *t2, jl_value_t **isect JL_REQUIRE_ROOTED_SLOT, jl_value_t **isect2 JL_REQUIRE_ROOTED_SLOT) JL_CANSAFEPOINT
{
    *isect2 = NULL;
    int is_subty = 0;
    *isect = jl_type_intersection_env_s(t1, t2, NULL, &is_subty);
    if (*isect == jl_bottom_type)
        return 0;
    if (is_subty)
        return 1;
    // TODO: sometimes type intersection returns types with free variables
    if (jl_has_free_typevars(t1) || jl_has_free_typevars(t2))
        return 1;
    // determine if type-intersection can be convinced to give a better, non-bad answer
    // if the intersection was imprecise, see if we can do better by switching the types
    *isect2 = jl_type_intersection(t2, t1);
    if (*isect2 == jl_bottom_type) {
        *isect = jl_bottom_type;
        *isect2 = NULL;
        return 0;
    }
    if (jl_types_struct_equiv(*isect2, *isect)) {
        *isect2 = NULL;
    }
    return 1;
}
```
-/
def jlTypeIntersection2 (n : Nat) (T : Types) (ops : GfOps) (t1 t2 : Val) :
    CM (Bool × Val × Option Val) := do
  let T := withBuiltinTypes T
  let (isect, _, isSubty) ← ops.typeIntersectionEnvS t1 t2 false
  if isect == .bottom then
    return (false, .bottom, none)
  if isSubty then
    return (true, isect, none)
  if t1.hasFreeTypevars || t2.hasFreeTypevars then
    return (true, isect, none)
  -- determine if type-intersection can be convinced to give a better, non-bad answer
  -- if the intersection was imprecise, see if we can do better by switching the types
  let isect2 ← ops.typeIntersection t2 t1
  if isect2 == .bottom then
    return (false, .bottom, none)
  if ← typesStructEquiv n T isect2 isect then
    return (true, isect, none)
  return (true, isect, some isect2)

/-- `is_replacing`: check if `type` is replacing `m` with an ambiguity here, given other methods in `d` that already match it.

Julia source: src/gf.c:2622-2644 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_replacing(char ambig, jl_value_t *type, jl_method_t *m, jl_method_t *const *d, size_t n, jl_value_t *isect, jl_value_t *isect2, char *morespec) JL_CANSAFEPOINT
{
    size_t k;
    for (k = 0; k < n; k++) {
        jl_method_t *m2 = d[k];
        // see if m2 also fully covered this intersection
        if (m == m2 || !(jl_subtype(isect, m2->sig) || (isect2 && jl_subtype(isect2, m2->sig))))
            continue;
        if (morespec[k])
            // not actually shadowing this--m2 will still be better
            return 0;
        // if type is not more specific than m (thus now dominating it)
        // then there is a new ambiguity here,
        // since m2 was also a previous match over isect,
        // see if m was previously dominant over all m2
        // or if this was already ambiguous before
        if (ambig && !jl_type_morespecific(m->sig, m2->sig)) {
            // m and m2 were previously ambiguous over the full intersection of mi with type, and will still be ambiguous with addition of type
            return 0;
        }
    }
    return 1;
}
```
-/
def isReplacing (ops : GfOps) (ambig : Bool) (m : Method) (d : Array Method)
    (isect : Val) (isect2 : Option Val) (morespec : Array Bool) : CM Bool := do
  for k in [0:d.size] do
    let m2 := d[k]!
    if m.uid != m2.uid then
      let sub1 ← ops.subtype isect m2.sig
      let sub2 ← match isect2 with
        | some i2 => if sub1 then pure true else ops.subtype i2 m2.sig
        | none => pure sub1
      if sub2 then
        if morespec[k]! then
          -- not actually shadowing this--m2 will still be better
          return false
        if ambig then
          if !(← ops.typeMorespecific m.sig m2.sig) then
            -- m and m2 were previously ambiguous over the full intersection of mi with type, and will still be ambiguous with addition of type
            return false
  return true

/-- `typemap_search`

Julia source: src/gf.c:3222-3229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typemap_search(jl_typemap_entry_t *entry, void *closure)
{
    if ((void*)(entry->func.method) == *(jl_method_t**)closure) {
        *(jl_typemap_entry_t**)closure = entry;
        return 0;
    }
    return 1;
}
```
-/
def typemapSearch (targetUid : Nat) (entry : TypemapEntry) (found : Option TypemapEntry) :
    CM (Bool × Option TypemapEntry) := do
  if entry.func == targetUid then
    return (false, some entry)
  return (true, found)

/-- `do_typemap_search`

Julia source: src/gf.c:3231-3237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_typemap_entry_t *do_typemap_search(jl_methtable_t *mt JL_PROPAGATES_ROOT, jl_method_t *method) JL_CANSAFEPOINT
{
    jl_value_t *closure = (jl_value_t*)(method);
    if (jl_typemap_visitor(jl_atomic_load_relaxed(&mt->defs), typemap_search, &closure))
        jl_error("method not in method table");
    return (jl_typemap_entry_t *)closure;
}
```
-/
def doTypemapSearch (n : Nat) (mt : MethodTable) (method : Method) : CM TypemapEntry := do
  let (notFound, entry?) ← jlTypemapVisitor n mt.defs (typemapSearch method.uid) none
  if notFound then
    throw "method not in method table"
  match entry? with
  | some e => return e
  | none => throw "method not in method table"

/-- Update the `maxWorld` of the entry for `targetUid` in a `Typemap`. -/
def updateTypemapEntryWorlds (n : Nat) (map : Typemap) (targetUid : Nat) (minW maxW : Nat) :
    CM Typemap :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match map with
    | .entries es =>
      return .entries (es.map fun e => if e.func == targetUid then { e with minWorld := minW, maxWorld := maxW } else e)
    | .level arg1 targ name1 tname linear any =>
      let arg1' ← arg1.mapM fun (k, v) => do return (k, ← updateTypemapEntryWorlds n v targetUid minW maxW)
      let targ' ← targ.mapM fun (k, v) => do return (k, ← updateTypemapEntryWorlds n v targetUid minW maxW)
      let name1' ← name1.mapM fun (k, v) => do return (k, ← updateTypemapEntryWorlds n v targetUid minW maxW)
      let tname' ← tname.mapM fun (k, v) => do return (k, ← updateTypemapEntryWorlds n v targetUid minW maxW)
      let linear' := linear.map fun e => if e.func == targetUid then { e with minWorld := minW, maxWorld := maxW } else e
      let any' ← updateTypemapEntryWorlds n any targetUid minW maxW
      return .level arg1' targ' name1' tname' linear' any'
    | .memory pairs =>
      let pairs' ← pairs.mapM fun (k, v) => do return (k, ← updateTypemapEntryWorlds n v targetUid minW maxW)
      return .memory pairs'
/-- `jl_method_table_disable`

Julia source: src/gf.c:3348-3375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT void jl_method_table_disable(jl_method_t *method) JL_CANSAFEPOINT
{
    // The image being generated cannot carry a deletion: the method's own image
    // keeps it, and the activation records of the methods defined meanwhile would
    // vouch for a method table without it. So refuse before touching anything.
    if (jl_options.incremental && jl_generating_output())
        jl_error("Method deletion is not possible during Module precompile.");
    jl_methtable_t *mt = jl_method_get_table(method);
    jl_typemap_entry_t *methodentry = do_typemap_search(mt, method);
    JL_LOCK(&world_counter_lock);
    if (!jl_atomic_load_relaxed(&allow_new_worlds))
        jl_error("Method changes have been disabled via a call to disable_new_worlds.");
    int enabled = jl_atomic_load_relaxed(&methodentry->max_world) == ~(size_t)0;
    if (enabled) {
        // Narrow the world age on the method to make it uncallable
        size_t world = jl_atomic_load_relaxed(&jl_world_counter);
        assert(method == methodentry->func.method);
        jl_atomic_store_relaxed(&method->dispatch_status, 0);
        assert(jl_atomic_load_relaxed(&methodentry->max_world) == ~(size_t)0);
        jl_atomic_store_relaxed(&methodentry->max_world, world);
        jl_method_table_invalidate(method, world, 1);
        contributor_tag_method(mt, method, -1); // a deletion is a contributor of no image
        jl_atomic_store_release(&jl_world_counter, world + 1);
    }
    JL_UNLOCK(&world_counter_lock);
    if (!enabled)
        jl_errorf("Method of %s already disabled", jl_symbol_name(method->name));
}
```
-/
def jlMethodTableDisable (n : Nat) (mt : MethodTable) (method : Method) : CM MethodTable := do
  let methodentry ← doTypemapSearch n mt method
  let enabled := methodentry.maxWorld == worldMax
  if !enabled then
    throw "Method already disabled"
  let world := mt.worldCounter
  let defs' ← updateTypemapEntryWorlds n mt.defs method.uid methodentry.minWorld world
  let m' := { method with dispatchStatus := 0, deletedWorld := world }
  let methods' := mt.methods.set! method.uid m'
  return { mt with defs := defs', methods := methods', worldCounter := world + 1 }

/-- `jl_method_table_add`

Julia source: src/gf.c:3377-3397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_typemap_entry_t *jl_method_table_add(jl_methtable_t *mt, jl_method_t *method, jl_tupletype_t *simpletype)
{
    JL_TIMING(ADD_METHOD, ADD_METHOD);
    assert(jl_is_method(method));
    assert(jl_is_mtable(mt));
    jl_timing_show_method(method, JL_TIMING_DEFAULT_BLOCK);
    jl_typemap_entry_t *newentry = NULL;
    JL_GC_PUSH1(&newentry);
    // add our new entry
    assert(jl_atomic_load_relaxed(&method->primary_world) == ~(size_t)0); // min-world
    assert((jl_atomic_load_relaxed(&method->dispatch_status) & METHOD_SIG_LATEST_WHICH) == 0);
    JL_LOCK(&mt->cache->writelock);
    newentry = jl_typemap_alloc((jl_tupletype_t*)method->sig, simpletype, jl_emptysvec, (jl_value_t*)method, ~(size_t)0, 1);
    jl_typemap_insert(&mt->defs, (jl_value_t*)mt, newentry, 0);

    if (mt == jl_method_table)
        update_max_args(method->sig);
    JL_UNLOCK(&mt->cache->writelock);
    JL_GC_POP();
    return newentry;
}
```
-/
def jlMethodTableAdd (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable) (method : Method)
    (simpletype : Option Val := none) : CM (MethodTable × TypemapEntry) := do
  let newentry ← jlTypemapAlloc T method.sig simpletype [] method.uid worldMax 1
  let defs' ← jlTypemapInsert n T ops mt.defs newentry 0
  return ({ mt with defs := defs' }, newentry)

/-- `has_key`

Julia source: src/gf.c:3399-3409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_key(jl_genericmemory_t *keys, jl_value_t *key)
{
    for (size_t l = keys->length, i = 0; i < l; i++) {
        jl_value_t *k = jl_genericmemory_ptr_ref(keys, i);
        if (k == NULL)
            return 0;
        if (jl_genericmemory_ptr_ref(keys, i) == key)
            return 1;
    }
    return 0;
}
```
-/
def hasKey (keys : List Nat) (key : Nat) : Bool :=
  keys.contains key

/-- `method_in_interferences`: check if `m2` is in `m1`'s interferences set, which means
`!morespecific(m1, m2)` for two methods that were at any point live in the same table at the same
time over some type-intersection.

Julia source: src/gf.c:3414-3417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int method_in_interferences(jl_method_t *m2, jl_method_t *m1)
{
    return has_key(jl_atomic_load_relaxed(&m1->interferences), (jl_value_t*)m2);
}
```
-/
def methodInInterferences (m2 m1 : Method) : Bool :=
  hasKey m1.interferences m2.uid

/-- `find_method_in_matches`: find the index of a method (by `uid`) in the method match array.

Julia source: src/gf.c:3420-3429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int find_method_in_matches(jl_array_t *t, jl_method_t *method)
{
    size_t len = jl_array_nrows(t);
    for (size_t i = 0; i < len; i++) {
        jl_method_match_t *matc = (jl_method_match_t*)jl_array_ptr_ref(t, i);
        if (matc->method == method)
            return i;
    }
    return -1;
}
```
-/
def findMethodInMatches (t : Array MethodMatch) (methodUid : Nat) : Option Nat := Id.run do
  for i in [0:t.size] do
    if t[i]!.method.uid == methodUid then
      return some i
  return none

/-- `method_morespecific_recorded`: whether `targetMethod` is morespecific than `startMethod`,
and has a type-intersection.

Julia source: src/gf.c:3432-3445 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int method_morespecific_recorded(jl_method_t *target_method, jl_method_t *start_method) JL_CANSAFEPOINT
{
    if (target_method == start_method)
        return 0;
    int result = method_in_interferences(target_method, start_method) &&
                 !method_in_interferences(start_method, target_method);
    //// Expensive cross-check: the recorded relation must agree with ground truth
    //// for every intersecting pair.
    //assert(result == jl_method_morespecific(target_method, start_method) ||
    //       jl_has_empty_intersection(target_method->sig, start_method->sig) ||
    //       jl_has_empty_intersection(start_method->sig, target_method->sig));
    assert(!result || !(jl_atomic_load_relaxed(&target_method->dispatch_status) & METHOD_SIG_NO_LOSERS));
    return result;
}
```
-/
def methodMorespecificRecorded (targetMethod startMethod : Method) : Bool :=
  if targetMethod.uid == startMethod.uid then
    false
  else
    methodInInterferences targetMethod startMethod &&
    !methodInInterferences startMethod targetMethod

/-- `admissible_cover`: whether `m2id` is admissible as a cover of `m`: reported in the match list,
strictly morespecific than `m` (a one-directional recorded edge), and already finalized by the sort.

Julia source: src/gf.c:3451-3463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int admissible_cover(jl_method_t *m, jl_method_t *m2, jl_array_t *t, arraylist_t *visited)
{
    if (m2 == NULL)
        return 0;
    int idx = find_method_in_matches(t, m2);
    if (idx < 0)
        return 0;
    if (method_in_interferences(m, m2))
        return 0; // mutually ambiguous, so not a dominator
    if (visited->items[idx] != (void*)1)
        return 0; // not finalized yet (part of the same SCC cycle, handled by ambiguity later)
    return 1;
}
```
-/
def admissibleCover (m : Method) (m2id : Nat) (t : Array MethodMatch) (visited : Array Nat) :
    Option Method :=
  match findMethodInMatches t m2id with
  | none => none
  | some idx =>
    let m2 := t[idx]!.method
    if methodInInterferences m m2 then
      none -- mutually ambiguous, so not a dominator
    else if visited[idx]! != 1 then
      none -- not finalized yet (part of the same SCC cycle, handled by ambiguity later)
    else
      some m2

/-- `union_of_sigs_covers`: whether `ti` is contained in the union of the signatures of the methods in `ms`.

Julia source: src/gf.c:3467-3482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int union_of_sigs_covers(jl_value_t *ti, jl_method_t **ms, size_t n) JL_CANSAFEPOINT
{
    if (n == 0)
        return 0;
    arraylist_t sigs;
    arraylist_new(&sigs, n);
    for (size_t i = 0; i < n; i++)
        arraylist_push(&sigs, (void*)ms[i]->sig);
    jl_value_t *u = NULL;
    JL_GC_PUSH1(&u);
    u = jl_type_union((jl_value_t**)sigs.items, sigs.len);
    arraylist_free(&sigs);
    int result = jl_subtype(ti, u);
    JL_GC_POP();
    return result;
}
```
-/
def unionOfSigsCovers (n : Nat) (T : Types) (ops : GfOps) (ti : Val) (ms : List Method) :
    CM Bool := do
  let T := withBuiltinTypes T
  if ms.isEmpty then
    return false
  let sigs := ms.map (·.sig)
  let u ← typeUnion n T ops.toOps sigs
  ops.subtype ti u

/-- `check_blocker_transfer`

Julia source: src/gf.c:3504-3535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int check_blocker_transfer(jl_value_t *ti, jl_value_t *ti_S, jl_method_t *S, jl_method_t **covers, size_t ncovers) JL_CANSAFEPOINT
{
    size_t j;
    for (j = 0; j < ncovers; j++) {
        if (method_morespecific_recorded(S, covers[j]))
            break;
    }
    if (j == ncovers)
        return 1;
    int result = 0;
    jl_value_t *region = NULL;
    JL_GC_PUSH1(&region);
    region = jl_type_intersection(ti, ti_S);
    if (region == jl_bottom_type) {
        // D was never a witness of S within the query, so S doesn't block its removal
        result = 1;
    }
    else {
        arraylist_t blockers;
        arraylist_new(&blockers, 0);
        for (j = 0; j < ncovers; j++) {
            // a cover that S does not beat blocks S, whether it is strictly
            // morespecific than S or merely unordered with it
            if (method_in_interferences(covers[j], S))
                arraylist_push(&blockers, (void*)covers[j]);
        }
        result = union_of_sigs_covers(region, (jl_method_t**)blockers.items, blockers.len);
        arraylist_free(&blockers);
    }
    JL_GC_POP();
    return result;
}
```
-/
def checkBlockerTransfer (n : Nat) (T : Types) (ops : GfOps) (ti tiS : Val) (S : Method)
    (covers : List Method) : CM Bool := do
  let beatsAny := covers.any fun c => methodMorespecificRecorded S c
  if !beatsAny then
    return true
  let region ← ops.typeIntersection ti tiS
  if region == .bottom then
    -- D was never a witness of S within the query, so S doesn't block its removal
    return true
  let blockers := covers.filter fun c => methodInInterferences c S
  unionOfSigsCovers n T ops region blockers

/-- `check_dominance_transfer`

Julia source: src/gf.c:3547-3600 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int check_dominance_transfer(jl_method_t *D, jl_value_t *ti, jl_method_t **covers, size_t ncovers, jl_array_t *t) JL_CANSAFEPOINT
{
    // First, the matches D was unordered with. Both members of such a pair
    // record each other, so D's own interference set is enough to enumerate
    // them.
    // (n.b. even with `!include_ambiguous`, where D is dropped either way, this
    // scan is still needed to compute *has_ambiguity: usually a surviving S
    // re-reports the same pair from `check_fully_ambiguous`, but S can be
    // exempt from that scan -- notably when S is the minmax method, which the
    // sort never visits -- leaving this check as the only witness of the pair
    // when D's only cover is a match that S beats (test `AmbigMinmaxPartner`))
    jl_genericmemory_t *interferences = jl_atomic_load_relaxed(&D->interferences);
    JL_GC_PUSH1(&interferences);
    for (size_t i = 0; i < interferences->length; i++) {
        jl_method_t *S = (jl_method_t*)jl_genericmemory_ptr_ref(interferences, i);
        if (S == NULL)
            continue;
        if (!method_in_interferences(D, S))
            continue; // S is morespecific than D, so D was not blocking it
        int idx = find_method_in_matches(t, S);
        if (idx < 0)
            continue;
        jl_method_match_t *matc = (jl_method_match_t*)jl_array_ptr_ref(t, idx);
        if (!check_blocker_transfer(ti, (jl_value_t*)matc->spec_types, S, covers, ncovers)) {
            JL_GC_POP();
            return 0;
        }
    }
    JL_GC_POP();
    // Next, the methods `D` was beating: those stay unselectable through the
    // covers by the same rule.
    //
    // If D is not strictly morespecific than anything it intersects
    // (METHOD_SIG_NO_LOSERS), it was beating nobody and there is nothing more to
    // transfer: the removal is silent (as a fast-path).
    if (jl_atomic_load_relaxed(&D->dispatch_status) & METHOD_SIG_NO_LOSERS)
        return 1;
    size_t len = jl_array_nrows(t);
    for (size_t i = 0; i < len; i++) {
        jl_method_match_t *matc = (jl_method_match_t*)jl_array_ptr_ref(t, i);
        jl_method_t *S = matc->method;
        if (S == D)
            continue;
        // An S that beats nothing can never strictly beat a cover, so its
        // blocking transfers automatically (as a fast-path)
        if (jl_atomic_load_relaxed(&S->dispatch_status) & METHOD_SIG_NO_LOSERS)
            continue;
        if (!method_morespecific_recorded(D, S))
            continue;
        if (!check_blocker_transfer(ti, (jl_value_t*)matc->spec_types, S, covers, ncovers))
            return 0;
    }
    return 1;
}
```
-/
def checkDominanceTransfer (n : Nat) (T : Types) (ops : GfOps) (D : Method) (ti : Val)
    (covers : List Method) (t : Array MethodMatch) : CM Bool := do
  -- First, the matches D was unordered with.
  for sid in D.interferences do
    let some idx := findMethodInMatches t sid | continue
    let matc := t[idx]!
    let S := matc.method
    if !methodInInterferences D S then
      continue -- S is morespecific than D, so D was not blocking it
    if !(← checkBlockerTransfer n T ops ti matc.specTypes S covers) then
      return false
  -- Next, the methods `D` was beating: those stay unselectable through the covers by the same rule.
  if (D.dispatchStatus &&& methodSigNoLosers) != 0 then
    return true
  for i in [0:t.size] do
    let matc := t[i]!
    let S := matc.method
    if S.uid == D.uid then
      continue
    if (S.dispatchStatus &&& methodSigNoLosers) != 0 then
      continue
    if !methodMorespecificRecorded D S then
      continue
    if !(← checkBlockerTransfer n T ops ti matc.specTypes S covers) then
      return false
  return true

/-- Outcome of the cover analysis for one match `m` over its region `ti` (`src/gf.c:3616-3621`). -/
inductive CoverStatus where
  | none
  | ambiguous
  | certified
  deriving BEq, Repr

/-- `check_interferences_covers`: check if some morespecific method (or a union of them) covers
the given type intersection; returns `(dropMatch, hasAmbiguity)`.

Julia source: src/gf.c:3612-3689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int check_interferences_covers(jl_method_t *m, jl_value_t *ti, jl_array_t *t, arraylist_t *visited, jl_method_t *minmaxm, int include_ambiguous, int *has_ambiguity) JL_CANSAFEPOINT
{
    // Outcome of the cover analysis for one match `m` over its region `ti`, in
    // increasing strength -- each step of the analysis only ever raises it:
    enum {
        COVER_NONE = 0,      // no strictly-morespecific cover contains ti: m may still be selectable
        COVER_AMBIGUOUS = 1, // covers contain ti (so m can never win) but could not take over the
                             // roles m had in the sort, so the apparent ambiguity is real
        COVER_CERTIFIED = 2, // covers contain ti and took over m's roles: dropping m is silent
    } status = COVER_NONE;

    // Optimization: when ambiguity is already known and the caller does not want ambiguous
    // matches reported, m is dropped either way, so skip the transfer proofs.
    int prove_transfer = include_ambiguous || !*has_ambiguity;

    // The minmax method contains every match's region, is reported unconditionally,
    // and is pre-finalized, so whenever it strictly beats `m` it is an admissible cover:
    // probe it directly before scanning the interference set in storage order.
    int probed_minmax = 0;
    if (minmaxm != NULL && method_morespecific_recorded(minmaxm, m) &&
        jl_subtype(ti, (jl_value_t*)minmaxm->sig)) {
        probed_minmax = 1;
        // m can never win dispatch here.
        // Drop m if minmaxm also takes over the roles m had in the sort:
        // a specificity cycle may lead back from a cover to a method that only
        // m beat, or m may be the last match blocking another one, and either
        // way the apparent ambiguity is real.
        if (prove_transfer && !check_dominance_transfer(m, ti, &minmaxm, 1, t))
            status = COVER_AMBIGUOUS;
        else
            return 1; // COVER_CERTIFIED
    }
    // Scan the interference set: each admissible cover (recorded
    // strictly-morespecific interference the sort has already finalized) is
    // both attempted as a single cover of ti and collected for the union check
    // below. (The transfer obligations are the same as for the minmax probe
    // above.)
    arraylist_t covers;
    arraylist_new(&covers, 0);
    jl_genericmemory_t *interferences = jl_atomic_load_relaxed(&m->interferences);
    JL_GC_PUSH1(&interferences);
    for (size_t i = 0; status != COVER_CERTIFIED && i < interferences->length; i++) {
        jl_method_t *m2 = (jl_method_t*)jl_genericmemory_ptr_ref(interferences, i);
        if (!admissible_cover(m, m2, t, visited))
            continue;
        arraylist_push(&covers, (void*)m2);
        if (probed_minmax && m2 == minmaxm)
            continue; // its transfer already failed above
        if (!jl_subtype(ti, (jl_value_t*)m2->sig))
            continue;
        status = (prove_transfer && !check_dominance_transfer(m, ti, &m2, 1, t)) ?
                 COVER_AMBIGUOUS : COVER_CERTIFIED;
    }
    JL_GC_POP();
    // No single morespecific method certified covering ti, but a union of them
    // may (e.g. several methods each covering one component of a Union-typed
    // argument). Whether such a union really certifies the removal is left to
    // `check_dominance_transfer` again: a cover may be tangled in a specificity
    // cycle that leads back to `m`, or may fail to block what `m` was blocking
    // (test `AmbigUnionCycle`).
    if (status != COVER_CERTIFIED && covers.len > 1 &&
        union_of_sigs_covers(ti, (jl_method_t**)covers.items, covers.len)) {
        status = (prove_transfer &&
                  !check_dominance_transfer(m, ti, (jl_method_t**)covers.items, covers.len, t)) ?
                 COVER_AMBIGUOUS : COVER_CERTIFIED;
    }
    arraylist_free(&covers);
    if (status == COVER_AMBIGUOUS) {
        // Some cover, or the union of the covers, dominated m over all of ti,
        // but none of them could take over the roles m had in the sort: the
        // apparent ambiguity is real. Per the contract above, the dominated m
        // is still dropped when `!include_ambiguous`, but kept as a witness
        // when ambiguity-reporting consumers need to see it.
        *has_ambiguity = 1;
        return !include_ambiguous;
    }
    return status == COVER_CERTIFIED;
}
```
-/
def checkInterferencesCovers (n : Nat) (T : Types) (ops : GfOps) (m : Method) (ti : Val)
    (t : Array MethodMatch) (visited : Array Nat) (minmaxm : Option Method)
    (includeAmbiguous : Bool) (hasAmbiguity : Bool) : CM (Bool × Bool) := do
  let mut status : CoverStatus := .none
  let proveTransfer := includeAmbiguous || !hasAmbiguity
  let mut probedMinmax := false
  if let some mm := minmaxm then
    if methodMorespecificRecorded mm m then
      if ← ops.subtype ti mm.sig then
        probedMinmax := true
        if proveTransfer then
          if !(← checkDominanceTransfer n T ops m ti [mm] t) then
            status := .ambiguous
          else
            return (true, hasAmbiguity)
        else
          return (true, hasAmbiguity)
  let mut covers : List Method := []
  for m2id in m.interferences do
    if status == .certified then break
    let some m2 := admissibleCover m m2id t visited | continue
    covers := covers ++ [m2]
    if probedMinmax && (minmaxm.map (·.uid) == some m2.uid) then
      continue
    if !(← ops.subtype ti m2.sig) then
      continue
    if proveTransfer then
      if !(← checkDominanceTransfer n T ops m ti [m2] t) then
        status := .ambiguous
      else
        status := .certified
    else
      status := .certified
  if status != .certified && covers.length > 1 then
    if ← unionOfSigsCovers n T ops ti covers then
      if proveTransfer then
        if !(← checkDominanceTransfer n T ops m ti covers t) then
          status := .ambiguous
        else
          status := .certified
      else
        status := .certified
  if status == .ambiguous then
    return (!includeAmbiguous, true)
  return (status == .certified, hasAmbiguity)

/-- `check_fully_ambiguous`: returns `(result, hasAmbiguity)`.

Julia source: src/gf.c:3691-3737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int check_fully_ambiguous(jl_method_t *m, jl_value_t *ti, jl_array_t *t, int include_ambiguous, int *has_ambiguity) JL_CANSAFEPOINT
{
    if (include_ambiguous && *has_ambiguity)
        return 0; // this can only compute *has_ambiguity, which is already known
    int result = 0;
    jl_value_t *region = NULL;
    jl_genericmemory_t *interferences = jl_atomic_load_relaxed(&m->interferences);
    JL_GC_PUSH2(&interferences, &region);
    for (size_t i = 0; i < interferences->length; i++) {
        jl_method_t *m2 = (jl_method_t*)jl_genericmemory_ptr_ref(interferences, i);
        if (m2 == NULL)
            continue;
        int idx = find_method_in_matches(t, m2);
        if (idx < 0)
            continue;
        if (!method_in_interferences(m, m2))
            continue;
        if (!*has_ambiguity) {
            jl_method_match_t *matc2 = (jl_method_match_t*)jl_array_ptr_ref(t, idx);
            region = jl_type_intersection(ti, (jl_value_t*)matc2->spec_types);
            // A match's region can lose a constraint its signature imposes
            // (the diagonal `T` of `(::Type{T}, ::T) where T`), so keep
            // re-intersecting with the signatures to try to eliminate the
            // intersection before setting the (potentially costly) ambiguity flag.
            if (region != jl_bottom_type)
                region = jl_type_intersection(region, (jl_value_t*)m->sig);
            if (region != jl_bottom_type)
                region = jl_type_intersection(region, (jl_value_t*)m2->sig);
            if (region == jl_bottom_type) {
                // The pair is recorded as overlapping, but not anywhere inside
                // this query, so nothing here can dispatch ambiguously between
                // them. Nor can `m2` cover `ti`, which it does not even
                // intersect, so there is nothing else to do with this partner.
                continue;
            }
            *has_ambiguity = 1;
        }
        if (include_ambiguous)
            break; // the rest of the scan could only set *has_ambiguity again
        if (jl_subtype(ti, m2->sig)) {
            result = 1;
            break;
        }
    }
    JL_GC_POP();
    return result;
}
```
-/
def checkFullyAmbiguous (ops : GfOps) (m : Method) (ti : Val) (t : Array MethodMatch)
    (includeAmbiguous : Bool) (hasAmbiguity : Bool) : CM (Bool × Bool) := do
  if includeAmbiguous && hasAmbiguity then
    return (false, hasAmbiguity)
  let mut result := false
  let mut hasAmbig := hasAmbiguity
  for m2id in m.interferences do
    let some idx := findMethodInMatches t m2id | continue
    let matc2 := t[idx]!
    let m2 := matc2.method
    if !methodInInterferences m m2 then
      continue
    if !hasAmbig then
      let mut region ← ops.typeIntersection ti matc2.specTypes
      if region != .bottom then
        region ← ops.typeIntersection region m.sig
      if region != .bottom then
        region ← ops.typeIntersection region m2.sig
      if region == .bottom then
        continue
      hasAmbig := true
    if includeAmbiguous then
      break
    if ← ops.subtype ti m2.sig then
      result := true
      break
  return (result, hasAmbig)

/-- `activate_against_methods`: settle the specificity of each pair between `method` and `d`
(the methods intersecting it), update both interference sets and the `NO_LOSERS` bits.

Julia source: src/gf.c:3795-3904 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_genericmemory_t *activate_against_methods(struct activate_env *env, jl_method_t *method, jl_value_t *type,
                                                     jl_method_t *const *d, size_t n, char *morespec, char *ambigs, size_t nknown,
                                                     jl_genericmemory_t *interferences, jl_array_t *oldmi, jl_array_t *newrecord) JL_CANSAFEPOINT
{
    jl_value_t *specs = NULL;
    jl_value_t *isect = NULL;
    jl_value_t *isect2 = NULL;
    JL_GC_PUSH4(&interferences, &specs, &isect, &isect2);
    size_t j;
    // Compute the morespec values not given upfront
    for (j = nknown; j < n; j++)
        morespec[j] = (char)jl_type_morespecific(d[j]->sig, type);
    // `d` has no duplicates, so a duplicate key can only be one of the entries
    // already present at loop entry (a precompile re-activation, or a replayed
    // record); for a freshly defined method the set starts empty and the probe
    // would be a guaranteed-miss linear scan of the growing set.
    int check_dup_key = interferences->length > 0;
    // This method, when of an image, is what the record of each scanned method of
    // no image it does not beat would have held had this image been loaded when
    // that method activated: that record is completed with it below.
    int completing = n > nknown && recording_ext_backinterferences() && jl_ext_backinterferences != NULL && jl_object_in_image((jl_value_t*)method);
    for (j = 0; j < n; j++) {
        jl_method_t *m = d[j];
        // Compute ambig state: is there an ambiguity between new method and old m?
        if (j >= nknown)
            ambigs[j] = !morespec[j] && !jl_type_morespecific(type, m->sig);
        char ambig = ambigs[j];
        if (newrecord && j >= nknown && !morespec[j] && jl_object_in_image((jl_value_t*)m))
            jl_array_ptr_1d_push(newrecord, (jl_value_t*)m); // gains the new method in its interference set below
        if (morespec[j] || ambig) {
            // !morespecific(new, old): add the old method to this interference set
            ssize_t idx;
            if (!check_dup_key || !has_key(interferences, (jl_value_t*)m))
                interferences = jl_idset_put_key(interferences, (jl_value_t*)m, &env->interferences_max, &idx);
            if (completing && j >= nknown && !jl_object_in_image((jl_value_t*)m)) {
                jl_value_t *record = jl_eqtable_get(jl_ext_backinterferences, (jl_value_t*)m, NULL);
                if (record != NULL)
                    jl_array_ptr_1d_push((jl_array_t*)record, (jl_value_t*)method);
            }
        }
        if (morespec[j]) {
            // morespecific(old, new): the old method gained a strict loser
            // (a replayed method's image was saved before this method existed)
            int m_dispatch = jl_atomic_load_relaxed(&m->dispatch_status);
            if (m_dispatch & METHOD_SIG_NO_LOSERS)
                jl_atomic_store_relaxed(&m->dispatch_status, m_dispatch & ~METHOD_SIG_NO_LOSERS);
        }
        else if (!ambig) {
            // morespecific(new, old): the new method beats something
            env->dispatch_bits &= ~METHOD_SIG_NO_LOSERS;
        }
        if (!morespec[j]) {
            // !morespecific(old, new): add the new method to its interference set.
            // Live, no duplicate-key probe is needed: `d` was collected against the
            // prior world, and the methods of a loaded image activate together in a
            // single world bump, so a same-image method -- the only kind whose
            // serialized interference set could already contain `method` -- never
            // appears in `d`. A replay still probes, as a duplicate key would stay in the set.
            if (j >= nknown || !method_in_interferences(method, m)) {
                jl_genericmemory_t *m_interferences = jl_atomic_load_relaxed(&m->interferences);
                ssize_t idx;
                size_t m_max = jl_idset_max(m_interferences);
                m_interferences = jl_idset_put_key(m_interferences, (jl_value_t*)method, &m_max, &idx);
                jl_gc_write_atomic(m, m->interferences, jl_genericmemory_t, m_interferences, release);
            }
        }
        // Now examine if this caused any invalidations.
        jl_method_instance_t *unspec = jl_atomic_load_relaxed(&m->unspecialized);
        if (unspec && !morespec[j])
            jl_array_ptr_1d_push(oldmi, (jl_value_t*)unspec);
        if (morespec[j])
            continue;
        _Atomic(jl_method_instance_t*) *data;
        size_t l = method_specializations(m, &specs, &data);
        for (size_t i = 0; i < l; i++) {
            jl_method_instance_t *mi = jl_atomic_load_relaxed(&data[i]);
            if ((jl_value_t*)mi == jl_nothing)
                continue;
            if (jl_type_intersection2(type, mi->specTypes, &isect, &isect2)) {
                // Replacing a method--see if this really was the selected method previously
                // over the intersection (not ambiguous) and the new method will be selected now (morespec).
                // TODO: this only checks pair-wise for ambiguities, but the ambiguities could arise from the interaction of multiple methods
                // and thus might miss a case where we introduce an ambiguity between`.u two existing methods
                // We could instead work to sort this into 3 groups `morespecific .. ambiguous .. lesspecific`, with `type` in ambiguous,
                // such that everything in `morespecific` dominates everything in `ambiguous`, and everything in `ambiguous` dominates everything in `lessspecific`
                // And then compute where each isect falls, and whether it changed group--necessitating invalidation--or not.
                int replaced_dispatch = is_replacing(ambig, type, m, d, n, isect, isect2, morespec);
                invalidate_specialization(env, mi, type, m, d, n, replaced_dispatch, ambig, morespec, oldmi);
            }
            // TODO: do we have any interesting cases left where isect3 is useful
            //jl_value_t *isect3 = NULL;
            //jl_value_t *isect4 = NULL;
            //jl_value_t *isect5 = NULL;
            //JL_GC_PUSH3(&isec3, &isect4, &isect5);
            //isect3 = jl_type_intersection(m->sig, (jl_value_t*)mi->specTypes);
            //jl_type_intersection2(type, isect3, &isect4, &isect5);
            //if (!jl_types_equal(isect, isect4) && (!isect2 || !jl_types_equal(isect2, isect4)) &&
            //    (!isect5 || (!jl_types_equal(isect, isect5) && (!isect2 || !jl_types_equal(isect2, isect5))))) {
            //    jl_(type);
            //    jl_(mi->specTypes);
            //    jl_(m->sig);
            //}
            //JL_GC_POP();
            isect = NULL;
            isect2 = NULL;
        }
    }
    JL_GC_POP();
    return interferences;
}
```
-/
def activateAgainstMethods (ops : GfOps) (methods : Array Method) (method : Method) (type : Val)
    (d : Array Nat) (dispatchBits : Nat) (interferences : List Nat) :
    CM (Array Method × Nat × List Nat) := do
  let n := d.size
  let mut morespec : Array Bool := #[]
  for j in [0:n] do
    let m := methods[d[j]!]!
    let ms ← ops.typeMorespecific m.sig type
    morespec := morespec.push ms
  let checkDupKey := !interferences.isEmpty
  let mut methods := methods
  let mut dispatchBits := dispatchBits
  let mut interferences := interferences
  for j in [0:n] do
    let mUid := d[j]!
    let m := methods[mUid]!
    let ms := morespec[j]!
    let ambig ←
      if ms then pure false
      else pure (!(← ops.typeMorespecific type m.sig))
    if ms || ambig then
      -- !morespecific(new, old): add the old method to this interference set
      if !checkDupKey || !hasKey interferences mUid then
        interferences := interferences ++ [mUid]
    if ms then
      -- morespecific(old, new): the old method gained a strict loser
      let mDispatch := m.dispatchStatus
      if (mDispatch &&& methodSigNoLosers) != 0 then
        let m := { m with dispatchStatus := mDispatch - (mDispatch &&& methodSigNoLosers) }
        methods := methods.set! mUid m
    else if !ambig then
      -- morespecific(new, old): the new method beats something
      dispatchBits := dispatchBits - (dispatchBits &&& methodSigNoLosers)
    if !ms then
      -- !morespecific(old, new): add the new method to its interference set.
      let m := methods[mUid]!
      if !hasKey m.interferences method.uid then
        let m := { m with interferences := m.interferences ++ [method.uid] }
        methods := methods.set! mUid m
  return (methods, dispatchBits, interferences)

/-- `jl_method_table_activate_with_record`

Julia source: src/gf.c:3916-4130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void jl_method_table_activate_with_record(jl_typemap_entry_t *newentry, jl_array_t *record, size_t image, jl_array_t *deferred) JL_CANSAFEPOINT
{
    JL_TIMING(ADD_METHOD, ADD_METHOD);
    jl_method_t *method = newentry->func.method;
    jl_methtable_t *mt = jl_method_get_table(method);
    assert(jl_is_mtable(mt));
    assert(jl_is_method(method));
    jl_timing_show_method(method, JL_TIMING_DEFAULT_BLOCK);
    jl_value_t *type = (jl_value_t*)newentry->sig;
    jl_value_t *oldvalue = NULL;
    jl_array_t *oldmi = NULL;
    size_t world = jl_atomic_load_relaxed(&method->primary_world);
    assert(world == jl_atomic_load_relaxed(&jl_world_counter) + 1); // min-world
    assert((jl_atomic_load_relaxed(&method->dispatch_status) & METHOD_SIG_LATEST_WHICH) == 0);
    assert(jl_atomic_load_relaxed(&newentry->min_world) == ~(size_t)0);
    assert(jl_atomic_load_relaxed(&newentry->max_world) == 1);
    jl_atomic_store_relaxed(&newentry->min_world, world);
    jl_atomic_store_relaxed(&method->primary_world, world);
    size_t max_world = world - 1;
    jl_value_t *loctag = NULL;  // debug info for invalidation
    jl_value_t *isect = NULL;
    jl_value_t *isect2 = NULL;
    jl_genericmemory_t *interferences = NULL;
    jl_array_t *newrecord = NULL; // the record being made, when recording
    JL_GC_PUSH7(&oldvalue, &oldmi, &loctag, &isect, &isect2, &interferences, &newrecord);
    // only a method of no image can be saved with its record (as an extext method of
    // the image being generated); an image's method is replayed or scanned, not recorded
    int recording = recording_ext_backinterferences() && mt == jl_method_table && !jl_object_in_image((jl_value_t*)method);
    int replaying = record != NULL && image != (size_t)-1 && mt == jl_method_table;
    // does every contributor to this signature's typenames lie in an image the record
    // covers? Then its scan saw every method on them.
    int all_covered = replaying && jl_sig_contributors_world(type, mt, image) != 0;
    jl_typemap_entry_t *replaced = NULL;
    // Holds the set of all intersecting methods not more specific than this one.
    interferences = (jl_genericmemory_t*)jl_atomic_load_relaxed(&method->interferences);
    // When replaying, `oldvalue` starts with the methods the record covers, as the
    // worker found them: those the record lists (the methods of covered images not
    // more specific than this one), then, from the interference set the image
    // preserved, the more specific methods of covered images; the scan appends the
    // methods of uncovered images after them.
    size_t rn = 0; // that replayed head
    size_t nrec = 0; // of which the record's own entries
    if (replaying) {
        nrec = jl_array_nrows(record);
        oldvalue = (jl_value_t*)jl_alloc_vec_any(0);
        for (size_t i = 0; i < nrec; i++)
            jl_array_ptr_1d_push((jl_array_t*)oldvalue, jl_array_ptr_ref(record, i));
        size_t nint = jl_idset_max(interferences);
        for (size_t i = 0; i < nint; i++) {
            jl_method_t *m = (jl_method_t*)jl_genericmemory_ptr_ref(interferences, i);
            if (m == NULL || !interference_covered_by_record(m, image))
                continue;
            size_t j = 0;
            while (j < nrec && jl_array_ptr_ref(oldvalue, j) != (jl_value_t*)m)
                j++;
            if (j < nrec)
                continue; // ambiguous, listed above
            jl_array_ptr_1d_push((jl_array_t*)oldvalue, (jl_value_t*)m);
        }
        rn = jl_array_nrows(oldvalue);
        // a recorded method was deleted or replaced since, so scan everything
        for (size_t i = 0; i < rn && replaying; i++) {
            jl_method_t *m = (jl_method_t*)jl_array_ptr_ref(oldvalue, i);
            if (!(jl_atomic_load_relaxed(&m->dispatch_status) & METHOD_SIG_LATEST_WHICH))
                replaying = 0;
        }
        if (!replaying) {
            oldvalue = NULL;
            rn = 0;
        }
    }
    // scan only the methods of other images; the checks below still see every intersecting method
    if (replaying && all_covered) {
        // no other image has a method on these typenames, so the scan would find nothing
    }
    else {
        oldvalue = get_intersect_matches(jl_atomic_load_relaxed(&mt->defs), newentry, &replaced, max_world, replaying ? image : (size_t)-1, oldvalue);
    }
    recording = recording && !replaying && replaced == NULL;
    jl_method_t *const *d;
    size_t j, n;
    if (oldvalue == NULL) {
        d = NULL;
        n = 0;
    }
    else {
        assert(jl_is_array(oldvalue));
        d = (jl_method_t**)jl_array_ptr_data((jl_array_t*)oldvalue);
        n = jl_array_nrows(oldvalue);
        oldmi = jl_alloc_vec_any(0); // the specializations whose dispatch may have changed
    }
    if (recording)
        newrecord = jl_alloc_vec_any(0);

    int precompiled_status = jl_atomic_load_relaxed(&method->dispatch_status);
    struct activate_env env = {
        max_world,
        jl_idset_max(interferences),
        // Always set LATEST_WHICH and carry over NO_LOSERS from initialization and across precompilation
        METHOD_SIG_LATEST_WHICH | (precompiled_status & METHOD_SIG_NO_LOSERS),
        /* .invalidated = */ 0,
    };
    if (oldvalue && replaced) {
        jl_method_t *m = replaced->func.method;
        env.invalidated = 1;
        method_overwrite(newentry, m);
        // This is an optimized version of below, given we know the type-intersection is exact
        jl_method_table_invalidate(m, max_world, 0);
        // The replacement strictly beats the replaced method (the recency
        // tiebreak in `jl_method_morespecific` for type-equal signatures).
        env.dispatch_bits &= ~METHOD_SIG_NO_LOSERS;
        // Clear METHOD_SIG_LATEST_WHICH bit
        jl_atomic_store_relaxed(&m->dispatch_status, 0);
        // Take over the interference list from the replaced method.
        // (TODO: we should consider recomputing it instead, since type-equal
        // doesn't imply more-specific-equal: an inherited edge may misstate
        // this method's specificity against a third method, making the
        // interference records incorrect.
        jl_genericmemory_t *m_interferences = jl_atomic_load_relaxed(&m->interferences);
        if (interferences->length == 0) {
            interferences = jl_genericmemory_copy(m_interferences);
        }
        else {
            for (size_t i = 0; i < m_interferences->length; i++) {
                jl_value_t *k = jl_genericmemory_ptr_ref(m_interferences, i);
                if (k && !has_key(interferences, (jl_value_t*)k)) {
                    ssize_t idx;
                    interferences = jl_idset_put_key(interferences, (jl_value_t*)k, &env.interferences_max, &idx);
                }
            }
        }
        ssize_t idx;
        size_t m_max = jl_idset_max(m_interferences);
        m_interferences = jl_idset_put_key(m_interferences, (jl_value_t*)method, &m_max, &idx);
        jl_gc_write_atomic(m, m->interferences, jl_genericmemory_t, m_interferences, release);
        // over every intersecting method, replayed and scanned alike (a replayed
        // method could not be the replaced one: the worker would have refused it)
        for (j = 0; j < n; j++) {
            jl_method_t *m2 = d[j];
            if (!m2 || m == m2)
                continue;
            if (method_in_interferences(m, m2)) {
                jl_genericmemory_t *m2_interferences = jl_atomic_load_relaxed(&m2->interferences);
                ssize_t idx;
                size_t m2_max = jl_idset_max(m2_interferences);
                m2_interferences = jl_idset_put_key(m2_interferences, (jl_value_t*)method, &m2_max, &idx);
                jl_gc_write_atomic(m2, m2->interferences, jl_genericmemory_t, m2_interferences, release);
            }
        }
        _Atomic(jl_method_instance_t*) *data;
        size_t l = method_specializations(m, &loctag, &data); // loctag roots the specializations
        for (size_t i = 0; i < l; i++) {
            jl_method_instance_t *mi = jl_atomic_load_relaxed(&data[i]);
            if ((jl_value_t*)mi == jl_nothing)
                continue;
            jl_array_ptr_1d_push(oldmi, (jl_value_t*)mi);
        }
        jl_method_instance_t *unspec = jl_atomic_load_relaxed(&m->unspecialized);
        if (unspec)
            jl_array_ptr_1d_push(oldmi, (jl_value_t*)unspec);
        d = NULL;
        n = 0;
    }
    else if (n > 0) {
        char *morespec = (char*)alloca(n);
        char *ambigs = (char*)alloca(n);
        // the specificity of the replayed head, as the worker's scan found it: a method
        // the record lists is not more specific (ambiguous when also in the preserved
        // interference set), one taken from that set alone is more specific
        for (j = 0; j < rn; j++) {
            morespec[j] = j >= nrec;
            ambigs[j] = j < nrec && has_key(interferences, (jl_value_t*)d[j]);
        }
        interferences = activate_against_methods(&env, method, type, d, n, morespec, ambigs, rn, interferences, oldmi, newrecord);
    }

    // the method joins the contributors of its typenames as it is activated
    contributor_tag_method(mt, method, contributor_tag_for(method));
    jl_methcache_t *mc = jl_method_table->cache;
    JL_LOCK(&mc->writelock);
    struct _typename_invalidate_backedge typename_env = {type, &isect, &isect2, d, n, max_world, env.invalidated};
    invalidate_missing_backedges(&typename_env);
    env.invalidated |= typename_env.invalidated;
    if (oldmi && jl_array_nrows(oldmi)) {
        if (deferred) {
            for (size_t i = 0, l = jl_array_nrows(oldmi); i < l; i++) {
                jl_array_ptr_1d_push(deferred, jl_array_ptr_ref(oldmi, i));
                jl_array_ptr_1d_push(deferred, type);
            }
        }
        else {
            // drop leafcache and search mc->cache and drop anything that might overlap with the new method
            // this is very cheap, so we don't mind being very conservative at over-approximating this
            struct invalidate_mt_env mt_cache_env;
            mt_cache_env.max_world = max_world;
            mt_cache_env.shadowed = oldmi;
            mt_cache_env.newentry_sig = type;

            jl_typemap_visitor(jl_atomic_load_relaxed(&mc->cache), invalidate_mt_cache, (void*)&mt_cache_env);
            invalidate_leafcache(mc, max_world);
        }
    }
    JL_UNLOCK(&mc->writelock);
    if (env.invalidated && _jl_debug_method_invalidation) {
        jl_array_ptr_1d_push(_jl_debug_method_invalidation, (jl_value_t*)method);
        loctag = jl_cstr_to_string("jl_method_table_insert");
        jl_array_ptr_1d_push(_jl_debug_method_invalidation, loctag);
    }
    jl_atomic_store_relaxed(&newentry->max_world, ~(size_t)0);
    jl_atomic_store_relaxed(&method->dispatch_status, env.dispatch_bits); // TODO: this should be sequenced fully after the world counter store
    jl_gc_write_atomic(method, method->interferences, jl_genericmemory_t, interferences, release);
    if (newrecord != NULL)
        record_ext_backinterferences(method, newrecord); // completed by the activations of the images loaded from now on
    JL_GC_POP();
}
```
-/
def jlMethodTableActivateWithRecord (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable)
    (newentry : TypemapEntry) : CM MethodTable := do
  let method := mt.methods[newentry.func]!
  let type := newentry.sig
  let world := method.primaryWorld
  let maxWorld := Nat.max (world - 1) mt.worldCounter
  let (dList, replaced?) ← getIntersectMatches n T ops mt newentry maxWorld []
  let d := dList.toArray
  let mut methods := mt.methods
  let mut interferences := method.interferences
  let precompiledStatus := method.dispatchStatus
  let mut dispatchBits := methodSigLatestWhich ||| (precompiledStatus &&& methodSigNoLosers)
  if !d.isEmpty && replaced?.isSome then
    let some repEntry := replaced? | throw "unreachable"
    let mUid := repEntry.func
    let m := methods[mUid]!
    -- The replacement strictly beats the replaced method (the recency
    -- tiebreak in `jl_method_morespecific` for type-equal signatures).
    dispatchBits := dispatchBits - (dispatchBits &&& methodSigNoLosers)
    -- Clear METHOD_SIG_LATEST_WHICH bit
    let m := { m with dispatchStatus := 0 }
    -- Take over the interference list from the replaced method.
    if interferences.isEmpty then
      interferences := m.interferences
    else
      for k in m.interferences do
        if !hasKey interferences k then
          interferences := interferences ++ [k]
    let m := { m with interferences := m.interferences ++ [method.uid] }
    methods := methods.set! mUid m
    for j in [0:d.size] do
      let m2Uid := d[j]!
      if m2Uid != mUid then
        let m2 := methods[m2Uid]!
        if methodInInterferences m m2 then
          let m2 := { m2 with interferences := m2.interferences ++ [method.uid] }
          methods := methods.set! m2Uid m2
  else if !d.isEmpty then
    let (methods', bits', intf') ← activateAgainstMethods ops methods method type d dispatchBits interferences
    methods := methods'
    dispatchBits := bits'
    interferences := intf'
  let defs' ← updateTypemapEntryWorlds n mt.defs method.uid world worldMax
  let method' := { method with
    primaryWorld := world
    dispatchStatus := dispatchBits
    interferences := interferences
  }
  methods := methods.set! method.uid method'
  return { mt with defs := defs', methods := methods }

/-- `jl_method_table_activate`

Julia source: src/gf.c:3906-3909 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void jl_method_table_activate(jl_typemap_entry_t *newentry)
{
    jl_method_table_activate_with_record(newentry, NULL, (size_t)-1, NULL);
}
```
-/
def jlMethodTableActivate (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable)
    (newentry : TypemapEntry) : CM MethodTable :=
  jlMethodTableActivateWithRecord n T ops mt newentry

/-- `jl_method_table_insert`

Julia source: src/gf.c:4132-4145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT void jl_method_table_insert(jl_methtable_t *mt, jl_method_t *method, jl_tupletype_t *simpletype)
{
    jl_typemap_entry_t *newentry = jl_method_table_add(mt, method, simpletype);
    JL_GC_PUSH1(&newentry);
    JL_LOCK(&world_counter_lock);
    if (!jl_atomic_load_relaxed(&allow_new_worlds))
        jl_error("Method changes have been disabled via a call to disable_new_worlds.");
    size_t world = jl_atomic_load_relaxed(&jl_world_counter) + 1;
    jl_atomic_store_relaxed(&method->primary_world, world);
    jl_method_table_activate(newentry);
    jl_atomic_store_release(&jl_world_counter, world);
    JL_UNLOCK(&world_counter_lock);
    JL_GC_POP();
}
```
-/
def jlMethodTableInsert (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable) (method : Method)
    (simpletype : Option Val := none) : CM MethodTable := do
  let uid := mt.methods.size
  let world := if method.primaryWorld == worldMax then mt.worldCounter + 1 else method.primaryWorld
  let method := { method with uid := uid, primaryWorld := world }
  let mt := { mt with methods := mt.methods.push method }
  let (mt, newentry) ← jlMethodTableAdd n T ops mt method simpletype
  let mt ← jlMethodTableActivate n T ops mt newentry
  let newWorldCounter := Nat.max mt.worldCounter world
  return { mt with worldCounter := newWorldCounter }

/-- `make_method_match`

Julia source: src/gf.c:5725-5734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_method_match_t *make_method_match(jl_tupletype_t *spec_types, jl_svec_t *sparams, jl_method_t *method, int fully_covers) JL_CANSAFEPOINT
{
    jl_task_t *ct = jl_current_task;
    jl_method_match_t *match = (jl_method_match_t*)jl_gc_alloc(ct->ptls, sizeof(jl_method_match_t), jl_method_match_type);
    match->spec_types = spec_types;
    match->sparams = sparams;
    match->method = method;
    match->fully_covers = fully_covers != 0;
    return match;
}
```
-/
def makeMethodMatch (specTypes : Val) (sparams : List Val) (method : Method) (fullyCovers : Bool) :
    MethodMatch :=
  { specTypes := specTypes, sparams := sparams, method := method, fullyCovers := fullyCovers }

/-- `struct ml_matches_env` (`src/gf.c:5713-5723`). -/
structure MlMatchesEnv where
  intersections : Bool
  world : Nat
  lim : Int
  includeAmbiguous : Bool
  t : Array MethodMatch := #[]
  matc : Option MethodMatch := none
  deriving Repr, Inhabited

/-- `ml_matches_visitor`

Julia source: src/gf.c:5742-5804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int ml_matches_visitor(jl_typemap_entry_t *ml, struct typemap_intersection_env *closure0) JL_CANSAFEPOINT
{
    struct ml_matches_env *closure = container_of(closure0, struct ml_matches_env, match);
    if (closure->intersections == 0 && !closure0->issubty)
        return 1;

    // First, check the world range of the typemap entry to ensure that it intersects
    // the query world. If it does not, narrow the result world range to guarantee
    // excluding it from the results is valid for the full span.
    size_t min_world = jl_atomic_load_relaxed(&ml->min_world);
    size_t max_world = jl_atomic_load_relaxed(&ml->max_world);
    if (closure->world < min_world) {
        // exclude method table entries that are part of a later world
        if (closure->match.max_valid >= min_world)
            closure->match.max_valid = min_world - 1;
        return 1;
    }
    else if (closure->world > max_world) {
        // exclude method table entries that have been replaced in the current world
        if (closure->match.min_valid <= max_world)
            closure->match.min_valid = max_world + 1;
        return 1;
    }
    // Every entry possibly matched here may affect the final answer,
    // whether directly or through ambiguity. Whether it affects the answer can be tricky to compute,
    // and unlikely to be profitable to be exact, so just use the range of every method intersected.
    if (closure->match.min_valid < min_world)
        closure->match.min_valid = min_world;
    if (closure->match.max_valid > max_world)
        closure->match.max_valid = max_world;
    jl_method_t *meth = ml->func.method;
    int only = jl_atomic_load_relaxed(&meth->interferences)->length == 0;
    if (closure->lim >= 0 && only) {
        if (closure->lim == 0) {
            closure->t = jl_an_empty_vec_any;
            return 0;
        }
        closure->lim--;
    }
    closure->matc = make_method_match((jl_tupletype_t*)closure->match.ti,
        closure->match.env, meth,
        closure->match.issubty);
    size_t len = jl_array_nrows(closure->t);
    if (closure->match.issubty && only) {
        if (len == 0)
            closure->t = (jl_value_t*)jl_alloc_vec_any(1);
        else if (len > 1)
            jl_array_del_end((jl_array_t*)closure->t, len - 1);
        jl_array_ptr_set(closure->t, 0, (jl_value_t*)closure->matc);
        return 0;
    }
    if (len == 0) {
        closure->t = (jl_value_t*)jl_alloc_vec_any(1);
        jl_array_ptr_set(closure->t, 0, (jl_value_t*)closure->matc);
    }
    else {
        jl_array_ptr_1d_push((jl_array_t*)closure->t, (jl_value_t*)closure->matc);
    }
    // don't need to consider other similar methods if this ml will always fully intersect with them and dominates all of them
    if (!closure->include_ambiguous || closure->lim != -1)
        typemap_bottom_search(ml, &closure->match);
    return 1;
}
```
-/
def mlMatchesVisitor (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable)
    (ml : TypemapEntry) (closure0 : TypemapIntersectionEnv) (env : MlMatchesEnv) :
    CM (Bool × TypemapIntersectionEnv × MlMatchesEnv) := do
  if !env.intersections && !closure0.issubty then
    return (true, closure0, env)
  let minWorld := ml.minWorld
  let maxWorld := ml.maxWorld
  let mut closure := closure0
  if env.world < minWorld then
    if closure.maxValid ≥ minWorld then
      closure := { closure with maxValid := minWorld - 1 }
    return (true, closure, env)
  else if env.world > maxWorld then
    if closure.minValid ≤ maxWorld then
      closure := { closure with minValid := maxWorld + 1 }
    return (true, closure, env)
  if closure.minValid < minWorld then
    closure := { closure with minValid := minWorld }
  if closure.maxValid > maxWorld then
    closure := { closure with maxValid := maxWorld }
  let meth := mt.methods[ml.func]!
  let only := meth.interferences.isEmpty
  let mut env := env
  if env.lim ≥ 0 && only then
    if env.lim == 0 then
      return (false, closure, { env with t := #[] })
    env := { env with lim := env.lim - 1 }
  let matc := makeMethodMatch closure.ti (closure.env.getD []) meth closure.issubty
  env := { env with matc := some matc }
  if closure.issubty && only then
    return (false, closure, { env with t := #[matc] })
  env := { env with t := env.t.push matc }
  if !env.includeAmbiguous || env.lim != -1 then
    closure ← typemapBottomSearch n T ops ml closure
  return (true, closure, env)

/-- `enum sort_state` (`src/gf.c:5822-5827`). -/
inductive SortState where
  | visiting
  | processingInterferences
  | checkCovers
  | finalizeScc
  deriving BEq, Repr, Inhabited

/-- `sort_stack_frame_t` (`src/gf.c:5829-5840`). -/
structure SortStackFrame where
  idx : Nat
  interferenceIndex : Nat := 0
  interferenceCount : Nat := 0
  depth : Nat := 0
  cycle : Nat := 0
  matc : Option MethodMatch := none
  m : Option Method := none
  ti : Val := .bottom
  childResult : Int := 0
  state : SortState := .visiting
  deriving Repr, Inhabited

/-- `sort_mlmatches`: Tarjan's SCC specificity sort over candidate matches `t`.
Returns `(finalResult, visited, stack, result, hasAmbiguity)`.

Julia source: src/gf.c:5846-6047 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int sort_mlmatches(jl_array_t *t, size_t idx, arraylist_t *visited, arraylist_t *stack, arraylist_t *result, int lim, int include_ambiguous, jl_method_t *minmaxm, int *has_ambiguity) JL_CANSAFEPOINT
{
    // Use arraylist_t for explicit stack of processing frames
    arraylist_t frame_stack;
    arraylist_new(&frame_stack, 0);

    // Push initial frame
    sort_stack_frame_t initial_frame = {
        .idx = idx,
        .interference_index = 0,
        .interference_count = 0,
        .depth = 0,
        .cycle = 0,
        .matc = NULL,
        .m = NULL,
        .ti = NULL,
        .child_result = 0,
        .state = STATE_VISITING
    };
    arraylist_push(&frame_stack, memcpy(malloc(sizeof(sort_stack_frame_t)), &initial_frame, sizeof(sort_stack_frame_t)));

    int final_result = 0;

    while (1) {
        sort_stack_frame_t *current = (sort_stack_frame_t*)frame_stack.items[frame_stack.len - 1];
        JL_GC_PROMISE_ROOTED(current->m);
        JL_GC_PROMISE_ROOTED(current->ti);

        switch (current->state) {
            case STATE_VISITING: {
                size_t cycle = (size_t)visited->items[current->idx];
                if (cycle != 0) {
                    final_result = cycle - 1;
                    goto propagate_to_parent;
                }

                arraylist_push(stack, (void*)current->idx);
                current->depth = stack->len;
                visited->items[current->idx] = (void*)(1 + current->depth);
                current->matc = (jl_method_match_t*)jl_array_ptr_ref(t, current->idx);
                current->m = current->matc->method;
                current->ti = (jl_value_t*)current->matc->spec_types;
                current->cycle = current->depth;
                current->interference_count = jl_atomic_load_relaxed(&current->m->interferences)->length;
                current->interference_index = 0;
                current->state = STATE_PROCESSING_INTERFERENCES;
                break;
            }

            case STATE_PROCESSING_INTERFERENCES: {
                // If we have a child result to process, handle it first
                if (current->child_result != 0) {
                    if (current->child_result == -1) {
                        final_result = -1;
                        goto propagate_to_parent;
                    }
                    // record the cycle will resolve at depth "cycle"
                    if (current->child_result && current->child_result < current->cycle)
                        current->cycle = current->child_result;
                    current->child_result = 0; // Clear after processing
                }

                // Process interferences iteratively.
                while (current->interference_index < current->interference_count) {
                    jl_genericmemory_t *interferences = jl_atomic_load_relaxed(&current->m->interferences);
                    jl_method_t *m2 = (jl_method_t*)jl_genericmemory_ptr_ref(interferences, current->interference_index);
                    current->interference_index++;

                    if (m2 == NULL)
                        continue;

                    int childidx = find_method_in_matches(t, m2);
                    if (childidx < 0 || (size_t)childidx == current->idx)
                        continue;

                    int child_cycle = (size_t)visited->items[childidx];
                    if (child_cycle == 1)
                        continue; // already handled
                    if (child_cycle != 0 && child_cycle - 1 >= current->cycle)
                        continue; // already part of this cycle
                    if (method_in_interferences(current->m, m2))
                        continue;

                    // m2 is morespecific, so attempt to visit it first
                    if (child_cycle != 0) {
                        // Child already being processed, use cached result
                        int child_result = child_cycle - 1;
                        if (child_result == -1) {
                            final_result = -1;
                            goto propagate_to_parent;
                        }
                        if (child_result && child_result < current->cycle)
                            current->cycle = child_result;
                    }
                    else {
                        // Need to process child - push new frame and pause current processing
                        sort_stack_frame_t child_frame = {
                            .idx = childidx,
                            .interference_index = 0,
                            .interference_count = 0,
                            .depth = 0,
                            .cycle = 0,
                            .matc = NULL,
                            .m = NULL,
                            .ti = NULL,
                            .child_result = 0,
                            .state = STATE_VISITING
                        };
                        arraylist_push(&frame_stack, memcpy(malloc(sizeof(sort_stack_frame_t)), &child_frame, sizeof(sort_stack_frame_t)));
                        goto continue_main_loop; // Resume processing after child completes
                    }
                }

                current->state = STATE_CHECK_COVERS;
                break;
            }

            case STATE_CHECK_COVERS: {
                // There is some probability that this method is already fully covered
                // now, and we can delete this vertex now without anyone noticing.
               if (check_interferences_covers(current->m, current->ti, t, visited, minmaxm, include_ambiguous, has_ambiguity)) {
                    visited->items[current->idx] = (void*)1;
                }
                else if (check_fully_ambiguous(current->m, current->ti, t, include_ambiguous, has_ambiguity)) {
                    visited->items[current->idx] = (void*)1;
                }

                // If there were no cycles hit either, then we can potentially delete all of its edges too.
                if ((size_t)visited->items[current->idx] == 1 && stack->len == current->depth) {
                    // n.b. cycle might be < depth, if we had a cycle with a child
                    // idx, but since we are on the top of the stack, nobody
                    // observed that and so we are content to ignore this
                    size_t childidx = (size_t)arraylist_pop(stack);
                    assert(childidx == current->idx); (void)childidx;
                    final_result = 0;
                    goto propagate_to_parent;
                }

                if (current->cycle != current->depth) {
                    final_result = current->cycle;
                    goto propagate_to_parent;
                }

                current->state = STATE_FINALIZE_SCC;
                break;
            }

            case STATE_FINALIZE_SCC: {
                // If this is in an SCC group, do some additional checks before returning or setting has_ambiguity
                if (current->depth != stack->len) {
                    int scc_count = 0;
                    for (size_t i = current->depth - 1; i < stack->len; i++) {
                        size_t childidx = (size_t)stack->items[i];
                        if (visited->items[childidx] == (void*)1)
                            continue;
                        scc_count++;
                    }
                    if (scc_count > 1)
                        *has_ambiguity = 1;
                }

                // copy this cycle into the results
                for (size_t i = current->depth - 1; i < stack->len; i++) {
                    size_t childidx = (size_t)stack->items[i];
                    if ((size_t)visited->items[childidx] == 1)
                        continue;
                    assert(visited->items[childidx] == (void*)(2 + i));
                    visited->items[childidx] = (void*)1;
                    if (lim == -1 || result->len < lim)
                        arraylist_push(result, (void*)childidx);
                    else {
                        final_result = -1;
                        goto propagate_to_parent;
                    }
                }

                // now finally cleanup the stack
                while (stack->len >= current->depth) {
                    size_t childidx = (size_t)arraylist_pop(stack);
                    assert(visited->items[childidx] == (void*)1); (void)childidx;
                }

                final_result = 0;
                goto propagate_to_parent;
            }
        }

        continue_main_loop:
            continue;

        propagate_to_parent:
            // Propagate result to parent if exists
            free(arraylist_pop(&frame_stack));
            if (frame_stack.len == 0)
                break;
            sort_stack_frame_t *parent = (sort_stack_frame_t*)frame_stack.items[frame_stack.len - 1];
            parent->child_result = final_result;
    }
    assert(frame_stack.len == 0);
    arraylist_free(&frame_stack);
    return final_result;
}
```
-/
def sortMlmatches (n : Nat) (T : Types) (ops : GfOps) (t : Array MethodMatch) (idx : Nat)
    (visited : Array Nat) (stack : Array Nat) (result : Array Nat) (lim : Int)
    (includeAmbiguous : Bool) (minmaxm : Option Method) (hasAmbiguity : Bool) :
    CM (Int × Array Nat × Array Nat × Array Nat × Bool) := do
  let initialFrame : SortStackFrame := { idx := idx, state := .visiting }
  let mut frameStack : Array SortStackFrame := #[initialFrame]
  let mut visited := visited
  let mut stack := stack
  let mut result := result
  let mut hasAmbiguity := hasAmbiguity
  let mut finalResult : Int := 0
  let mut steps := n
  while !frameStack.isEmpty do
    if steps == 0 then outOfBudget
    steps := steps - 1
    let topIdx := frameStack.size - 1
    let mut current := frameStack[topIdx]!
    let mut propagate := false
    let mut pushedChild : Option SortStackFrame := none
    match current.state with
    | .visiting =>
      let cycle := visited[current.idx]!
      if cycle != 0 then
        finalResult := Int.ofNat cycle - 1
        propagate := true
      else
        stack := stack.push current.idx
        let depth := stack.size
        visited := visited.set! current.idx (1 + depth)
        let matc := t[current.idx]!
        let m := matc.method
        current := { current with
          depth := depth
          matc := some matc
          m := some m
          ti := matc.specTypes
          cycle := depth
          interferenceCount := m.interferences.length
          interferenceIndex := 0
          state := .processingInterferences
        }
        frameStack := frameStack.set! topIdx current
    | .processingInterferences =>
      if current.childResult != 0 then
        if current.childResult == -1 then
          finalResult := -1
          propagate := true
        else
          if current.childResult > 0 && current.childResult.toNat < current.cycle then
            current := { current with cycle := current.childResult.toNat }
          current := { current with childResult := 0 }
      if !propagate then
        let m := current.m.getD default
        while current.interferenceIndex < current.interferenceCount do
          let m2id := m.interferences[current.interferenceIndex]!
          current := { current with interferenceIndex := current.interferenceIndex + 1 }
          let some childidx := findMethodInMatches t m2id | continue
          if childidx == current.idx then
            continue
          let childCycle := visited[childidx]!
          if childCycle == 1 then
            continue -- already handled
          if childCycle != 0 && childCycle - 1 ≥ current.cycle then
            continue -- already part of this cycle
          let m2 := t[childidx]!.method
          if methodInInterferences m m2 then
            continue
          -- m2 is morespecific, so attempt to visit it first
          if childCycle != 0 then
            let childRes : Int := Int.ofNat childCycle - 1
            if childRes == -1 then
              finalResult := -1
              propagate := true
              break
            if childRes > 0 && childRes.toNat < current.cycle then
              current := { current with cycle := childRes.toNat }
          else
            pushedChild := some { idx := childidx, state := .visiting }
            break
        if !propagate then
          if let some childFrame := pushedChild then
            frameStack := frameStack.set! topIdx current
            frameStack := frameStack.push childFrame
          else
            current := { current with state := .checkCovers }
            frameStack := frameStack.set! topIdx current
    | .checkCovers =>
      let m := current.m.getD default
      let (covered, hasAmbig1) ← checkInterferencesCovers n T ops m current.ti t visited minmaxm includeAmbiguous hasAmbiguity
      hasAmbiguity := hasAmbig1
      if covered then
        visited := visited.set! current.idx 1
      else
        let (ambigDrop, hasAmbig2) ← checkFullyAmbiguous ops m current.ti t includeAmbiguous hasAmbiguity
        hasAmbiguity := hasAmbig2
        if ambigDrop then
          visited := visited.set! current.idx 1
      if visited[current.idx]! == 1 && stack.size == current.depth then
        stack := stack.pop
        finalResult := 0
        propagate := true
      else if current.cycle != current.depth then
        finalResult := Int.ofNat current.cycle
        propagate := true
      else
        current := { current with state := .finalizeScc }
        frameStack := frameStack.set! topIdx current
    | .finalizeScc =>
      if current.depth != stack.size then
        let mut sccCount : Nat := 0
        for i in [current.depth - 1 : stack.size] do
          let childidx := stack[i]!
          if visited[childidx]! == 1 then
            continue
          sccCount := sccCount + 1
        if sccCount > 1 then
          hasAmbiguity := true
      for i in [current.depth - 1 : stack.size] do
        let childidx := stack[i]!
        if visited[childidx]! == 1 then
          continue
        visited := visited.set! childidx 1
        if lim == -1 || Int.ofNat result.size < lim then
          result := result.push childidx
        else
          finalResult := -1
          propagate := true
          break
      if !propagate then
        while stack.size ≥ current.depth do
          stack := stack.pop
        finalResult := 0
        propagate := true
    if propagate then
      frameStack := frameStack.pop
      if frameStack.isEmpty then
        break
      let pIdx := frameStack.size - 1
      let parent := frameStack[pIdx]!
      frameStack := frameStack.set! pIdx { parent with childResult := finalResult }
  return (finalResult, visited, stack, result, hasAmbiguity)

/-- `sort_method_matches`: sort the intersecting matches in `t` into dispatch order, removing
every match that can never be the dispatch target over its intersection with the query.
Returns `(sorted?, hasAmbiguity)`, where `sorted?` is `none` if `lim` was exceeded (`-1` in C).

Julia source: src/gf.c:6069-6248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static ssize_t sort_method_matches(jl_array_t *t, int lim, int include_ambiguous, int approximate_ambig, int *has_ambiguity_out) JL_CANSAFEPOINT
{
    int has_ambiguity = 0;
    size_t i, j, len = jl_array_nrows(t);
    size_t len_in = len;

    // the 'minmax' method is a method that (1) fully-covers the queried type, and (2) is
    // more-specific than any other fully-covering method (but if !all_subtypes, there are
    // non-fully-covering methods to which it is _likely_ not more specific).
    // n.b. its absence does not mean the query is unresolvable, and in particular
    // must not be short-circuited into an empty result: the sort below still has to
    // run to compute `has_ambiguity` and to keep the matches that witness the
    // ambiguity, else an ambiguous call would be reported as having no applicable
    // method (see test `AmbigNoBeatAll`).
    jl_method_match_t *minmax = NULL;
    size_t minmax_idx = 0;
    int minmax_dominates = 0;
    int any_subtypes = 0;
    if (len > 1) {
        // First try to pre-process the results to find the most specific option
        // among the fully-covering methods, since we can do this in O(n^2)
        // time, and the rest is O(n^3).
        //   - First, find a candidate for the best of these method results.
        for (i = 0; i < len; i++) {
            jl_method_match_t *matc = (jl_method_match_t*)jl_array_ptr_ref(t, i);
            if (matc->fully_covers) {
                any_subtypes = 1;
                jl_method_t *m = matc->method;
                // A fully-covering match with an empty interference set is
                // strictly morespecific than every method it intersects
                // meaning it is already proven to be the `minmax` choice
                // without exploring the list any further.
                if (jl_atomic_load_relaxed(&m->interferences)->length == 0) {
                    minmax = matc;
                    minmax_idx = i;
                    minmax_dominates = 1;
                    break;
                }
                for (j = 0; j < len; j++) {
                    if (i == j)
                        continue;
                    jl_method_match_t *matc2 = (jl_method_match_t*)jl_array_ptr_ref(t, j);
                    if (matc2->fully_covers) {
                        jl_method_t *m2 = matc2->method;
                        if (!method_morespecific_recorded(m, m2))
                            break;
                    }
                }
                if (j == len) {
                    // Found the minmax method.
                    minmax = matc;
                    minmax_idx = i;
                    break;
                }
            }
        }
        //   - It may even dominate (be more specific than) some choices that are not fully-covering!
        //     If it dominates all of them, the fast-return below applies; otherwise
        //     the sort rediscovers minmax as the certifying cover for each match it
        //     dominates (`check_interferences_covers` probes it first).
        //   - We could always check here if *any* fully-covering method is
        //     more-specific (instead of just considering minmax), but that may
        //     cost much extra and is less likely to help us hit a fast path
        //     (we will look for this later, when we compute the full sort).
        int all_subtypes = any_subtypes;
        if (any_subtypes && !minmax_dominates) {
            jl_method_t *minmaxm = NULL;
            if (minmax != NULL)
                minmaxm = minmax->method;
            for (i = 0; i < len; i++) {
                jl_method_match_t *matc = (jl_method_match_t*)jl_array_ptr_ref(t, i);
                if (!matc->fully_covers) {
                    jl_method_t *m = matc->method;
                    if (minmaxm != NULL && method_morespecific_recorded(minmaxm, m))
                        continue; // minmax dominates this match too
                    all_subtypes = 0;
                    break;
                }
            }
        }
        //    - Now we might have a fast-return here, if we see that
        //      we've already processed all of the possible outputs.
        if (all_subtypes) {
            if (minmax == NULL) {
                // All intersecting methods are fully-covering, but none of them
                // is more specific than every other one. Since `morespecific` is
                // not transitive, that does not make the call unresolvable: the
                // comparison may be blocked by a method that is itself dominated
                // (m1 ≻ m2, m2 ≻ m3, m3 unordered with m1 leaves no
                // beat-everything winner even though removing m2 and m3 leaves
                // m1 alone). Fall through to the coverage and SCC pass below,
                // which removes the dominated matches and reports an ambiguity
                // only if one actually remains.
            }
            else {
                // `minmax` is more-specific than all other matches and is fully-covering
                // we can return it as our only result
                jl_array_ptr_set(t, 0, minmax);
                jl_array_del_end(t, len - 1);
                len = 1;
            }
        }
        if (minmax && lim == 0) {
            // protect some later algorithms from underflow
            return -1;
        }
    }
    if (len > 1) {
        arraylist_t stack, visited, result;
        arraylist_new(&result, lim != -1 && lim < len ? lim : len);
        arraylist_new(&stack, 0);
        arraylist_new(&visited, len);
        arraylist_grow(&visited, len);
        memset(visited.items, 0, len * sizeof(size_t));
        // minmax is reported unconditionally (appended after the sort below),
        // so pre-mark it as finalized: the sort then never visits it, and it is
        // admissible as a cover for every dominance check, so a match it
        // dominates is certified against it together with the other finalized
        // covers and their union -- a lone minmax transfer could consult
        // neither (tests `AmbigMinmaxSkip`, `AmbigMinmaxUnion`).
        jl_method_t *minmaxm = NULL;
        if (minmax != NULL) {
            minmaxm = minmax->method;
            assert((jl_method_match_t*)jl_array_ptr_ref(t, minmax_idx) == minmax);
            visited.items[minmax_idx] = (void*)1;
        }
        if (approximate_ambig) // if we don't care about the result, set it now so we won't bother attempting to compute it accurately later
            has_ambiguity = 1;
        for (i = 0; i < len; i++) {
            assert(visited.items[i] == (void*)0 || visited.items[i] == (void*)1);
            int child_cycle = sort_mlmatches(t, i, &visited, &stack, &result, lim == -1 || minmax == NULL ? lim : lim - 1, include_ambiguous, minmaxm, &has_ambiguity);
            if (child_cycle == -1) {
                arraylist_free(&visited);
                arraylist_free(&stack);
                arraylist_free(&result);
                return -1;
            }
            assert(child_cycle == 0); (void)child_cycle;
            assert(stack.len == 0);
            assert(visited.items[i] == (void*)1);
        }
        arraylist_free(&visited);
        arraylist_free(&stack);
        for (j = 0; j < result.len; j++) {
            i = (size_t)result.items[j];
            result.items[j] = (void*)jl_array_ptr_ref(t, i);
        }
        if (minmax) {
            arraylist_push(&result, minmax);
            j++;
        }
        // A method is only selected when it is morespecific than every applicable
        // method, so an ambiguity has to be witnessed by at least two reported
        // methods: with only one left, the caller would read the result as a
        // resolved call (and an error would come out as `no method matching`).
        // Since a dominated match may only be dropped above when the matches that
        // certified the removal also block everything it was blocking
        // (`check_dominance_transfer`), the last blocker of the survivor
        // should not have been removed.
        // (n.b. `approximate_ambig` sets `has_ambiguity` without computing it)
        assert(!(include_ambiguous && !approximate_ambig && has_ambiguity && result.len == 1) &&
               "dropped the last witness of an ambiguity");
        memcpy(jl_array_data(t, jl_method_match_t*), result.items, j * sizeof(jl_method_match_t*));
        arraylist_free(&result);
        if (j != len)
            jl_array_del_end(t, len - j);
        len = j;
    }
    // Every match can only be removed by being dominated or by being part of an
    // ambiguity, and a chain of dominated matches has to bottom out somewhere
    // unless it makes a cycle (which is an ambiguity). So emptying a non-empty
    // match list means the query is ambiguous, never that no method applies --
    // reporting the latter would turn an ambiguous call into a `no method
    // matching` error (test `AmbigNoBeatAll`).
    assert((len > 0 || len_in == 0 || has_ambiguity) &&
           "dropped every applicable method without recording an ambiguity");
    (void)len_in;
    *has_ambiguity_out = has_ambiguity;
    return len;
}
```
-/
def sortMethodMatches (n : Nat) (T : Types) (ops : GfOps) (t : Array MethodMatch) (lim : Int)
    (includeAmbiguous : Bool) (approximateAmbig : Bool) :
    CM (Option (Array MethodMatch) × Bool) := do
  let mut hasAmbiguity := false
  let mut t := t
  let mut len := t.size
  let mut minmax : Option MethodMatch := none
  let mut minmaxIdx : Nat := 0
  let mut minmaxDominates := false
  let mut anySubtypes := false
  if len > 1 then
    for i in [0:len] do
      let matc := t[i]!
      if matc.fullyCovers then
        anySubtypes := true
        let m := matc.method
        if m.interferences.isEmpty then
          minmax := some matc
          minmaxIdx := i
          minmaxDominates := true
          break
        let mut beatsAll := true
        for j in [0:len] do
          if i == j then continue
          let matc2 := t[j]!
          if matc2.fullyCovers then
            let m2 := matc2.method
            if !methodMorespecificRecorded m m2 then
              beatsAll := false
              break
        if beatsAll then
          minmax := some matc
          minmaxIdx := i
          break
    let mut allSubtypes := anySubtypes
    if anySubtypes && !minmaxDominates then
      let minmaxm := minmax.map (·.method)
      for i in [0:len] do
        let matc := t[i]!
        if !matc.fullyCovers then
          let m := matc.method
          let dom := match minmaxm with
            | some mm => methodMorespecificRecorded mm m
            | none => false
          if !dom then
            allSubtypes := false
            break
    if allSubtypes then
      if let some mm := minmax then
        t := #[mm]
        len := 1
    if minmax.isSome && lim == 0 then
      return (none, hasAmbiguity)
  if len > 1 then
    let mut result : Array Nat := #[]
    let mut stack : Array Nat := #[]
    let mut visited : Array Nat := Array.mk (List.replicate len 0)
    let minmaxm := minmax.map (·.method)
    if minmax.isSome then
      visited := visited.set! minmaxIdx 1
    if approximateAmbig then
      hasAmbiguity := true
    let subLim : Int := if lim == -1 || minmax.isNone then lim else lim - 1
    for i in [0:len] do
      let (childCycle, vis', stk', res', hasAmbig') ←
        sortMlmatches n T ops t i visited stack result subLim includeAmbiguous minmaxm hasAmbiguity
      visited := vis'
      stack := stk'
      result := res'
      hasAmbiguity := hasAmbig'
      if childCycle == -1 then
        return (none, hasAmbiguity)
    let mut outMatches : Array MethodMatch := result.map fun idx => t[idx]!
    if let some mm := minmax then
      outMatches := outMatches.push mm
    t := outMatches
  return (some t, hasAmbiguity)

/-- `jl_sort_method_matches`

Julia source: src/gf.c:6256-6263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_sort_method_matches(jl_array_t *t, int include_ambiguous) JL_CANSAFEPOINT
{
    JL_TYPECHK(sort_method_matches, array_any, (jl_value_t*)t);
    int has_ambiguity = 0;
    ssize_t sorted = sort_method_matches(t, -1, include_ambiguous, 0, &has_ambiguity);
    assert(sorted != -1); (void)sorted; // lim == -1 cannot be exceeded
    return has_ambiguity;
}
```
-/
def jlSortMethodMatches (n : Nat) (T : Types) (ops : GfOps) (t : Array MethodMatch)
    (includeAmbiguous : Bool) : CM (Array MethodMatch × Bool) := do
  let (sorted?, hasAmbiguity) ← sortMethodMatches n T ops t (-1) includeAmbiguous false
  return (sorted?.getD #[], hasAmbiguity)

/-- `ml_matches`: collect form of calling `jl_typemap_intersection_visitor` with optimizations
to skip fully shadowed methods. Returns `(matches?, minValid, maxValid, hasAmbiguity)`.

Julia source: src/gf.c:6274-6446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *ml_matches(jl_methtable_t *mt, jl_methcache_t *mc,
                              jl_tupletype_t *type, int lim, int include_ambiguous,
                              int intersections, size_t world, int cache_result_recursion,
                              size_t *min_valid, size_t *max_valid, int *ambig)
{
    size_t current_world = jl_atomic_load_acquire(&jl_world_counter);
    if (world > current_world)
        return jl_nothing; // the future is not enumerable
    JL_TIMING(METHOD_MATCH, METHOD_MATCH);
    int has_ambiguity = 0;
    jl_value_t *unw = jl_unwrap_unionall((jl_value_t*)type);
    assert(jl_is_datatype(unw));
    size_t l = jl_svec_len(((jl_datatype_t*)unw)->parameters);
    jl_value_t *va = NULL;
    if (l > 0) {
        va = jl_tparam(unw, l - 1);
        if (jl_is_vararg(va))
            va = jl_unwrap_vararg(va);
        else
            va = NULL;
    }
    struct ml_matches_env env = {
        /* match */ {
            /* inputs */
            /* fptr / callback */ ml_matches_visitor,
            /* sig */ (jl_value_t*)type,
            /* vararg type / tparam0 */ va,

            /* temporaries */
            /* .search_bottom = */ 0,

            /* outputs */
            /* .min_valid = */ *min_valid,
            /* .max_valid = */ *max_valid,
            /* .ti = */ NULL,
            /* .env = */ jl_emptysvec,
            /* .issubty = */ 0
        },
        /* inputs */
        intersections,
        world,
        lim,
        include_ambiguous,

        /* outputs */
        /* .t = */ jl_an_empty_vec_any,

        /* temporaries */
        /* .matc = */ NULL
    };
    struct jl_typemap_assoc search = {(jl_value_t*)type, world, jl_emptysvec};
    jl_value_t *isect2 = NULL;
    JL_GC_PUSH6(&env.t, &env.matc, &env.match.env, &search.env, &env.match.ti, &isect2);

    if (mc) {
        // first check the leaf cache if the type might have been put in there
        if (((jl_datatype_t*)unw)->isdispatchtuple) {
            jl_genericmemory_t *leafcache = jl_atomic_load_relaxed(&mc->leafcache);
            jl_typemap_entry_t *entry = lookup_leafcache(leafcache, (jl_value_t*)type, world);
            if (entry) {
                // leafcache found a match, construct the MethodMatch by computing the effective
                // types + sparams and the world bounds
                jl_method_instance_t *mi = typemap_entry_linfo(entry);
                jl_method_t *meth = mi->def.method;
                if (!jl_is_unionall(meth->sig)) {
                    env.match.env = jl_emptysvec;
                    env.match.ti = unw;
                }
                else if (jl_egal((jl_value_t*)type, mi->specTypes)) {
                    env.match.env = mi->sparam_vals;
                    env.match.ti = mi->specTypes;
                }
                else {
                    // this just calls jl_subtype_env (since we know that `type <: meth->sig` by transitivity)
                    env.match.ti = jl_type_intersection_env((jl_value_t*)type, (jl_value_t*)meth->sig, &env.match.env);
                }
                env.matc = make_method_match((jl_tupletype_t*)env.match.ti,
                    env.match.env, meth, 1);
                env.t = (jl_value_t*)jl_alloc_vec_any(1);
                jl_array_ptr_set(env.t, 0, env.matc);
                size_t min_world = jl_atomic_load_relaxed(&entry->min_world);
                size_t max_world = jl_atomic_load_relaxed(&entry->max_world);
                if (*min_valid < min_world)
                    *min_valid = min_world;
                if (*max_valid > max_world)
                    *max_valid = max_world;
                JL_GC_POP();
                return env.t;
            }
        }

        // then check the full cache if it seems profitable
        if (((jl_datatype_t*)unw)->isdispatchtuple) {
            jl_typemap_entry_t *entry = jl_typemap_assoc_by_type(jl_atomic_load_relaxed(&mc->cache), &search, jl_cachearg_offset(), /*subtype*/1);
            if (entry && (((jl_datatype_t*)unw)->isdispatchtuple || entry->guardsigs == jl_emptysvec)) {
                // full cache found a match, construct the MethodMatch by computing the effective
                // types + sparams and the world bounds
                jl_method_instance_t *mi = typemap_entry_linfo(entry);
                jl_method_t *meth = mi->def.method;
                size_t min_world = jl_atomic_load_relaxed(&entry->min_world);
                // only return this if it appears min_would is fully computed, otherwise do the full lookup to compute min_world exactly
                if (min_world == jl_atomic_load_relaxed(&meth->primary_world)) {
                    size_t max_world = jl_atomic_load_relaxed(&entry->max_world);
                    if (!jl_is_unionall(meth->sig) && ((jl_datatype_t*)unw)->isdispatchtuple) {
                        env.match.env = jl_emptysvec;
                        env.match.ti = unw;
                    }
                    else {
                        // this just calls jl_subtype_env (since we know that `type <: meth->sig` by transitivity)
                        env.match.ti = jl_type_intersection_env((jl_value_t*)type, (jl_value_t*)meth->sig, &env.match.env);
                    }
                    env.matc = make_method_match((jl_tupletype_t*)env.match.ti,
                        env.match.env, meth, 1);
                    env.t = (jl_value_t*)jl_alloc_vec_any(1);
                    jl_array_ptr_set(env.t, 0, env.matc);
                    if (*min_valid < min_world)
                        *min_valid = min_world;
                    if (*max_valid > max_world)
                        *max_valid = max_world;
                    JL_GC_POP();
                    return env.t;
                }
            }
        }
    }
    // then scan everything
    if (!jl_typemap_intersection_visitor(jl_atomic_load_relaxed(&mt->defs), 0, &env.match) && env.t == jl_an_empty_vec_any) {
        JL_GC_POP();
        // if we return early without returning methods, lim was proven to be exceeded
        // during the search set only the min/max valid collected from matching
        *min_valid = env.match.min_valid;
        *max_valid = env.match.max_valid;
        return jl_nothing;
    }
    // if we return early, set only the min/max valid collected from matching
    *min_valid = env.match.min_valid;
    *max_valid = env.match.max_valid;
    // done with many of these values now
    env.match.ti = NULL; env.matc = NULL; env.match.env = NULL; search.env = NULL;

    // all intersecting methods have been collected now. the remaining work is to sort
    // these and apply specificity to determine a list of dispatch-possible call targets
    size_t len;
    {
        ssize_t sorted = sort_method_matches((jl_array_t*)env.t, lim, include_ambiguous, ambig == NULL, &has_ambiguity);
        if (sorted == -1) {
            JL_GC_POP();
            return jl_nothing;
        }
        len = (size_t)sorted;
    }
    if (mc && cache_result_recursion && ((jl_datatype_t*)unw)->isdispatchtuple) { // cache_result_recursion prevents lock confusion and unnecessary work
        if (len == 1 && !has_ambiguity) {
            env.matc = (jl_method_match_t*)jl_array_ptr_ref(env.t, 0);
            jl_method_t *meth = env.matc->method;
            jl_svec_t *tpenv = env.matc->sparams;
            JL_LOCK(&mc->writelock);
            // a matching entry may already be present here (e.g. ml_matches fell
            // through the full-cache check above to recompute min_world exactly),
            // so cache_method must keep its own presence check to avoid a
            // duplicate insertion
            cache_result(mt, mc, &mc->cache, (jl_value_t*)mc, (jl_tupletype_t*)unw, meth, world, env.match.min_valid, env.match.max_valid, current_world, tpenv, /*tt_known_absent*/0);
        }
    }
    *min_valid = env.match.min_valid;
    *max_valid = env.match.max_valid;
    if (ambig != NULL)
        *ambig = has_ambiguity;
    JL_GC_POP();
    if (lim >= 0 && len > lim)
        return jl_nothing;
    return env.t;
}
```
-/
def mlMatches (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable) (type : Val) (lim : Int)
    (includeAmbiguous : Bool) (intersections : Bool) (world : Nat) (minValid maxValid : Nat)
    (wantAmbig : Bool) : CM (Option (List MethodMatch) × Nat × Nat × Bool) := do
  let currentWorld := mt.worldCounter
  if world > currentWorld then
    return (none, minValid, maxValid, false) -- the future is not enumerable
  let unw := type.unwrapUnionall
  let l := unw.nparams
  let va : Option Val :=
    if l > 0 then
      let last := unw.params[l - 1]!
      if last.isVararg then some last.unwrapVararg else none
    else
      none
  let matchEnv : TypemapIntersectionEnv := {
    type := type
    va := va
    searchBottom := 0
    minValid := minValid
    maxValid := maxValid
    ti := .bottom
    env := some []
    issubty := false
    emptinessOnly := false
  }
  let initEnv : MlMatchesEnv := {
    intersections := intersections
    world := world
    lim := lim
    includeAmbiguous := includeAmbiguous
    t := #[]
    matc := none
  }
  let (ok, matchEnvOut, mlEnvOut) ← jlTypemapIntersectionVisitor n T ops mt.defs 0 matchEnv initEnv
    (mlMatchesVisitor n T ops mt) none
  let minValid := matchEnvOut.minValid
  let maxValid := matchEnvOut.maxValid
  if !ok && mlEnvOut.t.isEmpty then
    return (none, minValid, maxValid, false)
  let (sorted?, hasAmbiguity) ←
    sortMethodMatches n T ops mlEnvOut.t lim includeAmbiguous (!wantAmbig)
  let some sorted := sorted? | return (none, minValid, maxValid, hasAmbiguity)
  if lim ≥ 0 && Int.ofNat sorted.size > lim then
    return (none, minValid, maxValid, hasAmbiguity)
  return (some sorted.toList, minValid, maxValid, hasAmbiguity)

/-- `jl_matching_methods`

Julia source: src/gf.c:4234-4248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_matching_methods(jl_tupletype_t *types, jl_value_t *mt, int lim, int include_ambiguous,
                                             size_t world, size_t *min_valid, size_t *max_valid, int *ambig)
{
    if (ambig != NULL)
        *ambig = 0;
    jl_value_t *unw = jl_unwrap_unionall((jl_value_t*)types);
    if (!jl_is_tuple_type(unw))
        return (jl_value_t*)jl_an_empty_vec_any;
    if (unw == (jl_value_t*)jl_emptytuple_type || jl_tparam0(unw) == jl_bottom_type)
        return (jl_value_t*)jl_an_empty_vec_any;
    if (mt == jl_nothing)
        mt = (jl_value_t*)jl_method_table;
    jl_methcache_t *mc = ((jl_methtable_t*)mt)->cache;
    return ml_matches((jl_methtable_t*)mt, mc, types, lim, include_ambiguous, 1, world, 1, min_valid, max_valid, ambig);
}
```
-/
def jlMatchingMethods (n : Nat) (T : Types) (ops : GfOps) (types : Val) (mt : MethodTable)
    (lim : Int) (includeAmbiguous : Bool) (world : Nat) (minValid maxValid : Nat)
    (wantAmbig : Bool := true) : CM (Option (List MethodMatch) × Nat × Nat × Bool) := do
  let unw := types.unwrapUnionall
  if !unw.isTupleType then
    return (some [], minValid, maxValid, false)
  if unw == emptytupleType || unw.params.head? == some .bottom then
    return (some [], minValid, maxValid, false)
  mlMatches n T ops mt types lim includeAmbiguous true world minValid maxValid wantAmbig

/-- `jl_argtype_with_function_type`

Julia source: src/gf.c:5188-5202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_argtype_with_function_type(jl_value_t *ft JL_MAYBE_UNROOTED, jl_value_t *types0)
{
    jl_value_t *types = jl_unwrap_unionall(types0);
    size_t l = jl_nparams(types);
    jl_value_t *tt = NULL;
    JL_GC_PUSH2(&tt, &ft);
    tt = (jl_value_t*)jl_alloc_svec(1+l);
    jl_svecset(tt, 0, ft);
    for (size_t i = 0; i < l; i++)
        jl_svecset(tt, i+1, jl_tparam(types,i));
    tt = (jl_value_t*)jl_apply_tuple_type((jl_svec_t*)tt, 1);
    tt = jl_rewrap_unionall_(tt, types0);
    JL_GC_POP();
    return tt;
}
```
-/
def jlArgtypeWithFunctionType (n : Nat) (T : Types) (ops : GfOps) (ft types0 : Val) : CM Val := do
  let T := withBuiltinTypes T
  let types := types0.unwrapUnionall
  let some tt ← instDatatypeInner n T ops.toOps tupleName (ft :: types.params) true 0
    | throw "jl_argtype_with_function_type: tuple instantiation failed"
  return rewrapUnionall_ tt types0

/-- `jl_argtype_with_function`

Julia source: src/gf.c:5183-5186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_argtype_with_function(jl_value_t *f, jl_value_t *types0)
{
    return jl_argtype_with_function_type(jl_is_type(f) ? (jl_value_t*)jl_wrap_Type(f) : jl_typeof(f), types0);
}
```
-/
def jlArgtypeWithFunction (n : Nat) (T : Types) (ops : GfOps) (f types0 : Val) : CM Val := do
  let T := withBuiltinTypes T
  let ft ← if f.isType then wrapType n T ops.toOps f else pure (typeOf f)
  jlArgtypeWithFunctionType n T ops ft types0

/-- `jl_argtype_without_function`

Julia source: src/gf.c:5205-5219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_argtype_without_function(jl_value_t *ftypes)
{
    jl_value_t *types = jl_unwrap_unionall(ftypes);
    size_t l = jl_nparams(types);
    if (l == 1 && jl_is_vararg(jl_tparam0(types)))
        return ftypes;
    jl_value_t *tt = (jl_value_t*)jl_alloc_svec(l - 1);
    JL_GC_PUSH1(&tt);
    for (size_t i = 1; i < l; i++)
        jl_svecset(tt, i - 1, jl_tparam(types, i));
    tt = (jl_value_t*)jl_apply_tuple_type((jl_svec_t*)tt, 0);
    tt = jl_rewrap_unionall_(tt, types);
    JL_GC_POP();
    return tt;
}
```
-/
def jlArgtypeWithoutFunction (n : Nat) (T : Types) (ops : GfOps) (ftypes : Val) : CM Val := do
  let T := withBuiltinTypes T
  let types := ftypes.unwrapUnionall
  let l := types.nparams
  if l == 1 && types.params[0]!.isVararg then
    return ftypes
  let some tt ← instDatatypeInner n T ops.toOps tupleName types.params.tail true 0
    | throw "jl_argtype_without_function: tuple instantiation failed"
  return rewrapUnionall_ tt types

/-- `_gf_invoke_lookup`

Julia source: src/gf.c:5560-5573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_method_match_t *_gf_invoke_lookup(jl_value_t *types JL_PROPAGATES_ROOT, jl_methtable_t *mt, size_t world, int cache_result_recursion, size_t *min_valid, size_t *max_valid)
{
    jl_value_t *unw = jl_unwrap_unionall((jl_value_t*)types);
    if (!jl_is_tuple_type(unw))
        return NULL;
    if (jl_tparam0(unw) == jl_bottom_type)
        return NULL;
    jl_methcache_t *mc = ((jl_methtable_t*)mt)->cache;
    jl_value_t *matches = ml_matches((jl_methtable_t*)mt, mc, (jl_tupletype_t*)types, 1, 0, 0, world, cache_result_recursion, min_valid, max_valid, NULL);
    if (matches == jl_nothing || jl_array_nrows(matches) != 1)
        return NULL;
    jl_method_match_t *matc = (jl_method_match_t*)jl_array_ptr_ref(matches, 0);
    return matc;
}
```
-/
def gfInvokeLookupInternal (n : Nat) (T : Types) (ops : GfOps) (types : Val) (mt : MethodTable)
    (world : Nat) (minValid maxValid : Nat) : CM (Option MethodMatch × Nat × Nat) := do
  let unw := types.unwrapUnionall
  if !unw.isTupleType then
    return (none, minValid, maxValid)
  if unw.params.isEmpty || unw.params[0]! == .bottom then
    return (none, minValid, maxValid)
  let (matches?, minV, maxV, _) ← mlMatches n T ops mt types 1 false false world minValid maxValid false
  match matches? with
  | some [matc] => return (some matc, minV, maxV)
  | _ => return (none, minV, maxV)

/-- `jl_gf_invoke_lookup`

Julia source: src/gf.c:5575-5586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_gf_invoke_lookup(jl_value_t *types, jl_value_t *mt, size_t world)
{
    // Deprecated: Use jl_gf_invoke_lookup_worlds for future development
    size_t min_valid = 0;
    size_t max_valid = ~(size_t)0;
    if (mt == jl_nothing)
        mt = (jl_value_t*)jl_method_table;
    jl_method_match_t *matc = _gf_invoke_lookup(types, (jl_methtable_t*)mt, world, 1, &min_valid, &max_valid);
    if (matc == NULL)
        return jl_nothing;
    return (jl_value_t*)matc->method;
}
```
-/
def jlGfInvokeLookup (n : Nat) (T : Types) (ops : GfOps) (types : Val) (mt : MethodTable)
    (world : Nat) : CM (Option Method) := do
  let (matc?, _, _) ← gfInvokeLookupInternal n T ops types mt world 0 worldMax
  return matc?.map (·.method)

/-- `jl_gf_invoke_lookup_worlds`

Julia source: src/gf.c:5589-5597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_gf_invoke_lookup_worlds(jl_value_t *types, jl_value_t *mt, size_t world, size_t *min_world, size_t *max_world)
{
    if (mt == jl_nothing)
        mt = (jl_value_t*)jl_method_table;
    jl_method_match_t *matc = _gf_invoke_lookup(types, (jl_methtable_t*)mt, world, 1, min_world, max_world);
    if (matc == NULL)
        return jl_nothing;
    return (jl_value_t*)matc;
}
```
-/
def jlGfInvokeLookupWorlds (n : Nat) (T : Types) (ops : GfOps) (types : Val) (mt : MethodTable)
    (world : Nat) (minWorld maxWorld : Nat) : CM (Option MethodMatch × Nat × Nat) :=
  gfInvokeLookupInternal n T ops types mt world minWorld maxWorld

/-- `jl_has_concrete_subtype`

Julia source: src/gf.c:6451-6461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_has_concrete_subtype(jl_value_t *typ)
{
    if (typ == jl_bottom_type)
        return 0;
    typ = jl_unwrap_unionall(typ);
    if (jl_is_vararg(typ))
        typ = jl_unwrap_vararg(typ);
    if (!jl_is_datatype(typ))
        return 1;
    return ((jl_datatype_t*)typ)->has_concrete_subtype;
}
```
-/
def jlHasConcreteSubtype (n : Nat) (T : Types) (typ : Val) : CM Bool := do
  let T := withBuiltinTypes T
  if typ == .bottom then
    return false
  let typ := typ.unwrapUnionall
  let typ := if typ.isVararg then typ.unwrapVararg else typ
  if !typ.isDatatype then
    return true
  hasConcreteSubtype n T typ

/-- Build a `MethodTable` from a list of methods (sorting by `primaryWorld` ascending so that
chronological insertion order matches Julia's definition order even when `T` lines were dumped
from `methods(fn)`). -/
def buildMethodTable (n : Nat) (T : Types) (ops : GfOps) (ms : List Method) : CM MethodTable := do
  let sorted := (ms.toArray.qsort (fun a b => a.primaryWorld < b.primaryWorld)).toList
  let mut mt : MethodTable := {}
  for m in sorted do
    mt ← jlMethodTableInsert n T ops mt m none
  return mt

/-- Entry point mapping `(mt, argt, world)` to `method i | nomethod | ambiguous`, matching the
runtime lookup path (`jl_lookup_generic_` -> `jl_mt_assoc_by_type` ->
`_gf_invoke_lookup`, followed on failure by `MethodError` ambiguity classification via
`methods_including_ambiguous` -> `jl_matching_methods(..., lim=-1, include_ambiguous=1)`). -/
def gfLookup (n : Nat) (T : Types) (ops : GfOps) (mt : MethodTable) (argt : Val)
    (world : Nat := mt.worldCounter) : CM LookupResult := do
  let (matc?, _, _) ← jlGfInvokeLookupWorlds n T ops argt mt world 0 worldMax
  match matc? with
  | some matc => return .method matc.method.ret
  | none =>
    let (ms?, _, _, _) ← jlMatchingMethods n T ops argt mt (-1) true world 0 worldMax false
    match ms? with
    | some ms =>
      if ms.length > 1 then return .ambiguous
      else return .nomethod
    | none => return .nomethod

/-- Wire all `subtype.c` operations required by `typemap.c` and `gf.c` at fuel `n`. -/
def gfOps (n : Nat) (T : Types) : GfOps :=
  let T := withBuiltinTypes T
  { subOps n T with
    typeMorespecific := jlTypeMorespecific n T
    typeIntersectionEnvS := jlTypeIntersectionEnvS n T
    subtypeMatching := jlSubtypeMatching n T
    isa := jlIsa n T
    isTypeofbottomParam := fun t => jlIsTypeofbottomParam n (some t)
    obviouslyUnequal := jlObviouslyUnequal n T }

end JuliaLean.C
