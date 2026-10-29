import JuliaLean.src.jltypes_c

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JuliaLean.C

/-- `jl_bits_stack_t` and `jl_unionstate_t`; bits past `used` are overwritten before use.

Julia source: src/subtype.c:43-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef struct jl_bits_stack_t {
    uint32_t data[16];
    struct jl_bits_stack_t *next;
} jl_bits_stack_t;

typedef struct {
    int16_t depth;
    int16_t more;
    int16_t used;
    jl_bits_stack_t stack;
} jl_unionstate_t;
```
-/
structure UnionState where
  depth : Nat := 0
  more : Nat := 0
  used : Nat := 0
  stack : Array Bool := #[]
  deriving Inhabited, Repr

/-- `jl_saved_unionstate_t`.

Julia source: src/subtype.c:55-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef struct {
    int16_t depth;
    int16_t more;
    int16_t used;
    uint8_t *stack;
} jl_saved_unionstate_t;
```
-/
abbrev SavedUnionState := UnionState

/-- `jl_bound_certainty_t`, ordered as the C enum.

Julia source: src/subtype.c:66-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef enum {
    BOUND_NONE  = 0, // no (non-Bottom) lower-bound contribution yet
    BOUND_PROXY = 1, // derives from another variable's declared bounds: a
                     // `==`-equal rep of the query need not bind this var at all
    BOUND_EQ    = 2, // derives from a query value reached through an `==`
                     // equality wrapper (`Type{A}`): every `==`-equal rep of the
                     // query also binds this var, but only to an `==`-equal value
    BOUND_EGAL  = 3, // derives from an egality-pinned position (`TypeEgal`/type
                     // tag): the value is `===`-certain
} jl_bound_certainty_t;
```
-/
inductive BoundCertainty | none | proxy | eq | egal
  deriving BEq, Ord, Inhabited, Repr


def BoundCertainty.rank : BoundCertainty → Nat
  | .none => 0 | .proxy => 1 | .eq => 2 | .egal => 3

instance : LE BoundCertainty := ⟨fun a b => a.rank ≤ b.rank⟩
instance : DecidableLE BoundCertainty := fun a b => inferInstanceAs (Decidable (a.rank ≤ b.rank))
instance : Min BoundCertainty := ⟨fun a b => if a ≤ b then a else b⟩
instance : Max BoundCertainty := ⟨fun a b => if a ≤ b then b else a⟩
/-- `jl_varbinding_t`; an `innervars` pointer indexes the environment's array heap.

Julia source: src/subtype.c:82-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef struct jl_varbinding_t {
    jl_tvar_t *var; // store NULL to "delete" this from env (temporarily)
    jl_value_t *JL_NONNULL lb;
    jl_value_t *JL_NONNULL ub;
    int8_t existential; // whether this variable should be treated as existential
    int8_t occurs;      // occurs in any position
    int8_t occurs_inv;  // occurs in invariant position
    int8_t pinned;      // an invariant occurrence matched a term free of existential vars
    int8_t occurs_cov;  // # of occurrences in covariant position within the
                        // current consistency-check scope (reset on entry to
                        // `subtype_ccheck` / `intersect_aside`, restored on
                        // exit). Saturates at 2. Covariant occurrences inside
                        // nested Tuple{} accumulate into this counter as long
                        // as no consistency check is entered.
    int8_t cov_diag;    // max value `occurs_cov` reached in any (already-closed)
                        // consistency-check scope. The diagonal-rule test is
                        // `max(occurs_cov, cov_diag) > 1`, so a variable is
                        // diagonal iff it occurred >= 2 times in some single
                        // scope (the outer scope or any consistency check),
                        // rather than summed across consistency checks.
    int8_t concrete;    // 1 if another variable has a constraint forcing this one to be concrete
    int8_t max_offset;  // record the maximum positive offset of the variable (up to 32)
                        // max_offset < 0 if this variable occurs outside VarargNum.
    // constraintkind: in covariant position, we try three different ways to compute var ∩ type:
    // let ub = var.ub ∩ type
    // 0 - var.ub <: type ? var : ub
    // 1 - var.ub = ub; return var
    // 2 - var.lb = lb; return ub
    int8_t constraintkind;
    int8_t intvalued; // intvalued: must be integer-valued; i.e. occurs as N in Vararg{_,N}
    int8_t limited;
    int8_t intersected; // whether this variable has been intersected
    int8_t widened_to_kind;   // Type{X} was widened to a union of kinds
    int8_t lb_certainty; // strongest channel (jl_bound_certainty_t) through which a
                         // lower-bound contribution arrived; a type-valued binding
                         // below BOUND_EGAL is only known up to `==` (#61323) and is
                         // wrapped as an uncertainty marker in `envout`, with the
                         // marker `constrained` (defined for every `==`-equal query
                         // rep) iff the channel is at least BOUND_EQ
    int8_t lb_required;  // a lower-bound contribution came from a covariant tuple
                         // element that is present in every concrete member of
                         // the current left-side branch
    int8_t lb_spell;     // spelling authority (`jl_stenv_t.spell_channel`) of the
                         // contribution that supplied the current `lb` OBJECT.
                         // Among `==`-equal spellings the runtime binding takes
                         // whichever object won the join, so a spelling recorded
                         // through an equality wrapper (a bare argument value,
                         // `==`-authoritative only) must not displace a canonical
                         // type-tag-derived spelling: that keeps the binding agreed
                         // between by-type queries and the runtime MethodInstances
                         // they cover (#61323)
    int8_t tainted_inner; // 1 if this var's bounds reference a TypeVar from a vb that
                          // was pushed at depth0 *strictly greater* than this var's
                          // depth0 and has since been popped. Such "inner" tvars
                          // would not be substituted by going to a more concrete LHS
                          // (they live inside Type{...}/etc value positions), so the
                          // binding is leaky regardless of what `constrained` says.
    int8_t body_occurs_inv; // cached `var_occurs_invariant(u->body, u->var)` — the
                            // static "occurs invariantly" check used by the diagonal
                            // rule (since #34272). Unlike the dynamic `occurs_inv`
                            // counter, this is a pure structural property of the
                            // UnionAll body and does not change during traversal.
                            // -1 until computed from `body` (see `vb_body_occurs_inv`).
    int16_t depth0;         // # of invariant constructors nested around the UnionAll type for this var
    // array of typevars that our bounds depend on, whose UnionAlls need to be
    // moved outside ours.
    jl_array_t *innervars;
    jl_value_t *body;       // the UnionAll body, for computing `body_occurs_inv` on demand
    struct jl_varbinding_t *prev;
} jl_varbinding_t;
```
-/
structure VarBinding where
  var : Val
  lb : Val
  ub : Val
  existential : Bool := false
  occurs : Nat := 0
  occursInv : Nat := 0
  pinned : Bool := false
  occursCov : Nat := 0
  covDiag : Nat := 0
  concrete : Bool := false
  maxOffset : Int := 0
  constraintkind : Nat := 0
  intvalued : Bool := false
  limited : Bool := false
  intersected : Bool := false
  widenedToKind : Bool := false
  lbCertainty : BoundCertainty := .none
  lbRequired : Bool := false
  lbSpell : BoundCertainty := .none
  taintedInner : Bool := false
  bodyOccursInv : Option Bool := none
  depth0 : Nat := 0
  innervars : Option Nat := none
  body : Val := .bottom
  deriving Inhabited, Repr

/-- `jl_stenv_t` for `envout == NULL`; bindings are oldest first, pointers are indices.

Julia source: src/subtype.c:173-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef struct JL_GC_TRACKED_TYPE jl_stenv_t {
    // N.B.: varbindings are created on the stack and rooted there
    jl_varbinding_t *vars;    // type variable environment
    jl_unionstate_t Lunions;  // union state for unions on the left of A <: B
    jl_unionstate_t Runions;  // union state for unions on the right
    // N.B.: envout is gc-rooted
    jl_value_t **envout;      // for passing caller the computed bounds of right-side variables
    int envsz;                // length of envout
    int envidx;               // current index in envout
    int invdepth;             // current number of invariant constructors we're nested in
    int bound_channel;        // certainty (jl_bound_certainty_t) of lower-bound
                              // contributions recorded in the current context;
                              // starts at BOUND_EGAL and is only ever lowered:
                              // to BOUND_EQ inside an x-side equality wrapper
                              // (`Type{A}` matched by `==`), to BOUND_PROXY inside
                              // a bounds-consistency check on a typevar-containing
                              // x-term (whose bindings derive from another var's
                              // declared bounds rather than from a query value)
    int value_descent;        // true inside a bounds-consistency check on a closed
                              // x-term: the x-term is then a concrete type OBJECT
                              // (a candidate variable bound), so structural descent
                              // into it preserves the identity certainty carried by
                              // `bound_channel` and the covariant equality-wrapper
                              // demotion (which encodes that an argument-slot
                              // *spelling* only pins the runtime value up to `==`)
                              // does not apply
    int spell_channel;        // authority (jl_bound_certainty_t) of the *spelling*
                              // a lower-bound contribution carries in the current
                              // context. Mirrors `bound_channel`, but is also
                              // lowered to BOUND_EQ when descending from an
                              // egality-pinned value into an equality wrapper
                              // (`TypeEgal{A} <: Type{B}`): the value `A` is
                              // egal-known, yet `Type{B}` constrains `B` only up
                              // to `==`, so `A`'s spelling must not displace a
                              // canonical (type-tag-derived) spelling of the same
                              // binding (see `jl_varbinding_t.lb_spell`)
    int intersection;         // true iff subtype is being called from intersection
    int emptiness_only;       // true iff intersection only needs to test for emptiness
    int triangular;           // when intersecting Ref{X} with Ref{<:Y}
    int ignore_lb_required;   // true while checking a variable's declared bound
    int closed_inputs;        // true iff the top-level inputs have no free typevars, so a
                              // UnionAll var can only alias one already in `vars`;
                              // -1 until computed from `inputs` (see `may_capture_free_var`)
    jl_value_t *inputs[2];    // the top-level inputs (rooted by the caller)
    jl_typeenv_t *intersecting; // (var, type) pairs whose bound intersection is in progress
    // Used to represent the length difference between 2 vararg.
    // intersect(X, Y) ==> X = Y + Loffset
    int Loffset;
} jl_stenv_t;
```
-/
structure StEnv where
  vars : Array VarBinding := #[]
  Lunions : UnionState := {}
  Runions : UnionState := {}
  envidx : Nat := 0
  invdepth : Nat := 0
  boundChannel : BoundCertainty := .egal
  valueDescent : Bool := false
  spellChannel : BoundCertainty := .egal
  intersection : Bool := false
  emptinessOnly : Bool := false
  triangular : Nat := 0
  ignoreLbRequired : Bool := false
  closedInputs : Option Bool := some false
  inputs : Val × Val := (.bottom, .bottom)
  Loffset : Int := 0
  innerArrays : Array (Array Val) := #[]
  typevars : List (Nat × Val) := []
  deriving Inhabited

abbrev STM := StateT StEnv CM

def getBinding (i : Nat) : STM VarBinding := do
  match (← get).vars[i]? with
  | some b => return b
  | none => throw "invalid varbinding pointer"

def changeBinding (i : Nat) (f : VarBinding → VarBinding) : STM Unit := do
  let b ← getBinding i
  modify fun e => { e with vars := e.vars.set! i (f b) }

def innerVars (b : VarBinding) : STM (Array Val) := do
  match b.innervars with
  | none => return #[]
  | some i =>
    match (← get).innerArrays[i]? with
    | some vs => return vs
    | none => throw "invalid innervars pointer"

/-- Read mutable TypeVar objects through their identity after an inner-bound update. -/
def resolveVal (n : Nat) (v : Val) : STM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if (← get).typevars.isEmpty then return v
    match v with
    | .typevar id .. => return ((← get).typevars.lookup id).getD v
    | .datatype name ps => return .datatype name (← ps.mapM (resolveVal n))
    | .union a b => return .union (← resolveVal n a) (← resolveVal n b)
    | .intersect a b => return .intersect (← resolveVal n a) (← resolveVal n b)
    | .typeeq a => return .typeeq (← resolveVal n a)
    | .typeegal a => return .typeegal (← resolveVal n a)
    | .unionall id nm lb ub body =>
      let v ← resolveVal n (.typevar id nm lb ub)
      return .unionall id nm v.tvLb v.tvUb (← resolveVal n body)
    | .vararg a b => return .vararg (← a.mapM (resolveVal n)) (← b.mapM (resolveVal n))
    | .typeapp a b => return .typeapp (← resolveVal n a) (← resolveVal n b)
    | _ => return v

/-- `binding_has_innervar`.

Julia source: src/subtype.c:226-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int binding_has_innervar(jl_varbinding_t *b, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    if (b->innervars == NULL)
        return 0;
    for (size_t i = 0; i < jl_array_len(b->innervars); i++) {
        if ((jl_tvar_t*)jl_array_ptr_ref(b->innervars, i) == v)
            return 1;
    }
    return 0;
}
```
-/
def bindingHasInnervar (b : VarBinding) (v : Val) : STM Bool := do
  return (← innerVars b).any (fun w => w.tvId == v.tvId)

/-- `push_innervar`.

Julia source: src/subtype.c:237-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void push_innervar(jl_varbinding_t *b, jl_value_t *v) JL_CANSAFEPOINT
{
    assert(jl_is_typevar(v));
    if (binding_has_innervar(b, (jl_tvar_t*)v))
        return;
    if (b->innervars == NULL)
        b->innervars = jl_alloc_array_1d(jl_array_any_type, 0);
    jl_array_ptr_1d_push(b->innervars, v);
}
```
-/
def pushInnervar (i : Nat) (v : Val) : STM Unit := do
  let b ← getBinding i
  if ← bindingHasInnervar b v then return
  let ptr ← match b.innervars with
    | some p => pure p
    | none => do
      let p := (← get).innerArrays.size
      modify fun e => { e with innerArrays := e.innerArrays.push #[] }
      changeBinding i fun b => { b with innervars := some p }
      pure p
  modify fun e => { e with innerArrays := e.innerArrays.modify ptr (·.push v) }

/-- `lookup_binding`; the second result is the C `innervar` out-parameter.

Julia source: src/subtype.c:248-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_varbinding_t *lookup_binding(jl_stenv_t *e, jl_tvar_t *v, int *innervar) JL_GLOBALLY_ROOTED JL_NOTSAFEPOINT
{
    jl_varbinding_t *b = e->vars;
    while (b != NULL) {
        if (b->var == v) {
            if (innervar)
                *innervar = 0;
            return b;
        }
        b = b->prev;
    }
    if (innervar) {
        b = e->vars;
        while (b != NULL) {
            if (binding_has_innervar(b, v)) {
                *innervar = 1;
                return NULL;
            }
            b = b->prev;
        }
        *innervar = 0;
    }
    return NULL;
}
```
-/
def lookupBinding (v : Val) : STM (Option Nat × Bool) := do
  let vars := (← get).vars
  for i in (List.range vars.size).reverse do
    if vars[i]!.var.tvId == v.tvId then return (some i, false)
  for i in (List.range vars.size).reverse do
    if ← bindingHasInnervar vars[i]! v then return (none, true)
  return (none, false)

/-- `lookup`.

Julia source: src/subtype.c:277-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_varbinding_t *lookup(jl_stenv_t *e, jl_tvar_t *v) JL_GLOBALLY_ROOTED JL_NOTSAFEPOINT
{
    return lookup_binding(e, v, NULL);
}
```
-/
def lookup (v : Val) : STM (Option Nat) := return (← lookupBinding v).1

/-- `statestack_get`.

Julia source: src/subtype.c:284-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int statestack_get(jl_unionstate_t *st, int i) JL_NOTSAFEPOINT
{
    assert(i >= 0 && i < 32767); // limited by the depth bit.
    // get the `i`th bit in an array of 32-bit words
    jl_bits_stack_t *stack = &st->stack;
    while (i >= sizeof(stack->data) * 8) {
        // We should have set this bit.
        assert(stack->next);
        stack = stack->next;
        i -= sizeof(stack->data) * 8;
    }
    return (stack->data[i>>5] & (1u<<(i&31))) != 0;
}
```
-/
def statestackGet (st : UnionState) (i : Nat) : CM Bool := do
  if i ≥ 32767 then throw "union stack depth assertion"
  match st.stack[i]? with
  | some b => return b
  | none => throw "uninitialized union decision"

/-- `statestack_set`; allocation and word packing have no observable role.

Julia source: src/subtype.c:298-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void statestack_set(jl_unionstate_t *st, int i, int val) JL_NOTSAFEPOINT
{
    assert(i >= 0 && i < 32767); // limited by the depth bit.
    jl_bits_stack_t *stack = &st->stack;
    while (i >= sizeof(stack->data) * 8) {
        if (__unlikely(stack->next == NULL)) {
            stack->next = (jl_bits_stack_t *)malloc(sizeof(jl_bits_stack_t));
            stack->next->next = NULL;
        }
        stack = stack->next;
        i -= sizeof(stack->data) * 8;
    }
    if (val)
        stack->data[i>>5] |= (1u<<(i&31));
    else
        stack->data[i>>5] &= ~(1u<<(i&31));
}
```
-/
def statestackSet (st : UnionState) (i : Nat) (v : Bool) : CM UnionState := do
  if i ≥ 32767 then throw "union stack depth assertion"
  let stack := st.stack ++ Array.replicate (i + 1 - st.stack.size) false
  return { st with stack := stack.set! i v }

def unionState (R : Bool) : STM UnionState := do
  let e ← get
  return if R then e.Runions else e.Lunions

def setUnionState (R : Bool) (st : UnionState) : STM Unit :=
  modify fun e => if R then { e with Runions := st } else { e with Lunions := st }

/-- `next_union_state`.

Julia source: src/subtype.c:318-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int next_union_state(jl_stenv_t *e, int8_t R) JL_NOTSAFEPOINT
{
    jl_unionstate_t *state = R ? &e->Runions : &e->Lunions;
    if (state->more == 0)
        return 0;
    // reset `used` and let `pick_union_decision` clean the stack.
    state->used = state->more;
    statestack_set(state, state->used - 1, 1);
    return 1;
}
```
-/
def nextUnionState (R : Bool) : STM Bool := do
  let st ← unionState R
  if st.more == 0 then return false
  let st := { st with used := st.more }
  let st ← statestackSet st (st.used - 1) true
  setUnionState R st
  return true

/-- `pick_union_decision`.

Julia source: src/subtype.c:329-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int pick_union_decision(jl_stenv_t *e, int8_t R) JL_NOTSAFEPOINT
{
    jl_unionstate_t *state = R ? &e->Runions : &e->Lunions;
    if (state->depth >= state->used) {
        statestack_set(state, state->used, 0);
        state->used++;
    }
    int ui = statestack_get(state, state->depth);
    state->depth++;
    if (ui == 0)
        state->more = state->depth; // memorize that this was the deepest available choice
    return ui;
}
```
-/
def pickUnionDecision (R : Bool) : STM Bool := do
  let mut st ← unionState R
  if st.depth ≥ st.used then
    st ← statestackSet st st.used false
    st := { st with used := st.used + 1 }
  let ui ← statestackGet st st.depth
  st := { st with depth := st.depth + 1 }
  if !ui then st := { st with more := st.depth }
  setUnionState R st
  return ui

/-- `pick_union_element`.

Julia source: src/subtype.c:343-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *pick_union_element(jl_value_t *u JL_PROPAGATES_ROOT, jl_stenv_t *e, int8_t R) JL_NOTSAFEPOINT
{
    do {
        if (pick_union_decision(e, R))
            u = ((jl_uniontype_t*)u)->b;
        else
            u = ((jl_uniontype_t*)u)->a;
    } while (jl_is_uniontype(u));
    return u;
}
```
-/
def pickUnionElement (n : Nat) (u : Val) (R : Bool) : STM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let .union a b := u | throw "pick_union_element: not a Union"
    let u := if ← pickUnionDecision R then b else a
    if u.isUnion then pickUnionElement n u R else return u

/-- `push_unionstate`; all bits that can be read are copied.

Julia source: src/subtype.c:354-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#define push_unionstate(saved, src)                                  \
    do {                                                             \
        (saved)->depth = (src)->depth;                               \
        (saved)->more = (src)->more;                                 \
        (saved)->used = (src)->used;                                 \
        jl_bits_stack_t *srcstack = &(src)->stack;                   \
        int pushbits = ((saved)->used+7)/8;                          \
        (saved)->stack = (uint8_t *)alloca(pushbits);                \
        for (int n = 0; n < pushbits; n += sizeof(srcstack->data)) { \
            assert(srcstack != NULL);                                \
            int rest = pushbits - n;                                 \
            if (rest > sizeof(srcstack->data))                       \
                rest = sizeof(srcstack->data);                       \
            memcpy(&(saved)->stack[n], &srcstack->data, rest);       \
            srcstack = srcstack->next;                               \
        }                                                            \
    } while (0);
```
-/
def pushUnionstate (st : UnionState) : SavedUnionState :=
  { st with stack := st.stack.extract 0 (((st.used + 7) / 8) * 8) }

/-- `pop_unionstate`; preserves the destination bits beyond the copied bytes.

Julia source: src/subtype.c:372-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#define pop_unionstate(dst, saved)                                  \
    do {                                                            \
        (dst)->depth = (saved)->depth;                              \
        (dst)->more = (saved)->more;                                \
        (dst)->used = (saved)->used;                                \
        jl_bits_stack_t *dststack = &(dst)->stack;                  \
        int popbits = ((saved)->used+7)/8;                          \
        for (int n = 0; n < popbits; n += sizeof(dststack->data)) { \
            assert(dststack != NULL);                               \
            int rest = popbits - n;                                 \
            if (rest > sizeof(dststack->data))                      \
                rest = sizeof(dststack->data);                      \
            memcpy(&dststack->data, &(saved)->stack[n], rest);      \
            dststack = dststack->next;                              \
        }                                                           \
    } while (0);
```
-/
def popUnionstate (dst : UnionState) (saved : SavedUnionState) : UnionState :=
  { saved with stack := saved.stack ++ dst.stack.extract saved.stack.size dst.stack.size }

/-- `current_env_length`.

Julia source: src/subtype.c:389-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int current_env_length(jl_stenv_t *e)
{
    jl_varbinding_t *v = e->vars;
    int len = 0;
    while (v) {
        len++;
        v = v->prev;
    }
    return len;
}
```
-/
def currentEnvLength : STM Nat := return (← get).vars.size

/-- `cov_count`.

Julia source: src/subtype.c:408-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static inline int8_t cov_count(const jl_varbinding_t *vb) JL_NOTSAFEPOINT
{
    return vb->occurs_cov > vb->cov_diag ? vb->occurs_cov : vb->cov_diag;
}
```
-/
def covCount (vb : VarBinding) : Nat := max vb.occursCov vb.covDiag

/-- `jl_savedenv_t`, including the nine saved bytes and optionally the three rooted slots.

Julia source: src/subtype.c:413-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef struct {
    int8_t *buf;
    int rdepth;
    int8_t _space[72]; // == 8 * JL_SAVEDENV_BYTES_PER_VAR
    jl_gcframe_t gcframe;
    jl_value_t *roots[24]; // == 8 * 3 (lb, ub, innervars)
} jl_savedenv_t;
```
-/
structure SavedEnv where
  vars : Array VarBinding
  rdepth : Nat
  deriving Inhabited

/-- `jl_param_pos_t`.

Julia source: src/subtype.c:424-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef enum {
    PARAM_NONE      = 0,  // not inside a covariant/invariant context (top-level
                          // entry, UnionAll body before any constructor, or
                          // bound consistency recheck) — no occurrence recorded
    PARAM_COVARIANT = 1,  // inside a covariant parameter (Tuple/Vararg element)
    PARAM_INVARIANT = 2,  // inside an invariant parameter (most DataType
                          // parameters, Vararg length)
} jl_param_pos_t;
```
-/
inductive ParamPos | none | covariant | invariant
  deriving BEq, Inhabited, Repr

/-- `re_save_env`; GC bookkeeping is omitted.

Julia source: src/subtype.c:441-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void re_save_env(jl_stenv_t *e, jl_savedenv_t *se, int root)
{
    jl_value_t **roots = NULL;
    jl_svec_t *sv = NULL;
    int nroots = 0;
    if (root) {
        if (se->gcframe.nroots == JL_GC_ENCODE_PUSHARGS(1)) {
            sv = (jl_svec_t*)se->roots[0];
            assert(jl_is_svec(sv));
            roots = jl_svec_data(sv);
            nroots = jl_svec_len(sv);
        }
        else {
            roots = se->roots;
            nroots = JL_GC_DECODE_NROOTS(se->gcframe.nroots);
        }
    }
    jl_varbinding_t *v = e->vars;
    int i = 0, j = 0;
    while (v != NULL) {
        if (root) {
            set_env_root(sv, &roots[i++], v->lb);
            set_env_root(sv, &roots[i++], v->ub);
            set_env_root(sv, &roots[i++], (jl_value_t*)v->innervars);
        }
        se->buf[j++] = v->occurs;
        se->buf[j++] = v->occurs_inv;
        se->buf[j++] = v->occurs_cov;
        se->buf[j++] = v->cov_diag;
        se->buf[j++] = v->max_offset;
        se->buf[j++] = v->lb_certainty;
        se->buf[j++] = v->lb_required;
        se->buf[j++] = v->lb_spell;
        se->buf[j++] = v->pinned;
        v = v->prev;
    }
    assert(i == nroots); (void)nroots;
    se->rdepth = e->Runions.depth;
}
```
-/
def reSaveEnv : STM SavedEnv := do
  return { vars := (← get).vars, rdepth := (← get).Runions.depth }

/-- `save_env`; allocation is handled by Lean.

Julia source: src/subtype.c:512-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void save_env(jl_stenv_t *e, jl_savedenv_t *se, int root) JL_CANSAFEPOINT
{
    alloc_env(e, se, root);
    re_save_env(e, se, root);
}
```
-/
def saveEnv : STM SavedEnv := reSaveEnv

/-- `restore_env`; only the C-saved fields are restored. `envout` is NULL.

Julia source: src/subtype.c:547-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void restore_env(jl_stenv_t *e, jl_savedenv_t *se, int root) JL_NOTSAFEPOINT
{
    jl_value_t *JL_NONNULL *roots = NULL;
    int nroots = 0;
    if (root) {
        if (se->gcframe.nroots == JL_GC_ENCODE_PUSHARGS(1)) {
            jl_svec_t *sv = (jl_svec_t*)se->roots[0];
            assert(jl_is_svec(sv));
            roots = jl_svec_data(sv);
            nroots = jl_svec_len(sv);
        }
        else {
            roots = se->roots;
            nroots = JL_GC_DECODE_NROOTS(se->gcframe.nroots);
        }
    }
    jl_varbinding_t *v = e->vars;
    int i = 0, j = 0;
    while (v != NULL) {
        if (root) {
            v->lb = roots[i++];
            v->ub = roots[i++];
            v->innervars = (jl_array_t*)roots[i++];
        }
        v->occurs = se->buf[j++];
        v->occurs_inv = se->buf[j++];
        v->occurs_cov = se->buf[j++];
        v->cov_diag = se->buf[j++];
        v->max_offset = se->buf[j++];
        v->lb_certainty = se->buf[j++];
        v->lb_required = se->buf[j++];
        v->lb_spell = se->buf[j++];
        v->pinned = se->buf[j++];
        v = v->prev;
    }
    assert(i == nroots); (void)nroots;
    e->Runions.depth = se->rdepth;
    if (e->envout && e->envidx < e->envsz)
        memset(&e->envout[e->envidx], 0, (e->envsz - e->envidx)*sizeof(void*));
}
```
-/
def restoreEnv (se : SavedEnv) (root : Bool := true) : STM Unit := do
  if (← get).vars.size != se.vars.size then throw "restore_env: environment length assertion"
  for i in [0:se.vars.size] do
    let s := se.vars[i]!
    changeBinding i fun v => { v with
      lb := if root then s.lb else v.lb
      ub := if root then s.ub else v.ub
      innervars := if root then s.innervars else v.innervars
      occurs := s.occurs, occursInv := s.occursInv, occursCov := s.occursCov
      covDiag := s.covDiag, maxOffset := s.maxOffset, lbCertainty := s.lbCertainty
      lbRequired := s.lbRequired, lbSpell := s.lbSpell, pinned := s.pinned }
  modify fun e => { e with Runions := { e.Runions with depth := se.rdepth } }

/-- `is_bottom_bound`.

Julia source: src/subtype.c:593-608 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_bottom_bound(jl_value_t *T) JL_NOTSAFEPOINT
{
    while (1) {
        if (jl_is_typevar(T)) {
            T = ((jl_tvar_t*)T)->ub;
        }
        else if (jl_is_uniontype(T)) {
            if (!is_bottom_bound(((jl_uniontype_t*)T)->a))
                return 0;
            T = ((jl_uniontype_t*)T)->b;
        }
        else {
            return T == jl_bottom_type;
        }
    }
}
```
-/
def isBottomBound (n : Nat) (t : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t with
    | .typevar _ _ _ ub => isBottomBound n ub
    | .union a b =>
      if !(← isBottomBound n a) then return false
      isBottomBound n b
    | _ => return t == .bottom

/-- `is_typeofbottom_typealias`.

Julia source: src/subtype.c:611-620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_typeofbottom_typealias(jl_value_t *t) JL_NOTSAFEPOINT
{
    if (t == NULL)
        return 0;
    if (jl_typeofbottom_type == NULL)
        return 0;
    if (t == (jl_value_t*)jl_typeofbottom_type)
        return 1;
    return jl_is_typeeq(t) && is_bottom_bound(jl_typeeq_T(t));
}
```
-/
def isTypeofbottomTypealias (n : Nat) (t : Val) : CM Bool := do
  if t == typeofbottomType then return true
  if t.isTypeeq then isBottomBound n t.someTypeT else return false

/-- `normalize_typeofbottom_typealias`.

Julia source: src/subtype.c:622-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *normalize_typeofbottom_typealias(jl_value_t *t) JL_NOTSAFEPOINT
{
    return is_typeofbottom_typealias(t) ? (jl_value_t*)jl_typeofbottom_type : t;
}
```
-/
def normalizeTypeofbottomTypealias (n : Nat) (t : Val) : CM Val := do
  return if ← isTypeofbottomTypealias n t then typeofbottomType else t

/-- `obviously_egal`.

Julia source: src/subtype.c:628-669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int obviously_egal(jl_value_t *a, jl_value_t *b) JL_NOTSAFEPOINT
{
    if (a == b) return 1;
    // NB: do NOT normalize the `Type{Union{}}`/`TypeofBottom` typealias here.
    // Those two are `==` but not `===`, so conflating them is unsound for an
    // egality test — in particular for egality-keyed `TypeEgal{...}` slots,
    // where `TypeEgal{Type{Union{}}}` and `TypeEgal{TypeofBottom}` are distinct
    // types with different subtype behavior (#61323). (`obviously_unequal`
    // keeps the normalization: under `==` the pair is equal, hence not unequal.)
    if (jl_typeof(a) != jl_typeof(b)) return 0;
    if (jl_is_datatype(a)) {
        jl_datatype_t *ad = (jl_datatype_t*)a;
        jl_datatype_t *bd = (jl_datatype_t*)b;
        if (ad->name != bd->name) return 0;
        if (ad->isconcretetype || bd->isconcretetype) return 0;
        size_t i, np = jl_nparams(ad);
        if (np != jl_nparams(bd)) return 0;
        for (i = 0; i < np; i++) {
            if (!obviously_egal(jl_tparam(ad,i), jl_tparam(bd,i)))
                return 0;
        }
        return 1;
    }
    if (jl_is_uniontype(a) || jl_is_intersecttype(a)) {
        return obviously_egal(((jl_uniontype_t*)a)->a, ((jl_uniontype_t*)b)->a) &&
            obviously_egal(((jl_uniontype_t*)a)->b, ((jl_uniontype_t*)b)->b);
    }
    if (jl_is_unionall(a)) {
        return ((jl_unionall_t*)a)->var == ((jl_unionall_t*)b)->var &&
            obviously_egal(((jl_unionall_t*)a)->body, ((jl_unionall_t*)b)->body);
    }
    if (jl_is_vararg(a)) {
        jl_vararg_t *vma = (jl_vararg_t *)a;
        jl_vararg_t *vmb = (jl_vararg_t *)b;
        return obviously_egal(jl_unwrap_vararg(vma), jl_unwrap_vararg(vmb)) &&
            ((!vma->N && !vmb->N) || (vma->N && vmb->N && obviously_egal(vma->N, vmb->N)));
    }
    if (jl_is_some_Type(a))
        return obviously_egal(jl_some_Type_T(a), jl_some_Type_T(b));
    if (jl_is_typevar(a)) return 0;
    return !jl_is_type(a) && jl_egal(a,b);
}
```
-/
def obviouslyEgal (n : Nat) (T : Types) (a b : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == b then return true
    if typeOf a != typeOf b then return false
    match a, b with
    | .datatype an ap, .datatype bn bp =>
      if an != bn then return false
      if ← isConcreteType T a then return false
      if ← isConcreteType T b then return false
      if ap.length != bp.length then return false
      (ap.zip bp).allM fun (x, y) => obviouslyEgal n T x y
    | .union a b, .union c d | .intersect a b, .intersect c d =>
      if !(← obviouslyEgal n T a c) then return false
      obviouslyEgal n T b d
    | .unionall ai _ _ _ ab, .unionall bi _ _ _ bb =>
      if ai != bi then return false
      obviouslyEgal n T ab bb
    | .vararg aT an, .vararg bT bn =>
      if !(← obviouslyEgal n T (aT.getD anyType) (bT.getD anyType)) then return false
      match an, bn with
      | none, none => return true
      | some an, some bn => obviouslyEgal n T an bn
      | _, _ => return false
    | .typeeq a, .typeeq b | .typeegal a, .typeegal b => obviouslyEgal n T a b
    | .typevar .., _ => return false
    | _, _ => if !a.isType then egal n T a b else return false

/-- `in_union`.

Julia source: src/subtype.c:749-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int in_union(jl_value_t *u, jl_value_t *x) JL_NOTSAFEPOINT
{
    if (u == x) return 1;
    if (!jl_is_uniontype(u)) return 0;
    return in_union(((jl_uniontype_t*)u)->a, x) || in_union(((jl_uniontype_t*)u)->b, x);
}
```
-/
def inUnion (n : Nat) (u x : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if u == x then return true
    match u with
    | .union a b => if ← inUnion n a x then return true else inUnion n b x
    | _ => return false

/-- `obviously_in_union`.

Julia source: src/subtype.c:756-776 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int obviously_in_union(jl_value_t *u, jl_value_t *x)
{
    jl_value_t *a = NULL, *b = NULL;
    if (jl_is_uniontype(x)) {
        a = ((jl_uniontype_t*)x)->a;
        b = ((jl_uniontype_t*)x)->b;
        JL_GC_PUSH2(&a, &b);
        int res = obviously_in_union(u, a) && obviously_in_union(u, b);
        JL_GC_POP();
        return res;
    }
    if (jl_is_uniontype(u)) {
        a = ((jl_uniontype_t*)u)->a;
        b = ((jl_uniontype_t*)u)->b;
        JL_GC_PUSH2(&a, &b);
        int res = obviously_in_union(a, x) || obviously_in_union(b, x);
        JL_GC_POP();
        return res;
    }
    return obviously_egal(u, x);
}
```
-/
def obviouslyInUnion (n : Nat) (T : Types) (u x : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match x with
    | .union a b =>
      if !(← obviouslyInUnion n T u a) then return false
      obviouslyInUnion n T u b
    | _ =>
      match u with
      | .union a b =>
        if ← obviouslyInUnion n T a x then return true
        obviouslyInUnion n T b x
      | _ => obviouslyEgal n T u x

/-- `is_kind_or_anytype`.

Julia source: src/subtype.c:780-783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
STATIC_INLINE int is_kind_or_anytype(jl_value_t *t) JL_NOTSAFEPOINT
{
    return jl_is_kind(t) || t == (jl_value_t*)jl_anytype_type;
}
```
-/
def isKindOrAnytype (t : Val) : Bool := isKind t || t == anytypeType

/-- `jl_type_type`, initialized as `TypeEq(T) where T` in jltypes.c:3770-3773.
The permanent global variable has identity 0; serialized case variables start at 1. -/
def typeType : Val :=
  .unionall 0 "T" .bottom anyType (.typeeq (.typevar 0 "T" .bottom anyType))

/-- `is_leaf_bound`.

Julia source: src/subtype.c:1411-1426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int is_leaf_bound(jl_value_t *v) JL_NOTSAFEPOINT
{
    if (v == jl_bottom_type)
        return 1;
    if (jl_is_intersecttype(v)) // internal meet node (see #61917), not a concrete leaf
        return 0;
    if (jl_is_some_Type(v))
        return 1;
    if (jl_is_datatype(v)) {
        if (((jl_datatype_t*)v)->name->abstract) {
            return 0;
        }
        return ((jl_datatype_t*)v)->isconcretetype;
    }
    return !jl_is_type(v) && !jl_is_typevar(v);
}
```
-/
def isLeafBound (_n : Nat) (T : Types) (v : Val) : CM Bool := do
  if v == .bottom then return true
  if v.isIntersect then return false
  if v.isSomeType then return true
  if v.isDatatype then
    if ← isAbstractType T v then return false
    return ← isConcreteType T v
  return !v.isType && !v.isTypevar

/-- `is_leaf_typevar`.

Julia source: src/subtype.c:1428-1431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_leaf_typevar(jl_tvar_t *v) JL_NOTSAFEPOINT
{
    return is_leaf_bound(v->lb);
}
```
-/
def isLeafTypevar (n : Nat) (T : Types) (v : Val) : CM Bool := isLeafBound n T v.tvLb

/-- `typeeq_varctx_t`, innermost first.

Julia source: src/subtype.c:1433-1437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typedef struct _typeeq_varctx_t {
    jl_tvar_t *var;
    int pinned; // lb === ub: occurrences behave like that closed bound
    struct _typeeq_varctx_t *prev;
} typeeq_varctx_t;
```
-/
abbrev TypeeqVarctx := List (Nat × Bool)

/-- `typeeq_lookup_var`.

Julia source: src/subtype.c:1439-1447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static typeeq_varctx_t *typeeq_lookup_var(typeeq_varctx_t *env, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    while (env != NULL) {
        if (env->var == v)
            return env;
        env = env->prev;
    }
    return NULL;
}
```
-/
def typeeqLookupVar (env : TypeeqVarctx) (v : Val) : Option Bool :=
  v.tvId.bind fun id => env.lookup id

/-- `var_occurs_inside`, also used by subtyping's static diagonal check.

Julia source: src/subtype.c:4753-4791 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int var_occurs_inside(jl_value_t *v, jl_tvar_t *var, int inside, int want_inv) JL_NOTSAFEPOINT
{
    if (v == (jl_value_t*)var) {
        return inside;
    }
    else if (jl_is_uniontype(v) || jl_is_intersecttype(v)) {
        return var_occurs_inside(((jl_uniontype_t*)v)->a, var, inside, want_inv) ||
            var_occurs_inside(((jl_uniontype_t*)v)->b, var, inside, want_inv);
    }
    else if (jl_is_unionall(v)) {
        jl_unionall_t *ua = (jl_unionall_t*)v;
        if (ua->var == var)
            return 0;
        if (var_occurs_inside(ua->var->lb, var, inside, want_inv) || var_occurs_inside(ua->var->ub, var, inside, want_inv))
            return 1;
        return var_occurs_inside(ua->body, var, inside, want_inv);
    }
    else if (jl_is_vararg(v)) {
        jl_vararg_t *vm = (jl_vararg_t*)v;
        if (vm->T) {
            if (var_occurs_inside(vm->T, var, inside || !want_inv, want_inv))
                return 1;
            return vm->N && var_occurs_inside(vm->N, var, 1, want_inv);
        }
    }
    else if (jl_is_some_Type(v)) {
        return var_occurs_inside(jl_some_Type_T(v), var, 1, want_inv);
    }
    else if (jl_is_datatype(v)) {
        size_t i;
        int istuple = jl_is_tuple_type(v);
        for (i=0; i < jl_nparams(v); i++) {
            int ins_i = inside || !want_inv || !istuple;
            if (var_occurs_inside(jl_tparam(v,i), var, ins_i, want_inv))
                return 1;
        }
    }
    return 0;
}
```
-/
def varOccursInside (n : Nat) (v var : Val) (inside wantInv : Bool) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if v == var then return inside
    match v with
    | .union a b | .intersect a b =>
      if ← varOccursInside n a var inside wantInv then return true
      varOccursInside n b var inside wantInv
    | .unionall id _ lb ub body =>
      if some id == var.tvId then return false
      if ← varOccursInside n lb var inside wantInv then return true
      if ← varOccursInside n ub var inside wantInv then return true
      varOccursInside n body var inside wantInv
    | .vararg (some t) N =>
      if ← varOccursInside n t var (inside || !wantInv) wantInv then return true
      match N with
      | none => return false
      | some N => varOccursInside n N var true wantInv
    | .typeeq t | .typeegal t => varOccursInside n t var true wantInv
    | .datatype name ps =>
      ps.anyM fun p => varOccursInside n p var (inside || !wantInv || name != tupleName) wantInv
    | _ => return false

/-- `var_occurs_invariant`.

Julia source: src/subtype.c:1685-1688 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int var_occurs_invariant(jl_value_t *v, jl_tvar_t *var) JL_NOTSAFEPOINT
{
    return var_occurs_inside(v, var, 0, 1);
}
```
-/
def varOccursInvariant (n : Nat) (v var : Val) : CM Bool := varOccursInside n v var false true

/-- `vb_body_occurs_inv`.

Julia source: src/subtype.c:1690-1695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int vb_body_occurs_inv(jl_varbinding_t *vb) JL_NOTSAFEPOINT
{
    if (vb->body_occurs_inv < 0)
        vb->body_occurs_inv = var_occurs_invariant(vb->body, vb->var);
    return vb->body_occurs_inv;
}
```
-/
def vbBodyOccursInv (n : Nat) (i : Nat) : STM Bool := do
  let b ← getBinding i
  match b.bodyOccursInv with
  | some v => return v
  | none =>
    let v ← varOccursInvariant n b.body b.var
    changeBinding i fun b => { b with bodyOccursInv := some v }
    return v

/-- `has_existential_typevar`.

Julia source: src/subtype.c:1727-1742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_existential_typevar(jl_value_t *x, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    jl_typeenv_t *env = NULL;
    jl_varbinding_t *v = e->vars;
    while (v != NULL) {
        if (v->existential) {
            jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
            newenv->var = v->var;
            newenv->val = NULL;
            newenv->prev = env;
            env = newenv;
        }
        v = v->prev;
    }
    return env != NULL && jl_has_bound_typevars(x, env);
}
```
-/
def hasExistentialTypevar (x : Val) : STM Bool := do
  let env := (← get).vars.toList.filterMap fun b =>
    if b.existential then b.var.tvId.map fun id => ({ var := id, val := none } : TypeEnvEntry) else none
  return !env.isEmpty && hasBoundTypevars x env

/-- `has_universal_typevar`.

Julia source: src/subtype.c:1744-1768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_universal_typevar(jl_value_t *x, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    jl_typeenv_t *env = NULL;
    jl_varbinding_t *v = e->vars;
    while (v != NULL) {
        if (!v->existential) {
            jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
            newenv->var = v->var;
            newenv->val = NULL;
            newenv->prev = env;
            env = newenv;
        }
        if (v->innervars != NULL) {
            for (size_t i = 0; i < jl_array_len(v->innervars); i++) {
                jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
                newenv->var = (jl_tvar_t*)jl_array_ptr_ref(v->innervars, i);
                newenv->val = NULL;
                newenv->prev = env;
                env = newenv;
            }
        }
        v = v->prev;
    }
    return env != NULL && jl_has_bound_typevars(x, env);
}
```
-/
def hasUniversalTypevar (x : Val) : STM Bool := do
  let mut env : TypeEnv := []
  for b in (← get).vars do
    if !b.existential then
      if let some id := b.var.tvId then env := { var := id, val := none } :: env
    for v in (← innerVars b) do
      if let some id := v.tvId then env := { var := id, val := none } :: env
  return !env.isEmpty && hasBoundTypevars x env

/-- `has_env_typevar`.

Julia source: src/subtype.c:1770-1774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_env_typevar(jl_value_t *x, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    return jl_has_free_typevars(x) &&
        (has_universal_typevar(x, e) || has_existential_typevar(x, e));
}
```
-/
def hasEnvTypevar (x : Val) : STM Bool := do
  if !x.hasFreeTypevars then return false
  if ← hasUniversalTypevar x then return true
  hasExistentialTypevar x

/-- `record_var_pin`; `envsz == 0`, so C's condition is false.

Julia source: src/subtype.c:1114-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void record_var_pin(jl_varbinding_t *vb, jl_value_t *a, jl_stenv_t *e, jl_param_pos_t param) JL_NOTSAFEPOINT
{
    if (e->envsz > 0 && param == PARAM_INVARIANT && e->invdepth > vb->depth0 && !vb->pinned &&
        (!jl_has_free_typevars(a) || !has_existential_typevar(a, e)))
        vb->pinned = 1;
}
```
-/
def recordVarPin (_i : Nat) (_a : Val) (_param : ParamPos) : STM Unit := pure ()

/-- `record_var_occurrence`.

Julia source: src/subtype.c:1121-1136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void record_var_occurrence(jl_varbinding_t *vb, jl_stenv_t *e, jl_param_pos_t param) JL_NOTSAFEPOINT
{
    if (vb != NULL) {
        // saturate counters at 2; we don't need values bigger than that
        if (vb->occurs < 2)
            vb->occurs++;
        if (param == PARAM_INVARIANT && e->invdepth > vb->depth0 && vb->occurs_inv < 2)
            vb->occurs_inv++;
        else if (param == PARAM_COVARIANT && vb->occurs_cov < 2)
            vb->occurs_cov++;
        // Always set `max_offset` to `-1` during the 1st round intersection.
        // Would be recovered in `intersect_varargs`/`subtype_tuple_varargs` if needed.
        if (!vb->intersected)
            vb->max_offset = -1;
    }
}
```
-/
def recordVarOccurrence (i : Option Nat) (param : ParamPos) : STM Unit := do
  if let some i := i then
    let invdepth := (← get).invdepth
    changeBinding i fun b => { b with
      occurs := min 2 (b.occurs + 1)
      occursInv := if param == .invariant && invdepth > b.depth0 then min 2 (b.occursInv + 1) else b.occursInv
      occursCov := if !(param == .invariant && invdepth > b.depth0) && param == .covariant then min 2 (b.occursCov + 1) else b.occursCov
      maxOffset := if !b.intersected then -1 else b.maxOffset }

/-- `push_consistency_scope`.

Julia source: src/subtype.c:1151-1161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int push_consistency_scope(jl_stenv_t *e, int8_t *saved) JL_NOTSAFEPOINT
{
    jl_varbinding_t *v = e->vars;
    int i = 0;
    while (v != NULL) {
        saved[i++] = v->occurs_cov;
        v->occurs_cov = 0;
        v = v->prev;
    }
    return i;
}
```
-/
def pushConsistencyScope : STM (Array Nat) := do
  let saved := (← get).vars.map (·.occursCov)
  modify fun e => { e with vars := e.vars.map fun b => { b with occursCov := 0 } }
  return saved

/-- `pop_consistency_scope`.

Julia source: src/subtype.c:1163-1173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void pop_consistency_scope(jl_stenv_t *e, const int8_t *saved, int nsaved) JL_NOTSAFEPOINT
{
    jl_varbinding_t *v = e->vars;
    int i = 0;
    while (v != NULL && i < nsaved) {
        if (v->occurs_cov > v->cov_diag)
            v->cov_diag = v->occurs_cov;
        v->occurs_cov = saved[i++];
        v = v->prev;
    }
}
```
-/
def popConsistencyScope (saved : Array Nat) : STM Unit := do
  let len := min (← get).vars.size saved.size
  for i in [0:len] do
    changeBinding i fun b => { b with covDiag := max b.covDiag b.occursCov, occursCov := saved[i]! }

/-- `push_forall_bound_scope`.

Julia source: src/subtype.c:1183-1194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int push_forall_bound_scope(jl_stenv_t *e, int8_t *saved) JL_NOTSAFEPOINT
{
    jl_varbinding_t *v = e->vars;
    int i = 0;
    while (v != NULL) {
        saved[i++] = v->occurs_cov;
        if (!v->existential)
            v->occurs_cov = 0;
        v = v->prev;
    }
    return i;
}
```
-/
def pushForallBoundScope : STM (Array Nat) := do
  let saved := (← get).vars.map (·.occursCov)
  modify fun e => { e with vars := e.vars.map fun b => if b.existential then b else { b with occursCov := 0 } }
  return saved

/-- `pop_forall_bound_scope`.

Julia source: src/subtype.c:1196-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void pop_forall_bound_scope(jl_stenv_t *e, const int8_t *saved, int nsaved) JL_NOTSAFEPOINT
{
    jl_varbinding_t *v = e->vars;
    int i = 0;
    while (v != NULL && i < nsaved) {
        if (!v->existential) {
            if (v->occurs_cov > v->cov_diag)
                v->cov_diag = v->occurs_cov;
            v->occurs_cov = saved[i];
        }
        i++;
        v = v->prev;
    }
}
```
-/
def popForallBoundScope (saved : Array Nat) : STM Unit := do
  let len := min (← get).vars.size saved.size
  for i in [0:len] do
    changeBinding i fun b => if b.existential then b else
      { b with covDiag := max b.covDiag b.occursCov, occursCov := saved[i]! }

/-- `get_occurs_cov`.

Julia source: src/subtype.c:1211-1216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void get_occurs_cov(jl_stenv_t *e, int8_t *buf) JL_NOTSAFEPOINT
{
    int i = 0;
    for (jl_varbinding_t *v = e->vars; v != NULL; v = v->prev)
        buf[i++] = v->occurs_cov;
}
```
-/
def getOccursCov : STM (Array Nat) := return (← get).vars.map (·.occursCov)

/-- `set_occurs_cov`.

Julia source: src/subtype.c:1218-1223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void set_occurs_cov(jl_stenv_t *e, const int8_t *buf) JL_NOTSAFEPOINT
{
    int i = 0;
    for (jl_varbinding_t *v = e->vars; v != NULL; v = v->prev)
        v->occurs_cov = buf[i++];
}
```
-/
def setOccursCov (saved : Array Nat) : STM Unit := do
  for i in [0:(← get).vars.size] do
    changeBinding i fun b => { b with occursCov := saved[i]! }

/-- `max_occurs_cov`.

Julia source: src/subtype.c:1225-1232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void max_occurs_cov(jl_stenv_t *e, int8_t *buf) JL_NOTSAFEPOINT
{
    int i = 0;
    for (jl_varbinding_t *v = e->vars; v != NULL; v = v->prev, i++) {
        if (v->occurs_cov > buf[i])
            buf[i] = v->occurs_cov;
    }
}
```
-/
def maxOccursCov (saved : Array Nat) : STM (Array Nat) := do
  return (← get).vars.mapIdx fun i b => max b.occursCov saved[i]!

/-- `var_outside`.

Julia source: src/subtype.c:1235-1244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int var_outside(jl_stenv_t *e, jl_tvar_t *x, jl_tvar_t *y)
{
    jl_varbinding_t *btemp = e->vars;
    while (btemp != NULL) {
        if (btemp->var == x) return 0;
        if (btemp->var == y) return 1;
        btemp = btemp->prev;
    }
    return 0;
}
```
-/
def varOutside (x y : Val) : STM Bool := do
  let vars := (← get).vars
  for i in (List.range vars.size).reverse do
    if vars[i]!.var.tvId == x.tvId then return false
    if vars[i]!.var.tvId == y.tvId then return true
  return false

/-- `singleton_typevar_subtype`.

Julia source: src/subtype.c:1250-1258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int singleton_typevar_subtype(jl_tvar_t *v, jl_value_t *a) JL_NOTSAFEPOINT
{
    if (a == (jl_value_t*)v || a == (jl_value_t*)jl_any_type)
        return 1;
    if (jl_is_uniontype(a))
        return singleton_typevar_subtype(v, ((jl_uniontype_t*)a)->a) ||
               singleton_typevar_subtype(v, ((jl_uniontype_t*)a)->b);
    return 0;
}
```
-/
def singletonTypevarSubtype (n : Nat) (v a : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == v || a == anyType then return true
    match a with
    | .union a b =>
      if ← singletonTypevarSubtype n v a then return true
      singletonTypevarSubtype n v b
    | _ => return false

/-- `subtype_singleton_typevar`.

Julia source: src/subtype.c:1260-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_singleton_typevar(jl_value_t *a, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    if (a == (jl_value_t*)v || a == jl_bottom_type)
        return 1;
    if (jl_is_uniontype(a))
        return subtype_singleton_typevar(((jl_uniontype_t*)a)->a, v) &&
               subtype_singleton_typevar(((jl_uniontype_t*)a)->b, v);
    return 0;
}
```
-/
def subtypeSingletonTypevar (n : Nat) (a v : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == v || a == .bottom then return true
    match a with
    | .union a b =>
      if !(← subtypeSingletonTypevar n a v) then return false
      subtypeSingletonTypevar n b v
    | _ => return false

/-- `var_occurs_covariant_only`.

Julia source: src/subtype.c:1783-1813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int var_occurs_covariant_only(jl_value_t *t, jl_tvar_t *var, int covariant) JL_NOTSAFEPOINT
{
    if (t == (jl_value_t*)var)
        return covariant;
    else if (jl_is_uniontype(t)) {
        return var_occurs_covariant_only(((jl_uniontype_t*)t)->a, var, covariant) &&
               var_occurs_covariant_only(((jl_uniontype_t*)t)->b, var, covariant);
    }
    else if (jl_is_unionall(t)) {
        if (((jl_unionall_t*)t)->var == var)
            return 1; // shadowed
        return !jl_has_typevar(t, var);
    }
    else if (jl_is_vararg(t)) {
        jl_vararg_t *vm = (jl_vararg_t*)t;
        if (vm->N && jl_has_typevar(vm->N, var))
            return 0;
        return vm->T == NULL || var_occurs_covariant_only(vm->T, var, covariant);
    }
    else if (jl_is_datatype(t)) {
        int incov = covariant && jl_is_tuple_type(t);
        for (size_t i = 0; i < jl_nparams(t); i++) {
            if (!var_occurs_covariant_only(jl_tparam(t, i), var, incov))
                return 0;
        }
        return 1;
    }
    // conservative for internal nodes (TypeEq, TypeApp, Intersect); plain
    // values contain no typevars
    return !jl_has_typevar(t, var);
}
```
-/
def varOccursCovariantOnly (n : Nat) (t var : Val) (covariant : Bool) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if t == var then return covariant
    match t with
    | .union a b =>
      if !(← varOccursCovariantOnly n a var covariant) then return false
      varOccursCovariantOnly n b var covariant
    | .unionall id .. => return some id == var.tvId || !t.hasTypevar var
    | .vararg vt vn =>
      if vn.any (·.hasTypevar var) then return false
      match vt with
      | none => return true
      | some vt => varOccursCovariantOnly n vt var covariant
    | .datatype name ps => ps.allM fun p => varOccursCovariantOnly n p var (covariant && name == tupleName)
    | _ => return !t.hasTypevar var

/-- `may_capture_free_var`.

Julia source: src/subtype.c:1892-1899 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int may_capture_free_var(jl_value_t *t, jl_tvar_t *v, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    if (jl_is_datatype(t) && !((jl_datatype_t*)t)->hasfreetypevars)
        return 0;
    if (e->closed_inputs < 0)
        e->closed_inputs = !jl_has_free_typevars(e->inputs[0]) && !jl_has_free_typevars(e->inputs[1]);
    return !e->closed_inputs && jl_has_typevar(t, v);
}
```
-/
def mayCaptureFreeVar (t v : Val) : STM Bool := do
  if t.isDatatype && !t.dtHasFreeTypevars then return false
  if (← get).closedInputs.isNone then
    let (x, y) := (← get).inputs
    modify fun e => { e with closedInputs := some (!x.hasFreeTypevars && !y.hasFreeTypevars) }
  return !(← get).closedInputs.getD false && t.hasTypevar v

/-- `count_occurs`, required by `typeeq_kind_mask1`.

Julia source: src/subtype.c:7369-7398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int count_occurs(jl_value_t *t, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    if (t == (jl_value_t*)v)
        return 1;
    if (jl_is_uniontype(t)) {
        int a = count_occurs(((jl_uniontype_t*)t)->a, v);
        int b = count_occurs(((jl_uniontype_t*)t)->b, v);
        return a > b ? a : b;
    }
    if (jl_is_unionall(t)) {
        if (((jl_unionall_t*)t)->var == v)
            return 0;
        return count_occurs(((jl_unionall_t*)t)->body, v);
    }
    if (jl_is_vararg(t)) {
        jl_vararg_t *vm = (jl_vararg_t*)t;
        if (vm->T) {
            return count_occurs(vm->T, v) + (vm->N ? count_occurs(vm->N, v) : 0);
        }
    }
    if (jl_is_some_Type(t))
        return count_occurs(jl_some_Type_T(t), v);
    if (jl_is_datatype(t)) {
        int i, c=0;
        for(i=0; i < jl_nparams(t); i++)
            c += count_occurs(jl_tparam(t,i), v);
        return c;
    }
    return 0;
}
```
-/
def countOccurs (n : Nat) (t v : Val) : CM Nat := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if t == v then return 1
    match t with
    | .union a b => return max (← countOccurs n a v) (← countOccurs n b v)
    | .unionall id _ _ _ body => if some id == v.tvId then return 0 else countOccurs n body v
    | .vararg (some t) N =>
      let c ← countOccurs n t v
      return c + (← match N with | some N => countOccurs n N v | none => pure 0)
    | .typeeq t | .typeegal t => countOccurs n t v
    | .datatype _ ps =>
      let mut c := 0
      for p in ps do c := c + (← countOccurs n p v)
      return c
    | _ => return 0

/-- `is_indefinite_length_tuple_type`.

Julia source: src/subtype.c:3265-3272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_indefinite_length_tuple_type(jl_value_t *x)
{
    x = jl_unwrap_unionall(x);
    if (!jl_is_tuple_type(x))
        return 0;
    size_t n = jl_nparams(x);
    return n > 0 && jl_vararg_kind(jl_tparam(x, n-1)) == JL_VARARG_UNBOUND;
}
```
-/
def isIndefiniteLengthTupleType (x : Val) : Bool :=
  let x := x.unwrapUnionall
  x.isTupleType && x.params.getLast?.any (·.varargKind == .unbound)

/-- `is_definite_length_tuple_type`.

Julia source: src/subtype.c:3274-3286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_definite_length_tuple_type(jl_value_t *x)
{
    if (jl_is_typevar(x))
        x = ((jl_tvar_t*)x)->ub;
    x = jl_unwrap_unionall(x);
    if (!jl_is_tuple_type(x))
        return 0;
    size_t n = jl_nparams(x);
    if (n == 0)
        return 1;
    jl_vararg_kind_t k = jl_vararg_kind(jl_tparam(x, n-1));
    return k == JL_VARARG_NONE || k == JL_VARARG_INT;
}
```
-/
def isDefiniteLengthTupleType (x : Val) : Bool :=
  let x := (if x.isTypevar then x.tvUb else x).unwrapUnionall
  x.isTupleType && (x.params.isEmpty || x.params.getLast?.any (fun p => p.varargKind == .none || p.varargKind == .int))

/-- `is_existential_typevar`.

Julia source: src/subtype.c:3288-3294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int is_existential_typevar(jl_value_t *x, jl_stenv_t *e)
{
    if (!jl_is_typevar(x))
        return 0;
    jl_varbinding_t *vb = lookup(e, (jl_tvar_t *)x);
    return vb && vb->existential;
}
```
-/
def isExistentialTypevar (x : Val) : STM Bool := do
  if !x.isTypevar then return false
  match ← lookup x with
  | none => return false
  | some i => return (← getBinding i).existential

/-- `init_stenv` for NULL envout.

Julia source: src/subtype.c:3556-3583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void init_stenv(jl_stenv_t *e, jl_value_t **env, int envsz)
{
    e->vars = NULL;
    e->envsz = envsz;
    e->envout = env;
    if (envsz) {
        assert(env != NULL);
        memset(env, 0, envsz*sizeof(void*));
    }
    e->envidx = 0;
    e->invdepth = 0;
    e->bound_channel = BOUND_EGAL;
    e->spell_channel = BOUND_EGAL;
    e->value_descent = 0;
    e->intersection = 0;
    e->emptiness_only = 0;
    e->triangular = 0;
    e->ignore_lb_required = 0;
    e->closed_inputs = 0;
    e->inputs[0] = e->inputs[1] = NULL;
    e->intersecting = NULL;
    e->Loffset = 0;
    e->Lunions.depth = 0;      e->Runions.depth = 0;
    e->Lunions.more = 0;       e->Runions.more = 0;
    e->Lunions.used = 0;       e->Runions.used = 0;
    e->Lunions.stack.next = NULL;
    e->Runions.stack.next = NULL;
}
```
-/
def initStenv : StEnv := {}

/-- `jl_subtype_env_size`.

Julia source: src/subtype.c:3587-3595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_subtype_env_size(jl_value_t *t)
{
    int sz = 0;
    while (jl_is_unionall(t)) {
        sz++;
        t = ((jl_unionall_t*)t)->body;
    }
    return sz;
}
```
-/
def jlSubtypeEnvSize (n : Nat) (t : Val) : CM Nat := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t with
    | .unionall _ _ _ _ body => return 1 + (← jlSubtypeEnvSize n body)
    | _ => return 0

/-- `concrete_min`.

Julia source: src/subtype.c:3599-3622 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int concrete_min(jl_value_t *t)
{
    if (jl_is_unionall(t))
        t = jl_unwrap_unionall(t);
    if (t == (jl_value_t*)jl_bottom_type)
        return 1;
    if (jl_is_some_Type(t))
        return 0; // Type{T}/TypeEgal{T} may have the concrete supertype `typeof(T)`, so don't try to handle them here
    if (jl_is_datatype(t)) {
        return jl_is_concrete_type(t) ? 1 : 2;
    }
    if (jl_is_vararg(t))
        return 0;
    if (jl_is_typevar(t))
        return 0; // could be 0 or more, since we didn't track if it was unbound
    if (jl_is_uniontype(t)) {
        int count = concrete_min(((jl_uniontype_t*)t)->a);
        if (count > 1)
            return count;
        return count + concrete_min(((jl_uniontype_t*)t)->b);
    }
    assert(!jl_is_kind(t));
    return 1; // a non-Type is also considered concrete
}
```
-/
def concreteMin (n : Nat) (T : Types) (t : Val) : CM Nat := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let t := t.unwrapUnionall
    if t == .bottom then return 1
    if t.isSomeType then return 0
    if t.isDatatype then return if ← isConcreteType T t then 1 else 2
    if t.isVararg || t.isTypevar then return 0
    match t with
    | .union a b =>
      let c ← concreteMin n T a
      if c > 1 then return c
      return c + (← concreteMin n T b)
    | _ => return 1

/-- `find_var_body`.

Julia source: src/subtype.c:3624-3659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *find_var_body(jl_value_t *t, jl_tvar_t *v) JL_NOTSAFEPOINT
{
    if (jl_is_unionall(t)) {
        if (((jl_unionall_t*)t)->var == v)
            return ((jl_unionall_t*)t)->body;
        jl_value_t *b = find_var_body(((jl_unionall_t*)t)->var->lb, v);
        if (b) return b;
        b = find_var_body(((jl_unionall_t*)t)->var->ub, v);
        if (b) return b;
        return find_var_body(((jl_unionall_t*)t)->body, v);
    }
    else if (jl_is_uniontype(t)) {
        jl_value_t *b = find_var_body(((jl_uniontype_t*)t)->a, v);
        if (b) return b;
        return find_var_body(((jl_uniontype_t*)t)->b, v);
    }
    else if (jl_is_vararg(t)) {
        jl_vararg_t *vm = (jl_vararg_t *)t;
        if (vm->T) {
            jl_value_t *b = find_var_body(vm->T, v);
            if (b) return b;
            if (vm->N) {
                return find_var_body(vm->N, v);
            }
        }
    }
    else if (jl_is_datatype(t)) {
        size_t i;
        for (i=0; i < jl_nparams(t); i++) {
            jl_value_t *b = find_var_body(jl_tparam(t, i), v);
            if (b)
                return b;
        }
    }
    return NULL;
}
```
-/
def findVarBody (n : Nat) (t v : Val) : CM (Option Val) := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t with
    | .unionall id _ lb ub body =>
      if some id == v.tvId then return some body
      if let some b ← findVarBody n lb v then return some b
      if let some b ← findVarBody n ub v then return some b
      findVarBody n body v
    | .union a b =>
      if let some r ← findVarBody n a v then return some r
      findVarBody n b v
    | .vararg (some t) N =>
      if let some b ← findVarBody n t v then return some b
      match N with | some N => findVarBody n N v | none => return none
    | .datatype _ ps =>
      for p in ps do
        if let some b ← findVarBody n p v then return some b
      return none
    | _ => return none

/-- `typeeq_splittable`.

Julia source: src/subtype.c:2504-2541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_splittable(jl_value_t *p, typeeq_varctx_t *env) JL_NOTSAFEPOINT
{
    if (jl_is_uniontype(p))
        return 1;
    if (jl_is_vararg(p))
        // `Tuple{Vararg{T}} == Union{Tuple{}, Tuple{T, Vararg{T}}}` (a length
        // split); fixed-length varargs were expanded at construction time
        return 1;
    if (jl_is_typevar(p)) {
        typeeq_varctx_t *ctx = typeeq_lookup_var(env, (jl_tvar_t*)p);
        if (ctx != NULL && ctx->pinned)
            return typeeq_splittable(((jl_tvar_t*)p)->lb, env);
        jl_value_t *ub = ((jl_tvar_t*)p)->ub;
        // a var can range over (or instantiate to) union values unless its
        // upper bound is concrete
        if (jl_has_free_typevars(ub) || !jl_is_concrete_type(ub))
            return 1;
        return typeeq_splittable(ub, env);
    }
    if (jl_is_unionall(p)) {
        jl_unionall_t *u = (jl_unionall_t*)p;
        typeeq_varctx_t ctx = { u->var, u->var->lb == u->var->ub, env };
        return typeeq_splittable(u->body, &ctx);
    }
    if (jl_is_datatype(p)) {
        if (((jl_datatype_t*)p)->name == jl_tuple_typename) {
            size_t i, np = jl_nparams(p);
            for (i = 0; i < np; i++) {
                if (typeeq_splittable(jl_tparam(p, i), env))
                    return 1;
            }
        }
        return 0;
    }
    // `TypeEq`/`TypeEgal` wrappers are invariant in their parameter; remaining
    // values (numbers, symbols) are not types
    return 0;
}
```
-/
def typeeqSplittable (n : Nat) (T : Types) (p : Val) (env : TypeeqVarctx) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match p with
    | .union .. | .vararg .. => return true
    | .typevar _ _ lb ub =>
      if typeeqLookupVar env p == some true then return ← typeeqSplittable n T lb env
      if ub.hasFreeTypevars then return true
      if !(← isConcreteType T ub) then return true
      typeeqSplittable n T ub env
    | .unionall id _ lb ub body => typeeqSplittable n T body ((id, lb == ub) :: env)
    | .datatype name ps =>
      if name != tupleName then return false
      ps.anyM fun p => typeeqSplittable n T p env
    | _ => return false

/-- `typeeq_bottomable`.

Julia source: src/subtype.c:2547-2578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_bottomable(jl_value_t *p, typeeq_varctx_t *env) JL_NOTSAFEPOINT
{
    if (p == jl_bottom_type)
        return 1;
    if (jl_is_typevar(p)) {
        typeeq_varctx_t *ctx = typeeq_lookup_var(env, (jl_tvar_t*)p);
        if (ctx != NULL)
            return ctx->pinned ? typeeq_bottomable(((jl_tvar_t*)p)->lb, env) : 0;
        jl_value_t *lb = ((jl_tvar_t*)p)->lb;
        return lb == jl_bottom_type || jl_is_typevar(lb);
    }
    if (jl_is_uniontype(p)) {
        return typeeq_bottomable(((jl_uniontype_t*)p)->a, env) &&
               typeeq_bottomable(((jl_uniontype_t*)p)->b, env);
    }
    if (jl_is_unionall(p)) {
        jl_unionall_t *u = (jl_unionall_t*)p;
        typeeq_varctx_t ctx = { u->var, u->var->lb == u->var->ub, env };
        return typeeq_bottomable(u->body, &ctx);
    }
    if (jl_is_datatype(p) && ((jl_datatype_t*)p)->name == jl_tuple_typename) {
        size_t i, np = jl_nparams(p);
        for (i = 0; i < np; i++) {
            jl_value_t *pi = jl_tparam(p, i);
            // a `Union{}` instantiation of a `Vararg` element admits length 0
            // instead of collapsing the tuple
            if (!jl_is_vararg(pi) && typeeq_bottomable(pi, env))
                return 1;
        }
    }
    return 0;
}
```
-/
def typeeqBottomable (n : Nat) (p : Val) (env : TypeeqVarctx) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if p == .bottom then return true
    match p with
    | .typevar _ _ lb _ =>
      match typeeqLookupVar env p with
      | some true => typeeqBottomable n lb env
      | some false => return false
      | none => return lb == .bottom || lb.isTypevar
    | .union a b =>
      if !(← typeeqBottomable n a env) then return false
      typeeqBottomable n b env
    | .unionall id _ lb ub body => typeeqBottomable n body ((id, lb == ub) :: env)
    | .datatype name ps =>
      if name != tupleName then return false
      ps.anyM fun p => if p.isVararg then pure false else typeeqBottomable n p env
    | _ => return false

/-- `typeeq_union_arms_stable`.

Julia source: src/subtype.c:2584-2590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_union_arms_stable(jl_value_t *t) JL_NOTSAFEPOINT
{
    if (jl_is_uniontype(t))
        return typeeq_union_arms_stable(((jl_uniontype_t*)t)->a) &&
               typeeq_union_arms_stable(((jl_uniontype_t*)t)->b);
    return jl_is_datatype(t) || jl_is_typeeq(t) || jl_is_typeegal(t);
}
```
-/
def typeeqUnionArmsStable (n : Nat) (t : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t with
    | .union a b =>
      if !(← typeeqUnionArmsStable n a) then return false
      typeeqUnionArmsStable n b
    | _ => return t.isDatatype || t.isSomeType

/-- `typeeq_all_tuplish`.

Julia source: src/subtype.c:2595-2603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_all_tuplish(jl_value_t *t) JL_NOTSAFEPOINT
{
    while (jl_is_unionall(t))
        t = ((jl_unionall_t*)t)->body;
    if (jl_is_uniontype(t))
        return typeeq_all_tuplish(((jl_uniontype_t*)t)->a) &&
               typeeq_all_tuplish(((jl_uniontype_t*)t)->b);
    return jl_is_datatype(t) && ((jl_datatype_t*)t)->name == jl_tuple_typename;
}
```
-/
def typeeqAllTuplish (n : Nat) (t : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t.unwrapUnionall with
    | .union a b =>
      if !(← typeeqAllTuplish n a) then return false
      typeeqAllTuplish n b
    | t => return t.isTupleType

/-- `typeeq_kind_mask1`.

Julia source: src/subtype.c:2605-2730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_kind_mask1(jl_value_t *t, typeeq_varctx_t *env) JL_NOTSAFEPOINT
{
    if (t == jl_bottom_type)
        return TYPEEQ_KIND_BOTTOM;
    if (jl_is_typevar(t)) {
        typeeq_varctx_t *ctx = typeeq_lookup_var(env, (jl_tvar_t*)t);
        if (ctx != NULL) {
            if (ctx->pinned)
                return typeeq_kind_mask1(((jl_tvar_t*)t)->lb, env);
            // a parameter-local `S where lb<:S<:ub` with a bare-var body
            // denotes the class of `ub`
            return typeeq_kind_mask1(((jl_tvar_t*)t)->ub, env);
        }
        // a bare environment var is handled by the typevar rules instead
        return TYPEEQ_KIND_ALL;
    }
    if (jl_is_typeeq(t)) {
        // members are `Type{X}` objects; if the parameter can instantiate to
        // `Union{}`, the class also contains the `TypeofBottom` DataType
        // (`Type{Union{}} == TypeofBottom`, the bottom object being unique).
        // A typevar parameter additionally admits the nominal `AnyType`
        // DataType: `(Type{S} where S) == AnyType` when `S` spans all types.
        int mask = TYPEEQ_KIND_TYPEEQ;
        jl_value_t *tp = jl_typeeq_T(t);
        if (jl_is_typevar(tp) || typeeq_bottomable(tp, env))
            mask |= TYPEEQ_KIND_DATATYPE;
        return mask;
    }
    if (jl_is_typeegal(t))
        return TYPEEQ_KIND_TYPEEGAL;
    if (jl_is_datatype(t)) {
        jl_datatype_t *dt = (jl_datatype_t*)t;
        if (dt == jl_typeofbottom_type)
            // `TypeofBottom == Type{Union{}}`, whose object is `TypeEq`-kinded
            return TYPEEQ_KIND_DATATYPE | TYPEEQ_KIND_TYPEEQ;
        int mask = TYPEEQ_KIND_DATATYPE;
        if (dt->name == jl_tuple_typename) {
            size_t i, np = jl_nparams(t);
            for (i = 0; i < np; i++) {
                jl_value_t *pi = jl_tparam(t, i);
                if (typeeq_splittable(pi, env))
                    mask |= TYPEEQ_KIND_UNION;
                if (!jl_is_vararg(pi) && typeeq_bottomable(pi, env))
                    mask |= TYPEEQ_KIND_BOTTOM;
            }
        }
        return mask;
    }
    if (jl_is_uniontype(t)) {
        jl_uniontype_t *u = (jl_uniontype_t*)t;
        if (!typeeq_union_arms_stable(t))
            return TYPEEQ_KIND_ALL;
        int mask = TYPEEQ_KIND_UNION;
        if (typeeq_all_tuplish(t))
            mask |= TYPEEQ_KIND_DATATYPE;
        // instantiating a free var can collapse the union: a component may
        // become empty or absorb into another (`Union{Ref{T},Ref{Int}}` is the
        // DataType `Ref{Int}` when `T == Int`), leaving the class of any
        // subset of the components (of `Union{}` itself if all become empty)
        int collapse = jl_has_free_typevars(t);
        int abot = typeeq_bottomable(u->a, env);
        int bbot = typeeq_bottomable(u->b, env);
        if (abot || collapse)
            mask |= typeeq_kind_mask1(u->b, env);
        if (bbot || collapse)
            mask |= typeeq_kind_mask1(u->a, env);
        if (abot && bbot)
            mask |= TYPEEQ_KIND_BOTTOM;
        return mask;
    }
    if (jl_is_unionall(t)) {
        jl_unionall_t *u = (jl_unionall_t*)t;
        if (u->var->lb == u->var->ub) {
            // a pinned var is equivalent to substituting its bound
            typeeq_varctx_t ctx = { u->var, 1, env };
            return typeeq_kind_mask1(u->body, &ctx);
        }
        // Try the "wrapper-like" shape: every non-pinned var has `lb === Union{}`
        // and closed bounds and occurs exactly once, directly as a parameter of
        // a nominal (non-Tuple) core -- e.g. `Vector` = `Array{T,1} where T`.
        // No `DataType` or `Union` can be `==` to such a type: a mutual-subtype
        // candidate would have to match that invariant parameter for every
        // instantiation of a var that ranges over at least two distinct
        // classes. Its class then consists of `UnionAll` representatives only.
        jl_value_t *core = t;
        int wrapperlike = 1;
        while (jl_is_unionall(core)) {
            jl_tvar_t *v = ((jl_unionall_t*)core)->var;
            jl_value_t *body = ((jl_unionall_t*)core)->body;
            if (v->lb != v->ub &&
                (v->lb != jl_bottom_type || jl_has_free_typevars(v->ub) ||
                 count_occurs(body, v) != 1)) {
                wrapperlike = 0;
                break;
            }
            core = body;
        }
        if (wrapperlike && jl_is_datatype(core) &&
            ((jl_datatype_t*)core)->name != jl_tuple_typename &&
            (jl_datatype_t*)core != jl_typeofbottom_type) {
            // each non-pinned var must appear directly as a parameter of the core
            jl_value_t *w = t;
            size_t i, np = jl_nparams(core);
            while (jl_is_unionall(w)) {
                jl_tvar_t *v = ((jl_unionall_t*)w)->var;
                if (v->lb != v->ub) {
                    for (i = 0; i < np; i++) {
                        if (jl_tparam(core, i) == (jl_value_t*)v)
                            break;
                    }
                    if (i == np) {
                        wrapperlike = 0;
                        break;
                    }
                }
                w = ((jl_unionall_t*)w)->body;
            }
            if (wrapperlike)
                return 0; // `UnionAll` representatives only
        }
        // conservative: analyze the body with the var ranging over its bounds
        typeeq_varctx_t ctx = { u->var, 0, env };
        return typeeq_kind_mask1(u->body, &ctx);
    }
    return TYPEEQ_KIND_ALL; // non-type (defensive)
}
```
-/
def typeeqKindMask1 (n : Nat) (T : Types) (t : Val) (env : TypeeqVarctx) : CM Nat := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if t == .bottom then return 1
    match t with
    | .typevar _ _ lb ub =>
      match typeeqLookupVar env t with
      | some pinned => typeeqKindMask1 n T (if pinned then lb else ub) env
      | none => return 63
    | .typeeq p =>
      if p.isTypevar then return 18
      if ← typeeqBottomable n p env then return 18
      return 16
    | .typeegal _ => return 32
    | .datatype name ps =>
      if t == typeofbottomType then return 18
      let mut mask := 2
      if name == tupleName then
        for p in ps do
          if ← typeeqSplittable n T p env then mask := mask ||| 4
          if !p.isVararg then
            if ← typeeqBottomable n p env then mask := mask ||| 1
      return mask
    | .union a b =>
      if !(← typeeqUnionArmsStable n t) then return 63
      let mut mask := 4
      if ← typeeqAllTuplish n t then mask := mask ||| 2
      let collapse := t.hasFreeTypevars
      let abot ← typeeqBottomable n a env
      let bbot ← typeeqBottomable n b env
      if abot || collapse then mask := mask ||| (← typeeqKindMask1 n T b env)
      if bbot || collapse then mask := mask ||| (← typeeqKindMask1 n T a env)
      if abot && bbot then mask := mask ||| 1
      return mask
    | .unionall id _ lb ub body =>
      if lb == ub then return ← typeeqKindMask1 n T body ((id, true) :: env)
      let mut core := t
      let mut wrapperlike := true
      for _ in [0:n] do
        match core with
        | .unionall id nm lb ub body =>
          if lb != ub then
            if lb != .bottom || ub.hasFreeTypevars then wrapperlike := false; break
            if (← countOccurs n body (.typevar id nm lb ub)) != 1 then wrapperlike := false; break
          core := body
        | _ => break
      if core.isUnionall && wrapperlike then outOfBudget
      else if wrapperlike && core.isDatatype && !core.isTupleType && core != typeofbottomType then
        let mut w := t
        for _ in [0:n] do
          match w with
          | .unionall id nm lb ub body =>
            if lb != ub && !core.params.contains (.typevar id nm lb ub) then
              wrapperlike := false
              break
            w := body
          | _ => break
        if w.isUnionall && wrapperlike then outOfBudget
        else if wrapperlike then return 0
        else typeeqKindMask1 n T body ((id, false) :: env)
      else typeeqKindMask1 n T body ((id, false) :: env)
    | _ => return 63

/-- `typeeq_kind_mask`.

Julia source: src/subtype.c:2735-2740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_kind_mask(jl_value_t *t) JL_NOTSAFEPOINT
{
    if (t == jl_bottom_type)
        return TYPEEQ_KIND_BOTTOM; // the bottom object is unique (see above)
    return TYPEEQ_KIND_UNIONALL | typeeq_kind_mask1(t, NULL);
}
```
-/
def typeeqKindMask (n : Nat) (T : Types) (t : Val) : CM Nat := do
  if t == .bottom then return 1
  return 8 ||| (← typeeqKindMask1 n T t [])

/-- `typeeq_kind_datatype`.

Julia source: src/subtype.c:2762-2773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_datatype_t *typeeq_kind_datatype(int bit) JL_NOTSAFEPOINT
{
    switch (bit) {
    case TYPEEQ_KIND_BOTTOM:   return jl_typeofbottom_type;
    case TYPEEQ_KIND_DATATYPE: return jl_datatype_type;
    case TYPEEQ_KIND_UNION:    return jl_uniontype_type;
    case TYPEEQ_KIND_UNIONALL: return jl_unionall_type;
    case TYPEEQ_KIND_TYPEEQ:   return jl_typeeq_type;
    default:                   assert(bit == TYPEEQ_KIND_TYPEEGAL);
                               return jl_typeegal_type;
    }
}
```
-/
def typeeqKindDatatype (bit : Nat) : CM Val :=
  match bit with
  | 1 => pure typeofbottomType
  | 2 => pure datatypeType
  | 4 => pure uniontypeType
  | 8 => pure unionallType
  | 16 => pure typeeqType
  | 32 => pure typeegalType
  | _ => throw "typeeq_kind_datatype: kind bit assertion"

/-- `typeeq_collect_closed_components`, capped at 32 in its only subtyping caller.

Julia source: src/subtype.c:2823-2832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void typeeq_collect_closed_components(jl_value_t *y, jl_value_t **out, size_t *n, size_t cap) JL_NOTSAFEPOINT
{
    if (jl_is_uniontype(y)) {
        typeeq_collect_closed_components(((jl_uniontype_t*)y)->a, out, n, cap);
        typeeq_collect_closed_components(((jl_uniontype_t*)y)->b, out, n, cap);
        return;
    }
    if (*n < cap && !jl_has_free_typevars(y))
        out[(*n)++] = y;
}
```
-/
def typeeqCollectClosedComponents (n : Nat) (y : Val) (acc : Array Val) (cap : Nat) : CM (Array Val) := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match y with
    | .union a b =>
      let acc ← typeeqCollectClosedComponents n a acc cap
      typeeqCollectClosedComponents n b acc cap
    | _ => return if acc.size < cap && !y.hasFreeTypevars then acc.push y else acc

/-- `union_has_kind_component`.

Julia source: src/subtype.c:2867-2873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int union_has_kind_component(jl_value_t *y) JL_NOTSAFEPOINT
{
    if (jl_is_uniontype(y))
        return union_has_kind_component(((jl_uniontype_t*)y)->a) ||
               union_has_kind_component(((jl_uniontype_t*)y)->b);
    return is_kind_or_anytype(y);
}
```
-/
def unionHasKindComponent (n : Nat) (y : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match y with
    | .union a b =>
      if ← unionHasKindComponent n a then return true
      unionHasKindComponent n b
    | _ => return isKindOrAnytype y

/-- `typeeq_vars_bound_in_env`.

Julia source: src/subtype.c:2883-2916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_vars_bound_in_env(jl_value_t *t, jl_stenv_t *e, typeeq_varctx_t *wenv) JL_NOTSAFEPOINT
{
    if (jl_is_typevar(t)) {
        int inner = 0;
        return lookup_binding(e, (jl_tvar_t*)t, &inner) != NULL || inner ||
               typeeq_lookup_var(wenv, (jl_tvar_t*)t) != NULL;
    }
    if (jl_is_uniontype(t))
        return typeeq_vars_bound_in_env(((jl_uniontype_t*)t)->a, e, wenv) ||
               typeeq_vars_bound_in_env(((jl_uniontype_t*)t)->b, e, wenv);
    if (jl_is_unionall(t)) {
        jl_unionall_t *u = (jl_unionall_t*)t;
        return typeeq_vars_bound_in_env(u->var->lb, e, wenv) ||
               typeeq_vars_bound_in_env(u->var->ub, e, wenv) ||
               typeeq_vars_bound_in_env(u->body, e, wenv);
    }
    if (jl_is_vararg(t)) {
        jl_vararg_t *vm = (jl_vararg_t*)t;
        return (vm->T && typeeq_vars_bound_in_env(vm->T, e, wenv)) ||
               (vm->N && typeeq_vars_bound_in_env(vm->N, e, wenv));
    }
    if (jl_is_some_Type(t))
        return typeeq_vars_bound_in_env(jl_some_Type_T(t), e, wenv);
    if (jl_is_datatype(t)) {
        if (!((jl_datatype_t*)t)->hasfreetypevars)
            return 0;
        size_t i, np = jl_nparams(t);
        for (i = 0; i < np; i++) {
            if (typeeq_vars_bound_in_env(jl_tparam(t, i), e, wenv))
                return 1;
        }
    }
    return 0;
}
```
-/
def typeeqVarsBoundInEnv (n : Nat) (t : Val) (wenv : TypeeqVarctx) : STM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t with
    | .typevar .. =>
      let (ptr, inner) ← lookupBinding t
      return ptr.isSome || inner || (typeeqLookupVar wenv t).isSome
    | .union a b =>
      if ← typeeqVarsBoundInEnv n a wenv then return true
      typeeqVarsBoundInEnv n b wenv
    | .unionall _ _ lb ub body =>
      if ← typeeqVarsBoundInEnv n lb wenv then return true
      if ← typeeqVarsBoundInEnv n ub wenv then return true
      typeeqVarsBoundInEnv n body wenv
    | .vararg t N =>
      if let some t := t then if ← typeeqVarsBoundInEnv n t wenv then return true
      if let some N := N then return ← typeeqVarsBoundInEnv n N wenv
      return false
    | .typeeq t | .typeegal t => typeeqVarsBoundInEnv n t wenv
    | .datatype _ ps =>
      if !t.dtHasFreeTypevars then return false
      ps.anyM fun p => typeeqVarsBoundInEnv n p wenv
    | _ => return false

/-- `typeeq_is_dangling_key`.

Julia source: src/subtype.c:2920-2923 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_is_dangling_key(jl_value_t *t, jl_stenv_t *e, typeeq_varctx_t *wenv) JL_NOTSAFEPOINT
{
    return jl_has_free_typevars(t) && !typeeq_vars_bound_in_env(t, e, wenv);
}
```
-/
def typeeqIsDanglingKey (n : Nat) (t : Val) (wenv : TypeeqVarctx) : STM Bool := do
  if !t.hasFreeTypevars then return false
  return !(← typeeqVarsBoundInEnv n t wenv)

/-- `widen_pinned_Type`.

Julia source: src/subtype.c:1458-1470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *widen_pinned_Type(jl_value_t *t JL_PROPAGATES_ROOT, jl_stenv_t *e, typeeq_varctx_t *wenv) JL_NOTSAFEPOINT
{
    if (jl_is_typeegal(t))
        return jl_typeof(jl_typeegal_T(t));
    if (jl_is_typeeq(t) && !jl_is_typevar(jl_typeeq_T(t))) {
        jl_value_t *T = jl_typeeq_T(t);
        if (T == jl_bottom_type)
            return (jl_value_t*)jl_typeofbottom_type;
        if (jl_has_free_typevars(T) && !typeeq_vars_bound_in_env(T, e, wenv))
            return jl_typeof(T);
    }
    return NULL;
}
```
-/
def widenPinnedType (n : Nat) (t : Val) (wenv : TypeeqVarctx) : STM (Option Val) := do
  if t.isTypeegal then return some (typeOf t.someTypeT)
  if t.isTypeeq && !t.someTypeT.isTypevar then
    let tp := t.someTypeT
    if tp == .bottom then return some typeofbottomType
    if tp.hasFreeTypevars then
      if !(← typeeqVarsBoundInEnv n tp wenv) then return some (typeOf tp)
  return none

/-- `pins_typeof_static`.

Julia source: src/subtype.c:1566-1597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int pins_typeof_static(jl_tvar_t *v, jl_value_t *t) JL_NOTSAFEPOINT
{
    if (t == (jl_value_t*)v)
        return 1;
    while (jl_is_unionall(t)) {
        jl_unionall_t *ua = (jl_unionall_t*)t;
        if (ua->var->ub == (jl_value_t*)v && ua->var->lb == jl_bottom_type &&
            pins_typeof_static(ua->var, ua->body))
            // the least solution for `v` is the other variable's value
            return 1;
        if (ua->var == v)
            return 0; // `v` is rebound
        t = ua->body;
    }
    if (jl_is_uniontype(t)) {
        return pins_typeof_static(v, ((jl_uniontype_t*)t)->a) &&
               pins_typeof_static(v, ((jl_uniontype_t*)t)->b);
    }
    if (!jl_is_datatype(t) || jl_is_abstracttype(t))
        return 0;
    jl_datatype_t *dt = (jl_datatype_t*)t;
    if (dt->name == jl_tuple_typename) {
        size_t fc = jl_nparams(dt);
        for (size_t i = 0; i < fc; i++) {
            jl_value_t *p = jl_tparam(dt, i);
            // a `Vararg` tail may match zero arguments
            if (!jl_is_vararg(p) && pins_typeof_static(v, p))
                return 1;
        }
    }
    return 0;
}
```
-/
def pinsTypeofStatic (n : Nat) (T : Types) (v t : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if t == v then return true
    match t with
    | .unionall id nm lb ub body =>
      let tv := Val.typevar id nm lb ub
      if ub == v && lb == .bottom then
        if ← pinsTypeofStatic n T tv body then return true
      if tv.tvId == v.tvId then return false
      pinsTypeofStatic n T v body
    | .union a b =>
      if !(← pinsTypeofStatic n T v a) then return false
      pinsTypeofStatic n T v b
    | .datatype name ps =>
      if ← isAbstractType T t then return false
      if name != tupleName then return false
      ps.anyM fun p => if p.isVararg then pure false else pinsTypeofStatic n T v p
    | _ => return false

/-- `constrains_param_static`.

Julia source: src/subtype.c:1607-1670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int constrains_param_static(jl_tvar_t *var, jl_value_t *typ, int covariant) JL_NOTSAFEPOINT
{
    if (typ == (jl_value_t*)var)
        // a covariant occurrence contributes `typeof` of an argument as a
        // lower bound, which determines the least solution only when the
        // declared lower bound does not also union into it
        return !covariant || var->lb == jl_bottom_type;
    while (jl_is_unionall(typ)) {
        jl_unionall_t *ua = (jl_unionall_t*)typ;
        // occurrences in the inner variable's declared bound pin `var` only
        // when every call pins that variable to a `typeof`-produced argument
        // type, satisfying its bounds without constraining them.
        if (covariant && ua->var->lb == jl_bottom_type &&
            jl_has_typevar(ua->var->ub, var) &&
            pins_typeof_static(ua->var, ua->body) &&
            constrains_param_static(var, ua->var->ub, 1))
            return 1;
        if (ua->var == var) // `var` is rebound
            return 0;
        typ = ua->body;
    }
    if (jl_is_uniontype(typ)) {
        // conservatively, both alternatives must constrain var
        return constrains_param_static(var, ((jl_uniontype_t*)typ)->a, covariant) &&
               constrains_param_static(var, ((jl_uniontype_t*)typ)->b, covariant);
    }
    else if (jl_is_typeeq(typ)) {
        return constrains_param_static(var, jl_typeeq_T(typ), 0);
    }
    else if (jl_is_datatype(typ)) {
        jl_datatype_t *dt = (jl_datatype_t*)typ;
        size_t fc = jl_nparams(dt);
        if (fc > 0) {
            if (dt->name == jl_tuple_typename) {
                for (size_t i = 0; i < fc - 1; i++) {
                    if (constrains_param_static(var, jl_tparam(dt, i), covariant))
                        return 1;
                }
                jl_value_t *lastp = jl_tparam(dt, fc - 1);
                jl_value_t *vararg = jl_unwrap_unionall(lastp);
                if (jl_is_vararg(vararg)) {
                    jl_value_t *vN = jl_unwrap_vararg_num(vararg);
                    if (vN) {
                        if (constrains_param_static(var, vN, covariant))
                            return 1;
                    }
                    else if (constrains_param_static(var, lastp, covariant)) {
                        return 1;
                    }
                }
                else if (constrains_param_static(var, lastp, covariant)) {
                    return 1;
                }
            }
            else {
                for (size_t i = 0; i < fc; i++) {
                    if (constrains_param_static(var, jl_tparam(dt, i), 0))
                        return 1;
                }
            }
        }
    }
    return 0;
}
```
-/
def constrainsParamStatic (n : Nat) (T : Types) (var typ : Val) (covariant : Bool) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if typ == var then return !covariant || var.tvLb == .bottom
    match typ with
    | .unionall id nm lb ub body =>
      let tv := Val.typevar id nm lb ub
      if covariant && lb == .bottom && ub.hasTypevar var then
        if ← pinsTypeofStatic n T tv body then
          if ← constrainsParamStatic n T var ub true then return true
      if some id == var.tvId then return false
      constrainsParamStatic n T var body covariant
    | .union a b =>
      if !(← constrainsParamStatic n T var a covariant) then return false
      constrainsParamStatic n T var b covariant
    | .typeeq p => constrainsParamStatic n T var p false
    | .datatype name ps =>
      if ps.isEmpty then return false
      if name == tupleName then
        for p in ps.dropLast do
          if ← constrainsParamStatic n T var p covariant then return true
        let p := ps.getLast!
        let va := p.unwrapUnionall
        if va.isVararg then
          match va.varargN? with
          | some N => constrainsParamStatic n T var N covariant
          | none => constrainsParamStatic n T var p covariant
        else constrainsParamStatic n T var p covariant
      else ps.anyM fun p => constrainsParamStatic n T var p false
    | _ => return false

/-- `mark_required_tuple_element`.

Julia source: src/subtype.c:1672-1681 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void mark_required_tuple_element(jl_stenv_t *e, jl_value_t *rhs) JL_NOTSAFEPOINT
{
    if (e->ignore_lb_required)
        return;
    for (jl_varbinding_t *v = e->vars; v != NULL; v = v->prev) {
        if (v->existential && v->lb != jl_bottom_type && !v->lb_required &&
            constrains_param_static(v->var, rhs, 1))
            v->lb_required = 1;
    }
}
```
-/
def markRequiredTupleElement (n : Nat) (T : Types) (rhs : Val) : STM Unit := do
  if (← get).ignoreLbRequired then return
  for i in [0:(← get).vars.size] do
    let b ← getBinding i
    if b.existential && b.lb != .bottom && !b.lbRequired then
      if ← constrainsParamStatic n T b.var rhs true then
        changeBinding i fun b => { b with lbRequired := true }

/-- `env_unchanged`.

Julia source: src/subtype.c:1003-1034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int env_unchanged(jl_stenv_t *e, jl_savedenv_t *se) JL_NOTSAFEPOINT
{
    jl_value_t **roots = NULL;
    if (se->gcframe.nroots == JL_GC_ENCODE_PUSHARGS(1)) {
        jl_svec_t *sv = (jl_svec_t*)se->roots[0];
        assert(jl_is_svec(sv));
        roots = jl_svec_data(sv);
    }
    else if (se->gcframe.nroots) {
        roots = se->roots;
    }
    jl_varbinding_t *v = e->vars;
    int i = 0, j = 2;
    while (v != NULL) {
        assert(roots != NULL);
        if (v->existential) {
            if (v->lb != roots[i] || v->ub != roots[i + 1])
                return 0; // check if bounds changed
            int8_t saved_cov = se->buf[j];     // saved occurs_cov
            int8_t saved_diag = se->buf[j+1];  // saved cov_diag
            int8_t saved_max = saved_cov > saved_diag ? saved_cov : saved_diag;
            if (is_leaf_typevar(v->var) && cov_count(v) > 1 && saved_max <= 1 && !vb_body_occurs_inv(v))
                return 0; // check if a variable became diagonal from non-diagonal
            if (v->lb_required != se->buf[j+4])
                return 0; // check if envout constrainedness changed
        }
        i += 3; // lb, ub, innervars
        j += JL_SAVEDENV_BYTES_PER_VAR;
        v = v->prev;
    }
    return 1;
}
```
-/
def envUnchanged (n : Nat) (T : Types) (se : SavedEnv) : STM Bool := do
  let vars := (← get).vars
  for i in (List.range vars.size).reverse do
    let b := vars[i]!
    let s := se.vars[i]!
    if b.existential then
      if b.lb != s.lb || b.ub != s.ub then return false
      if ← isLeafTypevar n T b.var then
        if covCount b > 1 && covCount s ≤ 1 then
          if !(← vbBodyOccursInv n i) then return false
      if b.lbRequired != s.lbRequired then return false
  return true

/-- `jl_datatype_compute_super`: instantiate the declared supertype over wrapper variables.

Julia source: src/jltypes.c:3407-3439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_datatype_t *jl_datatype_compute_super(jl_datatype_t *ndt JL_PROPAGATES_ROOT)
{
    // one-time lazy initialization; the acquire pairs with the releasing
    // compare-and-swap below and makes the computed object graph visible
    _Atomic(jl_datatype_t*) *superp = (_Atomic(jl_datatype_t*)*)&ndt->super;
    jl_datatype_t *super = jl_atomic_load_acquire(superp);
    if (super != NULL)
        return super;
    if (ndt->name->wrapper == NULL)
        return NULL; // too early in bootstrap
    jl_datatype_t *primarydt = (jl_datatype_t*)jl_unwrap_unionall(ndt->name->wrapper);
    if (primarydt == ndt || primarydt->super == NULL)
        return NULL; // definition in progress
    size_t nparams = jl_svec_len(ndt->parameters), pi;
    jl_typeenv_t *penv = (jl_typeenv_t*)alloca(nparams * sizeof(jl_typeenv_t));
    for (pi = 0; pi < nparams; pi++) {
        penv[pi].var = (jl_tvar_t*)jl_svecref(primarydt->parameters, pi);
        penv[pi].val = jl_svecref(ndt->parameters, pi);
        penv[pi].prev = pi == 0 ? NULL : &penv[pi - 1];
    }
    jl_typestack_t stop = { ndt, NULL };
    jl_value_t *s = inst_type_w_((jl_value_t*)primarydt->super,
                                 nparams == 0 ? NULL : &penv[nparams - 1],
                                 &stop, 1, 0, NULL);
    // concurrent first queries compute equal values; the compare-and-swap
    // keeps a single winner
    super = NULL;
    jl_gc_wb(ndt, (void*)superp, s);
    if (jl_atomic_cmpswap(superp, &super, (jl_datatype_t*)s)) {
        super = (jl_datatype_t*)s;
    }
    return super;
}
```
-/
def superOf (n : Nat) (T : Types) (ops : Ops) (dt : Val) : CM Val := do
  if n == 0 then outOfBudget else
  if dt == anyType || dt.isTupleType then return anyType
  let .datatype name ps := dt | throw "superOf: not a DataType"
  let tn ← T.typename name
  let some sup := tn.super | throw s!"supertype of {name} is not defined yet"
  let vars := wrapperVars tn.wrapper
  if vars.length != ps.length then throw "superOf: wrong parameter count"
  let env := ((vars.zip ps).map fun (v, p) => (v.tvId.getD 0, p)).reverse
  let some result ← instTypeW n T ops sup env true 0 | throw "unreachable: NULL supertype"
  return result


/-- `has_next_union_state(e, R)` (`src/subtype.c:316`). -/
def hasNextUnionState (R : Bool) : STM Bool := do
  let st ← unionState R
  return st.more != 0

/-- `flip_offset(e)` (`src/subtype.c:588`). -/
def flipOffset : STM Unit :=
  modify fun e => { e with Loffset := -e.Loffset }

/-- `flip_vars`

Julia source: src/subtype.c:5732-5739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void flip_vars(jl_stenv_t *e)
{
    jl_varbinding_t *btemp = e->vars;
    while (btemp != NULL) {
        btemp->existential = !btemp->existential;
        btemp = btemp->prev;
    }
}
```
-/
def flipVars : STM Unit :=
  modify fun e => { e with vars := e.vars.map fun b => { b with existential := !b.existential } }

/-- `wrap_tvar_env(tvar, constrained)`: in `Val`, represented by the `TypeVar` value `tvar`
(matching `_jl_instantiate_type_in_env`'s unwrapping of `svec(tvar, constrained)`).

Julia source: src/subtype.c:1556-1559 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *wrap_tvar_env(jl_value_t *tvar, int constrained) JL_CANSAFEPOINT
{
    return (jl_value_t*)jl_svec2(tvar, constrained ? jl_true : jl_false);
}
```
-/
def wrapTvarEnv (tvar : Val) (_constrained : Bool) : Val :=
  tvar


/-- `jl_is_not_broken_subtype`

Julia source: src/subtype.c:4192-4197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_is_not_broken_subtype(jl_value_t *a, jl_value_t *b)
{
    // TODO: the final commented out check here isn't correct; it should be closer to the
    // `issingletype` check used by `isnotbrokensubtype` in `base/compiler/typeutils.jl`
    return !jl_is_kind(b) || !jl_is_some_Type(a); // || jl_is_datatype_singleton((jl_datatype_t*)jl_tparam0(a));
}
```
-/
def jlIsNotBrokenSubtype (a b : Val) : Bool :=
  !isKind b || !a.isSomeType

/-- `jl_has_intersect_type_not_kind`: return `true` if `t` may meet a type object by its identity
(a `TypeEq{...}` or `TypeEgal{...}` component), rather than only through a kind it contains in full.

Julia source: src/subtype.c:4236-4250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_has_intersect_type_not_kind(jl_value_t *t)
{
    t = jl_unwrap_unionall(t);
    if (t == (jl_value_t*)jl_any_type)
        return 1;
    assert(!jl_is_vararg(t));
    if (jl_is_uniontype(t))
        return jl_has_intersect_type_not_kind(((jl_uniontype_t*)t)->a) ||
               jl_has_intersect_type_not_kind(((jl_uniontype_t*)t)->b);
    if (jl_is_some_Type(t))
        return 1;
    if (jl_is_typevar(t))
        return jl_has_intersect_type_not_kind(((jl_tvar_t*)t)->ub);
    return 0;
}
```
-/
def jlHasIntersectTypeNotKind (n : Nat) (t : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let t := t.unwrapUnionall
    if t == anyType then
      return true
    if let .union ua ub := t then
      if ← jlHasIntersectTypeNotKind n ua then
        return true
      return ← jlHasIntersectTypeNotKind n ub
    if t.isSomeType then
      return true
    if let .typevar _ _ _ ub := t then
      return ← jlHasIntersectTypeNotKind n ub
    return false


/-- `jl_is_dispatch_tupletype` (`src/julia.h:2123-2126`, `src/jltypes.c:2096-2120`). -/
def jlIsDispatchTupletype (T : Types) (v : Val) : CM Bool := do
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

/-- `set_var_to_const`: set a variable at binding index `bb` to a non-type constant.

Julia source: src/subtype.c:4392-4419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *set_var_to_const(jl_varbinding_t *bb, jl_value_t *v JL_MAYBE_UNROOTED, jl_stenv_t *e, int R) JL_CANSAFEPOINT
{
    int offset = R ? -e->Loffset : e->Loffset;
    if (bb->lb == jl_bottom_type && bb->ub == (jl_value_t*)jl_any_type) {
        if (offset == 0)
            bb->lb = bb->ub = v;
        else if (jl_is_long(v)) {
            size_t iv = jl_unbox_long(v);
            v = jl_box_long(iv + offset);
            bb->lb = bb->ub = v;
            // Here we always return the shorter `Vararg`'s length.
            if (offset > 0)
                return jl_box_long(iv);
        }
        else
            return jl_bottom_type;
    }
    else if (jl_is_long(v) && jl_is_long(bb->lb)) {
        if (jl_unbox_long(v) + offset != jl_unbox_long(bb->lb))
            return jl_bottom_type;
        // Here we always return the shorter `Vararg`'s length.
        if (offset < 0) return bb->lb;
    }
    else if (!jl_egal(v, bb->lb)) {
        return jl_bottom_type;
    }
    return v;
}
```
-/
def setVarToConst (n : Nat) (T : Types) (bb : Nat) (v : Val) (R : Bool) : STM Val := do
  let loff := (← get).Loffset
  let offset : Int := if R then -loff else loff
  let b ← getBinding bb
  let mut v := v
  if b.lb == .bottom && b.ub == anyType then
    if offset == 0 then
      changeBinding bb fun x => { x with lb := v, ub := v }
    else if let .long iv := v then
      v := .long (iv + offset)
      changeBinding bb fun x => { x with lb := v, ub := v }
      if offset > 0 then
        return .long iv
    else
      return .bottom
  else if let (.long iv, .long blb) := (v, b.lb) then
    if iv + offset != blb then
      return .bottom
    if offset < 0 then
      return b.lb
  else
    if !(← egal n T v b.lb) then
      return .bottom
  return v

/-- `bound_var_below`

Julia source: src/subtype.c:4421-4450 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *bound_var_below(jl_tvar_t *tv, jl_varbinding_t *bb, jl_stenv_t *e, int R) JL_CANSAFEPOINT {
    if (!bb)
        return (jl_value_t*)tv;
    if (bb->depth0 != e->invdepth)
        return jl_bottom_type;
    e->invdepth++;
    record_var_occurrence(bb, e, PARAM_INVARIANT);
    e->invdepth--;
    int offset = R ? -e->Loffset : e->Loffset;
    if (jl_is_long(bb->lb)) {
        ssize_t blb = jl_unbox_long(bb->lb);
        if (blb < offset || blb < 0)
            return jl_bottom_type;
        // Here we always return the shorter `Vararg`'s length.
        if (offset <= 0)
            return bb->lb;
        return jl_box_long(blb - offset);
    }
    if (offset > 0) {
        if (bb->innervars == NULL)
            bb->innervars = jl_alloc_array_1d(jl_array_any_type, 0);
        jl_value_t *ntv = NULL;
        JL_GC_PUSH1(&ntv);
        ntv = (jl_value_t *)jl_new_typevar(tv->name, jl_bottom_type, (jl_value_t *)jl_any_type);
        jl_array_ptr_1d_push(bb->innervars, ntv);
        JL_GC_POP();
        return ntv;
    }
    return (jl_value_t*)tv;
}
```
-/
def boundVarBelow (tv : Val) (bb : Option Nat) (R : Bool) : STM Val := do
  let some idx := bb | return tv
  let b ← getBinding idx
  if b.depth0 != (← get).invdepth then
    return .bottom
  modify fun e => { e with invdepth := e.invdepth + 1 }
  recordVarOccurrence (some idx) .invariant
  modify fun e => { e with invdepth := e.invdepth - 1 }
  let loff := (← get).Loffset
  let offset : Int := if R then -loff else loff
  if let .long blb := b.lb then
    if blb < offset || blb < 0 then
      return .bottom
    if offset ≤ 0 then
      return b.lb
    return .long (blb - offset)
  if offset > 0 then
    let .typevar _ nm _ _ := tv | return tv
    let ntv ← newTypevar nm .bottom anyType
    pushInnervar idx ntv
    return ntv
  return tv

/-- `compareto_var`

Julia source: src/subtype.c:5835-5851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int compareto_var(jl_value_t *x, jl_tvar_t *y, jl_stenv_t *e, int cmp) JL_NOTSAFEPOINT
{
    if (x == (jl_value_t*)y)
        return 1;
    if (!jl_is_typevar(x))
        return 0;
    int innervar = 0;
    jl_varbinding_t *xv = lookup_binding(e, (jl_tvar_t*)x, &innervar);
    if (xv == NULL && !innervar)
        return 0;
    int ans = 1;
    if (cmp <= 0)
        ans &= compareto_var(xv ? xv->ub : ((jl_tvar_t*)x)->ub, y, e, cmp);
    if (cmp >= 0)
        ans &= compareto_var(xv ? xv->lb : ((jl_tvar_t*)x)->lb, y, e, cmp);
    return ans;
}
```
-/
def comparetoVar (n : Nat) (x y : Val) (cmp : Int) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let x ← resolveVal n x
    let y ← resolveVal n y
    if x.tvId == y.tvId && x.isTypevar then
      return true
    if !x.isTypevar then
      return false
    let (xv, innervar) ← lookupBinding x
    if xv.isNone && !innervar then
      return false
    let xb ← match xv with | some i => do pure (some (← getBinding i)) | none => pure none
    let mut ans := true
    if cmp ≤ 0 then
      let ub := match xb with | some b => b.ub | none => x.tvUb
      ans ← comparetoVar n ub y cmp
    if ans && cmp ≥ 0 then
      let lb := match xb with | some b => b.lb | none => x.tvLb
      ans ← comparetoVar n lb y cmp
    return ans

/-- `subtype_by_bounds`: check whether the environment already asserts `x <: y` via recorded bounds.

Julia source: src/subtype.c:5856-5861 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_by_bounds(jl_value_t *x, jl_value_t *y, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    if (!jl_is_typevar(x) || !jl_is_typevar(y))
        return 0;
    return compareto_var(x, (jl_tvar_t*)y, e, -1) || compareto_var(y, (jl_tvar_t*)x, e, 1);
}
```
-/
def subtypeByBounds (n : Nat) (x y : Val) : STM Bool := do
  if !x.isTypevar || !y.isTypevar then
    return false
  if ← comparetoVar n x y (-1) then
    return true
  comparetoVar n y x 1

/-- `try_subtype_by_bounds`: similar to `subtype_by_bounds`, used to avoid stack-overflow caused by circular constraints.

Julia source: src/subtype.c:4455-4476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int try_subtype_by_bounds(jl_value_t *a, jl_value_t *b, jl_stenv_t *e)
{
    if (jl_is_uniontype(a))
        return try_subtype_by_bounds(((jl_uniontype_t *)a)->a, b, e) &&
               try_subtype_by_bounds(((jl_uniontype_t *)a)->b, b, e);
    else if (jl_is_uniontype(b))
        return try_subtype_by_bounds(a, ((jl_uniontype_t *)b)->a, e) ||
               try_subtype_by_bounds(a, ((jl_uniontype_t *)b)->b, e);
    else if (a == jl_bottom_type || b == (jl_value_t *)jl_any_type || obviously_egal(a, b))
        return 1;
    else if (!jl_is_typevar(b))
        return 0;
    else if (jl_is_typevar(a) && subtype_by_bounds(a, b, e))
        return 1;
    // check if `Union{a, ...} <: b`.
    int innervar = 0;
    jl_varbinding_t *vb = lookup_binding(e, (jl_tvar_t *)b, &innervar);
    if (vb == NULL && !innervar)
        return subtype_singleton_typevar(a, (jl_tvar_t*)b);
    jl_value_t *blb = vb ? vb->lb : ((jl_tvar_t *)b)->lb;
    return obviously_in_union(a, blb);
}
```
-/
def trySubtypeByBounds (n : Nat) (T : Types) (a b : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let a ← resolveVal n a
    let b ← resolveVal n b
    if let .union ua ub := a then
      if !(← trySubtypeByBounds n T ua b) then
        return false
      return ← trySubtypeByBounds n T ub b
    else if let .union ua ub := b then
      if ← trySubtypeByBounds n T a ua then
        return true
      return ← trySubtypeByBounds n T a ub
    else if a == .bottom || b == anyType then
      return true
    else if ← obviouslyEgal n T a b then
      return true
    else if !b.isTypevar then
      return false
    else
      if a.isTypevar then
        if ← subtypeByBounds n a b then
          return true
      let (vb, innervar) ← lookupBinding b
      if vb.isNone && !innervar then
        return ← subtypeSingletonTypevar n a b
      let blb ← match vb with
        | some i => do pure (← getBinding i).lb
        | none => pure b.tvLb
      obviouslyInUnion n T a blb

/-- `_reachable_var`: see if var `y` is reachable from `x` via bounds; used to avoid cycles.

Julia source: src/subtype.c:4558-4581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int _reachable_var(jl_value_t *x, jl_tvar_t *y, jl_stenv_t *e, jl_typeenv_t *log) JL_NOTSAFEPOINT
{
    if (in_union(x, (jl_value_t*)y))
        return 1;
    if (jl_is_uniontype(x) || jl_is_intersecttype(x))
        return _reachable_var(((jl_uniontype_t *)x)->a, y, e, log) ||
               _reachable_var(((jl_uniontype_t *)x)->b, y, e, log);
    if (!jl_is_typevar(x))
        return 0;
    jl_typeenv_t *t = log;
    while (t != NULL) {
        if (x == (jl_value_t *)t->var)
            return 0;
        t = t->prev;
    }
    int innervar = 0;
    jl_varbinding_t *xv = lookup_binding(e, (jl_tvar_t*)x, &innervar);
    if (xv == NULL && !innervar)
        return 0;
    jl_value_t *lb = xv == NULL ? ((jl_tvar_t*)x)->lb : xv->lb;
    jl_value_t *ub = xv == NULL ? ((jl_tvar_t*)x)->ub : xv->ub;
    jl_typeenv_t newlog = { (jl_tvar_t*)x, NULL, log };
    return _reachable_var(ub, y, e, &newlog) || _reachable_var(lb, y, e, &newlog);
}
```
-/
def reachableVar_ (n : Nat) (x y : Val) (log : List Nat) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let x ← resolveVal n x
    let y ← resolveVal n y
    if ← inUnion n x y then
      return true
    match x with
    | .union a b | .intersect a b =>
      if ← reachableVar_ n a y log then
        return true
      return ← reachableVar_ n b y log
    | _ => pure ()
    let .typevar xid _ xlb xub := x | return false
    if log.contains xid then
      return false
    let (xv, innervar) ← lookupBinding x
    if xv.isNone && !innervar then
      return false
    let (lb, ub) ← match xv with
      | none => pure (xlb, xub)
      | some i => do
        let b ← getBinding i
        pure (b.lb, b.ub)
    let newlog := xid :: log
    if ← reachableVar_ n ub y newlog then
      return true
    reachableVar_ n lb y newlog

/-- `reachable_var`

Julia source: src/subtype.c:4583-4586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int reachable_var(jl_value_t *x, jl_tvar_t *y, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    return _reachable_var(x, y, e, NULL);
}
```
-/
def reachableVar (n : Nat) (x y : Val) : STM Bool :=
  reachableVar_ n x y []

/-- `set_bound`

Julia source: src/subtype.c:4506-4511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void set_bound(jl_value_t **bound, jl_value_t *val, jl_tvar_t *v, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    if (reachable_var(val, v, e))
        return;
    *bound = val;
}
```
-/
def setBoundLb (n : Nat) (idx : Nat) (val v : Val) : STM Unit := do
  if ← reachableVar n val v then
    return
  changeBinding idx fun b => { b with lb := val }

def setBoundUb (n : Nat) (idx : Nat) (val v : Val) : STM Unit := do
  if ← reachableVar n val v then
    return
  changeBinding idx fun b => { b with ub := val }

/-- `check_unsat_bound`: check whether setting `v == t` implies `v == SomeType{v}`, which is unsatisfiable.

Julia source: src/subtype.c:4589-4601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int check_unsat_bound(jl_value_t *t, jl_tvar_t *v, jl_stenv_t *e) JL_NOTSAFEPOINT
{
    if (var_occurs_inside(t, v, 0, 0))
        return 1;
    jl_varbinding_t *btemp = e->vars;
    while (btemp != NULL) {
        if (btemp->lb == (jl_value_t*)v && btemp->ub == (jl_value_t*)v &&
            var_occurs_inside(t, btemp->var, 0, 0))
            return 1;
        btemp = btemp->prev;
    }
    return 0;
}
```
-/
def checkUnsatBound (n : Nat) (t v : Val) : STM Bool := do
  if ← varOccursInside n t v false false then
    return true
  let vars := (← get).vars
  for i in (List.range vars.size).reverse do
    let btemp := vars[i]!
    if btemp.lb == v && btemp.ub == v then
      if ← varOccursInside n t btemp.var false false then
        return true
  return false

/-- `always_occurs_cov`

Julia source: src/subtype.c:5325-5356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int always_occurs_cov(jl_value_t *v, jl_tvar_t *var, jl_param_pos_t param) JL_NOTSAFEPOINT
{
    if (param == PARAM_INVARIANT) {
        return 0;
    }
    else if (v == (jl_value_t*)var) {
        return param == PARAM_COVARIANT;
    }
    else if (jl_is_uniontype(v)) {
        return always_occurs_cov(((jl_uniontype_t*)v)->a, var, param) &&
               always_occurs_cov(((jl_uniontype_t*)v)->b, var, param);
    }
    else if (jl_is_unionall(v)) {
        jl_unionall_t *ua = (jl_unionall_t*)v;
        return ua->var != var && always_occurs_cov(ua->body, var, param);
    }
    else if (jl_is_vararg(v)) {
        jl_vararg_t *vm = (jl_vararg_t*)v;
        return vm->T && always_occurs_cov(vm->T, var, param);
    }
    else if (jl_is_some_Type(v)) {
        return always_occurs_cov(jl_some_Type_T(v), var, PARAM_INVARIANT);
    }
    else if (jl_is_datatype(v)) {
        jl_param_pos_t nparam = jl_is_tuple_type(v) ? PARAM_COVARIANT : param;
        for (size_t i = 0; i < jl_nparams(v); i++) {
            if (always_occurs_cov(jl_tparam(v, i), var, nparam))
                return 1;
        }
    }
    return 0;
}
```
-/
def alwaysOccursCov (n : Nat) (v var : Val) (param : ParamPos) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if param == .invariant then
      return false
    else if v == var then
      return param == .covariant
    else if let .union a b := v then
      if !(← alwaysOccursCov n a var param) then
        return false
      alwaysOccursCov n b var param
    else if let .unionall id _ _ _ body := v then
      if some id == var.tvId then
        return false
      alwaysOccursCov n body var param
    else if let .vararg (some t) _ := v then
      alwaysOccursCov n t var param
    else if v.isSomeType then
      alwaysOccursCov n v.someTypeT var .invariant
    else if let .datatype _ ps := v then
      let nparam : ParamPos := if v.isTupleType then .covariant else param
      for p in ps do
        if ← alwaysOccursCov n p var nparam then
          return true
      return false
    else
      return false

/-- `never_occurs_in_inside_ub`

Julia source: src/subtype.c:5358-5387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int never_occurs_in_inside_ub(jl_value_t *v, jl_tvar_t *var) JL_NOTSAFEPOINT
{
    if (jl_is_uniontype(v)) {
        return never_occurs_in_inside_ub(((jl_uniontype_t*)v)->a, var) &&
               never_occurs_in_inside_ub(((jl_uniontype_t*)v)->b, var);
    }
    else if (jl_is_unionall(v)) {
        jl_unionall_t *ua = (jl_unionall_t*)v;
        if (ua->var == var) return 1;
        return !jl_has_typevar((jl_value_t *)(ua->var->ub), var) && never_occurs_in_inside_ub(ua->body, var);
    }
    else if (jl_is_vararg(v)) {
        jl_vararg_t *vm = (jl_vararg_t*)v;
        return (vm->T == NULL || never_occurs_in_inside_ub(vm->T, var)) &&
               (vm->N == NULL || never_occurs_in_inside_ub(vm->N, var));
    }
    else if (jl_is_some_Type(v)) {
        return never_occurs_in_inside_ub(jl_some_Type_T(v), var);
    }
    else if (jl_is_datatype(v)) {
        for (size_t i = 0; i < jl_nparams(v); i++) {
            if (!never_occurs_in_inside_ub(jl_tparam(v, i), var))
                return 0;
        }
        return 1;
    }
    // conservative for internal nodes (TypeEq, TypeApp, Intersect); plain
    // values contain no typevars
    return jl_is_typevar(v) || !jl_has_typevar(v, var);
}
```
-/
def neverOccursInInsideUb (n : Nat) (v var : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let .union a b := v then
      if !(← neverOccursInInsideUb n a var) then
        return false
      neverOccursInInsideUb n b var
    else if let .unionall id _ _ ub body := v then
      if some id == var.tvId then
        return true
      if ub.hasTypevar var then
        return false
      neverOccursInInsideUb n body var
    else if let .vararg t? n? := v then
      let okt ← match t? with | some t => neverOccursInInsideUb n t var | none => pure true
      if !okt then
        return false
      match n? with | some nv => neverOccursInInsideUb n nv var | none => pure true
    else if v.isSomeType then
      neverOccursInInsideUb n v.someTypeT var
    else if let .datatype _ ps := v then
      for p in ps do
        if !(← neverOccursInInsideUb n p var) then
          return false
      return true
    else
      return v.isTypevar || !v.hasTypevar var

/-- `has_typevar_via_env`

Julia source: src/subtype.c:5948-5963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_typevar_via_env(jl_value_t *x, jl_tvar_t *t, jl_stenv_t *e)
{
    if (e->Loffset == 0) {
        jl_varbinding_t *temp = e->vars;
        while (temp != NULL) {
            if (temp->var == t)
                break;
            if (temp->lb == temp->ub &&
                temp->lb == (jl_value_t *)t &&
                jl_has_typevar(x, temp->var))
                return 1;
            temp = temp->prev;
        }
    }
    return jl_has_typevar(x, t);
}
```
-/
def hasTypevarViaEnv (x t : Val) : STM Bool := do
  if (← get).Loffset == 0 then
    let vars := (← get).vars
    for i in (List.range vars.size).reverse do
      let temp := vars[i]!
      if temp.var.tvId == t.tvId then
        break
      if temp.lb == temp.ub && temp.lb == t && x.hasTypevar temp.var then
        return true
  return x.hasTypevar t

/-- `var_always_occurs_as_parameter`: check if a type variable always occurs as a parameter in a datatype.

Julia source: src/subtype.c:5966-5992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int var_always_occurs_as_parameter(jl_value_t *t, jl_tvar_t *var, int param) JL_NOTSAFEPOINT
{
    if (t == (jl_value_t*)var)
        return param;
    else if (jl_is_uniontype(t)) {
        return var_always_occurs_as_parameter(((jl_uniontype_t*)t)->a, var, 0) &&
               var_always_occurs_as_parameter(((jl_uniontype_t*)t)->b, var, 0);
    }
    else if (jl_is_unionall(t)) {
        if (((jl_unionall_t*)t)->var == var)
            return 0;
        return var_always_occurs_as_parameter(((jl_unionall_t*)t)->body, var, param);
    }
    else if (jl_is_vararg(t)) {
        jl_vararg_t *vm = (jl_vararg_t*)t;
        return (vm->T != NULL && var_always_occurs_as_parameter(vm->T, var, param)) ||
               (vm->N != NULL && var_always_occurs_as_parameter(vm->N, var, param)) ;
    }
    else if (jl_is_datatype(t)) {
        for (size_t i = 0; i < jl_nparams(t); i++) {
            if (var_always_occurs_as_parameter(jl_tparam(t, i), var, 1))
                return 1;
        }
        return 0;
    }
    return 0;
}
```
-/
def varAlwaysOccursAsParameter (n : Nat) (t var : Val) (param : Bool) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if t == var then
      return param
    else if let .union a b := t then
      if !(← varAlwaysOccursAsParameter n a var false) then
        return false
      varAlwaysOccursAsParameter n b var false
    else if let .unionall id _ _ _ body := t then
      if some id == var.tvId then
        return false
      varAlwaysOccursAsParameter n body var param
    else if let .vararg t? n? := t then
      let okt ← match t? with | some tv => varAlwaysOccursAsParameter n tv var param | none => pure false
      if okt then
        return true
      match n? with | some nv => varAlwaysOccursAsParameter n nv var param | none => pure false
    else if let .datatype _ ps := t then
      for p in ps do
        if ← varAlwaysOccursAsParameter n p var true then
          return true
      return false
    else
      return false

/-- One entry of `allvars` (`jl_ivarbinding_t`, `src/subtype.c:153-163`) in `finish_unionall`. -/
structure IVarEntry where
  var : Val
  lb : Val
  ub : Val
  /-- `none` if `root` is the popped `vb`; `some idx` if `root` is `e.vars[idx]`. -/
  rootIdx : Option Nat
  rootDepth0 : Nat
  rootVar : Val
  deriving Repr, Inhabited

/-- `has_typevar_via_flatten_env`

Julia source: src/subtype.c:4847-4889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int has_typevar_via_flatten_env(jl_value_t *x, jl_tvar_t *t, jl_ivarbinding_t *allvars, int8_t *checked) JL_NOTSAFEPOINT
{
    if (jl_is_unionall(x)) {
        jl_tvar_t *var = ((jl_unionall_t *)x)->var;
        if (has_typevar_via_flatten_env(var->lb, t, allvars, checked) ||
            has_typevar_via_flatten_env(var->ub, t, allvars, checked))
            return 1;
        return has_typevar_via_flatten_env(((jl_unionall_t *)x)->body, t, allvars, checked);
    }
    else if (jl_is_uniontype(x)) {
        return has_typevar_via_flatten_env(((jl_uniontype_t *)x)->a, t, allvars, checked) ||
            has_typevar_via_flatten_env(((jl_uniontype_t *)x)->b, t, allvars, checked);
    }
    else if (jl_is_vararg(x)) {
        jl_vararg_t *v = (jl_vararg_t *)x;
        return (v->T && has_typevar_via_flatten_env(v->T, t, allvars, checked)) ||
            (v->N && has_typevar_via_flatten_env(v->N, t, allvars, checked));
    }
    else if (jl_is_datatype(x)) {
        for (size_t i = 0; i < jl_nparams(x); i++) {
            if (has_typevar_via_flatten_env(jl_tparam(x, i), t, allvars, checked))
                return 1;
        }
        return 0;
    }
    else if (jl_is_typevar(x)) {
        if (t == (jl_tvar_t *)x)
            return 1;
        size_t ind = 0;
        jl_ivarbinding_t *itemp = allvars;
        while (itemp && *itemp->var != (jl_tvar_t *)x)
        {
            ind++;
            itemp = itemp->next;
        }
        if (itemp == NULL || checked[ind])
            return 0;
        checked[ind] = 1;
        return has_typevar_via_flatten_env(*itemp->lb, t, allvars, checked) ||
            has_typevar_via_flatten_env(*itemp->ub, t, allvars, checked);
    }
    return 0;
}
```
-/
def hasTypevarViaFlattenEnv (n : Nat) (x t : Val) (allvars : Array IVarEntry)
    (checked : Array Bool) : CM (Bool × Array Bool) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match x with
    | .unionall _ _ lb ub body =>
      let (ok1, c1) ← hasTypevarViaFlattenEnv n lb t allvars checked
      if ok1 then return (true, c1)
      let (ok2, c2) ← hasTypevarViaFlattenEnv n ub t allvars c1
      if ok2 then return (true, c2)
      hasTypevarViaFlattenEnv n body t allvars c2
    | .union a b =>
      let (ok1, c1) ← hasTypevarViaFlattenEnv n a t allvars checked
      if ok1 then return (true, c1)
      hasTypevarViaFlattenEnv n b t allvars c1
    | .vararg t? n? =>
      let (ok1, c1) ← match t? with
        | some tv => hasTypevarViaFlattenEnv n tv t allvars checked
        | none => pure (false, checked)
      if ok1 then return (true, c1)
      match n? with
      | some nv => hasTypevarViaFlattenEnv n nv t allvars c1
      | none => pure (false, c1)
    | .datatype _ ps =>
      let mut checked := checked
      for p in ps do
        let (ok, c') ← hasTypevarViaFlattenEnv n p t allvars checked
        checked := c'
        if ok then return (true, checked)
      return (false, checked)
    | .typevar .. =>
      if t.tvId == x.tvId then
        return (true, checked)
      let mut ind : Nat := 0
      let mut found := false
      for entry in allvars do
        if entry.var.tvId == x.tvId then
          found := true
          break
        ind := ind + 1
      if !found || ind ≥ checked.size || checked[ind]! then
        return (false, checked)
      let checked := checked.set! ind true
      let entry := allvars[ind]!
      let (ok1, c1) ← hasTypevarViaFlattenEnv n entry.lb t allvars checked
      if ok1 then return (true, c1)
      hasTypevarViaFlattenEnv n entry.ub t allvars c1
    | _ =>
      return (false, checked)


/-- `jl_outer_unionall_vars`

Julia source: src/subtype.c:6505-6517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_svec_t *jl_outer_unionall_vars(jl_value_t *u)
{
    int ntvars = jl_subtype_env_size((jl_value_t*)u);
    jl_svec_t *vec = jl_alloc_svec_uninit(ntvars);
    jl_unionall_t *ua = (jl_unionall_t*)u;
    int i;
    for (i = 0; i < ntvars; i++) {
        assert(jl_is_unionall(ua));
        jl_gc_write_fresh(vec, jl_svec_data(vec)[i], jl_value_t, (jl_value_t*)ua->var);
        ua = (jl_unionall_t*)ua->body;
    }
    return vec;
}
```
-/
def jlOuterUnionallVars (n : Nat) (u : Val) : CM (List Val) := do
  let ntvars ← jlSubtypeEnvSize n u
  let mut cur := u
  let mut out : List Val := []
  for _ in [0:ntvars] do
    out := out ++ [cur.uaVar]
    cur := cur.uaBody
  return out

/-- `might_intersect_concrete`

Julia source: src/subtype.c:6598-6625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int might_intersect_concrete(jl_value_t *a) JL_NOTSAFEPOINT
{
    if (jl_is_unionall(a))
        a = jl_unwrap_unionall(a);
    if (jl_is_typevar(a))
        return 1; // (maybe)
    if (jl_is_uniontype(a))
        return might_intersect_concrete(((jl_uniontype_t*)a)->a) ||
               might_intersect_concrete(((jl_uniontype_t*)a)->b);
    if (jl_is_vararg(a))
        return might_intersect_concrete(jl_unwrap_vararg(a));
    if (jl_is_some_Type(a))
        return 1;
    if (jl_is_datatype(a)) {
        int tpl = jl_is_tuple_type(a);
        int i, n = jl_nparams(a);
        for (i = 0; i < n; i++) {
            jl_value_t *p = jl_tparam(a, i);
            if (jl_is_typevar(p))
                return 1;
            if (tpl && p == jl_bottom_type)
                return 1;
            if (tpl && might_intersect_concrete(p))
                return 1;
        }
    }
    return 0;
}
```
-/
def mightIntersectConcrete (n : Nat) (a : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let a := if a.isUnionall then a.unwrapUnionall else a
    if a.isTypevar then
      return true
    if let .union ua ub := a then
      if ← mightIntersectConcrete n ua then
        return true
      return ← mightIntersectConcrete n ub
    if a.isVararg then
      return ← mightIntersectConcrete n a.unwrapVararg
    if a.isSomeType then
      return true
    if let .datatype _ ps := a then
      let tpl := a.isTupleType
      for p in ps do
        if p.isTypevar then
          return true
        if tpl && p == .bottom then
          return true
        if tpl then
          if ← mightIntersectConcrete n p then
            return true
    return false

mutual
/-- `obviously_unequal`.

Julia source: src/subtype.c:671-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int obviously_unequal(jl_value_t *a, jl_value_t *b) JL_NOTSAFEPOINT
{
    if (a == b)
        return 0;
    a = normalize_typeofbottom_typealias(a);
    b = normalize_typeofbottom_typealias(b);
    if (a == b)
        return 0;
    if (jl_is_unionall(a))
        a = jl_unwrap_unionall(a);
    if (jl_is_unionall(b))
        b = jl_unwrap_unionall(b);
    if (jl_is_datatype(a)) {
        if (b == jl_bottom_type)
            return 1;
        if (jl_is_datatype(b)) {
            jl_datatype_t *ad = (jl_datatype_t*)a;
            jl_datatype_t *bd = (jl_datatype_t*)b;
            if (a == (jl_value_t*)jl_typeofbottom_type && jl_is_typeeq(b))
                return obviously_unequal(jl_bottom_type, jl_tparam(bd, 0));
            if (jl_is_typeeq(a) && b == (jl_value_t*)jl_typeofbottom_type)
                return obviously_unequal(jl_tparam(ad, 0), jl_bottom_type);
            if (ad->name != bd->name)
                return 1;
            int istuple = (ad->name == jl_tuple_typename);
            if (jl_type_equality_is_identity(a, b))
                return 1;
            size_t i, np;
            if (istuple) {
                size_t na = jl_nparams(ad), nb = jl_nparams(bd);
                if (jl_is_va_tuple(ad)) {
                    na -= 1;
                    if (jl_is_va_tuple(bd))
                        nb -= 1;
                }
                else if (jl_is_va_tuple(bd)) {
                    nb -= 1;
                }
                else if (na != nb) {
                    return 1;
                }
                np = na < nb ? na : nb;
            }
            else {
                np = jl_nparams(ad);
                if (np != jl_nparams(bd))
                    return 1;
            }
            for (i = 0; i < np; i++) {
                if (obviously_unequal(jl_tparam(ad, i), jl_tparam(bd, i)))
                    return 1;
            }
        }
    }
    else if (a == jl_bottom_type && jl_is_datatype(b)) {
        return 1;
    }
    if (jl_is_typeegal(a) && jl_is_typeegal(b))
        return obviously_unequal(jl_typeegal_T(a), jl_typeegal_T(b));
    if (jl_is_typevar(a) && jl_is_typevar(b) && obviously_unequal(((jl_tvar_t*)a)->ub, ((jl_tvar_t*)b)->ub))
        return 1;
    if (jl_is_long(a)) {
        if (jl_is_long(b) && jl_unbox_long(a) != jl_unbox_long(b))
            return 1;
    }
    else if (jl_is_long(b)) {
        return 1;
    }
    if ((jl_is_symbol(a) || jl_is_symbol(b)) && a != b)
        return 1;
    return 0;
}
```
-/
def obviouslyUnequal (n : Nat) (T : Types) (a b : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == b then return false
    let a ← normalizeTypeofbottomTypealias n a
    let b ← normalizeTypeofbottomTypealias n b
    if a == b then return false
    let a := a.unwrapUnionall
    let b := b.unwrapUnionall
    if a.isDatatype then
      if b == .bottom then return true
      if b.isDatatype then
        if a.name? != b.name? then return true
        if ← typeEqualityIsIdentity n T a b then return true
        let ap := a.params
        let bp := b.params
        if a.isTupleType && !a.isVaTuple && !b.isVaTuple && ap.length != bp.length then return true
        if !a.isTupleType && ap.length != bp.length then return true
        let np := if a.isTupleType then
          min (ap.length - (if a.isVaTuple then 1 else 0)) (bp.length - (if b.isVaTuple then 1 else 0))
          else ap.length
        for i in [0:np] do
          if ← obviouslyUnequal n T ap[i]! bp[i]! then return true
    else if a == .bottom && b.isDatatype then return true
    if a.isTypeegal && b.isTypeegal then
      return ← obviouslyUnequal n T a.someTypeT b.someTypeT
    if a.isTypevar && b.isTypevar then
      if ← obviouslyUnequal n T a.tvUb b.tvUb then return true
    if let .long x := a then
      if let .long y := b then if x != y then return true
    else if b.isLong then return true
    if (a.isSymbol || b.isSymbol) && a != b then return true
    return false
termination_by structural n

/-- `datatype_may_contain_types`.

Julia source: src/subtype.c:786-799 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int datatype_may_contain_types(jl_datatype_t *d) JL_NOTSAFEPOINT
{
    if (d == jl_any_type)
        return 1;
    while (d != jl_any_type) {
        if (d == jl_anytype_type)
            return 1;
        // raw read: a deferred (unset) supertype conservatively proves nothing
        d = d->super;
        if (d == NULL)
            return 1;
    }
    return 0;
}
```
-/
def datatypeMayContainTypes (n : Nat) (T : Types) (d : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if d == anyType then return true
    if d == anytypeType then return true
    let sup ← superOf n T (subOps n T) d
    if sup == anyType then return false
    datatypeMayContainTypes n T sup
termination_by structural n

/-- `obviously_disjoint`.

Julia source: src/subtype.c:801-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int obviously_disjoint(jl_value_t *a, jl_value_t *b, int specificity) JL_NOTSAFEPOINT
{
    if (a == b || a == (jl_value_t*)jl_any_type || b == (jl_value_t*)jl_any_type)
        return 0;
    if (specificity && a == (jl_value_t*)jl_typeofbottom_type)
        return 0;
    if (jl_is_concrete_type(a) && jl_is_concrete_type(b) && jl_type_equality_is_identity(a, b))
        return 1;
    if (jl_is_unionall(a)) a = jl_unwrap_unionall(a);
    if (jl_is_unionall(b)) b = jl_unwrap_unionall(b);
    if (jl_is_uniontype(a))
        return obviously_disjoint(((jl_uniontype_t *)a)->a, b, specificity) &&
               obviously_disjoint(((jl_uniontype_t *)a)->b, b, specificity);
    if (jl_is_uniontype(b))
        return obviously_disjoint(a, ((jl_uniontype_t *)b)->a, specificity) &&
               obviously_disjoint(a, ((jl_uniontype_t *)b)->b, specificity);
    if (!specificity && (jl_is_some_Type(a) || jl_is_some_Type(b))) {
        if (jl_is_some_Type(a) && jl_is_some_Type(b)) {
            // the members are the types `==` to each parameter; a concrete type is never
            // `==` to a type it is disjoint from
            jl_value_t *ta = jl_some_Type_T(a), *tb = jl_some_Type_T(b);
            if (jl_has_free_typevars(ta) || jl_has_free_typevars(tb))
                return 0;
            return (jl_is_concrete_type(ta) || jl_is_concrete_type(tb)) && obviously_disjoint(ta, tb, 0);
        }
        // the members are type objects, which only a supertype of some kind can hold
        jl_value_t *d = jl_is_some_Type(a) ? b : a;
        return jl_is_datatype(d) && !datatype_may_contain_types((jl_datatype_t*)d);
    }
    if (jl_is_datatype(a) && jl_is_datatype(b)) {
        jl_datatype_t *ad = (jl_datatype_t*)a, *bd = (jl_datatype_t*)b;
        if (ad->name != bd->name) {
            jl_datatype_t *temp = ad;
            while (temp != jl_any_type && temp->name != bd->name) {
                // raw read: this heuristic must not reach a safepoint, so a
                // deferred (unset) supertype conservatively proves nothing
                temp = temp->super;
                if (temp == NULL)
                    return 0;
            }
            if (temp == jl_any_type) {
                temp = bd;
                while (temp != jl_any_type && temp->name != ad->name) {
                    temp = temp->super;
                    if (temp == NULL)
                        return 0;
                }
                if (temp == jl_any_type)
                    return 1;
                bd = temp;
            }
            else {
                ad = temp;
            }
            if (specificity) {
                // account for declared subtypes taking priority (issue #21710)
                return 0;
            }
        }
        int istuple = (ad->name == jl_tuple_typename);
        size_t np;
        if (istuple) {
            size_t na = jl_nparams(ad), nb = jl_nparams(bd);
            if (jl_is_va_tuple(ad)) {
                na -= 1;
                if (jl_is_va_tuple(bd))
                    nb -= 1;
            }
            else if (jl_is_va_tuple(bd)) {
                nb -= 1;
            }
            else if (!specificity && na != nb) {
                // note: some disjoint types (e.g. tuples of different lengths) can be more specific
                return 1;
            }
            np = na < nb ? na : nb;
        }
        else {
            np = jl_nparams(ad);
        }
        size_t i;
        for (i = 0; i < np; i++) {
            jl_value_t *ai = jl_tparam(ad, i);
            jl_value_t *bi = jl_tparam(bd, i);
            if (jl_is_typevar(ai) || jl_is_typevar(bi))
                continue; // it's possible that Union{} is in this intersection
            if (jl_is_type(ai)) {
                if (jl_is_type(bi)) {
                    if (istuple && (ai == jl_bottom_type || bi == jl_bottom_type))
                        ; // TODO: this can return 1 if and when Tuple{Union{}} === Union{}
                    else if (obviously_disjoint(ai, bi, specificity))
                        return 1;
                }
                else if (ai != (jl_value_t*)jl_any_type) {
                    return 1;
                }
            }
            else if (jl_is_type(bi)) {
                if (bi != (jl_value_t*)jl_any_type)
                    return 1;
            }
            else if (!jl_egal(ai, bi)) {
                return 1;
            }
        }
    }
    else if (a == jl_bottom_type || b == jl_bottom_type) {
        return 1;
    }
    return 0;
}
```
-/
def obviouslyDisjoint (n : Nat) (T : Types) (a b : Val) (specificity : Bool) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == b || a == anyType || b == anyType then return false
    if specificity && a == typeofbottomType then return false
    if ← isConcreteType T a then
      if ← isConcreteType T b then
        if ← typeEqualityIsIdentity n T a b then return true
    let a := a.unwrapUnionall
    let b := b.unwrapUnionall
    if let .union a1 a2 := a then
      if !(← obviouslyDisjoint n T a1 b specificity) then return false
      return ← obviouslyDisjoint n T a2 b specificity
    if let .union b1 b2 := b then
      if !(← obviouslyDisjoint n T a b1 specificity) then return false
      return ← obviouslyDisjoint n T a b2 specificity
    if !specificity && (a.isSomeType || b.isSomeType) then
      if a.isSomeType && b.isSomeType then
        let ta := a.someTypeT
        let tb := b.someTypeT
        if ta.hasFreeTypevars || tb.hasFreeTypevars then return false
        let ca ← isConcreteType T ta
        let cb ← if ca then pure false else isConcreteType T tb
        if !(ca || cb) then return false
        return ← obviouslyDisjoint n T ta tb false
      let d := if a.isSomeType then b else a
      if !d.isDatatype then return false
      return !(← datatypeMayContainTypes n T d)
    if a.isDatatype && b.isDatatype then
      let mut ad := a
      let mut bd := b
      if ad.name? != bd.name? then
        let mut temp := ad
        let mut finished := false
        for _ in [0:n] do
          if temp == anyType || temp.name? == bd.name? then finished := true; break
          temp ← superOf n T (subOps n T) temp
        if !finished then outOfBudget
        if temp == anyType then
          temp := bd
          finished := false
          for _ in [0:n] do
            if temp == anyType || temp.name? == ad.name? then finished := true; break
            temp ← superOf n T (subOps n T) temp
          if !finished then outOfBudget
          if temp == anyType then return true
          bd := temp
        else ad := temp
        if specificity then return false
      let istuple := ad.isTupleType
      if istuple && !ad.isVaTuple && !bd.isVaTuple && !specificity && ad.nparams != bd.nparams then return true
      let np := if istuple then
        min (ad.nparams - (if ad.isVaTuple then 1 else 0)) (bd.nparams - (if bd.isVaTuple then 1 else 0))
        else ad.nparams
      for i in [0:np] do
        let ai := ad.params[i]!
        let bi := bd.params[i]!
        if ai.isTypevar || bi.isTypevar then continue
        if ai.isType then
          if bi.isType then
            if !(istuple && (ai == .bottom || bi == .bottom)) then
              if ← obviouslyDisjoint n T ai bi specificity then return true
          else if ai != anyType then return true
        else if bi.isType then
          if bi != anyType then return true
        else if !(← egal n T ai bi) then return true
    else if a == .bottom || b == .bottom then return true
    return false
termination_by structural n

/-- `simple_join`.

Julia source: src/subtype.c:914-938 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *simple_join(jl_value_t *a, jl_value_t *b) JL_CANSAFEPOINT
{
    if (a == jl_bottom_type || b == (jl_value_t*)jl_any_type || obviously_egal(a, b))
        return b;
    if (b == jl_bottom_type || a == (jl_value_t*)jl_any_type)
        return a;
    if (!(jl_is_type(a) || jl_is_typevar(a)) || !(jl_is_type(b) || jl_is_typevar(b)))
        return (jl_value_t*)jl_any_type;
    // a kind absorbs a `TypeEgal{T}` with that tag (its sole member is `T`
    // itself) and `Type{Union{}}` (`== TypeofBottom`); it does not absorb other
    // `Type{T}`s, whose members straddle several kinds (#33136)
    if (jl_is_kind(a) && jl_is_typeegal(b) && jl_typeof(jl_typeegal_T(b)) == a)
        return a;
    if (jl_is_kind(b) && jl_is_typeegal(a) && jl_typeof(jl_typeegal_T(a)) == b)
        return b;
    if (a == (jl_value_t*)jl_typeofbottom_type && jl_is_typeeq(b) && jl_typeeq_T(b) == jl_bottom_type)
        return a;
    if (b == (jl_value_t*)jl_typeofbottom_type && jl_is_typeeq(a) && jl_typeeq_T(a) == jl_bottom_type)
        return b;
    if (jl_is_typevar(a) && obviously_egal(b, ((jl_tvar_t*)a)->lb))
        return a;
    if (jl_is_typevar(b) && obviously_egal(a, ((jl_tvar_t*)b)->lb))
        return b;
    return simple_union(a, b);
}
```
-/
def simpleJoin (n : Nat) (T : Types) (a b : Val) : CM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == .bottom || b == anyType then return b
    if ← obviouslyEgal n T a b then return b
    if b == .bottom || a == anyType then return a
    if !(a.isType || a.isTypevar) || !(b.isType || b.isTypevar) then return anyType
    if isKind a && b.isTypeegal && typeOf b.someTypeT == a then return a
    if isKind b && a.isTypeegal && typeOf a.someTypeT == b then return b
    if a == typeofbottomType && b.isTypeeq && b.someTypeT == .bottom then return a
    if b == typeofbottomType && a.isTypeeq && a.someTypeT == .bottom then return b
    if a.isTypevar then if ← obviouslyEgal n T b a.tvLb then return a
    if b.isTypevar then if ← obviouslyEgal n T a b.tvLb then return b
    simpleUnion n T (subOps n T) a b
termination_by structural n

/-- `simple_meet`.

Julia source: src/subtype.c:943-970 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *simple_meet(jl_value_t *a, jl_value_t *b, int overesi) JL_CANSAFEPOINT
{
    if (a == (jl_value_t*)jl_any_type || b == jl_bottom_type || obviously_egal(a,b))
        return b;
    if (b == (jl_value_t*)jl_any_type || a == jl_bottom_type)
        return a;
    if (overesi == 1 && (jl_is_intersecttype(a) || jl_is_intersecttype(b)))
        // one operand is already an internal `Intersect` meet node.
        // Represent the combined meet exactly by nesting.
        return jl_new_struct(jl_intersect_type, a, b);
    if (!(jl_is_type(a) || jl_is_typevar(a)) || !(jl_is_type(b) || jl_is_typevar(b)))
        return jl_bottom_type;
    // as in `simple_join`: a kind contains a `TypeEgal{T}` with that tag and
    // `Type{Union{}}` (`== TypeofBottom`), but not other `Type{T}`s (#33136)
    if (jl_is_kind(a) && jl_is_typeegal(b) && jl_typeof(jl_typeegal_T(b)) == a)
        return b;
    if (jl_is_kind(b) && jl_is_typeegal(a) && jl_typeof(jl_typeegal_T(a)) == b)
        return a;
    if (a == (jl_value_t*)jl_typeofbottom_type && jl_is_typeeq(b) && jl_typeeq_T(b) == jl_bottom_type)
        return b;
    if (b == (jl_value_t*)jl_typeofbottom_type && jl_is_typeeq(a) && jl_typeeq_T(a) == jl_bottom_type)
        return a;
    if (jl_is_typevar(a) && obviously_egal(b, ((jl_tvar_t*)a)->ub))
        return a;
    if (jl_is_typevar(b) && obviously_egal(a, ((jl_tvar_t*)b)->ub))
        return b;
    return simple_intersect(a, b, overesi);
}
```
-/
def simpleMeet (n : Nat) (T : Types) (a b : Val) (overesi : Nat) : CM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a == anyType || b == .bottom then return b
    if ← obviouslyEgal n T a b then return b
    if b == anyType || a == .bottom then return a
    if overesi == 1 && (a.isIntersect || b.isIntersect) then return .intersect a b
    if !(a.isType || a.isTypevar) || !(b.isType || b.isTypevar) then return .bottom
    if isKind a && b.isTypeegal && typeOf b.someTypeT == a then return b
    if isKind b && a.isTypeegal && typeOf a.someTypeT == b then return a
    if a == typeofbottomType && b.isTypeeq && b.someTypeT == .bottom then return b
    if b == typeofbottomType && a.isTypeeq && a.someTypeT == .bottom then return a
    if a.isTypevar then if ← obviouslyEgal n T b a.tvUb then return a
    if b.isTypevar then if ← obviouslyEgal n T a b.tvUb then return b
    simpleIntersect n T (subOps n T) a b overesi
termination_by structural n

/-- `widen_intersect`.

Julia source: src/subtype.c:979-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *widen_intersect(jl_value_t *t) JL_CANSAFEPOINT
{
    if (t == NULL || !jl_is_intersecttype(t))
        return t;
    jl_value_t *a = NULL, *b = NULL, *res = NULL;
    JL_GC_PUSH2(&a, &b);
    a = widen_intersect(((jl_intersecttype_t*)t)->a);
    b = widen_intersect(((jl_intersecttype_t*)t)->b);
    res = simple_meet(a, b, 2);
    JL_GC_POP();
    return res;
}
```
-/
def widenIntersect (n : Nat) (T : Types) (t : Val) : CM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    match t with
    | .intersect a b =>
      let a ← widenIntersect n T a
      let b ← widenIntersect n T b
      simpleMeet n T a b 2
    | _ => return t
termination_by structural n


/-- `typeeq_kind_le`.

Julia source: src/subtype.c:2744-2755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_kind_le(jl_datatype_t *k, jl_value_t *y) JL_NOTSAFEPOINT
{
    if (!jl_is_datatype(y))
        return 0;
    jl_datatype_t *yd = (jl_datatype_t*)y;
    while (k != jl_any_type) {
        if (k == yd)
            return 1;
        k = k->super;
    }
    return yd == jl_any_type;
}
```
-/
def typeeqKindLe (n : Nat) (T : Types) (k y : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if !y.isDatatype then return false
    if k == anyType then return y == anyType
    if k == y then return true
    let sup ← superOf n T (subOps n T) k
    typeeqKindLe n T sup y
termination_by structural n

/-- `typeeq_mask_le`.

Julia source: src/subtype.c:2798-2807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_mask_le(int mask, jl_value_t *y) JL_NOTSAFEPOINT
{
    int i;
    for (i = 0; i < 6; i++) {
        if ((mask & typeeq_kind_bits[i]) &&
            !typeeq_kind_le(typeeq_kind_datatype(typeeq_kind_bits[i]), y))
            return 0;
    }
    return 1;
}
```
-/
def typeeqMaskLe (n : Nat) (T : Types) (mask : Nat) (y : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    for bit in [1, 2, 4, 8, 16, 32] do
      if mask &&& bit != 0 then
        let kind ← typeeqKindDatatype bit
        if !(← typeeqKindLe n T kind y) then return false
    return true
termination_by structural n

/-- `typeeq_unpin_tvar`.

Julia source: src/subtype.c:2782-2795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *typeeq_unpin_tvar(jl_value_t *tp0 JL_PROPAGATES_ROOT) JL_CANSAFEPOINT
{
    while (jl_is_typevar(tp0)) {
        jl_value_t *lb = ((jl_tvar_t*)tp0)->lb;
        jl_value_t *ub = ((jl_tvar_t*)tp0)->ub;
        if (lb != ub) {
            if (jl_has_free_typevars(lb) || jl_has_free_typevars(ub) ||
                !jl_types_equal(lb, ub))
                break;
        }
        tp0 = lb;
    }
    return tp0;
}
```
-/
def typeeqUnpinTvar (n : Nat) (T : Types) (tp : Val) : CM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if !tp.isTypevar then return tp
    let lb := tp.tvLb
    let ub := tp.tvUb
    if lb != ub then
      if lb.hasFreeTypevars || ub.hasFreeTypevars then return tp
      if !(← jlTypesEqual n T lb ub) then return tp
    typeeqUnpinTvar n T lb
termination_by structural n

/-- `typeeq_subtype_kind_cover`.

Julia source: src/subtype.c:2841-2863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_subtype_kind_cover(jl_value_t *tp0, jl_value_t *y) JL_CANSAFEPOINT
{
    int mask = typeeq_kind_mask(tp0);
    jl_value_t *kinds[6];
    size_t n = 0;
    int i;
    for (i = 0; i < 6; i++) {
        if (mask & typeeq_kind_bits[i])
            kinds[n++] = (jl_value_t*)typeeq_kind_datatype(typeeq_kind_bits[i]);
    }
    jl_value_t *closed[32];
    size_t nc = 0;
    typeeq_collect_closed_components(y, closed, &nc, sizeof(closed) / sizeof(closed[0]));
    if (nc == 0)
        return 0;
    jl_value_t *cover = NULL, *target = NULL;
    JL_GC_PUSH2(&cover, &target);
    cover = jl_type_union(kinds, n);
    target = jl_type_union(closed, nc);
    int ans = jl_subtype(cover, target);
    JL_GC_POP();
    return ans;
}
```
-/
def typeeqSubtypeKindCover (n : Nat) (T : Types) (tp y : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let mask ← typeeqKindMask n T tp
    let bits := [1, 2, 4, 8, 16, 32].filter fun bit => mask &&& bit != 0
    let kinds ← bits.mapM typeeqKindDatatype
    let closed ← typeeqCollectClosedComponents n y #[] 32
    if closed.isEmpty then return false
    let cover ← typeUnion n T (subOps n T) kinds
    let target ← typeUnion n T (subOps n T) closed.toList
    jlSubtype n T cover target
termination_by structural n

/-- `widen_Type_if_concrete`.

Julia source: src/subtype.c:1479-1504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *widen_Type_if_concrete(jl_value_t *t JL_PROPAGATES_ROOT, jl_stenv_t *e, typeeq_varctx_t *wenv, int existential) JL_NOTSAFEPOINT
{
    jl_value_t *w = widen_pinned_Type(t, e, wenv);
    if (w == NULL && jl_is_typeeq(t) && !jl_is_typevar(jl_typeeq_T(t))) {
        jl_value_t *tag = jl_typeof(jl_typeeq_T(t));
        if (existential || typeeq_mask_le(typeeq_kind_mask(jl_typeeq_T(t)), tag))
            w = tag;
    }
    if (w != NULL)
        return w;
    if (jl_is_uniontype(t)) {
        jl_value_t *a = widen_Type_if_concrete(((jl_uniontype_t*)t)->a, e, wenv, existential);
        jl_value_t *b = widen_Type_if_concrete(((jl_uniontype_t*)t)->b, e, wenv, existential);
        if (a == b)
            return a;
    }
    if (jl_is_unionall(t)) {
        // vars bound by binders we walk past are not dangling
        jl_unionall_t *u = (jl_unionall_t*)t;
        typeeq_varctx_t ctx = { u->var, 0, wenv };
        jl_value_t *body = widen_Type_if_concrete(u->body, e, &ctx, existential);
        if (body != u->body && !jl_has_typevar(body, u->var))
            return body;
    }
    return t;
}
```
-/
def widenTypeIfConcrete (n : Nat) (T : Types) (t : Val) (wenv : TypeeqVarctx) (existential : Bool) : STM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let mut w ← widenPinnedType n t wenv
    if w.isNone && t.isTypeeq && !t.someTypeT.isTypevar then
      let tag := typeOf t.someTypeT
      let ok ← if existential then pure true else do
        let mask ← typeeqKindMask n T t.someTypeT
        typeeqMaskLe n T mask tag
      if ok then w := some tag
    if let some widened := w then return widened
    if let .union a b := t then
      let a ← widenTypeIfConcrete n T a wenv existential
      let b ← widenTypeIfConcrete n T b wenv existential
      if a == b then return a
    if let .unionall id _ _ _ body := t then
      let b ← widenTypeIfConcrete n T body ((id, false) :: wenv) existential
      if b != body && !b.hasTypevar t.uaVar then return b
    return t
termination_by structural n

/-- `unalias_unionall`.

Julia source: src/subtype.c:1697-1725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_unionall_t *unalias_unionall(jl_unionall_t *u, jl_stenv_t *e) JL_CANSAFEPOINT
{
    jl_varbinding_t *btemp = e->vars;
    // if the var for this unionall (based on identity) already appears somewhere
    // in the environment, rename to get a fresh var.
    JL_GC_PUSH1(&u);
    while (btemp != NULL) {
        int aliased = btemp->var == u->var ||
            // outer var can only refer to inner var if bounds changed (mainly for subtyping path)
            (btemp->lb != btemp->var->lb && jl_has_typevar(btemp->lb, u->var)) ||
            (btemp->ub != btemp->var->ub && jl_has_typevar(btemp->ub, u->var));
        if (!aliased && btemp->innervars != NULL) {
            for (size_t i = 0; i < jl_array_len(btemp->innervars); i++) {
                jl_tvar_t *ivar = (jl_tvar_t*)jl_array_ptr_ref(btemp->innervars, i);
                if (ivar == u->var) {
                    aliased = 1;
                    break;
                }
            }
        }
        if (aliased) {
            u = jl_rename_unionall(u);
            break;
        }
        btemp = btemp->prev;
    }
    JL_GC_POP();
    return u;
}
```
-/
def unaliasUnionall (n : Nat) (T : Types) (u : Val) : STM Val := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let vars := (← get).vars
    for i in (List.range vars.size).reverse do
      let b := vars[i]!
      let aliased := b.var.tvId == u.uaVar.tvId ||
        (b.lb != b.var.tvLb && b.lb.hasTypevar u.uaVar) ||
        (b.ub != b.var.tvUb && b.ub.hasTypevar u.uaVar)
      if aliased then return ← renameUnionall n T (subOps n T) u
      if ← bindingHasInnervar b u.uaVar then return ← renameUnionall n T (subOps n T) u
    return u
termination_by structural n


/-- `typeeq_mask_meets`: does some kind in `mask` lie in `y`? (`Type{T} ∩ y` nonemptiness).

Julia source: src/subtype.c:2810-2819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int typeeq_mask_meets(int mask, jl_value_t *y) JL_NOTSAFEPOINT
{
    int i;
    for (i = 0; i < 6; i++) {
        if ((mask & typeeq_kind_bits[i]) &&
            typeeq_kind_le(typeeq_kind_datatype(typeeq_kind_bits[i]), y))
            return 1;
    }
    return 0;
}
```
-/
def typeeqMaskMeets (n : Nat) (T : Types) (mask : Nat) (y : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    for bit in [1, 2, 4, 8, 16, 32] do
      if (mask &&& bit) != 0 then
        let kind ← typeeqKindDatatype bit
        if ← typeeqKindLe n T kind y then
          return true
    return false
termination_by structural n

/-- `merge_env`

Julia source: src/subtype.c:6319-6403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int merge_env(jl_stenv_t *e, jl_savedenv_t *me, jl_savedenv_t *se, int count) JL_CANSAFEPOINT
{
    if (count == 0) {
        save_env(e, me, 1);
        return 1;
    }
    jl_value_t **merged = NULL;
    jl_value_t **saved = NULL;
    jl_svec_t *msv = NULL;
    int nroots = 0;
    assert(se->gcframe.nroots == me->gcframe.nroots);
    if (se->gcframe.nroots == JL_GC_ENCODE_PUSHARGS(1)) {
        jl_svec_t *sv = (jl_svec_t*)se->roots[0];
        assert(jl_is_svec(sv));
        saved = jl_svec_data(sv);
        nroots = jl_svec_len(sv);
        msv = (jl_svec_t*)me->roots[0];
        assert(jl_is_svec(msv));
        merged = jl_svec_data(msv);
        assert(nroots == jl_svec_len(msv));
    }
    else {
        saved = se->roots;
        merged = me->roots;
        nroots = JL_GC_DECODE_NROOTS(se->gcframe.nroots);
    }
    assert(nroots == current_env_length(e) * 3);
    assert(nroots % 3 == 0);
    int m = 0, n = 0;
    jl_varbinding_t *v = e->vars;
    while (v != NULL) {
        jl_value_t *b0, *b1, *b2;
        // merge `lb`
        b0 = saved[n];
        b1 = merged[n];
        JL_GC_PROMISE_ROOTED(b1); // clang-sagc doesn't know this came from our GC frame
        b2 = v->lb;
        JL_GC_PROMISE_ROOTED(b2); // clang-sagc doesn't know the fields of this are stack GC roots
        set_env_root(msv, &merged[n], (b1 == b0 || b2 == b0) ? b0 : simple_meet(b1, b2, 0));
        // merge `ub`
        b0 = saved[n+1];
        b1 = merged[n+1];
        JL_GC_PROMISE_ROOTED(b1); // clang-sagc doesn't know this came from our GC frame
        b2 = v->ub;
        JL_GC_PROMISE_ROOTED(b2); // clang-sagc doesn't know the fields of this are stack GC roots
        set_env_root(msv, &merged[n+1], (b1 == b0 || b2 == b0) ? b0 : simple_join(b1, b2));
        // merge `innervars`
        b1 = merged[n+2];
        JL_GC_PROMISE_ROOTED(b1); // clang-sagc doesn't know this came from our GC frame
        b2 = (jl_value_t*)v->innervars;
        JL_GC_PROMISE_ROOTED(b2); // clang-sagc doesn't know the fields of this are stack GC roots
        if (b2 && b1 != b2) {
            if (b1)
                jl_array_ptr_1d_append((jl_array_t*)b1, (jl_array_t*)b2);
            else
                set_env_root(msv, &merged[n+2], b2);
        }
        // merge occurs/occurs_inv/occurs_cov/cov_diag by max (never decrease)
        if (v->occurs > me->buf[m])
            me->buf[m] = v->occurs;
        if (v->occurs_inv > me->buf[m+1])
            me->buf[m+1] = v->occurs_inv;
        if (v->occurs_cov > me->buf[m+2])
            me->buf[m+2] = v->occurs_cov;
        if (v->cov_diag > me->buf[m+3])
            me->buf[m+3] = v->cov_diag;
        // merge max_offset by min
        if (!v->intersected && v->max_offset < me->buf[m+4])
            me->buf[m+4] = v->max_offset;
        // required lower-bound evidence must hold for every merged branch
        if (!v->lb_required)
            me->buf[m+6] = 0;
        // the merged binding's spelling is only as authoritative as its
        // weakest contributor
        if (v->lb_spell < me->buf[m+7])
            me->buf[m+7] = v->lb_spell;
        if (!v->pinned)
            me->buf[m+8] = 0;
        m = m + JL_SAVEDENV_BYTES_PER_VAR;
        n = n + 3;
        v = v->prev;
    }
    assert(n == nroots); (void)nroots;
    return count + 1;
}
```
-/
def mergeEnv (n : Nat) (T : Types) (me se : SavedEnv) (count : Nat) : STM (Nat × SavedEnv) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if count == 0 then
      let me' ← saveEnv
      return (1, me')
    let vars := (← get).vars
    let mut mergedVars := me.vars
    for i in (List.range vars.size).reverse do
      let s := se.vars[i]!
      let m := mergedVars[i]!
      let v := vars[i]!
      -- merge `lb`
      let b0 := s.lb
      let b1 := m.lb
      let b2 := v.lb
      let newLb ← if b1 == b0 || b2 == b0 then pure b0 else simpleMeet n T b1 b2 0
      -- merge `ub`
      let ub0 := s.ub
      let ub1 := m.ub
      let ub2 := v.ub
      let newUb ← if ub1 == ub0 || ub2 == ub0 then pure ub0 else simpleJoin n T ub1 ub2
      -- merge `innervars`
      let mut newInner := m.innervars
      if let some i2 := v.innervars then
        if m.innervars != some i2 then
          match m.innervars with
          | some i1 =>
            let arr1 ← innerVars m
            let arr2 ← innerVars v
            modify fun e => { e with innerArrays := e.innerArrays.set! i1 (arr1 ++ arr2) }
            newInner := some i1
          | none =>
            newInner := some i2
      let newMaxOffset :=
        if !v.intersected && v.maxOffset < m.maxOffset then v.maxOffset else m.maxOffset
      let m' : VarBinding := { m with
        lb := newLb
        ub := newUb
        innervars := newInner
        occurs := max v.occurs m.occurs
        occursInv := max v.occursInv m.occursInv
        occursCov := max v.occursCov m.occursCov
        covDiag := max v.covDiag m.covDiag
        maxOffset := newMaxOffset
        lbRequired := m.lbRequired && v.lbRequired
        lbSpell := min v.lbSpell m.lbSpell
        pinned := m.pinned && v.pinned
      }
      mergedVars := mergedVars.set! i m'
    return (count + 1, { me with vars := mergedVars })
termination_by structural n
  

/-- `omit_bad_union`

Julia source: src/subtype.c:4793-4844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *omit_bad_union(jl_value_t *u, jl_tvar_t *t) JL_CANSAFEPOINT
{
    if (!jl_has_typevar(u, t))
        return u; // return u if possible as many checks use `==`.
    jl_value_t *res = NULL;
    if (jl_is_unionall(u)) {
        jl_tvar_t *var = ((jl_unionall_t *)u)->var;
        jl_value_t *ub = var->ub, *body = ((jl_unionall_t *)u)->body;
        assert(var != t);
        JL_GC_PUSH3(&ub, &body, &var);
        body = omit_bad_union(body, t);
        if (!jl_has_typevar(body, var)) {
            res = body;
        }
        else if (jl_has_typevar(var->lb, t)) {
            res = jl_bottom_type;
        }
        else {
            ub = omit_bad_union(ub, t);
            if (ub == jl_bottom_type && var->lb != ub) {
                res = jl_bottom_type;
            }
            else if (obviously_egal(var->lb, ub)) {
                res = jl_substitute_var_nothrow(body, var, ub, 2);
                if (res == NULL)
                    res = jl_bottom_type;
            }
            else {
                if (ub != var->ub) {
                    var = jl_new_typevar(var->name, var->lb, ub);
                    body = jl_substitute_var(body, ((jl_unionall_t *)u)->var, (jl_value_t *)var);
                }
                res = jl_new_struct(jl_unionall_type, var, body);
            }
        }
        JL_GC_POP();
    }
    else if (jl_is_uniontype(u)) {
        jl_value_t *a = ((jl_uniontype_t *)u)->a;
        jl_value_t *b = ((jl_uniontype_t *)u)->b;
        JL_GC_PUSH2(&a, &b);
        a = omit_bad_union(a, t);
        b = omit_bad_union(b, t);
        res = simple_join(a, b);
        JL_GC_POP();
    }
    else {
        res = jl_bottom_type;
    }
    assert(res != NULL);
    return res;
}
```
-/
def omitBadUnion (n : Nat) (T : Types) (u t : Val) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if !u.hasTypevar t then
      return u
    if let .unionall uid nm lb ub body := u then
      let var := Val.typevar uid nm lb ub
      let body' ← omitBadUnion n T body t
      if !body'.hasTypevar var then
        return body'
      else if lb.hasTypevar t then
        return .bottom
      else
        let ub' ← omitBadUnion n T ub t
        if ub' == .bottom && lb != ub' then
          return .bottom
        else if ← obviouslyEgal n T lb ub' then
          let res? ← substituteVarNothrow n T (subOps n T) body' var ub' 2
          return res?.getD .bottom
        else
          let mut var' := var
          let mut body'' := body'
          if ub' != ub then
            var' ← newTypevar nm lb ub'
            body'' ← substituteVar n T (subOps n T) body' var var'
          let .typevar vid vnm vlb vub := var' | throw "unreachable"
          return .unionall vid vnm vlb vub body''
    else if let .union a b := u then
      let a' ← omitBadUnion n T a t
      let b' ← omitBadUnion n T b t
      simpleJoin n T a' b'
    else
      return .bottom
termination_by structural n

/-- `finish_unionall`

Julia source: src/subtype.c:4892-5240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *finish_unionall(jl_value_t *res JL_MAYBE_UNROOTED, jl_varbinding_t *vb, jl_unionall_t *u, jl_stenv_t *e) JL_CANSAFEPOINT
{
    jl_value_t *varval = NULL, *ilb = NULL, *iub = NULL, *nivar = NULL;
    jl_tvar_t *newvar = vb->var, *ivar = NULL;
    JL_GC_PUSH6(&res, &newvar, &ivar, &nivar, &ilb, &iub);
    // Note: `Intersect` is subtype accounting only and is widened away before
    // it leaves the subtype path (see `subtype_unionall`), so the intersection
    // result here never contains one.
    assert(!jl_is_intersecttype(vb->ub));
    // try to reduce var to a single value
    if (jl_is_long(vb->ub) && jl_is_typevar(vb->lb)) {
        varval = vb->ub;
    }
    else if (obviously_egal(vb->lb, vb->ub)) {
        // given x<:T<:x, substitute x for T
        varval = vb->ub;
    }
    // TODO: `vb.occurs_cov == 1`, we could also substitute Tuple{<:X} => Tuple{X},
    // but it may change some ambiguity errors so we don't need to do it yet.
    else if (cov_count(vb) && is_leaf_bound(vb->ub) && !jl_has_free_typevars(vb->ub)) {
        // replace T<:x with x in covariant position when possible
        varval = vb->ub;
    }

    if (vb->intvalued) {
        if ((varval && jl_is_long(varval)) ||
            (vb->lb == jl_bottom_type && vb->ub == (jl_value_t*)jl_any_type) ||
            (jl_is_typevar(vb->lb) && vb->ub == vb->lb)) {
            // int-valued typevar must either be an Int, or have Bottom-Any bounds,
            // or be set equal to another typevar.
        }
        else {
            JL_GC_POP();
            return jl_bottom_type;
        }
    }

    // TODO: this can prevent us from matching typevar identities later
    if (!varval && (vb->lb != vb->var->lb || vb->ub != vb->var->ub))
        newvar = jl_new_typevar(vb->var->name, vb->lb, vb->ub);

    // flatten all innervar into a (reversed) list
    size_t icount = 0;
    if (vb->innervars)
        icount += jl_array_nrows(vb->innervars);
    for (jl_varbinding_t *btemp = e->vars; btemp != NULL; btemp = btemp->prev) {
        if (btemp->innervars != NULL)
            icount += jl_array_nrows(btemp->innervars);
    }
    jl_svec_t *p = NULL;
    jl_value_t **iparams;
    jl_value_t **roots;
    JL_GC_PUSHARGS(roots, icount < 22 ? 3*icount : 1);
    if (icount < 22) {
        iparams = roots;
    }
    else {
        p = jl_alloc_svec(3*icount);
        roots[0] = (jl_value_t*)p;
        iparams = jl_svec_data(p);
    }
    jl_ivarbinding_t *allvars = NULL;
    size_t niparams = 0;
    if (vb->innervars) {
        for (size_t i = 0; i < jl_array_nrows(vb->innervars); i++) {
            jl_tvar_t *ivar = (jl_tvar_t *)jl_array_ptr_ref(vb->innervars, i);
            jl_ivarbinding_t *inew = (jl_ivarbinding_t *)alloca(sizeof(jl_ivarbinding_t));
            inew->var = (jl_tvar_t **)&iparams[niparams++]; *inew->var = ivar;
            inew->lb = &iparams[niparams++]; *inew->lb = ivar->lb;
            inew->ub = &iparams[niparams++]; *inew->ub = ivar->ub;
            inew->owner = (jl_value_t*)p;
            inew->root = vb;
            inew->next = allvars;
            allvars = inew;
        }
    }
    for (jl_varbinding_t *btemp = e->vars; btemp != NULL; btemp = btemp->prev) {
        jl_ivarbinding_t *inew = (jl_ivarbinding_t *)alloca(sizeof(jl_ivarbinding_t));
        inew->var = &btemp->var;
        inew->lb = &btemp->lb;
        inew->ub = &btemp->ub;
        inew->owner = NULL;
        inew->root = btemp;
        inew->next = allvars;
        allvars = inew;
        if (btemp->innervars) {
            for (size_t i = 0; i < jl_array_nrows(btemp->innervars); i++) {
                jl_tvar_t *ivar = (jl_tvar_t *)jl_array_ptr_ref(btemp->innervars, i);
                jl_ivarbinding_t *inew = (jl_ivarbinding_t *)alloca(sizeof(jl_ivarbinding_t));
                inew->var = (jl_tvar_t **)&iparams[niparams++]; *inew->var = ivar;
                inew->lb = &iparams[niparams++]; *inew->lb = ivar->lb;
                inew->ub = &iparams[niparams++]; *inew->ub = ivar->ub;
                inew->owner = (jl_value_t*)p;
                inew->root = btemp;
                inew->next = allvars;
                allvars = inew;
            }
        }
    }

    // remove/replace/rewrap free occurrences of this var in the environment
    int wrapped = 0;
    jl_ivarbinding_t *pwrap = NULL;
    int vcount = icount + current_env_length(e);
    int8_t *checked = (int8_t *)alloca(vcount);
    for (jl_ivarbinding_t *btemp = allvars, *pbtemp = NULL; btemp != NULL; btemp = btemp->next) {
        int bdepth0 = btemp->root->depth0;
        int innerflag = 0;
        ivar = *btemp->var;
        ilb = *btemp->lb;
        iub = *btemp->ub;
        if (jl_has_typevar(ilb, vb->var)) {
            assert(btemp->root->var == ivar || bdepth0 == vb->depth0);
            if (vb->lb == (jl_value_t*)ivar) {
                JL_GC_POP();
                JL_GC_POP();
                return jl_bottom_type;
            }
            if (varval) {
                JL_TRY {
                    set_ivar_slot(btemp, btemp->lb, jl_substitute_var(ilb, vb->var, varval));
                }
                JL_CATCH {
                    res = jl_bottom_type;
                }
            }
            else if (ilb == (jl_value_t*)vb->var) {
                set_ivar_slot(btemp, btemp->lb, vb->lb);
            }
            else {
                innerflag |= 1;
            }
        }
        if (jl_has_typevar(iub, vb->var)) {
            assert(btemp->root->var == ivar || bdepth0 == vb->depth0);
            if (vb->ub == (jl_value_t*)ivar) {
                set_ivar_slot(btemp, btemp->ub, omit_bad_union(iub, vb->var));
                if (*btemp->ub == jl_bottom_type && *btemp->ub != *btemp->lb) {
                    JL_GC_POP();
                    JL_GC_POP();
                    return jl_bottom_type;
                }
            }
            if (varval) {
                iub = jl_substitute_var_nothrow(iub, vb->var, varval, 2);
                if (iub == NULL)
                    res = jl_bottom_type;
                else
                    set_ivar_slot(btemp, btemp->ub, iub);
            }
            else if (iub == (jl_value_t*)vb->var) {
                // TODO: this loses some constraints, such as in this test, where we replace T4<:S3 (e.g. T4==S3 since T4 only appears covariantly once) with T4<:Any
                // a = Tuple{Float64,T3,T4} where T4 where T3
                // b = Tuple{S2,Tuple{S3},S3} where S2 where S3
                // Tuple{Float64, T3, T4} where {S3, T3<:Tuple{S3}, T4<:S3}
                set_ivar_slot(btemp, btemp->ub, vb->ub);
            }
            else {
                innerflag |= 2;
            }
        }
        if (innerflag) {
            memset(checked, 0, vcount);
            if (btemp->root == vb || bdepth0 != vb->depth0 ||
                has_typevar_via_flatten_env(vb->lb, ivar, allvars, checked) ||
                has_typevar_via_flatten_env(vb->ub, ivar, allvars, checked)) {
                if (innerflag & 1)
                    set_ivar_slot(btemp, btemp->lb, jl_new_struct(jl_unionall_type, vb->var, ilb));
                if (innerflag & 2)
                    set_ivar_slot(btemp, btemp->ub, jl_new_struct(jl_unionall_type, vb->var, iub));
            }
            else {
                assert(btemp->root != vb);
                // if our variable is T, and some outer variable has constraint S = Ref{T},
                // move the `where T` outside `where S` instead of putting it here. issue #21243.
                if (newvar != vb->var) {
                    if (innerflag & 1)
                        set_ivar_slot(btemp, btemp->lb, jl_substitute_var(ilb, vb->var, (jl_value_t*)newvar));
                    if (innerflag & 2)
                        set_ivar_slot(btemp, btemp->ub, jl_substitute_var(iub, vb->var, (jl_value_t*)newvar));
                }
                if (!wrapped)
                    pwrap = pbtemp;
                wrapped = 1;
            }
            assert((jl_value_t*)ivar != *btemp->lb);
            assert((jl_value_t*)ivar != *btemp->ub);
        }
        pbtemp = btemp;
    }

    // Insert the newvar into the (reversed) var list if needed.
    if (wrapped) {
        jl_ivarbinding_t *wrap = pwrap == NULL ? allvars : pwrap->next;
        jl_ivarbinding_t *inew = (jl_ivarbinding_t *)alloca(sizeof(jl_ivarbinding_t));
        inew->var = &newvar;
        inew->lb = &newvar->lb;
        inew->ub = &newvar->ub;
        inew->owner = (jl_value_t*)newvar;
        inew->root = wrap->root;
        inew->next = wrap;
        if (pwrap != NULL)
            pwrap->next = inew;
        else
            allvars = inew;
        vcount++;
    }

    // Re-sort the innervar inside the (reversed) var list.
    // `jl_has_typevar` is used as the partial-ordering predicate.
    // If this is slow, we could possibly switch to a simpler graph sort, such as Tarjan's SCC.
    if (icount > 0) {
        jl_ivarbinding_t *pib1 = NULL;
#ifndef NDEBUG
        size_t sort_count = 0;
#endif
        while (1) {
            jl_ivarbinding_t *ib1 = pib1 == NULL ? allvars : pib1->next;
            if (ib1 == NULL) break;
            assert((++sort_count) <= (vcount * (vcount + 1)) >> 1);
            int lbfree = jl_has_free_typevars(*ib1->lb);
            int ubfree = jl_has_free_typevars(*ib1->ub);
            if (lbfree || ubfree) {
                int changed = 0;
                jl_ivarbinding_t *pib2 = ib1, *ib2 = ib1->next;
                while (ib2 != NULL) {
                    int isinnervar = ib2->root->var != *ib2->var;
                    if (isinnervar && ib1->root->depth0 == ib2->root->depth0 &&
                        ((lbfree && jl_has_typevar(*ib1->lb, *ib2->var)) ||
                         (ubfree && jl_has_typevar(*ib1->ub, *ib2->var)))) {
                        pib2->next = ib2->next;
                        ib2->next = ib1;
                        ib2->root = ib1->root;
                        if (pib1)
                            pib1->next = ib2;
                        else
                            allvars = ib2;
                        changed = 1;
                        break;
                    }
                    pib2 = ib2;
                    ib2 = ib2->next;
                }
                if (changed) continue;
            }
            pib1 = ib1;
        }
    }

    // Freeze the innervars' lb/ub and perform substitution if needed.
    for (jl_ivarbinding_t *btemp1 = allvars; btemp1 != NULL; btemp1 = btemp1->next) {
        ivar = *btemp1->var;
        ilb = *btemp1->lb;
        iub = *btemp1->ub;
        int isinnervar = btemp1->root->var != ivar;
        if (isinnervar && (ivar->lb != ilb || ivar->ub != iub)) {
            nivar = (jl_value_t *)jl_new_typevar(ivar->name, ilb, iub);
            if (jl_has_typevar(res, ivar))
                res = jl_substitute_var(res, ivar, nivar);
            for (jl_ivarbinding_t *btemp2 = btemp1->next; btemp2 != NULL; btemp2 = btemp2->next) {
                ilb = *btemp2->lb;
                iub = *btemp2->ub;
                if (jl_has_typevar(ilb, ivar))
                    set_ivar_slot(btemp2, btemp2->lb, jl_substitute_var(ilb, ivar, nivar));
                if (jl_has_typevar(iub, ivar))
                    set_ivar_slot(btemp2, btemp2->ub, jl_substitute_var(iub, ivar, nivar));
            }
            if (!wrapped && !varval) {
                // newvar also needs bounds substitution.
                if (jl_has_typevar(vb->lb, ivar))
                    vb->lb = jl_substitute_var(vb->lb, ivar, nivar);
                if (jl_has_typevar(vb->ub, ivar))
                    vb->ub = jl_substitute_var(vb->ub, ivar, nivar);
            }
            set_ivar_slot(btemp1, btemp1->var, (jl_value_t*)nivar);
        }
    }

    // Switch back the innervars' storage.
    while (1) {
        jl_ivarbinding_t *btemp = allvars;
        jl_varbinding_t *root = btemp ? btemp->root : vb;
        size_t icount = 0;
        while (btemp && btemp->root == root) {
            btemp = btemp->next;
            icount++;
        }
        if (root != vb) icount--;
        if (root->innervars != NULL) {
            jl_array_t *rinnervars = root->innervars;
            JL_GC_PROMISE_ROOTED(rinnervars);
            size_t len = jl_array_nrows(rinnervars);
            if (icount > len)
                jl_array_grow_end(rinnervars, icount - len);
            if (icount < len)
                jl_array_del_end(rinnervars, len - icount);
        }
        else if (icount > 0) {
            root->innervars = jl_alloc_array_1d(jl_array_any_type, icount);
        }
        btemp = allvars;
        for (size_t i = icount; i > 0; i--) {
            jl_array_ptr_set(root->innervars, i - 1, (jl_value_t*)*btemp->var);
            btemp = btemp->next;
        }
        if (root == vb) break;
        assert(*btemp->var == root->var);
        allvars = btemp->next;
        assert(allvars == NULL || allvars->root != root);
    }
    JL_GC_POP();

    // if `v` still occurs, re-wrap body in `UnionAll v` or eliminate the UnionAll
    if (jl_has_typevar(res, vb->var)) {
        if (varval) {
            // you can construct `T{x} where x` even if T's parameter is actually
            // limited. in that case we might get an invalid instantiation here.
            res = jl_substitute_var_nothrow(res, vb->var, varval, 2);
            // simplify chains of UnionAlls where bounds become equal
            while (res != NULL && jl_is_unionall(res) && obviously_egal(((jl_unionall_t*)res)->var->lb,
                                                         ((jl_unionall_t*)res)->var->ub)) {
                jl_unionall_t * ures = (jl_unionall_t *)res;
                res = jl_substitute_var_nothrow(ures->body, ures->var, ures->var->lb, 2);
            }
            if (res == NULL)
                res = jl_bottom_type;
        }
        else {
            // re-fresh newvar if bounds changed.
            if (vb->lb != newvar->lb || vb->ub != newvar->ub)
                newvar = jl_new_typevar(newvar->name, vb->lb, vb->ub);
            if (newvar != vb->var)
                res = jl_substitute_var(res, vb->var, (jl_value_t*)newvar);
            varval = (jl_value_t*)newvar;
            if (!wrapped)
                res = jl_type_unionall((jl_tvar_t*)newvar, res);
        }
    }

    if (vb->innervars != NULL) {
        for (size_t i = 0; i < jl_array_nrows(vb->innervars); i++) {
            jl_tvar_t *var = (jl_tvar_t*)jl_array_ptr_ref(vb->innervars, i);
            res = jl_type_unionall(var, res);
        }
    }

    JL_GC_POP();
    return res;
}
```
-/
def finishUnionall (n : Nat) (T : Types) (res0 : Val) (vb0 : VarBinding) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut res ← resolveVal n res0
    let mut vb := { vb0 with
      lb := (← resolveVal n vb0.lb)
      ub := (← resolveVal n vb0.ub)
    }
    let mut varval : Option Val := none
    if vb.ub.isLong && vb.lb.isTypevar then
      varval := some vb.ub
    else if ← obviouslyEgal n T vb.lb vb.ub then
      varval := some vb.ub
    else if covCount vb != 0 && !vb.ub.hasFreeTypevars then
      if ← isLeafBound n T vb.ub then
        varval := some vb.ub
    if vb.intvalued then
      let okInt :=
        (match varval with | some vv => vv.isLong | none => false) ||
        (vb.lb == .bottom && vb.ub == anyType) ||
        (vb.lb.isTypevar && vb.ub == vb.lb)
      if !okInt then
        return .bottom
    let mut newvar := vb.var
    if varval.isNone && (vb.lb != vb.var.tvLb || vb.ub != vb.var.tvUb) then
      let .typevar _ nm _ _ := vb.var | throw "finish_unionall: not a TypeVar"
      newvar ← newTypevar nm vb.lb vb.ub
    -- flatten all innervars into a (reversed) list
    let mut allvarsList : List IVarEntry := []
    let vbInners ← innerVars vb
    for ivar0 in vbInners do
      let ivar ← resolveVal n ivar0
      let entry : IVarEntry := {
        var := ivar, lb := ivar.tvLb, ub := ivar.tvUb,
        rootIdx := none, rootDepth0 := vb.depth0, rootVar := vb.var
      }
      allvarsList := entry :: allvarsList
    let envVars := (← get).vars
    for idx in (List.range envVars.size).reverse do
      let btemp := envVars[idx]!
      let bEntry : IVarEntry := {
        var := btemp.var, lb := (← resolveVal n btemp.lb), ub := (← resolveVal n btemp.ub),
        rootIdx := some idx, rootDepth0 := btemp.depth0, rootVar := btemp.var
      }
      allvarsList := bEntry :: allvarsList
      let bInners ← innerVars btemp
      for ivar0 in bInners do
        let ivar ← resolveVal n ivar0
        let iEntry : IVarEntry := {
          var := ivar, lb := ivar.tvLb, ub := ivar.tvUb,
          rootIdx := some idx, rootDepth0 := btemp.depth0, rootVar := btemp.var
        }
        allvarsList := iEntry :: allvarsList
    let mut allvars : Array IVarEntry := allvarsList.toArray
    let icount : Nat := allvars.size - envVars.size
    let mut wrapped := false
    let mut wrapIdx : Nat := 0
    for idx in [0:allvars.size] do
      let mut btemp := allvars[idx]!
      let bdepth0 := btemp.rootDepth0
      let mut innerflag : Nat := 0
      let ivar := btemp.var
      let ilb := btemp.lb
      let iub := btemp.ub
      if ilb.hasTypevar vb.var then
        if vb.lb == ivar then
          return .bottom
        if let some vv := varval then
          let sub? ← (try pure (some (← substituteVar n T (subOps n T) ilb vb.var vv))
                      catch _ => pure none : CM (Option Val))
          match sub? with
          | some s => btemp := { btemp with lb := s }
          | none => res := .bottom
        else if ilb == vb.var then
          btemp := { btemp with lb := vb.lb }
        else
          innerflag := innerflag ||| 1
      if iub.hasTypevar vb.var then
        let mut iubCur := iub
        if vb.ub == ivar then
          let omitted ← omitBadUnion n T iubCur vb.var
          btemp := { btemp with ub := omitted }
          iubCur := omitted
          if btemp.ub == .bottom && btemp.ub != btemp.lb then
            return .bottom
        if let some vv := varval then
          let sub? ← substituteVarNothrow n T (subOps n T) iubCur vb.var vv 2
          match sub? with
          | none => res := .bottom
          | some s => btemp := { btemp with ub := s }
        else if iubCur == vb.var then
          btemp := { btemp with ub := vb.ub }
        else
          innerflag := innerflag ||| 2
      allvars := allvars.set! idx btemp
      if innerflag != 0 then
        let checkedInit := Array.replicate allvars.size false
        let (hasLb, c1) ←
          if btemp.rootIdx.isNone || bdepth0 != vb.depth0 then
            pure (true, checkedInit)
          else
            hasTypevarViaFlattenEnv n vb.lb ivar allvars checkedInit
        let (hasUb, _) ←
          if hasLb then
            pure (true, c1)
          else
            hasTypevarViaFlattenEnv n vb.ub ivar allvars c1
        if hasLb || hasUb then
          let .typevar vid vnm vlb vub := vb.var | throw "unreachable"
          if (innerflag &&& 1) != 0 then
            btemp := { btemp with lb := .unionall vid vnm vlb vub ilb }
          if (innerflag &&& 2) != 0 then
            btemp := { btemp with ub := .unionall vid vnm vlb vub btemp.ub }
          allvars := allvars.set! idx btemp
        else
          if newvar != vb.var then
            if (innerflag &&& 1) != 0 then
              let s ← substituteVar n T (subOps n T) ilb vb.var newvar
              btemp := { btemp with lb := s }
            if (innerflag &&& 2) != 0 then
              let s ← substituteVar n T (subOps n T) btemp.ub vb.var newvar
              btemp := { btemp with ub := s }
            allvars := allvars.set! idx btemp
          if !wrapped then
            wrapIdx := idx
          wrapped := true
    -- Insert newvar into the (reversed) var list if needed.
    if wrapped then
      let wrapTarget := allvars[wrapIdx]!
      let inew : IVarEntry := {
        var := newvar, lb := vb.lb, ub := vb.ub,
        rootIdx := wrapTarget.rootIdx, rootDepth0 := wrapTarget.rootDepth0, rootVar := wrapTarget.rootVar
      }
      let prefixArr := allvars.extract 0 wrapIdx
      let suffixArr := allvars.extract wrapIdx allvars.size
      allvars := (prefixArr.push inew) ++ suffixArr
    -- Re-sort the innervar inside the (reversed) var list.
    if icount > 0 then
      let mut i1 : Nat := 0
      let mut sortSteps := n
      while i1 < allvars.size do
        if sortSteps == 0 then outOfBudget
        sortSteps := sortSteps - 1
        let ib1 := allvars[i1]!
        let lbfree := ib1.lb.hasFreeTypevars
        let ubfree := ib1.ub.hasFreeTypevars
        if lbfree || ubfree then
          let mut changed := false
          for i2 in [i1 + 1 : allvars.size] do
            let ib2 := allvars[i2]!
            let isinnervar := ib2.rootVar.tvId != ib2.var.tvId
            if isinnervar && ib1.rootDepth0 == ib2.rootDepth0 &&
                ((lbfree && ib1.lb.hasTypevar ib2.var) || (ubfree && ib1.ub.hasTypevar ib2.var)) then
              let moved : IVarEntry := { ib2 with
                rootIdx := ib1.rootIdx, rootDepth0 := ib1.rootDepth0, rootVar := ib1.rootVar
              }
              let part1 := allvars.extract 0 i1
              let part2 := allvars.extract i1 i2
              let part3 := allvars.extract (i2 + 1) allvars.size
              allvars := ((part1.push moved) ++ part2) ++ part3
              changed := true
              break
          if changed then
            continue
        i1 := i1 + 1
    -- Freeze the innervars' lb/ub and perform substitution if needed.
    for idx1 in [0:allvars.size] do
      let btemp1 := allvars[idx1]!
      let ivar := btemp1.var
      let ilb := btemp1.lb
      let iub := btemp1.ub
      let isinnervar := btemp1.rootVar.tvId != ivar.tvId
      if isinnervar && (ivar.tvLb != ilb || ivar.tvUb != iub) then
        let .typevar _ inm _ _ := ivar | throw "unreachable"
        let nivar ← newTypevar inm ilb iub
        if res.hasTypevar ivar then
          res ← substituteVar n T (subOps n T) res ivar nivar
        for idx2 in [idx1 + 1 : allvars.size] do
          let mut btemp2 := allvars[idx2]!
          if btemp2.lb.hasTypevar ivar then
            let s ← substituteVar n T (subOps n T) btemp2.lb ivar nivar
            btemp2 := { btemp2 with lb := s }
          if btemp2.ub.hasTypevar ivar then
            let s ← substituteVar n T (subOps n T) btemp2.ub ivar nivar
            btemp2 := { btemp2 with ub := s }
          allvars := allvars.set! idx2 btemp2
        if !wrapped && varval.isNone then
          if vb.lb.hasTypevar ivar then
            let s ← substituteVar n T (subOps n T) vb.lb ivar nivar
            vb := { vb with lb := s }
          if vb.ub.hasTypevar ivar then
            let s ← substituteVar n T (subOps n T) vb.ub ivar nivar
            vb := { vb with ub := s }
        allvars := allvars.set! idx1 { btemp1 with var := nivar, lb := ilb, ub := iub }
    -- Switch back the innervars' storage.
    let mut pos : Nat := 0
    for envIdx in [0:envVars.size] do
      let mut groupInners : Array Val := #[]
      while pos < allvars.size && allvars[pos]!.rootIdx == some envIdx &&
          allvars[pos]!.var.tvId != allvars[pos]!.rootVar.tvId do
        groupInners := groupInners.push allvars[pos]!.var
        pos := pos + 1
      let revInners := groupInners.reverse
      if pos < allvars.size && allvars[pos]!.rootIdx == some envIdx then
        let rootEntry := allvars[pos]!
        pos := pos + 1
        let curB ← getBinding envIdx
        let newPtr ← match curB.innervars with
          | some arrIdx =>
            modify fun e => { e with innerArrays := e.innerArrays.set! arrIdx revInners }
            pure (some arrIdx)
          | none =>
            if revInners.isEmpty then
              pure none
            else do
              let arrIdx := (← get).innerArrays.size
              modify fun e => { e with innerArrays := e.innerArrays.push revInners }
              pure (some arrIdx)
        changeBinding envIdx fun b => { b with lb := rootEntry.lb, ub := rootEntry.ub, innervars := newPtr }
    let mut vbGroupInners : Array Val := #[]
    while pos < allvars.size do
      vbGroupInners := vbGroupInners.push allvars[pos]!.var
      pos := pos + 1
    let vbFinalInners := vbGroupInners.reverse
    -- if `v` still occurs, re-wrap body in `UnionAll v` or eliminate the UnionAll
    if res.hasTypevar vb.var then
      if let some vv := varval then
        let mut res? ← substituteVarNothrow n T (subOps n T) res vb.var vv 2
        let mut simpSteps := n
        while res?.isSome do
          if simpSteps == 0 then outOfBudget
          simpSteps := simpSteps - 1
          let some r := res? | break
          if let .unionall uid nm ulb uub ubody := r then
            if ← obviouslyEgal n T ulb uub then
              let uvar := Val.typevar uid nm ulb uub
              res? ← substituteVarNothrow n T (subOps n T) ubody uvar ulb 2
            else
              break
          else
            break
        res := res?.getD .bottom
      else
        if vb.lb != newvar.tvLb || vb.ub != newvar.tvUb then
          let .typevar _ nm _ _ := newvar | throw "unreachable"
          newvar ← newTypevar nm vb.lb vb.ub
        if newvar != vb.var then
          res ← substituteVar n T (subOps n T) res vb.var newvar
        if !wrapped then
          res ← typeUnionall n T (subOps n T) newvar res
    for var in vbFinalInners do
      res ← typeUnionall n T (subOps n T) var res
    return res
termination_by structural n

/-- `widen_Type_to_union`: map `Type{X}` to kind type over union only if the widened kind satisfies `bound`.

Julia source: src/subtype.c:1510-1548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *widen_Type_to_union(jl_value_t *t, jl_value_t *bound, jl_stenv_t *e) JL_CANSAFEPOINT
{
    if (jl_is_some_Type(t) && !jl_is_typevar(jl_some_Type_T(t))) {
        // This runs in the existential (intersection) direction only, where
        // the tag selects the (nonempty) tag-homogeneous slice of `Type{X}`'s
        // members as the witness for the variable, so widening the bound to
        // the tag remains a valid choice under `==`-class semantics (#33136);
        // the result may then under-represent members of other tags, as
        // intersection always could for diagonal variables.
        jl_value_t *w = jl_typeof(jl_some_Type_T(t));
        if (!try_subtype_in_env_existential(w, bound, e))
            return t;
        return w;
    }
    if (jl_is_uniontype(t)) {
        jl_value_t *wa = NULL, *wb = NULL;
        JL_GC_PUSH2(&wa, &wb);
        wa = widen_Type_to_union(((jl_uniontype_t*)t)->a, bound, e);
        wb = widen_Type_to_union(((jl_uniontype_t*)t)->b, bound, e);
        if (wa != ((jl_uniontype_t*)t)->a || wb != ((jl_uniontype_t*)t)->b)
            wa = simple_join(wa, wb);
        else
            wa = t;
        JL_GC_POP();
        return wa;
    }
    if (jl_is_unionall(t)) {
        jl_unionall_t *u = (jl_unionall_t*)t;
        jl_value_t *body = NULL;
        JL_GC_PUSH1(&body);
        body = widen_Type_to_union(u->body, bound, e);
        if (body != u->body && !jl_has_typevar(body, u->var)) {
            JL_GC_POP();
            return body;
        }
        JL_GC_POP();
    }
    return t;
}
```
-/
def widenTypeToUnion (n : Nat) (T : Types) (t bound : Val) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if t.isSomeType && !t.someTypeT.isTypevar then
      let w := typeOf t.someTypeT
      if !(← trySubtypeInEnvExistential n T w bound) then
        return t
      return w
    if let .union ua ub := t then
      let wa ← widenTypeToUnion n T ua bound
      let wb ← widenTypeToUnion n T ub bound
      if wa != ua || wb != ub then
        return ← simpleJoin n T wa wb
      return t
    if let .unionall _ _ _ _ body := t then
      let body' ← widenTypeToUnion n T body bound
      if body' != body && !body'.hasTypevar t.uaVar then
        return body'
    return t
termination_by structural n

/-- `try_subtype_in_env_existential`

Julia source: src/subtype.c:4480-4490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int try_subtype_in_env_existential(jl_value_t *a, jl_value_t *b, jl_stenv_t *e) JL_CANSAFEPOINT
{
    if (try_subtype_by_bounds(a, b, e))
        return 1;
    jl_savedenv_t se;
    save_env(e, &se, 1);
    int ret = subtype_in_env_existential(a, b, e);
    restore_env(e, &se, 1);
    free_env(&se);
    return ret;
}
```
-/
def trySubtypeInEnvExistential (n : Nat) (T : Types) (a b : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if ← trySubtypeByBounds n T a b then
      return true
    let se ← saveEnv
    let ret ← subtypeInEnvExistential n T a b
    restoreEnv se true
    return ret
termination_by structural n

/-- `try_subtype_in_env_nonexistential`

Julia source: src/subtype.c:4494-4504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int try_subtype_in_env_nonexistential(jl_value_t *a, jl_value_t *b, jl_stenv_t *e) JL_CANSAFEPOINT
{
    if (try_subtype_by_bounds(a, b, e))
        return 1;
    jl_savedenv_t se;
    save_env(e, &se, 0); // Set root=0 as this is a nonexistential subtype check (no bounds change in env)
    int ret = subtype_in_env_nonexistential(a, b, e);
    restore_env(e, &se, 0);
    free_env(&se);
    return ret;
}
```
-/
def trySubtypeInEnvNonexistential (n : Nat) (T : Types) (a b : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if ← trySubtypeByBounds n T a b then
      return true
    let se ← saveEnv
    let ret ← subtypeInEnvNonexistential n T a b
    restoreEnv se false
    return ret
termination_by structural n

/-- `subtype_in_env_existential`: subtype, treating all vars as existential.

Julia source: src/subtype.c:4514-4533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_in_env_existential(jl_value_t *x, jl_value_t *y, jl_stenv_t *e) JL_CANSAFEPOINT
{
    if (x == jl_bottom_type || y == (jl_value_t*)jl_any_type || obviously_in_union(y, x))
        return 1;
    int8_t *rs = (int8_t*)alloca(current_env_length(e));
    jl_varbinding_t *v = e->vars;
    int n = 0;
    while (v != NULL) {
        rs[n++] = v->existential;
        v->existential = 1;
        v = v->prev;
    }
    int issub = subtype_in_env(x, y, e);
    n = 0; v = e->vars;
    while (v != NULL) {
        v->existential = rs[n++];
        v = v->prev;
    }
    return issub;
}
```
-/
def subtypeInEnvExistential (n : Nat) (T : Types) (x y : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if x == .bottom || y == anyType then
      return true
    if ← obviouslyInUnion n T y x then
      return true
    let rs := (← get).vars.map (·.existential)
    modify fun e => { e with vars := e.vars.map fun b => { b with existential := true } }
    let issub ← subtypeInEnv n T x y
    modify fun e => { e with vars := e.vars.mapIdx fun i b => { b with existential := rs[i]! } }
    return issub
termination_by structural n

/-- `subtype_in_env_nonexistential`: subtype, treating all vars as nonexistential.

Julia source: src/subtype.c:4536-4555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_in_env_nonexistential(jl_value_t *x, jl_value_t *y, jl_stenv_t *e) JL_CANSAFEPOINT
{
    if (x == jl_bottom_type || y == (jl_value_t*)jl_any_type || obviously_in_union(y, x))
        return 1;
    int8_t *rs = (int8_t*)alloca(current_env_length(e));
    jl_varbinding_t *v = e->vars;
    int n = 0;
    while (v != NULL) {
        rs[n++] = v->existential;
        v->existential = 0;
        v = v->prev;
    }
    int issub = subtype_in_env(x, y, e);
    n = 0; v = e->vars;
    while (v != NULL) {
        v->existential = rs[n++];
        v = v->prev;
    }
    return issub;
}
```
-/
def subtypeInEnvNonexistential (n : Nat) (T : Types) (x y : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if x == .bottom || y == anyType then
      return true
    if ← obviouslyInUnion n T y x then
      return true
    let rs := (← get).vars.map (·.existential)
    modify fun e => { e with vars := e.vars.map fun b => { b with existential := false } }
    let issub ← subtypeInEnv n T x y
    modify fun e => { e with vars := e.vars.mapIdx fun i b => { b with existential := rs[i]! } }
    return issub
termination_by structural n

/-- `subtype_in_env` preserving `e.intersection` (`src/subtype.c:4087-4103`).

Julia source: src/subtype.c:4087-4103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_in_env(jl_value_t *x, jl_value_t *y, jl_stenv_t *e) JL_CANSAFEPOINT
{
    jl_stenv_t e2;
    init_stenv(&e2, NULL, 0);
    e2.vars = e->vars;
    e2.intersection = e->intersection;
    e2.invdepth = e->invdepth;
    e2.envsz = e->envsz;
    e2.envout = e->envout;
    e2.envidx = e->envidx;
    e2.ignore_lb_required = e->ignore_lb_required;
    e2.closed_inputs = e->closed_inputs;
    e2.inputs[0] = e->inputs[0];
    e2.inputs[1] = e->inputs[1];
    e2.Loffset = e->Loffset;
    return forall_exists_subtype(x, y, &e2, PARAM_NONE);
}
```
-/
def subtypeInEnv (n : Nat) (T : Types) (x y : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let e ← get
    let e2 := { initStenv with
      vars := e.vars
      intersection := e.intersection
      invdepth := e.invdepth
      envidx := e.envidx
      ignoreLbRequired := e.ignoreLbRequired
      closedInputs := e.closedInputs
      inputs := e.inputs
      Loffset := e.Loffset
      innerArrays := e.innerArrays
      typevars := e.typevars }
    let (ans, e2) ← (forallExistsSubtype n T x y .none).run e2
    modify fun e => { e with vars := e2.vars, innerArrays := e2.innerArrays, typevars := e2.typevars }
    return ans
termination_by structural n

/-- `forall_exists_subtype` with intersection branches enabled (`src/subtype.c:3533-3554`).

Julia source: src/subtype.c:3533-3554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int forall_exists_subtype(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, jl_param_pos_t param)
{
    // The depth recursion has the following shape, after simplification:
    // ∀₁
    //   ∃₁
    assert(e->Runions.depth == 0);
    assert(e->Lunions.depth == 0);
    jl_savedenv_t se;
    save_env(e, &se, 1);

    e->Lunions.used = 0;
    int sub;
    while (1) {
        sub = exists_subtype(x, y, e, &se, param);
        if (!sub || !next_union_state(e, 0))
            break;
        re_save_env(e, &se, 1);
    }

    free_env(&se);
    return sub;
}
```
-/
def forallExistsSubtype (n : Nat) (T : Types) (x y : Val) (param : ParamPos) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut se ← saveEnv
    modify fun e => { e with Lunions := { e.Lunions with used := 0 } }
    for _ in [0:n] do
      let sub ← existsSubtype n T x y se param
      let next ← if sub then nextUnionState false else pure false
      if !sub || !next then return sub
      se ← reSaveEnv
    outOfBudget
termination_by structural n

/-- `exists_subtype` with intersection branches enabled (`src/subtype.c:3509-3531`).

Julia source: src/subtype.c:3509-3531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int exists_subtype(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, jl_savedenv_t *se, jl_param_pos_t param) JL_CANSAFEPOINT
{
    e->Runions.used = 0;
    while (1) {
        e->Runions.depth = 0;
        e->Runions.more = 0;
        e->Lunions.depth = 0;
        e->Lunions.more = 0;
        if (subtype(x, y, e, param))
            return 1;
        if (next_union_state(e, 1)) {
            // We preserve `envout` here as `subtype_unionall` needs previous assigned env values.
            int oldidx = e->envidx;
            e->envidx = e->envsz;
            restore_env(e, se, 1);
            e->envidx = oldidx;
        }
        else {
            restore_env(e, se, 1);
            return 0;
        }
    }
}
```
-/
def existsSubtype (n : Nat) (T : Types) (x y : Val) (se : SavedEnv) (param : ParamPos) :
    STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    modify fun e => { e with Runions := { e.Runions with used := 0 } }
    for _ in [0:n] do
      modify fun e => { e with
        Runions := { e.Runions with depth := 0, more := 0 }
        Lunions := { e.Lunions with depth := 0, more := 0 } }
      if ← subtype n T x y param then return true
      if ← nextUnionState true then restoreEnv se
      else
        restoreEnv se
        return false
    outOfBudget
termination_by structural n

/-- `subtype_ccheck` with intersection branches enabled (`src/subtype.c:1040-1091`).

Julia source: src/subtype.c:1040-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_ccheck(jl_value_t *x, jl_value_t *y, jl_stenv_t *e) JL_CANSAFEPOINT
{
    if (jl_is_long(x) && jl_is_long(y))
        return jl_unbox_long(x) == jl_unbox_long(y) + e->Loffset;
    if (x == y)
        return 1;
    if (x == jl_bottom_type && jl_is_type(y))
        return 1;
    if (y == (jl_value_t*)jl_any_type && jl_is_type(x))
        return 1;
    if (jl_is_uniontype(x) && jl_egal(x, y))
        return 1;
    if (x == (jl_value_t*)jl_any_type && jl_is_datatype(y))
        return 0;
    if (obviously_in_union(y, x))
        return 1;
    jl_saved_unionstate_t oldLunions; push_unionstate(&oldLunions, &e->Lunions);
    // Consistency check for a typevar bound: covariant occurrences inside this
    // call should not accumulate into the surrounding scope's diagonality
    // counter. Save & reset the counters, then fold the local max into
    // cov_diag on exit.
    int8_t *saved_cov = (int8_t*)alloca(current_env_length(e));
    int nsaved_cov = push_consistency_scope(e, saved_cov);
    // A check on a closed x-term checks an actual value of the query, so bounds
    // recorded inside keep the current certainty channel; descent into that
    // value is structural (`value_descent`), so it also preserves identity
    // across equality wrappers. A typevar-containing x checks a typevar bound
    // proxy, whose bindings need not exist for every call. NOTE: tuple-prefix
    // `lb_required` marking stays active here on purpose — a var reached only
    // through another var's declared tuple bound (e.g. `E` via
    // `S <: Tuple{Vararg{E}}`) is pinned by every member exactly when the
    // x-term supplies a fixed prefix element (see `mark_required_tuple_element`).
    int saved_channel = e->bound_channel;
    int saved_spell = e->spell_channel;
    int saved_descent = e->value_descent;
    if (jl_has_free_typevars(x)) {
        if (e->bound_channel > BOUND_PROXY)
            e->bound_channel = BOUND_PROXY;
        if (e->spell_channel > BOUND_PROXY)
            e->spell_channel = BOUND_PROXY;
    }
    else {
        e->value_descent = 1;
    }
    int sub = local_forall_exists_subtype(x, y, e, PARAM_COVARIANT, 1);
    e->bound_channel = saved_channel;
    e->spell_channel = saved_spell;
    e->value_descent = saved_descent;
    pop_consistency_scope(e, saved_cov, nsaved_cov);
    pop_unionstate(&e->Lunions, &oldLunions);
    return sub;
}
```
-/
def subtypeCcheck (n : Nat) (T : Types) (x y : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let (.long a, .long b) := (x, y) then return a == b + (← get).Loffset
    if x == y then return true
    if x == .bottom && y.isType then return true
    if y == anyType && x.isType then return true
    if x.isUnion then if ← egal n T x y then return true
    if x == anyType && y.isDatatype then return false
    if ← obviouslyInUnion n T y x then return true
    let oldL := pushUnionstate (← get).Lunions
    let savedCov ← pushConsistencyScope
    let e ← get
    if x.hasFreeTypevars then
      modify fun e => { e with boundChannel := min e.boundChannel .proxy, spellChannel := min e.spellChannel .proxy }
    else modify fun e => { e with valueDescent := true }
    let sub ← localForallExistsSubtype n T x y .covariant 1
    modify fun cur => { cur with boundChannel := e.boundChannel, spellChannel := e.spellChannel, valueDescent := e.valueDescent }
    popConsistencyScope savedCov
    modify fun e => { e with Lunions := popUnionstate e.Lunions oldL }
    return sub
termination_by structural n

/-- `subtype_left_var` with intersection branches enabled (`src/subtype.c:1093-1108`).

Julia source: src/subtype.c:1093-1108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_left_var(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, jl_param_pos_t param) JL_CANSAFEPOINT
{
    if (jl_is_long(x) && jl_is_long(y))
        return jl_unbox_long(x) == jl_unbox_long(y) + e->Loffset;
    if (x == y && !(jl_is_unionall(y)))
        return 1;
    if (x == jl_bottom_type && jl_is_type(y))
        return 1;
    if (y == (jl_value_t*)jl_any_type && jl_is_type(x))
        return 1;
    if (jl_is_uniontype(x) && jl_egal(x, y))
        return 1;
    if (x == (jl_value_t*)jl_any_type && jl_is_datatype(y))
        return 0;
    return subtype(x, y, e, param);
}
```
-/
def subtypeLeftVar (n : Nat) (T : Types) (x y : Val) (param : ParamPos) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let (.long a, .long b) := (x, y) then return a == b + (← get).Loffset
    if x == y && !y.isUnionall then return true
    if x == .bottom && y.isType then return true
    if y == anyType && x.isType then return true
    if x.isUnion then if ← egal n T x y then return true
    if x == anyType && y.isDatatype then return false
    subtype n T x y param
termination_by structural n

/-- `var_lt` including `e.intersection` branches (`src/subtype.c:1271-1320`).

Julia source: src/subtype.c:1271-1320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int var_lt(jl_tvar_t *b, jl_value_t *a, jl_stenv_t *e, jl_param_pos_t param, jl_varbinding_t *bb, int innervar) JL_CANSAFEPOINT
{
    if (bb == NULL) {
        if (innervar && e->intersection)
            return 1;
        if (innervar)
            return subtype_left_var(b->ub, a, e, param);
        return singleton_typevar_subtype(b, a);
    }
    record_var_occurrence(bb, e, param);
    assert(!jl_is_long(a) || e->Loffset == 0);
    if (e->Loffset != 0 && !jl_is_typevar(a) &&
        a != jl_bottom_type && a != (jl_value_t *)jl_any_type)
        return 0;
    if (!bb->existential) {  // check ∀b . b<:a
        // The expanded bound `bb->ub` lives in the forall-side context;
        // its covariant typevar occurrences must not combine with the
        // surrounding tuple body's occurrences.
        int8_t *saved_fb = (int8_t*)alloca(current_env_length(e));
        int nsaved_fb = push_forall_bound_scope(e, saved_fb);
        int sub = subtype_left_var(bb->ub, a, e, param);
        pop_forall_bound_scope(e, saved_fb, nsaved_fb);
        return sub;
    }
    record_var_pin(bb, a, e, param);
    if (bb->ub == a)
        return 1;
    if (!((bb->lb == jl_bottom_type && !jl_is_type(a) && !jl_is_typevar(a)) || subtype_ccheck(bb->lb, a, e)))
        return 0;
    // for this to work we need to compute issub(left,right) before issub(right,left),
    // since otherwise the issub(a, bb.ub) check in var_gt becomes vacuous.
    if (e->intersection) {
        jl_value_t *ub = intersect_aside(a, bb->ub, e, bb->depth0);
        JL_GC_PUSH1(&ub);
        if (ub != (jl_value_t*)b && !reachable_var(ub, b, e))
            bb->ub = ub;
        JL_GC_POP();
    }
    else {
        // `simple_meet` resolves the greatest-lower-bound of `bb->ub` and `a`
        // precisely when one operand subsumes the other (or they are disjoint);
        // otherwise it now returns an exact `Intersect{bb->ub, a}` meet node
        // rather than over-approximating to one side, which would let `b` escape
        // its declared range (e.g. equating `∃b<:Foo` with an outer `∀a<:Bar`
        // even though `Bar ⊄ Foo`). See #61917.
        bb->ub = simple_meet(bb->ub, a, 1);
    }
    assert(bb->ub != (jl_value_t*)b);
    return 1;
}
```
-/
def varLt (n : Nat) (T : Types) (b a : Val) (param : ParamPos) (bb : Option Nat)
    (innervar : Bool) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let b ← resolveVal n b
    let some i := bb | do
      if innervar && (← get).intersection then return true
      if innervar then return ← subtypeLeftVar n T b.tvUb a param
      return ← singletonTypevarSubtype n b a
    recordVarOccurrence (some i) param
    let vb ← getBinding i
    if (← get).Loffset != 0 && !a.isTypevar && a != .bottom && a != anyType then return false
    if !vb.existential then
      let saved ← pushForallBoundScope
      let sub ← subtypeLeftVar n T vb.ub a param
      popForallBoundScope saved
      return sub
    recordVarPin i a param
    if vb.ub == a then return true
    if !(vb.lb == .bottom && !a.isType && !a.isTypevar) then
      if !(← subtypeCcheck n T vb.lb a) then return false
    let vb ← getBinding i
    if (← get).intersection then
      let ub ← intersectAside n T a vb.ub vb.depth0 []
      if ub != b then
        if !(← reachableVar n ub b) then
          changeBinding i fun x => { x with ub := ub }
    else
      let ub0 ← resolveVal n vb.ub
      let ub ← simpleMeet n T ub0 a 1
      changeBinding i fun x => { x with ub := ub }
    return true
termination_by structural n

/-- `var_gt` including `e.intersection` branches (`src/subtype.c:1323-1381`).

Julia source: src/subtype.c:1323-1381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int var_gt(jl_tvar_t *b, jl_value_t *a, jl_stenv_t *e, jl_param_pos_t param, jl_varbinding_t *bb, int innervar) JL_CANSAFEPOINT
{
    if (bb == NULL) {
        if (innervar && e->intersection)
            return 1;
        if (innervar)
            return subtype_left_var(a, b->lb, e, param);
        return subtype_singleton_typevar(a, b);
    }
    record_var_occurrence(bb, e, param);
    assert(!jl_is_long(a) || e->Loffset == 0);
    if (e->Loffset != 0 && !jl_is_typevar(a) &&
        a != jl_bottom_type && a != (jl_value_t *)jl_any_type)
        return 0;
    if (!bb->existential) {  // check ∀b . b>:a
        // Symmetric to var_lt: scope forall-side occurrences from the expanded
        // lower bound away from the enclosing tuple body.
        int8_t *saved_fb = (int8_t*)alloca(current_env_length(e));
        int nsaved_fb = push_forall_bound_scope(e, saved_fb);
        int sub = subtype_left_var(a, bb->lb, e, param);
        pop_forall_bound_scope(e, saved_fb, nsaved_fb);
        return sub;
    }
    record_var_pin(bb, a, e, param);
    if (a != jl_bottom_type && bb->lb_certainty < e->bound_channel)
        bb->lb_certainty = e->bound_channel;
    if (bb->lb == a) {
        if (bb->lb_spell < e->spell_channel)
            bb->lb_spell = e->spell_channel;
        return 1;
    }
    if (!(bb->ub == (jl_value_t*)jl_any_type && !jl_is_type(a) && !jl_is_typevar(a))) {
        int saved = e->ignore_lb_required;
        e->ignore_lb_required = 1;
        int ub_ok = subtype_ccheck(a, bb->ub, e);
        e->ignore_lb_required = saved;
        if (!ub_ok)
            return 0;
    }
    // when the var is pinned (`lb === ub`), `a <= ub` was just checked and a
    // join picking `a` proves `lb <= a`, i.e. `a` respells the same type: keep
    // the existing spelling unless `a`'s is more authoritative (see `lb_spell`)
    int pinned = (bb->lb == bb->ub && bb->lb != jl_bottom_type);
    jl_value_t *lb = simple_join(bb->lb, a);
    JL_GC_PUSH1(&lb);
    if (pinned && lb == a && e->spell_channel <= bb->lb_spell) {
        // keep bb->lb (and bb->ub) as-is
    }
    else if (!e->intersection || !jl_is_typevar(lb) || !reachable_var(lb, b, e)) {
        if (bb->lb != lb) {
            bb->lb = lb;
            bb->lb_spell = e->spell_channel;
        }
    }
    JL_GC_POP();
    // this bound should not be directly circular
    assert(bb->lb != (jl_value_t*)b);
    return 1;
}
```
-/
def varGt (n : Nat) (T : Types) (b a : Val) (param : ParamPos) (bb : Option Nat)
    (innervar : Bool) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let b ← resolveVal n b
    let some i := bb | do
      if innervar && (← get).intersection then return true
      if innervar then return ← subtypeLeftVar n T a b.tvLb param
      return ← subtypeSingletonTypevar n a b
    recordVarOccurrence (some i) param
    let vb ← getBinding i
    if (← get).Loffset != 0 && !a.isTypevar && a != .bottom && a != anyType then return false
    if !vb.existential then
      let saved ← pushForallBoundScope
      let sub ← subtypeLeftVar n T a vb.lb param
      popForallBoundScope saved
      return sub
    recordVarPin i a param
    let channel := (← get).boundChannel
    if a != .bottom then changeBinding i fun x => { x with lbCertainty := max x.lbCertainty channel }
    if vb.lb == a then
      let spell := (← get).spellChannel
      changeBinding i fun x => { x with lbSpell := max x.lbSpell spell }
      return true
    if !(vb.ub == anyType && !a.isType && !a.isTypevar) then
      let saved := (← get).ignoreLbRequired
      modify fun e => { e with ignoreLbRequired := true }
      let ok ← subtypeCcheck n T a vb.ub
      modify fun e => { e with ignoreLbRequired := saved }
      if !ok then return false
    let vb ← getBinding i
    let pinned := vb.lb == vb.ub && vb.lb != .bottom
    let lb0 ← resolveVal n vb.lb
    let lb ← simpleJoin n T lb0 a
    let spell := (← get).spellChannel
    if !(pinned && lb == a && spell ≤ vb.lbSpell) then
      let canSet ←
        if !(← get).intersection || !lb.isTypevar then pure true
        else pure (!(← reachableVar n lb b))
      if canSet && vb.lb != lb then
        changeBinding i fun x => { x with lb := lb, lbSpell := spell }
    return true
termination_by structural n

/-- `subtype_var` including `e.intersection` branches (`src/subtype.c:1383-1406`).

Julia source: src/subtype.c:1383-1406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_var(jl_tvar_t *b, jl_value_t *a, jl_stenv_t *e, int R, jl_param_pos_t param, jl_varbinding_t *bb, int innervar) JL_CANSAFEPOINT
{
    if (e->intersection) {
        jl_value_t *bub = bb ? bb->ub : innervar ? ((jl_tvar_t*)b)->ub : (jl_value_t*)b;
        jl_value_t *blb = bb ? bb->lb : innervar ? ((jl_tvar_t*)b)->lb : (jl_value_t*)b;
        if (bub == blb && jl_is_typevar(bub) && bub != (jl_value_t*)b) {
            int bubinner = 0;
            jl_varbinding_t *bubb = lookup_binding(e, (jl_tvar_t*)bub, &bubinner);
            int sub = subtype_var((jl_tvar_t *)bub, a, e, R, param, bubb, bubinner);
            return sub;
        }
    }
    if (e->Loffset != 0 && jl_is_long(a)) {
        int old_offset = R ? -e->Loffset : e->Loffset;
        jl_value_t *na = jl_box_long(jl_unbox_long(a) + old_offset);
        JL_GC_PUSH1(&na);
        e->Loffset = 0;
        int sub = R ? var_gt(b, na, e, param, bb, innervar) : var_lt(b, na, e, param, bb, innervar);
        e->Loffset = R ? -old_offset : old_offset;
        JL_GC_POP();
        return sub;
    }
    return R ? var_gt(b, a, e, param, bb, innervar) : var_lt(b, a, e, param, bb, innervar);
}
```
-/
def subtypeVar (n : Nat) (T : Types) (b a : Val) (R : Bool) (param : ParamPos) (bb : Option Nat)
    (innervar : Bool) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if (← get).intersection then
      let xb ← match bb with | some i => do pure (some (← getBinding i)) | none => pure none
      let bub := match xb with | some v => v.ub | none => if innervar then b.tvUb else b
      let blb := match xb with | some v => v.lb | none => if innervar then b.tvLb else b
      if bub == blb && bub.isTypevar && bub != b then
        recordVarOccurrence bb param
        return ← (if R then subtype n T a bub param else subtype n T bub a param)
    if let .long v := a then
      if (← get).Loffset != 0 then
        let offset := (← get).Loffset
        let oldOffset := if R then -offset else offset
        modify fun e => { e with Loffset := 0 }
        let sub ← if R then varGt n T b (.long (v + oldOffset)) param bb innervar
          else varLt n T b (.long (v + oldOffset)) param bb innervar
        modify fun e => { e with Loffset := offset }
        return sub
    if R then varGt n T b a param bb innervar else varLt n T b a param bb innervar
termination_by structural n

/-- `subtype_unionall` including `e.intersection` branches (`src/subtype.c:1901-2121`).

Julia source: src/subtype.c:1901-2121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_unionall(jl_value_t *t, jl_unionall_t *u, jl_stenv_t *e, int8_t R, jl_param_pos_t param) JL_CANSAFEPOINT
{
    u = unalias_unionall(u, e);
    jl_value_t *new_tvar = NULL;
    jl_varbinding_t vb;
    memset(&vb, 0, sizeof(vb));
    vb.existential = R;
    vb.depth0 = e->invdepth;
    vb.prev = e->vars;
    JL_GC_PUSH5(&u, &vb.lb, &vb.ub, &vb.innervars, &new_tvar);
    // a free input typevar sharing `u->var`'s identity is not in `e->vars`, so
    // `unalias_unionall` cannot see it; closed inputs have no such occurrences
    if (may_capture_free_var(t, u->var, e))
        u = jl_rename_unionall(u);
    vb.var = u->var;
    vb.lb = u->var->lb;
    vb.ub = u->var->ub;
    vb.body_occurs_inv = -1;
    vb.body = u->body;
    e->vars = &vb;
    int ans;
    if (R) {
        e->envidx++;
        ans = subtype(t, u->body, e, param);
        e->envidx--;
    }
    else {
        // ∀ path: a variable with a trivial lower bound, a union upper bound,
        // and only covariant occurrences in the body ranges over each arm of
        // its upper bound independently, i.e. the UnionAll distributes over
        // the arms:
        //   (Tuple{T,T} where T<:Union{A,B}) ==
        //       Union{Tuple{T,T} where T<:A, Tuple{T,T} where T<:B}
        // (diagonality, if any, is preserved: each value of the variable is
        // concrete and therefore lies entirely within a single arm).
        // Split the bound here by registering one ordinary left-union decision
        // per Union node, so that the enclosing ∀∃ loop enumerates all arms.
        if (!e->intersection && vb.lb == jl_bottom_type && jl_is_uniontype(vb.ub) &&
            !vb_body_occurs_inv(&vb) && var_occurs_covariant_only(u->body, u->var, 1))
            vb.ub = pick_union_element(vb.ub, e, 0);
        ans = subtype(u->body, t, e, param);
    }

    // handle the "diagonal dispatch" rule, which says that a type var occurring more
    // than once, and only in covariant position, is constrained to concrete types. E.g.
    //  ( Tuple{Int, Int}    <: Tuple{T, T} where T) but
    // !( Tuple{Int, String} <: Tuple{T, T} where T)
    // Then check concreteness by checking that the lower bound is not an abstract type.
    int diagonal = cov_count(&vb) > 1 && !vb_body_occurs_inv(&vb);
    // Widen Type{x} to typeof(x) for ordinary argument-slot occurrences and
    // diagonal constraints, but not invariant matches. This is only a local
    // view for checks and envout; keep `vb.lb` structurally precise.
    int widen_lb = !vb.occurs_inv && (diagonal || (vb.occurs_cov == 1 && vb.cov_diag == 0));
    jl_value_t *widened_lb = widen_lb ? widen_Type_if_concrete(vb.lb, e, NULL, e->intersection) : vb.lb;
    if (ans && (vb.concrete || (diagonal && is_leaf_typevar(u->var)))) {
        jl_value_t *concrete_lb = diagonal ? widened_lb : vb.lb;
        if (vb.concrete && !diagonal && !is_leaf_bound(vb.ub)) {
            // a non-diagonal var can only be a subtype of a diagonal var if its
            // upper bound is concrete.
            ans = 0;
        }
        else if (jl_is_typevar(vb.lb)) {
            jl_tvar_t *v = (jl_tvar_t*)vb.lb;
            jl_varbinding_t *vlb = lookup(e, v);
            if (vlb)
                vlb->concrete = 1;
        }
        else if (!is_leaf_bound(concrete_lb)) {
            ans = 0;
        }
    }
    e->vars = vb.prev;

    if (!ans) {
        JL_GC_POP();
        return 0;
    }

    // An internal `Intersect` meet node (see #61917) is exact for subtyping but
    // must not appear in a result type or static parameter (it is not a real
    // type). It only ever occurs as the top layer of `vb.ub`; over-approximate
    // it now, before `vb.ub` is used to build any result typevar below.
    vb.ub = widen_intersect(vb.ub);

    // If this variable was resolved to something concrete, just use that value for the
    // substitution below.
    if (vb.lb == vb.ub) {
        new_tvar = vb.lb;
    }

    // It is possible for bounds of outer existential vars to refer to universally qualified
    // inner vars. In this case, we should treat this variable as universally qualified over
    // the bounds at this point in future subtype queries. However, we need to do some work
    // to keep track that this situation happened to distinguish it from the case where
    // we have a free typevar in the input.
    jl_varbinding_t *outermost = NULL;
    for (jl_varbinding_t *btemp = vb.prev; btemp; btemp = btemp->prev)
        outermost = btemp;
    for (jl_varbinding_t *btemp = vb.prev; btemp; btemp = btemp->prev) {
        if (!btemp->existential)
            continue;

        // TODO: This takes significant time
        int ub_has_var = jl_has_typevar(btemp->ub, vb.var);
        int lb_has_var = jl_has_typevar(btemp->lb, vb.var);

        jl_tvar_t *old_tvar = vb.var;
        // Rooted by `u` in `vb`'s frame
        JL_GC_PROMISE_ROOTED(old_tvar);
        if (ub_has_var || lb_has_var) {
            if (btemp->depth0 != vb.depth0) {
                // If we've passed through an invariant constructor, the bounds of the outer var can never
                // be satisfied. Consider (ignoring normalization) Ref{T where T} <: Ref{S} where S. This ends
                // up as T<:S<:T. Since `T` is universally qualified over its bounds, this would require `S` to
                // take the full range. However, the `∃` qualifier needs a single value, so unless `T` is similarly
                // constrained, this is unsatisfiable.
                if (vb.lb != vb.ub) {
                    JL_GC_POP();
                    return 0;
                }
            }
            btemp->tainted_inner = 1;

            // We need to rename the typevar to prevent confusion. Ordinarily typevar identity conflicts
            // are taken care of by jl_rename_unionall, but of course if the tvar is not in the environment
            // anymore, that code path does not know that it needs to do any renaming.
            if (!new_tvar) {
                new_tvar = (jl_value_t*)jl_new_typevar(vb.var->name, vb.lb, vb.ub);
                if (outermost != NULL)
                    push_innervar(outermost, new_tvar);
            }
            if (ub_has_var)
                btemp->ub = jl_substitute_var(btemp->ub, old_tvar, (jl_value_t*)new_tvar);
            if (lb_has_var)
                btemp->lb = jl_substitute_var(btemp->lb, old_tvar, (jl_value_t*)new_tvar);
        }

        if (new_tvar && btemp->innervars != NULL) {
            jl_array_t *innervars = btemp->innervars;
            JL_GC_PUSH1(&innervars);
            for (size_t i = 0; i < jl_array_nrows(innervars); i++) {
                jl_tvar_t *ivar = (jl_tvar_t*)jl_array_ptr_ref(innervars, i);
                jl_value_t *lb = NULL;
                jl_value_t *ub = NULL;
                JL_GC_PUSH2(&lb, &ub);
                if (jl_has_typevar(ivar->lb, old_tvar)) {
                    lb = ivar->lb;
                    lb = jl_substitute_var(lb, old_tvar, (jl_value_t*)new_tvar);
                    jl_gc_write((jl_value_t*)ivar, ivar->lb, jl_value_t, lb);
                }
                if (jl_has_typevar(ivar->ub, old_tvar)) {
                    ub = ivar->ub;
                    ub = jl_substitute_var(ub, old_tvar, (jl_value_t*)new_tvar);
                    jl_gc_write((jl_value_t*)ivar, ivar->ub, jl_value_t, ub);
                }
                JL_GC_POP();
            }
            JL_GC_POP();
        }
    }

    // fill variable values into `envout` up to `envsz`
    if (R && ans && e->envidx < e->envsz) {
        jl_value_t *lb = widened_lb;
        if (vb.pinned && has_existential_typevar(vb.lb, e) && !has_env_typevar(vb.ub, e))
            lb = vb.ub;
        // A var bound only through another variable's declared bounds (BOUND_PROXY)
        // need not be pinned by every call: matching `Type{<:Tuple{Vararg{E}}}`
        // against `Type{S} where S<:NInt` reaches `E` through `S`'s bound, but the
        // `S = Tuple{}` member leaves `E` unbound. So its retained covariant
        // occurrence count must not mark it defined. A fixed prefix on the left,
        // however, is present in every concrete member even when the tuple tail
        // length is free, so a statically constraining right-side element at that
        // position records `lb_required` while matching that tuple element.
        int eff_constrained = (vb.occurs_inv ||
            (cov_count(&vb) && u->var->lb == jl_bottom_type &&
             (vb.lb_certainty > BOUND_PROXY || vb.lb_required)));
        jl_value_t *val = subtype_unionall_envout_value(t, u, e, &vb, lb, &new_tvar,
                                                        eff_constrained);
        jl_value_t *oldval = e->envout[e->envidx];
        // if we try to assign different variable values (due to checking
        // multiple union members), consider the value unknown. Use AND
        // semantics on the `constrained` flag across iterations: the var is
        // constrained only if every iteration (i.e., every LHS union branch)
        // pinned it.
        if (oldval && !jl_egal(oldval, val)) {
            // Distinct spellings may still pin the same value: a plain value in
            // one branch, a pinned uncertainty marker (with its own fresh
            // typevar) in another. When both branches pin egal values, keep
            // the weaker (`==`-pinned marker) spelling rather than degrading
            // the variable to unbound.
            jl_value_t *oldrep = jl_sparam_defined_value(oldval);
            jl_value_t *newrep = jl_sparam_defined_value(val);
            if (oldrep != NULL && newrep != NULL && jl_egal(oldrep, newrep)) {
                if (!jl_is_svec(oldval))
                    e->envout[e->envidx] = val;
                // else keep oldval, which is already the marker spelling
            }
            else {
                int old_iter_constrained;
                if (jl_is_svec(oldval) && jl_svec_len((jl_svec_t*)oldval) == 2)
                    old_iter_constrained = jl_svecref(oldval, 1) == jl_true;
                else
                    old_iter_constrained = 1; // oldval is a concrete value: iter pinned var
                int new_iter_constrained;
                if (jl_is_svec(val) && jl_svec_len((jl_svec_t*)val) == 2)
                    new_iter_constrained = jl_svecref(val, 1) == jl_true;
                else
                    new_iter_constrained = 1;
                e->envout[e->envidx] = wrap_tvar_env((jl_value_t*)u->var,
                                                     old_iter_constrained && new_iter_constrained);
            }
        }
        else
            e->envout[e->envidx] = val;
        // TODO: substitute the value (if any) of this variable into previous envout entries
    }

    JL_GC_POP();
    return ans;
}
```
-/
def subtypeUnionall (n : Nat) (T : Types) (t u : Val) (R : Bool) (param : ParamPos) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut u ← unaliasUnionall n T u
    if ← mayCaptureFreeVar t u.uaVar then u ← renameUnionall n T (subOps n T) u
    let .unionall _ _ _ _ body := u | throw "subtype_unionall: not a UnionAll"
    let i := (← get).vars.size
    let v := u.uaVar
    let vb : VarBinding := { var := v, lb := v.tvLb, ub := v.tvUb, existential := R, depth0 := (← get).invdepth, body := body }
    modify fun e => { e with vars := e.vars.push vb }
    let mut ans ← if R then do
      modify fun e => { e with envidx := e.envidx + 1 }
      let ans ← subtype n T t body param
      modify fun e => { e with envidx := e.envidx - 1 }
      pure ans
    else do
      if !(← get).intersection && vb.lb == .bottom && vb.ub.isUnion then
        if !(← vbBodyOccursInv n i) then
          if ← varOccursCovariantOnly n body v true then
            let ub ← pickUnionElement n vb.ub false
            changeBinding i fun b => { b with ub := ub }
      subtype n T body t param
    let vb ← getBinding i
    let noinv := !(← vbBodyOccursInv n i)
    let diagonal := covCount vb > 1 && noinv
    let widenLb := vb.occursInv == 0 && (diagonal || (vb.occursCov == 1 && vb.covDiag == 0))
    let isIsect := (← get).intersection
    let widenedLb ← if widenLb then widenTypeIfConcrete n T vb.lb [] isIsect else pure vb.lb
    let checkConcrete ← if vb.concrete then pure true else if diagonal then isLeafTypevar n T v else pure false
    if ans && checkConcrete then
      let concreteLb := if diagonal then widenedLb else vb.lb
      if vb.concrete && !diagonal && !(← isLeafBound n T vb.ub) then ans := false
      else if vb.lb.isTypevar then
        if let some j ← lookup vb.lb then changeBinding j fun b => { b with concrete := true }
      else if !(← isLeafBound n T concreteLb) then ans := false
    let mut vb ← getBinding i
    modify fun e => { e with vars := e.vars.pop }
    if !ans then return false
    let ub0 ← resolveVal n vb.ub
    vb := { vb with ub := (← widenIntersect n T ub0) }
    let mut newTvar := if vb.lb == vb.ub then some vb.lb else none
    for j in (List.range i).reverse do
      let b ← getBinding j
      if !b.existential then continue
      let ubHasVar := b.ub.hasTypevar vb.var
      let lbHasVar := b.lb.hasTypevar vb.var
      if ubHasVar || lbHasVar then
        if b.depth0 != vb.depth0 && vb.lb != vb.ub then return false
        changeBinding j fun b => { b with taintedInner := true }
        if newTvar.isNone then
          let .typevar _ nm _ _ := vb.var | throw "subtype_unionall: not a TypeVar"
          let nv ← newTypevar nm vb.lb vb.ub
          newTvar := some nv
          if i > 0 then pushInnervar 0 nv
        let some nv := newTvar | throw "unreachable: new_tvar is NULL"
        if ubHasVar then
          let ub0 ← resolveVal n (← getBinding j).ub
          let ub ← substituteVar n T (subOps n T) ub0 vb.var nv
          changeBinding j fun b => { b with ub := ub }
        if lbHasVar then
          let lb0 ← resolveVal n (← getBinding j).lb
          let lb ← substituteVar n T (subOps n T) lb0 vb.var nv
          changeBinding j fun b => { b with lb := lb }
      if let some nv := newTvar then
        let inners ← innerVars (← getBinding j)
        for ivar in inners do
          let ivar ← resolveVal n ivar
          let .typevar id nm ilb iub := ivar | throw "innervars: not a TypeVar"
          let lb ← if ilb.hasTypevar vb.var then substituteVar n T (subOps n T) ilb vb.var nv else pure ilb
          let ub ← if iub.hasTypevar vb.var then substituteVar n T (subOps n T) iub vb.var nv else pure iub
          if lb != ilb || ub != iub then
            modify fun e => { e with typevars := (id, .typevar id nm lb ub) :: e.typevars }
    return ans
termination_by structural n

/-- `check_vararg_length` with intersection branches enabled (`src/subtype.c:2124-2139`).

Julia source: src/subtype.c:2124-2139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int check_vararg_length(jl_value_t *v, ssize_t n, jl_stenv_t *e) JL_CANSAFEPOINT
{
    jl_value_t *N = jl_unwrap_vararg_num(v);
    // only do the check if N is free in the tuple type's last parameter
    if (N) {
        jl_value_t *nn = jl_box_long(n);
        JL_GC_PUSH1(&nn);
        e->invdepth++;
        int ans = subtype(nn, N, e, PARAM_INVARIANT) && subtype(N, nn, e, PARAM_NONE);
        e->invdepth--;
        JL_GC_POP();
        if (!ans)
            return 0;
    }
    return 1;
}
```
-/
def checkVarargLength (n : Nat) (T : Types) (v : Val) (len : Int) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let some N := v.varargN? then
      modify fun e => { e with invdepth := e.invdepth + 1 }
      let mut ans ← subtype n T (.long len) N .invariant
      if ans then ans ← subtype n T N (.long len) .none
      modify fun e => { e with invdepth := e.invdepth - 1 }
      if !ans then return false
    return true
termination_by structural n

/-- `subtype_tuple_varargs` with intersection branches enabled (`src/subtype.c:2143-2294`).

Julia source: src/subtype.c:2143-2294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_tuple_varargs(
    jl_vararg_t *vtx, jl_vararg_t *vty,
    jl_value_t *lastx, jl_value_t *lasty,
    size_t vx, size_t vy, size_t x_reps,
    jl_stenv_t *e, jl_param_pos_t param) JL_CANSAFEPOINT
{
    jl_value_t *xp0 = jl_unwrap_vararg(vtx); jl_value_t *xp1 = jl_unwrap_vararg_num(vtx);
    jl_value_t *yp0 = jl_unwrap_vararg(vty); jl_value_t *yp1 = jl_unwrap_vararg_num(vty);

    jl_varbinding_t *xlv = NULL, *ylv = NULL;
    if (xp1 && jl_is_typevar(xp1))
        xlv = lookup(e, (jl_tvar_t*)xp1);
    if (yp1 && jl_is_typevar(yp1))
        ylv = lookup(e, (jl_tvar_t*)yp1);

    int8_t max_offsetx = xlv ? xlv->max_offset : 0;
    int8_t max_offsety = ylv ? ylv->max_offset : 0;

    jl_value_t *xl = xlv ? xlv->lb : xp1;
    jl_value_t *yl = ylv ? ylv->lb : yp1;

    if (!xp1) {
        // Unconstrained on the left, constrained on the right
        if (yl && jl_is_long(yl))
            return 0;
    }
    else {
        if (jl_is_long(xl)) {
            if (jl_unbox_long(xl) + 1 == vx) {
                // LHS is exhausted. We're a subtype if the RHS is either
                // exhausted as well or unbounded (in which case we need to
                // set it to 0).
                if (yl) {
                    if (jl_is_long(yl)) {
                        return jl_unbox_long(yl) + 1 == vy;
                    }
                } else {
                    // We can skip the subtype check, but we still
                    // need to make sure to constrain the length of y
                    // to 0.
                    goto constrain_length;
                }
            }
        }
    }
    {
        int x_same = vx > 1 || (lastx && obviously_egal(xp0, lastx));
        int y_same = vy > 1 || (lasty && obviously_egal(yp0, lasty));
        // keep track of number of consecutive identical subtyping
        x_reps = y_same && x_same ? x_reps + 1 : 1;
        if (x_reps > 2) {
            // an identical type on the left doesn't need to be compared to the same
            // element type on the right more than twice.
        }
        else if (x_same && e->Runions.depth == 0 && y_same &&
            !jl_has_free_typevars(xp0) && !jl_has_free_typevars(yp0)) {
            // fast path for repeated elements
        }
        else if ((e->Runions.depth == 0 ? !jl_has_free_typevars(xp0) : jl_is_concrete_type(xp0)) && !jl_has_free_typevars(yp0)) {
            // fast path for separable sub-formulas
            if (!jl_subtype(xp0, yp0))
                return 0;
        }
        else {
            // in Vararg{T1} <: Vararg{T2}, need to check subtype twice to
            // simulate the possibility of multiple arguments, which is needed
            // to implement the diagonal rule correctly.
            if (!subtype(xp0, yp0, e, param)) return 0;
            if (x_reps < 2 && !subtype(xp0, yp0, e, PARAM_COVARIANT)) return 0;
        }
    }
constrain_length:
    if (!yp1) {
        return 1;
    }
    if (!xp1) {
        jl_value_t *yl = yp1;
        jl_varbinding_t *ylv = NULL;
        if (jl_is_typevar(yl)) {
            ylv = lookup(e, (jl_tvar_t*)yl);
            if (ylv)
                yl = ylv->lb;
        }
        if (jl_is_long(yl)) {
            // The length of the x tuple is unconstrained, but the
            // length of the y tuple is now fixed (this could have happened
            // as a result of the subtype call above).
            return 0;
        }

        if (ylv) {
            if (ylv->depth0 != e->invdepth ||
                ylv->lb != jl_bottom_type ||
                ylv->ub != (jl_value_t *)jl_any_type)
                return 0;
            ylv->intvalued = 1;
        }
        // set lb to Any. Since `intvalued` is set, we'll interpret that
        // appropriately.
        e->invdepth++;
        int ans = subtype((jl_value_t*)jl_any_type, yp1, e, PARAM_INVARIANT);
        if (ylv && !ylv->intersected)
            ylv->max_offset = max_offsety;
        e->invdepth--;
        return ans;
    }

    // Vararg{T,N} <: Vararg{T2,N2}; equate N and N2
    e->invdepth++;
    JL_GC_PUSH2(&xp1, &yp1);
    int ans;
    jl_varbinding_t *bxp1 = jl_is_typevar(xp1) ? lookup(e, (jl_tvar_t *)xp1) : NULL;
    jl_varbinding_t *byp1 = jl_is_typevar(yp1) ? lookup(e, (jl_tvar_t *)yp1) : NULL;
    if (bxp1) {
        if (bxp1->intvalued == 0)
            bxp1->intvalued = 1;
        assert(bxp1->lb); // make static analyzer happy
        if (jl_is_long(bxp1->lb))
            xp1 = bxp1->lb;
    }
    if (byp1) {
        if (byp1->intvalued == 0)
            byp1->intvalued = 1;
        assert(byp1->lb); // make static analyzer happy
        if (jl_is_long(byp1->lb))
            yp1 = byp1->lb;
    }
    if (jl_is_long(xp1) && jl_is_long(yp1))
        ans = jl_unbox_long(xp1) - vx == jl_unbox_long(yp1) - vy;
    else {
        if (jl_is_long(xp1) && vx != vy) {
            xp1 = jl_box_long(jl_unbox_long(xp1) + vy - vx);
            vx = vy;
        }
        if (jl_is_long(yp1) && vy != vx) {
            yp1 = jl_box_long(jl_unbox_long(yp1) + vx - vy);
            vy = vx;
        }
        assert(e->Loffset == 0);
        e->Loffset = vx - vy;
        ans = forall_exists_equal(xp1, yp1, e);
        assert(e->Loffset == vx - vy);
        e->Loffset = 0;
    }
    JL_GC_POP();
    if (ylv && !ylv->intersected)
        ylv->max_offset = max_offsety;
    if (xlv && !xlv->intersected)
        xlv->max_offset = max_offsetx;
    e->invdepth--;
    return ans;
}
```
-/
def subtypeTupleVarargs (n : Nat) (T : Types) (vtx vty : Val) (lastx lasty : Option Val)
    (vx0 vy0 reps0 : Nat) (param : ParamPos) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let xp0 := vtx.unwrapVararg
    let mut xp1 := vtx.varargN?
    let yp0 := vty.unwrapVararg
    let mut yp1 := vty.varargN?
    let xlv ← match xp1 with | some x => if x.isTypevar then lookup x else pure none | none => pure none
    let ylv ← match yp1 with | some y => if y.isTypevar then lookup y else pure none | none => pure none
    let maxOffsetx ← match xlv with | some i => do pure (← getBinding i).maxOffset | none => pure 0
    let maxOffsety ← match ylv with | some i => do pure (← getBinding i).maxOffset | none => pure 0
    let xl ← match xlv with | some i => do pure (some (← getBinding i).lb) | none => pure xp1
    let yl ← match ylv with | some i => do pure (some (← getBinding i).lb) | none => pure yp1
    let mut skipChecks := false
    if xp1.isNone then
      if yl.any Val.isLong then return false
    else if let some (.long x) := xl then
      if x + 1 == (vx0 : Int) then
        match yl with
        | some (.long y) => return y + 1 == (vy0 : Int)
        | none => skipChecks := true
        | _ => pure ()
    let mut reps := reps0
    if !skipChecks then
      let xsame ← if vx0 > 1 then pure true else
        match lastx with | some x => obviouslyEgal n T xp0 x | none => pure false
      let ysame ← if vy0 > 1 then pure true else
        match lasty with | some y => obviouslyEgal n T yp0 y | none => pure false
      reps := if xsame && ysame then reps + 1 else 1
      let rzero := (← get).Runions.depth == 0
      if reps > 2 then pure ()
      else if xsame && rzero && ysame && !xp0.hasFreeTypevars && !yp0.hasFreeTypevars then pure ()
      else
        let separable ← if rzero then pure (!xp0.hasFreeTypevars) else isConcreteType T xp0
        if separable && !yp0.hasFreeTypevars then
          if !(← jlSubtype n T xp0 yp0) then return false
        else
          if !(← subtype n T xp0 yp0 param) then return false
          if reps < 2 then if !(← subtype n T xp0 yp0 .covariant) then return false
    let some yp := yp1 | return true
    if xp1.isNone then
      let ylv ← if yp.isTypevar then lookup yp else pure none
      let yl ← match ylv with | some i => do pure (← getBinding i).lb | none => pure yp
      if yl.isLong then return false
      if let some i := ylv then
        let yb ← getBinding i
        if yb.depth0 != (← get).invdepth || yb.lb != .bottom || yb.ub != anyType then return false
        changeBinding i fun b => { b with intvalued := true }
      modify fun e => { e with invdepth := e.invdepth + 1 }
      let ans ← subtype n T anyType yp .invariant
      if let some i := ylv then
        if !(← getBinding i).intersected then changeBinding i fun b => { b with maxOffset := maxOffsety }
      modify fun e => { e with invdepth := e.invdepth - 1 }
      return ans
    modify fun e => { e with invdepth := e.invdepth + 1 }
    let some xp := xp1 | throw "unreachable: xp1 is NULL"
    if xp.isTypevar then
      if let some i ← lookup xp then
        changeBinding i fun b => { b with intvalued := true }
        if (← getBinding i).lb.isLong then xp1 := some (← getBinding i).lb
    if yp.isTypevar then
      if let some i ← lookup yp then
        changeBinding i fun b => { b with intvalued := true }
        if (← getBinding i).lb.isLong then yp1 := some (← getBinding i).lb
    let mut vx := vx0
    let mut vy := vy0
    let mut xp := xp1.getD xp
    let mut yp := yp1.getD yp
    let ans ← match xp, yp with
      | .long x, .long y => pure (x - (vx : Int) == y - (vy : Int))
      | _, _ => do
        if let .long x := xp then
          if vx != vy then xp := .long (x + (vy : Int) - (vx : Int)); vx := vy
        if let .long y := yp then
          if vy != vx then yp := .long (y + (vx : Int) - (vy : Int)); vy := vx
        if (← get).Loffset != 0 then throw "subtype_tuple_varargs: offset assertion"
        modify fun e => { e with Loffset := (vx : Int) - (vy : Int) }
        let ans ← forallExistsEqual n T xp yp
        modify fun e => { e with Loffset := 0 }
        pure ans
    if let some i := ylv then
      if !(← getBinding i).intersected then changeBinding i fun b => { b with maxOffset := maxOffsety }
    if let some i := xlv then
      if !(← getBinding i).intersected then changeBinding i fun b => { b with maxOffset := maxOffsetx }
    modify fun e => { e with invdepth := e.invdepth - 1 }
    return ans
termination_by structural n

/-- `subtype_tuple_tail` with intersection branches enabled (`src/subtype.c:2296-2394`).

Julia source: src/subtype.c:2296-2394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_tuple_tail(jl_datatype_t *xd, jl_datatype_t *yd, int8_t R, jl_stenv_t *e, jl_param_pos_t param) JL_CANSAFEPOINT
{
    size_t lx = jl_nparams(xd);
    size_t ly = jl_nparams(yd);
    size_t i = 0, j = 0, vx = 0, vy = 0, x_reps = 1;
    jl_value_t *lastx = NULL, *lasty = NULL;
    jl_value_t *xi = NULL, *yi = NULL;

    for (;;) {
        if (i < lx) {
            xi = jl_tparam(xd, i);
            if (i == lx-1 && (vx || jl_is_vararg(xi))) {
                vx += 1;
            }
        }

        if (j < ly) {
            yi = jl_tparam(yd, j);
            if (j == ly-1 && (vy || jl_is_vararg(yi))) {
                vy += 1;
            }
        }

        if (i >= lx)
            break;

        int all_varargs = vx && vy;
        if (!all_varargs && vy == 1) {
            if (jl_unwrap_vararg(yi) == (jl_value_t*)jl_any_type) {
                // Tuple{...} <: Tuple{..., Vararg{Any, _}}
                // fast path all the type checks away
                xi = jl_tparam(xd, lx-1);
                if (jl_is_vararg(xi)) {
                    all_varargs = 1;
                    // count up to lx-2 rather than lx-1.
                    vy += lx - i - 1;
                    vx = 1;
                } else {
                    break;
                }
            }
        }

        if (all_varargs) {
            // Tuple{..., Vararg{xi, _}} <: Tuple{..., Vararg{yi, _}}
            return subtype_tuple_varargs(
                (jl_vararg_t*)xi,
                (jl_vararg_t*)yi,
                lastx, lasty,
                vx, vy, x_reps, e, param);
        }

        if (j >= ly)
            return !!vx;

        xi = vx ? jl_unwrap_vararg(xi) : xi;
        yi = vy ? jl_unwrap_vararg(yi) : yi;
        int required_lhs_element = !vx && param == PARAM_COVARIANT;
        int x_same = vx > 1 || (lastx && obviously_egal(xi, lastx));
        int y_same = vy > 1 || (lasty && obviously_egal(yi, lasty));
        // keep track of number of consecutive identical subtyping
        x_reps = y_same && x_same ? x_reps + 1 : 1;
        if (x_reps > 2) {
            // an identical type on the left doesn't need to be compared to the same
            // element type on the right more than twice.
        }
        else if (x_same && e->Runions.depth == 0 &&
            ((y_same && !jl_has_free_typevars(xi) && !jl_has_free_typevars(yi)) ||
             (yi == lastx && !vx && vy && jl_is_concrete_type(xi)))) {
            // fast path for repeated elements
        }
        else if ((e->Runions.depth == 0 ? !jl_has_free_typevars(xi) : jl_is_concrete_type(xi)) && !jl_has_free_typevars(yi)) {
            // fast path for separable sub-formulas
            int sub = jl_subtype(xi, yi);
            if (!sub)
                return 0;
        }
        else {
            int sub = subtype(xi, yi, e, param);
            if (!sub)
                return 0;
        }
        if (required_lhs_element)
            mark_required_tuple_element(e, yi);
        lastx = xi; lasty = yi;
        if (i < lx-1 || !vx)
            i++;
        if (j < ly-1 || !vy)
            j++;
    }

    if (vy && !vx && lx+1 >= ly) {
        // in Tuple{...,tn} <: Tuple{...,Vararg{T,N}}, check (lx+1-ly) <: N
        if (!check_vararg_length(yi, lx+1-ly, e))
            return 0;
    }
    assert((lx + vx == ly + vy) || (vy && (lx >= (vx ? ly : (ly-1)))));
    return 1;
}
```
-/
def subtypeTupleTail (n : Nat) (T : Types) (xd yd : Val) (_R : Bool) (param : ParamPos) :
    STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let lx := xd.nparams
    let ly := yd.nparams
    let mut i := 0
    let mut j := 0
    let mut vx := 0
    let mut vy := 0
    let mut reps := 1
    let mut lastx : Option Val := none
    let mut lasty : Option Val := none
    let mut xi := Val.bottom
    let mut yi := Val.bottom
    let mut finished := false
    for _ in [0:n] do
      if i < lx then
        xi := xd.params[i]!
        if i == lx - 1 && (vx != 0 || xi.isVararg) then vx := vx + 1
      if j < ly then
        yi := yd.params[j]!
        if j == ly - 1 && (vy != 0 || yi.isVararg) then vy := vy + 1
      if i ≥ lx then finished := true; break
      let mut allVarargs := vx != 0 && vy != 0
      if !allVarargs && vy == 1 then
        if yi.unwrapVararg == anyType then
          xi := xd.params[lx - 1]!
          if xi.isVararg then
            allVarargs := true
            vy := vy + lx - i - 1
            vx := 1
          else finished := true; break
      if allVarargs then
        return ← subtypeTupleVarargs n T xi yi lastx lasty vx vy reps param
      if j ≥ ly then return vx != 0
      xi := if vx != 0 then xi.unwrapVararg else xi
      yi := if vy != 0 then yi.unwrapVararg else yi
      let required := vx == 0 && param == .covariant
      let xsame ← if vx > 1 then pure true else
        match lastx with | some x => obviouslyEgal n T xi x | none => pure false
      let ysame ← if vy > 1 then pure true else
        match lasty with | some y => obviouslyEgal n T yi y | none => pure false
      reps := if ysame && xsame then reps + 1 else 1
      let rzero := (← get).Runions.depth == 0
      let mut fastRepeat := false
      if xsame && rzero then
        if ysame && !xi.hasFreeTypevars && !yi.hasFreeTypevars then fastRepeat := true
        else if some yi == lastx && vx == 0 && vy != 0 then fastRepeat ← isConcreteType T xi
      if reps > 2 || fastRepeat then pure ()
      else
        let separable ← if rzero then pure (!xi.hasFreeTypevars) else isConcreteType T xi
        if separable && !yi.hasFreeTypevars then
          if !(← jlSubtype n T xi yi) then return false
        else if !(← subtype n T xi yi param) then return false
      if required then markRequiredTupleElement n T yi
      lastx := some xi
      lasty := some yi
      if i < lx - 1 || vx == 0 then i := i + 1
      if j < ly - 1 || vy == 0 then j := j + 1
    if !finished then outOfBudget
    if vy != 0 && vx == 0 && lx + 1 ≥ ly then
      if !(← checkVarargLength n T yi ((lx : Int) + 1 - (ly : Int))) then return false
    return true
termination_by structural n

/-- `subtype_tuple` with intersection branches enabled (`src/subtype.c:2396-2458`).

Julia source: src/subtype.c:2396-2458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype_tuple(jl_datatype_t *xd, jl_datatype_t *yd, jl_stenv_t *e, jl_param_pos_t param) JL_CANSAFEPOINT
{
    // Check tuple compatibility based on tuple length only (fastpath)
    size_t lx = jl_nparams(xd);
    size_t ly = jl_nparams(yd);

    if (lx == 0 && ly == 0)
        return 1;

    jl_vararg_kind_t vvx = JL_VARARG_NONE;
    jl_vararg_kind_t vvy = JL_VARARG_NONE;
    jl_varbinding_t *xbb = NULL;
    jl_value_t *xva = NULL, *yva = NULL;
    if (lx > 0) {
        xva = jl_tparam(xd, lx-1);
        vvx = jl_vararg_kind(xva);
        if (vvx == JL_VARARG_BOUND)
            xbb = lookup(e, (jl_tvar_t *)jl_unwrap_vararg_num(xva));
    }
    if (ly > 0) {
        yva = jl_tparam(yd, ly-1);
        vvy = jl_vararg_kind(yva);
    }
    if (vvx != JL_VARARG_NONE && vvx != JL_VARARG_INT &&
        (!xbb || !jl_is_long(xbb->lb))) {
        if (vvx == JL_VARARG_UNBOUND || (xbb && !xbb->existential)) {
            // Unbounded on the LHS, bounded on the RHS
            if (vvy == JL_VARARG_NONE || vvy == JL_VARARG_INT)
                return 0;
            else if (lx < ly) // Unbounded includes N == 0
                return 0;
        }
        else if (vvy == JL_VARARG_NONE && !check_vararg_length(xva, ly+1-lx, e)) {
            return 0;
        }
    }
    else {
        size_t nx = lx;
        if (vvx == JL_VARARG_INT)
            nx += jl_vararg_length(xva) - 1;
        else if (xbb && jl_is_long(xbb->lb))
            nx += jl_unbox_long(xbb->lb) - 1;
        else
            assert(vvx == JL_VARARG_NONE);
        size_t ny = ly;
        if (vvy == JL_VARARG_INT)
            ny += jl_vararg_length(yva) - 1;
        else if (vvy != JL_VARARG_NONE)
            ny -= 1;
        if (vvy == JL_VARARG_NONE || vvy == JL_VARARG_INT) {
            if (nx != ny)
                return 0;
        }
        else {
            if (ny > nx)
                return 0;
        }
    }

    if (param == PARAM_NONE) param = PARAM_COVARIANT;
    int ans = subtype_tuple_tail(xd, yd, 0, e, param);
    return ans;
}
```
-/
def subtypeTuple (n : Nat) (T : Types) (xd yd : Val) (param : ParamPos) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let lx := xd.nparams
    let ly := yd.nparams
    if lx == 0 && ly == 0 then return true
    let xva := xd.params.getLast?.getD .bottom
    let yva := yd.params.getLast?.getD .bottom
    let vvx := xva.varargKind
    let vvy := yva.varargKind
    let xbb ← if vvx == .bound then
      match xva.varargN? with | some v => lookup v | none => pure none
      else pure none
    let xb ← match xbb with | some i => do pure (some (← getBinding i)) | none => pure none
    if vvx != .none && vvx != .int && !(xb.any fun b => b.lb.isLong) then
      if vvx == .unbound || xb.any (fun b => !b.existential) then
        if vvy == .none || vvy == .int then return false
        if lx < ly then return false
      else if vvy == .none then
        if !(← checkVarargLength n T xva ((ly : Int) + 1 - (lx : Int))) then return false
    else
      let mut nx : Int := lx
      if vvx == .int then
        let some (.long len) := xva.varargN? | throw "Vararg integer length assertion"
        nx := nx + len - 1
      else if let some b := xb then
        if let .long len := b.lb then nx := nx + len - 1
      let mut ny : Int := ly
      if vvy == .int then
        let some (.long len) := yva.varargN? | throw "Vararg integer length assertion"
        ny := ny + len - 1
      else if vvy != .none then ny := ny - 1
      if vvy == .none || vvy == .int then
        if nx != ny then return false
      else if ny > nx then return false
    subtypeTupleTail n T xd yd false (if param == .none then .covariant else param)
termination_by structural n

/-- `subtype` including `e.intersection` branches (`src/subtype.c:2925-3263`).

Julia source: src/subtype.c:2925-3263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int subtype(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, jl_param_pos_t param)
{
    if (jl_is_uniontype(x)) {
        if (obviously_egal(x, y))
            return 1;
        if (e->Runions.depth == 0 && jl_is_typevar(y) && !jl_has_free_typevars(x)) {
            // Similar to fast path for repeated elements: if there have been no outer
            // unions on the right, and the right side is a typevar, then we can handle the
            // typevar first before picking a union element, under the theory that it may
            // be easy to match or reject this whole union in comparing and setting the lb
            // and ub of the variable binding, without needing to examine each element.
            // However, if x contains any free typevars, then each element with a free
            // typevar must be handled separately from the union of all elements without
            // free typevars, since the typevars presence might lead to those elements
            // getting eliminated (omit_bad_union) or degenerate (Union{Ptr{T}, Ptr}) or
            // combined (Union{T, S} where {T, S <: T}).
            jl_tvar_t *yvar = (jl_tvar_t *)y;
            int yinner = 0;
            jl_varbinding_t *yb = lookup_binding(e, yvar, &yinner);
            while (e->intersection && yb != NULL && yb->lb == yb->ub && jl_is_typevar(yb->lb)) {
                yvar = (jl_tvar_t *)yb->lb;
                yb = lookup_binding(e, yvar, &yinner);
            }
            // Note: `x <: ∃y` performs a local ∀-∃ check between `x` and `yb->ub`.
            // We need to ensure that there's no ∃ typevar as otherwise that check
            // might cause false alarm due to the accumulated env change.
            if (yb == NULL || !yb->existential || !has_existential_typevar(yb->ub, e))
                return subtype_var(yvar, x, e, 1, param, yb, yinner);
        }
        x = pick_union_element(x, e, 0);
    }
    if (jl_is_uniontype(y)) {
        if (obviously_in_union(y, x))
            return 1;
        // The members of a `Type{T}` straddle several kinds, so e.g.
        // `Type{Int} <: Union{DataType,UnionAll}` holds without holding for
        // either branch alone; check the kind cover against the whole union
        // first. This is a closed side query (the cover and `y` have no free
        // vars), so no bindings are recorded and free vars of `T` are not
        // descended into -- matching the kind leaf rule below; a `Type{T'}`
        // branch with `T' == T` -- which covers all of `Type{T}` or nothing --
        // is still found by the per-branch decomposition below.
        if (jl_is_typeeq(x) && union_has_kind_component(y)) {
            jl_value_t *xp0 = typeeq_unpin_tvar(jl_typeeq_T(x));
            // a dangling-var dispatch key has a single tag, found by the
            // per-branch decomposition instead
            if (!jl_is_typevar(xp0) && !typeeq_is_dangling_key(xp0, e, NULL) &&
                typeeq_subtype_kind_cover(xp0, y))
                return 1;
        }
        if (jl_is_unionall(x))
            return subtype_unionall(y, (jl_unionall_t*)x, e, 0, param);
        int ui = 1;
        if (jl_is_typevar(x)) {
            // The `convert(Type{T},T)` pattern, where T is a Union, required changing priority
            // of unions and vars: if matching `typevar <: union`, first try to match the whole
            // union against the variable before trying to take it apart to see if there are any
            // variables lurking inside.
            // note: for forall var, there's no need to split y if it has no free typevars.
            jl_varbinding_t *xx = lookup(e, (jl_tvar_t *)x);
            ui = ((xx && xx->existential) || jl_has_free_typevars(y)) && pick_union_decision(e, 1);
        }
        if (ui == 1)
            y = pick_union_element(y, e, 1);
    }
    // An internal `Intersect` meet node is only ever produced as an existential
    // upper bound, so it can appear on the right (`x <: a ∩ b`) but never on the
    // left. Handling the left case (`a ∩ b <: y`) precisely needs the
    // intersection machinery, so for now we assert it does not arise.
    assert(!jl_is_intersecttype(x));
    if (jl_is_intersecttype(y)) {
        // `x <: a ∩ b`  iff  `x <: a` and `x <: b` (dual to `Union` on the left).
        jl_intersecttype_t *iy = (jl_intersecttype_t*)y;
        return subtype(x, iy->a, e, param) && subtype(x, iy->b, e, param);
    }
    if (jl_is_typevar(x)) {
        if (jl_is_typevar(y)) {
            if (x == y) return 1;
            int xinner = 0, yinner = 0;
            jl_varbinding_t *xx = lookup_binding(e, (jl_tvar_t*)x, &xinner);
            jl_varbinding_t *yy = lookup_binding(e, (jl_tvar_t*)y, &yinner);
            int xfree_singleton = xx == NULL && !xinner;
            int yfree_singleton = yy == NULL && !yinner;
            if (xfree_singleton && yfree_singleton)
                return 0;
            jl_value_t *xub = xx ? xx->ub : xinner ? ((jl_tvar_t*)x)->ub : x;
            jl_value_t *ylb = yy ? yy->lb : yinner ? ((jl_tvar_t*)y)->lb : y;
            if (e->intersection) {
                jl_value_t *xlb = xx ? xx->lb : xinner ? ((jl_tvar_t*)x)->lb : x;
                jl_value_t *yub = yy ? yy->ub : yinner ? ((jl_tvar_t*)y)->ub : y;
                // find equivalence class for typevars during intersection
                if (xub != x && ((jl_is_typevar(xub) && xub == xlb) ||
                                  !jl_is_type(xub)))
                    return subtype(xub, y, e, param);
                if (yub != y && ((jl_is_typevar(yub) && yub == ylb) ||
                                  !jl_is_type(yub)))
                    return subtype(x, yub, e, param);
            }
            int xr = xx && xx->existential;  // treat free variables as "forall" (left)
            int yr = yy && yy->existential;
            if (xr) {
                if (yr) {
                    // TODO: Why is this sound?
                    if (e->intersection && try_subtype_by_bounds(xx->lb, yy->ub, e))
                        return 1;

                    // Both variables are existential. We need to annotate the constraint
                    // on the inner-most variable, so check which one that is.
                    if (var_outside(e, (jl_tvar_t*)x, (jl_tvar_t*)y)) {
                        record_var_occurrence(xx, e, param);
                        return var_gt((jl_tvar_t*)y, x, e, param, yy, yinner);
                    }
                }
                if (yy) record_var_occurrence(yy, e, param);
                return var_lt((jl_tvar_t*)x, y, e, param, xx, xinner);
            }
            else if (yr) {
                if (xx) {
                    record_var_occurrence(xx, e, param);
                    // This encodes the following:
                    //
                    // When we have `∀A ∃B, A <: B`, then the existence of
                    // `B` depends on every particular choice of `A`
                    // (in particular each choice of `A` may have a different
                    // choice of `B`. We encode this as `B->lb = A`.
                    //
                    // However, `∃B ∀A` is different: This requires a single `B`
                    // that works for all `A`. We encode this as `B->lb = A->ub`
                    // (note that A's ub cannot change during the course of the
                    // algorithm). Semantically, at each invariant depth, we push
                    // all universal quantifiers before all existential qualifiers,
                    // so asking which of these cases we're in is equivalent to
                    // asking whether `B`'s depth is greater than `A`'s depth.
                    if (yy && yy->depth0 < xx->depth0)
                        return var_gt((jl_tvar_t*)y, xx->ub, e, param, yy, yinner);
                }
                return var_gt((jl_tvar_t*)y, x, e, param, yy, yinner);
            }
            // check ∀x,y . x<:y
            // the bounds of left-side variables never change, and can only lead
            // to other left-side variables, so using || here is safe.
            if (xfree_singleton)
                return singleton_typevar_subtype((jl_tvar_t*)x, y);
            if (yfree_singleton)
                return subtype_singleton_typevar(xub, (jl_tvar_t*)y);
            // skip <: check during intersection if we meet 2 inner vars,
            // just like var_lt/var_gt.
            if (xinner && yinner && e->intersection)
                return 1;
            return subtype(xub, y, e, param) || subtype(x, ylb, e, param);
        }
        int xinner = 0;
        jl_varbinding_t *xb = lookup_binding(e, (jl_tvar_t*)x, &xinner);
        if (jl_is_unionall(y)) {
            jl_value_t *xub = xb == NULL ? (xinner ? ((jl_tvar_t *)x)->ub : x) : xb->ub;
            if ((xb == NULL ? !xinner || !e->intersection : !xb->existential) && xub != y) {
                // We'd better unwrap `y::UnionAll` eagerly if `x` isa ∀-var.
                // This makes sure the following cases work correct:
                // 1) `∀T <: Union{∃S, SomeType{P}} where {P}`: `S == Any` ==> `S >: T`
                // 2) `∀T <: Union{∀T, SomeType{P}} where {P}`:
                // note: if xub == y we'd better try `subtype_var` as `subtype_left_var`
                // hit `==` based fast path.
                return subtype_unionall(x, (jl_unionall_t*)y, e, 1, param);
            }
        }
        return subtype_var((jl_tvar_t*)x, y, e, 0, param, xb, xinner);
    }
    if (jl_is_typevar(y)) {
        int yinner = 0;
        jl_varbinding_t *yb = lookup_binding(e, (jl_tvar_t*)y, &yinner);
        return subtype_var((jl_tvar_t*)y, x, e, 1, param, yb, yinner);
    }
    if (y == (jl_value_t*)jl_any_type && !jl_has_free_typevars(x))
        return 1;
    if (x == jl_bottom_type && !jl_has_free_typevars(y))
        return 1;
    jl_value_t *ux = jl_unwrap_unionall(x);
    jl_value_t *uy = jl_unwrap_unionall(y);
    if ((x != ux || y != uy) && y != (jl_value_t*)jl_any_type && jl_is_datatype(ux) && jl_is_datatype(uy) &&
        !jl_is_typeeq(ux)) {
        assert(ux);
        if (uy == (jl_value_t*)jl_any_type)
            return 1;
        jl_datatype_t *xd = (jl_datatype_t*)ux, *yd = (jl_datatype_t*)uy;
        while (xd != NULL && xd != jl_any_type && xd->name != yd->name) {
            xd = jl_datatype_compute_super(xd);
        }
        if (xd == jl_any_type)
            return 0;
    }
    // handle forall ("left") vars first
    if (jl_is_unionall(x)) {
        if (x == y && !(e->envidx < e->envsz))
            return 1;
        return subtype_unionall(y, (jl_unionall_t*)x, e, 0, param);
    }
    // fast path: every member of a closed `Type{T}`/`TypeEgal{T}` is a type,
    // so bare `Type` (`Type{T} where T`) on the right always holds -- without
    // opening `Type`'s var. Only when no envout slot remains to be filled
    // (`Type` as the top-level RHS of `jl_subtype_env` must still bind its
    // var into the environment) and `x` is closed (nothing to record).
    if (y == (jl_value_t*)jl_type_type && !(e->envidx < e->envsz) &&
        jl_is_some_Type(x) && !jl_has_free_typevars((jl_value_t*)x))
        return 1;
    if (jl_is_unionall(y))
        return subtype_unionall(x, (jl_unionall_t*)y, e, 1, param);
    if (jl_is_typeegal(x)) {
        // the sole (closed) instance `A` lies in `y` iff `A === B` for `TypeEgal{B}`,
        // iff `A == B` for `Type{B}` (egal implies equal), and otherwise iff the
        // singleton `typeof(A)` is a subtype of `y`
        jl_value_t *A = jl_typeegal_T(x);
        if (jl_is_typeegal(y))
            return jl_egal(A, jl_typeegal_T(y));
        if (jl_is_typeeq(y)) {
            // `A` is egal-known, but `Type{B}` constrains `B` only up to `==`:
            // bindings keep their certainty (the descent of the one object `A`
            // is deterministic), while `A`'s spelling is only `==`-authoritative
            int saved_spell = e->spell_channel;
            if (e->spell_channel > BOUND_EQ)
                e->spell_channel = BOUND_EQ;
            e->invdepth++;
            int ans = forall_exists_equal(A, jl_typeeq_T(y), e);
            e->invdepth--;
            e->spell_channel = saved_spell;
            return ans;
        }
        return subtype(jl_typeof(A), y, e, param);
    }
    if (jl_is_typeegal(y)) {
        // nothing else (besides `Union{}`, already handled) is a subset of `{B}`
        return 0;
    }
    if (x == (jl_value_t*)jl_typeofbottom_type && jl_is_typeeq(y)) {
        jl_value_t *tp0 = jl_typeeq_T(y);
        e->invdepth++;
        int ans = forall_exists_equal(jl_bottom_type, tp0, e);
        e->invdepth--;
        return ans;
    }
    if (jl_is_typeeq(x) && jl_is_typeeq(y)) {
        // Bounds recorded under a covariant (argument-slot) x-side equality wrapper
        // only pin variables up to `==` (an egality-pinned slot arrives as `TypeEgal`
        // above instead). An invariant occurrence is a parameter of a type tag, whose
        // identity pins its parameters exactly, and inside a bounds-consistency
        // check on a closed x-term (`value_descent`) the x-side is a concrete
        // type object rather than an argument-slot spelling, so descent keeps
        // the incoming certainty.
        int saved_channel = e->bound_channel;
        int saved_spell = e->spell_channel;
        if (param != PARAM_INVARIANT && !e->value_descent && e->bound_channel > BOUND_EQ)
            e->bound_channel = BOUND_EQ;
        if (param != PARAM_INVARIANT && !e->value_descent && e->spell_channel > BOUND_EQ)
            e->spell_channel = BOUND_EQ;
        e->invdepth++;
        int ans = forall_exists_equal(jl_typeeq_T(x), jl_typeeq_T(y), e);
        e->invdepth--;
        e->bound_channel = saved_channel;
        e->spell_channel = saved_spell;
        return ans;
    }
    if (jl_is_typeeq(x) && jl_is_datatype(y)) {
        // fast path: every member of a `Type{T}` is a type, so `AnyType` (and
        // `Any`, reachable here when `T` has free vars) need no classification
        if (y == (jl_value_t*)jl_anytype_type || y == (jl_value_t*)jl_any_type)
            return 1;
        jl_value_t *tp0 = typeeq_unpin_tvar(jl_typeeq_T(x));
        if (!jl_is_typevar(tp0)) {
            // a dispatch key for one specific open type object (dangling free
            // typevars, see `typeeq_vars_bound_in_env`) is pinned to that
            // object's type tag
            if (typeeq_is_dangling_key(tp0, e, NULL))
                return subtype(jl_typeof(tp0), y, e, param);
            // `Type{T} <: y` iff `isa(U, y)` for every `U == T`, i.e. iff every
            // possible type tag of such members lies in `y` (#33136, #62141).
            // For example `Type{Int} <: Union{DataType,UnionAll}` but
            // `Type{Int} <: DataType` does not hold: spellings like
            // `Union{Int,S} where Int<:S<:Int` are `==` to `Int` but are not
            // `DataType`s.
            return typeeq_mask_le(typeeq_kind_mask(tp0), y);
        }
        // `TypeEq(T)` for a free typevar `T` is the kind of all types matching
        // `T`'s bounds; every such instance is itself a type, i.e. a `Kind`. So
        // `Type{T} <: y` reduces to `Kind <: y` (in particular `Type === Kind`).
        return subtype((jl_value_t*)jl_anytype_type, y, e, param);
    }
    if (jl_is_datatype(x) && jl_is_typeeq(y) && x != (jl_value_t*)jl_typeofbottom_type) {
        jl_value_t *tp0 = jl_typeeq_T(y);
        if (jl_is_typevar(tp0)) {
            // kinds and `AnyType` are subtypes of `Type` but of no narrower `Type{T'}`,
            // and no `TypeEq` appears in their supertype chains to derive this from; so
            // answer as for `Type <: Type{T}`, at the depth where `Type{T}` occurs (the
            // depth of `x` doesn't matter: it doesn't contain the variable)
            if (!is_kind_or_anytype(x))
                return 0;
            return subtype((jl_value_t*)jl_type_type, y, e, param);
        }
        // `Type{Type{T}}` with an unbounded `T` contains every `Type{X}` value
        // (among others), so a kind contained in `TypeEq` is a subtype
        if (jl_is_typeeq(tp0)) {
            jl_value_t *inner = jl_typeeq_T(tp0);
            if (jl_is_typevar(inner) && ((jl_tvar_t*)inner)->lb == jl_bottom_type &&
                    ((jl_tvar_t*)inner)->ub == (jl_value_t*)jl_any_type)
                return subtype(x, (jl_value_t*)jl_typeeq_type, e, param);
        }
        return 0;
    }
    if (jl_is_datatype(x) && jl_is_datatype(y)) {
        if (x == y) return 1;
        if (y == (jl_value_t*)jl_any_type) return 1;
        jl_datatype_t *xd = (jl_datatype_t*)x, *yd = (jl_datatype_t*)y;
        while (xd != jl_any_type && xd->name != yd->name) {
            jl_datatype_t *xsuper = jl_datatype_compute_super(xd);
            if (xsuper == NULL) {
                assert(xd->parameters && jl_is_typename(xd->name));
                jl_errorf("circular type parameter constraint in definition of %s", jl_symbol_name(xd->name->name));
            }
            xd = xsuper;
        }
        if (xd == jl_any_type) return 0;
        if (xd->name == jl_tuple_typename)
            return subtype_tuple(xd, yd, e, param);
        size_t i, np = jl_nparams(xd);
        int ans = 1;
        e->invdepth++;
        for (i=0; i < np; i++) {
            jl_value_t *xi = jl_tparam(xd, i), *yi = jl_tparam(yd, i);
            if (!(xi == yi || forall_exists_equal(xi, yi, e))) {
                ans = 0; break;
            }
        }
        e->invdepth--;
        return ans;
    }
    if (jl_is_type(y))
        return x == jl_bottom_type;
    if (jl_is_long(x) && jl_is_long(y))
        return jl_unbox_long(x) == jl_unbox_long(y) + e->Loffset;
    return jl_egal(x, y);
}
```
-/
def subtype (n : Nat) (T : Types) (x0 y0 : Val) (param : ParamPos) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut x ← resolveVal n x0
    let mut y ← resolveVal n y0
    if x.isUnion then
      if ← obviouslyEgal n T x y then return true
      if (← get).Runions.depth == 0 && y.isTypevar && !x.hasFreeTypevars then
        let mut yvar := y
        let mut ybIdxAndInner ← lookupBinding yvar
        let mut steps := n
        while (← get).intersection do
          if steps == 0 then outOfBudget
          steps := steps - 1
          let some i := ybIdxAndInner.1 | break
          let b ← getBinding i
          if b.lb == b.ub && b.lb.isTypevar then
            yvar := b.lb
            ybIdxAndInner ← lookupBinding yvar
          else
            break
        let (yb, yinner) := ybIdxAndInner
        let usable ← match yb with
          | none => pure true
          | some i => do
            let b ← getBinding i
            if !b.existential then pure true
            else pure (!(← hasExistentialTypevar b.ub))
        if usable then return ← subtypeVar n T yvar x true param yb yinner
      x ← pickUnionElement n x false
    if y.isUnion then
      if ← obviouslyInUnion n T y x then return true
      if x.isTypeeq then
        if ← unionHasKindComponent n y then
          let xp ← typeeqUnpinTvar n T x.someTypeT
          if !xp.isTypevar then
            if !(← typeeqIsDanglingKey n xp []) then
              if ← typeeqSubtypeKindCover n T xp y then return true
      if x.isUnionall then return ← subtypeUnionall n T y x false param
      let mut ui := true
      if x.isTypevar then
        let xx ← lookup x
        let ex ← match xx with | some i => do pure (← getBinding i).existential | none => pure false
        ui ← if ex || y.hasFreeTypevars then pickUnionDecision true else pure false
      if ui then y ← pickUnionElement n y true
    if x.isIntersect then throw "subtype: Intersect on left assertion"
    if let .intersect a b := y then
      if !(← subtype n T x a param) then return false
      return ← subtype n T x b param
    if x.isTypevar then
      if y.isTypevar then
        if x.tvId == y.tvId then return true
        let (xx, xinner) ← lookupBinding x
        let (yy, yinner) ← lookupBinding y
        let xfree := xx.isNone && !xinner
        let yfree := yy.isNone && !yinner
        if xfree && yfree then return false
        let xb ← match xx with | some i => do pure (some (← getBinding i)) | none => pure none
        let yb ← match yy with | some i => do pure (some (← getBinding i)) | none => pure none
        let xub := xb.map (·.ub) |>.getD (if xinner then x.tvUb else x)
        let ylb := yb.map (·.lb) |>.getD (if yinner then y.tvLb else y)
        if (← get).intersection then
          let xlb := xb.map (·.lb) |>.getD (if xinner then x.tvLb else x)
          let yub := yb.map (·.ub) |>.getD (if yinner then y.tvUb else y)
          if xub != x && ((xub.isTypevar && xub == xlb) || !xub.isType) then
            return ← subtype n T xub y param
          if ylb != y && ((ylb.isTypevar && yub == ylb) || !ylb.isType) then
            return ← subtype n T x ylb param
        let xr := xb.any (·.existential)
        let yr := yb.any (·.existential)
        if xr then
          if yr then
            if let (some xbVal, some ybVal) := (xb, yb) then
              if (← get).intersection then
                if ← trySubtypeByBounds n T xbVal.lb ybVal.ub then
                  return true
            if ← varOutside x y then
              recordVarOccurrence xx param
              return ← varGt n T y x param yy yinner
          recordVarOccurrence yy param
          return ← varLt n T x y param xx xinner
        else if yr then
          if let some xbVal := xb then
            recordVarOccurrence xx param
            if let some ybVal := yb then
              if ybVal.depth0 < xbVal.depth0 then return ← varGt n T y xbVal.ub param yy yinner
          return ← varGt n T y x param yy yinner
        if xfree then return ← singletonTypevarSubtype n x y
        if yfree then return ← subtypeSingletonTypevar n xub y
        if xinner && yinner && (← get).intersection then return true
        if ← subtype n T xub y param then return true
        return ← subtype n T x ylb param
      let (xb, xinner) ← lookupBinding x
      if y.isUnionall then
        let xub ← match xb with
          | some i => do pure (← getBinding i).ub
          | none => pure (if xinner then x.tvUb else x)
        let isIsect := (← get).intersection
        let universal ← match xb with
          | none => pure (!xinner || !isIsect)
          | some i => do pure (!(← getBinding i).existential)
        if universal && xub != y then return ← subtypeUnionall n T x y true param
      return ← subtypeVar n T x y false param xb xinner
    if y.isTypevar then
      let (yb, yinner) ← lookupBinding y
      return ← subtypeVar n T y x true param yb yinner
    if y == anyType && !x.hasFreeTypevars then return true
    if x == .bottom && !y.hasFreeTypevars then return true
    let ux := x.unwrapUnionall
    let uy := y.unwrapUnionall
    if (x != ux || y != uy) && y != anyType && ux.isDatatype && uy.isDatatype && !ux.isTypeeq then
      if uy == anyType then return true
      let mut xd := ux
      let mut finished := false
      for _ in [0:n] do
        if xd == anyType || xd.name? == uy.name? then finished := true; break
        xd ← superOf n T (subOps n T) xd
      if !finished then outOfBudget
      if xd == anyType then return false
    if x.isUnionall then
      if x == y then return true
      return ← subtypeUnionall n T y x false param
    if y == typeType && x.isSomeType && !x.hasFreeTypevars then return true
    if y.isUnionall then return ← subtypeUnionall n T x y true param
    if x.isTypeegal then
      let A := x.someTypeT
      if y.isTypeegal then return ← egal n T A y.someTypeT
      if y.isTypeeq then
        let saved := (← get).spellChannel
        modify fun e => { e with spellChannel := min e.spellChannel .eq, invdepth := e.invdepth + 1 }
        let ans ← forallExistsEqual n T A y.someTypeT
        modify fun e => { e with invdepth := e.invdepth - 1, spellChannel := saved }
        return ans
      return ← subtype n T (typeOf A) y param
    if y.isTypeegal then return false
    if x == typeofbottomType && y.isTypeeq then
      modify fun e => { e with invdepth := e.invdepth + 1 }
      let ans ← forallExistsEqual n T .bottom y.someTypeT
      modify fun e => { e with invdepth := e.invdepth - 1 }
      return ans
    if x.isTypeeq && y.isTypeeq then
      let saved ← get
      if param != .invariant && !saved.valueDescent then
        modify fun e => { e with boundChannel := min e.boundChannel .eq, spellChannel := min e.spellChannel .eq }
      modify fun e => { e with invdepth := e.invdepth + 1 }
      let ans ← forallExistsEqual n T x.someTypeT y.someTypeT
      modify fun e => { e with invdepth := e.invdepth - 1, boundChannel := saved.boundChannel, spellChannel := saved.spellChannel }
      return ans
    if x.isTypeeq && y.isDatatype then
      if y == anytypeType || y == anyType then return true
      let tp ← typeeqUnpinTvar n T x.someTypeT
      if !tp.isTypevar then
        if ← typeeqIsDanglingKey n tp [] then return ← subtype n T (typeOf tp) y param
        let mask ← typeeqKindMask n T tp
        return ← typeeqMaskLe n T mask y
      return ← subtype n T anytypeType y param
    if x.isDatatype && y.isTypeeq && x != typeofbottomType then
      let tp := y.someTypeT
      if tp.isTypevar then
        if !isKindOrAnytype x then return false
        return ← subtype n T typeType y param
      if tp.isTypeeq then
        let inner := tp.someTypeT
        if inner.isTypevar && inner.tvLb == .bottom && inner.tvUb == anyType then
          return ← subtype n T x typeeqType param
      return false
    if x.isDatatype && y.isDatatype then
      if x == y then return true
      if y == anyType then return true
      let mut xd := x
      let mut finished := false
      for _ in [0:n] do
        if xd == anyType || xd.name? == y.name? then finished := true; break
        xd ← superOf n T (subOps n T) xd
      if !finished then outOfBudget
      if xd == anyType then return false
      if xd.isTupleType then return ← subtypeTuple n T xd y param
      let mut ans := true
      modify fun e => { e with invdepth := e.invdepth + 1 }
      for i in [0:xd.nparams] do
        let xi := xd.params[i]!
        let yi := y.params[i]!
        if xi != yi then
          if !(← forallExistsEqual n T xi yi) then ans := false; break
      modify fun e => { e with invdepth := e.invdepth - 1 }
      return ans
    if y.isType then return x == .bottom
    if let (.long a, .long b) := (x, y) then return a == b + (← get).Loffset
    egal n T x y
termination_by structural n

/-- `local_forall_exists_subtype` with intersection branches enabled (`src/subtype.c:3298-3396`).

Julia source: src/subtype.c:3298-3396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int local_forall_exists_subtype(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, jl_param_pos_t param, int limit_slow)
{
    int16_t oldRmore = e->Runions.more;
    int sub;
    // fast-path for #49857
    if (obviously_in_union(y, x))
        return 1;
    int kindx = !jl_has_free_typevars(x);
    int kindy = !jl_has_free_typevars(y);
    if (kindx && kindy)
        return jl_subtype(x, y);
    int has_exists = (!kindx && has_existential_typevar(x, e)) ||
                     (!kindy && has_existential_typevar(y, e));
    if (!has_exists) {
        // We can use ∀_∃_subtype safely for ∃ free inputs.
        // This helps to save some bits in union stack.
        jl_saved_unionstate_t oldRunions; push_unionstate(&oldRunions, &e->Runions);
        e->Lunions.used = e->Runions.used = 0;
        e->Lunions.depth = e->Runions.depth = 0;
        e->Lunions.more = e->Runions.more = 0;
        sub = forall_exists_subtype(x, y, e, param);
        pop_unionstate(&e->Runions, &oldRunions);
        return sub;
    }
    if (is_existential_typevar(x, e) != is_existential_typevar(y, e)) {
        int nvars = current_env_length(e);
        int8_t *cov_entry = (int8_t*)alloca(2 * nvars);
        int8_t *cov_max = cov_entry + nvars;
        get_occurs_cov(e, cov_entry);
        memcpy(cov_max, cov_entry, nvars);
        e->Lunions.used = 0;
        while (1) {
            e->Lunions.more = 0;
            e->Lunions.depth = 0;
            set_occurs_cov(e, cov_entry);
            sub = subtype(x, y, e, param);
            max_occurs_cov(e, cov_max);
            if (!sub || !next_union_state(e, 0))
                break;
        }
        if (sub)
            set_occurs_cov(e, cov_max);
        return sub;
    }
    if (limit_slow == -1)
        limit_slow = kindx || kindy;
    jl_savedenv_t se;
    save_env(e, &se, 1);
    int nvars = current_env_length(e);
    int8_t *cov_entry = (int8_t*)alloca(2 * nvars);
    int8_t *cov_max = cov_entry + nvars;
    get_occurs_cov(e, cov_entry);
    int count, limited = 0, ini_count = 0;
    jl_saved_unionstate_t latestLunions = {0, 0, 0, NULL};
    while (1) {
        count = ini_count;
        get_occurs_cov(e, cov_max);
        if (ini_count == 0)
            e->Lunions.used = 0;
        else
            pop_unionstate(&e->Lunions, &latestLunions);
        while (1) {
            e->Lunions.more = 0;
            e->Lunions.depth = 0;
            if (count < 4) count++;
            set_occurs_cov(e, cov_entry);
            sub = subtype(x, y, e, param);
            max_occurs_cov(e, cov_max);
            if (limit_slow && count == 4)
                limited = 1;
            if (!sub || !next_union_state(e, 0))
                break;
            if (limited || e->Runions.more == oldRmore) {
                // re-save env and freeze the ∃decision for previous ∀Union
                ini_count = count;
                push_unionstate(&latestLunions, &e->Lunions);
                set_occurs_cov(e, cov_max);
                re_save_env(e, &se, 1);
                e->Runions.more = oldRmore;
            }
        }
        if (sub || e->Runions.more == oldRmore)
            break;
        assert(e->Runions.more > oldRmore);
        next_union_state(e, 1);
        restore_env(e, &se, 1); // also restore Rdepth here
        e->Runions.more = oldRmore;
    }
    if (sub)
        set_occurs_cov(e, cov_max);
    if (!sub)
        assert(e->Runions.more == oldRmore);
    else if (e->Runions.more > oldRmore && (limited || env_unchanged(e, &se)))
        // Ignore the rest ∃Union decisions if env is unchanged/limited.
        // As otherwise it might cause combinatorial explosion without making any difference to the result.
        e->Runions.more = oldRmore;
    free_env(&se);
    return sub;
}
```
-/
def localForallExistsSubtype (n : Nat) (T : Types) (x y : Val) (param : ParamPos)
    (limitSlow0 : Int) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let oldRmore := (← get).Runions.more
    if ← obviouslyInUnion n T y x then return true
    let kindx := !x.hasFreeTypevars
    let kindy := !y.hasFreeTypevars
    if kindx && kindy then return ← jlSubtype n T x y
    let ex ← if kindx then pure false else hasExistentialTypevar x
    let ey ← if ex || kindy then pure false else hasExistentialTypevar y
    if !(ex || ey) then
      let oldR := pushUnionstate (← get).Runions
      modify fun e => { e with
        Lunions := { e.Lunions with used := 0, depth := 0, more := 0 }
        Runions := { e.Runions with used := 0, depth := 0, more := 0 } }
      let sub ← forallExistsSubtype n T x y param
      modify fun e => { e with Runions := popUnionstate e.Runions oldR }
      return sub
    let ex ← isExistentialTypevar x
    let ey ← isExistentialTypevar y
    if ex != ey then
      let covEntry ← getOccursCov
      let mut covMax := covEntry
      modify fun e => { e with Lunions := { e.Lunions with used := 0 } }
      for _ in [0:n] do
        modify fun e => { e with Lunions := { e.Lunions with more := 0, depth := 0 } }
        setOccursCov covEntry
        let sub ← subtype n T x y param
        covMax ← maxOccursCov covMax
        let next ← if sub then nextUnionState false else pure false
        if !sub || !next then
          if sub then setOccursCov covMax
          return sub
      outOfBudget
    else
      let limitSlow := if limitSlow0 == -1 then kindx || kindy else limitSlow0 != 0
      let mut se ← saveEnv
      let covEntry ← getOccursCov
      let mut covMax := covEntry
      let mut limited := false
      let mut iniCount := 0
      let mut latestL : SavedUnionState := {}
      let mut sub := false
      let mut finished := false
      for _ in [0:n] do
        let mut count := iniCount
        covMax ← getOccursCov
        if iniCount == 0 then
          modify fun e => { e with Lunions := { e.Lunions with used := 0 } }
        else modify fun e => { e with Lunions := popUnionstate e.Lunions latestL }
        let mut innerFinished := false
        for _ in [0:n] do
          modify fun e => { e with Lunions := { e.Lunions with more := 0, depth := 0 } }
          if count < 4 then count := count + 1
          setOccursCov covEntry
          sub ← subtype n T x y param
          covMax ← maxOccursCov covMax
          if limitSlow && count == 4 then limited := true
          let next ← if sub then nextUnionState false else pure false
          if !sub || !next then innerFinished := true; break
          if limited || (← get).Runions.more == oldRmore then
            iniCount := count
            latestL := pushUnionstate (← get).Lunions
            setOccursCov covMax
            se ← reSaveEnv
            modify fun e => { e with Runions := { e.Runions with more := oldRmore } }
        if !innerFinished then outOfBudget
        if sub || (← get).Runions.more == oldRmore then finished := true; break
        if (← get).Runions.more ≤ oldRmore then throw "local_forall_exists_subtype: union assertion"
        let _ ← nextUnionState true
        restoreEnv se
        modify fun e => { e with Runions := { e.Runions with more := oldRmore } }
      if !finished then outOfBudget
      if sub then setOccursCov covMax
      if sub && (← get).Runions.more > oldRmore then
        let unchanged ← if limited then pure true else envUnchanged n T se
        if unchanged then modify fun e => { e with Runions := { e.Runions with more := oldRmore } }
      return sub
termination_by structural n

/-- `equal_var` including `e.intersection` branches (`src/subtype.c:3398-3459`).

Julia source: src/subtype.c:3398-3459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int equal_var(jl_tvar_t *v, jl_value_t *x, jl_stenv_t *e) JL_CANSAFEPOINT
{
    assert(e->Loffset == 0);
    // Theoretically bounds change would be merged for union inputs.
    // But intersection is not happy as splitting helps to avoid circular env.
    assert(!e->intersection || !jl_is_uniontype(x));
    int innervar = 0;
    jl_varbinding_t *vb = lookup_binding(e, v, &innervar);
    if (e->intersection && vb != NULL && vb->lb == vb->ub && jl_is_typevar(vb->lb))
        return equal_var((jl_tvar_t *)vb->lb, x, e);
    record_var_occurrence(vb, e, PARAM_INVARIANT);
    if (vb == NULL) {
        if (innervar && e->intersection)
            return 1;
        if (innervar)
            return local_forall_exists_subtype(x, v->lb, e, PARAM_INVARIANT, !jl_has_free_typevars(x)) &&
                   local_forall_exists_subtype(v->ub, x, e, PARAM_NONE, 0);
        return x == (jl_value_t*)v;
    }
    if (!vb->existential)
        return local_forall_exists_subtype(x, vb->lb, e, PARAM_INVARIANT, !jl_has_free_typevars(x)) &&
               local_forall_exists_subtype(vb->ub, x, e, PARAM_NONE, 0);
    record_var_pin(vb, x, e, PARAM_INVARIANT);
    if (x != jl_bottom_type && vb->lb_certainty < e->bound_channel)
        vb->lb_certainty = e->bound_channel;
    if (vb->lb == x) {
        if (vb->lb_spell < e->spell_channel)
            vb->lb_spell = e->spell_channel;
        return var_lt(v, x, e, PARAM_NONE, vb, innervar);
    }
    if (!subtype_ccheck(x, vb->ub, e))
        return 0;
    // when the var is pinned (`lb === ub`), `x <= ub` was just checked and a
    // join picking `x` proves `lb <= x`, i.e. `x` respells the same type: keep
    // the existing spelling unless `x`'s is more authoritative (see `lb_spell`)
    int pinned = (vb->lb == vb->ub && vb->lb != jl_bottom_type);
    jl_value_t *lb = simple_join(vb->lb, x);
    JL_GC_PUSH1(&lb);
    if (pinned && lb == x && e->spell_channel <= vb->lb_spell) {
        JL_GC_POP();
        // validate the inclusion the respell path would have checked below,
        // then keep both existing spellings
        if (!subtype_ccheck(vb->lb, x, e))
            return 0;
        return 1;
    }
    if (!e->intersection || !jl_is_typevar(lb) || !reachable_var(lb, v, e)) {
        if (vb->lb != lb) {
            vb->lb = lb;
            vb->lb_spell = e->spell_channel;
        }
    }
    JL_GC_POP();
    if (vb->ub == x)
        return 1;
    if (!subtype_ccheck(vb->lb, x, e))
        return 0;
    // skip `simple_meet` here as we have proven `x <: vb->ub`
    if (!e->intersection || !reachable_var(x, v, e))
        vb->ub = x;
    return 1;
}
```
-/
def equalVar (n : Nat) (T : Types) (v0 x : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if (← get).Loffset != 0 then throw "equal_var: offset assertion"
    let v ← resolveVal n v0
    let (ptr, innervar) ← lookupBinding v
    if (← get).intersection then
      if let some i := ptr then
        let b ← getBinding i
        if b.lb == b.ub && b.lb.isTypevar then
          return ← equalVar n T b.lb x
    recordVarOccurrence ptr .invariant
    let some i := ptr | do
      if innervar && (← get).intersection then return true
      if innervar then
        if !(← localForallExistsSubtype n T x v.tvLb .invariant (if x.hasFreeTypevars then 0 else 1)) then return false
        localForallExistsSubtype n T v.tvUb x .none 0
      else return x == v
    let b ← getBinding i
    if !b.existential then
      if !(← localForallExistsSubtype n T x b.lb .invariant (if x.hasFreeTypevars then 0 else 1)) then return false
      return ← localForallExistsSubtype n T b.ub x .none 0
    recordVarPin i x .invariant
    let channel := (← get).boundChannel
    if x != .bottom then changeBinding i fun b => { b with lbCertainty := max b.lbCertainty channel }
    if b.lb == x then
      let spell := (← get).spellChannel
      changeBinding i fun b => { b with lbSpell := max b.lbSpell spell }
      return ← varLt n T v x .none ptr innervar
    if !(← subtypeCcheck n T x b.ub) then return false
    let b ← getBinding i
    let pinned := b.lb == b.ub && b.lb != .bottom
    let lb0 ← resolveVal n b.lb
    let lb ← simpleJoin n T lb0 x
    let spell := (← get).spellChannel
    if pinned && lb == x && spell ≤ b.lbSpell then
      if !(← subtypeCcheck n T b.lb x) then return false
      return true
    let canSetLb ←
      if !(← get).intersection || !lb.isTypevar then pure true
      else pure (!(← reachableVar n lb v))
    if canSetLb && b.lb != lb then
      changeBinding i fun b => { b with lb := lb, lbSpell := spell }
    let b ← getBinding i
    if b.ub == x then return true
    if !(← subtypeCcheck n T b.lb x) then return false
    let canSetUb ←
      if !(← get).intersection then pure true
      else pure (!(← reachableVar n x v))
    if canSetUb then
      changeBinding i fun b => { b with ub := x }
    return true
termination_by structural n

/-- `forall_exists_equal` including `e.intersection` branches (`src/subtype.c:3461-3507`).

Julia source: src/subtype.c:3461-3507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int forall_exists_equal(jl_value_t *x, jl_value_t *y, jl_stenv_t *e)
{
    if (obviously_egal(x, y)) return 1;

    if ((is_indefinite_length_tuple_type(x) && is_definite_length_tuple_type(y)) ||
        (is_definite_length_tuple_type(x) && is_indefinite_length_tuple_type(y)))
        return 0;

    if (jl_is_datatype(x) && jl_is_datatype(y)) {
        // Fastpath for nested constructor. Skip the unneeded `>:` check.
        // Note: since there is no changes to the environment or union stack implied by `x` or `y`, this will simply forward to calling
        // `forall_exists_equal(xi, yi, e)` on each parameter `(xi, yi)` of `(x, y)`,
        // which means this subtype call will give the same result for `subtype(x, y)` and `subtype(y, x)`.
        jl_datatype_t *xd = (jl_datatype_t*)x, *yd = (jl_datatype_t*)y;
        if (xd->name != yd->name)
            return 0;
        if (xd->name != jl_tuple_typename)
            return subtype(x, y, e, PARAM_INVARIANT);
    }

    if ((jl_is_uniontype(x) && jl_is_uniontype(y))) {
        // For 2 unions, first try a more efficient greedy algorithm that compares the unions
        // componentwise. If failed, `exists_subtype` would memorize that this branch should be skipped.
        // Note: this is valid because the normal path checks `>:` locally.
        if (pick_union_decision(e, 1) == 0) {
            return forall_exists_equal(((jl_uniontype_t *)x)->a, ((jl_uniontype_t *)y)->a, e) &&
                   forall_exists_equal(((jl_uniontype_t *)x)->b, ((jl_uniontype_t *)y)->b, e);
        }
    }

    if (e->Loffset == 0 && jl_is_typevar(y) && jl_is_type(x) && (!e->intersection || !jl_is_uniontype(x))) {
        // Fastpath for Type == TypeVar.
        // Avoid duplicated `<:` check between adjacent `var_gt` and `var_lt`
        return equal_var((jl_tvar_t *)y, x, e);
    }

    jl_saved_unionstate_t oldLunions; push_unionstate(&oldLunions, &e->Lunions);

    int sub = local_forall_exists_subtype(x, y, e, PARAM_INVARIANT, -1);
    if (sub) {
        flip_offset(e);
        sub = local_forall_exists_subtype(y, x, e, PARAM_NONE, 0);
        flip_offset(e);
    }
    pop_unionstate(&e->Lunions, &oldLunions);
    return sub;
}
```
-/
def forallExistsEqual (n : Nat) (T : Types) (x y : Val) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if ← obviouslyEgal n T x y then return true
    if (isIndefiniteLengthTupleType x && isDefiniteLengthTupleType y) ||
        (isDefiniteLengthTupleType x && isIndefiniteLengthTupleType y) then return false
    if x.isDatatype && y.isDatatype then
      if x.name? != y.name? then return false
      if !x.isTupleType then return ← subtype n T x y .invariant
    if let (.union xa xb, .union ya yb) := (x, y) then
      if !(← pickUnionDecision true) then
        if !(← forallExistsEqual n T xa ya) then return false
        return ← forallExistsEqual n T xb yb
    let curEnv ← get
    if curEnv.Loffset == 0 && y.isTypevar && x.isType && (!curEnv.intersection || !x.isUnion) then
      return ← equalVar n T y x
    let oldL := pushUnionstate (← get).Lunions
    let mut sub ← localForallExistsSubtype n T x y .invariant (-1)
    if sub then
      modify fun e => { e with Loffset := -e.Loffset }
      sub ← localForallExistsSubtype n T y x .none 0
      modify fun e => { e with Loffset := -e.Loffset }
    modify fun e => { e with Lunions := popUnionstate e.Lunions oldL }
    return sub
termination_by structural n

/-- `intersect_aside`: intersect in nested union environment, similar to `subtype_ccheck`.

Julia source: src/subtype.c:4318-4364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_aside(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, int depth)
{
    // band-aid for #30335
    if (x == (jl_value_t*)jl_any_type && !jl_is_typevar(y))
        return y;
    if (y == (jl_value_t*)jl_any_type && !jl_is_typevar(x))
        return x;
    // band-aid for #46736 #56040
    if (obviously_in_union(x, y))
        return y;
    if (obviously_in_union(y, x))
        return x;

    // Consistency check for a typevar bound: covariant occurrences inside this
    // call should not accumulate into the surrounding scope's diagonality
    // counter. Save & reset the counters before any env truncation so all
    // vars are captured, and restore after the env is put back.
    int8_t *saved_cov = (int8_t*)alloca(current_env_length(e));
    int nsaved_cov = push_consistency_scope(e, saved_cov);

    jl_varbinding_t *vars = NULL;
    jl_varbinding_t *bbprev = NULL;
    int xinner = 0, yinner = 0;
    jl_varbinding_t *xb = jl_is_typevar(x) ? lookup_binding(e, (jl_tvar_t *)x, &xinner) : NULL;
    jl_varbinding_t *yb = jl_is_typevar(y) ? lookup_binding(e, (jl_tvar_t *)y, &yinner) : NULL;
    int simple_x = jl_is_typevar(x) ? (xb ? !jl_has_free_typevars(xb->ub) : !xinner) : !jl_has_free_typevars(x);
    int simple_y = jl_is_typevar(y) ? (yb ? !jl_has_free_typevars(yb->ub) : !yinner) : !jl_has_free_typevars(y);
    if (simple_x && simple_y && !(xb && yb)) {
        vars = e->vars;
        e->vars = xb ? xb : yb;
        if (e->vars != NULL) {
            bbprev = e->vars->prev;
            e->vars->prev = NULL;
        }
    }
    jl_saved_unionstate_t oldRunions; push_unionstate(&oldRunions, &e->Runions);
    int savedepth = e->invdepth;
    e->invdepth = depth;
    jl_value_t *res = intersect_all(x, y, e);
    e->invdepth = savedepth;
    pop_unionstate(&e->Runions, &oldRunions);
    if (bbprev) e->vars->prev = bbprev;
    if (vars) e->vars = vars;

    pop_consistency_scope(e, saved_cov, nsaved_cov);
    return res;
}
```
-/
def intersectAside (n : Nat) (T : Types) (x0 y0 : Val) (depth : Nat)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let x ← resolveVal n x0
    let y ← resolveVal n y0
    if x == anyType && !y.isTypevar then return y
    if y == anyType && !x.isTypevar then return x
    if ← obviouslyInUnion n T x y then return y
    if ← obviouslyInUnion n T y x then return x
    let savedCov ← pushConsistencyScope
    let (xb, xinner) ← if x.isTypevar then lookupBinding x else pure (none, false)
    let (yb, yinner) ← if y.isTypevar then lookupBinding y else pure (none, false)
    let simpleX ←
      if x.isTypevar then
        match xb with
        | some i => do pure (!(← getBinding i).ub.hasFreeTypevars)
        | none => pure (!xinner)
      else pure (!x.hasFreeTypevars)
    let simpleY ←
      if y.isTypevar then
        match yb with
        | some i => do pure (!(← getBinding i).ub.hasFreeTypevars)
        | none => pure (!yinner)
      else pure (!y.hasFreeTypevars)
    let truncIdx? : Option (Option Nat) :=
      if simpleX && simpleY && !(xb.isSome && yb.isSome) then
        some (if xb.isSome then xb else yb)
      else
        none
    let savedVars := (← get).vars
    if let some keepOpt := truncIdx? then
      match keepOpt with
      | none => modify fun e => { e with vars := #[] }
      | some idx =>
        let b := savedVars[idx]!
        modify fun e => { e with vars := #[b] }
    let oldR := pushUnionstate (← get).Runions
    let savedepth := (← get).invdepth
    modify fun e => { e with invdepth := depth }
    let res ← intersectAll n T x y intersecting
    modify fun e => { e with invdepth := savedepth, Runions := popUnionstate e.Runions oldR }
    if let some keepOpt := truncIdx? then
      match keepOpt with
      | none => modify fun e => { e with vars := savedVars }
      | some idx =>
        let bUpdated := (← get).vars[0]!
        modify fun e => { e with vars := savedVars.set! idx bUpdated }
    popConsistencyScope savedCov
    return res
termination_by structural n

/-- `intersect_union`

Julia source: src/subtype.c:4366-4389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_union(jl_value_t *x, jl_uniontype_t *u, jl_stenv_t *e, int8_t R, jl_param_pos_t param) JL_CANSAFEPOINT
{
    int no_free = !jl_has_free_typevars(x) && !jl_has_free_typevars((jl_value_t*)u);
    if (param == PARAM_INVARIANT || no_free) {
        jl_value_t *a=NULL, *b=NULL;
        JL_GC_PUSH2(&a, &b);
        jl_varbinding_t *vars = NULL;
        if (no_free) {
            vars = e->vars;
            e->vars = NULL;
        }
        jl_saved_unionstate_t oldRunions; push_unionstate(&oldRunions, &e->Runions);
        a = R ? intersect_all(x, u->a, e) : intersect_all(u->a, x, e);
        b = R ? intersect_all(x, u->b, e) : intersect_all(u->b, x, e);
        pop_unionstate(&e->Runions, &oldRunions);
        if (vars) e->vars = vars;
        jl_value_t *i = simple_join(a,b);
        JL_GC_POP();
        return i;
    }
    jl_value_t *choice = pick_union_element((jl_value_t*)u, e, 1);
    // try all possible choices in covariant position; union them all together at the top level
    return R ? intersect(x, choice, e, param) : intersect(choice, x, e, param);
}
```
-/
def intersectUnion (n : Nat) (T : Types) (x u : Val) (R : Bool) (param : ParamPos)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let .union ua ub := u | throw "intersect_union: not a Union"
    let noFree := !x.hasFreeTypevars && !u.hasFreeTypevars
    if param == .invariant || noFree then
      let savedVars := (← get).vars
      if noFree then
        modify fun e => { e with vars := #[] }
      let oldR := pushUnionstate (← get).Runions
      let a ← if R then intersectAll n T x ua intersecting else intersectAll n T ua x intersecting
      let b ← if R then intersectAll n T x ub intersecting else intersectAll n T ub x intersecting
      modify fun e => { e with Runions := popUnionstate e.Runions oldR }
      if noFree then
        modify fun e => { e with vars := savedVars }
      return ← simpleJoin n T a b
    let choice ← pickUnionElement n u true
    if R then intersect n T x choice param intersecting
    else intersect n T choice x param intersecting
termination_by structural n

/-- `intersect_var`

Julia source: src/subtype.c:4606-4748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_var(jl_tvar_t *b, jl_value_t *a, jl_stenv_t *e, int8_t R, jl_param_pos_t param) JL_CANSAFEPOINT
{
    int innervar = 0;
    jl_varbinding_t *bb = lookup_binding(e, b, &innervar);
    if (bb == NULL) {
        if (innervar)
            return R ? intersect_aside(a, b->ub, e, 0) : intersect_aside(b->ub, a, e, 0);
        if (singleton_typevar_subtype(b, a))
            return (jl_value_t*)b;
        if (subtype_singleton_typevar(a, b))
            return a;
        return jl_bottom_type;
    }
    if (reachable_var(bb->lb, b, e) || reachable_var(bb->ub, b, e))
        return a;
    for (jl_typeenv_t *f = e->intersecting; f != NULL; f = f->prev) {
        if (f->var == b && obviously_egal(f->val, a))
            return a;
    }
    if (bb->lb == bb->ub && jl_is_typevar(bb->lb))
        return R ? intersect(a, bb->lb, e, param) : intersect(bb->lb, a, e, param);
    if (!jl_is_type(a) && !jl_is_typevar(a))
        return set_var_to_const(bb, a, e, R);
    if (param == PARAM_INVARIANT) {
        jl_value_t *ub = NULL;
        JL_GC_PUSH1(&ub);
        if (!jl_has_free_typevars(a)) {
            if (R) flip_offset(e);
            int ccheck = intersect_var_ccheck_in_env(bb->lb, bb->ub, a, a, e, !R);
            if (R) flip_offset(e);
            if (!ccheck) {
                JL_GC_POP();
                return jl_bottom_type;
            }
            ub = a;
        }
        else {
            if (jl_subtype(a, bb->ub)) {
                ub = a;
            }
            else {
                int old_triangular = e->triangular;
                // Memorize the side we meet the triangular intersection on.
                e->triangular = R + 1;
                ub = R ? intersect_aside(a, bb->ub, e, bb->depth0) : intersect_aside(bb->ub, a, e, bb->depth0);
                e->triangular = old_triangular;
            }
            jl_savedenv_t se;
            save_env(e, &se, 1);
            int issub = subtype_in_env_existential(bb->lb, ub, e);
            restore_env(e, &se, 1);
            free_env(&se);
            if (!issub) {
                JL_GC_POP();
                return jl_bottom_type;
            }
        }
        if (ub != (jl_value_t*)b) {
            if (jl_has_free_typevars(ub)) {
                if (check_unsat_bound(ub, b, e)) {
                    JL_GC_POP();
                    return jl_bottom_type;
                }
                if (reachable_var(ub, b, e)) {
                    JL_GC_POP();
                    return a;
                }
            }
            bb->ub = ub;
            if ((jl_is_uniontype(ub) && !jl_is_uniontype(a)) ||
                (jl_is_unionall(ub) && !jl_is_unionall(a)))
                ub = (jl_value_t*)b;
            else
                bb->lb = ub;
        }
        JL_GC_POP();
        return ub;
    }
    jl_typeenv_t frame = { b, a, e->intersecting };
    e->intersecting = &frame;
    jl_value_t *ub = R ? intersect_aside(a, bb->ub, e, bb->depth0) : intersect_aside(bb->ub, a, e, bb->depth0);
    e->intersecting = frame.prev;
    if (ub == jl_bottom_type)
        return jl_bottom_type;
    if (e->triangular && ((e->triangular - 1) != R)) {
        if (check_unsat_bound(ub, b, e))
            return jl_bottom_type;
        set_bound(&bb->ub, ub, b, e);
        return (jl_value_t*)b;
    }
    if (bb->constraintkind == 1) {
        if (!jl_is_some_Type(ub) && !jl_is_uniontype(ub) && !jl_is_unionall(ub)) {
            // this branch is a fast path if there are no `Type`s and not needed for correctness
            set_bound(&bb->ub, ub, b, e);
            return (jl_value_t*)b;
        }
        jl_value_t *ub2 = NULL;
        JL_GC_PUSH2(&ub, &ub2);
        ub2 = widen_Type_to_union(ub, bb->ub, e);
        if (ub2 != ub) {
            set_bound(&bb->ub, ub2, b, e);
            if (jl_is_concrete_type(ub2)) {
                // all members widened to the same concrete kind
                JL_GC_POP();
                return ub;
            }
            bb->widened_to_kind = 1;
            JL_GC_POP();
            return (jl_value_t*)b;
        }
        set_bound(&bb->ub, ub, b, e);
        JL_GC_POP();
        return (jl_value_t*)b;
    }
    else if (bb->constraintkind == 0) {
        JL_GC_PUSH1(&ub);
        if (!jl_is_typevar(a) && try_subtype_in_env_nonexistential(bb->ub, a, e)) {
            JL_GC_POP();
            return (jl_value_t*)b;
        }
        JL_GC_POP();
        return ub;
    }
    assert(bb->constraintkind == 2);
    if (ub == a && bb->lb != jl_bottom_type)
        return ub;
    if (jl_egal(bb->ub, bb->lb))
        return ub;
    if (is_leaf_bound(ub))
        set_bound(&bb->lb, ub, b, e);
    // TODO: can we improve this bound by pushing a new variable into the environment
    // and adding that to the lower bound of our variable?
    //jl_value_t *ntv = NULL;
    //JL_GC_PUSH2(&ntv, &ub);
    //if (bb->innervars == NULL)
    //    bb->innervars = jl_alloc_array_1d(jl_array_any_type, 0);
    //ntv = (jl_value_t*)jl_new_typevar(b->name, bb->lb, ub);
    //jl_array_ptr_1d_push(bb->innervars, ntv);
    //jl_value_t *lb = simple_join(b->lb, ntv);
    //JL_GC_POP();
    //bb->lb = lb;
    return ub;
}
```
-/
def intersectVar (n : Nat) (T : Types) (b0 a0 : Val) (R : Bool) (param : ParamPos)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let b ← resolveVal n b0
    let a ← resolveVal n a0
    let (bb, innervar) ← lookupBinding b
    let some idx := bb | do
      if innervar then
        return ← (if R then intersectAside n T a b.tvUb 0 intersecting
                  else intersectAside n T b.tvUb a 0 intersecting)
      if ← singletonTypevarSubtype n b a then
        return b
      if ← subtypeSingletonTypevar n a b then
        return a
      return .bottom
    let vb ← getBinding idx
    if ← reachableVar n vb.lb b then return a
    if ← reachableVar n vb.ub b then return a
    for (fv, fval) in intersecting do
      if fv.tvId == b.tvId then
        if ← obviouslyEgal n T fval a then
          return a
    if vb.lb == vb.ub && vb.lb.isTypevar then
      return ← (if R then intersect n T a vb.lb param intersecting
                else intersect n T vb.lb a param intersecting)
    if !a.isType && !a.isTypevar then
      return ← setVarToConst n T idx a R
    if param == .invariant then
      let mut ub : Val := .bottom
      if !a.hasFreeTypevars then
        if R then flipOffset
        let ccheck ← intersectVarCcheckInEnv n T vb.lb vb.ub a a (!R)
        if R then flipOffset
        if !ccheck then
          return .bottom
        ub := a
      else
        if ← jlSubtype n T a vb.ub then
          ub := a
        else
          let oldTriangular := (← get).triangular
          modify fun e => { e with triangular := if R then 2 else 1 }
          ub ← if R then intersectAside n T a vb.ub vb.depth0 intersecting
                else intersectAside n T vb.ub a vb.depth0 intersecting
          modify fun e => { e with triangular := oldTriangular }
        let se ← saveEnv
        let issub ← subtypeInEnvExistential n T (← getBinding idx).lb ub
        restoreEnv se true
        if !issub then
          return .bottom
      if ub != b then
        if ub.hasFreeTypevars then
          if ← checkUnsatBound n ub b then
            return .bottom
          if ← reachableVar n ub b then
            return a
        changeBinding idx fun x => { x with ub := ub }
        if (ub.isUnion && !a.isUnion) || (ub.isUnionall && !a.isUnionall) then
          ub := b
        else
          changeBinding idx fun x => { x with lb := ub }
      return ub
    let frame := (b, a) :: intersecting
    let vb ← getBinding idx
    let ub ← if R then intersectAside n T a vb.ub vb.depth0 frame
              else intersectAside n T vb.ub a vb.depth0 frame
    if ub == .bottom then
      return .bottom
    let tri := (← get).triangular
    if tri != 0 && ((tri - 1) != (if R then 1 else 0)) then
      if ← checkUnsatBound n ub b then
        return .bottom
      setBoundUb n idx ub b
      return b
    let vb ← getBinding idx
    if vb.constraintkind == 1 then
      if !ub.isSomeType && !ub.isUnion && !ub.isUnionall then
        setBoundUb n idx ub b
        return b
      let ub2 ← widenTypeToUnion n T ub vb.ub
      if ub2 != ub then
        setBoundUb n idx ub2 b
        if ← isConcreteType T ub2 then
          return ub
        changeBinding idx fun x => { x with widenedToKind := true }
        return b
      setBoundUb n idx ub b
      return b
    else if vb.constraintkind == 0 then
      if !a.isTypevar then
        if ← trySubtypeInEnvNonexistential n T (← getBinding idx).ub a then
          return b
      return ub
    if ub == a && (← getBinding idx).lb != .bottom then
      return ub
    let vb ← getBinding idx
    if ← egal n T vb.ub vb.lb then
      return ub
    if ← isLeafBound n T ub then
      setBoundLb n idx ub b
    return ub
termination_by structural n

/-- `intersect_unionall_`

Julia source: src/subtype.c:5242-5323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_unionall_(jl_value_t *t, jl_unionall_t *u, jl_stenv_t *e, int8_t R, jl_param_pos_t param, jl_varbinding_t *vb) JL_CANSAFEPOINT
{
    jl_varbinding_t *btemp = e->vars;
    int envsize = 0;
    while (btemp != NULL) {
        envsize++;
        if (envsize > 120) {
            vb->limited = 1;
            return t;
        }
        btemp = btemp->prev;
    }
    u = unalias_unionall(u, e);
    JL_GC_PUSH1(&u);
    if (may_capture_free_var(t, u->var, e))
        u = jl_rename_unionall(u);
    vb->var = u->var;
    e->vars = vb;
    jl_value_t *res;
    if (R) {
        e->envidx++;
        res = intersect(t, u->body, e, param);
        e->envidx--;
    }
    else {
        res = intersect(u->body, t, e, param);
    }
    vb->concrete |= (cov_count(vb) > 1 && is_leaf_typevar(u->var) &&
                     !vb->body_occurs_inv);

    // handle the "diagonal dispatch" rule, which says that a type var occurring more
    // than once, and only in covariant position, is constrained to concrete types. E.g.
    //  ( Tuple{Int, Int}    <: Tuple{T, T} where T) but
    // !( Tuple{Int, String} <: Tuple{T, T} where T)
    // Then check concreteness by checking that the lower bound is not an abstract type.
    if (res != jl_bottom_type && vb->concrete) {
        if (jl_is_typevar(vb->lb)) {
        }
        else if (!is_leaf_bound(vb->lb)) {
            // in the existential direction a `Type{X}` member of the bound
            // stands for its (nonempty) tag-homogeneous slice, so check the
            // tag-widened bound before rejecting (see `widen_Type_if_concrete`)
            jl_value_t *wlb = widen_Type_if_concrete(vb->lb, e, NULL, 1);
            if (!is_leaf_bound(wlb))
                res = jl_bottom_type;
        }
    }

    // Propagate "deeper-popped tvar leaks into outer bounds" taint upward.
    // See the matching block in `subtype_unionall`.
    for (jl_varbinding_t *btemp = vb->prev; btemp; btemp = btemp->prev) {
        if ((vb->depth0 > btemp->depth0 || vb->tainted_inner) &&
            (jl_has_typevar(btemp->lb, vb->var) || jl_has_typevar(btemp->ub, vb->var))) {
            btemp->tainted_inner = 1;
        }
    }

    e->vars = vb->prev;

    if (res != jl_bottom_type) {
        if (vb->ub == jl_bottom_type && cov_count(vb)) {
            // T=Bottom in covariant position
            res = jl_bottom_type;
        }
        else if (jl_has_typevar(vb->lb, u->var)) {
            // fail on circular constraints
            res = jl_bottom_type;
        }
        else {
            JL_GC_PUSH1(&res);
            vb->ub = omit_bad_union(vb->ub, u->var);
            JL_GC_POP();
            if (vb->ub == jl_bottom_type && vb->ub != vb->lb)
                res = jl_bottom_type;
        }
    }
    if (res != jl_bottom_type)
        // res is rooted by callee
        res = finish_unionall(res, vb, u, e);
    JL_GC_POP();
    return res;
}
```
-/
def intersectUnionall_ (n : Nat) (T : Types) (t u0 : Val) (R : Bool) (param : ParamPos)
    (vb0 : VarBinding) (intersecting : List (Val × Val)) : STM (Val × VarBinding) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if (← get).vars.size > 120 then
      return (t, { vb0 with limited := true })
    let mut u ← unaliasUnionall n T u0
    if ← mayCaptureFreeVar t u.uaVar then
      u ← renameUnionall n T (subOps n T) u
    let v := u.uaVar
    let body := u.uaBody
    let idx := (← get).vars.size
    let vbInit := { vb0 with var := v, body := body }
    modify fun e => { e with vars := e.vars.push vbInit }
    let mut res ←
      if R then do
        modify fun e => { e with envidx := e.envidx + 1 }
        let r ← intersect n T t body param intersecting
        modify fun e => { e with envidx := e.envidx - 1 }
        pure r
      else
        intersect n T body t param intersecting
    let mut vb ← getBinding idx
    let isLeafTv ← isLeafTypevar n T v
    let bodyInv := vb.bodyOccursInv.getD false
    if covCount vb > 1 && isLeafTv && !bodyInv then
      vb := { vb with concrete := true }
      changeBinding idx fun _ => vb
    if res != .bottom && vb.concrete then
      if vb.lb.isTypevar then
        pure ()
      else if !(← isLeafBound n T vb.lb) then
        let wlb ← widenTypeIfConcrete n T vb.lb [] true
        if !(← isLeafBound n T wlb) then
          res := .bottom
    vb ← getBinding idx
    for j in (List.range idx).reverse do
      let btemp ← getBinding j
      if (vb.depth0 > btemp.depth0 || vb.taintedInner) &&
          (btemp.lb.hasTypevar vb.var || btemp.ub.hasTypevar vb.var) then
        changeBinding j fun b => { b with taintedInner := true }
    modify fun e => { e with vars := e.vars.pop }
    if res != .bottom then
      if vb.ub == .bottom && covCount vb != 0 then
        res := .bottom
      else if vb.lb.hasTypevar v then
        res := .bottom
      else
        let ub' ← omitBadUnion n T vb.ub v
        vb := { vb with ub := ub' }
        if vb.ub == .bottom && vb.ub != vb.lb then
          res := .bottom
    if res != .bottom then
      res ← finishUnionall n T res vb
    return (res, vb)
termination_by structural n

/-- `intersect_unionall`

Julia source: src/subtype.c:5389-5461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_unionall(jl_value_t *t, jl_unionall_t *u, jl_stenv_t *e, int8_t R, jl_param_pos_t param) JL_CANSAFEPOINT
{
    jl_value_t *res = NULL;
    jl_savedenv_t se;
    int body_occurs_inv = var_occurs_invariant(u->body, u->var);
    jl_varbinding_t vb;
    memset(&vb, 0, sizeof(vb));
    vb.var = u->var;
    vb.lb = u->var->lb;
    vb.ub = u->var->ub;
    vb.existential = R;
    vb.body_occurs_inv = body_occurs_inv;
    vb.depth0 = e->invdepth;
    vb.prev = e->vars;
    JL_GC_PUSH4(&res, &vb.lb, &vb.ub, &vb.innervars);
    save_env(e, &se, 1);
    int noinv = !body_occurs_inv;
    // Setting constraintkind=1 for covariant var might be invalid if it also occurs in triangular positions.
    if (is_leaf_typevar(u->var) && noinv && always_occurs_cov(u->body, u->var, param) && never_occurs_in_inside_ub(u->body, u->var))
        vb.constraintkind = 1;
    res = intersect_unionall_(t, u, e, R, param, &vb);
    vb.intersected = 1;
    if (vb.limited) {
        // if the environment got too big, avoid tree recursion and propagate the flag
        if (e->vars)
            e->vars->limited = 1;
    }
    else if (res != jl_bottom_type) {
        int constraint1 = vb.constraintkind;
        if (vb.concrete || vb.occurs_inv>1 || (vb.occurs_inv && cov_count(&vb)))
            vb.constraintkind = vb.concrete ? 1 : 2;
        else if (u->var->lb != jl_bottom_type)
            vb.constraintkind = 2;
        else if (cov_count(&vb) && vb.occurs < 2 && noinv && never_occurs_in_inside_ub(u->body, u->var))
            vb.constraintkind = 1;
        int reintersection = constraint1 != vb.constraintkind || vb.concrete || (vb.occurs_inv == 1 && vb.occurs > 1);
        if (reintersection) {
            if (constraint1 == 1) {
                vb.lb = vb.var->lb;
                vb.ub = vb.var->ub;
            }
            restore_env(e, &se, vb.constraintkind == 1 ? 1 : 0);
            vb.occurs = vb.occurs_cov = vb.occurs_inv = vb.cov_diag = 0;
            res = intersect_unionall_(t, u, e, R, param, &vb);
        }
    }
    if (res != jl_bottom_type && vb.constraintkind == 1 && vb.widened_to_kind == 1) {
        // a `Type` was widened to a non-concrete kind union during intersection
        if (cov_count(&vb) > 1) {
            // diagonal: reintersect if able to narrow across positions to a leaf bound
            // otherwise use original (possibly non-precise) bound
            if (is_leaf_bound(vb.ub)) {
                restore_env(e, &se, 1);
                vb.lb = vb.var->lb;
                vb.occurs = vb.occurs_cov = vb.occurs_inv = vb.cov_diag = 0;
                res = intersect_unionall_(t, u, e, R, param, &vb);
            }
        }
        else {
            // actually non-diagonal: reintersect without widening or constraint
            restore_env(e, &se, 1);
            vb.lb = vb.var->lb;
            vb.ub = vb.var->ub;
            vb.constraintkind = 0;
            vb.widened_to_kind = 0;
            vb.occurs = vb.occurs_cov = vb.occurs_inv = vb.cov_diag = 0;
            res = intersect_unionall_(t, u, e, R, param, &vb);
        }
    }
    free_env(&se);
    JL_GC_POP();
    return res;
}
```
-/
def intersectUnionall (n : Nat) (T : Types) (t u : Val) (R : Bool) (param : ParamPos)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let uvar := u.uaVar
    let ubody := u.uaBody
    let bodyOccursInv ← varOccursInvariant n ubody uvar
    let mut vb : VarBinding := {
      var := uvar
      lb := uvar.tvLb
      ub := uvar.tvUb
      existential := R
      bodyOccursInv := some bodyOccursInv
      depth0 := (← get).invdepth
      body := ubody
    }
    let se ← saveEnv
    let noinv := !bodyOccursInv
    if (← isLeafTypevar n T uvar) && noinv then
      if ← alwaysOccursCov n ubody uvar param then
        if ← neverOccursInInsideUb n ubody uvar then
          vb := { vb with constraintkind := 1 }
    let (res0, vb1) ← intersectUnionall_ n T t u R param vb intersecting
    let mut res := res0
    vb := { vb1 with intersected := true }
    if vb.limited then
      let sz := (← get).vars.size
      if sz > 0 then
        changeBinding (sz - 1) fun b => { b with limited := true }
    else if res != .bottom then
      let constraint1 := vb.constraintkind
      if vb.concrete || vb.occursInv > 1 || (vb.occursInv != 0 && covCount vb != 0) then
        vb := { vb with constraintkind := if vb.concrete then 1 else 2 }
      else if uvar.tvLb != .bottom then
        vb := { vb with constraintkind := 2 }
      else if covCount vb != 0 && vb.occurs < 2 && noinv then
        if ← neverOccursInInsideUb n ubody uvar then
          vb := { vb with constraintkind := 1 }
      let reintersection :=
        constraint1 != vb.constraintkind || vb.concrete || (vb.occursInv == 1 && vb.occurs > 1)
      if reintersection then
        if constraint1 == 1 then
          vb := { vb with lb := vb.var.tvLb, ub := vb.var.tvUb }
        restoreEnv se (vb.constraintkind == 1)
        vb := { vb with occurs := 0, occursCov := 0, occursInv := 0, covDiag := 0 }
        let (res2, vb2) ← intersectUnionall_ n T t u R param vb intersecting
        res := res2
        vb := { vb2 with intersected := true }
    if res != .bottom && vb.constraintkind == 1 && vb.widenedToKind then
      if covCount vb > 1 then
        if ← isLeafBound n T vb.ub then
          restoreEnv se true
          vb := { vb with lb := vb.var.tvLb, occurs := 0, occursCov := 0, occursInv := 0, covDiag := 0 }
          let (res3, vb3) ← intersectUnionall_ n T t u R param vb intersecting
          res := res3
          vb := vb3
      else
        restoreEnv se true
        vb := { vb with
          lb := vb.var.tvLb, ub := vb.var.tvUb,
          constraintkind := 0, widenedToKind := false,
          occurs := 0, occursCov := 0, occursInv := 0, covDiag := 0
        }
        let (res3, vb3) ← intersectUnionall_ n T t u R param vb intersecting
        res := res3
        vb := vb3
    return res
termination_by structural n

/-- `intersect_vararg_length`: check `n = (length of vararg type v)`.

Julia source: src/subtype.c:5466-5479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int intersect_vararg_length(jl_value_t *v, ssize_t n, jl_stenv_t *e, int8_t R) JL_CANSAFEPOINT
{
    jl_value_t *N = jl_unwrap_vararg_num(v);
    // only do the check if N is free in the tuple type's last parameter
    if (N && jl_is_typevar(N)) {
        jl_value_t *len = jl_box_long(n);
        JL_GC_PUSH1(&len);
        jl_value_t *il = R ? intersect_invariant(len, N, e) : intersect_invariant(N, len, e);
        JL_GC_POP();
        if (il == NULL || il == jl_bottom_type)
            return 0;
    }
    return 1;
}
```
-/
def intersectVarargLength (n : Nat) (T : Types) (v : Val) (len : Int) (R : Bool)
    (intersecting : List (Val × Val)) : STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if let some nv := v.varargN? then
      if nv.isTypevar then
        let lenVal := Val.long len
        let il? ← if R then intersectInvariant n T lenVal nv intersecting
                  else intersectInvariant n T nv lenVal intersecting
        match il? with
        | none | some .bottom => return false
        | some _ => return true
    return true
termination_by structural n

/-- `intersect_varargs`

Julia source: src/subtype.c:5481-5561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_varargs(jl_vararg_t *vmx, jl_vararg_t *vmy, ssize_t offset, jl_stenv_t *e, jl_param_pos_t param) JL_CANSAFEPOINT
{
    // Vararg: covariant in first parameter, invariant in second
    jl_value_t *xp1=jl_unwrap_vararg(vmx), *xp2=jl_unwrap_vararg_num(vmx),
                *yp1=jl_unwrap_vararg(vmy), *yp2=jl_unwrap_vararg_num(vmy);
    // in Vararg{T1} <: Vararg{T2}, need to check subtype twice to
    // simulate the possibility of multiple arguments, which is needed
    // to implement the diagonal rule correctly.
    if (intersect(xp1, yp1, e, param == PARAM_NONE ? PARAM_COVARIANT : param) == jl_bottom_type)
        return jl_bottom_type;
    jl_value_t *i2=NULL, *ii = intersect(xp1, yp1, e, PARAM_COVARIANT);
    if (ii == jl_bottom_type)
        return jl_bottom_type;
    if (!xp2 && !yp2) {
        if (obviously_egal(xp1, ii))
            ii = (jl_value_t*)vmx;
        else if (obviously_egal(yp1, ii))
            ii = (jl_value_t*)vmy;
        else {
            JL_GC_PUSH1(&ii);
            ii = (jl_value_t*)jl_wrap_vararg(ii, NULL, 1, 0);
            JL_GC_POP();
        }
        return ii;
    }
    JL_GC_PUSH2(&ii, &i2);
    assert(e->Loffset == 0);
    e->Loffset = offset;
    jl_varbinding_t *xb = NULL, *yb = NULL;
    int8_t max_offsetx = 0, max_offsety = 0;
    if (xp2) {
        assert(jl_is_typevar(xp2));
        xb = lookup(e, (jl_tvar_t*)xp2);
        if (xb) xb->intvalued = 1;
        if (xb) max_offsetx = xb->max_offset;
        if (!yp2)
            i2 = bound_var_below((jl_tvar_t*)xp2, xb, e, 0);
    }
    if (yp2) {
        assert(jl_is_typevar(yp2));
        yb = lookup(e, (jl_tvar_t*)yp2);
        if (yb) yb->intvalued = 1;
        if (yb) max_offsety = yb->max_offset;
        if (!xp2)
            i2 = bound_var_below((jl_tvar_t*)yp2, yb, e, 1);
    }
    if (xp2 && yp2) {
        // Vararg{T,N} <: Vararg{T2,N2}; equate N and N2
        i2 = intersect_invariant(xp2, yp2, e);
        if (i2 == NULL || i2 == jl_bottom_type || (jl_is_long(i2) && jl_unbox_long(i2) < 0) ||
            !((jl_is_typevar(i2) && ((jl_tvar_t*)i2)->lb == jl_bottom_type &&
                ((jl_tvar_t*)i2)->ub == (jl_value_t*)jl_any_type) || jl_is_long(i2))) {
            i2 = jl_bottom_type;
        }
    }
    assert(e->Loffset == offset);
    e->Loffset = 0;
    if (i2 == jl_bottom_type) {
        ii = (jl_value_t*)jl_bottom_type;
    }
    else {
        if (xb && !xb->intersected) {
            xb->max_offset = max_offsetx;
            if (offset > xb->max_offset && xb->max_offset >= 0)
                xb->max_offset = offset > 32 ? 32 : offset;
        }
        if (yb && !yb->intersected) {
            yb->max_offset = max_offsety;
            if (-offset > yb->max_offset && yb->max_offset >= 0)
                yb->max_offset = -offset > 32 ? 32 : -offset;
        }
        if (xp2 && obviously_egal(xp1, ii) && obviously_egal(xp2, i2))
            ii = (jl_value_t*)vmx;
        else if (yp2 && obviously_egal(yp1, ii) && obviously_egal(yp2, i2))
            ii = (jl_value_t*)vmy;
        else
            ii = (jl_value_t*)jl_wrap_vararg(ii, i2, 1, 0);
    }
    JL_GC_POP();
    return ii;
}
```
-/
def intersectVarargs (n : Nat) (T : Types) (vmx vmy : Val) (offset : Int) (param : ParamPos)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let xp1 := vmx.unwrapVararg
    let xp2 := vmx.varargN?
    let yp1 := vmy.unwrapVararg
    let yp2 := vmy.varargN?
    let p1 := if param == .none then .covariant else param
    if (← intersect n T xp1 yp1 p1 intersecting) == .bottom then
      return .bottom
    let ii ← intersect n T xp1 yp1 .covariant intersecting
    if ii == .bottom then
      return .bottom
    if xp2.isNone && yp2.isNone then
      if ← obviouslyEgal n T xp1 ii then
        return vmx
      else if ← obviouslyEgal n T yp1 ii then
        return vmy
      else
        let some va ← wrapVararg n T (subOps n T) (some ii) none true 0
          | return .bottom
        return va
    modify fun e => { e with Loffset := offset }
    let mut xb : Option Nat := none
    let mut yb : Option Nat := none
    let mut maxOffsetx : Int := 0
    let mut maxOffsety : Int := 0
    let mut i2 : Val := .bottom
    if let some x2 := xp2 then
      xb ← lookup x2
      if let some idx := xb then
        maxOffsetx := (← getBinding idx).maxOffset
        changeBinding idx fun b => { b with intvalued := true }
      if yp2.isNone then
        i2 ← boundVarBelow x2 xb false
    if let some y2 := yp2 then
      yb ← lookup y2
      if let some idx := yb then
        maxOffsety := (← getBinding idx).maxOffset
        changeBinding idx fun b => { b with intvalued := true }
      if xp2.isNone then
        i2 ← boundVarBelow y2 yb true
    if let (some x2, some y2) := (xp2, yp2) then
      match ← intersectInvariant n T x2 y2 intersecting with
      | none => i2 := .bottom
      | some iv =>
        let badLong := match iv with | .long k => k < 0 | _ => false
        let validShape := (iv.isTypevar && iv.tvLb == .bottom && iv.tvUb == anyType) || iv.isLong
        if iv == .bottom || badLong || !validShape then
          i2 := .bottom
        else
          i2 := iv
    modify fun e => { e with Loffset := 0 }
    if i2 == .bottom then
      return .bottom
    if let some idx := xb then
      let b ← getBinding idx
      if !b.intersected then
        let mo := if offset > maxOffsetx && maxOffsetx ≥ 0 then min 32 offset else maxOffsetx
        changeBinding idx fun x => { x with maxOffset := mo }
    if let some idx := yb then
      let b ← getBinding idx
      if !b.intersected then
        let mo := if -offset > maxOffsety && maxOffsety ≥ 0 then min 32 (-offset) else maxOffsety
        changeBinding idx fun x => { x with maxOffset := mo }
    if let some x2 := xp2 then
      if ← obviouslyEgal n T xp1 ii then
        if ← obviouslyEgal n T x2 i2 then
          return vmx
    if let some y2 := yp2 then
      if ← obviouslyEgal n T yp1 ii then
        if ← obviouslyEgal n T y2 i2 then
          return vmy
    let some va ← wrapVararg n T (subOps n T) (some ii) (some i2) true 0
      | return .bottom
    return va
termination_by structural n

/-- `intersect_tuple`

Julia source: src/subtype.c:5564-5730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_tuple(jl_datatype_t *xd, jl_datatype_t *yd, jl_stenv_t *e, jl_param_pos_t param) JL_CANSAFEPOINT
{
    size_t lx = jl_nparams(xd), ly = jl_nparams(yd);
    size_t llx = lx, lly = ly;
    if (lx == 0 && ly == 0)
        return (jl_value_t*)yd;
    int vx=0, vy=0;
    jl_vararg_kind_t vvx = lx > 0 ? jl_vararg_kind(jl_tparam(xd, lx-1)) : JL_VARARG_NONE;
    jl_vararg_kind_t vvy = ly > 0 ? jl_vararg_kind(jl_tparam(yd, ly-1)) : JL_VARARG_NONE;
    if (vvx == JL_VARARG_INT)
        llx += jl_unbox_long(jl_unwrap_vararg_num((jl_vararg_t *)jl_tparam(xd, lx-1))) - 1;
    if (vvy == JL_VARARG_INT)
        lly += jl_unbox_long(jl_unwrap_vararg_num((jl_vararg_t *)jl_tparam(yd, ly-1))) - 1;
    if (vvx == JL_VARARG_BOUND && (vvy == JL_VARARG_BOUND || vvy == JL_VARARG_UNBOUND)) {
        jl_value_t *xlen = jl_unwrap_vararg_num((jl_vararg_t*)jl_tparam(xd, lx-1));
        assert(xlen && jl_is_typevar(xlen));
        jl_varbinding_t *xb = lookup(e, (jl_tvar_t*)xlen);
        if (xb && xb->intersected && xb->max_offset > 0) {
            assert(xb->max_offset <= 32);
            llx += xb->max_offset;
        }
    }
    if (vvy == JL_VARARG_BOUND && (vvx == JL_VARARG_BOUND || vvx == JL_VARARG_UNBOUND)) {
        jl_value_t *ylen = jl_unwrap_vararg_num((jl_vararg_t*)jl_tparam(yd, ly-1));
        assert(ylen && jl_is_typevar(ylen));
        jl_varbinding_t *yb = lookup(e, (jl_tvar_t*)ylen);
        if (yb && yb->intersected && yb->max_offset > 0) {
            assert(yb->max_offset <= 32);
            lly += yb->max_offset;
        }
    }

    if ((vvx == JL_VARARG_NONE || vvx == JL_VARARG_INT) &&
        (vvy == JL_VARARG_NONE || vvy == JL_VARARG_INT)) {
        if (llx != lly)
            return jl_bottom_type;
    }

    size_t np = llx > lly ? llx : lly;
    jl_value_t *res = NULL;
    jl_svec_t *p = NULL;
    jl_value_t **params;
    jl_value_t **roots;
    JL_GC_PUSHARGS(roots, np < 64 ? np : 1);
    if (np < 64) {
        params = roots;
    }
    else {
        p = jl_alloc_svec(np);
        roots[0] = (jl_value_t*)p;
        params = jl_svec_data(p);
    }
    size_t i=0, j=0;
    jl_value_t *xi, *yi;
    int isx = 1, isy = 1; // try to reuse the object x or y as res whenever we can (e.g. when it is the supertype) instead of allocating a copy
    while (1) {
        vx = vy = 0;
        xi = i < llx ? jl_tparam(xd, i < lx ? i : lx - 1) : NULL;
        yi = j < lly ? jl_tparam(yd, j < ly ? j : ly - 1) : NULL;
        if (xi == NULL && yi == NULL) {
            assert(i == j && i == np);
            break;
        }
        if (xi && jl_is_vararg(xi)) vx = vvx == JL_VARARG_UNBOUND || (vvx == JL_VARARG_BOUND && i == llx - 1);
        if (yi && jl_is_vararg(yi)) vy = vvy == JL_VARARG_UNBOUND || (vvy == JL_VARARG_BOUND && j == lly - 1);
        if (xi == NULL || yi == NULL) {
            if (vx && intersect_vararg_length(xi, lly+1-llx, e, 0)) {
                np = j;
                p = NULL;
            }
            else if (vy && intersect_vararg_length(yi, llx+1-lly, e, 1)) {
                np = i;
                p = NULL;
            }
            else {
                res = jl_bottom_type;
            }
            break;
        }
        jl_value_t *ii = NULL;
        if (vx && vy) {
            jl_savedenv_t se;
            save_env(e, &se, 1);
            ii = intersect_varargs((jl_vararg_t*)xi,
                                   (jl_vararg_t*)yi,
                                   lly - llx, // xi's offset: {A^n...,Vararg{T,N}} ∩ {Vararg{S,M}}
                                            // {(A∩S)^n...,Vararg{T∩S,N}} plus N = M-n
                                   e,
                                   param);
            if (ii == jl_bottom_type)
                restore_env(e, &se, 1);
            free_env(&se);
        }
        else {
            ii = intersect(jl_is_vararg(xi) ? jl_unwrap_vararg(xi) : xi,
                           jl_is_vararg(yi) ? jl_unwrap_vararg(yi) : yi,
                           e,
                           param == PARAM_NONE ? PARAM_COVARIANT : param);
        }
        if (ii == jl_bottom_type) {
            if (vx && vy) {
                jl_varbinding_t *xb=NULL, *yb=NULL;
                jl_value_t *xlen = jl_unwrap_vararg_num(xi);
                assert(xlen == NULL || jl_is_typevar(xlen));
                if (xlen) xb = lookup(e, (jl_tvar_t*)xlen);
                jl_value_t *ylen = jl_unwrap_vararg_num(yi);
                assert(ylen == NULL || jl_is_typevar(ylen));
                if (ylen) yb = lookup(e, (jl_tvar_t*)ylen);
                int len = i > j ? i : j;
                if ((xb && jl_is_long(xb->lb) && llx-1+jl_unbox_long(xb->lb) != len) ||
                    (yb && jl_is_long(yb->lb) && lly-1+jl_unbox_long(yb->lb) != len)) {
                    res = jl_bottom_type;
                }
                else {
                    assert(e->Loffset == 0);
                    if (xb) set_var_to_const(xb, jl_box_long(len-llx+1), e, 0);
                    if (yb) set_var_to_const(yb, jl_box_long(len-lly+1), e, 1);
                    np = len;
                    p = NULL;
                }
            }
            else {
                res = jl_bottom_type;
            }
            break;
        }
        isx = isx && ii == xi;
        isy = isy && ii == yi;
        if (p)
            jl_svecset(p, (i > j ? i : j), ii);
        else
            params[i > j ? i : j] = ii;
        if (vx && vy)
            break;
        if (!vx) i++;
        if (!vy) j++;
    }
    // TODO: handle Vararg with explicit integer length parameter
    if (res == NULL) {
        assert(!p || np == jl_svec_len(p));
        isx = isx && lx == np;
        isy = isy && ly == np;
        if (!isx && !isy) {
            // do a more careful check now for equivalence
            if (lx == np) {
                isx = 1;
                for (i = 0; i < np; i++)
                    isx = isx && obviously_egal(params[i], jl_tparam(xd, i));
            }
            if (!isx && ly == np) {
                isy = 1;
                for (i = 0; i < np; i++)
                    isy = isy && obviously_egal(params[i], jl_tparam(yd, i));
            }
        }
        if (isx)
            res = (jl_value_t*)xd;
        else if (isy)
            res = (jl_value_t*)yd;
        else if (p)
            res = jl_apply_tuple_type(p, 1);
        else
            res = jl_apply_tuple_type_v(params, np);
    }
    JL_GC_POP();
    return res;
}
```
-/
def intersectTuple (n : Nat) (T : Types) (xd yd : Val) (param : ParamPos)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let lx := xd.nparams
    let ly := yd.nparams
    if lx == 0 && ly == 0 then
      return yd
    let vvx := if lx > 0 then xd.params[lx - 1]!.varargKind else .none
    let vvy := if ly > 0 then yd.params[ly - 1]!.varargKind else .none
    let mut llx : Int := Int.ofNat lx
    let mut lly : Int := Int.ofNat ly
    if vvx == .int then
      if let some (.long k) := xd.params[lx - 1]!.varargN? then
        llx := llx + k - 1
    if vvy == .int then
      if let some (.long k) := yd.params[ly - 1]!.varargN? then
        lly := lly + k - 1
    if vvx == .bound && (vvy == .bound || vvy == .unbound) then
      if let some xlen := xd.params[lx - 1]!.varargN? then
        if let some idx ← lookup xlen then
          let xb ← getBinding idx
          if xb.intersected && xb.maxOffset > 0 then
            llx := llx + xb.maxOffset
    if vvy == .bound && (vvx == .bound || vvx == .unbound) then
      if let some ylen := yd.params[ly - 1]!.varargN? then
        if let some idx ← lookup ylen then
          let yb ← getBinding idx
          if yb.intersected && yb.maxOffset > 0 then
            lly := lly + yb.maxOffset
    if (vvx == .none || vvx == .int) && (vvy == .none || vvy == .int) then
      if llx != lly then
        return .bottom
    if llx < 0 || lly < 0 then
      return .bottom
    let llxNat := llx.toNat
    let llyNat := lly.toNat
    let mut np := max llxNat llyNat
    let mut params : Array Val := Array.replicate np .bottom
    let mut i : Nat := 0
    let mut j : Nat := 0
    let mut isx := true
    let mut isy := true
    let mut res? : Option Val := none
    let mut steps := n
    while true do
      if steps == 0 then outOfBudget
      steps := steps - 1
      let xi? : Option Val := if i < llxNat then some xd.params[if i < lx then i else lx - 1]! else none
      let yi? : Option Val := if j < llyNat then some yd.params[if j < ly then j else ly - 1]! else none
      if xi?.isNone && yi?.isNone then
        break
      let vx := match xi? with
        | some xi => xi.isVararg && (vvx == .unbound || (vvx == .bound && i == llxNat - 1))
        | none => false
      let vy := match yi? with
        | some yi => yi.isVararg && (vvy == .unbound || (vvy == .bound && j == llyNat - 1))
        | none => false
      if xi?.isNone || yi?.isNone then
        if vx then
          if ← intersectVarargLength n T (xi?.getD .bottom) (lly + 1 - llx) false intersecting then
            np := j
            break
        if vy then
          if ← intersectVarargLength n T (yi?.getD .bottom) (llx + 1 - lly) true intersecting then
            np := i
            break
        res? := some .bottom
        break
      let xi := xi?.getD .bottom
      let yi := yi?.getD .bottom
      let ii ←
        if vx && vy then do
          let se ← saveEnv
          let r ← intersectVarargs n T xi yi (lly - llx) param intersecting
          if r == .bottom then
            restoreEnv se true
          pure r
        else do
          let xelt := if xi.isVararg then xi.unwrapVararg else xi
          let yelt := if yi.isVararg then yi.unwrapVararg else yi
          intersect n T xelt yelt (if param == .none then .covariant else param) intersecting
      if ii == .bottom then
        if vx && vy then
          let xb ← match xi.varargN? with | some v => lookup v | none => pure none
          let yb ← match yi.varargN? with | some v => lookup v | none => pure none
          let len : Int := Int.ofNat (max i j)
          let mut conflict := false
          if let some xidx := xb then
            if let .long k := (← getBinding xidx).lb then
              if llx - 1 + k != len then conflict := true
          if let some yidx := yb then
            if let .long k := (← getBinding yidx).lb then
              if lly - 1 + k != len then conflict := true
          if conflict then
            res? := some .bottom
          else
            if let some xidx := xb then
              let _ ← setVarToConst n T xidx (.long (len - llx + 1)) false
            if let some yidx := yb then
              let _ ← setVarToConst n T yidx (.long (len - lly + 1)) true
            np := max i j
        else
          res? := some .bottom
        break
      isx := isx && ii == xi
      isy := isy && ii == yi
      params := params.set! (max i j) ii
      if vx && vy then
        break
      if !vx then i := i + 1
      if !vy then j := j + 1
    if let some r := res? then
      return r
    let finalParams := (params.extract 0 np).toList
    isx := isx && lx == np
    isy := isy && ly == np
    if !isx && !isy then
      if lx == np then
        let mut eqX := true
        for k in [0:np] do
          if !(← obviouslyEgal n T finalParams[k]! xd.params[k]!) then
            eqX := false
            break
        isx := eqX
      if !isx && ly == np then
        let mut eqY := true
        for k in [0:np] do
          if !(← obviouslyEgal n T finalParams[k]! yd.params[k]!) then
            eqY := false
            break
        isy := eqY
    if isx then
      return xd
    else if isy then
      return yd
    else
      let some tup ← instDatatypeInner n T (subOps n T) tupleName finalParams true 0
        | return .bottom
      return tup
termination_by structural n

/-- `intersect_sub_datatype`: intersection where `xd` nominally inherits from `yd`.

Julia source: src/subtype.c:5742-5756 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_sub_datatype(jl_datatype_t *xd, jl_datatype_t *yd, jl_stenv_t *e, int R, jl_param_pos_t param) JL_CANSAFEPOINT
{
    // attempt to populate additional constraints into `e`
    // if that attempt fails, then return bottom
    // otherwise return xd (finish_unionall will later handle propagating those constraints)
    assert(e->Loffset == 0);
    jl_datatype_t *xdsuper = jl_datatype_compute_super(xd);
    if (xdsuper == NULL)
        return jl_bottom_type; // definition in progress
    jl_value_t *isuper = R ? intersect((jl_value_t*)yd, (jl_value_t*)xdsuper, e, param) :
                             intersect((jl_value_t*)xdsuper, (jl_value_t*)yd, e, param);
    if (isuper == jl_bottom_type)
        return jl_bottom_type;
    return (jl_value_t*)xd;
}
```
-/
def intersectSubDatatype (n : Nat) (T : Types) (xd yd : Val) (R : Bool) (param : ParamPos)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let xdsuper ← superOf n T (subOps n T) xd
    let isuper ← if R then intersect n T yd xdsuper param intersecting
                  else intersect n T xdsuper yd param intersecting
    if isuper == .bottom then
      return .bottom
    return xd
termination_by structural n

/-- `intersect_invariant`; `none` is `NULL`, `some .bottom` is `jl_bottom_type`.

Julia source: src/subtype.c:5758-5795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_invariant(jl_value_t *x, jl_value_t *y, jl_stenv_t *e)
{
    if (e->Loffset == 0 && !jl_has_free_typevars(x) && !jl_has_free_typevars(y)) {
        return (jl_subtype(x,y) && jl_subtype(y,x)) ? y : NULL;
    }
    e->invdepth++;
    jl_value_t *ii = intersect(x, y, e, PARAM_INVARIANT);
    e->invdepth--;
    if (jl_is_typevar(x) && jl_is_typevar(y) && jl_is_typevar(ii))
        return ii; // skip the following check due to possible circular constraints.
    if (ii == jl_bottom_type) {
        if (!subtype_in_env(x, jl_bottom_type, e))
            return NULL;
        flip_vars(e); flip_offset(e);
        if (!subtype_in_env(y, jl_bottom_type, e)) {
            flip_vars(e); flip_offset(e);
            return NULL;
        }
        flip_vars(e); flip_offset(e);
        return jl_bottom_type;
    }
    jl_savedenv_t se;
    JL_GC_PUSH1(&ii);
    save_env(e, &se, 1);
    if (!subtype_in_env_existential(x, y, e))
        ii = NULL;
    else {
        restore_env(e, &se, 1);
        flip_offset(e);
        if (!subtype_in_env_existential(y, x, e))
            ii = NULL;
        flip_offset(e);
    }
    restore_env(e, &se, 1);
    free_env(&se);
    JL_GC_POP();
    return ii;
}
```
-/
def intersectInvariant (n : Nat) (T : Types) (x0 y0 : Val)
    (intersecting : List (Val × Val)) : STM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let x ← resolveVal n x0
    let y ← resolveVal n y0
    if (← get).Loffset == 0 && !x.hasFreeTypevars && !y.hasFreeTypevars then
      if ← jlSubtype n T x y then
        if ← jlSubtype n T y x then
          return some y
      return none
    modify fun e => { e with invdepth := e.invdepth + 1 }
    let ii ← intersect n T x y .invariant intersecting
    modify fun e => { e with invdepth := e.invdepth - 1 }
    if x.isTypevar && y.isTypevar && ii.isTypevar then
      return some ii
    if ii == .bottom then
      if !(← subtypeInEnv n T x .bottom) then
        return none
      flipVars
      flipOffset
      let okY ← subtypeInEnv n T y .bottom
      flipVars
      flipOffset
      if !okY then
        return none
      return some .bottom
    let se ← saveEnv
    let mut out : Option Val := some ii
    if !(← subtypeInEnvExistential n T x y) then
      out := none
    else
      restoreEnv se true
      flipOffset
      if !(← subtypeInEnvExistential n T y x) then
        out := none
      flipOffset
    restoreEnv se true
    return out
termination_by structural n

/-- `intersect_type_type`: intersection where `x == Type{...}` and `y` is not.

Julia source: src/subtype.c:5798-5831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_type_type(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, int8_t R) JL_CANSAFEPOINT
{
    assert(e->Loffset == 0);
    // fast path: every member of a `Type{T}` is a type
    if (y == (jl_value_t*)jl_anytype_type || y == (jl_value_t*)jl_any_type)
        return x;
    jl_value_t *p0 = typeeq_unpin_tvar(jl_typeeq_T(x));
    if (!jl_is_typevar(p0)) {
        // a dispatch key for one specific open type object (dangling free
        // typevars, see `typeeq_vars_bound_in_env`) is pinned to its type tag
        if (typeeq_is_dangling_key(p0, e, NULL))
            return (jl_typeof(p0) == y) ? x : jl_bottom_type;
        // `Type{T}`'s members can carry any type tag in the kind mask, so the
        // intersection with `y` (a kind or a kind's supertype) is nonempty
        // whenever some kind in the mask lies in `y`. `Type{T}` itself is the
        // best expressible bound for the members with that tag (e.g. the
        // `Vector{S} where Int<:S<:Int` member of `Type{Vector{Int}} ∩ UnionAll`).
        return typeeq_mask_meets(typeeq_kind_mask(p0), y) ? x : jl_bottom_type;
    }
    if (!is_kind_or_anytype(y)) return jl_bottom_type;
    if (y == (jl_value_t*)jl_typeofbottom_type && ((jl_tvar_t*)p0)->lb == jl_bottom_type)
        return (jl_value_t*)jl_wrap_Type(jl_bottom_type);
    if (((jl_tvar_t*)p0)->ub == (jl_value_t*)jl_any_type)
        return y;
    return x;
    /*
    jl_value_t *ii = R ? intersect_invariant(y, jl_tparam0(x), e) : intersect_invariant(jl_tparam0(x), y, e);
    // NOTE: we cannot express e.g. DataType ∩ (UnionAll T<:Integer Type{T}), so returning `x`
    // here is a conservative over-estimate.
    if (ii == NULL || ii == jl_bottom_type) return x;
    if (ii == y) return ii;
    return (jl_value_t*)jl_wrap_Type(ii);
    */
}
```
-/
def intersectTypeType (n : Nat) (T : Types) (x y : Val) (_R : Bool) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if y == anytypeType || y == anyType then
      return x
    let p0 ← typeeqUnpinTvar n T x.someTypeT
    if !p0.isTypevar then
      if ← typeeqIsDanglingKey n p0 [] then
        return if typeOf p0 == y then x else .bottom
      let mask ← typeeqKindMask n T p0
      return if ← typeeqMaskMeets n T mask y then x else .bottom
    if !isKindOrAnytype y then
      return .bottom
    if y == typeofbottomType && p0.tvLb == .bottom then
      return ← wrapType n T (subOps n T) .bottom
    if p0.tvUb == anyType then
      return y
    return x
termination_by structural n

/-- `intersect_var_ccheck_in_env`

Julia source: src/subtype.c:5863-5946 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int intersect_var_ccheck_in_env(jl_value_t *xlb, jl_value_t *xub, jl_value_t *ylb, jl_value_t *yub, jl_stenv_t *e, int flip)
{
    int easy_check1 = xlb == jl_bottom_type ||
                      yub == (jl_value_t *)jl_any_type ||
                      (e->Loffset == 0 && obviously_in_union(yub, xlb));
    int easy_check2 = ylb == jl_bottom_type ||
                      xub == (jl_value_t *)jl_any_type ||
                      (e->Loffset == 0 && obviously_in_union(xub, ylb));
    int nofree1 = 0, nofree2 = 0;
    if (!easy_check1) {
        nofree1 = !jl_has_free_typevars(xlb) && !jl_has_free_typevars(yub);
        if (nofree1 && e->Loffset == 0) {
            easy_check1 = jl_subtype(xlb, yub);
            if (!easy_check1)
                return 0;
        }
    }
    if (!easy_check2) {
        nofree2 = !jl_has_free_typevars(ylb) && !jl_has_free_typevars(xub);
        if (nofree2 && e->Loffset == 0) {
            easy_check2 = jl_subtype(ylb, xub);
            if (!easy_check2)
                return 0;
        }
    }
    if (easy_check1 && easy_check2)
        return 1;
    int ccheck = 0;
    if ((easy_check1 || nofree1) && (easy_check2 || nofree2)) {
        jl_varbinding_t *vars = e->vars;
        e->vars = NULL;
        ccheck = easy_check1 || subtype_in_env(xlb, yub, e);
        if (ccheck && !easy_check2) {
            flip_offset(e);
            ccheck = subtype_in_env(ylb, xub, e);
            flip_offset(e);
        }
        e->vars = vars;
        return ccheck;
    }
    jl_savedenv_t se;
    save_env(e, &se, 1);
    // first try normal flip.
    if (flip) flip_vars(e);
    ccheck = easy_check1 || subtype_in_env(xlb, yub, e);
    if (ccheck && !easy_check2) {
        flip_offset(e);
        ccheck = subtype_in_env(ylb, xub, e);
        flip_offset(e);
    }
    if (flip) flip_vars(e);
    if (!ccheck) {
        // then try reverse flip.
        restore_env(e, &se, 1);
        if (!flip) flip_vars(e);
        ccheck = easy_check1 || subtype_in_env(xlb, yub, e);
        if (ccheck && !easy_check2) {
            flip_offset(e);
            ccheck = subtype_in_env(ylb, xub, e);
            flip_offset(e);
        }
        if (!flip) flip_vars(e);
    }
    if (!ccheck) {
        // then try existential.
        restore_env(e, &se, 1);
        if (easy_check1)
            ccheck = 1;
        else {
            ccheck = subtype_in_env_existential(xlb, yub, e);
            restore_env(e, &se, 1);
        }
        if (ccheck && !easy_check2) {
            flip_offset(e);
            ccheck = subtype_in_env_existential(ylb, xub, e);
            flip_offset(e);
            restore_env(e, &se, 1);
        }
    }
    if (ccheck && ((!easy_check1 && jl_has_free_typevars(xlb)) || (!easy_check2 && jl_has_free_typevars(ylb))))
        restore_env(e, &se, 1);
    free_env(&se);
    return ccheck;
}
```
-/
def intersectVarCcheckInEnv (n : Nat) (T : Types) (xlb0 xub0 ylb0 yub0 : Val) (flip : Bool) :
    STM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let xlb ← resolveVal n xlb0
    let xub ← resolveVal n xub0
    let ylb ← resolveVal n ylb0
    let yub ← resolveVal n yub0
    let mut easyCheck1 ←
      if xlb == .bottom || yub == anyType then pure true
      else if (← get).Loffset == 0 then obviouslyInUnion n T yub xlb
      else pure false
    let mut easyCheck2 ←
      if ylb == .bottom || xub == anyType then pure true
      else if (← get).Loffset == 0 then obviouslyInUnion n T xub ylb
      else pure false
    let mut nofree1 := false
    let mut nofree2 := false
    if !easyCheck1 then
      nofree1 := !xlb.hasFreeTypevars && !yub.hasFreeTypevars
      if nofree1 && (← get).Loffset == 0 then
        easyCheck1 ← jlSubtype n T xlb yub
        if !easyCheck1 then
          return false
    if !easyCheck2 then
      nofree2 := !ylb.hasFreeTypevars && !xub.hasFreeTypevars
      if nofree2 && (← get).Loffset == 0 then
        easyCheck2 ← jlSubtype n T ylb xub
        if !easyCheck2 then
          return false
    if easyCheck1 && easyCheck2 then
      return true
    if (easyCheck1 || nofree1) && (easyCheck2 || nofree2) then
      let savedVars := (← get).vars
      modify fun e => { e with vars := #[] }
      let mut ccheck ← if easyCheck1 then pure true else subtypeInEnv n T xlb yub
      if ccheck && !easyCheck2 then
        flipOffset
        ccheck ← subtypeInEnv n T ylb xub
        flipOffset
      modify fun e => { e with vars := savedVars }
      return ccheck
    let se ← saveEnv
    -- first try normal flip.
    if flip then flipVars
    let mut ccheck ← if easyCheck1 then pure true else subtypeInEnv n T xlb yub
    if ccheck && !easyCheck2 then
      flipOffset
      ccheck ← subtypeInEnv n T ylb xub
      flipOffset
    if flip then flipVars
    if !ccheck then
      -- then try reverse flip.
      restoreEnv se true
      if !flip then flipVars
      ccheck ← if easyCheck1 then pure true else subtypeInEnv n T xlb yub
      if ccheck && !easyCheck2 then
        flipOffset
        ccheck ← subtypeInEnv n T ylb xub
        flipOffset
      if !flip then flipVars
    if !ccheck then
      -- then try existential.
      restoreEnv se true
      if easyCheck1 then
        ccheck := true
      else
        ccheck ← subtypeInEnvExistential n T xlb yub
        restoreEnv se true
      if ccheck && !easyCheck2 then
        flipOffset
        ccheck ← subtypeInEnvExistential n T ylb xub
        flipOffset
        restoreEnv se true
    if ccheck && ((!easyCheck1 && xlb.hasFreeTypevars) || (!easyCheck2 && ylb.hasFreeTypevars)) then
      restoreEnv se true
    return ccheck
termination_by structural n

/-- `intersect`

Julia source: src/subtype.c:5994-6317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, jl_param_pos_t param)
{
    if (x == y) return y;
    if (jl_is_typevar(x)) {
        if (jl_is_typevar(y)) {
            int xinner = 0, yinner = 0;
            jl_varbinding_t *xx = lookup_binding(e, (jl_tvar_t*)x, &xinner);
            jl_varbinding_t *yy = lookup_binding(e, (jl_tvar_t*)y, &yinner);
            int xfree_singleton = xx == NULL && !xinner;
            int yfree_singleton = yy == NULL && !yinner;
            if (xfree_singleton && yfree_singleton)
                return jl_bottom_type;
            int R = 0;
            if (xx && yy && var_outside(e, (jl_tvar_t*)x, (jl_tvar_t*)y)) {
                // to preserve variable identities correctly, always accumulate bounds
                // on the outer variable, return the outer variable, and set the inner
                // variable equal to the outer variable.
                jl_value_t *temp; jl_varbinding_t *tvb;
                temp = x; x = y; y = temp;
                tvb = xx; xx = yy; yy = tvb;
                R = 1;
            }
            if (param == PARAM_INVARIANT) {
                jl_value_t *xlb = xx ? xx->lb : xinner ? ((jl_tvar_t*)x)->lb : x;
                jl_value_t *xub = xx ? xx->ub : xinner ? ((jl_tvar_t*)x)->ub : x;
                jl_value_t *ylb = yy ? yy->lb : yinner ? ((jl_tvar_t*)y)->lb : y;
                jl_value_t *yub = yy ? yy->ub : yinner ? ((jl_tvar_t*)y)->ub : y;
                if (xx && yy && xx->depth0 != yy->depth0) {
                    record_var_occurrence(xx, e, param);
                    record_var_occurrence(yy, e, param);
                    return subtype_in_env(yy->ub, yy->lb, e) ? y : jl_bottom_type;
                }
                if (xub == xlb && jl_is_typevar(xub) && xub != x) {
                    record_var_occurrence(xx, e, param);
                    if (y == xub) {
                        record_var_occurrence(yy, e, param);
                        return y;
                    }
                    if (R) flip_offset(e);
                    jl_value_t *res = intersect(xub, y, e, param);
                    if (R) flip_offset(e);
                    return res;
                }
                if (yub == ylb && jl_is_typevar(yub) && yub != y) {
                    record_var_occurrence(yy, e, param);
                    if (R) flip_offset(e);
                    jl_value_t *res = intersect(x, yub, e, param);
                    if (R) flip_offset(e);
                    return res;
                }
                record_var_occurrence(xx, e, param);
                record_var_occurrence(yy, e, param);
                int xoffset = R ? -e->Loffset : e->Loffset;
                if (!jl_is_type(ylb) && !jl_is_typevar(ylb)) {
                    if (xx)
                        return set_var_to_const(xx, ylb, e, R);
                    if ((xlb == jl_bottom_type && xub == (jl_value_t*)jl_any_type) || jl_egal(xlb, ylb)) {
                        if (xoffset == 0)
                            return ylb;
                        else if (jl_is_long(ylb)) {
                            if (xoffset > 0)
                                return ylb;
                            else
                                return jl_box_long(jl_unbox_long(ylb) + xoffset);
                        }
                    }
                    return jl_bottom_type;
                }
                if (!jl_is_type(xlb) && !jl_is_typevar(xlb)) {
                    if (yy)
                        return set_var_to_const(yy, xlb, e, !R);
                    if (ylb == jl_bottom_type && yub == (jl_value_t*)jl_any_type) {
                        if (xoffset == 0)
                            return xlb;
                        else if (jl_is_long(xlb)) {
                            if (xoffset < 0)
                                return xlb;
                            else
                                return jl_box_long(jl_unbox_long(ylb) - xoffset);
                        }
                    }
                    return jl_bottom_type;
                }
                int ccheck;
                if (R) flip_offset(e);
                if (xlb == xub && ylb == yub &&
                    jl_has_typevar(xlb, (jl_tvar_t *)y) &&
                    jl_has_typevar(ylb, (jl_tvar_t *)x)) {
                    // special case for e.g.
                    // 1) Val{Y}<:X<:Val{Y} && Val{X}<:Y<:Val{X}
                    // 2) Y<:X<:Y && Val{X}<:Y<:Val{X} => Val{Y}<:Y<:Val{Y}
                    ccheck = 0;
                }
                else if (var_always_occurs_as_parameter(xub, (jl_tvar_t*)y, 0) ||
                         var_always_occurs_as_parameter(yub, (jl_tvar_t*)x, 0)) {
                    // special case for X<:Val{Y} ∩ Y
                    ccheck = 0;
                }
                else if (yub == xub ||
                    (subtype_by_bounds(xlb, yub, e) && subtype_by_bounds(ylb, xub, e))) {
                    ccheck = 1;
                }
                else {
                    // try many subtype check to avoid false `Union{}`
                    ccheck = intersect_var_ccheck_in_env(xlb, xub, ylb, yub, e, R);
                }
                if (R) flip_offset(e);
                if (!ccheck)
                    return jl_bottom_type;
                if ((has_typevar_via_env(xub, (jl_tvar_t*)y, e) || has_typevar_via_env(xub, (jl_tvar_t*)x, e)) &&
                    (has_typevar_via_env(yub, (jl_tvar_t*)x, e) || has_typevar_via_env(yub, (jl_tvar_t*)y, e))) {
                    // TODO: This doesn't make much sense.
                    // circular constraint. the result will be Bottom, but in the meantime
                    // we need to avoid computing intersect(xub, yub) since it won't terminate.
                    return y;
                }
                jl_value_t *ub=NULL, *lb=NULL;
                JL_GC_PUSH2(&lb, &ub);
                int d = xx ? xx->depth0 : yy ? yy->depth0 : 0;
                ub = R ? intersect_aside(yub, xub, e, d) : intersect_aside(xub, yub, e, d);
                if (reachable_var(xlb, (jl_tvar_t*)y, e))
                    lb = ylb;
                else
                    lb = simple_join(xlb, ylb);
                if (yy && xoffset == 0) {
                    yy->lb = lb;
                    if (!reachable_var(ub, (jl_tvar_t*)y, e))
                        yy->ub = ub;
                    assert(yy->ub != y);
                    assert(yy->lb != y);
                }
                if (xx && xoffset == 0 && !reachable_var(y, (jl_tvar_t*)x, e)) {
                    xx->lb = y;
                    xx->ub = y;
                    assert(xx->ub != x);
                }
                JL_GC_POP();
                // Here we always return the shorter `Vararg`'s length.
                return xoffset < 0 ? x : y;
            }
            assert(e->Loffset == 0);
            record_var_occurrence(xx, e, param);
            record_var_occurrence(yy, e, param);
            if (xx && yy && ((xx->concrete && !yy->concrete) || (xx->lb == xx->ub && xx->lb == y))) {
                return intersect_var((jl_tvar_t*)x, y, e, R, param);
            }
            return intersect_var((jl_tvar_t*)y, x, e, !R, param);
        }
        record_var_occurrence(lookup(e, (jl_tvar_t*)x), e, param);
        return intersect_var((jl_tvar_t*)x, y, e, 0, param);
    }
    if (jl_is_typevar(y)) {
        record_var_occurrence(lookup(e, (jl_tvar_t*)y), e, param);
        return intersect_var((jl_tvar_t*)y, x, e, 1, param);
    }
    if (e->Loffset == 0 && !jl_has_free_typevars(x) && !jl_has_free_typevars(y)) {
        if (jl_subtype(x, y)) return x;
        if (jl_subtype(y, x)) return y;
    }
    if (jl_is_uniontype(x)) {
        if (obviously_in_union(x, y))
            return y;
        if (jl_is_uniontype(y) && obviously_in_union(y, x))
            return x;
        return intersect_union(y, (jl_uniontype_t*)x, e, 0, param);
    }
    if (jl_is_uniontype(y)) {
        if (obviously_in_union(y, x))
            return x;
        if (jl_is_unionall(x) && (jl_has_free_typevars(x) || jl_has_free_typevars(y)))
            return intersect_unionall(y, (jl_unionall_t*)x, e, 0, param);
        return intersect_union(x, (jl_uniontype_t*)y, e, 1, param);
    }
    if (y == (jl_value_t*)jl_any_type) return x;
    if (x == (jl_value_t*)jl_any_type) return y;
    if (jl_is_unionall(x)) {
        if (jl_is_unionall(y)) {
            jl_value_t *a=NULL, *b=jl_bottom_type, *res=NULL;
            JL_GC_PUSH2(&a, &b);
            jl_savedenv_t se;
            save_env(e, &se, 0);
            a = intersect_unionall(y, (jl_unionall_t*)x, e, 0, param);
            if (jl_is_unionall(a)) {
                jl_unionall_t *ua = (jl_unionall_t*)a;
                if (jl_is_unionall(ua->body)) {
                    jl_unionall_t *ub = (jl_unionall_t*)ua->body;
                    if (jl_has_typevar(ub->var->ub, ua->var) ||
                        jl_has_typevar(ub->var->lb, ua->var)) {
                        restore_env(e, &se, 0); // restore counts
                        b = intersect_unionall(x, (jl_unionall_t*)y, e, 1, param);
                    }
                }
            }
            free_env(&se);
            if (!jl_has_free_typevars(a) && !jl_has_free_typevars(b)) {
                if (jl_subtype(a, b))
                    res = b;
                else if (jl_subtype(b, a))
                    res = a;
            }
            if (!res) res = simple_join(a, b);
            JL_GC_POP();
            return res;
        }
        return intersect_unionall(y, (jl_unionall_t*)x, e, 0, param);
    }
    if (jl_is_unionall(y))
        return intersect_unionall(x, (jl_unionall_t*)y, e, 1, param);
    if (jl_is_typeegal(x) || jl_is_typeegal(y)) {
        // the intersection is `TypeEgal{A}` itself when `A` lies in the other
        // operand (binding its typevars), else `Bottom`
        int8_t R = 0;
        if (!jl_is_typeegal(x)) { jl_value_t *t = x; x = y; y = t; R = 1; }
        jl_value_t *A = jl_typeegal_T(x);
        if (jl_is_typeegal(y))
            return jl_egal(A, jl_typeegal_T(y)) ? x : jl_bottom_type; // intersection is nonempty iff `A === B`
        if (jl_is_typeeq(y)) {
            jl_value_t *yp = jl_typeeq_T(y);
            // as in the subtype rule: `A` is egal-known, but `Type{B}` pins `B`
            // only up to `==`, so `A`'s spelling is only `==`-authoritative
            int saved_spell = e->spell_channel;
            if (e->spell_channel > BOUND_EQ)
                e->spell_channel = BOUND_EQ;
            jl_value_t *ii = R ? intersect_invariant(yp, A, e) : intersect_invariant(A, yp, e);
            e->spell_channel = saved_spell;
            return (ii == NULL || ii == jl_bottom_type) ? jl_bottom_type : x;
        }
        // `A` lies in `y` iff the singleton `typeof(A)` does; `jl_subtype` also
        // covers abstract supertypes (e.g. `AnyType`) when the closed-types
        // fast path above was skipped
        if (param != PARAM_INVARIANT && !jl_has_free_typevars(y) &&
            jl_subtype(jl_typeof(A), y))
            return x;
        return jl_bottom_type;
    }
    if (jl_is_typeeq(x) && jl_is_typeeq(y)) {
        jl_value_t *xp = jl_typeeq_T(x);
        jl_value_t *yp = jl_typeeq_T(y);
        jl_value_t *ii = intersect_invariant(xp, yp, e);
        if (ii == NULL)
            return jl_bottom_type;
        JL_GC_PUSH1(&ii);
        jl_value_t *ans = (jl_value_t*)jl_wrap_Type(ii);
        JL_GC_POP();
        return ans;
    }
    if (param != PARAM_INVARIANT) {
        if (jl_is_typeeq(x))
            return intersect_type_type(x, y, e, 0);
        if (jl_is_typeeq(y))
            return intersect_type_type(y, x, e, 1);
    }
    if (jl_is_datatype(x) && jl_is_datatype(y)) {
        jl_datatype_t *xd = (jl_datatype_t*)x, *yd = (jl_datatype_t*)y;
        if (param != PARAM_INVARIANT) {
            if (jl_is_typeeq(x)) {
                if (!jl_is_typeeq(y))
                    return intersect_type_type(x, y, e, 0);
            }
            else if (jl_is_typeeq(y)) {
                return intersect_type_type(y, x, e, 1);
            }
        }
        if (xd->name == yd->name) {
            if (jl_is_tuple_type(xd))
                return intersect_tuple(xd, yd, e, param);
            size_t i, np = jl_nparams(xd);
            jl_value_t **newparams;
            JL_GC_PUSHARGS(newparams, np);
            int isx = 1, isy = 1; // try to reuse the object x or y as res whenever we can (e.g. when it is the supertype) instead of allocating a copy
            for (i = 0; i < np; i++) {
                jl_value_t *xi = jl_tparam(xd, i), *yi = jl_tparam(yd, i);
                jl_value_t *ii = intersect_invariant(xi, yi, e);
                if (ii == NULL)
                    break;
                isx = isx && ii == xi;
                isy = isy && ii == yi;
                newparams[i] = ii;
            }
            jl_value_t *res = jl_bottom_type;
            if (i == np) {
                if (!isx && !isy) {
                    // do a more careful check now for equivalence
                    isx = 1;
                    for (i = 0; i < np; i++)
                        isx = isx && obviously_egal(newparams[i], jl_tparam(xd, i));
                    if (!isx) {
                        isy = 1;
                        for (i = 0; i < np; i++)
                            isy = isy && obviously_egal(newparams[i], jl_tparam(yd, i));
                    }
                }
                if (isx)
                    res = x;
                else if (isy)
                    res = y;
                else {
                    JL_TRY {
                        res = jl_apply_type(xd->name->wrapper, newparams, np);
                    }
                    JL_CATCH {
                        res = jl_bottom_type;
                    }
                }
            }
            JL_GC_POP();
            return res;
        }
        if (param == PARAM_INVARIANT) return jl_bottom_type;
        while (xd != NULL && xd != jl_any_type && xd->name != yd->name)
            xd = jl_datatype_compute_super(xd);
        if (xd == NULL || xd == jl_any_type) {
            xd = (jl_datatype_t*)x;
            while (yd != NULL && yd != jl_any_type && yd->name != xd->name)
                yd = jl_datatype_compute_super(yd);
            if (yd == NULL || yd == jl_any_type)
                return jl_bottom_type;
            return intersect_sub_datatype((jl_datatype_t*)y, xd, e, 1, param);
        }
        return intersect_sub_datatype((jl_datatype_t*)x, yd, e, 0, param);
    }
    if (jl_egal(x, y)) return y;
    return jl_bottom_type;
}
```
-/
def intersect (n : Nat) (T : Types) (x0 y0 : Val) (param : ParamPos)
    (intersecting : List (Val × Val)) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let mut x ← resolveVal n x0
    let mut y ← resolveVal n y0
    if x == y then return y
    if x.isTypevar then
      if y.isTypevar then
        let (xx, xinner) ← lookupBinding x
        let (yy, yinner) ← lookupBinding y
        let xfreeSingleton := xx.isNone && !xinner
        let yfreeSingleton := yy.isNone && !yinner
        if xfreeSingleton && yfreeSingleton then
          return .bottom
        let mut xx := xx
        let mut yy := yy
        let mut R := false
        if xx.isSome && yy.isSome then
          if ← varOutside x y then
            let temp := x; x := y; y := temp
            let tvb := xx; xx := yy; yy := tvb
            R := true
        if param == .invariant then
          let xb ← match xx with | some i => do pure (some (← getBinding i)) | none => pure none
          let yb ← match yy with | some i => do pure (some (← getBinding i)) | none => pure none
          let xlb := match xb with | some b => b.lb | none => if xinner then x.tvLb else x
          let xub := match xb with | some b => b.ub | none => if xinner then x.tvUb else x
          let ylb := match yb with | some b => b.lb | none => if yinner then y.tvLb else y
          let yub := match yb with | some b => b.ub | none => if yinner then y.tvUb else y
          if let (some xbVal, some ybVal) := (xb, yb) then
            if xbVal.depth0 != ybVal.depth0 then
              recordVarOccurrence xx param
              recordVarOccurrence yy param
              return if ← subtypeInEnv n T ybVal.ub ybVal.lb then y else .bottom
          if xub == xlb && xub.isTypevar && xub != x then
            recordVarOccurrence xx param
            if y == xub then
              recordVarOccurrence yy param
              return y
            if R then flipOffset
            let res ← intersect n T xub y param intersecting
            if R then flipOffset
            return res
          if yub == ylb && yub.isTypevar && yub != y then
            recordVarOccurrence yy param
            if R then flipOffset
            let res ← intersect n T x yub param intersecting
            if R then flipOffset
            return res
          recordVarOccurrence xx param
          recordVarOccurrence yy param
          let loff := (← get).Loffset
          let xoffset : Int := if R then -loff else loff
          if !ylb.isType && !ylb.isTypevar then
            if let some xidx := xx then
              return ← setVarToConst n T xidx ylb R
            let eqB ← if xlb == .bottom && xub == anyType then pure true else egal n T xlb ylb
            if eqB then
              if xoffset == 0 then
                return ylb
              else if let .long yv := ylb then
                if xoffset > 0 then
                  return ylb
                else
                  return .long (yv + xoffset)
            return .bottom
          if !xlb.isType && !xlb.isTypevar then
            if let some yidx := yy then
              return ← setVarToConst n T yidx xlb (!R)
            if ylb == .bottom && yub == anyType then
              if xoffset == 0 then
                return xlb
              else if xlb.isLong then
                if xoffset < 0 then
                  return xlb
                else if let .long yv := ylb then
                  return .long (yv - xoffset)
            return .bottom
          if R then flipOffset
          let ccheck ←
            if xlb == xub && ylb == yub && xlb.hasTypevar y && ylb.hasTypevar x then
              pure false
            else do
              let p1 ← varAlwaysOccursAsParameter n xub y false
              let p2 ← if p1 then pure true else varAlwaysOccursAsParameter n yub x false
              if p2 then pure false
              else if yub == xub then
                pure true
              else do
                let s1 ← subtypeByBounds n xlb yub
                let s2 ← if s1 then subtypeByBounds n ylb xub else pure false
                if s2 then pure true
                else intersectVarCcheckInEnv n T xlb xub ylb yub R
          if R then flipOffset
          if !ccheck then
            return .bottom
          let cy1 ← hasTypevarViaEnv xub y
          let cx1 ← if cy1 then pure true else hasTypevarViaEnv xub x
          if cx1 then
            let cy2 ← hasTypevarViaEnv yub x
            let cx2 ← if cy2 then pure true else hasTypevarViaEnv yub y
            if cx2 then
              return y
          let d := match xb, yb with
            | some b, _ => b.depth0
            | none, some b => b.depth0
            | none, none => 0
          let ub ← if R then intersectAside n T yub xub d intersecting
                    else intersectAside n T xub yub d intersecting
          let lb ← if ← reachableVar n xlb y then pure ylb else simpleJoin n T xlb ylb
          if let some yidx := yy then
            if xoffset == 0 then
              changeBinding yidx fun b => { b with lb := lb }
              if !(← reachableVar n ub y) then
                changeBinding yidx fun b => { b with ub := ub }
          if let some xidx := xx then
            if xoffset == 0 then
              if !(← reachableVar n y x) then
                changeBinding xidx fun b => { b with lb := y, ub := y }
          return if xoffset < 0 then x else y
        recordVarOccurrence xx param
        recordVarOccurrence yy param
        if let (some xidx, some yidx) := (xx, yy) then
          let xbVal ← getBinding xidx
          let ybVal ← getBinding yidx
          if (xbVal.concrete && !ybVal.concrete) || (xbVal.lb == xbVal.ub && xbVal.lb == y) then
            return ← intersectVar n T x y R param intersecting
        return ← intersectVar n T y x (!R) param intersecting
      let xidx ← lookup x
      recordVarOccurrence xidx param
      return ← intersectVar n T x y false param intersecting
    if y.isTypevar then
      let yidx ← lookup y
      recordVarOccurrence yidx param
      return ← intersectVar n T y x true param intersecting
    if (← get).Loffset == 0 && !x.hasFreeTypevars && !y.hasFreeTypevars then
      if ← jlSubtype n T x y then return x
      if ← jlSubtype n T y x then return y
    if x.isUnion then
      if ← obviouslyInUnion n T x y then return y
      if y.isUnion then
        if ← obviouslyInUnion n T y x then return x
      return ← intersectUnion n T y x false param intersecting
    if y.isUnion then
      if ← obviouslyInUnion n T y x then return x
      if x.isUnionall && (x.hasFreeTypevars || y.hasFreeTypevars) then
        return ← intersectUnionall n T y x false param intersecting
      return ← intersectUnion n T x y true param intersecting
    if y == anyType then return x
    if x == anyType then return y
    if x.isUnionall then
      if y.isUnionall then
        let se ← saveEnv
        let a ← intersectUnionall n T y x false param intersecting
        let mut b : Val := .bottom
        if let .unionall _ _ _ _ abody := a then
          if abody.isUnionall then
            let ubVar := abody.uaVar
            let uaVar := a.uaVar
            if ubVar.tvUb.hasTypevar uaVar || ubVar.tvLb.hasTypevar uaVar then
              restoreEnv se false
              b ← intersectUnionall n T x y true param intersecting
        let mut res? : Option Val := none
        if !a.hasFreeTypevars && !b.hasFreeTypevars then
          if ← jlSubtype n T a b then
            res? := some b
          else if ← jlSubtype n T b a then
            res? := some a
        match res? with
        | some r => return r
        | none => return ← simpleJoin n T a b
      return ← intersectUnionall n T y x false param intersecting
    if y.isUnionall then
      return ← intersectUnionall n T x y true param intersecting
    if x.isTypeegal || y.isTypeegal then
      let mut R := false
      if !x.isTypeegal then
        let t := x; x := y; y := t; R := true
      let A := x.someTypeT
      if y.isTypeegal then
        return if ← egal n T A y.someTypeT then x else .bottom
      if y.isTypeeq then
        let yp := y.someTypeT
        let savedSpell := (← get).spellChannel
        modify fun e => { e with spellChannel := min e.spellChannel .eq }
        let ii? ← if R then intersectInvariant n T yp A intersecting
                  else intersectInvariant n T A yp intersecting
        modify fun e => { e with spellChannel := savedSpell }
        return match ii? with
          | none | some .bottom => .bottom
          | some _ => x
      if param != .invariant && !y.hasFreeTypevars then
        if ← jlSubtype n T (typeOf A) y then
          return x
      return .bottom
    if x.isTypeeq && y.isTypeeq then
      let xp := x.someTypeT
      let yp := y.someTypeT
      match ← intersectInvariant n T xp yp intersecting with
      | none => return .bottom
      | some ii => return ← wrapType n T (subOps n T) ii
    if param != .invariant then
      if x.isTypeeq then
        return ← intersectTypeType n T x y false
      if y.isTypeeq then
        return ← intersectTypeType n T y x true
    if x.isDatatype && y.isDatatype then
      if param != .invariant then
        if x.isTypeeq then
          if !y.isTypeeq then
            return ← intersectTypeType n T x y false
        else if y.isTypeeq then
          return ← intersectTypeType n T y x true
      if x.name? == y.name? then
        if x.isTupleType then
          return ← intersectTuple n T x y param intersecting
        let np := x.nparams
        let mut newparams : Array Val := #[]
        let mut isx := true
        let mut isy := true
        let mut failed := false
        for i in [0:np] do
          let xi := x.params[i]!
          let yi := y.params[i]!
          match ← intersectInvariant n T xi yi intersecting with
          | none =>
            failed := true
            break
          | some ii =>
            isx := isx && ii == xi
            isy := isy && ii == yi
            newparams := newparams.push ii
        if failed then
          return .bottom
        if !isx && !isy then
          let mut eqX := true
          for i in [0:np] do
            if !(← obviouslyEgal n T newparams[i]! x.params[i]!) then
              eqX := false
              break
          isx := eqX
          if !isx then
            let mut eqY := true
            for i in [0:np] do
              if !(← obviouslyEgal n T newparams[i]! y.params[i]!) then
                eqY := false
                break
            isy := eqY
        if isx then
          return x
        else if isy then
          return y
        else
          let dtName := x.name?.getD ""
          let applied? ← (try instDatatypeInner n T (subOps n T) dtName newparams.toList true 0
                          catch _ => pure none : CM (Option Val))
          return applied?.getD .bottom
      if param == .invariant then
        return .bottom
      let mut xd := x
      let mut steps := n
      while xd != anyType && xd.name? != y.name? do
        if steps == 0 then outOfBudget
        steps := steps - 1
        xd ← superOf n T (subOps n T) xd
      let mut yd := y
      if xd == anyType then
        xd := x
        while yd != anyType && yd.name? != xd.name? do
          if steps == 0 then outOfBudget
          steps := steps - 1
          yd ← superOf n T (subOps n T) yd
        if yd == anyType then
          return .bottom
        return ← intersectSubDatatype n T y xd true param intersecting
      return ← intersectSubDatatype n T x yd false param intersecting
    if ← egal n T x y then
      return y
    return .bottom
termination_by structural n

/-- `intersect_all`

Julia source: src/subtype.c:6405-6465 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_all(jl_value_t *x, jl_value_t *y, jl_stenv_t *e)
{
    e->Runions.depth = 0;
    e->Runions.more = 0;
    e->Runions.used = 0;
    jl_value_t **is;
    JL_GC_PUSHARGS(is, 2);
    jl_savedenv_t se, me;
    save_env(e, &se, 1);
    int niter = 0, total_iter = 0;
    is[0] = intersect(x, y, e, PARAM_NONE); // root
    if (is[0] == jl_bottom_type) {
        restore_env(e, &se, 1);
    }
    else if (!e->emptiness_only && has_next_union_state(e, 1)) {
        niter = merge_env(e, &me, &se, niter);
        restore_env(e, &se, 1);
    }
    while (next_union_state(e, 1)) {
        if (e->emptiness_only && is[0] != jl_bottom_type)
            break;
        e->Runions.depth = 0;
        e->Runions.more = 0;

        is[1] = intersect(x, y, e, PARAM_NONE);
        if (is[1] == jl_bottom_type) {
            restore_env(e, &se, 1);
        }
        else if (niter > 0 || (!e->emptiness_only && has_next_union_state(e, 1))) {
            niter = merge_env(e, &me, &se, niter);
            restore_env(e, &se, 1);
        }
        else {
            assert(is[0] == jl_bottom_type);
        }
        if (is[0] == jl_bottom_type)
            is[0] = is[1];
        else if (is[1] != jl_bottom_type) {
            // TODO: the repeated subtype checks in here can get expensive
            is[0] = jl_type_union(is, 2);
        }
        total_iter++;
        if (has_next_union_state(e, 1) && (niter > 4 || total_iter > 400000)) {
            is[0] = y;
            // we give up precise intersection here, just restore the saved env
            restore_env(e, &se, 1);
            if (niter > 0) {
                free_env(&me);
                niter = 0;
            }
            break;
        }
    }
    if (niter) {
        restore_env(e, &me, 1);
        free_env(&me);
    }
    free_env(&se);
    JL_GC_POP();
    return is[0];
}
```
-/
def intersectAll (n : Nat) (T : Types) (x y : Val)
    (intersecting : List (Val × Val) := []) : STM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    modify fun e => { e with Runions := { e.Runions with depth := 0, more := 0, used := 0 } }
    let se ← saveEnv
    let mut me : SavedEnv := se
    let mut niter : Nat := 0
    let mut totalIter : Nat := 0
    let mut is0 ← intersect n T x y .none intersecting
    if is0 == .bottom then
      restoreEnv se true
    else if !(← get).emptinessOnly then
      if ← hasNextUnionState true then
        let (ni, me') ← mergeEnv n T me se niter
        niter := ni
        me := me'
        restoreEnv se true
    let mut steps := n
    while ← nextUnionState true do
      if steps == 0 then outOfBudget
      steps := steps - 1
      if (← get).emptinessOnly && is0 != .bottom then
        break
      modify fun e => { e with Runions := { e.Runions with depth := 0, more := 0 } }
      let is1 ← intersect n T x y .none intersecting
      if is1 == .bottom then
        restoreEnv se true
      else do
        let doMerge ←
          if niter > 0 then pure true
          else if !(← get).emptinessOnly then hasNextUnionState true
          else pure false
        if doMerge then
          let (ni, me') ← mergeEnv n T me se niter
          niter := ni
          me := me'
          restoreEnv se true
      if is0 == .bottom then
        is0 := is1
      else if is1 != .bottom then
        is0 ← typeUnion n T (subOps n T) [is0, is1]
      totalIter := totalIter + 1
      if (← hasNextUnionState true) && (niter > 4 || totalIter > 400000) then
        is0 := y
        restoreEnv se true
        niter := 0
        break
    if niter > 0 then
      restoreEnv me true
    return is0
termination_by structural n

/-- `intersect_types`

Julia source: src/subtype.c:6469-6491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *intersect_types(jl_value_t *x, jl_value_t *y, int emptiness_only) JL_CANSAFEPOINT
{
    jl_stenv_t e;
    if (obviously_disjoint(x, y, 0))
        return jl_bottom_type;
    if (jl_is_dispatch_tupletype(x) || jl_is_dispatch_tupletype(y)) {
        if (jl_subtype(x, y))
            return x;
        else if (jl_subtype(y, x))
            return y;
        else
            return jl_bottom_type;
    }
    init_stenv(&e, NULL, 0);
    e.intersection = 1;
    e.emptiness_only = emptiness_only;
    e.closed_inputs = -1;
    e.inputs[0] = x;
    e.inputs[1] = y;
    jl_value_t *ans = intersect_all(x, y, &e);
    free_stenv(&e);
    return ans;
}
```
-/
def intersectTypes (n : Nat) (T : Types) (x y : Val) (emptinessOnly : Bool) : CM Val :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if ← obviouslyDisjoint n T x y false then
      return .bottom
    let dtX ← jlIsDispatchTupletype T x
    let dtY ← if dtX then pure true else jlIsDispatchTupletype T y
    if dtY then
      if ← jlSubtype n T x y then
        return x
      else if ← jlSubtype n T y x then
        return y
      else
        return .bottom
    let e : StEnv := { initStenv with
      intersection := true
      emptinessOnly := emptinessOnly
      closedInputs := none
      inputs := (x, y)
    }
    return (← (intersectAll n T x y []).run e).1
termination_by structural n

/-- `jl_has_empty_intersection`

Julia source: src/subtype.c:6499-6502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_has_empty_intersection(jl_value_t *x, jl_value_t *y)
{
    return intersect_types(x, y, 1) == jl_bottom_type;
}
```
-/
def jlHasEmptyIntersection (n : Nat) (T : Types) (x y : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    return (← intersectTypes n T x y true) == .bottom
termination_by structural n

/-- `Ops` callbacks for `jltypes.c`, with `hasEmptyIntersection` wired to `jlHasEmptyIntersection`. -/
def subOps (n : Nat) (T : Types) : Ops :=
  match n with
  | 0 => {
      subtype := fun _ _ => outOfBudget
      typesEqual := fun _ _ => outOfBudget
      isLeafBound := fun _ => outOfBudget
      hasEmptyIntersection := fun _ _ => outOfBudget
      obviouslyDisjoint := fun _ _ _ => outOfBudget }
  | n + 1 => {
      subtype := jlSubtype n T
      typesEqual := jlTypesEqual n T
      isLeafBound := isLeafBound n T
      hasEmptyIntersection := jlHasEmptyIntersection n T
      obviouslyDisjoint := obviouslyDisjoint n T }
termination_by structural n

/-- `obvious_subtype`; `none` is the C return value 0 (undecided).

Julia source: src/subtype.c:3666-4027 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int obvious_subtype(jl_value_t *x, jl_value_t *y, jl_value_t *y0, int *subtype)
{
    if (x == y || y == (jl_value_t*)jl_any_type) {
        *subtype = 1;
        return 1;
    }
    while (jl_is_unionall(x)) {
        if (!jl_is_unionall(y)) {
            if (obvious_subtype(jl_unwrap_unionall(x), y, y0, subtype) && !*subtype)
                return 1;
            return 0;
        }
        x = ((jl_unionall_t*)x)->body;
        y = ((jl_unionall_t*)y)->body;
    }
    if (jl_is_unionall(y))
        y = jl_unwrap_unionall(y);
    if (is_typeofbottom_typealias(x))
        x = (jl_value_t*)jl_typeofbottom_type;
    if (is_typeofbottom_typealias(y))
        y = (jl_value_t*)jl_typeofbottom_type;
    if (x == y || y == (jl_value_t*)jl_any_type) {
        *subtype = 1;
        return 1;
    }
    if (jl_is_typevar(x)) {
        return 0;
    }
    if (jl_is_typevar(y)) {
        return 0;
    }
    if (x == (jl_value_t*)jl_bottom_type) {
        *subtype = 1;
        return 1;
    }
    if (y == (jl_value_t*)jl_bottom_type) {
        *subtype = 0;
        return 1;
    }
    if (jl_is_vararg(x)) {
        if (!jl_is_vararg(y)) {
            *subtype = 0;
            return 1;
        }
        return 0;
    }
    // `Intersect` is an internal meet node, not a real type tag. Handle it
    // before the non-type fallback, which would otherwise treat it as egal-only.
    if (jl_is_intersecttype(y)) {
        jl_intersecttype_t *iy = (jl_intersecttype_t*)y;
        int sub_a, sub_b;
        int known_a = obvious_subtype(x, iy->a, y0, &sub_a);
        if (known_a && !sub_a) {
            *subtype = 0;
            return 1;
        }
        int known_b = obvious_subtype(x, iy->b, y0, &sub_b);
        if (known_b && !sub_b) {
            *subtype = 0;
            return 1;
        }
        if (known_a && sub_a && known_b && sub_b) {
            *subtype = 1;
            return 1;
        }
        return 0;
    }
    if (jl_is_intersecttype(x))
        return 0;
    if (!jl_is_type(x) || !jl_is_type(y)) {
        *subtype = jl_egal(x, y);
        return 1;
    }
    if (jl_is_typeegal(x)) {
        jl_value_t *A = jl_typeegal_T(x);
        if (jl_is_typeegal(y)) {
            *subtype = jl_egal(A, jl_typeegal_T(y)); // `TypeEgal{A} <: TypeEgal{B}` iff `A === B`
            return 1;
        }
        // `Type{B}` (equality) and unions are left for the full subtype check
        if (jl_is_datatype(y))
            return obvious_subtype(jl_typeof(A), y, y0, subtype);
        return 0;
    }
    if (jl_is_typeegal(y)) {
        // nothing but `Union{}` (handled above) and egal `TypeEgal`s is a subtype
        *subtype = 0;
        return 1;
    }
    if (jl_is_uniontype(x)) {
        // TODO: consider handling more LHS unions, being wary of covariance
        jl_value_t *xa = ((jl_uniontype_t*)x)->a;
        jl_value_t *xb = ((jl_uniontype_t*)x)->b;
        if (obvious_subtype(xa, y, y0, subtype) && *subtype) {
            if (obvious_subtype(xb, y, y0, subtype) && *subtype)
                return 1;
        }
        //if (obvious_subtype(((jl_uniontype_t*)x)->a, y, y0, subtype)) {
        //    if (!*subtype)
        //        return 1;
        //    if (obvious_subtype(((jl_uniontype_t*)x)->b, y, y0, subtype))
        //        return 1;
        //}
        //else if (obvious_subtype(((jl_uniontype_t*)x)->b, y, y0, subtype)) {
        //    if (!*subtype)
        //        return 1;
        //}
        return 0;
    }
    if (jl_is_uniontype(y)) {
        jl_value_t *ya = ((jl_uniontype_t*)y)->a;
        jl_value_t *yb = ((jl_uniontype_t*)y)->b;
        if (obvious_subtype(x, ya, y0, subtype)) {
            if (*subtype)
                return 1;
            if (obvious_subtype(x, yb, y0, subtype))
                return 1;
        }
        else if (obvious_subtype(x, yb, y0, subtype)) {
            if (*subtype)
                return 1;
        }
        return 0;
    }
    if (x == (jl_value_t*)jl_any_type) {
        *subtype = 0;
        return 1;
    }
    // `Type{T}` is a `TypeEq`, not a `DataType`, so the `jl_is_datatype` cases
    // below miss it; decide the obvious `X <: Type{T}` rejections here.
    if (jl_is_typeeq(y) && !jl_is_typeeq(x) && jl_is_datatype(x) &&
            x != (jl_value_t*)jl_typeofbottom_type) {
        jl_value_t *t0 = jl_typeeq_T(y);
        if (jl_is_typevar(t0)) {
            if (!is_kind_or_anytype(x)) {
                *subtype = 0;    // an ordinary type value is never a subtype of `Type{T}`
                return 1;
            }
            return 0;            // a kind may be: `Type <: Type{T}` is handled by `subtype`
        }
        if (!jl_is_typeeq(t0)) {
            *subtype = 0;        // `X <: Type{ConcreteType}` (X not a `Type{}`) is never true
            return 1;
        }
        // `Type{Type{...}}`: leave to `subtype`
    }
    if (jl_is_datatype(y)) {
        int istuple = (((jl_datatype_t*)y)->name == jl_tuple_typename);
        int iscov = istuple;
        // TODO: this would be a nice fast-path to have, unfortunately,
        //       datatype allocation fails to correctly hash-cons them
        //       and the subtyping tests include tests for this case
        //if (!iscov && ((jl_datatype_t*)y)->isconcretetype && !jl_is_typeeq(x)) {
        //    *subtype = 0;
        //    return 1;
        //}
        if (jl_is_datatype(x)) {
            // Weaker version of above, but runs into the same problem
            //if (((jl_datatype_t*)x)->isconcretetype && ((jl_datatype_t*)y)->isconcretetype && (!istuple || !istuple_x)) {
            //    *subtype = 0;
            //    return 1;
            //}
            int uncertain = 0;
            if (((jl_datatype_t*)x)->name != ((jl_datatype_t*)y)->name) {
                jl_datatype_t *temp = (jl_datatype_t*)x;
                while (temp->name != ((jl_datatype_t*)y)->name) {
                    // raw read: this heuristic must not reach a safepoint, so
                    // a deferred (unset) supertype stays undecided and the
                    // full algorithm resolves it
                    temp = temp->super;
                    if (temp == NULL)
                        return 0;
                    if (temp == jl_any_type) {
                        *subtype = 0;
                        return 1;
                    }
                }
                if (obvious_subtype((jl_value_t*)temp, y, y0, subtype) && *subtype)
                    return 1;
                return 0;
            }
            if (!iscov && !((jl_datatype_t*)x)->hasfreetypevars) {
                // by transitivity, if `wrapper <: y`, then `x <: y` if x is a leaf type of its name
                jl_value_t *wrapper = ((jl_datatype_t*)x)->name->wrapper;
                int wrapper_sub = 0;
                JL_GC_PUSH1(&wrapper);
                wrapper_sub = obvious_subtype(wrapper, y, y0, subtype);
                JL_GC_POP();
                if (wrapper_sub && *subtype)
                    return 1;
            }
            int i, npx = jl_nparams(x), npy = jl_nparams(y);
            jl_vararg_kind_t vx = JL_VARARG_NONE;
            jl_vararg_kind_t vy = JL_VARARG_NONE;
            jl_value_t *vxt = NULL;
            int nparams_expanded_x = npx;
            int nparams_expanded_y = npy;
            if (istuple) {
                if (npx > 0) {
                    jl_value_t *xva = jl_tparam(x, npx - 1);
                    vx = jl_vararg_kind(xva);
                    if (vx != JL_VARARG_NONE) {
                        vxt = jl_unwrap_vararg(xva);
                        nparams_expanded_x -= 1;
                        if (vx == JL_VARARG_INT)
                            nparams_expanded_x += jl_vararg_length(xva);
                    }
                }
                if (npy > 0) {
                    jl_value_t *yva = jl_tparam(y, npy - 1);
                    vy = jl_vararg_kind(yva);
                    if (vy != JL_VARARG_NONE) {
                        nparams_expanded_y -= 1;
                        if (vy == JL_VARARG_INT)
                            nparams_expanded_y += jl_vararg_length(yva);
                    }
                }
                // if the nparams aren't equal, or at least one of them is a typevar (uncertain), they may be obviously disjoint
                if (nparams_expanded_x != nparams_expanded_y || (vx != JL_VARARG_NONE && vx != JL_VARARG_INT) || (vy != JL_VARARG_NONE && vy != JL_VARARG_INT)) {
                    // we have a stronger bound on x if:
                    if (vy == JL_VARARG_NONE || vy == JL_VARARG_INT) { // the bound on y is certain
                        if (vx == JL_VARARG_NONE || vx == JL_VARARG_INT || vx == JL_VARARG_UNBOUND || // and the bound on x is also certain
                            nparams_expanded_x > nparams_expanded_y || npx > nparams_expanded_y) { // or x is unknown, but definitely longer than y
                            *subtype = 0;
                            return 1; // number of fixed parameters in x are more than declared in y
                        }
                    }
                    if (nparams_expanded_x < nparams_expanded_y) {
                        *subtype = 0;
                        return 1; // number of fixed parameters in x could be fewer than in y
                    }
                    uncertain = 1;
                }
            }
            else if (npx != npy) {
                *subtype = 0;
                return 1;
            }

            // inspect the fixed parameters in y against x
            for (i = 0; i < npy - (vy == JL_VARARG_NONE ? 0 : 1); i++) {
                jl_value_t *a;
                if (i >= (npx - (vx == JL_VARARG_NONE ? 0 : 1))) {
                    a = vxt;
                    assert(a != NULL);
                }
                else {
                    a = jl_tparam(x, i);
                }
                jl_value_t *b = jl_tparam(y, i);
                if (iscov || jl_is_typevar(b)) {
                    if (obvious_subtype(a, b, y0, subtype)) {
                        if (!*subtype)
                            return 1;
                        if (jl_has_free_typevars(b)) // b is actually more constrained that this
                            uncertain = 1;
                    }
                    else {
                        uncertain = 1;
                    }
                }
                else {
                    if (!obviously_egal(a, b)) {
                        if (obvious_subtype(a, b, y0, subtype)) {
                            if (!*subtype)
                                return 1;
                            if (jl_has_free_typevars(b)) // b is actually more constrained that this
                                uncertain = 1;
                        }
                        else {
                            uncertain = 1;
                        }
                        if (!jl_has_free_typevars(b) && obvious_subtype(b, a, y0, subtype)) {
                            if (!*subtype)
                                return 1;
                            if (jl_has_free_typevars(a)) // a is actually more constrained that this
                                uncertain = 1;
                        }
                        else {
                            uncertain = 1;
                        }
                    }
                }
            }
            if (i < nparams_expanded_x) {
                // there are elements left in x (possibly just a Vararg), check them against the Vararg tail of y too
                assert(vy != JL_VARARG_NONE && istuple && iscov);
                jl_value_t *a1 = (vx != JL_VARARG_NONE && i >= npx - 1) ? vxt : jl_tparam(x, i);
                jl_value_t *b = jl_unwrap_vararg(jl_tparam(y, i));
                if (jl_is_typevar(b)) {
                    jl_value_t *body = find_var_body(y0, (jl_tvar_t*)b);
                    if (body == NULL)
                        body = y0;
                    if (var_occurs_invariant(body, (jl_tvar_t*)b))
                        return 0;
                }
                if (nparams_expanded_x > npy && jl_is_typevar(b) && is_leaf_typevar((jl_tvar_t *)b) && concrete_min(a1) > 1) {
                    // diagonal rule for 2 or more elements: they must all be concrete on the LHS
                    *subtype = 0;
                    return 1;
                }
                jl_value_t *a1u = jl_unwrap_unionall(a1);
                // only `TypeEgal{T}` (a tag-exact singleton) and `Type{Union{}}`
                // (`== TypeofBottom`) lie in their `typeof`; other `Type{T}`
                // elements straddle kinds (#33136) and are left to the full
                // algorithm below (conservatively marked uncertain)
                if (jl_is_typeegal(a1u) ||
                    (jl_is_typeeq(a1u) && jl_typeeq_T(a1u) == jl_bottom_type)) {
                    a1 = jl_typeof(jl_some_Type_T(a1u));
                }
                for (; i < nparams_expanded_x; i++) {
                    jl_value_t *a = (vx != JL_VARARG_NONE && i >= npx - 1) ? vxt : jl_tparam(x, i);
                    if (i > npy && jl_is_typevar(b) && is_leaf_typevar((jl_tvar_t *)b)) { // i == npy implies a == a1
                        // diagonal rule: all the later parameters are also constrained to be type-equal to the first
                        jl_value_t *a2 = a;
                        jl_value_t *au = jl_unwrap_unionall(a);
                        if (jl_is_typeegal(au) ||
                            (jl_is_typeeq(au) && jl_typeeq_T(au) == jl_bottom_type)) {
                            // a `TypeEgal{T}` (or `Type{Union{}}`) element lies
                            // exactly in the concrete typeof(T); see above
                            a2 = jl_typeof(jl_some_Type_T(au));
                        }
                        if (!obviously_egal(a1, a2)) {
                            if (obvious_subtype(a2, a1, y0, subtype)) {
                                if (!*subtype)
                                    return 1;
                                if (jl_has_free_typevars(a1)) // a1 is actually more constrained that this
                                    uncertain = 1;
                            }
                            else {
                                uncertain = 1;
                            }
                            if (obvious_subtype(a1, a2, y0, subtype)) {
                                if (!*subtype)
                                    return 1;
                                if (jl_has_free_typevars(a2)) // a2 is actually more constrained that this
                                    uncertain = 1;
                            }
                            else {
                                uncertain = 1;
                            }
                        }
                    }
                    if (obvious_subtype(a, b, y0, subtype)) {
                        if (!*subtype)
                            return 1;
                        if (jl_has_free_typevars(b)) // b is actually more constrained that this
                            uncertain = 1;
                    }
                    else {
                        uncertain = 1;
                    }
                }
            }
            if (uncertain)
                return 0;
            *subtype = 1;
            return 1;
        }
    }
    return 0;
}
```
-/
def obviousSubtype (n : Nat) (T : Types) (x0 y0 yorig : Val) : CM (Option Bool) := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    let mut x := x0
    let mut y := y0
    if x == y || y == anyType then return some true
    let mut finished := false
    for _ in [0:n] do
      if !x.isUnionall then finished := true; break
      if !y.isUnionall then
        if (← obviousSubtype n T x.unwrapUnionall y yorig) == some false then return some false
        return none
      x := x.uaBody
      y := y.uaBody
    if !finished then outOfBudget
    y := y.unwrapUnionall
    x ← normalizeTypeofbottomTypealias n x
    y ← normalizeTypeofbottomTypealias n y
    if x == y || y == anyType then return some true
    if x.isTypevar || y.isTypevar then return none
    if x == .bottom then return some true
    if y == .bottom then return some false
    if x.isVararg then return if y.isVararg then none else some false
    if let .intersect a b := y then
      let ka ← obviousSubtype n T x a yorig
      if ka == some false then return some false
      let kb ← obviousSubtype n T x b yorig
      if kb == some false then return some false
      if ka == some true && kb == some true then return some true
      return none
    if x.isIntersect then return none
    if !x.isType || !y.isType then return some (← egal n T x y)
    if x.isTypeegal then
      let a := x.someTypeT
      if y.isTypeegal then return some (← egal n T a y.someTypeT)
      if y.isDatatype then return ← obviousSubtype n T (typeOf a) y yorig
      return none
    if y.isTypeegal then return some false
    if let .union a b := x then
      if (← obviousSubtype n T a y yorig) == some true then
        if (← obviousSubtype n T b y yorig) == some true then return some true
      return none
    if let .union a b := y then
      match ← obviousSubtype n T x a yorig with
      | some true => return some true
      | some false => return ← obviousSubtype n T x b yorig
      | none =>
        if (← obviousSubtype n T x b yorig) == some true then return some true
        return none
    if x == anyType then return some false
    if y.isTypeeq && !x.isTypeeq && x.isDatatype && x != typeofbottomType then
      let tp := y.someTypeT
      if tp.isTypevar then
        if !isKindOrAnytype x then return some false
        return none
      if !tp.isTypeeq then return some false
    if y.isDatatype && x.isDatatype then
      let istuple := y.isTupleType
      let mut uncertain := false
      if x.name? != y.name? then
        let mut temp := x
        let mut reachedName := false
        for _ in [0:n] do
          if temp.name? == y.name? then reachedName := true; break
          temp ← superOf n T (subOps n T) temp
          if temp == anyType then return some false
        if !reachedName then outOfBudget
        if (← obviousSubtype n T temp y yorig) == some true then return some true
        return none
      if !istuple && !x.dtHasFreeTypevars then
        let wrapper := (← T.typename (x.name?.getD "")).wrapper
        if (← obviousSubtype n T wrapper y yorig) == some true then return some true
      let npx := x.nparams
      let npy := y.nparams
      let mut vx := VarargKind.none
      let mut vy := VarargKind.none
      let mut vxt := Val.bottom
      let mut nx : Int := npx
      let mut ny : Int := npy
      if istuple then
        if npx > 0 then
          let va := x.params[npx-1]!
          vx := va.varargKind
          if vx != .none then
            vxt := va.unwrapVararg
            nx := nx - 1
            if vx == .int then
              let some (.long len) := va.varargN? | throw "Vararg integer length assertion"
              nx := nx + len
        if npy > 0 then
          let va := y.params[npy-1]!
          vy := va.varargKind
          if vy != .none then
            ny := ny - 1
            if vy == .int then
              let some (.long len) := va.varargN? | throw "Vararg integer length assertion"
              ny := ny + len
        if nx != ny || (vx != .none && vx != .int) || (vy != .none && vy != .int) then
          if vy == .none || vy == .int then
            if vx == .none || vx == .int || vx == .unbound || nx > ny || (npx : Int) > ny then return some false
          if nx < ny then return some false
          uncertain := true
      else if npx != npy then return some false
      let fixedY := npy - (if vy == .none then 0 else 1)
      let fixedX := npx - (if vx == .none then 0 else 1)
      for i in [0:fixedY] do
        let a := if i ≥ fixedX then vxt else x.params[i]!
        let b := y.params[i]!
        if istuple || b.isTypevar then
          match ← obviousSubtype n T a b yorig with
          | some false => return some false
          | some true => if b.hasFreeTypevars then uncertain := true
          | none => uncertain := true
        else if !(← obviouslyEgal n T a b) then
          match ← obviousSubtype n T a b yorig with
          | some false => return some false
          | some true => if b.hasFreeTypevars then uncertain := true
          | none => uncertain := true
          if !b.hasFreeTypevars then
            match ← obviousSubtype n T b a yorig with
            | some false => return some false
            | some true => if a.hasFreeTypevars then uncertain := true
            | none => uncertain := true
          else uncertain := true
      if (fixedY : Int) < nx then
        if vy == .none || !istuple then throw "obvious_subtype: tuple tail assertion"
        let mut a1 := if vx != .none && fixedY ≥ npx - 1 then vxt else x.params[fixedY]!
        let b := y.params[fixedY]!.unwrapVararg
        if b.isTypevar then
          let body := (← findVarBody n yorig b).getD yorig
          if ← varOccursInvariant n body b then return none
        if nx > (npy : Int) && b.isTypevar then
          if ← isLeafTypevar n T b then
            if (← concreteMin n T a1) > 1 then return some false
        let a1u := a1.unwrapUnionall
        if a1u.isTypeegal || (a1u.isTypeeq && a1u.someTypeT == .bottom) then a1 := typeOf a1u.someTypeT
        for i in [fixedY:nx.toNat] do
          let a := if vx != .none && i ≥ npx - 1 then vxt else x.params[i]!
          if i > npy && b.isTypevar then
            if ← isLeafTypevar n T b then
              let au := a.unwrapUnionall
              let a2 := if au.isTypeegal || (au.isTypeeq && au.someTypeT == .bottom) then typeOf au.someTypeT else a
              if !(← obviouslyEgal n T a1 a2) then
                match ← obviousSubtype n T a2 a1 yorig with
                | some false => return some false
                | some true => if a1.hasFreeTypevars then uncertain := true
                | none => uncertain := true
                match ← obviousSubtype n T a1 a2 yorig with
                | some false => return some false
                | some true => if a2.hasFreeTypevars then uncertain := true
                | none => uncertain := true
          match ← obviousSubtype n T a b yorig with
          | some false => return some false
          | some true => if b.hasFreeTypevars then uncertain := true
          | none => uncertain := true
      return if uncertain then none else some true
    return none
termination_by structural n

/-- `jl_subtype_env(x,y,NULL,0)`; debug and release builds return the same heuristic answer.

Julia source: src/subtype.c:4038-4085 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_subtype_env(jl_value_t *x, jl_value_t *y, jl_value_t **env, int envsz)
{
    jl_stenv_t e;
    if (y == (jl_value_t*)jl_any_type || x == jl_bottom_type)
        return 1;
    if (x == y ||
        (jl_typeof(x) == jl_typeof(y) &&
         (jl_is_unionall(y) || jl_is_uniontype(y) || jl_is_some_Type(y)) &&
         jl_types_struct_equiv(x, y))) {
        if (envsz != 0) { // quickly copy env from x
            jl_unionall_t *ua = (jl_unionall_t*)x;
            int i;
            for (i = 0; i < envsz; i++) {
                assert(jl_is_unionall(ua));
                int constrained = constrains_param_static(ua->var, ua->body, 1);
                env[i] = wrap_tvar_env((jl_value_t*)ua->var, constrained);
                ua = (jl_unionall_t*)ua->body;
            }
        }
        return 1;
    }
    if (jl_is_typeapp(x) || jl_is_typeapp(y))
        jl_error("internal error: TypeApp in subtyping");
    int obvious_subtype = 2;
    if (jl_obvious_subtype(x, y, &obvious_subtype)) {
#ifdef NDEBUG
        if (obvious_subtype == 0)
            return obvious_subtype;
        else if (envsz == 0)
            return obvious_subtype;
#endif
    }
    else {
        obvious_subtype = 3;
    }
    init_stenv(&e, env, envsz);
    e.closed_inputs = -1;
    e.inputs[0] = x;
    e.inputs[1] = y;
    int subtype = forall_exists_subtype(x, y, &e, PARAM_NONE);
    free_stenv(&e);
    assert(obvious_subtype == 3 || obvious_subtype == subtype || jl_has_free_typevars(x) || jl_has_free_typevars(y));
#ifndef NDEBUG
    if (obvious_subtype == 0 || (obvious_subtype == 1 && envsz == 0))
        subtype = obvious_subtype; // this ensures that running in a debugger doesn't change the result
#endif
    return subtype;
}
```
-/
def jlSubtypeEnv (n : Nat) (T : Types) (x y : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if y == anyType || x == .bottom then return true
    if x == y then return true
    if typeOf x == typeOf y && (y.isUnionall || y.isUnion || y.isSomeType) then
      if ← typesStructEquiv n T x y then return true
    if x.isTypeapp || y.isTypeapp then throw "internal error: TypeApp in subtyping"
    if let some answer ← obviousSubtype n T x y y then return answer
    let e := { initStenv with closedInputs := none, inputs := (x, y) }
    return (← (forallExistsSubtype n T x y .none).run e).1
termination_by structural n

/-- `jl_subtype`.

Julia source: src/subtype.c:4105-4108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_subtype(jl_value_t *x, jl_value_t *y)
{
    return jl_subtype_env(x, y, NULL, 0);
}
```
-/
def jlSubtype (n : Nat) (T : Types) (a b : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 => jlSubtypeEnv n T a b
termination_by structural n

/-- `jl_types_equal`, interleaving both heuristic checks before full subtyping.

Julia source: src/subtype.c:4110-4190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_types_equal(jl_value_t *a, jl_value_t *b)
{
    if (a == b)
        return 1;
    if (jl_typeof(a) == jl_typeof(b) && jl_types_struct_equiv(a, b))
        return 1;
    if (obviously_unequal(a, b))
        return 0;
    // the following is an interleaved version of:
    //   return jl_subtype(a, b) && jl_subtype(b, a)
    // where we try to do the fast checks before the expensive ones
    if (jl_is_datatype(a) && !jl_is_concrete_type(b)) {
        // if one type looks simpler, check it on the right
        // first in order to reject more quickly.
        jl_value_t *temp = a;
        a = b;
        b = temp;
    }
    // first check if a <: b has an obvious answer
    int subtype_ab = 2;
    if (b == (jl_value_t*)jl_any_type || a == jl_bottom_type) {
        subtype_ab = 1;
    }
    else if (jl_obvious_subtype(a, b, &subtype_ab)) {
#ifdef NDEBUG
        if (subtype_ab == 0)
            return 0;
#endif
    }
    else {
        subtype_ab = 3;
    }
    // next check if b <: a has an obvious answer
    int subtype_ba = 2;
    if (a == (jl_value_t*)jl_any_type || b == jl_bottom_type) {
        subtype_ba = 1;
    }
    else if (jl_obvious_subtype(b, a, &subtype_ba)) {
#ifdef NDEBUG
        if (subtype_ba == 0)
            return 0;
#endif
    }
    else {
        subtype_ba = 3;
    }
    // finally, do full subtyping for any inconclusive test
    jl_stenv_t e;
#ifdef NDEBUG
    if (subtype_ab != 1)
#endif
    {
        init_stenv(&e, NULL, 0);
        int subtype = forall_exists_subtype(a, b, &e, PARAM_NONE);
        free_stenv(&e);
        assert(subtype_ab == 3 || subtype_ab == subtype || jl_has_free_typevars(a) || jl_has_free_typevars(b));
#ifndef NDEBUG
        if (subtype_ab != 0 && subtype_ab != 1) // ensures that running in a debugger doesn't change the result
#endif
        subtype_ab = subtype;
#ifdef NDEBUG
        if (subtype_ab == 0)
            return 0;
#endif
    }
#ifdef NDEBUG
    if (subtype_ba != 1)
#endif
    {
        init_stenv(&e, NULL, 0);
        int subtype = forall_exists_subtype(b, a, &e, PARAM_NONE);
        free_stenv(&e);
        assert(subtype_ba == 3 || subtype_ba == subtype || jl_has_free_typevars(a) || jl_has_free_typevars(b));
#ifndef NDEBUG
        if (subtype_ba != 0 && subtype_ba != 1) // ensures that running in a debugger doesn't change the result
#endif
        subtype_ba = subtype;
    }
    // all tests successful
    return subtype_ab && subtype_ba;
}
```
-/
def jlTypesEqual (n : Nat) (T : Types) (a0 b0 : Val) : CM Bool := do
  match n with
  | 0 => outOfBudget
  | n + 1 =>
    if a0 == b0 then return true
    if typeOf a0 == typeOf b0 then if ← typesStructEquiv n T a0 b0 then return true
    if ← obviouslyUnequal n T a0 b0 then return false
    let swap ← if a0.isDatatype then pure (!(← isConcreteType T b0)) else pure false
    let a := if swap then b0 else a0
    let b := if swap then a0 else b0
    let ab ← if b == anyType || a == .bottom then pure (some true) else obviousSubtype n T a b b
    if ab == some false then return false
    let ba ← if a == anyType || b == .bottom then pure (some true) else obviousSubtype n T b a a
    if ba == some false then return false
    if ab != some true then
      let (ans, _) ← (forallExistsSubtype n T a b .none).run initStenv
      if !ans then return false
    if ba != some true then
      let (ans, _) ← (forallExistsSubtype n T b a .none).run initStenv
      if !ans then return false
    return true
termination_by structural n
end

/-- `jl_obviously_unequal`.

Julia source: src/subtype.c:744-747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_obviously_unequal(jl_value_t *a, jl_value_t *b)
{
    return obviously_unequal(a, b);
}
```
-/
def jlObviouslyUnequal (n : Nat) (T : Types) (a b : Val) : CM Bool := obviouslyUnequal n T a b

/-- `jl_obvious_subtype`.

Julia source: src/subtype.c:4029-4032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_obvious_subtype(jl_value_t *x, jl_value_t *y, int *subtype)
{
    return obvious_subtype(x, y, y, subtype);
}
```
-/
def jlObviousSubtype (n : Nat) (T : Types) (x y : Val) : CM (Option Bool) := obviousSubtype n T x y y


/-- `jl_isa`

Julia source: src/subtype.c:4253-4309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_isa(jl_value_t *x, jl_value_t *t)
{
    if (t == (jl_value_t*)jl_any_type || jl_typetagis(x,t))
        return 1;
    if (jl_typetagof(x) < (jl_max_tags << 4) && jl_is_datatype(t) && jl_typetagis(x,((jl_datatype_t*)t)->smalltag << 4))
        return 1;
    if (jl_is_typeapp(t))
        jl_error("internal error: TypeApp in jl_isa");
    if (jl_is_type(x)) {
        if (t == (jl_value_t*)jl_type_type)
            return 1;
        if (!jl_has_free_typevars(x)) {
            if (jl_is_concrete_type(t))
                return 0;
            if (jl_is_typeeq(t))
                return jl_types_equal(x, jl_typeeq_T(t));
            if (jl_is_typeegal(t))
                return jl_egal(x, jl_typeegal_T(t));
            jl_value_t *t2 = jl_unwrap_unionall(t);
            if (jl_is_typeeq(t2)) {
                jl_value_t *tp = jl_typeeq_T(t2);
                if (jl_is_typevar(tp)) {
                    if (((jl_tvar_t*)tp)->lb == jl_bottom_type) {
                        while (jl_is_typevar(tp))
                            tp = ((jl_tvar_t*)tp)->ub;
                        if (!jl_has_free_typevars(tp))
                            return jl_subtype(x, tp);
                    }
                    else if (((jl_tvar_t*)tp)->ub == (jl_value_t*)jl_any_type) {
                        while (jl_is_typevar(tp))
                            tp = ((jl_tvar_t*)tp)->lb;
                        if (!jl_has_free_typevars(tp))
                            return jl_subtype(tp, x);
                    }
                }
            }
            else if (jl_is_datatype(t2)) {
                return jl_subtype(jl_typeof(x), t);
            }
            if (jl_subtype(jl_typeof(x), t))
                return 1;
            if (jl_has_intersect_type_not_kind(t2)) {
                // wrap as the egality kind: `TypeEgal{x} <: Type{B}` also holds
                // whenever `x == B`, so this covers both wrapper kinds in `t`
                jl_value_t *wrapped = jl_wrap_TypeEgal(x);  // TODO jb/subtype avoid jl_wrap_TypeEgal
                JL_GC_PUSH1(&wrapped);
                int ans = jl_subtype(wrapped, t);
                JL_GC_POP();
                return ans;
            }
            return 0;
        }
    }
    if (jl_is_concrete_type(t))
        return 0;
    return jl_subtype(jl_typeof(x), t);
}
```
-/
def jlIsa (n : Nat) (T : Types) (x t : Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if t == anyType || typeOf x == t then
      return true
    if t.isTypeapp then
      throw "internal error: TypeApp in jl_isa"
    if x.isType then
      if t == typeType then
        return true
      if !x.hasFreeTypevars then
        if ← isConcreteType T t then
          return false
        if t.isTypeeq then
          return ← jlTypesEqual n T x t.someTypeT
        if t.isTypeegal then
          return ← egal n T x t.someTypeT
        let t2 := t.unwrapUnionall
        if t2.isTypeeq then
          let mut tp := t2.someTypeT
          if tp.isTypevar then
            if tp.tvLb == .bottom then
              let mut steps := n
              while tp.isTypevar do
                if steps == 0 then outOfBudget
                steps := steps - 1
                tp := tp.tvUb
              if !tp.hasFreeTypevars then
                return ← jlSubtype n T x tp
            else if tp.tvUb == anyType then
              let mut steps := n
              while tp.isTypevar do
                if steps == 0 then outOfBudget
                steps := steps - 1
                tp := tp.tvLb
              if !tp.hasFreeTypevars then
                return ← jlSubtype n T tp x
        else if t2.isDatatype then
          return ← jlSubtype n T (typeOf x) t
        if ← jlSubtype n T (typeOf x) t then
          return true
        if ← jlHasIntersectTypeNotKind n t2 then
          let wrapped ← wrapTypeEgal x
          return ← jlSubtype n T wrapped t
        return false
    if ← isConcreteType T t then
      return false
    jlSubtype n T (typeOf x) t

/-- `jl_tuple1_isa`

Julia source: src/subtype.c:4199-4219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_tuple1_isa(jl_value_t *child1, jl_value_t **child, size_t cl, jl_datatype_t *pdt)
{
    if (jl_is_tuple_type(pdt) && !jl_is_va_tuple(pdt)) {
        if (cl != jl_nparams(pdt))
            return 0;
        size_t i;
        if (!jl_isa(child1, jl_tparam(pdt, 0)))
            return 0;
        for (i = 1; i < cl; i++) {
            if (!jl_isa(child[i - 1], jl_tparam(pdt, i)))
                return 0;
        }
        return 1;
    }
    jl_value_t *tu = (jl_value_t*)arg_type_tuple(child1, child, cl);
    int ans;
    JL_GC_PUSH1(&tu);
    ans = jl_subtype(tu, (jl_value_t*)pdt);
    JL_GC_POP();
    return ans;
}
```
-/
def jlTuple1Isa (n : Nat) (T : Types) (child1 : Val) (child : List Val) (cl : Nat) (pdt : Val) :
    CM Bool := do
  if pdt.isTupleType && !pdt.isVaTuple then
    if cl != pdt.nparams then
      return false
    if !(← jlIsa n T child1 pdt.params[0]!) then
      return false
    for i in [1:cl] do
      if !(← jlIsa n T child[i - 1]! pdt.params[i]!) then
        return false
    return true
  let argTypes ← (child1 :: child).mapM fun v => do
    if v.isType then wrapTypeEgal v else pure (typeOf v)
  let tu := Val.datatype tupleName argTypes
  jlSubtype n T tu pdt

/-- `jl_tuple_isa`

Julia source: src/subtype.c:4221-4231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_tuple_isa(jl_value_t **child, size_t cl, jl_datatype_t *pdt)
{
    if (cl == 0) {
        if (pdt == jl_emptytuple_type)
            return 1;
        if (jl_is_tuple_type(pdt) && (jl_nparams(pdt) != 1 || !jl_is_va_tuple(pdt)))
            return 0;
        return jl_isa(jl_emptytuple, (jl_value_t*)pdt);
    }
    return jl_tuple1_isa(child[0], &child[1], cl, pdt);
}
```
-/
def jlTupleIsa (n : Nat) (T : Types) (child : List Val) (pdt : Val) : CM Bool := do
  match child with
  | [] =>
    if pdt == emptytupleType then
      return true
    if pdt.isTupleType && (pdt.nparams != 1 || !pdt.isVaTuple) then
      return false
    jlSubtype n T emptytupleType pdt
  | c1 :: rest =>
    jlTuple1Isa n T c1 rest (child.length) pdt


/-- `jl_intersect_types`

Julia source: src/subtype.c:6493-6496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_intersect_types(jl_value_t *x, jl_value_t *y) JL_CANSAFEPOINT
{
    return intersect_types(x, y, 0);
}
```
-/
def jlIntersectTypes (n : Nat) (T : Types) (x y : Val) : CM Val :=
  intersectTypes n T x y false

/-- `switch_union_tuple`: for (possibly unions or unionalls of) tuples `a` and `b`,
return the tuple of pointwise unions, or `none` (`NULL`).

Julia source: src/subtype.c:6523-6593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *switch_union_tuple(jl_value_t *a, jl_value_t *b) JL_CANSAFEPOINT
{
    if (jl_is_unionall(a)) {
        jl_unionall_t *ua = (jl_unionall_t*)a;
        if (jl_is_unionall(b)) {
            jl_unionall_t *ub = (jl_unionall_t*)b;
            if (ub->var->lb == ua->var->lb && ub->var->ub == ua->var->ub) {
                jl_value_t *ub2 = jl_instantiate_unionall(ub, (jl_value_t*)ua->var);
                jl_value_t *ans = NULL;
                JL_GC_PUSH2(&ub2, &ans);
                ans = switch_union_tuple(ua->body, ub2);
                if (ans != NULL)
                    ans = jl_type_unionall(ua->var, ans);
                JL_GC_POP();
                return ans;
            }
        }
        jl_value_t *ans = switch_union_tuple(ua->body, b);
        if (ans == NULL)
            return NULL;
        JL_GC_PUSH1(&ans);
        ans = jl_type_unionall(ua->var, ans);
        JL_GC_POP();
        return ans;
    }
    if (jl_is_unionall(b)) {
        jl_value_t *ans = switch_union_tuple(a, ((jl_unionall_t*)b)->body);
        if (ans == NULL)
            return NULL;
        JL_GC_PUSH1(&ans);
        ans = jl_type_unionall(((jl_unionall_t*)b)->var, ans);
        JL_GC_POP();
        return ans;
    }
    if (jl_is_uniontype(a)) {
        a = switch_union_tuple(((jl_uniontype_t*)a)->a, ((jl_uniontype_t*)a)->b);
        if (a == NULL)
            return NULL;
        JL_GC_PUSH1(&a);
        jl_value_t *ans = switch_union_tuple(a, b);
        JL_GC_POP();
        return ans;
    }
    if (jl_is_uniontype(b)) {
        b = switch_union_tuple(((jl_uniontype_t*)b)->a, ((jl_uniontype_t*)b)->b);
        if (b == NULL)
            return NULL;
        JL_GC_PUSH1(&b);
        jl_value_t *ans = switch_union_tuple(a, b);
        JL_GC_POP();
        return ans;
    }
    if (!jl_is_tuple_type(a) || !jl_is_tuple_type(b)) {
        return NULL;
    }
    if (jl_nparams(a) != jl_nparams(b) || jl_is_va_tuple((jl_datatype_t*)a) ||
            jl_is_va_tuple((jl_datatype_t*)b)) {
        return NULL;
    }
    jl_svec_t *vec = jl_alloc_svec(jl_nparams(a));
    JL_GC_PUSH1(&vec);
    for (int i = 0; i < jl_nparams(a); i++) {
        jl_value_t *ts[2];
        ts[0] = jl_tparam(a, i);
        ts[1] = jl_tparam(b, i);
        jl_svecset(vec, i, jl_type_union(ts, 2));
    }
    jl_value_t *ans = jl_apply_tuple_type(vec, 1);
    JL_GC_POP();
    return ans;
}
```
-/
def switchUnionTuple (n : Nat) (T : Types) (a b : Val) : CM (Option Val) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if a.isUnionall then
      let uavar := a.uaVar
      let uabody := a.uaBody
      if b.isUnionall then
        let ubvar := b.uaVar
        if ubvar.tvLb == uavar.tvLb && ubvar.tvUb == uavar.tvUb then
          let ub2 ← instantiateUnionall n T (subOps n T) b uavar
          let ans? ← switchUnionTuple n T uabody ub2
          match ans? with
          | some ans => return some (← typeUnionall n T (subOps n T) uavar ans)
          | none => return none
      let ans? ← switchUnionTuple n T uabody b
      match ans? with
      | none => return none
      | some ans => return some (← typeUnionall n T (subOps n T) uavar ans)
    if b.isUnionall then
      let ans? ← switchUnionTuple n T a b.uaBody
      match ans? with
      | none => return none
      | some ans => return some (← typeUnionall n T (subOps n T) b.uaVar ans)
    if let .union ua ub := a then
      let some a' ← switchUnionTuple n T ua ub | return none
      return ← switchUnionTuple n T a' b
    if let .union va vb := b then
      let some b' ← switchUnionTuple n T va vb | return none
      return ← switchUnionTuple n T a b'
    if !a.isTupleType || !b.isTupleType then
      return none
    if a.nparams != b.nparams || a.isVaTuple || b.isVaTuple then
      return none
    let mut vec : List Val := []
    for i in [0:a.nparams] do
      let u ← typeUnion n T (subOps n T) [a.params[i]!, b.params[i]!]
      vec := vec ++ [u]
    instDatatypeInner n T (subOps n T) tupleName vec true 0

/-- `jl_type_intersection_env_s(a, b, penv, &issubty)`: returns `(ans, env, issubty)`.

Julia source: src/subtype.c:6628-6738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_type_intersection_env_s(jl_value_t *a, jl_value_t *b, jl_svec_t **penv, int *issubty)
{
    if (issubty) *issubty = 0;
    if (obviously_disjoint(a, b, 0)) {
        if (issubty && a == jl_bottom_type) *issubty = 1;
        return jl_bottom_type;
    }
    if (jl_is_typeapp(a) || jl_is_typeapp(b))
        jl_error("internal error: TypeApp in type intersection");
    int szb = penv ? jl_subtype_env_size(b) : 0;
    int sz = 0, i = 0;
    jl_value_t **env, **ans;
    JL_GC_PUSHARGS(env, szb+1);
    ans = &env[szb];
    *ans = jl_bottom_type;
    int lta = jl_is_concrete_type(a);
    int ltb = jl_is_concrete_type(b);
    if (jl_subtype_env(a, b, env, szb)) {
        *ans = a; sz = szb;
        if (issubty) *issubty = 1;
    }
    // else if (lta && ltb) { // !jl_type_equality_is_identity known in this case because obviously_disjoint returned false
    //     goto bot;
    // }
    else if (jl_subtype(b, a)) {
        *ans = b;
    }
    else {
        // TODO: these tests could probably be ordered better with above
        if (lta && !might_intersect_concrete(b))
            goto bot;
        if (ltb && !might_intersect_concrete(a))
            goto bot;
        // A dispatch tuple is a concrete leaf type, so its intersection with any other
        // type is just itself (when it is a subtype) or empty. The subtype checks above
        // having failed, the intersection must be empty.
        if (jl_is_dispatch_tupletype(a) || jl_is_dispatch_tupletype(b))
            goto bot;
        jl_stenv_t e;
        init_stenv(&e, NULL, 0);
        e.intersection = 1;
        e.closed_inputs = -1;
        e.inputs[0] = a;
        e.inputs[1] = b;
        e.envout = env;
        if (szb)
            memset(env, 0, szb*sizeof(void*));
        e.envsz = szb;
        *ans = intersect_all(a, b, &e);
        free_stenv(&e);
        if (*ans == jl_bottom_type) goto bot;
        // TODO: code dealing with method signatures is not able to handle unions, so if
        // `a` and `b` are both tuples, we need to be careful and may not return a union,
        // even if `intersect` produced one
        if (jl_is_tuple_type(jl_unwrap_unionall(a)) && jl_is_tuple_type(jl_unwrap_unionall(b)) &&
            !jl_is_datatype(jl_unwrap_unionall(*ans))) {
            jl_value_t *ans_unwrapped = jl_unwrap_unionall(*ans);
            JL_GC_PUSH1(&ans_unwrapped);
            if (jl_is_uniontype(ans_unwrapped)) {
                ans_unwrapped = switch_union_tuple(((jl_uniontype_t*)ans_unwrapped)->a, ((jl_uniontype_t*)ans_unwrapped)->b);
                if (ans_unwrapped != NULL) {
                    *ans = jl_rewrap_unionall_(ans_unwrapped, *ans);
                }
            }
            JL_GC_POP();
            if (!jl_is_datatype(jl_unwrap_unionall(*ans))) {
                // Bail: caller can't handle a non-datatype here. The env computed
                // by `intersect` is meaningless after this assignment, but the
                // subtype call below recovers a usable env via the `x == y` fast
                // path in `jl_subtype_env` (typevars from `b`).
                *ans = b;
            }
        }
        sz = szb;
        // TODO: compute better `env` directly during intersection.
        // for now, we attempt to compute env by using subtype on the intersection result
        if (szb > 0 && !jl_types_equal(b, (jl_value_t*)jl_type_type)) {
            if (!jl_subtype_env(*ans, b, env, szb)) {
                sz = 0;
            }
        }
    }
    if (sz > 0 && szb > 0) {
        for (i = 0; i < sz; i++) {
            if (!env[i]) {
                sz = 0;
                break;
            }
        }
    }
    if (sz == 0 && szb > 0) {
        jl_unionall_t *ub = (jl_unionall_t*)b;
        while (jl_is_unionall(ub)) {
            int constrained = constrains_param_static(ub->var, ub->body, 1);
            env[i++] = wrap_tvar_env((jl_value_t*)ub->var, constrained);
            ub = (jl_unionall_t*)ub->body;
        }
        sz = szb;
    }
    if (penv) {
        jl_svec_t *e = jl_alloc_svec(sz);
        for (i = 0; i < sz; i++) {
            assert(env[i]);
            jl_svecset(e, i, env[i]);
        }
        *penv = e;
    }
 bot:
    JL_GC_POP();
    return *ans;
}
```
-/
def jlTypeIntersectionEnvS (n : Nat) (T : Types) (a b : Val) (withEnv : Bool) :
    CM (Val × List Val × Bool) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if ← obviouslyDisjoint n T a b false then
      return (.bottom, [], a == .bottom)
    if a.isTypeapp || b.isTypeapp then
      throw "internal error: TypeApp in type intersection"
    let szb ← if withEnv then jlSubtypeEnvSize n b else pure 0
    let mut ans : Val := .bottom
    let mut issubty := false
    let lta ← isConcreteType T a
    let ltb ← isConcreteType T b
    if ← jlSubtypeEnv n T a b then
      ans := a
      issubty := true
    else if ← jlSubtype n T b a then
      ans := b
    else
      if lta then
        if !(← mightIntersectConcrete n b) then
          return (.bottom, [], false)
      if ltb then
        if !(← mightIntersectConcrete n a) then
          return (.bottom, [], false)
      let dtA ← jlIsDispatchTupletype T a
      let dtB ← if dtA then pure true else jlIsDispatchTupletype T b
      if dtB then
        return (.bottom, [], false)
      let e : StEnv := { initStenv with
        intersection := true
        closedInputs := none
        inputs := (a, b)
      }
      ans := (← (intersectAll n T a b []).run e).1
      if ans == .bottom then
        return (.bottom, [], false)
      if a.unwrapUnionall.isTupleType && b.unwrapUnionall.isTupleType &&
          !ans.unwrapUnionall.isDatatype then
        let ansUnwrapped := ans.unwrapUnionall
        if let .union ua ub := ansUnwrapped then
          if let some switched ← switchUnionTuple n T ua ub then
            ans := rewrapUnionall_ switched ans
        if !ans.unwrapUnionall.isDatatype then
          ans := b
    let mut envOut : List Val := []
    if withEnv && szb > 0 then
      let mut ub := b
      while ub.isUnionall do
        let constrained ← constrainsParamStatic n T ub.uaVar ub.uaBody true
        envOut := envOut ++ [wrapTvarEnv ub.uaVar constrained]
        ub := ub.uaBody
    return (ans, envOut, issubty)

/-- `jl_type_intersection_env`

Julia source: src/subtype.c:6740-6743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
jl_value_t *jl_type_intersection_env(jl_value_t *a, jl_value_t *b, jl_svec_t **penv)
{
    return jl_type_intersection_env_s(a, b, penv, NULL);
}
```
-/
def jlTypeIntersectionEnv (n : Nat) (T : Types) (a b : Val) (withEnv : Bool) :
    CM (Val × List Val) := do
  let (ans, env, _) ← jlTypeIntersectionEnvS n T a b withEnv
  return (ans, env)

/-- `jl_type_intersection`

Julia source: src/subtype.c:6745-6748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_type_intersection(jl_value_t *a, jl_value_t *b)
{
    return jl_type_intersection_env(a, b, NULL);
}
```
-/
def jlTypeIntersection (n : Nat) (T : Types) (a b : Val) : CM Val := do
  let (ans, _, _) ← jlTypeIntersectionEnvS n T a b false
  return ans

/-- `jl_type_intersection_with_env`

Julia source: src/subtype.c:6750-6759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_svec_t *jl_type_intersection_with_env(jl_value_t *a, jl_value_t *b) JL_CANSAFEPOINT
{
    jl_svec_t *env = jl_emptysvec;
    jl_value_t *ti = NULL;
    JL_GC_PUSH2(&env, &ti);
    ti = jl_type_intersection_env(a, b, &env);
    jl_svec_t *pair = jl_svec2(ti, env);
    JL_GC_POP();
    return pair;
}
```
-/
def jlTypeIntersectionWithEnv (n : Nat) (T : Types) (a b : Val) : CM (Val × List Val) :=
  jlTypeIntersectionEnv n T a b true

/-- `jl_subtype_matching`

Julia source: src/subtype.c:6761-6782 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_subtype_matching(jl_value_t *a, jl_value_t *b, jl_svec_t **penv)
{
    int szb = penv ? jl_subtype_env_size(b) : 0;
    if (szb == 0)
        return jl_subtype_env(a, b, NULL, szb);

    jl_value_t **env;
    JL_GC_PUSHARGS(env, szb);
    int sub = jl_subtype_env(a, b, env, szb);
    if (sub) {
        // copy env to svec for return
        int i = 0;
        jl_svec_t *e = jl_alloc_svec(szb);
        for (i = 0; i < szb; i++) {
            assert(env[i]);
            jl_svecset(e, i, env[i]);
        }
        *penv = e;
    }
    JL_GC_POP();
    return sub;
}
```
-/
def jlSubtypeMatching (n : Nat) (T : Types) (a b : Val) (withEnv : Bool) :
    CM (Bool × List Val) := do
  let szb ← if withEnv then jlSubtypeEnvSize n b else pure 0
  let sub ← jlSubtypeEnv n T a b
  if !sub || szb == 0 then
    return (sub, [])
  let mut envOut : List Val := []
  let mut ub := b
  for _ in [0:szb] do
    if ub.isUnionall then
      let constrained ← constrainsParamStatic n T ub.uaVar ub.uaBody true
      envOut := envOut ++ [wrapTvarEnv ub.uaVar constrained]
      ub := ub.uaBody
  return (true, envOut)

/-- `check_diagonal`

Julia source: src/subtype.c:6785-6872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static void check_diagonal(jl_value_t *t, jl_varbinding_t *troot, jl_param_pos_t param)
{
    if (jl_is_uniontype(t)) {
        int i, len = 0;
        jl_varbinding_t *v;
        for (v = troot; v != NULL; v = v->prev)
            len++;
        // 3 bytes per var: [occurs_inv, occurs_cov, cov_diag].
        int8_t *occurs = (int8_t *)alloca(len * 3);
        for (v = troot, i = 0; v != NULL; v = v->prev, i++) {
            occurs[i*3]   = v->occurs_inv;
            occurs[i*3+1] = v->occurs_cov;
            occurs[i*3+2] = v->cov_diag;
        }
        jl_value_t *a = ((jl_uniontype_t *)t)->a;
        check_diagonal(a, troot, param);
        for (v = troot, i = 0; v != NULL; v = v->prev, i++) {
            int8_t a_inv = v->occurs_inv;
            int8_t a_cov = v->occurs_cov;
            int8_t a_diag = v->cov_diag;
            v->occurs_inv = occurs[i*3];
            v->occurs_cov = occurs[i*3+1];
            v->cov_diag   = occurs[i*3+2];
            occurs[i*3]   = a_inv;
            occurs[i*3+1] = a_cov;
            occurs[i*3+2] = a_diag;
        }
        jl_value_t *b = ((jl_uniontype_t *)t)->b;
        check_diagonal(b, troot, param);
        for (v = troot, i = 0; v != NULL; v = v->prev, i++) {
            if (v->occurs_inv < occurs[i*3])
                v->occurs_inv = occurs[i*3];
            if (v->occurs_cov < occurs[i*3+1])
                v->occurs_cov = occurs[i*3+1];
            if (v->cov_diag  < occurs[i*3+2])
                v->cov_diag  = occurs[i*3+2];
        }
    }
    else if (jl_is_unionall(t)) {
        assert(troot != NULL);
        jl_varbinding_t *v1 = troot, *v2 = troot->prev;
        while (v2 != NULL) {
            if (v2->var == ((jl_unionall_t *)t)->var) {
                v1->prev = v2->prev;
                break;
            }
            v1 = v2;
            v2 = v2->prev;
        }
        jl_value_t *body = ((jl_unionall_t *)t)->body;
        check_diagonal(body, troot, param);
        v1->prev = v2;
    }
    else if (jl_is_some_Type(t)) {
        jl_value_t *T = jl_some_Type_T(t);
        check_diagonal(T, troot, PARAM_INVARIANT);
    }
    else if (jl_is_datatype(t)) {
        jl_param_pos_t nparam = jl_is_tuple_type(t) ? PARAM_COVARIANT : PARAM_INVARIANT;
        if (nparam < param) nparam = param;
        for (size_t i = 0; i < jl_nparams(t); i++) {
            jl_value_t *p = jl_tparam(t, i);
            check_diagonal(p, troot, nparam);
        }
    }
    else if (jl_is_vararg(t)) {
        jl_value_t *T = jl_unwrap_vararg(t);
        jl_value_t *N = jl_unwrap_vararg_num(t);
        int n = (N && jl_is_long(N)) ? jl_unbox_long(N) : 2;
        if (T && n > 0) check_diagonal(T, troot, param);
        if (T && n > 1) check_diagonal(T, troot, param);
        if (N)          check_diagonal(N, troot, PARAM_INVARIANT);
    }
    else if (jl_is_typevar(t)) {
        jl_varbinding_t *v = troot;
        for (; v != NULL; v = v->prev) {
            if (v->var == (jl_tvar_t *)t) {
                if (param == PARAM_COVARIANT && v->occurs_cov < 2) v->occurs_cov++;
                if (param == PARAM_INVARIANT && v->occurs_inv < 2) v->occurs_inv++;
                break;
            }
        }
        if (v == NULL) {
            jl_value_t *ub = ((jl_tvar_t *)t)->ub;
            check_diagonal(ub, troot, PARAM_NONE);
        }
    }
}
```
-/
def checkDiagonal (n : Nat) (t : Val) (troot : Array VarBinding) (param : ParamPos) :
    CM (Array VarBinding) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match t with
    | .union a b =>
      let saved := troot.map fun v => (v.occursInv, v.occursCov, v.covDiag)
      let afterA ← checkDiagonal n a troot param
      let savedA := afterA.map fun v => (v.occursInv, v.occursCov, v.covDiag)
      let restored := afterA.mapIdx fun i v =>
        let (inv0, cov0, diag0) := saved[i]!
        { v with occursInv := inv0, occursCov := cov0, covDiag := diag0 }
      let afterB ← checkDiagonal n b restored param
      return afterB.mapIdx fun i v =>
        let (invA, covA, diagA) := savedA[i]!
        { v with
          occursInv := max v.occursInv invA
          occursCov := max v.occursCov covA
          covDiag := max v.covDiag diagA }
    | .unionall uid _ _ _ body =>
      let masked := troot.mapIdx fun i v =>
        if i + 1 < troot.size && v.var.tvId == some uid then
          { v with var := .bottom }
        else v
      let afterBody ← checkDiagonal n body masked param
      return afterBody.mapIdx fun i v => { v with var := troot[i]!.var }
    | .typeeq T | .typeegal T =>
      checkDiagonal n T troot .invariant
    | .datatype _ ps =>
      let nparam : ParamPos :=
        let base := if t.isTupleType then ParamPos.covariant else ParamPos.invariant
        if param == .invariant then .invariant
        else if param == .covariant || base == .covariant then .covariant
        else .none
      let mut cur := troot
      for p in ps do
        cur ← checkDiagonal n p cur nparam
      return cur
    | .vararg t? n? =>
      let Tval := t.unwrapVararg
      let count : Int := match n? with | some (.long k) => k | _ => 2
      let mut cur := troot
      if t?.isSome && count > 0 then cur ← checkDiagonal n Tval cur param
      if t?.isSome && count > 1 then cur ← checkDiagonal n Tval cur param
      if let some nv := n? then cur ← checkDiagonal n nv cur .invariant
      return cur
    | .typevar .. =>
      let mut found := false
      let mut out := troot
      for idx in (List.range troot.size).reverse do
        let v := troot[idx]!
        if v.var.tvId == t.tvId && v.var.isTypevar then
          found := true
          let cov' := if param == .covariant && v.occursCov < 2 then v.occursCov + 1 else v.occursCov
          let inv' := if param == .invariant && v.occursInv < 2 then v.occursInv + 1 else v.occursInv
          out := out.set! idx { v with occursCov := cov', occursInv := inv' }
          break
      if !found then
        out ← checkDiagonal n t.tvUb out .none
      return out
    | _ =>
      return troot

/-- `insert_nondiagonal`

Julia source: src/subtype.c:6874-6996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *insert_nondiagonal(jl_value_t *type, jl_varbinding_t *troot, int widen2ub) JL_CANSAFEPOINT
{
    if (jl_is_typevar(type)) {
        int concretekind = widen2ub > 1 ? 0 : 1;
        jl_varbinding_t *v = troot;
        for (; v != NULL; v = v->prev) {
            if (v->occurs_inv == 0 &&
                cov_count(v) > concretekind &&
                v->var == (jl_tvar_t *)type)
                break;
        }
        if (v != NULL) {
            if (widen2ub) {
                jl_value_t *ub = ((jl_tvar_t *)type)->ub;
                type = insert_nondiagonal(ub, troot, 2);
            }
            else {
                // we must replace each covariant occurrence of newvar with a different newvar2<:newvar (diagonal rule)
                if (v->innervars == NULL)
                    v->innervars = jl_alloc_array_1d(jl_array_any_type, 0);
                jl_value_t *newvar = NULL, *lb = v->var->lb, *ub = (jl_value_t *)v->var;
                jl_array_t *innervars = v->innervars;
                JL_GC_PUSH4(&newvar, &lb, &ub, &innervars);
                newvar = (jl_value_t *)jl_new_typevar(v->var->name, lb, ub);
                jl_array_ptr_1d_push(innervars, newvar);
                JL_GC_POP();
                type = newvar;
            }
        }
    }
    else if (jl_is_unionall(type)) {
        jl_value_t *body = ((jl_unionall_t*)type)->body;
        jl_tvar_t *var = ((jl_unionall_t*)type)->var;
        jl_varbinding_t *v = troot;
        for (; v != NULL; v = v->prev) {
            if (v->var == var)
                break;
        }
        if (v) v->var = NULL; // Temporarily remove `type->var` from binding list.
        jl_value_t *newbody = insert_nondiagonal(body, troot, widen2ub);
        if (v) v->var = var; // And restore it after inner insertation.
        jl_value_t *newvar = NULL;
        JL_GC_PUSH3(&newbody, &newvar, &type);
        if (body == newbody || jl_has_typevar(newbody, var)) {
            if (body != newbody)
                type = jl_new_struct(jl_unionall_type, var, newbody);
            // n.b. we do not widen lb, since that would be the wrong direction
            jl_value_t *ub = var->ub;
            newvar = insert_nondiagonal(ub, troot, widen2ub);
            if (newvar != ub) {
                jl_value_t *lb = var->lb;
                newvar = (jl_value_t*)jl_new_typevar(var->name, lb, newvar);
                newbody = jl_apply_type1(type, newvar);
                type = jl_type_unionall((jl_tvar_t*)newvar, newbody);
            }
        }
        JL_GC_POP();
    }
    else if (jl_is_uniontype(type)) {
        jl_value_t *a = ((jl_uniontype_t*)type)->a;
        jl_value_t *b = ((jl_uniontype_t*)type)->b;
        jl_value_t *newa = NULL;
        jl_value_t *newb = NULL;
        JL_GC_PUSH2(&newa, &newb);
        newa = insert_nondiagonal(a, troot, widen2ub);
        newb = insert_nondiagonal(b, troot, widen2ub);
        if (newa != a || newb != b)
            type = simple_union(newa, newb);
        JL_GC_POP();
    }
    else if (jl_is_vararg(type)) {
        // As for Vararg we'd better widen its var to ub as otherwise they are still diagonal
        jl_value_t *t = jl_unwrap_vararg(type);
        jl_value_t *n = jl_unwrap_vararg_num(type);
        if (widen2ub == 0)
            widen2ub = !(n && jl_is_long(n)) || jl_unbox_long(n) > 1;
        jl_value_t *newt = insert_nondiagonal(t, troot, widen2ub);
        if (t != newt) {
            JL_GC_PUSH1(&newt);
            type = (jl_value_t *)jl_wrap_vararg(newt, n, 0, 0);
            JL_GC_POP();
        }
    }
    else if (jl_is_typeeq(type)) {
        jl_value_t *T = jl_typeeq_T(type);
        jl_value_t *newT = insert_nondiagonal(T, troot, 1);
        if (T != newT) {
            JL_GC_PUSH1(&newT);
            type = (jl_value_t*)jl_wrap_Type(newT);
            JL_GC_POP();
        }
    }
    else if (jl_is_typeegal(type)) {
        // a no-op for closed `T`; kept parallel to the `TypeEq` case
        jl_value_t *T = jl_typeegal_T(type);
        jl_value_t *newT = insert_nondiagonal(T, troot, 1);
        if (T != newT) {
            JL_GC_PUSH1(&newT);
            type = jl_wrap_TypeEgal(newT);
            JL_GC_POP();
        }
    }
    else if (jl_is_datatype(type)) {
        if (jl_is_tuple_type(type)) {
            jl_svec_t *newparams = NULL;
            jl_value_t *newelt = NULL;
            JL_GC_PUSH2(&newparams, &newelt);
            for (size_t i = 0; i < jl_nparams(type); i++) {
                jl_value_t *elt = jl_tparam(type, i);
                newelt = insert_nondiagonal(elt, troot, widen2ub);
                if (elt != newelt) {
                    if (!newparams)
                        newparams = jl_svec_copy(((jl_datatype_t*)type)->parameters);
                    jl_svecset(newparams, i, newelt);
                }
            }
            if (newparams)
                type = (jl_value_t*)jl_apply_tuple_type(newparams, 1);
            JL_GC_POP();
        }
    }
    return type;
}
```
-/
def insertNondiagonal (n : Nat) (T : Types) (type : Val)
    (troot : Array (VarBinding × List Val)) (widen2ub : Nat) :
    CM (Val × Array (VarBinding × List Val)) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    match type with
    | .typevar _ _ _ ub =>
      let concretekind : Nat := if widen2ub > 1 then 0 else 1
      let mut foundIdx : Option Nat := none
      for idx in (List.range troot.size).reverse do
        let (v, _) := troot[idx]!
        if v.occursInv == 0 && covCount v > concretekind && v.var.tvId == type.tvId && v.var.isTypevar then
          foundIdx := some idx
          break
      if let some idx := foundIdx then
        if widen2ub != 0 then
          return ← insertNondiagonal n T ub troot 2
        else
          let (v, inners) := troot[idx]!
          let .typevar _ vnm vlb _ := v.var | return (type, troot)
          let newvar ← newTypevar vnm vlb v.var
          let troot' := troot.set! idx (v, inners ++ [newvar])
          return (newvar, troot')
      return (type, troot)
    | .unionall uid nm lb ub body =>
      let var := Val.typevar uid nm lb ub
      let mut foundIdx : Option Nat := none
      for idx in (List.range troot.size).reverse do
        if troot[idx]!.1.var.tvId == some uid then
          foundIdx := some idx
          break
      let mut troot1 := troot
      if let some idx := foundIdx then
        let (v, inners) := troot1[idx]!
        troot1 := troot1.set! idx ({ v with var := .bottom }, inners)
      let (newbody, troot2) ← insertNondiagonal n T body troot1 widen2ub
      let mut troot3 := troot2
      if let some idx := foundIdx then
        let (v, inners) := troot3[idx]!
        troot3 := troot3.set! idx ({ v with var := var }, inners)
      let mut outType := type
      if body == newbody || newbody.hasTypevar var then
        if body != newbody then
          outType := .unionall uid nm lb ub newbody
        let (newub, troot4) ← insertNondiagonal n T ub troot3 widen2ub
        troot3 := troot4
        if newub != ub then
          let newvar ← newTypevar nm lb newub
          let newbody2 ← instantiateUnionall n T (subOps n T) outType newvar
          outType ← typeUnionall n T (subOps n T) newvar newbody2
      return (outType, troot3)
    | .union a b =>
      let (newa, troot1) ← insertNondiagonal n T a troot widen2ub
      let (newb, troot2) ← insertNondiagonal n T b troot1 widen2ub
      if newa != a || newb != b then
        let u ← simpleUnion n T (subOps n T) newa newb
        return (u, troot2)
      return (type, troot2)
    | .vararg _ n? =>
      let t := type.unwrapVararg
      let w2 :=
        if widen2ub == 0 then
          match n? with
          | some (.long k) => if k > 1 then 1 else 0
          | _ => 1
        else widen2ub
      let (newt, troot1) ← insertNondiagonal n T t troot w2
      if newt != t then
        let some va ← wrapVararg n T (subOps n T) (some newt) n? false 0
          | return (type, troot1)
        return (va, troot1)
      return (type, troot1)
    | .typeeq te =>
      let (newT, troot1) ← insertNondiagonal n T te troot 1
      if newT != te then
        let w ← wrapType n T (subOps n T) newT
        return (w, troot1)
      return (type, troot1)
    | .typeegal te =>
      let (newT, troot1) ← insertNondiagonal n T te troot 1
      if newT != te then
        let w ← wrapTypeEgal newT
        return (w, troot1)
      return (type, troot1)
    | .datatype name ps =>
      if name == tupleName then
        let mut changed := false
        let mut newps : List Val := []
        let mut cur := troot
        for elt in ps do
          let (newelt, cur') ← insertNondiagonal n T elt cur widen2ub
          cur := cur'
          if newelt != elt then changed := true
          newps := newps ++ [newelt]
        if changed then
          let some tup ← instDatatypeInner n T (subOps n T) tupleName newps true 0
            | return (type, cur)
          return (tup, cur)
        return (type, cur)
      return (type, troot)
    | _ =>
      return (type, troot)

/-- `_widen_diagonal`

Julia source: src/subtype.c:6998-7006 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *_widen_diagonal(jl_value_t *t, jl_varbinding_t *troot) JL_CANSAFEPOINT {
    check_diagonal(t, troot, PARAM_NONE);
    int any_concrete = 0;
    for (jl_varbinding_t *v = troot; v != NULL; v = v->prev)
        any_concrete |= cov_count(v) > 1 && v->occurs_inv == 0;
    if (!any_concrete)
        return t; // no diagonal
    return insert_nondiagonal(t, troot, 0);
}
```
-/
def widenDiagonal_ (n : Nat) (T : Types) (t : Val) (troot : Array VarBinding) :
    CM (Val × Array (VarBinding × List Val)) := do
  let checked ← checkDiagonal n t troot .none
  let anyConcrete := checked.any fun v => covCount v > 1 && v.occursInv == 0
  let withInners := checked.map fun v => (v, ([] : List Val))
  if !anyConcrete then
    return (t, withInners)
  insertNondiagonal n T t withInners 0

/-- `widen_diagonal`

Julia source: src/subtype.c:7008-7029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *widen_diagonal(jl_value_t *t, jl_unionall_t *u, jl_varbinding_t *troot) JL_CANSAFEPOINT
{
    jl_varbinding_t vb;
    memset(&vb, 0, sizeof(vb));
    vb.var = u->var;
    vb.existential = 1;
    vb.prev = troot;
    jl_value_t *nt = NULL;
    JL_GC_PUSH2(&vb.innervars, &nt);
    if (jl_is_unionall(u->body))
        nt = widen_diagonal(t, (jl_unionall_t *)u->body, &vb);
    else
        nt = _widen_diagonal(t, &vb);
    if (vb.innervars != NULL) {
        for (size_t i = 0; i < jl_array_nrows(vb.innervars); i++) {
            jl_tvar_t *var = (jl_tvar_t*)jl_array_ptr_ref(vb.innervars, i);
            nt = jl_type_unionall(var, nt);
        }
    }
    JL_GC_POP();
    return nt;
}
```
-/
def widenDiagonal (n : Nat) (T : Types) (t u : Val) (troot : Array VarBinding) :
    CM (Val × Array (VarBinding × List Val)) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let vb : VarBinding := {
      var := u.uaVar
      lb := u.uaVar.tvLb
      ub := u.uaVar.tvUb
      existential := true
    }
    let troot' := troot.push vb
    let (nt0, outRoot) ←
      if u.uaBody.isUnionall then
        widenDiagonal n T t u.uaBody troot'
      else
        widenDiagonal_ n T t troot'
    let (_, myInners) := outRoot[outRoot.size - 1]!
    let mut nt := nt0
    for ivar in myInners do
      nt ← typeUnionall n T (subOps n T) ivar nt
    return (nt, outRoot.pop)

/-- `jl_widen_diagonal`

Julia source: src/subtype.c:7031-7034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT jl_value_t *jl_widen_diagonal(jl_value_t *t, jl_unionall_t *ua) JL_CANSAFEPOINT
{
    return widen_diagonal(t, ua, NULL);
}
```
-/
def jlWidenDiagonal (n : Nat) (T : Types) (t ua : Val) : CM Val := do
  return (← widenDiagonal n T t ua #[]).1

/-! ## Type specificity comparison (`src/subtype.c:7036-7733`) -/

/-- Numeric rank of `jl_vararg_kind_t` (`src/julia_internal.h:1280-1285`):
`JL_VARARG_NONE = 0`, `JL_VARARG_INT = 1`, `JL_VARARG_BOUND = 2`, `JL_VARARG_UNBOUND = 3`. -/
def VarargKind.rank : VarargKind → Nat
  | .none => 0
  | .int => 1
  | .bound => 2
  | .unbound => 3

/-- `jl_va_tuple_kind` (`src/julia_internal.h:1339-1347`). -/
def vaTupleKind (t : Val) : VarargKind :=
  let t := t.unwrapUnionall
  match t.params.getLast? with
  | none => .none
  | some p => p.varargKind

/-- A `jl_typeenv_t` entry as used by `type_morespecific_`: `var` is the `TypeVar` object
and `numOccurs` is `(int)(ssize_t)env->val`. -/
structure MspEnvEntry where
  var : Val
  numOccurs : Nat
  deriving Repr, BEq, Inhabited

/-- `jl_typeenv_t` chain for `type_morespecific_`, innermost binding first. -/
abbrev MspEnv := List MspEnvEntry

/-- `count_missing_wrap`

Julia source: src/subtype.c:7037-7063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int count_missing_wrap(jl_value_t *x, jl_typeenv_t *env)
{
    if (!jl_has_free_typevars(x))
        return 0;
    jl_typeenv_t *wrapped = NULL;
    int count = 0;
    for (jl_typeenv_t *env2 = env; env2 != NULL; env2 = env2->prev) {
        int need_wrap = 0;
        for (jl_typeenv_t *env3 = wrapped; env3 != NULL && need_wrap == 0; env3 = env3->prev) {
            if (env3->var == env2->var)
                need_wrap = -1;
            else if (jl_has_typevar(env3->var->lb, env2->var) || jl_has_typevar(env3->var->ub, env2->var))
                need_wrap = 1;
        }
        need_wrap = need_wrap == 0 ? jl_has_typevar(x, env2->var) :
                    need_wrap == -1 ? 0 : 1;
        if (need_wrap) {
            count++;
            jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
            newenv->var = env2->var;
            newenv->val = NULL;
            newenv->prev = wrapped;
            wrapped = newenv;
        }
    }
    return count;
}
```
-/
def countMissingWrap (x : Val) (env : MspEnv) : Nat := Id.run do
  if !x.hasFreeTypevars then
    return 0
  let mut wrapped : List Val := []
  let mut count : Nat := 0
  for env2 in env do
    let mut needWrap : Int := 0
    for v3 in wrapped do
      if needWrap != 0 then break
      if v3.tvId == env2.var.tvId then
        needWrap := -1
      else if v3.tvLb.hasTypevar env2.var || v3.tvUb.hasTypevar env2.var then
        needWrap := 1
    let doWrap : Bool :=
      if needWrap == 0 then x.hasTypevar env2.var
      else if needWrap == -1 then false
      else true
    if doWrap then
      count := count + 1
      wrapped := env2.var :: wrapped
  return count

/-- `obvious_subtype_msp`; `none` is the C return value `0` (undecided).

Julia source: src/subtype.c:7065-7086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int obvious_subtype_msp(jl_value_t *x, jl_value_t *y, jl_value_t *y0, int *subtype, int wrapx, int wrapy)
{
    if (wrapx != 0 || wrapy != 0) {
        int wrap_count = wrapx - wrapy;
        while (wrap_count > 0 && jl_is_unionall(y))
        {
            y = ((jl_unionall_t*)y)->body;
            wrap_count--;
        }
        while (wrap_count < 0 && jl_is_unionall(x))
        {
            x = ((jl_unionall_t*)x)->body;
            wrap_count++;
        }
        if (wrap_count > 0) {
            if (obvious_subtype(jl_unwrap_unionall(x), y, y0, subtype) && !*subtype)
                return 1;
            return 0;
        }
    }
    return obvious_subtype(x, y, y0, subtype);
}
```
-/
def obviousSubtypeMsp (n : Nat) (T : Types) (x y y0 : Val) (wrapx wrapy : Nat) : CM (Option Bool) := do
  let mut x := x
  let mut y := y
  if wrapx != 0 || wrapy != 0 then
    let mut wrapCount : Int := Int.ofNat wrapx - Int.ofNat wrapy
    while wrapCount > 0 && y.isUnionall do
      y := y.uaBody
      wrapCount := wrapCount - 1
    while wrapCount < 0 && x.isUnionall do
      x := x.uaBody
      wrapCount := wrapCount + 1
    if wrapCount > 0 then
      if (← obviousSubtype n T x.unwrapUnionall y y0) == some false then
        return some false
      return none
  obviousSubtype n T x y y0

/-- `eq_msp`

Julia source: src/subtype.c:7088-7181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int eq_msp(jl_value_t *a, jl_value_t *b, jl_value_t *a0, jl_value_t *b0, jl_typeenv_t *env) JL_CANSAFEPOINT
{
    if (!(jl_is_type(a) || jl_is_typevar(a)) ||
        !(jl_is_type(b) || jl_is_typevar(b)))
        return jl_egal(a, b);
    if (a == b) // assume the TypeVar env is the same??
        return 1;
    if (jl_typeof(a) == jl_typeof(b) && jl_types_struct_equiv(a, b))
        return 1;
    if (obviously_unequal(a, b))
        return 0;
    // the following is an interleaved version of:
    //   return jl_type_equal(a, b)
    // where we try to do the fast checks before the expensive ones
    if (jl_is_datatype(a) && !jl_is_concrete_type(b)) {
        // if one type looks simpler, check it on the right
        // first in order to reject more quickly.
        jl_value_t *temp = a;
        a = b;
        b = temp;
    }
    int wrapa = count_missing_wrap(a, env);
    int wrapb = count_missing_wrap(b, env);
    // first check if a <: b has an obvious answer
    int subtype_ab = 2;
    if (b == (jl_value_t*)jl_any_type || a == jl_bottom_type) {
        subtype_ab = 1;
    }
    else if (obvious_subtype_msp(a, b, b0, &subtype_ab, wrapa, wrapb)) {
#ifdef NDEBUG
        if (subtype_ab == 0)
            return 0;
#endif
    }
    else {
        subtype_ab = 3;
    }
    // next check if b <: a has an obvious answer
    int subtype_ba = 2;
    if (a == (jl_value_t*)jl_any_type || b == jl_bottom_type) {
        subtype_ba = 1;
    }
    else if (obvious_subtype_msp(b, a, a0, &subtype_ba, wrapb, wrapa)) {
#ifdef NDEBUG
        if (subtype_ba == 0)
            return 0;
#endif
    }
    else {
        subtype_ba = 3;
    }
    // finally, do full subtyping for any inconclusive test
    JL_GC_PUSH2(&a, &b);
    jl_typeenv_t *env2 = env;
    while (env2 != NULL) {
        a = jl_type_unionall(env2->var, a);
        b = jl_type_unionall(env2->var, b);
        env2 = env2->prev;
    }
    jl_stenv_t e;
#ifdef NDEBUG
    if (subtype_ab != 1)
#endif
    {
        init_stenv(&e, NULL, 0);
        int subtype = forall_exists_subtype(a, b, &e, PARAM_NONE);
        assert(subtype_ab == 3 || subtype_ab == subtype || jl_has_free_typevars(a) || jl_has_free_typevars(b));
#ifndef NDEBUG
        if (subtype_ab != 0 && subtype_ab != 1) // ensures that running in a debugger doesn't change the result
#endif
        subtype_ab = subtype;
#ifdef NDEBUG
        if (subtype_ab == 0) {
            JL_GC_POP();
            return 0;
        }
#endif
    }
#ifdef NDEBUG
    if (subtype_ba != 1)
#endif
    {
        init_stenv(&e, NULL, 0);
        int subtype = forall_exists_subtype(b, a, &e, PARAM_NONE);
        assert(subtype_ba == 3 || subtype_ba == subtype || jl_has_free_typevars(a) || jl_has_free_typevars(b));
#ifndef NDEBUG
        if (subtype_ba != 0 && subtype_ba != 1) // ensures that running in a debugger doesn't change the result
#endif
        subtype_ba = subtype;
    }
    JL_GC_POP();
    // all tests successful
    return subtype_ab && subtype_ba;
}
```
-/
def eqMsp (n : Nat) (T : Types) (a b a0 b0 : Val) (env : MspEnv) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if !(a.isType || a.isTypevar) || !(b.isType || b.isTypevar) then
      return ← egal n T a b
    if a == b then
      return true
    if typeOf a == typeOf b then
      if ← typesStructEquiv n T a b then
        return true
    if ← obviouslyUnequal n T a b then
      return false
    -- if one type looks simpler, check it on the right first in order to reject more quickly.
    let swap ← if a.isDatatype then pure (!(← isConcreteType T b)) else pure false
    let (a0Swap, b0Swap) := if swap then (b, a) else (a, b)
    let mut a := a0Swap
    let mut b := b0Swap
    let wrapa := countMissingWrap a env
    let wrapb := countMissingWrap b env
    -- first check if a <: b has an obvious answer
    let subtypeAb ←
      if b == anyType || a == .bottom then
        pure (some true)
      else
        obviousSubtypeMsp n T a b b0 wrapa wrapb
    if subtypeAb == some false then
      return false
    -- next check if b <: a has an obvious answer
    let subtypeBa ←
      if a == anyType || b == .bottom then
        pure (some true)
      else
        obviousSubtypeMsp n T b a a0 wrapb wrapa
    if subtypeBa == some false then
      return false
    -- finally, do full subtyping for any inconclusive test
    for env2 in env do
      a ← typeUnionall n T (subOps n T) env2.var a
      b ← typeUnionall n T (subOps n T) env2.var b
    let ab ← match subtypeAb with
      | some true => pure true
      | some false => pure false
      | none => pure (← (forallExistsSubtype n T a b .none).run initStenv).1
    if !ab then
      return false
    let ba ← match subtypeBa with
      | some true => pure true
      | some false => pure false
      | none => pure (← (forallExistsSubtype n T b a .none).run initStenv).1
    return ab && ba

/-- `sub_msp`

Julia source: src/subtype.c:7183-7225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int sub_msp(jl_value_t *x, jl_value_t *y, jl_value_t *y0, jl_typeenv_t *env) JL_CANSAFEPOINT
{
    jl_stenv_t e;
    if (y == (jl_value_t*)jl_any_type || x == jl_bottom_type)
        return 1;
    if (x == y ||
        (jl_typeof(x) == jl_typeof(y) &&
         (jl_is_unionall(y) || jl_is_uniontype(y)) &&
         jl_types_struct_equiv(x, y))) {
        return 1;
    }
    int obvious_sub = 2;
    int wrapx = count_missing_wrap(x, env);
    int wrapy = count_missing_wrap(y, env);
    if (obvious_subtype_msp(x, y, y0, &obvious_sub, wrapx, wrapy)) {
#ifdef NDEBUG
        return obvious_sub;
#endif
    }
    else {
        obvious_sub = 3;
    }
    JL_GC_PUSH2(&x, &y);
    while (env != NULL) {
        if (jl_is_type(x) || jl_is_typevar(x))
            x = jl_type_unionall(env->var, x);
        if (jl_is_type(y) || jl_is_typevar(y))
            y = jl_type_unionall(env->var, y);
        env = env->prev;
    }
    init_stenv(&e, NULL, 0);
    e.closed_inputs = -1;
    e.inputs[0] = x;
    e.inputs[1] = y;
    int subtype = forall_exists_subtype(x, y, &e, PARAM_NONE);
    assert(obvious_sub == 3 || obvious_sub == subtype || jl_has_free_typevars(x) || jl_has_free_typevars(y));
#ifndef NDEBUG
    if (obvious_sub == 0 || obvious_sub == 1)
        subtype = obvious_sub; // this ensures that running in a debugger doesn't change the result
#endif
    JL_GC_POP();
    return subtype;
}
```
-/
def subMsp (n : Nat) (T : Types) (x y y0 : Val) (env : MspEnv) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if y == anyType || x == .bottom then
      return true
    if x == y then
      return true
    if typeOf x == typeOf y && (y.isUnionall || y.isUnion) then
      if ← typesStructEquiv n T x y then
        return true
    let wrapx := countMissingWrap x env
    let wrapy := countMissingWrap y env
    if let some ans ← obviousSubtypeMsp n T x y y0 wrapx wrapy then
      return ans
    let mut x := x
    let mut y := y
    for e in env do
      if x.isType || x.isTypevar then
        x ← typeUnionall n T (subOps n T) e.var x
      if y.isType || y.isTypevar then
        y ← typeUnionall n T (subOps n T) e.var y
    let st : StEnv := { initStenv with closedInputs := none, inputs := (x, y) }
    return (← (forallExistsSubtype n T x y .none).run st).1

/-- `nth_tuple_elt`

Julia source: src/subtype.c:7231-7248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static jl_value_t *nth_tuple_elt(jl_datatype_t *t JL_PROPAGATES_ROOT, size_t i) JL_NOTSAFEPOINT
{
    size_t len = jl_nparams(t);
    if (len == 0)
        return NULL;
    if (i < len-1)
        return jl_tparam(t, i);
    jl_value_t *last = jl_unwrap_unionall(jl_tparam(t, len-1));
    if (jl_is_vararg(last)) {
        jl_value_t *n = jl_unwrap_vararg_num(last);
        if (n && jl_is_long(n) && i >= len-1+jl_unbox_long(n))
            return NULL;
        return jl_unwrap_vararg(last);
    }
    if (i == len-1)
        return jl_tparam(t, i);
    return NULL;
}
```
-/
def nthTupleElt (t : Val) (i : Nat) : Option Val :=
  let len := t.nparams
  if len == 0 then
    none
  else if i < len - 1 then
    some t.params[i]!
  else
    let last := t.params[len - 1]!.unwrapUnionall
    if last.isVararg then
      match last.varargN? with
      | some (.long k) =>
        if Int.ofNat i ≥ Int.ofNat (len - 1) + k then none
        else some last.unwrapVararg
      | _ => some last.unwrapVararg
    else if i == len - 1 then
      some t.params[i]!
    else
      none

/-- `tuple_full_length`

Julia source: src/subtype.c:7323-7334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static size_t tuple_full_length(jl_value_t *t)
{
    size_t n = jl_nparams(t);
    if (n == 0) return 0;
    jl_value_t *last = jl_unwrap_unionall(jl_tparam(t,n-1));
    if (jl_is_vararg(last)) {
        jl_value_t *N = jl_unwrap_vararg_num(last);
        if (jl_is_long(N))
            n += jl_unbox_long(N)-1;
    }
    return n;
}
```
-/
def tupleFullLength (t : Val) : Int :=
  let n := t.nparams
  if n == 0 then 0
  else
    let last := t.params[n - 1]!.unwrapUnionall
    if last.isVararg then
      match last.varargN? with
      | some (.long k) => Int.ofNat n + k - 1
      | _ => Int.ofNat n
    else
      Int.ofNat n

/-- `num_occurs`

Julia source: src/subtype.c:7400-7408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int num_occurs(jl_tvar_t *v, jl_typeenv_t *env)
{
    while (env != NULL) {
        if (env->var == v)
            return (int)(ssize_t)env->val;
        env = env->prev;
    }
    return 0;
}
```
-/
def numOccurs (v : Val) (env : MspEnv) : Nat :=
  match env.find? (fun e => e.var.tvId == v.tvId && v.isTypevar) with
  | some e => e.numOccurs
  | none => 0

/-- `jl_is_typeofbottom_param`: return `true` if `t == Type{Union{}}`, so that `morespecific`
ranks `t` above any other parameter.

Julia source: src/subtype.c:7414-7432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
int jl_is_typeofbottom_param(jl_value_t *t) JL_NOTSAFEPOINT
{
    if (t == NULL)
        return 0;
    while (1) {
        t = jl_unwrap_unionall(t);
        if (jl_is_typevar(t)) {
            t = ((jl_tvar_t*)t)->ub;
        }
        else if (jl_is_uniontype(t)) {
            if (!jl_is_typeofbottom_param(((jl_uniontype_t*)t)->a))
                return 0;
            t = ((jl_uniontype_t*)t)->b;
        }
        else {
            return is_typeofbottom_typealias(t);
        }
    }
}
```
-/
def jlIsTypeofbottomParam (n : Nat) (t : Option Val) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let some t := t | return false
    let t := t.unwrapUnionall
    match t with
    | .typevar _ _ _ ub =>
      jlIsTypeofbottomParam n (some ub)
    | .union a b =>
      if !(← jlIsTypeofbottomParam n (some a)) then
        return false
      jlIsTypeofbottomParam n (some b)
    | _ =>
      isTypeofbottomTypealias n t

/-- `tuple_cmp_typeofbottom`

Julia source: src/subtype.c:7434-7447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int tuple_cmp_typeofbottom(jl_datatype_t *a, jl_datatype_t *b)
{
    size_t i, la = jl_nparams(a), lb = jl_nparams(b);
    for (i = 0; i < la || i < lb; i++) {
        jl_value_t *pa = i < la ? jl_tparam(a, i) : NULL;
        jl_value_t *pb = i < lb ? jl_tparam(b, i) : NULL;
        assert(jl_typeofbottom_type); // for clang-sa
        int xa = jl_is_typeofbottom_param(pa);
        int xb = jl_is_typeofbottom_param(pb);
        if (xa != xb)
            return xa - xb;
    }
    return 0;
}
```
-/
def tupleCmpTypeofbottom (n : Nat) (a b : Val) : CM Int := do
  let la := a.nparams
  let lb := b.nparams
  let lmax := max la lb
  for i in [0:lmax] do
    let pa := if i < la then some a.params[i]! else none
    let pb := if i < lb then some b.params[i]! else none
    let xa ← if ← jlIsTypeofbottomParam n pa then pure (1 : Int) else pure 0
    let xb ← if ← jlIsTypeofbottomParam n pb then pure (1 : Int) else pure 0
    if xa != xb then
      return xa - xb
  return 0

mutual
/-- `tuple_morespecific`

Julia source: src/subtype.c:7250-7321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int tuple_morespecific(jl_datatype_t *cdt, jl_datatype_t *pdt, jl_value_t *c0, jl_value_t *p0, int invariant, jl_typeenv_t *env) JL_CANSAFEPOINT
{
    size_t plen = jl_nparams(pdt);
    if (plen == 0) return 0;
    size_t clen = jl_nparams(cdt);
    if (clen == 0) return 1;
    int i = 0;
    jl_value_t *clast = jl_tparam(cdt,clen-1);
    jl_vararg_kind_t ckind = jl_vararg_kind(clast);
    int cva = ckind > JL_VARARG_INT;
    int pva = jl_vararg_kind(jl_tparam(pdt,plen-1)) > JL_VARARG_INT;
    int cdiag = 0, pdiag = 0;
    int some_morespecific = 0;
    while (1) {
        if (cva && pva && i >= clen && i >= plen)
            break;

        jl_value_t *ce = nth_tuple_elt(cdt, i);
        jl_value_t *pe = nth_tuple_elt(pdt, i);

        if (ce == NULL) {
            if (pe == NULL) break;
            return 1;
        }
        if (pe == NULL) {
            if (!cva && !some_morespecific)
                return 0;
            break;
        }

        if (type_morespecific_(pe, ce, p0, c0, invariant, env)) {
            assert(!type_morespecific_(ce, pe, c0, p0, invariant, env));
            return 0;
        }

        if (!cdiag && jl_is_typevar(ce) && num_occurs((jl_tvar_t*)ce,env) > 1)
            cdiag = 1;
        if (!pdiag && jl_is_typevar(pe) && num_occurs((jl_tvar_t*)pe,env) > 1)
            pdiag = 1;

        // in Tuple{a,b...} and Tuple{c,d...} allow b and d to be disjoint
        if (cva && pva && i >= clen-1 && i >= plen-1 && (some_morespecific || (cdiag && !pdiag)))
            return 1;

        int cms = type_morespecific_(ce, pe, c0, p0, invariant, env);

        if (!cms && !sub_msp(ce, pe, p0, env)) {
            /*
              A bound vararg tuple can be more specific despite disjoint elements in order to
              preserve transitivity. For example in
              A = Tuple{Array{T,N}, Vararg{Int,N}} where {T,N}
              B = Tuple{Array, Int}
              C = Tuple{AbstractArray, Int, Array}
              we need A < B < C and A < C.
            */
            return some_morespecific && cva && ckind == JL_VARARG_BOUND && num_occurs((jl_tvar_t*)jl_unwrap_vararg_num(clast), env) > 1;
        }

        // Tuple{..., T} not more specific than Tuple{..., Vararg{S}} if S is diagonal
        if (!cms && i == clen-1 && clen == plen && !cva && pva && eq_msp(ce, pe, c0, p0, env) &&
            jl_is_typevar(ce) && jl_is_typevar(pe) && !cdiag && pdiag)
            return 0;

        if (cms) some_morespecific = 1;
        i++;
    }
    if (cva && pva && clen > plen && (!pdiag || cdiag))
        return 1;
    if (cva && !pva && !some_morespecific)
        return 0;
    return some_morespecific || (cdiag && !pdiag);
}
```
-/
def tupleMorespecific (n : Nat) (T : Types) (cdt pdt c0 p0 : Val)
    (invariant : Bool) (env : MspEnv) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let plen := pdt.nparams
    if plen == 0 then return false
    let clen := cdt.nparams
    if clen == 0 then return true
    let clast := cdt.params[clen - 1]!
    let ckind := clast.varargKind
    let cva := ckind.rank > VarargKind.int.rank
    let pva := pdt.params[plen - 1]!.varargKind.rank > VarargKind.int.rank
    let mut cdiag := false
    let mut pdiag := false
    let mut someMorespecific := false
    let mut i : Nat := 0
    let mut steps := n
    while true do
      if steps == 0 then outOfBudget
      steps := steps - 1
      if cva && pva && i ≥ clen && i ≥ plen then
        break
      let ce? := nthTupleElt cdt i
      let pe? := nthTupleElt pdt i
      let some ce := ce? | do
        if pe?.isNone then break
        return true
      let some pe := pe? | do
        if !cva && !someMorespecific then
          return false
        break
      if ← typeMorespecific_ n T pe ce p0 c0 invariant env then
        return false
      if !cdiag && ce.isTypevar && numOccurs ce env > 1 then
        cdiag := true
      if !pdiag && pe.isTypevar && numOccurs pe env > 1 then
        pdiag := true
      -- in Tuple{a,b...} and Tuple{c,d...} allow b and d to be disjoint
      if cva && pva && i ≥ clen - 1 && i ≥ plen - 1 && (someMorespecific || (cdiag && !pdiag)) then
        return true
      let cms ← typeMorespecific_ n T ce pe c0 p0 invariant env
      if !cms then
        if !(← subMsp n T ce pe p0 env) then
          let nocc := match clast.varargN? with
            | some nv => numOccurs nv env
            | none => 0
          return someMorespecific && cva && ckind == .bound && nocc > 1
      -- Tuple{..., T} not more specific than Tuple{..., Vararg{S}} if S is diagonal
      if !cms && i == clen - 1 && clen == plen && !cva && pva then
        if ← eqMsp n T ce pe c0 p0 env then
          if ce.isTypevar && pe.isTypevar && !cdiag && pdiag then
            return false
      if cms then
        someMorespecific := true
      i := i + 1
    if cva && pva && clen > plen && (!pdiag || cdiag) then
      return true
    if cva && !pva && !someMorespecific then
      return false
    return someMorespecific || (cdiag && !pdiag)

/-- `args_morespecific_fix1`: called when `a` is a bound-vararg and `b` is not a vararg.
Sets the vararg length in `a` to match `b`, as long as this makes some earlier argument more specific.

Julia source: src/subtype.c:7338-7367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int args_morespecific_fix1(jl_value_t *a, jl_value_t *b, jl_value_t *a0, jl_value_t *b0, int swap, jl_typeenv_t *env) JL_CANSAFEPOINT
{
    size_t n = jl_nparams(a);
    int taillen = tuple_full_length(b)-n+1;
    if (taillen <= 0)
        return -1;
    assert(jl_is_va_tuple((jl_datatype_t*)a));
    jl_datatype_t *new_a = NULL;
    jl_value_t *e[2] = { jl_unwrap_vararg_num(jl_unwrap_unionall(jl_tparam(a, n-1))), jl_box_long(taillen) };
    JL_GC_PUSH2(&new_a, &e[1]);
    new_a = (jl_datatype_t*)jl_instantiate_type_with((jl_value_t*)a, e, 1);
    int changed = 0;
    for (size_t i = 0; i < n-1; i++) {
        if (jl_tparam(a, i) != jl_tparam(new_a, i)) {
            changed = 1;
            break;
        }
    }
    int ret = -1;
    if (changed) {
        if (eq_msp(b, (jl_value_t*)new_a, b0, a0, env))
            ret = swap;
        else if (swap)
            ret = type_morespecific_(b, (jl_value_t*)new_a, b0, a0, 0, env);
        else
            ret = type_morespecific_((jl_value_t*)new_a, b, a0, b0, 0, env);
    }
    JL_GC_POP();
    return ret;
}
```
-/
def argsMorespecificFix1 (n : Nat) (T : Types) (a b a0 b0 : Val) (swap : Bool)
    (env : MspEnv) : CM (Option Bool) :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    let na := a.nparams
    let taillen : Int := tupleFullLength b - Int.ofNat na + 1
    if taillen ≤ 0 then
      return none
    let lasta := a.params[na - 1]!.unwrapUnionall
    let instEnv : InstEnv :=
      match lasta.varargN?.bind Val.tvId with
      | some id => [(id, .long taillen)]
      | none => []
    let some newA ← instTypeW n T (subOps n T) a instEnv true 0
      | throw "unreachable: NULL with nothrow 0 in args_morespecific_fix1"
    let mut changed := false
    for i in [0:na - 1] do
      if a.params[i]! != newA.params[i]! then
        changed := true
        break
    if !changed then
      return none
    if ← eqMsp n T b newA b0 a0 env then
      return some swap
    else if swap then
      return some (← typeMorespecific_ n T b newA b0 a0 false env)
    else
      return some (← typeMorespecific_ n T newA b a0 b0 false env)

/-- `type_morespecific_`

Julia source: src/subtype.c:7462-7695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
static int type_morespecific_(jl_value_t *a, jl_value_t *b, jl_value_t *a0, jl_value_t *b0, int invariant, jl_typeenv_t *env)
{
    if (a == b)
        return 0;

    if (jl_is_tuple_type(a) && jl_is_tuple_type(b)) {
        // compare whether a and b have Type{Union{}} included,
        // which makes them instantly the most specific, regardless of all else,
        // for whichever is left most (the left-to-right behavior here ensures
        // we do not need to keep track of conflicts with multiple methods).
        int msp = tuple_cmp_typeofbottom((jl_datatype_t*)a, (jl_datatype_t*)b);
        if (msp)
            return msp > 0;
        // When one is JL_VARARG_BOUND and the other has fixed length,
        // allow the argument length to fix the tvar
        jl_vararg_kind_t akind = jl_va_tuple_kind((jl_datatype_t*)a);
        jl_vararg_kind_t bkind = jl_va_tuple_kind((jl_datatype_t*)b);
        int ans = -1;
        if (akind == JL_VARARG_BOUND && bkind < JL_VARARG_BOUND) {
            ans = args_morespecific_fix1(a, b, a0, b0, 0, env);
            if (ans == 1) return 1;
        }
        if (bkind == JL_VARARG_BOUND && akind < JL_VARARG_BOUND) {
            ans = args_morespecific_fix1(b, a, b0, a0, 1, env);
            if (ans == 0) return 0;
        }
        return tuple_morespecific((jl_datatype_t*)a, (jl_datatype_t*)b, a0, b0, invariant, env);
    }

    if (!invariant) {
        if ((jl_datatype_t*)a == jl_any_type) return 0;
        if ((jl_datatype_t*)b == jl_any_type && !jl_is_typevar(a)) return 1;
    }

    if (jl_is_uniontype(a)) {
        if (jl_is_unionall(b)) {
            HANDLE_UNIONALL_B;
        }
        // Union a is more specific than b if some element of a is more specific than b, but
        // not vice-versa.
        if (sub_msp(b, a, a0, env))
            return 0;
        jl_uniontype_t *u = (jl_uniontype_t*)a;
        if (type_morespecific_(u->a, b, a0, b0, invariant, env) || type_morespecific_(u->b, b, a0, b0, invariant, env)) {
            if (jl_is_uniontype(b)) {
                jl_uniontype_t *v = (jl_uniontype_t*)b;
                if (type_morespecific_(v->a, a, b0, a0, invariant, env) || type_morespecific_(v->b, a, b0, a0, invariant, env))
                    return 0;
            }
            return 1;
        }
        return 0;
    }

    if (jl_is_some_Type(a) && !invariant) {
        if (b == (jl_value_t*)jl_typeofbottom_type)
            return 0;
        jl_value_t *tp0a = jl_some_Type_T(a);
        if (jl_is_typevar(tp0a)) {
            jl_value_t *ub = ((jl_tvar_t*)tp0a)->ub;
            if (jl_is_kind(b) && !sub_msp((jl_value_t*)jl_any_type, ub, b0, env))
                return 1;
        }
        else if (tp0a == jl_bottom_type) {
            if (sub_msp(b, (jl_value_t*)jl_type_type, (jl_value_t*)jl_type_type, env))
                return 1;
        }
        else if (jl_is_kind(b)) {
            return 1;
        }
    }

    if (jl_is_uniontype(b)) {
        if (jl_is_unionall(a)) {
            HANDLE_UNIONALL_A;
        }
        jl_uniontype_t *u = (jl_uniontype_t*)b;
        if (type_morespecific_(a, u->a, a0, b0, invariant, env) || type_morespecific_(a, u->b, a0, b0, invariant, env))
            return !type_morespecific_(b, a, b0, a0, invariant, env);
        return 0;
    }

    if (jl_is_some_Type(a) && jl_is_some_Type(b)) {
        jl_value_t *apara = jl_some_Type_T(a);
        jl_value_t *bpara = jl_some_Type_T(b);
        int afree = jl_has_free_typevars(apara);
        int bfree = jl_has_free_typevars(bpara);
        if (!afree && !bfree && !jl_types_equal(apara, bpara))
            return 0;
        if (type_morespecific_(apara, bpara, a0, b0, 1, env) && (jl_is_typevar(apara) || !afree || bfree))
            return 1;
        if (type_morespecific_(bpara, apara, b0, a0, 1, env) && (jl_is_typevar(bpara) || !bfree || afree))
            return 0;
        if (eq_msp(apara, bpara, a0, b0, env))
            return !afree && bfree;
        return 0;
    }

    if (jl_is_kind(a) && jl_is_typeeq(b) && !invariant) {
        // a kind (e.g. `DataType`) is more specific than an unbounded `Type{T}`
        jl_value_t *tp0b = jl_typeeq_T(b);
        if (jl_is_typevar(tp0b) && sub_msp((jl_value_t*)jl_any_type, ((jl_tvar_t*)tp0b)->ub, b0, env))
            return 1;
    }

    if (jl_is_datatype(a) && jl_is_datatype(b)) {
        jl_datatype_t *tta = (jl_datatype_t*)a, *ttb = (jl_datatype_t*)b;
        // Type{Union{}} is more specific than other types, so TypeofBottom must be too
        if (tta == jl_typeofbottom_type && (is_kind_or_anytype(b) || jl_is_typeeq(b)))
            return 1;
        int super = 0;
        while (tta != jl_any_type) {
            if (tta->name == ttb->name) {
                if (super) {
                    if (!jl_is_typeeq(b)) return 1;
                    jl_value_t *tp0 = jl_typeeq_T(b);
                    if (jl_is_typevar(tp0)) {
                        if (sub_msp((jl_value_t*)jl_any_type, ((jl_tvar_t*)tp0)->ub, b0, env))
                            return 1;
                    }
                }
                assert(jl_nparams(tta) == jl_nparams(ttb));
                int ascore=0, bscore=0, ascore1=0, bscore1=0, adiag=0, bdiag=0;
                for(size_t i=0; i < jl_nparams(tta); i++) {
                    jl_value_t *apara = jl_tparam(tta,i);
                    jl_value_t *bpara = jl_tparam(ttb,i);
                    int afree = jl_has_free_typevars(apara);
                    int bfree = jl_has_free_typevars(bpara);
                    if (!afree && !bfree && !jl_types_equal(apara, bpara))
                        return 0;
                    if (type_morespecific_(apara, bpara, a0, b0, 1, env) && (jl_is_typevar(apara) || !afree || bfree))
                        ascore += 1;
                    else if (type_morespecific_(bpara, apara, b0, a0, 1, env) && (jl_is_typevar(bpara) || !bfree || afree))
                        bscore += 1;
                    else if (eq_msp(apara, bpara, a0, b0, env)) {
                        if (!afree && bfree)
                            ascore += 1;
                        else if (afree && !bfree)
                            bscore += 1;
                    }
                    if (jl_is_typevar(bpara) && !jl_is_typevar(apara) && !jl_is_type(apara))
                        ascore1 = 1;
                    else if (jl_is_typevar(apara) && !jl_is_typevar(bpara) && !jl_is_type(bpara))
                        bscore1 = 1;
                    if (!adiag && jl_is_typevar(apara)) {
                        for(int j=i+1; j < jl_nparams(tta); j++) {
                            if (jl_has_typevar(jl_tparam(tta,j), (jl_tvar_t*)apara)) {
                                adiag = 1; break;
                            }
                        }
                    }
                    if (!bdiag && jl_is_typevar(bpara)) {
                        for(int j=i+1; j < jl_nparams(ttb); j++) {
                            if (jl_has_typevar(jl_tparam(ttb,j), (jl_tvar_t*)bpara)) {
                                bdiag = 1; break;
                            }
                        }
                    }
                }
                if (ascore1 > bscore1)
                    return 1;
                if (bscore1 > ascore1 || bscore > ascore || bdiag > adiag)
                    return 0;
                return ascore > bscore || adiag > bdiag;
            }
            tta = jl_datatype_compute_super(tta); super = 1;
            if (tta == NULL)
                return 0; // definition in progress
        }
        return 0;
    }

    if (jl_is_typevar(a)) {
        if (jl_is_typevar(b)) {
            return (( type_morespecific_((jl_value_t*)((jl_tvar_t*)a)->ub,
                                         (jl_value_t*)((jl_tvar_t*)b)->ub, a0, b0, 0, env) &&
                     !type_morespecific_((jl_value_t*)((jl_tvar_t*)a)->lb,
                                         (jl_value_t*)((jl_tvar_t*)b)->lb, a0, b0, 0, env)) ||
                    ( type_morespecific_((jl_value_t*)((jl_tvar_t*)b)->lb,
                                         (jl_value_t*)((jl_tvar_t*)a)->lb, b0, a0, 0, env) &&
                     !type_morespecific_((jl_value_t*)((jl_tvar_t*)b)->ub,
                                         (jl_value_t*)((jl_tvar_t*)a)->ub, b0, a0, 0, env)));
        }
        if (!jl_is_type(b))
            return 0;
        if (invariant) {
            if (((jl_tvar_t*)a)->ub == jl_bottom_type)
                return 1;
            if (!jl_has_free_typevars(b))
                return 0;
            if (eq_msp(((jl_tvar_t*)a)->ub, b, a0, b0, env))
                return num_occurs((jl_tvar_t*)a, env) >= 2;
        }
        else {
            // need `{T,T} where T` more specific than `{Any, Any}`
            if (b == (jl_value_t*)jl_any_type && ((jl_tvar_t*)a)->ub == (jl_value_t*)jl_any_type &&
                num_occurs((jl_tvar_t*)a, env) >= 2)
                return 1;
        }
        return type_morespecific_(((jl_tvar_t*)a)->ub, b, a0, b0, 0, env);
    }
    if (jl_is_typevar(b)) {
        if (!jl_is_type(a))
            return 1;
        if (invariant) {
            if (((jl_tvar_t*)b)->ub == jl_bottom_type)
                return 0;
            if (jl_has_free_typevars(a)) {
                if (type_morespecific_(a, ((jl_tvar_t*)b)->ub, a0, b0, 0, env))
                    return 1;
                if (eq_msp(a, ((jl_tvar_t*)b)->ub, a0, b0, env))
                    return num_occurs((jl_tvar_t*)b, env) < 2;
                return 0;
            }
            else {
                if (obviously_disjoint(a, ((jl_tvar_t*)b)->ub, 1))
                    return 0;
                if (type_morespecific_(((jl_tvar_t*)b)->ub, a, b0, a0, 0, env))
                    return 0;
                return 1;
            }
        }
        return type_morespecific_(a, ((jl_tvar_t*)b)->ub, a0, b0, 0, env);
    }

    if (jl_is_unionall(a)) {
        HANDLE_UNIONALL_A;
    }
    if (jl_is_unionall(b)) {
        HANDLE_UNIONALL_B;
    }

    return 0;
}
```
-/
def typeMorespecific_ (n : Nat) (T : Types) (a b a0 b0 : Val) (invariant : Bool)
    (env : MspEnv) : CM Bool :=
  match n with
  | 0 => outOfBudget
  | n + 1 => do
    if a == b then
      return false
    if a.isTupleType && b.isTupleType then
      let msp ← tupleCmpTypeofbottom n a b
      if msp != 0 then
        return msp > 0
      let akind := vaTupleKind a
      let bkind := vaTupleKind b
      if akind == .bound && bkind.rank < VarargKind.bound.rank then
        let ans ← argsMorespecificFix1 n T a b a0 b0 false env
        if ans == some true then
          return true
      if bkind == .bound && akind.rank < VarargKind.bound.rank then
        let ans ← argsMorespecificFix1 n T b a b0 a0 true env
        if ans == some false then
          return false
      return ← tupleMorespecific n T a b a0 b0 invariant env
    if !invariant then
      if a == anyType then return false
      if b == anyType && !a.isTypevar then return true
    if let .union ua ub := a then
      if let .unionall id nm lb ubVar body := b then
        let var := Val.typevar id nm lb ubVar
        let occ ← countOccurs n body var
        return ← typeMorespecific_ n T a body a0 b0 invariant ({ var := var, numOccurs := occ } :: env)
      if ← subMsp n T b a a0 env then
        return false
      let mspUa ← typeMorespecific_ n T ua b a0 b0 invariant env
      let mspUb ← if mspUa then pure true else typeMorespecific_ n T ub b a0 b0 invariant env
      if mspUb then
        if let .union va vb := b then
          let mspVa ← typeMorespecific_ n T va a b0 a0 invariant env
          let mspVb ← if mspVa then pure true else typeMorespecific_ n T vb a b0 a0 invariant env
          if mspVb then
            return false
        return true
      return false
    if a.isSomeType && !invariant then
      if b == typeofbottomType then
        return false
      let tp0a := a.someTypeT
      if tp0a.isTypevar then
        let ub := tp0a.tvUb
        if isKind b then
          if !(← subMsp n T anyType ub b0 env) then
            return true
      else if tp0a == .bottom then
        if ← subMsp n T b typeType typeType env then
          return true
      else if isKind b then
        return true
    if let .union ua ub := b then
      if let .unionall id nm lb ubVar body := a then
        let var := Val.typevar id nm lb ubVar
        let occ ← countOccurs n body var
        return ← typeMorespecific_ n T body b a0 b0 invariant ({ var := var, numOccurs := occ } :: env)
      let mspUa ← typeMorespecific_ n T a ua a0 b0 invariant env
      let mspUb ← if mspUa then pure true else typeMorespecific_ n T a ub a0 b0 invariant env
      if mspUb then
        return !(← typeMorespecific_ n T b a b0 a0 invariant env)
      return false
    if a.isSomeType && b.isSomeType then
      let apara := a.someTypeT
      let bpara := b.someTypeT
      let afree := apara.hasFreeTypevars
      let bfree := bpara.hasFreeTypevars
      if !afree && !bfree then
        if !(← jlTypesEqual n T apara bpara) then
          return false
      if ← typeMorespecific_ n T apara bpara a0 b0 true env then
        if apara.isTypevar || !afree || bfree then
          return true
      if ← typeMorespecific_ n T bpara apara b0 a0 true env then
        if bpara.isTypevar || !bfree || afree then
          return false
      if ← eqMsp n T apara bpara a0 b0 env then
        return !afree && bfree
      return false
    if isKind a && b.isTypeeq && !invariant then
      let tp0b := b.someTypeT
      if tp0b.isTypevar then
        if ← subMsp n T anyType tp0b.tvUb b0 env then
          return true
    if a.isDatatype && b.isDatatype then
      if a == typeofbottomType && (isKindOrAnytype b || b.isTypeeq) then
        return true
      let mut tta := a
      let ttb := b
      let mut isSuper := false
      let mut steps := n
      while tta != anyType do
        if steps == 0 then outOfBudget
        steps := steps - 1
        if tta.name? == ttb.name? then
          if isSuper then
            if !b.isTypeeq then
              return true
            let tp0 := b.someTypeT
            if tp0.isTypevar then
              if ← subMsp n T anyType tp0.tvUb b0 env then
                return true
          let np := tta.nparams
          let mut ascore : Nat := 0
          let mut bscore : Nat := 0
          let mut ascore1 : Nat := 0
          let mut bscore1 : Nat := 0
          let mut adiag : Nat := 0
          let mut bdiag : Nat := 0
          for i in [0:np] do
            let apara := tta.params[i]!
            let bpara := ttb.params[i]!
            let afree := apara.hasFreeTypevars
            let bfree := bpara.hasFreeTypevars
            if !afree && !bfree then
              if !(← jlTypesEqual n T apara bpara) then
                return false
            let mspAB ← typeMorespecific_ n T apara bpara a0 b0 true env
            if mspAB && (apara.isTypevar || !afree || bfree) then
              ascore := ascore + 1
            else
              let mspBA ← typeMorespecific_ n T bpara apara b0 a0 true env
              if mspBA && (bpara.isTypevar || !bfree || afree) then
                bscore := bscore + 1
              else if ← eqMsp n T apara bpara a0 b0 env then
                if !afree && bfree then
                  ascore := ascore + 1
                else if afree && !bfree then
                  bscore := bscore + 1
            if bpara.isTypevar && !apara.isTypevar && !apara.isType then
              ascore1 := 1
            else if apara.isTypevar && !bpara.isTypevar && !bpara.isType then
              bscore1 := 1
            if adiag == 0 && apara.isTypevar then
              for j in [i + 1 : np] do
                if tta.params[j]!.hasTypevar apara then
                  adiag := 1
                  break
            if bdiag == 0 && bpara.isTypevar then
              for j in [i + 1 : ttb.nparams] do
                if ttb.params[j]!.hasTypevar bpara then
                  bdiag := 1
                  break
          if ascore1 > bscore1 then
            return true
          if bscore1 > ascore1 || bscore > ascore || bdiag > adiag then
            return false
          return ascore > bscore || adiag > bdiag
        tta ← superOf n T (subOps n T) tta
        isSuper := true
      return false
    if a.isTypevar then
      if b.isTypevar then
        let ubAB ← typeMorespecific_ n T a.tvUb b.tvUb a0 b0 false env
        let branch1 ←
          if ubAB then
            pure (!(← typeMorespecific_ n T a.tvLb b.tvLb a0 b0 false env))
          else
            pure false
        if branch1 then
          return true
        let lbBA ← typeMorespecific_ n T b.tvLb a.tvLb b0 a0 false env
        if lbBA then
          return !(← typeMorespecific_ n T b.tvUb a.tvUb b0 a0 false env)
        return false
      if !b.isType then
        return false
      if invariant then
        if a.tvUb == .bottom then
          return true
        if !b.hasFreeTypevars then
          return false
        if ← eqMsp n T a.tvUb b a0 b0 env then
          return numOccurs a env ≥ 2
      else
        -- need `{T,T} where T` more specific than `{Any, Any}`
        if b == anyType && a.tvUb == anyType && numOccurs a env ≥ 2 then
          return true
      return ← typeMorespecific_ n T a.tvUb b a0 b0 false env
    if b.isTypevar then
      if !a.isType then
        return true
      if invariant then
        if b.tvUb == .bottom then
          return false
        if a.hasFreeTypevars then
          if ← typeMorespecific_ n T a b.tvUb a0 b0 false env then
            return true
          if ← eqMsp n T a b.tvUb a0 b0 env then
            return numOccurs b env < 2
          return false
        else
          if ← obviouslyDisjoint n T a b.tvUb true then
            return false
          if ← typeMorespecific_ n T b.tvUb a b0 a0 false env then
            return false
          return true
      return ← typeMorespecific_ n T a b.tvUb a0 b0 false env
    if let .unionall id nm lb ubVar body := a then
      let var := Val.typevar id nm lb ubVar
      let occ ← countOccurs n body var
      return ← typeMorespecific_ n T body b a0 b0 invariant ({ var := var, numOccurs := occ } :: env)
    if let .unionall id nm lb ubVar body := b then
      let var := Val.typevar id nm lb ubVar
      let occ ← countOccurs n body var
      return ← typeMorespecific_ n T a body a0 b0 invariant ({ var := var, numOccurs := occ } :: env)
    return false
end

/-- `jl_type_morespecific`

Julia source: src/subtype.c:7697-7708 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_type_morespecific(jl_value_t *a, jl_value_t *b)
{
    if (obviously_disjoint(a, b, 1))
        return 0;
    if (jl_has_free_typevars(a) || jl_has_free_typevars(b))
        return 0;
    if (jl_subtype(b, a))
        return 0;
    if (jl_subtype(a, b))
        return 1;
    return type_morespecific_(a, b, a, b, 0, NULL);
}
```
-/
def jlTypeMorespecific (n : Nat) (T : Types) (a b : Val) : CM Bool := do
  if ← obviouslyDisjoint n T a b true then
    return false
  if a.hasFreeTypevars || b.hasFreeTypevars then
    return false
  if ← jlSubtype n T b a then
    return false
  if ← jlSubtype n T a b then
    return true
  typeMorespecific_ n T a b a b false []

/-- `jl_type_morespecific_no_subtype`

Julia source: src/subtype.c:7710-7713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_type_morespecific_no_subtype(jl_value_t *a, jl_value_t *b)
{
    return type_morespecific_(a, b, a, b, 0, NULL);
}
```
-/
def jlTypeMorespecificNoSubtype (n : Nat) (T : Types) (a b : Val) : CM Bool :=
  typeMorespecific_ n T a b a b false []

/-- `jl_method_morespecific`: equivalent to `jl_type_morespecific` of the signatures, except that
more recent methods (`maPrimaryWorld > mbPrimaryWorld`) are more specific iff the method signatures
are type-equal.

Julia source: src/subtype.c:7717-7733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
JL_DLLEXPORT int jl_method_morespecific(jl_method_t *ma, jl_method_t *mb)
{
    jl_value_t *a = (jl_value_t*)ma->sig;
    jl_value_t *b = (jl_value_t*)mb->sig;
    if (obviously_disjoint(a, b, 1))
        return 0;
    if (jl_has_free_typevars(a) || jl_has_free_typevars(b))
        return 0;
    if (jl_subtype(b, a)) {
        if (jl_types_equal(a, b))
            return jl_atomic_load_relaxed(&ma->primary_world) > jl_atomic_load_relaxed(&mb->primary_world);
        return 0;
    }
    if (jl_subtype(a, b))
        return 1;
    return type_morespecific_(a, b, a, b, 0, NULL);
}
```
-/
def jlMethodMorespecific (n : Nat) (T : Types) (maSig : Val) (maPrimaryWorld : Nat)
    (mbSig : Val) (mbPrimaryWorld : Nat) : CM Bool := do
  let a := maSig
  let b := mbSig
  if ← obviouslyDisjoint n T a b true then
    return false
  if a.hasFreeTypevars || b.hasFreeTypevars then
    return false
  if ← jlSubtype n T b a then
    if ← jlTypesEqual n T a b then
      return maPrimaryWorld > mbPrimaryWorld
    return false
  if ← jlSubtype n T a b then
    return true
  typeMorespecific_ n T a b a b false []

end JuliaLean.C
