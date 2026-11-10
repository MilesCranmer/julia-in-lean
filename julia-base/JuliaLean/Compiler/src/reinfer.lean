import JuliaLean.Compiler.src.bindinginvalidations

/-!
Model of `Compiler/src/reinfer.jl`: edge verification when a package image loads.

`insert_backedges` re-checks every code instance of a loaded image against the method table and
bindings of the loading process. Each code instance's edge list records what the image saw:
the matches of each dispatch call (`verify_call`), the target of each `invoke`
(`verify_invokesig`), each binding read, and the code instances it calls, which are verified
recursively with Tarjan's strongly-connected-components walk (`verify_method`). The result is
a world range written back into each code instance (`max_world == 0` rejects it).

The state machine of `verify_method` is mirrored step by step: the three state arrays, the
Tarjan stack and `visiting` table, and the stages. The heap (`State.lean`) holds the objects;
the C runtime queries are the `Oracle`.

Not modelled: the `_jl_debug_method_invalidation` log, which changes control flow when it is
on (the model is the default, log off); `needs_instrumentation` under code coverage or
allocation logging (an `unmodelled` failure); the bodies of the C side effects
`jl_mi_cache_insert` and `store_backedges` (an event each; of `store_backedges` only the effect
of its binding items on `did_scan_source` and the binding flags is applied) and the locking in
`jl_promote_mi_to_current`.
-/

namespace JuliaLean.Compiler.Reinfer

open JuliaLean.C JuliaLean.Compiler.CICache

/-- The memoized lookup `VerifyMethodLookup`.

Julia source: Compiler/src/reinfer.jl:41-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A memoized `_methods_by_ftype` lookup: the same callee signature is verified once per
# caller, and the answer is the same for every query world inside its validity range.
struct VerifyMethodLookup
    lim::Int
    world::UInt
    result::Union{Nothing,Vector{Any}}
    min_world::UInt
    max_world::UInt
    has_ambig::Int32
end
```
-/
structure Lookup where
  lim : Int
  world : Nat
  result : Option (List Nat)
  minWorld : Nat
  maxWorld : Nat
  hasAmbig : Int
  deriving Inhabited

/-- `VerifyMethodInitialState`; `codeinst`, `mi`, `def` are ids.

Julia source: Compiler/src/reinfer.jl:20-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VerifyMethodInitialState
    codeinst::CodeInstance
    mi::MethodInstance
    def::Method
    callees::Core.SimpleVector
    image::UInt # linkage blob owning `codeinst`, or typemax(UInt) if it is in no image
end
```
-/
structure InitialState where
  codeinst : Nat
  mi : Nat
  def_ : Nat
  callees : Array Edge
  image : Nat
  deriving Inhabited

/-- The `stage` symbols of `VerifyMethodWorkState`. -/
inductive Stage where
  | initAndProcessCallees
  | recursivePhase
  | cleanup
  | returnToParent
  deriving Inhabited, BEq, DecidableEq, Repr

/-- `VerifyMethodWorkState`

Julia source: Compiler/src/reinfer.jl:28-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VerifyMethodWorkState
    depth::Int
    cause::CodeInstance
    recursive_index::Int
    stage::Symbol
end
```
-/
structure WorkState where
  depth : Nat
  cause : Nat
  recursiveIndex : Nat
  stage : Stage
  deriving Inhabited

/-- `VerifyMethodResultState`

Julia source: Compiler/src/reinfer.jl:35-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct VerifyMethodResultState
    child_cycle::Int
    result_minworld::UInt
    result_maxworld::UInt
end
```
-/
structure ResultState where
  childCycle : Nat
  resultMinworld : Nat
  resultMaxworld : Nat
  deriving Inhabited, BEq, Repr

/-- `VerifyMethodWorkspace`. `visiting` is an `IdDict{CodeInstance,Int}`, `lookups` an
`IdDict` keyed by the signature object (`Sig.oid`). The scratch vectors `matches`, `expected`
and the `RefValue`s are locals of the model's functions; `backedge_scratch` only serves
`store_backedges`.

Julia source: Compiler/src/reinfer.jl:52-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Container for all the work arrays
struct VerifyMethodWorkspace
    # Arrays of different state categories
    initial_states::Vector{VerifyMethodInitialState}
    work_states::Vector{VerifyMethodWorkState}
    result_states::Vector{VerifyMethodResultState}

    # Tarjan's algorithm working data
    stack::Vector{CodeInstance}
    visiting::IdDict{CodeInstance,Int}

    # Scratch for `verify_call`, reused across calls to avoid allocating per edge
    matches::Vector{Any}
    expected::Vector{Method}
    minworld::RefValue{UInt}
    maxworld::RefValue{UInt}
    has_ambig::RefValue{Int32}
    lookups::IdDict{Any,VerifyMethodLookup}
    backedge_scratch::IdSet{Any}

    function VerifyMethodWorkspace()
        new(VerifyMethodInitialState[], VerifyMethodWorkState[], VerifyMethodResultState[],
            CodeInstance[], IdDict{CodeInstance,Int}(),
            Any[], Method[], RefValue{UInt}(1), RefValue{UInt}(typemax(UInt)), RefValue{Int32}(0),
            IdDict{Any,VerifyMethodLookup}(), IdSet{Any}())
    end
end
```
-/
structure Workspace where
  initialStates : Array InitialState := #[]
  workStates : Array WorkState := #[]
  resultStates : Array ResultState := #[]
  stack : Array Nat := #[]
  visiting : List (Nat × Nat) := []
  lookups : List (Nat × Lookup) := []
  deriving Inhabited

abbrev VM := RM Workspace

def getWS : VM Workspace := do return (← get).ws
def modifyWS (f : Workspace → Workspace) : VM Unit := modify fun s => { s with ws := f s.ws }

/-- The debug log `_jl_debug_method_invalidation[]` is off in the model. -/
def debugLog : Bool := false

def assert' (c : Bool) (msg : String) : VM Unit :=
  if c then pure () else jlThrow "AssertionError" msg

/-- `VerifyMethodInitialState(codeinst)`, `VerifyMethodWorkState(dummy_cause)`,
`VerifyMethodResultState()`. `mi.def::Method` holds for every method instance in the heap.

Julia source: Compiler/src/reinfer.jl:80-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Helper functions to create default states
function VerifyMethodInitialState(codeinst::CodeInstance)
    mi = get_ci_mi(codeinst)
    def = mi.def::Method
    image = external_blob_index(codeinst)
    VerifyMethodInitialState(codeinst, mi, def, codeinst.edges, image)
end

function VerifyMethodWorkState(dummy_cause::CodeInstance)
    VerifyMethodWorkState(0, dummy_cause, 1, :init_and_process_callees)
end

function VerifyMethodResultState()
    VerifyMethodResultState(0, 0, 0)
end
```
-/
def mkInitialState (ci : Nat) : VM InitialState := do
  let H ← getHeap
  let c ← liftE (H.ciR ci)
  let mi ← liftE (H.miR c.mi)
  return { codeinst := ci, mi := c.mi, def_ := mi.def_, callees := c.callees, image := c.blob }

def mkWorkState (dummyCause : Nat) : WorkState := ⟨0, dummyCause, 1, .initAndProcessCallees⟩
def mkResultState : ResultState := ⟨0, 0, 0⟩

/-- `needs_instrumentation(codeinst, mi, def, validation_world)` without coverage or allocation
logging; with either on it is `unmodelled`.

Julia source: Compiler/src/reinfer.jl:180-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function needs_instrumentation(codeinst::CodeInstance, mi::MethodInstance, def::Method, validation_world::UInt)
    # foreign CIs (owner !== nothing) aren't run as native code here, so instrumenting them is moot
    codeinst.owner === nothing || return false
    if JLOptions().code_coverage != 0 || JLOptions().malloc_log != 0
        # test if the code needs to run with instrumentation, in which case we cannot use existing generated code
        if isdefined(def, :debuginfo) ? # generated_only functions do not have debuginfo, so fall back to considering their codeinst debuginfo though this may be slower and less reliable
            should_instrument(def.module, def.debuginfo) :
            isdefined(codeinst, :debuginfo) && should_instrument(def.module, codeinst.debuginfo)
            # Compatible image code already has the requested counters.
            # Allocation tracking still needs fresh instrumentation.
            if JLOptions().malloc_log == 0 && ccall(:jl_codeinst_coverage_compatible, Cint, (Any,), codeinst) != 0
                return false
            end
            return true
        end
        gensig = gen_staged_sig(def, mi)
        if gensig !== nothing
            # if this is defined by a generator, try to consider forcing re-running the generators too, to add coverage for them
            minworld = RefValue{UInt}(1)
            maxworld = RefValue{UInt}(typemax(UInt))
            has_ambig = RefValue{Int32}(0)
            result = _methods_by_ftype(gensig, nothing, -1, validation_world, #=ambig=#false, minworld, maxworld, has_ambig)
            if result !== nothing
                for k = 1:length(result)
                    match = result[k]::Core.MethodMatch
                    genmethod = match.method
                    # no, I refuse to refuse to recurse into your cursed generated function generators and will only test one level deep here
                    if isdefined(genmethod, :debuginfo) && should_instrument(genmethod.module, genmethod.debuginfo)
                        return true
                    end
                end
            end
        end
    end
    return false
end
```
-/
def needsInstrumentation (ci : Nat) : VM Bool := do
  let H ← getHeap
  let c ← liftE (H.ciR ci)
  if !c.ownerNothing then return false
  if H.instrumenting then throw "unmodelled: needs_instrumentation under coverage"
  return false

/-- `get_method_from_edge(t)`: `t` is a `Method`, `CodeInstance` or `MethodInstance`
(`t::MethodInstance` throws a `TypeError` otherwise).

Julia source: Compiler/src/reinfer.jl:468-479 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_method_from_edge(@nospecialize t)
    if t isa Method
        return t
    else
        if t isa CodeInstance
            t = get_ci_mi(t)::MethodInstance
        else
            t = t::MethodInstance
        end
        return t.def::Method
    end
end
```
-/
def getMethodFromEdge (t : Edge) : VM Nat := do
  let H ← getHeap
  match t with
  | .method m => return m
  | .ci c => do let c ← liftE (H.ciR c); return (← liftE (H.miR c.mi)).def_
  | .mi m => return (← liftE (H.miR m)).def_
  | _ => jlThrow "TypeError" "typeassert MethodInstance"

/-- `get_mi_from_edge(t)`

Julia source: Compiler/src/reinfer.jl:481-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The MethodInstance behind an edge, or `nothing` for a bare Method edge
function get_mi_from_edge(@nospecialize t)
    t isa Method && return nothing
    t isa CodeInstance && return get_ci_mi(t)::MethodInstance
    return t::MethodInstance
end
```
-/
def getMiFromEdge (t : Edge) : VM (Option Nat) := do
  match t with
  | .method _ => return none
  | .ci c => return some (← liftE ((← getHeap).ciR c)).mi
  | .mi m => return some m
  | _ => jlThrow "TypeError" "typeassert MethodInstance"

/-- `expected_dominates_sig(meth, mi)`

Julia source: Compiler/src/reinfer.jl:488-497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The single expected match provably dominates the queried signature, so the result of
# `ml_matches` is already known to be just this method (only valid when `fully_covers`)
function expected_dominates_sig(meth::Method, mi::Union{Nothing,MethodInstance})
    if mi !== nothing && !iszero(mi.dispatch_status & METHOD_SIG_LATEST_ONLY)
        return true # the sole match for `mi.specTypes`
    end
    # an empty interference set is the Method-level equivalent of
    # METHOD_SIG_LATEST_ONLY: the method beats everything it intersects
    return isempty(meth.interferences)
end
```
-/
def expectedDominatesSig (meth : MethodR) (mi : Option MIR) : Bool :=
  match mi with
  | some mi => if hasBit mi.dispatchStatus methodSigLatestOnly then true
               else meth.interferencesLen == 0
  | none => meth.interferencesLen == 0

/-- `method_in_expecteds(m, expected)`

Julia source: Compiler/src/reinfer.jl:499-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Check if `m` is one of the expected methods of this run
function method_in_expecteds(m::Method, expected::Vector{Method})
    for meth in expected
        if m === meth
            return true
        end
    end
    return false
end
```
-/
def methodInExpecteds (m : Nat) (expected : List Nat) : Bool := expected.contains m

/-- `eachinterference(m, cutoff)` iterated to the end: the assigned entries, stopping before the
first one whose method's `primary_world` is past `cutoff`.

Julia source: Compiler/src/reinfer.jl:509-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Iterate a method's `interferences` set. The set is an idset used append-only,
# in method-definition order. Iteration therefore stops at the first
# unassigned slot and, given a world cutoff, at the first entry defined in a
# future world (which hides all later ones too).
struct EachInterference
    interferences::Memory{Any}
    cutoff::UInt # typemax(UInt) means no world cutoff
end
eachinterference(m::Method, cutoff::UInt=typemax(UInt)) = EachInterference(m.interferences, cutoff)
function Base.iterate(ei::EachInterference, k::Int=1)
    interferences = ei.interferences
    k > length(interferences) && return nothing
    isassigned(interferences, k) || return nothing # no more entries
    interference_method = interferences[k]::Method
    ei.cutoff < interference_method.primary_world && return nothing # this and later entries are for a future world
    return interference_method, k + 1
end
```
-/
def eachinterference (H : Heap) (m : MethodR) (cutoff : Nat := typemaxUInt) :
    Except String (List MethodR) := do
  let mut out : Array MethodR := #[]
  for k in m.interferences do
    let im ← H.method k
    if cutoff < im.primaryWorld then break
    out := out.push im
  return out.toList

/-- `method_in_interferences(method2, method1)`: `method2` is in `method1`'s set.

Julia source: Compiler/src/reinfer.jl:527-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Check if method2 is in method1's interferences set
# Returns true if method2 is found (meaning !morespecific(method1, method2))
function method_in_interferences(method2::Method, method1::Method)
    for interference_method in eachinterference(method1)
        if interference_method === method2
            return true
        end
    end
    return false
end
```
-/
def methodInInterferences (H : Heap) (method2 method1 : MethodR) : Except String Bool := do
  return (← eachinterference H method1).any (·.uid == method2.uid)

/-- `method_morespecific_recorded(method1, method2)`

Julia source: Compiler/src/reinfer.jl:538-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Check if method1 is more specific than method2 via the interference graph
# equivalent to: morespecific(method1, method2) && typeintersect(method1.sig, method2.sig) !== Union{}
function method_morespecific_recorded(method1::Method, method2::Method)
    method1 === method2 && return false
    return method_in_interferences(method1, method2) && !method_in_interferences(method2, method1)
end
```
-/
def methodMorespecificRecorded (H : Heap) (method1 method2 : MethodR) : Except String Bool := do
  if method1.uid == method2.uid then return false
  if !(← methodInInterferences H method1 method2) then return false
  return !(← methodInInterferences H method2 method1)

/-- `method_is_latest_which(m)`

Julia source: Compiler/src/reinfer.jl:545-548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The fast-path `dispatch_status` bit is set: `which` would return this method when
# invoking `method.sig` in the current latest world. False indicates unknown, so callers
# must treat a false result as conservatively as an actually deleted method.
method_is_latest_which(m::Method) = !iszero(m.dispatch_status & METHOD_SIG_LATEST_WHICH)
```
-/
def methodIsLatestWhich (m : MethodR) : Bool := hasBit m.dispatchStatus methodSigLatestWhich

/-- `method_in_image_deps(m, image)`

Julia source: Compiler/src/reinfer.jl:550-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return true if `m` was already present when `image` was precompiled.
function method_in_image_deps(m::Method, image::UInt)
    image == typemax(UInt) && return false # code of no image had no worker
    blob = external_blob_index(m)
    blob == typemax(UInt) && return false # a method of no image
    return ccall(:jl_linkage_blob_dep_world, Csize_t, (Csize_t, Csize_t), image, blob) != 0
end
```
-/
def methodInImageDeps (O : Oracle) (m : MethodR) (image : Nat) : Except String Bool := do
  if image == typemaxUInt then return false
  let blob := m.blob
  if blob == typemaxUInt then return false
  return (← O.linkageBlobDepWorld image blob) != 0

/-- `sig_contributors_world(sig, mt, image)`

Julia source: Compiler/src/reinfer.jl:558-564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return the world since which every method in `mt` that could match `sig` has been present,
# if all of them were already present when `image` was precompiled, else 0.
function sig_contributors_world(@nospecialize(sig), mt::Core.MethodTable, image::UInt)
    _jl_debug_method_invalidation[] === nothing || return UInt(0)
    image == typemax(UInt) && return UInt(0)
    return ccall(:jl_sig_contributors_world, Csize_t, (Any, Any, Csize_t), sig, mt, image)
end
```
-/
def sigContributorsWorld (O : Oracle) (sig : Val) (image : Nat) : Except String Nat := do
  if debugLog then return 0
  if image == typemaxUInt then return 0
  O.sigContributorsWorld sig image

/-- `promote_mi_to_current(mi, minworld, world)` with `jl_promote_mi_to_current`
(`src/gf.c:2283-2302`): when the world counter is still `world`, the method's interference set
is nonempty, `minworld` is its `primary_world` and the instance lacks `METHOD_SIG_LATEST_ONLY`,
the instance's `dispatch_status` becomes exactly `METHOD_SIG_LATEST_ONLY`.

Julia source: Compiler/src/reinfer.jl:566-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_mi_to_current(mi::Union{Nothing,MethodInstance}, minworld::UInt, world::UInt)
    if mi isa MethodInstance
        ccall(:jl_promote_mi_to_current, Cvoid, (Any, UInt, UInt), mi, minworld, world)
    end
    nothing
end
```
-/
def promoteMiToCurrent (mi : Option Nat) (minworld world : Nat) : VM Unit := do
  let some mi := mi | return
  let H ← getHeap
  if H.worldCounter > world then return
  let miR ← liftE (H.miR mi)
  let definition ← liftE (H.method miR.def_)
  if definition.interferencesLen == 0 || minworld != definition.primaryWorld ||
      hasBit miR.dispatchStatus methodSigLatestOnly then return
  if H.worldCounter == world then
    emit (.path "promote-mi")
    modifyHeap (·.setMI { miR with dispatchStatus := methodSigLatestOnly })

/-- `VERIFY_INTERF_CAP` (`Compiler/src/reinfer.jl:576`). -/
def verifyInterfCap : Nat := 8

/-- `expected_is_minmax(meth, interference_method, sig, expected)`

Julia source: Compiler/src/reinfer.jl:638-649 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expected_is_minmax(meth::Method, interference_method::Method, @nospecialize(sig),
                            expected::Vector{Method})
    sig <: meth.sig || return false                 # `meth` fully covers sig
    sig <: interference_method.sig && return false  # its partner does not
    for meth2 in expected      # and `meth` beats every other full cover
        meth2 === meth && continue
        if sig <: meth2.sig && !method_morespecific_recorded(meth, meth2)
            return false
        end
    end
    return true
end
```
-/
def expectedIsMinmax (O : Oracle) (H : Heap) (meth im : MethodR) (sig : Val)
    (expected : List MethodR) : Except String Bool := do
  if !(← O.sub sig meth.sig) then return false
  if ← O.sub sig im.sig then return false
  for meth2 in expected do
    if meth2.uid == meth.uid then continue
    if ← O.sub sig meth2.sig then
      if !(← methodMorespecificRecorded H meth meth2) then return false
  return true

/-- `has_empty_set_cover(interference_method, ti, expected)`

Julia source: Compiler/src/reinfer.jl:651-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Look for an expected method that covers the removed `interference_method` over their
# intersection `ti` and provably certifies the removal as silent: only an expected with an
# empty interference set qualifies, since such a method beats everything it intersects, so:
#  - nothing beats or ties it, so it can never sit in a specificity cycle and always
#    finalizes before the sort needs it as a cover;
#  - every blocker transfer through it passes automatically;
#  - being recorded in the set of every method it intersects, it patches any
#    blocker-transfer region inside its signature for the other drops too.
# The `Union{}` bottom-slurp methods are exactly this shape, keeping verification fast when
# a later-added method intersects sig only at the `Type{Union{}}` corner they resolve. Any
# other unexpected entry is left to the full lookup (the sort's dominance-transfer
# protocol): anything weaker re-opens the cycle counterexamples, where a cover tangled in a
# specificity cycle certifies a drop it must not.
function has_empty_set_cover(interference_method::Method, @nospecialize(ti),
                             expected::Vector{Method})
    for meth2 in expected
        # the emptiness test is the O(1) bail, and also makes the second half of
        # `method_morespecific_recorded` a scan of the empty set
        if isempty(meth2.interferences) &&
            method_morespecific_recorded(meth2, interference_method) &&
            ti <: meth2.sig
            return true
        end
    end
    return false
end
```
-/
def hasEmptySetCover (O : Oracle) (H : Heap) (im : MethodR) (ti : Val)
    (expected : List MethodR) : Except String Bool := do
  for meth2 in expected do
    if meth2.interferencesLen == 0 then
      if ← methodMorespecificRecorded H meth2 im then
        if ← O.sub ti meth2.sig then return true
  return false

/-- `morespecific_cannot_cycle(interference_method, world)`

Julia source: Compiler/src/reinfer.jl:678-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Require every strictly morespecific method of the removed `interference_method` to have an empty
# interference set itself: like the cover found by `has_empty_set_cover`, such a method
# cannot continue a specificity cycle. This is the condition the last bullet above
# `newmethod_removed_silently` relies on to keep an acceptance conservative.
#
# Without it, a cycle through invisible methods could encounter the less-specific expected behind
# the caller's scan's back (dragging it into an SCC mid-sort, where it stops covering the
# invisible members and they survive into the result): detecting that re-entry edge
# directly would mean intersecting `interference_method`'s own set against sig -- the full
# lookup's price.
function morespecific_cannot_cycle(interference_method::Method, world::UInt)
    for msp in eachinterference(interference_method, world)
        # the iteration supplies `msp ∈ interference_method`'s set, which is the first
        # half of `method_morespecific_recorded(msp, interference_method)`, so this only
        # needs to now check the second half
        if !isempty(msp.interferences) &&
            !method_in_interferences(interference_method, msp)
            # a strict morespecific method that could itself sit on a cycle
            return false
        end
    end
    return true
end
```
-/
def morespecificCannotCycle (H : Heap) (im : MethodR) (world : Nat) : Except String Bool := do
  for msp in ← eachinterference H im world do
    if msp.interferencesLen != 0 then
      if !(← methodInInterferences H im msp) then return false
  return true

/-- `newmethod_removed_silently(meth, interference_method, ti, sig, expected, world)`

Julia source: Compiler/src/reinfer.jl:578-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The unexpected `interference_method` (the new method), recorded in expected method
# `meth`'s interference set, intersects the queried `sig` over the nonempty `ti`. Decide
# whether the sort provably removes it: acceptance implies the full `ml_matches`
# lookup would return exactly the `expected` methods with no ambiguity
# flag caused by the new method. Returns `false` conservative when a full lookup is
# necessary to decide.
#
# Accepting stays conservative even though the caller only ever offers up the unexpected
# methods recorded in the expected methods' own sets, because that scan witnesses every
# visible change:
#  - fully_covers means every method intersecting sig intersects some expected pointwise;
#  - methods invisible to it (strictly less-specific than every expected they intersect,
#    hence in no expected's set) always removed silently: the union of their intersecting
#    expecteds covers them, and a failing blocker transfer would need a blocker that beats
#    an expected cover -- which recording makes visible;
#  - any cycle that could flag or change the result must thread an expected, entering through
#    a visible interference method strictly morespecific than it -- an entry of that scan,
#    which is either rejected by the conditions below or by `morespecific_cannot_cycle`,
#    are provably not on any cycle.
function newmethod_removed_silently(meth::Method, interference_method::Method, @nospecialize(ti), @nospecialize(sig),
                                    expected::Vector{Method}, world::UInt)
    # the caller's scan supplies `interference_method ∈ meth`'s set, so this single probe
    # decides `method_morespecific_recorded(interference_method, meth)`: found means the
    # two are mutually ambiguous, absent means the new method strictly beats `meth`
    if method_in_interferences(meth, interference_method)
        expected_is_minmax(meth, interference_method, sig, expected) || return false
    end
    # Either way, the drop needs a certifying cover. This cheap search is the common
    # bail, so it runs before the morespecific list scan (each probe of which is a linear set
    # scan of its own).
    has_empty_set_cover(interference_method, ti, expected) || return false
    return morespecific_cannot_cycle(interference_method, world)
end
```
-/
def newmethodRemovedSilently (O : Oracle) (H : Heap) (meth im : MethodR) (ti sig : Val)
    (expected : List MethodR) (world : Nat) : Except String Bool := do
  if ← methodInInterferences H meth im then
    if !(← expectedIsMinmax O H meth im sig expected) then return false
  if !(← hasEmptySetCover O H im ti expected) then return false
  morespecificCannotCycle H im world

/-- `verify_call_lookup(sig, lim, world, workspace, memoize)`

Julia source: Compiler/src/reinfer.jl:702-725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `_methods_by_ftype` for `sig`, memoized in `workspace` unless the debug log is on (the log
# path mutates the result vector). A cached answer is reused when its validity range covers
# `world`, since the matches are the same in every world of that range.
function verify_call_lookup(@nospecialize(sig), lim::Int, world::UInt, workspace::VerifyMethodWorkspace, memoize::Bool)
    if memoize
        cached = get(workspace.lookups, sig, nothing)
        if cached !== nothing && cached.lim == lim
            if cached.result === nothing ? cached.world == world : (cached.min_world <= world <= cached.max_world)
                return cached.result, cached.min_world, cached.max_world, cached.has_ambig
            end
        end
    end
    minworld = workspace.minworld
    maxworld = workspace.maxworld
    has_ambig = workspace.has_ambig
    minworld[] = 1
    maxworld[] = typemax(UInt)
    has_ambig[] = 0
    result = _methods_by_ftype(sig, nothing, lim, world, #=ambig=#false, minworld, maxworld, has_ambig)
    if memoize
        workspace.lookups[sig] = VerifyMethodLookup(lim, world, result, minworld[], maxworld[], has_ambig[])
    end
    return result, minworld[], maxworld[], has_ambig[]
end
```
-/
def verifyCallLookup (O : Oracle) (sig : Sig) (lim : Int) (world : Nat) (memoize : Bool) :
    VM (Option (List Nat) × Nat × Nat × Int) := do
  if memoize then
    if let some cached := (← getWS).lookups.lookup sig.oid then
      if cached.lim == lim then
        let hit := match cached.result with
          | none => cached.world == world
          | some _ => cached.minWorld ≤ world && world ≤ cached.maxWorld
        if hit then
          emit (.path "lookup:memo-hit")
          return (cached.result, cached.minWorld, cached.maxWorld, cached.hasAmbig)
  let (result, minworld, maxworld, hasAmbig) ← liftE (O.matchingMethods sig.t lim world)
  if memoize then
    let l : Lookup := ⟨lim, world, result, minworld, maxworld, hasAmbig⟩
    modifyWS fun ws => { ws with lookups := (sig.oid, l) :: ws.lookups.filter (·.1 != sig.oid) }
  return (result, minworld, maxworld, hasAmbig)

/-- `expecteds[k]` on the 1-based edge list. -/
def svecRef (es : Array Edge) (k : Nat) : VM Edge :=
  if h : 1 ≤ k ∧ k ≤ es.size then pure es[k - 1] else jlThrow "BoundsError" "svec index"

/-- `verify_call(sig, expecteds, i, n, world, fully_covers, possibly_ambiguous, workspace,
image)`: the world range over which the matches of `sig` are the `n` expected methods at
`expecteds[i:i+n-1]`.

Julia source: Compiler/src/reinfer.jl:727-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Return true if a call to `sig` was the same matches as `expecteds` when run in `world` as it was in `image`.
# `image` is the linkage blob owning the code instance for the caller of this edge
function verify_call(@nospecialize(sig), expecteds::Core.SimpleVector, i::Int, n::Int, world::UInt, fully_covers::Bool, possibly_ambiguous::Bool, workspace::VerifyMethodWorkspace, image::UInt)
    # verify that these edges intersect with the same methods as before
    matches = workspace.matches
    # Collect the expected methods once: indexing the edges list boxes the index (no inline
    # codegen for `_svec_ref`), and the loops below would otherwise do it per interference.
    expected = workspace.expected
    empty!(expected)
    mi = nothing
    expected_deleted = false
    for j = 1:n
        meth = get_method_from_edge(expecteds[i+j-1])
        push!(expected, meth)
        if !method_is_latest_which(meth)
            expected_deleted = true
        end
    end
    if expected_deleted
        if _jl_debug_method_invalidation[] === nothing && world == get_world_counter()
            return UInt(1), UInt(0)
        end
    else # n >= 1
        if n == 1
            # first, fast-path a check if the expected method simply dominates its sig anyways
            # so the result of ml_matches is already simply known
            let t = expecteds[i], meth = expected[1], minworld
                mi = get_mi_from_edge(t) # also recorded for `jl_promote_mi_to_current` below
                # Fast path is legal when fully_covers=true
                if fully_covers && expected_dominates_sig(meth, mi)
                    minworld = meth.primary_world
                    @assert minworld ≤ world "expected method not present in verification world"
                    return minworld, typemax(UInt)
                end
            end
        end
        # If every method that could match `sig` was already present in `image`, the
        # result computed there is still exact.
        let minworld = sig_contributors_world(sig, Core.methodtable, image)
            if minworld != 0
                @assert minworld ≤ world "contributor activated after the verification world"
                # Without an ambiguity the matched methods win in every older world where all
                # of them are present, so date from the newest of them, as a lookup would. A
                # lookup can drop an ambiguous pair of which one was the sole match in an older
                # world, so an ambiguous or empty result is dated from the newest contributor.
                if !possibly_ambiguous && n != 0
                    minworld = UInt(1)
                    for meth in expected
                        minworld = max(minworld, meth.primary_world)
                    end
                    promote_mi_to_current(mi, minworld, world)
                end
                return minworld, typemax(UInt)
            end
        end
        # Try the interference set fast path (used by both n==1, when the O(1) checks above
        # did not resolve it, and n>1): the result is unchanged as long as no interfering
        # method intersects sig outside of what the expected method(s) cover.
        interference_fast_path_success = fully_covers
        if interference_fast_path_success && n == 1
            # Skip to ml_matches for large interference sets (see VERIFY_INTERF_CAP). The set
            # is packed, so isassigned(., cap+1) tests "size > cap" without any typeintersect.
            let interf = expected[1].interferences, cap = VERIFY_INTERF_CAP
                if length(interf) > cap && isassigned(interf, cap + 1)
                    interference_fast_path_success = false
                end
            end
        end
        # If it didn't fail yet, then check that all interference methods are either expected, or not applicable.
        if interference_fast_path_success
            local interference_minworld::UInt = 1
            for meth in expected
                if interference_minworld < meth.primary_world
                    interference_minworld = meth.primary_world
                end
                # manual `eachinterference(meth, world)`: the deleted-entry check
                # below runs before the world cutoff, so a deleted future-world
                # entry conservatively fails the fast path instead of being hidden
                interferences = meth.interferences
                for k = 1:length(interferences)
                    isassigned(interferences, k) || break # no more entries
                    interference_method = interferences[k]::Method
                    if !method_is_latest_which(interference_method)
                        # detected a deleted interference_method, so need the full lookup to compute minworld
                        interference_fast_path_success = false
                        break
                    end
                    world < interference_method.primary_world && break # this and later entries are for a future world
                    if !method_in_expecteds(interference_method, expected)
                        # if interference_method was visible in `image` already, it must have already been considered
                        # and isn't unexpected now, which is a quick test to verify
                        method_in_image_deps(interference_method, image) && continue
                        ti = typeintersect(sig, interference_method.sig)
                        if !(ti === Union{})
                            # An unexpected method intersecting sig can change more than the
                            # match set: even when an expected method fully covers it (so
                            # the sorted result below would compare equal), it can make
                            # `ml_matches` flag an ambiguity -- a mutual pair or a
                            # specificity cycle with a reported match -- which must
                            # invalidate below unless the edge was recorded as
                            # `possibly_ambiguous`. The fast-path here doesn't use that bit:
                            # it checks that this method causes no ambiguity at all, without
                            # knowing whether it already existed (and was already ambiguous)
                            # when the edge was recorded, so a `possibly_ambiguous` edge
                            # whose recorded ambiguity involves an unexpected method always
                            # falls through to the full lookup.
                            if !newmethod_removed_silently(meth, interference_method, ti, sig, expected, world)
                                interference_fast_path_success = false
                                break
                            end
                        end
                    end
                end
                if !interference_fast_path_success
                    break
                end
            end
            if interference_fast_path_success
                # All interference sets are covered by expecteds, can return success
                @assert interference_minworld ≤ world "expected method not present in verification world"
                return interference_minworld, typemax(UInt)
            end
        end
   end
    # next, compare the current result of ml_matches to the old result
    debug = _jl_debug_method_invalidation[] !== nothing
    lim = debug ? Int(typemax(Int32)) : n
    result, minworld, maxworld, has_ambig = verify_call_lookup(sig, lim, world, workspace, !debug)
    if result === nothing
        empty!(matches)
        maxworld = UInt(0)
    else
        # A method added after this edge was recorded can be ambiguous with an expected
        # match without changing this result: the new method is removed when an expected
        # match fully covers their overlap, yet dispatch in the contested region now throws
        # a MethodError that inference and optimizations didn't account for.
        if has_ambig != 0 && !possibly_ambiguous
            maxworld = UInt(0)
        end
        # setdiff!(result, expected)
        if length(result) ≠ n
            maxworld = UInt(0)
        end
        ins = 0
        for k = 1:length(result)
            match = result[k]::Core.MethodMatch
            if !method_in_expecteds(match.method, expected)
                # intersection has a new method or a method was
                # deleted--this is now probably no good, just invalidate
                # everything about it now
                maxworld = UInt(0)
                debug || break
                ins += 1
                result[ins] = match.method
            end
        end
        if maxworld ≠ typemax(UInt) && debug
            resize!(result, ins)
            copy!(matches, result)
        end
    end
    if maxworld == typemax(UInt)
        promote_mi_to_current(mi, minworld, world)
    end
    return minworld, maxworld
end
```
-/
def verifyCall (O : Oracle) (sig : Sig) (expecteds : Array Edge) (i n : Nat) (world : Nat)
    (fullyCovers possiblyAmbiguous : Bool) (image : Nat) : VM (Nat × Nat) := do
  let H ← getHeap
  let mut expected : Array MethodR := #[]
  let mut mi : Option Nat := none
  let mut expectedDeleted := false
  for j in [1:n+1] do
    let meth ← liftE (H.method (← getMethodFromEdge (← svecRef expecteds (i + j - 1))))
    expected := expected.push meth
    if !methodIsLatestWhich meth then expectedDeleted := true
  let expectedL := expected.toList
  let expectedIds := expectedL.map (·.uid)
  if expectedDeleted then
    if !debugLog && world == H.worldCounter then
      emit (.path "call:deleted")
      return (1, 0)
  else
    if n == 1 then
      let t ← svecRef expecteds i
      let meth := expected[0]!
      mi ← getMiFromEdge t
      let miR ← match mi with
        | some m => do let r ← liftE (H.miR m); pure (some r)
        | none => pure none
      if fullyCovers && expectedDominatesSig meth miR then
        let minworld := meth.primaryWorld
        assert' (minworld ≤ world) "expected method not present in verification world"
        emit (.path "call:dominates")
        return (minworld, typemaxUInt)
    let cw ← liftE (sigContributorsWorld O sig.t image)
    if cw != 0 then
      assert' (cw ≤ world) "contributor activated after the verification world"
      let mut minworld := cw
      if !possiblyAmbiguous && n != 0 then
        minworld := 1
        for meth in expectedL do
          minworld := max minworld meth.primaryWorld
        promoteMiToCurrent mi minworld world
      emit (.path "call:contributors")
      return (minworld, typemaxUInt)
    let mut success := fullyCovers
    if success && n == 1 then
      let m0 := expected[0]!
      if m0.interferencesLen > verifyInterfCap && m0.interferences.length ≥ verifyInterfCap + 1 then
        success := false
    if success then
      let mut interferenceMinworld : Nat := 1
      for meth in expectedL do
        if interferenceMinworld < meth.primaryWorld then
          interferenceMinworld := meth.primaryWorld
        for k in meth.interferences do
          let im ← liftE (H.method k)
          if !methodIsLatestWhich im then
            success := false
            break
          if world < im.primaryWorld then break
          if !methodInExpecteds im.uid expectedIds then
            if ← liftE (methodInImageDeps O im image) then
              emit (.path "call:interference-image-dep")
              continue
            let ti ← liftE (O.isect sig.t im.sig)
            if !(ti matches .bottom) then
              let silent ← liftE (newmethodRemovedSilently O H meth im ti sig.t expectedL world)
              emit (.path (if silent then "call:removed-silently" else "call:not-silent"))
              if !silent then
                success := false
                break
        if !success then break
      if success then
        assert' (interferenceMinworld ≤ world) "expected method not present in verification world"
        emit (.path "call:interference-ok")
        return (interferenceMinworld, typemaxUInt)
  -- the full lookup, compared with the expected methods
  let lim : Int := if debugLog then 2147483647 else n
  let (result, minworld, maxworld0, hasAmbig) ← verifyCallLookup O sig lim world (!debugLog)
  let mut maxworld := maxworld0
  match result with
  | none => maxworld := 0
  | some result =>
    if hasAmbig != 0 && !possiblyAmbiguous then maxworld := 0
    if result.length != n then maxworld := 0
    for m in result do
      if !methodInExpecteds m expectedIds then
        maxworld := 0
        break
  if maxworld == typemaxUInt then promoteMiToCurrent mi minworld world
  emit (.path (if result.isNone then "call:lookup-none" else if maxworld == 0 then "call:lookup-reject" else "call:lookup-ok"))
  return (minworld, maxworld)

/-- `verify_invokesig(invokesig, expected, world, matches, image)`. The scratch `matches` is
only read by the debug log and is not modelled.

Julia source: Compiler/src/reinfer.jl:894-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function verify_invokesig(@nospecialize(invokesig), expected::Method, world::UInt, matches::Vector{Any}, image::UInt)
    @assert invokesig isa Type "corrupt edges list"
    local minworld::UInt, maxworld::UInt
    empty!(matches)
    if invokesig === expected.sig && method_is_latest_which(expected)
        # the invoke match is `expected` for `expected->sig`, unless `expected` is replaced
        minworld = expected.primary_world
        @assert minworld ≤ world "expected method not present in verification world"
        maxworld = typemax(UInt)
    else
        mt = get_methodtable(expected)
        if mt === nothing
            minworld = 1
            maxworld = 0
        elseif method_is_latest_which(expected) && sig_contributors_world(invokesig, mt, image) != 0
            # the target still stands and nothing outside `image` could have displaced it
            minworld = expected.primary_world
            @assert minworld ≤ world "expected method not present in verification world"
            maxworld = typemax(UInt)
        else
            matched, valid_worlds = _findsup(invokesig, mt, world)
            minworld, maxworld = valid_worlds.min_world, valid_worlds.max_world
            if matched === nothing
                maxworld = 0
            else
                matched = matched.method
                push!(matches, matched)
                if matched !== expected
                    maxworld = 0
                end
            end
        end
    end
    return minworld, maxworld
end
```
-/
def verifyInvokesig (O : Oracle) (invokesig : Edge) (expected : MethodR) (world : Nat)
    (image : Nat) : VM (Nat × Nat) := do
  let .ty invokesig := invokesig | jlThrow "AssertionError" "corrupt edges list"
  if (← liftE (O.egal invokesig.t expected.sig)) && methodIsLatestWhich expected then
    let minworld := expected.primaryWorld
    assert' (minworld ≤ world) "expected method not present in verification world"
    emit (.path "invoke:egal")
    return (minworld, typemaxUInt)
  if !expected.hasMethodTable then return (1, 0)
  if methodIsLatestWhich expected then
    if (← liftE (sigContributorsWorld O invokesig.t image)) != 0 then
      let minworld := expected.primaryWorld
      assert' (minworld ≤ world) "expected method not present in verification world"
      emit (.path "invoke:contributors")
      return (minworld, typemaxUInt)
  let (matched, minworld, maxworld) ← liftE (O.findsup invokesig.t world)
  emit (.path (if matched == some expected.uid then "invoke:findsup-same" else "invoke:findsup-other"))
  match matched with
  | none => return (minworld, 0)
  | some m => return (minworld, if m != expected.uid then 0 else maxworld)

def wsGet {α : Type} [Inhabited α] (a : Array α) (k : Nat) (what : String) : VM α :=
  if h : 1 ≤ k ∧ k ≤ a.size then pure a[k - 1] else throw s!"model: workspace {what} index {k}"

def setAt {α : Type} (a : Array α) (k : Nat) (x : α) : Array α := a.set! (k - 1) x

/-- One `:init_and_process_callees` step for the state at `currentDepth`.

Julia source: Compiler/src/reinfer.jl:233-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        if work.stage == :init_and_process_callees
            # Initialize state and handle early returns
            world = initial.codeinst.min_world
            let max_valid2 = initial.codeinst.max_world
                if max_valid2 ≠ WORLD_AGE_REVALIDATION_SENTINEL
                    workspace.result_states[current_depth] = VerifyMethodResultState(0, world, max_valid2)
                    workspace.work_states[current_depth] = VerifyMethodWorkState(work.depth, work.cause, work.recursive_index, :return_to_parent)
                    continue
                end
            end

            if needs_instrumentation(initial.codeinst, initial.mi, initial.def, validation_world)
                workspace.result_states[current_depth] = VerifyMethodResultState(0, world, UInt(0))
                workspace.work_states[current_depth] = VerifyMethodWorkState(work.depth, work.cause, work.recursive_index, :return_to_parent)
                continue
            end

            if haskey(workspace.visiting, initial.codeinst)
                workspace.result_states[current_depth] = VerifyMethodResultState(workspace.visiting[initial.codeinst], UInt(1), validation_world)
                workspace.work_states[current_depth] = VerifyMethodWorkState(work.depth, work.cause, work.recursive_index, :return_to_parent)
                continue
            end

            push!(workspace.stack, initial.codeinst)
            depth = length(workspace.stack)
            workspace.visiting[initial.codeinst] = depth

            # unable to backdate before require_world, since Bindings are not able to track that information
            minworld, maxworld = get_require_world(), validation_world

            # Check for invalidation of GlobalRef edges
            if (initial.def.did_scan_source & 0x1) == 0x0
                backedges_only = unsafe_load(cglobal(:jl_first_image_replacement_world, UInt)) == typemax(UInt)
                scan_new_method!(initial.def, validation_world, backedges_only)
            end
            if (initial.def.did_scan_source & 0x4) != 0x0
                maxworld = 0
                invalidations = _jl_debug_method_invalidation[]
                if invalidations !== nothing
                    push!(invalidations, initial.def, "method_globalref", initial.codeinst, nothing)
                end
            end

            # Process all non-CodeInstance edges
            if !isempty(initial.callees) && maxworld != get_require_world()
                matches = workspace.matches
                empty!(matches)
                j = 1
                while j <= length(initial.callees)
                    local min_valid2::UInt, max_valid2::UInt
                    edge = initial.callees[j]
                    @assert !(edge isa Method) "unexpected Method edge indicates corrupt edges list creation"
                    possibly_ambiguous = edge isa Core.PossiblyAmbiguous
                    if possibly_ambiguous
                        j += 1
                        edge = initial.callees[j]
                    end

                    if edge isa CodeInstance
                        # Convert CodeInstance to MethodInstance for validation (like original)
                        edge = get_ci_mi(edge)
                    end

                    if edge isa MethodInstance
                        sig = edge.specTypes
                        min_valid2, max_valid2 = verify_call(sig, initial.callees, j, 1, world, true, possibly_ambiguous, workspace, initial.image)
                        j += 1
                    elseif edge isa Int
                        sig = initial.callees[j+1]
                        nmatches = abs(edge)
                        fully_covers = edge > 0
                        min_valid2, max_valid2 = verify_call(sig, initial.callees, j+2, nmatches, world, fully_covers, possibly_ambiguous, workspace, initial.image)
                        j += 2 + nmatches
                        edge = sig
                    elseif edge isa Core.Binding
                        j += 1
                        # Check that what of and how this code accessed the leaf partition is still valid.
                        wr = binding_access_range_at(edge, validation_world)
                        if min_world(wr) > get_require_world()
                            # Nothing can be backdated before the require world, so an access
                            # whose range does not reach it cannot be shown valid at all.
                            min_valid2 = 1
                            max_valid2 = 0
                        else
                            min_valid2 = min_world(wr)
                            max_valid2 = max_world(wr)
                        end
                    else
                        callee = initial.callees[j+1]
                        if callee isa Core.MethodTable
                            j += 2
                            continue
                        end
                        if callee isa CodeInstance
                            callee = get_ci_mi(callee)
                        end
                        if callee isa MethodInstance
                            meth = callee.def::Method
                        else
                            meth = callee::Method
                        end
                        min_valid2, max_valid2 = verify_invokesig(edge, meth, world, matches, initial.image)
                        j += 2
                    end

                    if minworld < min_valid2
                        minworld = min_valid2
                    end
                    if maxworld > max_valid2
                        maxworld = max_valid2
                    end
                    invalidations = _jl_debug_method_invalidation[]
                    if max_valid2 ≠ typemax(UInt) && invalidations !== nothing
                        push!(invalidations, edge, "insert_backedges_callee", initial.codeinst, copy(matches))
                    end
                    if max_valid2 == 0 && invalidations === nothing
                        break
                    end
                end
            end

            # Store computed minworld/maxworld in result state and transition to recursive phase
            workspace.result_states[current_depth] = VerifyMethodResultState(depth, minworld, maxworld)
            workspace.work_states[current_depth] = VerifyMethodWorkState(depth, work.cause, 1, :recursive_phase)
```
-/
def initAndProcessCallees (O : Oracle) (validationWorld currentDepth : Nat) : VM Unit := do
  let ws ← getWS
  let initial ← wsGet ws.initialStates currentDepth "initial"
  let work ← wsGet ws.workStates currentDepth "work"
  let H ← getHeap
  let c ← liftE (H.ciR initial.codeinst)
  let world := c.minWorld
  let setResult (r : ResultState) (w : WorkState) : VM Unit := modifyWS fun ws => { ws with
    resultStates := setAt ws.resultStates currentDepth r
    workStates := setAt ws.workStates currentDepth w }
  let toParent : WorkState := ⟨work.depth, work.cause, work.recursiveIndex, .returnToParent⟩
  if c.maxWorld != worldAgeRevalidationSentinel then
    emit (.path "method:already-validated")
    setResult ⟨0, world, c.maxWorld⟩ toParent
    return
  if ← needsInstrumentation initial.codeinst then
    setResult ⟨0, world, 0⟩ toParent
    return
  if let some d := ws.visiting.lookup initial.codeinst then
    emit (.path "method:cycle-back-edge")
    setResult ⟨d, 1, validationWorld⟩ toParent
    return
  modifyWS fun ws => { ws with stack := ws.stack.push initial.codeinst }
  let depth := (← getWS).stack.size
  modifyWS fun ws => { ws with visiting := (initial.codeinst, depth) :: ws.visiting }
  let requireWorld := H.requireWorld
  let mut minworld := requireWorld
  let mut maxworld := validationWorld
  let defR ← liftE (H.method initial.def_)
  if defR.didScanSource &&& 0x1 == 0 then
    let backedgesOnly := H.firstImageReplacementWorld == typemaxUInt
    scanNewMethod O initial.def_ validationWorld backedgesOnly
  let defR ← liftE ((← getHeap).method initial.def_)
  if defR.didScanSource &&& 0x4 != 0 then
    emit (.path "method:globalref-flag")
    maxworld := 0
  let callees := initial.callees
  if !callees.isEmpty && maxworld != requireWorld then
    let mut j := 1
    -- each pass consumes at least one item, so `callees.size` passes suffice
    for _ in [0:callees.size] do
      if !(j ≤ callees.size) then break
      let mut edge ← svecRef callees j
      if let .method _ := edge then
        jlThrow "AssertionError" "unexpected Method edge indicates corrupt edges list creation"
      let possiblyAmbiguous := edge matches .possiblyAmbiguous
      if possiblyAmbiguous then
        j := j + 1
        edge ← svecRef callees j
      if let .ci e := edge then
        edge := .mi (← liftE ((← getHeap).ciR e)).mi
      let mut minValid2 := 0
      let mut maxValid2 := 0
      match edge with
      | .mi m =>
        let sig := (← liftE ((← getHeap).miR m)).specTypes
        let r ← verifyCall O sig callees j 1 world true possiblyAmbiguous initial.image
        minValid2 := r.1
        maxValid2 := r.2
        j := j + 1
      | .int k =>
        let .ty sig ← svecRef callees (j + 1) | throw "unmodelled: non-type call signature in edges"
        let nmatches := k.natAbs
        let fullyCovers := k > 0
        let r ← verifyCall O sig callees (j + 2) nmatches world fullyCovers possiblyAmbiguous
          initial.image
        minValid2 := r.1
        maxValid2 := r.2
        j := j + 2 + nmatches
      | .binding b =>
        j := j + 1
        let wr ← bindingAccessRangeAt O b validationWorld
        if wr.minWorld > (← getHeap).requireWorld then
          emit (.path "method:binding-reject")
          minValid2 := 1
          maxValid2 := 0
        else
          minValid2 := wr.minWorld
          maxValid2 := wr.maxWorld
      | _ =>
        let callee ← svecRef callees (j + 1)
        if callee matches .methodTable then
          j := j + 2
          continue
        let H ← getHeap
        let meth ← match callee with
          | .ci c => do let c ← liftE (H.ciR c); let r ← liftE (H.miR c.mi); pure r.def_
          | .mi m => do let r ← liftE (H.miR m); pure r.def_
          | .method m => pure m
          | _ => jlThrow "TypeError" "typeassert Method"
        let methR ← liftE (H.method meth)
        let r ← verifyInvokesig O edge methR world initial.image
        minValid2 := r.1
        maxValid2 := r.2
        j := j + 2
      if minworld < minValid2 then minworld := minValid2
      if maxworld > maxValid2 then maxworld := maxValid2
      if maxValid2 == 0 && !debugLog then break
    if j ≤ callees.size && maxworld != 0 then
      throw "model: edge walk did not finish"
  setResult ⟨depth, minworld, maxworld⟩ ⟨depth, work.cause, 1, .recursivePhase⟩

/-- One `:recursive_phase` step.

Julia source: Compiler/src/reinfer.jl:358-380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        elseif work.stage == :recursive_phase
            # Find next CodeInstance edge that needs processing
            recursive_index = work.recursive_index
            found_child = false
            while recursive_index ≤ length(initial.callees)
                edge = initial.callees[recursive_index]
                recursive_index += 1

                if edge isa CodeInstance
                    # Create child state and add to stack
                    workspace.work_states[current_depth] = VerifyMethodWorkState(work.depth, work.cause, recursive_index, :recursive_phase)
                    push!(workspace.initial_states, VerifyMethodInitialState(edge))
                    push!(workspace.work_states, VerifyMethodWorkState(edge))
                    push!(workspace.result_states, VerifyMethodResultState())
                    current_depth += 1
                    found_child = true
                    break
                end
            end

            if !found_child
                workspace.work_states[current_depth] = VerifyMethodWorkState(work.depth, work.cause, recursive_index, :cleanup)
            end
```
-/
def recursivePhase (currentDepth : Nat) : VM Nat := do
  let ws ← getWS
  let initial ← wsGet ws.initialStates currentDepth "initial"
  let work ← wsGet ws.workStates currentDepth "work"
  let mut recursiveIndex := work.recursiveIndex
  -- each pass advances `recursiveIndex`, so `callees.size` passes reach the end; a bounded `for`
  -- rather than `while` keeps the step reducible in proofs
  for _ in [0:initial.callees.size] do
    if !(recursiveIndex ≤ initial.callees.size) then break
    let edge ← svecRef initial.callees recursiveIndex
    recursiveIndex := recursiveIndex + 1
    if let .ci e := edge then
      let st ← mkInitialState e
      let w : WorkState := ⟨work.depth, work.cause, recursiveIndex, .recursivePhase⟩
      modifyWS fun ws => { ws with
        workStates := (setAt ws.workStates currentDepth w).push (mkWorkState e)
        initialStates := ws.initialStates.push st
        resultStates := ws.resultStates.push mkResultState }
      return currentDepth + 1
  let w : WorkState := ⟨work.depth, work.cause, recursiveIndex, .cleanup⟩
  modifyWS fun ws => { ws with workStates := setAt ws.workStates currentDepth w }
  return currentDepth

/-- One `:cleanup` step: the root of a strongly connected component (or a failed node) writes
its result into every code instance above it on the Tarjan stack.

Julia source: Compiler/src/reinfer.jl:382-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        elseif work.stage == :cleanup
            # If we are the top of the current cycle, now mark all other parts of
            # our cycle with what we found.
            # Or if we found a failed edge, also mark all of the other parts of the
            # cycle as also having a failed edge.
            result = workspace.result_states[current_depth]
            if result.result_maxworld == 0 || result.child_cycle == work.depth
                while length(workspace.stack) ≥ work.depth
                    child = pop!(workspace.stack)
                    if result.result_maxworld ≠ 0
                        @atomic :monotonic child.min_world = result.result_minworld
                        # Finally, if this CI is still valid in some world age and marked as valid in the native cache, poke it in that mi's cache now
                        if child.flags & CI_FLAGS_NATIVE_CACHE_VALID == CI_FLAGS_NATIVE_CACHE_VALID
                            @ccall jl_mi_cache_insert(get_ci_mi(child)::Any, child::Any)::Cvoid
                        end
                    end
                    @atomic :monotonic child.max_world = result.result_maxworld
                    if result.result_maxworld == validation_world && validation_world == get_world_counter() && isdefined(child, :edges)
                        store_backedges(child, child.edges, workspace.backedge_scratch)
                    end
                    @assert workspace.visiting[child] == length(workspace.stack) + 1 "internal error maintaining workspace"
                    delete!(workspace.visiting, child)
                    invalidations = _jl_debug_method_invalidation[]
                    if invalidations !== nothing && result.result_maxworld < validation_world
                        push!(invalidations, child, "verify_methods", work.cause)
                    end
                end

                workspace.result_states[current_depth] = VerifyMethodResultState(0, result.result_minworld, result.result_maxworld)
            end

            workspace.work_states[current_depth] = VerifyMethodWorkState(work.depth, work.cause, work.recursive_index, :return_to_parent)
```
-/
def cleanup (validationWorld currentDepth : Nat) : VM Unit := do
  let ws ← getWS
  let work ← wsGet ws.workStates currentDepth "work"
  let result ← wsGet ws.resultStates currentDepth "result"
  if result.resultMaxworld == 0 || result.childCycle == work.depth then
    let before := (← getWS).stack.size
    if before > work.depth then
      emit (.path (if result.resultMaxworld == 0 then "method:group-rejected" else "method:group-accepted"))
    for _ in [0:(← getWS).stack.size] do
      let ws ← getWS
      if !(ws.stack.size ≥ work.depth) then break
      let child := ws.stack.back!
      modifyWS fun ws => { ws with stack := ws.stack.pop }
      let c ← liftE ((← getHeap).ciR child)
      let mut c := c
      if result.resultMaxworld != 0 then
        c := { c with minWorld := result.resultMinworld }
        if c.flags &&& ciFlagsNativeCacheValid == ciFlagsNativeCacheValid then
          emit (.miCacheInsert c.mi child)
      c := { c with maxWorld := result.resultMaxworld }
      modifyHeap (·.setCI c)
      let H ← getHeap
      if result.resultMaxworld == validationWorld && validationWorld == H.worldCounter &&
          c.edges.isSome then
        emit (.storeBackedges child)
        -- the binding items of the edge list reach `jl_maybe_add_binding_backedge`
        let def_ := (← liftE ((← getHeap).miR c.mi)).def_
        for e in c.callees do
          if let .binding b := e then maybeAddBindingBackedge b def_
      let ws ← getWS
      assert' (ws.visiting.lookup child == some (ws.stack.size + 1)) "internal error maintaining workspace"
      modifyWS fun ws => { ws with visiting := ws.visiting.filter (·.1 != child) }
    let r : ResultState := ⟨0, result.resultMinworld, result.resultMaxworld⟩
    modifyWS fun ws => { ws with resultStates := setAt ws.resultStates currentDepth r }
  let w : WorkState := ⟨work.depth, work.cause, work.recursiveIndex, .returnToParent⟩
  modifyWS fun ws => { ws with workStates := setAt ws.workStates currentDepth w }

/-- One `:return_to_parent` step: pops the state at `currentDepth` and merges its result into
the parent. Returns the new depth, and the root's result when the walk is done.

Julia source: Compiler/src/reinfer.jl:415-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        elseif work.stage == :return_to_parent
            # Pass results to parent and process them
            pop!(workspace.initial_states)
            pop!(workspace.work_states)
            result = pop!(workspace.result_states)
            current_depth -= 1
            if current_depth == 0 # Return results from the root call
                return (result.child_cycle, result.result_minworld, result.result_maxworld)
            end
            # Propagate results to parent
            parent_work = workspace.work_states[current_depth]
            parent_result = workspace.result_states[current_depth]
            callee = initial.codeinst
            child_cycle, min_valid2, max_valid2 = result.child_cycle, result.result_minworld, result.result_maxworld
            parent_cycle = parent_result.child_cycle
            parent_minworld = parent_result.result_minworld
            parent_maxworld = parent_result.result_maxworld
            parent_cause = parent_work.cause
            parent_stage = parent_work.stage
            if parent_minworld < min_valid2
                parent_minworld = min_valid2
            end
            if parent_minworld > max_valid2
                max_valid2 = 0
            end
            if parent_maxworld > max_valid2
                parent_cause = callee
                parent_maxworld = max_valid2
            end
            if max_valid2 == 0
                # found what we were looking for, so terminate early
                # The parent should break out of its loop in :recursive_phase
                parent_stage = :cleanup
            elseif child_cycle ≠ 0 && child_cycle < parent_cycle
                # record the cycle will resolve at depth "cycle"
                parent_cycle = child_cycle
            end
            workspace.work_states[current_depth] = VerifyMethodWorkState(parent_work.depth, parent_cause, parent_work.recursive_index, parent_stage)
            workspace.result_states[current_depth] = VerifyMethodResultState(parent_cycle, parent_minworld, parent_maxworld)
        end
    end
```
-/
def returnToParent (currentDepth : Nat) : VM (Nat × Option (Nat × Nat × Nat)) := do
  let ws ← getWS
  let initial ← wsGet ws.initialStates currentDepth "initial"
  let result := ws.resultStates.back!
  modifyWS fun ws => { ws with
    initialStates := ws.initialStates.pop
    workStates := ws.workStates.pop
    resultStates := ws.resultStates.pop }
  let currentDepth := currentDepth - 1
  if currentDepth == 0 then
    return (0, some (result.childCycle, result.resultMinworld, result.resultMaxworld))
  let ws ← getWS
  let parentWork ← wsGet ws.workStates currentDepth "work"
  let parentResult ← wsGet ws.resultStates currentDepth "result"
  let callee := initial.codeinst
  let childCycle := result.childCycle
  let minValid2 := result.resultMinworld
  let mut maxValid2 := result.resultMaxworld
  let mut parentCycle := parentResult.childCycle
  let mut parentMinworld := parentResult.resultMinworld
  let mut parentMaxworld := parentResult.resultMaxworld
  let mut parentCause := parentWork.cause
  let mut parentStage := parentWork.stage
  if parentMinworld < minValid2 then parentMinworld := minValid2
  if parentMinworld > maxValid2 then maxValid2 := 0
  if parentMaxworld > maxValid2 then
    parentCause := callee
    parentMaxworld := maxValid2
  if maxValid2 == 0 then
    parentStage := .cleanup
  else if childCycle != 0 && childCycle < parentCycle then
    parentCycle := childCycle
  let w : WorkState := ⟨parentWork.depth, parentCause, parentWork.recursiveIndex, parentStage⟩
  let r : ResultState := ⟨parentCycle, parentMinworld, parentMaxworld⟩
  modifyWS fun ws => { ws with
    workStates := setAt ws.workStates currentDepth w
    resultStates := setAt ws.resultStates currentDepth r }
  return (currentDepth, none)

/-- `verify_method(codeinst, validation_world, workspace)`: returns `(child_cycle, minworld,
maxworld)`. The `while true` loop runs at most `fuel` steps; running out is a model failure,
never a Julia outcome.

Julia source: Compiler/src/reinfer.jl:217-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Test all edges relevant to a method:
# - Visit the entire call graph, starting from `codeinst` to determine if that method is valid
# - Implements Tarjan's SCC (strongly connected components) algorithm, simplified to remove the count variable
#   and slightly modified with an early termination option once the computation reaches its minimum
function verify_method(codeinst::CodeInstance, validation_world::UInt, workspace::VerifyMethodWorkspace)
    # Initialize root state
    push!(workspace.initial_states, VerifyMethodInitialState(codeinst))
    push!(workspace.work_states, VerifyMethodWorkState(codeinst))
    push!(workspace.result_states, VerifyMethodResultState())

    current_depth = 1 # == length(workspace._states) == end
    while true
        # Get current state indices
        initial = workspace.initial_states[current_depth]
        work = workspace.work_states[current_depth]

```
-/
def verifyMethod (O : Oracle) (fuel : Nat) (codeinst validationWorld : Nat) :
    VM (Nat × Nat × Nat) := do
  let st ← mkInitialState codeinst
  modifyWS fun ws => { ws with
    initialStates := ws.initialStates.push st
    workStates := ws.workStates.push (mkWorkState codeinst)
    resultStates := ws.resultStates.push mkResultState }
  let mut currentDepth := 1
  for _ in [0:fuel] do
    let work ← wsGet (← getWS).workStates currentDepth "work"
    match work.stage with
    | .initAndProcessCallees => initAndProcessCallees O validationWorld currentDepth
    | .recursivePhase => currentDepth ← recursivePhase currentDepth
    | .cleanup => cleanup validationWorld currentDepth
    | .returnToParent =>
      let (d, r) ← returnToParent currentDepth
      if let some r := r then return r
      currentDepth := d
  throw "model: out of fuel in verify_method"

/-- `verify_method_graph(codeinst, validation_world, workspace)`

Julia source: Compiler/src/reinfer.jl:149-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function verify_method_graph(codeinst::CodeInstance, validation_world::UInt, workspace::VerifyMethodWorkspace)
    @assert isempty(workspace.stack) "workspace corrupted"
    @assert isempty(workspace.visiting) "workspace corrupted"
    @assert isempty(workspace.initial_states) "workspace corrupted"
    @assert isempty(workspace.work_states) "workspace corrupted"
    @assert isempty(workspace.result_states) "workspace corrupted"
    child_cycle, minworld, maxworld = verify_method(codeinst, validation_world, workspace)
    @assert child_cycle == 0
    @assert isempty(workspace.stack) "workspace corrupted"
    @assert isempty(workspace.visiting) "workspace corrupted"
    @assert isempty(workspace.initial_states) "workspace corrupted"
    @assert isempty(workspace.work_states) "workspace corrupted"
    @assert isempty(workspace.result_states) "workspace corrupted"
    nothing
end
```
-/
def verifyMethodGraph (O : Oracle) (fuel : Nat) (codeinst validationWorld : Nat) : VM Unit := do
  let empty (ws : Workspace) : Bool := ws.stack.isEmpty && ws.visiting.isEmpty &&
    ws.initialStates.isEmpty && ws.workStates.isEmpty && ws.resultStates.isEmpty
  assert' (empty (← getWS)) "workspace corrupted"
  let (childCycle, _, _) ← verifyMethod O fuel codeinst validationWorld
  assert' (childCycle == 0) "child_cycle == 0"
  assert' (empty (← getWS)) "workspace corrupted"

/-- `jl_promote_ci_to_current(ci, validated_world)` (`jl_promote_cis_to_current`).

When the world counter is still `validated_world`, every code instance reached from `ci`
through code-instance edges whose `max_world` is `validated_world` gets `max_world =
typemax(UInt)` (`src/gf.c:2247-2276`).
-/
def jlPromoteCiToCurrent (fuel : Nat) (ci validatedWorld : Nat) : VM Unit := do
  let H ← getHeap
  if H.worldCounter > validatedWorld then return
  if H.worldCounter != validatedWorld then return
  let mut workqueue : Array Nat := #[ci]
  for _ in [0:fuel] do
    if workqueue.isEmpty then return
    let current := workqueue.back!
    workqueue := workqueue.pop
    let c ← liftE ((← getHeap).ciR current)
    if c.maxWorld != validatedWorld then continue
    modifyHeap (·.setCI { c with maxWorld := typemaxUInt })
    for e in c.callees do
      if let .ci d := e then workqueue := workqueue.push d
  if !workqueue.isEmpty then throw "model: out of fuel in jl_promote_cis_to_current"

/-- `scan_new_code!(internal_methods, workspace)`

Julia source: Compiler/src/reinfer.jl:128-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scan_new_code!(internal_methods::Vector{Any}, workspace::VerifyMethodWorkspace)
    lookup_world = get_world_counter()
    for i = 1:length(internal_methods)
        codeinst = internal_methods[i]
        codeinst isa CodeInstance || continue
        # codeinst.owner === nothing || continue
        validation_world = get_world_counter()
        if validation_world != lookup_world
            # a method was added or deleted since the memoized lookups were made (an open-ended
            # `max_world` in them is no longer trustworthy)
            empty!(workspace.lookups)
            lookup_world = validation_world
        end
        verify_method_graph(codeinst, validation_world, workspace)
        # After validation, under the world_counter_lock, set max_world to typemax(UInt) for all dependencies
        # (recursively). From that point onward the ordinary backedge mechanism is responsible for maintaining
        # validity.
        @ccall jl_promote_ci_to_current(codeinst::Any, validation_world::UInt)::Cvoid
    end
end
```
-/
def scanNewCode (O : Oracle) (fuel : Nat) (internal : List InternalItem) : VM Unit := do
  let mut lookupWorld := (← getHeap).worldCounter
  for item in internal do
    let .ci codeinst := item | continue
    let validationWorld := (← getHeap).worldCounter
    if validationWorld != lookupWorld then
      modifyWS fun ws => { ws with lookups := [] }
      lookupWorld := validationWorld
    verifyMethodGraph O fuel codeinst validationWorld
    jlPromoteCiToCurrent fuel codeinst validationWorld

/-- `insert_backedges(internal_methods)`

Julia source: Compiler/src/reinfer.jl:117-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Restore backedges to external targets
# `internal_methods` = [caller1, ...], the list of worklist-owned code instances internally
function insert_backedges(internal_methods::Vector{Any})
    # determine which CodeInstance objects are still valid in our image
    # to enable any applicable new codes
    backedges_only = unsafe_load(cglobal(:jl_first_image_replacement_world, UInt)) == typemax(UInt)
    scan_new_methods!(internal_methods, get_world_counter(), backedges_only)
    scan_new_code!(internal_methods, VerifyMethodWorkspace())
    nothing
end
```
-/
def insertBackedges (O : Oracle) (fuel : Nat) (internal : List InternalItem) : VM Unit := do
  let H ← getHeap
  let backedgesOnly := H.firstImageReplacementWorld == typemaxUInt
  scanNewMethods O internal H.worldCounter backedgesOnly
  modifyWS fun _ => {}
  scanNewCode O fuel internal

end JuliaLean.Compiler.Reinfer
