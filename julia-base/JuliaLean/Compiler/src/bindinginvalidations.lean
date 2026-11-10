import JuliaLean.Compiler.src.reinfer.Bindings

/-!
Model of `Compiler/src/bindinginvalidations.jl`. The two binding queries of
`Compiler/src/reinfer.jl` that its source scan calls are in `reinfer/Bindings.lean`.

A method's lowered source is represented by what these functions read from it: for each
statement, whether it is a `GlobalRef` and the values its `userefs` yield (`MethodR.source`,
`Stmt`). A `GlobalRef` is named by its binding: `convert(Core.Binding, gr)` is one binding per
`(gr.mod, gr.name)`, and `isgr` compares exactly that pair, so comparing bindings is comparing
`GlobalRef`s the way `should_invalidate_code_for_globalref` does.
-/

namespace JuliaLean.Compiler.Reinfer

open JuliaLean.C JuliaLean.Compiler.CICache

variable {W : Type}

/-- `foreachgr(visit, src)`: the `GlobalRef`s visited, in order.

Julia source: Compiler/src/bindinginvalidations.jl:10-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function foreachgr(visit, src::CodeInfo)
    stmts = src.code
    for i = 1:length(stmts)
        stmt = stmts[i]
        isa(stmt, GlobalRef) && visit(stmt)
        for ur in userefs(stmt)
            arg = ur[]
            isa(arg, GlobalRef) && visit(arg)
        end
    end
end
```
The two loops are mirrored as recursion over the statements and over their `userefs` values.
-/
def foreachgr {m : Type → Type} [Monad m] (visit : Nat → m Unit) : List Stmt → m Unit
  | [] => pure ()
  | stmt :: rest => do
    if let some g := stmt.gr then visit g
    foreachUse visit stmt.uses
    foreachgr visit rest
where
  foreachUse (visit : Nat → m Unit) : List (Option Nat) → m Unit
    | [] => pure ()
    | arg :: args => do
      if let some g := arg then visit g
      foreachUse visit args

/-- `anygr(visit, src)`

Julia source: Compiler/src/bindinginvalidations.jl:22-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function anygr(visit, src::CodeInfo)
    stmts = src.code
    for i = 1:length(stmts)
        stmt = stmts[i]
        if isa(stmt, GlobalRef)
            visit(stmt) && return true
            continue
        end
        for ur in userefs(stmt)
            arg = ur[]
            isa(arg, GlobalRef) && visit(arg) && return true
        end
    end
    return false
end
```
A `GlobalRef` statement skips its `userefs` (`continue`); the loops stop at the first `true`.
-/
def anygr (visit : Nat → Bool) : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
    match stmt.gr with
    | some g => if visit g then true else anygr visit rest
    | none => if anyUse stmt.uses then true else anygr visit rest
where
  anyUse : List (Option Nat) → Bool
    | [] => false
    | arg :: args => match arg with
      | some g => if visit g then true else anyUse args
      | none => anyUse args

/-- `should_invalidate_code_for_globalref(gr, src)`

Julia source: Compiler/src/bindinginvalidations.jl:38-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function should_invalidate_code_for_globalref(gr::GlobalRef, src::CodeInfo)
    isgr(g::GlobalRef) = gr.mod == g.mod && gr.name === g.name
    isgr(g) = false
    return anygr(isgr, src)
end
```
-/
def shouldInvalidateCodeForGlobalref (gr : Nat) (src : List Stmt) : Bool :=
  anygr (fun g => g == gr) src

/-- `scan_edge_list(ci, binding)`

Julia source: Compiler/src/bindinginvalidations.jl:44-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scan_edge_list(ci::Core.CodeInstance, binding::Core.Binding)
    isdefined(ci, :edges) || return false
    edges = ci.edges
    i = 1
    while i <= length(edges)
        if isassigned(edges, i) && edges[i] === binding
            return true
        end
        i += 1
    end
    return false
end
```
-/
def scanEdgeList (ci : CIR) (binding : Nat) : Bool :=
  match ci.edges with
  | none => false
  | some es => es.any fun | .binding b => b == binding | _ => false

/-- `jl_invalidate_code_instance(ci, max_world)` (`src/gf.c:2494-2527`): when `ci.max_world`
is `typemax(UInt)`, it becomes `max_world` and the backedges of `ci`'s method instance are
invalidated too (recorded as the event, not followed); otherwise nothing changes. -/
def jlInvalidateCodeInstance (ci : Nat) (maxWorld : Nat) : RM W Unit := do
  let c ← liftE ((← getHeap).ciR ci)
  if c.maxWorld == typemaxUInt then
    modifyHeap (·.setCI { c with maxWorld := maxWorld })
  emit (.invalidateCI ci maxWorld)

/-- `invalidate_method_for_globalref!(gr, method, invalidated_bpart, new_max_world)`

Julia source: Compiler/src/bindinginvalidations.jl:57-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invalidate_method_for_globalref!(gr::GlobalRef, method::Method, invalidated_bpart::Core.BindingPartition, new_max_world::UInt)
    invalidate_all = false
    binding = convert(Core.Binding, gr)
    if isdefined(method, :source) && isa(method.source, MaybeCompressed)
        src = _uncompressed_ir(method)
        invalidate_all = should_invalidate_code_for_globalref(gr, src)
    end
    if invalidate_all && !generating_output()
        @atomic method.did_scan_source |= 0x4
    end
    invalidated_any = false
    for mi in specializations(method)
        isdefined(mi, :cache) || continue
        ci = mi.cache
        invalidated = false
        while true
            if ci.max_world > new_max_world && (invalidate_all || scan_edge_list(ci, binding))
                ccall(:jl_invalidate_code_instance, Cvoid, (Any, UInt), ci, new_max_world)
                invalidated = true
            end
            isdefined(ci, :next) || break
            ci = ci.next
        end
        invalidated && ccall(:jl_maybe_log_binding_invalidation, Cvoid, (Any,), mi)
        invalidated_any |= invalidated
    end
    return invalidated_any
end
```
`gr` is named by its binding. -/
def invalidateMethodForGlobalref (gr : Nat) (method : Nat) (newMaxWorld : Nat) : RM W Bool := do
  let H ← getHeap
  let m ← liftE (H.method method)
  let binding := gr
  let mut invalidateAll := false
  if let some src := m.source then
    invalidateAll := shouldInvalidateCodeForGlobalref gr src
  if invalidateAll && !H.generatingOutput then
    modifyHeap (·.setMethod { m with didScanSource := m.didScanSource ||| 0x4 })
  let mut invalidatedAny := false
  for miId in m.specializations do
    let mi ← liftE ((← getHeap).miR miId)
    if mi.cache.isEmpty then continue
    let mut invalidated := false
    for ciId in mi.cache do
      let ci ← liftE ((← getHeap).ciR ciId)
      if ci.maxWorld > newMaxWorld && (invalidateAll || scanEdgeList ci binding) then
        jlInvalidateCodeInstance ciId newMaxWorld
        invalidated := true
    if invalidated then emit .logBindingInvalidation
    invalidatedAny := invalidatedAny || invalidated
  return invalidatedAny

/-- `export_affecting_partition_flags(bpart)`

Julia source: Compiler/src/bindinginvalidations.jl:86-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
export_affecting_partition_flags(bpart::Core.BindingPartition) =
    ((bpart.kind & PARTITION_MASK_KIND) == PARTITION_KIND_GUARD,
     (bpart.kind & PARTITION_FLAG_EXPORTED) != 0,
     (bpart.kind & PARTITION_FLAG_DEPRECATED) != 0)
```
-/
def exportAffectingPartitionFlags (p : Partition) : Bool × Bool × Bool :=
  ((p.kind &&& partitionMaskKind) == partitionKindGuard,
   (p.kind &&& partitionFlagExported) != 0,
   (p.kind &&& partitionFlagDeprecated) != 0)

/-- An entry of `b.backedges` (`jl_binding_backedges_getindex`). -/
inductive BindingBackedge where
  | ci (id : Nat)
  | binding (id : Nat)
  | method (uid : Nat)
  deriving Inhabited, BEq, Repr

/-- The runtime queries `invalidate_code_for_globalref!` makes besides the heap: the leaf
access keys (`walk_binding_partition` and `binding_access_key`,
`Compiler/src/abstractinterpretation.jl:4127-4234`), the binding and module backedge lists,
and implicit re-resolution. -/
structure BindingInvalidationOracle where
  /-- `binding_access_key(ileaf) !== binding_access_key(nleaf)` for
  `walk_binding_partition(b, invalidated_bpart, new_max_world, false)` and
  `walk_binding_partition(b, new_bpart, new_max_world+1, false)`. -/
  accessKeyChanged : (b : Nat) → (invalidated new : Partition) → (newMaxWorld : Nat) → Except String Bool
  /-- `jl_module_scanned_methods_getindex(gr.mod, i)` for `i = 1:nmethods`, for the module of
  binding `b`. -/
  moduleScannedMethods : Nat → Except String (List Nat)
  /-- `jl_binding_backedges_getindex(b, i)` for `i = 1:nbackedges`. -/
  bindingBackedges : Nat → Except String (List BindingBackedge)
  /-- For each module of `jl_get_module_usings_backedges(gr.mod)` (`none` is `nothing`), the
  result of `jl_get_module_binding_or_nothing(user, gr.name)`. -/
  usingsBackedges : Nat → Except String (Option (List (Option Nat)))
  /-- `jl_maybe_reresolve_implicit(user_binding, new_max_world)`. Its effect on the user
  binding's partitions is part of the answer: the new partition list. -/
  reresolveImplicit : (b : Nat) → (newMaxWorld : Nat) → Except String (Partition × List Partition)

/-- `invalidate_code_for_globalref!(b, invalidated_bpart, new_bpart, new_max_world)`

Julia source: Compiler/src/bindinginvalidations.jl:91-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function invalidate_code_for_globalref!(b::Core.Binding, invalidated_bpart::Core.BindingPartition, new_bpart::Core.BindingPartition, new_max_world::UInt)
    gr = b.globalref

    (_, ileaf) = walk_binding_partition(b, invalidated_bpart, new_max_world, false)
    (_, nleaf) = walk_binding_partition(b, new_bpart, new_max_world+1, false)

    # `binding_access_key` captures everything inference/codegen accesses about a binding partition.
    # If this information does not change, we do not need to invalidate any code that inference created
    # because we know that the result will not change.
    need_to_invalidate_code = binding_access_key(ileaf) !== binding_access_key(nleaf)

    need_to_invalidate_export = export_affecting_partition_flags(invalidated_bpart) !==
                                export_affecting_partition_flags(new_bpart)

    invalidated_any = false
    queued_bindings = Tuple{Core.Binding, Core.BindingPartition, Core.BindingPartition}[]    # defer handling these to keep the logging coherent
    if need_to_invalidate_code
        if (b.flags & BINDING_FLAG_ANY_IMPLICIT_EDGES) != 0
            nmethods = ccall(:jl_module_scanned_methods_length, Csize_t, (Any,), gr.mod)
            for i = 1:nmethods
                method = ccall(:jl_module_scanned_methods_getindex, Any, (Any, Csize_t), gr.mod, i)::Method
                invalidated_any |= invalidate_method_for_globalref!(gr, method, invalidated_bpart, new_max_world)
            end
        end
        nbackedges = ccall(:jl_binding_backedges_length, Csize_t, (Any,), b)
        for i = 1:nbackedges
            edge = ccall(:jl_binding_backedges_getindex, Any, (Any, Csize_t), b, i)
            if isa(edge, CodeInstance)
                ccall(:jl_invalidate_code_instance, Cvoid, (Any, UInt), edge, new_max_world)
                invalidated_any = true
            elseif isa(edge, Core.Binding)
                isdefined(edge, :partitions) || continue
                latest_bpart = edge.partitions
                latest_bpart.max_world == typemax(UInt) || continue
                is_some_imported(binding_kind(latest_bpart)) || continue
                if is_some_binding_imported(binding_kind(latest_bpart))
                    partition_restriction(latest_bpart) === b || continue
                end
                push!(queued_bindings, (edge, latest_bpart, latest_bpart))
            else
                invalidated_any |= invalidate_method_for_globalref!(gr, edge::Method, invalidated_bpart, new_max_world)
            end
        end
    end

    if need_to_invalidate_code || need_to_invalidate_export
        # This binding was exported - we need to check all modules that `using` us to see if they
        # have a binding that is affected by this change.
        usings_backedges = ccall(:jl_get_module_usings_backedges, Any, (Any,), gr.mod)
        if usings_backedges !== nothing
            for user::Module in usings_backedges::Vector{Any}
                user_binding = ccall(:jl_get_module_binding_or_nothing, Any, (Any, Any), user, gr.name)::Union{Core.Binding, Nothing}
                user_binding === nothing && continue
                isdefined(user_binding, :partitions) || continue
                latest_bpart = user_binding.partitions
                latest_bpart.max_world == typemax(UInt) || continue
                is_some_implicit(binding_kind(latest_bpart)) || continue
                # A partition starting past `new_max_world` was created during this invalidation:
                # either this binding was already re-resolved (it reaches `b` through more than one
                # `using`) and queued then with its partitions on both sides of the change, or a
                # resolution materialized it just now and nothing compiled depends on it yet. Either
                # way there is nothing left to do here, and `latest_bpart` is not the old partition.
                latest_bpart.min_world > new_max_world && continue
                new_bpart = ccall(:jl_maybe_reresolve_implicit, Any, (Any, Csize_t), user_binding, new_max_world)
                if need_to_invalidate_code || new_bpart !== latest_bpart
                    push!(queued_bindings, (convert(Core.Binding, user_binding), latest_bpart, new_bpart))
                end
            end
        end
    end
    invalidated_any && ccall(:jl_maybe_log_binding_invalidation, Cvoid, (Any,), invalidated_bpart)
    for (edge, invalidated_bpart, new_bpart) in queued_bindings
        invalidated_any |= invalidate_code_for_globalref!(edge, invalidated_bpart, new_bpart, new_max_world)
    end
    return invalidated_any
end
```
The recursion over `queued_bindings` follows binding backedges and `using` chains, which the
runtime keeps acyclic only by the `max_world` and `min_world` guards above; the model bounds it
with `fuel` and fails (not a Julia outcome) when it runs out. `new_max_world+1` is computed
inside the oracle.
-/
def invalidateCodeForGlobalref (BO : BindingInvalidationOracle) :
    Nat → Nat → Partition → Partition → Nat → RM W Bool
  | 0, _, _, _, _ => throw "model: out of fuel in invalidate_code_for_globalref!"
  | fuel + 1, b, invalidatedBpart, newBpart, newMaxWorld => do
    let gr := b
    let needToInvalidateCode ← liftE (BO.accessKeyChanged b invalidatedBpart newBpart newMaxWorld)
    let needToInvalidateExport :=
      exportAffectingPartitionFlags invalidatedBpart != exportAffectingPartitionFlags newBpart
    let mut invalidatedAny := false
    let mut queued : Array (Nat × Partition × Partition) := #[]
    if needToInvalidateCode then
      let br ← liftE ((← getHeap).bindingR b)
      if (br.flags &&& bindingFlagAnyImplicitEdges) != 0 then
        for method in ← liftE (BO.moduleScannedMethods b) do
          let r ← invalidateMethodForGlobalref gr method newMaxWorld
          invalidatedAny := invalidatedAny || r
      for edge in ← liftE (BO.bindingBackedges b) do
        match edge with
        | .ci c =>
          jlInvalidateCodeInstance c newMaxWorld
          invalidatedAny := true
        | .binding e =>
          let eb ← liftE ((← getHeap).bindingR e)
          let some latest := eb.partitions.head? | continue
          if latest.maxWorld != typemaxUInt then continue
          if !isSomeImported (bindingKind latest.kind) then continue
          if isSomeBindingImported (bindingKind latest.kind) then
            if latest.restriction != some b then continue
          queued := queued.push (e, latest, latest)
        | .method m =>
          let r ← invalidateMethodForGlobalref gr m newMaxWorld
          invalidatedAny := invalidatedAny || r
    if needToInvalidateCode || needToInvalidateExport then
      if let some users ← liftE (BO.usingsBackedges b) then
        for user in users do
          let some ub := user | continue
          let ubr ← liftE ((← getHeap).bindingR ub)
          let some latest := ubr.partitions.head? | continue
          if latest.maxWorld != typemaxUInt then continue
          if !isSomeImplicit (bindingKind latest.kind) then continue
          if latest.minWorld > newMaxWorld then continue
          let (newB, parts) ← liftE (BO.reresolveImplicit ub newMaxWorld)
          modifyHeap fun H => { H with bindings := H.bindings.map fun d =>
            if d.id == ub then { d with partitions := parts } else d }
          if needToInvalidateCode || newB.pid != latest.pid then
            queued := queued.push (ub, latest, newB)
    if invalidatedAny then emit .logBindingInvalidation
    for (edge, ib, nb) in queued do
      let r ← invalidateCodeForGlobalref BO fuel edge ib nb newMaxWorld
      invalidatedAny := invalidatedAny || r
    return invalidatedAny

/-- A `GlobalRef`: its module and name (object ids) and its cached `binding` field, if set. -/
structure GlobalRefR where
  mod : Nat
  name : Nat
  binding : Option Nat := none
  deriving Inhabited, BEq, Repr

/-- `convert(Core.Binding, gr)` (`base/runtime_internals.jl:293-299`): the cached binding, or
`jl_get_module_binding(gr.mod, gr.name, true)`, which creates the binding when there is none (a
missing table entry is a model failure). -/
def convertBinding (H : Heap) (gr : GlobalRefR) : Except String Nat :=
  match gr.binding with
  | some b => pure b
  | none => match H.moduleBindings.lookup (gr.mod, gr.name) with
    | some b => pure b
    | none => throw s!"model: no binding for {gr.mod}.{gr.name}"

/-- `invalidate_code_for_globalref!(gr::GlobalRef, invalidated_bpart, new_bpart, new_max_world)`

Julia source: Compiler/src/bindinginvalidations.jl:167-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
invalidate_code_for_globalref!(gr::GlobalRef, invalidated_bpart::Core.BindingPartition, new_bpart::Core.BindingPartition, new_max_world::UInt) =
    invalidate_code_for_globalref!(convert(Core.Binding, gr), invalidated_bpart, new_bpart, new_max_world)
```
-/
def invalidateCodeForGlobalrefGR (BO : BindingInvalidationOracle) (fuel : Nat) (gr : GlobalRefR)
    (invalidatedBpart newBpart : Partition) (newMaxWorld : Nat) : RM W Bool := do
  let b ← liftE (convertBinding (← getHeap) gr)
  invalidateCodeForGlobalref BO fuel b invalidatedBpart newBpart newMaxWorld

/-- `maybe_add_binding_backedge!(b, edge)` (`Compiler/src/typeinfer.jl:887-891`) with
`jl_maybe_add_binding_backedge(b, edge, meth)` (`src/module.c:1900-1915`), where `meth` is the
method of `edge`: when `b` belongs to `meth`'s module, no backedge is stored; `b` gets
`BINDING_FLAG_ANY_IMPLICIT_EDGES` and `meth` gets `did_scan_source` bit `0x2` (and is added to
the module's scanned-methods list, an event here). Otherwise the backedge is stored on `b`
(an event). -/
def maybeAddBindingBackedge (b method : Nat) : RM W Unit := do
  let H ← getHeap
  let br ← liftE (H.bindingR b)
  let m ← liftE (H.method method)
  if br.module_ == m.module_ then
    modifyHeap fun H => { H with bindings := H.bindings.map fun d =>
      if d.id == b then { d with flags := d.flags ||| bindingFlagAnyImplicitEdges } else d }
    modifyHeap (·.setMethod { m with didScanSource := m.didScanSource ||| 0x2 })
  else
    emit (.bindingBackedge b method)

/-- `scan_new_method!(method, world, image_backedges_only)`

Julia source: Compiler/src/bindinginvalidations.jl:170-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Reconstruct, for a method whose source this process has not scanned yet, the invalidation
# that a binding change would have triggered had this code been present when it happened.
# Not every access records an edge (one inference left on the runtime path does not), so this
# source scan is what covers them, and it must ask the same question the edge check asks:
# `binding_changed_since_require_world`, not just "was this binding repartitioned".
function scan_new_method!(method::Method, world::UInt, image_backedges_only::Bool)
    isdefined(method, :source) || return
    isa(method.source, MaybeCompressed) || return
    if image_backedges_only && !has_image_globalref(method)
        return
    end
    src = _uncompressed_ir(method)
    mod = method.module
    foreachgr(src) do gr::GlobalRef
        b = convert(Core.Binding, gr)
        if binding_changed_since_require_world(b, world)
            # TODO: We could turn this into an additional if condition. For now, use it as a reasonably cheap
            # additional consistency check
            @assert !image_backedges_only
            @atomic method.did_scan_source |= 0x4
        end
        maybe_add_binding_backedge!(b, method)
    end
    @atomic method.did_scan_source |= 0x1
end
```
-/
def scanNewMethod (O : Oracle) (method : Nat) (world : Nat) (imageBackedgesOnly : Bool) :
    RM W Unit := do
  let m ← liftE ((← getHeap).method method)
  let some src := m.source | return
  if imageBackedgesOnly && !m.hasImageGlobalref then return
  foreachgr (fun b => do
    if ← bindingChangedSinceRequireWorld O b world then
      if imageBackedgesOnly then jlThrow "AssertionError" "!image_backedges_only"
      let m ← liftE ((← getHeap).method method)
      modifyHeap (·.setMethod { m with didScanSource := m.didScanSource ||| 0x4 })
    maybeAddBindingBackedge b method) src
  let m ← liftE ((← getHeap).method method)
  modifyHeap (·.setMethod { m with didScanSource := m.didScanSource ||| 0x1 })

/-- An entry of the `internal_methods` vector handed to `insert_backedges`. -/
inductive InternalItem where
  | method (uid : Nat)
  | ci (id : Nat)
  | other
  deriving Inhabited, BEq, Repr

/-- `scan_new_methods!(internal_methods, world, image_backedges_only)`

Julia source: Compiler/src/bindinginvalidations.jl:196-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scan_new_methods!(internal_methods::Vector{Any}, world::UInt, image_backedges_only::Bool)
    if image_backedges_only && generating_output(true)
        # Replacing image bindings is forbidden during incremental precompilation - skip backedge insertion
        return
    end
    for method in internal_methods
        if isa(method, Method)
            scan_new_method!(method, world, image_backedges_only)
        end
    end
end
```
-/
def scanNewMethods (O : Oracle) (internal : List InternalItem) (world : Nat)
    (imageBackedgesOnly : Bool) : RM W Unit := do
  if imageBackedgesOnly && (← getHeap).generatingOutputIncremental then return
  scanEach internal
where
  /-- The loop over `internal_methods`, keeping the `Method` items. -/
  scanEach : List InternalItem → RM W Unit
    | [] => pure ()
    | .method m :: rest => do
      scanNewMethod O m world imageBackedgesOnly
      scanEach rest
    | _ :: rest => scanEach rest

end JuliaLean.Compiler.Reinfer
