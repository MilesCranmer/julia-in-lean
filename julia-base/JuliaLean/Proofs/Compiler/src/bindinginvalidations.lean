import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.bindinginvalidations
import JuliaLean.Proofs.Compiler.src.reinfer.Monad

/-!
Properties of `Compiler/src/bindinginvalidations.jl`. The model is
`JuliaLean/Compiler/src/bindinginvalidations.lean`; the runtime queries of
`invalidate_code_for_globalref!` are its `BindingInvalidationOracle`.
-/

namespace JuliaLean.Proofs.Compiler.src.bindinginvalidations

open JuliaLean.Registry JuliaLean.Compiler.CICache JuliaLean.Compiler.Reinfer
open JuliaLean.Proofs.Compiler.src.reinfer.Monad

/-- The bindings of the `GlobalRef`s `foreachgr` visits, in order: a statement's own binding when
it is a `GlobalRef`, then each `GlobalRef` its `userefs` yield. -/
def grVisits (src : List Stmt) : List Nat :=
  src.flatMap fun st => st.gr.toList ++ st.uses.filterMap id

/-- What `anygr` asks about: only the statement when it is a `GlobalRef` (it skips that
statement's `userefs`), otherwise the `GlobalRef`s its `userefs` yield. -/
def anyVisits (src : List Stmt) : List Nat :=
  src.flatMap fun st => match st.gr with | some g => [g] | none => st.uses.filterMap id

/-- `userefs(stmt)` yields nothing for a statement that is a `GlobalRef`: `userefs` marks only
`Expr`s, control-flow nodes, SSA values, `PiNode`s, `PhiNode`s, `UpsilonNode`s, `EnterNode`s and
`Argument`s as relevant (`Compiler/src/ssair/ir.jl:722-726`), and iteration of an irrelevant
statement stops at once (`:738-739`). -/
def GRStmtsHaveNoUses (src : List Stmt) : Prop := ∀ st ∈ src, st.gr.isSome = true → st.uses = []

/-- `foreachgr(visit, src)` calls `visit` on each visited `GlobalRef` in order; `anygr(visit, src)`
answers whether `visit` holds for one of the `GlobalRef`s it asks about, and those are exactly the
ones `foreachgr` visits when `GlobalRef` statements have no `userefs` (so the early `continue` loses
nothing); `should_invalidate_code_for_globalref(gr, src)` then holds exactly when `src` reads `gr`;
`scan_edge_list(ci, b)` holds exactly when `ci` has an edge list that contains the binding `b`;
`export_affecting_partition_flags` reads the guard kind and the exported and deprecated flags. -/
def GlobalrefScan : Prop :=
  (∀ {m : Type → Type} [Monad m] [LawfulMonad m] (visit : Nat → m Unit) (src : List Stmt),
    foreachgr visit src = (grVisits src).forM visit) ∧
  (∀ (visit : Nat → Bool) (src : List Stmt), anygr visit src = (anyVisits src).any visit) ∧
  (∀ src, GRStmtsHaveNoUses src → anyVisits src = grVisits src) ∧
  (∀ gr src, GRStmtsHaveNoUses src → (shouldInvalidateCodeForGlobalref gr src = true ↔ gr ∈ grVisits src)) ∧
  (∀ (c : CIR) (b : Nat), scanEdgeList c b = true ↔
    ∃ es, c.edges = some es ∧ ∃ e ∈ es.toList, (match e with | .binding b' => b' = b | _ => False)) ∧
  (∀ p : Partition, exportAffectingPartitionFlags p = (p.kind % 16 == 9, p.kind &&& 0x10 != 0, p.kind &&& 0x20 != 0))

theorem foreachUse_eq {m : Type → Type} [Monad m] [LawfulMonad m] (visit : Nat → m Unit) :
    ∀ uses : List (Option Nat), foreachgr.foreachUse visit uses = (uses.filterMap id).forM visit
  | [] => rfl
  | none :: us => by simp [foreachgr.foreachUse, foreachUse_eq visit us]
  | some g :: us => by simp [foreachgr.foreachUse, foreachUse_eq visit us]

theorem foreachgr_eq {m : Type → Type} [Monad m] [LawfulMonad m] (visit : Nat → m Unit) :
    ∀ src : List Stmt, foreachgr visit src = (grVisits src).forM visit
  | [] => rfl
  | st :: rest => by
    have ih := foreachgr_eq visit rest
    simp only [grVisits] at ih
    simp only [foreachgr, grVisits, List.flatMap_cons, foreachUse_eq]
    cases st.gr <;> simp [List.forM_append, ih]

theorem anyUse_eq (visit : Nat → Bool) :
    ∀ uses : List (Option Nat), anygr.anyUse visit uses = (uses.filterMap id).any visit
  | [] => rfl
  | none :: us => by simp [anygr.anyUse, anyUse_eq visit us]
  | some g :: us => by
    simp only [anygr.anyUse, List.filterMap_cons, id, List.any_cons, anyUse_eq visit us]
    cases visit g <;> simp

theorem anygr_eq (visit : Nat → Bool) :
    ∀ src : List Stmt, anygr visit src = (anyVisits src).any visit
  | [] => rfl
  | st :: rest => by
    have ih := anygr_eq visit rest
    have hcons : anyVisits (st :: rest) =
        (match st.gr with | some g => [g] | none => st.uses.filterMap id) ++ anyVisits rest := by
      simp [anyVisits]
    rw [hcons, List.any_append, ← ih]
    simp only [anygr]
    cases st.gr with
    | some g => cases visit g <;> simp
    | none =>
      simp only [anyUse_eq]
      cases (st.uses.filterMap id).any visit <;> simp

theorem anyVisits_eq : ∀ src : List Stmt, GRStmtsHaveNoUses src → anyVisits src = grVisits src
  | [] => fun _ => rfl
  | st :: rest => fun h => by
    have ih := anyVisits_eq rest (fun x hx => h x (by simp [hx]))
    simp only [anyVisits, grVisits, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases hg : st.gr with
    | none => simp
    | some g =>
      have := h st (by simp) (by simp [hg])
      simp [this]

theorem gr_spec : GlobalrefScan := by
  refine ⟨fun visit src => foreachgr_eq visit src, anygr_eq, anyVisits_eq, ?_, ?_, ?_⟩
  · intro gr src h
    simp only [shouldInvalidateCodeForGlobalref, anygr_eq, anyVisits_eq src h, List.any_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro h; exact ⟨gr, h, rfl⟩
  · intro c b
    unfold scanEdgeList
    cases hce : c.edges with
    | none => simp
    | some es =>
      simp only [Option.some.injEq, exists_eq_left']
      rw [← Array.any_toList, List.any_eq_true]
      constructor
      · rintro ⟨e, he, hb⟩
        refine ⟨e, by simpa using he, ?_⟩
        cases e <;> simp_all
      · rintro ⟨e, he, hb⟩
        refine ⟨e, by simpa using he, ?_⟩
        cases e <;> simp_all
  · intro p
    simp only [exportAffectingPartitionFlags, partitionMaskKind, partitionKindGuard,
      partitionFlagExported, partitionFlagDeprecated]
    rw [show (0x0f : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `invalidate_code_for_globalref!(gr::GlobalRef, ...)` is the `Binding` method on
`convert(Core.Binding, gr)`: the cached `gr.binding` when it is set, otherwise the module's binding
of that name. -/
def GlobalRefForwards : Prop :=
  ∀ (BO : BindingInvalidationOracle) (fuel : Nat) (gr : GlobalRefR) (ib nb : Partition) (nmw : Nat)
    (s : RS Workspace) (b : Nat),
    (gr.binding = some b ∨ (gr.binding = none ∧ s.heap.moduleBindings.lookup (gr.mod, gr.name) = some b)) →
    (invalidateCodeForGlobalrefGR BO fuel gr ib nb nmw).run s =
      (invalidateCodeForGlobalref BO fuel b ib nb nmw).run s

theorem gr_forwards : GlobalRefForwards := by
  intro BO fuel gr ib nb nmw s b h
  have hc : convertBinding s.heap gr = .ok b := by
    unfold convertBinding
    rcases h with h | ⟨h1, h2⟩
    · simp [h]
    · simp [h1, h2]
  unfold invalidateCodeForGlobalrefGR
  simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hc]

/-- When a binding change leaves `binding_access_key` of the leaf partition and the export-affecting flags unchanged, `invalidate_code_for_globalref!` invalidates nothing, changes nothing and returns false (precision: no needless invalidation). -/
def InvalidateCodeForGlobalrefNoChange : Prop :=
  ∀ (BO : BindingInvalidationOracle) (fuel b nmw : Nat) (ib nb : Partition) (s : RS Workspace) (hk : BO.accessKeyChanged b ib nb nmw = .ok false) (he : exportAffectingPartitionFlags ib = exportAffectingPartitionFlags nb),
    (invalidateCodeForGlobalref BO (fuel + 1) b ib nb nmw).run s = .ok (false, s)

theorem icg_noop : InvalidateCodeForGlobalrefNoChange := by
  intro BO fuel b nmw ib nb s hk he
  simp only [invalidateCodeForGlobalref, liftE, StateT.run, hk, he, bne_self_eq_false]
  rfl

def NoChangeAndForwards : Prop := InvalidateCodeForGlobalrefNoChange ∧ GlobalRefForwards
theorem noChangeAndForwards : NoChangeAndForwards := ⟨icg_noop, gr_forwards⟩

/-- `scan_new_methods!` does nothing during incremental precompilation when only image backedges are needed; `scan_new_method!` does nothing for a method without a (compressed) source, nor for one without image `GlobalRef`s when only image backedges are needed. -/
def ScanSkips : Prop :=
  ∀ (O : Oracle) (internal : List InternalItem) (world method : Nat) (bo : Bool) (s : RS Workspace) (m : MethodR) (hm : s.heap.method method = .ok m),
    (s.heap.generatingOutputIncremental = true →
      (scanNewMethods (W := Workspace) O internal world true).run s = .ok ((), s)) ∧
    (m.source = none → (scanNewMethod (W := Workspace) O method world bo).run s = .ok ((), s)) ∧
    (m.hasImageGlobalref = false → (scanNewMethod (W := Workspace) O method world true).run s = .ok ((), s))

theorem scan_skip : ScanSkips := by
  intro O internal world method bo s m hm
  refine ⟨?_, ?_, ?_⟩
  · intro hg
    unfold scanNewMethods
    simp only [getHeap, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hg, Bool.and_self, if_true]
  · intro hs
    unfold scanNewMethod
    simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hm, hs]
  · intro hi
    unfold scanNewMethod
    cases hs : m.source with
    | none => simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hm, hs]
    | some src =>
      simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hm, hs, hi,
        Bool.not_false, Bool.and_self, if_true]

/-! ## What the source scan does -/

theorem st_bind_ok {σ α β : Type} (x : StateT σ (Except String) α) (f : α → StateT σ (Except String) β)
    (s : σ) (b : β) (s' : σ) (h : (x >>= f).run s = .ok (b, s')) :
    ∃ a s2, x.run s = .ok (a, s2) ∧ (f a).run s2 = .ok (b, s') := by
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h
  cases hx : x s with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, hx, h⟩

theorem find_map_set (x y : MethodR) (hy : y.uid = x.uid) :
    ∀ l : List MethodR, l.find? (·.uid == x.uid) = some x →
      (l.map fun d => if d.uid == y.uid then y else d).find? (·.uid == x.uid) = some y
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : a.uid = x.uid
    · simp [ha, hy]
    · have hb : ¬ a.uid = y.uid := by rw [hy]; exact ha
      have ha' : (a.uid == x.uid) = false := by simpa using ha
      have hb' : (a.uid == y.uid) = false := by simpa using hb
      rw [List.find?_cons, ha'] at h
      rw [List.map_cons, hb', List.find?_cons]
      simp only [Bool.false_eq_true, if_false, ha']
      exact find_map_set x y hy l h

theorem st_bind_ok' {σ α β : Type} (x : StateT σ (Except String) α) (f : α → StateT σ (Except String) β)
    (s : σ) (b : β) (s' : σ) (h : StateT.bind x f s = .ok (b, s')) :
    ∃ a s2, x s = .ok (a, s2) ∧ f a s2 = .ok (b, s') := by
  simp only [StateT.bind, Except.bind] at h
  cases hx : x s with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem setMethod_method (H : Heap) (u : Nat) (x : MethodR) (d : Nat) (h : H.method u = .ok x) :
    (H.setMethod { x with didScanSource := d }).method u = .ok { x with didScanSource := d } := by
  have hu : x.uid = u := method_uid H u x h
  subst hu
  unfold Heap.method at h ⊢
  unfold Heap.setMethod
  split at h
  · rename_i y hy
    cases h
    rw [← Array.find?_toList] at hy
    have := find_map_set x { x with didScanSource := d } rfl H.methods.toList hy
    rw [← Array.find?_toList, Array.toList_map, this]
    rfl
  · cases h

/-- After `scan_new_method!(method, world, image_backedges_only)` runs on a method that has a
(compressed) source and is not skipped (`image_backedges_only` false, or the method has image
`GlobalRef`s), its `did_scan_source` has bit `0x1`: the source was scanned
(`Compiler/src/bindinginvalidations.jl:194`), so `verify_method` does not scan it again. -/
def ScanMarksScanned : Prop :=
  ∀ (O : Oracle) (method world : Nat) (bo : Bool) (s s' : RS Workspace) (m : MethodR),
    (scanNewMethod (W := Workspace) O method world bo).run s = .ok ((), s') →
    s.heap.method method = .ok m → m.source.isSome = true → (bo = false ∨ m.hasImageGlobalref = true) →
    ∃ m', s'.heap.method method = .ok m' ∧ hasBit m'.didScanSource 1 = true

theorem scan_marks : ScanMarksScanned := by
  intro O method world bo s s' m h hm hsrc hb
  obtain ⟨src, hs⟩ : ∃ src, m.source = some src := Option.isSome_iff_exists.1 hsrc
  have hskip : (bo && !m.hasImageGlobalref) = false := by
    rcases hb with hb | hb <;> simp [hb]
  unfold scanNewMethod at h
  simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hm, hs, hskip] at h
  rw [if_neg (by simp)] at h
  obtain ⟨_, s2, _, h2⟩ := st_bind_ok' _ _ _ _ _ h
  simp only [StateT.bind, StateT.get, StateT.pure, StateT.lift, Except.bind, pure, Except.pure] at h2
  simp only [ok_bind] at h2
  cases hx : s2.heap.method method with
  | error e => rw [hx] at h2; cases h2
  | ok x =>
    rw [hx] at h2
    simp only [ok_bind, modifyHeap, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h2
    cases h2
    exact ⟨_, setMethod_method _ _ _ _ hx, by simp [hasBit]⟩

/-- `scan_new_methods!(internal_methods, world, image_backedges_only)`, unless it skips (only image
backedges are needed during incremental precompilation), runs `scan_new_method!` on exactly the
`Method` items of `internal_methods`, in order, and nothing else. -/
def ScanMethodsEach : Prop :=
  ∀ (O : Oracle) (internal : List InternalItem) (world : Nat) (bo : Bool) (s : RS Workspace),
    (bo && s.heap.generatingOutputIncremental) = false →
    (scanNewMethods (W := Workspace) O internal world bo).run s =
      ((internal.filterMap fun | .method m => some m | _ => none).forM
        (fun m => scanNewMethod (W := Workspace) O m world bo)).run s

theorem scanMethods_loop (O : Oracle) (world : Nat) (bo : Bool) :
    ∀ (internal : List InternalItem),
    scanNewMethods.scanEach (W := Workspace) O world bo internal =
      ((internal.filterMap fun | .method m => some m | _ => none).forM
        (fun m => scanNewMethod (W := Workspace) O m world bo))
  | [] => rfl
  | .method m :: rest => by
    simp only [scanNewMethods.scanEach, List.filterMap_cons, List.forM_cons]
    rw [scanMethods_loop O world bo rest]
    rfl
  | .ci c :: rest => by
    simp only [scanNewMethods.scanEach, List.filterMap_cons]
    exact scanMethods_loop O world bo rest
  | .other :: rest => by
    simp only [scanNewMethods.scanEach, List.filterMap_cons]
    exact scanMethods_loop O world bo rest

theorem scanMethods_each : ScanMethodsEach := by
  intro O internal world bo s hg
  unfold scanNewMethods
  simp only [getHeap, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.bind, Except.pure, hg, Bool.false_eq_true, if_false]
  rw [scanMethods_loop O world bo internal]

/-- Both halves for each function: what it skips, and what it does when it does not. -/
def ScanSkipsAndEffects : Prop := ScanSkips ∧ ScanMarksScanned ∧ ScanMethodsEach
theorem scanSkipsAndEffects : ScanSkipsAndEffects := ⟨scan_skip, scan_marks, scanMethods_each⟩

def entries : List Entry := [
  { id := "compiler-bi-globalref-scan", juliaFile := "Compiler/src/bindinginvalidations.jl",
    juliaFns := ["foreachgr(visit, src::CodeInfo)", "anygr(visit, src::CodeInfo)", "should_invalidate_code_for_globalref(gr::GlobalRef, src::CodeInfo)", "isgr(g::GlobalRef)", "scan_edge_list(ci::Core.CodeInstance, binding::Core.Binding)", "export_affecting_partition_flags(bpart::Core.BindingPartition)"],
    statement := "foreachgr(visit, src) calls visit on each statement that is a GlobalRef and on each GlobalRef its userefs yield, in order; anygr(visit, src) answers whether visit holds for one of the GlobalRefs it asks about (skipping the userefs of GlobalRef statements), which are exactly the ones foreachgr visits since userefs yields nothing for a GlobalRef; should_invalidate_code_for_globalref(gr, src) then holds exactly when src reads gr; scan_edge_list(ci, b) holds exactly when ci has an edge list containing the binding b; export_affecting_partition_flags reads (kind == GUARD, EXPORTED, DEPRECATED).",
    source := "Compiler/src/bindinginvalidations.jl:10-55, 86-89 (what the helpers compute) and Compiler/src/ssair/ir.jl:722-739 (userefs of a GlobalRef)",
    status := .proven, prop := ``GlobalrefScan, thm := some ``gr_spec,
    notes := "The model takes each statement of the CodeInfo with what the scans read: its own binding when it is a GlobalRef, and the values its userefs yield. The difftest builds them with the pinned userefs and tallies any GlobalRef statement with uses (stmt:globalref-with-uses, expected 0)." },
  { id := "compiler-bi-no-change-no-invalidation", juliaFile := "Compiler/src/bindinginvalidations.jl",
    juliaFns := ["invalidate_code_for_globalref!(gr::GlobalRef, invalidated_bpart::Core.BindingPartition, new_bpart::Core.BindingPartition, new_max_world::UInt)"],
    statement := "When a binding change leaves binding_access_key of the leaf partition and the export-affecting flags unchanged, invalidate_code_for_globalref! invalidates nothing, changes nothing and returns false; the GlobalRef method is the Binding method on convert(Core.Binding, gr), the cached gr.binding or the module's binding of that name.",
    source := "comment Compiler/src/bindinginvalidations.jl:96-98 (if this information does not change, we do not need to invalidate any code), :167-168 and base/runtime_internals.jl:293-299",
    status := .proven, prop := ``NoChangeAndForwards, thm := some ``noChangeAndForwards,
    notes := "The runtime queries (walk_binding_partition with binding_access_key, the backedge lists, jl_maybe_reresolve_implicit) are an oracle and are not difftested. What the Binding method does when the key changes has no proven statement (its row is todo)." },
  { id := "compiler-bi-scan-skips", juliaFile := "Compiler/src/bindinginvalidations.jl",
    juliaFns := ["scan_new_method!(method::Method, world::UInt, image_backedges_only::Bool)", "scan_new_methods!(internal_methods::Vector{Any}, world::UInt, image_backedges_only::Bool)"],
    statement := "scan_new_methods! does nothing during incremental precompilation when only image backedges are needed, and otherwise runs scan_new_method! on exactly the Method items of internal_methods, in order; scan_new_method! does nothing for a method without a compressed source, nor for one without image GlobalRefs when only image backedges are needed, and otherwise ends with bit 0x1 of did_scan_source set.",
    source := "Compiler/src/bindinginvalidations.jl:175-206 (the early returns, their comment, and the final did_scan_source |= 0x1)",
    status := .proven, prop := ``ScanSkipsAndEffects, thm := some ``scanSkipsAndEffects,
    notes := "Open, no entry: that bit 0x4 is set exactly when a visited binding changed since the require world (needs a loop invariant over the visits; the heap changes the body makes leave partitions and the require world alone)." }
]

end JuliaLean.Proofs.Compiler.src.bindinginvalidations
