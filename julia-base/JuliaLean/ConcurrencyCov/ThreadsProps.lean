import JuliaLean.ConcurrencyCov.Threads

/-! Properties of `base/threadingconstructs.jl` and their proofs or refutations. -/

namespace JuliaLean.ConcurrencyCov.Threads

open JuliaLean JuliaLean.ConcurrencyCov

/-- A runtime with one interactive pool, one default pool, and `nf` foreign threads. -/
def twoPools (cur ni nd nf ngc : Nat) : ThreadRt :=
  { cur, nThreads := ni + nd + nf, perPool := [ni, nd], nGcThreads := ngc }

/-- The query wrappers preserve the runtime values and the source branch order
(`base/threadingconstructs.jl:36-169`). -/
def ThreadQueriesSpec : Prop :=
  (∀ rt, threadid rt = i64 ((rt.cur : Int) + 1)) ∧
  (∀ rt, maxthreadid rt = i64 rt.nThreads) ∧
  (∀ t rt, nthreadsInPool t rt =
    if 0 ≤ t.val then (rt.perPool[t.val.toNat]?).map fun n => i64 n else none) ∧
  (∀ t, tpidToSym t =
    if t.val = 0 then .ok "interactive"
    else if t.val = 1 then .ok "default"
    else if t.val = -1 then .ok "foreign"
    else .error (.argumentError s!"Unrecognized threadpool id {t.val}")) ∧
  (∀ p, symToTpid p =
    if p = "interactive" then .ok (i8 0)
    else if p = "default" then .ok (i8 1)
    else if p = "foreign" then .ok (i8 (-1))
    else .error (.argumentError s!"Unrecognized threadpool name `{p}`")) ∧
  (∀ p rt, nthreads p rt = threadpoolsize p rt) ∧
  (∀ rt, nthreadpools rt = i64 rt.perPool.length) ∧
  (∀ rt, ngcthreads rt = i64 rt.nGcThreads + i64 1) ∧
  (∀ p rt, threadpoolsize p rt =
    if p = "default" ∨ p = "interactive" then do
      let tpid ← symToTpid p
      return nthreadsInPool tpid rt
    else if p = "foreign" then
      .error (.errorException "Threadpool size of `:foreign` is indeterminant")
    else .error (.errorException "invalid threadpool specified")) ∧
  (∀ p rt, threadpooltids p rt =
    let ni := (nthreadsInPool (i8 0) rt).getD (i64 0)
    if p = "interactive" then .ok (unitRange 1 ni.val)
    else if p = "default" then
      let nd := (nthreadsInPool (i8 1) rt).getD (i64 0)
      .ok (unitRange (ni.val + 1) (ni.val + nd.val))
    else .error (.errorException "invalid threadpool specified")) ∧
  (∀ tid rt, threadpool tid rt = do
    let t ← toI16 (tid - i64 1)
    let tpid ← jlThreadpoolid t rt
    tpidToSym tpid)

theorem threadQueriesSpec_proven : ThreadQueriesSpec := by
  repeat' apply And.intro
  all_goals intros
  all_goals rfl

/-- `threadpooldescription(t)` labels exactly the GC-thread ids as `foreign: gc`.
The implementation uses `ngcthreads()`, which includes one mutator thread
(`base/threadingconstructs.jl:106-117,169`). -/
def ThreadpoolDescriptionGc : Prop :=
  ∀ cur ni nd nf ngc (t : Nat), ngc ≤ nf → ni + nd + nf < 2 ^ 15 → 1 ≤ t → t ≤ ni + nd + nf →
    (threadpooldescription (i64 t) (twoPools cur ni nd nf ngc) = .ok "foreign: gc" ↔
      (ni + nd < t ∧ t ≤ ni + nd + ngc))

theorem threadpoolDescriptionGc_refuted : ¬ ThreadpoolDescriptionGc := by
  intro h
  have hd : threadpooldescription (i64 (3 : Nat)) (twoPools 0 1 1 1 0) = .ok "foreign: gc" :=
    rfl
  have bad := (h 0 1 1 1 0 3 (by omega) (by omega) (by omega) (by omega)).mp hd
  omega

/-- The macro front end preserves its argument checks and dispatches loops and
comprehensions to the source-selected expansion (`base/threadingconstructs.jl:182,257-389,789-824`). -/
def ThreadsMacroSpec : Prop :=
  (∀ (β : Type) (f : Nat → β) i, threadsCall f i = f i) ∧
  (∀ s, threadingRunExpr s = ⟨s = "static"⟩) ∧
  (∀ s, threadsfor s = .loop (s = "greedy") (threadingRunExpr s)) ∧
  (∀ filtered greedy flatten productFlag typed sched,
    singleIterator filtered greedy flatten productFlag typed sched =
      ⟨if greedy then .greedy else if !filtered && !flatten then .fast else .default,
        productFlag, filtered, flatten, sched = "static", typed⟩) ∧
  (∀ c sched typed, multiIterator c sched typed =
    singleIterator c.cond.isSome (sched = "greedy") c.flatten true typed sched) ∧
  (∀ args, threadsMacro args = do
    let (sched, ex) ← threadsArgs args
    threadsExpand sched ex) ∧
  (∀ c sched typed, c.iters = [] →
    threadsforComprehension c sched typed = .error (.assertionError "gen.head === :generator"))

theorem threadsMacroSpec_proven : ThreadsMacroSpec := by
  refine ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, ?_⟩
  intro c sched typed h
  cases c with
  | mk flatten iters cond => simp only at h; subst iters; rfl

/-- The generated comprehension helpers preserve source order, output shape, and
element-type branch selection (`base/threadingconstructs.jl:331-565`). -/
def ComprehensionSpec : Prop :=
  (∀ (α β : Type) (body : α → β) x, bodyFunc body x = body x) ∧
  (∀ (α : Type) (cond : Option (α → Bool)) x,
    predExpr cond x = match cond with | none => true | some p => p x) ∧
  (∀ (β : Type) (dest vals : List β), addExpr dest vals = dest ++ vals) ∧
  (∀ (α β : Type) (items : Items α) (body : α → β) n,
    (fastRun items body n).shape = items.shape ∧
    (fastRun items body n).elems.length = items.elems.length) ∧
  (∀ (α β : Type) (items : Items α) (pred : α → Bool) (vals : α → List β) n,
    (defaultRun items pred vals n).shape = [(defaultRun items pred vals n).elems.length]) ∧
  (∀ (α β : Type) (items : Items α) hasShape (pred : α → Bool) (vals : α → List β) oneEach order,
    (greedyRun items hasShape pred vals oneEach order).shape =
      if oneEach && hasShape then items.shape
      else [(greedyRun items hasShape pred vals oneEach order).elems.length]) ∧
  (∀ (τ β : Type) (A : TyAlg τ β) (ET : τ) (elems : List β),
    comprehensionResultType A ET elems = match elems with
      | [] => A.joinUnion ET
      | x :: rest => if A.concrete ET then ET else widenedEltype A (A.typeOf x) rest) ∧
  (∀ (τ β : Type) (A : TyAlg τ β) (T : τ) (rest : List β),
    widenedEltype A T rest = match rest with
      | [] => T
      | x :: xs => if A.isa x T then widenedEltype A T xs
        else widenedEltype A (A.join T (A.typeOf x)) xs)

theorem comprehensionSpec_proven : ComprehensionSpec := by
  refine ⟨fun _ _ _ _ => rfl, ?_, fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro α cond x
    cases cond <;> rfl
  · intro α β items body n
    exact ⟨rfl, by simp [fastRun]⟩
  · intro α β items pred vals n
    rfl
  · intro α β items hasShape pred vals oneEach order
    rfl
  · intro τ β A ET elems
    cases elems <;> rfl
  · intro τ β A T rest
    cases rest <;> rfl

/-- `@spawn` preserves the source argument checks, same-pool resolution, pool
fallback, synchronization registration, and non-sticky task flag
(`base/threadingconstructs.jl:826-920`). -/
def SpawnSpec : Prop :=
  (∀ tp rt, spawnSetThrpool tp rt = do
    let tpid ← symToTpid tp
    let n := nthreadsInPool tpid rt
    if tpid.val = -1 ∨ zeroCount n then return i8 1 else return tpid) ∧
  (∀ args inSync rt s, spawnMacro args inSync rt = .ok s →
    s.synced = inSync ∧ s.sticky = false)

theorem spawnSpec_proven : SpawnSpec := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro args inSync rt s h
  unfold spawnMacro at h
  obtain ⟨tp, -, h⟩ := bind_ok h
  obtain ⟨tp', -, h⟩ := bind_ok h
  obtain ⟨tpid, -, h⟩ := bind_ok h
  cases h
  exact ⟨rfl, rfl⟩

end JuliaLean.ConcurrencyCov.Threads
