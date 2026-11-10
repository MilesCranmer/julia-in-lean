import JuliaLean.Proofs.Compiler.src.inferenceresult

/-!
Branch-by-branch statements of the result-caching code. They answer the review of the length and
soundness entries in `inferenceresult.lean`: for each method, what it returns on each branch,
given what the calls it makes return.

`Gives m v` says that every run of `m` that returns, returns `v`. A hypothesis `Gives m v` on a
call the method makes fixes the answer of that call; the conclusion then fixes the method's
answer. `Via m m'` says that every result of `m` is a result of `m'`, from some state. `Res m x`
says that `x` is one result of `m`.
-/

namespace JuliaLean.Proofs.Compiler.src.inferenceresult

open JuliaLean.Registry JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-- Every run of `m` that returns, returns `v`. -/
abbrev Gives {α : Type} (m : CM α) (v : α) : Prop := Returns m (· = v)

/-- Every result of `m` is a result of `m'` from some state, with the same final state. -/
def Via {α : Type} (m m' : CM α) : Prop :=
  ∀ s r s', m.run s = .ok (r, s') → ∃ s₁, m'.run s₁ = .ok (r, s')

/-- `x` is a result of some run of `m`. -/
def Res {α : Type} (m : CM α) (x : α) : Prop := ∃ s s', m.run s = .ok (x, s')

theorem pure_ok_inv' {α : Type} {x r : α} {s s' : Nat}
    (h : (pure x : CM α).run s = .ok (r, s')) : r = x ∧ s' = s := by
  cases h; exact ⟨rfl, rfl⟩

theorem gives_run {α : Type} {m : CM α} {v : α} {s r s'} (h : Gives m v) (hr : m.run s = .ok (r, s')) :
    r = v := h s r s' hr

/-! ## `elim_free_typevars` -/

/-- `elim_free_typevars(t)` (`Compiler/src/inferenceresult.jl:204-215`): following its comment, a
type with free type variables becomes `Type` when it is a `Type{...}` (the only malformed type
that can reach here at runtime) and `Any` otherwise. -/
def ElimFreeTypevarsChoice : Prop :=
  (∀ t, JuliaLean.Compiler.hasFreeTypevars t = true → JuliaLean.Compiler.isType t = true →
    elimFreeTypevars t = typeTypeVal) ∧
  (∀ t, JuliaLean.Compiler.hasFreeTypevars t = true → JuliaLean.Compiler.isType t = false →
    elimFreeTypevars t = anyType) ∧
  typeTypeVal ≠ anyType

theorem elimFreeTypevarsChoice_proven : ElimFreeTypevarsChoice := by
  refine ⟨fun t h1 h2 => ?_, fun t h1 h2 => ?_, fun h => by simp [typeTypeVal, anyType] at h⟩
  · simp [elimFreeTypevars, h1, h2]
  · simp [elimFreeTypevars, h1, h2]

/-! ## `is_argtype_match` -/

/-- `is_argtype_match(𝕃, given, cache, overridden_by_const)` (`Compiler/src/inferenceresult.jl:100-109`):
for a forwardable `given` (a `Const`, `PartialStruct`, ... the lattice can forward) it is exactly
`is_lattice_equal(𝕃, given, cache)`; otherwise it is `!overridden_by_const`, so a position the cache
entry did not override matches whatever the cache type is, and one it overrode never matches. -/
def IsArgtypeMatchExact : Prop :=
  (∀ n E L g c o, isForwardableArgtype L g = false → isArgtypeMatch n E L g c o = pure (!o)) ∧
  (∀ n E L g c o, isForwardableArgtype L g = true →
    ∀ s, (isArgtypeMatch n E L g c o).run s = (isLatticeEqual n E L g c).run s)

theorem isArgtypeMatchExact_proven : IsArgtypeMatchExact := by
  refine ⟨fun n E L g c o h => ?_, fun n E L g c o h s => ?_⟩
  · simp [isArgtypeMatch, h]
  · simp [isArgtypeMatch, h]

/-! ## `constprop_cache_lookup` -/

/-- The inner loop of `constprop_cache_lookup` over the positions is the conjunction of the
per-position `is_argtype_match` answers: an empty query matches, and a position's answer `b`
followed by the rest's answer `r` gives `b && r` (the first failing position ends the loop). -/
def ArgtypesMatchExact : Prop :=
  (∀ n E L cs os, Gives (argtypesMatch n E L [] cs os) true) ∧
  (∀ n E L g gs c cs o os b r, Gives (isArgtypeMatch n E L g c o) b →
    Gives (argtypesMatch n E L gs cs os) r →
    Gives (argtypesMatch n E L (g :: gs) (c :: cs) (o :: os)) (b && r))

theorem argtypesMatchExact_proven : ArgtypesMatchExact := by
  refine ⟨fun n E L cs os => ?_, fun n E L g gs c cs o os b r hb hr => ?_⟩
  · intro s x s' h; unfold argtypesMatch at h; cases h; rfl
  · intro s x s' h
    unfold argtypesMatch at h
    obtain ⟨b', s₁, h1, h2⟩ := run_bind_inv h
    have := hb _ _ _ h1; subst this
    cases b'
    · simp at h2; cases h2; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h2
      simp [hr _ _ _ h2]

/-- Whether entry `c` passes every test of `constprop_cache_lookup` for the query, with `m c` what
the position loop answers for it: same `MethodInstance`, made in `world` and valid there, a key of
the query's length, and `overridden_by_const` set. -/
def EntryPasses (mi : ObjId) (given : List LElt) (world : Nat) (m : ConstpropEntry → Bool)
    (c : ConstpropEntry) : Bool :=
  c.mi == mi && c.cacheWorld == world &&
    (if c.isLocal then c.proofWorlds else c.validWorlds).contains world &&
    c.argtypes.length == given.length && c.overriddenByConst.isSome && m c

/-- What `constprop_cache_lookup` answers when `p` says which entries pass: the 1-based position of
the first passing entry that is not a tombstone; else `missing` when a passing entry is a
tombstone; else `nothing`. -/
def lookupAnswer (cache : List ConstpropEntry) (p : ConstpropEntry → Bool) : ConstpropLookup :=
  match cache.findIdx? (fun c => p c && !c.tombstone) with
  | some i => .found (i + 1)
  | none => if cache.any (fun c => p c && c.tombstone) then .missing_ else .nothing_

/-- `constprop_cache_lookup(𝕃, mi, given, cache, world)` (`Compiler/src/inferenceresult.jl:217-261`)
returns the first entry that answers the query and is not a tombstone, `missing` when only
tombstones answer it, and `nothing` when no entry does. `m c` is what the position loop answers for
an entry that reaches it. So a cache hit is pinned, not only its soundness: an entry of the same
`MethodInstance` and world whose key matches is returned. -/
def ConstpropLookupExact : Prop :=
  ∀ n E L mi miVa given cache world (m : ConstpropEntry → Bool),
    (∀ c ∈ cache, ∀ ov, c.mi = mi → c.cacheWorld = world → c.argtypes.length = given.length →
      c.overriddenByConst = some ov → Gives (argtypesMatch n E L given c.argtypes ov) (m c)) →
    Gives (constpropCacheLookup n E L mi miVa given cache world)
      (lookupAnswer cache (EntryPasses mi given world m))

theorem lookupLoop_exact (n E L mi miVa given world) (m : ConstpropEntry → Bool) :
    ∀ (cache : List ConstpropEntry) (idx : Nat) (ft : Bool),
    (∀ c ∈ cache, ∀ ov, c.mi = mi → c.cacheWorld = world → c.argtypes.length = given.length →
      c.overriddenByConst = some ov → Gives (argtypesMatch n E L given c.argtypes ov) (m c)) →
    Gives (constpropLookupLoop n E L mi miVa given world idx ft cache)
      (match cache.findIdx? (fun c => EntryPasses mi given world m c && !c.tombstone) with
        | some i => .found (idx + i + 1)
        | none => if ft || cache.any (fun c => EntryPasses mi given world m c && c.tombstone)
            then .missing_ else .nothing_)
  | [], idx, ft, _ => by
    intro s r s' h
    unfold constpropLookupLoop at h
    cases h
    cases ft <;> rfl
  | c :: rest, idx, ft, hm => by
    have ih := fun ft' => lookupLoop_exact n E L mi miVa given world m rest (idx + 1) ft'
      (fun c' hc' => hm c' (List.mem_cons_of_mem _ hc'))
    -- The answer when entry `c` does not pass.
    have skip : ∀ ft', EntryPasses mi given world m c = false → (ft' = ft) →
        ∀ s r s', (constpropLookupLoop n E L mi miVa given world (idx + 1) ft' rest).run s = .ok (r, s') →
        r = (match (c :: rest).findIdx? (fun c => EntryPasses mi given world m c && !c.tombstone) with
          | some i => .found (idx + i + 1)
          | none => if ft || (c :: rest).any (fun c => EntryPasses mi given world m c && c.tombstone)
              then .missing_ else .nothing_) := by
      intro ft' hp hft s r s' h
      subst hft
      rw [ih ft' s r s' h]
      simp only [List.findIdx?_cons, hp, Bool.false_and, List.any_cons, Bool.false_or]
      cases List.findIdx? (fun c => EntryPasses mi given world m c && !c.tombstone) rest with
      | none => rfl
      | some i => simp only [Option.map_some]; congr 1; omega
    intro s r s' h
    unfold constpropLookupLoop at h
    by_cases h1 : (c.mi != mi || c.cacheWorld != world) = true
    · simp only [h1, ite_true, bind_pure] at h
      refine skip ft ?_ rfl s r s' h
      simp only [EntryPasses]
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h1
      rcases h1 with h1 | h1 <;> simp [h1]
    simp only [h1, ite_false, Bool.false_eq_true] at h
    have hmi : c.mi = mi ∧ c.cacheWorld = world := by
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at h1
      exact h1
    by_cases h2 : (!(if c.isLocal then c.proofWorlds else c.validWorlds).contains world) = true
    · simp only [h2, ite_true, bind_pure] at h
      refine skip ft ?_ rfl s r s' h
      simp only [Bool.not_eq_true'] at h2
      simp [EntryPasses, h2]
    simp only [h2, ite_false, Bool.false_eq_true] at h
    have hw : (if c.isLocal then c.proofWorlds else c.validWorlds).contains world = true := by
      simpa using h2
    by_cases h3 : (c.argtypes.length != given.length) = true
    · simp only [h3, ite_true] at h
      by_cases h4 : (!miVa) = true
      · simp only [h4, ite_true] at h
        rw [run_bind_error (jlThrow_run _ _ _)] at h
        cases h
      · simp only [h4, ite_false, Bool.false_eq_true, pure_bind, bind_pure] at h
        refine skip ft ?_ rfl s r s' h
        simp only [bne_iff_ne, ne_eq] at h3
        simp [EntryPasses, h3]
    simp only [h3, ite_false, Bool.false_eq_true] at h
    have hl : c.argtypes.length = given.length := by simpa using h3
    cases hov : c.overriddenByConst with
    | none =>
      simp only [hov] at h
      refine skip ft ?_ rfl s r s' h
      simp [EntryPasses, hov]
    | some ov =>
      simp only [hov] at h
      obtain ⟨b, s₁, hb, hk⟩ := run_bind_inv h
      have hbm := hm c List.mem_cons_self ov hmi.1 hmi.2 hl hov _ _ _ hb
      subst hbm
      have hp : EntryPasses mi given world m c = m c := by
        simp [EntryPasses, hmi.1, hmi.2, hw, hl, hov]
      cases hmc : m c with
      | false =>
        simp only [hmc, Bool.not_false, ite_true, bind_pure] at hk
        exact skip ft (by rw [hp, hmc]) rfl s₁ r s' hk
      | true =>
        simp only [hmc, Bool.not_true, Bool.false_eq_true, ite_false] at hk
        by_cases ht : c.tombstone = true
        · simp only [ht, ite_true, bind_pure] at hk
          rw [ih true s₁ r s' hk]
          simp only [List.findIdx?_cons, hp, hmc, ht, Bool.not_true, Bool.and_false, List.any_cons,
            Bool.and_self, Bool.true_or, Bool.or_true, ite_true]
          cases List.findIdx? (fun c => EntryPasses mi given world m c && !c.tombstone) rest with
          | none => rfl
          | some i => simp only [Option.map_some]; congr 1; omega
        · simp only [ht, ite_false, Bool.false_eq_true, pure_run, Except.ok.injEq, Prod.mk.injEq] at hk
          obtain ⟨rfl, -⟩ := hk
          have ht' : c.tombstone = false := by simpa using ht
          simp [List.findIdx?_cons, hp, hmc, ht']

theorem constpropLookupExact_proven : ConstpropLookupExact := by
  intro n E L mi miVa given cache world m hm s r s' h
  rw [lookupLoop_exact n E L mi miVa given world m cache 0 false hm s r s' h]
  unfold lookupAnswer
  cases cache.findIdx? (fun c => EntryPasses mi given world m c && !c.tombstone) with
  | none => simp
  | some i => simp

/-! ## `pick_const_arg` -/

/-- `pick_const_arg(𝕃, given, cache)` (`Compiler/src/inferenceresult.jl:49-62`) on the branches where
the given argument type is forwardable and not lattice-equal to the cache type: it keeps the given
type, except that a `PartialStruct` that is not strictly below a cache `Type` is narrowed by
`tmeet` with it. (The branches that return the cache type are `PickConstArgKeepsCache`.) -/
def PickConstArgPrefersGiven : Prop :=
  (∀ ops n E L g c, isForwardableArgtype L g = true → Gives (isLatticeEqual n E L g c) false →
    ¬(g.isPartialStruct = true ∧ c.isTypeElt = true) → Gives (pickConstArg ops n E L g c) g) ∧
  (∀ ops n E L g ct, isForwardableArgtype L g = true → g.isPartialStruct = true →
    (LElt.ty ct).isTypeElt = true → Gives (isLatticeEqual n E L g (.ty ct)) false →
    Gives (sqsubStrict n E L g (.ty ct)) true → Gives (pickConstArg ops n E L g (.ty ct)) g) ∧
  (∀ ops n E L g ct, isForwardableArgtype L g = true → g.isPartialStruct = true →
    (LElt.ty ct).isTypeElt = true → Gives (isLatticeEqual n E L g (.ty ct)) false →
    Gives (sqsubStrict n E L g (.ty ct)) false → Via (pickConstArg ops n E L g (.ty ct)) (tmeet ops n E L g ct))

theorem pickConstArgPrefersGiven_proven : PickConstArgPrefersGiven := by
  refine ⟨fun ops n E L g c hf he hps => ?_, fun ops n E L g ct hf hps hct he hst => ?_,
    fun ops n E L g ct hf hps hct he hst => ?_⟩
  · intro s r s' h
    unfold pickConstArg isArgtypeMatch at h
    simp only [hf, ite_true] at h
    obtain ⟨b, s₁, h1, h2⟩ := run_bind_inv h
    have := he _ _ _ h1; subst this
    simp only [Bool.not_false, ite_true] at h2
    have hb : (g.isPartialStruct && c.isTypeElt) = false := by
      cases h3 : g.isPartialStruct <;> cases h4 : c.isTypeElt <;> simp_all
    simp only [hb, Bool.false_eq_true, ite_false] at h2
    exact (pure_ok_inv' h2).1
  · intro s r s' h
    unfold pickConstArg isArgtypeMatch at h
    simp only [hf, ite_true] at h
    obtain ⟨b, s₁, h1, h2⟩ := run_bind_inv h
    have := he _ _ _ h1; subst this
    simp only [Bool.not_false, ite_true, hps, hct] at h2
    obtain ⟨b, s₂, h3, h4⟩ := run_bind_inv h2
    have := hst _ _ _ h3; subst this
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h4
    cases h4; rfl
  · intro s r s' h
    unfold pickConstArg isArgtypeMatch at h
    simp only [hf, ite_true] at h
    obtain ⟨b, s₁, h1, h2⟩ := run_bind_inv h
    have := he _ _ _ h1; subst this
    simp only [Bool.not_false, ite_true, hps, hct] at h2
    obtain ⟨b, s₂, h3, h4⟩ := run_bind_inv h2
    have := hst _ _ _ h3; subst this
    simp only [Bool.not_false, ite_true] at h4
    obtain ⟨x, s₃, h5, h6⟩ := run_bind_inv h4
    cases h6
    exact ⟨s₂, h5⟩

/-! ## `matching_cache_argtypes` (simple argument types) -/

/-- `w` is a result of `widenslotwrapper(a)` as `matching_cache_argtypes` applies it: a
`Conditional` is widened by `widenconditional`, a `MustAlias` by `widenmustalias`, and anything
else is kept. -/
def WidenedArg (a w : LElt) : Prop :=
  if a.isAnyConditional then Res (widenconditional a) w
  else if a.isAnyMustAlias then Res (widenmustalias a) w
  else w = a

theorem widenslotwrapper_res {a w : LElt} {s s'} (h : (widenslotwrapper a).run s = .ok (w, s')) :
    WidenedArg a w := by
  unfold widenslotwrapper at h
  unfold WidenedArg
  by_cases hc : a.isAnyConditional = true
  · simp only [hc, ite_true] at h ⊢
    exact ⟨s, s', h⟩
  · simp only [hc, ite_false, Bool.false_eq_true] at h ⊢
    by_cases hm : a.isAnyMustAlias = true
    · simp only [hm, ite_true] at h ⊢
      exact ⟨s, s', h⟩
    · simp only [hm, ite_false, Bool.false_eq_true] at h ⊢
      cases h; rfl

/-- `WidenedArg` at every position of two lists of the same length. -/
def AllWidened : List LElt → List LElt → Prop
  | [], [] => True
  | a :: as, w :: ws => WidenedArg a w ∧ AllWidened as ws
  | _, _ => False

theorem mapM_widen : ∀ (args : List LElt) (s : Nat) (ws : List LElt) (s' : Nat),
    (args.mapM widenslotwrapper).run s = .ok (ws, s') → AllWidened args ws
  | [], s, ws, s', h => by simp only [List.mapM_nil] at h; cases h; trivial
  | a :: as, s, ws, s', h => by
    simp only [List.mapM_cons] at h
    obtain ⟨w, s₁, h1, h2⟩ := run_bind_inv h
    obtain ⟨ws', s₂, h3, h4⟩ := run_bind_inv h2
    cases h4
    exact ⟨widenslotwrapper_res h1, mapM_widen as s₁ ws' _ h3⟩

/-- `matching_cache_argtypes(𝕃, mi, simple_argtypes, cache_argtypes)`
(`Compiler/src/inferenceresult.jl:38-47`) is `pick_const_args!` on the call's argument types after
`widenslotwrapper` at every position: its result is a result of `pick_const_args!` on a list that
agrees with the argument types position by position, except that slot wrappers are widened. -/
def MatchingCacheArgtypesSimpleVia : Prop :=
  ∀ ops n E L args ca s r s', (matchingCacheArgtypesSimple ops n E L args ca).run s = .ok (r, s') →
    ∃ ws, AllWidened args ws ∧ ∃ s₁, (pickConstArgs ops n E L ws ca).run s₁ = .ok (r, s')

theorem matchingCacheArgtypesSimpleVia_proven : MatchingCacheArgtypesSimpleVia := by
  intro ops n E L args ca s r s' h
  unfold matchingCacheArgtypesSimple at h
  obtain ⟨ws, s₁, h1, h2⟩ := run_bind_inv h
  exact ⟨ws, mapM_widen args s ws s₁ h1, s₁, h2⟩

/-! ## `keep_source_for_output` and `maybe_compress_codeinfo` -/

/-- `keep_source_for_output(mi)` (`Compiler/src/typeinfer.jl:590-593`) holds exactly when Julia is
generating output and the method instance has a compileable signature; it asks
`isa_compileable_sig` only when generating output. -/
def KeepSourceForOutputExact : Prop :=
  (∀ gen (cs : Unit → Bool), keepSourceForOutput gen cs = true ↔ gen = true ∧ cs () = true) ∧
  (∀ (cs : Unit → Bool), keepSourceForOutput false cs = false)

theorem keepSourceForOutputExact_proven : KeepSourceForOutputExact := by
  refine ⟨fun gen cs => ?_, fun cs => rfl⟩
  simp [keepSourceForOutput]

/-- `maybe_compress_codeinfo(interp, mi, ci)` (`Compiler/src/typeinfer.jl:595-610`) on every input.
Toplevel code (`mi.def` not a `Method`) is returned as it is. For a method: when trees may be
discarded and the source is not inlineable, `precompile_keep_ir` keeps the `CodeInfo`, and
otherwise the source is dropped (`nothing`) unless `keep_source_for_output` holds. Every other
method source is compressed exactly when `may_compress` holds. -/
def MaybeCompressExact : Prop :=
  ∀ isM mdt inl keepIr gen mc (cs : Unit → Bool),
    let r := maybeCompressCodeinfo isM mdt inl keepIr gen mc cs
    let drops := mdt = true ∧ inl = false
    (r = .nothing_ ↔ isM = true ∧ drops ∧ keepIr = false ∧ keepSourceForOutput gen cs = false) ∧
    (r = .compressed ↔ isM = true ∧ mc = true ∧ ¬(drops ∧ (keepIr = true ∨ keepSourceForOutput gen cs = false))) ∧
    (isM = false → r = .codeinfo)

theorem maybeCompressExact_proven : MaybeCompressExact := by
  intro isM mdt inl keepIr gen mc cs
  simp only
  rcases Bool.eq_false_or_eq_true (keepSourceForOutput gen cs) with hk | hk <;>
  · unfold maybeCompressCodeinfo
    cases isM <;> cases mdt <;> cases inl <;> cases keepIr <;> cases mc <;> simp [Id.run, hk] <;> rfl

/-! ## `count_const_size` -/

/-- A loop over `List.range' start k` that may stop early: `I i b` holds before step `i`, a
`yield` re-establishes it for `i + 1`, and a `done` gives `D`. -/
theorem returns_forIn_range'_done {β : Type} (I : Nat → β → Prop) (D : β → Prop)
    (f : Nat → β → CM (ForInStep β)) (k start : Nat)
    (hstep : ∀ i b, start ≤ i → i < start + k → I i b →
      Returns (f i b) (fun r => match r with | .yield b' => I (i + 1) b' | .done b' => D b')) :
    ∀ b, I start b → Returns (forIn (List.range' start k) b f) (fun r => I (start + k) r ∨ D r) := by
  induction k generalizing start with
  | zero => intro b hb; simp only [List.range'_zero, List.forIn_nil]; exact returns_pure (Or.inl (by simpa using hb))
  | succ k ih =>
    intro b hb
    simp only [List.range'_succ, List.forIn_cons]
    refine returns_bind (hstep start b (Nat.le_refl _) (by omega) hb) ?_
    intro r hr
    cases r with
    | done b' => exact returns_pure (Or.inr hr)
    | yield b' =>
      have := ih (start + 1) (fun i b hi1 hi2 hI => hstep i b (by omega) (by omega) hI) b' hr
      rw [show start + (k + 1) = start + 1 + k by omega]
      exact this

/-- `c 1 + ... + c m`. -/
def sumTo (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumTo c m + c (m + 1)

theorem sumTo_mono (c : Nat → Nat) : ∀ {i j : Nat}, i ≤ j → sumTo c i ≤ sumTo c j := by
  intro i j h
  induction j with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_trans (ih (by omega)) (by simp [sumTo])
    · rw [h]; exact Nat.le_refl _

/-- The size `count_const_size` reports for a total `t`: `t` itself up to `MAX_INLINE_CONST_SIZE`,
and `MAX_INLINE_CONST_SIZE + 1` ("too large") above it. -/
def capSize (t : Nat) : Nat := if t ≤ MAX_INLINE_CONST_SIZE then t else MAX_INLINE_CONST_SIZE + 1

/-- Whether field `i` (1-based) of a type with facts `f` is stored as a pointer. -/
def fieldIsptr (f : DTFacts) (i : Nat) : Bool := f.isptr[i - 1]?.getD false

/-- What field `i` adds to the size: nothing when it is undefined or an inline pointer-free field,
otherwise the recursive count `k i`. -/
def fieldAdd (f : DTFacts) (fv : Nat → Option Val) (pf : Nat → Bool) (k : Nat → Nat) (i : Nat) : Nat :=
  match fv i with
  | none => 0
  | some _ => if fieldIsptr f i = false ∧ pf i = true then 0 else k i

/-- What the calls in the field loop of `count_const_size(x, ...)` answer: field `i` is `fv i`
(`none` when undefined), the type of an inline field value is pointer-free when `pf i`, and the
recursive count of a field that is counted is `k i`. -/
structure FieldAnswers (n : Nat) (E : CEnv) (C : ConstLayout) (x : Val) (f : DTFacts)
    (fv : Nat → Option Val) (pf : Nat → Bool) (k : Nat → Nat) : Prop where
  field : ∀ i, 1 ≤ i → i ≤ f.isptr.length → Gives (fieldOf C x i) (fv i)
  pfree : ∀ i v, 1 ≤ i → i ≤ f.isptr.length → fv i = some v → fieldIsptr f i = false →
    Returns (C.facts (typeOf v)) (fun g => g.pointerfree = pf i)
  count : ∀ i v, 1 ≤ i → i ≤ f.isptr.length → fv i = some v →
    ¬(fieldIsptr f i = false ∧ pf i = true) → Gives (countConstSize n E C v (fieldIsptr f i)) (k i)

/-- `x` is none of `Type`, `TypeName`, `Symbol` (the first line of `count_const_size`). -/
def NotShortcut (x : Val) : Prop :=
  (x.isType || typeNameOf x == "Core.TypeName" || x.isSymbol) = false

/-- `x` passes the mutability checks of `count_const_size`: it is immutable, or mutable but not a
`GenericMemory`, `String`, `SimpleVector`, `Module`, `Method` or `CodeInstance`, with every field
`const` (a type mutable only for identity). -/
def PassesMutable (E : CEnv) (x : Val) (f : DTFacts) : Prop :=
  Gives (ismutable E x) false ∨
  (Gives (ismutable E x) true ∧
    (typeNameOf x == "Core.GenericMemory" || typeNameOf x == "Core.String" ||
      typeNameOf x == "Core.SimpleVector") = false ∧
    (x.isModule || typeNameOf x == "Core.Method" || typeNameOf x == "Core.CodeInstance") = false ∧
    ∀ j < f.isconst.length, f.isconst[j]?.getD false = true)

/-- Every branch of `count_const_size(x, count_self)` (`Compiler/src/utilities.jl:37-75`), given
what the calls it makes answer. `Type`, `TypeName` and `Symbol` count 0. A mutable
`GenericMemory`, `String` or `SimpleVector` is too large (`MAX_INLINE_CONST_SIZE + 1`); a
`Module`, `Method` or `CodeInstance` counts `sizeof(Ptr{Cvoid}) = 8`; any other mutable object with
a non-`const` field is too large. An `isbits` value counts its size. Every other object counts
`sizeof(typeof(x))` when `count_self`, plus the counts of its pointer fields and of its inline
fields that are not pointer-free, capped: the sum when it is at most `MAX_INLINE_CONST_SIZE`, and
`MAX_INLINE_CONST_SIZE + 1` otherwise. -/
def CountConstSizeExact : Prop :=
  (∀ n E C x cs, (x.isType || typeNameOf x == "Core.TypeName" || x.isSymbol) = true →
    Gives (countConstSize (n + 1) E C x cs) 0) ∧
  (∀ n E C x cs, NotShortcut x → Gives (ismutable E x) true →
    (typeNameOf x == "Core.GenericMemory" || typeNameOf x == "Core.String" ||
      typeNameOf x == "Core.SimpleVector") = true →
    Gives (countConstSize (n + 1) E C x cs) (MAX_INLINE_CONST_SIZE + 1)) ∧
  (∀ n E C x cs, NotShortcut x → Gives (ismutable E x) true →
    (typeNameOf x == "Core.GenericMemory" || typeNameOf x == "Core.String" ||
      typeNameOf x == "Core.SimpleVector") = false →
    (x.isModule || typeNameOf x == "Core.Method" || typeNameOf x == "Core.CodeInstance") = true →
    Gives (countConstSize (n + 1) E C x cs) 8) ∧
  (∀ n E C x cs f, NotShortcut x → Gives (ismutable E x) true →
    (typeNameOf x == "Core.GenericMemory" || typeNameOf x == "Core.String" ||
      typeNameOf x == "Core.SimpleVector") = false →
    (x.isModule || typeNameOf x == "Core.Method" || typeNameOf x == "Core.CodeInstance") = false →
    Gives (C.facts (typeOf x)) f → (∃ j < f.isconst.length, f.isconst[j]?.getD false = false) →
    Gives (countConstSize (n + 1) E C x cs) (MAX_INLINE_CONST_SIZE + 1)) ∧
  (∀ n E C x cs f, NotShortcut x → PassesMutable E x f → Gives (C.facts (typeOf x)) f →
    f.isbits = true → Gives (countConstSize (n + 1) E C x cs) f.size) ∧
  (∀ n E C x cs f fv pf k, NotShortcut x → PassesMutable E x f → Gives (C.facts (typeOf x)) f →
    f.isbits = false → FieldAnswers n E C x f fv pf k →
    Gives (countConstSize (n + 1) E C x cs)
      (capSize ((if cs then f.size else 0) + sumTo (fieldAdd f fv pf k) f.isptr.length)))

/-- Monotonicity of `count_const_size` in `count_self` (`Compiler/src/utilities.jl:37-75`): leaving
out the object's own size never gives a larger count. With the same answers from the calls the
function makes, every result of `count_const_size(x, false)` is at most every result of
`count_const_size(x, true)`. -/
def CountConstSizeSelfMono : Prop :=
  ∀ n E C x f fv pf k, NotShortcut x → PassesMutable E x f → Gives (C.facts (typeOf x)) f →
    FieldAnswers n E C x f fv pf k →
    ∀ s a s' t b t', (countConstSize (n + 1) E C x false).run s = .ok (a, s') →
      (countConstSize (n + 1) E C x true).run t = .ok (b, t') → a ≤ b

theorem bool_absurd {b : Bool} (h1 : b = true) (h2 : b = false) : False := by simp_all

set_option hygiene false in
/-- The `isbits` exit of `count_const_size`, after the mutability checks. -/
macro "ccs_bits" : tactic => `(tactic| (
  refine returns_bind hf (fun f' hf' => ?_)
  subst f'
  exact returns_ite (fun _ => returns_pure rfl) (fun hb => absurd hbits hb)))

set_option hygiene false in
/-- The field loop of `count_const_size`, after the mutability checks, for a value that is not
`isbits`. -/
macro "ccs_sum" : tactic => `(tactic| (
  refine returns_bind hf (fun f' hf' => ?_)
  subst f'
  generalize (if cs = true then f.size else 0) = base
  refine returns_ite (fun hb => absurd hb (by simp [hbits])) (fun _ => ?_)
  refine returns_ite (fun hsz => returns_pure ?_) (fun hsz => ?_)
  · unfold capSize; rw [if_neg (by omega)]
  rw [range_size_succ]
  refine returns_bind (returns_forIn_range'_done
    (fun i b => b.1 = none ∧ b.2 = base + sumTo (fieldAdd f fv pf k) (i - 1) ∧
       b.2 ≤ MAX_INLINE_CONST_SIZE)
    (fun b => b.1 = some (MAX_INLINE_CONST_SIZE + 1) ∧
       MAX_INLINE_CONST_SIZE < base + sumTo (fieldAdd f fv pf k) f.isptr.length)
    _ _ _ ?_ _ ⟨rfl, by simp [sumTo], by omega⟩) (fun r hr => ?_)
  · intro i b hi1 hi2 ⟨hb1, hb2, hb3⟩
    refine returns_bind (hA.field i hi1 (by omega)) (fun o ho => ?_)
    subst o
    have hsum : sumTo (fieldAdd f fv pf k) (i + 1 - 1) =
        sumTo (fieldAdd f fv pf k) (i - 1) + fieldAdd f fv pf k i := by
      rw [show i + 1 - 1 = (i - 1) + 1 by omega]; simp only [sumTo]; rw [show i - 1 + 1 = i by omega]
    have hmono : sumTo (fieldAdd f fv pf k) (i + 1 - 1) ≤ sumTo (fieldAdd f fv pf k) f.isptr.length :=
      sumTo_mono _ (by omega)
    split
    · rename_i v hv
      have hadd' : ¬(fieldIsptr f i = false ∧ pf i = true) → fieldAdd f fv pf k i = k i := by
        intro h; simp only [fieldAdd, hv]; rw [if_neg h]
      refine returns_ite (fun hnp => ?_) (fun hnp => ?_)
      · have hip : fieldIsptr f i = false := by simpa [fieldIsptr] using hnp
        refine returns_bind (hA.pfree i v hi1 (by omega) hv hip) (fun g hg => ?_)
        refine returns_ite (fun hpf => returns_pure ⟨rfl, ?_, hb3⟩) (fun hpf => ?_)
        · have h0 : fieldAdd f fv pf k i = 0 := by
            have : pf i = true := by rw [← hg]; exact hpf
            simp [fieldAdd, hv, hip, this]
          rw [hsum, h0]; omega
        have hnot : ¬(fieldIsptr f i = false ∧ pf i = true) := by
          rintro ⟨-, h⟩; rw [← hg] at h; exact hpf h
        refine returns_bind (hA.count i v hi1 (by omega) hv hnot) (fun kk hk => ?_)
        subst kk
        have ha := hadd' hnot
        refine returns_ite (fun hgt => returns_pure ⟨rfl, ?_⟩) (fun hle => returns_pure ⟨rfl, ?_, ?_⟩)
        · rw [hsum, ha] at hmono; omega
        · rw [hsum, ha]; omega
        · omega
      · have hip : fieldIsptr f i = true := by simpa [fieldIsptr] using hnp
        have hnot : ¬(fieldIsptr f i = false ∧ pf i = true) := by simp [hip]
        refine returns_bind (hA.count i v hi1 (by omega) hv hnot) (fun kk hk => ?_)
        subst kk
        have ha := hadd' hnot
        refine returns_ite (fun hgt => returns_pure ⟨rfl, ?_⟩) (fun hle => returns_pure ⟨rfl, ?_, ?_⟩)
        · rw [hsum, ha] at hmono; omega
        · rw [hsum, ha]; omega
        · omega
    · rename_i hv
      have hn : fv i = none := by
        cases h : fv i with
        | none => rfl
        | some v => exact (hv v h).elim
      have h0 : fieldAdd f fv pf k i = 0 := by simp [fieldAdd, hn]
      exact returns_pure ⟨rfl, by rw [hsum, h0]; omega, hb3⟩
  rcases hr with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · rw [h1]
    refine returns_pure ?_
    simp only [Nat.add_sub_cancel_left] at h2
    rw [h2]; unfold capSize
    rw [if_pos (by omega)]
  · rw [h1]
    refine returns_pure ?_
    unfold capSize; rw [if_neg (by omega)]))

theorem countConstSize_sum (n E C x cs f fv pf k) (hns : NotShortcut x) (hpm : PassesMutable E x f)
    (hf : Gives (C.facts (typeOf x)) f) (hbits : f.isbits = false) (hA : FieldAnswers n E C x f fv pf k) :
    Gives (countConstSize (n + 1) E C x cs)
      (capSize ((if cs then f.size else 0) + sumTo (fieldAdd f fv pf k) f.isptr.length)) := by
  rw [countConstSize]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine returns_ite (fun h => (bool_absurd h hns).elim) (fun _ => ?_)
  rcases hpm with hm | ⟨hm, hg, hmod, hall⟩
  · refine returns_bind hm (fun b hb => ?_)
    subst b
    simp only [Bool.false_eq_true, ite_false]
    ccs_sum
  · refine returns_bind hm (fun b hb => ?_)
    subst b
    simp only [ite_true, hg, hmod, Bool.false_eq_true, ite_false]
    refine returns_bind hf (fun f' hf' => ?_)
    subst f'
    rw [range_size_succ]
    refine returns_bind (returns_forIn_range'_done (fun _ b => b.1 = none) (fun _ => False) _ _ _ ?_ _ rfl)
      (fun r hr => ?_)
    · intro i b hi1 hi2 hb
      refine returns_ite (fun h => ?_) (fun _ => returns_pure rfl)
      exfalso
      have := hall (i - 1) (by omega)
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
      rw [this] at h; cases h
    rcases hr with h1 | h1
    · rw [h1]
      ccs_sum
    · exact h1.elim

theorem countConstSize_bits (n E C x cs f) (hns : NotShortcut x) (hpm : PassesMutable E x f)
    (hf : Gives (C.facts (typeOf x)) f) (hbits : f.isbits = true) :
    Gives (countConstSize (n + 1) E C x cs) f.size := by
  rw [countConstSize]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine returns_ite (fun h => (bool_absurd h hns).elim) (fun _ => ?_)
  rcases hpm with hm | ⟨hm, hg, hmod, hall⟩
  · refine returns_bind hm (fun b hb => ?_)
    subst b
    simp only [Bool.false_eq_true, ite_false]
    ccs_bits
  · refine returns_bind hm (fun b hb => ?_)
    subst b
    simp only [ite_true, hg, hmod, Bool.false_eq_true, ite_false]
    refine returns_bind hf (fun f' hf' => ?_)
    subst f'
    rw [range_size_succ]
    refine returns_bind (returns_forIn_range'_done (fun _ b => b.1 = none) (fun _ => False) _ _ _ ?_ _ rfl)
      (fun r hr => ?_)
    · intro i b hi1 hi2 hb
      refine returns_ite (fun h => ?_) (fun _ => returns_pure rfl)
      exfalso
      have := hall (i - 1) (by omega)
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
      rw [this] at h; cases h
    rcases hr with h1 | h1
    · rw [h1]
      ccs_bits
    · exact h1.elim

theorem countConstSizeExact_proven : CountConstSizeExact := by
  refine ⟨fun n E C x cs h => ?_, fun n E C x cs hns hm hg => ?_, fun n E C x cs hns hm hg hmod => ?_,
    fun n E C x cs f hns hm hg hmod hf hj => ?_, fun n E C x cs f hns hpm hf hbits => countConstSize_bits n E C x cs f hns hpm hf hbits,
    fun n E C x cs f fv pf k hns hpm hf hbits hA => countConstSize_sum n E C x cs f fv pf k hns hpm hf hbits hA⟩
  · rw [countConstSize]
    exact returns_ite (fun _ => returns_pure rfl) (fun h' => absurd h h')
  · rw [countConstSize]
    refine returns_ite (fun h => (bool_absurd h hns).elim) (fun _ => ?_)
    refine returns_bind hm (fun b hb => ?_)
    subst b
    simp only [ite_true, hg]
    exact returns_pure rfl
  · rw [countConstSize]
    refine returns_ite (fun h => (bool_absurd h hns).elim) (fun _ => ?_)
    refine returns_bind hm (fun b hb => ?_)
    subst b
    simp only [ite_true, hg, hmod, Bool.false_eq_true, ite_false]
    exact returns_pure rfl
  · rw [countConstSize]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    refine returns_ite (fun h => (bool_absurd h hns).elim) (fun _ => ?_)
    refine returns_bind hm (fun b hb => ?_)
    subst b
    simp only [ite_true, hg, hmod, Bool.false_eq_true, ite_false]
    refine returns_bind hf (fun f' hf' => ?_)
    subst f'
    rw [range_size_succ]
    refine returns_bind (returns_forIn_range'_done
      (fun i b => b.1 = none ∧ ∀ j < i - 1, f.isconst[j]?.getD false = true)
      (fun b => b.1 = some (MAX_INLINE_CONST_SIZE + 1)) _ _ _ ?_ _ ⟨rfl, fun j hj => by omega⟩)
      (fun r hr => ?_)
    · intro i b hi1 hi2 ⟨hb1, hb2⟩
      refine returns_ite (fun h => returns_pure rfl) (fun h => returns_pure ⟨rfl, fun j hj => ?_⟩)
      rcases Nat.lt_or_eq_of_le (show j ≤ i - 1 by omega) with hj' | hj'
      · exact hb2 j hj'
      · subst hj'; simpa using h
    rcases hr with ⟨h1, h2⟩ | h1
    · exfalso
      obtain ⟨j, hj, hjf⟩ := hj
      have := h2 j (by omega)
      rw [hjf] at this; cases this
    · rw [h1]; exact returns_pure rfl

theorem countConstSizeSelfMono_proven : CountConstSizeSelfMono := by
  intro n E C x f fv pf k hns hpm hf hA s a s' t b t' ha hb
  cases hbits : f.isbits
  · have e1 := countConstSize_sum n E C x false f fv pf k hns hpm hf hbits hA _ _ _ ha
    have e2 := countConstSize_sum n E C x true f fv pf k hns hpm hf hbits hA _ _ _ hb
    subst e1 e2
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.zero_add]
    unfold capSize
    split <;> split <;> omega
  · have e1 := countConstSize_bits n E C x false f hns hpm hf hbits _ _ _ ha
    have e2 := countConstSize_bits n E C x true f hns hpm hf hbits _ _ _ hb
    omega

/-! ## `pick_const_args!` position by position -/

theorem returns_res {α : Type} (m : CM α) : Returns m (Res m) := fun s _ s' h => ⟨s, s', h⟩

theorem range_size (a b : Nat) : Std.Legacy.Range.size [a:b] = b - a := by
  simp [Std.Legacy.Range.size]

theorem getElem?_set!' {α : Type} (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v)[j]? = if i = j then (if i < a.size then some v else none) else a[j]? := by
  simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]

theorem returns_setOpt' (a : Array (Option LElt)) (i : Nat) (x : LElt) :
    Returns (setOpt a i x) (fun r => 1 ≤ i ∧ i ≤ a.size ∧ r = a.set! (i - 1) (some x)) := by
  unfold setOpt
  refine returns_ite (fun h => returns_pure ?_) (fun _ => returns_throw _ _)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2, rfl⟩

theorem returns_getOpt (a : Array (Option LElt)) (i : Nat) :
    Returns (getOpt a i) (fun x => a[i - 1]? = some (some x)) := by
  unfold getOpt
  split
  · rename_i x hx; exact returns_pure hx
  · exact returns_throw _ _
  · exact returns_throw _ _

theorem getElem?_resizeOpt (a : Array (Option LElt)) (k j : Nat) (hj : j < k) :
    (resizeOpt a k)[j]? = if j < a.size then a[j]? else some none := by
  unfold resizeOpt
  split
  · rw [Array.getElem?_extract]
    split
    · simp only [Nat.zero_add]; rw [if_pos (by omega)]
    · omega
  · rw [Array.getElem?_append]
    split
    · rfl
    · simp only [Array.getElem?_replicate]; rw [if_pos (by omega)]

theorem getElem?_mapSome (given : List LElt) (j : Nat) (hj : j < given.length) :
    ((given.map some).toArray)[j]? = some (some given[j]!) := by
  simp [hj]

/-- A loop `for i in a:(a + k - 1); g[i] = v; end` over the working vector. -/
theorem fill_loop (v : LElt) : ∀ (k a : Nat) (g : Array (Option LElt)),
    Returns (forIn (List.range' a k) g (fun i r => do
        let g ← setOpt r i v
        pure (ForInStep.yield g)))
      (fun g' => g'.size = g.size ∧ ∀ j, g'[j]? = if a ≤ j + 1 ∧ j + 1 < a + k then some (some v) else g[j]?) := by
  intro k
  induction k with
  | zero =>
    intro a g
    simp only [List.range'_zero, List.forIn_nil]
    exact returns_pure ⟨rfl, fun j => by rw [if_neg (by omega)]⟩
  | succ k ih =>
    intro a g
    simp only [List.range'_succ, List.forIn_cons, bind_assoc, pure_bind]
    refine returns_bind (returns_setOpt' _ _ _) (fun g1 ⟨h1, h2, hg1⟩ => ?_)
    subst hg1
    refine returns_mono (ih (a + 1) _) (fun g' ⟨hs, hg⟩ => ⟨by rw [hs, Array.size_set!], fun j => ?_⟩)
    rw [hg j, getElem?_set!']
    by_cases hj : a ≤ j + 1 ∧ j + 1 < a + (k + 1)
    · rw [if_pos hj]
      by_cases hj' : a + 1 ≤ j + 1 ∧ j + 1 < a + 1 + k
      · rw [if_pos hj']
      · rw [if_neg hj', if_pos (by omega), if_pos (by omega)]
    · rw [if_neg hj, if_neg (by omega), if_neg (by omega)]

/-- The argument type `pick_const_args!` holds at position `j` (1-based) before its main loop: the
given argument type, or the given `Vararg`'s element type at and after the given `Vararg`. -/
def keyGiven (given : List LElt) (j : Nat) : LElt :=
  if given.getLast!.isVarargElt = true ∧ given.length ≤ j then unwrapvaLElt given.getLast! else given[j - 1]!

/-- `x` can be key position `j`: a result of `pick_const_arg` on `keyGiven given j` and
`argtype_by_index(cache_argtypes, j)`. -/
def PickAt (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice) (given ca : List LElt) (j : Nat) (x : LElt) : Prop :=
  ∃ c, Res (argtypeByIndex ca j) c ∧ Res (pickConstArg ops n E L (keyGiven given j) c) x

/-- The number of key positions the main loop of `pick_const_args!` fills: the key length, less the
final `Vararg` when both lists end in one. -/
def keyFixed (given ca : List LElt) : Nat :=
  if given.getLast!.isVarargElt = true ∧ ca.getLast!.isVarargElt = true then keyLength given ca - 1
  else keyLength given ca

theorem pick_loop (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice) (given ca : List LElt) (N : Nat)
    (g0 : Array (Option LElt)) (hsize : N ≤ g0.size)
    (hinit : ∀ j, 1 ≤ j → j ≤ N → g0[j - 1]? = some (some (keyGiven given j))) :
    Returns (forIn (List.range' 1 N) g0 (fun i r => do
        let givenArgtype ← getOpt r i
        let cacheArgtype ← argtypeByIndex ca (i : Int)
        let d ← pickConstArg ops n E L givenArgtype cacheArgtype
        let g ← setOpt r i d
        pure (ForInStep.yield g)))
      (fun g => g.size = g0.size ∧
        (∀ j, 1 ≤ j → j ≤ N → ∃ x, PickAt ops n E L given ca j x ∧ g[j - 1]? = some (some x)) ∧
        ∀ j, N ≤ j → g[j]? = g0[j]?) := by
  let I : Nat → Array (Option LElt) → Prop := fun i g => g.size = g0.size ∧
    (∀ j, 1 ≤ j → j < i → ∃ x, PickAt ops n E L given ca j x ∧ g[j - 1]? = some (some x)) ∧
    (∀ j, i ≤ j → j ≤ N → g[j - 1]? = some (some (keyGiven given j))) ∧
    ∀ j, N ≤ j → g[j]? = g0[j]?
  refine returns_mono (returns_forIn_range'_done I (fun _ => False) _ N 1 ?_ g0
    ⟨rfl, fun j h1 h2 => by omega, fun j h1 h2 => hinit j (by omega) h2, fun _ _ => rfl⟩) ?_
  · intro i g hi1 hi2 ⟨hs, hpre, hsuf, hrest⟩
    refine returns_bind (returns_getOpt _ _) (fun x0 hx0 => ?_)
    have hx0' : x0 = keyGiven given i := by
      have := hsuf i (Nat.le_refl _) (by omega); rw [this] at hx0; simpa using hx0.symm
    subst hx0'
    refine returns_bind (returns_res _) (fun c hc => ?_)
    refine returns_bind (returns_res _) (fun x hx => ?_)
    refine returns_bind (returns_setOpt' _ _ _) (fun g' ⟨h1, h2, hg'⟩ => ?_)
    subst hg'
    refine returns_pure ⟨by rw [Array.size_set!, hs], fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_eq_of_le (show j ≤ i by omega) with hj | hj
      · obtain ⟨y, hy, hgy⟩ := hpre j hj1 hj
        refine ⟨y, hy, ?_⟩
        rw [getElem?_set!', if_neg (by omega)]; exact hgy
      · subst hj
        refine ⟨x, ⟨c, hc, hx⟩, ?_⟩
        rw [getElem?_set!', if_pos rfl, if_pos (by omega)]
    · rw [getElem?_set!', if_neg (by omega)]; exact hsuf j (by omega) hj2
    · rw [getElem?_set!', if_neg (by omega)]; exact hrest j hj
  · rintro g (⟨hs, hpre, -, hrest⟩ | h)
    · exact ⟨hs, fun j h1 h2 => hpre j h1 (by omega), hrest⟩
    · exact h.elim

theorem mapM_unwrap (f : Option LElt → CM LElt) (hf : ∀ e s, (f (some e)).run s = .ok (e, s)) :
    ∀ (l : List (Option LElt)) s r s', (l.mapM f).run s = .ok (r, s') →
      ∀ (j : Nat) (x : LElt), l[j]? = some (some x) → r[j]? = some x
  | [], _, _, _, _, j, x, hj => by simp at hj
  | a :: l, s, r, s', h, j, x, hj => by
    simp only [List.mapM_cons] at h
    obtain ⟨b, s₁, h1, h2⟩ := run_bind_inv h
    obtain ⟨bs, s₂, h3, h4⟩ := run_bind_inv h2
    cases h4
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [hf x s] at h1
      cases h1; rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      exact mapM_unwrap f hf l s₁ bs _ h3 j x hj

/-- `pick_const_args!(𝕃, given_argtypes, cache_argtypes)` (`Compiler/src/inferenceresult.jl:64-98`)
position by position. At each fixed key position `j` the key holds a result of `pick_const_arg` on
the given argument type there (the element type of the given `Vararg` at and after it) and on
`argtype_by_index(cache_argtypes, j)`. When both lists end in a `Vararg`, the last key position is
`Vararg{pick_const_arg(𝕃, unwrapva(given_va), unwrapva(cache_va))}`. With `ConstpropKeyLength`
this pins the whole key. -/
def PickConstArgsExact : Prop :=
  ∀ ops n E L given ca, Returns (pickConstArgs ops n E L given ca) fun r =>
    (∀ j, 1 ≤ j → j ≤ keyFixed given ca → ∃ x, PickAt ops n E L given ca j x ∧ r[j - 1]? = some x) ∧
    (given ≠ [] → ca ≠ [] → given.getLast!.isVarargElt = true → ca.getLast!.isVarargElt = true →
      ∃ x, Res (pickConstArg ops n E L (unwrapvaLElt given.getLast!) (unwrapvaLElt ca.getLast!)) x ∧
        ∃ v, Res (varargOfElt n E x) v ∧ r[keyLength given ca - 1]? = some v)

theorem unwrap_some (e : LElt) (s : Nat) :
    ((fun x => match x with
      | some e => (pure e : CM LElt)
      | none => jlThrow "UndefRefError" "given_argtypes") (some e)).run s = .ok (e, s) := rfl

set_option hygiene false in
/-- The end of `pick_const_args!`: the main loop from `g0`, then the unwrap of the vector. -/
macro "pick_finish" N:term : tactic => `(tactic| (
  refine returns_bind (pick_loop ops n E L given ca $N _ (by omega) hinit) (fun g4 ⟨hs4, hpre4, hrest4⟩ => ?_)
  intro s r s' h
  have hun := mapM_unwrap _ (fun e s => rfl) _ s r s' h
  have hlen := (returns_mapM_length _ g4.toList) s r s' h
  simp only [Array.length_toList] at hlen
  refine ⟨fun j hj1 hj2 => ?_, fun hg hc hgv' hcv' => ?_⟩))

theorem pickConstArgsExact_proven : PickConstArgsExact := by
  intro ops n E L given ca
  unfold pickConstArgs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size, Nat.add_sub_cancel]
  refine returns_ite (fun h0 => returns_pure ⟨fun j hj1 hj2 => ?_, fun hg hc _ _ => ?_⟩) (fun h0 => ?_)
  · have : keyFixed given ca = 0 := by
      unfold keyFixed keyLength; rw [if_pos h0]; split <;> rfl
    omega
  · exfalso
    simp only [Bool.or_eq_true, beq_iff_eq, List.length_eq_zero_iff] at h0
    rcases h0 with h0 | h0 <;> contradiction
  have hne : given ≠ [] ∧ ca ≠ [] := by
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h0
    exact ⟨fun h => h0.1 (by simp [h]), fun h => h0.2 (by simp [h])⟩
  have hng : 0 < given.length := List.length_pos_iff.mpr hne.1
  have hnc : 0 < ca.length := List.length_pos_iff.mpr hne.2
  refine returns_ite (fun hgv => ?_) (fun hgv => ?_)
  · refine returns_ite (fun hcv => ?_) (fun hcv => ?_)
    · -- Both lists end in `Vararg`.
      have hK : keyLength given ca = max (given.length - 1) (ca.length - 1) + 1 := by
        unfold keyLength; rw [if_neg h0, if_pos hgv, if_pos hcv]
      have hF : keyFixed given ca = max (given.length - 1) (ca.length - 1) := by
        unfold keyFixed; rw [if_pos ⟨hgv, hcv⟩, hK]; rfl
      refine returns_bind (returns_res _) (fun picked hp => ?_)
      refine returns_bind (returns_res _) (fun vv hvv => ?_)
      refine returns_bind (returns_setOpt' _ _ _) (fun g2 ⟨_, _, hg2⟩ => ?_)
      subst hg2
      refine returns_bind (fill_loop _ _ _ _) (fun g3 ⟨hs3, hg3⟩ => ?_)
      have hsz : (resizeOpt (List.map some given).toArray (max (given.length - 1) (ca.length - 1) + 1)).size =
          max (given.length - 1) (ca.length - 1) + 1 := resizeOpt_size _ _
      have hinit : ∀ j, 1 ≤ j → j ≤ max (given.length - 1) (ca.length - 1) →
          g3[j - 1]? = some (some (keyGiven given j)) := by
        intro j hj1 hj2
        rw [hg3]
        by_cases hj : given.length ≤ j
        · rw [if_pos (by omega)]; unfold keyGiven; rw [if_pos ⟨hgv, hj⟩]
        · rw [if_neg (by omega), getElem?_set!', if_neg (by omega), getElem?_resizeOpt _ _ _ (by omega),
            if_pos (by simp; omega), getElem?_mapSome _ _ (by omega)]
          unfold keyGiven; rw [if_neg (by omega)]
      have hs3' : max (given.length - 1) (ca.length - 1) ≤ g3.size := by
        rw [hs3, Array.size_set!, hsz]; omega
      pick_finish (max (given.length - 1) (ca.length - 1))
      · rw [hF] at hj2
        obtain ⟨x, hx, hgx⟩ := hpre4 j hj1 hj2
        exact ⟨x, hx, hun (j - 1) x (by rw [Array.getElem?_toList]; exact hgx)⟩
      · refine ⟨picked, hp, vv, hvv, ?_⟩
        rw [hK, Nat.add_sub_cancel]
        refine hun _ vv ?_
        rw [Array.getElem?_toList, hrest4 _ (Nat.le_refl _), hg3, if_neg (by omega), getElem?_set!', hsz,
          if_pos (by omega), if_pos (by omega)]
    · -- Only the given list ends in `Vararg`.
      have hK : keyLength given ca = ca.length := by
        unfold keyLength; rw [if_neg h0, if_pos hgv, if_neg hcv]
      have hF : keyFixed given ca = ca.length := by
        unfold keyFixed; rw [if_neg (fun h => hcv h.2), hK]
      refine returns_bind (fill_loop _ _ _ _) (fun g3 ⟨hs3, hg3⟩ => ?_)
      have hinit : ∀ j, 1 ≤ j → j ≤ ca.length → g3[j - 1]? = some (some (keyGiven given j)) := by
        intro j hj1 hj2
        rw [hg3]
        by_cases hj : given.length ≤ j
        · rw [if_pos (by omega)]; unfold keyGiven; rw [if_pos ⟨hgv, hj⟩]
        · rw [if_neg (by omega), getElem?_resizeOpt _ _ _ (by omega),
            if_pos (by simp; omega), getElem?_mapSome _ _ (by omega)]
          unfold keyGiven; rw [if_neg (by omega)]
      have hs3' : ca.length ≤ g3.size := by rw [hs3, resizeOpt_size]; exact Nat.le_refl _
      pick_finish ca.length
      · rw [hF] at hj2
        obtain ⟨x, hx, hgx⟩ := hpre4 j hj1 hj2
        exact ⟨x, hx, hun (j - 1) x (by rw [Array.getElem?_toList]; exact hgx)⟩
      · exact absurd hcv' hcv
  · have hkg : ∀ j, 1 ≤ j → j ≤ given.length →
        ((List.map some given).toArray)[j - 1]? = some (some (keyGiven given j)) := by
      intro j hj1 hj2
      rw [getElem?_mapSome _ _ (by omega)]
      unfold keyGiven; rw [if_neg (fun h => hgv h.1)]
    have hK : keyLength given ca = given.length := by
      unfold keyLength; rw [if_neg h0, if_neg hgv]
    have hF : keyFixed given ca = given.length := by
      unfold keyFixed; rw [if_neg (fun h => hgv h.1), hK]
    have hs0 : given.length ≤ ((List.map some given).toArray).size := by simp
    refine returns_ite (fun hcv => ?_) (fun hcv => ?_)
    · have hinit := hkg
      pick_finish given.length
      · rw [hF] at hj2
        obtain ⟨x, hx, hgx⟩ := hpre4 j hj1 hj2
        exact ⟨x, hx, hun (j - 1) x (by rw [Array.getElem?_toList]; exact hgx)⟩
      · exact absurd hgv' hgv
    · refine returns_ite (fun _ => returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim))
        (fun _ => ?_)
      have hinit := hkg
      pick_finish given.length
      · rw [hF] at hj2
        obtain ⟨x, hx, hgx⟩ := hpre4 j hj1 hj2
        exact ⟨x, hx, hun (j - 1) x (by rw [Array.getElem?_toList]; exact hgx)⟩
      · exact absurd hgv' hgv

/-! ## `va_process_argtypes` position by position -/

/-- The `Conditional` step of `va_process_argtypes` on one argument type: when `c` (the lattice has
`Conditional`s, and for the fixed arguments the method is varargs) holds, a `Conditional` on a slot
past the fixed arguments is widened; anything else is kept. -/
def CondStep (c : Bool) (nf : Int) (a y : LElt) : Prop :=
  match a with
  | .conditional slot .. => if c = true ∧ slot > nf then Res (widenconditional a) y else y = a
  | _ => y = a

/-- The `MustAlias` step, the same way. -/
def AliasStep (c : Bool) (nf : Int) (a y : LElt) : Prop :=
  match a with
  | .mustAlias slot .. => if c = true ∧ slot > nf then Res (widenmustalias a) y else y = a
  | _ => y = a

/-- The `Conditional` step and then the `MustAlias` step. -/
def VaWidened (c1 c2 : Bool) (nf : Int) (a x : LElt) : Prop := ∃ a1, CondStep c1 nf a a1 ∧ AliasStep c2 nf a1 x

theorem vaw_intro {c1 c2 : Bool} {nf : Int} {a a1 x : LElt} (h1 : CondStep c1 nf a a1) (h2 : AliasStep c2 nf a1 x) :
    VaWidened c1 c2 nf a x := ⟨a1, h1, h2⟩

theorem cond_yes {c : Bool} {nf slot sd : Int} {t e : LElt} {d : Bool} {y : LElt} (hc : c = true) (hs : slot > nf)
    (h : Res (widenconditional (.conditional slot sd t e d)) y) : CondStep c nf (.conditional slot sd t e d) y := by
  simp only [CondStep]; rw [if_pos ⟨hc, hs⟩]; exact h
theorem cond_noslot {c : Bool} {nf slot sd : Int} {t e : LElt} {d : Bool} (hs : ¬ slot > nf) :
    CondStep c nf (.conditional slot sd t e d) (.conditional slot sd t e d) := by
  simp [CondStep, hs]
theorem cond_off {c : Bool} {nf : Int} {a : LElt} (hc : ¬ c = true) : CondStep c nf a a := by
  cases a <;> simp [CondStep, hc]
theorem cond_other {c : Bool} {nf : Int} {a : LElt}
    (h : ∀ slot sd t e d, a = .conditional slot sd t e d → False) : CondStep c nf a a := by
  cases a <;> simp only [CondStep]
  exact (h _ _ _ _ _ rfl).elim
theorem alias_yes {c : Bool} {nf slot sd fi : Int} {vt ft : LElt} {y : LElt} (hc : c = true) (hs : slot > nf)
    (h : Res (widenmustalias (.mustAlias slot sd vt fi ft)) y) : AliasStep c nf (.mustAlias slot sd vt fi ft) y := by
  simp only [AliasStep]; rw [if_pos ⟨hc, hs⟩]; exact h
theorem alias_noslot {c : Bool} {nf slot sd fi : Int} {vt ft : LElt} (hs : ¬ slot > nf) :
    AliasStep c nf (.mustAlias slot sd vt fi ft) (.mustAlias slot sd vt fi ft) := by
  simp [AliasStep, hs]
theorem alias_off {c : Bool} {nf : Int} {a : LElt} (hc : ¬ c = true) : AliasStep c nf a a := by
  cases a <;> simp [AliasStep, hc]
theorem alias_other {c : Bool} {nf : Int} {a : LElt}
    (h : ∀ slot sd vt fi ft, a = .mustAlias slot sd vt fi ft → False) : AliasStep c nf a a := by
  cases a <;> simp only [AliasStep]
  exact (h _ _ _ _ _ rfl).elim

macro "cond_auto" : tactic => `(tactic| first
  | exact cond_yes (by assumption) (by assumption) (by assumption)
  | exact cond_noslot (by assumption)
  | exact cond_off (by assumption)
  | exact cond_other (by assumption))

macro "alias_auto" : tactic => `(tactic| first
  | exact alias_yes (by assumption) (by assumption) (by assumption)
  | exact alias_noslot (by assumption)
  | exact alias_off (by assumption)
  | exact alias_other (by assumption))

theorem returns_atIdx' (xs : List LElt) (i : Int) :
    Returns (atIdx xs i) (fun x => 1 ≤ i ∧ xs[(i - 1).toNat]? = some x) := by
  unfold atIdx
  refine returns_ite (fun _ => returns_throw _ _) (fun h => ?_)
  split
  · rename_i x hx; exact returns_pure ⟨by omega, hx⟩
  · exact returns_throw _ _

theorem returns_sliceIdx (xs : List LElt) (a b : Int) :
    Returns (sliceIdx xs a b) (fun ws => (a > b ∧ ws = []) ∨
      (a ≤ b ∧ 1 ≤ a ∧ b ≤ xs.length ∧ ws = (xs.drop (a - 1).toNat).take (b - a + 1).toNat)) := by
  unfold sliceIdx
  refine returns_ite (fun h => returns_pure (Or.inl ⟨h, rfl⟩)) (fun h => ?_)
  refine returns_ite (fun _ => returns_throw _ _) (fun h' => ?_)
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h'
  exact returns_pure (Or.inr ⟨by omega, by omega, by omega, rfl⟩)

/-- A widening loop of the tail of `va_process_argtypes`: step `k` touches only position
`nargs + k - 1`, and relates its old and new value by `W`. -/
theorem widen_loop (nargs : Nat) (W : LElt → LElt → Prop) (body : Nat → Array LElt → CM (ForInStep (Array LElt)))
    (hbody : ∀ k (s : Array LElt), Returns (body k s) (fun r => ∃ s', r = .yield s' ∧ s'.size = s.size ∧
      (∃ a y, s[nargs + k - 1]? = some a ∧ s'[nargs + k - 1]? = some y ∧ W a y) ∧ 1 ≤ nargs + k ∧
      ∀ j, j ≠ nargs + k - 1 → s'[j]? = s[j]?)) :
    ∀ m k0 (g : Array LElt), Returns (forIn (List.range' k0 m) g body)
      (fun g' => g'.size = g.size ∧ ∀ j < g.size, ∃ a y, g[j]? = some a ∧ g'[j]? = some y ∧
        (nargs + k0 ≤ j + 1 ∧ j + 1 < nargs + k0 + m → W a y) ∧
        (¬(nargs + k0 ≤ j + 1 ∧ j + 1 < nargs + k0 + m) → y = a)) := by
  intro m
  induction m with
  | zero =>
    intro k0 g
    simp only [List.range'_zero, List.forIn_nil]
    refine returns_pure ⟨rfl, fun j hj => ⟨g[j], g[j], by simp [hj], by simp [hj], fun h => by omega, fun _ => rfl⟩⟩
  | succ m ih =>
    intro k0 g
    simp only [List.range'_succ, List.forIn_cons]
    refine returns_bind (hbody k0 g) ?_
    rintro r ⟨s1, rfl, hs1, ⟨a0, y0, ha0, hy0, hw⟩, hk, hrest⟩
    refine returns_mono (ih (k0 + 1) s1) (fun g' ⟨hs', hg'⟩ => ⟨by rw [hs', hs1], fun j hj => ?_⟩)
    obtain ⟨a1, y1, ha1, hy1, hin, hout⟩ := hg' j (by omega)
    by_cases hji : j = nargs + k0 - 1
    · subst hji
      have := hout (by omega)
      subst this
      rw [hy0] at ha1; cases ha1
      exact ⟨a0, y0, ha0, hy1, fun _ => hw, fun h => absurd ⟨by omega, by omega⟩ h⟩
    · rw [hrest j hji] at ha1
      refine ⟨a1, y1, ha1, hy1, fun h => hin ⟨by omega, by omega⟩, fun h => hout (by omega)⟩

/-- `nargs - isva`, the number of fixed arguments, as `va_process_argtypes` compares slots with it. -/
def vaNfixed (nargs : Nat) (isva : Bool) : Int := (nargs : Int) - if isva = true then 1 else 0

/-- Where the tuple of trailing arguments starts: at the given `Vararg` when fewer than `nargs`
argument types end in one, at position `nargs` otherwise. -/
def vaLast (given : List LElt) (nargs : Nat) : Nat :=
  if given.length < nargs ∧ (given[given.length - 1]?.map LElt.isVarargElt) = some true then given.length else nargs

/-- `va_process_argtypes(𝕃, given_argtypes, nargs, isva, mi)` (`Compiler/src/inferenceresult.jl:111-160`)
position by position. Without `isva` and without a trailing `Vararg` the argument types come back
unchanged. Each fixed position `i ≤ nargs - isva` holds `argtype_by_index(given_argtypes, i)`, with a
`Conditional` or `MustAlias` on a slot past the fixed arguments widened when the method is varargs
and the lattice has them. For a varargs method, position `nargs` holds `tuple_tfunc` of the trailing
argument types from `vaLast` on, each widened the same way. -/
def VaProcessExact : Prop :=
  ∀ n E L given nargs isva, Returns (vaProcessArgtypes n E L given nargs isva) fun r =>
    (isva = false → (given.getLast?.map LElt.isVarargElt) ≠ some true → r = given) ∧
    (∀ i : Nat, 1 ≤ i → (i : Int) ≤ vaNfixed nargs isva → ∃ a x, Res (argtypeByIndex given i) a ∧
      VaWidened (isva && hasConditional L) (isva && hasMustalias L) (vaNfixed nargs isva) a x ∧ r[i - 1]? = some x) ∧
    (isva = true → ∃ ws x, Res (tupleTfunc n E L ws) x ∧ r[nargs - 1]? = some x ∧
      ws.length = given.length + 1 - vaLast given nargs ∧
      ∀ k a w, given[vaLast given nargs - 1 + k]? = some a → ws[k]? = some w →
        VaWidened (hasConditional L) (hasMustalias L) (vaNfixed nargs isva) a w)

theorem lt_of_getElem?_some_list {l : List LElt} {i : Nat} {x : LElt} (h : l[i]? = some x) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none hge] at h; cases h

theorem lt_of_getElem?_some {s : Array LElt} {i : Nat} {x : LElt} (h : s[i]? = some x) : i < s.size := by
  rw [← Array.getElem?_toList] at h
  have := lt_of_getElem?_some_list h
  simpa using this

theorem not_cond_of_vararg {a : LElt} (h : a.isVarargElt = true) :
    ∀ slot sd t e d, a = .conditional slot sd t e d → False := by
  intro slot sd t e d ha; subst ha; simp [LElt.isVarargElt] at h

theorem not_alias_of_vararg {a : LElt} (h : a.isVarargElt = true) :
    ∀ slot sd vt fi ft, a = .mustAlias slot sd vt fi ft → False := by
  intro slot sd vt fi ft ha; subst ha; simp [LElt.isVarargElt] at h

theorem va_leaf {L : Lattice} {isva : Bool} {nargs i : Nat} {given : List LElt} {b : Array (Option LElt)}
    {a x : LElt}
    (hI : b.size = nargs ∧ ∀ j, 1 ≤ j → j < i → ∃ a x, Res (argtypeByIndex given j) a ∧
      VaWidened (isva && hasConditional L) (isva && hasMustalias L) (vaNfixed nargs isva) a x ∧
      b[j - 1]? = some (some x))
    (hi1 : 1 ≤ i) (hlt : i - 1 < b.size) (ha : Res (argtypeByIndex given i) a)
    (hw : VaWidened (isva && hasConditional L) (isva && hasMustalias L) (vaNfixed nargs isva) a x) :
    (b.set! (i - 1) (some x)).size = nargs ∧ ∀ j, 1 ≤ j → j < i + 1 → ∃ a' x', Res (argtypeByIndex given j) a' ∧
      VaWidened (isva && hasConditional L) (isva && hasMustalias L) (vaNfixed nargs isva) a' x' ∧
      (b.set! (i - 1) (some x))[j - 1]? = some (some x') := by
  refine ⟨by rw [Array.size_set!, hI.1], fun j hj1 hj2 => ?_⟩
  rcases Nat.lt_or_eq_of_le (show j ≤ i by omega) with hj | hj
  · obtain ⟨a', x', h1, h2, h3⟩ := hI.2 j hj1 hj
    exact ⟨a', x', h1, h2, by rw [getElem?_set!', if_neg (by omega)]; exact h3⟩
  · subst hj
    exact ⟨a, x, ha, hw, by rw [getElem?_set!', if_pos rfl, if_pos hlt]⟩

theorem argtypeByIndex_nonva (given : List LElt) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ given.length)
    (hl : (given.getLast?.map LElt.isVarargElt) ≠ some true) :
    Res (argtypeByIndex given i) given[i - 1]! := by
  refine ⟨0, 0, ?_⟩
  have hne : given ≠ [] := by intro h; subst h; simp at hi2; omega
  have hlast : given[given.length - 1]? = given.getLast? := by
    rw [List.getLast?_eq_getElem?]
  obtain ⟨v, hv⟩ : ∃ v, given.getLast? = some v := by
    cases h : given.getLast? with
    | none => simp_all
    | some v => exact ⟨v, rfl⟩
  have hvv : v.isVarargElt = false := by
    rw [hv] at hl; simpa using hl
  unfold argtypeByIndex atIdx
  have h1 : ¬((given.length : Int) < 1) := by omega
  have h2 : ¬((i : Int) < 1) := by omega
  have h3 : ¬((i : Int) > given.length) := by omega
  have e1 : ((given.length : Int) - 1).toNat = given.length - 1 := by omega
  have e2 : ((i : Int) - 1).toNat = i - 1 := by omega
  have hgi : given[i - 1]? = some given[i - 1]! := by
    rw [List.getElem?_eq_getElem (by omega)]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show i - 1 < given.length by omega)]
  simp only [h1, h2, h3, e1, e2, ite_false, decide_false, Bool.false_eq_true, hlast, hv, hgi, pure_bind, hvv]
  rfl

set_option hygiene false in
/-- The end of the tail of `va_process_argtypes`: the slice of the widened list `G` from `st`, its
`tuple_tfunc`, and the result vector. Needs `hisva`, `hout`, `hvl : vaLast given nargs = st`,
`hGlen` and `hG`. -/
macro "va_finish" st:term : tactic => `(tactic| (
  refine returns_bind (returns_sliceIdx _ _ _) (fun ws hws => ?_)
  refine returns_bind (returns_res _) (fun tt htt => ?_)
  refine returns_ite (fun _ => returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim))
    (fun hn0 => ?_)
  have hn0' : nargs ≠ 0 := by simpa using hn0
  intro s r s' h
  have hun := mapM_unwrap _ (fun e s => rfl) _ s r s' h
  refine ⟨fun h => absurd h (by simp [hisva]), fun i hi1 hi2 => ?_, fun _ => ⟨ws, tt, htt, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, x, h1, h2, h3⟩ := hout.2 i hi1 hi2
    have hi3 : (i : Int) ≤ (nargs : Int) - 1 := by simpa [vaNfixed, hisva] using hi2
    refine ⟨a, x, h1, h2, hun _ _ ?_⟩
    rw [Array.getElem?_toList, getElem?_set!', if_neg (by omega)]
    exact h3
  · exact hun _ _ (by rw [Array.getElem?_toList, getElem?_set!', if_pos rfl, if_pos (by rw [hout.1]; omega)])
  · rw [hvl]
    rcases hws with ⟨hgt, rfl⟩ | ⟨hle, h1, h2, rfl⟩
    · simp; omega
    · simp only [List.length_take, List.length_drop, hGlen]; omega
  · intro k a w ha hw
    rw [hvl] at ha
    rcases hws with ⟨hgt, rfl⟩ | ⟨hle, h1, h2, rfl⟩
    · simp at hw
    · rw [List.getElem?_take, List.getElem?_drop] at hw
      split at hw
      · have e : ((($st : Nat) : Int) - 1).toNat = $st - 1 := by omega
        rw [e] at hw
        obtain ⟨a', y, ha', hy, hwid⟩ := hG ($st - 1 + k) (by
          have := lt_of_getElem?_some_list hw; rw [hGlen] at this; exact this)
        rw [ha] at ha'; cases ha'
        rw [hy] at hw; cases hw
        exact hwid (by omega)
      · cases hw))

set_option hygiene false in
/-- The body of the `Conditional` (or `MustAlias`) widening loop over the tail. -/
macro "va_body" yes:ident noslot:ident other:ident : tactic => `(tactic| (
  intro k s
  refine returns_bind (returns_atIdx' _ _) (fun x ⟨hi, hx⟩ => ?_)
  have hidx : ((nargs : Int) + (k : Int) - 1).toNat = nargs + k - 1 := by omega
  rw [hidx, Array.getElem?_toList] at hx
  have hlt := lt_of_getElem?_some hx
  split
  · refine returns_ite (fun hs => ?_) (fun hs => ?_)
    · refine returns_bind (returns_res _) (fun w hw => returns_pure ⟨_, rfl, by simp, ⟨_, w, hx,
        by rw [hidx, getElem?_set!', if_pos rfl, if_pos hlt], $yes (by assumption) hs hw⟩, by omega,
        fun j hj => by rw [hidx, getElem?_set!', if_neg (by omega)]⟩)
    · exact returns_pure ⟨s, rfl, rfl, ⟨_, _, hx, hx, $noslot hs⟩, by omega, fun _ _ => rfl⟩
  · exact returns_pure ⟨s, rfl, rfl, ⟨_, _, hx, hx, $other (by assumption)⟩, by omega, fun _ _ => rfl⟩))

set_option hygiene false in
/-- The tail of `va_process_argtypes` when the trailing arguments start at position `nargs`. -/
macro "va_nonva" : tactic => `(tactic| (
  have hm0 : ∀ j, j < given.length → nargs ≤ j + 1 →
      j + 1 < nargs + 0 + ((given.length : Int) - (nargs : Int) + 1).toNat := by
    intro j h1 h2; omega
  refine returns_ite (fun hc => ?_) (fun hc => ?_)
  · refine returns_bind (widen_loop nargs (CondStep (hasConditional L) (vaNfixed nargs isva)) _ ?_ _ 0 _)
      (fun g1 ⟨hs1, hg1⟩ => ?_)
    · va_body cond_yes cond_noslot cond_other
    refine returns_ite (fun hm => ?_) (fun hm => ?_)
    · refine returns_bind (widen_loop nargs (AliasStep (hasMustalias L) (vaNfixed nargs isva)) _ ?_ _ 0 _)
        (fun g2 ⟨hs2, hg2⟩ => ?_)
      · va_body alias_yes alias_noslot alias_other
      have hGlen : g2.toList.length = given.length := by simp [hs2, hs1]
      have hG : ∀ j < given.length, ∃ a y, given[j]? = some a ∧ g2.toList[j]? = some y ∧
          (nargs ≤ j + 1 → VaWidened (hasConditional L) (hasMustalias L) (vaNfixed nargs isva) a y) := by
        intro j hj
        obtain ⟨a, y1, ha, hy1, hin1, -⟩ := hg1 j (by simpa using hj)
        obtain ⟨a', y2, ha', hy2, hin2, -⟩ := hg2 j (by rw [hs1]; simpa using hj)
        rw [hy1] at ha'; cases ha'
        exact ⟨a, y2, by simpa using ha, by simpa using hy2,
          fun h => vaw_intro (hin1 ⟨by omega, hm0 j hj h⟩) (hin2 ⟨by omega, hm0 j hj h⟩)⟩
      va_finish nargs
    · have hGlen : g1.toList.length = given.length := by simp [hs1]
      have hG : ∀ j < given.length, ∃ a y, given[j]? = some a ∧ g1.toList[j]? = some y ∧
          (nargs ≤ j + 1 → VaWidened (hasConditional L) (hasMustalias L) (vaNfixed nargs isva) a y) := by
        intro j hj
        obtain ⟨a, y1, ha, hy1, hin1, -⟩ := hg1 j (by simpa using hj)
        exact ⟨a, y1, by simpa using ha, by simpa using hy1,
          fun h => vaw_intro (hin1 ⟨by omega, hm0 j hj h⟩) (alias_off hm)⟩
      va_finish nargs
  · refine returns_ite (fun hm => ?_) (fun hm => ?_)
    · refine returns_bind (widen_loop nargs (AliasStep (hasMustalias L) (vaNfixed nargs isva)) _ ?_ _ 0 _)
        (fun g2 ⟨hs2, hg2⟩ => ?_)
      · va_body alias_yes alias_noslot alias_other
      have hGlen : g2.toList.length = given.length := by simp [hs2]
      have hG : ∀ j < given.length, ∃ a y, given[j]? = some a ∧ g2.toList[j]? = some y ∧
          (nargs ≤ j + 1 → VaWidened (hasConditional L) (hasMustalias L) (vaNfixed nargs isva) a y) := by
        intro j hj
        obtain ⟨a, y2, ha, hy2, hin2, -⟩ := hg2 j (by simpa using hj)
        exact ⟨a, y2, by simpa using ha, by simpa using hy2,
          fun h => vaw_intro (cond_off hc) (hin2 ⟨by omega, hm0 j hj h⟩)⟩
      va_finish nargs
    · have hGlen : given.length = given.length := rfl
      have hG : ∀ j < given.length, ∃ a y, given[j]? = some a ∧ given[j]? = some y ∧
          (nargs ≤ j + 1 → VaWidened (hasConditional L) (hasMustalias L) (vaNfixed nargs isva) a y) := by
        intro j hj
        exact ⟨given[j], given[j], by simp [hj], by simp [hj], fun _ => vaw_intro (cond_off hc) (alias_off hm)⟩
      va_finish nargs))

theorem vaProcessExact_proven : VaProcessExact := by
  intro n E L given nargs isva
  unfold vaProcessArgtypes
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size, Nat.add_sub_cancel, Nat.sub_zero,
    List.size_toArray]
  refine returns_ite (fun hva => ?_) (fun hva => ?_)
  rotate_left
  · have hisva : isva = false := by cases isva <;> simp_all
    have hl : (given.getLast?.map LElt.isVarargElt) ≠ some true := by
      intro h; apply hva; rw [hisva]; cases hg : given.getLast? <;> simp_all
    refine returns_ite (fun _ => returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim))
      (fun hlen => returns_pure ⟨fun _ _ => rfl, fun i hi1 hi2 => ?_, fun h => absurd h (by simp [hisva])⟩)
    have hlen' : given.length = nargs := by simpa using hlen
    have hi2' : i ≤ given.length := by simp only [vaNfixed, hisva] at hi2; simp at hi2; omega
    refine ⟨given[i - 1]!, given[i - 1]!, argtypeByIndex_nonva given i hi1 hi2' hl,
      vaw_intro (cond_off (by simp [hisva])) (alias_off (by simp [hisva])), ?_⟩
    rw [List.getElem?_eq_getElem (by omega)]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show i - 1 < given.length by omega)]
  have hnf : ((nargs : Int) - if isva = true then 1 else 0).toNat ≤ nargs := by split <;> omega
  refine returns_bind (returns_forIn_range'_done
    (fun i b => b.size = nargs ∧ ∀ j, 1 ≤ j → j < i → ∃ a x, Res (argtypeByIndex given j) a ∧
      VaWidened (isva && hasConditional L) (isva && hasMustalias L) (vaNfixed nargs isva) a x ∧
      b[j - 1]? = some (some x)) (fun _ => False) _ _ 1 ?_ _ ⟨by simp, fun j h1 h2 => by omega⟩)
    (fun out hout => ?_)
  · intro i b hi1 hi2 hI
    have hlt : i - 1 < b.size := by rw [hI.1]; omega
    refine returns_bind (returns_res _) (fun a ha => ?_)
    repeat (first
      | exact returns_pure (va_leaf hI hi1 hlt ha (vaw_intro (by cond_auto) (by alias_auto)))
      | contradiction
      | refine returns_ite (fun _ => ?_) (fun _ => ?_)
      | refine returns_bind (returns_res _) (fun _ _ => ?_)
      | split)
  replace hout : out.size = nargs ∧ ∀ j : Nat, 1 ≤ j → (j : Int) ≤ vaNfixed nargs isva → ∃ a x,
      Res (argtypeByIndex given j) a ∧
      VaWidened (isva && hasConditional L) (isva && hasMustalias L) (vaNfixed nargs isva) a x ∧
      out[j - 1]? = some (some x) := by
    rcases hout with ⟨h1, h2⟩ | h
    · exact ⟨h1, fun j hj1 hj2 => h2 j hj1 (by simp only [vaNfixed] at hj2; omega)⟩
    · exact h.elim
  refine returns_ite (fun hisva => ?_) (fun hisva => ?_)
  rotate_left
  · have hisva' : isva = false := by simpa using hisva
    intro s r s' h
    have hun := mapM_unwrap _ (fun e s => rfl) _ s r s' h
    refine ⟨fun _ hl => ?_, fun i hi1 hi2 => ?_, fun h => absurd h (by simp [hisva'])⟩
    · exfalso; apply hl; rw [hisva'] at hva; cases hg : given.getLast? <;> simp_all
    · obtain ⟨a, x, h1, h2, h3⟩ := hout.2 i hi1 hi2
      exact ⟨a, x, h1, h2, hun _ _ (by rw [Array.getElem?_toList]; exact h3)⟩
  have hisva' : isva = true := hisva
  refine returns_ite (fun hlt => ?_) (fun hlt => ?_)
  · refine returns_bind (returns_atIdx' _ _) (fun d ⟨hd1, hd⟩ => ?_)
    have e : ((given.length : Int) - 1).toNat = given.length - 1 := by omega
    rw [e] at hd
    refine returns_ite (fun hdv => ?_) (fun hdv => ?_)
    · have hvl : vaLast given nargs = given.length := by
        unfold vaLast; rw [if_pos ⟨by omega, by rw [hd]; simp [hdv]⟩]
      have hGlen : given.length = given.length := rfl
      have hG : ∀ j < given.length, ∃ a y, given[j]? = some a ∧ given[j]? = some y ∧
          (given.length ≤ j + 1 → VaWidened (hasConditional L) (hasMustalias L) (vaNfixed nargs isva) a y) := by
        intro j hj
        refine ⟨given[j], given[j], by simp [hj], by simp [hj], fun h => ?_⟩
        have hj' : j = given.length - 1 := by omega
        subst hj'
        have : given[given.length - 1] = d := by
          rw [List.getElem?_eq_getElem hj] at hd; cases hd; rfl
        rw [this]
        exact vaw_intro (cond_other (not_cond_of_vararg hdv)) (alias_other (not_alias_of_vararg hdv))
      va_finish given.length
    · have hvl : vaLast given nargs = nargs := by
        unfold vaLast; rw [if_neg (fun h => by rw [hd] at h; simp at h; simp_all)]
      va_nonva
  · simp only [Bool.false_eq_true, ite_false]
    have hvl : vaLast given nargs = nargs := by
      unfold vaLast; rw [if_neg (fun h => hlt (by exact_mod_cast h.1))]
    va_nonva

/-! ## `most_general_argtypes` position by position -/

/-- `x` is what `most_general_argtypes` makes of the parameter `p` of `specTypes`: after
`unwraptv`, a singleton type becomes `Const` of its instance, a `Type{T}` with a constant `T`
becomes `Const(T)`, and any other type is rewrapped in `specTypes`'s `UnionAll`s and passed
through `elim_free_typevars`. -/
def MgConv (n : Nat) (E : CEnv) (spec p : Val) (x : LElt) : Prop :=
  ∃ a, Res (unwraptv n p) a ∧ ∃ b, Res (issingletontype n E a) b ∧
    (b = true → x = .const (singletonInstance E a)) ∧
    (b = false → isconstType a = true → ∃ t, Res (typeParameter a) t ∧ x = .const t) ∧
    (b = false → isconstType a = false → ∃ t, Res (rewrapUnionallJ n E a spec) t ∧ x = .ty (elimFreeTypevars t))

theorem mg_single {n E spec p a b} (hu : Res (unwraptv n p) a) (hs : Res (issingletontype n E a) b)
    (hb : b = true) : MgConv n E spec p (.const (singletonInstance E a)) :=
  ⟨a, hu, b, hs, fun _ => rfl, fun h => by simp_all, fun h => by simp_all⟩

theorem mg_ctype {n E spec p a b t} (hu : Res (unwraptv n p) a) (hs : Res (issingletontype n E a) b)
    (hb : ¬ b = true) (hc : isconstType a = true) (ht : Res (typeParameter a) t) :
    MgConv n E spec p (.const t) :=
  ⟨a, hu, b, hs, fun h => absurd h hb, fun _ _ => ⟨t, ht, rfl⟩, fun _ h => by simp_all⟩

theorem mg_other {n E spec p a b t} (hu : Res (unwraptv n p) a) (hs : Res (issingletontype n E a) b)
    (hb : ¬ b = true) (hc : ¬ isconstType a = true) (ht : Res (rewrapUnionallJ n E a spec) t) :
    MgConv n E spec p (.ty (elimFreeTypevars t)) :=
  ⟨a, hu, b, hs, fun h => absurd h hb, fun _ h => absurd h hc, fun _ _ => ⟨t, ht, rfl⟩⟩

macro "mg_auto" : tactic => `(tactic| first
  | exact mg_single (by assumption) (by assumption) (by assumption)
  | exact mg_ctype (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  | exact mg_other (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

/-- What the main loop of `most_general_argtypes` has done before step `i`, on a vector of size `S`:
every earlier position that is not the `Vararg` tail holds its converted parameter, and after the
`Vararg` step the tail element `e` is in `lastatype`, at position `np` (unless the `Vararg` overwrote
it) and wrapped as `Vararg{widenconst(e)}` at the end. -/
def MgInv (n : Nat) (E : CEnv) (spec : Val) (params : List Val) (S : Nat) (i : Nat)
    (st : Array (Option LElt) × Option LElt) : Prop :=
  st.1.size = S ∧
  (∀ j, j < i - 1 → ¬(j + 1 = params.length ∧ params[j]!.isVararg = true) →
    ∃ x, MgConv n E spec params[j]! x ∧ st.1[j]? = some (some x)) ∧
  (i = params.length + 1 → 0 < params.length → params[params.length - 1]!.isVararg = true →
    ∃ e, MgConv n E spec (unwrapva params[params.length - 1]!) e ∧ st.2 = some e ∧
      (∃ w v, Res (widenconst n E e) w ∧ Res (jlVararg n E w) v ∧ st.1[S - 1]? = some (some (.ty v))) ∧
      (params.length - 1 < S - 1 → st.1[params.length - 1]? = some (some e)))

theorem mg_leaf_plain {n E spec params S i st x} (hI : MgInv n E spec params S i st) (hi1 : 1 ≤ i)
    (hi2 : i ≤ params.length) (hc : ¬(i == params.length && params[i - 1]!.isVararg) = true)
    (hx : MgConv n E spec params[i - 1]! x) (hS : params.length ≤ S) :
    MgInv n E spec params S (i + 1) (st.1.set! (i - 1) (some x), st.2) := by
  obtain ⟨hs, hpre, -⟩ := hI
  refine ⟨by simp [hs], fun j hj hnv => ?_, fun h _ hva => absurd (by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨by omega, by rw [show i - 1 = params.length - 1 by omega]; exact hva⟩) hc⟩
  rcases Nat.lt_or_eq_of_le (show j ≤ i - 1 by omega) with hj' | hj'
  · obtain ⟨y, hy, hgy⟩ := hpre j hj' hnv
    exact ⟨y, hy, by simp only; rw [getElem?_set!', if_neg (by omega)]; exact hgy⟩
  · subst hj'
    exact ⟨x, hx, by simp only; rw [getElem?_set!', if_pos rfl, if_pos (by omega)]⟩

theorem mg_leaf_va {n E spec params S i st x w v} (hI : MgInv n E spec params S i st) (hi1 : 1 ≤ i)
    (hi2 : i ≤ params.length) (hc : (i == params.length && params[i - 1]!.isVararg) = true)
    (hx : MgConv n E spec (unwrapva params[i - 1]!) x) (hw : Res (widenconst n E x) w)
    (hv : Res (jlVararg n E w) v) (hS : params.length ≤ S) :
    MgInv n E spec params S (i + 1)
      ((st.1.set! (i - 1) (some x)).set! ((st.1.set! (i - 1) (some x)).size - 1) (some (.ty v)), some x) := by
  obtain ⟨hs, hpre, -⟩ := hI
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hc1, hc2⟩ := hc
  subst hc1
  have hsz : (st.1.set! (params.length - 1) (some x)).size = S := by simp [hs]
  refine ⟨by simp [hs], fun j hj hnv => ?_, fun _ _ _ => ⟨x, hx, rfl, ⟨w, v, hw, hv, ?_⟩, fun hlt => ?_⟩⟩
  · have hj' : j < params.length - 1 := by
      rcases Nat.lt_or_eq_of_le (show j ≤ params.length - 1 by omega) with h | h
      · exact h
      · exact absurd ⟨by omega, by rw [h]; exact hc2⟩ hnv
    obtain ⟨y, hy, hgy⟩ := hpre j (by omega) hnv
    refine ⟨y, hy, ?_⟩
    simp only
    rw [getElem?_set!', hsz, if_neg (by omega), getElem?_set!', if_neg (by omega)]
    exact hgy
  · simp only
    rw [getElem?_set!', hsz, if_pos rfl, if_pos (by omega)]
  · simp only
    rw [getElem?_set!', hsz, if_neg (by omega), getElem?_set!', if_pos rfl, if_pos (by omega)]

/-- `most_general_argtypes(method, specTypes)` (`Compiler/src/inferenceresult.jl:162-202`), and so
`matching_cache_argtypes(𝕃, mi)` (`inferenceresult.jl:3-6`), position by position. Each parameter of
`specTypes` other than a trailing `Vararg` becomes its `MgConv` conversion. A trailing `Vararg{T}`
gives the conversion `e` of `T` at its own position and at every position padded up to
`method.nargs`, and the last position holds `Vararg{widenconst(e)}`. With `MostGeneralLength` this
pins the whole result. -/
def MostGeneralExact : Prop :=
  ∀ n E nargs? spec name params, spec.unwrapUnionall = .datatype name params →
    Returns (matchingCacheArgtypesMI n E nargs? spec) fun r =>
      (∀ j, j < params.length → ¬(j + 1 = params.length ∧ params[j]!.isVararg = true) →
        ∃ x, MgConv n E spec params[j]! x ∧ r[j]? = some x) ∧
      (0 < params.length → params[params.length - 1]!.isVararg = true →
        ∃ e, MgConv n E spec (unwrapva params[params.length - 1]!) e ∧
          (∃ w v, Res (widenconst n E e) w ∧ Res (jlVararg n E w) v ∧ r[r.length - 1]? = some (.ty v)) ∧
          ∀ j, params.length - 1 ≤ j → j + 1 < r.length → r[j]? = some e)

set_option hygiene false in
/-- The main loop, the padding loop and the result of `most_general_argtypes`, from a vector of
size `S`. Needs `hS : params.length ≤ S` and `hres`. -/
macro "mg_rest" S:term : tactic => `(tactic| (
  refine returns_bind (returns_forIn_range'_done (MgInv n E spec params $S) (fun _ => False) _ _ 1 ?_ _
    ⟨hA, fun j hj => by omega, fun h hp => by omega⟩) (fun st hst => ?_)
  · intro i b hi1 hi2 hI
    simp only [pure_bind, ite_true, if_true, Bool.false_eq_true, ite_false]
    repeat (first
      | exact returns_pure (mg_leaf_plain hI hi1 (by omega) (by assumption) (by mg_auto) hS)
      | exact returns_pure (mg_leaf_va hI hi1 (by omega) (by assumption) (by mg_auto) (by assumption)
          (by assumption) hS)
      | contradiction
      | refine returns_ite (fun _ => ?_) (fun _ => ?_)
      | refine returns_bind (returns_res _) (fun _ _ => ?_)
      | split)
  replace hst : MgInv n E spec params $S (params.length + 1) st := by
    rcases hst with h | h
    · rw [Nat.add_comm] at h; exact h
    · exact h.elim
  obtain ⟨hs0, hpre, hfin⟩ := hst
  refine returns_bind (returns_forIn_range'_done
    (fun i (s1 : Array (Option LElt)) => s1.size = $S ∧
      (∀ j, ¬(min params.length (N) ≤ j ∧ j + 1 < i) → s1[j]? = st.1[j]?) ∧
      (∀ j, min params.length (N) ≤ j → j + 1 < i → ∃ la, st.2 = some la ∧ s1[j]? = some (some la)))
    (fun _ => False) _ _ _ ?_ _ ⟨hs0, fun j _ => rfl, fun j h1 h2 => by omega⟩) (fun sf hsf => ?_)
  · intro i s1 hi1 hi2 ⟨hs, hun, hset⟩
    split
    · rename_i la hla
      refine returns_ite (fun _ => returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim))
        (fun hle => returns_pure ⟨by simp [hs], fun j hj => ?_, fun j hj1 hj2 => ?_⟩)
      · rw [getElem?_set!', if_neg (by omega)]; exact hun j (by omega)
      · rcases Nat.lt_or_eq_of_le (show j + 1 ≤ i by omega) with h | h
        · obtain ⟨la', h1, h2⟩ := hset j hj1 h
          exact ⟨la', h1, by rw [getElem?_set!', if_neg (by omega)]; exact h2⟩
        · exact ⟨la, hla, by rw [getElem?_set!', if_pos (by omega), if_pos (by simp at hle; omega)]⟩
    · exact returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim)
  replace hsf := hsf.resolve_right id
  obtain ⟨hsz, hunch, hfill⟩ := hsf
  intro s r s' h
  have hun := mapM_unwrap _ (fun e s => rfl) _ s r s' h
  have hlen := (returns_mapM_length _ sf.toList) s r s' h
  simp only [Array.length_toList] at hlen
  refine ⟨fun j hj hnv => ?_, fun hp hva => ?_⟩
  · obtain ⟨x, hx, hgx⟩ := hpre j (by omega) hnv
    refine ⟨x, hx, hun _ _ ?_⟩
    rw [Array.getElem?_toList, hunch j (by omega)]; exact hgx
  · obtain ⟨e, he, hla, ⟨w, v, hw, hv, hlast⟩, hnp⟩ := hfin rfl hp hva
    have hc' : ($S = N ∧ params.length < N) ∨ ($S = params.length ∧ N ≤ params.length) := by
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, h.2 hva⟩
    refine ⟨e, he, ⟨w, v, hw, hv, hun _ _ ?_⟩, fun j hj1 hj2 => hun _ _ ?_⟩
    · rw [hlen, hsz, Array.getElem?_toList, hunch _ (by omega)]; exact hlast
    · rw [Array.getElem?_toList]
      rw [hlen, hsz] at hj2
      rcases Nat.lt_or_eq_of_le hj1 with hj | hj
      · obtain ⟨la, h1, h2⟩ := hfill j (by omega) (by omega)
        rw [hla] at h1; cases h1; exact h2
      · subst hj
        rw [hunch _ (by omega)]; exact hnp (by omega)))

theorem mostGeneralExact_proven : MostGeneralExact := by
  intro n E nargs? spec name params hspec
  unfold matchingCacheArgtypesMI mostGeneralArgtypes
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', range_size, Nat.add_sub_cancel, List.size_toArray,
    List.length_map]
  generalize nargs?.getD 0 = N
  split
  · rename_i nm ps heq
    rw [hspec] at heq
    cases heq
    have hA0 : ((List.map (fun p => some (LElt.ty p)) params).toArray).size = params.length := by simp
    refine returns_ite (fun hlt => ?_) (fun hlt => ?_)
    · split
      · rename_i lastp hlp
        have hlp' : params[params.length - 1]! = lastp := by
          rw [List.getLast?_eq_getElem?] at hlp
          rw [List.getElem!_eq_getElem?_getD, hlp]; rfl
        refine returns_ite (fun hva => ?_) (fun hva => ?_)
        · have hA : ((List.map (fun p => some (LElt.ty p)) params).toArray ++
              Array.replicate (N - params.length) none).size = N := by
            simp; omega
          have hS : params.length ≤ N := by omega
          have hcase : (N = N ∧ params.length < N) ∨
              (N = params.length ∧ (params[params.length - 1]!.isVararg = true → N ≤ params.length)) :=
            Or.inl ⟨rfl, by omega⟩
          mg_rest N
        · have hA := hA0
          have hS : params.length ≤ params.length := Nat.le_refl _
          have hcase : (params.length = N ∧ params.length < N) ∨
              (params.length = params.length ∧ (params[params.length - 1]!.isVararg = true → N ≤ params.length)) :=
            Or.inr ⟨rfl, fun h => absurd (hlp' ▸ h) hva⟩
          mg_rest params.length
      · exact returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim)
    · have hA := hA0
      have hS : params.length ≤ params.length := Nat.le_refl _
      have hcase : (params.length = N ∧ params.length < N) ∨
          (params.length = params.length ∧ (params[params.length - 1]!.isVararg = true → N ≤ params.length)) :=
        Or.inr ⟨rfl, fun _ => by omega⟩
      mg_rest params.length
  · rename_i hne
    exact (hne name params hspec).elim

/-! ## Registry -/

/-- Registry entries that pin the bodies of the result-caching functions branch by branch. -/
def exactEntries : List Entry := [
  { id := "compiler-cacheresult-elim-free-typevars-choice", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["elim_free_typevars(@nospecialize t)"],
    statement := "elim_free_typevars(t) returns Type for a Type{...} with free type variables and Any for any other type with free type variables (and Type is not Any).",
    source := "comment Compiler/src/inferenceresult.jl:204-208",
    status := .proven, prop := ``ElimFreeTypevarsChoice, thm := some ``elimFreeTypevarsChoice_proven },
  { id := "compiler-cacheresult-is-argtype-match-exact", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["is_argtype_match(𝕃::AbstractLattice, @nospecialize(given_argtype), @nospecialize(cache_argtype), overridden_by_const::Bool)"],
    statement := "is_argtype_match(𝕃, given, cache, overridden_by_const) is !overridden_by_const when given is not forwardable, and runs exactly is_lattice_equal(𝕃, given, cache) when it is.",
    source := "Compiler/src/inferenceresult.jl:100-109",
    status := .proven, prop := ``IsArgtypeMatchExact, thm := some ``isArgtypeMatchExact_proven },
  { id := "compiler-cacheresult-argtypes-match-exact", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["constprop_cache_lookup(𝕃::AbstractLattice, mi::MethodInstance, given_argtypes::Vector{Any}, cache::InferenceCache, world::UInt)", "is_argtype_match(𝕃::AbstractLattice, @nospecialize(given_argtype), @nospecialize(cache_argtype), overridden_by_const::Bool)"],
    statement := "The position loop of constprop_cache_lookup answers the conjunction of the is_argtype_match answers at each position: true on an empty query, and b && r for a first position answering b followed by the rest answering r.",
    source := "Compiler/src/inferenceresult.jl:245-249",
    status := .proven, prop := ``ArgtypesMatchExact, thm := some ``argtypesMatchExact_proven },
  { id := "compiler-cacheresult-lookup-exact", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["constprop_cache_lookup(𝕃::AbstractLattice, mi::MethodInstance, given_argtypes::Vector{Any}, cache::InferenceCache, world::UInt)"],
    statement := "constprop_cache_lookup returns the first entry, in cache order, that is for the same MethodInstance, made in the query's world and valid there, has a key of the query's length, has overridden_by_const set and passes the position loop, and is not a tombstone; else missing when such an entry is a tombstone; else nothing.",
    source := "invariant: the lookup reuses a matching result (Compiler/src/inferenceresult.jl:217-261, comment at 250-252)",
    status := .proven, prop := ``ConstpropLookupExact, thm := some ``constpropLookupExact_proven,
    notes := "Together with compiler-cacheresult-argtypes-match-exact and -is-argtype-match-exact this pins a hit, not only its soundness." },
  { id := "compiler-cacheresult-pick-const-arg-prefers-given", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["pick_const_arg(𝕃::AbstractLattice, @nospecialize(given_argtype), @nospecialize(cache_argtype))"],
    statement := "pick_const_arg returns the given argument type when it is forwardable and not lattice-equal to the cache argument type, except that a PartialStruct against a cache Type it is not strictly below is narrowed by tmeet with that type.",
    source := "comments Compiler/src/inferenceresult.jl:51 and 54-55",
    status := .proven, prop := ``PickConstArgPrefersGiven, thm := some ``pickConstArgPrefersGiven_proven },
  { id := "compiler-cacheresult-matching-simple-via", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["matching_cache_argtypes(𝕃::AbstractLattice, ::MethodInstance, simple_argtypes::Union{SimpleArgtypes, WidenedArgtypes}, cache_argtypes::Vector{Any})"],
    statement := "matching_cache_argtypes(𝕃, mi, simple_argtypes, cache_argtypes) returns a result of pick_const_args! on the argument types with widenslotwrapper applied at each position: a Conditional widened by widenconditional, a MustAlias by widenmustalias, anything else kept.",
    source := "Compiler/src/inferenceresult.jl:38-47",
    status := .proven, prop := ``MatchingCacheArgtypesSimpleVia, thm := some ``matchingCacheArgtypesSimpleVia_proven },
  { id := "compiler-cacheresult-pick-const-args-exact", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["pick_const_args!(𝕃::AbstractLattice, given_argtypes::Vector{Any}, cache_argtypes::Vector{Any})", "matching_cache_argtypes(𝕃::AbstractLattice, ::MethodInstance, simple_argtypes::Union{SimpleArgtypes, WidenedArgtypes}, cache_argtypes::Vector{Any})"],
    statement := "pick_const_args! puts at each fixed key position j a result of pick_const_arg on the given argument type there (the given Vararg's element type at and after the given Vararg) and argtype_by_index(cache_argtypes, j); when both lists end in Vararg the last key position is Vararg{pick_const_arg(unwrapva(given_va), unwrapva(cache_va))}.",
    source := "comment Compiler/src/inferenceresult.jl:75 (process the common prefix, then join) and the body at 64-98",
    status := .proven, prop := ``PickConstArgsExact, thm := some ``pickConstArgsExact_proven,
    notes := "With compiler-cacheresult-key-length (the key's length) this pins every key position." },
  { id := "compiler-cacheresult-va-process-exact", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["va_process_argtypes(𝕃::AbstractLattice, given_argtypes::Vector{Any}, nargs::UInt, isva::Bool, mi::MethodInstance)"],
    statement := "va_process_argtypes returns the given argument types unchanged when the method is not varargs and they do not end in Vararg; each fixed position i <= nargs - isva holds argtype_by_index(given, i) with a Conditional or MustAlias on a slot past the fixed arguments widened when the method is varargs and the lattice has them; and for a varargs method position nargs holds tuple_tfunc of the trailing argument types from vaLast on, widened the same way.",
    source := "Compiler/src/inferenceresult.jl:111-160",
    status := .proven, prop := ``VaProcessExact, thm := some ``vaProcessExact_proven,
    notes := "vaLast is the given Vararg's position when fewer than nargs argument types end in one, and nargs otherwise (inferenceresult.jl:130-133). With compiler-cacheresult-va-process-length this pins every position." },
  { id := "compiler-cacheresult-most-general-exact", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["most_general_argtypes(method::Union{Method,Nothing}, @nospecialize(specTypes))", "matching_cache_argtypes(::AbstractLattice, mi::MethodInstance)"],
    statement := "most_general_argtypes(method, specTypes), and so matching_cache_argtypes(𝕃, mi), turns each parameter of specTypes other than a trailing Vararg into Const(instance) for a singleton type, Const(T) for a Type{T} with a constant T, and elim_free_typevars(rewrap_unionall(p, specTypes)) otherwise (after unwraptv); a trailing Vararg{T} gives the conversion e of T at its own position and at every position padded up to method.nargs, and Vararg{widenconst(e)} at the last position.",
    source := "comments Compiler/src/inferenceresult.jl:170-173 and 185, the loop at 176-197 and the padding loop at 198-200",
    status := .proven, prop := ``MostGeneralExact, thm := some ``mostGeneralExact_proven,
    notes := "With compiler-cacheresult-most-general-length this pins every position." }
]

/-- Registry entries of `Compiler/src/utilities.jl` that pin `count_const_size`. -/
def exactUtilityEntries : List Entry := [
  { id := "compiler-cacheresult-count-const-size-exact", juliaFile := "Compiler/src/utilities.jl",
    juliaFns := ["count_const_size(@nospecialize(x), count_self::Bool = true)"],
    statement := "count_const_size(x, count_self) is 0 for a Type, TypeName or Symbol; MAX_INLINE_CONST_SIZE + 1 for a mutable GenericMemory, String or SimpleVector; 8 for a Module, Method or CodeInstance; MAX_INLINE_CONST_SIZE + 1 for any other mutable object with a non-const field; the size of an isbits value; and otherwise sizeof(typeof(x)) (when count_self) plus the counts of its pointer fields and its inline fields that are not pointer-free, capped at MAX_INLINE_CONST_SIZE + 1.",
    source := "comments Compiler/src/utilities.jl:40-53 and the body at 37-75",
    status := .proven, prop := ``CountConstSizeExact, thm := some ``countConstSizeExact_proven,
    notes := "The answers of ismutable, the layout facts, the fields and the recursive counts are hypotheses (Gives), as in the typelimits branch statements." },
  { id := "compiler-cacheresult-count-const-size-self-mono", juliaFile := "Compiler/src/utilities.jl",
    juliaFns := ["count_const_size(@nospecialize(x), count_self::Bool = true)"],
    statement := "count_const_size(x, false) <= count_const_size(x, true): with the same answers from the calls it makes, leaving out the object's own size never gives a larger count.",
    source := "invariant: the count_self flag only drops the object's own size (Compiler/src/utilities.jl:62)",
    status := .proven, prop := ``CountConstSizeSelfMono, thm := some ``countConstSizeSelfMono_proven }
]

/-- Registry entries of `Compiler/src/typeinfer.jl` that pin the source-keeping decisions. -/
def exactTypeinferEntries : List Entry := [
  { id := "compiler-cacheresult-keep-source-exact", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["keep_source_for_output(mi::MethodInstance)"],
    statement := "keep_source_for_output(mi) holds exactly when jl_generating_output() is nonzero and isa_compileable_sig(mi) holds, and is false without asking isa_compileable_sig when not generating output.",
    source := "comment Compiler/src/typeinfer.jl:590-591",
    status := .proven, prop := ``KeepSourceForOutputExact, thm := some ``keepSourceForOutputExact_proven },
  { id := "compiler-cacheresult-maybe-compress-exact", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["maybe_compress_codeinfo(interp::AbstractInterpreter, mi::MethodInstance, ci::CodeInfo)"],
    statement := "maybe_compress_codeinfo returns toplevel code as it is; for a method it drops the source (nothing) exactly when trees may be discarded, the source is not inlineable, precompile_keep_ir is off and keep_source_for_output is false; and it compresses exactly when may_compress holds and the source is neither dropped nor kept by precompile_keep_ir.",
    source := "comments Compiler/src/typeinfer.jl:597 and 601-603, and the body at 595-610",
    status := .proven, prop := ``MaybeCompressExact, thm := some ``maybeCompressExact_proven }
]

end JuliaLean.Proofs.Compiler.src.inferenceresult
