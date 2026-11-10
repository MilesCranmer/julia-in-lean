import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.inferenceresult
import JuliaLean.Compiler.src.typeinfer
import JuliaLean.Proofs.Compiler.src.tfuncs.Common

/-!
Properties of the result-caching code: `Compiler/src/inferenceresult.jl` (cache argument types,
`Vararg` canonicalisation, the const-prop cache lookup), the result-caching decisions of
`Compiler/src/typeinfer.jl` and `count_const_size` / `is_inlineable_constant` of
`Compiler/src/utilities.jl`. The models are in `JuliaLean/Compiler/src/inferenceresult.lean`,
`typeinfer.lean` and `utilities.lean`.

As in `typelattice/Common.lean`, statements about `CM` computations are partial-correctness
statements: they constrain what a call returns when it returns.
-/

namespace JuliaLean.Proofs.Compiler.src.inferenceresult

open JuliaLean.Registry JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice
open JuliaLean.Proofs.Compiler.Tfuncs (cxE cxT)

set_option maxRecDepth 100000

/-! ## `elim_free_typevars` -/

/-- `elim_free_typevars(t)` never returns a type with free type variables, and returns a closed
type unchanged (`Compiler/src/inferenceresult.jl:204-215`). A free variable left in a cache
argument type would make the key depend on a variable no caller can name. -/
def ElimFreeTypevarsClosed : Prop :=
  ∀ t : Val, JuliaLean.Compiler.hasFreeTypevars (elimFreeTypevars t) = false ∧
    (JuliaLean.Compiler.hasFreeTypevars t = false → elimFreeTypevars t = t)

theorem elimFreeTypevarsClosed_proven : ElimFreeTypevarsClosed := by
  intro t
  unfold elimFreeTypevars
  by_cases h : JuliaLean.Compiler.hasFreeTypevars t = true
  · simp only [h, ite_true]
    refine ⟨?_, fun h' => by cases h'⟩
    split <;> rfl
  · simp only [Bool.not_eq_true] at h
    simp [h]

/-! ## The const-prop cache lookup -/

/-- One position of a cache hit is valid: a forwardable query argument (a `Const`,
`PartialStruct`, ...) is lattice-equal to the key's, and at a position where the query carries no
such information the key was not overridden by a constant, so the cached result was inferred for
the method instance's own argument type there. -/
def ArgHit (n : Nat) (E : CEnv) (L : Lattice) (g c : LElt) (o : Bool) : Prop :=
  if isForwardableArgtype L g then ∃ s s', (isLatticeEqual n E L g c).run s = .ok (true, s')
  else o = false

/-- `ArgHit` at every position of the query. -/
def KeyHit (n : Nat) (E : CEnv) (L : Lattice) : List LElt → List LElt → List Bool → Prop
  | [], _, _ => True
  | g :: gs, c :: cs, o :: os => ArgHit n E L g c o ∧ KeyHit n E L gs cs os
  | _ :: _, _, _ => False

/-- The cache entry `c` answers the query `given` for `mi` at `world`: same method instance, the
entry was made in `world` and is valid there, its key has the query's length and every position
is a valid hit. -/
def EntryHit (n : Nat) (E : CEnv) (L : Lattice) (mi : ObjId) (given : List LElt) (world : Nat)
    (c : ConstpropEntry) : Prop :=
  c.mi = mi ∧ c.cacheWorld = world ∧
    (if c.isLocal then c.proofWorlds else c.validWorlds).contains world = true ∧
    c.argtypes.length = given.length ∧
    ∃ ov, c.overriddenByConst = some ov ∧ KeyHit n E L given c.argtypes ov

/-- Soundness of `constprop_cache_lookup` (`Compiler/src/inferenceresult.jl:217-261`): a returned
entry answers the query and is not a tombstone, and `missing` is returned only when some entry
that answers the query is a tombstone. -/
def ConstpropLookupSound : Prop :=
  ∀ n E L mi miVa given cache world s r s',
    (constpropCacheLookup n E L mi miVa given cache world).run s = .ok (r, s') →
    (∀ idx, r = .found idx →
      ∃ c, cache[idx - 1]? = some c ∧ EntryHit n E L mi given world c ∧ c.tombstone = false) ∧
    (r = .missing_ → ∃ c ∈ cache, EntryHit n E L mi given world c ∧ c.tombstone = true)

theorem isArgtypeMatch_true {n E L g c o s s'} (h : (isArgtypeMatch n E L g c o).run s = .ok (true, s')) :
    ArgHit n E L g c o := by
  unfold isArgtypeMatch at h
  unfold ArgHit
  split at h
  · rename_i hf; simp only [hf, ite_true]; exact ⟨s, s', h⟩
  · rename_i hf
    simp only [hf, ite_false, Bool.false_eq_true]
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    simpa using h.1

theorem argtypesMatch_true {n E L} : ∀ (gs cs : List LElt) (os : List Bool) (s s' : Nat),
    (argtypesMatch n E L gs cs os).run s = .ok (true, s') → KeyHit n E L gs cs os
  | [], _, _, _, _, _ => trivial
  | g :: gs, c :: cs, o :: os, s, s', h => by
    unfold argtypesMatch at h
    obtain ⟨b, s₁, hb, hk⟩ := run_bind_inv h
    cases b with
    | false => simp at hk; cases hk
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hk
      exact ⟨isArgtypeMatch_true hb, argtypesMatch_true gs cs os s₁ s' hk⟩
  | _ :: _, [], _, s, _, h => by unfold argtypesMatch at h; cases h
  | _ :: _, _ :: _, [], s, _, h => by unfold argtypesMatch at h; cases h

theorem lookupLoop_sound (n E L mi miVa given world) :
    ∀ (cache : List ConstpropEntry) (idx : Nat) (ft : Bool) (s : Nat) (r : ConstpropLookup) (s' : Nat),
    (constpropLookupLoop n E L mi miVa given world idx ft cache).run s = .ok (r, s') →
    (∀ j, r = .found j → idx < j ∧
      ∃ c, cache[j - idx - 1]? = some c ∧ EntryHit n E L mi given world c ∧ c.tombstone = false) ∧
    (r = .missing_ → ft = true ∨ ∃ c ∈ cache, EntryHit n E L mi given world c ∧ c.tombstone = true)
  | [], idx, ft, s, r, s', h => by
    unfold constpropLookupLoop at h
    cases h
    refine ⟨fun j hj => ?_, fun hm => ?_⟩
    · cases ft <;> simp at hj
    · cases ft
      · simp at hm
      · exact Or.inl rfl
  | c :: rest, idx, ft, s, r, s', h => by
    have ih := lookupLoop_sound n E L mi miVa given world rest (idx + 1)
    -- A step that goes on to the next entry with flag `ft'`, where `ft' = true` only on a tombstone hit.
    have next : ∀ ft' s₁, (ft' = true → ft = true ∨ (EntryHit n E L mi given world c ∧ c.tombstone = true)) →
        (constpropLookupLoop n E L mi miVa given world (idx + 1) ft' rest).run s₁ = .ok (r, s') →
        (∀ j, r = .found j → idx < j ∧
          ∃ c', (c :: rest)[j - idx - 1]? = some c' ∧ EntryHit n E L mi given world c' ∧ c'.tombstone = false) ∧
        (r = .missing_ → ft = true ∨ ∃ c' ∈ c :: rest, EntryHit n E L mi given world c' ∧ c'.tombstone = true) := by
      intro ft' s₁ hft h'
      obtain ⟨h1, h2⟩ := ih ft' s₁ r s' h'
      refine ⟨fun j hj => ?_, fun hm => ?_⟩
      · obtain ⟨hlt, c', hc', hh⟩ := h1 j hj
        refine ⟨by omega, c', ?_, hh⟩
        have : j - idx - 1 = (j - (idx + 1) - 1) + 1 := by omega
        rw [this]; simpa using hc'
      · rcases h2 hm with hf | ⟨c', hc', hh⟩
        · rcases hft hf with hf | hh
          · exact Or.inl hf
          · exact Or.inr ⟨c, List.mem_cons_self, hh⟩
        · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', hh⟩
    unfold constpropLookupLoop at h
    by_cases h1 : (c.mi != mi || c.cacheWorld != world) = true
    · simp only [h1, ite_true, bind_pure] at h
      exact next ft s (fun hf => Or.inl hf) h
    simp only [h1, ite_false, Bool.false_eq_true] at h
    have hmi : c.mi = mi ∧ c.cacheWorld = world := by
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at h1
      exact h1
    by_cases h2 : (!(if c.isLocal then c.proofWorlds else c.validWorlds).contains world) = true
    · simp only [h2, ite_true, bind_pure] at h
      exact next ft s (fun hf => Or.inl hf) h
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
        exact next ft s (fun hf => Or.inl hf) h
    simp only [h3, ite_false, Bool.false_eq_true] at h
    have hl : c.argtypes.length = given.length := by simpa using h3
    cases hov : c.overriddenByConst with
    | none =>
      simp only [hov] at h
      exact next ft s (fun hf => Or.inl hf) h
    | some ov =>
      simp only [hov] at h
      obtain ⟨b, s₁, hb, hk⟩ := run_bind_inv h
      cases b with
      | false =>
        simp only [Bool.not_false, ite_true, bind_pure] at hk
        exact next ft s₁ (fun hf => Or.inl hf) hk
      | true =>
        have hit : EntryHit n E L mi given world c :=
          ⟨hmi.1, hmi.2, hw, hl, ov, hov, argtypesMatch_true _ _ _ _ _ hb⟩
        simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hk
        by_cases ht : c.tombstone = true
        · simp only [ht, ite_true, bind_pure] at hk
          exact next true s₁ (fun _ => Or.inr ⟨hit, ht⟩) hk
        · simp only [ht, ite_false, Bool.false_eq_true, pure_run, Except.ok.injEq, Prod.mk.injEq] at hk
          obtain ⟨rfl, -⟩ := hk
          refine ⟨fun j hj => ?_, fun hm => by cases hm⟩
          cases hj
          exact ⟨by omega, c, by simp, hit, by simpa using ht⟩

theorem constpropLookupSound_proven : ConstpropLookupSound := by
  intro n E L mi miVa given cache world s r s' h
  obtain ⟨h1, h2⟩ := lookupLoop_sound n E L mi miVa given world cache 0 false s r s' h
  refine ⟨fun idx hidx => ?_, fun hm => ?_⟩
  · obtain ⟨_, c, hc, hh⟩ := h1 idx hidx
    exact ⟨c, by simpa using hc, hh⟩
  · rcases h2 hm with hf | hh
    · cases hf
    · exact hh

/-! ## A const-prop result is found again under its own key -/

/-- The entry `const_prop_call` pushes for a fresh const-prop result: a raw `InferenceResult` for
`mi` made in `world` and valid there, with key `key` and flags `ov`
(`Compiler/src/abstractinterpretation.jl:1523-1543`). -/
def ownEntry (mi : ObjId) (world : Nat) (key : List LElt) (ov : List Bool) : ConstpropEntry :=
  { mi, isLocal := false, proofWorlds := (0, 0), cacheWorld := world, validWorlds := (world, world),
    argtypes := key, overriddenByConst := some ov, tombstone := false }

/-- Precision of the const-prop cache: `const_prop_call` builds the key `matching_cache_argtypes`
of the call's argument types and the method instance's cache argument types, flags the positions
where the key is not `===` the cache argument type, and caches the result under that key when a
flag is set (`Compiler/src/abstractinterpretation.jl:1484-1543`). The same call again builds the
same key, and the lookup must find that entry: otherwise every call site with the same constant
arguments runs constant propagation again. (The method is not `@nospecializeinfer`, so
`get_nospecializeinfer_argtypes` returns the key unchanged.) -/
def ConstpropKeyRehits : Prop :=
  ∀ ops n E L mi world given ca key ov s₁ s₁' s₂ s₂' s₃ r s₃',
    (matchingCacheArgtypesSimple ops n E L given ca).run s₁ = .ok (key, s₁') →
    (overriddenByConstFlags n E key ca).run s₂ = .ok (ov, s₂') →
    ov.any id = true →
    (constpropCacheLookup n E L mi true key [ownEntry mi world key ov] world).run s₃ = .ok (r, s₃') →
    r = .found 1

def vaLong : Val := .vararg (some longType) none

/-- `[Int64, Vararg{Int64}]`: the cache argument types of `g(a::Int, b::Int...)` without the
function slot. -/
def vaArgs : List LElt := [.ty longType, .ty vaLong]

theorem normalize_long : normalizeUnionalls 19 cxE.types (tops 20 cxE) longType = pure longType := by
  unfold normalizeUnionalls; rfl

theorem wrapVararg_long :
    wrapVararg 20 cxE.types (tops 20 cxE) (some longType) none true 0 = pure (some vaLong) := by
  unfold wrapVararg
  simp only [normalize_long]
  rfl

theorem jlVararg_long : jlVararg 20 cxE longType = pure vaLong := by
  unfold jlVararg; rw [wrapVararg_long]; rfl

theorem forwardable_ty (L : Lattice) (t : Val) : isForwardableArgtype L (.ty t) = false := by
  induction L <;> simp_all [isForwardableArgtype, LElt.isConst, LElt.isPartialStruct,
    LElt.isPartialOpaque, LElt.isPartialTask, LElt.isConditional, LElt.isMustAlias]

theorem pickConstArg_ty (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice) (t : Val) (c : LElt) :
    pickConstArg ops n E L (.ty t) c = pure c := by
  unfold pickConstArg isArgtypeMatch
  simp [forwardable_ty]

theorem varargOfElt_long : varargOfElt 20 cxE (.ty longType) = pure (.ty vaLong) := by
  unfold varargOfElt; dsimp only; rw [jlVararg_long]; rfl

theorem rehit_key (ops : TmeetOps) (L : Lattice) (s : Nat) :
    (matchingCacheArgtypesSimple ops 20 cxE L vaArgs vaArgs).run s = .ok (vaArgs, s) := by
  unfold matchingCacheArgtypesSimple pickConstArgs
  simp [vaArgs, widenslotwrapper, LElt.isAnyConditional, LElt.isAnyMustAlias, LElt.isConditional,
    LElt.isInterConditional, LElt.isMustAlias, LElt.isInterMustAlias, LElt.isVarargElt, vaLong,
    unwrapvaLElt, unwrapva, pickConstArg_ty, varargOfElt_long, resizeOpt, setOpt, getOpt,
    argtypeByIndex, atIdx, Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem egal_long_long : JuliaLean.C.egal 19 cxE.types longType longType = pure true :=
  JuliaLean.Proofs.Compiler.Tfuncs.egal_self_datatype0 18 _ _

theorem egal_va_long : JuliaLean.C.egal 19 cxE.types vaLong longType = pure false := by
  unfold JuliaLean.C.egal; rfl

theorem eltEgal_long_long : eltEgal 20 cxE (.ty longType) (.ty longType) = pure true := by
  unfold eltEgal; exact egal_long_long

theorem eltEgal_va_long :
    eltEgal 20 cxE (.ty (.vararg (some longType) none)) (.ty longType) = pure false := by
  unfold eltEgal; exact egal_va_long

theorem rehit_flags (s : Nat) :
    (overriddenByConstFlags 20 cxE vaArgs vaArgs).run s = .ok ([false, true], s) := by
  simp only [overriddenByConstFlags, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    vaArgs, List.length_cons, List.length_nil, List.range', List.forIn_cons, List.forIn_nil, atIdx,
    argtypeByIndex, LElt.isVarargElt, vaLong, unwrapvaLElt, unwrapva]
  simp [eltEgal_long_long, eltEgal_va_long, Val.isVararg]
  rfl

theorem rehit_lookup (s : Nat) :
    (constpropCacheLookup 20 cxE typeinfLattice 1 true vaArgs [ownEntry 1 7 vaArgs [false, true]] 7).run s =
      .ok (.nothing_, s) := by
  rfl

/-- Counterexample: for `g(a::Int, b::Int...)` with the cache argument types `[Int64, Vararg{Int64}]`
(function slot left out), the key is `[Int64, Vararg{Int64}]` again. The flags compare the key's
`Vararg{Int64}` with `argtype_by_index(cache_argtypes, 2)`, which unwraps the `Vararg` to `Int64`,
so the tail is flagged and the entry is cached. The lookup then reads the tail with
`overridden_by_const = true`; a `Vararg` is not forwardable, so `is_argtype_match` is `false` and
the entry is never found. `repro/compiler-cacheresult-va-tail-miss.jl` shows three identical
entries for three calls `g(1, v...)`. -/
theorem constpropKeyRehits_refuted : ¬ ConstpropKeyRehits := by
  intro h
  have := h (tfuncTmeetOps 20 cxT) 20 cxE typeinfLattice 1 7 vaArgs vaArgs vaArgs [false, true]
    0 0 0 0 0 .nothing_ 0 (rehit_key _ _ 0) (rehit_flags 0) rfl (rehit_lookup 0)
  cases this

/-! ## Reasoning about `CM` programs

`Returns m P` (from `typelattice/Common.lean`) composes along the program: these lemmas take a
goal about a whole function body apart one `bind`, `if` or loop at a time. -/

theorem returns_pure {α : Type} {x : α} {P : α → Prop} (h : P x) : Returns (pure x : CM α) P := by
  intro s r s' h'; simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h'; obtain ⟨rfl, -⟩ := h'; exact h

theorem returns_bind {α β : Type} {m : CM α} {k : α → CM β} {Q : α → Prop} {P : β → Prop}
    (hm : Returns m Q) (hk : ∀ a, Q a → Returns (k a) P) : Returns (m >>= k) P := by
  intro s r s' h
  obtain ⟨a, s₁, ha, hb⟩ := run_bind_inv h
  exact hk a (hm s a s₁ ha) s₁ r s' hb

theorem returns_ite {α : Type} {c : Prop} [Decidable c] {a b : CM α} {P : α → Prop}
    (ha : c → Returns a P) (hb : ¬c → Returns b P) : Returns (if c then a else b) P := by
  by_cases h : c
  · simp only [h, ite_true]; exact ha h
  · simp only [h, ite_false]; exact hb h

theorem returns_true {α : Type} (m : CM α) : Returns m (fun _ => True) := fun _ _ _ _ => trivial

theorem returns_throw {α : Type} (e : String) (P : α → Prop) : Returns (throw e : CM α) P := by
  intro s r s' h; cases h

theorem returns_forIn {α β : Type} (l : List α) (I D : β → Prop) (f : α → β → CM (ForInStep β))
    (hstep : ∀ a b, I b → Returns (f a b) (fun r => match r with | .yield b' => I b' | .done b' => D b')) :
    ∀ b, I b → Returns (forIn l b f) (fun r => I r ∨ D r) := by
  induction l with
  | nil => intro b hb; simp only [List.forIn_nil]; exact returns_pure (Or.inl hb)
  | cons a l ih =>
    intro b hb
    simp only [List.forIn_cons]
    refine returns_bind (hstep a b hb) ?_
    intro r hr
    cases r with
    | done b' => exact returns_pure (Or.inr hr)
    | yield b' => exact ih b' hr

theorem returns_facts (C : ConstLayout) (dt : Val) : Returns (C.facts dt) (fun f => C.facts dt = pure f) := by
  unfold ConstLayout.facts
  split
  · exact returns_pure rfl
  · exact returns_throw _ _

theorem returns_mono {α : Type} {m : CM α} {P Q : α → Prop} (h : Returns m P) (hq : ∀ a, P a → Q a) :
    Returns m Q := fun s r s' hr => hq r (h s r s' hr)

theorem returns_mapM_length {α β : Type} (f : α → CM β) : ∀ xs : List α,
    Returns (xs.mapM f) (fun r => r.length = xs.length)
  | [] => by simp only [List.mapM_nil]; exact returns_pure rfl
  | x :: xs => by
    simp only [List.mapM_cons]
    refine returns_bind (returns_true _) (fun b _ => ?_)
    refine returns_bind (returns_mapM_length f xs) (fun bs hbs => returns_pure ?_)
    simp [hbs]

theorem returns_jlThrow {α : Type} (exc msg : String) (P : α → Prop) : Returns (jlThrow exc msg : CM α) P := by
  intro s r s' h; rw [jlThrow_run] at h; cases h

theorem returns_setOpt (a : Array (Option LElt)) (i : Nat) (x : LElt) :
    Returns (setOpt a i x) (fun a' => a'.size = a.size) := by
  unfold setOpt
  refine returns_ite (fun _ => returns_pure (by simp)) (fun _ => returns_throw _ _)

theorem resizeOpt_size (a : Array (Option LElt)) (k : Nat) : (resizeOpt a k).size = k := by
  unfold resizeOpt
  split
  · simp; omega
  · simp; omega


/-! ## `count_const_size` -/

/-- What `count_const_size(x)` can return (`Compiler/src/utilities.jl:37-75`): at most
`MAX_INLINE_CONST_SIZE + 1`, the value that stands for "too large", except for an `isbits` value,
whose exact size it returns. -/
def SizeBound (C : ConstLayout) (x : Val) (r : Nat) : Prop :=
  r ≤ MAX_INLINE_CONST_SIZE + 1 ∨ ∃ f, C.facts (typeOf x) = pure f ∧ f.isbits = true ∧ r = f.size


/-- The join point of `count_const_size` after the mutability checks. -/
macro "countConstSize_jp" : tactic => `(tactic| (
  refine returns_bind (returns_facts _ _) (fun f hf => ?_)
  refine returns_ite (fun hb => returns_pure (Or.inr ⟨f, hf, hb, rfl⟩)) (fun _ => ?_)
  refine returns_ite (fun _ => returns_pure (Or.inl (Nat.le_refl _))) (fun hsz => ?_)
  refine returns_bind (returns_forIn _ (fun b => b.1 = none ∧ b.2 ≤ MAX_INLINE_CONST_SIZE)
    (fun b => b.1 = some (MAX_INLINE_CONST_SIZE + 1)) _ ?_ _ ⟨rfl, Nat.le_of_not_gt hsz⟩) (fun r hr => ?_)
  · intro i b hb
    refine returns_bind (returns_true _) (fun fv _ => ?_)
    split
    · refine returns_ite (fun _ => ?_) (fun _ => ?_)
      · refine returns_bind (returns_true _) (fun pf _ => ?_)
        refine returns_ite (fun _ => returns_pure ⟨rfl, hb.2⟩) (fun _ => ?_)
        refine returns_bind (returns_true _) (fun k _ => ?_)
        exact returns_ite (fun _ => returns_pure rfl) (fun h => returns_pure ⟨rfl, Nat.le_of_not_gt h⟩)
      · refine returns_bind (returns_true _) (fun k _ => ?_)
        exact returns_ite (fun _ => returns_pure rfl) (fun h => returns_pure ⟨rfl, Nat.le_of_not_gt h⟩)
    · exact returns_pure ⟨rfl, hb.2⟩
  · rcases hr with ⟨h1, h2⟩ | h1 <;> rw [h1]
    · exact returns_pure (Or.inl (Nat.le_succ_of_le h2))
    · exact returns_pure (Or.inl (Nat.le_refl _))))

theorem countConstSize_bound (n : Nat) (E : CEnv) (C : ConstLayout) (x : Val) (cs : Bool) :
    Returns (countConstSize n E C x cs) (SizeBound C x) := by
  cases n with
  | zero => unfold countConstSize; exact returns_throw _ _
  | succ n =>
    rw [countConstSize]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    refine returns_ite (fun _ => returns_pure (Or.inl (by decide))) (fun _ => ?_)
    refine returns_bind (returns_true _) (fun m _ => ?_)
    refine returns_ite (fun _ => ?_) (fun _ => ?_)
    · refine returns_ite (fun _ => returns_pure (Or.inl (by decide))) (fun _ => ?_)
      refine returns_ite (fun _ => returns_pure (Or.inl (by decide))) (fun _ => ?_)
      refine returns_bind (returns_true _) (fun f _ => ?_)
      refine returns_bind (returns_forIn _ (fun b => b.1 = none) (fun b => b.1 = some (MAX_INLINE_CONST_SIZE + 1))
        _ ?_ _ rfl) (fun r hr => ?_)
      · intro i b _
        exact returns_ite (fun _ => returns_pure rfl) (fun _ => returns_pure rfl)
      rcases hr with h1 | h1 <;> rw [h1]
      all_goals first | exact returns_pure (Or.inl (Nat.le_refl _)) | skip
      all_goals countConstSize_jp
    · countConstSize_jp


/-- `count_const_size(x, count_self)` (`Compiler/src/utilities.jl:37-75`) returns at most
`MAX_INLINE_CONST_SIZE + 1`, the value that stands for "too large", or the exact size of an
`isbits` value. Every walk over fields stops at the first partial sum over the limit, so the count
of a constant that is not `isbits` never grows past the limit plus one, however many fields it has.
`is_inlineable_constant(x)` (`Compiler/src/utilities.jl:77-79`) is the test of that result against
the limit. -/
def CountConstSizeBound : Prop :=
  (∀ n E C x cs, Returns (countConstSize n E C x cs) (SizeBound C x)) ∧
  (∀ n E C x s b s', (isInlineableConstant n E C x).run s = .ok (b, s') →
    (b = true ↔ ∃ k, (countConstSize n E C x).run s = .ok (k, s') ∧ k ≤ MAX_INLINE_CONST_SIZE))

theorem countConstSizeBound_proven : CountConstSizeBound := by
  refine ⟨countConstSize_bound, fun n E C x s b s' h => ?_⟩
  unfold isInlineableConstant at h
  obtain ⟨k, s₁, hk, hb⟩ := run_bind_inv h
  simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  constructor
  · intro hb; exact ⟨k, hk, by simpa using hb⟩
  · rintro ⟨k', hk', hle⟩
    rw [hk] at hk'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hk'
    simpa [hk'.1] using hle

/-! ## `get_nospecializeinfer_argtypes` -/

/-- Whether `get_nospecializeinfer_argtypes` puts back the cache argument type at 0-based position
`j`: the argument index `min(j, nargs - 1)` is positive and its `@nospecialize` bit is set. -/
def nospecWidened (mask nargs j : Nat) : Bool :=
  let iArg : Int := min (j : Int) ((nargs : Int) - 1)
  decide (iArg > 0) && mask.testBit (iArg - 1).toNat

/-- `get_nospecializeinfer_argtypes(argtypes, cache_argtypes, method)`
(`Compiler/src/inferenceresult.jl:8-25`) keeps `argtypes` for a method that is not
`@nospecializeinfer`. For one that is, the comment promises that the result has the length of
`cache_argtypes`, with the cache argument type at every `@nospecialize` argument position and the
given argument type everywhere else. -/
def NospecializeinferWidens : Prop :=
  ∀ flag mask nargs (args cache : List LElt),
    Returns (getNospecializeinferArgtypes flag mask nargs args cache) fun r =>
      ((flag && mask != 0) = false → r = args) ∧
      ((flag && mask != 0) = true → r.length = cache.length ∧
        ∀ j < cache.length, r[j]? = if nospecWidened mask nargs j then cache[j]? else args[j]?)

theorem returns_forIn_range' {β : Type} (I : Nat → β → Prop) (f : Nat → β → CM (ForInStep β))
    (hstep : ∀ i b, I i b → Returns (f i b) (fun r => ∃ b', r = .yield b' ∧ I (i + 1) b')) :
    ∀ k start b, I start b → Returns (forIn (List.range' start k) b f) (I (start + k)) := by
  intro k
  induction k with
  | zero => intro start b hb; simp only [List.range'_zero, List.forIn_nil]; exact returns_pure hb
  | succ k ih =>
    intro start b hb
    simp only [List.range'_succ, List.forIn_cons]
    refine returns_bind (hstep start b hb) ?_
    rintro r ⟨b', rfl, hb'⟩
    have := ih (start + 1) b' hb'
    rw [show start + (k + 1) = start + 1 + k by omega]
    exact this

theorem returns_atIdx (xs : List LElt) (i : Int) : Returns (atIdx xs i) (fun x => xs[(i - 1).toNat]? = some x) := by
  unfold atIdx
  refine returns_ite (fun _ => returns_throw _ _) (fun _ => ?_)
  split
  · rename_i x hx; exact returns_pure hx
  · exact returns_throw _ _

theorem range_size_succ (k : Nat) : Std.Legacy.Range.size [1:k + 1] = k := by
  simp [Std.Legacy.Range.size]

theorem nospec_step (mask nargs i : Nat) (out : List LElt) (args cache : List LElt) (hi : 1 ≤ i)
    (hlen : out.length = i - 1)
    (hpos : ∀ j < i - 1, out[j]? = if nospecWidened mask nargs j then cache[j]? else args[j]?)
    (x : LElt) (w : Bool) (hw : nospecWidened mask nargs (i - 1) = w)
    (hx : (if w then cache else args)[(i - 1)]? = some x) :
    (out ++ [x]).length = i + 1 - 1 ∧
      ∀ j < i + 1 - 1, (out ++ [x])[j]? = if nospecWidened mask nargs j then cache[j]? else args[j]? := by
  refine ⟨by simp [hlen]; omega, fun j hj => ?_⟩
  by_cases hj' : j < i - 1
  · rw [List.getElem?_append_left (by omega)]; exact hpos j hj'
  · have hji : j = i - 1 := by omega
    subst hji
    rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self, hw]
    cases w <;> simpa using hx.symm

theorem nospecializeinferWidens_proven : NospecializeinferWidens := by
  intro flag mask nargs args cache
  unfold getNospecializeinferArgtypes
  by_cases hact : (flag && mask != 0) = true
  · simp only [hact, Bool.not_true, Bool.false_eq_true, ite_false, Std.Legacy.Range.forIn_eq_forIn_range',
      range_size_succ]
    let I : Nat → List LElt → Prop := fun i out => 1 ≤ i ∧ out.length = i - 1 ∧
      ∀ j < i - 1, out[j]? = if nospecWidened mask nargs j then cache[j]? else args[j]?
    refine returns_bind (returns_forIn_range' I _ ?_ cache.length 1 [] ⟨Nat.le_refl _, rfl, by simp⟩)
      (fun r hr => ?_)
    rotate_left
    · refine returns_pure ⟨fun hf => absurd hf (by simp [hact]), fun _ => ⟨?_, fun j hj => ?_⟩⟩
      · have := hr.2.1; omega
      · exact hr.2.2 j (by omega)
    intro i out ⟨hi, hlen, hpos⟩
    have hcast : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
    have hidx : ((i : Int) - 1).toNat = i - 1 := by omega
    have hc : (decide (min ((i : Int) - 1) ((nargs : Int) - 1) > 0) &&
        mask.testBit (min ((i : Int) - 1) ((nargs : Int) - 1) - 1).toNat) =
        nospecWidened mask nargs (i - 1) := by
      simp only [nospecWidened, hcast]
    simp only [hc]
    refine returns_ite (fun hw => ?_) (fun hw => ?_)
    · refine returns_bind (returns_atIdx _ _) (fun x hx => returns_pure ⟨_, rfl, by omega, ?_⟩)
      rw [hidx] at hx
      exact nospec_step mask nargs i out args cache hi hlen hpos x true hw (by simpa using hx)
    · refine returns_bind (returns_atIdx _ _) (fun x hx => returns_pure ⟨_, rfl, by omega, ?_⟩)
      rw [hidx] at hx
      exact nospec_step mask nargs i out args cache hi hlen hpos x false (by simpa using hw) (by simpa using hx)
  · simp only [Bool.not_eq_true] at hact
    simp only [hact, Bool.not_false, ite_true]
    exact returns_pure ⟨fun _ => rfl, fun h => absurd h (by simp [hact])⟩

/-! ## `pick_const_args!` and the length of const-prop keys -/

/-- The length of the key `pick_const_args!` builds from argument types `given` and cache
argument types `ca`: empty when either is empty; with a `Vararg` tail on both, one more than the
longer fixed prefix; with a `Vararg` tail only in `given`, the cache's length; otherwise the
length of `given`. -/
def keyLength (given ca : List LElt) : Nat :=
  if given.length == 0 || ca.length == 0 then 0
  else if given.getLast!.isVarargElt then
    if ca.getLast!.isVarargElt then max (given.length - 1) (ca.length - 1) + 1 else ca.length
  else given.length

set_option hygiene false in
/-- The main loop and result of `pick_const_args!` keep the length of the working vector. -/
macro "pick_jp" k:term : tactic => `(tactic| (
  try simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine returns_bind (returns_forIn_range' (fun _ b => b.size = $k) _ ?_ _ _ _ (by simp)) (fun r hr => ?_)
  · intro i b hb
    refine returns_bind (returns_true _) (fun _ _ => ?_)
    refine returns_bind (returns_true _) (fun _ _ => ?_)
    refine returns_bind (returns_true _) (fun _ _ => ?_)
    exact returns_bind (returns_setOpt _ _ _) (fun g' hg' => returns_pure ⟨g', rfl, hg'.trans hb⟩)
  refine returns_mono (returns_mapM_length _ _) (fun x hx => ?_)))


theorem pickConstArgs_length (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice) (given ca : List LElt) :
    Returns (pickConstArgs ops n E L given ca) fun r => r.length = keyLength given ca ∧
      (given ≠ [] → ca ≠ [] → given.getLast!.isVarargElt = false → ca.getLast!.isVarargElt = false →
        given.length = ca.length) := by
  unfold pickConstArgs
  refine returns_ite (fun h0 => returns_pure ⟨by simp [keyLength, h0], fun hg hc => ?_⟩) (fun h0 => ?_)
  · simp at h0; rcases h0 with h0 | h0 <;> simp_all
  have hne : given ≠ [] ∧ ca ≠ [] := by
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h0
    exact ⟨fun h => h0.1 (by simp [h]), fun h => h0.2 (by simp [h])⟩
  refine returns_ite (fun hgv => ?_) (fun hgv => ?_)
  · refine returns_ite (fun hcv => ?_) (fun hcv => ?_)
    · refine returns_bind (returns_true _) (fun _ _ => ?_)
      refine returns_bind (returns_true _) (fun _ _ => ?_)
      refine returns_bind (returns_setOpt _ _ _) (fun g1 hg1 => ?_)
      try simp only [Std.Legacy.Range.forIn_eq_forIn_range']
      refine returns_bind (returns_forIn_range' (fun _ b => b.size = g1.size) _ ?_ _ _ _ rfl) (fun g2 hg2 => ?_)
      · intro i b hb
        exact returns_bind (returns_setOpt _ _ _) (fun g' hg' => returns_pure ⟨g', rfl, hg'.trans hb⟩)
      pick_jp g2.size
      refine ⟨?_, fun _ _ h => absurd hgv (by rw [h]; decide)⟩
      rw [hx, Array.length_toList, hr, hg2, hg1, resizeOpt_size]
      unfold keyLength; rw [if_neg h0, if_pos hgv, if_pos hcv]
    · try simp only [Std.Legacy.Range.forIn_eq_forIn_range']
      refine returns_bind (returns_forIn_range' (fun _ b => b.size = ca.length) _ ?_ _ _ _
        (resizeOpt_size _ _)) (fun g2 hg2 => ?_)
      · intro i b hb
        exact returns_bind (returns_setOpt _ _ _) (fun g' hg' => returns_pure ⟨g', rfl, hg'.trans hb⟩)
      pick_jp g2.size
      refine ⟨?_, fun _ _ h => absurd hgv (by rw [h]; decide)⟩
      rw [hx, Array.length_toList, hr, hg2]
      unfold keyLength; rw [if_neg h0, if_pos hgv, if_neg hcv]
  · refine returns_ite (fun hcv => ?_) (fun hcv => ?_)
    · pick_jp given.length
      refine ⟨?_, fun _ _ _ h => absurd hcv (by rw [h]; decide)⟩
      rw [hx, Array.length_toList, hr]
      unfold keyLength; rw [if_neg h0, if_neg hgv]
    · refine returns_ite (fun hneq => returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim))
        (fun hneq => ?_)
      pick_jp given.length
      have heq : given.length = ca.length := by simpa using hneq
      refine ⟨?_, fun _ _ _ _ => heq⟩
      rw [hx, Array.length_toList, hr]
      unfold keyLength; rw [if_neg h0, if_neg hgv]


/-- The length of const-prop keys (`Compiler/src/inferenceresult.jl:38-98`). `pick_const_args!`
returns a key of length `keyLength given ca`, and when neither side ends in `Vararg` it returns
only if the two have the same length (its `@assert`). So for a method instance whose cache
argument types do not end in `Vararg`, `matching_cache_argtypes` gives every nonempty argument
list a key of the cache's length: the lookup's `@assert` for a length mismatch, which allows one
only for a `specTypes` ending in `Vararg` (`Compiler/src/inferenceresult.jl:231-239`), cannot
fail for such keys. -/
def ConstpropKeyLength : Prop :=
  (∀ ops n E L given ca, Returns (pickConstArgs ops n E L given ca) fun r =>
    r.length = keyLength given ca ∧
    (given ≠ [] → ca ≠ [] → given.getLast!.isVarargElt = false → ca.getLast!.isVarargElt = false →
      given.length = ca.length)) ∧
  (∀ ops n E L args ca, args ≠ [] → ca ≠ [] → ca.getLast!.isVarargElt = false →
    Returns (matchingCacheArgtypesSimple ops n E L args ca) fun r => r.length = ca.length)

theorem constpropKeyLength_proven : ConstpropKeyLength := by
  refine ⟨pickConstArgs_length, fun ops n E L args ca ha hc hcv => ?_⟩
  unfold matchingCacheArgtypesSimple
  refine returns_bind (returns_mapM_length _ _) (fun given hg => returns_mono (pickConstArgs_length ops n E L given ca) ?_)
  rintro r ⟨h1, h2⟩
  have hgne : given ≠ [] := by
    intro h; apply ha; rw [h] at hg; exact List.eq_nil_of_length_eq_zero hg.symm
  have h0 : ¬(given.length == 0 || ca.length == 0) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq, not_or]
    exact ⟨fun h => hgne (List.eq_nil_of_length_eq_zero h), fun h => hc (List.eq_nil_of_length_eq_zero h)⟩
  rw [h1]
  unfold keyLength
  rw [if_neg h0]
  by_cases hgv : given.getLast!.isVarargElt = true
  · rw [if_pos hgv, if_neg (by rw [hcv]; decide)]
  · rw [if_neg hgv]
    exact h2 hgne hc (by simpa using hgv) hcv

/-! ## `va_process_argtypes` -/

/-- `va_process_argtypes(𝕃, given_argtypes, nargs, isva, mi)` (`Compiler/src/inferenceresult.jl:111-160`)
returns exactly `nargs` argument types: with a varargs method the trailing arguments are folded
into one tuple type at position `nargs`, and otherwise a list of another length is an
`AssertionError`. The inference state reads one argument type per slot. -/
def VaProcessLength : Prop :=
  ∀ n E L given nargs isva, Returns (vaProcessArgtypes n E L given nargs isva) (fun r => r.length = nargs)

theorem vaProcess_length (n : Nat) (E : CEnv) (L : Lattice) (given : List LElt) (nargs : Nat) (isva : Bool) :
    Returns (vaProcessArgtypes n E L given nargs isva) (fun r => r.length = nargs) := by
  unfold vaProcessArgtypes
  refine returns_ite (fun _ => ?_) (fun _ => ?_)
  · try simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    refine returns_bind (returns_forIn_range' (fun _ b => b.size = nargs) _ ?_ _ _ _ (by simp))
      (fun out hout => ?_)
    · intro i b hb
      repeat (first
        | exact returns_pure ⟨_, rfl, by simp [hb]⟩
        | refine returns_ite (fun _ => ?_) (fun _ => ?_)
        | refine returns_bind (returns_true _) (fun _ _ => ?_)
        | split)
    · repeat (first
        | exact returns_mono (returns_mapM_length _ _) (fun x hx => by simp_all)
        | refine returns_ite (fun _ => ?_) (fun _ => ?_)
        | refine returns_bind (returns_true _) (fun _ _ => ?_)
        | split)
  · refine returns_ite (fun _ => returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim))
      (fun h => returns_pure (by simpa using h))


theorem vaProcessLength_proven : VaProcessLength := vaProcess_length

/-! ## `most_general_argtypes` -/

theorem returns_forIn_preserve {β : Type} (μ : β → Nat) (f : Nat → β → CM (ForInStep β))
    (hstep : ∀ i b, Returns (f i b) (fun r => ∃ b', r = .yield b' ∧ μ b' = μ b)) :
    ∀ k start b, Returns (forIn (List.range' start k) b f) (fun r => μ r = μ b) := by
  intro k start b
  have := returns_forIn_range' (fun _ b' => μ b' = μ b) f
    (fun i b' hb' => returns_mono (hstep i b') (fun r ⟨b'', hr, h⟩ => ⟨b'', hr, h.trans hb'⟩)) k start b rfl
  exact this

/-- The length of `most_general_argtypes(method, specTypes)`: `method.nargs` when `specTypes` has
fewer parameters and ends in a `Vararg` (the tail is spread over the missing positions), and the
number of parameters otherwise. -/
def mgLength (nargs? : Option Nat) (spec : Val) : Nat :=
  match spec.unwrapUnionall with
  | .datatype _ ps =>
    if ps.length < nargs?.getD 0 ∧ ps.getLast?.any Val.isVararg = true then nargs?.getD 0 else ps.length
  | _ => 0

set_option hygiene false in
/-- The two loops and the result of `most_general_argtypes` keep the length of `mi_argtypes`. -/
macro "mg_jp" : tactic => `(tactic| (
  try simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine returns_bind (returns_forIn_preserve (fun b => b.1.size) _ ?_ _ _ _) (fun r hr => ?_)
  · intro i b
    repeat (first
      | exact returns_pure ⟨_, rfl, by simp⟩
      | refine returns_ite (fun _ => ?_) (fun _ => ?_)
      | refine returns_bind (returns_true _) (fun _ _ => ?_)
      | split)
  refine returns_bind (returns_forIn_preserve Array.size _ ?_ _ _ _) (fun r2 hr2 => ?_)
  · intro i b
    repeat (first
      | exact returns_pure ⟨_, rfl, by simp⟩
      | refine returns_ite (fun _ => ?_) (fun _ => ?_)
      | refine returns_bind (returns_true _) (fun _ _ => ?_)
      | split)
  refine returns_mono (returns_mapM_length _ _) (fun x hx => ?_)
  simp only [Array.length_toList] at hx
  rw [hx, hr2, hr]))

theorem mostGeneral_length (n : Nat) (E : CEnv) (nargs? : Option Nat) (spec : Val) :
    Returns (mostGeneralArgtypes n E nargs? spec) (fun r => r.length = mgLength nargs? spec) := by
  unfold mostGeneralArgtypes
  split
  · rename_i name params hspec
    refine returns_ite (fun hlt => ?_) (fun hlt => ?_)
    · split
      · rename_i lastp hl
        refine returns_ite (fun hva => ?_) (fun hva => ?_)
        · mg_jp
          simp [mgLength, hspec, hl, hva]
          simp at hlt
          split <;> omega
        · mg_jp
          simp [mgLength, hspec, hl, hva]
      · exact returns_bind (Q := fun _ => False) (returns_jlThrow _ _ _) (fun _ h => h.elim)
    · mg_jp
      simp [mgLength, hspec]
      intro h
      simp at hlt
      omega
  · exact returns_jlThrow _ _ _


/-- `most_general_argtypes(method, specTypes)` (`Compiler/src/inferenceresult.jl:162-202`), and so
`matching_cache_argtypes(𝕃, mi)` (`inferenceresult.jl:3-6`), gives the cache argument types of a
method instance one entry per parameter of `specTypes`, padded to `method.nargs` when a `Vararg`
tail stands for the missing arguments: the length `mgLength`. -/
def MostGeneralLength : Prop :=
  ∀ n E nargs? spec, Returns (matchingCacheArgtypesMI n E nargs? spec) (fun r => r.length = mgLength nargs? spec)

theorem mostGeneralLength_proven : MostGeneralLength := mostGeneral_length

/-! ## `pick_const_arg` -/

/-- `pick_const_arg(𝕃, given, cache)` (`Compiler/src/inferenceresult.jl:49-62`) puts the cache
argument type in the key wherever the call's argument type carries no forwardable information,
and also where the two are lattice-equal. Only forwardable information that differs from the cache
argument type enters a const-prop key. -/
def PickConstArgKeepsCache : Prop :=
  (∀ ops n E L g c, isForwardableArgtype L g = false → pickConstArg ops n E L g c = pure c) ∧
  (∀ ops n E L g c s s', isForwardableArgtype L g = true →
    (isLatticeEqual n E L g c).run s = .ok (true, s') → (pickConstArg ops n E L g c).run s = .ok (c, s'))

theorem pickConstArgKeepsCache_proven : PickConstArgKeepsCache := by
  refine ⟨fun ops n E L g c hf => ?_, fun ops n E L g c s s' hf he => ?_⟩
  · unfold pickConstArg isArgtypeMatch
    simp [hf]
  · unfold pickConstArg isArgtypeMatch
    simp only [hf, ite_true]
    rw [run_bind_ok he]
    rfl

/-! ## Constant-return ABI -/

/-- `is_result_constabi_eligible(result)` (`Compiler/src/typeinfer.jl:483-486`) holds exactly when
the result is a `Const`, the effects say a call can be replaced by its value (consistent,
effect-free, terminating, no undefined behaviour except under `@inbounds`, and nothrow:
`is_foldable_nothrow`, `Compiler/src/effects.jl:338-348`), and `count_const_size` of the value
is within `MAX_INLINE_CONST_SIZE`. `result_is_constabi` adds `may_discard_trees`
(`Compiler/src/typeinfer.jl:1537-1538`). A `CodeInstance` that gets the constant-return ABI loses
its inferred source, so a call to it is only ever its constant. -/
def ConstabiEligibleIff : Prop :=
  ∀ n E C rt eff s b s',
    (isResultConstabiEligible n E C rt eff).run s = .ok (b, s') →
    ((b = true ↔ ∃ c k, rt = .const c ∧ isConsistent eff = true ∧ isEffectFree eff = true ∧
        isTerminates eff = true ∧ isNothrow eff = true ∧
        (isNoub eff = true ∨ isNoubIfNoinbounds eff = true) ∧
        (countConstSize n E C c).run s = .ok (k, s') ∧ k ≤ MAX_INLINE_CONST_SIZE) ∧
      ∀ md, (resultIsConstabi n E C md rt eff).run s = if md then .ok (b, s') else .ok (false, s))

theorem isFoldableNothrow_iff (eff : Effects) : isFoldableNothrow eff = true ↔
    isConsistent eff = true ∧ isEffectFree eff = true ∧ isTerminates eff = true ∧
      isNothrow eff = true ∧ (isNoub eff = true ∨ isNoubIfNoinbounds eff = true) := by
  simp only [isFoldableNothrow, isFoldable, Bool.and_eq_true, Bool.or_eq_true, Bool.not_false,
    Bool.true_or, and_true]
  constructor
  · rintro ⟨⟨⟨⟨h1, h5⟩, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h5⟩, h2⟩, h3⟩, h4⟩

theorem constabiEligibleIff_proven : ConstabiEligibleIff := by
  intro n E C rt eff s b s' h
  have hr : ∀ md, (resultIsConstabi n E C md rt eff).run s = if md then .ok (b, s') else .ok (false, s) := by
    intro md
    cases md
    · rfl
    · simp only [resultIsConstabi, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      exact h
  refine ⟨?_, hr⟩
  unfold isResultConstabiEligible at h
  cases rt with
  | const c =>
    by_cases hf : isFoldableNothrow eff = true
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false] at h
      unfold isInlineableConstant at h
      obtain ⟨k, s₁, hk, hb⟩ := run_bind_inv h
      simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have hf' := (isFoldableNothrow_iff eff).1 hf
      constructor
      · intro hb
        exact ⟨c, k, rfl, hf'.1, hf'.2.1, hf'.2.2.1, hf'.2.2.2.1, hf'.2.2.2.2, hk, by simpa using hb⟩
      · rintro ⟨c', k', hc, -, -, -, -, -, hk', hle⟩
        cases hc
        rw [hk] at hk'
        simp only [Except.ok.injEq, Prod.mk.injEq] at hk'
        simpa [hk'.1] using hle
    · simp only [hf, Bool.not_false, ite_true, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨c', k', hc, h1, h2, h3, h4, h5, -⟩
      exact hf ((isFoldableNothrow_iff eff).2 ⟨h1, h2, h3, h4, h5⟩)
  | _ =>
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp

/-! ## Dropping and compressing inferred source -/

/-- The two places that drop inferred source for the global cache agree. `discard_optimized_result`
(`Compiler/src/typeinfer.jl:582-588`) drops an optimized result whose inlining cost is
`MAX_INLINE_COST`; `maybe_compress_codeinfo` (`Compiler/src/typeinfer.jl:595-610`) drops a
`CodeInfo` of a method that is not inlineable (`is_inlineable(ci)` is
`ci.inlining_cost != MAX_INLINE_COST`). For the same method instance and inlining cost, one drops
the source exactly when the other does. And when the source is needed for output
(`keep_source_for_output`, a cache without native code), neither drops it. -/
def DiscardMatchesCompress : Prop :=
  (∀ mdt keepIr gen mayCompress (cs : Unit → Bool) cost,
    discardOptimizedResult mdt keepIr gen cs cost = true ↔
      maybeCompressCodeinfo true mdt (cost != MAX_INLINE_COST) keepIr gen mayCompress cs = .nothing_) ∧
  (∀ isM mdt keepIr gen mayCompress (cs : Unit → Bool) cost inl,
    keepSourceForOutput gen cs = true →
      discardOptimizedResult mdt keepIr gen cs cost = false ∧
      maybeCompressCodeinfo isM mdt inl keepIr gen mayCompress cs ≠ .nothing_)

theorem discardMatchesCompress_proven : DiscardMatchesCompress := by
  refine ⟨fun mdt keepIr gen mc cs cost => ?_, fun isM mdt keepIr gen mc cs cost inl hk => ?_⟩
  · unfold discardOptimizedResult maybeCompressCodeinfo keepSourceForOutput
    simp only [bne]
    by_cases hb : cost = MAX_INLINE_COST <;> rcases Bool.eq_false_or_eq_true (cs ()) with hc | hc <;>
      cases mdt <;> cases keepIr <;> cases gen <;> cases mc <;> simp [Id.run, hb, hc] <;> rfl
  · unfold keepSourceForOutput at hk
    unfold discardOptimizedResult maybeCompressCodeinfo
    simp only [keepSourceForOutput, hk]
    cases isM <;> cases mdt <;> cases keepIr <;> cases mc <;> cases inl <;> simp [Id.run]

/-! ## Registry -/

/-- Registry entries of the result-caching area. -/
def entries : List Entry := [
  { id := "compiler-cacheresult-elim-free-typevars", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["elim_free_typevars(@nospecialize t)"],
    statement := "elim_free_typevars(t) never has free type variables, and a type without free type variables comes back unchanged.",
    source := "comment Compiler/src/inferenceresult.jl:204-208",
    status := .proven, prop := ``ElimFreeTypevarsClosed, thm := some ``elimFreeTypevarsClosed_proven },
  { id := "compiler-cacheresult-lookup-sound", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["constprop_cache_lookup(𝕃::AbstractLattice, mi::MethodInstance, given_argtypes::Vector{Any}, cache::InferenceCache, world::UInt)", "is_argtype_match(𝕃::AbstractLattice, @nospecialize(given_argtype), @nospecialize(cache_argtype), overridden_by_const::Bool)"],
    statement := "A result constprop_cache_lookup returns is an entry for the same MethodInstance, made in the query's world and valid there, not a tombstone, whose key has the query's length and, at every position, is lattice-equal to a forwardable query argument or was not overridden by a constant. It returns missing only when such an entry is a tombstone.",
    source := "invariant: a const-prop cache hit stands for inference with the query's argument types (Compiler/src/inferenceresult.jl:217-261, comment at 250-252)",
    status := .proven, prop := ``ConstpropLookupSound, thm := some ``constpropLookupSound_proven,
    notes := "The model's lookup loops are written as recursion over the entries and positions (constpropLookupLoop, argtypesMatch); the difftest (op cr.lookup) agrees with the pinned Julia on 7500 cases over three seeds." },
  { id := "compiler-cacheresult-va-tail-miss", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["constprop_cache_lookup(𝕃::AbstractLattice, mi::MethodInstance, given_argtypes::Vector{Any}, cache::InferenceCache, world::UInt)", "is_argtype_match(𝕃::AbstractLattice, @nospecialize(given_argtype), @nospecialize(cache_argtype), overridden_by_const::Bool)", "pick_const_args!(𝕃::AbstractLattice, given_argtypes::Vector{Any}, cache_argtypes::Vector{Any})"],
    statement := "A const-prop result that const_prop_call caches under the key matching_cache_argtypes builds, with the overridden_by_const flags it computes (abstractinterpretation.jl:1517-1522), is found again by constprop_cache_lookup for the same key.",
    source := "invariant: constprop_cache_lookup exists to reuse a result under its key (Compiler/src/inferenceresult.jl:217-261; Compiler/src/abstractinterpretation.jl:1499-1543)",
    status := .refuted, prop := ``ConstpropKeyRehits, thm := some ``constpropKeyRehits_refuted,
    issue := "none found (queries: constprop_cache_lookup Vararg; overridden_by_const; const prop cache vararg splat; argtype_by_index overridden; issues and PRs)",
    notes := "Counterexample: cache argument types [Int64, Vararg{Int64}]; the key is the same, its flags are [false, true] because argtype_by_index unwraps the Vararg, and the lookup rejects the non-forwardable Vararg tail. A missed cache entry, so a perf issue, not an unsound one. Reproduced on 1.13.3, the pinned f755f49a9e and nightly 290d5bb5f5; master eb844b8ebd has the same lines. The difftest op cr.rehit runs this chain against Julia: 51000/51000 agree over three seeds, with 676 of the 1464 keys that have a flag set missed." },
  { id := "compiler-cacheresult-nospecializeinfer-widens", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["get_nospecializeinfer_argtypes(argtypes::Vector{Any}, cache_argtypes::Vector{Any}, method::Method)"],
    statement := "For a method that is not @nospecializeinfer (or has no @nospecialize argument) get_nospecializeinfer_argtypes returns argtypes. Otherwise the result has the length of cache_argtypes, holds the cache argument type at every position whose argument index min(i-1, nargs-1) is positive with its @nospecialize bit set, and the given argument type at every other position.",
    source := "comment Compiler/src/inferenceresult.jl:8-10",
    status := .proven, prop := ``NospecializeinferWidens, thm := some ``nospecializeinferWidens_proven },
  { id := "compiler-cacheresult-pick-const-arg-keeps-cache", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["pick_const_arg(𝕃::AbstractLattice, @nospecialize(given_argtype), @nospecialize(cache_argtype))"],
    statement := "pick_const_arg returns the cache argument type when the given argument type is not forwardable, and when it is forwardable and lattice-equal to the cache argument type. Only forwardable information that differs from the method instance's argument type enters a const-prop key.",
    source := "comment Compiler/src/inferenceresult.jl:51 (prefer the given argtype only when it does not match)",
    status := .proven, prop := ``PickConstArgKeepsCache, thm := some ``pickConstArgKeepsCache_proven },
  { id := "compiler-cacheresult-key-length", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["pick_const_args!(𝕃::AbstractLattice, given_argtypes::Vector{Any}, cache_argtypes::Vector{Any})", "matching_cache_argtypes(𝕃::AbstractLattice, ::MethodInstance, simple_argtypes::Union{SimpleArgtypes, WidenedArgtypes}, cache_argtypes::Vector{Any})"],
    statement := "pick_const_args! returns a key of length 0 when either list is empty, max(ngiven-1, ncache-1)+1 when both end in Vararg, ncache when only the given types do, and ngiven otherwise, returning only when ngiven == ncache if neither ends in Vararg. So for cache argument types not ending in Vararg, matching_cache_argtypes gives every nonempty argument list a key of the cache's length, and the lookup's length assertion cannot fail for such keys.",
    source := "@assert at Compiler/src/inferenceresult.jl:89 and the comment and @assert at inferenceresult.jl:231-239 (only a Vararg specTypes may give keys of different lengths)",
    status := .proven, prop := ``ConstpropKeyLength, thm := some ``constpropKeyLength_proven },
  { id := "compiler-cacheresult-va-process-length", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["va_process_argtypes(𝕃::AbstractLattice, given_argtypes::Vector{Any}, nargs::UInt, isva::Bool, mi::MethodInstance)"],
    statement := "va_process_argtypes returns exactly nargs argument types (the trailing arguments of a varargs method folded into one tuple type), and throws otherwise.",
    source := "invariant: one argument type per slot of the method (Compiler/src/inferenceresult.jl:111-160, AssertionError at 155-158)",
    status := .proven, prop := ``VaProcessLength, thm := some ``vaProcessLength_proven },
  { id := "compiler-cacheresult-most-general-length", juliaFile := "Compiler/src/inferenceresult.jl",
    juliaFns := ["most_general_argtypes(method::Union{Method,Nothing}, @nospecialize(specTypes))", "matching_cache_argtypes(::AbstractLattice, mi::MethodInstance)"],
    statement := "most_general_argtypes(method, specTypes), and so matching_cache_argtypes(𝕃, mi), returns method.nargs argument types when specTypes has fewer parameters and ends in a Vararg, and one per parameter of specTypes otherwise.",
    source := "invariant: the cache argument types have one entry per argument slot (Compiler/src/inferenceresult.jl:162-202, the resize at 167-169 and the fill loop at 198-200)",
    status := .proven, prop := ``MostGeneralLength, thm := some ``mostGeneralLength_proven,
    notes := "Only the length is stated. That the last element is Vararg{widenconst(T)} and the padded positions hold the unwrapped element type is not stated." },
  { id := "compiler-cacheresult-count-const-size-bound", juliaFile := "Compiler/src/utilities.jl",
    juliaFns := ["count_const_size(@nospecialize(x), count_self::Bool = true)", "is_inlineable_constant(@nospecialize(x))"],
    statement := "count_const_size(x, count_self) returns at most MAX_INLINE_CONST_SIZE + 1, or the exact size of an isbits value: every walk over fields stops at the first partial sum over the limit. is_inlineable_constant(x) is true exactly when count_const_size(x) is at most MAX_INLINE_CONST_SIZE.",
    source := "comment Compiler/src/utilities.jl:40-50 (prevent rooting large amounts of data) and MAX_INLINE_CONST_SIZE at utilities.jl:35",
    status := .proven, prop := ``CountConstSizeBound, thm := some ``countConstSizeBound_proven,
    notes := "Layout facts and the fields of mutable objects come from tables the difftest fills from the pinned Julia. Monotonicity in count_self (count_const_size(x, false) <= count_const_size(x, true)) is not stated: it needs a simulation of two runs of the field loop." },
  { id := "compiler-cacheresult-constabi-eligible", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["is_result_constabi_eligible(result::InferenceResult)", "result_is_constabi(interp::AbstractInterpreter, result::InferenceResult)"],
    statement := "is_result_constabi_eligible(result) is true exactly when the result is a Const, the effects are consistent, effect-free, terminating and nothrow with noub or noub-if-noinbounds (is_foldable_nothrow without the rtcall check), and count_const_size of the value is at most MAX_INLINE_CONST_SIZE; result_is_constabi is that and may_discard_trees.",
    source := "Compiler/src/typeinfer.jl:483-486 and 1537-1538 with Compiler/src/effects.jl:338-348",
    status := .proven, prop := ``ConstabiEligibleIff, thm := some ``constabiEligibleIff_proven,
    notes := "is_inlineable_constant (Compiler/src/utilities.jl:77-79) is unfolded in this proof. The C side (gf.c jl_fill_codeinst, staticdata.c) reads only invoke == jl_fptr_const_return and does not re-derive effects for this decision." },
  { id := "compiler-cacheresult-discard-compress-agree", juliaFile := "Compiler/src/typeinfer.jl",
    juliaFns := ["discard_optimized_result(interp::AbstractInterpreter, mi::MethodInstance, inlining_cost::InlineCostType)", "maybe_compress_codeinfo(interp::AbstractInterpreter, mi::MethodInstance, ci::CodeInfo)", "keep_source_for_output(mi::MethodInstance)"],
    statement := "For a method instance and an inlining cost, discard_optimized_result drops the optimized result exactly when maybe_compress_codeinfo returns nothing for a CodeInfo with that cost (is_inlineable is cost != MAX_INLINE_COST); and when keep_source_for_output holds neither drops the source.",
    source := "comment Compiler/src/typeinfer.jl:590-591 (a cache without native code needs every compileable source) and the two drop sites typeinfer.jl:582-610",
    status := .proven, prop := ``DiscardMatchesCompress, thm := some ``discardMatchesCompress_proven,
    notes := "So on the optimized path of transform_result_for_cache, where the CodeInfo carries the cost just checked, the drop branch of maybe_compress_codeinfo can never fire; it fires only for sources that were not optimized. keep_source_for_output's true branch is not difftested (jl_generating_output() is 0 in the difftest)." }
]

end JuliaLean.Proofs.Compiler.src.inferenceresult
