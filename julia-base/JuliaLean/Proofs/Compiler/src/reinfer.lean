import JuliaLean.Registry.Types
import JuliaLean.Compiler.src.reinfer
import JuliaLean.Proofs.Compiler.src.reinfer.Monad

/-!
Properties of `Compiler/src/reinfer.jl`: edge verification when a package image loads. The model
is `JuliaLean/Compiler/src/reinfer.lean`.

The C lookups are the model's `Oracle`. Generic statements take it as a parameter. The soundness
statement takes, as a hypothesis, a set of promises the runtime keeps about the method table
(`RuntimeConsistent`), and the refutation exhibits a heap and oracle that keep them.
-/

namespace JuliaLean.Proofs.Compiler.src.reinfer

open JuliaLean.Registry JuliaLean.Compiler.CICache JuliaLean.Compiler.Reinfer
open JuliaLean.Proofs.Compiler.src.reinfer.Monad
open JuliaLean.C (Val)

/-! ## The runtime's promises -/

/-- What the runtime keeps true about the objects and the C lookups, as far as the verifier relies
on it:
- every world in play is between the require world and the world counter;
- a lookup in world `w` returns only methods active in `w`;
- a method `u` that a lookup of `sig` returns, other than a method `m` that covers `sig` and is
  active in that world, is recorded in `m`'s interference set (the set holds the intersecting
  methods `m` is not more specific than, `Compiler/src/reinfer.jl:527-529`), and the set's
  allocated length is at least its assigned prefix;
- a method with an empty interference set, active in `w` and covering `sig`, is the whole result
  of the lookup of `sig` in `w` (`Compiler/src/reinfer.jl:492-496`);
- a method instance with `METHOD_SIG_LATEST_ONLY` is the only match of its `specTypes` in the
  current world (`Compiler/src/reinfer.jl:461-463`). -/
structure RuntimeConsistent (O : Oracle) (H : Heap) : Prop where
  worlds : H.requireWorld ≤ H.worldCounter
  ciWorlds : ∀ c ∈ H.cis.toList, H.requireWorld ≤ c.minWorld ∧ c.minWorld ≤ H.worldCounter
  primary : ∀ m ∈ H.methods.toList, m.primaryWorld ≤ H.worldCounter
  lookupActive : ∀ sig lim w l lo hi amb, O.matchingMethods sig lim w = .ok (some l, lo, hi, amb) →
    ∀ u ∈ l, ∃ m ∈ H.methods.toList, m.uid = u ∧ m.primaryWorld ≤ w
  interferenceComplete : ∀ sig lim w l lo hi amb,
    O.matchingMethods sig lim w = .ok (some l, lo, hi, amb) →
    ∀ m ∈ H.methods.toList, m.primaryWorld ≤ w → O.sub sig m.sig = .ok true →
    ∀ u ∈ l, u ≠ m.uid → u ∈ m.interferences
  interferencesLen : ∀ m ∈ H.methods.toList, m.interferences.length ≤ m.interferencesLen
  emptySetDominates : ∀ sig w, ∀ m ∈ H.methods.toList, m.interferencesLen = 0 →
    m.primaryWorld ≤ w → O.sub sig m.sig = .ok true →
    ∃ lo hi, O.matchingMethods sig 1 w = .ok (some [m.uid], lo, hi, 0)
  latestOnly : ∀ mi ∈ H.mis.toList, hasBit mi.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = true →
    ∃ lo hi, O.matchingMethods mi.specTypes.t 1 H.worldCounter = .ok (some [mi.def_], lo, hi, 0)

/-! ## Soundness: accepted code matches the current method table -/

/-- The verifier's run on a fresh workspace. -/
def runVerify (O : Oracle) (H : Heap) (fuel ci vw : Nat) :
    Except String ((Nat × Nat × Nat) × RS Workspace) :=
  (verifyMethod O fuel ci vw).run ⟨H, #[], {}⟩

/-- Soundness of `verify_method` (property 1): when it accepts a code instance in the validation
world `vw` (the current world), then for every call edge `mi` of that code instance (a call whose
only match was `mi.def` when the image was built, `Compiler/src/reinfer.jl:296-299`), the
lookup of `mi.specTypes` in `vw` still gives exactly `mi.def`. -/
def VerifyMethodSound : Prop :=
  ∀ (O : Oracle) (H : Heap), RuntimeConsistent O H →
    ∀ (fuel ci : Nat) (r : Nat × Nat × Nat) (s' : RS Workspace),
    runVerify O H fuel ci H.worldCounter = .ok (r, s') → H.worldCounter ≤ r.2.2 →
    ∀ c, H.ciR ci = .ok c → ∀ m, Edge.mi m ∈ c.callees.toList → ∀ mi, H.miR m = .ok mi →
    ∀ l lo hi amb, O.matchingMethods mi.specTypes.t 1 H.worldCounter = .ok (some l, lo, hi, amb) →
      l = [mi.def_] ∧ amb = 0

namespace StaleMinWorld

/-- Type stand-ins: `Tuple{typeof(h), Integer}` (method 1), `Tuple{typeof(h), Int}` (method 2),
`Tuple{typeof(g), Any}` (method 3) and the call signature `Tuple{typeof(h), Int}` of the edge. -/
def sigHInteger : Val := .long 1
def sigHInt : Val := .long 2
def sigG : Val := .long 3
def sigCall : Val := .long 100

/-- `h(::Integer)` defined in world 1, `h(::Int)` added in world 3, the caller `g`. -/
def methods : Array MethodR := #[
  { m := { uid := 1, sig := sigHInteger, primaryWorld := 1, dispatchStatus := 1, interferences := [2] },
    interferencesLen := 1, didScanSource := 1, blob := typemaxUInt, hasMethodTable := true,
    source := none, hasImageGlobalref := false },
  { m := { uid := 2, sig := sigHInt, primaryWorld := 3, dispatchStatus := 1, interferences := [] },
    interferencesLen := 0, didScanSource := 1, blob := typemaxUInt, hasMethodTable := true,
    source := none, hasImageGlobalref := false },
  { m := { uid := 3, sig := sigG, primaryWorld := 1, dispatchStatus := 1, interferences := [] },
    interferencesLen := 0, didScanSource := 1, blob := typemaxUInt, hasMethodTable := true,
    source := none, hasImageGlobalref := false }]

/-- The code instance of `g(::Int)`, activated in world 2, still carrying the revalidation
sentinel, with the one call edge `h(::Int) -> h(::Integer)` recorded when it was built. -/
def heap : Heap where
  worldCounter := 3
  requireWorld := 1
  methods := methods
  mis := #[{ id := 10, def_ := 1, specTypes := ⟨100, sigCall⟩, dispatchStatus := 0 },
           { id := 11, def_ := 3, specTypes := ⟨101, sigG⟩, dispatchStatus := 0 }]
  cis := #[{ id := 20, mi := 11, ownerNothing := true, minWorld := 2, maxWorld := 1, flags := 0,
             edges := some #[.mi 10], blob := typemaxUInt }]
  bindings := #[]

/-- The method table: `h(::Int)` matches the call from world 3 on, `h(::Integer)` before. -/
def oracle : Oracle where
  sub _ t := .ok (match t with | .long 1 => true | .long 2 => true | _ => false)
  isect _ t := .ok t
  egal _ _ := .ok false
  matchingMethods _ _ w := .ok (if 3 ≤ w then (some [2], 3, typemaxUInt, 0)
    else if 1 ≤ w then (some [1], 1, 2, 0) else (some [], 0, 0, 0))
  findsup _ _ := .ok (none, 1, 0)
  sigContributorsWorld _ _ := .ok 0
  linkageBlobDepWorld _ _ := .ok 0
  bindingAccessRange _ _ := .ok ⟨1, typemaxUInt⟩

theorem consistent : RuntimeConsistent oracle heap := by
  constructor
  · decide
  · intro c hc
    simp [heap] at hc
    subst hc; decide
  · intro m hm
    simp [heap, methods] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  · intro sig lim w l lo hi amb h u hu
    simp only [oracle] at h
    split at h
    · cases h; simp at hu; subst hu
      exact ⟨methods[1]!, by simp [heap, methods], rfl, by simp [methods, MethodR.primaryWorld]; omega⟩
    · split at h <;> cases h <;> simp at hu
      subst hu
      exact ⟨methods[0]!, by simp [heap, methods], rfl, by simp [methods, MethodR.primaryWorld]; omega⟩
  · intro sig lim w l lo hi amb h m hm hpw hsub u hu hne
    simp [heap, methods] at hm
    simp only [oracle] at h
    rcases hm with rfl | rfl | rfl
    · split at h
      · cases h; simp at hu; subst hu; decide
      · split at h <;> cases h <;> simp at hu
        subst hu; exact absurd rfl hne
    · split at h
      · cases h; simp at hu; subst hu; exact absurd rfl hne
      · rename_i hw
        simp [MethodR.primaryWorld] at hpw; omega
    · simp [oracle, sigG, MethodR.sig] at hsub
  · intro m hm
    simp [heap, methods] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  · intro sig w m hm hlen hpw hsub
    simp [heap, methods] at hm
    rcases hm with rfl | rfl | rfl
    · simp at hlen
    · simp [MethodR.primaryWorld] at hpw
      exact ⟨3, typemaxUInt, by simp [oracle, hpw]; rfl⟩
    · simp [oracle, sigG, MethodR.sig] at hsub
  · intro mi hmi hbit
    simp [heap] at hmi
    rcases hmi with rfl | rfl <;> simp [hasBit, JuliaLean.Compiler.Reinfer.methodSigLatestOnly] at hbit

/-- The verifier accepts the code instance up to the validation world 3. -/
theorem accepts :
    (match runVerify oracle heap 50 20 3 with
     | .ok ((c, mn, mx), _) => c == 0 && mn == 1 && mx == 3
     | .error _ => false) = true := by
  decide +kernel

end StaleMinWorld

/-- Counterexample: a code instance activated in world 2 calls `h(::Int)`, whose only match was
`h(::Integer)`; `h(::Int)` is added in world 3, before the edges are verified in world 3. The
lookups of `verify_call` run in `codeinst.min_world` = 2 (`Compiler/src/reinfer.jl:235`), and the
interference scan stops at `h(::Int)` because its `primary_world` is past that world
(`reinfer.jl:814`), so the edge is accepted and the code instance gets `[1, 3]`, although in
world 3 the call dispatches to `h(::Int)`. Reproduced on the pinned Julia, with stale code running
after a package load (`repro/compiler-reinfer-stale-min-world.jl`). -/
theorem verifyMethodSound_refuted : ¬ VerifyMethodSound := by
  intro h
  have hacc := StaleMinWorld.accepts
  generalize hr : runVerify StaleMinWorld.oracle StaleMinWorld.heap 50 20 3 = res at hacc
  match res, hr, hacc with
  | .ok ((c, mn, mx), s'), hr, hacc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hacc
    obtain ⟨⟨_, _⟩, hmx⟩ := hacc
    have := h StaleMinWorld.oracle StaleMinWorld.heap StaleMinWorld.consistent 50 20 (c, mn, mx) s'
      hr (by simp [StaleMinWorld.heap, hmx])
      { id := 20, mi := 11, ownerNothing := true, minWorld := 2, maxWorld := 1, flags := 0,
        edges := some #[.mi 10], blob := typemaxUInt } rfl 10 (by simp [CIR.callees])
      { id := 10, def_ := 1, specTypes := ⟨100, StaleMinWorld.sigCall⟩, dispatchStatus := 0 } rfl
      [2] 3 typemaxUInt 0 rfl
    simp at this


/-- Soundness of what the loader keeps (property 1, end to end): after `insert_backedges`
(`Compiler/src/reinfer.jl:117-126`) runs over the loaded code instances (through
`scan_new_methods!`, `scan_new_code!`, `verify_method_graph`, `verify_method` and
`jl_promote_ci_to_current`), every one of them that is valid in the current world has call edges
whose lookup in the current world still gives exactly the method recorded when the image was
built. -/
def InsertBackedgesSound : Prop :=
  ∀ (O : Oracle) (H : Heap), RuntimeConsistent O H →
    ∀ (fuel : Nat) (internal : List InternalItem) (s' : RS Workspace),
    (insertBackedges O fuel internal).run ⟨H, #[], {}⟩ = .ok ((), s') →
    ∀ ci, InternalItem.ci ci ∈ internal → ∀ c', s'.heap.ciR ci = .ok c' →
      c'.minWorld ≤ H.worldCounter → H.worldCounter ≤ c'.maxWorld →
    ∀ c, H.ciR ci = .ok c → ∀ m, Edge.mi m ∈ c.callees.toList → ∀ mi, H.miR m = .ok mi →
    ∀ l lo hi amb, O.matchingMethods mi.specTypes.t 1 H.worldCounter = .ok (some l, lo, hi, amb) →
      l = [mi.def_] ∧ amb = 0

namespace StaleMinWorld

/-- `insert_backedges([g's code instance])` succeeds and leaves the code instance valid from
world 1 to `typemax(UInt)`, promoted by `jl_promote_ci_to_current`. -/
theorem insert_accepts :
    (match (insertBackedges oracle 50 [.ci 20]).run ⟨heap, #[], {}⟩ with
     | .ok (_, s') => (match s'.heap.ciR 20 with
        | .ok c => decide (c.minWorld ≤ 3 ∧ 3 ≤ c.maxWorld)
        | .error _ => false)
     | .error _ => false) = true := by
  decide +kernel

end StaleMinWorld

/-- Counterexample: the same heap as `verifyMethodSound_refuted`, run through the loader's entry
point. `insert_backedges` keeps `g`'s code instance valid in world 3 and later, while its call
`h(::Int)` dispatches to `h(::Integer)` in the image and to `h(::Int)` in world 3. -/
theorem insertBackedgesSound_refuted : ¬ InsertBackedgesSound := by
  intro h
  have hacc := StaleMinWorld.insert_accepts
  generalize hr : (insertBackedges StaleMinWorld.oracle 50 [.ci 20]).run ⟨StaleMinWorld.heap, #[], {}⟩ = res at hacc
  match res, hr, hacc with
  | .ok ((), s'), hr, hacc =>
    simp only at hacc
    generalize hc : s'.heap.ciR 20 = rc at hacc
    match rc, hc, hacc with
    | .ok c', hc, hacc =>
      simp only [decide_eq_true_eq] at hacc
      have := h StaleMinWorld.oracle StaleMinWorld.heap StaleMinWorld.consistent 50 [.ci 20] s' hr 20
        (by simp) c' hc (by simpa [StaleMinWorld.heap] using hacc.1) (by simpa [StaleMinWorld.heap] using hacc.2)
        { id := 20, mi := 11, ownerNothing := true, minWorld := 2, maxWorld := 1, flags := 0,
          edges := some #[.mi 10], blob := typemaxUInt } rfl 10 (by simp [CIR.callees])
        { id := 10, def_ := 1, specTypes := ⟨100, StaleMinWorld.sigCall⟩, dispatchStatus := 0 } rfl
        [2] 3 typemaxUInt 0 rfl
      simp at this

/-! ## Interference sets -/

/-- `eachinterference(m, cutoff)` yields the assigned entries of `m.interferences` in definition
order, stopping before the first one whose `primary_world` is past `cutoff` (the longest prefix
visible in that world); `method_in_interferences(m2, m1)` is membership of `m2` in `m1`'s set;
`method_morespecific_recorded` is irreflexive and asymmetric. -/
def InterferenceSets : Prop :=
  (∀ (H : Heap) (m : MethodR) (cutoff : Nat) (f : Nat → MethodR),
    (∀ k ∈ m.interferences, H.method k = .ok (f k)) →
    eachinterference H m cutoff =
      .ok ((m.interferences.map f).takeWhile (fun x => decide (x.primaryWorld ≤ cutoff)))) ∧
  (∀ (H : Heap) (m2 m1 : MethodR),
    (∀ k ∈ m1.interferences, ∃ x, H.method k = .ok x ∧ x.primaryWorld ≤ typemaxUInt) →
    methodInInterferences H m2 m1 = .ok (decide (m2.uid ∈ m1.interferences))) ∧
  (∀ (H : Heap) (a b : MethodR), methodMorespecificRecorded H a b = .ok true →
    methodMorespecificRecorded H b a = .ok false ∧ a.uid ≠ b.uid)

theorem interferenceSets_proven : InterferenceSets :=
  ⟨fun H m c f hf => ei_spec H m c f hf, fun H m2 m1 hf => mii_spec H m2 m1 hf,
   fun H a b h => msr_asymm H a b h⟩

/-! ## Edge checks -/

set_option hygiene false in
macro "rinf_opath" : tactic => `(tactic| (right; cases hm : O.matchingMethods sig.t lim world with
  | error e => simp [hm] at h
  | ok v => (simp [hm] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, by simp [List.lookup]⟩)))


set_option hygiene false in
macro "rinf_accpath" : tactic => `(tactic| (
  try simp only [st_bind_assoc, get_bind, stpure_bind] at h
  by_cases hw : s.heap.requireWorld ≤ world
  all_goals simp [hw, jlThrow, get_proj_bind, st_bind_assoc, st_throw_bind] at h
  all_goals (
    cases hr : O.bindingAccessRange b world with
    | error e => simp [hr] at h
    | ok wr =>
      simp [hr] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, fun h0 => Or.inr ⟨wr, rfl, by simp at h0; omega⟩,
        fun h1 => ⟨wr, rfl, by simp at h1; omega⟩⟩)))


/-- When `expected_is_minmax(meth, m, sig, expected)` returns true, `sig <: meth.sig`, `sig <: m.sig` is false, and `meth` recorded-beats every other expected method that fully covers `sig` (the three conditions its comment lists). -/
def ExpectedIsMinmaxSound : Prop :=
  ∀ (O : Oracle) (H : Heap) (meth im : MethodR) (sig : Val) (expected : List MethodR),
    expectedIsMinmax O H meth im sig expected = .ok true →
    O.sub sig meth.sig = .ok true ∧ O.sub sig im.sig = .ok false ∧
    ∀ meth2 ∈ expected, meth2.uid ≠ meth.uid → O.sub sig meth2.sig = .ok true →
      methodMorespecificRecorded H meth meth2 = .ok true

theorem minmax_true : ExpectedIsMinmaxSound := by
  intro O H meth im sig expected
  unfold expectedIsMinmax
  intro h
  cases h1 : O.sub sig meth.sig with
  | error e => simp [h1] at h
  | ok b1 =>
    cases b1 <;> simp only [h1, ok_bind, Bool.not_false, Bool.not_true, if_true, if_false] at h
    · simp at h
    cases h2 : O.sub sig im.sig with
    | error e => simp [h2] at h
    | ok b2 =>
      cases b2 <;> simp only [h2, ok_bind, if_true, if_false] at h
      · refine ⟨rfl, rfl, ?_⟩
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i st hfor
            cases hst1 : st.fst with
            | some r =>
              rw [hst1] at h; simp at h; subst h
              have key := forIn_some _ ?_ expected st hfor (by simp [hst1])
              · obtain ⟨x, _, hx⟩ := key
                revert hx; rinf_loopcase
              · intro x s' hx; revert hx; rinf_loopcase
            | none =>
              have hall := forIn_none _ ?_ ?_ expected st hfor hst1
              · intro meth2 hm hne hsub
                have := hall meth2 hm
                revert this; rinf_loopcase
              · intro x s' hx; revert hx; rinf_loopcase
              · intro x s' hx; revert hx; rinf_loopcase
      · simp at h

/-- When `has_empty_set_cover(m, ti, expected)` returns true, some expected method has an empty interference set, recorded-beats `m`, and covers `ti`. -/
def HasEmptySetCoverSound : Prop :=
  ∀ (O : Oracle) (H : Heap) (im : MethodR) (ti : Val) (expected : List MethodR),
    hasEmptySetCover O H im ti expected = .ok true →
    ∃ meth2 ∈ expected, meth2.interferencesLen = 0 ∧
      methodMorespecificRecorded H meth2 im = .ok true ∧ O.sub ti meth2.sig = .ok true

theorem cover_true : HasEmptySetCoverSound := by
  intro O H im ti expected
  unfold hasEmptySetCover
  intro h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i st hfor
    cases hst1 : st.fst with
    | none => rw [hst1] at h; simp at h
    | some r =>
      have key := forIn_some _ ?_ expected st hfor (by simp [hst1])
      · obtain ⟨x, hxm, hx⟩ := key
        refine ⟨x, hxm, ?_⟩
        revert hx; rinf_loopcase
      · intro x s' hx; revert hx; rinf_loopcase

/-- When `morespecific_cannot_cycle(m, world)` returns true, every method of `m`'s interference set visible in `world` has an empty interference set or has `m` in its own set (is not strictly more specific than `m`). -/
def MorespecificCannotCycleSound : Prop :=
  ∀ (H : Heap) (im : MethodR) (world : Nat) (ms : List MethodR) (hei : eachinterference H im world = .ok ms),
    morespecificCannotCycle H im world = .ok true →
    ∀ msp ∈ ms, msp.interferencesLen = 0 ∨ methodInInterferences H im msp = .ok true

theorem cannotCycle_true : MorespecificCannotCycleSound := by
  intro H im world ms hei
  unfold morespecificCannotCycle
  intro h
  rw [hei] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i st hfor
    cases hst1 : st.fst with
    | some r =>
      rw [hst1] at h; simp at h; subst h
      have key := forIn_some _ ?_ ms st hfor (by simp [hst1])
      · obtain ⟨x, _, hx⟩ := key
        revert hx; rinf_loopcase
      · intro x s' hx; revert hx; rinf_loopcase
    | none =>
      have hall := forIn_none _ ?_ ?_ ms st hfor hst1
      · intro msp hm
        have := hall msp hm
        revert this; rinf_loopcase
      · intro x s' hx; revert hx; rinf_loopcase
      · intro x s' hx; revert hx; rinf_loopcase

/-- When `newmethod_removed_silently(meth, m, ti, sig, expected, world)` returns true, `has_empty_set_cover` and `morespecific_cannot_cycle` returned true, and so did `expected_is_minmax` when `meth` is in `m`'s set (the mutually ambiguous case). -/
def NewmethodRemovedSilentlySound : Prop :=
  ∀ (O : Oracle) (H : Heap) (meth im : MethodR) (ti sig : Val) (expected : List MethodR) (world : Nat),
    newmethodRemovedSilently O H meth im ti sig expected world = .ok true →
    (methodInInterferences H meth im = .ok true → expectedIsMinmax O H meth im sig expected = .ok true) ∧
    hasEmptySetCover O H im ti expected = .ok true ∧ morespecificCannotCycle H im world = .ok true

theorem silent_true : NewmethodRemovedSilentlySound := by
  intro O H meth im ti sig expected world
  unfold newmethodRemovedSilently
  intro h
  cases h1 : methodInInterferences H meth im with
  | error e => rw [h1] at h; cases h
  | ok b1 =>
    rw [h1] at h
    simp only [ok_bind] at h
    have hrest : ∀ h' : (do
        if !(← hasEmptySetCover O H im ti expected) then return false
        morespecificCannotCycle H im world : Except String Bool) = .ok true,
        hasEmptySetCover O H im ti expected = .ok true ∧ morespecificCannotCycle H im world = .ok true := by
      intro h'
      cases h2 : hasEmptySetCover O H im ti expected with
      | error e => rw [h2] at h'; cases h'
      | ok b2 =>
        rw [h2] at h'
        cases b2 <;> simp at h' <;> simp [h']
    cases b1
    · simp only [Bool.false_eq_true, if_false] at h
      exact ⟨fun e => absurd e (by simp), hrest h⟩
    · simp only [if_true] at h
      cases h3 : expectedIsMinmax O H meth im sig expected with
      | error e => rw [h3] at h; cases h
      | ok b3 =>
        rw [h3] at h
        cases b3
        · simp at h
        · simp only [ok_bind, Bool.not_true, Bool.false_eq_true, if_false] at h
          exact ⟨fun _ => rfl, hrest h⟩

/-- `promote_mi_to_current(mi, minworld, world)` changes nothing, or (only when `mi` is a method instance, the world counter is still `world`, the method's interference set is nonempty, `minworld` is its `primary_world`, and the instance lacks `METHOD_SIG_LATEST_ONLY`) sets that instance's `dispatch_status` to exactly `METHOD_SIG_LATEST_ONLY` and nothing else. -/
def PromoteMiEffect : Prop :=
  ∀ (mi : Option Nat) (mw w : Nat) (s s' : RS Workspace),
    (promoteMiToCurrent mi mw w).run s = .ok ((), s') →
    s'.heap = s.heap ∨
    ∃ m miR d, mi = some m ∧ s.heap.worldCounter = w ∧ s.heap.miR m = .ok miR ∧
      s.heap.method miR.def_ = .ok d ∧ d.interferencesLen ≠ 0 ∧ mw = d.primaryWorld ∧
      hasBit miR.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = false ∧
      s'.heap = s.heap.setMI { miR with dispatchStatus := JuliaLean.Compiler.Reinfer.methodSigLatestOnly }

theorem promote_spec : PromoteMiEffect := by
  intro mi mw w s s'
  intro h
  unfold promoteMiToCurrent at h
  cases mi with
  | none => simp at h; cases h; exact Or.inl rfl
  | some m =>
    simp only [getHeap, liftE, modifyHeap, emit, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.pure, StateT.run, StateT.lift, Except.bind,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h
    split at h
    · simp [StateT.pure, pure, Except.pure] at h; cases h; exact Or.inl rfl
    · cases hm : s.heap.miR m with
      | error e => simp [hm, StateT.lift, StateT.bind, bind] at h
      | ok miR =>
        simp only [hm, StateT.lift, StateT.bind, bind, pure_ok, ok_bind'] at h
        cases hd : s.heap.method miR.def_ with
        | error e => simp [hd] at h
        | ok d =>
          simp only [hd, ok_bind', pure_ok] at h
          split at h
          · simp [StateT.pure, pure, Except.pure] at h; cases h; exact Or.inl rfl
          · rename_i hc
            split at h
            · rename_i hw
              simp only [StateT.bind, StateT.modifyGet, bind, pure_ok, ok_bind', pure] at h
              cases h
              right
              simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or] at hc
              refine ⟨m, miR, d, rfl, by simpa using hw, hm, hd, hc.1.1, by have := hc.1.2; omega,
                by simpa using hc.2, rfl⟩
            · simp [StateT.pure, pure, Except.pure] at h; cases h; exact Or.inl rfl

/-- When `verify_invokesig(invokesig, expected, world, ...)` accepts (returns `max_world != 0`), the signature is a type and either it is `expected.sig` with `expected` still the latest `which` (range `[primary_world, typemax]`), or `expected` is still the latest `which`, has a method table and every contributor to the signature was present in the image (same range), or `_findsup(invokesig, mt, world)` returned `expected` itself and the range is the lookup's. -/
def VerifyInvokesigSound : Prop :=
  ∀ (O : Oracle) (isig : Edge) (exp : MethodR) (world image : Nat) (s s' : RS Workspace) (r : Nat × Nat),
    (verifyInvokesig O isig exp world image).run s = .ok (r, s') → r.2 ≠ 0 →
    ∃ t, isig = .ty t ∧ (
      (O.egal t.t exp.sig = .ok true ∧ methodIsLatestWhich exp = true ∧ r = (exp.primaryWorld, typemaxUInt)) ∨
      (exp.hasMethodTable = true ∧ methodIsLatestWhich exp = true ∧
        (∃ c, sigContributorsWorld O t.t image = .ok c ∧ c ≠ 0) ∧ r = (exp.primaryWorld, typemaxUInt)) ∨
      (exp.hasMethodTable = true ∧ ∃ lo hi, O.findsup t.t world = .ok (some exp.uid, lo, hi) ∧ r = (lo, hi)))

theorem invoke_spec : VerifyInvokesigSound := by
  intro O isig exp world image s s' r
  intro h hr
  unfold verifyInvokesig at h
  cases isig with
  | ty t =>
    refine ⟨t, rfl, ?_⟩
    rinf_vmsimp at h
    cases he : O.egal t.t exp.sig with
    | error e => simp [he] at h
    | ok b =>
      simp only [he, ok_bind'] at h
      rinf_vmsimp2 at h
      by_cases hl : methodIsLatestWhich exp = true
      · by_cases hpw : exp.primaryWorld ≤ world
        · cases b
          · by_cases hmt : exp.hasMethodTable = true
            · cases hc : sigContributorsWorld O t.t image with
              | error e => simp [hl, hmt, hc] at h
              | ok c =>
                by_cases c0 : c = 0
                · subst c0
                  cases hf : O.findsup t.t world with
                  | error e => simp [hl, hmt, hc, hf] at h
                  | ok fr =>
                    obtain ⟨mt, lo, hi⟩ := fr
                    right; right
                    refine ⟨hmt, lo, hi, ?_⟩
                    cases mt with
                    | none => simp [hl, hmt, hc, hf] at h; obtain ⟨rfl, rfl⟩ := h; simp at hr
                    | some u =>
                      by_cases hu : u = exp.uid
                      · subst hu; simp [hl, hmt, hc, hf] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
                      · simp [hl, hmt, hc, hf, hu] at h; obtain ⟨rfl, rfl⟩ := h; simp at hr
                · simp [hl, hmt, hc, c0, hpw] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact Or.inr (Or.inl ⟨hmt, hl, ⟨c, rfl, c0⟩, rfl⟩)
            · simp [hl, hmt] at h; obtain ⟨rfl, rfl⟩ := h; simp at hr
          · simp [hl, hpw] at h; obtain ⟨rfl, rfl⟩ := h
            exact Or.inl ⟨rfl, hl, rfl⟩
        · cases b
          · by_cases hmt : exp.hasMethodTable = true
            · cases hc : sigContributorsWorld O t.t image with
              | error e => simp [hl, hmt, hc] at h
              | ok c =>
                by_cases c0 : c = 0
                · subst c0
                  cases hf : O.findsup t.t world with
                  | error e => simp [hl, hmt, hc, hf] at h
                  | ok fr =>
                    obtain ⟨mt, lo, hi⟩ := fr
                    right; right
                    refine ⟨hmt, lo, hi, ?_⟩
                    cases mt with
                    | none => simp [hl, hmt, hc, hf] at h; obtain ⟨rfl, rfl⟩ := h; simp at hr
                    | some u =>
                      by_cases hu : u = exp.uid
                      · subst hu; simp [hl, hmt, hc, hf] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
                      · simp [hl, hmt, hc, hf, hu] at h; obtain ⟨rfl, rfl⟩ := h; simp at hr
                · simp [hl, hmt, hc, c0, hpw] at h
            · simp [hl, hmt] at h; obtain ⟨rfl, rfl⟩ := h; simp at hr
          · simp [hl, hpw] at h
      · have hl' : methodIsLatestWhich exp = false := by simpa using hl
        by_cases hmt : exp.hasMethodTable = true
        · cases hf : O.findsup t.t world with
          | error e => cases b <;> simp [hl', hmt, hf] at h
          | ok fr =>
            obtain ⟨mt, lo, hi⟩ := fr
            right; right
            refine ⟨hmt, lo, hi, ?_⟩
            cases mt with
            | none => cases b <;> simp [hl', hmt, hf] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp at hr
            | some u =>
              by_cases hu : u = exp.uid
              · subst hu; cases b <;> simp [hl', hmt, hf] at h <;> obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩
              · cases b <;> simp [hl', hmt, hf, hu] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp at hr
        · cases b <;> simp [hl', hmt] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp at hr
  | _ => all_goals (rinf_vmsimp at h; rinf_vmsimp2 at h; simp at h)

/-- `verify_call_lookup(sig, lim, world, workspace, memoize)` returns either a memoized answer for the same signature object and `lim`, whose validity range contains `world` (or, for a `nothing` result, made in `world` itself), without changing the workspace; or the answer of `_methods_by_ftype(sig, lim, world)`, which it stores under the signature when memoizing. -/
def VerifyCallLookupMemo : Prop :=
  ∀ (O : Oracle) (sig : Sig) (lim : Int) (world : Nat) (memo : Bool) (s s' : RS Workspace) (res : Option (List Nat) × Nat × Nat × Int),
    (verifyCallLookup O sig lim world memo).run s = .ok (res, s') →
    (memo = true ∧ ∃ c, s.ws.lookups.lookup sig.oid = some c ∧ c.lim = lim ∧
        (match c.result with | none => c.world = world | some _ => c.minWorld ≤ world ∧ world ≤ c.maxWorld) ∧
        res = (c.result, c.minWorld, c.maxWorld, c.hasAmbig) ∧ s'.heap = s.heap ∧ s'.ws = s.ws) ∨
    (O.matchingMethods sig.t lim world = .ok res ∧ s'.heap = s.heap ∧
      (memo = true → s'.ws.lookups.lookup sig.oid =
        some ⟨lim, world, res.1, res.2.1, res.2.2.1, res.2.2.2⟩))

theorem lookup_spec : VerifyCallLookupMemo := by
  intro O sig lim world memo s s' res
  intro h
  unfold verifyCallLookup at h
  rinf_vmsimp at h
  cases memo
  · simp only [Bool.false_eq_true, if_false] at h
    rinf_opath
  · simp only [if_true, get_proj_bind] at h
    cases hl : List.lookup sig.oid s.ws.lookups with
    | none => simp only [hl] at h; rinf_opath
    | some c =>
      simp only [hl] at h
      by_cases hlim : c.lim = lim
      · simp only [hlim, beq_self_eq_true, if_true] at h
        cases hr : c.result with
        | none =>
          simp only [hr] at h
          by_cases hw : c.world = world
          · simp [hw] at h; obtain ⟨rfl, rfl⟩ := h
            exact Or.inl ⟨rfl, c, rfl, hlim, by simp [hr, hw], by simp [hr], rfl, rfl⟩
          · simp [hw] at h
            rinf_opath
        | some l =>
          simp only [hr] at h
          by_cases hw : c.minWorld ≤ world ∧ world ≤ c.maxWorld
          · simp [hw] at h; obtain ⟨rfl, rfl⟩ := h
            exact Or.inl ⟨rfl, c, rfl, hlim, by simp [hr, hw], by simp [hr], rfl, rfl⟩
          · simp [hw] at h
            rinf_opath
      · have : (c.lim == lim) = false := by simpa using hlim
        simp only [this, Bool.false_eq_true, if_false] at h
        rinf_opath

def isMethodLike : Edge → Bool
  | .method _ | .mi _ | .ci _ => true
  | _ => false

/-- `get_method_from_edge` and `get_mi_from_edge` return the method and method instance behind a `Method`, `MethodInstance` or `CodeInstance` edge (`nothing` for a bare `Method`), change no state, and throw a `TypeError` for any other edge item. -/
def EdgeAccessors : Prop :=
  ∀ (s : RS Workspace),
    (∀ u, (getMethodFromEdge (.method u)).run s = .ok (u, s) ∧ (getMiFromEdge (.method u)).run s = .ok (none, s)) ∧
    (∀ m mi, s.heap.miR m = .ok mi →
      (getMethodFromEdge (.mi m)).run s = .ok (mi.def_, s) ∧ (getMiFromEdge (.mi m)).run s = .ok (some m, s)) ∧
    (∀ c cr mi, s.heap.ciR c = .ok cr → s.heap.miR cr.mi = .ok mi →
      (getMethodFromEdge (.ci c)).run s = .ok (mi.def_, s) ∧ (getMiFromEdge (.ci c)).run s = .ok (some cr.mi, s)) ∧
    (∀ e, isMethodLike e = false →
      (getMethodFromEdge e).run s = .error "julia:TypeError: typeassert MethodInstance" ∧
      (getMiFromEdge e).run s = .error "julia:TypeError: typeassert MethodInstance")

theorem edge_spec : EdgeAccessors := by
  intro s
  refine ⟨fun u => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro m mi hm
    unfold getMethodFromEdge getMiFromEdge
    simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Functor.map, StateT.map, StateT.lift, hm, Except.bind, Except.pure]
    exact ⟨trivial, trivial⟩
  · intro c cr mi hc hm
    unfold getMethodFromEdge getMiFromEdge
    simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Functor.map, StateT.map, StateT.lift, hc, hm, Except.bind, Except.pure]
    exact ⟨trivial, trivial⟩
  · intro e he
    cases e <;> simp [isMethodLike] at he <;> exact ⟨rfl, rfl⟩

/-- `method_in_image_deps(m, image)` is false for code of no image and for a method of no image, and otherwise asks `jl_linkage_blob_dep_world(image, blob) != 0`; `sig_contributors_world(sig, mt, image)` is 0 for code of no image, and otherwise the C answer. -/
def ImageQueries : Prop :=
  ∀ (O : Oracle) (m : MethodR) (image : Nat) (sig : Val),
    methodInImageDeps O m typemaxUInt = .ok false ∧
    (m.blob = typemaxUInt → methodInImageDeps O m image = .ok false) ∧
    (image ≠ typemaxUInt → m.blob ≠ typemaxUInt →
      methodInImageDeps O m image = (O.linkageBlobDepWorld image m.blob).map (· != 0)) ∧
    sigContributorsWorld O sig typemaxUInt = .ok 0 ∧
    (image ≠ typemaxUInt → sigContributorsWorld O sig image = O.sigContributorsWorld sig image)

theorem image_spec : ImageQueries := by
  intro O m image sig
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩
  · intro hb
    unfold methodInImageDeps
    by_cases hi : image = typemaxUInt
    · simp [hi]
    · simp [hi, hb]
  · intro hi hb
    unfold methodInImageDeps
    simp only [hi, hb, beq_iff_eq, if_false]
    cases O.linkageBlobDepWorld image m.blob <;> rfl
  · intro hi
    unfold sigContributorsWorld
    simp [hi, debugLog]

/-- `expected_dominates_sig(meth, mi)` holds exactly when `mi` carries `METHOD_SIG_LATEST_ONLY` or `meth`'s interference set is empty; `method_in_expecteds` is list membership; `method_is_latest_which` tests bit `0x1` of `dispatch_status`. -/
def DispatchBits : Prop :=
  ∀ (meth : MethodR) (mi : Option MIR) (m : Nat) (l : List Nat),
    (expectedDominatesSig meth mi = true ↔
      ((∃ r, mi = some r ∧ hasBit r.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = true) ∨
        meth.interferencesLen = 0)) ∧
    (methodInExpecteds m l = true ↔ m ∈ l) ∧
    (methodIsLatestWhich meth = true ↔ meth.dispatchStatus % 2 = 1)

theorem bits_spec : DispatchBits := by
  intro meth mi m l
  refine ⟨?_, by simp [methodInExpecteds], ?_⟩
  · cases mi with
    | none => simp [expectedDominatesSig]
    | some r =>
      simp only [expectedDominatesSig]
      by_cases hb : hasBit r.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = true
      · simp [hb]
      · simp [hb]
  · simp only [methodIsLatestWhich, hasBit, JuliaLean.Compiler.Reinfer.methodSigLatestWhich,
      JuliaLean.C.methodSigLatestWhich, bne_iff_ne, ne_eq]
    rw [Nat.and_one_is_mod]
    omega

/-- `binding_access_range_at(b, world)` is the C `binding_access_range` answer when `world >= require_world` and throws the `ErrorException` of `WorldWithRange` otherwise; `binding_changed_since_require_world(b, world)` changes nothing, returns false only through the fast path (the latest partition starts by the require world and is a leaf) or when the access range reaches back to the require world, and returns true only when it does not. -/
def BindingQueries : Prop :=
  ∀ (O : Oracle) (b world : Nat) (s s' : RS Workspace) (r : Bool),
    (s.heap.requireWorld ≤ world →
      (bindingAccessRangeAt (W := Workspace) O b world).run s = (O.bindingAccessRange b world).map (·, s)) ∧
    (world < s.heap.requireWorld → (bindingAccessRangeAt (W := Workspace) O b world).run s =
      .error "julia:ErrorException: invalid age range update") ∧
    ((bindingChangedSinceRequireWorld (W := Workspace) O b world).run s = .ok (r, s') →
      s' = s ∧ (r = false →
        (∃ br p rest, s.heap.bindingR b = .ok br ∧ br.partitions = p :: rest ∧
          p.minWorld ≤ s.heap.requireWorld ∧ isLeafPartition p = true) ∨
        (∃ wr, O.bindingAccessRange b world = .ok wr ∧ wr.minWorld ≤ s.heap.requireWorld)) ∧
      (r = true → ∃ wr, O.bindingAccessRange b world = .ok wr ∧ s.heap.requireWorld < wr.minWorld))

theorem binding_spec : BindingQueries := by
  intro O b world s s' r
  refine ⟨?_, ?_, ?_⟩
  · intro hw
    unfold bindingAccessRangeAt
    simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hw, decide_true, Bool.not_true,
      Bool.false_eq_true, if_false]
    cases O.bindingAccessRange b world <;> rfl
  · intro hw
    unfold bindingAccessRangeAt
    have : ¬ s.heap.requireWorld ≤ world := by omega
    simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, StateT.lift, Except.bind, Except.pure, this, decide_false, Bool.not_false,
      if_true, jlThrow]
    rfl
  · intro h
    unfold bindingChangedSinceRequireWorld bindingAccessRangeAt at h
    rinf_vmsimp at h
    simp only [Except.pure, ok_bind'] at h
    cases hb : s.heap.bindingR b with
    | error e => simp [hb] at h
    | ok br =>
      simp only [hb, ok_bind'] at h
      cases hp : br.partitions with
      | nil => simp only [hp] at h; rinf_accpath
      | cons p rest =>
        simp only [hp] at h
        by_cases hf : (decide (p.minWorld ≤ s.heap.requireWorld) && isLeafPartition p) = true
        · simp only [hf, if_true, stpure_app] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
          exact ⟨rfl, fun _ => Or.inl ⟨br, p, rest, rfl, hp, hf.1, hf.2⟩, fun h1 => by cases h1⟩
        · simp only [hf, Bool.false_eq_true, if_false] at h
          rinf_accpath


/-- Without code coverage or allocation logging, or for a code instance of a foreign owner, `needs_instrumentation` returns false and changes nothing. -/
def NeedsInstrumentationOff : Prop :=
  ∀ (ci : Nat) (s : RS Workspace) (c : CIR) (hc : s.heap.ciR ci = .ok c) (hi : s.heap.instrumenting = false ∨ c.ownerNothing = false),
    (needsInstrumentation ci).run s = .ok (false, s)

theorem instr_spec : NeedsInstrumentationOff := by
  intro ci s c hc hi
  unfold needsInstrumentation
  simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hc]
  rcases hi with hi | hi
  · cases c.ownerNothing <;> simp [hi]
  · simp [hi]

/-- `jl_promote_ci_to_current(ci, validated_world)` changes nothing when the world counter is no longer `validated_world`. -/
def PromoteCiNoop : Prop :=
  ∀ (fuel ci vw : Nat) (s : RS Workspace) (h : s.heap.worldCounter ≠ vw),
    (jlPromoteCiToCurrent fuel ci vw).run s = .ok ((), s)

theorem promoteCi_noop : PromoteCiNoop := by
  intro fuel ci vw s h
  unfold jlPromoteCiToCurrent
  by_cases hg : s.heap.worldCounter > vw
  · simp only [getHeap, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hg, decide_true, if_true]
  · simp only [getHeap, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hg, decide_false, if_false, h, bne_iff_ne, ne_eq,
      not_false_eq_true, decide_true, if_true, Bool.false_eq_true]



/-! ## Exact answers of the interference-set predicates

Each statement below gives the whole answer of a predicate, for both outcomes, in the terms its
comment uses, so a predicate that always answers `false` (or always `true`) does not satisfy it.
They take as hypotheses that the lookups they make answer (`<:` is total, the interference sets
name methods of the heap). -/

/-- Every entry of `m`'s interference set names a method of the heap. -/
def SetResolves (H : Heap) (m : MethodR) : Prop :=
  ∀ k ∈ m.interferences, ∃ x, H.method k = .ok x ∧ x.primaryWorld ≤ typemaxUInt

/-- `method_morespecific_recorded(m1, m2)` (`Compiler/src/reinfer.jl:538-543`) holds exactly when
`m1` and `m2` differ, `m1` is in `m2`'s interference set (`m2` is not more specific than `m1`) and
`m2` is not in `m1`'s (`m1` is more specific than `m2`). -/
def MorespecificRecordedExact : Prop :=
  ∀ (H : Heap) (a b : MethodR), SetResolves H a → SetResolves H b →
    methodMorespecificRecorded H a b =
      .ok (decide (a.uid ≠ b.uid ∧ a.uid ∈ b.interferences ∧ b.uid ∉ a.interferences))

theorem msr_exact : MorespecificRecordedExact := by
  intro H a b ha hb
  unfold methodMorespecificRecorded
  rw [mii_spec H a b hb, mii_spec H b a ha]
  by_cases hab : a.uid = b.uid
  · simp [hab]
  · by_cases h1 : a.uid ∈ b.interferences <;> by_cases h2 : b.uid ∈ a.interferences <;>
      simp [hab, h1, h2]

/-- The interference-set statements together: the iteration, membership, the exact answer of
`method_morespecific_recorded`, and (a consequence) its asymmetry. -/
def InterferenceSetsExact : Prop := InterferenceSets ∧ MorespecificRecordedExact

theorem interferenceSetsExact_proven : InterferenceSetsExact :=
  ⟨interferenceSets_proven, msr_exact⟩

/-- `expected_is_minmax(meth, m, sig, expected)` answers, and answers true exactly when `sig <:
meth.sig`, not `sig <: m.sig`, and `meth` recorded-beats every other expected method that fully
covers `sig` (`Compiler/src/reinfer.jl:612-637`). -/
def ExpectedIsMinmaxExact : Prop :=
  ∀ (O : Oracle) (H : Heap) (meth im : MethodR) (sig : Val) (expected : List MethodR)
    (sub : Val → Val → Bool) (mr : MethodR → MethodR → Bool),
    (∀ a b, O.sub a b = .ok (sub a b)) → (∀ a b, methodMorespecificRecorded H a b = .ok (mr a b)) →
    ∃ r, expectedIsMinmax O H meth im sig expected = .ok r ∧
      (r = true ↔ (sub sig meth.sig = true ∧ sub sig im.sig = false ∧
        ∀ m2 ∈ expected, m2.uid ≠ meth.uid → sub sig m2.sig = true → mr meth m2 = true))

theorem minmax_exact : ExpectedIsMinmaxExact := by
  intro O H meth im sig expected sub mr hsub hmr
  unfold expectedIsMinmax
  simp only [hsub, ok_bind]
  cases h1 : sub sig meth.sig
  · simp
  · cases h2 : sub sig im.sig
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
      rw [forIn_bool _ (fun m2 => m2.uid != meth.uid && sub sig m2.sig && !mr meth m2) false ?_ expected]
      · by_cases ha : (expected.any fun m2 => m2.uid != meth.uid && sub sig m2.sig && !mr meth m2) = true
        · simp only [ha, if_true]
          refine ⟨false, rfl, ?_⟩
          simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at ha
          obtain ⟨x, hx, ⟨hne, hs⟩, hm⟩ := ha
          simp only [Bool.false_eq_true, false_iff, true_and]
          intro hall
          have := hall x hx hne hs
          simp [this] at hm
        · simp only [ha, Bool.false_eq_true, if_false]
          refine ⟨true, rfl, ?_⟩
          simp only [true_iff, true_and]
          intro m2 hm2 hne hs
          cases hmv : mr meth m2
          · exfalso
            apply ha
            simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
            exact ⟨m2, hm2, ⟨hne, hs⟩, hmv⟩
          · rfl
      · intro x
        by_cases hu : x.uid = meth.uid
        · simp [hu]
        · cases hs : sub sig x.sig <;> cases hm : mr meth x <;> simp [hu, hs, hm, hmr]
    · simp

/-- `has_empty_set_cover(m, ti, expected)` answers, and answers true exactly when some expected
method has an empty interference set, recorded-beats `m` and covers `ti`
(`Compiler/src/reinfer.jl:651-663`). -/
def HasEmptySetCoverExact : Prop :=
  ∀ (O : Oracle) (H : Heap) (im : MethodR) (ti : Val) (expected : List MethodR)
    (sub : Val → Val → Bool) (mr : MethodR → MethodR → Bool),
    (∀ a b, O.sub a b = .ok (sub a b)) → (∀ a b, methodMorespecificRecorded H a b = .ok (mr a b)) →
    ∃ r, hasEmptySetCover O H im ti expected = .ok r ∧
      (r = true ↔ ∃ m2 ∈ expected, m2.interferencesLen = 0 ∧ mr m2 im = true ∧ sub ti m2.sig = true)

theorem cover_exact : HasEmptySetCoverExact := by
  intro O H im ti expected sub mr hsub hmr
  unfold hasEmptySetCover
  simp only [bind, Except.bind]
  rw [forIn_bool _ (fun m2 => m2.interferencesLen == 0 && mr m2 im && sub ti m2.sig) true ?_ expected]
  · by_cases ha : (expected.any fun m2 => m2.interferencesLen == 0 && mr m2 im && sub ti m2.sig) = true
    · simp only [ha, if_true]
      refine ⟨true, rfl, ?_⟩
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨x, hx, ⟨hl, hm⟩, hs⟩ := ha
      exact ⟨fun _ => ⟨x, hx, hl, hm, hs⟩, fun _ => rfl⟩
    · simp only [ha, Bool.false_eq_true, if_false]
      refine ⟨false, rfl, ?_⟩
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro m2 hm2 hl hm hs
      apply ha
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨m2, hm2, ⟨hl, hm⟩, hs⟩
  · intro x
    by_cases hl : x.interferencesLen = 0
    · cases hm : mr x im <;> cases hs : sub ti x.sig <;> simp [hl, hm, hs, hsub, hmr]
    · simp [hl]

/-- `morespecific_cannot_cycle(m, world)` answers, and answers true exactly when every method of
`m`'s interference set visible in `world` has an empty interference set or has `m` in its own
set (`Compiler/src/reinfer.jl:678-700`). -/
def MorespecificCannotCycleExact : Prop :=
  ∀ (H : Heap) (im : MethodR) (world : Nat) (ms : List MethodR) (mii : MethodR → MethodR → Bool),
    eachinterference H im world = .ok ms → (∀ a b, methodInInterferences H a b = .ok (mii a b)) →
    ∃ r, morespecificCannotCycle H im world = .ok r ∧
      (r = true ↔ ∀ msp ∈ ms, msp.interferencesLen = 0 ∨ mii im msp = true)

theorem cannotCycle_exact : MorespecificCannotCycleExact := by
  intro H im world ms mii hei hmii
  unfold morespecificCannotCycle
  rw [hei]
  simp only [bind, Except.bind]
  rw [forIn_bool _ (fun msp => msp.interferencesLen != 0 && !mii im msp) false ?_ ms]
  · by_cases ha : (ms.any fun msp => msp.interferencesLen != 0 && !mii im msp) = true
    · simp only [ha, if_true]
      refine ⟨false, rfl, ?_⟩
      simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at ha
      obtain ⟨x, hx, hl, hm⟩ := ha
      simp only [Bool.false_eq_true, false_iff]
      intro hall
      rcases hall x hx with h | h
      · exact hl h
      · simp [h] at hm
    · simp only [ha, Bool.false_eq_true, if_false]
      refine ⟨true, rfl, ?_⟩
      simp only [true_iff]
      intro msp hm
      simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_exists,
        not_and] at ha
      by_cases hl : msp.interferencesLen = 0
      · exact Or.inl hl
      · right
        cases hv : mii im msp
        · exact absurd hv (ha msp hm hl)
        · rfl
  · intro x
    by_cases hl : x.interferencesLen = 0
    · simp [hl]
    · cases hm : mii im x <;> simp [hl, hm, hmii]

/-- `newmethod_removed_silently(meth, m, ti, sig, expected, world)` is exactly the conjunction of
its three conditions: `expected_is_minmax` when `meth` is in `m`'s set (the mutually ambiguous
case), `has_empty_set_cover` and `morespecific_cannot_cycle` (`Compiler/src/reinfer.jl:578-610`).
With the exact answers above, this pins the whole decision. -/
def NewmethodRemovedSilentlyExact : Prop :=
  ∀ (O : Oracle) (H : Heap) (meth im : MethodR) (ti sig : Val) (expected : List MethodR) (world : Nat)
    (a c d e : Bool),
    methodInInterferences H meth im = .ok a → expectedIsMinmax O H meth im sig expected = .ok c →
    hasEmptySetCover O H im ti expected = .ok d → morespecificCannotCycle H im world = .ok e →
    newmethodRemovedSilently O H meth im ti sig expected world = .ok ((!a || c) && d && e)

theorem silent_exact : NewmethodRemovedSilentlyExact := by
  intro O H meth im ti sig expected world a c d e h1 h2 h3 h4
  unfold newmethodRemovedSilently
  rw [h1]
  cases a <;> cases c <;> cases d <;> simp [h2, h3, h4]

/-- Both directions of each predicate. -/
def ExpectedIsMinmaxBoth : Prop := ExpectedIsMinmaxSound ∧ ExpectedIsMinmaxExact
def HasEmptySetCoverBoth : Prop := HasEmptySetCoverSound ∧ HasEmptySetCoverExact
def MorespecificCannotCycleBoth : Prop := MorespecificCannotCycleSound ∧ MorespecificCannotCycleExact
def NewmethodRemovedSilentlyBoth : Prop := NewmethodRemovedSilentlySound ∧ NewmethodRemovedSilentlyExact

theorem minmax_both : ExpectedIsMinmaxBoth := ⟨minmax_true, minmax_exact⟩
theorem cover_both : HasEmptySetCoverBoth := ⟨cover_true, cover_exact⟩
theorem cannotCycle_both : MorespecificCannotCycleBoth := ⟨cannotCycle_true, cannotCycle_exact⟩
theorem silent_both : NewmethodRemovedSilentlyBoth := ⟨silent_true, silent_exact⟩

/-! ## `promote_mi_to_current`, both outcomes -/

/-- `promote_mi_to_current(mi, minworld, world)` (`Compiler/src/reinfer.jl:566-571` with
`jl_promote_mi_to_current`, `src/gf.c:2283-2302`) does nothing for `nothing`, and for a method
instance sets its `dispatch_status` to exactly `METHOD_SIG_LATEST_ONLY` if and only if the world
counter is still `world`, its method's interference set is nonempty, `minworld` is that method's
`primary_world` and the instance lacks the bit; otherwise it leaves the heap as it was. -/
def PromoteMiExact : Prop :=
  (∀ (mw w : Nat) (s : RS Workspace), (promoteMiToCurrent none mw w).run s = .ok ((), s)) ∧
  ∀ (m mw w : Nat) (s : RS Workspace) (miR : MIR) (d : MethodR),
    s.heap.miR m = .ok miR → s.heap.method miR.def_ = .ok d →
    ∃ s', (promoteMiToCurrent (some m) mw w).run s = .ok ((), s') ∧ s'.ws = s.ws ∧
      s'.heap = (if s.heap.worldCounter = w ∧ d.interferencesLen ≠ 0 ∧ mw = d.primaryWorld ∧
          hasBit miR.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = false
        then s.heap.setMI { miR with dispatchStatus := JuliaLean.Compiler.Reinfer.methodSigLatestOnly }
        else s.heap)

macro "rinf_unf" : tactic => `(tactic| simp only [promoteMiToCurrent, getHeap, liftE, modifyHeap, emit,
  bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, StateT.run,
  StateT.lift, Except.bind, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet])

theorem promote_exact : PromoteMiExact := by
  refine ⟨fun mw w s => rfl, ?_⟩
  intro m mw w s miR d hm hd
  by_cases hc : s.heap.worldCounter = w ∧ d.interferencesLen ≠ 0 ∧ mw = d.primaryWorld ∧
      hasBit miR.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = false
  · rw [if_pos hc]
    obtain ⟨h0, h1, h2, h3⟩ := hc
    refine ⟨⟨s.heap.setMI { miR with dispatchStatus := JuliaLean.Compiler.Reinfer.methodSigLatestOnly },
      s.events.push (.path "promote-mi"), s.ws⟩, ?_, rfl, rfl⟩
    have hg : ¬ s.heap.worldCounter > w := by omega
    rinf_unf; simp [ modifyHeap, emit, hm, hd, h0, h1, h2, h3, StateT.run]
    rfl
  · rw [if_neg hc]
    refine ⟨s, ?_, rfl, rfl⟩
    by_cases hg : s.heap.worldCounter > w
    · rinf_unf; simp [hg]
    · have hg' : s.heap.worldCounter ≤ w := by omega
      by_cases hw : s.heap.worldCounter = w
      · have hc' : ¬ (d.interferencesLen ≠ 0 ∧ mw = d.primaryWorld ∧
            hasBit miR.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = false) :=
          fun h => hc ⟨hw, h⟩
        by_cases h1 : d.interferencesLen = 0
        · rinf_unf; simp [hg, hm, hd, h1]
        · by_cases h2 : mw = d.primaryWorld
          · have h3 : hasBit miR.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly = true := by
              cases hb : hasBit miR.dispatchStatus JuliaLean.Compiler.Reinfer.methodSigLatestOnly
              · exact absurd ⟨h1, h2, hb⟩ hc'
              · rfl
            rinf_unf; simp [hg, hm, hd, h1, h2, h3]
          · rinf_unf; simp [hg, hm, hd, h1, h2]
      · rinf_unf; simp [hg, hm, hd, hw]

def PromoteMiBoth : Prop := PromoteMiEffect ∧ PromoteMiExact
theorem promote_both : PromoteMiBoth := ⟨promote_spec, promote_exact⟩

/-! ## `verify_invokesig`, both outcomes -/

/-- When its lookups answer and `expected` is present in the verification world (a runtime
promise, `Compiler/src/reinfer.jl:964, 974`), `verify_invokesig` returns without changing the heap
or the workspace, and accepts (`max_world != 0`) exactly when the signature is `expected.sig` and
`expected` is still the latest `which`, or `expected` is still the latest `which` and every
contributor to the signature was present in the image, or `_findsup(invokesig, mt, world)`
returns `expected` itself with a nonempty range. In particular an invoke edge whose target is
unchanged is accepted (precision). -/
def VerifyInvokesigExact : Prop :=
  ∀ (O : Oracle) (t : Sig) (exp : MethodR) (world image : Nat) (s : RS Workspace) (e : Bool)
    (c : Nat) (mt : Option Nat) (lo hi : Nat),
    O.egal t.t exp.sig = .ok e → sigContributorsWorld O t.t image = .ok c →
    O.findsup t.t world = .ok (mt, lo, hi) → exp.primaryWorld ≤ world →
    ∃ r s', (verifyInvokesig O (.ty t) exp world image).run s = .ok (r, s') ∧
      s'.heap = s.heap ∧ s'.ws = s.ws ∧
      (r.2 ≠ 0 ↔ ((e = true ∧ methodIsLatestWhich exp = true) ∨
        (exp.hasMethodTable = true ∧ methodIsLatestWhich exp = true ∧ c ≠ 0) ∨
        (exp.hasMethodTable = true ∧ mt = some exp.uid ∧ hi ≠ 0)))

theorem invoke_exact : VerifyInvokesigExact := by
  intro O t exp world image s e c mt lo hi he hc hf hpw
  unfold verifyInvokesig
  have ht : typemaxUInt ≠ 0 := by decide
  simp only [getHeap, liftE, modifyHeap, emit, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, StateT.run, StateT.lift, Except.bind, assert',
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, he, hc, hf, hpw, decide_true,
    if_true]
  cases e <;> cases hl : methodIsLatestWhich exp <;> cases hmt : exp.hasMethodTable <;>
    by_cases c0 : c = 0
  all_goals (cases mt with
    | none => simp [hl, hmt, c0, ht, and_assoc]
    | some u => by_cases hu : u = exp.uid <;> simp [hl, hmt, c0, ht, hu, and_assoc])

def VerifyInvokesigBoth : Prop := VerifyInvokesigSound ∧ VerifyInvokesigExact
theorem invoke_both : VerifyInvokesigBoth := ⟨invoke_spec, invoke_exact⟩

/-! ## The binding fast path agrees with the walk -/

/-- `binding_changed_since_require_world` without its fast path: only the walk's answer. -/
def bindingChangedSlow (O : Oracle) (b world : Nat) : RM Workspace Bool := do
  let H ← getHeap
  return (← bindingAccessRangeAt O b world).minWorld > H.requireWorld

/-- What `binding_access_range` (`Compiler/src/abstractinterpretation.jl:4241-4284`) promises
for a binding whose newest partition is a leaf containing the query world: the partition found
is that one, `walk_binding_partition` returns its own range for a leaf (`:4127-4140`), and the
backward scan only lowers the start (`union` with earlier ranges, or an earlier range), so the
access range starts no later than the partition. -/
def LeafRangePromise (O : Oracle) (H : Heap) : Prop :=
  ∀ b br p rest world, H.bindingR b = .ok br → br.partitions = p :: rest → isLeafPartition p = true →
    p.minWorld ≤ world → world ≤ p.maxWorld → H.requireWorld ≤ world →
    ∃ wr, O.bindingAccessRange b world = .ok wr ∧ wr.minWorld ≤ p.minWorld

/-- The comment's promise (`Compiler/src/reinfer.jl:104-109`): for a world at or after the require
world in which the newest partition is current, the fast path gives the same answer as the walk
(`min_world(binding_access_range_at(b, world)) > require_world`), so it never hides a change. -/
def BindingFastPathAgrees : Prop :=
  ∀ (O : Oracle) (s : RS Workspace) (b world : Nat) (br : BindingR),
    LeafRangePromise O s.heap → s.heap.bindingR b = .ok br → s.heap.requireWorld ≤ world →
    (∀ p rest, br.partitions = p :: rest → world ≤ p.maxWorld) →
    (bindingChangedSinceRequireWorld O b world).run s = (bindingChangedSlow O b world).run s

theorem fastpath_agrees : BindingFastPathAgrees := by
  intro O s b world br hP hb hw hmax
  unfold bindingChangedSinceRequireWorld bindingChangedSlow
  simp only [getHeap, liftE, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, StateT.run, StateT.lift, Except.bind, Except.pure, hb]
  cases hp : br.partitions with
  | nil => rfl
  | cons p rest =>
    simp only
    by_cases hf : (decide (p.minWorld ≤ s.heap.requireWorld) && isLeafPartition p) = true
    · simp only [hf, if_true]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨wr, hwr, hle⟩ := hP b br p rest world hb hp hf.2 (by omega) (hmax p rest hp) hw
      unfold bindingAccessRangeAt
      simp only [getHeap, liftE, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, StateT.lift, Except.bind, Except.pure, hw, decide_true, Bool.not_true,
        Bool.false_eq_true, if_false, hwr]
      have : ¬ wr.minWorld > s.heap.requireWorld := by omega
      simp [this]
    · simp only [hf, Bool.false_eq_true, if_false, StateT.bind]
      rfl

def BindingQueriesBoth : Prop := BindingQueries ∧ BindingFastPathAgrees
theorem binding_both : BindingQueriesBoth := ⟨binding_spec, fastpath_agrees⟩

/-! ## Workspace states -/

/-- `VerifyMethodInitialState(codeinst)` reads `codeinst`'s method instance, its method, its edge
list and its image without changing anything; `VerifyMethodWorkState(cause)` starts at depth 0,
recursive index 1, stage `:init_and_process_callees`; `VerifyMethodResultState()` is `(0, 0, 0)`. -/
def StateCtors : Prop :=
  (∀ (s : RS Workspace) (ci : Nat) (c : CIR) (mi : MIR), s.heap.ciR ci = .ok c → s.heap.miR c.mi = .ok mi →
    (mkInitialState ci).run s =
      .ok ({ codeinst := ci, mi := c.mi, def_ := mi.def_, callees := c.callees, image := c.blob }, s)) ∧
  (∀ cause, mkWorkState cause = ⟨0, cause, 1, .initAndProcessCallees⟩) ∧
  mkResultState = ⟨0, 0, 0⟩

theorem stateCtors_proven : StateCtors := by
  refine ⟨?_, fun _ => rfl, rfl⟩
  intro s ci c mi hc hm
  unfold mkInitialState
  simp only [getHeap, liftE, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, StateT.lift, Except.bind, Except.pure, hc, hm]

/-! ## Open properties -/

/-- `a`'s edge list holds the code instance `b`, and both still await verification. A cycle
through a code instance that is already validated is not one the verifier walks: it stops there
and takes that instance's range. -/
def CIEdge (H : Heap) (a b : Nat) : Prop :=
  ∃ c d, H.ciR a = .ok c ∧ H.ciR b = .ok d ∧ Edge.ci b ∈ c.callees.toList ∧
    c.maxWorld = worldAgeRevalidationSentinel ∧ d.maxWorld = worldAgeRevalidationSentinel

/-- Reachability through code-instance edges. -/
inductive Reach (H : Heap) : Nat → Nat → Prop
  | edge {a b : Nat} : CIEdge H a b → Reach H a b
  | trans {a b c : Nat} : Reach H a b → Reach H b c → Reach H a c

/-- Cycle handling (property 3): two code instances on a common cycle of instances awaiting
verification are never left by a run of `verify_method` one valid in the validation world and
the other not. -/
def CycleGroupConsistent : Prop :=
  ∀ (O : Oracle) (H : Heap) (fuel ci : Nat) (r : Nat × Nat × Nat) (s' : RS Workspace),
    runVerify O H fuel ci H.worldCounter = .ok (r, s') →
    ∀ a b ca cb ca' cb', Reach H a b → Reach H b a →
      H.ciR a = .ok ca → H.ciR b = .ok cb →
      ca.maxWorld = worldAgeRevalidationSentinel → cb.maxWorld = worldAgeRevalidationSentinel →
      s'.heap.ciR a = .ok ca' → s'.heap.ciR b = .ok cb' →
      ca'.maxWorld ≠ worldAgeRevalidationSentinel → cb'.maxWorld ≠ worldAgeRevalidationSentinel →
      ((ca'.minWorld ≤ H.worldCounter ∧ H.worldCounter ≤ ca'.maxWorld) ↔
        (cb'.minWorld ≤ H.worldCounter ∧ H.worldCounter ≤ cb'.maxWorld))

/-- Property 4: the range `verify_method` returns for a code instance awaiting verification lies
within `[require_world, validation_world]` when it is not a rejection. -/
def VerifyRangeBounded : Prop :=
  ∀ (O : Oracle) (H : Heap) (fuel ci vw : Nat) (c : CIR) (cyc mn mx : Nat) (s' : RS Workspace),
    H.ciR ci = .ok c → c.maxWorld = worldAgeRevalidationSentinel → H.requireWorld ≤ vw →
    runVerify O H fuel ci vw = .ok ((cyc, mn, mx), s') →
    mx ≤ vw ∧ (mx ≠ 0 → H.requireWorld ≤ mn)

/-! ## Entries -/

def entries : List Entry := [
  { id := "compiler-reinfer-stale-min-world", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["verify_method(codeinst::CodeInstance, validation_world::UInt, workspace::VerifyMethodWorkspace)", "verify_method_graph(codeinst::CodeInstance, validation_world::UInt, workspace::VerifyMethodWorkspace)", "verify_call(@nospecialize(sig), expecteds::Core.SimpleVector, i::Int, n::Int, world::UInt, fully_covers::Bool, possibly_ambiguous::Bool, workspace::VerifyMethodWorkspace, image::UInt)", "scan_new_code!(internal_methods::Vector{Any}, workspace::VerifyMethodWorkspace)", "insert_backedges(internal_methods::Vector{Any})"],
    statement := "After insert_backedges runs over the loaded code instances (scan_new_methods!, then scan_new_code! with verify_method_graph, verify_method and jl_promote_ci_to_current), every one of them that is valid in the current world has call edges whose lookup in that world gives the methods recorded when the image was built (soundness: no stale code is kept).",
    source := "invariant: insert_backedges must not keep code whose edges changed (Compiler/src/reinfer.jl:117-147, 727-729)",
    status := .refuted, prop := ``InsertBackedgesSound, thm := some ``insertBackedgesSound_refuted,
    issue := "none found (queries listed in bugs/compiler-reinfer-stale-min-world.yaml)",
    notes := "verify_call looks up in codeinst.min_world, the activation world, and the interference fast path skips entries with primary_world past that world. A method defined by another thread between jl_restore_package_image's unlock of world_counter_lock (src/staticdata.c:4986) and insert_backedges (base/loading.jl:1516) is hidden, and the code instance is accepted and promoted. Reproduced with a real package on the pinned Julia and nightly 290d5bb5f5: RISPkg.g(1) returns 1 while RISDep.h(1) returns 2. The Lean counterexample runs the whole insert_backedges on the heap (decide +kernel), and its verify_method_graph assertions pass there; verifyMethodSound_refuted is the same counterexample one level down, at verify_method." },
  { id := "compiler-reinfer-state-ctors", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["VerifyMethodInitialState(codeinst::CodeInstance)", "VerifyMethodWorkState(dummy_cause::CodeInstance)", "VerifyMethodResultState()"],
    statement := "VerifyMethodInitialState(codeinst) reads codeinst's method instance, method, edges and image without changing anything; VerifyMethodWorkState(cause) is (0, cause, 1, :init_and_process_callees); VerifyMethodResultState() is (0, 0, 0).",
    source := "Compiler/src/reinfer.jl:80-94 (what the helpers build)",
    status := .proven, prop := ``StateCtors, thm := some ``stateCtors_proven },
  { id := "compiler-reinfer-binding-queries", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["binding_access_range_at(b::Core.Binding, world::UInt)", "binding_changed_since_require_world(b::Core.Binding, world::UInt)"],
    statement := "binding_access_range_at(b, world) is binding_access_range over [require_world, world] and throws when world < require_world; binding_changed_since_require_world changes nothing, returns false only through its fast path (latest partition from the require world on, and a leaf) or when the access range reaches back to the require world, and true only when it does not; and its fast path agrees with the walk: for a world at or after the require world in which the newest partition is current, it answers min_world(binding_access_range_at(b, world)) > require_world.",
    source := "comment Compiler/src/reinfer.jl:102-108 (whether an access can resolve differently now than in any process that serialized code against it)",
    status := .proven, prop := ``BindingQueriesBoth, thm := some ``binding_both,
    notes := "Second half (BindingFastPathAgrees): given the promise of binding_access_range for a newest leaf partition containing the world (its range starts no later than the partition, read from Compiler/src/abstractinterpretation.jl:4127-4140, 4241-4284), for a world at or after the require world in which the newest partition is current, the function answers exactly as the walk alone (min_world(binding_access_range_at(b, world)) > require_world). The difftest checks the promise and the agreement on every r.bindingChanged case (leafpromise:*, fastpath:* tallies)." },
  { id := "compiler-reinfer-needs-instrumentation-off", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["needs_instrumentation(codeinst::CodeInstance, mi::MethodInstance, def::Method, validation_world::UInt)"],
    statement := "Without code coverage or allocation logging, or for a code instance of a foreign owner, needs_instrumentation returns false and changes nothing.",
    source := "Compiler/src/reinfer.jl:180-215 (the two early returns)",
    status := .proven, prop := ``NeedsInstrumentationOff, thm := some ``instr_spec,
    notes := "The branch under coverage or malloc logging is not modelled (an unmodelled failure)." },
  { id := "compiler-reinfer-edge-accessors", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["get_method_from_edge(@nospecialize t)", "get_mi_from_edge(@nospecialize t)"],
    statement := "get_method_from_edge and get_mi_from_edge return the method and method instance behind a Method, MethodInstance or CodeInstance edge (nothing for a bare Method), change no state, and throw a TypeError for any other edge item.",
    source := "comments Compiler/src/reinfer.jl:468-486",
    status := .proven, prop := ``EdgeAccessors, thm := some ``edge_spec },
  { id := "compiler-reinfer-dispatch-bits", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["expected_dominates_sig(meth::Method, mi::Union{Nothing,MethodInstance})", "method_in_expecteds(m::Method, expected::Vector{Method})", "method_is_latest_which(m::Method)"],
    statement := "expected_dominates_sig(meth, mi) holds exactly when mi carries METHOD_SIG_LATEST_ONLY or meth's interference set is empty; method_in_expecteds is membership by identity; method_is_latest_which tests bit 0x1 of dispatch_status.",
    source := "comments Compiler/src/reinfer.jl:458-466, 488-497, 545-548",
    status := .proven, prop := ``DispatchBits, thm := some ``bits_spec },
  { id := "compiler-reinfer-interference-sets", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["eachinterference(m::Method, cutoff::UInt=typemax(UInt))", "Base.iterate(ei::EachInterference, k::Int=1)", "method_in_interferences(method2::Method, method1::Method)", "method_morespecific_recorded(method1::Method, method2::Method)"],
    statement := "eachinterference(m, cutoff) yields the assigned entries of m.interferences in definition order up to the first one whose primary_world is past cutoff; method_in_interferences(m2, m1) is membership of m2 in m1's set; method_morespecific_recorded(m1, m2) is exactly: m1 and m2 differ, m1 is in m2's set and m2 is not in m1's (so it is irreflexive and asymmetric).",
    source := "comments Compiler/src/reinfer.jl:509-543",
    status := .proven, prop := ``InterferenceSetsExact, thm := some ``interferenceSetsExact_proven },
  { id := "compiler-reinfer-image-queries", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["method_in_image_deps(m::Method, image::UInt)", "sig_contributors_world(@nospecialize(sig), mt::Core.MethodTable, image::UInt)"],
    statement := "method_in_image_deps(m, image) is false for code of no image and for a method of no image, and otherwise jl_linkage_blob_dep_world(image, blob) != 0; sig_contributors_world(sig, mt, image) is 0 for code of no image and otherwise the C answer.",
    source := "comments Compiler/src/reinfer.jl:550-564",
    status := .proven, prop := ``ImageQueries, thm := some ``image_spec },
  { id := "compiler-reinfer-promote-mi", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["promote_mi_to_current(mi::Union{Nothing,MethodInstance}, minworld::UInt, world::UInt)"],
    statement := "promote_mi_to_current does nothing for nothing; for a method instance it sets dispatch_status to exactly METHOD_SIG_LATEST_ONLY if and only if the world counter is still world, its method's interference set is nonempty, minworld is the method's primary_world and the instance lacks the bit, and otherwise leaves the heap as it was.",
    source := "jl_promote_mi_to_current (src/gf.c:2283-2302) and Compiler/src/reinfer.jl:566-571",
    status := .proven, prop := ``PromoteMiBoth, thm := some ``promote_both },
  { id := "compiler-reinfer-removed-silently", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["newmethod_removed_silently(meth::Method, interference_method::Method, @nospecialize(ti), @nospecialize(sig), expected::Vector{Method}, world::UInt)"],
    statement := "newmethod_removed_silently answers exactly (meth not in the new method's set, or expected_is_minmax) and has_empty_set_cover and morespecific_cannot_cycle: true only when all three conditions hold and true whenever they do.",
    source := "comment Compiler/src/reinfer.jl:578-610 (the three conditions)",
    status := .proven, prop := ``NewmethodRemovedSilentlyBoth, thm := some ``silent_both,
    notes := "Open, no entry: the comment's promise that acceptance implies the full ml_matches lookup returns exactly the expected methods. The oracle's _methods_by_ftype is uninterpreted, so stating it needs a model of the ml_matches sort over the interference graph; not attempted." },
  { id := "compiler-reinfer-expected-is-minmax", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["expected_is_minmax(meth::Method, interference_method::Method, @nospecialize(sig), expected::Vector{Method})"],
    statement := "expected_is_minmax(meth, m, sig, expected) returns true exactly when sig <: meth.sig, not sig <: m.sig, and meth recorded-beats every other expected method that fully covers sig (both directions, with <: and method_morespecific_recorded answering).",
    source := "comment Compiler/src/reinfer.jl:612-637",
    status := .proven, prop := ``ExpectedIsMinmaxBoth, thm := some ``minmax_both },
  { id := "compiler-reinfer-empty-set-cover", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["has_empty_set_cover(interference_method::Method, @nospecialize(ti), expected::Vector{Method})"],
    statement := "has_empty_set_cover(m, ti, expected) returns true exactly when some expected method has an empty interference set, recorded-beats m, and covers ti (both directions, with <: and method_morespecific_recorded answering).",
    source := "comment Compiler/src/reinfer.jl:651-663",
    status := .proven, prop := ``HasEmptySetCoverBoth, thm := some ``cover_both },
  { id := "compiler-reinfer-cannot-cycle", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["morespecific_cannot_cycle(interference_method::Method, world::UInt)"],
    statement := "morespecific_cannot_cycle(m, world) returns true exactly when every method of m's interference set visible in world has an empty interference set or has m in its own set (both directions).",
    source := "comment Compiler/src/reinfer.jl:678-687",
    status := .proven, prop := ``MorespecificCannotCycleBoth, thm := some ``cannotCycle_both },
  { id := "compiler-reinfer-lookup-memo", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["verify_call_lookup(@nospecialize(sig), lim::Int, world::UInt, workspace::VerifyMethodWorkspace, memoize::Bool)"],
    statement := "verify_call_lookup returns either a memoized answer for the same signature object and lim whose validity range contains world (a nothing answer: made in world itself) without changing the workspace, or the answer of _methods_by_ftype(sig, lim, world), stored under the signature when memoizing.",
    source := "comment Compiler/src/reinfer.jl:702-704",
    status := .proven, prop := ``VerifyCallLookupMemo, thm := some ``lookup_spec,
    notes := "Whether reusing an answer across its validity range is exact rests on the C promise that _methods_by_ftype gives the same matches in every world of the range it reports." },
  { id := "compiler-reinfer-invokesig-sound", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["verify_invokesig(@nospecialize(invokesig), expected::Method, world::UInt, matches::Vector{Any}, image::UInt)"],
    statement := "verify_invokesig accepts exactly when the signature is expected.sig and expected is still the latest which, or expected is still the latest which with a method table and every contributor to the signature was present in the image, or _findsup(invokesig, mt, world) returns expected itself with a nonempty range (that lookup's range); when it accepts, the signature is a type.",
    source := "comments Compiler/src/reinfer.jl:899, 909 (verify_invokesig, 894-928)",
    status := .proven, prop := ``VerifyInvokesigBoth, thm := some ``invoke_both,
    notes := "Second half (VerifyInvokesigExact): when its lookups answer and expected is present in the verification world, it changes no state and accepts exactly in those three cases, so an invoke edge whose _findsup answer is still expected (with a nonempty range) is accepted (precision). The first two cases return [primary_world, typemax]; they rest on the METHOD_SIG_LATEST_WHICH and jl_sig_contributors_world promises." },
  { id := "compiler-reinfer-promote-ci-noop", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["scan_new_code!(internal_methods::Vector{Any}, workspace::VerifyMethodWorkspace)"],
    statement := "jl_promote_ci_to_current(ci, validated_world), called by scan_new_code! after each graph, changes nothing when the world counter is no longer validated_world.",
    source := "comment Compiler/src/reinfer.jl:142-144 and src/gf.c:2247-2276",
    status := .proven, prop := ``PromoteCiNoop, thm := some ``promoteCi_noop },
  { id := "compiler-reinfer-cycle-group", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["verify_method(codeinst::CodeInstance, validation_world::UInt, workspace::VerifyMethodWorkspace)"],
    statement := "Two code instances on a common cycle of code instances awaiting verification are never left by verify_method one valid in the validation world and the other not.",
    source := "comment Compiler/src/reinfer.jl:383-386 (mark all other parts of the cycle with what we found)",
    status := .todo, prop := ``CycleGroupConsistent,
    notes := "Needs an invariant of the Tarjan stack over the whole state machine (stack members above a depth are exactly the open members of that SCC). Reading the source: a failure propagates to every ancestor up to the SCC root, and the root writes its result to every member, so no counterexample is known. The order of edges can change the written max_world of an empty range (min > max) but not whether a world is valid. The difftest checks it on every r.verifyMethod case (cycle:* tallies). An earlier version of the check that also followed edges through already-validated code instances reported splits; those cycles are not ones the verifier walks (it stops at a validated instance), and such a heap (a validated instance calling one still awaiting verification) is not one the runtime builds, so CIEdge only follows instances awaiting verification." },
  { id := "compiler-reinfer-range-bounded", juliaFile := "Compiler/src/reinfer.jl",
    juliaFns := ["verify_method(codeinst::CodeInstance, validation_world::UInt, workspace::VerifyMethodWorkspace)"],
    statement := "For a code instance awaiting verification, verify_method returns max_world <= validation_world, and min_world >= require_world unless it rejects.",
    source := "comment Compiler/src/reinfer.jl:260-261 (unable to backdate before require_world)",
    status := .todo, prop := ``VerifyRangeBounded,
    notes := "Needs the same whole-loop invariant (every initialized result state lies in [require_world, validation_world]). Each merge step only raises min and lowers max (returnToParent), which is what the invariant would rest on. The difftest checks it on every r.verifyMethod case of a root awaiting verification (range:* tallies)." }
]

end JuliaLean.Proofs.Compiler.src.reinfer
