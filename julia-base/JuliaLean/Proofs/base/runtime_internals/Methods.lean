import JuliaLean.base.runtime_internals
import JuliaLean.Proofs.base.runtime_internals.TypePreds
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.Methods

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.TypePreds


theorem enumFrom_eq (s : List (Option Nat)) (i : Nat) : enumFrom s i = (s.drop i).filterMap id := by
  rcases iterateIdx_spec s i with ⟨h1, h2⟩ | ⟨x, j, h1, h2, h3, h4⟩
  · rw [enumFrom, h2]; split
    · rfl
    · rename_i x j h; rw [h1] at h; cases h
  · rw [enumFrom, h4]; split
    · rename_i h; rw [h1] at h; cases h
    · rename_i x' j' h
      rw [h1] at h; cases h
      rw [enumFrom_eq s j]
termination_by s.length - i

/-! ## Properties -/

theorem juliaSlots_mem (n i : Nat) : i ∈ juliaSlots n ↔ 3 ≤ i ∧ i ≤ n ∧ i % 2 = 1 := by
  simp only [juliaSlots, List.mem_range']
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨(i - 3) / 2, by omega, by omega⟩

theorem checkArgs_sound (sf : Nat → Nat) (nsp : Nat) (ps : List Ty) :
    ∀ is, checkArgs sf nsp ps is = .ok true →
      ∀ i ∈ is, ∀ p, ps[i - 1]? = some p → slotUsed (sf (1 + i + nsp)) = true → isdispatchelem p = true
  | [], _, i, hi, _, _, _ => by simp at hi
  | k :: ks, h, i, hi, p, hp, hu => by
    simp only [checkArgs] at h
    split at h
    · cases h
    · rename_i q hq
      split at h
      · cases h
      · rename_i hc
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [hp] at hq; cases hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hc
          by_cases hd : isdispatchelem p = true
          · exact hd
          · exact absurd hu (by simp_all)
        · exact checkArgs_sound sf nsp ps ks h i hi p hp hu

theorem checkArgs_unused (sf : Nat → Nat) (nsp : Nat) (ps : List Ty) :
    ∀ is, (∀ i ∈ is, i - 1 < ps.length ∧ slotUsed (sf (1 + i + nsp)) = false) →
      checkArgs sf nsp ps is = .ok true
  | [], _ => rfl
  | k :: ks, h => by
    obtain ⟨h1, h2⟩ := h k (by simp)
    simp only [checkArgs, List.getElem?_eq_getElem h1, h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact checkArgs_unused sf nsp ps ks (fun i hi => h i (by simp [hi]))

theorem substTrivialBounds_noinst (egal : Ty → Ty → Bool) (fuel : Nat) :
    ∀ t, substTrivialBounds egal (fun _ _ => none) fuel t = t := by
  induction fuel with
  | zero => intro t; rfl
  | succ f ih =>
    intro t
    cases t with
    | unionAll v lb ub body =>
      simp only [substTrivialBounds, ih]
      split <;> rfl
    | _ => rfl

def MethodsBodies : Prop :=
  (∀ m : MethodList, mlSize m = [m.ms.length]) ∧
  (∀ m : MethodList, ∀ i : Int, 1 ≤ i → i ≤ m.ms.length → mlGetindex m i = .ok (m.ms.getD (i - 1).toNat 0)) ∧
  (∀ m : MethodList, ∀ i : Int, (i < 1 ∨ m.ms.length < i) → mlGetindex m i = .error .boundsError) ∧
  -- `methods` with a module filter keeps exactly the matches defined in it, in
  -- the runtime's order
  (∀ jl modOf sig tn world mods r, methods jl modOf sig tn world (some mods) = .ok r →
      ∀ m ∈ r.ms, modOf m ∈ mods) ∧
  (∀ jl modOf sig tn world mods r, methods jl modOf sig tn world mods = .ok r →
      ∃ tt ms, sig = .ok tt ∧ jl ⟨tt, none, -1, false, world, 0, typemaxUInt⟩ = some ms ∧ r.ms.Sublist ms ∧
        r.tn = tn) ∧
  (∀ jl modOf sig tn mods, methods jl modOf sig tn typemaxUInt mods = .error reflectionError) ∧
  (∀ jl modOf sig tn world tt ms, world ≠ typemaxUInt → sig = .ok tt →
      jl ⟨tt, none, -1, false, world, 0, typemaxUInt⟩ = some ms →
      methods jl modOf sig tn world none = .ok ⟨ms, tn⟩) ∧
  (∀ jl modOf sig tn world mod, methodsMod jl modOf sig tn world mod = methods jl modOf sig tn world (some [mod])) ∧
  (∀ jl modOf sig tn world mods, methodsAll jl modOf sig tn world mods = methods jl modOf sig tn world mods) ∧
  (∀ jl modOf sig tn world tt ms, world ≠ typemaxUInt → sig = .ok tt →
      jl ⟨tt, none, -1, true, world, 0, typemaxUInt⟩ = some ms →
      methodsIncludingAmbiguous jl modOf sig tn world = .ok ⟨ms, tn⟩) ∧
  (∀ jl t lim world, methodsByFtype3 jl t lim world = jl ⟨t, none, lim, false, world, 0, typemaxUInt⟩) ∧
  (∀ jl t mt lim world, methodsByFtype4 jl t mt lim world = jl ⟨t, mt, lim, false, world, 0, typemaxUInt⟩) ∧
  (∀ jl tt lim world, methods_ jl (.ok tt) lim world = .ok (methodsByFtype3 jl tt lim world)) ∧
  (∀ m, deleteMethod m = .disable m) ∧
  (∀ m, hasgeneratorMI m = m.hasGenerator) ∧
  -- IR access: compressed sources are decompressed, generated-only methods and
  -- missing code are errors with their documented messages
  (∀ u m s, m.source = some (.str s) → uncompressedIr u m = .ok (u m s)) ∧
  (∀ u m c, m.source = some (.codeInfo c) → uncompressedIr u m = .ok c) ∧
  (∀ u m, m.source = none → m.hasGenerator = true →
      uncompressedIr u m = .error (.errorException "Method is @generated; try `code_lowered` instead.")) ∧
  (∀ u m, m.source = none → m.hasGenerator = false →
      uncompressedIr u m = .error (.errorException "Code for this Method is not available.")) ∧
  (∀ u d ci s, uncompressedIrCI u d ci s = u d ci s) ∧
  (∀ m, getCiMi (.abiOverride m) = .ok m ∧ getCiMi (.mi m) = .ok m) ∧
  -- `generating_output`: no output means false; `true`/`false` select package
  -- or system-image generation
  (∀ o i, generatingOutput 0 o i = false) ∧
  (∀ g o, g ≠ 0 → generatingOutput g o none = true) ∧
  (∀ g o inc, g ≠ 0 → (generatingOutput g o (some inc) = true ↔ o = inc)) ∧
  (∀ (κ : Type) (rt : κ → Nat → Nat) c i, astSlotflag rt c i = rt c (i - 1)) ∧
  (∀ rt m, hasImageGlobalref rt m = rt m.source) ∧
  -- `may_invoke_generator`
  (∀ g m atp sp, mayInvokeGenerator true g m atp sp = .ok true) ∧
  (∀ g m atp sp, g.isStub = false → mayInvokeGenerator false g m atp sp = .ok false) ∧
  (∀ g m sp, mayInvokeGenerator false g m none sp = .ok false ∨ ∃ e, mayInvokeGenerator false g m none sp = .error e) ∧
  (∀ g m ps sp, mayInvokeGenerator false g m (some ps) sp = .ok true →
      let nsp := sp.length
      let nonva := if m.isva then m.nargs - 1 else m.nargs
      (∀ i, 1 ≤ i → i ≤ nsp → sp.getD (i - 1) false = true → slotUsed (g.slotflag (1 + i)) = false) ∧
      (∀ i, 1 ≤ i → i ≤ nonva → ∀ p, ps[i - 1]? = some p → slotUsed (g.slotflag (1 + i + nsp)) = true →
        isdispatchelem p = true)) ∧
  (∀ g m ps sp, g.isStub = true → g.genMethods.map List.length = some 1 → g.hasSource = true →
      g.nslots ≥ 1 + sp.length + ps.length → m.isva = false → m.nargs ≤ ps.length →
      (∀ k, slotUsed (g.slotflag k) = false) → mayInvokeGenerator false g m (some ps) sp = .ok true) ∧
  (∀ isDT g m atp sp, mayInvokeGeneratorMI isDT g m atp sp = mayInvokeGenerator isDT g m atp sp) ∧
  -- trivial-bound substitution changes nothing when no bound can be substituted
  (∀ egal fuel t, substTrivialBounds egal (fun _ _ => none) fuel t = t) ∧
  (∀ egal inst fuel t, (∀ v lb ub b, t ≠ .unionAll v lb ub b) → substTrivialBounds egal inst fuel t = t) ∧
  (∀ egal eqT env m atype sp, (∀ t, egal t t = true) →
      normalizeTypevars egal (fun _ _ => none) eqT env m atype sp = (atype, sp)) ∧
  (∀ norm m d ps sp, getNospecializeinferSig norm m (.dt d ps) sp = norm (.dt d ps) sp m) ∧
  (∀ norm m t sp, (∀ d ps, t ≠ .dt d ps) → getNospecializeinferSig norm m t sp = m.sig) ∧
  (∀ m, isNospecializeinfer m = true → isNospecialized m = true) ∧
  -- `specialize_method` hands a concrete signature through unchanged
  (∀ egal inst eqT env norm m d ps sp, isNospecializeinfer m = false →
      specializeMethod egal inst eqT env norm m (.dt d ps) sp false = .getLinfo m.id (.dt d ps) sp ∧
      specializeMethod egal inst eqT env norm m (.dt d ps) sp true = .lookup m.id (.dt d ps)) ∧
  (∀ egal inst eqT env norm mm p, specializeMethodMatch egal inst eqT env norm mm p =
      specializeMethod egal inst eqT env norm mm.method mm.specTypes mm.sparams p) ∧
  -- the method-table walk reads only the value slots `3:2:length(e)`, all in bounds
  (∀ n i, i ∈ juliaSlots n ↔ 3 ≤ i ∧ i ≤ n ∧ i % 2 = 1) ∧
  (∀ f funcs, visitTM (f + 1) (.entry funcs) = funcs) ∧
  (∀ fuel mt, lengthMT fuel mt = (methodListMT fuel mt).ms.length) ∧
  (∀ fuel mt, isemptyMT mt = true → lengthMT fuel mt = 0) ∧
  -- the specializations iterator yields exactly the non-empty slots, in order
  (∀ s, specializations false s = .none ∧ specializations true s = s) ∧
  iterateSpecs .none = none ∧ (∀ mi, iterateSpecs (.one mi) = some (mi, .nothing)) ∧
  (∀ sp, iterateSpecsFrom sp .nothing = .ok none) ∧
  (∀ s i, enumFrom s i = (s.drop i).filterMap id) ∧
  (∀ s, lengthSpecs (.svec s) = (s.filterMap id).length) ∧
  (∀ s i, (iterateIdx s i = none ∧ (s.drop i).filterMap id = []) ∨
    (∃ x j, iterateIdx s i = some (x, j) ∧ i < j ∧ j ≤ s.length ∧
      (s.drop i).filterMap id = x :: (s.drop j).filterMap id))

theorem methodsBodies_proven : MethodsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; rfl
  · intro m i h1 h2; simp [mlGetindex, h1, h2]
  · intro m i h
    have : ¬ (1 ≤ i ∧ i ≤ (m.ms.length : Int)) := by omega
    simp [mlGetindex, this]
  · intro jl modOf sig tn world mods r h m hm
    unfold methods at h
    split at h
    · cases h
    · simp only [methods_, bind, Except.bind] at h
      cases hs : sig with
      | error e => rw [hs] at h; cases h
      | ok tt =>
        rw [hs] at h
        simp only [pure, Except.pure] at h
        split at h
        · cases h
        · rename_i ms _
          cases h
          simp only [matchesToMethods, List.mem_filter, List.contains_iff_mem] at hm
          exact hm.2
  · intro jl modOf sig tn world mods r h
    unfold methods at h
    split at h
    · cases h
    · simp only [methods_, bind, Except.bind] at h
      cases hs : sig with
      | error e => rw [hs] at h; cases h
      | ok tt =>
        rw [hs] at h
        simp only [pure, Except.pure] at h
        split at h
        · cases h
        · rename_i ms hms
          cases h
          refine ⟨tt, ms, rfl, ?_, ?_, ?_⟩
          · simpa [methodsByFtype3, methodsByFtype4, methodsByFtype8] using hms
          · cases mods with
            | none => exact List.Sublist.refl _
            | some ms' => exact List.filter_sublist
          · cases mods <;> rfl
  · intro _ _ _ _ _; simp [methods]
  · intro jl modOf sig tn world tt ms hw hs hj
    simp [methods, hw, methods_, hs, bind, Except.bind, methodsByFtype3, methodsByFtype4, methodsByFtype8,
      hj, pure, Except.pure, matchesToMethods]
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro jl modOf sig tn world tt ms hw hs hj
    simp [methodsIncludingAmbiguous, hw, hs, bind, Except.bind, methodsByFtype8, hj, pure, Except.pure,
      matchesToMethods]
  · intro _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _; rfl
  · intro _; rfl
  · intro u m s h; simp [uncompressedIr, h, uncompressedIr_]
  · intro u m c h; simp [uncompressedIr, h, uncompressedIr_]
  · intro u m h1 h2; simp [uncompressedIr, h1, h2]
  · intro u m h1 h2; simp [uncompressedIr, h1, h2]
  · intro _ _ _ _; rfl
  · intro _; exact ⟨rfl, rfl⟩
  · intro o i; simp [generatingOutput]
  · intro g o h; simp [generatingOutput, h]
  · intro g o inc h
    simp only [generatingOutput, h, ↓reduceIte]
    by_cases hc : o = inc <;> simp [hc]
  · intro _ _ _ _; rfl
  · intro _ _; rfl
  · intro _ _ _ _; rfl
  · intro g m atp sp h; simp [mayInvokeGenerator, h]
  · intro g m sp
    unfold mayInvokeGenerator
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · left; rfl
    · split
      · left; rfl
      · split
        · left; rfl
        · split
          · left; rfl
          · left; rfl
  · intro g m ps sp h
    simp only
    unfold mayInvokeGenerator at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    split at h
    · cases h
    · rename_i gm _
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      · rename_i hany
        split at h
        · cases h
        · cases h
        · rename_i hc
          refine ⟨?_, ?_⟩
          · intro i h1 h2 hs
            cases hu : slotUsed (g.slotflag (1 + i))
            · rfl
            · exfalso; apply hany
              simp only [List.any_eq_true, List.mem_range', Bool.and_eq_true]
              exact ⟨i, ⟨i - 1, by omega, by omega⟩, hs, hu⟩
          · intro i h1 h2 p hp hu
            apply checkArgs_sound _ _ _ _ hc i _ p hp hu
            apply List.mem_range'.mpr
            refine ⟨i - 1, ?_, by omega⟩
            revert h2; split <;> intro h2 <;> omega
  · intro g m ps sp hst hgm hsrc hsl hva hn hu
    cases hg : g.genMethods with
    | none => rw [hg] at hgm; cases hgm
    | some gm =>
      rw [hg] at hgm
      simp only [Option.map_some, Option.some.injEq] at hgm
      have hca : checkArgs g.slotflag sp.length ps (List.range' 1 m.nargs) = .ok true := by
        apply checkArgs_unused
        intro i hi
        simp only [List.mem_range'] at hi
        obtain ⟨k, hk, rfl⟩ := hi
        exact ⟨by omega, hu _⟩
      simp [mayInvokeGenerator, hst, hg, hgm, hsrc, hsl, hva, hu, hca]
  · intro _ _ _ _ _; rfl
  · exact fun egal fuel t => substTrivialBounds_noinst egal fuel t
  · intro egal inst fuel t ht
    cases fuel with
    | zero => rfl
    | succ f =>
      cases t with
      | unionAll v lb ub b => exact absurd rfl (ht v lb ub b)
      | _ => rfl
  · intro egal eqT env m atype sp hrefl
    simp [normalizeTypevars, substTrivialBounds_noinst, hrefl]
  · intro _ _ _ _ _; rfl
  · intro norm m t sp ht
    cases t with
    | dt d ps => exact absurd rfl (ht d ps)
    | _ => rfl
  · intro m h; simp only [isNospecializeinfer, Bool.and_eq_true] at h; exact h.2
  · intro egal inst eqT env norm m d ps sp h
    simp [specializeMethod, h]
  · intro _ _ _ _ _ _ _; rfl
  · exact juliaSlots_mem
  · intro _ _; rfl
  · intro _ _; rfl
  · intro fuel mt h
    simp only [isemptyMT, Option.isNone_iff_eq_none] at h
    simp [lengthMT, visitMT, h]
  · intro s; exact ⟨rfl, rfl⟩
  · rfl
  · intro _; rfl
  · intro sp; cases sp <;> rfl
  · exact enumFrom_eq
  · intro s; simp [lengthSpecs, enumFrom_eq]
  · exact iterateIdx_spec
end JuliaLean.RuntimeCov.Methods
end
