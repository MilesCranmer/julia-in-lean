import JuliaLean.base.cpuid
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.CpuId

open JuliaLean.RuntimeCov

/-! ## Properties -/

/-- The documented and invariant behaviour of `base/cpuid.jl`. Every decoded
feature bit is below `8 * length(buf)` and comes from a set bit; empty lookups
give the empty ISA; `feature_names` returns one name per feature as a
permutation of the mapped names; ISA lists keep their labels; CPU-supports
names accept exactly literal symbols and strings; normalization maps the
documented aliases; `@cpu_supports` errors on unknown architectures and folds
to `false` on other hosts. -/
def CpuIdBodies : Prop :=
  (∀ (buf : List Nat) (n : Nat), n ∈ (featurebytesToIsa buf).features →
      n < 8 * buf.length ∧ (buf.getD (n / 8) 0 >>> (n % 8)) % 2 ≠ 0) ∧
  (∀ (lookup : Nat × List Nat), crossLookupCpu 0 lookup = ⟨[]⟩) ∧
  (∀ (n : Nat) (buf : List Nat), n ≠ 0 → crossLookupCpu n (0, buf) = ⟨[]⟩) ∧
  (∀ (ret : Int) (buf : List Nat), ret ≠ 0 → lookupCpu ret buf = ⟨[]⟩) ∧
  (∀ (buf : List Nat), lookupCpu 0 buf = hostIsa buf ∧ cpuIsa buf = hostIsa buf) ∧
  (∀ (entries : List (Option String × Int)) (isa : ISA),
      (featureNamesIsa entries isa).length = isa.features.length ∧
      (featureNamesIsa entries isa).Perm (isa.features.map (nameOf (buildBitToName entries [])))) ∧
  (∀ (entries : List (Option String × Int)) (n : Nat) (lk : Nat × List Nat),
      featureNamesCpu entries n lk = featureNamesIsa entries (crossLookupCpu n lk)) ∧
  (∀ (e : List (Option String × Int)) (isa : ISA),
      featureNamesHost e isa = featureNamesIsa e isa) ∧
  (∀ (cross : String → ISA) (entries : List (String × String)),
      (makeIsaList cross entries).map Prod.fst = entries.map Prod.fst) ∧
  (∀ (rt : Nat → Bool) (f : Nat), testCpuFeature rt f = rt f) ∧
  (∀ r : Option String, cpuModelFeatures r = none ↔ r = none) ∧
  (∀ x : MacroArg, (∃ s, cpuSupportsName x = .ok s) ↔
      (match x with | .sym _ | .quoteSym _ | .str _ => True | _ => False)) ∧
  (∀ (lower : String → String) (s : String), lower s = "amd64" → normalizeArch lower s = "x86_64") ∧
  (∀ (lower : String → String) (s : String), lower s = "arm64" → normalizeArch lower s = "aarch64") ∧
  (∀ (lower : String → String) (hostArch : Sym) known model (a0 : MacroArg) (rest : List MacroArg)
      (s : Sym), rest ≠ [] → cpuSupportsName a0 = .ok s →
      normalizeArch lower s ∉ supportsArches →
      ∃ e, cpuSupports lower hostArch known model (a0 :: rest) = .error e) ∧
  (∀ (lower : String → String) (hostArch : Sym) known model (a0 : MacroArg) (rest : List MacroArg)
      (s : Sym) (ns : List Sym), rest ≠ [] → cpuSupportsName a0 = .ok s →
      normalizeArch lower s ∈ supportsArches → normalizeArch lower s ≠ hostArch →
      mapNames rest = .ok ns →
      cpuSupports lower hostArch known model (a0 :: rest) = .ok .constFalse) ∧
  (∀ (lower : String → String) (hostArch : Sym) known model (a : MacroArg),
      ∃ e, cpuSupports lower hostArch known model [a] = .error e)

theorem byteBits_mem (i b n : Nat) (h : n ∈ byteBits i b) :
    i * 8 ≤ n ∧ n < i * 8 + 8 ∧ (b >>> (n - i * 8)) % 2 ≠ 0 := by
  unfold byteBits at h
  split at h
  · simp at h
  · simp only [List.mem_filterMap, List.mem_range] at h
    obtain ⟨bit, hbit, hs⟩ := h
    split at hs
    · simp at hs; subst hs
      refine ⟨by omega, by omega, ?_⟩
      have : i * 8 + bit - i * 8 = bit := by omega
      rw [this]; assumption
    · simp at hs

theorem featurebytes_mem (buf : List Nat) (n : Nat) (h : n ∈ (featurebytesToIsa buf).features) :
    n < 8 * buf.length ∧ (buf.getD (n / 8) 0 >>> (n % 8)) % 2 ≠ 0 := by
  simp only [featurebytesToIsa, List.mem_flatMap, List.mem_range] at h
  obtain ⟨i, hi, hn⟩ := h
  obtain ⟨h1, h2, h3⟩ := byteBits_mem i _ n hn
  have hdiv : n / 8 = i := by omega
  have hmod : n % 8 = n - i * 8 := by omega
  refine ⟨by omega, ?_⟩
  rw [hdiv, hmod]; exact h3

theorem makeIsaList_fst (cross : String → ISA) : ∀ entries : List (String × String),
    (makeIsaList cross entries).map Prod.fst = entries.map Prod.fst
  | [] => rfl
  | (l, c) :: rest => by
      show (if c.isEmpty then (l, (⟨[]⟩ : ISA)) else (l, cross c)).1 ::
          (makeIsaList cross rest).map Prod.fst = l :: rest.map Prod.fst
      rw [makeIsaList_fst cross rest]
      split <;> rfl

theorem cpuIdBodies_proven : CpuIdBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro buf n h; exact featurebytes_mem buf n h
  · intro lookup; simp [crossLookupCpu]
  · intro n buf hn; simp [crossLookupCpu, hn]
  · intro ret buf h; simp [lookupCpu, h]
  · intro buf; exact ⟨by simp [lookupCpu, hostIsa], rfl⟩
  · intro entries isa
    refine ⟨?_, ?_⟩
    · simp [featureNamesIsa, List.length_mergeSort]
    · exact List.mergeSort_perm _ _
  · intro _ _ _; rfl
  · intro _ _; rfl
  · intro cross entries; exact makeIsaList_fst cross entries
  · intro _ _; rfl
  · intro r; cases r <;> simp [cpuModelFeatures]
  · intro x; cases x <;> simp [cpuSupportsName]
  · intro lower s h; simp [normalizeArch, h]
  · intro lower s h; simp [normalizeArch, h]
  · intro lower hostArch known model a0 rest s hrest hs hn
    cases rest with
    | nil => exact absurd rfl hrest
    | cons r1 rs =>
      simp only [cpuSupports, hs, bind, Except.bind]
      simp [hn]
  · intro lower hostArch known model a0 rest s ns hrest hs hin hne hns
    cases rest with
    | nil => exact absurd rfl hrest
    | cons r1 rs =>
      simp only [cpuSupports, hs, bind, Except.bind]
      simp [hin, hns, hne]
      try rfl
  · intro lower hostArch known model a; exact ⟨_, rfl⟩

/-- The `isless` contract ("a fixed total order"): incomparability under
`isless(::ISA, ::ISA)` is transitive, as `sort` and other ordered algorithms
require of their `lt`. -/
def IsaIslessStrictWeak : Prop :=
  ∀ x y z : ISA, isless x y = false → isless y x = false →
    isless y z = false → isless z y = false → isless x z = false

/-- `{1}` and `{3}` are incomparable, `{3}` and `{1,2}` are incomparable, yet
`{1} ⊊ {1,2}`. -/
theorem isaIslessStrictWeak_refuted : ¬ IsaIslessStrictWeak := by
  intro h
  have := h ⟨[1]⟩ ⟨[3]⟩ ⟨[1, 2]⟩ (by decide) (by decide) (by decide) (by decide)
  revert this; decide
end JuliaLean.RuntimeCov.CpuId
end
