import JuliaLean.Loading.Props

namespace JuliaLean.Loading

theorem lookupPrecedence_proven : LookupPrecedence := by
  intro earlier later pkg habsent
  induction earlier with
  | nil => simp [identifyPackage]
  | cons answer rest ih =>
      have hanswer : answer = .absent := habsent answer (by simp)
      subst answer
      have hrest : ∀ candidate ∈ rest, candidate = EnvAnswer.absent := by
        intro candidate hmem
        exact habsent candidate (by simp [hmem])
      simpa [identifyPackage] using ih hrest

theorem locatePrecedence_proven : LocatePrecedence := by
  intro earlier later spec habsent
  induction earlier with
  | nil => simp [locatePackage]
  | cons answer rest ih =>
      have hanswer : answer = none := habsent answer (by simp)
      subst answer
      have hrest : ∀ candidate ∈ rest, candidate = none := by
        intro candidate hmem
        exact habsent candidate (by simp [hmem])
      simpa [locatePackage] using ih hrest

theorem loadPathVersionExpansion_proven : LoadPathVersionExpansion := by
  intro version
  simp [expandHashes, expandHashesGo, versionComponent]

theorem manifestFieldsRoundtrip_proven : ManifestFieldsRoundtrip := by
  intro document
  cases document
  rfl

theorem extensionTriggersExact_proven : ExtensionTriggersExact := by
  constructor
  · intro trigger name
    simp [extMayLoadWeakdep]
  constructor
  · intro triggers name
    simp [extMayLoadWeakdep]
  · intro triggers loaded
    simp [extensionReady]

theorem cacheStalenessExact_proven : CacheStalenessExact := by
  intro facts
  rcases facts with ⟨a, b, c, d, e, f, g, h, i, j, k⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> decide

theorem cacheRelocatabilityExact_proven : CacheRelocatabilityExact := by
  intro includes
  simp [cacheRelocatable, Bool.and_eq_true, Bool.or_eq_true]

theorem preferencesStalenessExact_proven : PreferencesStalenessExact := by
  intro record current
  simp [stalePreferences]

private theorem mem_cycleTrace (current : Nat) (waitingOwners : List Nat) :
    current ∈ cycleTrace current waitingOwners ↔ current ∈ waitingOwners := by
  induction waitingOwners with
  | nil => simp [cycleTrace]
  | cons task rest ih =>
      by_cases h : task = current
      · subst task
        simp [cycleTrace]
      · simp [cycleTrace, h, ih]

theorem cycleDetectionExact_proven : CycleDetectionExact := by
  intro current waitingOwners
  simpa [cycleDetected] using mem_cycleTrace current waitingOwners

end JuliaLean.Loading
