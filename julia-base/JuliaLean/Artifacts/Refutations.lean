import JuliaLean.Artifacts.Props

namespace JuliaLean.Artifacts

open JuliaLean

/-- `payload/../escaped.txt` is accepted although its tail escapes the artifact directory. -/
theorem slashLookupContained_refuted : ¬ SlashLookupContained := by
  intro h
  have accepted : ∃ result, artifactSlashLookup (s% "payload/../escaped.txt") = .ok result :=
    ⟨splitArtifactSlash (s% "payload/../escaped.txt"), rfl⟩
  have safe := (h (s% "payload/../escaped.txt")).1 accepted
  exact (by decide : unsafeSlashName (s% "payload/../escaped.txt") ≠ false) safe

/-- Both accepted `pkg_uuid` keywords leave the override state unchanged. -/
theorem pkgUuidKeywordsProcessOverrides_refuted : ¬ PkgUuidKeywordsProcessOverrides := by
  intro h
  let name : Name := s% "payload"
  let artifacts : ArtifactHashes := [(name, [7])]
  let state : OverrideState :=
    { uuid := [(1, [(name, .path 9)])], hash := [] }
  have bad := h artifacts 1 name state
  revert bad
  decide

def cycleOverrides : HashOverrides := [(1, .hash 2), (2, .hash 1)]

theorem resolveCycle_none : ∀ fuel,
    resolveOverride fuel cycleOverrides 1 = none ∧
    resolveOverride fuel cycleOverrides 2 = none
  | 0 => by decide
  | fuel + 1 => by
      rw [show resolveOverride (fuel + 1) cycleOverrides 1 =
          resolveOverride fuel cycleOverrides 2 by rfl]
      rw [show resolveOverride (fuel + 1) cycleOverrides 2 =
          resolveOverride fuel cycleOverrides 1 by rfl]
      exact ⟨(resolveCycle_none fuel).2, (resolveCycle_none fuel).1⟩

/-- Two individually valid hash redirects can form a cycle that no finite unfolding resolves. -/
theorem acceptedOverridesResolve_refuted : ¬ AcceptedOverridesResolve := by
  intro h
  obtain ⟨fuel, target, resolved⟩ := h cycleOverrides 1
  rw [(resolveCycle_none fuel).1] at resolved
  contradiction

end JuliaLean.Artifacts
