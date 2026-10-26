import JuliaLean.Loading.Props

namespace JuliaLean.Loading

theorem v1ManifestFormatPackagePreserved_refuted : ¬ V1ManifestFormatPackagePreserved := by
  intro h
  have bad := h []
  revert bad
  decide

theorem namedEnvContained_refuted : ¬ NamedEnvContained := by
  intro h
  have bad := h "/tmp/depot".toList "../../outside".toList
  revert bad
  decide +kernel

theorem workspaceHomeBoundary_refuted : ¬ WorkspaceHomeBoundary := by
  intro h
  have bad := h "/tmp/home".toList "/tmp/home2/member".toList
  revert bad
  decide +kernel

end JuliaLean.Loading
