import JuliaLean.Artifacts.Model
import JuliaLean.Platforms.Props

/-! Properties promised by Artifacts docstrings or required by the artifact-container invariant. -/

namespace JuliaLean.Artifacts

open JuliaLean

/-- Slash lookup accepts exactly a nonempty artifact name followed by nonempty child
components other than `..`. In particular, every successful lookup remains within the
artifact directory. -/
def SlashLookupContained : Prop :=
  ∀ name : Str, (∃ result, artifactSlashLookup name = .ok result) ↔ unsafeSlashName name = false

/-- Bare names are unchanged, and forward and backward separators split identically when
the name and one tail component contain no separator. -/
def SlashSplitSemantics : Prop :=
  ∀ (name tail : Str), name.all (!isSlash ·) = true → tail.all (!isSlash ·) = true →
    splitArtifactSlash name = (name, []) ∧
    splitArtifactSlash (name ++ '/' :: tail) = (name, tail) ∧
    splitArtifactSlash (name ++ '\\' :: tail) = (name, tail)

/-- Missing `os` or `arch` is reported by `unpack_platform` as `nothing`. -/
def UnpackPlatformRequired : Prop :=
  ∀ (lc : Char → Char) (m : Meta),
    (dget m.stringFields (s% "os") = none ∨ dget m.stringFields (s% "arch") = none) →
    unpackPlatform lc m = .ok none

/-- `pack_platform!` writes every platform tag into the metadata dictionary. -/
def PackPlatformTags : Prop :=
  ∀ (m : Meta) (platform : Platforms.Platform) (key value : Str),
    (key, value) ∈ platform.tags →
    ∃ packedValue, dget (packPlatform m platform).stringFields key = some packedValue

/-- Artifact platform selection inherits the documented BinaryPlatforms best-match rule. -/
def ArtifactMetaSelectsBest : Prop :=
  ∀ (usem : Platforms.UserSem) (order : Platforms.Platform → List Platforms.Str)
    (entries : List (Platforms.Platform × Str)) (host : Platforms.Platform) (result : Option Str),
    artifactMetaPlatform usem order entries host = .ok result →
    match result with
    | none => ∀ entry ∈ entries,
        Platforms.platformsMatch usem (order entry.1) entry.1 host = .ok false
    | some value => ∃ platform, (platform, value) ∈ entries ∧
        Platforms.platformsMatch usem (order platform) platform host = .ok true ∧
        ∀ other ∈ entries,
          Platforms.platformsMatch usem (order other.1) other.1 host = .ok true →
          Platforms.matchLoss platform host ≤ Platforms.matchLoss other.1 host ∧
          (Platforms.matchLoss other.1 host = Platforms.matchLoss platform host →
            ∀ selectedTriplet otherTriplet,
              Platforms.triplet platform = .ok selectedTriplet →
              Platforms.triplet other.1 = .ok otherTriplet →
              Platforms.strLt selectedTriplet otherTriplet = false)

/-- `artifact_meta` returns a selected dictionary exactly when it contains a tree hash. -/
def ArtifactMetaRequiresHash : Prop :=
  ∀ m : Meta, requireHash (some m) = some m ↔ m.hash.isSome

/-- Download selection includes exactly resolved metadata with a download stanza, excluding
lazy metadata unless `include_lazy` is true. -/
def LazySelection : Prop :=
  ∀ (includeLazy : Bool) (resolved : List Resolved) (name : Name) (m : Meta),
    (name, m) ∈ selectDownloadable includeLazy resolved ↔
      (name, some m) ∈ resolved ∧ downloadable includeLazy m = true

/-- Higher-priority depot hash overrides win, and a processed UUID/name override wins over
an existing direct hash override for the bound artifact. -/
def OverridePrecedence : Prop :=
  (∀ (hash : Hash) (low high : OverrideTarget),
    nget (loadHashDepots [[(hash, .target high)], [(hash, .target low)]]).hash hash = some high) ∧
  (∀ (pkg : Uuid) (name : Name) (hash : Hash) (direct named : OverrideTarget),
    let state : OverrideState :=
      { uuid := [(pkg, [(name, named)])], hash := [(hash, direct)] }
    nget (processNameOverrides [(name, [hash])] pkg state).hash hash = some named)

/-- A malformed direct override emits an error and does not change the hash mapping. -/
def MalformedOverridesReported : Prop :=
  ∀ (state : OverrideState) (hash : Hash),
    let result := applyHashEntry state hash .invalid
    result.errors = state.errors + 1 ∧ result.hash = state.hash

/-- Both helpers that accept `pkg_uuid` process UUID/name overrides just as the file form of
`artifact_meta` does. -/
def PkgUuidKeywordsProcessOverrides : Prop :=
  ∀ (artifacts : ArtifactHashes) (pkg : Uuid) (name : Name) (state : OverrideState),
    (artifactHashState artifacts name (some pkg) state).2 =
        artifactMetaState artifacts (some pkg) state ∧
    selectDownloadableState artifacts (some pkg) state =
        artifactMetaState artifacts (some pkg) state

/-- Every accepted graph of path and hash override targets eventually resolves. -/
def AcceptedOverridesResolve : Prop :=
  ∀ (overrides : HashOverrides) (hash : Hash),
    ∃ fuel target, resolveOverride fuel overrides hash = some target

/-- A direct path override replaces all depot paths, and existence tests that path. -/
def ArtifactPathOverride : Prop :=
  ∀ (hash : Hash) (path : Nat) (depots : List Nat) (isDir : ArtifactLocation → Bool),
    artifactPaths 1 [(hash, .path path)] depots hash = some [.override path] ∧
    artifactExists isDir [.override path] = isDir (.override path) ∧
    artifactPath isDir [.override path] = some (.override path)

end JuliaLean.Artifacts
