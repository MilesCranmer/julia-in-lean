import JuliaLean.Loading.Model

/-! Deterministic differential rows. -/

namespace JuliaLean.Loading.Validation

open JuliaLean.Loading

private def s (text : String) : Str := text.toList

private def sampleDocument : LoadingDocument :=
  { projectName := some (s "Root"), projectUuid := some 1
    deps := [⟨some 2, s "Dep"⟩], weakdeps := [⟨some 3, s "Weak"⟩]
    extensions := [(s "RootExt", [s "Weak"])], sources := [(s "Dep", s "../Dep")]
    manifestFormat := some (s "2.0"), entryUuid := some 2
    entryDeps := [⟨some 3, s "Weak"⟩], entryWeakdeps := []
    entryExtensions := [(s "DepExt", [s "Weak"])], entryPath := some (s "../Dep")
    entryfile := some (s "lib/Dep.jl"), gitTreeSha1 := some (s "abc")
    syntaxMinor := some 15 }

private def freshCache : CacheFacts :=
  ⟨true, true, true, true, true, true, true, true, true, true, true⟩

def differential : IO Unit := do
  let first := PkgId.mk (some 1) (s "X")
  let second := PkgId.mk (some 2) (s "X")
  IO.println s!"lookup precedence => {identifyPackage [.absent, .found first, .found second] == some first}"
  IO.println s!"lookup blocked => {identifyPackage [.absent, .blocked, .found second] == none}"
  IO.println s!"manifest roundtrip => {parseDocument (renderDocument sampleDocument) == sampleDocument}"
  let collision : RawManifest :=
    { manifestFormat := some (.arrayTables true)
      topLevel := [(s "manifest_format", [sampleDocument])], depsTable := [] }
  IO.println s!"v1 collision => {isV1FormatManifest collision.manifestFormat},{getDeps collision == []}"
  IO.println s!"version expansion => {expandHashes ⟨1, 15, 0⟩ (s "v#.#.#.#") == s "v1.15.0.#"}"
  IO.println s!"extension triggers => {extMayLoadWeakdep (.one (s "Weak")) (s "Weak")},{extMayLoadWeakdep (.many [s "A", s "Weak"]) (s "Weak")}"
  IO.println s!"cache fresh => {staleCache freshCache}"
  IO.println s!"cache missing => {staleCache { freshCache with openable := false }}"
  IO.println s!"cache preferences stale => {staleCache { freshCache with preferencesMatch := false }}"
  IO.println s!"cycle => {cycleDetected 1 [2, 3, 1, 4]},{cycleDetected 1 [2, 3, 4]}"
  let depot := s "/tmp/depot"
  let escaped := namedEnvProjectPath depot (s "../../outside")
  IO.println s!"named environment contained => {pathContained (namedEnvRoot depot) escaped}"
  let home := s "/tmp/home"
  let project := s "/tmp/home2/member"
  IO.println s!"workspace boundary => {startsInHome home project},{actuallyInHome home project}"

end JuliaLean.Loading.Validation
