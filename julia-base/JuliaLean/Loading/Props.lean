import JuliaLean.Loading.Model

/-! Properties from the code-loading docstrings, manual, and source invariants. -/

namespace JuliaLean.Loading

def LookupPrecedence : Prop :=
  ∀ (earlier later : List EnvAnswer) (pkg : PkgId),
    (∀ answer ∈ earlier, answer = .absent) →
    identifyPackage (earlier ++ .found pkg :: later) = some pkg ∧
    identifyPackage (earlier ++ .blocked :: later) = none

def LocatePrecedence : Prop :=
  ∀ (earlier later : List (Option PkgLoadSpec)) (spec : PkgLoadSpec),
    (∀ answer ∈ earlier, answer = none) →
    locatePackage (earlier ++ some spec :: later) = some spec

def LoadPathVersionExpansion : Prop :=
  ∀ version : Version,
    expandHashes version "v#.#.#.#".toList =
      ['v'] ++ Nat.toDigits 10 version.major ++ ['.'] ++
      Nat.toDigits 10 version.minor ++ ['.'] ++ Nat.toDigits 10 version.patch ++ ['.', '#']

def ManifestFieldsRoundtrip : Prop :=
  ∀ document : LoadingDocument, parseDocument (renderDocument document) = document

def manifestFormatName : Str := "manifest_format".toList

/-- The compatibility branch claims to preserve a v1 package named
`manifest_format`, represented by a TOML array of tables. -/
def V1ManifestFormatPackagePreserved : Prop :=
  ∀ entries : List LoadingDocument,
    getDeps { manifestFormat := some (.arrayTables true)
              topLevel := [(manifestFormatName, entries)], depsTable := [] } =
      [(manifestFormatName, entries)]

def ExtensionTriggersExact : Prop :=
  (∀ trigger name : Str,
    extMayLoadWeakdep (.one trigger) name = true ↔ trigger = name) ∧
  (∀ triggers : List Str, ∀ name : Str,
    extMayLoadWeakdep (.many triggers) name = true ↔ name ∈ triggers) ∧
  (∀ triggers loaded : List PkgId,
    extensionReady triggers loaded = true ↔ ∀ trigger ∈ triggers, trigger ∈ loaded)

def CacheStalenessExact : Prop :=
  ∀ facts : CacheFacts, staleCache facts = !cacheUsable facts

def CacheRelocatabilityExact : Prop :=
  ∀ includes : List IncludeFact,
    cacheRelocatable includes = true ↔
      ∀ inc ∈ includes,
        inc.depotTagged = true ∧ (inc.sourceFile = true ∨ inc.tracksContent = true)

def PreferencesStalenessExact : Prop :=
  ∀ (record : PreferenceRecord) (current : PrefState),
    stalePreferences record current = false ↔
      (∀ entry ∈ record.observed, prefGet current entry.1 = some entry.2) ∧
      (∀ key ∈ record.unset, prefGet current key = none)

def CycleDetectionExact : Prop :=
  ∀ (current : Nat) (waitingOwners : List Nat),
    cycleDetected current waitingOwners = true ↔ current ∈ waitingOwners

/-- Named `@name` environments stay below the documented depot environments directory. -/
def NamedEnvContained : Prop :=
  ∀ (depot name : Str),
    pathContained (namedEnvRoot depot) (namedEnvProjectPath depot name) = true

/-- The home-boundary classification uses path components rather than a lexical prefix. -/
def WorkspaceHomeBoundary : Prop :=
  ∀ (home project : Str), startsInHome home project = actuallyInHome home project

end JuliaLean.Loading
