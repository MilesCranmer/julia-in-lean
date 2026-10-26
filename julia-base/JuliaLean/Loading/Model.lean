import JuliaLean.Paths.Model

/-!
# Julia code-loading model

Pure control flow from `base/loading.jl` and the load-path expansion in
`base/initdefs.jl` at Julia `bbfa0ce4150`. POSIX path operations reuse the
existing `JuliaLean.Paths` model. Filesystem observations are explicit inputs.
-/

namespace JuliaLean.Loading

open JuliaLean

abbrev Str := Paths.Str
abbrev Uuid := Nat

/-! ## Package identity and ordered environment lookup -/

structure PkgId where
  uuid : Option Uuid
  name : Str
  deriving DecidableEq, Repr

structure PkgLoadSpec where
  path : Str
  editionMinor : Nat
  deriving DecidableEq, Repr

/-- The three results of `environment_deps_get` used by contextual
`identify_package_env`; `base/loading.jl:378-390`. -/
inductive EnvAnswer where
  | absent
  | blocked
  | found (pkg : PkgId)
  deriving DecidableEq, Repr

/-- Ordered environment search in `identify_package_env`; the UUID-less sentinel
stops the search without returning a package. -/
def identifyPackage : List EnvAnswer → Option PkgId
  | [] => none
  | .absent :: rest => identifyPackage rest
  | .blocked :: _ => none
  | .found pkg :: _ => some pkg

/-- Ordered search in `locate_package_env`; `base/loading.jl:480-536`. -/
def locatePackage : List (Option PkgLoadSpec) → Option PkgLoadSpec
  | [] => none
  | none :: rest => locatePackage rest
  | some spec :: _ => some spec

/-! ## LOAD_PATH expansion -/

structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr

def versionComponent (version : Version) : Nat → Str
  | 0 => Nat.toDigits 10 version.major
  | 1 => Nat.toDigits 10 version.minor
  | 2 => Nat.toDigits 10 version.patch
  | _ => ['#']

/-- The three sequential `replace(..., '#', count=1)` calls in
`base/initdefs.jl:346-348`. Further `#` characters remain unchanged. -/
def expandHashesGo (version : Version) : Str → Nat → Str
  | [], _ => []
  | c :: rest, seen =>
      if c == '#' then versionComponent version seen ++ expandHashesGo version rest (seen + 1)
      else c :: expandHashesGo version rest seen

def expandHashes (version : Version) (name : Str) : Str := expandHashesGo version name 0

def environmentsName : Str := "environments".toList
def projectName : Str := "Project.toml".toList

/-- Named-environment construction before filesystem probing;
`base/initdefs.jl:350-361`. -/
def namedEnvProjectPath (depot name : Str) : Str :=
  Paths.normpath ([environmentsName, name, projectName].foldl Paths.joinStep depot)

def namedEnvRoot (depot : Str) : Str := Paths.normpath (Paths.joinStep depot environmentsName)

def pathContained (root path : Str) : Bool :=
  path == root || (root ++ ['/']).isPrefixOf path

/-! ## Projects, manifests, and extensions -/

structure LoadingDocument where
  projectName : Option Str
  projectUuid : Option Uuid
  deps : List PkgId
  weakdeps : List PkgId
  extensions : List (Str × List Str)
  sources : List (Str × Str)
  manifestFormat : Option Str
  entryUuid : Option Uuid
  entryDeps : List PkgId
  entryWeakdeps : List PkgId
  entryExtensions : List (Str × List Str)
  entryPath : Option Str
  entryfile : Option Str
  gitTreeSha1 : Option Str
  syntaxMinor : Option Nat
  deriving DecidableEq, Repr

/-- Typed wire representation of the fields consumed from Project.toml and
Manifest.toml; `base/loading.jl:767-979,1094-1304`. -/
structure LoadingDocumentWire where
  projectName : Option Str
  projectUuid : Option Uuid
  deps : List PkgId
  weakdeps : List PkgId
  extensions : List (Str × List Str)
  sources : List (Str × Str)
  manifestFormat : Option Str
  entryUuid : Option Uuid
  entryDeps : List PkgId
  entryWeakdeps : List PkgId
  entryExtensions : List (Str × List Str)
  entryPath : Option Str
  entryfile : Option Str
  gitTreeSha1 : Option Str
  syntaxMinor : Option Nat
  deriving DecidableEq, Repr

def renderDocument (document : LoadingDocument) : LoadingDocumentWire :=
  ⟨document.projectName, document.projectUuid, document.deps, document.weakdeps,
   document.extensions, document.sources, document.manifestFormat, document.entryUuid,
   document.entryDeps, document.entryWeakdeps, document.entryExtensions,
   document.entryPath, document.entryfile, document.gitTreeSha1, document.syntaxMinor⟩

def parseDocument (wire : LoadingDocumentWire) : LoadingDocument :=
  ⟨wire.projectName, wire.projectUuid, wire.deps, wire.weakdeps, wire.extensions,
   wire.sources, wire.manifestFormat, wire.entryUuid, wire.entryDeps,
   wire.entryWeakdeps, wire.entryExtensions, wire.entryPath, wire.entryfile,
   wire.gitTreeSha1, wire.syntaxMinor⟩

inductive RawManifestValue where
  | scalar
  | table (hasUuid : Bool)
  | arrayTables (hasUuid : Bool)
  deriving DecidableEq, Repr

/-- `is_v1_format_manifest`; `base/loading.jl:1109-1120`. -/
def isV1FormatManifest : Option RawManifestValue → Bool
  | none => true
  | some (.table true) => true
  | some _ => false

abbrev ManifestDeps := List (Str × List LoadingDocument)

structure RawManifest where
  manifestFormat : Option RawManifestValue
  topLevel : ManifestDeps
  depsTable : ManifestDeps
  deriving DecidableEq, Repr

/-- `get_deps`; `base/loading.jl:1123-1129`. -/
def getDeps (manifest : RawManifest) : ManifestDeps :=
  if isV1FormatManifest manifest.manifestFormat then manifest.topLevel else manifest.depsTable

inductive TriggerSpec where
  | one (name : Str)
  | many (names : List Str)
  deriving DecidableEq, Repr

/-- Both methods of `ext_may_load_weakdep`; `base/loading.jl:782-783`. -/
def extMayLoadWeakdep (triggers : TriggerSpec) (name : Str) : Bool :=
  match triggers with
  | .one trigger => trigger == name
  | .many names => names.contains name

/-- Extension triggering after all declared trigger packages are loaded;
`base/loading.jl:1753-1925`. -/
def extensionReady (triggers loaded : List PkgId) : Bool :=
  triggers.all (fun trigger => loaded.contains trigger)

/-! ## Workspace boundary handling -/

/-- The raw `startswith(project_dir, home_dir)` test at `base/loading.jl:730`. -/
def startsInHome (home project : Str) : Bool := home.isPrefixOf project

/-- Path-component containment required by the comment at `base/loading.jl:729-730`. -/
def actuallyInHome (home project : Str) : Bool :=
  pathContained (Paths.normpath home) (Paths.normpath project)

/-! ## Cache validity and cycle detection -/

structure CacheFacts where
  openable : Bool
  headerCompatible : Bool
  flagsMatch : Bool
  modulesPresent : Bool
  syntaxMatches : Bool
  packageImageUsable : Bool
  identityMatches : Bool
  dependenciesUsable : Bool
  sourceFresh : Bool
  checksumsValid : Bool
  preferencesMatch : Bool
  deriving DecidableEq, Repr

/-- The early rejection sequence of `stale_cachefile`;
`base/loading.jl:4919-5135`. -/
def staleCache (facts : CacheFacts) : Bool :=
  if !facts.openable then true
  else if !facts.headerCompatible then true
  else if !facts.flagsMatch then true
  else if !facts.modulesPresent then true
  else if !facts.syntaxMatches then true
  else if !facts.packageImageUsable then true
  else if !facts.identityMatches then true
  else if !facts.dependenciesUsable then true
  else if !facts.sourceFresh then true
  else if !facts.checksumsValid then true
  else if !facts.preferencesMatch then true
  else false

def cacheUsable (facts : CacheFacts) : Bool :=
  facts.openable && facts.headerCompatible && facts.flagsMatch && facts.modulesPresent &&
  facts.syntaxMatches && facts.packageImageUsable && facts.identityMatches &&
  facts.dependenciesUsable && facts.sourceFresh && facts.checksumsValid && facts.preferencesMatch

structure IncludeFact where
  depotTagged : Bool
  sourceFile : Bool
  tracksContent : Bool
  deriving DecidableEq, Repr

/-- `isrelocatable`; `base/loading.jl:2303-2322`. -/
def cacheRelocatable (includes : List IncludeFact) : Bool :=
  includes.all fun inc =>
    inc.depotTagged && (inc.sourceFile || inc.tracksContent)

inductive PrefValue where
  | natural (value : Nat)
  | boolean (value : Bool)
  | string (value : Str)
  deriving DecidableEq, Repr

abbrev PrefKey := Uuid × Str
abbrev PrefState := List (PrefKey × PrefValue)

def prefGet (state : PrefState) (key : PrefKey) : Option PrefValue :=
  (state.find? (·.1 == key)).map (·.2)

structure PreferenceRecord where
  observed : PrefState
  unset : List PrefKey
  deriving DecidableEq, Repr

/-- `stale_prefs`; recorded values must remain equal and recorded missing keys
must remain absent; `base/loading.jl:4885-4909`. -/
def stalePreferences (record : PreferenceRecord) (current : PrefState) : Bool :=
  record.observed.any (fun entry => prefGet current entry.1 != some entry.2) ||
  record.unset.any (fun key => (prefGet current key).isSome)

/-- The dependency names collected while `canstart_loading` follows task waiters;
the walk stops when it reaches the current task; `base/loading.jl:2588-2609`. -/
def cycleTrace (current : Nat) : List Nat → List Nat
  | [] => []
  | task :: rest =>
      if task == current then [task] else task :: cycleTrace current rest

def cycleDetected (current : Nat) (waitingOwners : List Nat) : Bool :=
  (cycleTrace current waitingOwners).contains current

end JuliaLean.Loading
