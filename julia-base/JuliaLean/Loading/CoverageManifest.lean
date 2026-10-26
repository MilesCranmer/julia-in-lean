import JuliaLean.Loading.CoverageEarly

namespace JuliaLean.Loading.Coverage.Manifest

open JuliaLean.Loading.Coverage
open JuliaLean.Loading.Coverage.Early

def method767 (dependency : Option Nat) (name : String) : PackageId :=
  match dependency with | none => ⟨none, name⟩ | some uuid => ⟨some uuid, name⟩

def Property767 : Prop := ∀ dependency name,
  (method767 dependency name).name = name ∧ (method767 dependency name).uuid = dependency
theorem property767 : Property767 := by
  intro dependency name
  cases dependency <;> simp [method767]

def method774 (projectIdentity : PackageId) (context : Option PackageId)
    (dependency : PackageId) : Option PackageId :=
  match context with
  | some pkg => if projectIdentity != pkg then none else some dependency
  | none => some dependency

def Property774 : Prop := ∀ project context dependency result,
  method774 project context dependency = some result → result = dependency
theorem property774 : Property774 := by
  intro project context dependency result h
  cases context <;> simp_all [method774]

structure ExtensionFacts where
  declared : Bool
  identityMatches : Bool
  triggerMatches : Bool
  weakdep : Option PackageId
  ordinaryDep : PackageId
  deriving Repr, DecidableEq

def method785 (facts : ExtensionFacts) : Option PackageId :=
  if facts.declared && facts.identityMatches then
    if facts.triggerMatches then choose facts.weakdep (some facts.ordinaryDep)
    else some facts.ordinaryDep
  else none

def Property785 : Prop := ∀ facts pkg,
  method785 facts = some pkg → facts.declared = true ∧ facts.identityMatches = true ∧
    (pkg = facts.ordinaryDep ∨ facts.weakdep = some pkg)
theorem property785 : Property785 := by
  intro facts pkg h
  rcases facts with ⟨declared, identity, trigger, weakdep, ordinary⟩
  cases declared <;> cases identity <;> cases trigger <;> cases weakdep <;>
    simp_all [method785, choose]

inductive ProjectKind where | missing | implicit | explicit
  deriving Repr, DecidableEq

structure EnvironmentFacts where
  kind : ProjectKind
  topLevel : Bool
  implicitPackage : Option PackageId
  implicitProjectFound : Bool
  projectPackage : Option PackageId
  extensionPackage : Option PackageId
  manifestPackage : Option PackageId
  deriving Repr, DecidableEq

def method809 (facts : EnvironmentFacts) : Option PackageId :=
  match facts.kind with
  | .missing => none
  | .implicit =>
      if facts.topLevel then facts.implicitPackage
      else if !facts.implicitProjectFound then none
      else match facts.projectPackage with
        | some pkg => some pkg
        | none => choose facts.extensionPackage (some ⟨none, ""⟩)
  | .explicit =>
      match facts.projectPackage with
      | some pkg => if facts.topLevel && pkg.uuid.isNone then none else some pkg
      | none => choose facts.extensionPackage facts.manifestPackage

def Property809 : Prop := ∀ facts pkg,
  method809 facts = some pkg → facts.kind ≠ .missing
theorem property809 : Property809 := by
  intro facts pkg h
  rcases facts with ⟨kind, top, implicitPkg, projectFound, projectPkg, extensionPkg, manifestPkg⟩
  cases kind <;> simp_all [method809, choose]

inductive ManifestSpecFacts where
  | explicit (project extension manifest : Option LoadSpec)
  | implicit (project extension : Option LoadSpec)
  | missing
  deriving Repr, DecidableEq

def method868 : ManifestSpecFacts → Option LoadSpec
  | .explicit project extension manifest => choose project (choose extension manifest)
  | .implicit project extension => choose project extension
  | .missing => none

def Property868 : Prop := ∀ facts spec,
  method868 facts = some spec →
  match facts with
  | .explicit project extension manifest => spec ∈ [project, extension, manifest].filterMap id
  | .implicit project extension => spec ∈ [project, extension].filterMap id
  | .missing => False
theorem property868 : Property868 := by
  intro facts spec h
  cases facts with
  | missing => simp [method868] at h
  | explicit project extension manifest =>
      cases project <;> cases extension <;> cases manifest <;> simp_all [method868, choose]
  | implicit project extension =>
      cases project <;> cases extension <;> simp_all [method868, choose]

def method910 (nestedExists : Bool) (nested flat : String) : String :=
  if nestedExists then nested else flat
def Property910 : Prop := ∀ isPresent nested flat,
  method910 isPresent nested flat = nested ∨ method910 isPresent nested flat = flat
theorem property910 : Property910 := by
  intro isPresent nested flat
  cases isPresent <;> simp [method910]

def method916 (declared identityMatches : Bool) (path : String) (edition : Nat) : Option LoadSpec :=
  if declared && identityMatches then some ⟨path, edition⟩ else none
def Property916 : Prop := ∀ declared identity path edition spec,
  method916 declared identity path edition = some spec →
  declared = true ∧ identity = true ∧ spec = ⟨path, edition⟩
theorem property916 : Property916 := by simp [Property916, method916]

def method930 (declaredName fallbackName : String) (declaredUuid dummyUuid : Option Nat) : PackageId :=
  ⟨choose declaredUuid dummyUuid, if declaredName.isEmpty then fallbackName else declaredName⟩
def Property930 : Prop := ∀ declared fallback uuid dummy,
  (method930 declared fallback uuid dummy).uuid = choose uuid dummy
theorem property930 : Property930 := by simp [Property930, method930, choose]

def method938 (syntaxVersion compat current oldest : Option Nat) : Nat :=
  let selected := choose syntaxVersion compat
  match selected with
  | none => current.getD 0
  | some version => max (oldest.getD 0) version
def Property938 : Prop := ∀ syntaxVersion compat current oldest,
  method938 syntaxVersion compat current oldest ≥ oldest.getD 0 ∨ syntaxVersion.isNone ∧ compat.isNone
theorem property938 : Property938 := by
  intro syntaxVersion compat current oldest
  simp only [method938]
  cases syntaxVersion <;> cases compat <;> simp [choose] <;> omega

def method970 (oldPath entryfile : Option String) (defaultPath : String) (edition : Nat) : LoadSpec :=
  ⟨choose oldPath entryfile |>.getD defaultPath, edition⟩
def Property970 : Prop := ∀ old entry defaultPath edition,
  (method970 old entry defaultPath edition).edition = edition
theorem property970 : Property970 := by simp [Property970, method970]

def method981 (base manifest : Option String) : Option String :=
  if base.isSome then manifest else none
def Property981 : Prop := ∀ base manifest result,
  method981 base manifest = some result → base.isSome ∧ manifest = some result
theorem property981 : Property981 := by
  intro base manifest result h; cases base <;> simp_all [method981]

def method989 (projectExists : Bool) (projectEdition currentEdition : Nat)
    (parseSucceeded : Bool) : Nat :=
  if projectExists && parseSucceeded then projectEdition else currentEdition
def Property989 : Prop := ∀ isPresent project current success,
  method989 isPresent project current success = project ∨ method989 isPresent project current success = current
theorem property989 : Property989 := by
  intro isPresent project current success
  cases isPresent <;> cases success <;> simp [method989]

structure ManifestPathFacts where
  projectExists : Bool
  workspace : Option String
  explicit : Option String
  named : List String
  deriving Repr, DecidableEq

def method1003 (facts : ManifestPathFacts) : Option String :=
  if !facts.projectExists then none
  else choose facts.workspace (choose facts.explicit facts.named.head?)
def Property1003 : Prop := ∀ facts path,
  method1003 facts = some path → facts.projectExists = true ∧
    (facts.workspace = some path ∨ facts.explicit = some path ∨ path ∈ facts.named)
theorem property1003 : Property1003 := by
  intro facts path h
  rcases facts with ⟨projectExists, workspace, explicitPath, named⟩
  cases projectExists <;> cases workspace <;> cases explicitPath <;> cases named <;>
    simp_all [method1003, choose]

def method1043 (source : Option String) (projectCandidates : List String) : Option String × Option String :=
  match source with
  | none => (none, none)
  | some path => (some path, projectCandidates.head?)
def Property1043 : Prop := ∀ source projects path project,
  method1043 source projects = (some path, project) → source = some path
theorem property1043 : Property1043 := by
  intro source projects path project h; cases source <;> simp_all [method1043]

def method1056 (directory dotJl bare : Option (String × Option String)) : Option (String × Option String) :=
  choose directory (choose dotJl bare)
def Property1056 : Prop := ∀ directory dotJl bare result,
  method1056 directory dotJl bare = some result →
  directory = some result ∨ dotJl = some result ∨ bare = some result
theorem property1056 : Property1056 := by
  intro directory dotJl bare result h
  cases directory <;> cases dotJl <;> cases bare <;> simp_all [method1056, choose]

def method1070 (projects : List (Option (LoadSpec × String))) : Option (LoadSpec × String) :=
  firstSome projects
def Property1070 : Prop := ∀ projects result,
  method1070 projects = some result → some result ∈ projects
theorem property1070 : Property1070 := by
  intro projects result h
  induction projects with
  | nil => simp [method1070, firstSome] at h
  | cons head rest ih => cases head <;> simp_all [method1070, firstSome]

def method1083 (pathIsFile : Bool) (path defaultEntry entryfile : String) : String :=
  if pathIsFile then path else if entryfile.isEmpty then defaultEntry else entryfile
def Property1083 : Prop := ∀ isFile path defaultEntry entry,
  method1083 isFile path defaultEntry entry ∈ [path, defaultEntry, entry]
theorem property1083 : Property1083 := by
  intro isFile path defaultEntry entry
  cases isFile <;> by_cases h : entry.isEmpty <;> simp [method1083, h]

def method1094 (rootName name : String) (rootUuid dummyUuid dependency : Option Nat) : Option Nat :=
  if rootName == name then choose rootUuid dummyUuid else dependency
def Property1094 : Prop := ∀ root name uuid dummy dep result,
  method1094 root name uuid dummy dep = some result →
  result ∈ [uuid, dummy, dep].filterMap id
theorem property1094 : Property1094 := by
  intro root name uuid dummy dep result h
  simp only [method1094] at h
  split at h <;> simp_all
  all_goals cases uuid <;> cases dummy <;> cases dep <;> simp_all [choose]

def method1132 (entries : List (String × Nat)) (name : String) : Option PackageId :=
  (entries.find? fun pair => pair.1 == name).map fun pair => ⟨some pair.2, name⟩
def Property1132 : Prop := ∀ entries name pkg,
  method1132 entries name = some pkg → pkg.name = name ∧ pkg.uuid.isSome
theorem property1132 : Property1132 := by
  intro entries name pkg h
  simp [method1132] at h
  rcases h with ⟨entryName, uuid, found, rfl⟩
  simp

def method1142 (entries : List String) (name : String) : Option PackageId :=
  if name ∈ entries then some ⟨none, name⟩ else none
def Property1142 : Prop := ∀ entries name pkg,
  method1142 entries name = some pkg → name ∈ entries ∧ pkg = ⟨none, name⟩
theorem property1142 : Property1142 := by simp [Property1142, method1142]

def method1147 (_name : String) : Option PackageId := none
def Property1147 : Prop := ∀ name, method1147 name = none
theorem property1147 : Property1147 := by simp [Property1147, method1147]

inductive DependencyAnswer where
  | unrelated
  | blocked (name : String)
  | found (pkg : PackageId)
  deriving Repr, DecidableEq

def method1149 : List DependencyAnswer → Option PackageId
  | [] => none
  | .unrelated :: rest => method1149 rest
  | .blocked name :: _ => some ⟨none, name⟩
  | .found pkg :: _ => some pkg
def Property1149 : Prop := ∀ answers pkg,
  method1149 answers = some pkg →
  DependencyAnswer.found pkg ∈ answers ∨
  ∃ name, DependencyAnswer.blocked name ∈ answers ∧ pkg = ⟨none, name⟩
theorem property1149 : Property1149 := by
  intro answers pkg h
  induction answers with
  | nil => simp [method1149] at h
  | cons answer rest ih =>
      cases answer <;> simp_all [method1149]

inductive SpecAnswer where | skip | found (spec : LoadSpec) | stop
  deriving Repr, DecidableEq
def method1222 : List SpecAnswer → Option (Option LoadSpec)
  | [] => none
  | .skip :: rest => method1222 rest
  | .found spec :: _ => some (some spec)
  | .stop :: _ => some none
def Property1222 : Prop := ∀ answers spec,
  method1222 answers = some (some spec) → SpecAnswer.found spec ∈ answers
theorem property1222 : Property1222 := by
  intro answers spec h
  induction answers with
  | nil => simp [method1222] at h
  | cons answer rest ih => cases answer <;> simp_all [method1222]

structure EntrySpecFacts where
  edition : Nat
  path : Option String
  stdlib : Option String
  depotPaths : List String
  deriving Repr, DecidableEq
def method1259 (facts : EntrySpecFacts) : Option (Option LoadSpec) :=
  match facts.path with
  | some path => some (some ⟨path, facts.edition⟩)
  | none => match facts.stdlib with
    | some path => some (some ⟨path, facts.edition⟩)
    | none => match facts.depotPaths.head? with
      | some path => some (some ⟨path, facts.edition⟩)
      | none => some none
def Property1259 : Prop := ∀ facts spec,
  method1259 facts = some (some spec) → spec.edition = facts.edition
theorem property1259 : Property1259 := by
  intro facts spec h
  rcases facts with ⟨edition, path, stdlib, depots⟩
  cases path <;> cases stdlib <;> cases depots <;> simp_all [method1259]
  all_goals cases h; rfl

def method1308 (source : Option String) (project : Option PackageId) (name : String) : Option PackageId :=
  match project with
  | none => if source.isSome then some ⟨none, name⟩ else none
  | some pkg => if pkg.name == name then some pkg else none
def Property1308 : Prop := ∀ source project name pkg,
  method1308 source project name = some pkg → pkg.name = name
theorem property1308 : Property1308 := by
  intro source project name pkg h
  cases project with
  | none =>
      simp [method1308] at h
      exact (congrArg PackageId.name h.2).symm
  | some found =>
      simp [method1308] at h
      exact h.2 ▸ h.1

def method1319 (uuidPresent : Bool) (project extension : Option String)
    (identityMatches : Bool) : Option String :=
  if !uuidPresent then none else match project with
  | none => extension
  | some path => if identityMatches then some path else none
def Property1319 : Prop := ∀ uuid project extension identity path,
  method1319 uuid project extension identity = some path → uuid = true
theorem property1319 : Property1319 := by
  intro uuid project extension identity path h
  cases uuid <;> simp_all [method1319]

def method1332 (source : Option String) (project : Option PackageId)
    (requested : PackageId) (edition : Nat) : Option LoadSpec :=
  match source, project with
  | none, _ => none
  | some path, none => if requested.uuid.isNone then some ⟨path, edition⟩ else none
  | some path, some pkg => if pkg == requested then some ⟨path, edition⟩ else none
def Property1332 : Prop := ∀ source project requested edition spec,
  method1332 source project requested edition = some spec → spec.edition = edition
theorem property1332 : Property1332 := by
  intro source project requested edition spec h
  cases source <;> cases project <;> simp [method1332] at h
  all_goals exact (congrArg LoadSpec.edition h.2).symm

def method1346 (absolute localPath installed : Option String) : Option String :=
  choose absolute (choose localPath installed)
def Property1346 : Prop := ∀ absolute localPath installed result,
  method1346 absolute localPath installed = some result →
  absolute = some result ∨ localPath = some result ∨ installed = some result
theorem property1346 : Property1346 := by
  intro absolute localPath installed result h
  cases absolute <;> cases localPath <;> cases installed <;> simp_all [method1346, choose]

def method1355 (buildShare share dataRoot : String) : List String :=
  (if buildShare == share then [] else [buildShare, share]) ++
  (if dataRoot.isEmpty then [] else [dataRoot, share]) ++ ["", share ++ "/base"]
def Property1355 : Prop := ∀ build share data,
  "" ∈ method1355 build share data
theorem property1355 : Property1355 := by simp [Property1355, method1355]

def method1366 (uuid : Option Nat) (name version slug : String) : String × String :=
  match uuid with
  | none => ("compiled/" ++ version, name)
  | some _ => ("compiled/" ++ version ++ "/" ++ name, slug)
def Property1366 : Prop := ∀ uuid name version slug,
  (method1366 uuid name version slug).1.startsWith "compiled/" = true
theorem property1366 : Property1366 := by
  intro uuid name version slug; cases uuid <;> simp [method1366]

def method1378 (directoryExists useImages : Bool)
    (entries : List (String × Bool)) : List String × List Bool :=
  if !directoryExists then ([], []) else
  (entries.map Prod.fst, entries.map fun entry => useImages && entry.2)
def Property1378 : Prop := ∀ directoryExists useImages entries,
  (method1378 directoryExists useImages entries).1.length =
  (method1378 directoryExists useImages entries).2.length
theorem property1378 : Property1378 := by
  intro directoryExists useImages entries; cases directoryExists <;> simp [method1378]

structure CacheCandidate where
  path : String
  pkgimage : Bool
  mtime : Nat
  deriving Repr, DecidableEq
def candidateBefore (a b : CacheCandidate) : Bool :=
  if a.pkgimage != b.pkgimage then a.pkgimage && !b.pkgimage else a.mtime > b.mtime
def insertCandidate (x : CacheCandidate) : List CacheCandidate → List CacheCandidate
  | [] => [x]
  | y :: ys => if candidateBefore x y then x :: y :: ys else y :: insertCandidate x ys
def method1401 : List CacheCandidate → List CacheCandidate
  | [] => []
  | x :: xs => insertCandidate x (method1401 xs)
def Property1401 : Prop := ∀ candidates,
  (method1401 candidates).length = candidates.length
theorem property1401 : Property1401 := by
  intro candidates
  induction candidates with
  | nil => rfl
  | cons x xs ih =>
      simp only [method1401]
      have insertLength : ∀ ys, (insertCandidate x ys).length = ys.length + 1 := by
        intro ys; induction ys with
        | nil => rfl
        | cons y ys ih' => simp [insertCandidate]; split <;> simp_all
      simp [insertLength, ih]

def method1403 (candidate : CacheCandidate) : Bool × Nat := (candidate.pkgimage, candidate.mtime)
def Property1403 : Prop := ∀ candidate, (method1403 candidate).1 = candidate.pkgimage
theorem property1403 : Property1403 := by simp [Property1403, method1403]

def method1404 (a b : CacheCandidate) : Bool := candidateBefore a b
def Property1404 : Prop := ∀ a b,
  a.pkgimage = true → b.pkgimage = false → method1404 a b = true
theorem property1404 : Property1404 := by
  intro a b ha hb
  simp [method1404, candidateBefore, ha, hb]

def method1423 (hasDepot inWritable inBundled touchSucceeds : Bool) : Bool :=
  hasDepot && inWritable && !inBundled && touchSucceeds
def Property1423 : Prop := ∀ depot writable bundled touched,
  method1423 depot writable bundled touched = true →
  depot = true ∧ writable = true ∧ bundled = false
theorem property1423 : Property1423 := by simp [Property1423, method1423]

def method1435 (sort : List CacheCandidate → List CacheCandidate)
    (candidates : List CacheCandidate) := sort candidates
def Property1435 : Prop := ∀ sort candidates,
  (sort candidates).length = candidates.length →
  (method1435 sort candidates).length = candidates.length
theorem property1435 : Property1435 := by simp [Property1435, method1435]

def method1440 (isStdlib : Bool) (depots : List String) : List String :=
  if isStdlib then depots.reverse else depots
def Property1440 : Prop := ∀ isStdlib depots,
  (method1440 isStdlib depots).length = depots.length
theorem property1440 : Property1440 := by
  intro isStdlib depots
  cases isStdlib <;> simp [method1440]

def method1447 (perDepot : List (List String)) : List String := perDepot.flatten
def Property1447 : Prop := ∀ perDepot path,
  path ∈ method1447 perDepot ↔ ∃ paths ∈ perDepot, path ∈ paths
theorem property1447 : Property1447 := by simp [Property1447, method1447]

def method1452 (paths : List (List String)) : List String := paths.flatten
def Property1452 : Prop := ∀ paths,
  (method1452 paths).length = (paths.map List.length).sum
theorem property1452 : Property1452 := by simp [Property1452, method1452, List.length_flatten]

def chopSuffix (suffix : String) (path : String) : String :=
  if path.endsWith suffix then path.dropRight suffix.length else path
def method1463 (extension cachefile : String) : String := chopSuffix ".ji" cachefile ++ "." ++ extension
def Property1463 : Prop := ∀ extension cachefile,
  ∃ pre, method1463 extension cachefile = pre ++ "." ++ extension
theorem property1463 : Property1463 := by
  intro extension cachefile
  exact ⟨chopSuffix ".ji" cachefile, rfl⟩

def method1464 (extension cachefile : String) : String := chopSuffix ("." ++ extension) cachefile ++ ".ji"
def Property1464 : Prop := ∀ extension cachefile,
  ∃ pre, method1464 extension cachefile = pre ++ ".ji"
theorem property1464 : Property1464 := by
  intro extension cachefile
  exact ⟨chopSuffix ("." ++ extension) cachefile, rfl⟩

end JuliaLean.Loading.Coverage.Manifest
