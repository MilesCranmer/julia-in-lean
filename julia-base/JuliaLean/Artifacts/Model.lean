import JuliaLean.Paths.Model
import JuliaLean.Platforms.Match

/-!
# Artifacts pure-logic model

The pure parts of `stdlib/Artifacts/src/Artifacts.jl` at Julia `bbfa0ce4150`.
Strings are character lists, TOML dictionaries are association lists with unique
keys, and hashes and UUIDs are abstract natural numbers. Platform matching is the
existing `JuliaLean.Platforms` model of `base/binaryplatforms.jl`.
-/

namespace JuliaLean.Artifacts

open JuliaLean

abbrev Str := List Char
abbrev Hash := Nat
abbrev Uuid := Nat
abbrev Name := Str
abbrev Dict (α : Type) := Platforms.Dict α

def dget {α : Type} (d : Dict α) (k : Str) : Option α := Platforms.dget d k
def dset {α : Type} (d : Dict α) (k : Str) (v : α) : Dict α := Platforms.dset d k v

def ddelete {α : Type} (d : Dict α) (k : Str) : Dict α := d.filter (·.1 != k)

/-! ## Artifact slash lookup, `Artifacts.jl:541-662` -/

/-- Both delimiters matched by `r"(/|\\)"`; `Artifacts.jl:636-637`. -/
def isSlash (c : Char) : Bool := c == '/' || c == '\\'

/-- `split(name, r"(/|\\)")`, including empty components; `Artifacts.jl:637`. -/
def splitSlashes : Str → List Str
  | [] => [[]]
  | c :: cs =>
      let parts := splitSlashes cs
      if isSlash c then [] :: parts
      else match parts with
        | [] => [[c]]
        | p :: ps => (c :: p) :: ps

/-- POSIX `joinpath(parts...)` for the nonempty tail; `Artifacts.jl:641`. -/
def joinParts : List Str → Str
  | [] => []
  | p :: ps => ps.foldl Paths.joinStep p

/-- `split_artifact_slash`; `Artifacts.jl:636-642`. -/
def splitArtifactSlash (name : Str) : Str × Str :=
  match splitSlashes name with
  | [] => ([], [])
  | [artifact] => (artifact, [])
  | artifact :: tail => (artifact, joinParts tail)

/-- `jointail`; `Artifacts.jl:544-549`. -/
def jointail (dir tail : Str) : Str := if tail.isEmpty then dir else Paths.joinStep dir tail

/-- The current lookup performs no validation before returning the split; `Artifacts.jl:653-662`. -/
def artifactSlashLookup (name : Str) : Jl (Str × Str) := pure (splitArtifactSlash name)

def dotdot : Str := ['.', '.']

/-- Inputs that cannot denote a nonempty artifact name followed by ordinary child components. -/
def unsafeSlashName (name : Str) : Bool :=
  let parts := splitSlashes name
  (parts.headD []).isEmpty || (parts.drop 1).any (fun p => p.isEmpty || p == dotdot)

/-! ## Artifact metadata, `Artifacts.jl:274-476` -/

/-- The string-valued fields consumed by `unpack_platform`, plus artifact fields used later. -/
structure Meta where
  stringFields : Dict Str
  hash : Option Hash
  download : Bool
  lazy : Bool
  deriving DecidableEq, Repr

def platformField (k : Str) : Bool :=
  k != s% "os" && k != s% "arch" && k != s% "git-tree-sha1"

/-- String-valued mappings passed as platform tags after deleting the three known keys;
`Artifacts.jl:292-303`. -/
def extraPlatformTags (m : Meta) : List (Str × Platforms.TagVal) :=
  (m.stringFields.filter (platformField ·.1)).map fun e => (e.1, .str e.2)

/-- `unpack_platform`; missing `os` or `arch` logs an error and returns `nothing`;
`Artifacts.jl:280-304`. Constructor exceptions remain exceptions. -/
def unpackPlatform (lc : Char → Char) (m : Meta) : Jl (Option Platforms.Platform) := do
  let some os := dget m.stringFields (s% "os") | return none
  let some arch := dget m.stringFields (s% "arch") | return none
  return some (← Platforms.platform lc arch os (extraPlatformTags m) false)

/-- One iteration of `pack_platform!`; `Artifacts.jl:306-312`. -/
def packTag (m : Meta) (e : Str × Str) : Meta :=
  { m with stringFields := dset m.stringFields e.1 e.2 }

/-- `pack_platform!`: all non-`nothing` platform tags are strings in the platform model. -/
def packPlatform (m : Meta) (p : Platforms.Platform) : Meta := p.tags.foldl packTag m

/-- The `git-tree-sha1` check at `Artifacts.jl:422-429`. -/
def requireHash (m : Option Meta) : Option Meta :=
  match m with
  | some m => if m.hash.isSome then some m else none
  | none => none

/-- The platform-selection branch of `artifact_meta`; `Artifacts.jl:408-415`.
The entries have already passed through `unpack_platform`. -/
def artifactMetaPlatform (usem : Platforms.UserSem)
    (order : Platforms.Platform → List Platforms.Str)
    (entries : List (Platforms.Platform × Str)) (host : Platforms.Platform) : Jl (Option Str) :=
  Platforms.selectPlatform usem order entries host

/-- A resolved artifact name and the result of `artifact_meta`. -/
abbrev Resolved := Name × Option Meta

def downloadable (includeLazy : Bool) (m : Meta) : Bool :=
  m.download && (!m.lazy || includeLazy)

/-- The filtering loop of `select_downloadable_artifacts`; `Artifacts.jl:460-475`. -/
def selectDownloadable (includeLazy : Bool) : List Resolved → List (Name × Meta)
  | [] => []
  | (_name, none) :: rest => selectDownloadable includeLazy rest
  | (name, some m) :: rest =>
      if downloadable includeLazy m then (name, m) :: selectDownloadable includeLazy rest
      else selectDownloadable includeLazy rest

/-! ## Overrides, `Artifacts.jl:74-215,315-375` -/

inductive OverrideTarget where
  | path (id : Nat)
  | hash (hash : Hash)
  deriving DecidableEq, Repr

inductive RawMapping where
  | target (value : OverrideTarget)
  | clear
  | invalid
  deriving DecidableEq, Repr

abbrev HashOverrides := List (Hash × OverrideTarget)
abbrev NameOverrides := Dict OverrideTarget
abbrev UuidOverrides := List (Uuid × NameOverrides)

def nget {α : Type} (d : List (Nat × α)) (k : Nat) : Option α :=
  (d.find? (·.1 == k)).map (·.2)

def nset {α : Type} (d : List (Nat × α)) (k : Nat) (v : α) : List (Nat × α) :=
  if (nget d k).isSome then d.map (fun e => if e.1 == k then (k, v) else e) else d ++ [(k, v)]

def ndelete {α : Type} (d : List (Nat × α)) (k : Nat) : List (Nat × α) := d.filter (·.1 != k)

structure OverrideState where
  uuid : UuidOverrides := []
  hash : HashOverrides := []
  errors : Nat := 0
  deriving DecidableEq, Repr

/-- Direct hash entry handling, including empty-string un-override and malformed-entry log;
`Artifacts.jl:133-155`. -/
def applyHashEntry (state : OverrideState) (hash : Hash) : RawMapping → OverrideState
  | .target value => { state with hash := nset state.hash hash value }
  | .clear => { state with hash := ndelete state.hash hash }
  | .invalid => { state with errors := state.errors + 1 }

def applyHashFile (state : OverrideState) (file : List (Hash × RawMapping)) : OverrideState :=
  file.foldl (fun s e => applyHashEntry s e.1 e.2) state

/-- Depots arrive in `DEPOT_PATH` priority order. Julia iterates them in reverse so higher
priority files apply last; `Artifacts.jl:127`. -/
def loadHashDepots (depots : List (List (Hash × RawMapping))) : OverrideState :=
  depots.reverse.foldl applyHashFile {}

/-- UUID/name entry handling, including empty-string un-override; `Artifacts.jl:164-177`. -/
def applyNameEntry (state : OverrideState) (uuid : Uuid) (name : Name) : RawMapping → OverrideState
  | .invalid => { state with errors := state.errors + 1 }
  | mapping =>
      let names := (nget state.uuid uuid).getD []
      let names := match mapping with
        | .target value => dset names name value
        | .clear => ddelete names name
        | .invalid => names
      { state with uuid := nset state.uuid uuid names }

abbrev ArtifactHashes := Dict (List Hash)

def installNameHashes (target : OverrideTarget) (state : OverrideState) : List Hash → OverrideState
  | [] => state
  | hash :: rest => installNameHashes target { state with hash := nset state.hash hash target } rest

/-- UUID/name overrides become hash overrides and therefore overwrite any direct mapping for
the bound hashes; `Artifacts.jl:341-371`. -/
def processNameOverrides (artifacts : ArtifactHashes) (pkg : Uuid) (state : OverrideState) : OverrideState :=
  match nget state.uuid pkg with
  | none => state
  | some names => artifacts.foldl (fun s e =>
      match dget names e.1 with
      | none => s
      | some target => installNameHashes target s e.2) state

/-- The file overload of `artifact_meta` processes `pkg_uuid`; `Artifacts.jl:389-399`. -/
def artifactMetaState (artifacts : ArtifactHashes) (pkg : Option Uuid) (state : OverrideState) : OverrideState :=
  match pkg with
  | none => state
  | some uuid => processNameOverrides artifacts uuid state

/-- `artifact_hash` accepts `pkg_uuid` but omits it from the `artifact_meta` call;
`Artifacts.jl:445-453`. The returned component is the selected bound hash. -/
def artifactHashState (artifacts : ArtifactHashes) (name : Name) (_pkg : Option Uuid)
    (state : OverrideState) : Option Hash × OverrideState :=
  ((dget artifacts name).bind List.head?, state)

/-- The dictionary overload accepts but does not use `pkg_uuid`; `Artifacts.jl:456-475`. -/
def selectDownloadableState (_artifacts : ArtifactHashes) (_pkg : Option Uuid)
    (state : OverrideState) : OverrideState := state

/-! ## Recursive hash-to-hash resolution and artifact paths, `Artifacts.jl:195-271` -/

inductive ResolvedTarget where
  | path (id : Nat)
  | hash (hash : Hash)
  deriving DecidableEq, Repr

/-- A fuelled view of `query_override`/`artifact_path` recursion. `none` means the Julia call
has not terminated within the given number of redirects. -/
def resolveOverride : Nat → HashOverrides → Hash → Option ResolvedTarget
  | 0, _, _ => none
  | fuel + 1, overrides, hash =>
      match nget overrides hash with
      | none => some (.hash hash)
      | some (.path id) => some (.path id)
      | some (.hash next) => resolveOverride fuel overrides next

inductive ArtifactLocation where
  | override (id : Nat)
  | depot (depot : Nat) (hash : Hash)
  deriving DecidableEq, Repr

/-- `artifact_paths`, after `query_override` has resolved; `Artifacts.jl:224-234`. -/
def artifactPaths (fuel : Nat) (overrides : HashOverrides) (depots : List Nat)
    (hash : Hash) : Option (List ArtifactLocation) :=
  match resolveOverride fuel overrides hash with
  | none => none
  | some (.path id) => some [.override id]
  | some (.hash finalHash) => some (depots.map (fun depot => .depot depot finalHash))

/-- First existing path, or the first candidate if none exists; `Artifacts.jl:245-257`. -/
def artifactPath (isDir : ArtifactLocation → Bool) : List ArtifactLocation → Option ArtifactLocation
  | [] => none
  | first :: rest => (first :: rest).find? isDir |>.orElse (fun _ => some first)

/-- `artifact_exists`; `Artifacts.jl:270-271`. -/
def artifactExists (isDir : ArtifactLocation → Bool) (paths : List ArtifactLocation) : Bool :=
  paths.any isDir

end JuliaLean.Artifacts
