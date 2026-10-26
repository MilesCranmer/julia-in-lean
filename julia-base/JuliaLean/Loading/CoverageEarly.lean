import JuliaLean.Loading.CoverageCommon

namespace JuliaLean.Loading.Coverage.Early

open JuliaLean.Loading.Coverage

/-! ## Filesystem probes, lines 10 and 86-111 -/

/-- Linux `isfile_casesensitive`, line 10. -/
def method10 (isAccessibleFile : String → Result Bool) (path : String) : Result Bool :=
  isAccessibleFile path

def Property10 : Prop := ∀ isAccessibleFile path value,
  method10 isAccessibleFile path = .ok value ↔ isAccessibleFile path = .ok value

theorem property10 : Property10 := by simp [Property10, method10]

/-- Shared body of the three accessibility probes, lines 86-111. -/
def accessibilityProbe (probe : String → Result Bool) (path : String) : Result Bool :=
  catchIo (probe path)

def method86 := accessibilityProbe
def method95 := accessibilityProbe
def method104 := accessibilityProbe

def AccessProperty (method : (String → Result Bool) → String → Result Bool) : Prop :=
  (∀ probe path, probe path = .error .io → method probe path = .ok false) ∧
  (∀ probe path error, error ≠ .io → probe path = .error error →
    method probe path = .error error) ∧
  (∀ probe path value, probe path = .ok value → method probe path = .ok value)

def Property86 : Prop := AccessProperty method86
def Property95 : Prop := AccessProperty method95
def Property104 : Prop := AccessProperty method104

private theorem accessProperty : AccessProperty accessibilityProbe := by
  constructor
  · intro probe path h; simp [accessibilityProbe, catchIo, h]
  constructor
  · intro probe path error hne h
    cases error <;> simp_all [accessibilityProbe, catchIo]
  · intro probe path value h; simp [accessibilityProbe, catchIo, h]

theorem property86 : Property86 := accessProperty
theorem property95 : Property95 := accessProperty
theorem property104 : Property104 := accessProperty

/-! ## SHA value methods generated at lines 119-143 -/

structure Digest where
  width : Nat
  bytes : List Nat
  deriving Repr, DecidableEq

def validByte (byte : Nat) : Bool := byte < 256

/-- Generated `SHA1`/`SHA256` vector constructor, lines 119-123. -/
def method119 (width : Nat) (bytes : List Nat) : Result Digest :=
  if bytes.length = width then .ok ⟨width, bytes⟩ else .error .argument

def Property119 : Prop := ∀ width bytes,
  (∃ digest, method119 width bytes = .ok digest) ↔ bytes.length = width

theorem property119 : Property119 := by
  intro width bytes
  by_cases h : bytes.length = width
  · simp [method119, h]
  · simp [method119, h]

def hexNibble (char : Nat) : Option Nat :=
  if 48 ≤ char && char ≤ 57 then some (char - 48)
  else if 65 ≤ char && char ≤ 70 then some (char - 55)
  else if 97 ≤ char && char ≤ 102 then some (char - 87)
  else none

def hexPairs : List Nat → Option (List Nat)
  | [] => some []
  | high :: low :: rest => do
      let hi ← hexNibble high
      let lo ← hexNibble low
      return (16 * hi + lo) :: (← hexPairs rest)
  | [_] => none

/-- Generated string constructor, line 124: `hex2bytes` before the vector constructor. -/
def method124 (width : Nat) (text : List Nat) : Result Digest :=
  match hexPairs text with
  | none => .error .argument
  | some bytes => method119 width bytes

def Property124 : Prop := ∀ width text digest,
  method124 width text = .ok digest →
    digest.width = width ∧ digest.bytes.length = width

theorem property124 : Property124 := by
  intro width text digest h
  simp only [method124] at h
  cases hp : hexPairs text with
  | none => simp [hp] at h
  | some bytes =>
      by_cases hw : bytes.length = width
      · simp [hp, method119, hw] at h
        cases h
        simp [hw]
      · simp [hp, method119, hw] at h

/-- Generated `parse`, line 125. -/
def method125 (width : Nat) (text : List Nat) : Result Digest := method124 width text

def Property125 : Prop := ∀ width text digest,
  method125 width text = .ok digest → digest.bytes.length = width

theorem property125 : Property125 := by
  intro width text digest h
  exact (property124 width text digest h).2

/-- Generated `tryparse`, lines 126-135. -/
def method126 (parseDigest : List Nat → Result Digest) (text : List Nat) : Result (Option Digest) :=
  match parseDigest text with
  | .ok digest => .ok (some digest)
  | .error .argument => .ok none
  | .error error => .error error

def Property126 : Prop :=
  (∀ parseDigest text, parseDigest text = .error .argument →
    method126 parseDigest text = .ok none) ∧
  (∀ parseDigest text error, error ≠ .argument → parseDigest text = .error error →
    method126 parseDigest text = .error error) ∧
  (∀ parseDigest text digest, parseDigest text = .ok digest →
    method126 parseDigest text = .ok (some digest))

theorem property126 : Property126 := by
  constructor
  · intro parseDigest text h; simp [method126, h]
  constructor
  · intro parseDigest text error hne h
    cases error <;> simp_all [method126]
  · intro parseDigest text digest h; simp [method126, h]

def byteHex (byte : Nat) : Nat × Nat := ((byte / 16) % 16, byte % 16)
def bytesHex : List Nat → List Nat
  | [] => []
  | byte :: rest =>
      let pair := byteHex byte
      pair.1 :: pair.2 :: bytesHex rest

/-- Generated `string`, line 137. -/
def method137 (digest : Digest) : List Nat := bytesHex digest.bytes

def Property137 : Prop := ∀ digest,
  (method137 digest).length = 2 * digest.bytes.length

theorem property137 : Property137 := by
  unfold Property137
  intro digest
  have bytesHex_length : ∀ bytes : List Nat, (bytesHex bytes).length = 2 * bytes.length := by
    intro bytes
    induction bytes with
    | nil => simp [bytesHex]
    | cons byte rest ih => simp [bytesHex, ih, Nat.mul_succ]
  exact bytesHex_length digest.bytes

/-- Generated `print`, line 138, represented by bytes appended to the stream. -/
def method138 (stream : List Nat) (digest : Digest) : List Nat :=
  stream ++ bytesHex digest.bytes

def Property138 : Prop := ∀ stream digest,
  List.IsPrefix stream (method138 stream digest)

theorem property138 : Property138 := by
  intro stream digest
  simp [method138]

/-- Generated `show`, line 139. -/
def method139 (tag : List Nat) (stream : List Nat) (digest : Digest) : List Nat :=
  stream ++ tag ++ [40, 34] ++ bytesHex digest.bytes ++ [34, 41]

def Property139 : Prop := ∀ tag stream digest,
  List.IsPrefix stream (method139 tag stream digest) ∧
  List.IsSuffix [34, 41] (method139 tag stream digest)

theorem property139 : Property139 := by
  intro tag stream digest
  constructor
  · exact ⟨tag ++ [40, 34] ++ bytesHex digest.bytes ++ [34, 41], by
      simp [method139, List.append_assoc]⟩
  · exact ⟨stream ++ tag ++ [40, 34] ++ bytesHex digest.bytes, by
      simp [method139, List.append_assoc]⟩

/-- Generated lexicographic `isless`, line 141. -/
def method141 (a b : Digest) : Bool := a.bytes < b.bytes

def Property141 : Prop := ∀ digest, method141 digest digest = false

theorem property141 : Property141 := by
  intro digest
  simp [method141]

/-- Generated `hash`, line 142. -/
def method142 (hashPair : Nat → (Nat × List Nat) → Nat)
    (typeTag seed : Nat) (digest : Digest) : Nat :=
  hashPair seed (typeTag, digest.bytes)

def Property142 : Prop := ∀ hashPair typeTag seed a b,
  a = b → method142 hashPair typeTag seed a = method142 hashPair typeTag seed b

theorem property142 : Property142 := by
  intro hashPair typeTag seed a b h
  subst b
  rfl

/-- Generated equality, line 143. -/
def method143 (a b : Digest) : Bool := a.bytes == b.bytes

def Property143 : Prop := ∀ a b, method143 a b = true ↔ a.bytes = b.bytes

theorem property143 : Property143 := by
  intro a b
  simp [method143]

/-! ## UUIDs and slugs, lines 150-209 -/

structure FakeUuid where
  payload : Nat
  version : Nat
  variant : Nat
  deriving Repr, DecidableEq

def hashWords : Nat → (Nat → String → Nat) → String → Nat → Nat
  | 0, _, _, value => value
  | fuel + 1, hash, key, value =>
      hashWords fuel hash key ((value * 2 ^ 64 + hash value key) % 2 ^ 128)

/-- The four/eight-word hash loop and version/variant assignment in `uuid5`, lines 150-160. -/
def method150 (wordBytes : Nat) (hashNamespace : Nat) (hash : Nat → String → Nat)
    (key : String) : FakeUuid :=
  let words := 16 / wordBytes
  ⟨hashWords words hash key hashNamespace, 5, 2⟩

def Property150 : Prop := ∀ wordBytes hashNamespace hash key,
  (method150 wordBytes hashNamespace hash key).version = 5 ∧
  (method150 wordBytes hashNamespace hash key).variant = 2

theorem property150 : Property150 := by
  unfold Property150
  intros
  exact ⟨rfl, rfl⟩

structure DummyCache where
  values : List (String × FakeUuid)
  deriving Repr, DecidableEq

/-- `dummy_uuid`, lines 164-183. The realpath outcome and cache are explicit. -/
def method164 (uuid5 : String → FakeUuid) (projectFile : String)
    (realpath : Result String) (cache : Option DummyCache) : FakeUuid × Option DummyCache :=
  match cache.bind (fun c => lookupAssoc projectFile c.values) with
  | some uuid => (uuid, cache)
  | none =>
      let projectPath := match realpath with
        | .ok path => path
        | .error .io => projectFile
        | .error _ => projectFile
      let uuid := uuid5 projectPath
      let cache' := cache.map fun c => ⟨updateAssoc projectFile uuid c.values⟩
      (uuid, cache')

def Property164 : Prop := ∀ uuid5 projectFile realpath cache cached,
  cache.bind (fun c => lookupAssoc projectFile c.values) = some cached →
  method164 uuid5 projectFile realpath cache = (cached, cache)

theorem property164 : Property164 := by
  intro uuid5 projectFile realpath cache cached h
  simp [method164, h]

def slugChars : Nat := 62

/-- `slug`, lines 189-198, returning character indices in write order. -/
def slugLoop : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, value => value % slugChars :: slugLoop fuel (value / slugChars)

def method189 (value : Nat) (p : Int) : List Nat :=
  if p ≤ 0 then [] else slugLoop p.toNat value

def Property189 : Prop := ∀ value p,
  (method189 value p).length = (if p ≤ 0 then 0 else p.toNat) ∧
  ∀ digit ∈ method189 value p, digit < slugChars

private theorem slugLoop_spec (fuel value : Nat) :
    (slugLoop fuel value).length = fuel ∧
    ∀ digit ∈ slugLoop fuel value, digit < slugChars := by
  induction fuel generalizing value with
  | zero => simp [slugLoop]
  | succ fuel ih =>
      simp only [slugLoop]
      constructor
      · simp [ih]
      · intro digit h
        simp at h
        rcases h with h | h
        · subst digit; exact Nat.mod_lt _ (by decide)
        · exact (ih (value / slugChars)).2 digit h

theorem property189 : Property189 := by
  unfold Property189
  intro value p
  by_cases hp : p ≤ 0
  · simp [method189, hp]
  · simpa [method189, hp] using slugLoop_spec p.toNat value

/-- `package_slug`, lines 200-203. -/
def method200 (crc32 : Nat → Nat) (uuid : Nat) (p : Int) : List Nat :=
  method189 (crc32 uuid) p

def Property200 : Prop := ∀ crc32 uuid p,
  (method200 crc32 uuid p).length = (if p ≤ 0 then 0 else p.toNat)

theorem property200 : Property200 := by
  intro crc32 uuid p
  exact (property189 (crc32 uuid) p).1

/-- `version_slug`, lines 205-209. -/
def method205 (crcUuid : Nat → Nat) (crcBytes : List Nat → Nat → Nat)
    (uuid : Nat) (sha : List Nat) (p : Int) : List Nat :=
  method189 (crcBytes sha (crcUuid uuid)) p

def Property205 : Prop := ∀ crcUuid crcBytes uuid sha p,
  (method205 crcUuid crcBytes uuid sha p).length = (if p ≤ 0 then 0 else p.toNat)

theorem property205 : Property205 := by
  intro crcUuid crcBytes uuid sha p
  exact (property189 (crcBytes sha (crcUuid uuid)) p).1

/-! ## TOML and loading caches, lines 220-334 -/

structure FileStat where
  inode : Nat
  mtime : Nat
  size : Nat
  deriving Repr, DecidableEq

structure CachedToml (α : Type) where
  path : String
  inode : Nat
  mtime : Nat
  size : Nat
  hash : Nat
  value : α
  deriving Repr, DecidableEq

/-- `CachedTOMLDict`, lines 220-234. -/
def method220 (crc : List Nat → Nat) (parse : String → List Nat → Result α)
    (path : String) (stat : FileStat) (content : List Nat) : Result (CachedToml α) :=
  match parse path content with
  | .error error => .error error
  | .ok value => .ok ⟨path, stat.inode, stat.mtime, stat.size, crc content, value⟩

def Property220 : Prop := ∀ (α : Type) (crc : List Nat → Nat)
    (parse : String → List Nat → Result α) path stat content (cached : CachedToml α),
  method220 crc parse path stat content = .ok cached →
  cached.path = path ∧ cached.inode = stat.inode ∧ cached.mtime = stat.mtime ∧
    cached.size = stat.size ∧ cached.hash = crc content

theorem property220 : Property220 := by
  unfold Property220
  intro α crc parse path stat content cached h
  cases hp : parse path content with
  | error error =>
      simp [method220, hp] at h
  | ok value =>
      simp [method220, hp] at h
      cases h
      simp

/-- `get_updated_dict`, lines 236-254. -/
def method236 (crc : List Nat → Nat) (parse : String → List Nat → Result α)
    (cached : CachedToml α) (stat : FileStat) (content : List Nat) : Result (CachedToml α) :=
  if stat.inode != cached.inode || stat.mtime != cached.mtime || cached.size != stat.size then
    let newHash := crc content
    if newHash != cached.hash then
      match parse cached.path content with
      | .error error => .error error
      | .ok value => .ok ⟨cached.path, stat.inode, stat.mtime, stat.size, newHash, value⟩
    else .ok cached
  else .ok cached

def Property236 : Prop := ∀ (α : Type) (crc : List Nat → Nat)
    (parse : String → List Nat → Result α) (cached : CachedToml α) stat content
    (updated : CachedToml α),
  method236 crc parse cached stat content = .ok updated →
  updated.path = cached.path ∧
  (updated = cached ∨
    (updated.inode = stat.inode ∧ updated.mtime = stat.mtime ∧
      updated.size = stat.size ∧ updated.hash = crc content))

theorem property236 : Property236 := by
  unfold Property236
  intro α crc parse cached stat content updated h
  simp only [method236] at h
  split at h
  · split at h
    · cases hp : parse cached.path content with
      | error error => simp [hp] at h
      | ok value =>
          simp [hp] at h
          cases h
          simp
    · simp_all
  · simp_all

structure LoadingCacheModel where
  loadPath : List String
  dummyUuidCount : Nat := 0
  envProjectCount : Nat := 0
  manifestCount : Nat := 0
  parsedCount : Nat := 0
  identifiedWhereCount : Nat := 0
  identifiedCount : Nat := 0
  locatedCount : Nat := 0
  deriving Repr, DecidableEq

/-- `LoadingCache()`, lines 278-287. -/
def method278 (loadPath : List String) : LoadingCacheModel := { loadPath := loadPath }

def Property278 : Prop := ∀ loadPath,
  (method278 loadPath).loadPath = loadPath ∧
  (method278 loadPath).dummyUuidCount = 0 ∧
  (method278 loadPath).locatedCount = 0

theorem property278 : Property278 := by simp [Property278, method278]

structure TomlCacheModel (α : Type) where
  parser : Nat
  values : List (String × CachedToml α)
  deriving Repr, DecidableEq

/-- `TOMLCache(p)`, line 294. -/
def method294 (parser : Nat) : TomlCacheModel α := ⟨parser, []⟩

def Property294 : Prop := ∀ (α : Type) parser,
  (method294 (α := α) parser).values = []

theorem property294 : Property294 := by simp [Property294, method294]

/-- Converting-dictionary `TOMLCache` constructor, line 295. -/
def method295 (convert : List (String × α) → List (String × CachedToml α))
    (parser : Nat) (values : List (String × α)) : TomlCacheModel α :=
  ⟨parser, convert values⟩

def Property295 : Prop := ∀ (α : Type) convert parser values,
  (method295 (α := α) convert parser values).parser = parser ∧
  (method295 (α := α) convert parser values).values = convert values

theorem property295 : Property295 := by simp [Property295, method295]

/-- One-argument `parsed_toml`, line 299. -/
def method299 (globalCache : α) (globalLock : β)
    (parse : String → α → β → γ) (projectFile : String) : γ :=
  parse projectFile globalCache globalLock

def Property299 : Prop := ∀ (α β γ : Type) globalCache globalLock parse projectFile,
  method299 (α := α) (β := β) (γ := γ) globalCache globalLock parse projectFile =
    parse projectFile globalCache globalLock

theorem property299 : Property299 := by simp [Property299, method299]

structure ParsedCacheState (α : Type) where
  values : List (String × α)
  requireParsed : List String
  deriving Repr, DecidableEq

def finishParsed [BEq α] (projectFile : String) (hasLoadingCache : Bool)
    (state : ParsedCacheState α) : Result α → Result (α × ParsedCacheState α)
  | .error error => .error error
  | .ok value =>
      let values := updateAssoc projectFile value state.values
      let parsed := if hasLoadingCache then projectFile :: state.requireParsed else state.requireParsed
      .ok (value, ⟨values, parsed⟩)

def parsedResult [BEq α] (create update : String → Result α) (projectFile : String)
    (hasLoadingCache : Bool) (state : ParsedCacheState α) : Result α :=
  match lookupAssoc projectFile state.values with
  | none => create projectFile
  | some cached =>
      if hasLoadingCache && projectFile ∈ state.requireParsed then .ok cached
      else update projectFile

/-- Locked cache lookup/update in `parsed_toml`, lines 300-322. -/
def method300 [BEq α] (create update : String → Result α) (projectFile : String)
    (hasLoadingCache : Bool) (state : ParsedCacheState α) : Result (α × ParsedCacheState α) :=
  finishParsed projectFile hasLoadingCache state
    (parsedResult create update projectFile hasLoadingCache state)

def Property300 : Prop := ∀ (α : Type) [BEq α]
    (create update : String → Result α) projectFile hasCache (state : ParsedCacheState α)
    (value : α) (next : ParsedCacheState α),
  method300 create update projectFile hasCache state = .ok (value, next) →
  next.values.head? = some (projectFile, value)

theorem property300 : Property300 := by
  unfold Property300
  intro α inst create update projectFile hasCache state value next h
  cases hr : parsedResult create update projectFile hasCache state with
  | error error => simp [method300, finishParsed, hr] at h
  | ok found =>
      simp [method300, finishParsed, hr, updateAssoc] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

/-- `find_package`, lines 327-334. -/
def method327 (identify : α → Option (β × γ)) (locate : β → γ → Option String)
    (arg : α) : Option String :=
  match identify arg with
  | none => none
  | some (pkg, env) => locate pkg env

def Property327 : Prop :=
  (∀ (α β γ : Type) (identify : α → Option (β × γ))
    (locate : β → γ → Option String) (arg : α), identify arg = none →
    method327 (β := β) (γ := γ) identify locate arg = none) ∧
  (∀ (α β γ : Type) (identify : α → Option (β × γ))
    (locate : β → γ → Option String) (arg : α) (pkg : β) (env : γ) path,
    identify arg = some (pkg, env) → locate pkg env = some path →
    method327 identify locate arg = some path)

theorem property327 : Property327 := by
  constructor <;> intros <;> simp_all [method327]

/-- `is_stdlib`, lines 337-349. -/
def method337 [BEq α] (names : List String) (pkgName : String) (pkgUuid : α)
    (projectFile : Option String) (parsedUuid : Option α) : Bool :=
  if pkgName ∉ names then false else
  match projectFile, parsedUuid with
  | some _, some uuid => uuid == pkgUuid
  | _, _ => false

def Property337 : Prop := ∀ (α : Type) [BEq α] [LawfulBEq α] names pkgName (pkgUuid : α)
    project (parsed : Option α),
  method337 names pkgName pkgUuid project parsed = true →
  pkgName ∈ names ∧ project.isSome ∧ parsed = some pkgUuid

theorem property337 : Property337 := by
  unfold Property337
  intro α inst lawful names pkgName pkgUuid project parsed h
  simp only [method337] at h
  split at h <;> simp_all
  cases project <;> cases parsed <;> simp_all

/-! ## Identification and location wrappers, lines 358-765 -/

structure PackageId where
  uuid : Option Nat
  name : String
  deriving Repr, DecidableEq

def method358 (pkgId : α → PackageId)
    (identify : PackageId → String → Option (PackageId × Option String))
    (context : α) (name : String) : Option (PackageId × Option String) :=
  identify (pkgId context) name

def Property358 : Prop := ∀ (α : Type) (pkgId : α → PackageId)
    (identify : PackageId → String → Option (PackageId × Option String))
    (context : α) name result,
  method358 pkgId identify context name = result → identify (pkgId context) name = result

theorem property358 : Property358 := by simp [Property358, method358]

inductive EnvAnswer where
  | absent
  | blocked
  | found (pkg : PackageId) (env : String)
  deriving Repr, DecidableEq

def scanWhere : List EnvAnswer → Option (PackageId × Option String)
  | [] => none
  | .absent :: rest => scanWhere rest
  | .blocked :: _ => none
  | .found pkg env :: _ => some (pkg, some env)

/-- Contextual `identify_package_env`, lines 359-404. -/
def method359 (context : PackageId) (name : String) (cached : Option (Option (PackageId × Option String)))
    (answers : List EnvAnswer) (stdlibFallback : Option (PackageId × Option String))
    (isStdlib : Bool) : Option (PackageId × Option String) :=
  if context.name == name then some (context, none)
  else if context.uuid.isNone then
    match answers.find? (· != .absent) with
    | some (.found pkg env) => some (pkg, some env)
    | _ => none
  else match cached with
    | some answer => answer
    | none =>
        match scanWhere answers with
        | some answer => some answer
        | none => if isStdlib then stdlibFallback else none

def Property359 : Prop := ∀ context name cached answers fallback isStdlib,
  (context.name = name → method359 context name cached answers fallback isStdlib = some (context, none)) ∧
  (context.name ≠ name → context.uuid.isSome → cached = some none →
    method359 context name cached answers fallback isStdlib = none)

theorem property359 : Property359 := by
  unfold Property359
  intro context name cached answers fallback isStdlib
  constructor
  · intro h; simp [method359, h]
  · intro hname huuid hcached
    simp [method359, hname, Option.isSome_iff_ne_none.mp huuid, hcached]

/-- Top-level `identify_package_env`, lines 405-430. -/
def method405 (cached : Option (Option (PackageId × String)))
    (answers : List (Option (PackageId × String))) : Option (PackageId × String) :=
  match cached with | some answer => answer | none => firstSome answers

def Property405 : Prop := ∀ cached answers answer,
  cached = some answer → method405 cached answers = answer

theorem property405 : Property405 := by intro; simp_all [method405]

def method431 (method405 : Option PackageId → String → α) (name : String) : α :=
  method405 none name

def Property431 : Prop := ∀ (α : Type) identify name,
  method431 (α := α) identify name = identify none name

theorem property431 : Property431 := by simp [Property431, method431]

/-- Stdlib-project fallback, lines 433-447. -/
def method433 (projectFile : Option String) (depUuid : Option Nat)
    (depName : String) : Option (PackageId × String) :=
  match projectFile, depUuid with
  | some file, some uuid => some (⟨some uuid, depName⟩, file)
  | _, _ => none

def Property433 : Prop := ∀ project uuid name pkg file,
  method433 project uuid name = some (pkg, file) →
  project = some file ∧ ∃ value, uuid = some value ∧ pkg = ⟨some value, name⟩

theorem property433 : Property433 := by
  intro project uuid name pkg file h
  cases project <;> cases uuid <;> simp_all [method433]

def method449 (value : Option (α × β)) : Option α := value.map Prod.fst

def Property449 : Prop := ∀ (α β : Type) (value : Option (α × β)),
  method449 (α := α) (β := β) value = none ↔ value = none

theorem property449 : Property449 := by
  unfold Property449
  intro α β value
  cases value <;> simp [method449]

def method476 (locked : (α → String → Option (PackageId × β)) → α → String → Option PackageId)
    (identify : α → String → Option (PackageId × β)) (context : α) (name : String) :=
  locked identify context name

def method477 (locked : (α → String → Option (PackageId × β)) → α → String → Option PackageId)
    (identify : α → String → Option (PackageId × β)) (context : α) (name : String) :=
  locked identify context name

def method478 (locked : (String → Option (PackageId × β)) → String → Option PackageId)
    (identify : String → Option (PackageId × β)) (name : String) := locked identify name

def Property476 : Prop := ∀ (α β : Type)
    (locked : (α → String → Option (PackageId × β)) → α → String → Option PackageId)
    identify context name result,
  locked identify context name = result → method476 locked identify context name = result
def Property477 : Prop := ∀ (α β : Type)
    (locked : (α → String → Option (PackageId × β)) → α → String → Option PackageId)
    identify context name result,
  locked identify context name = result → method477 locked identify context name = result
def Property478 : Prop := ∀ (β : Type)
    (locked : (String → Option (PackageId × β)) → String → Option PackageId)
    identify name result,
  locked identify name = result → method478 locked identify name = result

theorem property476 : Property476 := by simp [Property476, method476]
theorem property477 : Property477 := by simp [Property477, method477]
theorem property478 : Property478 := by simp [Property478, method478]

structure LoadSpec where
  path : String
  edition : Nat
  deriving Repr, DecidableEq

inductive LocateAnswer where
  | absent
  | stop
  | found (spec : LoadSpec) (env : String)
  deriving Repr, DecidableEq

def scanLocate : List LocateAnswer → Option (LoadSpec × String)
  | [] => none
  | .absent :: rest => scanLocate rest
  | .stop :: _ => none
  | .found spec env :: _ => some (spec, env)

/-- Search and final case-sensitive existence check in `locate_package_env`, lines 480-537. -/
def method480 (cached : Option (Option (LoadSpec × String))) (answers : List LocateAnswer)
    (caseSensitive : String → Bool) : Option (LoadSpec × String) :=
  match cached with
  | some answer => answer
  | none => match scanLocate answers with
    | some (spec, env) => if caseSensitive spec.path then some (spec, env) else none
    | none => none

def Property480 : Prop := ∀ cached answers isPresent spec env,
  cached = none → scanLocate answers = some (spec, env) → isPresent spec.path = false →
  method480 cached answers isPresent = none

theorem property480 : Property480 := by
  unfold Property480
  intro cached answers isPresent spec env hcached hscan hfile
  subst cached
  simp [method480, hscan, hfile]

def method553 (locate : PackageId → Option String → Option (LoadSpec × String))
    (pkg : PackageId) (stop : Option String) : Option String :=
  (locate pkg stop).map fun pair => pair.1.path

def Property553 : Prop := ∀ locate pkg stop path,
  method553 locate pkg stop = some path →
  ∃ spec env, locate pkg stop = some (spec, env) ∧ spec.path = path

theorem property553 : Property553 := by
  intro locate pkg stop path h
  cases hl : locate pkg stop with
  | none => simp [method553, hl] at h
  | some pair =>
      rcases pair with ⟨spec, env⟩
      simp [method553, hl] at h
      subst path
      exact ⟨spec, env, rfl, rfl⟩

def method561 (locate : PackageId → Option String → Option (LoadSpec × String))
    (pkg : PackageId) (stop : Option String) : Option LoadSpec :=
  (locate pkg stop).map Prod.fst

def Property561 : Prop := ∀ locate pkg stop spec,
  method561 locate pkg stop = some spec → ∃ env, locate pkg stop = some (spec, env)

theorem property561 : Property561 := by
  intro locate pkg stop spec h
  cases hl : locate pkg stop with
  | none => simp [method561, hl] at h
  | some pair =>
      rcases pair with ⟨found, env⟩
      simp [method561, hl] at h
      subst found
      exact ⟨env, rfl⟩

structure Origin where
  path : Option String
  version : Option Nat
  deriving Repr, DecidableEq

def method580 (pkgId : α → PackageId) (origins : List (PackageId × Origin))
    (fixup : String → String) (module : α) : Option String :=
  (lookupAssoc (pkgId module) origins).bind (fun origin => origin.path.map fixup)

def Property580 : Prop := ∀ (α : Type) pkgId origins fixup module path,
  method580 (α := α) pkgId origins fixup module = some path →
  ∃ origin raw, lookupAssoc (pkgId module) origins = some origin ∧
    origin.path = some raw ∧ path = fixup raw

theorem property580 : Property580 := by
  intro α pkgId origins fixup module path h
  cases ho : lookupAssoc (pkgId module) origins with
  | none => simp [method580, ho] at h
  | some origin =>
      cases hp : origin.path with
      | none => simp [method580, ho, hp] at h
      | some raw =>
          simp [method580, ho, hp] at h
          subst path
          exact ⟨origin, raw, rfl, hp, rfl⟩

inductive PackageLayout where | src | extFile | extDir | other
  deriving Repr, DecidableEq

/-- `pkgdir`, lines 617-634, after `pathof` and path splitting. -/
def method617 (path : Option String) (layout : PackageLayout)
    (root parent : String) (join : String → List String → String) (parts : List String) : Option String :=
  match path with
  | none => none
  | some _ => match layout with
    | .src | .extFile => some (join root parts)
    | .extDir => some (join parent parts)
    | .other => none

def Property617 : Prop := ∀ path layout root parent join parts result,
  method617 path layout root parent join parts = some result →
  path.isSome ∧ (result = join root parts ∨ result = join parent parts)

theorem property617 : Property617 := by
  intro path layout root parent join parts result h
  cases path <;> cases layout <;> simp_all [method617]

def method636 (projectFile : Option String) (version : Option Nat) : Option Nat :=
  if projectFile.isSome then version else none

def Property636 : Prop := ∀ project version value,
  method636 project version = some value → project.isSome ∧ version = some value

theorem property636 : Property636 := by
  intro project version value h
  cases project <;> simp_all [method636]

def method663 (cached : Option Origin) (pkgdirVersion : Option Nat) : Option Nat × Option Origin :=
  match cached with
  | some origin => match origin.version with
    | some version => (some version, some origin)
    | none => (pkgdirVersion, some { origin with version := pkgdirVersion })
  | none => (pkgdirVersion, none)

def Property663 : Prop := ∀ cached fresh result next,
  method663 cached fresh = (result, next) →
  result = fresh ∨ ∃ origin, cached = some origin ∧ result = origin.version

theorem property663 : Property663 := by
  intro cached fresh result next h
  cases cached with
  | none => simp_all [method663]
  | some origin =>
      cases hv : origin.version with
      | none => simp_all [method663]
      | some version =>
          simp [method663, hv] at h
          rcases h with ⟨rfl, rfl⟩
          exact Or.inr ⟨origin, rfl, hv.symm⟩

def firstExistingProject : List (String × Bool) → Option String
  | [] => none
  | (path, true) :: _ => some path
  | (_, false) :: rest => firstExistingProject rest

/-- `locate_project_file`, lines 690-698. -/
def method690 (candidates : List (String × Bool)) : Option String := firstExistingProject candidates

def Property690 : Prop := ∀ candidates path,
  method690 candidates = some path → (path, true) ∈ candidates

theorem property690 : Property690 := by
  intro candidates path h
  induction candidates with
  | nil => simp [method690, firstExistingProject] at h
  | cons head rest ih =>
      rcases head with ⟨candidate, isFile⟩
      cases isFile <;> simp_all [method690, firstExistingProject]

inductive ProjectClass where | missing | implicit | explicit (path : String)
  deriving Repr, DecidableEq

def method704 (cached : Option ProjectClass) (isDir : Bool)
    (located : Option String) (isProjectFile : Bool) (env : String) : ProjectClass :=
  match cached with
  | some value => value
  | none => if isDir then located.map ProjectClass.explicit |>.getD .implicit
    else if isProjectFile then .explicit env else .missing

def Property704 : Prop := ∀ cached isDir located isProject env,
  ∀ value, cached = some value → method704 cached isDir located isProject env = value

theorem property704 : Property704 := by
  intro cached isDir located isProject env value h
  simp [method704, h]

structure WorkspaceLevel where
  parent : String
  atRoot : Bool
  outsideHome : Bool
  project : Option String
  membersOriginal : Bool
  deriving Repr, DecidableEq

def scanWorkspace : List WorkspaceLevel → Option String
  | [] => none
  | level :: rest =>
      if level.atRoot || level.outsideHome then none
      else if level.membersOriginal then level.project
      else scanWorkspace rest

/-- Upward workspace search in `base_project`, lines 725-765. -/
def method725 (levels : List WorkspaceLevel) : Option String := scanWorkspace levels

def Property725 : Prop := ∀ levels base,
  method725 levels = some base → ∃ level ∈ levels,
    level.project = some base ∧ level.membersOriginal = true ∧
    level.atRoot = false ∧ level.outsideHome = false

theorem property725 : Property725 := by
  intro levels base h
  induction levels with
  | nil => simp [method725, scanWorkspace] at h
  | cons level rest ih =>
      simp only [method725, scanWorkspace] at h
      split at h <;> try contradiction
      split at h
      · refine ⟨level, by simp, ?_, by simp_all, by simp_all, by simp_all⟩
        simpa using h
      · obtain ⟨found, hmem, hp, hm, hr, ho⟩ := ih h
        exact ⟨found, by simp [hmem], hp, hm, hr, ho⟩

end JuliaLean.Loading.Coverage.Early
