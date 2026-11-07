import JuliaLean.base.loading

namespace JuliaLean.Loading.Coverage.Early

open JuliaLean.Loading.Coverage

def Property10 : Prop := ∀ isAccessibleFile path value,
  method10 isAccessibleFile path = .ok value ↔ isAccessibleFile path = .ok value

theorem property10 : Property10 := by simp [Property10, method10]

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

def Property119 : Prop := ∀ width bytes,
  (∃ digest, method119 width bytes = .ok digest) ↔ bytes.length = width

theorem property119 : Property119 := by
  intro width bytes
  by_cases h : bytes.length = width
  · simp [method119, h]
  · simp [method119, h]

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

def Property125 : Prop := ∀ width text digest,
  method125 width text = .ok digest → digest.bytes.length = width

theorem property125 : Property125 := by
  intro width text digest h
  exact (property124 width text digest h).2

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

def Property138 : Prop := ∀ stream digest,
  List.IsPrefix stream (method138 stream digest)

theorem property138 : Property138 := by
  intro stream digest
  simp [method138]

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

def Property141 : Prop := ∀ digest, method141 digest digest = false

theorem property141 : Property141 := by
  intro digest
  simp [method141]

def Property142 : Prop := ∀ hashPair typeTag seed a b,
  a = b → method142 hashPair typeTag seed a = method142 hashPair typeTag seed b

theorem property142 : Property142 := by
  intro hashPair typeTag seed a b h
  subst b
  rfl

def Property143 : Prop := ∀ a b, method143 a b = true ↔ a.bytes = b.bytes

theorem property143 : Property143 := by
  intro a b
  simp [method143]

def Property150 : Prop := ∀ wordBytes hashNamespace hash key,
  (method150 wordBytes hashNamespace hash key).version = 5 ∧
  (method150 wordBytes hashNamespace hash key).variant = 2

theorem property150 : Property150 := by
  unfold Property150
  intros
  exact ⟨rfl, rfl⟩

def Property164 : Prop := ∀ uuid5 projectFile realpath cache cached,
  cache.bind (fun c => lookupAssoc projectFile c.values) = some cached →
  method164 uuid5 projectFile realpath cache = (cached, cache)

theorem property164 : Property164 := by
  intro uuid5 projectFile realpath cache cached h
  simp [method164, h]

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

def Property200 : Prop := ∀ crc32 uuid p,
  (method200 crc32 uuid p).length = (if p ≤ 0 then 0 else p.toNat)

theorem property200 : Property200 := by
  intro crc32 uuid p
  exact (property189 (crc32 uuid) p).1

def Property205 : Prop := ∀ crcUuid crcBytes uuid sha p,
  (method205 crcUuid crcBytes uuid sha p).length = (if p ≤ 0 then 0 else p.toNat)

theorem property205 : Property205 := by
  intro crcUuid crcBytes uuid sha p
  exact (property189 (crcBytes sha (crcUuid uuid)) p).1

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

def Property278 : Prop := ∀ loadPath,
  (method278 loadPath).loadPath = loadPath ∧
  (method278 loadPath).dummyUuidCount = 0 ∧
  (method278 loadPath).locatedCount = 0

theorem property278 : Property278 := by simp [Property278, method278]

def Property294 : Prop := ∀ (α : Type) parser,
  (method294 (α := α) parser).values = []

theorem property294 : Property294 := by simp [Property294, method294]

def Property295 : Prop := ∀ (α : Type) convert parser values,
  (method295 (α := α) convert parser values).parser = parser ∧
  (method295 (α := α) convert parser values).values = convert values

theorem property295 : Property295 := by simp [Property295, method295]

def Property299 : Prop := ∀ (α β γ : Type) globalCache globalLock parse projectFile,
  method299 (α := α) (β := β) (γ := γ) globalCache globalLock parse projectFile =
    parse projectFile globalCache globalLock

theorem property299 : Property299 := by simp [Property299, method299]

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

def Property358 : Prop := ∀ (α : Type) (pkgId : α → PackageId)
    (identify : PackageId → String → Option (PackageId × Option String))
    (context : α) name result,
  method358 pkgId identify context name = result → identify (pkgId context) name = result

theorem property358 : Property358 := by simp [Property358, method358]

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

def Property405 : Prop := ∀ cached answers answer,
  cached = some answer → method405 cached answers = answer

theorem property405 : Property405 := by intro; simp_all [method405]

def Property431 : Prop := ∀ (α : Type) identify name,
  method431 (α := α) identify name = identify none name

theorem property431 : Property431 := by simp [Property431, method431]

def Property433 : Prop := ∀ project uuid name pkg file,
  method433 project uuid name = some (pkg, file) →
  project = some file ∧ ∃ value, uuid = some value ∧ pkg = ⟨some value, name⟩

theorem property433 : Property433 := by
  intro project uuid name pkg file h
  cases project <;> cases uuid <;> simp_all [method433]

def Property449 : Prop := ∀ (α β : Type) (value : Option (α × β)),
  method449 (α := α) (β := β) value = none ↔ value = none

theorem property449 : Property449 := by
  unfold Property449
  intro α β value
  cases value <;> simp [method449]

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

def Property480 : Prop := ∀ cached answers isPresent spec env,
  cached = none → scanLocate answers = some (spec, env) → isPresent spec.path = false →
  method480 cached answers isPresent = none

theorem property480 : Property480 := by
  unfold Property480
  intro cached answers isPresent spec env hcached hscan hfile
  subst cached
  simp [method480, hscan, hfile]

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

def Property617 : Prop := ∀ path layout root parent join parts result,
  method617 path layout root parent join parts = some result →
  path.isSome ∧ (result = join root parts ∨ result = join parent parts)

theorem property617 : Property617 := by
  intro path layout root parent join parts result h
  cases path <;> cases layout <;> simp_all [method617]

def Property636 : Prop := ∀ project version value,
  method636 project version = some value → project.isSome ∧ version = some value

theorem property636 : Property636 := by
  intro project version value h
  cases project <;> simp_all [method636]

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

def Property690 : Prop := ∀ candidates path,
  method690 candidates = some path → (path, true) ∈ candidates

theorem property690 : Property690 := by
  intro candidates path h
  induction candidates with
  | nil => simp [method690, firstExistingProject] at h
  | cons head rest ih =>
      rcases head with ⟨candidate, isFile⟩
      cases isFile <;> simp_all [method690, firstExistingProject]

def Property704 : Prop := ∀ cached isDir located isProject env,
  ∀ value, cached = some value → method704 cached isDir located isProject env = value

theorem property704 : Property704 := by
  intro cached isDir located isProject env value h
  simp [method704, h]

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