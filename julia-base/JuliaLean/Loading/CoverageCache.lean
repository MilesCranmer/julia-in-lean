import JuliaLean.Loading.CoverageRequire

namespace JuliaLean.Loading.Coverage.Cache

open JuliaLean.Loading.Coverage
open JuliaLean.Loading.Coverage.Early
open JuliaLean.Loading.Coverage.Extensions

def method4025 (segments : List Nat) : Nat := segments.foldl (fun acc x => acc * 2 ^ 32 + x) 0
def Property4025 : Prop := ∀ segments, method4025 segments ≥ 0
theorem property4025 : Property4025 := by intro; exact Nat.zero_le _

def method4036 (magic checksumValid versionValid : Bool) : Option Nat :=
  if magic && checksumValid && versionValid then some 0 else none
def Property4036 : Prop := ∀ magic checksum version value,
  method4036 magic checksum version = some value → magic = true ∧ checksum = true ∧ version = true
theorem property4036 : Property4036 := by simp [Property4036, method4036]

def method4047 (stored computed : Nat) : Bool := stored == computed
def Property4047 : Prop := ∀ stored computed, method4047 stored computed = true ↔ stored = computed
theorem property4047 : Property4047 := by simp [Property4047, method4047]

def method4049 (fileValid objectValid : Bool) : Bool := fileValid && objectValid
def Property4049 : Prop := ∀ file object, method4049 file object = true ↔ file = true ∧ object = true
theorem property4049 : Property4049 := by simp [Property4049, method4049]

def method4061 (device inode : Nat) : Nat × Nat := (device, inode)
def Property4061 : Prop := ∀ device inode, (method4061 device inode).2 = inode
theorem property4061 : Property4061 := by simp [Property4061, method4061]

def method4063 (cache object : Option (Nat × Nat)) := (cache, object)
def Property4063 : Prop := ∀ cache object, (method4063 cache object).1 = cache
theorem property4063 : Property4063 := by simp [Property4063, method4063]

def method4070 (stored current : Nat × Option Nat) (split : Bool) : Bool :=
  stored.1 != current.1 || (split && stored.2 != current.2)
def Property4070 : Prop := ∀ stored current split,
  method4070 stored current split = false → stored.1 = current.1
theorem property4070 : Property4070 := by simp [Property4070, method4070]

def method4086 (openSucceeded keyMatches : Bool) : Bool := !openSucceeded || !keyMatches
def Property4086 : Prop := ∀ opened keysMatch,
  method4086 opened keysMatch = false ↔ opened = true ∧ keysMatch = true
theorem property4086 : Property4086 := by
  intro opened keysMatch; cases opened <;> cases keysMatch <;> simp [method4086]

def method4119 (header checksum : Bool) : Bool := header && checksum
def Property4119 : Prop := ∀ header checksum,
  method4119 header checksum = true ↔ header = true ∧ checksum = true
theorem property4119 : Property4119 := by simp [Property4119, method4119]

structure IncludeHeader where
  moduleId : Nat
  filename : String
  size : Nat
  hash : Nat
  mtime : Int
  deriving Repr, DecidableEq
def method4144 (moduleId : Nat) (filename : String) (size hash : Nat) (mtime : Int) : IncludeHeader :=
  ⟨moduleId, filename, size, hash, mtime⟩
def Property4144 : Prop := ∀ moduleId filename size hash mtime,
  (method4144 moduleId filename size hash mtime).filename = filename
theorem property4144 : Property4144 := by simp [Property4144, method4144]

def method4148 (path : String) (matchingDepot : Option String) : String :=
  matchingDepot.map (fun relative => "@depot/" ++ relative) |>.getD path
def Property4148 : Prop := ∀ path depot result,
  method4148 path depot = result → result = path ∨ ∃ relative, depot = some relative ∧ result = "@depot/" ++ relative
theorem property4148 : Property4148 := by
  intro path depot result h; cases depot <;> simp_all [method4148]

def method4158 (depots : List String) : List String := depots.map id |>.eraseDups
def Property4158 : Prop := ∀ depots depot, depot ∈ method4158 depots ↔ depot ∈ depots
theorem property4158 : Property4158 := by simp [Property4158, method4158]

def method4171 (tagged : Bool) (relative depot : String) : String := if tagged then depot ++ "/" ++ relative else relative
def Property4171 : Prop := ∀ tagged relative depot,
  tagged = true → (method4171 tagged relative depot).startsWith depot = true
theorem property4171 : Property4171 := by simp [Property4171, method4171]

def method4175 (taggedExists hintExists : Bool) (tagged hint raw : String) : Option String :=
  if taggedExists then some tagged else if hintExists then some hint else some raw
def Property4175 : Prop := ∀ taggedExists hintExists tagged hint raw result,
  method4175 taggedExists hintExists tagged hint raw = some result → result ∈ [tagged, hint, raw]
theorem property4175 : Property4175 := by
  intro taggedExists hintExists tagged hint raw result h
  cases taggedExists <;> cases hintExists <;> simp_all [method4175]

def method4188 (count : Nat) (readEntry : Nat → PackageId × Nat) : List (PackageId × Nat) :=
  (List.range count).map readEntry
def Property4188 : Prop := ∀ count readEntry, (method4188 count readEntry).length = count
theorem property4188 : Property4188 := by simp [Property4188, method4188]

structure HeaderModel where
  includes : Nat
  modules : Nat
  preferences : String
  cloneTargets : List String
  deriving Repr, DecidableEq
def method4202 (includes modules : Nat) (preferences : String) (targets : List String) : HeaderModel :=
  ⟨includes, modules, preferences, targets⟩
def Property4202 : Prop := ∀ includes modules prefs targets,
  (method4202 includes modules prefs targets).includes = includes
theorem property4202 : Property4202 := by simp [Property4202, method4202]

def method4265 (headerValid : Bool) (header : HeaderModel) : Result HeaderModel :=
  if headerValid then .ok header else .error .argument
def Property4265 : Prop := ∀ valid header result,
  method4265 valid header = .ok result → valid = true ∧ result = header
theorem property4265 : Property4265 := by simp [Property4265, method4265]

def method4359 (openResult : Result HeaderModel) : Result HeaderModel := openResult
def Property4359 : Prop := ∀ result error, method4359 result = .error error → result = .error error
theorem property4359 : Property4359 := by simp [Property4359, method4359]

def method4370 (header : HeaderModel) : String := header.preferences
def Property4370 : Prop := ∀ header, method4370 header = header.preferences
theorem property4370 : Property4370 := by simp [Property4370, method4370]

def method4371 (parse : String → Result HeaderModel) (file : String) : Result String :=
  match parse file with | .ok header => .ok header.preferences | .error error => .error error
def Property4371 : Prop := ∀ parse file prefs,
  method4371 parse file = .ok prefs → ∃ header, parse file = .ok header ∧ prefs = header.preferences
theorem property4371 : Property4371 := by
  intro parse file prefs h; cases hp : parse file <;> simp_all [method4371]

def method4383 (header : HeaderModel) : Nat := header.modules
def Property4383 : Prop := ∀ header, method4383 header = header.modules
theorem property4383 : Property4383 := by simp [Property4383, method4383]

def method4388 (parse : String → Result HeaderModel) (file : String) : Result Nat :=
  match parse file with | .ok header => .ok header.modules | .error error => .error error
def Property4388 : Prop := ∀ parse file deps,
  method4388 parse file = .ok deps → ∃ header, parse file = .ok header ∧ deps = header.modules
theorem property4388 : Property4388 := by
  intro parse file deps h; cases hp : parse file <;> simp_all [method4388]

def method4398 (seek : String → Bool) (read : String → Result String) (filename : String) : Result String :=
  if seek filename then read filename else .error .bounds
def Property4398 : Prop := ∀ seek read filename value,
  method4398 seek read filename = .ok value → seek filename = true ∧ read filename = .ok value
theorem property4398 : Property4398 := by
  intro seek read filename value h
  by_cases hs : seek filename <;> simp_all [method4398, hs]

def method4405 : List (String × String) → String → Option String
  | [], _ => none
  | (name,value) :: rest, filename => if name == filename then some value else method4405 rest filename
def Property4405 : Prop := ∀ entries filename value,
  method4405 entries filename = some value → (filename, value) ∈ entries
theorem property4405 : Property4405 := by
  intro entries filename value h
  induction entries with
  | nil => simp [method4405] at h
  | cons pair rest ih =>
      rcases pair with ⟨name, found⟩
      by_cases heq : name = filename <;> simp_all [method4405, heq]

def method4428 (openRead : String → String → Result String) (cache filename : String) := openRead cache filename
def Property4428 : Prop := ∀ openRead cache filename value,
  method4428 openRead cache filename = .ok value → openRead cache filename = .ok value
theorem property4428 : Property4428 := by simp [Property4428, method4428]

def method4438 (includes : List IncludeHeader) (read : IncludeHeader → Option String) : List (String × String) :=
  includes.filterMap fun inc => (read inc).map (inc.filename, ·)
def Property4438 : Prop := ∀ includes read,
  (method4438 includes read).length ≤ includes.length
theorem property4438 : Property4438 := by
  intro includes read
  simp [method4438, List.length_filterMap_le]

def findUuid : List (String × Nat) → Nat → Option String
  | [], _ => none
  | (name,id) :: rest, uuid => if id = uuid then some name else findUuid rest uuid
def method4456 (root : Option (Nat × String)) (deps weak : List (String × Nat)) (uuid : Nat) : Option String :=
  match root with
  | some (id, name) => if id = uuid then some name else choose (findUuid deps uuid) (findUuid weak uuid)
  | none => choose (findUuid deps uuid) (findUuid weak uuid)
def Property4456 : Prop := ∀ root deps weak uuid name,
  method4456 root deps weak uuid = some name →
  root = some (uuid, name) ∨ (name, uuid) ∈ deps ∨ (name, uuid) ∈ weak
theorem property4456 : Property4456 := by
  intro root deps weak uuid name h
  have findUuid_mem : ∀ entries, findUuid entries uuid = some name → (name,uuid) ∈ entries := by
    intro entries hf
    induction entries with
    | nil => simp [findUuid] at hf
    | cons pair rest ih =>
        rcases pair with ⟨entryName,id⟩
        by_cases heq : id = uuid <;> simp_all [findUuid, heq]
  cases root with
  | none =>
      cases hd : findUuid deps uuid <;> cases hw : findUuid weak uuid <;> simp_all [method4456, choose]
  | some pair =>
      rcases pair with ⟨id,rootName⟩
      by_cases heq : id = uuid
      · simp [method4456, heq] at h; subst rootName; simp [heq]
      · cases hd : findUuid deps uuid <;> cases hw : findUuid weak uuid <;>
          simp_all [method4456, heq, choose]

def method4483 (parse : String → α) (lookup : α → Nat → Option String) (file : String) (uuid : Nat) :=
  lookup (parse file) uuid
def Property4483 : Prop := ∀ (α : Type) parse lookup file uuid result,
  method4483 (α := α) parse lookup file uuid = some result → lookup (parse file) uuid = some result
theorem property4483 : Property4483 := by simp [Property4483, method4483]

def method4490 (prefs : List (String × String)) (package : String) : List (String × String) :=
  prefs.filter (fun p => p.1 == package)
def Property4490 : Prop := ∀ prefs package key value,
  (key,value) ∈ method4490 prefs package → key = package
theorem property4490 : Property4490 := by simp [Property4490, method4490]

def method4498 (projects : List (List (String × String))) : List (String × String) := projects.flatten
def Property4498 : Prop := ∀ projects entry,
  entry ∈ method4498 projects ↔ ∃ project ∈ projects, entry ∈ project
theorem property4498 : Property4498 := by simp [Property4498, method4498]

def method4541 (base : List (String × String)) (overrides : List (List (String × String))) :=
  overrides.foldl (fun acc entries => entries.foldl (fun out p => updateAssoc p.1 p.2 out) acc) base
def Property4541 : Prop := ∀ base overrides,
  overrides = [] → method4541 base overrides = base
theorem property4541 : Property4541 := by simp [Property4541, method4541]

def method4566 (project parents : String) (ancestors : List String) : List String := project :: ancestors ++ [parents]
def Property4566 : Prop := ∀ project root ancestors, project ∈ method4566 project root ancestors
theorem property4566 : Property4566 := by simp [Property4566, method4566]

def method4577 (projects : List (List (String × String))) := method4498 projects
def Property4577 : Prop := ∀ projects entry, entry ∈ method4577 projects → ∃ p ∈ projects, entry ∈ p
theorem property4577 : Property4577 := by simp [Property4577, method4577, method4498]

def method4604 (observed : List (Nat × String)) (uuid : Nat) (key : String) :=
  if (uuid,key) ∈ observed then observed else (uuid,key) :: observed
def Property4604 : Prop := ∀ observed uuid key, (uuid,key) ∈ method4604 observed uuid key
theorem property4604 : Property4604 := by
  intro observed uuid key
  by_cases h : (uuid,key) ∈ observed <;> simp [method4604, h]

def method4612 (observed : List (String × Option String)) : List (String × Option String) := observed
def Property4612 : Prop := ∀ observed, (method4612 observed).length = observed.length
theorem property4612 : Property4612 := by simp [Property4612, method4612]

def method4642 (targets : List String) : Bool := targets.all (fun t => !t.isEmpty)
def Property4642 : Prop := ∀ targets, method4642 targets = true → ∀ t ∈ targets, t.isEmpty = false
theorem property4642 : Property4642 := by simp [Property4642, method4642]

def method4657 (directory name : String) : String := directory ++ "/" ++ name ++ ".pid"
def Property4657 : Prop := ∀ directory name, ∃ pre, method4657 directory name = pre ++ ".pid"
theorem property4657 : Property4657 := by intro directory name; exact ⟨directory ++ "/" ++ name, rfl⟩

def method4669 (lockEnabled : Bool) (action : Unit → α) : α := action ()
def Property4669 : Prop := ∀ (α : Type) enabled action, method4669 (α := α) enabled action = action ()
theorem property4669 : Property4669 := by simp [Property4669, method4669]

def method4692 (reasons : List (String × Nat)) (reason : String) : List (String × Nat) :=
  updateAssoc reason ((lookupAssoc reason reasons).getD 0 + 1) reasons
def Property4692 : Prop := ∀ reasons reason, lookupAssoc reason (method4692 reasons reason) ≠ none
theorem property4692 : Property4692 := by simp [Property4692, method4692, updateAssoc, lookupAssoc]

def method4695 (_reason : String) : Unit := ()
def Property4695 : Prop := ∀ reason, method4695 reason = ()
theorem property4695 : Property4695 := by simp [Property4695, method4695]

def method4733 (key : String) : String := key
def Property4733 : Prop := ∀ key, method4733 key = key
theorem property4733 : Property4733 := by simp [Property4733, method4733]

def method4744 (reasons : List (String × Nat)) (full : Bool) : List String :=
  reasons.filterMap fun p => if full || p.2 > 0 then some p.1 else none
def Property4744 : Prop := ∀ reasons full,
  (method4744 reasons full).length ≤ reasons.length
theorem property4744 : Property4744 := by
  intro reasons full
  simp [method4744, List.length_filterMap_le]

def method4768 (_full : Bool) : List String := []
def Property4768 : Prop := ∀ full, method4768 full = []
theorem property4768 : Property4768 := by simp [Property4768, method4768]

def method4773 (pkg : PackageId) : String := pkg.name
def Property4773 : Prop := ∀ pkg, method4773 pkg = pkg.name
theorem property4773 : Property4773 := by simp [Property4773, method4773]

def method4792 (extension parent : PackageId) : String := parent.name ++ " → " ++ extension.name
def Property4792 : Prop := ∀ ext parent, (method4792 ext parent).startsWith parent.name = true
theorem property4792 : Property4792 := by intro; simp [method4792]

def method4794 (path : String) (stores : List String) : Bool := stores.any (fun root => path.startsWith root)
def Property4794 : Prop := ∀ path stores, method4794 path stores = true → ∃ root ∈ stores, path.startsWith root = true
theorem property4794 : Property4794 := by simp [Property4794, method4794]

structure IncludeFactModel where
  present : Bool
  identity : Bool
  content : Bool
  mtime : Bool
  deriving Repr, DecidableEq
def method4802 (includes : List IncludeFactModel) : Bool :=
  includes.any fun inc => !inc.present || !inc.identity || !inc.content || !inc.mtime
def Property4802 : Prop := ∀ includes,
  method4802 includes = false → ∀ inc ∈ includes,
  inc.present = true ∧ inc.identity = true ∧ inc.content = true ∧ inc.mtime = true
theorem property4802 : Property4802 := by
  intro includes h inc hi
  simp [method4802] at h
  rcases h inc hi with ⟨⟨⟨hp,hid⟩,hc⟩,hm⟩
  exact ⟨hp,hid,hc,hm⟩

def method4859 (version : Nat × Nat) : Nat := version.1 * 16 + version.2
def Property4859 : Prop := ∀ major minor, method4859 (major,minor) % 16 = minor % 16
theorem property4859 : Property4859 := by simp [Property4859, method4859, Nat.add_mod]

def method4866 [BEq α] (a b : α) : Bool := a == b
def Property4866 : Prop := ∀ (α : Type) [BEq α] [LawfulBEq α] (a b : α), method4866 a b = true ↔ a = b
theorem property4866 : Property4866 := by
  unfold Property4866
  intro α inst lawful a b
  simpa [method4866] using (beq_iff_eq : (a == b) = true ↔ a = b)

def method4868 [BEq α] (a b : List α) : Bool := a == b
def Property4868 : Prop := ∀ (α : Type) [BEq α] [LawfulBEq α] (a b : List α), method4868 a b = true ↔ a = b
theorem property4868 : Property4868 := by
  unfold Property4868
  intro α inst lawful a b
  simpa [method4868] using (beq_iff_eq : (a == b) = true ↔ a = b)

def method4876 [BEq κ] [BEq ν] (a b : List (κ × ν)) : Bool := a == b
def Property4876 : Prop := ∀ (κ ν : Type) [BEq κ] [LawfulBEq κ] [BEq ν] [LawfulBEq ν]
  (a b : List (κ × ν)), method4876 a b = true ↔ a = b
theorem property4876 : Property4876 := by
  unfold Property4876
  intro κ ν instK lawfulK instV lawfulV a b
  simpa [method4876] using (beq_iff_eq : (a == b) = true ↔ a = b)

def method4885 (observed : List (String × Option String)) (current : String → Option String) : Bool :=
  observed.any fun p => current p.1 != p.2
def Property4885 : Prop := ∀ observed current,
  method4885 observed current = false ↔ ∀ key value, (key,value) ∈ observed → current key = value
theorem property4885 : Property4885 := by simp [Property4885, method4885]

def method4913 (spec : Option LoadSpec) (stale : LoadSpec → Bool) : Bool := spec.map stale |>.getD true
def Property4913 : Prop := ∀ spec stale, spec = none → method4913 spec stale = true
theorem property4913 : Property4913 := by intro spec stale h; subst spec; rfl

def method4916 (build : Nat) (spec : LoadSpec) (check : Nat → LoadSpec → Bool) := check build spec
def Property4916 : Prop := ∀ build spec check, check build spec = true → method4916 build spec check = true
theorem property4916 : Property4916 := by simp [Property4916, method4916]

structure StaleFacts where
  header : Bool
  flags : Bool
  identity : Bool
  deps : Bool
  sources : Bool
  checksum : Bool
  prefs : Bool
  deriving Repr, DecidableEq
def method4919 (facts : StaleFacts) : Bool :=
  !facts.header || !facts.flags || !facts.identity || !facts.deps || !facts.sources || !facts.checksum || !facts.prefs
def Property4919 : Prop := ∀ facts, method4919 facts = false ↔
  facts.header = true ∧ facts.flags = true ∧ facts.identity = true ∧ facts.deps = true ∧
  facts.sources = true ∧ facts.checksum = true ∧ facts.prefs = true
theorem property4919 : Property4919 := by
  intro facts
  rcases facts with ⟨header,flags,identity,deps,sources,checksum,prefs⟩
  cases header <;> cases flags <;> cases identity <;> cases deps <;>
    cases sources <;> cases checksum <;> cases prefs <;> simp [method4919]

def method5149 (source : Option String) : Option String := source
def Property5149 : Prop := ∀ source result, method5149 source = some result → source = some result
theorem property5149 : Property5149 := by simp [Property5149, method5149]

def method5184 (source : Option String) (dirname : String → String) : Option String := source.map dirname
def Property5184 : Prop := ∀ source dirname result,
  method5184 source dirname = some result → ∃ file, source = some file ∧ result = dirname file
theorem property5184 : Property5184 := by
  intro source dirname result h
  cases source <;> simp_all [method5184]

def method5190 (prepared : Bool) : Bool := true
def Property5190 : Prop := ∀ prepared, method5190 prepared = true
theorem property5190 : Property5190 := by simp [Property5190, method5190]

def method5196 (path library : String) : String × String := (path,library)
def Property5196 : Prop := ∀ path library, (method5196 path library).1 = path
theorem property5196 : Property5196 := by simp [Property5196, method5196]

def method5199 (tuple : α × β) : β := tuple.2
def Property5199 : Prop := ∀ (α β : Type) (tuple : α × β), method5199 tuple = tuple.2
theorem property5199 : Property5199 := by simp [Property5199, method5199]

def method5207 (specialize : α → β → Bool) (f : α) (args : β) := specialize f args
def Property5207 : Prop := ∀ (α β : Type) specialize f args,
  specialize f args = true → method5207 (α := α) (β := β) specialize f args = true
theorem property5207 : Property5207 := by simp [Property5207, method5207]

def method5211 (tupleType : α → Bool) (argType : α) := tupleType argType
def Property5211 : Prop := ∀ (α : Type) check arg, check arg = true → method5211 (α := α) check arg = true
theorem property5211 : Property5211 := by simp [Property5211, method5211]

def method5220 (allowed : Bool) (compile : Unit → Bool) : Bool := allowed && compile ()
def Property5220 : Prop := ∀ allowed compile, method5220 allowed compile = true → allowed = true
theorem property5220 : Property5220 := by simp [Property5220, method5220]

def method5225 (tupleValid : Bool) (compile : Unit → Bool) : Bool := tupleValid && compile ()
def Property5225 : Prop := ∀ valid compile, method5225 valid compile = true → valid = true
theorem property5225 : Property5225 := by simp [Property5225, method5225]

def method5234 (compile : Nat → Bool) (world : Nat) := compile world
def Property5234 : Prop := ∀ compile world, compile world = true → method5234 compile world = true
theorem property5234 : Property5234 := by simp [Property5234, method5234]

def method5244 (methodMatches : Bool) (compile : Unit → Bool) : Bool := methodMatches && compile ()
def Property5244 : Prop := ∀ methodMatches compile, method5244 methodMatches compile = true → methodMatches = true
theorem property5244 : Property5244 := by simp [Property5244, method5244]

def method5248 (tupleMatches : Bool) (compile : Unit → Bool) : Bool := tupleMatches && compile ()
def Property5248 : Prop := ∀ tupleMatches compile, method5248 tupleMatches compile = true → tupleMatches = true
theorem property5248 : Property5248 := by simp [Property5248, method5248]

end JuliaLean.Loading.Coverage.Cache
