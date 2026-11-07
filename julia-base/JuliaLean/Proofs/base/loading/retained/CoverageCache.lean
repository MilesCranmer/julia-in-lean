import JuliaLean.base.loading
import JuliaLean.Proofs.base.loading.retained.CoverageRequire

namespace JuliaLean.Loading.Coverage.Cache

open JuliaLean.Loading.Coverage
open JuliaLean.Loading.Coverage.Early
open JuliaLean.Loading.Coverage.Extensions
def Property4025 : Prop := ∀ segments, method4025 segments ≥ 0
theorem property4025 : Property4025 := by intro; exact Nat.zero_le _
def Property4036 : Prop := ∀ magic checksum version value,
  method4036 magic checksum version = some value → magic = true ∧ checksum = true ∧ version = true
theorem property4036 : Property4036 := by simp [Property4036, method4036]
def Property4047 : Prop := ∀ stored computed, method4047 stored computed = true ↔ stored = computed
theorem property4047 : Property4047 := by simp [Property4047, method4047]
def Property4049 : Prop := ∀ file object, method4049 file object = true ↔ file = true ∧ object = true
theorem property4049 : Property4049 := by simp [Property4049, method4049]
def Property4061 : Prop := ∀ device inode, (method4061 device inode).2 = inode
theorem property4061 : Property4061 := by simp [Property4061, method4061]
def Property4063 : Prop := ∀ cache object, (method4063 cache object).1 = cache
theorem property4063 : Property4063 := by simp [Property4063, method4063]
def Property4070 : Prop := ∀ stored current split,
  method4070 stored current split = false → stored.1 = current.1
theorem property4070 : Property4070 := by simp [Property4070, method4070]
def Property4086 : Prop := ∀ opened keysMatch,
  method4086 opened keysMatch = false ↔ opened = true ∧ keysMatch = true
theorem property4086 : Property4086 := by
  intro opened keysMatch; cases opened <;> cases keysMatch <;> simp [method4086]
def Property4119 : Prop := ∀ header checksum,
  method4119 header checksum = true ↔ header = true ∧ checksum = true
theorem property4119 : Property4119 := by simp [Property4119, method4119]
def Property4144 : Prop := ∀ moduleId filename size hash mtime,
  (method4144 moduleId filename size hash mtime).filename = filename
theorem property4144 : Property4144 := by simp [Property4144, method4144]
def Property4148 : Prop := ∀ path depot result,
  method4148 path depot = result → result = path ∨ ∃ relative, depot = some relative ∧ result = "@depot/" ++ relative
theorem property4148 : Property4148 := by
  intro path depot result h; cases depot <;> simp_all [method4148]
def Property4158 : Prop := ∀ depots depot, depot ∈ method4158 depots ↔ depot ∈ depots
theorem property4158 : Property4158 := by simp [Property4158, method4158]
def Property4171 : Prop := ∀ tagged relative depot,
  tagged = true → (method4171 tagged relative depot).startsWith depot = true
theorem property4171 : Property4171 := by simp [Property4171, method4171]
def Property4175 : Prop := ∀ taggedExists hintExists tagged hint raw result,
  method4175 taggedExists hintExists tagged hint raw = some result → result ∈ [tagged, hint, raw]
theorem property4175 : Property4175 := by
  intro taggedExists hintExists tagged hint raw result h
  cases taggedExists <;> cases hintExists <;> simp_all [method4175]
def Property4188 : Prop := ∀ count readEntry, (method4188 count readEntry).length = count
theorem property4188 : Property4188 := by simp [Property4188, method4188]
def Property4202 : Prop := ∀ includes modules prefs targets,
  (method4202 includes modules prefs targets).includes = includes
theorem property4202 : Property4202 := by simp [Property4202, method4202]
def Property4265 : Prop := ∀ valid header result,
  method4265 valid header = .ok result → valid = true ∧ result = header
theorem property4265 : Property4265 := by simp [Property4265, method4265]
def Property4359 : Prop := ∀ result error, method4359 result = .error error → result = .error error
theorem property4359 : Property4359 := by simp [Property4359, method4359]
def Property4370 : Prop := ∀ header, method4370 header = header.preferences
theorem property4370 : Property4370 := by simp [Property4370, method4370]
def Property4371 : Prop := ∀ parse file prefs,
  method4371 parse file = .ok prefs → ∃ header, parse file = .ok header ∧ prefs = header.preferences
theorem property4371 : Property4371 := by
  intro parse file prefs h; cases hp : parse file <;> simp_all [method4371]
def Property4383 : Prop := ∀ header, method4383 header = header.modules
theorem property4383 : Property4383 := by simp [Property4383, method4383]
def Property4388 : Prop := ∀ parse file deps,
  method4388 parse file = .ok deps → ∃ header, parse file = .ok header ∧ deps = header.modules
theorem property4388 : Property4388 := by
  intro parse file deps h; cases hp : parse file <;> simp_all [method4388]
def Property4398 : Prop := ∀ seek read filename value,
  method4398 seek read filename = .ok value → seek filename = true ∧ read filename = .ok value
theorem property4398 : Property4398 := by
  intro seek read filename value h
  by_cases hs : seek filename <;> simp_all [method4398, hs]
def Property4405 : Prop := ∀ entries filename value,
  method4405 entries filename = some value → (filename, value) ∈ entries
theorem property4405 : Property4405 := by
  intro entries filename value h
  induction entries with
  | nil => simp [method4405] at h
  | cons pair rest ih =>
      rcases pair with ⟨name, found⟩
      by_cases heq : name = filename <;> simp_all [method4405, heq]
def Property4428 : Prop := ∀ openRead cache filename value,
  method4428 openRead cache filename = .ok value → openRead cache filename = .ok value
theorem property4428 : Property4428 := by simp [Property4428, method4428]
def Property4438 : Prop := ∀ includes read,
  (method4438 includes read).length ≤ includes.length
theorem property4438 : Property4438 := by
  intro includes read
  simp [method4438, List.length_filterMap_le]
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
def Property4483 : Prop := ∀ (α : Type) parse lookup file uuid result,
  method4483 (α := α) parse lookup file uuid = some result → lookup (parse file) uuid = some result
theorem property4483 : Property4483 := by simp [Property4483, method4483]
def Property4490 : Prop := ∀ prefs package key value,
  (key,value) ∈ method4490 prefs package → key = package
theorem property4490 : Property4490 := by simp [Property4490, method4490]
def Property4498 : Prop := ∀ projects entry,
  entry ∈ method4498 projects ↔ ∃ project ∈ projects, entry ∈ project
theorem property4498 : Property4498 := by simp [Property4498, method4498]
def Property4541 : Prop := ∀ base overrides,
  overrides = [] → method4541 base overrides = base
theorem property4541 : Property4541 := by simp [Property4541, method4541]
def Property4566 : Prop := ∀ project root ancestors, project ∈ method4566 project root ancestors
theorem property4566 : Property4566 := by simp [Property4566, method4566]
def Property4577 : Prop := ∀ projects entry, entry ∈ method4577 projects → ∃ p ∈ projects, entry ∈ p
theorem property4577 : Property4577 := by simp [Property4577, method4577, method4498]
def Property4604 : Prop := ∀ observed uuid key, (uuid,key) ∈ method4604 observed uuid key
theorem property4604 : Property4604 := by
  intro observed uuid key
  by_cases h : (uuid,key) ∈ observed <;> simp [method4604, h]
def Property4612 : Prop := ∀ observed, (method4612 observed).length = observed.length
theorem property4612 : Property4612 := by simp [Property4612, method4612]
def Property4642 : Prop := ∀ targets, method4642 targets = true → ∀ t ∈ targets, t.isEmpty = false
theorem property4642 : Property4642 := by simp [Property4642, method4642]
def Property4657 : Prop := ∀ directory name, ∃ pre, method4657 directory name = pre ++ ".pid"
theorem property4657 : Property4657 := by intro directory name; exact ⟨directory ++ "/" ++ name, rfl⟩
def Property4669 : Prop := ∀ (α : Type) enabled action, method4669 (α := α) enabled action = action ()
theorem property4669 : Property4669 := by simp [Property4669, method4669]
def Property4692 : Prop := ∀ reasons reason, lookupAssoc reason (method4692 reasons reason) ≠ none
theorem property4692 : Property4692 := by simp [Property4692, method4692, updateAssoc, lookupAssoc]
def Property4695 : Prop := ∀ reason, method4695 reason = ()
theorem property4695 : Property4695 := by simp [Property4695, method4695]
def Property4733 : Prop := ∀ key, method4733 key = key
theorem property4733 : Property4733 := by simp [Property4733, method4733]
def Property4744 : Prop := ∀ reasons full,
  (method4744 reasons full).length ≤ reasons.length
theorem property4744 : Property4744 := by
  intro reasons full
  simp [method4744, List.length_filterMap_le]
def Property4768 : Prop := ∀ full, method4768 full = []
theorem property4768 : Property4768 := by simp [Property4768, method4768]
def Property4773 : Prop := ∀ pkg, method4773 pkg = pkg.name
theorem property4773 : Property4773 := by simp [Property4773, method4773]
def Property4792 : Prop := ∀ ext parent, (method4792 ext parent).startsWith parent.name = true
theorem property4792 : Property4792 := by intro; simp [method4792]
def Property4794 : Prop := ∀ path stores, method4794 path stores = true → ∃ root ∈ stores, path.startsWith root = true
theorem property4794 : Property4794 := by simp [Property4794, method4794]
def Property4802 : Prop := ∀ includes,
  method4802 includes = false → ∀ inc ∈ includes,
  inc.present = true ∧ inc.identity = true ∧ inc.content = true ∧ inc.mtime = true
theorem property4802 : Property4802 := by
  intro includes h inc hi
  simp [method4802] at h
  rcases h inc hi with ⟨⟨⟨hp,hid⟩,hc⟩,hm⟩
  exact ⟨hp,hid,hc,hm⟩
def Property4859 : Prop := ∀ major minor, method4859 (major,minor) % 16 = minor % 16
theorem property4859 : Property4859 := by simp [Property4859, method4859, Nat.add_mod]
def Property4866 : Prop := ∀ (α : Type) [BEq α] [LawfulBEq α] (a b : α), method4866 a b = true ↔ a = b
theorem property4866 : Property4866 := by
  unfold Property4866
  intro α inst lawful a b
  simpa [method4866] using (beq_iff_eq : (a == b) = true ↔ a = b)
def Property4868 : Prop := ∀ (α : Type) [BEq α] [LawfulBEq α] (a b : List α), method4868 a b = true ↔ a = b
theorem property4868 : Property4868 := by
  unfold Property4868
  intro α inst lawful a b
  simpa [method4868] using (beq_iff_eq : (a == b) = true ↔ a = b)
def Property4876 : Prop := ∀ (κ ν : Type) [BEq κ] [LawfulBEq κ] [BEq ν] [LawfulBEq ν]
  (a b : List (κ × ν)), method4876 a b = true ↔ a = b
theorem property4876 : Property4876 := by
  unfold Property4876
  intro κ ν instK lawfulK instV lawfulV a b
  simpa [method4876] using (beq_iff_eq : (a == b) = true ↔ a = b)
def Property4885 : Prop := ∀ observed current,
  method4885 observed current = false ↔ ∀ key value, (key,value) ∈ observed → current key = value
theorem property4885 : Property4885 := by simp [Property4885, method4885]
def Property4913 : Prop := ∀ spec stale, spec = none → method4913 spec stale = true
theorem property4913 : Property4913 := by intro spec stale h; subst spec; rfl
def Property4916 : Prop := ∀ build spec check, check build spec = true → method4916 build spec check = true
theorem property4916 : Property4916 := by simp [Property4916, method4916]
def Property4919 : Prop := ∀ facts, method4919 facts = false ↔
  facts.header = true ∧ facts.flags = true ∧ facts.identity = true ∧ facts.deps = true ∧
  facts.sources = true ∧ facts.checksum = true ∧ facts.prefs = true
theorem property4919 : Property4919 := by
  intro facts
  rcases facts with ⟨header,flags,identity,deps,sources,checksum,prefs⟩
  cases header <;> cases flags <;> cases identity <;> cases deps <;>
    cases sources <;> cases checksum <;> cases prefs <;> simp [method4919]
def Property5149 : Prop := ∀ source result, method5149 source = some result → source = some result
theorem property5149 : Property5149 := by simp [Property5149, method5149]
def Property5184 : Prop := ∀ source dirname result,
  method5184 source dirname = some result → ∃ file, source = some file ∧ result = dirname file
theorem property5184 : Property5184 := by
  intro source dirname result h
  cases source <;> simp_all [method5184]
def Property5190 : Prop := ∀ prepared, method5190 prepared = true
theorem property5190 : Property5190 := by simp [Property5190, method5190]
def Property5196 : Prop := ∀ path library, (method5196 path library).1 = path
theorem property5196 : Property5196 := by simp [Property5196, method5196]
def Property5199 : Prop := ∀ (α β : Type) (tuple : α × β), method5199 tuple = tuple.2
theorem property5199 : Property5199 := by simp [Property5199, method5199]
def Property5207 : Prop := ∀ (α β : Type) specialize f args,
  specialize f args = true → method5207 (α := α) (β := β) specialize f args = true
theorem property5207 : Property5207 := by simp [Property5207, method5207]
def Property5211 : Prop := ∀ (α : Type) check arg, check arg = true → method5211 (α := α) check arg = true
theorem property5211 : Property5211 := by simp [Property5211, method5211]
def Property5220 : Prop := ∀ allowed compile, method5220 allowed compile = true → allowed = true
theorem property5220 : Property5220 := by simp [Property5220, method5220]
def Property5225 : Prop := ∀ valid compile, method5225 valid compile = true → valid = true
theorem property5225 : Property5225 := by simp [Property5225, method5225]
def Property5234 : Prop := ∀ compile world, compile world = true → method5234 compile world = true
theorem property5234 : Property5234 := by simp [Property5234, method5234]
def Property5244 : Prop := ∀ methodMatches compile, method5244 methodMatches compile = true → methodMatches = true
theorem property5244 : Property5244 := by simp [Property5244, method5244]
def Property5248 : Prop := ∀ tupleMatches compile, method5248 tupleMatches compile = true → tupleMatches = true
theorem property5248 : Property5248 := by simp [Property5248, method5248]

end JuliaLean.Loading.Coverage.Cache