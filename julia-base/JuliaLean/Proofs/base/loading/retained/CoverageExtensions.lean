import JuliaLean.base.loading
import JuliaLean.Proofs.base.loading.retained.CoverageManifest

namespace JuliaLean.Loading.Coverage.Extensions

open JuliaLean.Loading.Coverage
open JuliaLean.Loading.Coverage.Early
def Property1969 : Prop := ∀ images debug bounds inline opt coverage,
  (method1969 images debug bounds inline opt coverage).path = none
theorem property1969 : Property1969 := by simp [Property1969, method1969]
def Property1971 : Prop := ∀ flags coverage,
  (method1971 flags coverage).debug < 4 ∧ (method1971 flags coverage).bounds < 4 ∧
  (method1971 flags coverage).opt < 4
theorem property1971 : Property1971 := by
  intro flags coverage
  simp [method1971]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
def Property1979 : Prop := ∀ flags, (method1979 flags).coverage = 0
theorem property1979 : Property1979 := by simp [Property1979, method1979, method1971]
def Property1980 : Prop := ∀ base images debug bounds inline opt coverage path,
  (method1980 base images debug bounds inline opt coverage path).coverage = 0 →
  (method1980 base images debug bounds inline opt coverage path).path = none
theorem property1980 : Property1980 := by
  intro base images debug bounds inline opt coverage path h
  simp only [method1980] at h ⊢
  split <;> simp_all
def Property2000 : Prop := ∀ flags coverage path,
  coverage = 0 → (method2000 flags coverage path).path = none
theorem property2000 : Property2000 := by
  intro flags coverage path h
  simp [method2000, method1980, method1971, select, h]
def Property2004 : Prop := ∀ code malloc tracked path,
  method2004 code malloc tracked = some path → code = 3 ∧ malloc = 0 ∧ path = tracked
theorem property2004 : Property2004 := by simp [Property2004, method2004]
def Property2012 : Prop := ∀ flags,
  flags.debug < 4 → flags.bounds < 4 → flags.opt < 4 → method2012 flags < 256
theorem property2012 : Property2012 := by
  intro flags hd hb ho
  simp only [method2012]
  split <;> split <;> omega
def Property2022 : Prop := ∀ flags,
  method2022 flags flags = []
theorem property2022 : Property2022 := by
  intro flags; simp [method2022]
def Property2036 : Prop := ∀ flags,
  (method2036 flags).length ≥ 1
theorem property2036 : Property2036 := by intro; simp [method2036]; split <;> simp
def Property2044 : Prop := ∀ runtime requested actual,
  runtime requested.coverage actual.coverage = true → method2044 runtime requested actual = true
theorem property2044 : Property2044 := by simp [Property2044, method2044]
def Property2053 : Prop := ∀ requested actual sysimage overlap,
  method2053 requested actual sysimage overlap = true → actual.coverage = 0 ∧ requested.path.isSome
theorem property2053 : Property2053 := by
  intro requested actual sysimage overlap h
  simp only [method2053, Bool.and_eq_true, Bool.not_eq_true] at h
  rcases h with ⟨⟨⟨⟨_, hactual⟩, hpath⟩, _⟩, _⟩
  have hactual' : actual.coverage = 0 := by simpa using hactual
  exact ⟨hactual', hpath⟩
def Property2062 : Prop := ∀ requested path coverage,
  method2062 requested path coverage = true → requested.path = path ∧ requested.coverage = coverage
theorem property2062 : Property2062 := by simp [Property2062, method2062]
def Property2067 : Prop := ∀ accept buildId, method2067 accept buildId = accept buildId
theorem property2067 : Property2067 := by simp [Property2067, method2067]
def Property2069 : Prop := ∀ accepted buildId,
  accepted buildId = true → method2069 accepted buildId = true
theorem property2069 : Property2069 := by simp [Property2069, method2069]
def Property2073 : Prop := ∀ tracked path root,
  tracked path root = true → method2073 tracked path root = true
theorem property2073 : Property2073 := by simp [Property2073, method2073]
def Property2096 : Prop := ∀ known dirs files,
  known = false → method2096 known dirs files = true
theorem property2096 : Property2096 := by simp [Property2096, method2096]
def Property2104 : Prop := ∀ flags, (method2104 flags).length ≥ 6
theorem property2104 : Property2104 := by intro; simp [method2104]
def Property2126 : Prop := ∀ shape path parsed result,
  method2126 shape path parsed = .ok result → shape = true ∧ path = true ∧ result = parsed
theorem property2126 : Property2126 := by simp [Property2126, method2126]
def Property2156 : Prop := ∀ name flags base ext enabled disabled,
  (method2156 name flags base ext enabled disabled).name = name
theorem property2156 : Property2156 := by simp [Property2156, method2156]
def Property2171 : Prop := ∀ count (parse : Nat → ImageTargetModel),
  (method2171 count parse).length = count
theorem property2171 : Property2171 := by simp [Property2171, method2171]
def Property2181 : Prop := ∀ (reflect : Unit → List Nat)
    (parse : List Nat → List ImageTargetModel) (target : ImageTargetModel),
  target ∈ method2181 reflect parse → target ∈ parse (reflect ())
theorem property2181 : Property2181 := by simp [Property2181, method2181]
def Property2186 : Prop := ∀ target, target.name ∈ method2186 target
theorem property2186 : Property2186 := by intro; simp [method2186]
def Property1475 : Prop := ∀ deps restore register moduleId didRegister,
  method1475 deps restore register = (.loaded moduleId, didRegister) →
  restore = .loaded moduleId ∧ didRegister = register
theorem property1475 : Property1475 := by
  intro deps restore register moduleId didRegister h
  by_cases hdeps : deps.any Option.isNone
  · simp [method1475, hdeps] at h
  · cases restore <;> simp_all [method1475, hdeps]
def Property1548 : Prop := ∀ moduleName parent compile recompile,
  moduleName ∈ method1548 moduleName parent compile recompile
theorem property1548 : Property1548 := by simp [Property1548, method1548]
def Property1571 : Prop := ∀ moduleName connector compile recompile,
  moduleName ∈ method1571 moduleName connector compile recompile
theorem property1571 : Property1571 := by simp [Property1571, method1571]
def Property1592 : Prop := ∀ parts index nearEnd project result,
  method1592 parts index nearEnd project = some result → project = some result
theorem property1592 : Property1592 := by
  intro parts index nearEnd project result h
  cases index <;> cases nearEnd <;> simp_all [method1592]
def Property1612 : Prop := ∀ restored roots docs inits path,
  (method1612 restored roots docs inits path).restored = restored ∧
  (method1612 restored roots docs inits path).cachePath = path
theorem property1612 : Property1612 := by simp [Property1612, method1612]
def Property1645 : Prop := ∀ (α β : Type) timing hasInit run report result,
  method1645 (α := α) (β := β) timing hasInit run report = some result → timing = true ∧ hasInit = true
theorem property1645 : Property1645 := by
  intro α β timing hasInit run report result h
  cases timing <;> cases hasInit <;> simp_all [method1645]
def Property1670 : Prop := ∀ extension callbacks, method1670 extension callbacks = ()
theorem property1670 : Property1670 := by simp [Property1670, method1670]
def Property1720 : Prop := ∀ present generating reentrant result,
  method1720 present generating reentrant result = true →
  present = true ∧ generating = false ∧ reentrant = false ∧ result = .ok true
theorem property1720 : Property1720 := by
  intro present generating reentrant result h
  cases present <;> cases generating <;> cases reentrant <;> cases result <;> simp_all [method1720]
  rename_i value
  cases value <;> simp_all [method1720]
def Property1753 : Prop := ∀ uuid located inserted,
  method1753 uuid located inserted = true → uuid = true ∧ located = true
theorem property1753 : Property1753 := by simp [Property1753, method1753]
def Property1761 : Prop := ∀ project identity extensions manifest stdlib,
  method1761 project identity extensions manifest stdlib = .project →
  project = true ∧ identity = true ∧ extensions = true
theorem property1761 : Property1761 := by simp [Property1761, method1761]
def Property1807 : Prop := ∀ requested entries (expanded : List (String × Nat)),
  method1807 requested entries = .ok expanded → expanded.length = requested.length
theorem property1807 : Property1807 := by
  intro requested entries expanded
  induction requested generalizing expanded with
  | nil => simp [method1807]
  | cons name rest ih =>
      simp only [method1807]
      cases hf : entries.find? (fun entry => entry.1 == name) with
      | none => simp [hf]
      | some pair =>
          rcases pair with ⟨entryName, values⟩
          cases values with
          | nil => simp [hf]
          | cons uuid tail =>
              cases tail with
              | cons next tail => simp [hf]
              | nil =>
                  cases hr : method1807 rest entries <;> simp [hf, hr]
                  intro h
                  cases h
                  simp [ih _ hr]
def Property1838 : Prop := ∀ known parent id triggers unloaded ext,
  method1838 known parent id triggers unloaded = some ext →
  known = false ∧ ext.total = triggers.length + 1
theorem property1838 : Property1838 := by simp [Property1838, method1838]
def Property1868 : Prop := ∀ incremental result,
  method1868 incremental result = .ok true ↔ result = .ok ()
theorem property1868 : Property1868 := by
  intro incremental result
  cases result with
  | ok value => cases value; simp [method1868]
  | error error => cases incremental <;> simp [method1868]
def Property1893 : Prop := ∀ extensions ext,
  ext ∈ method1893 extensions → ext ∈ extensions ∧ ext.remaining = 1
theorem property1893 : Property1893 := by
  intro extensions ext h
  simp [method1893, readyExtensions] at h
  exact h
def Property1925 : Prop := ∀ failed retry ext,
  ext ∈ method1925 failed retry ↔ ext ∈ failed ∧ retry ext = false
theorem property1925 : Property1925 := by simp [Property1925, method1925]
def Property1944 : Prop := ∀ (α β : Type) pkgId get parent extension result,
  method1944 (α := α) (β := β) pkgId get parent extension = some result →
  get (pkgId parent) extension = some result
theorem property1944 : Property1944 := by simp [Property1944, method1944]
def Property1945 : Prop := ∀ (α : Type) parent extension lookup uuid5 result,
  method1945 (α := α) parent extension lookup uuid5 = some result → parent.uuid.isSome
theorem property1945 : Property1945 := by
  intro α parent extension lookup uuid5 result h
  rcases parent with ⟨uuid, name⟩
  cases uuid <;> simp_all [method1945]
def Property2206 : Prop := ∀ candidates path,
  method2206 candidates = some path → (path, true) ∈ candidates
theorem property2206 : Property2206 := by
  intro candidates path h
  induction candidates with
  | nil => simp [method2206] at h
  | cons candidate rest ih =>
      rcases candidate with ⟨candidatePath, valid⟩
      cases valid <;> simp_all [method2206]
def Property2289 : Prop := ∀ path, method2289 path = true ↔ ∃ value, path = some value
theorem property2289 : Property2289 := by intro path; cases path <;> simp [method2289]
def Property2303 : Prop := ∀ path header includes,
  method2303 path header includes = .ok true →
  ∀ inc ∈ includes, inc.depotTagged = true ∧ (inc.sourceFile = true ∨ inc.tracksContent = true)
theorem property2303 : Property2303 := by
  intro path header includes h inc hmem
  cases path with
  | none => simp [method2303] at h
  | some value =>
      cases header <;> simp [method2303] at h
      exact h inc hmem
def Property2324 : Prop := ∀ header modules checksum low uuid result,
  method2324 header modules checksum low uuid = .ok result →
  result = (checksum * 2 ^ 64 + low, uuid)
theorem property2324 : Property2324 := by simp [Property2324, method2324]
def Property2344 : Prop := ∀ started searched moduleId,
  method2344 started searched = .loaded moduleId →
  started = some (.loaded moduleId) ∨ searched = .loaded moduleId
theorem property2344 : Property2344 := by
  intro started searched moduleId h; cases started <;> simp_all [method2344]
def Property2372 : Prop := ∀ header checks deps loaded moduleId,
  method2372 header checks deps loaded = .loaded moduleId →
  header = true ∧ checks = true ∧ loaded = .loaded moduleId
theorem property2372 : Property2372 := by
  intro header checks deps loaded moduleId h
  cases header <;> cases checks <;> simp_all [method2372]
  split at h <;> simp_all
def Property2411 : Prop := ∀ candidates result,
  method2411 candidates = some result → some result ∈ candidates
theorem property2411 : Property2411 := by
  intro candidates result h
  induction candidates with
  | nil => simp [method2411, firstSome] at h
  | cons candidate rest ih => cases candidate <;> simp_all [method2411, firstSome]
def Property2568 : Prop := ∀ owner current loaded chain,
  method2568 owner current loaded chain = .cycle → owner = some current ∨ current ∈ chain
theorem property2568 : Property2568 := by
  intro owner current loaded chain h
  cases owner with
  | none => cases loaded <;> simp_all [method2568]
  | some owner =>
      by_cases heq : owner = current <;> simp_all [method2568, heq]
def Property2638 : Prop := ∀ answers condition,
  method2638 answers = .wait condition → False
theorem property2638 : Property2638 := by
  intro answers condition h
  induction answers with
  | nil => simp [method2638] at h
  | cons answer rest ih => cases answer <;> simp_all [method2638]
def Property2653 : Prop := ∀ locks key loaded,
  key ∉ (method2653 locks key loaded).1
theorem property2653 : Property2653 := by simp [Property2653, method2653]

end JuliaLean.Loading.Coverage.Extensions