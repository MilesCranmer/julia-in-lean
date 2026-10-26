import JuliaLean.RuntimeCov.Common

/-!
`base/cpuid.jl` (module `Base.CPUID`): instruction-set feature sets, their
order, the feature-byte decoder, cross-architecture lookups, feature-name
listing, the `@cpu_supports` macro expansion and architecture-name
normalization.  Library queries (`jl_cpufeatures_*`, `jl_cpu_*`) are inputs.
-/

namespace JuliaLean.RuntimeCov.CpuId

open JuliaLean.RuntimeCov

/-- `ISA(features::Set{UInt32})`, base/cpuid.jl:15-17: the feature bits,
modelled as a duplicate-free list. -/
structure ISA where
  features : List Nat
  deriving DecidableEq, Repr

/-- `a.features <= b.features` for sets: `issubset`. -/
def subset (a b : List Nat) : Bool := a.all (fun x => b.contains x)

/-- `Base.:<=(a::ISA, b::ISA)`, base/cpuid.jl:20. -/
def le (a b : ISA) : Bool := subset a.features b.features
/-- `Base.:<(a::ISA, b::ISA)`, base/cpuid.jl:21: `⊊` on sets. -/
def lt (a b : ISA) : Bool := subset a.features b.features && !subset b.features a.features
/-- `Base.isless(a::ISA, b::ISA)`, base/cpuid.jl:22. -/
def isless (a b : ISA) : Bool := lt a b

/-- The bits pushed for one byte `b` at byte index `i`, base/cpuid.jl:34-39. -/
def byteBits (i b : Nat) : List Nat :=
  if b = 0 then [] else
    (List.range 8).filterMap fun bit => if (b >>> bit) % 2 ≠ 0 then some (i * 8 + bit) else none

/-- `_featurebytes_to_isa(buf)`, base/cpuid.jl:31-43. -/
def featurebytesToIsa (buf : List Nat) : ISA :=
  ⟨(List.range buf.length).flatMap fun i => byteBits i (buf.getD i 0)⟩

/-- `_cross_lookup_cpu(arch, name)`, base/cpuid.jl:52-61: the library reports
the buffer size for `arch` and the bytes written with their buffer. -/
def crossLookupCpu (nbytes : Nat) (lookup : Nat × List Nat) : ISA :=
  if nbytes = 0 then ⟨[]⟩
  else if lookup.1 = 0 then ⟨[]⟩
  else featurebytesToIsa lookup.2

/-- `_build_bit_to_name(arch)`, base/cpuid.jl:68-79: for each feature index the
library returns a name pointer (`none` = `C_NULL`) and a bit (negative = skip);
later assignments to the same bit win. -/
def buildBitToName : List (Option String × Int) → List (Nat × String) → List (Nat × String)
  | [], acc => acc
  | (none, _) :: rest, acc => buildBitToName rest acc
  | (some nm, bit) :: rest, acc =>
    if bit < 0 then buildBitToName rest acc
    else buildBitToName rest ((bit.toNat, nm) :: acc.filter (fun p => p.1 ≠ bit.toNat))

/-- `get(mapping, bit, "unknown_$bit")`. -/
def nameOf (mapping : List (Nat × String)) (bit : Nat) : String :=
  match mapping.find? (fun p => p.1 = bit) with
  | some p => p.2
  | none => "unknown_" ++ toString bit

/-- `feature_names(arch, isa)`, base/cpuid.jl:103-106: names sorted. -/
def featureNamesIsa (entries : List (Option String × Int)) (isa : ISA) : List String :=
  (isa.features.map (nameOf (buildBitToName entries []))).mergeSort (fun a b => decide (a ≤ b))

/-- `feature_names(arch, cpu)`, base/cpuid.jl:99-102. -/
def featureNamesCpu (entries : List (Option String × Int)) (nbytes : Nat) (lookup : Nat × List Nat) :
    List String :=
  featureNamesIsa entries (crossLookupCpu nbytes lookup)

/-- `feature_names(isa)` and `feature_names()`, base/cpuid.jl:97-98: host
architecture (and host ISA). -/
def featureNamesHostIsa (hostEntries : List (Option String × Int)) (isa : ISA) : List String :=
  featureNamesIsa hostEntries isa
def featureNamesHost (hostEntries : List (Option String × Int)) (hostIsa : ISA) : List String :=
  featureNamesHostIsa hostEntries hostIsa

/-- `_lookup_cpu(name)`, base/cpuid.jl:114-120: nonzero return means not found. -/
def lookupCpu (ret : Int) (buf : List Nat) : ISA :=
  if ret ≠ 0 then ⟨[]⟩ else featurebytesToIsa buf

/-- `_host_isa()`, base/cpuid.jl:127-132, and `cpu_isa()`, lines 309-311. -/
def hostIsa (buf : List Nat) : ISA := featurebytesToIsa buf
def cpuIsa (buf : List Nat) : ISA := hostIsa buf

/-- `_make_isa_list(arch, entries)`, base/cpuid.jl:137-147, with the cross
lookup for each CPU name as an input. -/
def makeIsaList (cross : String → ISA) (entries : List (String × String)) : List (String × ISA) :=
  entries.map fun (label, cpu) => if cpu.isEmpty then (label, ⟨[]⟩) else (label, cross cpu)

/-- `test_cpu_feature(feature)`, base/cpuid.jl:179: the runtime's answer. -/
def testCpuFeature (runtime : Nat → Bool) (feature : Nat) : Bool := runtime feature

/-- `eachsplit(s, ','; keepempty=false)`. -/
def splitNonempty (s : String) : List String :=
  (s.splitOn ",").filter (fun t => !t.isEmpty)

/-- `_cpu_model_features(name)`, base/cpuid.jl:192-196. -/
def cpuModelFeatures (result : Option String) : Option (List String) :=
  result.map splitNonempty

/-- A macro argument of `@cpu_supports`. -/
inductive MacroArg where
  | sym (s : Sym)
  | quoteSym (s : Sym)
  | quoteOther
  | str (s : String)
  | other (reprText : String)

/-- `_cpu_supports_name(x)`, base/cpuid.jl:198-203. -/
def cpuSupportsName : MacroArg → Rt Sym
  | .sym s => .ok s
  | .quoteSym s => .ok s
  | .str s => .ok s
  | .quoteOther => .error (.errorException "@cpu_supports: expected a literal name")
  | .other r => .error (.errorException ("@cpu_supports: expected a literal name (Symbol or String), got " ++ r))

/-- `normalize_arch(arch)`, base/cpuid.jl:286-302, with Unicode `lowercase` as an input. -/
def normalizeArch (lower : String → String) (arch : String) : String :=
  let a := lower arch
  if a ∈ ["amd64"] then "x86_64"
  else if a ∈ ["i386", "i486", "i586"] then "i686"
  else if a ∈ ["armv6"] then "armv6l"
  else if a ∈ ["arm", "armv7", "armv8", "armv8l"] then "armv7l"
  else if a ∈ ["arm64"] then "aarch64"
  else if a ∈ ["ppc64le"] then "powerpc64le"
  else a

/-- `_CPU_SUPPORTS_ARCHES`, base/cpuid.jl:182. -/
def supportsArches : List Sym := ["x86_64", "aarch64", "riscv64"]

/-- The expansion of `@cpu_supports`. -/
inductive Expansion where
  | constFalse
  | query (q : List String)
  deriving DecidableEq, Repr

/-- Deduplicate keeping first occurrences (`unique!`). -/
def dedup : List String → List String
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· ≠ x)

/-- Map `_cpu_supports_name` over arguments, stopping at the first error. -/
def mapNames : List MacroArg → Rt (List Sym)
  | [] => .ok []
  | a :: as => do let n ← cpuSupportsName a; let ns ← mapNames as; pure (n :: ns)

/-- Expand each name to features (`known` codegen features, else CPU-model features). -/
def expandFeatures (known : Sym → Bool) (model : Sym → Option (List String)) :
    List Sym → Rt (List String)
  | [] => .ok []
  | n :: ns =>
    if known n then do let r ← expandFeatures known model ns; pure (n :: r)
    else match model n with
      | none => .error (.errorException ("@cpu_supports: `" ++ n ++ "` is neither a hardware feature nor a CPU model"))
      | some [] => .error (.errorException ("@cpu_supports: CPU model `" ++ n ++ "` has no features to test"))
      | some fs => do let r ← expandFeatures known model ns; pure (fs ++ r)

/-- `@cpu_supports arch names...`, base/cpuid.jl:258-283. The query symbol is
the sorted, deduplicated feature list joined by commas; it is kept as the
sorted list. -/
def cpuSupports (lower : String → String) (hostArch : Sym) (known : Sym → Bool)
    (model : Sym → Option (List String)) (args : List MacroArg) : Rt Expansion :=
  match args with
  | [] | [_] => .error (.errorException "@cpu_supports: usage is `@cpu_supports <arch> <name>...`")
  | a0 :: rest => do
    let archArg ← cpuSupportsName a0
    let arch := normalizeArch lower archArg
    if arch ∉ supportsArches then
      .error (.errorException ("@cpu_supports: first argument must be one of x86_64, aarch64, riscv64, got `" ++ archArg ++ "`"))
    else do
      let names ← mapNames rest
      if arch ≠ hostArch then pure .constFalse
      else do
        let features ← expandFeatures known model names
        pure (.query ((dedup features).mergeSort (fun a b => decide (a ≤ b))))

/-! ## Properties -/

/-- The documented and invariant behaviour of `base/cpuid.jl`. Every decoded
feature bit is below `8 * length(buf)` and comes from a set bit; empty lookups
give the empty ISA; `feature_names` returns one name per feature as a
permutation of the mapped names; ISA lists keep their labels; CPU-supports
names accept exactly literal symbols and strings; normalization maps the
documented aliases; `@cpu_supports` errors on unknown architectures and folds
to `false` on other hosts. -/
def CpuIdBodies : Prop :=
  (∀ (buf : List Nat) (n : Nat), n ∈ (featurebytesToIsa buf).features →
      n < 8 * buf.length ∧ (buf.getD (n / 8) 0 >>> (n % 8)) % 2 ≠ 0) ∧
  (∀ (lookup : Nat × List Nat), crossLookupCpu 0 lookup = ⟨[]⟩) ∧
  (∀ (n : Nat) (buf : List Nat), n ≠ 0 → crossLookupCpu n (0, buf) = ⟨[]⟩) ∧
  (∀ (ret : Int) (buf : List Nat), ret ≠ 0 → lookupCpu ret buf = ⟨[]⟩) ∧
  (∀ (buf : List Nat), lookupCpu 0 buf = hostIsa buf ∧ cpuIsa buf = hostIsa buf) ∧
  (∀ (entries : List (Option String × Int)) (isa : ISA),
      (featureNamesIsa entries isa).length = isa.features.length ∧
      (featureNamesIsa entries isa).Perm (isa.features.map (nameOf (buildBitToName entries [])))) ∧
  (∀ (entries : List (Option String × Int)) (n : Nat) (lk : Nat × List Nat),
      featureNamesCpu entries n lk = featureNamesIsa entries (crossLookupCpu n lk)) ∧
  (∀ (e : List (Option String × Int)) (isa : ISA),
      featureNamesHost e isa = featureNamesIsa e isa) ∧
  (∀ (cross : String → ISA) (entries : List (String × String)),
      (makeIsaList cross entries).map Prod.fst = entries.map Prod.fst) ∧
  (∀ (rt : Nat → Bool) (f : Nat), testCpuFeature rt f = rt f) ∧
  (∀ r : Option String, cpuModelFeatures r = none ↔ r = none) ∧
  (∀ x : MacroArg, (∃ s, cpuSupportsName x = .ok s) ↔
      (match x with | .sym _ | .quoteSym _ | .str _ => True | _ => False)) ∧
  (∀ (lower : String → String) (s : String), lower s = "amd64" → normalizeArch lower s = "x86_64") ∧
  (∀ (lower : String → String) (s : String), lower s = "arm64" → normalizeArch lower s = "aarch64") ∧
  (∀ (lower : String → String) (hostArch : Sym) known model (a0 : MacroArg) (rest : List MacroArg)
      (s : Sym), rest ≠ [] → cpuSupportsName a0 = .ok s →
      normalizeArch lower s ∉ supportsArches →
      ∃ e, cpuSupports lower hostArch known model (a0 :: rest) = .error e) ∧
  (∀ (lower : String → String) (hostArch : Sym) known model (a0 : MacroArg) (rest : List MacroArg)
      (s : Sym) (ns : List Sym), rest ≠ [] → cpuSupportsName a0 = .ok s →
      normalizeArch lower s ∈ supportsArches → normalizeArch lower s ≠ hostArch →
      mapNames rest = .ok ns →
      cpuSupports lower hostArch known model (a0 :: rest) = .ok .constFalse) ∧
  (∀ (lower : String → String) (hostArch : Sym) known model (a : MacroArg),
      ∃ e, cpuSupports lower hostArch known model [a] = .error e)

theorem byteBits_mem (i b n : Nat) (h : n ∈ byteBits i b) :
    i * 8 ≤ n ∧ n < i * 8 + 8 ∧ (b >>> (n - i * 8)) % 2 ≠ 0 := by
  unfold byteBits at h
  split at h
  · simp at h
  · simp only [List.mem_filterMap, List.mem_range] at h
    obtain ⟨bit, hbit, hs⟩ := h
    split at hs
    · simp at hs; subst hs
      refine ⟨by omega, by omega, ?_⟩
      have : i * 8 + bit - i * 8 = bit := by omega
      rw [this]; assumption
    · simp at hs

theorem featurebytes_mem (buf : List Nat) (n : Nat) (h : n ∈ (featurebytesToIsa buf).features) :
    n < 8 * buf.length ∧ (buf.getD (n / 8) 0 >>> (n % 8)) % 2 ≠ 0 := by
  simp only [featurebytesToIsa, List.mem_flatMap, List.mem_range] at h
  obtain ⟨i, hi, hn⟩ := h
  obtain ⟨h1, h2, h3⟩ := byteBits_mem i _ n hn
  have hdiv : n / 8 = i := by omega
  have hmod : n % 8 = n - i * 8 := by omega
  refine ⟨by omega, ?_⟩
  rw [hdiv, hmod]; exact h3

theorem makeIsaList_fst (cross : String → ISA) : ∀ entries : List (String × String),
    (makeIsaList cross entries).map Prod.fst = entries.map Prod.fst
  | [] => rfl
  | (l, c) :: rest => by
      show (if c.isEmpty then (l, (⟨[]⟩ : ISA)) else (l, cross c)).1 ::
          (makeIsaList cross rest).map Prod.fst = l :: rest.map Prod.fst
      rw [makeIsaList_fst cross rest]
      split <;> rfl

theorem cpuIdBodies_proven : CpuIdBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro buf n h; exact featurebytes_mem buf n h
  · intro lookup; simp [crossLookupCpu]
  · intro n buf hn; simp [crossLookupCpu, hn]
  · intro ret buf h; simp [lookupCpu, h]
  · intro buf; exact ⟨by simp [lookupCpu, hostIsa], rfl⟩
  · intro entries isa
    refine ⟨?_, ?_⟩
    · simp [featureNamesIsa, List.length_mergeSort]
    · exact List.mergeSort_perm _ _
  · intro _ _ _; rfl
  · intro _ _; rfl
  · intro cross entries; exact makeIsaList_fst cross entries
  · intro _ _; rfl
  · intro r; cases r <;> simp [cpuModelFeatures]
  · intro x; cases x <;> simp [cpuSupportsName]
  · intro lower s h; simp [normalizeArch, h]
  · intro lower s h; simp [normalizeArch, h]
  · intro lower hostArch known model a0 rest s hrest hs hn
    cases rest with
    | nil => exact absurd rfl hrest
    | cons r1 rs =>
      simp only [cpuSupports, hs, bind, Except.bind]
      simp [hn]
  · intro lower hostArch known model a0 rest s ns hrest hs hin hne hns
    cases rest with
    | nil => exact absurd rfl hrest
    | cons r1 rs =>
      simp only [cpuSupports, hs, bind, Except.bind]
      simp [hin, hns, hne]
      try rfl
  · intro lower hostArch known model a; exact ⟨_, rfl⟩

/-- The `isless` contract ("a fixed total order"): incomparability under
`isless(::ISA, ::ISA)` is transitive, as `sort` and other ordered algorithms
require of their `lt`. -/
def IsaIslessStrictWeak : Prop :=
  ∀ x y z : ISA, isless x y = false → isless y x = false →
    isless y z = false → isless z y = false → isless x z = false

/-- `{1}` and `{3}` are incomparable, `{3}` and `{1,2}` are incomparable, yet
`{1} ⊊ {1,2}`. -/
theorem isaIslessStrictWeak_refuted : ¬ IsaIslessStrictWeak := by
  intro h
  have := h ⟨[1]⟩ ⟨[3]⟩ ⟨[1, 2]⟩ (by decide) (by decide) (by decide) (by decide)
  revert this; decide

end JuliaLean.RuntimeCov.CpuId
