import JuliaLean.base.sysinfo
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.SysInfo

open JuliaLean.RuntimeCov

/-! ## Properties -/

theorem searchCandidates_found (join : String → String → String) (probe : String → Probe)
    (names : List String) : ∀ (dirs rest : List String) (p : String), rest ⊆ names →
    searchCandidates join probe names dirs rest = .ok (some p) →
    probe p = .found ∧ ∃ d ∈ dirs, ∃ n ∈ names, p = join d n
  | [], _, p, _, h => by simp [searchCandidates] at h
  | d :: ds, [], p, _, h => by
      rw [searchCandidates] at h
      obtain ⟨h1, d', hd', n, hn, hp⟩ :=
        searchCandidates_found join probe names ds names p (fun _ x => x) h
      exact ⟨h1, d', List.mem_cons_of_mem _ hd', n, hn, hp⟩
  | d :: ds, n :: ns, p, hsub, h => by
      rw [searchCandidates] at h
      have hn : n ∈ names := hsub (by simp)
      have hsub' : ns ⊆ names := fun x hx => hsub (List.mem_cons_of_mem _ hx)
      split at h
      · rename_i hpr
        simp at h; subst h
        exact ⟨hpr, d, by simp, n, hn, rfl⟩
      · exact searchCandidates_found join probe names (d :: ds) ns p hsub' h
      · exact searchCandidates_found join probe names (d :: ds) ns p hsub' h
      · simp at h
termination_by dirs rest => (dirs.length, rest.length)

/-- The documented behaviour of `base/sysinfo.jl`. -/
def SysInfoBodies : Prop :=
  -- `__init__`: an unset, unparsable or non-positive JULIA_CPU_THREADS falls
  -- back to the runtime count (with a warning for the latter two); a positive
  -- value is used; the effective count never exceeds CPU_THREADS.
  (∀ env tp a b u p w, (init env tp a b u p w).effectiveCpuThreads ≤ (init env tp a b u p w).cpuThreads) ∧
  (∀ s tp a b u p w n, tp s = some n → 0 < n → (init (some s) tp a b u p w).cpuThreads = n) ∧
  (∀ s tp a b u p w, (∀ n, tp s = some n → n ≤ 0) →
      (init (some s) tp a b u p w).cpuThreads = a ∧ (init (some s) tp a b u p w).warned = true) ∧
  (∀ tp a b u p w, (init none tp a b u p w).cpuThreads = a ∧ (init none tp a b u p w).warned = false) ∧
  (∀ env tp a b p w, (init env tp a b true p w).pagesize = p ∧ (init env tp a b false p w).pagesize = w) ∧
  -- `__init_build`: STDLIB ends in `julia/stdlib/vMAJOR.MINOR`.
  (∀ bd dr (ma mi : Nat), (initBuild bd dr ma mi).drop 2 =
      ["julia", "stdlib", "v" ++ toString ma ++ "." ++ toString mi]) ∧
  -- constructors copy every field
  (∀ m s u n sy i r, (mkCPUinfo m s u n sy i r).model = m ∧ (mkCPUinfo m s u n sy i r).speed = s) ∧
  (∀ u : UVCpuInfo, (ofUV u).model = u.model ∧ (ofUV u).user = u.user ∧ (ofUV u).irq = u.irq) ∧
  -- `show(::MIME"text/plain")` prints with the header and a four-space prefix
  (∀ rnd info, showPlain rnd info = showCpuinfo rnd info true "    ") ∧
  (∀ rnd info pfx, showCpuinfo rnd info false pfx = pfx ++ showCpuinfo rnd info false "") ∧
  (∀ (r : Int) (u : String), dcol r u = lpad (toString r) 9 ++ u) ∧
  -- `_cpu_summary`: up to nine CPUs give one row each, numbered from 1, with
  -- only the first carrying the header; ten or more give a single summary row.
  (∀ cpu i j, j - i < 9 → (cpuSummaryRows cpu i j).map (fun r => r.2.1) =
      (List.range ((cpu.drop (i - 1)).take (j - i + 1)).length).map (· == 0)) ∧
  (∀ cpu i j, 9 ≤ j - i → (cpuSummaryRows cpu i j).length = 1) ∧
  -- `cpu_summary`: an empty vector throws; otherwise the runs start at 1.
  cpuSummary [] = .error .boundsError ∧
  (∀ c cs, ∃ rs : Nat × List (Nat × Nat), cpuSummary (c :: cs) = .ok ((1, rs.1) :: rs.2)) ∧
  -- `cpu_info`: one record per libuv entry; no record keeps an empty or
  -- "unknown" model unless CPU_NAME is one; libuv errors throw.
  (∀ uv name cs, cpuInfo 0 uv name = .ok cs → cs.length = uv.length) ∧
  (∀ uv name cs, cpuInfo 0 uv name = .ok cs → ¬ name.isEmpty → name ≠ "unknown" →
      ∀ c ∈ cs, ¬ c.model.isEmpty ∧ c.model ≠ "unknown") ∧
  (∀ err uv name, err < 0 → cpuInfo err uv name = .error (.ioError err)) ∧
  (∀ s, sysimageTarget s = s) ∧
  -- `matched_sysimage_target`: index -1 selects the first entry.
  (∀ p ps, matchedSysimageTarget (-1) (p :: ps) = .ok p) ∧
  (∀ (i : Int) ps, 0 ≤ i → ps.length ≤ i.toNat → matchedSysimageTarget i ps = .error .boundsError) ∧
  (∀ e v, e < 0 → uptime e v = .error (.ioError e)) ∧
  (∀ a b c, (loadavg a b c).length = 3) ∧
  (∀ n, memQuery n = n) ∧
  -- `total_memory` never exceeds the physical memory and is the constraint when valid.
  (∀ c p, totalMemory c p ≤ p) ∧
  (∀ c p, 0 < c → c ≤ p → totalMemory c p = c) ∧
  (∀ c p, 0 < p → 0 < totalMemory c p) ∧
  (∀ buf t, getProcessTitle 0 buf = .ok t → 0 ∉ t ∧ t.length ≤ 512) ∧
  (∀ e, e < 0 → setProcessTitle e = .error (.ioError e)) ∧
  (∀ v, windowsVersionWin v = (v % 256, v / 256 % 256, v / 65536)) ∧
  windowsVersionOther = (0, 0, 0) ∧
  -- `which`: empty names give nothing; a returned path is an executable file
  -- built from a searched directory and a candidate name; a name with a
  -- directory searches only that directory.
  (∀ e, which e "" = .ok none) ∧
  (∀ e prog p, which e prog = .ok (some p) → e.probe p = .found) ∧
  (∀ e prog p, ¬ (e.dirname prog).isEmpty → which e prog = .ok (some p) →
      ∃ n, p = e.join (e.abspath (e.dirname prog)) n) ∧
  (∀ e prog p, e.iswindows = false → which e prog = .ok (some p) →
      ∃ d, p = e.join d (e.basename prog)) ∧
  (∀ (α : Type) e (f : α → String) x, whichAbstract e f x = which e (f x)) ∧
  -- `username` throws when the name is empty.
  (∀ n, n.isEmpty → username n = .error (.ioError UV_ENOENT)) ∧
  (∀ n, n.isEmpty = false → username n = .ok n)

theorem modelRuns_head (m : String) (ms : List String) (start : Nat) :
    ∃ k rs, modelRuns (m :: ms) start = (start, k) :: rs := by
  rw [modelRuns]; exact ⟨_, _, rfl⟩

theorem which_found (e : WhichEnv) (prog p : String) (h : which e prog = .ok (some p)) :
    e.probe p = .found ∧ (¬ (e.dirname prog).isEmpty → ∃ n, p = e.join (e.abspath (e.dirname prog)) n) ∧
    (e.iswindows = false → ∃ d, p = e.join d (e.basename prog)) := by
  unfold which at h
  by_cases hp : prog.isEmpty
  · simp [hp] at h
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨h1, d, hd, n, hn, hpj⟩ := searchCandidates_found _ _ _ _ _ _ (fun _ x => x) h
    refine ⟨h1, ?_, ?_⟩
    · intro hdir
      simp only [hdir, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hd
      exact ⟨n, by rw [hpj, hd]⟩
    · intro hw
      simp only [hw, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hn
      exact ⟨d, by rw [hpj, hn]⟩

theorem takeWhile_ne_zero (p : Nat → Bool) (h0 : p 0 = false) : ∀ l : List Nat, 0 ∉ l.takeWhile p
  | [] => by simp
  | x :: xs => by
    simp only [List.takeWhile]
    split
    · rename_i hx
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => by subst h; simp_all, takeWhile_ne_zero p h0 xs⟩
    · simp

theorem length_takeWhile_le' {α : Type} (p : α → Bool) : ∀ l : List α, (l.takeWhile p).length ≤ l.length
  | [] => by simp
  | x :: xs => by
    simp only [List.takeWhile]
    split
    · simp [length_takeWhile_le' p xs]
    · simp

theorem sysInfoBodies_proven : SysInfoBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro env tp a b u p w; exact Int.min_le_left _ _
  · intro s tp a b u p w n h hn
    have : ¬ n ≤ 0 := by omega
    simp [init, cpuThreadsOf, h, this]
  · intro s tp a b u p w h
    cases hs : tp s with
    | none => simp [init, cpuThreadsOf, hs]
    | some n => have := h n hs; simp [init, cpuThreadsOf, hs, this]
  · intro tp a b u p w; simp [init, cpuThreadsOf]
  · intro env tp a b p w; simp [init]
  · intro bd dr ma mi; rfl
  · intro m s u n sy i r; exact ⟨rfl, rfl⟩
  · intro u; exact ⟨rfl, rfl, rfl⟩
  · intro _ _; rfl
  · intro rnd info pfx; simp [showCpuinfo, String.append_assoc]
  · intro _ _; rfl
  · intro cpu i j h
    simp only [cpuSummaryRows, h, ↓reduceIte, List.map_map]
    rw [show ((fun r : CPUinfo × Bool × String => r.2.1) ∘
        fun p : Nat × CPUinfo => (p.2, p.1 == 0, "#" ++ toString (p.1 + 1) ++ " ")) =
        (fun k => k == 0) ∘ Prod.fst from rfl]
    rw [← List.map_map, List.map_fst_zip (by simp)]
  · intro cpu i j h
    have : ¬ j - i < 9 := by omega
    simp [cpuSummaryRows, this]
  · rfl
  · intro c cs
    obtain ⟨k, rs, h⟩ := modelRuns_head c.model (cs.map (·.model)) 1
    exact ⟨(k, rs), by simp [cpuSummary, h]⟩
  · intro uv name cs h
    simp [cpuInfo, uvError, bind, Except.bind, pure, Except.pure] at h
    subst h; simp
  · intro uv name cs h hn hu c hc
    simp [cpuInfo, uvError, bind, Except.bind, pure, Except.pure] at h
    subst h
    simp only [List.mem_map] at hc
    obtain ⟨u, _, rfl⟩ := hc
    split
    · first | exact ⟨hn, hu⟩ | simp_all
    · rename_i hm
      first | (simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hm; exact hm) | simp_all
  · intro err uv name h; simp [cpuInfo, uvError, h, bind, Except.bind]
  · intro _; rfl
  · intro p ps; simp [matchedSysimageTarget]
  · intro i ps h1 h2
    have hi : i ≠ -1 := by omega
    have : ¬ (1 ≤ i + 1 ∧ (i + 1).toNat ≤ ps.length) := by omega
    simp [matchedSysimageTarget, hi]; intro _; omega
  · intro e v h; simp [uptime, uvError, h, bind, Except.bind]
  · intro _ _ _; rfl
  · intro _; rfl
  · intro c p; unfold totalMemory; split <;> omega
  · intro c p h1 h2; simp [totalMemory, h1, h2]
  · intro c p hp; unfold totalMemory; split <;> omega
  · intro buf t h
    simp [getProcessTitle, uvError, bind, Except.bind, pure, Except.pure] at h
    subst h
    constructor
    · exact takeWhile_ne_zero _ (by simp) _
    · exact Nat.le_trans (length_takeWhile_le' _ _) (by simp only [List.length_take]; omega)
  · intro e h; simp [setProcessTitle, uvError, h]
  · intro _; rfl
  · rfl
  · intro e; simp [which]
  · intro e prog p h; exact (which_found e prog p h).1
  · intro e prog p hd h; exact (which_found e prog p h).2.1 hd
  · intro e prog p hw h; exact (which_found e prog p h).2.2 hw
  · intro _ _ _ _; rfl
  · intro n h; simp [username, h]
  · intro n h; simp [username, h]
end JuliaLean.RuntimeCov.SysInfo
end
