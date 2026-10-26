import JuliaLean.RuntimeCov.Common

/-!
`base/sysinfo.jl` (module `Base.Sys`): runtime initialization of the CPU and
path globals, `CPUinfo` and its printing and summaries, libuv system queries,
`which` and `username`.  libuv and runtime answers are inputs.
-/

namespace JuliaLean.RuntimeCov.SysInfo

open JuliaLean.RuntimeCov

/-- The globals set by `Sys.__init__`. -/
structure SysGlobals where
  cpuThreads : Int
  effectiveCpuThreads : Int
  warned : Bool
  pagesize : Int
  deriving DecidableEq, Repr

/-- `Sys.__init__()`, base/sysinfo.jl:155-177: `env` is `ENV["JULIA_CPU_THREADS"]`
if set, `tryparse` is `tryparse(Int, _)`, `jlCpuThreads`/`jlEffective` the
runtime counts, `unixPage`/`winGranularity` the two page-size queries. -/
def cpuThreadsOf (env : Option String) (tryparse : String → Option Int) (jlCpuThreads : Int) :
    Int × Bool :=
  match env with
  | some s =>
    match tryparse s with
    | some n => if n ≤ 0 then (jlCpuThreads, true) else (n, false)
    | none => (jlCpuThreads, true)
  | none => (jlCpuThreads, false)

def init (env : Option String) (tryparse : String → Option Int)
    (jlCpuThreads jlEffective : Int) (isunix : Bool) (unixPage winGranularity : Int) : SysGlobals :=
  let r := cpuThreadsOf env tryparse jlCpuThreads
  { cpuThreads := r.1, effectiveCpuThreads := min r.1 jlEffective, warned := r.2,
    pagesize := if isunix then unixPage else winGranularity }

/-- `Sys.__init_build()`, base/sysinfo.jl:180-185: the path components passed to
`abspath(BINDIR, DATAROOTDIR, "julia", "stdlib", vers)`. -/
def initBuild (bindir datarootdir : String) (major minor : Nat) : List String :=
  [bindir, datarootdir, "julia", "stdlib", "v" ++ toString major ++ "." ++ toString minor]

/-- `Sys.CPUinfo`, base/sysinfo.jl:211-222 (inner constructor at line 221). -/
structure CPUinfo where
  model : String
  speed : JInt .i32
  user : JInt .u64
  nice : JInt .u64
  sys : JInt .u64
  idle : JInt .u64
  irq : JInt .u64

/-- `CPUinfo(model,speed,u,n,s,id,ir)`, base/sysinfo.jl:221. -/
def mkCPUinfo (model : String) (speed : JInt .i32) (u n s id ir : JInt .u64) : CPUinfo :=
  ⟨model, speed, u, n, s, id, ir⟩

/-- `UV_cpu_info_t` with its model C string already read. -/
structure UVCpuInfo where
  model : String
  speed : JInt .i32
  user : JInt .u64
  nice : JInt .u64
  sys : JInt .u64
  idle : JInt .u64
  irq : JInt .u64

/-- `CPUinfo(info::UV_cpu_info_t)`, base/sysinfo.jl:223-225. -/
def ofUV (i : UVCpuInfo) : CPUinfo := ⟨i.model, i.speed, i.user, i.nice, i.sys, i.idle, i.irq⟩

/-- `d(i, unit=unit)`, base/sysinfo.jl:239, given the rounded integer `round(Int64, i)`. -/
def dcol (rounded : Int) (unit : String := " s  ") : String := lpad (toString rounded) 9 ++ unit

/-- `_show_cpuinfo(io, info, header, prefix)`, base/sysinfo.jl:229-244. `round`
maps a millisecond count to `round(Int64, ms / 1000)`. -/
def showCpuinfo (round : JInt .u64 → Int) (info : CPUinfo) (header : Bool) (pfx : String) : String :=
  (if header then
      info.model ++ ": \n" ++ String.ofList (List.replicate pfx.length ' ') ++
      "    " ++ lpad "speed" 5 ++ "    " ++ lpad "user" 9 ++ "    " ++ lpad "nice" 9 ++ "    " ++
      lpad "sys" 9 ++ "    " ++ lpad "idle" 9 ++ "    " ++ lpad "irq" 9 ++ "\n"
    else "") ++
  pfx ++ lpad (toString info.speed.val) 5 ++ " MHz  " ++
    dcol (round info.user) ++ dcol (round info.nice) ++ dcol (round info.sys) ++
    dcol (round info.idle) ++ dcol (round info.irq)

/-- `show(io, ::MIME"text/plain", info::CPUinfo)`, base/sysinfo.jl:246. -/
def showPlain (round : JInt .u64 → Int) (info : CPUinfo) : String :=
  showCpuinfo round info true "    "

/-- The aggregate built by `_cpu_summary` for a run of ten or more CPUs,
base/sysinfo.jl:257-268 (`Int32` and `UInt64` additions wrap). -/
def summaryOf (run : List CPUinfo) (model : String) : CPUinfo :=
  let z64 : JInt .u64 := JInt.lit .u64 0
  let s := run.foldl (fun (acc c : CPUinfo) =>
      { acc with speed := acc.speed + c.speed, user := acc.user + c.user, nice := acc.nice + c.nice,
                 sys := acc.sys + c.sys, idle := acc.idle + c.idle, irq := acc.irq + c.irq })
    (⟨model, JInt.lit .i32 0, z64, z64, z64, z64, z64⟩ : CPUinfo)
  { s with speed := JInt.lit .i32 (s.speed.val / (run.length : Int)) }

/-- What `_cpu_summary(io, cpu, i, j)` prints, base/sysinfo.jl:248-271: one row
per CPU numbered from `#1` with a header only on the first, or one `#1-count`
summary row. Rows are given as `(info, header, prefix)`. -/
def cpuSummaryRows (cpu : List CPUinfo) (i j : Nat) : List (CPUinfo × Bool × String) :=
  let run := (cpu.drop (i - 1)).take (j - i + 1)
  if j - i < 9 then
    ((List.range run.length).zip run).map fun p => (p.2, p.1 == 0, "#" ++ toString (p.1 + 1) ++ " ")
  else
    [(summaryOf run (run.headD ⟨"", JInt.lit .i32 0, JInt.lit .u64 0, JInt.lit .u64 0,
        JInt.lit .u64 0, JInt.lit .u64 0, JInt.lit .u64 0⟩).model, true,
      "#1-" ++ toString run.length ++ " ")]

/-- Maximal runs of consecutive equal models, as 1-based inclusive `(first, last)`. -/
def modelRuns : List String → Nat → List (Nat × Nat)
  | [], _ => []
  | m :: ms, start =>
    let k := (ms.takeWhile (· == m)).length
    (start, start + k) :: modelRuns (ms.drop k) (start + k + 1)
termination_by l => l.length
decreasing_by simp; omega

/-- `cpu_summary(io, cpu)`, base/sysinfo.jl:284-295: the `(first, last)` ranges
handed to `_cpu_summary`; `cpu[1]` throws a `BoundsError` on an empty vector. -/
def cpuSummary (cpu : List CPUinfo) : Rt (List (Nat × Nat)) :=
  match cpu with
  | [] => .error .boundsError
  | c :: cs =>
    -- the loop at lines 287-293 compares each model with the current run's model
    .ok (modelRuns (c.model :: cs.map (·.model)) 1)

/-- `cpu_info()`, base/sysinfo.jl:309-324. -/
def cpuInfo (err : Int) (uv : List UVCpuInfo) (cpuName : String) : Rt (List CPUinfo) := do
  uvError err
  pure (uv.map fun u =>
    let c := ofUV u
    if c.model.isEmpty || c.model == "unknown" then { c with model := cpuName } else c)

/-- `sysimage_target()`, base/sysinfo.jl:342-344. -/
def sysimageTarget (runtime : String) : String := runtime

/-- `matched_sysimage_target()`, base/sysinfo.jl:359-365: `parts` is
`split(sysimage_target(), ";")` and the result is `parts[idx]`. -/
def matchedSysimageTarget (idx : Int) (parts : List String) : Rt String :=
  let m : Int := if idx = -1 then 1 else idx + 1
  if 1 ≤ m ∧ m.toNat ≤ parts.length then .ok (parts.getD (m.toNat - 1) "") else .error .boundsError

/-- `uptime()`, base/sysinfo.jl:372-377, and the other libuv value queries. -/
def uptime (err : Int) (value : Float) : Rt Float := do uvError err; pure value
/-- `loadavg()`, base/sysinfo.jl:384-388: the three-element vector filled by libuv. -/
def loadavg (a b c : Float) : List Float := [a, b, c]
/-- `free_physical_memory()`, `total_physical_memory()`, `free_memory()`,
`maxrss()`, base/sysinfo.jl:396, 404, 411, 460: the runtime's `UInt64`/`Csize_t`. -/
def memQuery (runtime : Nat) : Nat := runtime

/-- `total_memory()`, base/sysinfo.jl:420-428. -/
def totalMemory (constrained physical : Nat) : Nat :=
  if 0 < constrained ∧ constrained ≤ physical then constrained else physical

/-- `get_process_title()`, base/sysinfo.jl:435-440: the 512-byte buffer read as
a C string. -/
def getProcessTitle (err : Int) (buf : List Nat) : Rt (List Nat) := do
  uvError err
  pure ((buf.take 512).takeWhile (· ≠ 0))

/-- `set_process_title(title)`, base/sysinfo.jl:447-450. -/
def setProcessTitle (err : Int) : Rt Unit := uvError err

/-- `windows_version()` on Windows, base/sysinfo.jl:463-466: fields of `GetVersion()`. -/
def windowsVersionWin (verinfo : Nat) : Nat × Nat × Nat :=
  (verinfo % 256, (verinfo / 256) % 256, verinfo / 65536)
/-- `windows_version()` elsewhere, base/sysinfo.jl:468: `v"0.0"`. -/
def windowsVersionOther : Nat × Nat × Nat := (0, 0, 0)

/-- The file-system facts `which` consults for one candidate path. -/
inductive Probe where
  | found
  | notFound
  | eacces
  | otherError (code : Int)
  deriving DecidableEq, Repr

/-- The candidate search of `which`, base/sysinfo.jl:535-557: the first
directory/name combination that is an executable file, skipping permission
errors and rethrowing other I/O errors. `rest` holds the names still to try
in the current directory. -/
def searchCandidates (join : String → String → String) (probe : String → Probe)
    (names : List String) : List String → List String → Rt (Option String)
  | [], _ => .ok none
  | _ :: ds, [] => searchCandidates join probe names ds names
  | d :: ds, n :: ns =>
    match probe (join d n) with
    | .found => .ok (some (join d n))
    | .notFound => searchCandidates join probe names (d :: ds) ns
    | .eacces => searchCandidates join probe names (d :: ds) ns
    | .otherError c => .error (.ioError c)
termination_by dirs rest => (dirs.length, rest.length)

/-- The host and path primitives `which` uses. -/
structure WhichEnv where
  iswindows : Bool
  basename : String → String
  dirname : String → String
  extension : String → String
  abspath : String → String
  join : String → String → String
  pwd : String
  pathEnv : Option String
  probe : String → Probe

/-- `which(program_name::String)`, base/sysinfo.jl:495-561. -/
def which (e : WhichEnv) (programName : String) : Rt (Option String) :=
  if programName.isEmpty then .ok none else
  let base := e.basename programName
  let names :=
    if e.iswindows then
      (if !(e.extension base).isEmpty then [base] else []) ++ [base ++ ".exe", base ++ ".com"]
    else [base]
  let dir := e.dirname programName
  let dirs :=
    if dir.isEmpty then
      let sep := if e.iswindows then ";" else ":"
      let ds := ((e.pathEnv.getD "").splitOn sep).map e.abspath
      if e.iswindows then e.pwd :: ds else ds
    else [e.abspath dir]
  searchCandidates e.join e.probe names dirs names

/-- `which(program_name::AbstractString)`, base/sysinfo.jl:562: converts to `String`. -/
def whichAbstract (e : WhichEnv) (toStr : α → String) (p : α) : Rt (Option String) :=
  which e (toStr p)

/-- `username()`, base/sysinfo.jl:581-585. -/
def username (pwName : String) : Rt String :=
  if pwName.isEmpty then .error (.ioError UV_ENOENT) else .ok pwName

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
