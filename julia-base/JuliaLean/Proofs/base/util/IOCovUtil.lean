import JuliaLean.base.util
import JuliaLean.Proofs.base.io.IOCovCommon
import JuliaLean.Proofs.stdlib.CRC32c.src.CRC32c.CrcProofs


section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Util

open JuliaLean JuliaLean.IOCov

def ColorCorrect : Prop :=
  -- without color, printstyled prints exactly what print would
  (∀ t c st, withOutputColor t c false st = t) ∧
  (∀ t iscolor st c, printstyled t iscolor st c = withOutputColor t c iscolor st) ∧
  -- a single nonempty line is enclosed in the enable and disable sequences
  (∀ (t : List Char) c st, t ≠ [] → '\n' ∉ t →
      outputColorString t c st = (enableAnsi st (normColor st c)).toList ++ t ++
        (disableAnsi st (normColor st c)).toList) ∧
  -- `:nothing` with no flags leaves the text unchanged
  (∀ t : List Char, outputColorString t (.sym "nothing") {} = t) ∧
  -- integer colors 0-255 use the 256-color escape
  (∀ n : Int, 0 ≤ n → n ≤ 255 → enableCode (.int n) = "\x1b[38;5;" ++ toString n ++ "m")

theorem splitNl_ne_nil (t : List Char) : splitNl t ≠ [] := by
  cases t with
  | nil => simp [splitNl]
  | cons c cs =>
    simp only [splitNl]
    split
    · simp
    · split <;> simp

theorem intercalate_splitNl (t : List Char) : List.intercalate ['\n'] (splitNl t) = t := by
  induction t with
  | nil => rfl
  | cons c cs ih =>
    simp only [splitNl]
    split
    · rename_i h; subst h
      cases hs : splitNl cs with
      | nil => exact absurd hs (splitNl_ne_nil cs)
      | cons w ws => rw [hs] at ih; simp [List.intercalate_cons_cons, ih]
    · cases hs : splitNl cs with
      | nil => exact absurd hs (splitNl_ne_nil cs)
      | cons w ws =>
        rw [hs] at ih
        cases ws with
        | nil => simp at ih ⊢; exact ih
        | cons w2 ws2 => simp [List.intercalate_cons_cons] at ih ⊢; exact ih

theorem splitNl_single (t : List Char) (h : '\n' ∉ t) : splitNl t = [t] := by
  induction t with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '\n' := fun e => h (e ▸ List.mem_cons_self ..)
    have := ih (fun m => h (List.mem_cons_of_mem _ m))
    simp [splitNl, hc, this]

theorem intercalate_splitOn_id (t : List Char) :
    List.intercalate ['\n'] ((splitNl t).map fun line => if line.isEmpty then [] else line) = t := by
  have : (fun line : List Char => if line.isEmpty then [] else line) = id := by
    funext l; cases l <;> rfl
  rw [this, List.map_id]
  exact intercalate_splitNl t

theorem colorCorrect : ColorCorrect := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro t c st ht hn
    have : splitNl t = [t] := splitNl_single t hn
    cases t with
    | nil => exact absurd rfl ht
    | cons x xs => simp [outputColorString, this]
  · intro t
    have he : (enableAnsi {} (normColor {} (.sym "nothing"))).toList = [] := by decide
    have hd : (disableAnsi {} (normColor {} (.sym "nothing"))).toList = [] := by decide
    simp only [outputColorString, he, hd, List.nil_append, List.append_nil]
    exact intercalate_splitOn_id t
  · intro n h1 h2; simp [enableCode, h1, h2]

def JuliaCmdCorrect : Prop :=
  (∀ j c i o, (juliaCmd j c i o).take 4 = [j, "-C", c, "-J" ++ i]) ∧
  (∀ o : Opts, "-g" ++ toString o.debugLevel ∈ addflags o) ∧
  (∀ o : Opts, o.checkBounds = 1 → "--check-bounds=yes" ∈ addflags o) ∧
  (∀ o : Opts, o.checkBounds = 2 → "--check-bounds=no" ∈ addflags o) ∧
  (∀ o : Opts, o.optLevel ≠ 2 → "-O" ++ toString o.optLevel ∈ addflags o) ∧
  (∀ d, juliaExename d = if d then "julia-debug" else "julia")

theorem juliaCmdCorrect : JuliaCmdCorrect := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_, fun _ => rfl⟩
  · intro o; simp [addflags]
  · intro o h; simp [addflags, h]
  · intro o h; simp [addflags, h]
  · intro o h; simp [addflags, h]

def SecurezeroCorrect : Prop :=
  (∀ a, (securezero a).length = a.length ∧ ∀ x ∈ securezero a, x = 0) ∧
  (∀ mem p len sz, p + len * sz ≤ mem.length →
      (unsafeSecurezero mem p len sz).length = mem.length ∧
      ((unsafeSecurezero mem p len sz).drop p).take (len * sz) = List.replicate (len * sz) 0 ∧
      (unsafeSecurezero mem p len sz).take p = mem.take p ∧
      (unsafeSecurezero mem p len sz).drop (p + len * sz) = mem.drop (p + len * sz)) ∧
  (∀ mem p len, unsafeSecurezeroVoid mem p len = unsafeSecurezero mem p len 1)

theorem securezeroCorrect : SecurezeroCorrect := by
  refine ⟨fun a => ⟨by simp [securezero], fun x hx => by simp [securezero] at hx; exact hx.2.symm⟩,
    ?_, fun _ _ _ => rfl⟩
  intro mem p len sz h
  have hm : min (len * sz) (mem.length - p) = len * sz := by omega
  have hp : (mem.take p).length = p := by simp; omega
  have hr : (List.replicate (len * sz) (0 : UInt8)).length = len * sz := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [unsafeSecurezero, hm]; omega
  · simp only [unsafeSecurezero, hm, List.append_assoc]
    rw [List.drop_left' hp, List.take_left' hr]
  · simp only [unsafeSecurezero, hm, List.append_assoc]
    rw [List.take_left' hp]
  · simp only [unsafeSecurezero, hm]
    have : (mem.take p ++ List.replicate (len * sz) 0).length = p + len * sz := by simp; omega
    rw [List.drop_left' this]

/-- The comment at line 381: Backspace deletes the last character typed. -/
def GetpassBackspace : Prop :=
  ∀ (pre : List Nat) (c : Nat), pre ≠ [] → (∀ b ∈ pre, 32 ≤ b ∧ b ≤ 126) → 32 ≤ c → c ≤ 126 →
    getpass (pre ++ [8, c, 13]) = .ok (pre.dropLast ++ [c])

theorem getpassBackspace_refuted : ¬ GetpassBackspace := by
  intro h
  have := h [97, 98] 99 (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- Documented: the result contains the secret typed, here any bytes other than ASCII
control bytes and the terminators. -/
def GetpassBytes : Prop :=
  ∀ s : List Nat, (∀ b ∈ s, 32 ≤ b ∧ b < 256 ∧ b ≠ 127 ∧ b ≠ 0xff) → s.length ≤ 128 →
    getpass (s ++ [13]) = .ok s

theorem getpassBytes_refuted : ¬ GetpassBytes := by
  intro h
  have := h [0xd1, 0x80] (by decide) (by decide)
  revert this; decide

theorem getpassLoop_ascii (s : List Nat) : ∀ (fuel : Nat) (acc : List Nat) (plen : Nat),
    (∀ b ∈ s, 32 ≤ b ∧ b ≤ 126) → s.length + 1 < fuel + 1 → plen < 128 →
    getpassLoop fuel (s ++ [13]) acc plen = .ok (acc ++ s) := by
  induction s with
  | nil =>
    intro fuel acc plen _ hf _
    cases fuel with
    | zero => simp at hf
    | succ f => simp [getpassLoop, getch, bind, Except.bind, pure, Except.pure]
  | cons b bs ih =>
    intro fuel acc plen hs hf hp
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hb := hs b (by simp)
      have h1 : ¬ (b == 0xff || b == 10 || b == 13 || b == 4) = true := by
        simp only [Bool.or_eq_true, beq_iff_eq]; omega
      have h2 : ¬ (b == 0 || b == 0xe0) = true := by
        simp only [Bool.or_eq_true, beq_iff_eq]; omega
      have h3 : ¬ (b == 8 && decide (plen > 0)) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq]; omega
      have h4 : (!isCntrlByte b && decide (plen < 128)) = true := by
        simp only [isCntrlByte, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
          Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq]
        omega
      simp only [getpassLoop, getch, List.cons_append, bind, Except.bind, pure, Except.pure]
      rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
      have := ih f (acc ++ [b]) plen (fun x hx => hs x (by simp [hx])) (by simp at hf ⊢; omega) hp
      rw [this]; simp

def GetpassAscii : Prop :=
  (∀ s : List Nat, (∀ b ∈ s, 32 ≤ b ∧ b ≤ 126) → getpass (s ++ [13]) = .ok s) ∧
  (∀ keys, getpassStdin keys = getpass keys) ∧
  (∀ keys : List Nat, getpassLoop 0 keys [] 0 = .error (.errorException "out of fuel")) ∧
  getpass [] = .error .eofError ∧
  (∀ size, (makeTermios size).length = size) ∧
  (∀ n r, tcCall n r = if r = 0 then .ok () else .error (.uvError n)) ∧
  (∀ c t, cfmakeraw c t = c t) ∧
  (∀ (α : Type) mode (f : R α), withRawTty true mode f = (f, mode)) ∧
  (∀ (α : Type) mode (f : R α), withRawTty false mode f = (argErr "with_raw_tty only works for stdin", mode))

theorem getpassAscii : GetpassAscii := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, rfl, fun _ => by simp [makeTermios], ?_, fun _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · intro s hs
    have := getpassLoop_ascii s (s.length + 1 + 1) [] 0 hs (by omega) (by decide)
    simp only [getpass, List.length_append, List.length_singleton]
    simpa using this
  · intro n r; by_cases h : r = 0 <;> simp [tcCall, h]

def PromptDoc : Prop :=
  -- "If a `default` is provided then the user can enter just a newline character to select
  -- the `default`."
  (∀ rest message default, (prompt (10 :: rest) message default).2 = some default) ∧
  -- EOF on a blank line gives `nothing`
  (∀ message default, (prompt [] message default).2 = none) ∧
  -- otherwise the line typed, without its newline
  (∀ line rest message default, line ≠ [] → 10 ∉ line → 13 ∉ line →
      (prompt (line ++ 10 :: rest) message default).2 = some line) ∧
  (∀ i m d, promptStdin i m d = prompt i m d)

theorem prompt_line (line rest : List UInt8) (h : 10 ∉ line) :
    readlineKeep (line ++ 10 :: rest) = line ++ [10] := by
  have : (line ++ 10 :: rest).idxOf? 10 = some line.length := by
    rw [List.idxOf?_eq_some_iff]
    refine ⟨by simp, by simp, ?_⟩
    intro j hj; rw [List.getElem_append_left hj]
    intro e; exact h (e ▸ List.getElem_mem hj)
  simp only [readlineKeep, this]
  exact take_length_succ_append line 10 rest

theorem promptDoc : PromptDoc := by
  refine ⟨?_, fun _ _ => rfl, ?_, fun _ _ _ => rfl⟩
  · intro rest message default
    have := prompt_line [] rest (by simp)
    simp at this
    simp [prompt, this, chomp]
  · intro line rest message default hne h10 h13
    rw [show (prompt (line ++ 10 :: rest) message default).2 =
      (let u := chomp (line ++ [10]); some (if u.isEmpty then default else u)) by
        simp [prompt, prompt_line line rest h10]]
    have hl : (line ++ [10]).dropLast = line := by simp
    have h13' : line.getLast? ≠ some 13 := by
      intro e; exact h13 (List.mem_of_getLast? e)
    have hc : chomp (line ++ [10]) = line := by
      simp only [chomp, List.getLast?_append, List.getLast?_singleton, Option.some_or]
      simp [hl, h13']
    simp only [hc]
    cases line with
    | nil => exact absurd rfl hne
    | cons x xs => rfl
end JuliaLean.IOCov.Util
end

section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Util

open JuliaLean JuliaLean.IOCov

/-! ## CRC-32c, lines 515-551 -/

open JuliaLean.Base64Uuid (U32 jl_crc32c Byte)

def Crc32cCorrect : Prop :=
  (∀ a crc, crc32cBytes a crc = jl_crc32c crc a) ∧
  (∀ a b crc, crc32cBytes (a ++ b) crc = crc32cBytes b (crc32cBytes a crc)) ∧
  (∀ k x crc, crc32cUInt k x crc = crc32cBytes (leBytes k x) crc) ∧
  (∀ k x, (leBytes k x).length = k) ∧
  (∀ crc, crc32cBytes [] crc = crc)

theorem crc32cCorrect : Crc32cCorrect := by
  refine ⟨fun a crc => by simp only [crc32cBytes, unsafeCrc32c, List.take_length], ?_, fun k x crc => by
    simp only [crc32cUInt, crc32cBytes, unsafeCrc32c, List.take_length], fun k x => by simp [leBytes], ?_⟩
  · intro a b crc
    simp only [crc32cBytes, unsafeCrc32c, List.take_length]
    rw [Base64Uuid.jl_crc32c_append]
  · intro crc; simp [crc32cBytes, unsafeCrc32c, Base64Uuid.jl_crc32c_nil]

def KwdefCorrect : Prop :=
  -- `a`, `a::T`, `a = v`, `a::T = v` give the name, the default, and the plain field
  (∀ n, defNameDefval (.sym n) = some (.sym n, n, none)) ∧
  (∀ n t, defNameDefval (.typed n t) = some (.typed n t, n, none)) ∧
  (∀ n v, defNameDefval (.assign (.sym n) v) = some (.sym n, n, some v)) ∧
  (∀ n t v, defNameDefval (.assign (.typed n t) v) = some (.typed n t, n, some v)) ∧
  (∀ n v, defNameDefval (.wrap "const" (.assign (.sym n) v)) = some (.wrap "const" (.sym n), n, some v)) ∧
  -- every recognised field contributes its name in order; others are kept unchanged
  (∀ items : List FieldExpr, (extractFields items).1.length = items.length ∧
      (extractFields items).2.map (·.1) =
        items.filterMap (fun i => (defNameDefval i).map (·.2.1))) ∧
  (∀ nds, kwParams nds = nds)

theorem kwdefCorrect : KwdefCorrect := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, ?_,
    fun _ => rfl⟩
  intro items
  induction items with
  | nil => exact ⟨rfl, rfl⟩
  | cons item rest ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [extractFields]
    cases hd : defNameDefval item with
    | none => simp [h1, h2, hd, List.filterMap_cons]
    | some v =>
      obtain ⟨d, n, dv⟩ := v
      simp [h1, h2, hd, List.filterMap_cons]

/-- The docstring signature, lines 685-687, gives `propagate_project=true` as the default:
called without the keyword, the current project is propagated (`--project` is passed). -/
def RuntestsDefaultPropagates : Prop :=
  ∀ julia tests, "--project" ∈ runtestsCmd julia tests

theorem runtestsDefaultPropagates_refuted : ¬ RuntestsDefaultPropagates := by
  intro h
  have := h [] []
  revert this; decide

def RuntestsCorrect : Prop :=
  (∀ t, runtestsArgs t false false none = t) ∧
  (∀ t, runtestsArgs t true false none = t ++ ["--exit-on-error"]) ∧
  (∀ t h, runtestsArgs t false false (some h) = t ++ ["--seed=0x" ++ h]) ∧
  (∀ j t, "--project" ∈ runtestsCmd j t true)

theorem runtestsCorrect : RuntestsCorrect := by
  refine ⟨fun t => by simp [runtestsArgs], fun t => by simp [runtestsArgs],
    fun t h => by simp [runtestsArgs], fun j t => by simp [runtestsCmd]⟩


/-! ## Per-method properties -/

def ColorCorrect_1 : Prop :=
  (∀ t c st, withOutputColor t c false st = t)
theorem colorCorrect_1 : ColorCorrect_1 := by
  have h := colorCorrect
  exact h.1

def ColorCorrect_2 : Prop :=
  (∀ t iscolor st c, printstyled t iscolor st c = withOutputColor t c iscolor st)
theorem colorCorrect_2 : ColorCorrect_2 := by
  have h := colorCorrect
  exact h.2.1

def ColorCorrect_3 : Prop :=
  (∀ (t : List Char) c st, t ≠ [] → '\n' ∉ t →
      outputColorString t c st = (enableAnsi st (normColor st c)).toList ++ t ++
        (disableAnsi st (normColor st c)).toList)
theorem colorCorrect_3 : ColorCorrect_3 := by
  have h := colorCorrect
  exact h.2.2.1

def ColorCorrect_4 : Prop :=
  (∀ t : List Char, outputColorString t (.sym "nothing") {} = t)
theorem colorCorrect_4 : ColorCorrect_4 := by
  have h := colorCorrect
  exact h.2.2.2.1

def ColorCorrect_5 : Prop :=
  (∀ n : Int, 0 ≤ n → n ≤ 255 → enableCode (.int n) = "\x1b[38;5;" ++ toString n ++ "m")
theorem colorCorrect_5 : ColorCorrect_5 := by
  have h := colorCorrect
  exact h.2.2.2.2

def JuliaCmdCorrect_1 : Prop :=
  (∀ j c i o, (juliaCmd j c i o).take 4 = [j, "-C", c, "-J" ++ i])
theorem juliaCmdCorrect_1 : JuliaCmdCorrect_1 := by
  have h := juliaCmdCorrect
  exact h.1

def JuliaCmdCorrect_2 : Prop :=
  (∀ o : Opts, "-g" ++ toString o.debugLevel ∈ addflags o)
theorem juliaCmdCorrect_2 : JuliaCmdCorrect_2 := by
  have h := juliaCmdCorrect
  exact h.2.1

def JuliaCmdCorrect_3 : Prop :=
  (∀ o : Opts, o.checkBounds = 1 → "--check-bounds=yes" ∈ addflags o)
theorem juliaCmdCorrect_3 : JuliaCmdCorrect_3 := by
  have h := juliaCmdCorrect
  exact h.2.2.1

def JuliaCmdCorrect_4 : Prop :=
  (∀ o : Opts, o.checkBounds = 2 → "--check-bounds=no" ∈ addflags o)
theorem juliaCmdCorrect_4 : JuliaCmdCorrect_4 := by
  have h := juliaCmdCorrect
  exact h.2.2.2.1

def JuliaCmdCorrect_5 : Prop :=
  (∀ o : Opts, o.optLevel ≠ 2 → "-O" ++ toString o.optLevel ∈ addflags o)
theorem juliaCmdCorrect_5 : JuliaCmdCorrect_5 := by
  have h := juliaCmdCorrect
  exact h.2.2.2.2.1

def JuliaCmdCorrect_6 : Prop :=
  (∀ d, juliaExename d = if d then "julia-debug" else "julia")
theorem juliaCmdCorrect_6 : JuliaCmdCorrect_6 := by
  have h := juliaCmdCorrect
  exact h.2.2.2.2.2

def SecurezeroCorrect_1 : Prop :=
  (∀ a, (securezero a).length = a.length ∧ ∀ x ∈ securezero a, x = 0)
theorem securezeroCorrect_1 : SecurezeroCorrect_1 := by
  have h := securezeroCorrect
  exact h.1

def SecurezeroCorrect_2 : Prop :=
  (∀ mem p len sz, p + len * sz ≤ mem.length →
      (unsafeSecurezero mem p len sz).length = mem.length ∧
      ((unsafeSecurezero mem p len sz).drop p).take (len * sz) = List.replicate (len * sz) 0 ∧
      (unsafeSecurezero mem p len sz).take p = mem.take p ∧
      (unsafeSecurezero mem p len sz).drop (p + len * sz) = mem.drop (p + len * sz))
theorem securezeroCorrect_2 : SecurezeroCorrect_2 := by
  have h := securezeroCorrect
  exact h.2.1

def SecurezeroCorrect_3 : Prop :=
  (∀ mem p len, unsafeSecurezeroVoid mem p len = unsafeSecurezero mem p len 1)
theorem securezeroCorrect_3 : SecurezeroCorrect_3 := by
  have h := securezeroCorrect
  exact h.2.2

def GetpassAscii_1 : Prop :=
  (∀ s : List Nat, (∀ b ∈ s, 32 ≤ b ∧ b ≤ 126) → getpass (s ++ [13]) = .ok s)
theorem getpassAscii_1 : GetpassAscii_1 := by
  have h := getpassAscii
  exact h.1

def GetpassAscii_2 : Prop :=
  (∀ keys, getpassStdin keys = getpass keys)
theorem getpassAscii_2 : GetpassAscii_2 := by
  have h := getpassAscii
  exact h.2.1

def GetpassAscii_3 : Prop :=
  (∀ keys : List Nat, getpassLoop 0 keys [] 0 = .error (.errorException "out of fuel")) ∧
  getpass [] = .error .eofError
theorem getpassAscii_3 : GetpassAscii_3 := by
  have h := getpassAscii
  exact ⟨h.2.2.1, h.2.2.2.1⟩

def GetpassAscii_4 : Prop :=
  (∀ size, (makeTermios size).length = size)
theorem getpassAscii_4 : GetpassAscii_4 := by
  have h := getpassAscii
  exact h.2.2.2.2.1

def GetpassAscii_5 : Prop :=
  (∀ n r, tcCall n r = if r = 0 then .ok () else .error (.uvError n))
theorem getpassAscii_5 : GetpassAscii_5 := by
  have h := getpassAscii
  exact h.2.2.2.2.2.1

def GetpassAscii_6 : Prop :=
  (∀ c t, cfmakeraw c t = c t)
theorem getpassAscii_6 : GetpassAscii_6 := by
  have h := getpassAscii
  exact h.2.2.2.2.2.2.1

def GetpassAscii_7 : Prop :=
  (∀ (α : Type) mode (f : R α), withRawTty true mode f = (f, mode))
theorem getpassAscii_7 : GetpassAscii_7 := by
  have h := getpassAscii
  exact h.2.2.2.2.2.2.2.1

def GetpassAscii_8 : Prop :=
  (∀ (α : Type) mode (f : R α), withRawTty false mode f = (argErr "with_raw_tty only works for stdin", mode))
theorem getpassAscii_8 : GetpassAscii_8 := by
  have h := getpassAscii
  exact h.2.2.2.2.2.2.2.2

def PromptDoc_1 : Prop :=
  (∀ rest message default, (prompt (10 :: rest) message default).2 = some default)
theorem promptDoc_1 : PromptDoc_1 := by
  have h := promptDoc
  exact h.1

def PromptDoc_2 : Prop :=
  (∀ message default, (prompt [] message default).2 = none)
theorem promptDoc_2 : PromptDoc_2 := by
  have h := promptDoc
  exact h.2.1

def PromptDoc_3 : Prop :=
  (∀ line rest message default, line ≠ [] → 10 ∉ line → 13 ∉ line →
      (prompt (line ++ 10 :: rest) message default).2 = some line)
theorem promptDoc_3 : PromptDoc_3 := by
  have h := promptDoc
  exact h.2.2.1

def PromptDoc_4 : Prop :=
  (∀ i m d, promptStdin i m d = prompt i m d)
theorem promptDoc_4 : PromptDoc_4 := by
  have h := promptDoc
  exact h.2.2.2

def Crc32cCorrect_1 : Prop :=
  (∀ a crc, crc32cBytes a crc = jl_crc32c crc a)
theorem crc32cCorrect_1 : Crc32cCorrect_1 := by
  have h := crc32cCorrect
  exact h.1

def Crc32cCorrect_2 : Prop :=
  (∀ a b crc, crc32cBytes (a ++ b) crc = crc32cBytes b (crc32cBytes a crc))
theorem crc32cCorrect_2 : Crc32cCorrect_2 := by
  have h := crc32cCorrect
  exact h.2.1

def Crc32cCorrect_3 : Prop :=
  (∀ k x crc, crc32cUInt k x crc = crc32cBytes (leBytes k x) crc)
theorem crc32cCorrect_3 : Crc32cCorrect_3 := by
  have h := crc32cCorrect
  exact h.2.2.1

def Crc32cCorrect_4 : Prop :=
  (∀ k x, (leBytes k x).length = k)
theorem crc32cCorrect_4 : Crc32cCorrect_4 := by
  have h := crc32cCorrect
  exact h.2.2.2.1

def Crc32cCorrect_5 : Prop :=
  (∀ crc, crc32cBytes [] crc = crc)
theorem crc32cCorrect_5 : Crc32cCorrect_5 := by
  have h := crc32cCorrect
  exact h.2.2.2.2

def KwdefCorrect_1 : Prop :=
  (∀ n, defNameDefval (.sym n) = some (.sym n, n, none))
theorem kwdefCorrect_1 : KwdefCorrect_1 := by
  have h := kwdefCorrect
  exact h.1

def KwdefCorrect_2 : Prop :=
  (∀ n t, defNameDefval (.typed n t) = some (.typed n t, n, none))
theorem kwdefCorrect_2 : KwdefCorrect_2 := by
  have h := kwdefCorrect
  exact h.2.1

def KwdefCorrect_3 : Prop :=
  (∀ n v, defNameDefval (.assign (.sym n) v) = some (.sym n, n, some v))
theorem kwdefCorrect_3 : KwdefCorrect_3 := by
  have h := kwdefCorrect
  exact h.2.2.1

def KwdefCorrect_4 : Prop :=
  (∀ n t v, defNameDefval (.assign (.typed n t) v) = some (.typed n t, n, some v))
theorem kwdefCorrect_4 : KwdefCorrect_4 := by
  have h := kwdefCorrect
  exact h.2.2.2.1

def KwdefCorrect_5 : Prop :=
  (∀ n v, defNameDefval (.wrap "const" (.assign (.sym n) v)) = some (.wrap "const" (.sym n), n, some v))
theorem kwdefCorrect_5 : KwdefCorrect_5 := by
  have h := kwdefCorrect
  exact h.2.2.2.2.1

def KwdefCorrect_6 : Prop :=
  (∀ items : List FieldExpr, (extractFields items).1.length = items.length ∧
      (extractFields items).2.map (·.1) =
        items.filterMap (fun i => (defNameDefval i).map (·.2.1)))
theorem kwdefCorrect_6 : KwdefCorrect_6 := by
  have h := kwdefCorrect
  exact h.2.2.2.2.2.1

def KwdefCorrect_7 : Prop :=
  (∀ nds, kwParams nds = nds)
theorem kwdefCorrect_7 : KwdefCorrect_7 := by
  have h := kwdefCorrect
  exact h.2.2.2.2.2.2

def RuntestsCorrect_1 : Prop :=
  (∀ t, runtestsArgs t false false none = t)
theorem runtestsCorrect_1 : RuntestsCorrect_1 := by
  have h := runtestsCorrect
  exact h.1

def RuntestsCorrect_2 : Prop :=
  (∀ t, runtestsArgs t true false none = t ++ ["--exit-on-error"])
theorem runtestsCorrect_2 : RuntestsCorrect_2 := by
  have h := runtestsCorrect
  exact h.2.1

def RuntestsCorrect_3 : Prop :=
  (∀ t h, runtestsArgs t false false (some h) = t ++ ["--seed=0x" ++ h])
theorem runtestsCorrect_3 : RuntestsCorrect_3 := by
  have h := runtestsCorrect
  exact h.2.2.1

def RuntestsCorrect_4 : Prop :=
  (∀ j t, "--project" ∈ runtestsCmd j t true)
theorem runtestsCorrect_4 : RuntestsCorrect_4 := by
  have h := runtestsCorrect
  exact h.2.2.2
/-- Printing to `stdout` styles the text exactly as printing to an `IO` does, and without
color prints it unchanged. -/
def PrintstyledStdout : Prop :=
  ∀ t iscolor st c, printstyledStdout t iscolor st c = withOutputColor t c iscolor st ∧
    printstyledStdout t false st c = t
theorem printstyledStdout_correct : PrintstyledStdout := fun t iscolor st c =>
  ⟨rfl, colorCorrect.1 t c st⟩

/-- `_getch()` returns the next typed key and throws `EOFError` when input ends. -/
def GetchCorrect : Prop := (∀ c cs, getch (c :: cs) = .ok (c, cs)) ∧ (∀ (cs : List Nat), cs = [] → getch cs = .error .eofError)
theorem getchCorrect : GetchCorrect := ⟨fun _ _ => rfl, fun cs h => by subst h; rfl⟩
/-- Both throw exactly when the C call reports failure. -/
def TcgetattrCorrect : Prop := ∀ r, tcgetattr r = .ok () ↔ r = 0
theorem tcgetattrCorrect : TcgetattrCorrect := fun r => by by_cases h : r = 0 <;> simp [tcgetattr, h]
def TcsetattrCorrect : Prop := ∀ r, tcsetattr r = .ok () ↔ r = 0
theorem tcsetattrCorrect : TcsetattrCorrect := fun r => by by_cases h : r = 0 <;> simp [tcsetattr, h]

/-- `unsafe_crc32c(a, n, crc)` checksums the first `n` bytes of `a`, continuing from `crc`. -/
def UnsafeCrc32cPrefix : Prop := ∀ a n crc, unsafeCrc32c a n crc = jl_crc32c crc (a.take n)
theorem unsafeCrc32cPrefix : UnsafeCrc32cPrefix := fun _ _ _ => rfl
/-- Each checksums all of its bytes, and checksumming `a ++ b` equals checksumming `b`
starting from the checksum of `a`. -/
def Crc32cTupleCorrect : Prop := ∀ a b crc, crc32cTuple a crc = jl_crc32c crc a ∧ crc32cTuple (a ++ b) crc = crc32cTuple b (crc32cTuple a crc)
def Crc32cDenseCorrect : Prop := ∀ a b crc, crc32cDense a crc = jl_crc32c crc a ∧ crc32cDense (a ++ b) crc = crc32cDense b (crc32cDense a crc)
def Crc32cStringCorrect : Prop := ∀ a b crc, crc32cString a crc = jl_crc32c crc a ∧ crc32cString (a ++ b) crc = crc32cString b (crc32cString a crc)
theorem crc32cTupleCorrect : Crc32cTupleCorrect := fun a b crc => ⟨crc32cCorrect.1 a crc, crc32cCorrect.2.1 a b crc⟩
theorem crc32cDenseCorrect : Crc32cDenseCorrect := fun a b crc => ⟨crc32cCorrect.1 a crc, crc32cCorrect.2.1 a b crc⟩
theorem crc32cStringCorrect : Crc32cStringCorrect := fun a b crc => ⟨crc32cCorrect.1 a crc, crc32cCorrect.2.1 a b crc⟩
/-- The checksum of an integer is that of its `sizeof(x)` bytes. -/
def Crc32cU128Bytes : Prop := ∀ x crc, crc32cU128 x crc = crc32cDense (leBytes 16 x) crc ∧ (leBytes 16 x).length = 16
def Crc32cU64Bytes : Prop := ∀ x crc, crc32cU64 x crc = crc32cDense (leBytes 8 x) crc ∧ (leBytes 8 x).length = 8
def Crc32cU32Bytes : Prop := ∀ x crc, crc32cU32 x crc = crc32cDense (leBytes 4 x) crc ∧ (leBytes 4 x).length = 4
def Crc32cU16Bytes : Prop := ∀ x crc, crc32cU16 x crc = crc32cDense (leBytes 2 x) crc ∧ (leBytes 2 x).length = 2
def Crc32cU8Bytes : Prop := ∀ x crc, crc32cU8 x crc = crc32cDense (leBytes 1 x) crc ∧ (leBytes 1 x).length = 1
theorem crc32cU128Bytes : Crc32cU128Bytes := fun x crc => ⟨(crc32cCorrect.1 _ crc).symm, crc32cCorrect.2.2.2.1 16 x⟩
theorem crc32cU64Bytes : Crc32cU64Bytes := fun x crc => ⟨(crc32cCorrect.1 _ crc).symm, crc32cCorrect.2.2.2.1 8 x⟩
theorem crc32cU32Bytes : Crc32cU32Bytes := fun x crc => ⟨(crc32cCorrect.1 _ crc).symm, crc32cCorrect.2.2.2.1 4 x⟩
theorem crc32cU16Bytes : Crc32cU16Bytes := fun x crc => ⟨(crc32cCorrect.1 _ crc).symm, crc32cCorrect.2.2.2.1 2 x⟩
theorem crc32cU8Bytes : Crc32cU8Bytes := fun x crc => ⟨(crc32cCorrect.1 _ crc).symm, crc32cCorrect.2.2.2.1 1 x⟩
end JuliaLean.IOCov.Util
end
