import JuliaLean.IOCov.Common
import JuliaLean.Base64Uuid.CrcProofs

set_option linter.unusedSimpArgs false

/-!
Models of `base/util.jl` at master `bbfa0ce4150` (Unix branches): terminal colors,
`julia_cmd`, secure zeroing, the raw-terminal `getpass`, `prompt`, the CRC-32c wrappers
(reusing `JuliaLean.Base64Uuid.jl_crc32c`), `@kwdef`'s field parsing and `runtests`.
-/

namespace JuliaLean.IOCov.Util

open JuliaLean JuliaLean.IOCov

/-! ## Colored output, lines 73-146 -/

/-- A `printstyled` color: one of the `text_colors` symbols, `:nothing`, or an integer. -/
inductive Color where
  | sym (s : String)
  | int (n : Int)
  deriving DecidableEq, Repr

/-- `get(text_colors, color, text_colors[:default])`, lines 3-48. -/
def enableCode : Color → String
  | .int n => if 0 ≤ n ∧ n ≤ 255 then "\x1b[38;5;" ++ toString n ++ "m" else "\x1b[39m"
  | .sym s =>
    match s with
    | "black" => "\x1b[30m" | "red" => "\x1b[31m" | "green" => "\x1b[32m" | "yellow" => "\x1b[33m"
    | "blue" => "\x1b[34m" | "magenta" => "\x1b[35m" | "cyan" => "\x1b[36m" | "white" => "\x1b[37m"
    | "light_black" => "\x1b[90m" | "light_red" => "\x1b[91m" | "light_green" => "\x1b[92m"
    | "light_yellow" => "\x1b[93m" | "light_blue" => "\x1b[94m" | "light_magenta" => "\x1b[95m"
    | "light_cyan" => "\x1b[96m" | "light_white" => "\x1b[97m" | "normal" => "\x1b[0m"
    | "default" => "\x1b[39m" | "bold" => "\x1b[1m" | "italic" => "\x1b[3m"
    | "underline" => "\x1b[4m" | "blink" => "\x1b[5m" | "reverse" => "\x1b[7m"
    | "hidden" => "\x1b[8m" | "nothing" => ""
    | _ => "\x1b[39m"

/-- `get(disable_text_style, color, text_colors[:default])`, lines 52-62. -/
def disableCode : Color → String
  | .sym "bold" => "\x1b[22m" | .sym "italic" => "\x1b[23m" | .sym "underline" => "\x1b[24m"
  | .sym "blink" => "\x1b[25m" | .sym "reverse" => "\x1b[27m" | .sym "hidden" => "\x1b[28m"
  | .sym "normal" => "" | .sym "default" => "" | .sym "nothing" => ""
  | _ => "\x1b[39m"

structure Style where
  bold : Bool := false
  italic : Bool := false
  underline : Bool := false
  blink : Bool := false
  reverse : Bool := false
  hidden : Bool := false

/-- The six `flag && color === :flag && (color = :nothing)` lines, 88-93. -/
def normColor (st : Style) (c : Color) : Color :=
  let c := if st.bold && c == .sym "bold" then .sym "nothing" else c
  let c := if st.italic && c == .sym "italic" then .sym "nothing" else c
  let c := if st.underline && c == .sym "underline" then .sym "nothing" else c
  let c := if st.blink && c == .sym "blink" then .sym "nothing" else c
  let c := if st.reverse && c == .sym "reverse" then .sym "nothing" else c
  if st.hidden && c == .sym "hidden" then .sym "nothing" else c

def enableAnsi (st : Style) (c : Color) : String :=
  enableCode c ++ (if st.bold then "\x1b[1m" else "") ++ (if st.italic then "\x1b[3m" else "") ++
    (if st.underline then "\x1b[4m" else "") ++ (if st.blink then "\x1b[5m" else "") ++
    (if st.reverse then "\x1b[7m" else "") ++ (if st.hidden then "\x1b[8m" else "")

def disableAnsi (st : Style) (c : Color) : String :=
  (if st.hidden then "\x1b[28m" else "") ++ (if st.reverse then "\x1b[27m" else "") ++
    (if st.blink then "\x1b[25m" else "") ++ (if st.underline then "\x1b[24m" else "") ++
    (if st.bold then "\x1b[22m" else "") ++ (if st.italic then "\x1b[23m" else "") ++ disableCode c

/-- `eachsplit(str, '\n')`: the pieces between newlines, empty ones included. -/
def splitNl : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '\n' then [] :: splitNl cs
    else match splitNl cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- `output_color_string(buf, str, color, flags...)`, lines 86-117: every nonempty line of
`eachsplit(str, '\n')` is wrapped in the enable and disable sequences. -/
def outputColorString (str : List Char) (c : Color) (st : Style) : List Char :=
  let c := normColor st c
  let e := (enableAnsi st c).toList
  let d := (disableAnsi st c).toList
  List.intercalate ['\n'] ((splitNl str).map fun line => if line.isEmpty then [] else e ++ line ++ d)

/-- `with_output_color(f, color, io, args...; flags...)`, lines 73-84: the text `f` printed
(`text`), colored only when `get(io, :color, false)`. -/
def withOutputColor (text : List Char) (c : Color) (iscolor : Bool) (st : Style) : List Char :=
  if iscolor then outputColorString text c st else text

/-- `printstyled(io, msg...; flags..., color=:normal)`, lines 143-144, and
`printstyled(msg...) = printstyled(stdout, msg...)`, lines 145-146. -/
def printstyled (printed : List Char) (iscolor : Bool) (st : Style) (c : Color := .sym "normal") :
    List Char := withOutputColor printed c iscolor st

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

/-! ## `julia_cmd`, `julia_exename`, lines 173-266 -/

/-- The fields of `JLOptions()` that `julia_cmd` reads. -/
structure Opts where
  compile : Nat
  depwarn : Nat
  checkBounds : Nat
  canInline : Nat
  compiledModules : Nat
  pkgimages : Nat
  optLevel : Nat
  optLevelMin : Nat
  debugLevel : Nat
  color : Nat
  quiet : Nat
  startupfile : Nat

/-- The `addflags` that `julia_cmd` computes, lines 180-252 (without the coverage and
allocation-tracking flags, which forward strings unchanged). `JL_OPTIONS_COMPILE_OFF = 0`,
`_ALL = 2`, `_MIN = 3`. -/
def addflags (o : Opts) : List String :=
  (if o.compile == 0 then ["--compile=no"] else if o.compile == 2 then ["--compile=all"]
    else if o.compile == 3 then ["--compile=min"] else []) ++
  (if o.depwarn == 1 then ["--depwarn=yes"] else if o.depwarn == 2 then ["--depwarn=error"] else []) ++
  (if o.checkBounds == 1 then ["--check-bounds=yes"] else if o.checkBounds == 2 then ["--check-bounds=no"] else []) ++
  (if o.canInline == 0 then ["--inline=no"] else []) ++
  (if o.compiledModules == 0 then ["--compiled-modules=no"] else []) ++
  (if o.compiledModules == 2 then ["--compiled-modules=existing"] else []) ++
  (if o.compiledModules == 3 then ["--compiled-modules=strict"] else []) ++
  (if o.pkgimages == 0 then ["--pkgimages=no"] else []) ++
  (if o.pkgimages == 2 then ["--pkgimages=existing"] else []) ++
  (if o.optLevel == 2 then [] else ["-O" ++ toString o.optLevel]) ++
  (if o.optLevelMin == 0 then [] else ["--min-optlevel=" ++ toString o.optLevelMin]) ++
  ["-g" ++ toString o.debugLevel] ++
  (if o.color == 1 then ["--color=yes"] else if o.color == 2 then ["--color=no"] else []) ++
  (if o.quiet != 0 then ["-q"] else []) ++
  (if o.startupfile == 2 then ["--startup-file=no"] else [])

/-- `julia_cmd(julia; cpu_target)`: `` `$julia -C $cpu_target -J$image_file $addflags` ``. -/
def juliaCmd (julia cpuTarget imageFile : String) (o : Opts) : List String :=
  [julia, "-C", cpuTarget, "-J" ++ imageFile] ++ addflags o

/-- `julia_exename()`, lines 260-266 (non-Windows). -/
def juliaExename (isdebug : Bool) : String := if isdebug then "julia-debug" else "julia"

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

/-! ## Secure zeroing, lines 276-280 -/

/-- `securezero!(a) = fill!(a, 0)`, line 277. -/
def securezero (a : List Int) : List Int := a.map (fun _ => 0)

/-- `unsafe_securezero!(p::Ptr{T}, len)`, lines 278-279: `memset(p, 0, len*sizeof(T))` on a
byte memory `mem` at offset `p`. The `Ptr{Cvoid}` method, line 280, uses `sizeof = 1`. -/
def unsafeSecurezero (mem : List UInt8) (p len sz : Nat) : List UInt8 :=
  mem.take p ++ List.replicate (min (len * sz) (mem.length - p)) 0 ++ mem.drop (p + len * sz)
def unsafeSecurezeroVoid (mem : List UInt8) (p len : Nat) : List UInt8 := unsafeSecurezero mem p len 1

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

/-! ## The raw terminal and `getpass`, lines 307-392 -/

/-- `_getch()`, lines 310-316 (Unix): `read(stdin, UInt8)`, `EOFError` at the end.
Bytes are natural numbers below 256. -/
def getch : List Nat → R (Nat × List Nat)
  | [] => .error .eofError
  | c :: cs => .ok (c, cs)

/-- `make_termios()`, line 319: `termios_size` zero bytes. -/
def makeTermios (size : Nat) : List UInt8 := List.replicate size 0

/-- `tcgetattr(fd, termios)` / `tcsetattr(fd, termios, mode)`, lines 325-336: a nonzero
return throws `IOError`. -/
def tcCall (name : String) (ret : Int) : R Unit :=
  if ret != 0 then .error (.uvError name) else .ok ()

/-- `cfmakeraw(termios)`, line 337: the C function's result. -/
def cfmakeraw (c : List UInt8 → List UInt8) (t : List UInt8) : List UInt8 := c t

/-- `with_raw_tty(f, input)`, lines 339-363: get the terminal mode, set raw mode, run `f`,
and in `finally` restore the saved mode. Returns `f`'s outcome and the final mode. -/
def withRawTty {α} (isStdin : Bool) (mode : List UInt8) (f : R α) : R α × List UInt8 :=
  if !isStdin then (argErr "with_raw_tty only works for stdin", mode)
  else (f, mode)

/-- `iscntrl(Char(c))` for a single byte `c`: the code point `U+00XX` is a control
character for `0x00-0x1f` and `0x7f-0x9f`. -/
def isCntrlByte (c : Nat) : Bool := c < 32 || (127 ≤ c && c ≤ 159)

/-- The read loop of `getpass(input::TTY, output, prompt)`, lines 371-385: `s` holds the
bytes written to the `SecretBuffer`, `plen` the counter. -/
def getpassLoop : Nat → List Nat → List Nat → Nat → R (List Nat)
  | 0, _, _, _ => .error (.errorException "out of fuel")
  | fuel + 1, input, s, plen => do
    let (c, input) ← getch input
    if c == 0xff || c == 10 || c == 13 || c == 4 then pure s
    else if c == 0 || c == 0xe0 then do
      let (_, input) ← getch input
      getpassLoop fuel input s plen
    else if c == 8 && plen > 0 then getpassLoop fuel input s (plen - 1)
    else if !isCntrlByte c && plen < 128 then getpassLoop fuel input (s ++ [c]) plen
    else getpassLoop fuel input s plen

/-- `getpass(input, output, prompt)`: the secret read from the typed bytes `keys`. -/
def getpass (keys : List Nat) : R (List Nat) := getpassLoop (keys.length + 1) keys [] 0

/-- `getpass(prompt; with_suffix) = getpass(stdin, stdout, prompt; with_suffix)`, line 392. -/
def getpassStdin (keys : List Nat) : R (List Nat) := getpass keys

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

/-! ## `prompt`, lines 413-424 -/

/-- `chomp(s)`: remove one trailing `"\n"` or `"\r\n"`. -/
def chomp (s : List UInt8) : List UInt8 :=
  if s.getLast? == some 10 then
    let t := s.dropLast
    if t.getLast? == some 13 then t.dropLast else t
  else s

/-- `readline(input, keep=true)`: the bytes up to and including the first `'\n'`. -/
def readlineKeep (input : List UInt8) : List UInt8 :=
  match input.idxOf? 10 with
  | some k => input.take (k + 1)
  | none => input

/-- `prompt(input, output, message; default)`, lines 413-420: the text printed and the
result (`none` is `nothing`). -/
def prompt (input message default : List UInt8) : List UInt8 × Option (List UInt8) :=
  let msg := if !default.isEmpty then message ++ bs " [" ++ default ++ bs "]: " else message ++ bs ": "
  let uinput := readlineKeep input
  if uinput.isEmpty then (msg, none)
  else
    let u := chomp uinput
    (msg, some (if u.isEmpty then default else u))

/-- `prompt(message; default) = prompt(stdin, stdout, message, default=default)`, line 424. -/
def promptStdin (input message default : List UInt8) : List UInt8 × Option (List UInt8) :=
  prompt input message default

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

/-! ## CRC-32c, lines 515-551 -/

open JuliaLean.Base64Uuid (U32 jl_crc32c Byte)

/-- `unsafe_crc32c(a, n, crc) = jl_crc32c(crc, a, n)`, line 515: the first `n` bytes. -/
def unsafeCrc32c (a : List Byte) (n : Nat) (crc : U32) : U32 := jl_crc32c crc (a.take n)

/-- `_crc32c(a::NTuple{N,UInt8}, crc)`, `_crc32c(a::DenseUInt8OrInt8, crc)` and
`_crc32c(s::String, crc)`, lines 517-526: one call over all `length`/`sizeof` bytes. -/
def crc32cBytes (a : List Byte) (crc : U32) : U32 := unsafeCrc32c a a.length crc

/-- Little-endian bytes of a `k`-byte unsigned integer. -/
def leBytes (k : Nat) (x : Nat) : List Byte :=
  (List.range k).map fun i => JInt.lit .u8 ((x / 256 ^ i) % 256)

/-- `_crc32c(x::UInt128/UInt64/UInt32/UInt16/UInt8, crc)`, lines 542-551: `jl_crc32c` over the
`sizeof(x)` bytes of `Ref(x)`, which are little-endian on the supported platforms. -/
def crc32cUInt (k : Nat) (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes k x)

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

/-! ## `@kwdef` field parsing, lines 590-684 -/

/-- The field expressions `@kwdef` accepts. -/
inductive FieldExpr where
  | sym (name : String)
  | typed (name : String) (ty : String)
  | assign (lhs : FieldExpr) (rhs : String)
  | wrap (head : String) (arg : FieldExpr)
  | other
  deriving DecidableEq, Repr

/-- `def_name_defval_from_kwdef_fielddef(kwdef)`, lines 667-684: the field definition
without its default, the field name, and the default (`none` = `nothing`); `none` overall
for an expression that is not a field (for example a docstring line or a method). -/
def defNameDefval : FieldExpr → Option (FieldExpr × String × Option String)
  | .sym n => some (.sym n, n, none)
  | .typed n t => some (.typed n t, n, none)
  | .assign lhs rhs =>
    match defNameDefval lhs with
    | some (d, n, _) => some (d, n, some rhs)
    | none => none
  | .wrap h a =>
    match defNameDefval a with
    | some (d, n, dv) =>
      if h == "const" || h == "atomic" then some (.wrap h d, n, dv)
      else if h == "escape" || h == "hygienic-scope" then some (.wrap h d, n, dv.map (fun v => h ++ "(" ++ v ++ ")"))
      else none
    | none => none
  | .other => none

/-- `extract_names_and_defvals_from_kwdef_fieldblock!` on a flat block, lines 646-665:
the rewritten fields and the `(name, default)` list, skipping non-fields. -/
def extractFields : List FieldExpr → List FieldExpr × List (String × Option String)
  | [] => ([], [])
  | item :: rest =>
    let (defs, nds) := extractFields rest
    match defNameDefval item with
    | some (d, n, dv) => (d :: defs, (n, dv) :: nds)
    | none => (item :: defs, nds)

/-- The keyword parameters of the generated constructor, lines 600-606: a plain name for a
field without default, `name = default` otherwise. -/
def kwParams (nds : List (String × Option String)) : List (String × Option String) := nds

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

/-! ## `runtests`, lines 703-739 -/

/-- The test-list arguments of `runtests`, lines 709-715: a string is split on spaces,
then `--exit-on-error`, `--revise` and `--seed=0x...` are appended. -/
def runtestsArgs (tests : List String) (exitOnError revise : Bool) (seedHex : Option String) :
    List String :=
  tests ++ (if exitOnError then ["--exit-on-error"] else []) ++ (if revise then ["--revise"] else []) ++
    (match seedHex with | some h => ["--seed=0x" ++ h] | none => [])

/-- The command `runtests` runs, lines 719-721, with the keyword defaults of line 703-708
(`propagate_project::Bool=false`): `julia_cmd() -q $julia_args $project_flag runtests.jl $tests`. -/
def runtestsCmd (julia : List String) (tests : List String) (propagateProject : Bool := false) :
    List String :=
  julia ++ ["-q"] ++ (if propagateProject then ["--project"] else []) ++ ["runtests.jl"] ++
    runtestsArgs tests false false none

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


/-! ## Separate overload models -/

/-- `printstyled(msg...; flags...) = printstyled(stdout, msg...; flags...)`, lines 145-146. -/
def printstyledStdout (printed : List Char) (iscolor : Bool) (st : Style) (c : Color := .sym "normal") :
    List Char := printstyled printed iscolor st c
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

/-- `tcgetattr(fd, termios)`, lines 325-330, and `tcsetattr(fd, termios, mode)`, lines 331-336. -/
def tcgetattr (ret : Int) : R Unit := if ret != 0 then .error (.uvError "tcgetattr") else .ok ()
def tcsetattr (ret : Int) : R Unit := if ret != 0 then .error (.uvError "tcsetattr") else .ok ()
/-- Both throw exactly when the C call reports failure. -/
def TcgetattrCorrect : Prop := ∀ r, tcgetattr r = .ok () ↔ r = 0
theorem tcgetattrCorrect : TcgetattrCorrect := fun r => by by_cases h : r = 0 <;> simp [tcgetattr, h]
def TcsetattrCorrect : Prop := ∀ r, tcsetattr r = .ok () ↔ r = 0
theorem tcsetattrCorrect : TcsetattrCorrect := fun r => by by_cases h : r = 0 <;> simp [tcsetattr, h]

/-- `unsafe_crc32c(a, n, crc)` checksums the first `n` bytes of `a`, continuing from `crc`. -/
def UnsafeCrc32cPrefix : Prop := ∀ a n crc, unsafeCrc32c a n crc = jl_crc32c crc (a.take n)
theorem unsafeCrc32cPrefix : UnsafeCrc32cPrefix := fun _ _ _ => rfl

/-- `_crc32c(a::NTuple{N,UInt8}, crc)`, lines 517-518: `unsafe_crc32c(Ref(a), length(a), crc)`. -/
def crc32cTuple (a : List Byte) (crc : U32) : U32 := unsafeCrc32c a a.length crc
/-- `_crc32c(a::DenseUInt8OrInt8, crc)`, lines 520-522: `unsafe_crc32c(a, length(a), crc)`. -/
def crc32cDense (a : List Byte) (crc : U32) : U32 := unsafeCrc32c a a.length crc
/-- `_crc32c(s::Union{String,SubString{String}}, crc)`, lines 524-526: `sizeof(s)` code units. -/
def crc32cString (s : List Byte) (crc : U32) : U32 := unsafeCrc32c s s.length crc
/-- Each checksums all of its bytes, and checksumming `a ++ b` equals checksumming `b`
starting from the checksum of `a`. -/
def Crc32cTupleCorrect : Prop := ∀ a b crc, crc32cTuple a crc = jl_crc32c crc a ∧ crc32cTuple (a ++ b) crc = crc32cTuple b (crc32cTuple a crc)
def Crc32cDenseCorrect : Prop := ∀ a b crc, crc32cDense a crc = jl_crc32c crc a ∧ crc32cDense (a ++ b) crc = crc32cDense b (crc32cDense a crc)
def Crc32cStringCorrect : Prop := ∀ a b crc, crc32cString a crc = jl_crc32c crc a ∧ crc32cString (a ++ b) crc = crc32cString b (crc32cString a crc)
theorem crc32cTupleCorrect : Crc32cTupleCorrect := fun a b crc => ⟨crc32cCorrect.1 a crc, crc32cCorrect.2.1 a b crc⟩
theorem crc32cDenseCorrect : Crc32cDenseCorrect := fun a b crc => ⟨crc32cCorrect.1 a crc, crc32cCorrect.2.1 a b crc⟩
theorem crc32cStringCorrect : Crc32cStringCorrect := fun a b crc => ⟨crc32cCorrect.1 a crc, crc32cCorrect.2.1 a b crc⟩

/-- `_crc32c(x::UInt128, crc)` (16 bytes), `UInt64` (8), `UInt32` (4), `UInt16` (2), `UInt8` (1),
lines 542-551: `jl_crc32c` over the little-endian bytes of `Ref(x)`. -/
def crc32cU128 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 16 x)
def crc32cU64 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 8 x)
def crc32cU32 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 4 x)
def crc32cU16 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 2 x)
def crc32cU8 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 1 x)
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
