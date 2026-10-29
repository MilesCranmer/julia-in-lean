import JuliaLean.ShowCov.Terminals
import JuliaLean.ShowCov.TermInfo

/-!
Properties of `base/Terminals.jl`, `base/coreio.jl` and `base/terminfo.jl`.
-/

namespace JuliaLean.ShowCov

open Terminals TermInfo

/-! ## `base/Terminals.jl` -/

/-- For a `TextTerminal` subtype that defines the documented interface
(`cmove(t, x, y)`, `getX`, `getY`, `displaysize`), every relative-move fallback
returns normally, i.e. ends in a `cmove(t, x', y')` call
(`base/Terminals.jl:42-70`). -/
def TextMoveFallbacks : Prop :=
  ∀ (t : TextTerm) (x y h w n : Int), t.getX = some x → t.getY = some y →
    t.displaysize = some (h, w) → t.cmove3 = true →
    cmoveUp t n = .ok () ∧ cmoveDown t n = .ok () ∧ cmoveLeft t n = .ok () ∧
    cmoveRight t n = .ok () ∧ cmoveLineUp t n = .ok () ∧ cmoveLineDown t n = .ok () ∧
    cmoveCol t n = .ok () ∧ cmoveUp1 t = .ok () ∧ cmoveDown1 t = .ok () ∧
    cmoveLeft1 t = .ok () ∧ cmoveRight1 t = .ok () ∧ cmoveLineUp1 t = .ok () ∧
    cmoveLineDown1 t = .ok ()

theorem textMoveFallbacks_refuted : ¬ TextMoveFallbacks := by
  intro h
  have := (h ⟨some 5, some 5, some (24, 80), true⟩ 5 5 24 80 1 rfl rfl rfl rfl).1
  simp [cmoveUp, getX, getY, cmove2] at this

/-- The `TextTerminal` interface fallbacks: the unimplemented methods throw
`ErrorException("Unimplemented")`; `pos`, `width`, `height` combine `getX`,
`getY`, `displaysize`; `hascolor` is `false`; `flush`, `beep` and the bracketed
paste toggles return `nothing` (`base/Terminals.jl:43-91`). -/
def TextTerminalInterface : Prop :=
  ∀ t : TextTerm,
    (textFallbackError : R Unit) = .error (.errorException "Unimplemented") ∧
    (∀ x y, t.getX = some x → t.getY = some y → pos t = .ok (x, y)) ∧
    (t.getX = none → pos t = .error (.errorException "Unimplemented")) ∧
    (∀ x, t.getX = some x → t.getY = none → pos t = .error (.errorException "Unimplemented")) ∧
    (∀ h w, t.displaysize = some (h, w) → width t = .ok w ∧ height t = .ok h) ∧
    (t.displaysize = none → width t = .error (.errorException "Unimplemented") ∧
      height t = .error (.errorException "Unimplemented")) ∧
    hascolorText t = false ∧ flushText t = () ∧ beepText t = () ∧ bracketedPasteText t = ()

theorem textTerminalInterface_proven : TextTerminalInterface := by
  intro t
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro x y hx hy; simp [pos, getX, getY, hx, hy]
  · intro hx; simp [pos, getX, hx, unimplemented]
  · intro x hx hy; simp [pos, getX, getY, hx, hy, unimplemented]
  · intro h w hd; simp [width, height, displaysize, hd]
  · intro hd; simp [width, height, displaysize, hd, unimplemented]

/-- The `UnixTerminal` methods write the documented escape sequences
(`base/Terminals.jl:113-158`): `CSI n A/B/C/D` for relative moves, `\r` plus a
right move of `n-1` columns for `cmove_col(t, n)` (`n > 1`), a move then `\r`
for the line moves; the constant sequences for bracketed paste, keypad mode,
`clear`, `clear_line`; `beep` writes BEL to the error stream. `write`'s byte
count is returned. -/
def UnixEscapes : Prop :=
  ∀ n : Int,
    (cmoveUpU n).out = ["\x1b[" ++ toString n ++ "A"] ∧
    (cmoveDownU n).out = ["\x1b[" ++ toString n ++ "B"] ∧
    (cmoveRightU n).out = ["\x1b[" ++ toString n ++ "C"] ∧
    (cmoveLeftU n).out = ["\x1b[" ++ toString n ++ "D"] ∧
    (cmoveUpU n).ret = ("\x1b[" ++ toString n ++ "A").utf8ByteSize ∧
    (n > 1 → (cmoveColU n).out = ["\r", "\x1b[" ++ toString (n - 1) ++ "C"] ∧
      (cmoveColU n).ret = .inr ("\x1b[" ++ toString (n - 1) ++ "C").utf8ByteSize) ∧
    (n ≤ 1 → (cmoveColU n).out = ["\r"] ∧ (cmoveColU n).ret = .inl false) ∧
    (cmoveLineUpU n).out = ["\x1b[" ++ toString n ++ "A", "\r"] ∧
    (cmoveLineDownU n).out = ["\x1b[" ++ toString n ++ "B", "\r"] ∧
    enableBracketedPasteU.out = ["\x1b[?2004h"] ∧ disableBracketedPasteU.out = ["\x1b[?2004l"] ∧
    endKeypadTransmitModeU.out = ["\x1b[?1l\x1b>"] ∧ clearU.out = ["\x1b[H\x1b[2J"] ∧
    clearLineU.out = ["\r\x1b[0K"] ∧ beepU.out = [] ∧ beepU.err = ["\x07"]

theorem unixEscapes_proven : UnixEscapes := by
  intro n
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro h; simp [cmoveColU, h, cmoveRightU, cmoveUnix, writeOut, CSI, intStr]
  · intro h
    have : ¬ n > 1 := by omega
    simp [cmoveColU, this]
  · simp [cmoveLineUpU, cmoveUpU, cmoveColU, cmoveUnix, writeOut, CSI, intStr]
  · simp [cmoveLineDownU, cmoveDownU, cmoveColU, cmoveUnix, writeOut, CSI, intStr]

theorem propGet_of_find {props : List (String × String)} {k d : String}
    (h : props.any (·.1 == k) = false) : propGet props k d = d := by
  unfold propGet
  have : props.find? (·.1 == k) = none := by
    rw [List.find?_eq_none]
    intro x hx
    simp only [List.any_eq_false] at h
    exact h x hx
  rw [this]

theorem propGet_indep {props : List (String × String)} {k : String} (d1 d2 : String)
    (h : props.any (·.1 == k) = true) : propGet props k d1 = propGet props k d2 := by
  unfold propGet
  cases hf : props.find? (·.1 == k) with
  | some p => rfl
  | none =>
    rw [List.find?_eq_none] at hf
    rw [List.any_eq_true] at h
    obtain ⟨x, hx, hp⟩ := h
    exact absurd hp (hf x hx)

/-- `TTYTerminal` forwards `pipe_reader`/`pipe_writer`/`displaysize` to its
streams and the dictionary methods to `pipe_writer(t)`; `getindex` agrees with
`get` for present keys and throws `KeyError` for absent ones, `hascolor` reads
`:color` (default `false`), `peek` returns the stream's value when it has the
requested type, `raw!` reports success of `jl_tty_set_mode`
(`base/Terminals.jl:97-98,143-168`). -/
def TTYForwarding : Prop :=
  ∀ (σ : Type) (t : UnixTerm σ) (key default : String) (h : Nat) (mode : Int),
    pipeReaderU t = t.inStream ∧ pipeWriterU t = t.outStream ∧ displaysizeU t = t.outDisplaysize ∧
    (Terminals.haskeyTTY t key = true → Terminals.getindexTTY t key = .ok (Terminals.getTTY t key default)) ∧
    (Terminals.haskeyTTY t key = false → Terminals.getindexTTY t key = .error (.keyError key) ∧
      Terminals.getTTY t key default = default) ∧
    (Terminals.haskeyTTY t "color" = false → hascolorTTY t = .ok false) ∧
    (propGet t.outProps "color" "false" = "true" → hascolorTTY t = .ok true) ∧
    (t.peekIsT = true → peekTTY t = t.peekIn) ∧
    rawTTY (some h) mode = .ok (mode == 0) ∧ rawTTY none mode = .error .typeError

theorem ttyForwarding_proven : TTYForwarding := by
  intro σ t key default h mode
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro hk
    simp only [Terminals.getindexTTY, hk, if_true, Terminals.getTTY]
    exact congrArg Except.ok (propGet_indep _ _ hk)
  · intro hk
    refine ⟨by simp [Terminals.getindexTTY, hk], ?_⟩
    exact propGet_of_find hk
  · intro hk
    have := propGet_of_find (d := "false") hk
    simp [hascolorTTY, this]
  · intro hc; simp [hascolorTTY, hc]
  · intro hp
    unfold peekTTY
    cases t.peekIn <;> simp [hp]

/-! ## `base/coreio.jl` -/

/-- `print`/`println` without a stream write to `stdout`, `println` appends
`"\n"`, `println(io)` writes `"\n"`; `DevNull` accepts every write (returning
the byte count, which must fit an `Int`), is empty, and `wait_close` blocks;
the `CoreSTDOUT`/`CoreSTDERR`/`DevNull` read side is at end of file
(`base/coreio.jl:6-40`). -/
def CoreIOBehaviour : Prop :=
  ∀ (xs : List String) (io : Stream) (b : UInt8) (n : Nat) (bytes : List UInt8) (nb : Int),
    print0 xs = xs.map (Stream.stdout, ·) ∧
    println0 xs = xs.map (Stream.stdout, ·) ++ [(.stdout, "\n")] ∧
    printlnIO io = [(io, "\n")] ∧
    writeDevNull b = 1 ∧
    (n ≤ int64Max → unsafeWriteDevNull n = .ok n) ∧
    (n > int64Max → unsafeWriteDevNull n = .error (.inexactError "Int64")) ∧
    bytesavailableDevNull = 0 ∧ closewriteDevNull = .returns ∧ closeDevNull = .returns ∧
    waitCloseDevNull = .blocksForever ∧ writeCore bytes = bytes ∧
    readCore = .error .eofError ∧ isopenCore = true ∧ isreadableCore = false ∧
    iswritableCore = true ∧ flushCore = () ∧ eofCore = true ∧ waitReadnbCore nb = ()

theorem coreIOBehaviour_proven : CoreIOBehaviour := by
  intro xs io b n bytes nb
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [println0, printIO]
  · intro h; simp [unsafeWriteDevNull, h]
  · intro h
    have : ¬ n ≤ int64Max := by omega
    simp [unsafeWriteDevNull, this]

/-! ## `base/terminfo.jl` -/

/-- Little-endian bytes of a 16-bit value. -/
def le16 (x : Int) : List UInt8 :=
  let u := (x % 65536).toNat
  [(u % 256).toUInt8, (u / 256).toUInt8]

/-- A legacy-format terminfo file named `x` with no standard capabilities and
an extended section holding one boolean capability `name = true`. -/
def flagOnlyFile (name : List UInt8) : List UInt8 :=
  le16 0o432 ++ le16 2 ++ le16 0 ++ le16 0 ++ le16 0 ++ le16 0 ++ [0x78, 0] ++
  le16 1 ++ le16 0 ++ le16 0 ++ le16 1 ++ le16 (name.length + 1) ++ [1, 0] ++ le16 0 ++ name ++ [0]

/-- The extended section's capability names are the NUL-terminated strings at
their offsets, counted from the start of the names, which follow the (here
empty) string values: a file whose extended section holds one flag `name`
parses with extended info `name => true` (term(5); `base/terminfo.jl:103-139`). -/
def ExtendedLabels : Prop :=
  ∀ name : List UInt8, name ≠ [] → (0 : UInt8) ∉ name → name.length < 64 →
    (readRaw (flagOnlyFile name)).map (·.extended) = .ok (some [(name, .bool true)])

/-- The same property for the previous nightly's parser. -/
def ExtendedLabelsHistorical : Prop :=
  ∀ name : List UInt8, name ≠ [] → (0 : UInt8) ∉ name → name.length < 64 →
    (readRawHistorical (flagOnlyFile name)).map (·.extended) = .ok (some [(name, .bool true)])

theorem extendedLabels_refuted : ¬ ExtendedLabelsHistorical := by
  intro h
  have := h [0x41, 0x58] (by decide) (by decide) (by decide)
  revert this
  decide

theorem extendedLabels_proven : ExtendedLabels := by
  intro name hn hz hl
  have hlen : (2 : Int) ≤ (name.length : Int) + 17 + 1 := by omega
  have h16 : le16 (name.length + 1) = [(name.length + 1).toUInt8, 0] := by
    have hi : (0 : Int) ≤ (name.length : Int) + 1 := by omega
    have hi' : (name.length : Int) + 1 < 65536 := by omega
    have hn' : name.length + 1 < 256 := by omega
    simp [le16, Int.emod_eq_of_lt hi hi', Nat.mod_eq_of_lt hn', Nat.div_eq_of_lt hn']
  simp only [flagOnlyFile, h16]
  have hn256 : name.length + 1 < 256 := by omega
  have hi256 : (name.length : Int) + 1 < 256 := by omega
  have hi0 : (0 : Int) ≤ (name.length : Int) + 1 := by omega
  have hlen2 : (1 : Int) ≤ (name.length : Int) + 5 := by omega
  have hbound : name.length + 1 < 32768 := by omega
  have ht : (name ++ [0]).take (name.length + 1) = name ++ [0] := by
    exact List.take_of_length_le (by simp)
  have htw : ∀ n : List UInt8, (0 : UInt8) ∉ n →
      (n ++ [0]).takeWhile (fun x => !decide (x = 0)) = n := by
    intro n
    induction n with
    | nil => simp
    | cons b bs ih =>
      intro h
      have hh : (0 : UInt8) ≠ b ∧ (0 : UInt8) ∉ bs := by simpa using h
      have hb : b ≠ 0 := Ne.symm hh.1
      simp [hb, ih hh.2]
  have hnonneg : ¬ ((name.length : Int) + 1 < 0) := by omega
  simp [flagOnlyFile, le16, readRaw, readRawAt, readU16, readI16, readU8, readExact,
    Rd.rest, Rd.eof, leSigned, alignEven, extendedterminfo, reinterpretInts,
    reinterpretIntsF, readStrings, readString, cstringAt, extendedNamesOffset,
    dictOfPairs, splitBar, hz, hn, hlen, hlen2, Nat.mod_eq_of_lt hn256,
    Int.emod_eq_of_lt hi0 hi256, hbound, hnonneg, ht, htw name hz, Except.map]

/-- `_terminfo_read_strings`: indices `-1` and `-2` give `nothing`, smaller ones
throw `ArgumentError`, and a nonnegative index gives the NUL-free bytes up to
the next NUL (`ArgumentError` if there is none), `base/terminfo.jl:141-162`;
`read(data, TermInfoRaw)` rejects data without one of the two magic numbers
(`base/terminfo.jl:74-81`). -/
def TermInfoStrings : Prop :=
  ∀ (table : List UInt8) (idx : Int) (a b : UInt8) (rest : List UInt8),
    (idx = -1 ∨ idx = -2 → readString table idx = .ok none) ∧
    (idx < -2 → readString table idx = .error (.argumentError "Terminfo table index is invalid")) ∧
    (0 ≤ idx → (0 : UInt8) ∈ table.drop idx.toNat →
      ∃ s, readString table idx = .ok (some s) ∧ (0 : UInt8) ∉ s ∧ s ++ [0] <+: table.drop idx.toNat) ∧
    (0 ≤ idx → (0 : UInt8) ∉ table.drop idx.toNat →
      readString table idx = .error (.argumentError "Terminfo table entry does not terminate with a null byte")) ∧
    (a.toNat + 256 * b.toNat ≠ 0o432 → a.toNat + 256 * b.toNat ≠ 0o1036 →
      readRaw (a :: b :: rest) = .error (.argumentError "Terminfo data did not start with the magic number 0o0432 or 0o01036"))

theorem takeWhile_ne_prefix (l : List UInt8) (h : (0 : UInt8) ∈ l) :
    l.takeWhile (· ≠ 0) ++ [0] <+: l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x = 0
    · subst hx; simp
    · have : (0 : UInt8) ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      simp only [List.takeWhile_cons, hx, ne_eq, not_false_eq_true, decide_true]
      exact List.prefix_cons_inj x |>.mpr (ih this)

theorem zero_not_mem_takeWhile (l : List UInt8) : (0 : UInt8) ∉ l.takeWhile (· ≠ 0) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x = 0
    · subst hx; simp
    · simp only [List.takeWhile_cons, hx, ne_eq, not_false_eq_true, decide_true, if_true, List.mem_cons]
      intro h
      rcases h with h | h
      · exact hx h.symm
      · exact ih h

theorem termInfoStrings_proven : TermInfoStrings := by
  intro table idx a b rest
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases h with h | h <;> subst h <;> simp [readString]
  · intro h
    have h1 : ¬ idx ≥ 0 := by omega
    have h2 : ¬ (idx = -1 ∨ idx = -2) := by omega
    simp [readString, h1, h2]
  · intro h0 hz
    refine ⟨(table.drop idx.toNat).takeWhile (· ≠ 0), ?_, ?_, takeWhile_ne_prefix _ hz⟩
    · simp [readString, h0, cstringAt, hz]
    · exact zero_not_mem_takeWhile _
  · intro h0 hz
    simp [readString, h0, cstringAt, hz]
  · intro h1 h2
    simp [readRaw, readRawAt, readU16, Rd.rest, h1, h2]

/-- `TermInfo` lookups: a key held by `flags`, `numbers` or `strings` is
returned directly (in that order), an absent key throws `KeyError`, `get`
resolves an alias before looking up, and `keys(ti)` is the union of the four
key sets (`base/terminfo.jl:214-229`). -/
def TermInfoLookup : Prop :=
  ∀ (ti : TI) (key : String) (fuel : Nat) (db : Bool) (di : Int) (ds : List UInt8),
    (hasKey ti.flags key = true → getindex (fuel + 1) ti key = .ok (.bool (getKey ti.flags key false))) ∧
    (hasKey ti.flags key = false → hasKey ti.numbers key = true →
      getindex (fuel + 1) ti key = .ok (.int (getKey ti.numbers key 0))) ∧
    (haskey ti key = false → getindex (fuel + 1) ti key = .error (.keyError key)) ∧
    getBool ti key db = getKey ti.flags (getKey ti.aliases key key) db ∧
    getInt ti key di = getKey ti.numbers (getKey ti.aliases key key) di ∧
    getStr ti key ds = getKey ti.strings (getKey ti.aliases key key) ds ∧
    (key ∈ keys ti ↔ haskey ti key = true)

theorem mem_pushSet (acc : List String) (x k : String) : k ∈ pushSet acc x ↔ k ∈ acc ∨ k = x := by
  unfold pushSet
  split
  · rename_i hx
    constructor
    · intro h; exact Or.inl h
    · rintro (h | rfl)
      · exact h
      · exact hx
  · simp

theorem mem_foldl_pushSet (l acc : List String) (k : String) :
    k ∈ l.foldl pushSet acc ↔ k ∈ acc ∨ k ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, mem_pushSet, List.mem_cons, or_assoc]

theorem termInfoLookup_proven : TermInfoLookup := by
  intro ti key fuel db di ds
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · intro h; simp [getindex, h]
  · intro h1 h2; simp [getindex, h1, h2]
  · intro h
    simp only [haskey, Bool.or_eq_false_iff] at h
    simp [getindex, h.1.1.1, h.1.1.2, h.1.2, h.2]
  · simp only [keys, mem_foldl_pushSet, List.not_mem_nil, false_or, List.mem_append, List.mem_map,
      haskey, hasKey, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]

/-- `TermInfo(raw)` keeps the terminal names and has extensions exactly when the
file had an extended section; `TermInfo()` is empty; `show(io, MIME"text/plain", ti)`
prints the names and the three capability counts, plus the extension count
when there are extensions (`base/terminfo.jl:69, 170-212, 231-237`). -/
def TermInfoBuild : Prop :=
  ∀ (tf tn ts : List Cap) (tu : Nat → String → Option String) (raw : Raw) (namesRepr : String) (ti : TI),
    (ofRaw tf tn ts tu raw).names = raw.names ∧
    ((ofRaw tf tn ts tu raw).extensions = none ↔ raw.extended = none) ∧
    blank = ⟨[], [], [], [], none, []⟩ ∧
    Out.text (showTI namesRepr ti) =
      "TermInfo(" ++ namesRepr ++ "; " ++ intStr ti.flags.length ++ " flags, " ++
      intStr ti.numbers.length ++ " numbers, " ++ intStr ti.strings.length ++ " strings" ++
      (match ti.extensions with
       | some e => ", " ++ intStr e.length ++ " extended capabilities"
       | none => "") ++ ")"

theorem termInfoBuild_proven : TermInfoBuild := by
  intro tf tn ts tu raw namesRepr ti
  refine ⟨?_, ?_, rfl, ?_⟩
  · unfold ofRaw; cases raw.extended <;> rfl
  · unfold ofRaw; cases raw.extended <;> simp
  · cases h : ti.extensions <;> simp [showTI, h, String.append_assoc]

/-- `find_terminfo_file(term)` returns `nothing` for an empty name and otherwise
either `nothing` or a path that is a file (`base/terminfo.jl:239-279`);
`load_terminfo` returns the blank `TermInfo` when no file is found or reading
throws an `ArgumentError`/`IOError`, the converted `TermInfo` when reading
succeeds, and rethrows other errors (`base/terminfo.jl:281-298`). -/
def TerminfoLoading : Prop :=
  ∀ (e : Env) (lower : String → String) (term : String) (readFile : String → ReadResult)
    (conv : Raw → TI) (p : String),
    findTerminfoFile e lower "" = .ok none ∧
    (findTerminfoFile e lower term = .ok (some p) → statCheck e.isfile p = .ok true) ∧
    (findTerminfoFile e lower term = .ok none → loadTerminfo e lower readFile conv term = .info blank) ∧
    (findTerminfoFile e lower term = .ok (some p) →
      (readFile p = .argumentError ∨ readFile p = .ioError) →
      loadTerminfo e lower readFile conv term = .info blank) ∧
    (findTerminfoFile e lower term = .ok (some p) → ∀ raw, readFile p = .ok raw →
      loadTerminfo e lower readFile conv term = .info (conv raw)) ∧
    (findTerminfoFile e lower term = .ok (some p) → readFile p = .otherError →
      loadTerminfo e lower readFile conv term = .rethrown)

theorem findTerminfoFile_go_isfile (e : Env) (lower : String → String)
    (term chr hex p : String) (dirs : List String)
    (h : findTerminfoFile.go e lower term chr hex dirs = .ok (some p)) :
    statCheck e.isfile p = .ok true := by
  induction dirs with
  | nil => simp [findTerminfoFile.go, pure, Except.pure] at h
  | cons d ds ih =>
    simp only [findTerminfoFile.go, bind, Except.bind, pure, Except.pure] at h
    cases h1 : statCheck e.isfile (joinpath [d, chr, term]) with
    | error err => simp [h1, Except.bind] at h
    | ok b =>
      cases b with
      | true => simp [h1, Except.bind, pure] at h; subst p; exact h1
      | false =>
        cases h2 : statCheck e.isfile (joinpath [d, hex, term]) with
        | error err => simp [h1, h2, Except.bind] at h
        | ok b =>
          cases b with
          | true => simp [h1, h2, Except.bind, pure] at h; subst p; exact h2
          | false =>
            cases h3 : statCheck e.isfile (joinpath [d, lower chr, lower term]) with
            | error err => simp [h1, h2, h3, Except.bind] at h
            | ok b =>
              cases b with
              | true => simp [h1, h2, h3, Except.bind, pure] at h; subst p; exact h3
              | false => apply ih; simpa [h1, h2, h3, Except.bind] using h

theorem findTerminfoFile_isfile (e : Env) (lower : String → String) (term p : String)
    (h : findTerminfoFile e lower term = .ok (some p)) :
    statCheck e.isfile p = .ok true := by
  unfold findTerminfoFile at h
  split at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · simp only [bind, Except.bind] at h
      cases hd : searchDirs e with
      | error err => simp [hd] at h
      | ok dirs =>
        apply findTerminfoFile_go_isfile e lower term _ _ p dirs
        simpa [hd] using h

theorem terminfoLoading_proven : TerminfoLoading := by
  intro e lower term readFile conv p
  refine ⟨?_, findTerminfoFile_isfile e lower term p, ?_, ?_, ?_, ?_⟩
  · simp [findTerminfoFile, pure, Except.pure]
  · intro h; simp [loadTerminfo, h]
  · intro h hr; rcases hr with hr | hr <;> simp [loadTerminfo, h, hr]
  · intro h raw hr; simp [loadTerminfo, h, hr]
  · intro h hr; simp [loadTerminfo, h, hr]

/-- Colour detection: on Windows `ttyhascolor()` is `true`, elsewhere it is
`haskey(terminfo, :setaf)`; `ttyhastruecolor()` is `true` when `COLORTERM` is
`truecolor` or `24bit`, or `TERM` starts with `linux`, `rxvt` or `st`, among the
documented conditions; the cached `get_have_color` returns the same value on
every call; the `TTY` dictionary methods expose exactly `:color`
(`base/terminfo.jl:314-391`). -/
def ColorDetection : Prop :=
  ∀ (ti : TI) (c : ColorEnv) (cache : Option Bool) (x y haveColor : Bool) (key : String) (v : Bool) (d : Bool),
    ttyhascolor true ti = true ∧ ttyhascolor false ti = haskey ti "setaf" ∧
    (c.env "COLORTERM" = some "truecolor" → ttyhastruecolor c ti = true) ∧
    (c.env "COLORTERM" = some "24bit" → ttyhastruecolor c ti = true) ∧
    (((c.env "TERM").getD "").startsWith "linux" = true → ttyhastruecolor c ti = true) ∧
    (getHaveCached (getHaveCached cache x).2 y).1 = (getHaveCached cache x).1 ∧
    (TermInfo.haskeyTTY key = true → TermInfo.getindexTTY haveColor key = .ok haveColor ∧
      TermInfo.getTTY haveColor key d = haveColor) ∧
    (TermInfo.haskeyTTY key = false → TermInfo.getindexTTY haveColor key = .error (.keyError key) ∧
      TermInfo.getTTY haveColor key d = d) ∧
    (TermInfo.inTTY haveColor key (some v) = true ↔ key = "color" ∧ v = haveColor) ∧
    TermInfo.inTTY haveColor key none = false

theorem colorDetection_proven : ColorDetection := by
  intro ti c cache x y haveColor key v d
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro h; simp [ttyhastruecolor, h]
  · intro h; simp [ttyhastruecolor, h]
  · intro h; simp [ttyhastruecolor, h]
  · cases cache <;> rfl
  · intro h; simp only [TermInfo.haskeyTTY, beq_iff_eq] at h; simp [TermInfo.getindexTTY, TermInfo.getTTY, h]
  · intro h; simp only [TermInfo.haskeyTTY, beq_eq_false_iff_ne, ne_eq] at h
    simp [TermInfo.getindexTTY, TermInfo.getTTY, h]
  · simp [TermInfo.inTTY]

end JuliaLean.ShowCov
