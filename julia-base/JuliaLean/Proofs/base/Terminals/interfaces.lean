import JuliaLean.base.Terminals
import JuliaLean.Proofs.base.terminfo.retained
import JuliaLean.Proofs.base.coreio.showSupport


namespace JuliaLean.ShowCov

open Terminals TermInfo

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

end JuliaLean.ShowCov
