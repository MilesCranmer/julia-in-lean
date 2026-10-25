import JuliaLean.ShellCmd.Props

/-! # Refutations: concrete counterexamples, checked by `decide` -/

namespace JuliaLean.ShellCmd

/-- `'é'`. -/
def eAcute : JC := 0xc3a90000

/-- `shell_split("    é\\\n x") == ["é"]`: the continuation skips one byte too many. -/
theorem lineContinuationJoins_refuted : ¬ LineContinuationJoins := by
  intro h
  have := h 4 [eAcute] [A ' '] [A 'x'] (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- `shell_split("a\\\t")` throws "dangling backslash". -/
theorem splitEscapedTrailingWhitespace_refuted : ¬ SplitEscapedTrailingWhitespace := by
  intro h
  have := h (A '\t') (by decide)
  revert this; decide

/-- `shell_escape_posixly("done")` is `done`. -/
theorem posixlyNoReservedWord_refuted : ¬ PosixlyNoReservedWord := by
  intro h
  have := h (S "done") []
  revert this; decide

/-- `shell_escape_csh()` and `escape_microsoft_c_args()` throw. -/
theorem escapeEmptyArgs_refuted : ¬ EscapeEmptyArgs := by
  intro h
  obtain ⟨⟨e, h1⟩, _⟩ := h []
  have he : shellEscapeCsh [] = .error emptyReduceErr := by decide
  rw [he] at h1
  cases h1

/-- `shell_escape_wincmd("%")` returns `"%"`. -/
theorem wincmdPercentThrows_refuted : ¬ WincmdPercentThrows := by
  intro h
  obtain ⟨msg, h1⟩ := h [A '%'] (by decide) (by decide) (by decide) (by decide)
  have he : shellEscapeWincmd [A '%'] = .ok [A '%'] := by decide
  rw [he] at h1
  cases h1

/-- `Cmd(["\\`"])` prints as `` `'\\`'` ``, which ends after `'\`. -/
theorem showLexesBackslash_refuted : ¬ ShowLexesBackslash := by
  intro h
  have := h [S "\\`"] (by decide)
  revert this; decide

/-- `Cmd(["\r"])` prints a raw carriage return, which lexes as `\n`. -/
theorem showLexesCR_refuted : ¬ ShowLexesCR := by
  intro h
  have := h [[A '\r']] (by decide)
  revert this; decide

/-- `Cmd(["\xff"])` prints a raw invalid byte, which does not lex. -/
theorem showLexesUtf8_refuted : ¬ ShowLexesUtf8 := by
  intro h
  have := h [[0xff000000]] (by decide)
  revert this; decide

/-- `show(setuid(cmd, 0x80000000))` throws `InexactError`. -/
theorem showUidTotal_refuted : ¬ ShowUidTotal := by
  intro h
  have := h [] 0x80000000
  revert this; decide

/-- `show(setenv(cmd, "é" => "1"))` throws `StringIndexError`. -/
theorem showEnvTotal_refuted : ¬ ShowEnvTotal := by
  intro h
  have hc : setenvPairs (cmdOf []) [([eAcute], [A '1'])] =
      .ok { cmdOf [] with env := some [[eAcute, A '=', A '1']] } := by decide
  have := h [] [eAcute] [A '1'] .redact (fun _ => false) _ (by decide) (by decide) hc
  revert this; decide

/-- `setcpuaffinity(cmd, [1]) == cmd`. -/
theorem cmdEqFieldwise_refuted : ¬ CmdEqFieldwise := by
  intro h
  have := h (cmdOf []) (setcpuaffinity (cmdOf []) [1]) (by decide)
  revert this; decide

/-- `addenv(setenv(cmd, "é" => "1"), "A" => "2")` throws `StringIndexError`. -/
theorem addenvSets_refuted : ¬ AddenvSets := by
  intro h
  have hc : setenvPairs (cmdOf []) [([eAcute], [A '1'])] =
      .ok { cmdOf [] with env := some [[eAcute, A '=', A '1']] } := by decide
  obtain ⟨c', h1, _⟩ := h [] [] [eAcute] [A '1'] [A 'A'] [A '2'] _
    (by decide) (by decide) (by decide) (by decide) (by decide) hc
  have he : addenv [] true { cmdOf [] with env := some [[eAcute, A '=', A '1']] }
      [([A 'A'], some [A '2'])] = .error .stringIndex := by decide
  rw [he] at h1
  cases h1

end JuliaLean.ShellCmd
