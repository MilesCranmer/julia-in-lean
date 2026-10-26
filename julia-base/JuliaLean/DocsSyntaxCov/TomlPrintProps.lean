import JuliaLean.DocsSyntaxCov.TomlPrint

/-!
# Properties of the TOML printer (`base/toml/printer.jl`)
-/

namespace JuliaLean.DocsSyntaxCov.TomlPrint

open JuliaLean JuliaLean.DocsSyntaxCov

/-- A byte that may appear raw in a TOML basic string or comment (TOML v1.1.0: control
characters other than tab are not allowed). -/
def okByte (b : Nat) : Prop := 32 ≤ b ∧ b ≠ 127

theorem enc_ok (c : Nat) (h : iscntrl c = false) : ∀ b ∈ enc c, okByte b := by
  unfold iscntrl at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff] at h
  intro b hb
  unfold enc Toml.utf8 at hb
  unfold okByte
  split at hb
  · simp at hb; omega
  · split at hb
    · simp at hb; omega
    · split at hb
      · simp at hb; omega
      · simp at hb; omega

theorem hexPad_ok : ∀ c, c < 160 → ∀ b ∈ hexPad c 4, okByte b := by
  unfold okByte; decide +kernel

/-! ## `print_toml_escaped` -/

/-- Every character becomes its TOML escape (`\b \t \n \f \r \" \\`), `\uXXXX` for other control
characters, or itself; invalid characters throw. Hence the escaped text of a string never
contains a raw control character, so it is a valid TOML basic-string body. -/
def EscapedBytesValid : Prop :=
  (∀ c, isvalidChar c = false → ∃ m, escapeChar c = .error (.errorException m)) ∧
  (escapeChar 8 = .ok [92, 98] ∧ escapeChar 9 = .ok [92, 116] ∧ escapeChar 10 = .ok [92, 110] ∧
    escapeChar 12 = .ok [92, 102] ∧ escapeChar 13 = .ok [92, 114] ∧ escapeChar 34 = .ok [92, 34] ∧
    escapeChar 92 = .ok [92, 92]) ∧
  (∀ c, isvalidChar c = true → iscntrl c = false → c ≠ 34 → c ≠ 92 → escapeChar c = .ok (enc c)) ∧
  ∀ (s : CP) (out : Out), printTomlEscaped s = .ok out → ∀ b ∈ out, okByte b

theorem escapeChar_ok (c : Nat) (out : Out) (h : escapeChar c = .ok out) : ∀ b ∈ out, okByte b := by
  unfold escapeChar at h
  by_cases hv : isvalidChar c = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, if_false] at h
    by_cases h8 : c = 8
    · subst h8; simp at h; subst h; unfold okByte; decide
    by_cases h9 : c = 9
    · subst h9; simp at h; subst h; unfold okByte; decide
    by_cases h10 : c = 10
    · subst h10; simp at h; subst h; unfold okByte; decide
    by_cases h12 : c = 12
    · subst h12; simp at h; subst h; unfold okByte; decide
    by_cases h13 : c = 13
    · subst h13; simp at h; subst h; unfold okByte; decide
    by_cases h34 : c = 34
    · subst h34; simp at h; subst h; unfold okByte; decide
    by_cases h92 : c = 92
    · subst h92; simp at h; subst h; unfold okByte; decide
    simp only [beq_iff_eq, h8, h9, h10, h12, h13, h34, h92, if_false] at h
    by_cases hc : iscntrl c = true
    · simp only [hc, if_true] at h
      injection h with h; subst h
      intro b hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with (rfl | rfl) | hb
      · unfold okByte; decide
      · unfold okByte; decide
      · have : c < 160 := by unfold iscntrl at hc; simp at hc; omega
        exact hexPad_ok c this b hb
    · simp only [hc, Bool.false_eq_true, if_false] at h
      injection h with h; subst h
      exact enc_ok c (by simpa using hc)
  · simp only [Bool.not_eq_true] at hv
    simp [hv] at h

theorem printTomlEscaped_ok : ∀ (s : CP) (out : Out), printTomlEscaped s = .ok out → ∀ b ∈ out, okByte b
  | [], out, h => by simp [printTomlEscaped] at h; subst h; simp
  | c :: cs, out, h => by
    simp only [printTomlEscaped] at h
    cases ha : escapeChar c with
    | error e => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      cases hb : printTomlEscaped cs with
      | error e => rw [hb] at h; cases h
      | ok b' =>
        rw [hb] at h
        injection h with h; subst h
        intro b hm
        rcases List.mem_append.mp hm with hm | hm
        · exact escapeChar_ok c a ha b hm
        · exact printTomlEscaped_ok cs b' hb b hm

theorem escapedBytesValid : EscapedBytesValid := by
  refine ⟨fun c hc => ⟨"TOML print: invalid character", by simp [escapeChar, hc]⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, printTomlEscaped_ok⟩
  intro c hv hc h34 h92
  have h8 : c ≠ 8 := by intro h; subst h; simp [iscntrl] at hc
  have h9 : c ≠ 9 := by intro h; subst h; simp [iscntrl] at hc
  have h10 : c ≠ 10 := by intro h; subst h; simp [iscntrl] at hc
  have h12 : c ≠ 12 := by intro h; subst h; simp [iscntrl] at hc
  have h13 : c ≠ 13 := by intro h; subst h; simp [iscntrl] at hc
  simp [escapeChar, hv, hc, h8, h9, h10, h12, h13, h34, h92]

/-! ## Validity, keys and conversion -/

/-- `_is_valid_toml_value` accepts every `BaseTOMLValue` and, for other types, defers to the
user's `is_valid_toml_value` methods; `to_toml_value` throws when no conversion function is
given or it returns an invalid value, and returns the converted value otherwise. -/
def ValidityAndConversion : Prop :=
  ∀ (env : Env),
    (∀ tag, isValid env (.other tag) = env.extValid tag) ∧
    (∀ v, (∀ tag, v ≠ .other tag) → isValid env v = true) ∧
    (∀ v, isValidTomlValue env.extValid v = match v with | .other tag => env.extValid tag | _ => true) ∧
    (env.toToml = none → ∀ v, ∃ m, toTomlValue env v = .error (.errorException m)) ∧
    (∀ f tag, env.toToml = some f → isValid env (f tag) = true → toTomlValue env (.other tag) = .ok (f tag)) ∧
    (∀ f tag, env.toToml = some f → isValid env (f tag) = false →
      ∃ m, toTomlValue env (.other tag) = .error (.errorException m))

theorem validityAndConversion : ValidityAndConversion := by
  intro env
  refine ⟨fun tag => by simp [isValid, isValidTomlValue], ?_, fun v => by cases v <;> rfl, ?_, ?_, ?_⟩
  · intro v hv
    cases v <;> simp [isValid] <;> exact (hv _ rfl).elim
  · intro h v
    cases v <;> simp [toTomlValue, h]
  · intro f tag h hv
    simp [toTomlValue, h, hv]
  · intro f tag h hv
    simp [toTomlValue, h, hv]

/-- A key is bare when it is non-empty and every character is in `A-Za-z0-9_-`. -/
def bareKey (k : CP) : Bool := !k.isEmpty && k.all bareChar

/-- `printkey` prints an empty key as `""`, a bare key as itself, any other key quoted and
escaped, and joins the parts of a dotted key with `.`. -/
def PrintkeyForms : Prop :=
  printkey [[]] = .ok [34, 34] ∧
  (∀ k, bareKey k = true → printkey [k] = .ok (k.flatMap enc)) ∧
  (∀ k e, k ≠ [] → k.any (fun c => !bareChar c) = true → printTomlEscaped k = .ok e →
    printkey [k] = .ok ([34] ++ e ++ [34])) ∧
  (∀ k k' ks a b, printOneKey k = .ok a → printkey (k' :: ks) = .ok b →
    printkey (k :: k' :: ks) = .ok (a ++ [46] ++ b))

theorem printkeyForms : PrintkeyForms := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro k hk
    unfold bareKey at hk
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at hk
    have h1 : k.length ≠ 0 := by
      intro h; exact hk.1 (List.eq_nil_of_length_eq_zero h)
    have h2 : k.any (fun c => !bareChar c) = false := by
      simp only [List.any_eq_false, Bool.not_eq_true', Bool.not_eq_false]
      intro c hc; simpa using hk.2 c hc
    simp [printkey, printOneKey, h1, h2]
  · intro k e hk hany he
    have h1 : k.length ≠ 0 := by intro h; exact hk (List.eq_nil_of_length_eq_zero h)
    simp [printkey, printOneKey, h1, hany, he]
  · intro k k' ks a b ha hb
    simp [printkey, ha] at hb ⊢
    rw [hb]; rfl

/-! ## Values -/

/-- Booleans print as `true`/`false`, signed integers in decimal, unsigned integers as `0x` and
`2 * ndigits(n, base=256)` hex digits, NaN and infinities as `nan`, `+inf`, `-inf`, dates
`YYYY-MM-DD`, times `HH:MM:SS[.mmm]`, date-times `dateTtimeZ`, strings in `"` (or `"""`
when they contain a newline), arrays as `[x, y]`, and dictionaries as inline tables. -/
def PrintvalueForms : Prop :=
  ∀ (env : Env) (n : Nat),
    (∀ b, printvalue env (n + 1) (.bool b) = .ok (if b then (bytes% "true") else (bytes% "false"))) ∧
    (∀ i, printvalue env (n + 1) (.sint i) = .ok (showInt i)) ∧
    (∀ u, printvalue env (n + 1) (.uint u) = .ok ((bytes% "0x") ++ hexPad u (2 * (Nat.toDigits 256 u).length))) ∧
    printvalue env (n + 1) .nan = .ok ((bytes% "nan")) ∧
    printvalue env (n + 1) (.inf true) = .ok ((bytes% "+inf")) ∧
    printvalue env (n + 1) (.inf false) = .ok ((bytes% "-inf")) ∧
    (∀ x, printvalue env (n + 1) (.float x) = .ok (env.showFloat x)) ∧
    (∀ y m d, printvalue env (n + 1) (.date y m d) = .ok (printDate y m d)) ∧
    (∀ h mi s ms, printvalue env (n + 1) (.time h mi s ms) = .ok (printTime h mi s ms)) ∧
    (∀ y m d h mi s ms, printvalue env (n + 1) (.datetime y m d h mi s ms) =
      .ok (printDate y m d ++ [84] ++ printTime h mi s ms ++ [90])) ∧
    (∀ s e, printTomlEscaped s = .ok e → printvalue env (n + 1) (.str s) =
      .ok ((if s.contains 10 then (bytes% "\"\"\"") else (bytes% "\"")) ++ e ++
        (if s.contains 10 then (bytes% "\"\"\"") else (bytes% "\"")))) ∧
    printvalue env (n + 2) (.arr []) = .ok [91, 93] ∧
    (∀ x o, printvalue env n x = .ok o → printvalue env (n + 2) (.arr [x]) = .ok ([91] ++ o ++ [93])) ∧
    (∀ id, printvalue env (n + 3) (.dict id []) = .ok [123, 125]) ∧
    (∀ tag tv o, toTomlValue env (.other tag) = .ok tv → printvalue env n tv = .ok o →
      printvalue env (n + 1) (.other tag) = .ok o)

theorem printvalueForms : PrintvalueForms := by
  intro env n
  refine ⟨fun b => rfl, fun i => rfl, fun u => rfl, rfl, rfl, rfl, fun x => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, ?_, rfl, ?_, fun id => ?_, ?_⟩
  · intro s e he
    simp [printvalue, printString, he]
  · intro x o h
    simp [printvalue, printItems, h]
  · cases hs : env.sorted <;> simp [printvalue, printInlineTable, printInlineEntries, sortKeys, sortBy, hs]
  · intro tag tv o h1 h2
    simp [printvalue, h1, h2]

/-- Times print `ms` only when it is non-zero, with three digits; the fields are padded to
two (year: four) digits with leading zeros. -/
def TimeDateDigits : Prop :=
  (∀ h mi s, printTime h mi s 0 = decPad h 2 ++ [58] ++ decPad mi 2 ++ [58] ++ decPad s 2) ∧
  (∀ h mi s ms, ms ≠ 0 → printTime h mi s ms =
    decPad h 2 ++ [58] ++ decPad mi 2 ++ [58] ++ decPad s 2 ++ [46] ++ decPad ms 3) ∧
  (∀ y m d, printDate y m d = decPad y 4 ++ [45] ++ decPad m 2 ++ [45] ++ decPad d 2) ∧
  ∀ (n : Nat) (p : Nat), decPad n p =
    List.replicate (p - (Nat.toDigits 10 n).length) 48 ++ (Nat.toDigits 10 n).map Char.toNat

theorem timeDateDigits : TimeDateDigits := by
  refine ⟨fun h mi s => by simp [printTime], fun h mi s ms hms => by simp [printTime, hms],
    fun _ _ _ => rfl, ?_⟩
  intro n p
  simp [decPad]

end JuliaLean.DocsSyntaxCov.TomlPrint
