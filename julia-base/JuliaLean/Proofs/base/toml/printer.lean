import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.Registry.Types
import JuliaLean.base.toml.printer


section

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

end

section

/-!
# `print_table` and the comment printers (`base/toml/printer.jl:182-393`)
-/

namespace JuliaLean.DocsSyntaxCov.TomlPrint

open JuliaLean JuliaLean.DocsSyntaxCov

/-! ## Comments -/

/-- A comment line starts with the indentation and `#`, ends with a newline, keeps tabs and
printable characters, drops other control characters, and continues every embedded newline
as a new `# ` line, so no comment text can introduce TOML syntax; an inline comment contains
no newline at all. Comments of a missing path print nothing. -/
def CommentSanitized : Prop :=
  (∀ (indent : Out) (text : CP), (∀ b ∈ indent, b = 32) →
    (printCommentLine indent text).getLast? = some 10 ∧
    (printCommentLine indent text).take (indent.length + 1) = indent ++ [35] ∧
    ∀ b ∈ printCommentLine indent text, b = 9 ∨ b = 10 ∨ okByte b) ∧
  (∀ (c : Comments) (path : List CP), ∀ b ∈ printCommentInline c path, b = 9 ∨ okByte b) ∧
  (∀ (c : Comments) (path : List CP) (indent : Out), lookup c.items path = none →
    printCommentsAbove c path indent = [] ∧ printCommentInline c path = []) ∧
  (∀ (c : Comments) (path : List CP) (indent : Out) (b : CommentBlock), lookup c.items path = some b →
    printCommentsAbove c path indent = b.above.flatMap (printCommentLine indent)) ∧
  (∀ (c : Comments) (path : List CP),
    hasComments c path = ((lookup c.items path).isSome || (lookup c.floating path).isSome)) ∧
  (∀ (c : Comments) (path : List CP) (indent : Out),
    printCommentsFloating c path indent =
      match lookup c.floating path with
      | none => ([], false)
      | some lines => (lines.flatMap (printCommentLine indent), !lines.isEmpty))

theorem lead_sp (text : CP) (b : Nat)
    (hb : b ∈ (match text with | [] => [] | c :: _ => if c == 32 || c == 9 then [] else [32] : Out)) :
    b = 32 := by
  split at hb
  · simp at hb
  · split at hb <;> simp at hb; omega

theorem commentLine_bytes (indent : Out) (text : CP) (hi : ∀ b ∈ indent, b = 32) :
    ∀ b ∈ printCommentLine indent text, b = 9 ∨ b = 10 ∨ okByte b := by
  have hsp : ∀ b ∈ indent, okByte b := fun b h => by rw [hi b h]; unfold okByte; decide
  have hch : ∀ c, ∀ b ∈ (if c == 10 then [10] ++ indent ++ [35, 32]
      else if c == 9 || !iscntrl c then enc c else []), b = 9 ∨ b = 10 ∨ okByte b := by
    intro c b hb
    by_cases h10 : c = 10
    · subst h10
      simp only [beq_self_eq_true, if_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with (rfl | hb) | rfl | rfl
      · right; left; rfl
      · exact Or.inr (Or.inr (hsp b hb))
      · right; right; unfold okByte; decide
      · right; right; unfold okByte; decide
    · by_cases h9 : c = 9
      · subst h9; simp [enc, Toml.utf8] at hb; left; exact hb
      · by_cases hc : iscntrl c = true
        · simp [h10, h9, hc] at hb
        · have hc' : iscntrl c = false := by simpa using hc
          simp [h10, h9, hc'] at hb
          exact Or.inr (Or.inr (enc_ok c hc' b hb))
  intro b hb
  unfold printCommentLine at hb
  simp only [List.mem_append, List.mem_flatMap] at hb
  rcases hb with (((hb | hb) | hb) | ⟨c, _, hc⟩) | hb
  · exact Or.inr (Or.inr (hsp b hb))
  · simp at hb; subst hb; right; right; unfold okByte; decide
  · rw [lead_sp text b hb]; right; right; unfold okByte; decide
  · exact hch c b hc
  · simp at hb; subst hb; right; left; rfl

theorem getLast?_snoc (l : List Nat) (a : Nat) : (l ++ [a]).getLast? = some a := by simp

theorem take_head (l r : List Nat) (a : Nat) : (l ++ a :: r).take (l.length + 1) = l ++ [a] := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem commentLine_last (indent : Out) (text : CP) :
    (printCommentLine indent text).getLast? = some 10 := by
  unfold printCommentLine; exact getLast?_snoc _ _

theorem commentLine_head (indent : Out) (text : CP) :
    (printCommentLine indent text).take (indent.length + 1) = indent ++ [35] := by
  unfold printCommentLine
  simp only [List.append_assoc, List.singleton_append]
  exact take_head _ _ _

theorem commentInline_bytes (c : Comments) (path : List CP) :
    ∀ b ∈ printCommentInline c path, b = 9 ∨ okByte b := by
  have hch : ∀ ch, ∀ b ∈ (if ch == 9 || (ch != 10 && !iscntrl ch) then enc ch else [32]),
      b = 9 ∨ okByte b := by
    intro ch b hb
    by_cases h9 : ch = 9
    · subst h9; simp [enc, Toml.utf8] at hb; left; exact hb
    · by_cases hc : iscntrl ch = false
      · by_cases h10 : ch = 10
        · subst h10; simp at hb; subst hb; right; unfold okByte; decide
        · simp [h9, h10, hc] at hb
          exact Or.inr (enc_ok ch hc b hb)
      · have hc' : iscntrl ch = true := by simpa using hc
        simp [h9, hc'] at hb; subst hb; right; unfold okByte; decide
  intro b hb
  unfold printCommentInline at hb
  split at hb
  · simp at hb
  · split at hb
    · simp at hb
    · rename_i text _
      simp only [List.mem_append, List.mem_flatMap] at hb
      rcases hb with ((hb | hb) | ⟨ch, _, hc⟩)
      · simp at hb; rcases hb with rfl | rfl <;> (right; unfold okByte; decide)
      · rw [lead_sp text b hb]; right; unfold okByte; decide
      · exact hch ch b hc

theorem commentSanitized : CommentSanitized := by
  refine ⟨fun indent text hi => ⟨commentLine_last indent text, commentLine_head indent text,
      commentLine_bytes indent text hi⟩, commentInline_bytes, ?_, ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩
  · intro c path indent h
    simp [printCommentsAbove, printCommentInline, h]
  · intro c path indent b h
    simp [printCommentsAbove, h]

/-! ## Table predicates -/

/-- `is_table` holds for dictionaries, `is_array_of_tables` for non-empty arrays of
dictionaries, `is_tabular` for either. -/
def TabularPredicates : Prop :=
  (∀ v, isTable v = true ↔ ∃ id kvs, v = .dict id kvs) ∧
  (∀ xs, isArrayOfTables (.arr xs) = (xs.length > 0 && xs.all isTable)) ∧
  (∀ v, (∀ xs, v ≠ .arr xs) → isArrayOfTables v = false) ∧
  (∀ v, isTabular v = (isTable v || isArrayOfTables v))

theorem tabularPredicates : TabularPredicates := by
  refine ⟨fun v => ?_, fun _ => rfl, fun v hv => ?_, fun _ => rfl⟩
  · cases v <;> simp [isTable]
  · cases v <;> simp [isArrayOfTables] <;> exact (hv _ rfl).elim

/-! ## `print_table` -/

/-- A printer environment with no comments, no conversion function, no inline tables, unsorted,
and floats printed as `1.0`. -/
def env0 : Env :=
  { toToml := none, extValid := fun _ => false, showFloat := fun _ => bytes% "1.0", byFn := id,
    inline := [], sorted := false, comments := none }

/-- The float printer produces TOML floats. -/
def FloatsValid (env : Env) : Prop :=
  ∀ x, Toml.accepted ((bytes% "a = ") ++ env.showFloat x ++ [10]) = true

/-- `TOML.print` writes TOML: whatever it prints parses. -/
def InlineArrayTableValid : Prop :=
  ∀ (env : Env), FloatsValid env → ∀ (id : Nat) (a : List (CP × TV)) (out : Out),
    printToml env id a = .ok out → Toml.accepted out = true

def envInline1 : Env := { env0 with inline := [1] }

/-- `Dict("a" => [inner])` with `inner = Dict("c" => 1)` in `inline_tables`. -/
def aotData : List (CP × TV) := [(bytes% "a", .arr [.dict 1 [(bytes% "c", .sint 1)]])]

theorem aot_print : printToml envInline1 0 aotData = .ok (bytes% "[[a]]\n{c = 1}") := by
  decide +kernel

theorem aot_rejected : Toml.accepted (bytes% "[[a]]\n{c = 1}") = false := by decide +kernel

theorem envInline1_floats : FloatsValid envInline1 := by
  intro _
  show Toml.accepted (bytes% "a = 1.0\n") = true
  decide +kernel

theorem inlineArrayTableValid_refuted : ¬ InlineArrayTableValid := by
  intro h
  have := h envInline1 envInline1_floats 0 aotData _ aot_print
  rw [aot_rejected] at this
  cases this

/-- A scalar value: no table, array or value needing conversion, and no string (which could
hold an invalid character). -/
def scalar : TV → Bool
  | .bool _ | .sint _ | .uint _ | .nan | .inf _ | .float _ | .date .. | .time .. | .datetime .. => true
  | _ => false

/-- With `sorted = true`, the keys of a table printed inline come in the order of `by`, as
the docstring promises for tables ("sort tables according to the function given by the
keyword argument `by`"). -/
def InlineSortedBy : Prop :=
  ∀ (env : Env) (n : Nat) (kvs : List (CP × TV)), env.sorted = true → (∀ kv ∈ kvs, scalar kv.2 = true) →
    printInlineTable env n kvs = printInlineTable { env with sorted := false } n (sortKeysBy env.byFn kvs)

/-- Reverse alphabetical order on one-letter keys. -/
def revBy (k : CP) : CP := k.map (255 - ·)

def envSortedRev : Env := { env0 with sorted := true, byFn := revBy }

def abData : List (CP × TV) := [(bytes% "a", .sint 1), (bytes% "b", .sint 2)]

theorem sorted_lhs : printInlineTable envSortedRev 4 abData = .ok (bytes% "{a = 1, b = 2}") := by
  decide +kernel

theorem sorted_rhs :
    printInlineTable { envSortedRev with sorted := false } 4 (sortKeysBy envSortedRev.byFn abData) =
      .ok (bytes% "{b = 2, a = 1}") := by
  decide +kernel

theorem inlineSortedBy_refuted : ¬ InlineSortedBy := by
  intro h
  have := h envSortedRev 4 abData rfl (by decide)
  rw [sorted_lhs, sorted_rhs] at this
  have := congrArg (fun r => match r with | .ok o => o | .error _ => []) this
  simp at this

/-- The output of a scalar under `printvalue` with enough fuel. -/
def scalarOut (env : Env) : TV → Out
  | .bool b => if b then bytes% "true" else bytes% "false"
  | .datetime y m d h mi s ms => printDate y m d ++ [84] ++ printTime h mi s ms ++ [90]
  | .time h mi s ms => printTime h mi s ms
  | .date y m d => printDate y m d
  | v@(.sint _) | v@(.uint _) => printInteger v
  | v@.nan | v@(.inf _) | v@(.float _) => printFloat env v
  | _ => []

theorem printvalue_scalar (env : Env) (n : Nat) (v : TV) (hv : scalar v = true) :
    printvalue env (n + 1) v = .ok (scalarOut env v) := by
  cases v <;> simp [scalar] at hv <;> rfl

theorem printSubtables_scalars (env : Env) (ks : List CP) (indent : Nat) :
    ∀ (kvs : List (CP × TV)) (n : Nat) (fb : Bool), kvs.length < n → (∀ kv ∈ kvs, scalar kv.2 = true) →
      printSubtables env n ks indent kvs fb = .ok []
  | [], n + 1, _, _, _ => by simp [printSubtables]
  | [], 0, _, h, _ => by simp at h
  | (k, v) :: rest, n + 1, fb, hl, hs => by
    have hv : scalar v = true := hs (k, v) (by simp)
    have hval : checkedValue env v = .ok v := by
      cases v <;> simp [scalar] at hv <;> rfl
    have ih := printSubtables_scalars env ks indent rest n fb (by simp at hl; omega)
      (fun kv h => hs kv (by simp [h]))
    simp only [printSubtables, hval, bind, Except.bind]
    cases v <;> simp [scalar] at hv <;> exact ih
  | _ :: _, 0, _, h, _ => by simp at h

theorem printEntries_scalars (env : Env) (fuel : Nat) (hc : env.comments = none) :
    ∀ (kvs : List (CP × TV)) (fb : Bool), (∀ kv ∈ kvs, scalar kv.2 = true ∧ bareKey kv.1 = true) →
      printEntries env (fuel + 1) [] [] kvs fb =
        .ok (kvs.flatMap (fun kv => kv.1.flatMap enc ++ (bytes% " = ") ++ scalarOut env kv.2 ++ [10]),
          if kvs.isEmpty then fb else false)
  | [], fb, _ => by simp [printEntries]
  | (k, v) :: rest, fb, hs => by
    obtain ⟨hv, hk⟩ := hs (k, v) (by simp)
    have hval : checkedValue env v = .ok v := by
      cases v <;> simp [scalar] at hv <;> rfl
    have htab : (isTabular v && !inInline env v) = false := by
      cases v <;> simp [scalar] at hv <;> rfl
    have hkey := printkeyForms.2.1 k hk
    have ih := printEntries_scalars env fuel hc rest false (fun kv h => hs kv (by simp [h]))
    simp only [printEntries, hval, bind, Except.bind, htab, Bool.false_eq_true, if_false, hc,
      printvalue_scalar env fuel v hv, hkey, ih]
    simp
    try (cases rest <;> simp)

/-- A table of scalars with bare keys prints one `key = value` line per entry, in `keys(d)`
order (or `by` order when sorted), with no headers. -/
def ScalarTableLines : Prop :=
  ∀ (env : Env) (id : Nat) (kvs : List (CP × TV)), env.comments = none → ¬ env.inline.contains id →
    (∀ kv ∈ kvs, scalar kv.2 = true ∧ bareKey kv.1 = true) →
    printToml env id kvs =
      .ok ((if env.sorted then sortKeysBy env.byFn kvs else kvs).flatMap
        (fun kv => kv.1.flatMap enc ++ (bytes% " = ") ++ scalarOut env kv.2 ++ [10]))

theorem sortBy_perm {α : Type} (lt : α → α → Bool) (xs : List α) : ∀ x, x ∈ sortBy lt xs ↔ x ∈ xs := by
  have ins : ∀ (y : α) (l : List α) (x : α), x ∈ insertBy lt y l ↔ x = y ∨ x ∈ l := by
    intro y l x
    induction l with
    | nil => simp [insertBy]
    | cons z zs ih =>
      unfold insertBy
      split <;> simp only [List.mem_cons, ih] <;> constructor <;> intro h <;>
        rcases h with h | h | h <;> simp [h]
  induction xs with
  | nil => simp [sortBy]
  | cons y ys ih =>
    intro x
    simp only [sortBy, List.foldr_cons] at ih ⊢
    rw [ins]; simp [ih]

theorem sortBy_length {α : Type} (lt : α → α → Bool) (xs : List α) : (sortBy lt xs).length = xs.length := by
  have ins : ∀ (y : α) (l : List α), (insertBy lt y l).length = l.length + 1 := by
    intro y l; induction l with
    | nil => rfl
    | cons z zs ih => unfold insertBy; split <;> simp [ih]
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [sortBy, List.foldr_cons] at ih ⊢; rw [ins, ih]; rfl

theorem printTable_scalars (env : Env) (m id : Nat) (kvs akeys : List (CP × TV))
    (hak : (if env.sorted then sortKeysBy env.byFn kvs else kvs) = akeys) (hc : env.comments = none)
    (hi : ¬ env.inline.contains id) (hs : ∀ kv ∈ akeys, scalar kv.2 = true ∧ bareKey kv.1 = true)
    (hlen : akeys.length < m + 1) :
    printTable env (m + 2) id kvs [] 0 true =
      .ok (akeys.flatMap (fun kv => kv.1.flatMap enc ++ (bytes% " = ") ++ scalarOut env kv.2 ++ [10])) := by
  have hent := printEntries_scalars env m hc akeys true hs
  have hsub := fun fb => printSubtables_scalars env [] 0 akeys (m + 1) fb hlen (fun kv h => (hs kv h).1)
  simp only [printTable, hi, hc, hak, Bool.false_eq_true, if_false, ↓reduceIte, spaces, Nat.zero_sub,
    Nat.mul_zero, List.replicate_zero, hent, exc_bind_ok, hsub, exc_pure]
  simp

theorem scalarTableLines : ScalarTableLines := by
  intro env id kvs hc hi hs
  have hs' : ∀ kv ∈ (if env.sorted then sortKeysBy env.byFn kvs else kvs),
      scalar kv.2 = true ∧ bareKey kv.1 = true := by
    intro kv h
    split at h
    · exact hs kv ((sortBy_perm _ kvs kv).mp h)
    · exact hs kv h
  have hlen : (if env.sorted then sortKeysBy env.byFn kvs else kvs).length = kvs.length := by
    split <;> simp [sortKeysBy, sortBy_length]
  have hsize : kvs.length < (TV.dict id kvs).size * 4 + 8 - 2 := by
    have : ∀ l : List (CP × TV), l.length ≤ TV.size.sizeKV l := by
      intro l; induction l with
      | nil => simp [TV.size.sizeKV]
      | cons kv r ih => obtain ⟨k, v⟩ := kv; simp [TV.size.sizeKV]; omega
    have := this kvs
    simp [TV.size]; omega
  unfold printToml
  obtain ⟨m, hm⟩ : ∃ m, (TV.dict id kvs).size * 4 + 8 = m + 2 := ⟨(TV.dict id kvs).size * 4 + 6, by omega⟩
  rw [hm]
  exact printTable_scalars env m id kvs _ rfl hc hi hs' (by rw [hlen]; omega)

/-- The four `TOML.print` methods are `print_table` with `f` (or `identity`) at the root:
`print(f, io, a)`, `print(f, a)` (to `stdout`), `print(io, a)` and `print(a)`. -/
def PrintApi : Prop :=
  ∀ (env : Env) (id : Nat) (a : List (CP × TV)),
    printToml env id a = printTable env ((TV.dict id a).size * 4 + 8) id a [] 0 true ∧
    printTomlStdout env id a = printToml env id a ∧
    printTomlIdentity env id a = printToml { env with toToml := none } id a ∧
    printTomlIdentityStdout env id a = printTomlIdentity env id a

theorem printApi : PrintApi := fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

end JuliaLean.DocsSyntaxCov.TomlPrint

end

section

/-! Row-specific properties not supplied by the initial area models. -/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

namespace Parse

open JuliaLean.ParsePrint.IntParse

end Parse

namespace TomlPrint

def HoistedCommentsBehavior : Prop :=
  (∀ c indent sorted kvs path, printHoisted c indent sorted 0 kvs path = []) ∧
  ∀ c indent sorted n kvs path, printHoisted c indent sorted (n + 1) kvs path =
    let fl := match lookup c.floating path with
      | none => [] | some lines => lines.flatMap (printCommentLine indent)
    let vkeys := if sorted then sortKeys kvs else kvs
    fl ++ vkeys.flatMap (fun (k, v) =>
      let kpath := path ++ [k]
      let blk := match lookup c.items kpath with
        | none => []
        | some b => b.above.flatMap (printCommentLine indent) ++
          (match b.inline with | none => [] | some t => printCommentLine indent t)
      blk ++ match v with | .dict _ kvs' => printHoisted c indent sorted n kvs' kpath | _ => [])

theorem hoistedCommentsBehavior : HoistedCommentsBehavior :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

end TomlPrint

namespace Binary

open JuliaLean.Platforms

end Binary

namespace TomlRows

open JuliaLean.Toml

end TomlRows

namespace Binary

open JuliaLean.Platforms

end Binary

namespace Syntax

end Syntax

end JuliaLean.DocsSyntaxCov

end

namespace JuliaLean.Proofs.base.toml.printer

open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-toml-print-escaped" "base/toml/printer.jl" ["print_toml_escaped"]
    "Escaped TOML output contains only valid bytes."
    "base/toml/printer.jl:7-33" ``TomlPrint.EscapedBytesValid ``TomlPrint.escapedBytesValid,
  proven "docssyntaxcov-toml-print-validity" "base/toml/printer.jl"
    ["is_valid_toml_value", "_is_valid_toml_value", "to_toml_value"]
    "TOML value validation and conversion follow the supported value types."
    "base/toml/printer.jl:38-43,66-75" ``TomlPrint.ValidityAndConversion ``TomlPrint.validityAndConversion,
  proven "docssyntaxcov-toml-print-key" "base/toml/printer.jl" ["printkey"]
    "TOML keys use bare form when valid and quoted escaped form otherwise."
    "base/toml/printer.jl:49-64" ``TomlPrint.PrintkeyForms ``TomlPrint.printkeyForms,
  proven "docssyntaxcov-toml-print-value" "base/toml/printer.jl" ["printvalue", "print_inline_table"]
    "TOML scalar, string, array and inline-table values use their specified syntax."
    "base/toml/printer.jl:82-173" ``TomlPrint.PrintvalueForms ``TomlPrint.printvalueForms,
  proven "docssyntaxcov-toml-print-comments" "base/toml/printer.jl"
    ["print_comment_line", "print_comments_above", "print_comment_inline", "has_comments", "print_comments_floating"]
    "Comment output is sanitized and attached only to its recorded path."
    "base/toml/printer.jl:182-225,252-259" ``TomlPrint.CommentSanitized ``TomlPrint.commentSanitized,
  proven "docssyntaxcov-toml-print-hoisted" "base/toml/printer.jl" ["print_hoisted_inline_comments"]
    "Hoisted inline comments traverse sorted or insertion-order table keys recursively."
    "base/toml/printer.jl:228-250" ``TomlPrint.HoistedCommentsBehavior ``TomlPrint.hoistedCommentsBehavior,
  proven "docssyntaxcov-toml-print-tabular" "base/toml/printer.jl" ["is_table", "is_array_of_tables", "is_tabular"]
    "Tabular predicates recognize dictionaries and nonempty arrays of dictionaries."
    "base/toml/printer.jl:265-270" ``TomlPrint.TabularPredicates ``TomlPrint.tabularPredicates,
  proven "docssyntaxcov-toml-print-table" "base/toml/printer.jl" ["print_table"]
    "Scalar tables produce one valid key-value line per entry."
    "base/toml/printer.jl:272-379" ``TomlPrint.ScalarTableLines ``TomlPrint.scalarTableLines,
  proven "docssyntaxcov-toml-print-api" "base/toml/printer.jl" ["print"]
    "All four print overloads delegate to root print_table with the requested conversion."
    "base/toml/printer.jl:386-393" ``TomlPrint.PrintApi ``TomlPrint.printApi,
  refuted "docssyntaxcov-toml-print-inline-array-table" "base/toml/printer.jl" ["print_table", "print"]
    "Every TOML.print result parses as TOML."
    "stdlib/TOML/src/TOML.jl print docstring"
    "none found (queries: TOML print, TOML print inline_tables, TOML print array of tables inline)"
    "An inline-marked element in an array of tables prints as a bare inline table after [[a]]."
    ``TomlPrint.InlineArrayTableValid ``TomlPrint.inlineArrayTableValid_refuted,
  refuted "docssyntaxcov-toml-print-by-inline" "base/toml/printer.jl"
    ["print_inline_table", "print_hoisted_inline_comments", "print"]
    "sorted=true applies the by function to inline tables."
    "stdlib/TOML/src/TOML.jl print docstring"
    "#46385 (closed, related); queries: TOML print sorted by, TOML inline table"
    "Inline tables use plain key sorting and ignore by."
    ``TomlPrint.InlineSortedBy ``TomlPrint.inlineSortedBy_refuted,
]

end JuliaLean.Proofs.base.toml.printer
