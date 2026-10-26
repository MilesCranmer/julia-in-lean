import JuliaLean.DocsSyntaxCov.TomlPrintProps

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
