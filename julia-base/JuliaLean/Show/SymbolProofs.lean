import JuliaLean.Show.Symbol
import JuliaLean.Show.EscapeProofs

/-!
# Properties of symbol printing
-/

namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- The bytes `var"`. -/
def varPrefix : List UInt8 := asc ['v', 'a', 'r', '"']

/-! ## Statements -/

/-- `repr(sym)` (`show(io, ::Symbol)`) succeeds for every symbol, i.e. every
name without NUL. -/
def SymbolReprTotal : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ name : JStr, 0 ∉ name.bytes →
    ∃ out, showSymbol d o name = .ok out

/-- `show_sym` prints a name that can stand as a field of `@NamedTuple{...}`:
`@NamedTuple` (`base/namedtuple.jl:514-523`) accepts only `name` or
`name::type` entries, and `name` is an identifier or a `var"..."` literal. -/
def NamedTupleFieldName : Prop :=
  ∀ (d : UData) (o : OpData), o.Faithful → ∀ (name : JStr) (out : List UInt8),
    showSym d o name = .ok out →
      (∃ t : JStr, t.bytes = out ∧ isidentifier d t = .ok true) ∨ out.take 4 = varPrefix

/-- `show_sym` "escape[s] invalid identifiers with var\"\" syntax"
(`base/show.jl:1864-1866`): a `var"..."` it prints parses back to the same name. -/
def ShowSymVarRoundTrip : Prop :=
  ∀ (d : UData) (o : OpData) (name : JStr) (out : List UInt8), showSym d o name = .ok out →
    out = name.bytes ∨ ∃ e, out = varPrefix ++ e ++ [0x22] ∧ rawDecode e = some name.bytes

/-! ## Counterexamples -/

/-- The one-byte name `"\x80"`. -/
def name80 : JStr := ⟨[0x80], by decide⟩

/-- The name `"+"`. -/
def namePlus : JStr := ⟨[0x2b], by decide⟩

/-- The name `"\r"`. -/
def nameCR : JStr := ⟨[0x0d], by decide⟩

theorem symbolReprTotal_refuted : ¬ SymbolReprTotal := by
  intro h
  obtain ⟨out, hout⟩ := h UData.empty opsFaithful opsFaithful_faithful name80 (by decide)
  have e : (showSymbol UData.empty opsFaithful name80).isOk = false := by decide
  rw [hout] at e
  cases e

theorem namedTupleFieldName_refuted : ¬ NamedTupleFieldName := by
  intro h
  have e : (showSym UData.empty opsFaithful namePlus).toOption = some [0x2b] := by decide
  cases hs : showSym UData.empty opsFaithful namePlus with
  | error _ => rw [hs] at e; simp [Except.toOption] at e
  | ok out =>
    rw [hs] at e
    have ho : out = [0x2b] := by simpa [Except.toOption] using e
    subst ho
    rcases h UData.empty opsFaithful opsFaithful_faithful namePlus [0x2b] hs with ⟨t, ht, hid⟩ | hp
    · have htn : t = namePlus := jstr_ext ht
      subst htn
      have e2 : (isidentifier UData.empty namePlus).toOption = some false := by decide
      rw [hid] at e2
      simp [Except.toOption] at e2
    · revert hp; decide

theorem showSymVarRoundTrip_refuted : ¬ ShowSymVarRoundTrip := by
  intro h
  have e : (showSym UData.empty opsFaithful nameCR).toOption = some (varPrefix ++ [0x0d] ++ [0x22]) := by
    decide
  cases hs : showSym UData.empty opsFaithful nameCR with
  | error _ => rw [hs] at e; simp [Except.toOption] at e
  | ok out =>
    rw [hs] at e
    have ho : out = varPrefix ++ [0x0d] ++ [0x22] := by simpa [Except.toOption] using e
    subst ho
    rcases h UData.empty opsFaithful nameCR _ hs with h1 | ⟨b, hb, hd⟩
    · revert h1; decide
    · have : b = [0x0d] := by
        have h' := hb
        simp at h'
        have h2 : [0x0d] ++ [0x22] = b ++ [0x22] := h'
        exact (List.append_cancel_right h2).symm
      subst this
      revert hd; decide

/-! ## `escape_raw_string` on bytes -/

/-- `escRawLoop` with `delim = '"'` on bytes. -/
def escRawB : Nat → List UInt8 → List UInt8 × Nat
  | escapes, [] => (List.replicate escapes 0x5c, escapes)
  | escapes, b :: bs =>
    if b = 0x5c then ((0x5c : UInt8) :: (escRawB (escapes + 1) bs).1, (escRawB (escapes + 1) bs).2)
    else if b = 0x22 then
      (List.replicate (escapes + 1) 0x5c ++ (0x22 : UInt8) :: (escRawB 0 bs).1, escapes + 1 + (escRawB 0 bs).2)
    else (b :: (escRawB 0 bs).1, (escRawB 0 bs).2)

theorem escRawB_plain : ∀ (w rest : List UInt8) (e : Nat), w ≠ [] → (∀ x ∈ w, 0x80 ≤ x) →
    escRawB e (w ++ rest) = (w ++ (escRawB 0 rest).1, (escRawB 0 rest).2)
  | [], _, _, h, _ => absurd rfl h
  | [x], rest, e, _, hw => by
    have hx := hw x (by simp)
    have n1 : x ≠ 0x5c := by intro h; rw [h] at hx; revert hx; decide
    have n2 : x ≠ 0x22 := by intro h; rw [h] at hx; revert hx; decide
    simp [escRawB, n1, n2]
  | x :: y :: w, rest, e, _, hw => by
    have hx := hw x (by simp)
    have n1 : x ≠ 0x5c := by intro h; rw [h] at hx; revert hx; decide
    have n2 : x ≠ 0x22 := by intro h; rw [h] at hx; revert hx; decide
    have ih := escRawB_plain (y :: w) rest 0 (by simp) (fun z hz => hw z (by simp [hz]))
    simp only [List.cons_append, escRawB, n1, n2, if_false] at ih ⊢
    rw [ih]

theorem bs_char : writeChar (ac 0x5c) = [0x5c] := by decide
theorem q_char : writeChar (ac 0x22) = [0x22] := by decide

theorem escRawLoop_bytes : ∀ (cs : List UInt32) (e : Nat), (∀ c ∈ cs, GoodChar c) →
    escRawLoop (ac 0x22) e cs = escRawB e (cs.flatMap writeChar)
  | [], e, _ => rfl
  | c :: cs, e, hg => by
    have ih0 := escRawLoop_bytes cs 0 (fun x hx => hg x (by simp [hx]))
    have ih1 := escRawLoop_bytes cs (e + 1) (fun x hx => hg x (by simp [hx]))
    simp only [List.flatMap_cons]
    by_cases h1 : c = ac 0x5c
    · subst h1
      simp only [escRawLoop, if_pos, bs_char, ih1]
      simp [escRawB]
    by_cases h2 : c = ac 0x22
    · subst h2
      simp only [escRawLoop, if_neg h1, if_pos rfl, q_char, ih0]
      simp [escRawB]
    simp only [escRawLoop, if_neg h1, if_neg h2, ih0]
    rcases hg c (by simp) with ⟨b, hb, hw⟩ | ⟨hne, hall⟩
    · have n1 : b ≠ 0x5c := by intro e; apply h1; rw [hb, e]; decide
      have n2 : b ≠ 0x22 := by intro e; apply h2; rw [hb, e]; decide
      rw [hw]
      simp [escRawB, n1, n2]
    · rw [escRawB_plain _ _ _ hne hall]

theorem escRawB_total0 : ∀ (x : List UInt8) (e : Nat), (escRawB e x).2 = 0 → (escRawB e x).1 = x
  | [], e, h => by simp [escRawB] at h ⊢; exact h
  | b :: bs, e, h => by
    by_cases h1 : b = 0x5c
    · subst h1; simp [escRawB] at h ⊢; exact escRawB_total0 bs (e + 1) h
    by_cases h2 : b = 0x22
    · subst h2; simp [escRawB] at h
    simp [escRawB, h1, h2] at h ⊢; exact escRawB_total0 bs 0 h

theorem escapeRawString_eq (s : JStr) : escapeRawString s = (escRawB 0 s.bytes).1 := by
  obtain ⟨hb, hg⟩ := chars_spec s
  have he : escRawLoop (ac 0x22) 0 (chars s) = escRawB 0 s.bytes := by rw [escRawLoop_bytes _ 0 hg, hb]
  unfold escapeRawString
  simp only []
  rw [he]
  by_cases ht : (escRawB 0 s.bytes).2 = 0
  · rw [if_pos ht]
    exact (escRawB_total0 s.bytes 0 ht).symm
  · rw [if_neg ht]

/-! ## Reading the escaped body back -/

theorem nBS_bs (z : List UInt8) : nBS (0x5c :: z) = nBS z + 1 := by
  simp [nBS, List.takeWhile_cons]

theorem nBS_other (b : UInt8) (z : List UInt8) (h : b ≠ 0x5c) : nBS (b :: z) = 0 := by
  simp [nBS, List.takeWhile_cons, h]

theorem nBS_rep : ∀ (m : Nat) (z : List UInt8), nBS (List.replicate m 0x5c ++ z) = m + nBS z
  | 0, z => by simp
  | m + 1, z => by rw [List.replicate_succ, List.cons_append, nBS_bs, nBS_rep m z]; omega

theorem drop_rep : ∀ (m : Nat) (z : List UInt8), (List.replicate m (0x5c : UInt8) ++ z).drop m = z
  | 0, _ => rfl
  | m + 1, z => by rw [List.replicate_succ, List.cons_append, List.drop_succ_cons, drop_rep m z]

theorem rawScan_bs (f : Nat) (r : List UInt8) : rawScan 0x22 (f + 1) (0x5c :: r) =
    match r.drop (1 + nBS r - 1) with
    | x :: r' => if x = 0x22 ∧ (1 + nBS r) % 2 = 1 then rawScan 0x22 f r' else rawScan 0x22 f (x :: r')
    | [] => rawScan 0x22 f [] := rfl

theorem unescRaw_bs (g : Nat) (r : List UInt8) : unescRaw 0x22 (g + 1) (0x5c :: r) =
    match r.drop (1 + nBS r - 1) with
    | [] => List.replicate ((1 + nBS r) / 2) 0x5c
    | x :: r' => List.replicate (if x = 0x22 then (1 + nBS r) / 2 else 1 + nBS r) 0x5c ++
        x :: unescRaw 0x22 g r' := rfl

theorem unescRaw_plain (g : Nat) (b : UInt8) (r : List UInt8) (h1 : b ≠ 0x5c) (h2 : b ≠ 0x0d) :
    unescRaw 0x22 (g + 1) (b :: r) = b :: unescRaw 0x22 g r := by
  have e : unescRaw 0x22 (g + 1) (b :: r) =
      if b ≠ 0x5c then
        (if b = 0x0d then
          (match r with
            | 0x0a :: r' => 0x0a :: unescRaw 0x22 g r'
            | _ => 0x0a :: unescRaw 0x22 g r)
        else b :: unescRaw 0x22 g r)
      else
        (match r.drop (1 + nBS r - 1) with
          | [] => List.replicate ((1 + nBS r) / 2) 0x5c
          | x :: r' => List.replicate (if x = 0x22 then (1 + nBS r) / 2 else 1 + nBS r) 0x5c ++
              x :: unescRaw 0x22 g r') := rfl
  rw [e, if_pos h1, if_neg h2]

theorem rawScan_plain (f : Nat) (b : UInt8) (r : List UInt8) (h1 : b ≠ 0x5c) (h2 : b ≠ 0x22) :
    rawScan 0x22 (f + 1) (b :: r) = rawScan 0x22 f r := by
  rw [rawScan, if_neg h2, if_neg h1]

theorem rs_cons (n : Nat) (x : UInt8) (r' : List UInt8) (f : Nat) (hx : x ≠ 0x5c) :
    rawScan 0x22 (f + 1) (List.replicate (n + 1) 0x5c ++ x :: r') =
      if x = 0x22 ∧ (n + 1) % 2 = 1 then rawScan 0x22 f r' else rawScan 0x22 f (x :: r') := by
  rw [List.replicate_succ, List.cons_append, rawScan_bs, nBS_rep, nBS_other x r' hx, Nat.add_zero,
    Nat.add_sub_cancel_left, drop_rep, Nat.add_comm 1 n]

theorem ur_cons (n : Nat) (x : UInt8) (r' : List UInt8) (g : Nat) (hx : x ≠ 0x5c) :
    unescRaw 0x22 (g + 1) (List.replicate (n + 1) 0x5c ++ x :: r') =
      List.replicate (if x = 0x22 then (n + 1) / 2 else n + 1) 0x5c ++ x :: unescRaw 0x22 g r' := by
  rw [List.replicate_succ, List.cons_append, unescRaw_bs, nBS_rep, nBS_other x r' hx, Nat.add_zero,
    Nat.add_sub_cancel_left, drop_rep, Nat.add_comm 1 n]

theorem ur_nil (n g : Nat) :
    unescRaw 0x22 (g + 1) (List.replicate (n + 1) 0x5c ++ []) = List.replicate ((n + 1) / 2) 0x5c := by
  have h0 : nBS ([] : List UInt8) = 0 := rfl
  rw [List.replicate_succ, List.cons_append, unescRaw_bs, nBS_rep, h0, Nat.add_zero,
    Nat.add_sub_cancel_left, drop_rep, Nat.add_comm 1 n]

theorem rep_snoc (k : Nat) (E : List UInt8) :
    List.replicate k (0x5c : UInt8) ++ 0x5c :: E = List.replicate (k + 1) 0x5c ++ E := by
  rw [List.replicate_succ', List.append_assoc]; rfl

theorem escRawB_nil (k : Nat) : (escRawB k []).1 = List.replicate k 0x5c := rfl

theorem escRawB_bs (k : Nat) (x : List UInt8) :
    (escRawB k (0x5c :: x)).1 = 0x5c :: (escRawB (k + 1) x).1 := by
  simp [escRawB]

theorem escRawB_q (k : Nat) (x : List UInt8) :
    (escRawB k (0x22 :: x)).1 = List.replicate (k + 1) 0x5c ++ 0x22 :: (escRawB 0 x).1 := by
  simp [escRawB]

theorem escRawB_other (k : Nat) (b : UInt8) (x : List UInt8) (h1 : b ≠ 0x5c) (h2 : b ≠ 0x22) :
    (escRawB k (b :: x)).1 = b :: (escRawB 0 x).1 := by
  simp [escRawB, h1, h2]

theorem raw_main : ∀ (x : List UInt8) (k : Nat), 0x0d ∉ x →
    (∀ f, (List.replicate k 0x5c ++ (escRawB k x).1).length + 2 ≤ f →
      rawScan 0x22 f (List.replicate k 0x5c ++ (escRawB k x).1 ++ [0x22]) = some [0x22]) ∧
    (∀ g, (List.replicate k 0x5c ++ (escRawB k x).1).length + 1 ≤ g →
      unescRaw 0x22 g (List.replicate k 0x5c ++ (escRawB k x).1) = List.replicate k 0x5c ++ x)
  | [], k, _ => by
    rw [escRawB_nil, List.replicate_append_replicate, List.append_nil]
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · simp only [List.length_replicate] at hf
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      cases k with
      | zero => simp [rawScan]
      | succ k =>
        rw [show k + 1 + (k + 1) = (2 * k + 1) + 1 by omega, rs_cons _ _ _ _ (by decide),
          if_neg (fun h => by omega)]
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        simp [rawScan]
    · simp only [List.length_replicate] at hg
      cases k with
      | zero => cases g <;> rfl
      | succ k =>
        obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
        rw [show k + 1 + (k + 1) = (2 * k + 1) + 1 by omega,
          ← List.append_nil (List.replicate (2 * k + 1 + 1) (0x5c : UInt8)), ur_nil]
        congr 1; omega
  | b :: x', k, hx => by
    have hx' : 0x0d ∉ x' := fun h => hx (by simp [h])
    have hb : b ≠ 0x0d := fun h => hx (by simp [h])
    by_cases h1 : b = 0x5c
    · subst h1
      have ih := raw_main x' (k + 1) hx'
      rw [escRawB_bs, rep_snoc, rep_snoc]
      exact ih
    obtain ⟨ihs, ihu⟩ := raw_main x' 0 hx'
    simp only [List.replicate_zero, List.nil_append] at ihs ihu
    by_cases h2 : b = 0x22
    · subst h2
      rw [escRawB_q, ← List.append_assoc, List.replicate_append_replicate,
        show k + (k + 1) = 2 * k + 1 by omega]
      refine ⟨fun f hf => ?_, fun g hg => ?_⟩
      · simp only [List.length_append, List.length_replicate, List.length_cons] at hf
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [List.append_assoc, List.cons_append, rs_cons _ _ _ _ (by decide), if_pos ⟨rfl, by omega⟩]
        exact ihs f (by omega)
      · simp only [List.length_append, List.length_replicate, List.length_cons] at hg
        obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
        rw [ur_cons _ _ _ _ (by decide), if_pos rfl, ihu g (by omega)]
        congr 2; omega
    rw [escRawB_other k b x' h1 h2]
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons] at hf
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      cases k with
      | zero =>
        rw [List.replicate_zero, List.nil_append, List.cons_append, rawScan_plain _ _ _ h1 h2]
        exact ihs f (by omega)
      | succ k =>
        rw [List.append_assoc, List.cons_append, rs_cons _ _ _ _ h1, if_neg (fun h => h2 h.1)]
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rw [rawScan_plain _ _ _ h1 h2]
        exact ihs f (by omega)
    · simp only [List.length_append, List.length_replicate, List.length_cons] at hg
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      cases k with
      | zero =>
        rw [List.replicate_zero, List.nil_append, List.nil_append, unescRaw_plain _ _ _ h1 hb,
          ihu g (by omega)]
      | succ k =>
        rw [ur_cons _ _ _ _ h1, if_neg h2, ihu g (by omega)]

/-- The escaping layer of `show_sym`: a `var"..."` body decodes, by the raw-string
rules alone, to the name, for every name without a carriage return. -/
def ShowSymVarRoundTripNoCR : Prop :=
  ∀ (d : UData) (o : OpData) (name : JStr) (out : List UInt8), 0x0d ∉ name.bytes →
    showSym d o name = .ok out →
    out = name.bytes ∨ ∃ e, out = varPrefix ++ e ++ [0x22] ∧ rawBody e = some name.bytes

theorem showSymVarRoundTripNoCR_proven : ShowSymVarRoundTripNoCR := by
  intro d o name out hcr h
  unfold showSym at h
  cases hv : isValidIdentifier d o name with
  | error e => rw [hv] at h; simp [bind, Except.bind] at h
  | ok v =>
    rw [hv] at h
    cases v
    · simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
        Except.ok.injEq] at h
      right
      refine ⟨escapeRawString name, h.symm, ?_⟩
      rw [escapeRawString_eq]
      obtain ⟨hs, hu⟩ := raw_main name.bytes 0 hcr
      simp only [List.replicate_zero, List.nil_append] at hs hu
      unfold rawBody
      rw [hs _ (by omega), hu _ (by omega)]
      rfl
    · simp only [bind, Except.bind, pure, Except.pure, eq_self_iff_true, ↓reduceIte,
        Except.ok.injEq] at h
      left; exact h.symm

/-! ## ASCII identifiers -/

theorem chars_ascii (s : JStr) (h : ∀ b ∈ s.bytes, b < 0x80) :
    chars s = s.bytes.map (fun b : UInt8 => b.toUInt32 <<< 24) := by
  obtain ⟨hb, hg⟩ := chars_spec s
  suffices key : ∀ (cs : List UInt32) (bs : List UInt8), cs.flatMap writeChar = bs →
      (∀ c ∈ cs, GoodChar c) → (∀ b ∈ bs, b < 0x80) → cs = bs.map (fun b : UInt8 => b.toUInt32 <<< 24) from
    key _ _ hb hg h
  intro cs
  induction cs with
  | nil => intro bs hfm _ _; subst hfm; rfl
  | cons c cs ih =>
    intro bs hfm hgc hbs
    rcases hgc c (by simp) with ⟨b, hc, hw⟩ | ⟨hne, hall⟩
    · rw [List.flatMap_cons, hw] at hfm
      subst hfm
      rw [List.singleton_append, List.map_cons, hc]
      exact congrArg _ (ih _ rfl (fun x hx => hgc x (by simp [hx])) (fun x hx => hbs x (by simp [hx])))
    · exfalso
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
      rw [List.flatMap_cons, hx] at hfm
      have h1 := hall x (by rw [hx]; simp)
      have h2 := hbs x (by rw [← hfm]; simp)
      rw [UInt8.le_iff_toNat_le] at h1
      rw [UInt8.lt_iff_toNat_lt] at h2
      have : (0x80 : UInt8).toNat = 128 := rfl
      omega

theorem u8_forall {P : UInt8 → Prop} (h : ∀ n : Fin 256, P n.val.toUInt8) (c : UInt8) : P c := by
  have hp : P c.toNat.toUInt8 := h ⟨c.toNat, c.toNat_lt⟩
  have hcc : c.toNat.toUInt8 = c := UInt8.toNat_inj.mp (by simp)
  rwa [hcc] at hp

/-- The ASCII test of `jl_id_start_char`. -/
abbrev idStartCond (wc : UInt32) : Bool :=
  (decide (65 ≤ wc) && decide (wc ≤ 90)) || (decide (97 ≤ wc) && decide (wc ≤ 122)) || wc == 95

/-- The ASCII test of `jl_id_char`. -/
abbrev idCharCond (wc : UInt32) : Bool :=
  (decide (65 ≤ wc) && decide (wc ≤ 90)) || (decide (97 ≤ wc) && decide (wc ≤ 122)) || wc == 95 ||
    (decide (48 ≤ wc) && decide (wc ≤ 57)) || wc == 33

theorem start_ok : ∀ n : Fin 256,
    ((65 ≤ n.val.toUInt8 ∧ n.val.toUInt8 ≤ 90) ∨ (97 ≤ n.val.toUInt8 ∧ n.val.toUInt8 ≤ 122) ∨
      n.val.toUInt8 = 95) → (n.val.toUInt8 < 0x80 ∧ idStartCond n.val.toUInt8.toUInt32 = true) := by
  decide +kernel

theorem char_ok : ∀ n : Fin 256,
    ((65 ≤ n.val.toUInt8 ∧ n.val.toUInt8 ≤ 90) ∨ (97 ≤ n.val.toUInt8 ∧ n.val.toUInt8 ≤ 122) ∨
      (48 ≤ n.val.toUInt8 ∧ n.val.toUInt8 ≤ 57) ∨ n.val.toUInt8 = 95 ∨ n.val.toUInt8 = 33) →
      (n.val.toUInt8 < 0x80 ∧ idCharCond n.val.toUInt8.toUInt32 = true) := by
  decide +kernel

theorem cp_ok : ∀ n : Fin 256, n.val.toUInt8 < 0x80 →
    (codepoint (n.val.toUInt8.toUInt32 <<< 24)).toOption = some n.val.toUInt8.toUInt32 := by
  decide +kernel

theorem codepoint_ascii (c : UInt8) (h : c < 0x80) : codepoint (c.toUInt32 <<< 24) = .ok c.toUInt32 := by
  have := u8_forall (P := fun c => c < 0x80 →
    (codepoint (c.toUInt32 <<< 24)).toOption = some c.toUInt32) cp_ok c h
  cases hc : codepoint (c.toUInt32 <<< 24) with
  | ok u => rw [hc] at this; simp [Except.toOption] at this; rw [this]
  | error e => rw [hc] at this; simp [Except.toOption] at this

theorem allIdChar_ascii (d : UData) : ∀ cs : List UInt8,
    (∀ x ∈ cs, (65 ≤ x ∧ x ≤ 90) ∨ (97 ≤ x ∧ x ≤ 122) ∨ (48 ≤ x ∧ x ≤ 57) ∨ x = 95 ∨ x = 33) →
    allIdChar d (cs.map (fun b : UInt8 => b.toUInt32 <<< 24)) = .ok true
  | [], _ => rfl
  | x :: cs, hcs => by
    obtain ⟨hlt, hcond⟩ := u8_forall (P := fun x => ((65 ≤ x ∧ x ≤ 90) ∨ (97 ≤ x ∧ x ≤ 122) ∨
      (48 ≤ x ∧ x ≤ 57) ∨ x = 95 ∨ x = 33) → (x < 0x80 ∧ idCharCond x.toUInt32 = true)) char_ok x
      (hcs x (by simp))
    have h1 : isIdCharJ d (x.toUInt32 <<< 24) = .ok true := by
      unfold isIdCharJ
      rw [codepoint_ascii x hlt]
      show Except.ok (idChar d x.toUInt32) = _
      unfold idChar
      rw [if_pos hcond]
    rw [List.map_cons]
    show (do if ← isIdCharJ d (x.toUInt32 <<< 24) then allIdChar d _ else pure false) = _
    rw [h1]
    exact allIdChar_ascii d cs (fun y hy => hcs y (by simp [hy]))

theorem kw_true : asc ['t', 'r', 'u', 'e'] ∈ keywordSyms := by decide

theorem kw_false : asc ['f', 'a', 'l', 's', 'e'] ∈ keywordSyms := by decide

theorem idStart_ascii (d : UData) (c : UInt8) (hlt : c < 0x80) (hcond : idStartCond c.toUInt32 = true) :
    isIdStartCharJ d (c.toUInt32 <<< 24) = .ok true := by
  unfold isIdStartCharJ
  rw [codepoint_ascii c hlt]
  show Except.ok (idStartChar d c.toUInt32) = _
  unfold idStartChar
  rw [if_pos hcond]

theorem isidentifier_ascii_ident (d : UData) (s : JStr) (c : UInt8) (cs : List UInt8)
    (hs : s.bytes = c :: cs) (hc : (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ c = 95)
    (hcs : ∀ x ∈ cs, (65 ≤ x ∧ x ≤ 90) ∨ (97 ≤ x ∧ x ≤ 122) ∨ (48 ≤ x ∧ x ≤ 57) ∨ x = 95 ∨ x = 33)
    (hk : s.bytes ∉ keywordSyms) : isidentifier d s = .ok true := by
  obtain ⟨hlt, hcond⟩ := u8_forall (P := fun x => ((65 ≤ x ∧ x ≤ 90) ∨ (97 ≤ x ∧ x ≤ 122) ∨ x = 95) →
    (x < 0x80 ∧ idStartCond x.toUInt32 = true)) start_ok c hc
  have hasc : ∀ b ∈ s.bytes, b < 0x80 := by
    rw [hs]; intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hlt
    · exact (u8_forall (P := fun x => ((65 ≤ x ∧ x ≤ 90) ∨ (97 ≤ x ∧ x ≤ 122) ∨
        (48 ≤ x ∧ x ≤ 57) ∨ x = 95 ∨ x = 33) → (x < 0x80 ∧ idCharCond x.toUInt32 = true)) char_ok b
        (hcs b hb)).1
  have ht : asc ['t', 'r', 'u', 'e'] ∈ keywordSyms := kw_true
  have hf : asc ['f', 'a', 'l', 's', 'e'] ∈ keywordSyms := kw_false
  have hnk : ¬ (s.bytes = asc ['t', 'r', 'u', 'e'] ∨ s.bytes = asc ['f', 'a', 'l', 's', 'e']) := by
    rintro (h | h)
    · exact hk (h ▸ ht)
    · exact hk (h ▸ hf)
  have h1 : isIdStartCharJ d (c.toUInt32 <<< 24) = .ok true := idStart_ascii d c hlt hcond
  unfold isidentifier
  rw [chars_ascii s hasc]
  have hm : s.bytes.map (fun b : UInt8 => b.toUInt32 <<< 24) =
      (c.toUInt32 <<< 24) :: cs.map (fun b : UInt8 => b.toUInt32 <<< 24) := by rw [hs, List.map_cons]
  rw [hm]
  show (if s.bytes = asc ['t', 'r', 'u', 'e'] ∨ s.bytes = asc ['f', 'a', 'l', 's', 'e'] then .ok false
    else do if ← isIdStartCharJ d (c.toUInt32 <<< 24) then allIdChar d _ else pure false) = _
  rw [if_neg hnk, h1]
  exact allIdChar_ascii d cs hcs

theorem showSym_ascii_ident (d : UData) (o : OpData) (s : JStr) (c : UInt8) (cs : List UInt8)
    (hs : s.bytes = c :: cs) (hc : (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ c = 95)
    (hcs : ∀ x ∈ cs, (65 ≤ x ∧ x ≤ 90) ∨ (97 ≤ x ∧ x ≤ 122) ∨ (48 ≤ x ∧ x ≤ 57) ∨ x = 95 ∨ x = 33)
    (hk : s.bytes ∉ keywordSyms) : showSym d o s = .ok s.bytes := by
  unfold showSym isValidIdentifier
  rw [isidentifier_ascii_ident d s c cs hs hc hcs hk, decide_eq_false hk]
  rfl

end JuliaLean.Show
