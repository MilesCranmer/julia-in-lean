import JuliaLean.Tuples.Lemmas

/-! Proofs of the equality, ordering and hashing properties. -/

namespace JuliaLean.Tuples

variable {α : Type}

theorem isequalRec_eq (o : Ops α) (t s : List α) (h : t.length = s.length) :
    isequalRec o t s = (List.zipWith o.isequal t s).all id := by
  induction t generalizing s with
  | nil => cases s with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a r ih => cases s with
    | nil => simp at h
    | cons b s' => simp [isequalRec, ih s' (by simpa using h)]

theorem isequalLoop_eq (o : Ops α) (t s : List α) (i k : Nat) (hl : t.length = s.length)
    (h : i + k = t.length) :
    isequalLoop o t s i k = (List.zipWith o.isequal (t.drop i) (s.drop i)).all id := by
  induction k generalizing i with
  | zero =>
    have h1 : t.length ≤ i := by omega
    have h2 : s.length ≤ i := by omega
    rw [drop_nil_of_le h1, drop_nil_of_le h2]
    rfl
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    rw [isequalLoop, getElem?_of_lt hi, getElem?_of_lt hj, ih (i + 1) (by omega),
      drop_cons_of_lt hi, drop_cons_of_lt hj, List.zipWith_cons_cons, List.all_cons]
    simp only
    cases o.isequal t[i] s[i] <;> simp

theorem isequal_eq (o : Ops α) (t s : List α) :
    isequal o t s = (t.length == s.length && (List.zipWith o.isequal t s).all id) := by
  unfold isequal
  by_cases hl : t.length = s.length
  · simp only [hl, beq_self_eq_true, Bool.true_and]
    split
    · rw [isequalLoop_eq o t s 0 _ hl (by omega)]; simp
    · exact isequalRec_eq o t s hl
  · have : (t.length == s.length) = false := by simpa using hl
    simp [this]

/-- `eqSpec` on lists of equal length, by its elementwise results. -/
def eqCode (cs : List (Option Bool)) (anymissing : Bool) : Option Bool :=
  if cs.contains (some false) then some false
  else if anymissing || cs.contains none then none else some true

theorem eqCode_none (cs : List (Option Bool)) (m : Bool) :
    eqCode (none :: cs) m = eqCode cs true := by
  by_cases h : some false ∈ cs <;> simp [eqCode, h]

theorem eqCode_false (cs : List (Option Bool)) (m : Bool) :
    eqCode (some false :: cs) m = some false := by
  simp [eqCode]

theorem eqCode_true (cs : List (Option Bool)) (m : Bool) :
    eqCode (some true :: cs) m = eqCode cs m := by
  by_cases h : some false ∈ cs <;> by_cases h' : none ∈ cs <;> simp [eqCode, h, h']

theorem eqMissing_eq (o : Ops α) (t s : List α) (h : t.length = s.length) :
    eqMissing o t s = eqCode (List.zipWith o.eq t s) true := by
  induction t generalizing s with
  | nil => cases s with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a r ih => cases s with
    | nil => simp at h
    | cons b s' =>
      rw [eqMissing, ih s' (by simpa using h)]
      unfold eqCode
      cases hab : o.eq a b with
      | none => simp [hab]
      | some c => cases c <;> simp [hab]

theorem eqRec_eq (o : Ops α) (t s : List α) (h : t.length = s.length) :
    eqRec o t s = eqCode (List.zipWith o.eq t s) false := by
  induction t generalizing s with
  | nil => cases s with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a r ih => cases s with
    | nil => simp at h
    | cons b s' =>
      have h' : r.length = s'.length := by simpa using h
      rw [eqRec]
      cases hab : o.eq a b with
      | none =>
        simp only
        rw [eqMissing_eq o r s' h']
        unfold eqCode
        simp [hab]
      | some c =>
        cases c with
        | false => simp [eqCode, hab]
        | true =>
          simp only
          rw [ih s' h']
          unfold eqCode
          simp [hab]

theorem eqLoop_eq (o : Ops α) (t s : List α) (i k : Nat) (m : Bool) (hl : t.length = s.length)
    (h : i + k = t.length) :
    eqLoop o t s i k m = eqCode (List.zipWith o.eq (t.drop i) (s.drop i)) m := by
  induction k generalizing i m with
  | zero =>
    have h1 : t.length ≤ i := by omega
    have h2 : s.length ≤ i := by omega
    rw [drop_nil_of_le h1, drop_nil_of_le h2]
    cases m <;> rfl
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    rw [eqLoop, getElem?_of_lt hi, getElem?_of_lt hj, drop_cons_of_lt hi, drop_cons_of_lt hj,
      List.zipWith_cons_cons]
    simp only
    cases hab : o.eq t[i] s[i] with
    | none => simp only; rw [ih (i + 1) true (by omega), eqCode_none]
    | some c =>
      cases c with
      | false => simp only; rw [eqCode_false]
      | true => simp only; rw [ih (i + 1) m (by omega), eqCode_true]

theorem eq_eq (o : Ops α) (t s : List α) : eq o t s = eqSpec o t s := by
  unfold eq eqSpec
  by_cases hl : t.length = s.length
  · have hn : ¬ (t.length ≠ s.length) := fun h => h hl
    rw [if_pos hl, if_neg hn]
    show (if t.length ≥ 32 then eqLoop o t s 0 t.length false else eqRec o t s) =
      eqCode (List.zipWith o.eq t s) false
    split
    · rw [eqLoop_eq o t s 0 t.length false hl (Nat.zero_add _), List.drop_zero, List.drop_zero]
    · exact eqRec_eq o t s hl
  · have hn : t.length ≠ s.length := hl
    rw [if_neg hl, if_pos hn]

theorem equalityCorrect : EqualityCorrect := fun _ o t s => ⟨isequal_eq o t s, eq_eq o t s⟩

theorem ltLoop_eq (o : Ops α) (t s : List α) (i k : Nat) (h : i + k = min t.length s.length) :
    ltLoop o t s i k = ltRec o (t.drop i) (s.drop i) := by
  induction k generalizing i with
  | zero =>
    simp only [ltLoop]
    rcases Nat.lt_trichotomy t.length s.length with h' | h' | h'
    · have h1 : t.length ≤ i := by omega
      have h2 : i < s.length := by omega
      rw [drop_nil_of_le h1, drop_cons_of_lt h2]
      simp [ltRec, h']
    · have h1 : t.length ≤ i := by omega
      have h2 : s.length ≤ i := by omega
      rw [drop_nil_of_le h1, drop_nil_of_le h2]
      simp [ltRec, h']
    · have h1 : s.length ≤ i := by omega
      have h2 : i < t.length := by omega
      rw [drop_nil_of_le h1, drop_cons_of_lt h2]
      simp [ltRec]; omega
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    rw [ltLoop, getElem?_of_lt hi, getElem?_of_lt hj, drop_cons_of_lt hi, drop_cons_of_lt hj]
    simp only [ltRec]
    cases o.eq t[i] s[i] with
    | none => rfl
    | some c => cases c with
      | false => rfl
      | true => exact ih (i + 1) (by omega)

theorem ltLexicographic : LtLexicographic := by
  intro α o t s
  unfold lt
  split
  · rw [ltLoop_eq o t s 0 _ (by omega)]; simp
  · rfl

section Order

variable {o : Ops α} (hL : Lawful o)
include hL

theorem isequal_refl (a : α) : o.isequal a a = true := by
  rw [hL.equiv, hL.irrefl]; rfl

theorem isequal_symm (a b : α) : o.isequal a b = o.isequal b a := by
  rw [hL.equiv, hL.equiv b a, Bool.and_comm]

theorem not_lt_of_isequal {a b : α} (h : o.isequal a b = true) : o.isless a b = false := by
  rw [hL.equiv] at h
  cases hab : o.isless a b <;> simp_all

theorem lt_or_lt_of_not_isequal {a b : α} (h : o.isequal a b = false) :
    o.isless a b = true ∨ o.isless b a = true := by
  rw [hL.equiv] at h
  cases hab : o.isless a b <;> cases hba : o.isless b a <;> simp_all

theorem lt_of_lt_of_eq {a b c : α} (h1 : o.isless a b = true) (h2 : o.isequal b c = true) :
    o.isless a c = true := by
  cases hac : o.isless a c
  · exfalso
    cases hca : o.isless c a
    · have hea : o.isequal a c = true := by rw [hL.equiv, hac, hca]; rfl
      have heb : o.isequal a b = true := by
        rw [isequal_symm hL b c] at h2
        exact hL.incompTrans a c b hea h2
      rw [not_lt_of_isequal hL heb] at h1
      exact absurd h1 (by decide)
    · have := hL.trans c a b hca h1
      rw [isequal_symm hL] at h2
      rw [not_lt_of_isequal hL h2] at this
      exact absurd this (by decide)
  · rfl

theorem lt_of_eq_of_lt {a b c : α} (h1 : o.isequal a b = true) (h2 : o.isless b c = true) :
    o.isless a c = true := by
  cases hac : o.isless a c
  · exfalso
    cases hca : o.isless c a
    · have hea : o.isequal a c = true := by rw [hL.equiv, hac, hca]; rfl
      have hbc : o.isequal b c = true := by
        rw [isequal_symm hL a b] at h1
        exact hL.incompTrans b a c h1 hea
      rw [not_lt_of_isequal hL hbc] at h2
      exact absurd h2 (by decide)
    · have := hL.trans b c a h2 hca
      rw [not_lt_of_isequal hL ((isequal_symm hL a b) ▸ h1)] at this
      exact absurd this (by decide)
  · rfl

theorem islessRec_irrefl (t : List α) : islessRec o t t = false := by
  induction t with
  | nil => rfl
  | cons a r ih => simp [islessRec, hL.irrefl, ih]

theorem islessRec_trans (t s u : List α) (h1 : islessRec o t s = true)
    (h2 : islessRec o s u = true) : islessRec o t u = true := by
  induction t generalizing s u with
  | nil =>
    cases s with
    | nil => simp [islessRec] at h1
    | cons b s' => cases u with
      | nil => simp [islessRec] at h2
      | cons c u' => rfl
  | cons a r ih =>
    cases s with
    | nil => simp [islessRec] at h1
    | cons b s' => cases u with
      | nil => simp [islessRec] at h2
      | cons c u' =>
        simp only [islessRec, Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
        rcases h1 with h1 | ⟨e1, r1⟩ <;> rcases h2 with h2 | ⟨e2, r2⟩
        · exact Or.inl (hL.trans a b c h1 h2)
        · exact Or.inl (lt_of_lt_of_eq hL h1 e2)
        · exact Or.inl (lt_of_eq_of_lt hL e1 h2)
        · exact Or.inr ⟨hL.incompTrans a b c e1 e2, ih s' u' r1 r2⟩

theorem islessRec_incomp (t s : List α) :
    (islessRec o t s = false ∧ islessRec o s t = false) ↔
      (t.length == s.length && (List.zipWith o.isequal t s).all id) = true := by
  induction t generalizing s with
  | nil => cases s <;> simp [islessRec]
  | cons a r ih =>
    cases s with
    | nil => simp [islessRec]
    | cons b s' =>
      have ihs := ih s'
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.zipWith_cons_cons,
        List.all_cons, id] at ihs ⊢
      cases hab : o.isequal a b
      · rcases lt_or_lt_of_not_isequal hL hab with h | h
        · simp [islessRec, h]
        · simp [islessRec, h]
      · have hba : o.isequal b a = true := by rw [isequal_symm hL]; exact hab
        simp [islessRec, not_lt_of_isequal hL hab, not_lt_of_isequal hL hba, hab, hba]
        simpa using ihs

theorem islessLoop_eq (t s : List α) (i k : Nat) (h : i + k = min t.length s.length) :
    islessLoop o t s i k = islessRec o (t.drop i) (s.drop i) := by
  induction k generalizing i with
  | zero =>
    simp only [islessLoop]
    rcases Nat.lt_trichotomy t.length s.length with h' | h' | h'
    · have h1 : t.length ≤ i := by omega
      have h2 : i < s.length := by omega
      rw [drop_nil_of_le h1, drop_cons_of_lt h2]
      simp [islessRec, h']
    · have h1 : t.length ≤ i := by omega
      have h2 : s.length ≤ i := by omega
      rw [drop_nil_of_le h1, drop_nil_of_le h2]
      simp [islessRec, h']
    · have h1 : s.length ≤ i := by omega
      have h2 : i < t.length := by omega
      rw [drop_nil_of_le h1, drop_cons_of_lt h2]
      simp [islessRec]; omega
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    rw [islessLoop, getElem?_of_lt hi, getElem?_of_lt hj, drop_cons_of_lt hi, drop_cons_of_lt hj]
    simp only [islessRec]
    cases he : o.isequal t[i] s[i]
    · simp
    · simp [not_lt_of_isequal hL he, ih (i + 1) (by omega)]

theorem isless_eq (t s : List α) : isless o t s = islessRec o t s := by
  unfold isless
  split
  · rw [islessLoop_eq hL t s 0 _ (by omega)]; simp
  · rfl

end Order

theorem islessStrictWeakOrder : IslessStrictWeakOrder := by
  intro α o hL
  have incomp : ∀ t s, (isless o t s = false ∧ isless o s t = false) ↔ isequal o t s = true := by
    intro t s
    rw [isless_eq hL, isless_eq hL, isequal_eq]
    exact islessRec_incomp hL t s
  refine ⟨?_, ?_, incomp, ?_, ?_⟩
  · intro t; rw [isless_eq hL]; exact islessRec_irrefl hL t
  · intro t s u h1 h2
    rw [isless_eq hL] at h1 h2 ⊢
    exact islessRec_trans hL t s u h1 h2
  · intro t s
    rw [← incomp]
    unfold cmp
    cases h1 : isless o t s <;> cases h2 : isless o s t <;> simp
  · intro a1 a2 b1 b2
    simp [islessPair, isless, islessRec]

theorem hashRec_eq (o : Ops α) (t : List α) (h : Nat) :
    hashRec o t h = t.foldr o.hash (h ^^^ tuplehashSeed) := by
  induction t with
  | nil => rfl
  | cons a r ih => simp [hashRec, ih]

theorem hashLoop_eq (o : Ops α) (t : List α) (k out : Nat) (hk : k ≤ t.length) :
    hashLoop o t k out = (t.take k).foldr o.hash out := by
  induction k generalizing out with
  | zero => simp [hashLoop]
  | succ k ih =>
    have hk' : k < t.length := by omega
    rw [hashLoop, getElem?_of_lt hk']
    simp only
    rw [ih _ (by omega), List.take_succ, getElem?_of_lt hk']
    simp only [List.foldr_append, Option.toList_some, List.foldr_cons, List.foldr_nil]

theorem hash_eq (o : Ops α) (t : List α) (h : Nat) :
    hash o t h = t.foldr o.hash (h ^^^ tuplehashSeed) := by
  unfold hash
  split
  · rw [hashLoop_eq o t _ _ (Nat.le_refl _), List.take_length]
  · exact hashRec_eq o t h

theorem foldr_hash_congr (o : Ops α) (hc : ∀ a b h, o.isequal a b = true → o.hash a h = o.hash b h)
    (t s : List α) (hl : t.length = s.length) (he : (List.zipWith o.isequal t s).all id = true)
    (x : Nat) : t.foldr o.hash x = s.foldr o.hash x := by
  induction t generalizing s with
  | nil => cases s with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a r ih => cases s with
    | nil => simp at hl
    | cons b s' =>
      simp only [List.zipWith_cons_cons, List.all_cons, id, Bool.and_eq_true] at he
      simp only [List.foldr_cons]
      rw [ih s' (by simpa using hl) he.2, hc a b _ he.1]

theorem hashIsequal : HashIsequal := by
  intro α o hc
  have tup : ∀ t s h, isequal o t s = true → hash o t h = hash o s h := by
    intro t s h he
    rw [isequal_eq] at he
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    rw [hash_eq, hash_eq]
    exact foldr_hash_congr o hc t s he.1 he.2 _
  refine ⟨tup, ?_⟩
  intro oid a b h he
  unfold isequalNT at he
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  unfold hashNT
  rw [he.1, tup _ _ h he.2]

end JuliaLean.Tuples
