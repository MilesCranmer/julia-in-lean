import JuliaLean.BigNums.Parse

/-!
Proof that `parse(BigInt, string(n; base, pad); base) == n` for bases `2..62` and `pad ≥ 1`
(`StringParseRoundtrip`).
-/

namespace JuliaLean.BigNums

open JuliaLean

private def Good (b : Nat) (c : Char) : Prop :=
  digitVal c b < b ∧ isSpace c = false ∧ c ≠ '-' ∧ c ≠ '+' ∧ c ≠ Char.ofNat 0

private theorem digitChar_table : ∀ b : Fin 63, ∀ d : Fin 62, 2 ≤ b.val → d.val < b.val →
    digitVal (digitChar d.val b.val) b.val = d.val ∧ isSpace (digitChar d.val b.val) = false ∧
      digitChar d.val b.val ≠ '-' ∧ digitChar d.val b.val ≠ '+' ∧
      digitChar d.val b.val ≠ Char.ofNat 0 := by
  decide +kernel

private theorem digitChar_good {b d : Nat} (hb2 : 2 ≤ b) (hb62 : b ≤ 62) (hd : d < b) :
    digitVal (digitChar d b) b = d ∧ Good b (digitChar d b) := by
  obtain ⟨h1, h2⟩ := digitChar_table ⟨b, by omega⟩ ⟨d, by omega⟩ hb2 hd
  exact ⟨h1, by rw [Good, h1]; exact ⟨hd, h2⟩⟩

private theorem absDigits_go (b : Nat) (hb2 : 2 ≤ b) :
    ∀ k n, n < k → absDigits.go b n k ≠ [] ∧ (∀ d ∈ absDigits.go b n k, d < b) ∧
      (absDigits.go b n k).foldr (fun (d : Nat) (acc : Int) => acc * (b : Int) + (d : Int)) 0 =
        (n : Int) := by
  intro k
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n hn
    rw [absDigits.go]
    by_cases h : n < b
    · simp only [h, ↓reduceIte]; simp [h]
    · simp only [h, ↓reduceIte]
      have hq : n / b < k := by
        have : n / b < n := Nat.div_lt_self (by omega) (by omega)
        omega
      obtain ⟨_, h2, h3⟩ := ih (n / b) hq
      refine ⟨by simp, ?_, ?_⟩
      · intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Nat.mod_lt _ (by omega)
        · exact h2 d hd
      · simp only [List.foldr_cons, h3]
        have h4 : n / b * b + n % b = n := by rw [Nat.mul_comm]; exact Nat.div_add_mod n b
        exact_mod_cast h4

private theorem dropWhile_good {b : Nat} {c : Char} {t : List Char} (h : Good b c) :
    (c :: t).dropWhile isSpace = c :: t := by
  simp [List.dropWhile, h.2.1]

private theorem preamble_pos (b : Nat) (hb : b ≠ 0) (c : Char) (t : List Char) (h : Good b c) :
    preamble b (c :: t) = (1, b, some (c :: t)) := by
  unfold preamble
  rw [dropWhile_good h]
  obtain ⟨_, _, h1, h2, _⟩ := h
  simp [hb]
  split <;> simp_all

private theorem preamble_neg (b : Nat) (hb : b ≠ 0) (c : Char) (t : List Char) (h : Good b c) :
    preamble b ('-' :: c :: t) = (-1, b, some (c :: t)) := by
  unfold preamble
  have hm : isSpace '-' = false := by decide
  simp only [List.dropWhile_cons, hm, Bool.false_eq_true, ↓reduceIte, dropWhile_good h]
  simp [hb]

private theorem mpz_body (b : Nat) (c : Char) (t : List Char) (hg : ∀ x ∈ c :: t, Good b x) :
    mpzSetStr (c :: t) b =
      some ((c :: t).foldl (fun acc x => acc * (b : Int) + digitVal x b) 0) := by
  have hc := hg c (by simp)
  unfold mpzSetStr
  rw [dropWhile_good hc]
  have hat : t.any (fun x => decide (digitVal x b ≥ b)) = false :=
    List.any_eq_false.2 (fun x hx => by simp; exact (hg x (by simp [hx])).1)
  have hft : t.filter (fun x => !isSpace x) = t :=
    List.filter_eq_self.2 (fun x hx => by simp [(hg x (by simp [hx])).2.1])
  obtain ⟨h0, hsp, h1, _, _⟩ := hc
  simp [h0, h1, hsp, hft, hat]

private theorem foldl_zeros (b z : Nat) :
    (List.replicate z '0').foldl (fun acc x => acc * (b : Int) + digitVal x b) 0 = 0 := by
  induction z with
  | zero => rfl
  | succ z ih =>
    have h0 : digitVal '0' b = 0 := rfl
    rw [List.replicate_succ, List.foldl_cons]
    simp [h0, ih]

private theorem foldr_map_digitChar (b : Nat) (hb2 : 2 ≤ b) (hb62 : b ≤ 62) :
    ∀ L : List Nat, (∀ d ∈ L, d < b) →
      (L.map (fun d => digitChar d b)).foldr
          (fun c (acc : Int) => acc * (b : Int) + digitVal c b) 0 =
        L.foldr (fun (d : Nat) (acc : Int) => acc * (b : Int) + (d : Int)) 0 := by
  intro L hL
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih (fun x hx => hL x (by simp [hx])), (digitChar_good hb2 hb62 (hL d (by simp))).1]

private theorem parse_body (b : Nat) (hb2 : 2 ≤ b) (hb62 : b ≤ 62) (body : List Char)
    (hne : body ≠ []) (hg : ∀ x ∈ body, Good b x) :
    parseBig body b = .ok (body.foldl (fun acc x => acc * (b : Int) + digitVal x b) 0) ∧
    parseBig ('-' :: body) b =
      .ok (-(body.foldl (fun acc x => acc * (b : Int) + digitVal x b) 0)) := by
  obtain ⟨c, t, rfl⟩ : ∃ c t, body = c :: t := by
    cases body with
    | nil => exact absurd rfl hne
    | cons c t => exact ⟨c, t, rfl⟩
  have hc := hg c (by simp)
  have hm := mpz_body b c t hg
  have hnul : ¬ (Char.ofNat 0 ∈ c :: t) := fun h => (hg _ h).2.2.2.2 rfl
  constructor
  · unfold parseBig
    rw [preamble_pos b (by omega) c t hc]
    simp [hb2, hb62, hm, hnul]
  · unfold parseBig
    rw [preamble_neg b (by omega) c t hc]
    have : Char.ofNat 0 ≠ '-' := by decide
    simp [hb2, hb62, hm, hnul, this]

theorem stringParseRoundtrip_proven : StringParseRoundtrip := by
  intro n b pad hb2 hb62 hpad
  have hs : stringBig n b pad = .ok (renderPos n b pad) := by
    unfold stringBig
    have h1 : ¬ ((b : Int) < 0) := by omega
    have h2 : 2 ≤ (b : Int) ∧ (b : Int) ≤ 62 := by omega
    simp only [h1, h2, ↓reduceIte]
    simp
  rw [hs]
  show parseBig (renderPos n b pad) b = .ok n
  obtain ⟨hne, hlt, hval⟩ := absDigits_go b hb2 (n.natAbs + 1) n.natAbs (by omega)
  let ds := digitChars n b
  let body := List.replicate (pad.toNat - ds.length) '0' ++ ds
  have hr : renderPos n b pad = (if n < 0 then ['-'] else []) ++ body := by
    have h0 : ¬ (n = 0 ∧ pad < 1) := by omega
    simp only [renderPos, h0, ↓reduceIte, List.append_assoc, body, ds]
  have hbne : body ≠ [] := by
    simp only [body, ds, digitChars]
    intro h
    simp at h
    exact hne h.2
  have hg : ∀ x ∈ body, Good b x := by
    intro x hx
    simp only [body, ds, digitChars, List.mem_append, List.mem_replicate, List.mem_reverse,
      List.mem_map] at hx
    rcases hx with ⟨_, rfl⟩ | ⟨d, hd, rfl⟩
    · exact (digitChar_good (d := 0) hb2 hb62 (by omega)).2
    · exact (digitChar_good hb2 hb62 (hlt d hd)).2
  have hfold : body.foldl (fun acc x => acc * (b : Int) + digitVal x b) 0 = (n.natAbs : Int) := by
    simp only [body, List.foldl_append, foldl_zeros]
    show List.foldl _ 0 ((absDigits n.natAbs b).map (fun d => digitChar d b)).reverse = _
    rw [List.foldl_reverse]
    exact (foldr_map_digitChar b hb2 hb62 _ hlt).trans hval
  obtain ⟨hp, hm⟩ := parse_body b hb2 hb62 body hbne hg
  rw [hr]
  by_cases hn : n < 0
  · simp only [hn, ↓reduceIte]
    show parseBig ('-' :: body) b = _
    rw [hm, hfold]
    congr 1
    omega
  · simp only [hn, ↓reduceIte, List.nil_append]
    rw [hp, hfold]
    congr 1
    omega

end JuliaLean.BigNums
