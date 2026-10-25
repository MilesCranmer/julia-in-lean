import JuliaLean.Sockets.Lemmas

namespace JuliaLean.Sockets

theorem repDigits_predicate (base : Nat) (hb : 0 < base) (toCh : Nat → Char) (P : Char → Prop)
    (hch : ∀ d, d < base → P (toCh d)) :
    ∀ fuel n acc, (∀ c ∈ acc, P c) → ∀ c ∈ repDigits base toCh fuel n acc, P c := by
  intro fuel
  induction fuel with
  | zero => intro n acc ha c hc; exact ha c hc
  | succ fuel ih =>
    intro n acc ha c hc
    by_cases hz : n = 0
    · exact ha c (by simpa [repDigits, hz] using hc)
    · simp only [repDigits, ite_eq_right hz] at hc
      apply ih _ _ (fun x hx => ?_) c hc
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hch _ (Nat.mod_lt _ hb)
      · exact ha x hx

theorem repDigits_length {base : Nat} (hb : 0 < base) (toCh : Nat → Char) :
    ∀ k fuel n acc, n < base ^ k → (repDigits base toCh fuel n acc).length ≤ k + acc.length := by
  intro k
  induction k with
  | zero =>
    intro fuel n acc hn
    have hz : n = 0 := by simpa using hn
    simp [hz, repDigits_zero]
  | succ k ih =>
    intro fuel n acc hn
    cases fuel with
    | zero => simp [repDigits]
    | succ fuel =>
      by_cases hz : n = 0
      · simp [hz, repDigits_zero]
      · have hq : n / base < base ^ k :=
          (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.pow_succ] using hn)
        have hh := ih fuel (n / base) (toCh (n % base) :: acc) hq
        simpa [repDigits, hz, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def LowerHex (c : Char) : Prop :=
  (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 102)

private theorem hexChar_lower_table : ∀ d : Fin 16, LowerHex (hexCh d) := by
  unfold LowerHex
  decide +kernel

theorem hexStr_lower (n : Nat) : ∀ c ∈ hexStr n, LowerHex c := by
  by_cases hz : n = 0
  · simp [hz, LowerHex]
  · unfold hexStr repStr
    rw [ite_eq_right hz]
    exact repDigits_predicate 16 (by decide) hexCh LowerHex
      (fun d hd => hexChar_lower_table ⟨d, hd⟩) _ _ _ (by simp)

theorem hexStr_head (n : Nat) (hn : 0 < n) : (hexStr n).head? ≠ some '0' := by
  unfold hexStr repStr
  rw [ite_eq_right (by omega)]
  exact repDigits_head (by decide) hexCh (fun d hd he => by
    have hv := congrArg digitVal he
    rw [digitVal_hexCh hd, digitVal_hexCh (by decide)] at hv
    omega) _ _ _ hn (by omega)

theorem hexStr_length (n : Nat) (hn : n < 65536) : (hexStr n).length ≤ 4 := by
  by_cases hz : n = 0
  · simp [hz]
  · unfold hexStr repStr
    rw [ite_eq_right hz]
    simpa using repDigits_length (base := 16) (by decide) hexCh 4 n n [] (by simpa using hn)

/-- RFC 5952 sections 4.1 and 4.3: no leading zeros, 1-4 lowercase digits. -/
def IPv6HexFormat : Prop := ∀ n : Nat, n < 65536 →
  (∀ c ∈ hexStr n, LowerHex c) ∧ hexStr n ≠ [] ∧
  (hexStr n = ['0'] ∨ (hexStr n).head? ≠ some '0') ∧ (hexStr n).length ≤ 4

theorem ipv6HexFormat_proven : IPv6HexFormat := by
  intro n hn
  refine ⟨hexStr_lower n, hexStr_nonempty n, ?_, hexStr_length n hn⟩
  by_cases hz : n = 0
  · exact Or.inl (by simp [hz])
  · exact Or.inr (hexStr_head n (by omega))

end JuliaLean.Sockets
