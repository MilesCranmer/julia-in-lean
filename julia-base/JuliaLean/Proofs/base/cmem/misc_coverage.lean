import JuliaLean.base.cmem

namespace JuliaLean.MiscCov.CMem

/-- The four wrappers call the C functions: for `0 ≤ n < 2^64`, `memcpy`/`memmove` make
`dst[k] == src[k]` for `k < n` and change nothing else, `memset` stores `val % 256`, all
return the destination pointer, and `memcmp` returns the sign of the first difference. -/
def Contract : Prop :=
  ∀ (m : Mem) (dst src : Nat) (n : Int), 0 ≤ n → n < 2 ^ 64 →
    (∃ m', memcpy m dst src n = .ok (m', dst) ∧
      (∀ k : Nat, k < n.toNat → m' (dst + k) = m (src + k)) ∧
      (∀ a, (a < dst ∨ dst + n.toNat ≤ a) → m' a = m a)) ∧
    (∃ m', memmove m dst src n = .ok (m', dst) ∧
      (∀ k : Nat, k < n.toNat → m' (dst + k) = m (src + k)) ∧
      (∀ a, (a < dst ∨ dst + n.toNat ≤ a) → m' a = m a)) ∧
    (∀ val : Int, -(2 ^ 31) ≤ val → val < 2 ^ 31 →
      ∃ m', memset m dst val n = .ok (m', dst) ∧
        ∀ k : Nat, k < n.toNat → m' (dst + k) = (val % 256).toNat) ∧
    memcmp m dst src n = .ok (cMemcmp m dst src n.toNat)

/-- A negative length is rejected with `InexactError` by every wrapper. -/
def NegativeLengthConsistent : Prop :=
  ∀ (m : Mem) (a b : Nat) (n : Int), n < 0 →
    memcpy m a b n = .error .inexactError ∧ memmove m a b n = .error .inexactError ∧
    memset m a 0 n = .error .inexactError ∧ memcmp m a b n = .error .inexactError

theorem contract_proven : Contract := by
  intro m dst src n h0 h1
  have hc : toCsize n = .ok n.toNat := by simp only [toCsize]; rw [if_pos ⟨h0, h1⟩]
  refine ⟨⟨(cMemcpy m dst src n.toNat).1, by simp only [memcpy, hc, bind, Except.bind, pure, Except.pure]; rfl, ?_, ?_⟩,
    ⟨(cMemmove m dst src n.toNat).1, by simp only [memmove, hc, bind, Except.bind, pure, Except.pure]; rfl, ?_, ?_⟩, ?_, ?_⟩
  · intro k hk; simp only [cMemcpy]; rw [if_pos (by omega)]; congr 1; omega
  · intro a ha; simp only [cMemcpy]; rw [if_neg (by omega)]
  · intro k hk; simp only [cMemmove]; rw [if_pos (by omega)]; congr 1; omega
  · intro a ha; simp only [cMemmove]; rw [if_neg (by omega)]
  · intro val hv0 hv1
    have hv : toCint val = .ok val := by simp only [toCint]; rw [if_pos ⟨hv0, hv1⟩]
    refine ⟨(cMemset m dst val n.toNat).1, by simp only [memset, hv, hc, bind, Except.bind, pure, Except.pure]; rfl, ?_⟩
    intro k hk; simp only [cMemset]; rw [if_pos (by omega)]
  · simp only [memcmp, remCsize]
    rw [Int.emod_eq_of_lt h0 h1]

theorem negativeLengthConsistent_refuted : ¬ NegativeLengthConsistent := by
  intro h
  have := (h (fun a => if a = 0 then 1 else 9) 0 1 (-1) (by decide)).2.2.2
  revert this
  decide

end JuliaLean.MiscCov.CMem
