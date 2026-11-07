import JuliaLean.base.tuple

namespace JuliaLean.Multidim

namespace SmallAux

/-! ## `isless` on `CartesianIndex` -/

theorem tupleLess_irrefl : ∀ a : List I64, tupleLess a a = false
  | [] => rfl
  | x :: xs => by simp [tupleLess, tupleLess_irrefl xs]

theorem tupleLess_trans : ∀ a b c : List I64,
    tupleLess a b = true → tupleLess b c = true → tupleLess a c = true
  | [], [], _, h, _ => by simp [tupleLess] at h
  | [], _ :: _, [], _, h => by simp [tupleLess] at h
  | [], _ :: _, _ :: _, _, _ => by simp [tupleLess]
  | _ :: _, [], _, h, _ => by simp [tupleLess] at h
  | _ :: _, _ :: _, [], _, h => by simp [tupleLess] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [tupleLess, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨by omega, tupleLess_trans xs ys zs h1' h2'⟩

theorem tupleLess_total : ∀ a b : List I64, a.length = b.length →
    tupleLess a b = true ∨ a = b ∨ tupleLess b a = true
  | [], [], _ => Or.inr (Or.inl rfl)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    have hl : xs.length = ys.length := by simpa using h
    simp only [tupleLess, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.cons.injEq]
    rcases Int.lt_trichotomy x.val y.val with hxy | hxy | hxy
    · exact Or.inl (Or.inl hxy)
    · have hxy' : x = y := Subtype.ext hxy
      rcases tupleLess_total xs ys hl with h' | h' | h'
      · exact Or.inl (Or.inr ⟨hxy, h'⟩)
      · exact Or.inr (Or.inl ⟨hxy', h'⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hxy.symm, h'⟩))
    · exact Or.inr (Or.inr (Or.inl hxy))

end SmallAux

open SmallAux


end JuliaLean.Multidim
