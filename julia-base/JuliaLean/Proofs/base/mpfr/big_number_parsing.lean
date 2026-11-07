import JuliaLean.base.mpfr

namespace JuliaLean.BigNums

open JuliaLean

/-- `tryparse(BigFloat, s; base)` never aborts the process, whatever `s` and `base`. -/
def TryparseBigFloatTotal : Prop :=
  ∀ (setStr : List Char → Nat → Option BF) (s : List Char) (base : Int),
    tryparseBF setStr s base ≠ .abort

theorem tryparseBigFloatTotal_refuted : ¬ TryparseBigFloatTotal := by
  intro h
  exact h (fun _ _ => none) ['1'] 1 (by decide)

/-- `tryparse(BigFloat, s)` returns a value or `nothing` and never throws (the `tryparse`
docstring, `base/parse.jl:241-246`). -/
def TryparseBigFloatNoThrow : Prop :=
  ∀ (setStr : List Char → Nat → Option BF) (s : List Char),
    ∃ v, tryparseBF setStr s 0 = .ok v

theorem tryparseBigFloatNoThrow_refuted : ¬ TryparseBigFloatNoThrow := by
  intro h
  obtain ⟨v, hv⟩ := h (fun _ _ => none) ['1', Char.ofNat 0]
  have h2 : tryparseBF (fun _ _ => none) ['1', Char.ofNat 0] 0 =
      .throw (.argumentError "embedded NULs are not allowed in C strings") := by decide
  rw [h2] at hv
  cases hv

end JuliaLean.BigNums
