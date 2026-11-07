import JuliaLean.base.version

namespace JuliaLean.VersionNumbers

open JuliaLean JuliaLean.ParsePrint.IntParse

/-- A bound `VersionBound(tin)` can produce: `n ≤ 3` and zeros past `n`. -/
def WellFormed (b : VersionBound) : Prop :=
  b.n ≤ 3 ∧ (b.n < 1 → b.t.1.val = 0) ∧ (b.n < 2 → b.t.2.1.val = 0) ∧ (b.n < 3 → b.t.2.2.val = 0)

/-- `VersionRange(string(r))` reconstructs a range with the same members as `r`
(`show(r)` prints `VersionRange("<string(r)>")`, `base/version.jl:466`). -/
def RangePrintRoundtrip : Prop :=
  ∀ lo hi, WellFormed lo → WellFormed hi →
    ∃ r', parseRange (printRange (mkRange lo hi)) = .ok r' ∧
      ∀ v, inRange v r' = inRange v (mkRange lo hi)

/-- `VersionRange("*-2")`: lower bound `*`, upper bound `2`. -/
def starToTwo : VersionRange := mkRange boundStar ⟨(u32 2, u32 0, u32 0), 1⟩

theorem starToTwo_parse : parseRange (ascii "*-2") = .ok starToTwo := by decide +kernel

theorem starToTwo_print : printRange starToTwo = ascii "0 -2.0.0" := by decide +kernel

theorem starToTwo_reparse :
    parseRange (printRange starToTwo) = .ok ⟨⟨(u32 0, u32 0, u32 0), 1⟩, ⟨(u32 2, u32 0, u32 0), 3⟩⟩ := by
  decide +kernel

/-- `v"2.5.0"`. -/
def v250 : VersionNumber := ⟨u32 2, u32 5, u32 0, [], []⟩

theorem rangePrintRoundtrip_refuted : ¬ RangePrintRoundtrip := by
  intro h
  obtain ⟨r', hp, hin⟩ := h boundStar ⟨(u32 2, u32 0, u32 0), 1⟩ (by unfold WellFormed; decide) (by unfold WellFormed; decide)
  have e : mkRange boundStar ⟨(u32 2, u32 0, u32 0), 1⟩ = starToTwo := rfl
  rw [e, starToTwo_reparse] at hp
  cases hp
  have := hin v250
  revert this
  decide

end JuliaLean.VersionNumbers
