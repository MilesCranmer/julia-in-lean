import JuliaLean.base.logging.logging
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.logging.logging

namespace Round1

open JuliaLean JuliaLean.base.logging.logging

/-
Public methods with no separate nontrivial promise (base/logging/logging.jl):
* catch_exceptions@72: The default constant true supplies the exception policy; the
  nontrivial record-construction behavior belongs to the full macro contracts.
* NullLogger@100: The generated empty constructor is plumbing; complete rejection
  without accepted records or backend output belongs to the macro filtering contract.
* min_enabled_level@102: The constant AboveMaxLevel supplies one early filter; full
  NullLogger rejection is tracked by the public pipeline contract.
* shouldlog@103: The constant false is rejection plumbing; lazy message rejection and
  absence of backend output belong to the full macro contract.
* handle_message@104: The fixed diagnostic guards a call rejected by the public
  NullLogger pipeline; no independent diagnostic punctuation promise is documented.
* LogLevel@129: The identity constructor adds no behavior beyond preserving an existing
  value; full converting construction and severity ordering are tracked separately.
* convert@137: This method projects the stored Int32 field; complete numeric
  construction and ordering carry the substantive behavior.
* min_enabled_level@696: This method projects the stored minimum; constructor and
  filtering contracts retain its observable role and the documented boundary
  inconsistency.
* catch_exceptions@698: The constant false selects propagation; complete macro and
  handler contracts retain construction and handling failures.
-/

/-- LogLevel comparison is a strict total order oriented upward through every
consecutive value of the complete Int32 severity range, with its true endpoints.
Julia source: base/logging/logging.jl:125-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:206-224; base/logging/logging.jl:111-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LogLevelStrictTotalOrderCorrect : Prop :=
  (∀ level : LogLevel, islessLogLevel level level = false) ∧
  (∀ a b : LogLevel,
    (a = b ∧ islessLogLevel a b = false ∧ islessLogLevel b a = false) ∨
    (a ≠ b ∧ islessLogLevel a b = true ∧ islessLogLevel b a = false) ∨
    (a ≠ b ∧ islessLogLevel a b = false ∧ islessLogLevel b a = true)) ∧
  (∀ a b c : LogLevel,
    islessLogLevel a b = true → islessLogLevel b c = true →
      islessLogLevel a c = true) ∧
  (∀ level : LogLevel,
    level.level.val < IntTy.max .i32 →
      islessLogLevel level ⟨JInt.wrap .i32 (level.level.val + 1)⟩ = true) ∧
  (∀ level : LogLevel,
    islessLogLevel level ⟨JInt.wrap .i32 (IntTy.min .i32)⟩ = false ∧
    islessLogLevel ⟨JInt.wrap .i32 (IntTy.max .i32)⟩ level = false)

end Round1

end JuliaLean.Proofs.base.logging.logging

namespace JuliaLean.ChatGPT.Batch4.Group12
open JuliaLean JuliaLean.base.logging.logging

private theorem logLevel_eq_of_value_eq (a b : LogLevel)
    (h : a.level.val = b.level.val) : a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      have hab : a = b := Subtype.ext h
      cases hab
      rfl

/-- concurrencycov-logging-less-level-level-v2 -/
theorem ConcurrencycovLoggingLessLevelLevelV2_proven :
    JuliaLean.Proofs.base.logging.logging.Round1.LogLevelStrictTotalOrderCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro level
    simp only [islessLogLevel, Int.lt_irrefl, decide_false]
  · intro a b
    by_cases h : a.level.val = b.level.val
    · have hab := logLevel_eq_of_value_eq a b h
      subst b
      exact Or.inl ⟨rfl, by simp only [islessLogLevel, Int.lt_irrefl, decide_false],
        by simp only [islessLogLevel, Int.lt_irrefl, decide_false]⟩
    · have hne : a ≠ b := by
        intro hab
        cases hab
        exact h rfl
      by_cases hlt : a.level.val < b.level.val
      · exact Or.inr (Or.inl ⟨hne,
          by simp only [islessLogLevel, hlt, decide_true],
          by simp only [islessLogLevel]; exact decide_eq_false (by omega)⟩)
      · exact Or.inr (Or.inr ⟨hne,
          by simp only [islessLogLevel, hlt, decide_false],
          by simp only [islessLogLevel]; exact decide_eq_true (by omega)⟩)
  · intro a b c hab hbc
    simp only [islessLogLevel, decide_eq_true_eq] at hab hbc ⊢
    omega
  · intro level hmax
    have hlow := level.level.property.1
    have hsucc : IntTy.min .i32 ≤ level.level.val + 1 ∧
        level.level.val + 1 ≤ IntTy.max .i32 := by omega
    simp only [islessLogLevel, JInt.wrap, wrapInt_of_inRange .i32 _ hsucc,
      decide_eq_true_eq]
    omega
  · intro level
    have bounds := level.level.property
    have hrange : IntTy.min .i32 ≤ IntTy.max .i32 := by decide
    have hmin := wrapInt_of_inRange .i32 (IntTy.min .i32) ⟨Int.le_refl _, hrange⟩
    have hmax := wrapInt_of_inRange .i32 (IntTy.max .i32) ⟨hrange, Int.le_refl _⟩
    simp only [islessLogLevel, JInt.wrap, hmin, hmax, decide_eq_false_iff_not]
    omega

end JuliaLean.ChatGPT.Batch4.Group12

namespace JuliaLean.Proofs.base.logging.logging

open JuliaLean.Registry
def entries : List JuliaLean.Registry.Entry := [
  { id := "concurrencycov-logging-less-level-level-v2", juliaFile := "base/logging/logging.jl",
    juliaFns := ["isless(::LogLevel,::LogLevel)"],
    statement := "Every LogLevel in the complete Int32 range obeys a strict total order, upward adjacency and true minimum/maximum endpoints; includes equality/trichotomy, irreflexivity and transitivity. Source base/logging/logging.jl:125-137; docs111-127 and base/operators.jl:206-224. The only successor bound is the real Int32 maximum, not a narrowed severity range. Uses installed islessLogLevel:74 and no callback laws, constructor/body equivalence or expected comparator.",
    source := "base/logging/logging.jl:125-137; base/operators.jl:206-224",
    status := .proven, prop := ``Round1.LogLevelStrictTotalOrderCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group12.ConcurrencycovLoggingLessLevelLevelV2_proven }
]

end JuliaLean.Proofs.base.logging.logging
