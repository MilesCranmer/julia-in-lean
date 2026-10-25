import JuliaLean.Logging.Props

namespace JuliaLean.Logging

open JuliaLean

theorem specialKeysFromSplat_refuted : ¬ SpecialKeysFromSplat := by
  intro property
  have result := property .fileKey (by decide)
  revert result
  decide

theorem customLevelAcceptedByBuiltins_refuted : ¬ CustomLevelAcceptedByBuiltins := by
  intro property
  have result := property (.custom Info)
  revert result
  decide

theorem disableLoggingTotal_refuted : ¬ DisableLoggingTotal := by
  intro property
  obtain ⟨threshold, result⟩ := property (JInt.typemax .i32)
  simp [disableLogging, addInt, JInt.convert, JInt.typemax, JInt.wrap,
    wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, IntTy.name] at result

theorem maxlogIntegerBound_refuted : ¬ MaxlogIntegerBound := by
  intro property
  have result := property .big 1 3
  revert result
  decide

theorem rightJustifyUsesDisplayWidth_refuted : ¬ RightJustifyUsesDisplayWidth := by
  intro property
  have result := property 20 19 [.wide] (by decide)
  revert result
  decide

theorem simpleMultilineValuePrefixed_refuted : ¬ SimpleMultilineValuePrefixed := by
  intro property
  have result := property "value" "one" ["two"]
  revert result
  decide

end JuliaLean.Logging
