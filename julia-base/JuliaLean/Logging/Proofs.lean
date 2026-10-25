import JuliaLean.Logging.Props

namespace JuliaLean.Logging

open JuliaLean

theorem logLevelOrderArithmetic_proven : LogLevelOrderArithmetic := by
  constructor
  · intro a b
    rfl
  constructor
  · intro level inc hmin hmax
    simp [addInt, JInt.convert, hmin, hmax]
  · intro level inc hmin hmax
    simp [subInt, JInt.convert, hmin, hmax]

theorem directSpecialKeyHandling_proven : DirectSpecialKeyHandling := by
  constructor
  · intro key special
    cases key <;> simp_all [Key.isSpecial, processArgs, processArg, ProcessedArgs.append]
  · decide

theorem foldIncludeTokens (names : List String) (config : DebugConfig) :
    (names.map DebugToken.include).foldl DebugConfig.addToken config =
      { config with includes := config.includes ++ names } := by
  induction names generalizing config with
  | nil => simp
  | cons name names ih =>
      simp [DebugConfig.addToken, ih, List.append_assoc]

theorem foldExcludeTokens (names : List String) (config : DebugConfig)
    (nonempty : ∀ name ∈ names, name.isEmpty = false) :
    (names.map DebugToken.exclude).foldl DebugConfig.addToken config =
      { config with excludes := config.excludes ++ names } := by
  induction names generalizing config with
  | nil => simp
  | cons name names ih =>
      have head := nonempty name (by simp)
      have tail : ∀ item ∈ names, item.isEmpty = false := by
        intro item member
        exact nonempty item (by simp [member])
      simp [DebugConfig.addToken, head, ih _ tail, List.append_assoc]

theorem debugEnvironmentExact_proven : DebugEnvironmentExact := by
  constructor
  · intro names
    simpa [DebugConfig.ofTokens] using foldIncludeTokens names ({} : DebugConfig)
  constructor
  · intro names nonempty
    simpa [DebugConfig.ofTokens] using foldExcludeTokens names ({} : DebugConfig) nonempty
  · intro includes excludes group moduleName rootName
    rfl

theorem builtinFilteringExact_proven : BuiltinFilteringExact := by
  intro globalMinimum minimum level debug group moduleName rootName idAvailable
  simp [macroEmits, Logger.minimum, Logger.shouldLog]

def limitInvariant (requested : Nat) (state : LimitState) : Prop :=
  state.emissions + state.remaining.getD requested ≤ requested

theorem maxlogCall_preserves (requested : Nat) (state : LimitState)
    (invariant : limitInvariant requested state) :
    limitInvariant requested (maxlogCall .builtin requested state) := by
  cases state with
  | mk remaining emissions =>
      cases remaining with
      | none =>
          by_cases zero : requested = 0
          · simp [limitInvariant, maxlogCall, zero] at invariant ⊢
            omega
          · simp [limitInvariant, maxlogCall, zero] at invariant ⊢
            omega
      | some remaining =>
          by_cases zero : remaining = 0
          · simpa [limitInvariant, maxlogCall, zero] using invariant
          · simp [limitInvariant, maxlogCall, zero] at invariant ⊢
            omega

theorem runMaxlogFrom_invariant (requested calls : Nat) (state : LimitState)
    (invariant : limitInvariant requested state) :
    limitInvariant requested (runMaxlogFrom .builtin requested calls state) := by
  induction calls generalizing state with
  | zero => exact invariant
  | succ calls ih =>
      exact ih (maxlogCall .builtin requested state) (maxlogCall_preserves requested state invariant)

theorem maxlogBuiltinBound_proven : MaxlogBuiltinBound := by
  intro requested calls
  have invariant := runMaxlogFrom_invariant requested calls ({} : LimitState) (by
    simp [limitInvariant])
  change (runMaxlogFrom .builtin requested calls {}).emissions ≤ requested
  unfold limitInvariant at invariant
  omega

theorem withLoggerRestores_proven : WithLoggerRestores := by
  intro previous installed outcome
  simp [withLogger, inheritedLogger]

theorem decorateRest_preserves : ∀ lines : List String,
    (decorateRest lines).map DecoratedLine.text = lines := by
  intro lines
  induction lines with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second tail => simp [decorateRest, ih]

theorem decorateConsole_preserves : ∀ lines : List String,
    (decorateConsole lines).map DecoratedLine.text = lines := by
  intro lines
  cases lines with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail => simp [decorateConsole, decorateRest_preserves]

theorem consoleFormattingPreservesLines_proven : ConsoleFormattingPreservesLines := by
  intro first rest
  constructor
  · exact decorateConsole_preserves (first :: rest)
  constructor <;> simp [simpleMessageLines, Function.comp_def]

end JuliaLean.Logging
