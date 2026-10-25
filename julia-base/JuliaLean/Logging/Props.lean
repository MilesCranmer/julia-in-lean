import JuliaLean.Logging.Model

namespace JuliaLean.Logging

open JuliaLean

def LogLevelOrderArithmetic : Prop :=
  (∀ a b : LogLevel, logLess a b ↔ a.val < b.val) ∧
  (∀ level : LogLevel, ∀ inc : Int,
    IntTy.i32.min ≤ level.val + inc → level.val + inc ≤ IntTy.i32.max →
    ∃ result, addInt level inc = .ok result ∧ result.val = level.val + inc) ∧
  (∀ level : LogLevel, ∀ inc : Int,
    IntTy.i32.min ≤ level.val - inc → level.val - inc ≤ IntTy.i32.max →
    ∃ result, subInt level inc = .ok result ∧ result.val = level.val - inc)

def DirectSpecialKeyHandling : Prop :=
  (∀ key : Key, key.isSpecial = true →
    processArgs [.assignment key] = { overrides := [key], kwargs := [] }) ∧
  processArgs [.assignment .maxlog, .assignment .exception] =
    { overrides := [], kwargs := [.maxlog, .exception] }

def SpecialKeysFromSplat : Prop := ∀ key : Key, key.isSpecial = true →
  processArgs [.splat [key]] = processArgs [.assignment key]

def CustomLevelAcceptedByBuiltins : Prop := ∀ level : InputLevel,
  builtinDispatch level = .message

def DebugEnvironmentExact : Prop :=
  (∀ names : List String,
    DebugConfig.ofTokens (names.map .include) = { includes := names }) ∧
  (∀ names : List String, (∀ name ∈ names, name.isEmpty = false) →
    DebugConfig.ofTokens (names.map .exclude) = { excludes := names }) ∧
  (∀ includes excludes : List String, ∀ group moduleName rootName : String,
    envOverride { includes, excludes } group moduleName rootName =
      if !excludes.contains "all" && (includes.contains "all" || !excludes.isEmpty) then
        if excludes.isEmpty then true
        else !matchesName excludes group moduleName rootName
      else
        if includes.isEmpty then false
        else matchesName includes group moduleName rootName)

def BuiltinFilteringExact : Prop :=
  ∀ globalMinimum minimum level : LogLevel, ∀ debug : DebugConfig,
    ∀ group moduleName rootName : String, ∀ idAvailable : Bool,
      macroEmits globalMinimum (.console minimum) level debug group moduleName rootName idAvailable =
        (levelAtLeast level globalMinimum &&
          (levelAtLeast level minimum || envOverride debug group moduleName rootName) && idAvailable) ∧
      macroEmits globalMinimum (.simple minimum) level debug group moduleName rootName idAvailable =
        (levelAtLeast level globalMinimum &&
          (levelAtLeast level minimum || envOverride debug group moduleName rootName) && idAvailable) ∧
      macroEmits globalMinimum .null level debug group moduleName rootName idAvailable = false

def DisableLoggingTotal : Prop := ∀ level : LogLevel, ∃ threshold : LogLevel,
  disableLogging level = .ok threshold

def MaxlogBuiltinBound : Prop := ∀ requested calls : Nat,
  (runMaxlog .builtin requested calls).emissions ≤ requested

def MaxlogIntegerBound : Prop := ∀ kind : IntegerKind, ∀ requested calls : Nat,
  (runMaxlog kind requested calls).emissions ≤ requested

def WithLoggerRestores : Prop := ∀ previous installed : Nat, ∀ outcome : Outcome,
  let trace := withLogger previous installed outcome
  trace.during = installed ∧ trace.after = previous ∧ trace.outcome = outcome ∧
    inheritedLogger trace.during = installed

def ConsoleFormattingPreservesLines : Prop := ∀ first : String, ∀ rest : List String,
  (decorateConsole (first :: rest)).map DecoratedLine.text = first :: rest ∧
    (simpleMessageLines (first :: rest)).map PhysicalLine.text = first :: rest ∧
    (simpleMessageLines (first :: rest)).all PhysicalLine.prefixed = true

def RightJustifyUsesDisplayWidth : Prop := ∀ target fixedWidth : Nat, ∀ message : List Cell,
  fixedWidth + terminalLength message ≤ target →
  rightJustifiedWidth target fixedWidth message = target

def SimpleMultilineValuePrefixed : Prop := ∀ key first : String, ∀ rest : List String,
  (simpleValueLines key (first :: rest)).all PhysicalLine.prefixed = true

end JuliaLean.Logging
