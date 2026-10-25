import JuliaLean.Logging.Model

/-! Deterministic rows, mirrored line by line by a Julia differential script. -/

namespace JuliaLean.Logging.Validation

open JuliaLean.Logging

private def outLevel : JuliaLean.Jl LogLevel → String
  | .ok level => toString level.val
  | .error _ => "error"

private def envRow (tokens : List DebugToken) : String :=
  let config := DebugConfig.ofTokens tokens
  s!"{envOverride config "other" "Main" "Main"},{envOverride config "other" "Base" "Base"}," ++
    s!"{envOverride config "loading" "Base" "Base"},{envOverride config "other" "Core" "Core"}"

private def simplePrefixRow : String :=
  match simpleValueLines "value" ["one", "two"] with
  | first :: second :: _ => s!"{first.prefixed},{second.prefixed}"
  | _ => "missing"

def differential : List String :=
  [ s!"level add-info {outLevel (addInt Info 1000)}"
  , s!"level sub-warn {outLevel (subInt Warn 1000)}"
  , s!"disable-max {outLevel (disableLogging (JuliaLean.JInt.typemax .i32))}"
  , s!"keys direct-file {(processArgs [.assignment .fileKey]).overrides == [.fileKey]}"
  , s!"keys splat-file {(processArgs [.splat [.fileKey]]).overrides == [.fileKey]}"
  , s!"keys conventional {(processArgs [.assignment .maxlog, .assignment .exception]).kwargs == [.maxlog, .exception]}"
  , s!"custom-dispatch {builtinDispatch (.custom Info) == .message}"
  , s!"env-empty {envRow []}"
  , s!"env-main {envRow [.include "Main"]}"
  , s!"env-space-main {envRow [.include " Main"]}"
  , s!"env-main-loading {envRow [.include "Main", .include "loading"]}"
  , s!"env-main-space-loading {envRow [.include "Main", .include " loading"]}"
  , s!"env-not-main {envRow [.exclude "Main"]}"
  , s!"env-main-not-base {envRow [.include "Main", .exclude "Base"]}"
  , s!"env-all {envRow [.include "all"]}"
  , s!"env-not-all {envRow [.exclude "all"]}"
  , s!"filter-debug {macroEmits Debug (.console Info) Debug {} "other" "Main" "Main" true}"
  , s!"filter-info {macroEmits Debug (.console Info) Info {} "other" "Main" "Main" true}"
  , s!"filter-null {macroEmits Debug .null Error {} "other" "Main" "Main" true}"
  , s!"maxlog-builtin {(runMaxlog .builtin 1 3).emissions}"
  , s!"maxlog-big {(runMaxlog .big 1 3).emissions}"
  , s!"scope-error-restored {(withLogger 1 2 .threw).after == 1}"
  , s!"format-console-lines {(decorateConsole ["first", "", "third"]).map DecoratedLine.text == ["first", "", "third"]}"
  , s!"justify-ascii {rightJustifiedWidth 20 17 [.ascii, .ascii, .ascii]}"
  , s!"justify-wide {rightJustifiedWidth 20 19 [.wide]}"
  , s!"justify-combining {rightJustifiedWidth 20 18 [.ascii, .combining]}"
  , s!"simple-value-prefixes {simplePrefixRow}"
  ]

end JuliaLean.Logging.Validation
