import JuliaLean.Registry.Types
import JuliaLean.Logging.Model
import JuliaLean.Logging.Props
import JuliaLean.Logging.Proofs
import JuliaLean.Logging.Refutations
import JuliaLean.Logging.Validation

namespace JuliaLean.Logging

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- refuted
  { id := "logging-splat-special-keys", juliaFile := "base/logging/logging.jl"
    juliaFns := ["@logmsg", "process_logmsg_exs"]
    statement := "Special metadata keys supplied by keyword splatting override the same fields as direct assignments."
    source := "base/logging/logging.jl:213-239 (keyword splatting and special-key overrides)", status := .refuted
    prop := ``SpecialKeysFromSplat, thm := some ``specialKeysFromSplat_refuted
    issue := "none found (queries: logging special keys splat, logging _file splat, logging keyword splatting)"
    notes := "A splatted `_file=\"fake.jl\"` is printed as ordinary metadata while the real source file remains the location. Direct assignment overrides it." },
  { id := "logging-custom-level-builtins", juliaFile := "base/logging/logging.jl"
    juliaFns := ["@logmsg", "handle_message(::ConsoleLogger, ...)", "handle_message(::SimpleLogger, ...)"]
    statement := "Every custom level accepted by @logmsg's LogLevel conversion can be handled by the built-in text loggers."
    source := "base/logging/logging.jl:201-207 (custom log level types)", status := .refuted
    prop := ``CustomLevelAcceptedByBuiltins, thm := some ``customLevelAcceptedByBuiltins_refuted
    issue := "related #33418; open PR #33960 explicitly fixes custom ConsoleLogger levels"
    notes := "The macro filters with the converted LogLevel but passes the original value to a handler constrained to LogLevel, replacing the intended record with an internal MethodError log." },
  { id := "logging-disable-typemax", juliaFile := "base/logging/logging.jl"
    juliaFns := ["disable_logging", "+(::LogLevel, ::Integer)"]
    statement := "disable_logging returns normally for every valid LogLevel and disables all messages at or below it."
    source := "base/logging/logging.jl:552-567 (disable_logging docstring and implementation)", status := .refuted
    prop := ``DisableLoggingTotal, thm := some ``disableLoggingTotal_refuted
    issue := "none found (queries: disable_logging, LogLevel typemax, disable_logging overflow)"
    notes := "LogLevel(typemax(Int32)) is valid, but level + 1 throws InexactError while converting 2147483648 back to Int32." },
  { id := "logging-maxlog-bigint", juliaFile := "base/logging/logging.jl"
    juliaFns := ["handle_message(::ConsoleLogger, ...)", "handle_message(::SimpleLogger, ...)"]
    statement := "For every nonnegative Integer maxlog=n, one id is emitted at most n times."
    source := "base/logging/logging.jl:233-236 (maxlog=integer contract)", status := .refuted
    prop := ``MaxlogIntegerBound, thm := some ``maxlogIntegerBound_refuted
    issue := "none found (queries: maxlog BigInt, maxlog Integer logging, Core.BuiltinInts maxlog)"
    notes := "maxlog=big(1) is ignored because both handlers test Core.BuiltinInts; three calls with one id emit three records." },
  { id := "logging-right-justify-unicode", juliaFile := "base/logging/ConsoleLogger.jl"
    juliaFns := ["termlength", "handle_message(::ConsoleLogger, ...)"]
    statement := "When a ConsoleLogger suffix fits on its line, right_justify places its right edge at the requested terminal column for every message."
    source := "base/logging/ConsoleLogger.jl:25-26,90-108,169-193", status := .refuted
    prop := ``RightJustifyUsesDisplayWidth, thm := some ``rightJustifyUsesDisplayWidth_refuted
    issue := "none found (queries: right_justify ConsoleLogger, termlength logging, ConsoleLogger unicode width)"
    notes := "At column 20, a CJK message ends at column 21 and an e plus combining acute message ends at column 19 because termlength counts characters rather than terminal cells." },
  { id := "logging-simplelogger-multiline-value", juliaFile := "base/logging/logging.jl"
    juliaFns := ["handle_message(::SimpleLogger, ...)"]
    statement := "Every physical line of a multiline SimpleLogger metadata value carries the record's box prefix."
    source := "structured-output invariant; base/logging/logging.jl:674-682,710-729", status := .refuted
    prop := ``SimpleMultilineValuePrefixed, thm := some ``simpleMultilineValuePrefixed_refuted
    issue := "none found (queries: SimpleLogger multiline, SimpleLogger newline value, logging key value multiline)"
    notes := "value=\"one\\ntwo\" prints the `two` continuation at column one between the prefixed value line and record footer." },
  -- proven
  { id := "logging-loglevel-order-arithmetic", juliaFile := "base/logging/logging.jl"
    juliaFns := ["isless(::LogLevel, ::LogLevel)", "+(::LogLevel, ::Integer)", "-(::LogLevel, ::Integer)"]
    statement := "LogLevel comparison is Int32 order, and addition or subtraction returns the exact integer result whenever it fits Int32."
    source := "base/logging/logging.jl:110-137", status := .proven
    prop := ``LogLevelOrderArithmetic, thm := some ``logLevelOrderArithmetic_proven },
  { id := "logging-direct-special-keys", juliaFile := "base/logging/logging.jl"
    juliaFns := ["@logmsg", "process_logmsg_exs"]
    statement := "Direct _module, _group, _id, _file, and _line assignments override generated fields, while maxlog and exception remain structured metadata."
    source := "base/logging/logging.jl:213-239,443-483", status := .proven
    prop := ``DirectSpecialKeyHandling, thm := some ``directSpecialKeyHandling_proven },
  { id := "logging-debug-environment", juliaFile := "base/logging/logging.jl"
    juliaFns := ["env_override_minlevel"]
    statement := "JULIA_DEBUG matches comma-separated group, module, or root names exactly; all enables every name, exclusions select all except their names, !all disables all, and whitespace is significant."
    source := "stdlib/Logging/docs/src/index.md:185-228; base/logging/logging.jl:569-616", status := .proven
    prop := ``DebugEnvironmentExact, thm := some ``debugEnvironmentExact_proven
    notes := "The manual documents positive module/file names, all, and comma separation. Negation and significant whitespace follow the source implementation and were differentially checked." },
  { id := "logging-builtin-filtering", juliaFile := "base/logging/logging.jl"
    juliaFns := ["min_enabled_level", "shouldlog", "current_logger_for_env", "disable_logging", "NullLogger"]
    statement := "ConsoleLogger and SimpleLogger emit exactly when the global threshold, logger minimum or JULIA_DEBUG override, and per-id shouldlog test pass; NullLogger never emits."
    source := "stdlib/Logging/docs/src/index.md:151-170; base/logging/logging.jl:94-105,340-346,396-427", status := .proven
    prop := ``BuiltinFilteringExact, thm := some ``builtinFilteringExact_proven },
  { id := "logging-maxlog-builtin-bound", juliaFile := "base/logging/logging.jl"
    juliaFns := ["shouldlog(::ConsoleLogger, ...)", "shouldlog(::SimpleLogger, ...)", "handle_message"]
    statement := "For nonnegative built-in integer maxlog=n, a shared logger emits one id at most n times across any task interleaving."
    source := "base/logging/logging.jl:681-708; base/logging/ConsoleLogger.jl:12-13,51-52,114-121", status := .proven
    prop := ``MaxlogBuiltinBound, thm := some ``maxlogBuiltinBound_proven
    notes := "The handler lock linearizes task calls into the proved serialized sequence. The 27-row differential used three calls for n=1." },
  { id := "logging-with-logger-restores", juliaFile := "base/logging/logging.jl"
    juliaFns := ["with_logstate", "with_logger", "current_logger"]
    statement := "with_logger installs its logger dynamically, child work inherits it, and the previous logger is restored after normal return or an exception."
    source := "stdlib/Logging/docs/src/index.md:126-138; base/logging/logging.jl:540-547,639-667", status := .proven
    prop := ``WithLoggerRestores, thm := some ``withLoggerRestores_proven },
  { id := "logging-formatting-lines", juliaFile := "base/logging/ConsoleLogger.jl"
    juliaFns := ["showvalue", "handle_message(::ConsoleLogger, ...)", "handle_message(::SimpleLogger, ...)"]
    statement := "ConsoleLogger preserves every physical message and showvalue line with one box decoration, and SimpleLogger preserves and prefixes every message line."
    source := "stdlib/Logging/docs/src/index.md:37-51; base/logging/ConsoleLogger.jl:56-63,124-194; base/logging/logging.jl:710-715", status := .proven
    prop := ``ConsoleFormattingPreservesLines, thm := some ``consoleFormattingPreservesLines_proven
    notes := "The property starts from the lines produced under the stream's displaysize and show_limited setting, so intentional show truncation is retained rather than treated as lost formatting." }
]

end JuliaLean.Logging
