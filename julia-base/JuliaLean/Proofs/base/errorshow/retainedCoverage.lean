import JuliaLean.base.errorshow


namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

theorem closeRepetitions_unfold (line frameCounter active : Nat) (cycles : List CycleClosing) :
    closeRepetitions line frameCounter active cycles =
      match cycles with
      | [] => (frameCounter, active)
      | cycle :: rest =>
          if line = cycle.startLine + cycle.cycleLength - 1 then
            closeRepetitions line (frameCounter + cycle.frameAdvance) (active - 1) rest
          else (frameCounter, active) := by
  cases cycles <;> rfl

def ErrorShowTypeDiffExact : Prop :=
  (∀ runtimeTypes, typesOf runtimeTypes = runtimeTypes) ∧
  (∀ isType typeText,
    stripType isType typeText = if isType then some typeText else none) ∧
  (∀ sameIdentity shown,
    printWithCompare sameIdentity shown =
      if sameIdentity then .same shown else .mismatch shown) ∧
  (∀ target source firstArgument,
    showConvertError target source firstArgument =
      match target with
      | none => "First argument to `convert` must be a Type, got " ++ firstArgument
      | some target => "Cannot `convert` an object of type " ++ source ++
          " to an object of type " ++ target) ∧
  (∀ compatible tokens,
    showNamedTupleDiff compatible tokens = if compatible then some tokens else none) ∧
  (∀ sameOuter nonempty parameters,
    descendParameters sameOuter nonempty parameters =
      if sameOuter && nonempty then some parameters else none) ∧
  (∀ moduleDefined parentSame,
    resolvesToSelf moduleDefined parentSame = (!moduleDefined || parentSame)) ∧
  (∀ shadows, shadowedTypeHints shadows = shadows.eraseDups) ∧
  (∀ color, showSeparator color =
    if color then [.literal "color(light_black)", .literal ", ", .literal "color(default)"]
    else [.literal ", "]) ∧
  (∀ text top color, showTypeMismatch text top color =
    if color then [.literal "error-color", .mismatch text, .literal "default-color"]
    else if top then [.literal "!Matched{", .mismatch text, .literal "}"]
    else [.literal "!Matched::", .mismatch text])

theorem errorShowTypeDiffExact : ErrorShowTypeDiffExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ErrorShowBacktraceExact : Prop :=
  (∀ value default, envBool value default = value.getD default) ∧
  (∀ message staticError,
    showErrorNoStdio message staticError = message ++ ":\n" ++ staticError ++ "\n") ∧
  (∀ fixed next, stacktraceColor fixed next = fixed.orElse (fun _ => next)) ∧
  (∀ line frameCounter active cycles,
    closeRepetitions line frameCounter active cycles =
      match cycles with
      | [] => (frameCounter, active)
      | cycle :: rest =>
          if line = cycle.startLine + cycle.cycleLength - 1 then
            closeRepetitions line (frameCounter + cycle.frameAdvance) (active - 1) rest
          else (frameCounter, active)) ∧
  (∀ linePrefix signature location number width active starts inlined,
    stackFrameLayout linePrefix signature location number width active starts inlined =
      linePrefix ++ " " ++ String.ofList (List.replicate (active - starts) '├') ++
        String.ofList (List.replicate starts '┌') ++
        String.ofList (List.replicate (width - (toString number).length - 2) ' ') ++
        "[" ++ toString number ++ "] " ++
        signature ++ "\n" ++ linePrefix ++ " " ++ String.ofList (List.replicate active '│') ++
        " @ " ++ location ++ (if inlined then " [inlined]" else "")) ∧
  (∀ empty singleUnknown large,
    showBacktraceRoute empty singleUnknown large =
      if empty then .empty else if singleUnknown then .suppressTopLevel
      else if large then .findCycles else .direct) ∧
  (∀ moduleName directory file line column,
    modulePathFile moduleName directory file line column =
      "@ " ++ (if moduleName.isEmpty then "" else moduleName ++ " ") ++
        (if directory.isEmpty then "" else directory ++ "/") ++ file ++ ":" ++
        (if line < 0 then "?" else toString line) ++
        (if column = 0 then "" else ":" ++ toString column)) ∧
  (∀ typeName code moduleName statement topLevel,
    showInterpreterIP typeName code moduleName statement topLevel =
      typeName ++ (if topLevel then " in top-level CodeInfo for " ++ moduleName
        else " in " ++ code) ++ " at statement " ++ toString statement) ∧
  (∀ frames, removeKwcallFrames frames = frames.filter fun frame => !frame.removeKwcall) ∧
  (∀ frames, simplifyIncludes frames = frames.filter fun frame => frame.keepInclude) ∧
  (∀ frame, isLoadingFrame frame = frame.loadingFrame) ∧
  (∀ frame, isLoadingAnchor frame = frame.loadingAnchor) ∧
  (∀ fullLoading frames,
    simplifyLoading fullLoading frames =
      if fullLoading then frames
      else frames.filter fun frame => !frame.loadingFrame || frame.loadingAnchor) ∧
  (∀ frames, collapseLocations frames = frames.filter fun frame => frame.keepLocation) ∧
  (∀ fullLoading frames, processBacktrace fullLoading frames =
    collapseRepeatedFrames
      (collapseLocations (simplifyLoading fullLoading (simplifyIncludes (removeKwcallFrames frames))))) ∧
  (∀ exceptions,
    showExceptionStack exceptions = String.intercalate "\ncaused by: " exceptions.reverse)

theorem errorShowBacktraceExact : ErrorShowBacktraceExact := by
  repeat' apply And.intro
  all_goals intros <;> first | rfl | exact closeRepetitions_unfold _ _ _ _

def ErrorShowHintsExact : Prop :=
  (∀ condition message,
    hintWhen condition message = if condition then .message message else .none) ∧
  (∀ fields properties,
    propertyNamesByType fields properties = (fields ++ properties).eraseDups) ∧
  (∀ stack, exceptionStackSize stack = stack.length) ∧
  (∀ stack index, exceptionStackGet? stack index = stack[index]?) ∧
  (∀ headIncomplete hasArgument kind,
    incompleteTag headIncomplete hasArgument kind =
      if !headIncomplete then .none else if !hasArgument then .other else kind)

theorem errorShowHintsExact : ErrorShowHintsExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.ErrorShow.Coverage
