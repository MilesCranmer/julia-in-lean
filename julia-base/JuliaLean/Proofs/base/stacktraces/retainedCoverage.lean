import JuliaLean.base.stacktraces


namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

def StackFrameMethodsExact : Prop :=
  (∀ functionName file line,
    shortFrame functionName file line = { functionName, file, line }) ∧
  (∀ left right : FullFrame,
    frameEqual left right =
      (left.line == right.line && left.fromC == right.fromC &&
       left.functionName == right.functionName && left.file == right.file &&
       left.inlined == right.inlined)) ∧
  (∀ hashPart frame seed,
    frameHash hashPart frame seed =
      let seed := seed ^^^ 0xf4fbda67fe20ce88
      let seed := hashPart frame.line.natAbs seed
      let seed := hashPart frame.file.length seed
      let seed := hashPart frame.functionName.length seed
      let seed := hashPart (if frame.fromC then 1 else 0) seed
      hashPart (if frame.inlined then 1 else 0) seed) ∧
  (∀ lookups : List (List FullFrame), ∀ includeC : Bool,
    flattenLookups lookups includeC =
      (lookups.flatten).filter (fun frame => includeC || !frame.fromC)) ∧
  (∀ stack : List FullFrame, ∀ moduleId : Nat,
    removeModuleFrames stack moduleId =
      stack.filter fun frame => frame.moduleId != some moduleId) ∧
  (∀ frame isCodeInfo,
    isTopLevelFrame frame isCodeInfo =
      (isCodeInfo || (frame.linfo.isNone && frame.functionName == "top-level scope"))) ∧
  (∀ owner, frameMethodOrModule owner = owner.getD .none) ∧
  (∀ linfo, frameMethodInstance linfo = linfo) ∧
  (∀ source fallbackFile fallbackLine pc,
    frameLocation source fallbackFile fallbackLine pc =
      source.getD (fallbackFile, fallbackLine, pc)) ∧
  (∀ own lineTableEdges ownEdges,
    addDebugFrames own lineTableEdges ownEdges =
      own :: (lineTableEdges.flatten ++ ownEdges.flatten))

theorem stackFrameMethodsExact : StackFrameMethodsExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def StackFrameDisplayExact : Prop :=
  (∀ signature location inlined,
    showFrame signature location inlined =
      signature ++ (if location.isEmpty then "" else " at " ++ location) ++
        (if inlined then " [inlined]" else "")) ∧
  (∀ methodModule codeModule : Option Nat,
    parentModuleOfFrame methodModule codeModule = methodModule.orElse (fun _ => codeModule)) ∧
  (∀ frameModule target, fromModule frameModule target = (frameModule == target))

theorem stackFrameDisplayExact : StackFrameDisplayExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.ErrorShow.Coverage
