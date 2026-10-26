import JuliaLean.ErrorShow.Coverage

/-! Method-specific models for `base/stacktraces.jl` at `bbfa0ce4150`. -/

namespace JuliaLean.ErrorShow.StacktracesFaithful

open JuliaLean.ErrorShow.Coverage

structure StackFrameM where
  functionName : String
  file : String
  line : Int
  linfo : Option String := none
  fromC : Bool := false
  inlined : Bool := false
  pointer : Nat := 0
  pc : Int := 0
  debugId : Option Nat := none
  moduleName : Option String := none
  column : Int := 0
  deriving Repr, DecidableEq, BEq, Inhabited

def stackFrameSeven (functionName file : String) (line : Int) (linfo : Option String)
    (fromC inlined : Bool) (pointer : Nat) : StackFrameM :=
  { functionName, file, line, linfo, fromC, inlined, pointer }

def StackFrameSevenExact : Prop := ∀ functionName file line linfo fromC inlined pointer,
  stackFrameSeven functionName file line linfo fromC inlined pointer =
    { functionName, file, line, linfo, fromC, inlined, pointer }
theorem stackFrameSevenExact : StackFrameSevenExact := by unfold StackFrameSevenExact; intros; rfl

def stackFrameThree (functionName file : String) (line : Int) : StackFrameM :=
  { functionName, file, line }
def StackFrameThreeExact : Prop := ∀ functionName file line,
  stackFrameThree functionName file line = { functionName, file, line }
theorem stackFrameThreeExact : StackFrameThreeExact := by unfold StackFrameThreeExact; intros; rfl

def frameEqual (a b : StackFrameM) : Bool :=
  a.line == b.line && a.fromC == b.fromC && a.functionName == b.functionName &&
    a.file == b.file && a.inlined == b.inlined
def FrameEqualExact : Prop := ∀ a b,
  frameEqual a b = (a.line == b.line && a.fromC == b.fromC &&
    a.functionName == b.functionName && a.file == b.file && a.inlined == b.inlined)
theorem frameEqualExact : FrameEqualExact := by unfold FrameEqualExact; intros; rfl

def frameHash (hashPart : String → Nat → Nat) (frame : StackFrameM) (seed : Nat) : Nat :=
  let seed := seed ^^^ 0xf4fbda67fe20ce88
  let seed := hashPart (toString frame.line) seed
  let seed := hashPart frame.file seed
  let seed := hashPart frame.functionName seed
  let seed := hashPart (toString frame.fromC) seed
  hashPart (toString frame.inlined) seed
def FrameHashExact : Prop := ∀ hashPart frame seed,
  frameHash hashPart frame seed =
    let seed := seed ^^^ 0xf4fbda67fe20ce88
    let seed := hashPart (toString frame.line) seed
    let seed := hashPart frame.file seed
    let seed := hashPart frame.functionName seed
    let seed := hashPart (toString frame.fromC) seed
    hashPart (toString frame.inlined) seed
theorem frameHashExact : FrameHashExact := by unfold FrameHashExact; intros; rfl

structure DebugNode where
  frame : StackFrameM
  lineTable : List StackFrameM
  edgeFrames : List StackFrameM
  deriving Repr, DecidableEq

def addLineTableFrames (frames : List StackFrameM) (lineTable edgeFrames : List StackFrameM) :
    List StackFrameM :=
  frames ++ lineTable ++ edgeFrames
def AddLineTableFramesExact : Prop := ∀ frames lineTable edgeFrames,
  addLineTableFrames frames lineTable edgeFrames = frames ++ lineTable ++ edgeFrames
theorem addLineTableFramesExact : AddLineTableFramesExact := by unfold AddLineTableFramesExact; intros; rfl

def addDebugFrames (frames : List StackFrameM) (node : DebugNode) : List StackFrameM :=
  addLineTableFrames (frames ++ [node.frame]) node.lineTable node.edgeFrames
def AddDebugFramesExact : Prop := ∀ frames node,
  addDebugFrames frames node =
    addLineTableFrames (frames ++ [node.frame]) node.lineTable node.edgeFrames
theorem addDebugFramesExact : AddDebugFramesExact := by unfold AddDebugFramesExact; intros; rfl

structure RawLookupFrame where
  frame : StackFrameM
  pc : Int
  deriving Repr, DecidableEq, Inhabited

def lookupPointer (pointer : Nat) (raw : List RawLookupFrame)
    (debugTree : Option (List StackFrameM)) : List StackFrameM :=
  match raw with
  | [] => [{ functionName := "", file := "", line := -1, fromC := true, pointer }]
  | _ =>
      let last := raw.getLast!
      if last.frame.fromC || last.pc ≤ 0 || debugTree.isNone then
        raw.map fun item => { item.frame with pointer, pc := if item.frame.fromC then item.pc else 0 }
      else debugTree.get!.reverse
def LookupPointerExact : Prop := ∀ pointer raw debugTree,
  lookupPointer pointer raw debugTree = match raw with
  | [] => [{ functionName := "", file := "", line := -1, fromC := true, pointer }]
  | _ =>
      let last := raw.getLast!
      if last.frame.fromC || last.pc ≤ 0 || debugTree.isNone then
        raw.map fun item => { item.frame with pointer, pc := if item.frame.fromC then item.pc else 0 }
      else debugTree.get!.reverse
theorem lookupPointerExact : LookupPointerExact := by
  unfold LookupPointerExact
  intro pointer raw debugTree
  cases raw <;> rfl

inductive InterpreterCode where
  | none
  | method (functionName file : String) (line : Int) (edges : List StackFrameM)
  | codeInfo (file : String) (line : Int) (edges : List StackFrameM)
  deriving Repr, DecidableEq

def lookupInterpreter (code : InterpreterCode) (statement : Int) : List StackFrameM :=
  match code with
  | .none => [{ functionName := "top-level scope", file := "", line := 0 }]
  | .method functionName file line edges =>
      ({ functionName, file, line, pc := max (statement + 1) 0 } :: edges).reverse
  | .codeInfo file line edges =>
      ({ functionName := "top-level scope", file, line, pc := max (statement + 1) 0 } :: edges).reverse
def LookupInterpreterExact : Prop := ∀ code statement,
  lookupInterpreter code statement = match code with
  | .none => [{ functionName := "top-level scope", file := "", line := 0 }]
  | .method functionName file line edges =>
      ({ functionName, file, line, pc := max (statement + 1) 0 } :: edges).reverse
  | .codeInfo file line edges =>
      ({ functionName := "top-level scope", file, line, pc := max (statement + 1) 0 } :: edges).reverse
theorem lookupInterpreterExact : LookupInterpreterExact := by
  unfold LookupInterpreterExact
  intro code statement
  cases code <;> rfl

def stacktraceFromLookups (lookups : List (List StackFrameM)) (includeC : Bool) : List StackFrameM :=
  lookups.flatten.filter fun frame => includeC || !frame.fromC
def StacktraceFromLookupsExact : Prop := ∀ lookups includeC,
  stacktraceFromLookups lookups includeC = lookups.flatten.filter fun frame => includeC || !frame.fromC
theorem stacktraceFromLookupsExact : StacktraceFromLookupsExact := by unfold StacktraceFromLookupsExact; intros; rfl

def removeThroughLastName (stack : List StackFrameM) (names : List String) : List StackFrameM :=
  (stack.reverse.takeWhile fun frame => !names.contains frame.functionName).reverse

def stacktraceHere (captured : List StackFrameM) (includeC : Bool) : List StackFrameM :=
  let withoutSelf := removeThroughLastName captured ["stacktrace"]
  if includeC then withoutSelf.dropWhile (·.fromC) else withoutSelf
def StacktraceHereExact : Prop := ∀ captured includeC,
  stacktraceHere captured includeC =
    let withoutSelf := removeThroughLastName captured ["stacktrace"]
    if includeC then withoutSelf.dropWhile (·.fromC) else withoutSelf
theorem stacktraceHereExact : StacktraceHereExact := by unfold StacktraceHereExact; intros; rfl

def removeFramesName (stack : List StackFrameM) (name : String) : List StackFrameM :=
  removeThroughLastName stack [name]
def RemoveFramesNameExact : Prop := ∀ stack name,
  removeFramesName stack name = removeThroughLastName stack [name]
theorem removeFramesNameExact : RemoveFramesNameExact := by unfold RemoveFramesNameExact; intros; rfl

def removeFramesNames (stack : List StackFrameM) (names : List String) : List StackFrameM :=
  removeThroughLastName stack names
def RemoveFramesNamesExact : Prop := ∀ stack names,
  removeFramesNames stack names = removeThroughLastName stack names
theorem removeFramesNamesExact : RemoveFramesNamesExact := by unfold RemoveFramesNamesExact; intros; rfl

def removeFramesModule (stack : List StackFrameM) (moduleName : String) : List StackFrameM :=
  stack.filter fun frame => frame.moduleName != some moduleName
def RemoveFramesModuleExact : Prop := ∀ stack moduleName,
  removeFramesModule stack moduleName = stack.filter fun frame => frame.moduleName != some moduleName
theorem removeFramesModuleExact : RemoveFramesModuleExact := by unfold RemoveFramesModuleExact; intros; rfl

def isTopLevelFrame (frame : StackFrameM) (linfoIsCodeInfo : Bool) : Bool :=
  linfoIsCodeInfo || (frame.linfo.isNone && frame.functionName == "top-level scope")
def IsTopLevelFrameExact : Prop := ∀ frame linfoIsCodeInfo,
  isTopLevelFrame frame linfoIsCodeInfo =
    (linfoIsCodeInfo || (frame.linfo.isNone && frame.functionName == "top-level scope"))
theorem isTopLevelFrameExact : IsTopLevelFrameExact := by unfold IsTopLevelFrameExact; intros; rfl

inductive MethodOrModule where | method (name : String) | moduleName (name : String) | none deriving Repr, DecidableEq

def frameMethodOrModule (owner : Option MethodOrModule) : MethodOrModule := owner.getD .none
def FrameMethodOrModuleExact : Prop := ∀ owner, frameMethodOrModule owner = owner.getD .none
theorem frameMethodOrModuleExact : FrameMethodOrModuleExact := by unfold FrameMethodOrModuleExact; intros; rfl

def frameMethodInstance (linfo : Option String) : Option String := linfo
def FrameMethodInstanceExact : Prop := ∀ linfo, frameMethodInstance linfo = linfo
theorem frameMethodInstanceExact : FrameMethodInstanceExact := by unfold FrameMethodInstanceExact; intros; rfl

def frameLocation (debugLocation : Option (String × Int × Int)) (frame : StackFrameM) : String × Int × Int :=
  debugLocation.getD (frame.file, frame.line, if frame.fromC then frame.pc else 0)
def FrameLocationExact : Prop := ∀ debugLocation frame,
  frameLocation debugLocation frame = debugLocation.getD (frame.file, frame.line, if frame.fromC then frame.pc else 0)
theorem frameLocationExact : FrameLocationExact := by unfold FrameLocationExact; intros; rfl

inductive SpecLinfoCase where
  | noInfoPointer (hexPointer : String)
  | noInfoTopLevel
  | noInfoFunction (demangled : String)
  | codeInfo
  | moduleFrame (demangled : String)
  | moduleMethodInstance (shown : String)
  | customCodeInstance (shown : String)
  | specializedMethod (shown : String)
  | method (shown : String)
  deriving Repr, DecidableEq

def showSpecLinfo : SpecLinfoCase → String
  | .noInfoPointer pointer => "ip:0x" ++ pointer
  | .noInfoTopLevel | .codeInfo => "top-level scope"
  | .noInfoFunction shown | .moduleFrame shown | .moduleMethodInstance shown |
      .customCodeInstance shown | .specializedMethod shown | .method shown => shown
def ShowSpecLinfoExact : Prop := ∀ input,
  showSpecLinfo input = match input with
  | .noInfoPointer pointer => "ip:0x" ++ pointer
  | .noInfoTopLevel | .codeInfo => "top-level scope"
  | .noInfoFunction shown | .moduleFrame shown | .moduleMethodInstance shown |
      .customCodeInstance shown | .specializedMethod shown | .method shown => shown
theorem showSpecLinfoExact : ShowSpecLinfoExact := by unfold ShowSpecLinfoExact; intro input; cases input <;> rfl

def showCustomSpecSig (methodName specializedTypes : String) : String :=
  methodName ++ specializedTypes
def ShowCustomSpecSigExact : Prop := ∀ methodName specializedTypes,
  showCustomSpecSig methodName specializedTypes = methodName ++ specializedTypes
theorem showCustomSpecSigExact : ShowCustomSpecSigExact := by unfold ShowCustomSpecSigExact; intros; rfl

structure KeywordName where
  raw : String
  withoutDots : String
  isVararg : Bool
  deriving Repr, DecidableEq

structure SpecSignatureInput where
  methodName : String
  positionalSignature : String
  positionalNames : List String
  keywordNames : List KeywordName
  keywordTypes : List String
  limit : Bool
  hasDisplaySize : Bool
  deriving Repr, DecidableEq

def showSpecSig (input : SpecSignatureInput) : String :=
  let names := input.positionalNames.map fun name => if name == "#unused#" then "" else name
  if input.keywordNames.isEmpty then
    input.methodName ++ "(" ++ String.intercalate "," names ++ ")::" ++ input.positionalSignature
  else
    let keywords := (input.keywordNames.zip input.keywordTypes).map fun (name, type) =>
      (if name.isVararg then name.withoutDots else name.raw) ++ "::" ++ type
    input.methodName ++ "(" ++ String.intercalate "," names ++ ";" ++
      String.intercalate "," keywords ++ ")::" ++ input.positionalSignature
def ShowSpecSigExact : Prop := ∀ input,
  showSpecSig input =
    let names := input.positionalNames.map fun name => if name == "#unused#" then "" else name
    if input.keywordNames.isEmpty then
      input.methodName ++ "(" ++ String.intercalate "," names ++ ")::" ++ input.positionalSignature
    else
      let keywords := (input.keywordNames.zip input.keywordTypes).map fun (name, type) =>
        (if name.isVararg then name.withoutDots else name.raw) ++ "::" ++ type
      input.methodName ++ "(" ++ String.intercalate "," names ++ ";" ++
        String.intercalate "," keywords ++ ")::" ++ input.positionalSignature
theorem showSpecSigExact : ShowSpecSigExact := by unfold ShowSpecSigExact; intros; rfl

def showFrame (signature : String) (location : Option String) (inlined : Bool) : String :=
  signature ++ (match location with | none => "" | some text => " at " ++ text) ++
    (if inlined then " [inlined]" else "")
def ShowFrameExact : Prop := ∀ signature location inlined,
  showFrame signature location inlined =
    signature ++ (match location with | none => "" | some text => " at " ++ text) ++
      (if inlined then " [inlined]" else "")
theorem showFrameExact : ShowFrameExact := by unfold ShowFrameExact; intros; rfl

inductive ParentModuleCase where
  | codeInstanceMethodInstance (moduleName : String)
  | codeInstanceModule (moduleName : String)
  | method (moduleName : String)
  | moduleValue (moduleName : String)
  | unavailable
  deriving Repr, DecidableEq

def parentModule : ParentModuleCase → Option String
  | .codeInstanceMethodInstance name | .codeInstanceModule name |
      .method name | .moduleValue name => some name
  | .unavailable => none
def ParentModuleExact : Prop := ∀ input,
  parentModule input = match input with
  | .codeInstanceMethodInstance name | .codeInstanceModule name |
      .method name | .moduleValue name => some name
  | .unavailable => none
theorem parentModuleExact : ParentModuleExact := by unfold ParentModuleExact; intro input; cases input <;> rfl

def fromModule (frameModule target : Option String) : Bool := frameModule == target
def FromModuleExact : Prop := ∀ frameModule target, fromModule frameModule target = (frameModule == target)
theorem fromModuleExact : FromModuleExact := by unfold FromModuleExact; intros; rfl

end JuliaLean.ErrorShow.StacktracesFaithful
