import JuliaLean.Proofs.base.path

namespace JuliaLean.Files.Coverage

open JuliaLean.Files

def PathPrimitiveBehavior : Prop :=
  (∀ char, posixSeparator char = (char == '/')) ∧
  (∀ byte, posixSeparatorByte byte = (byte == 47)) ∧
  (∀ path, posixSplitDrive path = ([], path)) ∧
  (pathSeparator = '/') ∧
  (∀ path, JuliaLean.Paths.isabspath path =
    match path with | [] => false | char :: _ => char == '/') ∧
  (∀ replies, bufferPath replies =
    match replies with
    | [] => .error .io []
    | .noBuffer _ :: rest => bufferPath rest
    | .success value :: _ => .ok value
    | .failure :: _ => .error .io []) ∧
  (∀ isString, assertString isString = if isString then .ok () else .error .argument ()) ∧
  (∀ attempts replies, lookupHome attempts replies =
    match attempts, replies with
    | 0, _ => none
    | _, [] => none
    | n + 1, .rangeError :: rest => lookupHome n rest
    | _, .found home :: _ => some home
    | _, .missing :: _ => none) ∧
  (∀ path resolved code, realpathCall path resolved code =
    if code < 0 then .error .io path else .ok resolved)

theorem pathPrimitiveBehavior : PathPrimitiveBehavior := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro path; cases path <;> rfl
  · intro replies
    cases replies with
    | nil => rfl
    | cons head tail => cases head <;> rfl
  · intros; rfl
  · intro attempts replies
    cases attempts with
    | zero => rfl
    | succ attempts =>
        cases replies with
        | nil => rfl
        | cons head tail => cases head <;> rfl
  · intros; rfl

def PathUserBehavior : Prop :=
  ∀ candidates original, contractCandidates candidates original =
    match candidates with
    | [] => original
    | candidate :: rest =>
        if !candidate.present then original
        else if candidate.currentHome then ['~'] ++ candidate.rest
        else match candidate.username with
          | some username => if candidate.userHome then ['~'] ++ username ++ candidate.rest
            else contractCandidates rest original
          | none => contractCandidates rest original

theorem pathUserBehavior : PathUserBehavior := by
  intro candidates original
  cases candidates <;> rfl

def PathUriBehavior : Prop :=
  (∀ value, hexDigit value = if value < 10 then 48 + value else 55 + value) ∧
  (∀ byte, uriUnit byte =
    if decide (65 ≤ byte ∧ byte ≤ 90) || decide (97 ≤ byte ∧ byte ≤ 122) ||
        decide (48 ≤ byte ∧ byte ≤ 57) || [45, 95, 46, 126, 47].contains byte then [byte]
    else [37, hexDigit (byte / 16), hexDigit (byte % 16)]) ∧
  (∀ bytes, encodeUri bytes = bytes.flatMap uriUnit) ∧
  (∀ host path, unixUriPath host path =
    "file://".toList.map Char.toNat ++ encodeUri host ++ [47] ++ encodeUri path)

theorem pathUriBehavior : PathUriBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-! ### Method-specific `base/path.jl` mirrors -/

def PathCoreMethods : Prop :=
  (∀ char, isseparatorCharMethod char = (char == '/')) ∧
  (∀ byte, isseparatorByteMethod byte = (byte == 47)) ∧
  (∀ path, splitdrivePosixMethod path = ([], path)) ∧
  (∀ path, isabspathPosixMethod path = JuliaLean.Paths.isabspath path) ∧
  (pathsepMethod = '/') ∧
  (∀ isString, assertstringMethod isString =
    if isString then .ok () else .error .argument ())

theorem pathCoreMethods : PathCoreMethods := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩ <;> intros <;> rfl

def PathHomedirMethod : Prop :=
  ∀ replies, homedirMethod replies =
    match replies with
    | [] => .error .io []
    | .noBuffer _ :: rest => homedirMethod rest
    | .success value :: _ => .ok value
    | .failure :: _ => .error .io []

theorem pathHomedirMethod : PathHomedirMethod := by
  intro replies
  cases replies with
  | nil => rfl
  | cons head tail => cases head <;> rfl

def PathRealpathMethod : Prop :=
  ∀ path resolved code, realpathMethod path resolved code =
    let events := [.allocate, .call, .cleanup, .free]
    if code < 0 then (events, .error .io path) else (events, .ok resolved)

theorem pathRealpathMethod : PathRealpathMethod := by unfold PathRealpathMethod; intros; rfl


def PathUserMethods : Prop :=
  (∀ attempts replies, homedirUsernameMethod attempts replies = lookupHome attempts replies) ∧
  (∀ candidates original, contractuserMethod candidates original =
    contractCandidates candidates original) ∧
  (∀ result, contractuserAbstractMethod result = result)

theorem pathUserMethods : PathUserMethods := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def PathUriMethods : Prop :=
  (∀ bytes, encodeUriComponentMethod bytes = bytes.flatMap uriUnit) ∧
  (∀ cwd path wsl distro hostname, uripathPosixMethod cwd path wsl distro hostname =
    let localPath := JuliaLean.Paths.joinSep
      (JuliaLean.Paths.splitAtSeps (JuliaLean.Paths.abspath cwd path) false)
    let host := if wsl then "wsl$/".toList.map Char.toNat ++ distro else hostname
    unixUriPath host (localPath.map Char.toNat)) ∧
  (∀ result, uripathAbstractMethod result = result)

theorem pathUriMethods : PathUriMethods := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def DirnameAbstractMethod : Prop := ∀ path,
  dirnameAbstractMethod path = (JuliaLean.Paths.splitdir path).1
theorem dirnameAbstractMethod_proven : DirnameAbstractMethod := by unfold DirnameAbstractMethod; intros; rfl

def BasenameAbstractMethod : Prop := ∀ path,
  basenameAbstractMethod path = (JuliaLean.Paths.splitdir path).2
theorem basenameAbstractMethod_proven : BasenameAbstractMethod := by unfold BasenameAbstractMethod; intros; rfl

def SplitpathAbstractMethod : Prop := ∀ path,
  splitpathAbstractMethod path = JuliaLean.Paths.splitpath path
theorem splitpathAbstractMethod_proven : SplitpathAbstractMethod := by unfold SplitpathAbstractMethod; intros; rfl

def JoinpathVarargsMethod : Prop := ∀ paths,
  joinpathVarargsMethod paths = JuliaLean.Paths.joinpath paths
theorem joinpathVarargsMethod_proven : JoinpathVarargsMethod := by unfold JoinpathVarargsMethod; intros; rfl

def NormpathVarargsMethod : Prop := ∀ paths,
  normpathVarargsMethod paths = (JuliaLean.Paths.joinpath paths).map JuliaLean.Paths.normpath
theorem normpathVarargsMethod_proven : NormpathVarargsMethod := by unfold NormpathVarargsMethod; intros; rfl

def AbspathVarargsMethod : Prop := ∀ cwd paths,
  abspathVarargsMethod cwd paths = (JuliaLean.Paths.joinpath paths).map (JuliaLean.Paths.abspath cwd)
theorem abspathVarargsMethod_proven : AbspathVarargsMethod := by unfold AbspathVarargsMethod; intros; rfl

def ExpanduserAbstractMethod : Prop := ∀ home path lookup userChar,
  expanduserAbstractMethod home path lookup userChar = JuliaLean.Paths.expanduser home lookup userChar path
theorem expanduserAbstractMethod_proven : ExpanduserAbstractMethod := by unfold ExpanduserAbstractMethod; intros; rfl

def RelpathAbstractMethod : Prop := ∀ cwd path start,
  relpathAbstractMethod cwd path start = JuliaLean.Paths.relpath cwd path start
theorem relpathAbstractMethod_proven : RelpathAbstractMethod := by unfold RelpathAbstractMethod; intros; rfl

end JuliaLean.Files.Coverage
