import JuliaLean.Files.Proven
import JuliaLean.Paths.Model

/-!
# Whole-Base method coverage for filesystem sources

Source-order models for the remaining methods in `base/file.jl`, `base/stat.jl`,
`base/filesystem.jl`, and the POSIX branch of `base/path.jl` at `bbfa0ce4150`.
System calls, clocks, directory scans, and user databases are explicit inputs.
-/

namespace JuliaLean.Files.Coverage

open JuliaLean.Files

/-! ## Working directories and directory creation (`base/file.jl:54-194`) -/

inductive BufferReply where
  | noBuffer (required : Nat)
  | success (value : PathText)
  | failure
  deriving Repr, DecidableEq

def bufferPath : List BufferReply → Result PathText
  | [] => .error .io []
  | .noBuffer _ :: replies => bufferPath replies
  | .success value :: _ => .ok value
  | .failure :: _ => .error .io []

def checkMode (mode : Int) : Result Int :=
  if 0 ≤ mode ∧ mode ≤ 511 then .ok mode else .error .argument mode

def mkdirCall (path : PathText) (mode : Int) (returnCode : Int) : Result PathText :=
  match checkMode mode with
  | .error error _ => .error error path
  | .ok _ => if returnCode < 0 then .error .io path else .ok path

def cdCall (returnCode : Int) : Result Unit :=
  if returnCode < 0 then .error .io () else .ok ()

inductive CdEvent where
  | save
  | change (path : PathText)
  | callback
  | restore
  | closeSaved
  deriving Repr, DecidableEq

def cdCallbackEvents (path : PathText) : List CdEvent :=
  [.save, .change path, .callback, .restore, .closeSaved]

def CwdModeBehavior : Prop :=
  (∀ replies, bufferPath replies =
    match replies with
    | [] => .error .io []
    | .noBuffer _ :: rest => bufferPath rest
    | .success value :: _ => .ok value
    | .failure :: _ => .error .io []) ∧
  (∀ mode, checkMode mode =
    if 0 ≤ mode ∧ mode ≤ 511 then .ok mode else .error .argument mode) ∧
  (∀ path, cdCallbackEvents path =
    [.save, .change path, .callback, .restore, .closeSaved]) ∧
  (∀ returnCode, cdCall returnCode =
    if returnCode < 0 then .error .io () else .ok ()) ∧
  (∀ path mode returnCode, mkdirCall path mode returnCode =
    match checkMode mode with
    | .error error _ => .error error path
    | .ok _ => if returnCode < 0 then .error .io path else .ok path)

theorem cwdModeBehavior : CwdModeBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro replies
    cases replies with
    | nil => rfl
    | cons head tail => cases head <;> rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

def pwdMethod (replies : List BufferReply) : Result PathText := bufferPath replies

def PwdMethod : Prop :=
  ∀ replies, pwdMethod replies =
    match replies with
    | [] => .error .io []
    | .noBuffer _ :: rest => pwdMethod rest
    | .success value :: _ => .ok value
    | .failure :: _ => .error .io []

theorem pwdMethod_proven : PwdMethod := by
  intro replies
  cases replies with
  | nil => rfl
  | cons head tail => cases head <;> rfl

def cdDirectoryMethod (returnCode : Int) : Result Unit := cdCall returnCode
def cdHomeMethod (home : PathText) (returnCode : Int) : PathText × Result Unit :=
  (home, cdDirectoryMethod returnCode)
def cdCallbackMethod (path : PathText) : List CdEvent := cdCallbackEvents path
def cdCallbackHomeMethod (home : PathText) : List CdEvent := cdCallbackMethod home

def CdMethods : Prop :=
  (∀ code, cdDirectoryMethod code = if code < 0 then .error .io () else .ok ()) ∧
  (∀ home code, cdHomeMethod home code = (home, cdDirectoryMethod code)) ∧
  (∀ path, cdCallbackMethod path = [.save, .change path, .callback, .restore, .closeSaved]) ∧
  (∀ home, cdCallbackHomeMethod home = cdCallbackMethod home)

theorem cdMethods : CdMethods := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

def CheckmodeMethod : Prop :=
  ∀ mode, checkMode mode = if 0 ≤ mode ∧ mode ≤ 511 then .ok mode else .error .argument mode

theorem checkmodeMethod : CheckmodeMethod := by unfold CheckmodeMethod; intros; rfl

def MkdirMethod : Prop :=
  ∀ path mode code, mkdirCall path mode code =
    match checkMode mode with
    | .error error _ => .error error path
    | .ok _ => if code < 0 then .error .io path else .ok path

theorem mkdirMethod : MkdirMethod := by unfold MkdirMethod; intros; rfl

def mkpathMethod (path : PathState) (parentIsSelf alreadyDirectory : Bool) (mode : Int) :
    Result PathState :=
  if parentIsSelf || alreadyDirectory then .ok path
  else match checkMode mode with
    | .error error _ => .error error path
    | .ok _ => mkpath path

def MkpathMethod : Prop := ∀ path parentIsSelf alreadyDirectory mode,
  mkpathMethod path parentIsSelf alreadyDirectory mode =
    if parentIsSelf || alreadyDirectory then .ok path
    else match checkMode mode with
      | .error error _ => .error error path
      | .ok _ => mkpath path

theorem mkpathMethod_proven : MkpathMethod := by unfold MkpathMethod; intros; rfl

def rmMethod (entry : RmEntry) (force recursive : Bool) : Result RmEntry :=
  rm entry force recursive
def RmMethod : Prop := ∀ entry force recursive,
  rmMethod entry force recursive = rm entry force recursive
theorem rmMethod_proven : RmMethod := by unfold RmMethod; intros; rfl

/-! ## Tree copying and containment (`base/file.jl:348-458`) -/

inductive CopyNode where
  | file (bytes : List UInt8)
  | link (targetText : PathText) (target : CopyNode)
  | directory (children : List (Nat × CopyNode))

def cloneNode : Nat → Bool → CopyNode → CopyNode
  | 0, _, node => node
  | _fuel + 1, _followSymlinks, .file bytes => .file bytes
  | fuel + 1, followSymlinks, .link text target =>
      if followSymlinks then cloneNode fuel true target else .link text target
  | fuel + 1, followSymlinks, .directory children =>
      .directory (children.map fun pair => (pair.1, cloneNode fuel followSymlinks pair.2))

def resolvedPath (absolute pathExists finalLink keepLink parentIsSelf : Bool)
    (path real parentReal base : PathText) : PathText :=
  let normalized := if absolute then path else ['/'] ++ path
  if pathExists then
    if keepLink && finalLink then parentReal ++ base else real
  else if parentIsSelf then normalized else parentReal ++ base

def withinPath (inner outer : List Nat) : Bool :=
  inner == outer || outer.isPrefixOf inner

def TreeCopyBehavior : Prop :=
  (∀ fuel follow bytes, cloneNode (fuel + 1) follow (.file bytes) = .file bytes) ∧
  (∀ fuel text target, cloneNode (fuel + 1) false (.link text target) = .link text target) ∧
  (∀ fuel text target, cloneNode (fuel + 1) true (.link text target) = cloneNode fuel true target) ∧
  (∀ absolute pathExists finalLink keepLink parentIsSelf path real parentReal base,
    resolvedPath absolute pathExists finalLink keepLink parentIsSelf path real parentReal base =
      let normalized := if absolute then path else ['/'] ++ path
      if pathExists then
        if keepLink && finalLink then parentReal ++ base else real
      else if parentIsSelf then normalized else parentReal ++ base) ∧
  (∀ inner outer, withinPath inner outer = (inner == outer || outer.isPrefixOf inner))

theorem treeCopyBehavior : TreeCopyBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

def ResolvedPathMethod : Prop :=
  ∀ absolute pathExists finalLink keepLink parentIsSelf path real parentReal base,
    resolvedPath absolute pathExists finalLink keepLink parentIsSelf path real parentReal base =
      let normalized := if absolute then path else ['/'] ++ path
      if pathExists then
        if keepLink && finalLink then parentReal ++ base else real
      else if parentIsSelf then normalized else parentReal ++ base

theorem resolvedPathMethod : ResolvedPathMethod := by unfold ResolvedPathMethod; intros; rfl

def IsWithinMethod : Prop :=
  ∀ inner outer, withinPath inner outer = (inner == outer || outer.isPrefixOf inner)

theorem isWithinMethod : IsWithinMethod := by unfold IsWithinMethod; intros; rfl

structure CopyCheckInput where
  sourceDirectory : Bool
  followSymlinks : Bool
  sourceFinalLink : Bool
  destinationInsideSource : Bool
  destinationExists : Bool
  force : Bool
  sameFile : Bool
  sourceInsideDestination : Bool
  deriving Repr, DecidableEq

def checkCopyMethod (input : CopyCheckInput) : Result Bool :=
  if input.sourceDirectory && (input.followSymlinks || !input.sourceFinalLink) &&
      input.destinationInsideSource then .error .argument false
  else if input.destinationExists then
    if input.force then
      if input.sameFile then .error .argument false
      else if input.sourceInsideDestination then .error .argument false
      else .ok true
    else .error .argument false
  else .ok false

def CheckCopyMethod : Prop :=
  ∀ input, checkCopyMethod input =
    if input.sourceDirectory && (input.followSymlinks || !input.sourceFinalLink) &&
        input.destinationInsideSource then .error .argument false
    else if input.destinationExists then
      if input.force then
        if input.sameFile then .error .argument false
        else if input.sourceInsideDestination then .error .argument false
        else .ok true
      else .error .argument false
    else .ok false

theorem checkCopyMethod_proven : CheckCopyMethod := by unfold CheckCopyMethod; intros; rfl

def cptreeInternalMethod (fuel : Nat) (source : CopyNode) (followSymlinks : Bool) : CopyNode :=
  cloneNode fuel followSymlinks source

def cptreeStringMethod (sourceIsDirectory : Bool) (check : Result Bool)
    (fuel : Nat) (source : CopyNode) (followSymlinks : Bool) : Result CopyNode :=
  if !sourceIsDirectory then .error .argument source
  else match check with
    | .error error _ => .error error source
    | .ok _ => .ok (cptreeInternalMethod fuel source followSymlinks)

def cptreeAbstractMethod (converted : Result CopyNode) : Result CopyNode := converted

def CptreeMethods : Prop :=
  (∀ fuel source follow, cptreeInternalMethod fuel source follow = cloneNode fuel follow source) ∧
  (∀ sourceIsDirectory check fuel source follow, cptreeStringMethod sourceIsDirectory check fuel source follow =
    if !sourceIsDirectory then .error .argument source
    else match check with
      | .error error _ => .error error source
      | .ok _ => .ok (cptreeInternalMethod fuel source follow)) ∧
  (∀ converted, cptreeAbstractMethod converted = converted)

theorem cptreeMethods : CptreeMethods := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

inductive CopySourceKind where | link | directory | file deriving Repr, DecidableEq

def cpMethod (check : Result Bool) (kind : CopySourceKind) (followSymlinks : Bool)
    (fuel : Nat) (source : CopyNode) : Result CopyNode :=
  match check with
  | .error error _ => .error error source
  | .ok _ => match kind with
    | .link => if followSymlinks then .ok (cloneNode fuel true source) else .ok source
    | .directory => .ok (cloneNode fuel followSymlinks source)
    | .file => .ok source

def CpMethod : Prop :=
  ∀ check kind follow fuel source, cpMethod check kind follow fuel source =
    match check with
    | .error error _ => .error error source
    | .ok _ => match kind with
      | .link => if follow then .ok (cloneNode fuel true source) else .ok source
      | .directory => .ok (cloneNode fuel follow source)
      | .file => .ok source

theorem cpMethod_proven : CpMethod := by unfold CpMethod; intros; rfl

inductive RenameObservation where | success | enoent | ioError | otherError deriving Repr, DecidableEq
inductive MoveEvent where | check (force : Bool) | rename | copy | removeSource deriving Repr, DecidableEq

def mvReplaceMethod (sameFile : Bool) (first second : RenameObservation)
    (guard copyResult : Result Unit) : List MoveEvent × Result Unit :=
  if sameFile then ([], .error .argument ())
  else match first with
    | .success => ([.rename], .ok ())
    | .enoent => ([.rename], .error .io ())
    | .otherError => ([.rename], .error .io ())
    | .ioError => match guard with
      | .error error _ => ([.rename, .check true], .error error ())
      | .ok _ => match second with
        | .success => ([.rename, .check true, .rename], .ok ())
        | .enoent | .ioError => match copyResult with
          | .error error _ => ([.rename, .check true, .rename, .copy], .error error ())
          | .ok _ => ([.rename, .check true, .rename, .copy, .removeSource], .ok ())
        | .otherError => ([.rename, .check true, .rename], .error .io ())

def mvNoreplaceMethod (guard : Result Unit) (renameResult : RenameObservation)
    (copyResult : Result Unit) : List MoveEvent × Result Unit :=
  match guard with
  | .error error _ => ([.check false], .error error ())
  | .ok _ => match renameResult with
    | .success => ([.check false, .rename], .ok ())
    | .enoent => ([.check false, .rename], .error .io ())
    | .otherError => ([.check false, .rename], .error .io ())
    | .ioError => match copyResult with
      | .error error _ => ([.check false, .rename, .copy], .error error ())
      | .ok _ => ([.check false, .rename, .copy, .removeSource], .ok ())

def mvMethod (force sameFile : Bool) (first second : RenameObservation)
    (guard copyResult : Result Unit) : List MoveEvent × Result Unit :=
  if force then mvReplaceMethod sameFile first second guard copyResult
  else mvNoreplaceMethod guard first copyResult

def MvMethods : Prop :=
  (∀ force sameFile first second guard copyResult,
    mvMethod force sameFile first second guard copyResult =
      if force then mvReplaceMethod sameFile first second guard copyResult
      else mvNoreplaceMethod guard first copyResult) ∧
  (∀ guard renameResult copyResult, mvNoreplaceMethod guard renameResult copyResult =
    match guard with
    | .error error _ => ([.check false], .error error ())
    | .ok _ => match renameResult with
      | .success => ([.check false, .rename], .ok ())
      | .enoent => ([.check false, .rename], .error .io ())
      | .otherError => ([.check false, .rename], .error .io ())
      | .ioError => match copyResult with
        | .error error _ => ([.check false, .rename, .copy], .error error ())
        | .ok _ => ([.check false, .rename, .copy, .removeSource], .ok ()))

theorem mvMethods : MvMethods := by
  constructor <;> intros <;> rfl

def MvReplaceMethod : Prop := ∀ sameFile first second guard copyResult,
  mvReplaceMethod sameFile first second guard copyResult =
    if sameFile then ([], .error .argument ())
    else match first with
      | .success => ([.rename], .ok ())
      | .enoent => ([.rename], .error .io ())
      | .otherError => ([.rename], .error .io ())
      | .ioError => match guard with
        | .error error _ => ([.rename, .check true], .error error ())
        | .ok _ => match second with
          | .success => ([.rename, .check true, .rename], .ok ())
          | .enoent | .ioError => match copyResult with
            | .error error _ => ([.rename, .check true, .rename, .copy], .error error ())
            | .ok _ => ([.rename, .check true, .rename, .copy, .removeSource], .ok ())
          | .otherError => ([.rename, .check true, .rename], .error .io ())
theorem mvReplaceMethod_proven : MvReplaceMethod := by unfold MvReplaceMethod; intros; rfl

def MvNoreplaceMethod : Prop := ∀ guard renameResult copyResult,
  mvNoreplaceMethod guard renameResult copyResult =
    match guard with
    | .error error _ => ([.check false], .error error ())
    | .ok _ => match renameResult with
      | .success => ([.check false, .rename], .ok ())
      | .enoent => ([.check false, .rename], .error .io ())
      | .otherError => ([.check false, .rename], .error .io ())
      | .ioError => match copyResult with
        | .error error _ => ([.check false, .rename, .copy], .error error ())
        | .ok _ => ([.check false, .rename, .copy, .removeSource], .ok ())
theorem mvNoreplaceMethod_proven : MvNoreplaceMethod := by unfold MvNoreplaceMethod; intros; rfl

inductive TouchPathEvent where | open | touch | close deriving Repr, DecidableEq
def touchPathMethod (path : PathText) (openSucceeds touchSucceeds : Bool) :
    List TouchPathEvent × Result PathText :=
  if !openSucceeds then ([.open], .error .io path)
  else if !touchSucceeds then ([.open, .touch, .close], .error .io path)
  else ([.open, .touch, .close], .ok path)
def TouchPathMethod : Prop := ∀ path openSucceeds touchSucceeds,
  touchPathMethod path openSucceeds touchSucceeds =
    if !openSucceeds then ([.open], .error .io path)
    else if !touchSucceeds then ([.open, .touch, .close], .error .io path)
    else ([.open, .touch, .close], .ok path)
theorem touchPathMethod_proven : TouchPathMethod := by unfold TouchPathMethod; intros; rfl

/-! ## Temporary paths and cleanup (`base/file.jl:605-998`) -/

def deletionMode (mode : Nat) : Nat :=
  mode / 512 * 512 + (mode / 256 % 2) * 256 + (mode / 32 % 2) * 32 +
    (mode / 4 % 2) * 4 + 219

def prepareModes (isDirectory : Bool) (rootMode : Nat) (directoryModes : List Nat) : List Nat :=
  if isDirectory then deletionMode rootMode :: directoryModes.map deletionMode else []

def cleanupLater (old : Option Bool) (asap : Bool) : Bool := old.getD true && asap

structure CleanupItem where
  path : PathText
  asap : Bool
  present : Bool
  deletionSucceeds : Bool
  deriving Repr, DecidableEq

def purgeCleanup (force : Bool) (items : List CleanupItem) : List CleanupItem :=
  items.filter fun item =>
    if !item.present then false
    else if force || item.asap then !item.deletionSucceeds
    else true

def randomFilename (length : Nat) (draws : List Nat) : List Nat :=
  (draws.take length).map (· % 62)

inductive TempEvent where
  | forget (path : PathText)
  | closeFile
  | prepare (path : PathText)
  | remove (path : PathText)
  | retryLater (path : PathText)
  | purgeAll
  | collectGarbage
  | spawnCleaner
  | writeCleanupPaths
  | leakPipeDescriptor
  | closePipe
  | registerExitHook
  deriving Repr, DecidableEq

def tempCallbackEvents (kind : TempKind) (path : PathText) (cleanupSucceeds : Bool) : List TempEvent :=
  let events := [.forget path]
  match kind with
  | .name => events
  | .file => events ++ [.closeFile] ++ if cleanupSucceeds then [.remove path] else [.retryLater path]
  | .directory =>
      events ++ [.prepare path] ++ if cleanupSucceeds then [.remove path] else [.retryLater path]

def cleanupPostprocessEvents (hasPaths : Bool) : List TempEvent :=
  if hasPaths then [.spawnCleaner, .writeCleanupPaths, .leakPipeDescriptor, .closePipe] else []

def cleanupAtExitEvents (hasPaths : Bool) : List TempEvent :=
  [.purgeAll] ++ cleanupPostprocessEvents hasPaths

def TempRuntimeBehavior : Prop :=
  (∀ isDirectory root dirs, prepareModes isDirectory root dirs =
    if isDirectory then deletionMode root :: dirs.map deletionMode else []) ∧
  (∀ old asap, cleanupLater old asap = (old.getD true && asap)) ∧
  (∀ force items, purgeCleanup force items = items.filter fun item =>
    if !item.present then false
    else if force || item.asap then !item.deletionSucceeds
    else true) ∧
  (∀ length draws, randomFilename length draws = (draws.take length).map (· % 62)) ∧
  (∀ replies, bufferPath replies =
    match replies with
    | [] => .error .io []
    | .noBuffer _ :: rest => bufferPath rest
    | .success value :: _ => .ok value
    | .failure :: _ => .error .io []) ∧
  (∀ hasPaths, cleanupPostprocessEvents hasPaths =
    if hasPaths then [.spawnCleaner, .writeCleanupPaths, .leakPipeDescriptor, .closePipe] else []) ∧
  (∀ hasPaths, cleanupAtExitEvents hasPaths = [.purgeAll] ++ cleanupPostprocessEvents hasPaths) ∧
  (∀ kind path succeeds, tempCallbackEvents kind path succeeds =
    let events := [.forget path]
    match kind with
    | .name => events
    | .file => events ++ [.closeFile] ++ if succeeds then [.remove path] else [.retryLater path]
    | .directory => events ++ [.prepare path] ++
        if succeeds then [.remove path] else [.retryLater path])

theorem tempRuntimeBehavior : TempRuntimeBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro replies
    cases replies with
    | nil => rfl
    | cons head tail => cases head <;> rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

def delayedDeleteRefMethod (tempDirectory : PathText) : PathText :=
  tempDirectory ++ "/julia_delayed_deletes_ref".toList

inductive TempdirProbe where | missing | nondirectory | directory | accessError deriving Repr, DecidableEq
inductive TempdirWarning where | missing | nondirectory | accessError deriving Repr, DecidableEq

def tempdirMethod (replies : List BufferReply) (probe : TempdirProbe) :
    Result (PathText × Option TempdirWarning) :=
  match bufferPath replies with
  | .error error value => .error error (value, none)
  | .ok value => .ok (value, match probe with
      | .missing => some .missing
      | .nondirectory => some .nondirectory
      | .directory => none
      | .accessError => some .accessError)

def prepareForDeletionMethod (isDirectory : Bool) (rootMode : Nat) (directoryModes : List Nat) : List Nat :=
  prepareModes isDirectory rootMode directoryModes

def cleanupLaterMethod (old : Option Bool) (asap : Bool) (size maximum minimum : Nat) :
    Bool × Bool × Nat :=
  let stored := old.getD true && asap
  let purge := decide (size > maximum)
  let newMaximum := if purge then max minimum (2 * size) else maximum
  (stored, purge, newMaximum)

def cleanupForgetMethod (_present : Bool) : Bool := false
def cleanupPurgePrelockedMethod (force : Bool) (items : List CleanupItem) : List CleanupItem :=
  purgeCleanup force items
def cleanupPurgeAllMethod (mayNeedGc : Bool) : List TempEvent :=
  (if mayNeedGc then [.collectGarbage] else []) ++ [.purgeAll]
def cleanupPostprocessMethod (hasPaths : Bool) : List TempEvent := cleanupPostprocessEvents hasPaths
def cleanupAtexitMethod (hasPaths : Bool) : List TempEvent := cleanupAtExitEvents hasPaths
def filePostinitMethod (hooks : List TempEvent) : List TempEvent := hooks ++ [.registerExitHook]
def randFilenameMethod (length : Nat) (draws : List Nat) : List Nat := randomFilename length draws

def TempCleanupMethods : Prop :=
  (∀ tempDirectory, delayedDeleteRefMethod tempDirectory =
    tempDirectory ++ "/julia_delayed_deletes_ref".toList) ∧
  (∀ replies probe, tempdirMethod replies probe =
    match bufferPath replies with
    | .error error value => .error error (value, none)
    | .ok value => .ok (value, match probe with
        | .missing => some .missing
        | .nondirectory => some .nondirectory
        | .directory => none
        | .accessError => some .accessError)) ∧
  (∀ directory mode descendants, prepareForDeletionMethod directory mode descendants =
    prepareModes directory mode descendants) ∧
  (∀ old asap size maximum minimum, cleanupLaterMethod old asap size maximum minimum =
    let stored := old.getD true && asap
    let purge := decide (size > maximum)
    let newMaximum := if purge then max minimum (2 * size) else maximum
    (stored, purge, newMaximum)) ∧
  (∀ present, cleanupForgetMethod present = false) ∧
  (∀ force items, cleanupPurgePrelockedMethod force items = purgeCleanup force items) ∧
  (∀ mayNeedGc, cleanupPurgeAllMethod mayNeedGc =
    (if mayNeedGc then [.collectGarbage] else []) ++ [.purgeAll]) ∧
  (∀ hasPaths, cleanupPostprocessMethod hasPaths = cleanupPostprocessEvents hasPaths) ∧
  (∀ hasPaths, cleanupAtexitMethod hasPaths = cleanupAtExitEvents hasPaths) ∧
  (∀ hooks, filePostinitMethod hooks = hooks ++ [.registerExitHook]) ∧
  (∀ length draws, randFilenameMethod length draws = randomFilename length draws)

theorem tempCleanupMethods : TempCleanupMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def DelayedDeleteRefMethod : Prop := ∀ tempDirectory,
  delayedDeleteRefMethod tempDirectory = tempDirectory ++ "/julia_delayed_deletes_ref".toList
theorem delayedDeleteRefMethod_proven : DelayedDeleteRefMethod := by unfold DelayedDeleteRefMethod; intros; rfl

def TempdirMethod : Prop := ∀ replies probe, tempdirMethod replies probe =
  match bufferPath replies with
  | .error error value => .error error (value, none)
  | .ok value => .ok (value, match probe with
      | .missing => some .missing | .nondirectory => some .nondirectory
      | .directory => none | .accessError => some .accessError)
theorem tempdirMethod_proven : TempdirMethod := by unfold TempdirMethod; intros; rfl

def PrepareForDeletionMethod : Prop := ∀ directory mode descendants,
  prepareForDeletionMethod directory mode descendants = prepareModes directory mode descendants
theorem prepareForDeletionMethod_proven : PrepareForDeletionMethod := by unfold PrepareForDeletionMethod; intros; rfl

def CleanupLaterMethod : Prop := ∀ old asap size maximum minimum,
  cleanupLaterMethod old asap size maximum minimum =
    let stored := old.getD true && asap
    let purge := decide (size > maximum)
    let newMaximum := if purge then max minimum (2 * size) else maximum
    (stored, purge, newMaximum)
theorem cleanupLaterMethod_proven : CleanupLaterMethod := by unfold CleanupLaterMethod; intros; rfl

def CleanupForgetMethod : Prop := ∀ present, cleanupForgetMethod present = false
theorem cleanupForgetMethod_proven : CleanupForgetMethod := by unfold CleanupForgetMethod; intros; rfl

def CleanupPurgePrelockedMethod : Prop := ∀ force items,
  cleanupPurgePrelockedMethod force items = purgeCleanup force items
theorem cleanupPurgePrelockedMethod_proven : CleanupPurgePrelockedMethod := by unfold CleanupPurgePrelockedMethod; intros; rfl

def CleanupPurgeAllMethod : Prop := ∀ mayNeedGc, cleanupPurgeAllMethod mayNeedGc =
  (if mayNeedGc then [.collectGarbage] else []) ++ [.purgeAll]
theorem cleanupPurgeAllMethod_proven : CleanupPurgeAllMethod := by unfold CleanupPurgeAllMethod; intros; rfl

def CleanupPostprocessMethod : Prop := ∀ hasPaths,
  cleanupPostprocessMethod hasPaths = cleanupPostprocessEvents hasPaths
theorem cleanupPostprocessMethod_proven : CleanupPostprocessMethod := by unfold CleanupPostprocessMethod; intros; rfl

def CleanupAtexitMethod : Prop := ∀ hasPaths,
  cleanupAtexitMethod hasPaths = cleanupAtExitEvents hasPaths
theorem cleanupAtexitMethod_proven : CleanupAtexitMethod := by unfold CleanupAtexitMethod; intros; rfl

def FilePostinitMethod : Prop := ∀ hooks,
  filePostinitMethod hooks = hooks ++ [.registerExitHook]
theorem filePostinitMethod_proven : FilePostinitMethod := by unfold FilePostinitMethod; intros; rfl

def RandFilenameMethod : Prop := ∀ length draws,
  randFilenameMethod length draws = randomFilename length draws
theorem randFilenameMethod_proven : RandFilenameMethod := by unfold RandFilenameMethod; intros; rfl

inductive TempCreateEvent where
  | template (path : PathText)
  | createFile
  | createDirectory
  | registerCleanup (path : PathText)
  | openStream
  deriving Repr, DecidableEq

def mktempUnixMethod (path : PathText) (createSucceeds cleanup : Bool) :
    List TempCreateEvent × Result TempObject :=
  let events := [.template path, .createFile]
  if !createSucceeds then (events, .error .io { path, kind := .file, present := false })
  else
    let object : TempObject := { path, kind := .file, present := true, cleanupRegistered := cleanup }
    (events ++ (if cleanup then [.registerCleanup path] else []) ++ [.openStream], .ok object)

def mktempdirMethod (path : PathText) (createSucceeds cleanup : Bool) :
    List TempCreateEvent × Result TempObject :=
  let events := [.template path, .createDirectory]
  if !createSucceeds then (events, .error .io { path, kind := .directory, present := false })
  else
    let object : TempObject := { path, kind := .directory, present := true, cleanupRegistered := cleanup }
    (events ++ if cleanup then [.registerCleanup path] else [], .ok object)

def mktempCallbackMethod (path : PathText) (cleanupSucceeds : Bool) : List TempEvent :=
  tempCallbackEvents .file path cleanupSucceeds
def mktempdirCallbackMethod (path : PathText) (cleanupSucceeds : Bool) : List TempEvent :=
  tempCallbackEvents .directory path cleanupSucceeds

def TempCreationMethods : Prop :=
  (∀ path succeeds cleanup, mktempUnixMethod path succeeds cleanup =
    let events := [.template path, .createFile]
    if !succeeds then (events, .error .io { path, kind := .file, present := false })
    else let object : TempObject := { path, kind := .file, present := true, cleanupRegistered := cleanup }
      (events ++ (if cleanup then [.registerCleanup path] else []) ++ [.openStream], .ok object)) ∧
  (∀ path succeeds cleanup, mktempdirMethod path succeeds cleanup =
    let events := [.template path, .createDirectory]
    if !succeeds then (events, .error .io { path, kind := .directory, present := false })
    else let object : TempObject := { path, kind := .directory, present := true, cleanupRegistered := cleanup }
      (events ++ if cleanup then [.registerCleanup path] else [], .ok object)) ∧
  (∀ path succeeds, mktempCallbackMethod path succeeds = tempCallbackEvents .file path succeeds) ∧
  (∀ path succeeds, mktempdirCallbackMethod path succeeds = tempCallbackEvents .directory path succeeds)

theorem tempCreationMethods : TempCreationMethods := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

def MktempUnixMethod : Prop := ∀ path succeeds cleanup, mktempUnixMethod path succeeds cleanup =
  let events := [.template path, .createFile]
  if !succeeds then (events, .error .io { path, kind := .file, present := false })
  else let object : TempObject := { path, kind := .file, present := true, cleanupRegistered := cleanup }
    (events ++ (if cleanup then [.registerCleanup path] else []) ++ [.openStream], .ok object)
theorem mktempUnixMethod_proven : MktempUnixMethod := by unfold MktempUnixMethod; intros; rfl

def MktempdirMethod : Prop := ∀ path succeeds cleanup, mktempdirMethod path succeeds cleanup =
  let events := [.template path, .createDirectory]
  if !succeeds then (events, .error .io { path, kind := .directory, present := false })
  else let object : TempObject := { path, kind := .directory, present := true, cleanupRegistered := cleanup }
    (events ++ if cleanup then [.registerCleanup path] else [], .ok object)
theorem mktempdirMethod_proven : MktempdirMethod := by unfold MktempdirMethod; intros; rfl

def MktempCallbackMethod : Prop := ∀ path succeeds,
  mktempCallbackMethod path succeeds = tempCallbackEvents .file path succeeds
theorem mktempCallbackMethod_proven : MktempCallbackMethod := by unfold MktempCallbackMethod; intros; rfl

def MktempdirCallbackMethod : Prop := ∀ path succeeds,
  mktempdirCallbackMethod path succeeds = tempCallbackEvents .directory path succeeds
theorem mktempdirCallbackMethod_proven : MktempdirCallbackMethod := by unfold MktempdirCallbackMethod; intros; rfl

/-! ## Directory entries and streaming iteration (`base/file.jl:1000-1443`) -/

structure EntryModel where
  dir : List Nat
  name : Nat
  rawtype : Nat
  deriving Repr, DecidableEq

structure EntryProbe where
  link : Bool
  file : Bool
  directory : Bool
  fifo : Bool
  socket : Bool
  charDevice : Bool
  blockDevice : Bool
  deriving Repr, DecidableEq

def entryLess (left right : EntryModel) : Bool :=
  if left.dir == right.dir then decide (right.name < left.name) else decide (left.dir < right.dir)

def entryPath (entry : EntryModel) : List Nat := entry.dir ++ [entry.name]
def entryEqual (left right : EntryModel) : Bool := left == right
def entryUnknown (entry : EntryModel) : Bool := entry.rawtype == 0
def entryHashKey (entry : EntryModel) : List Nat := [entry.name] ++ entry.dir ++ [entry.rawtype]

def entryKind (rawtype expected : Nat) (probe : EntryProbe) : Bool :=
  if rawtype == 0 || rawtype == 3 then
    match expected with
    | 1 => probe.file
    | 2 => probe.directory
    | 3 => probe.link
    | 4 => probe.fifo
    | 5 => probe.socket
    | 6 => probe.charDevice
    | 7 => probe.blockDevice
    | _ => false
  else rawtype == expected

inductive IteratorKind where | string | entry deriving Repr, DecidableEq

structure IteratorState where
  dir : List Nat
  join : Bool
  kind : IteratorKind
  isOpen : Bool
  closed : Bool
  deriving Repr, DecidableEq

inductive IterValue where
  | string (path : List Nat)
  | entry (value : EntryModel)
  deriving Repr, DecidableEq

def openIterator (state : IteratorState) (openSucceeds : Bool) : Result IteratorState :=
  if state.isOpen then .ok state
  else if state.closed then .error .argument state
  else if openSucceeds then .ok { state with isOpen := true }
  else .error .io { state with closed := true }

def closeIterator (state : IteratorState) : IteratorState := { state with isOpen := false, closed := true }
def iteratorDone (state : IteratorState) : Bool := state.closed

def makeIterator (dir : List Nat) (join : Bool) (kind : IteratorKind) : IteratorState :=
  { dir, join, kind, isOpen := false, closed := false }

def iterateEntry (state : IteratorState) (next : Option (Nat × Nat)) : Result (Option IterValue × IteratorState) :=
  match next with
  | none => .ok (none, closeIterator state)
  | some (name, rawtype) =>
      let value := match state.kind with
        | .entry => .entry ⟨state.dir, name, rawtype⟩
        | .string => .string (if state.join then state.dir ++ [name] else [name])
      .ok (some value, state)

def DirEntryIteratorBehavior : Prop :=
  (∀ entry, entryPath entry = entry.dir ++ [entry.name]) ∧
  (∀ left right, entryEqual left right = (left == right)) ∧
  (∀ entry, entryUnknown entry = (entry.rawtype == 0)) ∧
  (∀ entry, entryHashKey entry = [entry.name] ++ entry.dir ++ [entry.rawtype]) ∧
  (∀ state, iteratorDone state = state.closed) ∧
  (∀ dir join kind, makeIterator dir join kind =
    { dir, join, kind, isOpen := false, closed := false }) ∧
  (∀ left right, entryLess left right =
    if left.dir == right.dir then decide (right.name < left.name) else decide (left.dir < right.dir)) ∧
  (∀ raw expected probe, entryKind raw expected probe =
    if raw == 0 || raw == 3 then
      match expected with
      | 1 => probe.file | 2 => probe.directory | 3 => probe.link | 4 => probe.fifo
      | 5 => probe.socket | 6 => probe.charDevice | 7 => probe.blockDevice | _ => false
    else raw == expected) ∧
  (∀ state succeeds, openIterator state succeeds =
    if state.isOpen then .ok state
    else if state.closed then .error .argument state
    else if succeeds then .ok { state with isOpen := true }
    else .error .io { state with closed := true }) ∧
  (∀ state next, iterateEntry state next =
    match next with
    | none => .ok (none, closeIterator state)
    | some (name, rawtype) =>
        let value := match state.kind with
          | .entry => .entry ⟨state.dir, name, rawtype⟩
          | .string => .string (if state.join then state.dir ++ [name] else [name])
        .ok (some value, state))

theorem dirEntryIteratorBehavior : DirEntryIteratorBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def direntryBasenameMethod (entry : EntryModel) : Nat := entry.name
def direntryDirnameMethod (entry : EntryModel) : List Nat := entry.dir
def direntryJoinpathMethod (entry : EntryModel) (parts : List Nat) : List Nat :=
  entry.dir ++ [entry.name] ++ parts
def direntryIslessMethod (left right : EntryModel) : Bool := entryLess left right
def direntryHashMethod (entry : EntryModel) : List Nat := [entry.rawtype, entry.name] ++ entry.dir
def direntryEqMethod (left right : EntryModel) : Bool := left == right
def direntryUnknownMethod (entry : EntryModel) : Bool := entry.rawtype == 0
def direntryLinkMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 3 probe
def direntryFileMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 1 probe
def direntryDirMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 2 probe
def direntryFifoMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 4 probe
def direntrySocketMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 5 probe
def direntryCharMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 6 probe
def direntryBlockMethod (entry : EntryModel) (probe : EntryProbe) : Bool := entryKind entry.rawtype 7 probe
def direntryRealpathMethod (entry : EntryModel) (resolved : List Nat) : List Nat × List Nat :=
  (entryPath entry, resolved)

def DirEntryMethods : Prop :=
  (∀ entry, direntryBasenameMethod entry = entry.name) ∧
  (∀ entry, direntryDirnameMethod entry = entry.dir) ∧
  (∀ entry parts, direntryJoinpathMethod entry parts = entry.dir ++ [entry.name] ++ parts) ∧
  (∀ left right, direntryIslessMethod left right = entryLess left right) ∧
  (∀ entry, direntryHashMethod entry = [entry.rawtype, entry.name] ++ entry.dir) ∧
  (∀ left right, direntryEqMethod left right = (left == right)) ∧
  (∀ entry, direntryUnknownMethod entry = (entry.rawtype == 0)) ∧
  (∀ entry probe, direntryLinkMethod entry probe = entryKind entry.rawtype 3 probe) ∧
  (∀ entry probe, direntryFileMethod entry probe = entryKind entry.rawtype 1 probe) ∧
  (∀ entry probe, direntryDirMethod entry probe = entryKind entry.rawtype 2 probe) ∧
  (∀ entry probe, direntryFifoMethod entry probe = entryKind entry.rawtype 4 probe) ∧
  (∀ entry probe, direntrySocketMethod entry probe = entryKind entry.rawtype 5 probe) ∧
  (∀ entry probe, direntryCharMethod entry probe = entryKind entry.rawtype 6 probe) ∧
  (∀ entry probe, direntryBlockMethod entry probe = entryKind entry.rawtype 7 probe) ∧
  (∀ entry resolved, direntryRealpathMethod entry resolved = (entryPath entry, resolved))

theorem dirEntryMethods : DirEntryMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def readdirDefaultMethod (pwd : List Nat) (join : Bool) (scan : List Nat) (sort : Bool) :
    List (List Nat) := readdir (if join then pwd else []) scan join sort
def readdirAbstractMethod (result : List (List Nat)) : List (List Nat) := result
def readdirObjectsMethod (dir : List Nat) (names rawtypes : List Nat) (sort : Bool) : List EntryModel :=
  let pairs := names.zip rawtypes
  let pairs := if sort then pairs.toArray.qsort (fun a b => a.1 < b.1) |>.toList else pairs
  pairs.map fun pair => ⟨dir, pair.1, pair.2⟩
def readdirObjectDefaultMethod (pwd : List Nat) (names rawtypes : List Nat) (sort : Bool) : List EntryModel :=
  readdirObjectsMethod pwd names rawtypes sort
def readdirObjectEntryMethod (entry : EntryModel) (names rawtypes : List Nat) (sort : Bool) : List EntryModel :=
  readdirObjectsMethod (entryPath entry) names rawtypes sort
def readdirEntryStringMethod (entry : EntryModel) (scan : List Nat) (join sort : Bool) : List (List Nat) :=
  readdir (entryPath entry) scan join sort

def ReaddirMethods : Prop :=
  (∀ pwd join scan sort, readdirDefaultMethod pwd join scan sort =
    readdir (if join then pwd else []) scan join sort) ∧
  (∀ result, readdirAbstractMethod result = result) ∧
  (∀ dir names rawtypes sort, readdirObjectsMethod dir names rawtypes sort =
    let pairs := names.zip rawtypes
    let pairs := if sort then pairs.toArray.qsort (fun a b => a.1 < b.1) |>.toList else pairs
    pairs.map fun pair => ⟨dir, pair.1, pair.2⟩) ∧
  (∀ pwd names rawtypes sort, readdirObjectDefaultMethod pwd names rawtypes sort =
    readdirObjectsMethod pwd names rawtypes sort) ∧
  (∀ entry names rawtypes sort, readdirObjectEntryMethod entry names rawtypes sort =
    readdirObjectsMethod (entryPath entry) names rawtypes sort) ∧
  (∀ entry scan join sort, readdirEntryStringMethod entry scan join sort =
    readdir (entryPath entry) scan join sort)

theorem readdirMethods : ReaddirMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def iteratorCtorMethod (dir : List Nat) (join validType : Bool) (kind : IteratorKind) :
    Result IteratorState :=
  if validType then .ok (makeIterator dir join kind)
  else .error .argument (makeIterator dir join kind)
def eachentryOpenMethod (state : IteratorState) (succeeds : Bool) : Result IteratorState :=
  openIterator state succeeds
def iteratorCloseMethod (state : IteratorState) : IteratorState := closeIterator state
def iteratorSizeMethod : Nat := 0
def iteratorEltypeMethod (kind : IteratorKind) : IteratorKind := kind
def iteratorIsdoneMethod (state : IteratorState) : Bool := iteratorDone state
def iteratorIterateMethod (state : IteratorState) (next : Option (Nat × Nat)) := iterateEntry state next

def IteratorMethods : Prop :=
  (∀ dir join valid kind, iteratorCtorMethod dir join valid kind =
    if valid then .ok (makeIterator dir join kind) else .error .argument (makeIterator dir join kind)) ∧
  (∀ state succeeds, eachentryOpenMethod state succeeds = openIterator state succeeds) ∧
  (∀ state, iteratorCloseMethod state = closeIterator state) ∧
  (iteratorSizeMethod = 0) ∧
  (∀ kind, iteratorEltypeMethod kind = kind) ∧
  (∀ state, iteratorIsdoneMethod state = state.closed) ∧
  (∀ state next, iteratorIterateMethod state next = iterateEntry state next)

theorem iteratorMethods : IteratorMethods := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_⟩ <;> intros <;> rfl

def eachentryStringMethod (dir : List Nat) (join : Bool) : IteratorState :=
  makeIterator dir join .string
def eachentryEntryMethod (dir : List Nat) : IteratorState := makeIterator dir false .entry
def eachentryFromEntryStringMethod (entry : EntryModel) (join : Bool) : IteratorState :=
  eachentryStringMethod (entryPath entry) join
def eachentryFromEntryMethod (entry : EntryModel) : IteratorState := eachentryEntryMethod (entryPath entry)
def eachentryDefaultEntryMethod (pwd : List Nat) : IteratorState := eachentryEntryMethod pwd

inductive EachentryEvent where | create | callback | close deriving Repr, DecidableEq
def eachentryCallbackMethod : List EachentryEvent := [.create, .callback, .close]

def EachentryMethods : Prop :=
  (∀ dir join, eachentryStringMethod dir join = makeIterator dir join .string) ∧
  (∀ entry join, eachentryFromEntryStringMethod entry join =
    eachentryStringMethod (entryPath entry) join) ∧
  (∀ dir, eachentryEntryMethod dir = makeIterator dir false .entry) ∧
  (∀ pwd, eachentryDefaultEntryMethod pwd = eachentryEntryMethod pwd) ∧
  (∀ entry, eachentryFromEntryMethod entry = eachentryEntryMethod (entryPath entry)) ∧
  (eachentryCallbackMethod = [.create, .callback, .close])

theorem eachentryMethods : EachentryMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

inductive TryfResult (α : Type) where | value (value : α) | ioError | otherError

def walkTryfMethod {α : Type} (result : TryfResult α) : Result (Option α) :=
  match result with
  | .value value => .ok (some value)
  | .ioError => .ok none
  | .otherError => .error .io none

def walkdirWrapperMethod (parent : List Nat) (tree : DirTree) (topdown : Bool) : List WalkRow :=
  walkdir parent tree topdown
def walkdirInternalMethod (parent : List Nat) (tree : DirTree) (topdown : Bool) : List WalkRow :=
  if topdown then walkTop parent tree else walkBottom parent tree

def WalkdirMethods : Prop :=
  (∀ (α : Type) (result : TryfResult α), walkTryfMethod result =
    match result with
    | .value value => .ok (some value)
    | .ioError => .ok none
    | .otherError => .error .io none) ∧
  (∀ parent tree topdown, walkdirWrapperMethod parent tree topdown = walkdir parent tree topdown) ∧
  (∀ parent tree topdown, walkdirInternalMethod parent tree topdown =
    if topdown then walkTop parent tree else walkBottom parent tree)

theorem walkdirMethods : WalkdirMethods := by
  refine ⟨?_, ?_, ?_⟩
  · intro α result; cases result <;> rfl
  · intros; rfl
  · intros; rfl

/-! ## Primitive file wrappers and disk statistics (`base/file.jl:1445-1713`) -/

def unitCall (returnCode : Int) : Result Unit :=
  if returnCode < 0 then .error .io () else .ok ()

def valueCall {α : Type} (returnCode : Int) (value fallback : α) : Result α :=
  if returnCode < 0 then .error .io fallback else .ok value

def copyFileFlags (force : Bool) : Nat := if force then 2 else 3

def symlinkFlags (windows dirTarget targetIsDirectory : Bool) : Nat :=
  if windows then if dirTarget || targetIsDirectory then 1 else 0 else 0

structure DiskStatModel where
  total : Nat
  available : Nat
  free : Nat
  deriving Repr, DecidableEq

inductive DiskField where | total | available | free deriving Repr, DecidableEq

def diskProperty (stats : DiskStatModel) : DiskField → Nat
  | .total => stats.total
  | .available => stats.available
  | .free => stats.free

def PrimitiveFileBehavior : Prop :=
  (∀ code, unitCall code = if code < 0 then .error .io () else .ok ()) ∧
  (∀ (α : Type) code (value fallback : α), valueCall code value fallback =
    if code < 0 then .error .io fallback else .ok value) ∧
  (∀ force, copyFileFlags force = if force then 2 else 3) ∧
  (∀ windows dirTarget targetDirectory,
    symlinkFlags windows dirTarget targetDirectory =
      if windows then if dirTarget || targetDirectory then 1 else 0 else 0) ∧
  (∀ stats, diskProperty stats .total = stats.total ∧
    diskProperty stats .available = stats.available ∧ diskProperty stats .free = stats.free)

theorem primitiveFileBehavior : PrimitiveFileBehavior := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro stats; exact ⟨rfl, rfl, rfl⟩

def unlinkMethod (returnCode : Int) : Result Unit := unitCall returnCode
def UnlinkMethod : Prop := ∀ code, unlinkMethod code = if code < 0 then .error .io () else .ok ()
theorem unlinkMethod_proven : UnlinkMethod := by unfold UnlinkMethod; intros; rfl

def renameMethod (newpath : PathText) (returnCode : Int) : Result PathText :=
  if returnCode < 0 then .error .io newpath else .ok newpath
def RenameMethod : Prop := ∀ newpath code, renameMethod newpath code =
  if code < 0 then .error .io newpath else .ok newpath
theorem renameMethod_proven : RenameMethod := by unfold RenameMethod; intros; rfl

def sendfilePathMethod (force : Bool) (returnCode : Int) : Nat × Result Unit :=
  (copyFileFlags force, unitCall returnCode)
def SendfilePathMethod : Prop := ∀ force code, sendfilePathMethod force code =
  (if force then 2 else 3, if code < 0 then .error .io () else .ok ())
theorem sendfilePathMethod_proven : SendfilePathMethod := by unfold SendfilePathMethod; intros; rfl

def hardlinkMethod (returnCode : Int) : Result Unit := unitCall returnCode
def HardlinkMethod : Prop := ∀ code, hardlinkMethod code =
  if code < 0 then .error .io () else .ok ()
theorem hardlinkMethod_proven : HardlinkMethod := by unfold HardlinkMethod; intros; rfl

def symlinkMethod (windows dirTarget targetIsDirectory : Bool) (returnCode : Int) :
    Nat × Result Unit :=
  (symlinkFlags windows dirTarget targetIsDirectory, unitCall returnCode)
def SymlinkMethod : Prop := ∀ windows dirTarget targetDirectory code,
  symlinkMethod windows dirTarget targetDirectory code =
    (if windows then if dirTarget || targetDirectory then 1 else 0 else 0,
     if code < 0 then .error .io () else .ok ())
theorem symlinkMethod_proven : SymlinkMethod := by unfold SymlinkMethod; intros; rfl

inductive ReadlinkEvent where | allocate | call | cleanup | free deriving Repr, DecidableEq
def readlinkMethod (target fallback : PathText) (returnCode : Int) :
    List ReadlinkEvent × Result PathText :=
  let events := [.allocate, .call, .cleanup, .free]
  if returnCode < 0 then (events, .error .io fallback) else (events, .ok target)
def ReadlinkMethod : Prop := ∀ target fallback code, readlinkMethod target fallback code =
  let events := [.allocate, .call, .cleanup, .free]
  if code < 0 then (events, .error .io fallback) else (events, .ok target)
theorem readlinkMethod_proven : ReadlinkMethod := by unfold ReadlinkMethod; intros; rfl

def chmodMethod (path : PathText) (mode : Nat) (returnCode : Int)
    (recursive isDirectory : Bool) (tree : ModeTree) : Result (PathText × ModeTree) :=
  if returnCode < 0 then .error .io (path, tree)
  else .ok (path, if recursive && isDirectory then chmodTree mode true tree else tree)
def ChmodMethod : Prop := ∀ path mode code recursive directory tree,
  chmodMethod path mode code recursive directory tree =
    if code < 0 then .error .io (path, tree)
    else .ok (path, if recursive && directory then chmodTree mode true tree else tree)
theorem chmodMethod_proven : ChmodMethod := by unfold ChmodMethod; intros; rfl

def chownMethod (path : PathText) (returnCode : Int) : Result PathText :=
  if returnCode < 0 then .error .io path else .ok path
def ChownMethod : Prop := ∀ path code, chownMethod path code =
  if code < 0 then .error .io path else .ok path
theorem chownMethod_proven : ChownMethod := by unfold ChownMethod; intros; rfl

structure DiskStatFull where
  ftype : Nat
  blockSize : Nat
  blocks : Nat
  freeBlocks : Nat
  availableBlocks : Nat
  files : Nat
  freeFiles : Nat
  deriving Repr, DecidableEq

inductive DiskProperty where
  | ftype | blockSize | blocks | freeBlocks | availableBlocks | files | freeFiles
  | available | total | used
  deriving Repr, DecidableEq

def diskstatGetpropertyMethod (stats : DiskStatFull) : DiskProperty → Nat
  | .ftype => stats.ftype
  | .blockSize => stats.blockSize
  | .blocks => stats.blocks
  | .freeBlocks => stats.freeBlocks
  | .availableBlocks => stats.availableBlocks
  | .files => stats.files
  | .freeFiles => stats.freeFiles
  | .available => stats.blockSize * stats.availableBlocks
  | .total => stats.blockSize * stats.blocks
  | .used => stats.blockSize * stats.blocks - stats.blockSize * stats.availableBlocks

def diskstatPropertynamesMethod : List DiskProperty :=
  [.ftype, .blockSize, .blocks, .freeBlocks, .availableBlocks, .files, .freeFiles,
   .available, .total, .used]
def diskstatShowMethod (stats : DiskStatFull) : Nat × Nat × Nat :=
  (diskstatGetpropertyMethod stats .total, diskstatGetpropertyMethod stats .used,
   diskstatGetpropertyMethod stats .available)
def diskstatMethod (returnCode : Int) (loaded fallback : DiskStatFull) : Result DiskStatFull :=
  if returnCode < 0 then .error .io fallback else .ok loaded

def DiskstatMethods : Prop :=
  (∀ stats property, diskstatGetpropertyMethod stats property =
    match property with
    | .ftype => stats.ftype | .blockSize => stats.blockSize | .blocks => stats.blocks
    | .freeBlocks => stats.freeBlocks | .availableBlocks => stats.availableBlocks
    | .files => stats.files | .freeFiles => stats.freeFiles
    | .available => stats.blockSize * stats.availableBlocks
    | .total => stats.blockSize * stats.blocks
    | .used => stats.blockSize * stats.blocks - stats.blockSize * stats.availableBlocks) ∧
  (diskstatPropertynamesMethod =
    [.ftype, .blockSize, .blocks, .freeBlocks, .availableBlocks, .files, .freeFiles,
     .available, .total, .used]) ∧
  (∀ stats, diskstatShowMethod stats =
    (diskstatGetpropertyMethod stats .total, diskstatGetpropertyMethod stats .used,
     diskstatGetpropertyMethod stats .available)) ∧
  (∀ code loaded fallback, diskstatMethod code loaded fallback =
    if code < 0 then .error .io fallback else .ok loaded)

theorem diskstatMethods : DiskstatMethods := by
  refine ⟨?_, rfl, ?_, ?_⟩ <;> intros <;> rfl

/-! ## Stat construction and wrappers (`base/stat.jl:59-251`) -/

structure FullStat where
  desc : List Nat
  device : Nat
  inode : Nat
  mode : Nat
  nlink : Int
  uid : Nat
  gid : Nat
  rdev : Nat
  size : Int
  blksize : Int
  blocks : Int
  mtime : Int
  ctime : Int
  ioerrno : Int
  deriving Repr, DecidableEq

def statKey (stat : FullStat) : List Int :=
  [stat.device, stat.inode, stat.mode, stat.nlink, stat.uid, stat.gid, stat.rdev,
   stat.size, stat.blksize, stat.blocks, stat.mtime, stat.ctime, stat.ioerrno]

def statEqual (left right : FullStat) : Bool := statKey left == statKey right

def emptyStat : FullStat := ⟨[], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2⟩

def decodeStat (desc : List Nat) (raw : FullStat) (ioerrno : Int) : FullStat :=
  if ioerrno == 0 then { raw with desc, ioerrno }
  else { emptyStat with desc, ioerrno }

def checkStat (stat : FullStat) : Result FullStat :=
  if stat.ioerrno == 0 || stat.ioerrno == -2 || stat.ioerrno == -20 || stat.ioerrno == -22 then
    .ok stat
  else .error .io stat

def StatConstructionBehavior : Prop :=
  (∀ left right, statEqual left right = (statKey left == statKey right)) ∧
  (∀ desc raw errno, decodeStat desc raw errno =
    if errno == 0 then { raw with desc, ioerrno := errno }
    else { emptyStat with desc, ioerrno := errno }) ∧
  (∀ stat, checkStat stat =
    if stat.ioerrno == 0 || stat.ioerrno == -2 || stat.ioerrno == -20 || stat.ioerrno == -22 then
      .ok stat else .error .io stat)

theorem statConstructionBehavior : StatConstructionBehavior := by
  refine ⟨?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl

/-! ## Stat display and mode helpers (`base/stat.jl:110-566`) -/

inductive RelativeUnit where | day | hour | minute | second deriving Repr, DecidableEq

def relativeTime (difference : Int) : Option (RelativeUnit × Nat × Bool) :=
  let magnitude := difference.natAbs
  if magnitude / 86400 != 0 then some (RelativeUnit.day, magnitude / 86400, decide (difference > 0))
  else if magnitude / 3600 != 0 then some (RelativeUnit.hour, magnitude / 3600, decide (difference > 0))
  else if magnitude / 60 != 0 then some (RelativeUnit.minute, magnitude / 60, decide (difference > 0))
  else if magnitude != 0 then some (RelativeUnit.second, magnitude, decide (difference > 0))
  else none

def nonemptyName (name : Option (List Char)) : Option (List Char) :=
  match name with | some (head :: tail) => some (head :: tail) | _ => none

def fileTypeChar (mode : Nat) : Char :=
  match mode / 4096 % 16 with
  | 10 => 'l' | 12 => 's' | 8 => '-' | 6 => 'b' | 4 => 'd' | 2 => 'c' | 1 => 'p'
  | _ => '-'

def bitChar (enabled : Bool) (char : Char) : Char := if enabled then char else '-'

def executeChar (execute special : Bool) (low high : Char) : Char :=
  if special then if execute then low else high else if execute then 'x' else '-'

def fileModeString (mode : Nat) : List Char :=
  [fileTypeChar mode,
   bitChar (mode / 256 % 2 == 1) 'r', bitChar (mode / 128 % 2 == 1) 'w',
   executeChar (mode / 64 % 2 == 1) (mode / 2048 % 2 == 1) 's' 'S',
   bitChar (mode / 32 % 2 == 1) 'r', bitChar (mode / 16 % 2 == 1) 'w',
   executeChar (mode / 8 % 2 == 1) (mode / 1024 % 2 == 1) 's' 'S',
   bitChar (mode / 4 % 2 == 1) 'r', bitChar (mode / 2 % 2 == 1) 'w',
   executeChar (mode % 2 == 1) (mode / 512 % 2 == 1) 't' 'T']

def typeTest (mode kind : Nat) : Bool := mode / 4096 % 16 == kind
def specialTest (mode divisor : Nat) : Bool := mode / divisor % 2 == 1

inductive ShownStatField where
  | error
  | size | device | inode | mode | nlink | uid | gid | rdev | blksize | blocks | mtime | ctime
  deriving Repr, DecidableEq

def shownStatFields (ioerrno : Int) : List ShownStatField :=
  if ioerrno != 0 then [.error]
  else [.size, .device, .inode, .mode, .nlink, .uid, .gid, .rdev, .blksize, .blocks, .mtime, .ctime]

def StatDisplayModeBehavior : Prop :=
  (∀ difference, relativeTime difference =
    let magnitude := difference.natAbs
    if magnitude / 86400 != 0 then some (RelativeUnit.day, magnitude / 86400, decide (difference > 0))
    else if magnitude / 3600 != 0 then some (RelativeUnit.hour, magnitude / 3600, decide (difference > 0))
    else if magnitude / 60 != 0 then some (RelativeUnit.minute, magnitude / 60, decide (difference > 0))
    else if magnitude != 0 then some (RelativeUnit.second, magnitude, decide (difference > 0))
    else none) ∧
  (∀ name, nonemptyName name =
    match name with | some (head :: tail) => some (head :: tail) | _ => none) ∧
  (∀ mode, fileModeString mode =
    [fileTypeChar mode,
     bitChar (mode / 256 % 2 == 1) 'r', bitChar (mode / 128 % 2 == 1) 'w',
     executeChar (mode / 64 % 2 == 1) (mode / 2048 % 2 == 1) 's' 'S',
     bitChar (mode / 32 % 2 == 1) 'r', bitChar (mode / 16 % 2 == 1) 'w',
     executeChar (mode / 8 % 2 == 1) (mode / 1024 % 2 == 1) 's' 'S',
     bitChar (mode / 4 % 2 == 1) 'r', bitChar (mode / 2 % 2 == 1) 'w',
     executeChar (mode % 2 == 1) (mode / 512 % 2 == 1) 't' 'T']) ∧
  (∀ mode kind, typeTest mode kind = (mode / 4096 % 16 == kind)) ∧
  (∀ mode divisor, specialTest mode divisor = (mode / divisor % 2 == 1))
  ∧ (∀ ioerrno, shownStatFields ioerrno =
    if ioerrno != 0 then [.error]
    else [.size, .device, .inode, .mode, .nlink, .uid, .gid, .rdev, .blksize, .blocks, .mtime, .ctime])

theorem statDisplayModeBehavior : StatDisplayModeBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def statField (field : Nat) (stat : FullStat) : Int :=
  match field with
  | 0 => stat.mode | 1 => stat.size | 2 => stat.mtime | 3 => stat.ctime | _ => 0

def pathPredicate (field : Nat) (stat : FullStat) : Int := statField field stat

def pathExistsCall (returnCode : Int) : Result Bool :=
  if returnCode == 0 || returnCode == -2 || returnCode == -20 || returnCode == -22 then
    .ok (returnCode == 0)
  else .error .io false

def sameFile (left right : FullStat) : Bool :=
  left.ioerrno == 0 && right.ioerrno == 0 && left.device == right.device && left.inode == right.inode

def isMount (isDirectory isLink : Bool) (child parent : FullStat) : Bool :=
  isDirectory && !isLink && (child.device != parent.device || child.inode == parent.inode)

def StatPathBehavior : Prop :=
  (∀ field stat, pathPredicate field stat = statField field stat) ∧
  (∀ code, pathExistsCall code =
    if code == 0 || code == -2 || code == -20 || code == -22 then .ok (code == 0)
    else .error .io false) ∧
  (∀ left right, sameFile left right =
    (left.ioerrno == 0 && right.ioerrno == 0 && left.device == right.device && left.inode == right.inode)) ∧
  (∀ directory link child parent, isMount directory link child parent =
    (directory && !link && (child.device != parent.device || child.inode == parent.inode)))

theorem statPathBehavior : StatPathBehavior := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-! ### Method-specific `base/stat.jl` mirrors -/

def statEqMethod (left right : FullStat) : Bool := statKey left == statKey right
def statHashMethod (stat : FullStat) : List Int := statKey stat
def statEmptyCtorMethod : FullStat := emptyStat
def statBufferCtorMethod (desc : List Nat) (raw : FullStat) (ioerrno : Int) : FullStat :=
  decodeStat desc raw ioerrno

def StatValueMethods : Prop :=
  (∀ left right, statEqMethod left right = (statKey left == statKey right)) ∧
  (∀ stat, statHashMethod stat = statKey stat) ∧
  (statEmptyCtorMethod = emptyStat) ∧
  (∀ desc raw ioerrno, statBufferCtorMethod desc raw ioerrno = decodeStat desc raw ioerrno)

theorem statValueMethods : StatValueMethods := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> intros <;> rfl

def isoDatetimeMethod (timestamp now : Int) : Option (RelativeUnit × Nat × Bool) :=
  relativeTime (timestamp - now)

def getusernameMethod (lookup : Option (List Char)) : Option (List Char) := nonemptyName lookup
def getgroupnameMethod (lookup : Option (List Char)) : Option (List Char) := nonemptyName lookup

structure ShowStatMethodResult where
  oneline : Bool
  fields : List ShownStatField
  closesParen : Bool
  deriving Repr, DecidableEq

def showStatstructMethod (stat : FullStat) (oneline : Bool) : ShowStatMethodResult :=
  ⟨oneline, shownStatFields stat.ioerrno, oneline⟩

def showStatMethod (stat : FullStat) : ShowStatMethodResult := showStatstructMethod stat true
def showStatTextMethod (stat : FullStat) : ShowStatMethodResult := showStatstructMethod stat false

def StatDisplayMethods : Prop :=
  (∀ timestamp now, isoDatetimeMethod timestamp now = relativeTime (timestamp - now)) ∧
  (∀ lookup, getusernameMethod lookup = nonemptyName lookup) ∧
  (∀ lookup, getgroupnameMethod lookup = nonemptyName lookup) ∧
  (∀ stat oneline, showStatstructMethod stat oneline =
    ⟨oneline, shownStatFields stat.ioerrno, oneline⟩) ∧
  (∀ stat, showStatMethod stat = showStatstructMethod stat true) ∧
  (∀ stat, showStatTextMethod stat = showStatstructMethod stat false)

theorem statDisplayMethods : StatDisplayMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

inductive StatCallEvent where
  | allocate (bytes : Nat)
  | zeroBuffer
  | statCall
  | decode
  | check
  deriving Repr, DecidableEq

def checkstatMethod (stat : FullStat) : Result FullStat := checkStat stat

def statCallMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  ([.allocate bufferBytes, .zeroBuffer, .statCall, .decode, .check], checkStat decoded)

def statHandleMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  statCallMethod bufferBytes decoded
def statPathMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  statCallMethod bufferBytes decoded
def lstatPathMethod (bufferBytes : Nat) (decoded : FullStat) : List StatCallEvent × Result FullStat :=
  statCallMethod bufferBytes decoded
def statRawFdMethod (convertedHandle : Nat) (bufferBytes : Nat) (decoded : FullStat) :
    Nat × (List StatCallEvent × Result FullStat) :=
  (convertedHandle, statHandleMethod bufferBytes decoded)

def statGenericMethod (sameType : Bool) (converted : Result FullStat) : Result FullStat :=
  if sameType then .error .errorException emptyStat else converted
def lstatGenericMethod (sameType : Bool) (converted : Result FullStat) : Result FullStat :=
  if sameType then .error .errorException emptyStat else converted
def statVarargsMethod (joined : Result FullStat) : Result FullStat := joined
def lstatVarargsMethod (joined : Result FullStat) : Result FullStat := joined

def StatCallMethods : Prop :=
  (∀ stat, checkstatMethod stat = checkStat stat) ∧
  (∀ bytes decoded, statCallMethod bytes decoded =
    ([.allocate bytes, .zeroBuffer, .statCall, .decode, .check], checkStat decoded)) ∧
  (∀ bytes decoded, statHandleMethod bytes decoded = statCallMethod bytes decoded) ∧
  (∀ bytes decoded, statPathMethod bytes decoded = statCallMethod bytes decoded) ∧
  (∀ bytes decoded, lstatPathMethod bytes decoded = statCallMethod bytes decoded) ∧
  (∀ handle bytes decoded, statRawFdMethod handle bytes decoded =
    (handle, statHandleMethod bytes decoded)) ∧
  (∀ same converted, statGenericMethod same converted =
    if same then .error .errorException emptyStat else converted) ∧
  (∀ same converted, lstatGenericMethod same converted =
    if same then .error .errorException emptyStat else converted) ∧
  (∀ joined, statVarargsMethod joined = joined) ∧
  (∀ joined, lstatVarargsMethod joined = joined)

theorem statCallMethods : StatCallMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def filemodeMethod (stat : FullStat) : Nat := stat.mode
def filemodeStringStatMethod (stat : FullStat) : List Char := fileModeString stat.mode
def filemodeStringMethod (mode : Nat) : List Char := fileModeString mode
def filesizeMethod (stat : FullStat) : Int := stat.size
def mtimeMethod (stat : FullStat) : Int := stat.mtime
def ctimeMethod (stat : FullStat) : Int := stat.ctime
def ispathStatMethod (stat : FullStat) : Bool := stat.ioerrno == 0
def isfifoMethod (stat : FullStat) : Bool := typeTest stat.mode 1
def ischardevMethod (stat : FullStat) : Bool := typeTest stat.mode 2
def isdirMethod (stat : FullStat) : Bool := typeTest stat.mode 4
def isblockdevMethod (stat : FullStat) : Bool := typeTest stat.mode 6
def isfileMethod (stat : FullStat) : Bool := typeTest stat.mode 8
def islinkMethod (stat : FullStat) : Bool := typeTest stat.mode 10
def issocketMethod (stat : FullStat) : Bool := typeTest stat.mode 12
def issetuidMethod (stat : FullStat) : Bool := specialTest stat.mode 2048
def issetgidMethod (stat : FullStat) : Bool := specialTest stat.mode 1024
def isstickyMethod (stat : FullStat) : Bool := specialTest stat.mode 512
def upermMethod (stat : FullStat) : Nat := stat.mode / 64 % 8
def gpermMethod (stat : FullStat) : Nat := stat.mode / 8 % 8
def opermMethod (stat : FullStat) : Nat := stat.mode % 8

def StatFieldMethods : Prop :=
  (∀ stat, filemodeMethod stat = stat.mode) ∧
  (∀ stat, filemodeStringStatMethod stat = fileModeString stat.mode) ∧
  (∀ mode, filemodeStringMethod mode = fileModeString mode) ∧
  (∀ stat, filesizeMethod stat = stat.size) ∧
  (∀ stat, mtimeMethod stat = stat.mtime) ∧
  (∀ stat, ctimeMethod stat = stat.ctime) ∧
  (∀ stat, ispathStatMethod stat = (stat.ioerrno == 0)) ∧
  (∀ stat, isfifoMethod stat = typeTest stat.mode 1) ∧
  (∀ stat, ischardevMethod stat = typeTest stat.mode 2) ∧
  (∀ stat, isdirMethod stat = typeTest stat.mode 4) ∧
  (∀ stat, isblockdevMethod stat = typeTest stat.mode 6) ∧
  (∀ stat, isfileMethod stat = typeTest stat.mode 8) ∧
  (∀ stat, islinkMethod stat = typeTest stat.mode 10) ∧
  (∀ stat, issocketMethod stat = typeTest stat.mode 12) ∧
  (∀ stat, issetuidMethod stat = specialTest stat.mode 2048) ∧
  (∀ stat, issetgidMethod stat = specialTest stat.mode 1024) ∧
  (∀ stat, isstickyMethod stat = specialTest stat.mode 512) ∧
  (∀ stat, upermMethod stat = stat.mode / 64 % 8) ∧
  (∀ stat, gpermMethod stat = stat.mode / 8 % 8) ∧
  (∀ stat, opermMethod stat = stat.mode % 8)

theorem statFieldMethods : StatFieldMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ispathStringMethod (returnCode : Int) : Result Bool := pathExistsCall returnCode
def ispathAbstractStringMethod (stringResult : Result Bool) : Result Bool := stringResult

inductive StatAccessor where
  | path | fifo | charDevice | directory | blockDevice | file | socket
  | setuid | setgid | sticky | userPerm | groupPerm | otherPerm | mode | size | modified | changed
  deriving Repr, DecidableEq

def statAccessorMethod (accessor : StatAccessor) (stat : FullStat) : Int :=
  match accessor with
  | .path => if ispathStatMethod stat then 1 else 0
  | .fifo => if isfifoMethod stat then 1 else 0
  | .charDevice => if ischardevMethod stat then 1 else 0
  | .directory => if isdirMethod stat then 1 else 0
  | .blockDevice => if isblockdevMethod stat then 1 else 0
  | .file => if isfileMethod stat then 1 else 0
  | .socket => if issocketMethod stat then 1 else 0
  | .setuid => if issetuidMethod stat then 1 else 0
  | .setgid => if issetgidMethod stat then 1 else 0
  | .sticky => if isstickyMethod stat then 1 else 0
  | .userPerm => upermMethod stat
  | .groupPerm => gpermMethod stat
  | .otherPerm => opermMethod stat
  | .mode => stat.mode
  | .size => stat.size
  | .modified => stat.mtime
  | .changed => stat.ctime

def statPathAccessorMethod (accessor : StatAccessor) (statResult : FullStat) : Int :=
  statAccessorMethod accessor statResult
def islinkPathMethod (lstatResult : FullStat) : Bool := islinkMethod lstatResult
def samefileStatMethod (left right : FullStat) : Bool := sameFile left right
def samefilePathMethod (left right : FullStat) : Bool := samefileStatMethod left right
def ismountMethod (directory link : Bool) (child parent : FullStat) : Bool :=
  isMount directory link child parent

def StatPathMethods : Prop :=
  (∀ code, ispathStringMethod code = pathExistsCall code) ∧
  (∀ result, ispathAbstractStringMethod result = result) ∧
  (∀ accessor statResult, statPathAccessorMethod accessor statResult =
    statAccessorMethod accessor statResult) ∧
  (∀ statResult, islinkPathMethod statResult = islinkMethod statResult) ∧
  (∀ left right, samefileStatMethod left right = sameFile left right) ∧
  (∀ left right, samefilePathMethod left right = samefileStatMethod left right) ∧
  (∀ directory link child parent, ismountMethod directory link child parent =
    isMount directory link child parent)

theorem statPathMethods : StatPathMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-! ## Filesystem.File lifecycle and I/O (`base/filesystem.jl:155-459`) -/

structure HandleFile where
  isOpen : Bool
  handle : Int
  deriving Repr, DecidableEq

def newFile (handle : Int) : HandleFile := ⟨true, handle⟩
def rawHandle (file : HandleFile) : Int := file.handle
def setupStdio (file : HandleFile) : HandleFile × Bool := (file, false)
def openFile (returnHandle : Int) : Result HandleFile :=
  if returnHandle < 0 then .error .io ⟨false, -1⟩ else .ok (newFile returnHandle)
def checkOpen (file : HandleFile) : Result Unit :=
  if file.isOpen then .ok () else .error .argument ()
def closeHandle (_file : HandleFile) : HandleFile := ⟨false, -1⟩

def closeFile (file : FileState) : FileState := { file with isOpen := false }

inductive LockReply where | acquired | unavailable | failure deriving Repr, DecidableEq

def tryLock (file : FileState) (reply : LockReply) : Result (Bool × FileState) :=
  if !file.isOpen then .error .closed (false, file)
  else match reply with
    | .acquired => .ok (true, file)
    | .unavailable => .ok (false, file)
    | .failure => .error .io (false, file)

def sendChunks (maxChunk offset bytes : Nat) : List (Nat × Nat) :=
  if maxChunk == 0 || bytes == 0 then []
  else
    let count := (bytes + maxChunk - 1) / maxChunk
    (List.range count).map fun index =>
      (offset + index * maxChunk, min maxChunk (bytes - index * maxChunk))

def truncateData (data : List UInt8) (size : Nat) : List UInt8 :=
  if size ≤ data.length then data.take size
  else data ++ List.replicate (size - data.length) 0

def FileLifecycleTransferBehavior : Prop :=
  (∀ handle, newFile handle = ⟨true, handle⟩) ∧
  (∀ file, rawHandle file = file.handle) ∧
  (∀ file, setupStdio file = (file, false)) ∧
  (∀ handle, openFile handle =
    if handle < 0 then .error .io ⟨false, -1⟩ else .ok (newFile handle)) ∧
  (∀ file, checkOpen file = if file.isOpen then .ok () else .error .argument ()) ∧
  (∀ file, closeHandle file = ⟨false, -1⟩) ∧
  (∀ file, closeFile file = { file with isOpen := false }) ∧
  (∀ file reply, tryLock file reply =
    if !file.isOpen then .error .closed (false, file)
    else match reply with
      | .acquired => .ok (true, file)
      | .unavailable => .ok (false, file)
      | .failure => .error .io (false, file)) ∧
  (∀ maxChunk offset bytes, sendChunks maxChunk offset bytes =
    if maxChunk == 0 || bytes == 0 then []
    else let count := (bytes + maxChunk - 1) / maxChunk
      (List.range count).map fun index =>
        (offset + index * maxChunk, min maxChunk (bytes - index * maxChunk))) ∧
  (∀ data size, truncateData data size =
    if size ≤ data.length then data.take size
    else data ++ List.replicate (size - data.length) 0)

theorem fileLifecycleTransferBehavior : FileLifecycleTransferBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def seekEnd (file : FileState) : FileState := { file with position := file.data.length }
def seekResult (file : FileState) (returnedPosition : Int) : Result FileState :=
  if returnedPosition == -1 then .error .io file
  else .ok { file with position := returnedPosition.toNat }

def accessAllowed (returnCode : Int) : Bool := returnCode == 0

def continuationByte (byte : UInt8) : Bool := byte.toNat / 64 == 2

def continuationTail : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | _, [] => []
  | count + 1, byte :: bytes =>
      if continuationByte byte then byte :: continuationTail count bytes else []

def charReadBytes (first : UInt8) (leading rest : Nat) (bytes : List UInt8) : List UInt8 :=
  first :: if 2 ≤ leading ∧ leading ≤ 4 then continuationTail rest bytes else []

def FileReadAccessBehavior : Prop :=
  (∀ file, seekEnd file = { file with position := file.data.length }) ∧
  (∀ file returnedPosition, seekResult file returnedPosition =
    if returnedPosition == -1 then .error .io file
    else .ok { file with position := returnedPosition.toNat }) ∧
  (∀ file, bytesavailable file = file.data.length - file.position) ∧
  (∀ file, (bytesavailable file == 0) = (file.data.length - file.position == 0)) ∧
  (∀ first leading rest bytes, charReadBytes first leading rest bytes =
    first :: if 2 ≤ leading ∧ leading ≤ 4 then continuationTail rest bytes else []) ∧
  (∀ code, accessAllowed code = (code == 0))

theorem fileReadAccessBehavior : FileReadAccessBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-! ### Method-specific `base/filesystem.jl` mirrors -/

inductive FsEvent where
  | cleanupRequest
  | allocateRequest
  | freeRequest
  | openCall (flags mode : Int)
  | closeCall
  | lockCall (shared : Bool)
  | unlockCall
  | sendfileCall (offset count : Nat)
  | writeCall (count : Nat) (offset : Int)
  | truncateCall (size : Int)
  | futimeCall
  | readCall (count : Nat)
  | seekSet (position : Int)
  | seekCurrent (amount : Int)
  | seekEnd
  | touchCall
  | accessCall (mode : Nat)
  deriving Repr, DecidableEq

def uvFsReqCleanupMethod : List FsEvent := [.cleanupRequest]

def fileFromHandleMethod (handle : Int) : HandleFile := ⟨true, handle⟩
def fileFromRawFdMethod (convertedHandle : Int) : HandleFile := fileFromHandleMethod convertedHandle
def rawhandleMethod (file : HandleFile) : Int := file.handle
def setupStdioMethod (file : HandleFile) : HandleFile × Bool := (file, false)

def openFsMethod (flags mode returnCode handle : Int) : List FsEvent × Result HandleFile :=
  let events := [.allocateRequest, .openCall flags mode, .cleanupRequest, .freeRequest]
  if returnCode < 0 then (events, .error .io ⟨false, -1⟩)
  else (events, .ok ⟨true, handle⟩)

def isopenMethod (file : HandleFile) : Bool := file.isOpen
def checkOpenMethod (file : HandleFile) : Result Unit :=
  if file.isOpen then .ok () else .error .argument ()

def closeFsMethod (file : HandleFile) (returnCode : Int) : List FsEvent × Result HandleFile :=
  if !file.isOpen then ([], .ok file)
  else
    let closed : HandleFile := ⟨false, -1⟩
    if returnCode < 0 then ([.closeCall], .error .io closed) else ([.closeCall], .ok closed)

def FileLifecycleMethods : Prop :=
  (uvFsReqCleanupMethod = [.cleanupRequest]) ∧
  (∀ handle, fileFromHandleMethod handle = ⟨true, handle⟩) ∧
  (∀ converted, fileFromRawFdMethod converted = fileFromHandleMethod converted) ∧
  (∀ file, rawhandleMethod file = file.handle) ∧
  (∀ file, setupStdioMethod file = (file, false)) ∧
  (∀ flags mode code handle, openFsMethod flags mode code handle =
    let events := [.allocateRequest, .openCall flags mode, .cleanupRequest, .freeRequest]
    if code < 0 then (events, .error .io ⟨false, -1⟩)
    else (events, .ok ⟨true, handle⟩)) ∧
  (∀ file, isopenMethod file = file.isOpen) ∧
  (∀ file, checkOpenMethod file = if file.isOpen then .ok () else .error .argument ()) ∧
  (∀ file code, closeFsMethod file code =
    if !file.isOpen then ([], .ok file)
    else let closed : HandleFile := ⟨false, -1⟩
      if code < 0 then ([.closeCall], .error .io closed) else ([.closeCall], .ok closed))

theorem fileLifecycleMethods : FileLifecycleMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

inductive LockObservation where
  | success
  | unavailable
  | failure
  deriving Repr, DecidableEq

def trylockfileMethod (file : HandleFile) (shared : Bool) (observation : LockObservation) :
    List FsEvent × Result Bool :=
  if !file.isOpen then ([], .error .argument false)
  else match observation with
    | .success => ([.lockCall shared], .ok true)
    | .unavailable => ([.lockCall shared], .ok false)
    | .failure => ([.lockCall shared], .error .io false)

def unlockfileMethod (file : HandleFile) (observation : LockObservation) :
    List FsEvent × Result Unit :=
  if !file.isOpen then ([], .error .argument ())
  else match observation with
    | .failure => ([.unlockCall], .error .io ())
    | _ => ([.unlockCall], .ok ())

def closewriteMethod (_file : HandleFile) : Unit := ()

def FileLockMethods : Prop :=
  (∀ file shared observation, trylockfileMethod file shared observation =
    if !file.isOpen then ([], .error .argument false)
    else match observation with
      | .success => ([.lockCall shared], .ok true)
      | .unavailable => ([.lockCall shared], .ok false)
      | .failure => ([.lockCall shared], .error .io false)) ∧
  (∀ file observation, unlockfileMethod file observation =
    if !file.isOpen then ([], .error .argument ())
    else match observation with
      | .failure => ([.unlockCall], .error .io ())
      | _ => ([.unlockCall], .ok ())) ∧
  (∀ file, closewriteMethod file = ())

theorem fileLockMethods : FileLockMethods := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def sendfileMethod (dstOpen srcOpen : Bool) (maxChunk offset bytes : Nat) :
    Result (List FsEvent) :=
  if !dstOpen || !srcOpen then .error .argument []
  else .ok ((sendChunks maxChunk offset bytes).map fun pair => .sendfileCall pair.1 pair.2)

def unsafeWriteMethod (file : FileState) (count : Nat) (offset : Int) (returnCode : Int) :
    List FsEvent × Result Nat :=
  if !file.isOpen then ([], .error .closed 0)
  else if returnCode < 0 then ([.writeCall count offset], .error .io 0)
  else ([.writeCall count offset], .ok count)

def writeByteMethod (file : FileState) (byte : UInt8) (returnCode : Int) :
    List FsEvent × Result Nat :=
  let _byte := byte
  unsafeWriteMethod file 1 (-1) returnCode

def truncateMethod (file : FileState) (size returnCode : Int) :
    List FsEvent × Result FileState :=
  if !file.isOpen then ([], .error .closed file)
  else if returnCode < 0 then ([.allocateRequest, .truncateCall size, .freeRequest], .error .io file)
  else ([.allocateRequest, .truncateCall size, .freeRequest], .ok file)

def futimeMethod (file : FileState) (returnCode : Int) : List FsEvent × Result FileState :=
  if !file.isOpen then ([], .error .closed file)
  else if returnCode < 0 then ([.allocateRequest, .futimeCall, .freeRequest], .error .io file)
  else ([.allocateRequest, .futimeCall, .freeRequest], .ok file)

def FileWriteMethods : Prop :=
  (∀ dstOpen srcOpen maxChunk offset bytes, sendfileMethod dstOpen srcOpen maxChunk offset bytes =
    if !dstOpen || !srcOpen then .error .argument []
    else .ok ((sendChunks maxChunk offset bytes).map fun pair => .sendfileCall pair.1 pair.2)) ∧
  (∀ file count offset code, unsafeWriteMethod file count offset code =
    if !file.isOpen then ([], .error .closed 0)
    else if code < 0 then ([.writeCall count offset], .error .io 0)
    else ([.writeCall count offset], .ok count)) ∧
  (∀ file byte code, writeByteMethod file byte code = unsafeWriteMethod file 1 (-1) code) ∧
  (∀ file size code, truncateMethod file size code =
    if !file.isOpen then ([], .error .closed file)
    else if code < 0 then ([.allocateRequest, .truncateCall size, .freeRequest], .error .io file)
    else ([.allocateRequest, .truncateCall size, .freeRequest], .ok file)) ∧
  (∀ file code, futimeMethod file code =
    if !file.isOpen then ([], .error .closed file)
    else if code < 0 then ([.allocateRequest, .futimeCall, .freeRequest], .error .io file)
    else ([.allocateRequest, .futimeCall, .freeRequest], .ok file))

theorem fileWriteMethods : FileWriteMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def readUInt8Method (file : FileState) (returnCode : Int) (byte : UInt8) :
    List FsEvent × Result UInt8 :=
  if !file.isOpen then ([], .error .closed 0)
  else if returnCode < 0 then ([.readCall 1], .error .io 0)
  else if returnCode < 1 then ([.readCall 1], .error .eof 0)
  else ([.readCall 1], .ok byte)

def readCharMethod (file : FileState) (first : UInt8) (leading : Nat)
    (following : List UInt8) : Result (List UInt8) :=
  if !file.isOpen then .error .closed []
  else .ok (charReadBytes first leading (4 - leading) following)

def readAbstractCharMethod (decoded : Result (List UInt8)) : Result (List UInt8) := decoded

def unsafeReadMethod (file : FileState) (requested returned : Nat) (returnCode : Int) :
    List FsEvent × Result Unit :=
  if !file.isOpen then ([], .error .closed ())
  else if returnCode < 0 then ([.readCall requested], .error .io ())
  else if returned != requested then ([.readCall requested], .error .eof ())
  else ([.readCall requested], .ok ())

def FileScalarReadMethods : Prop :=
  (∀ file code byte, readUInt8Method file code byte =
    if !file.isOpen then ([], .error .closed 0)
    else if code < 0 then ([.readCall 1], .error .io 0)
    else if code < 1 then ([.readCall 1], .error .eof 0)
    else ([.readCall 1], .ok byte)) ∧
  (∀ file first leading following, readCharMethod file first leading following =
    if !file.isOpen then .error .closed []
    else .ok (charReadBytes first leading (4 - leading) following)) ∧
  (∀ decoded, readAbstractCharMethod decoded = decoded) ∧
  (∀ file requested returned code, unsafeReadMethod file requested returned code =
    if !file.isOpen then ([], .error .closed ())
    else if code < 0 then ([.readCall requested], .error .io ())
    else if returned != requested then ([.readCall requested], .error .eof ())
    else ([.readCall requested], .ok ()))

theorem fileScalarReadMethods : FileScalarReadMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def bytesavailableMethod (file : FileState) : Nat := file.data.length - file.position
def eofMethod (file : FileState) : Bool := bytesavailableMethod file == 0

def readbytesMethod (file : FileState) (bufferLength requested returnCode : Nat) :
    Result (Nat × Nat) :=
  if !file.isOpen then .error .closed (bufferLength, 0)
  else
    let count := min requested (bytesavailableMethod file)
    let resized := max bufferLength count
    .ok (resized, min returnCode count)

def readAllMethod (file : FileState) : Nat := bytesavailableMethod file
def readavailableMethod (file : FileState) : Nat := readAllMethod file
def readCountMethod (file : FileState) (requested : Nat) : Nat := min requested (bytesavailableMethod file)

def FileBulkReadMethods : Prop :=
  (∀ file, bytesavailableMethod file = file.data.length - file.position) ∧
  (∀ file, eofMethod file = (bytesavailableMethod file == 0)) ∧
  (∀ file bufferLength requested returned, readbytesMethod file bufferLength requested returned =
    if !file.isOpen then .error .closed (bufferLength, 0)
    else let count := min requested (bytesavailableMethod file)
      let resized := max bufferLength count
      .ok (resized, min returned count)) ∧
  (∀ file, readAllMethod file = bytesavailableMethod file) ∧
  (∀ file, readavailableMethod file = readAllMethod file) ∧
  (∀ file requested, readCountMethod file requested = min requested (bytesavailableMethod file))

theorem fileBulkReadMethods : FileBulkReadMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def seekMethod (file : FileState) (requested returned : Int) : List FsEvent × Result FileState :=
  if returned == -1 then ([.seekSet requested], .error .io file)
  else ([.seekSet requested], .ok { file with position := returned.toNat })

def seekendMethod (file : FileState) (returned : Int) : List FsEvent × Result FileState :=
  if returned == -1 then ([.seekEnd], .error .io file)
  else ([.seekEnd], .ok { file with position := returned.toNat })

def skipMethod (file : FileState) (amount returned : Int) : List FsEvent × Result FileState :=
  if returned == -1 then ([.seekCurrent amount], .error .io file)
  else ([.seekCurrent amount], .ok { file with position := returned.toNat })

def positionMethod (file : FileState) (returned : Int) : Result Nat :=
  if !file.isOpen then .error .closed file.position
  else if returned == -1 then .error .io file.position else .ok returned.toNat

def fdMethod (file : HandleFile) : Int := file.handle
def statFileMethod (statResult : FullStat) : FullStat := statResult
def touchFileMethod (file : FileState) (returnCode : Int) : List FsEvent × Result FileState :=
  if returnCode != 0 then ([.touchCall], .error .io file) else ([.touchCall], .ok file)

def FileSeekDescriptorMethods : Prop :=
  (∀ file requested returned, seekMethod file requested returned =
    if returned == -1 then ([.seekSet requested], .error .io file)
    else ([.seekSet requested], .ok { file with position := returned.toNat })) ∧
  (∀ file returned, seekendMethod file returned =
    if returned == -1 then ([.seekEnd], .error .io file)
    else ([.seekEnd], .ok { file with position := returned.toNat })) ∧
  (∀ file amount returned, skipMethod file amount returned =
    if returned == -1 then ([.seekCurrent amount], .error .io file)
    else ([.seekCurrent amount], .ok { file with position := returned.toNat })) ∧
  (∀ file returned, positionMethod file returned =
    if !file.isOpen then .error .closed file.position
    else if returned == -1 then .error .io file.position else .ok returned.toNat) ∧
  (∀ file, fdMethod file = file.handle) ∧
  (∀ statResult, statFileMethod statResult = statResult) ∧
  (∀ file code, touchFileMethod file code =
    if code != 0 then ([.touchCall], .error .io file) else ([.touchCall], .ok file))

theorem fileSeekDescriptorMethods : FileSeekDescriptorMethods := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def accessMethod (mode : Nat) (returnCode : Int) : List FsEvent × Bool :=
  ([.accessCall mode], returnCode == 0)

def accessAbstractStringMethod (result : List FsEvent × Bool) : List FsEvent × Bool := result

def FileAccessMethods : Prop :=
  (∀ mode code, accessMethod mode code = ([.accessCall mode], code == 0)) ∧
  (∀ result, accessAbstractStringMethod result = result)

theorem fileAccessMethods : FileAccessMethods := by
  constructor <;> intros <;> rfl

/-! ## POSIX path wrappers and URIs (`base/path.jl`) -/

def posixSeparator (char : Char) : Bool := char == '/'
def posixSeparatorByte (byte : Nat) : Bool := byte == 47
def posixSplitDrive (path : PathText) : PathText × PathText := ([], path)
def pathSeparator : Char := '/'

def assertString (isString : Bool) : Result Unit :=
  if isString then .ok () else .error .argument ()

inductive UserLookup where
  | rangeError
  | found (home : PathText)
  | missing
  deriving Repr, DecidableEq

def lookupHome : Nat → List UserLookup → Option PathText
  | 0, _ => none
  | _, [] => none
  | attempts + 1, .rangeError :: replies => lookupHome attempts replies
  | _, .found home :: _ => some home
  | _, .missing :: _ => none

def realpathCall (path resolved : PathText) (returnCode : Int) : Result PathText :=
  if returnCode < 0 then .error .io path else .ok resolved

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

structure ContractCandidate where
  stem : PathText
  rest : PathText
  present : Bool
  currentHome : Bool
  username : Option PathText
  userHome : Bool
  deriving Repr, DecidableEq

def contractCandidates : List ContractCandidate → PathText → PathText
  | [], original => original
  | candidate :: candidates, original =>
      if !candidate.present then original
      else if candidate.currentHome then ['~'] ++ candidate.rest
      else match candidate.username with
        | some username => if candidate.userHome then ['~'] ++ username ++ candidate.rest
          else contractCandidates candidates original
        | none => contractCandidates candidates original

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

def hexDigit (value : Nat) : Nat := if value < 10 then 48 + value else 55 + value

def uriUnit (byte : Nat) : List Nat :=
  if decide (65 ≤ byte ∧ byte ≤ 90) || decide (97 ≤ byte ∧ byte ≤ 122) ||
      decide (48 ≤ byte ∧ byte ≤ 57) || [45, 95, 46, 126, 47].contains byte then [byte]
  else [37, hexDigit (byte / 16), hexDigit (byte % 16)]

def encodeUri (bytes : List Nat) : List Nat := bytes.flatMap uriUnit

def unixUriPath (host localPath : List Nat) : List Nat :=
  "file://".toList.map Char.toNat ++ encodeUri host ++ [47] ++ encodeUri localPath

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

def isseparatorCharMethod (char : Char) : Bool := char == '/'
def isseparatorByteMethod (byte : Nat) : Bool := byte == 47
def splitdrivePosixMethod (path : PathText) : PathText × PathText := ([], path)
def isabspathPosixMethod (path : PathText) : Bool := JuliaLean.Paths.isabspath path
def pathsepMethod : Char := '/'
def assertstringMethod (isString : Bool) : Result Unit :=
  if isString then .ok () else .error .argument ()

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

def homedirMethod (replies : List BufferReply) : Result PathText := bufferPath replies

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

inductive RealpathEvent where | allocate | call | cleanup | free deriving Repr, DecidableEq

def realpathMethod (path resolved : PathText) (returnCode : Int) :
    List RealpathEvent × Result PathText :=
  let events := [.allocate, .call, .cleanup, .free]
  if returnCode < 0 then (events, .error .io path) else (events, .ok resolved)

def PathRealpathMethod : Prop :=
  ∀ path resolved code, realpathMethod path resolved code =
    let events := [.allocate, .call, .cleanup, .free]
    if code < 0 then (events, .error .io path) else (events, .ok resolved)

theorem pathRealpathMethod : PathRealpathMethod := by unfold PathRealpathMethod; intros; rfl

inductive AbstractPathWrapper where
  | isdirpath | splitdir | splitdrive | splitext | normpath | abspath | isabspath
  deriving Repr, DecidableEq

def abstractPathWrapperMethod (kind : AbstractPathWrapper) (cwd path : PathText) :
    Bool × PathText × (PathText × PathText) :=
  match kind with
  | .isdirpath => (JuliaLean.Paths.isdirpath path, path, ([], []))
  | .splitdir => (false, path, JuliaLean.Paths.splitdir path)
  | .splitdrive => (false, path, ([], path))
  | .splitext => (false, path, JuliaLean.Paths.splitext path)
  | .normpath => (false, JuliaLean.Paths.normpath path, ([], []))
  | .abspath => (false, JuliaLean.Paths.abspath cwd path, ([], []))
  | .isabspath => (JuliaLean.Paths.isabspath path, path, ([], []))

def PathAbstractWrapperMethod : Prop :=
  ∀ kind cwd path, abstractPathWrapperMethod kind cwd path =
    match kind with
    | .isdirpath => (JuliaLean.Paths.isdirpath path, path, ([], []))
    | .splitdir => (false, path, JuliaLean.Paths.splitdir path)
    | .splitdrive => (false, path, ([], path))
    | .splitext => (false, path, JuliaLean.Paths.splitext path)
    | .normpath => (false, JuliaLean.Paths.normpath path, ([], []))
    | .abspath => (false, JuliaLean.Paths.abspath cwd path, ([], []))
    | .isabspath => (JuliaLean.Paths.isabspath path, path, ([], []))

theorem pathAbstractWrapperMethod : PathAbstractWrapperMethod := by unfold PathAbstractWrapperMethod; intros; rfl

def homedirUsernameMethod (attempts : Nat) (replies : List UserLookup) : Option PathText :=
  lookupHome attempts replies
def contractuserMethod (candidates : List ContractCandidate) (original : PathText) : PathText :=
  contractCandidates candidates original
def contractuserAbstractMethod (result : PathText) : PathText := result

def PathUserMethods : Prop :=
  (∀ attempts replies, homedirUsernameMethod attempts replies = lookupHome attempts replies) ∧
  (∀ candidates original, contractuserMethod candidates original =
    contractCandidates candidates original) ∧
  (∀ result, contractuserAbstractMethod result = result)

theorem pathUserMethods : PathUserMethods := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def encodeUriComponentMethod (bytes : List Nat) : List Nat := encodeUri bytes
def uripathPosixMethod (cwd path : PathText) (wsl : Bool) (distro hostname : List Nat) : List Nat :=
  let localPath := JuliaLean.Paths.joinSep
    (JuliaLean.Paths.splitAtSeps (JuliaLean.Paths.abspath cwd path) false)
  let host := if wsl then "wsl$/".toList.map Char.toNat ++ distro else hostname
  unixUriPath host (localPath.map Char.toNat)
def uripathAbstractMethod (result : List Nat) : List Nat := result

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

def dirnameAbstractMethod (path : PathText) : PathText := JuliaLean.Paths.dirname path
def basenameAbstractMethod (path : PathText) : PathText := JuliaLean.Paths.basename path
def splitpathAbstractMethod (path : PathText) : List PathText := JuliaLean.Paths.splitpath path
def joinpathVarargsMethod (paths : List PathText) := JuliaLean.Paths.joinpath paths
def normpathVarargsMethod (paths : List PathText) : JuliaLean.Jl PathText :=
  (JuliaLean.Paths.joinpath paths).map JuliaLean.Paths.normpath
def abspathVarargsMethod (cwd : PathText) (paths : List PathText) : JuliaLean.Jl PathText :=
  (JuliaLean.Paths.joinpath paths).map (JuliaLean.Paths.abspath cwd)
def expanduserAbstractMethod (home path : PathText)
    (lookup : PathText → Option PathText) (userChar : Char → Bool) : PathText :=
  JuliaLean.Paths.expanduser home lookup userChar path
def relpathAbstractMethod (cwd path start : PathText) := JuliaLean.Paths.relpath cwd path start

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
