import JuliaLean.base.file
import JuliaLean.Proofs.base.file.Proven

/-!
# Whole-Base method coverage for filesystem sources

Source-order models for the remaining methods in `base/file.jl`, `base/stat.jl`,
`base/filesystem.jl`, and the POSIX branch of `base/path.jl` at `bbfa0ce4150`.
System calls, clocks, directory scans, and user databases are explicit inputs.
-/

namespace JuliaLean.Files.Coverage

open JuliaLean.Files

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

def MkpathMethod : Prop := ∀ path parentIsSelf alreadyDirectory mode,
  mkpathMethod path parentIsSelf alreadyDirectory mode =
    if parentIsSelf || alreadyDirectory then .ok path
    else match checkMode mode with
      | .error error _ => .error error path
      | .ok _ => mkpath path

theorem mkpathMethod_proven : MkpathMethod := by unfold MkpathMethod; intros; rfl

def RmMethod : Prop := ∀ entry force recursive,
  rmMethod entry force recursive = rm entry force recursive
theorem rmMethod_proven : RmMethod := by unfold RmMethod; intros; rfl

/-! ## Tree copying and containment (`base/file.jl:348-458`) -/

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

def CpMethod : Prop :=
  ∀ check kind follow fuel source, cpMethod check kind follow fuel source =
    match check with
    | .error error _ => .error error source
    | .ok _ => match kind with
      | .link => if follow then .ok (cloneNode fuel true source) else .ok source
      | .directory => .ok (cloneNode fuel follow source)
      | .file => .ok source

theorem cpMethod_proven : CpMethod := by unfold CpMethod; intros; rfl

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

def TouchPathMethod : Prop := ∀ path openSucceeds touchSucceeds,
  touchPathMethod path openSucceeds touchSucceeds =
    if !openSucceeds then ([.open], .error .io path)
    else if !touchSucceeds then ([.open, .touch, .close], .error .io path)
    else ([.open, .touch, .close], .ok path)
theorem touchPathMethod_proven : TouchPathMethod := by unfold TouchPathMethod; intros; rfl

/-! ## Temporary paths and cleanup (`base/file.jl:605-998`) -/

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

def UnlinkMethod : Prop := ∀ code, unlinkMethod code = if code < 0 then .error .io () else .ok ()
theorem unlinkMethod_proven : UnlinkMethod := by unfold UnlinkMethod; intros; rfl

def RenameMethod : Prop := ∀ newpath code, renameMethod newpath code =
  if code < 0 then .error .io newpath else .ok newpath
theorem renameMethod_proven : RenameMethod := by unfold RenameMethod; intros; rfl

def SendfilePathMethod : Prop := ∀ force code, sendfilePathMethod force code =
  (if force then 2 else 3, if code < 0 then .error .io () else .ok ())
theorem sendfilePathMethod_proven : SendfilePathMethod := by unfold SendfilePathMethod; intros; rfl

def HardlinkMethod : Prop := ∀ code, hardlinkMethod code =
  if code < 0 then .error .io () else .ok ()
theorem hardlinkMethod_proven : HardlinkMethod := by unfold HardlinkMethod; intros; rfl

def SymlinkMethod : Prop := ∀ windows dirTarget targetDirectory code,
  symlinkMethod windows dirTarget targetDirectory code =
    (if windows then if dirTarget || targetDirectory then 1 else 0 else 0,
     if code < 0 then .error .io () else .ok ())
theorem symlinkMethod_proven : SymlinkMethod := by unfold SymlinkMethod; intros; rfl

def ReadlinkMethod : Prop := ∀ target fallback code, readlinkMethod target fallback code =
  let events := [.allocate, .call, .cleanup, .free]
  if code < 0 then (events, .error .io fallback) else (events, .ok target)
theorem readlinkMethod_proven : ReadlinkMethod := by unfold ReadlinkMethod; intros; rfl

def ChmodMethod : Prop := ∀ path mode code recursive directory tree,
  chmodMethod path mode code recursive directory tree =
    if code < 0 then .error .io (path, tree)
    else .ok (path, if recursive && directory then chmodTree mode true tree else tree)
theorem chmodMethod_proven : ChmodMethod := by unfold ChmodMethod; intros; rfl

def ChownMethod : Prop := ∀ path code, chownMethod path code =
  if code < 0 then .error .io path else .ok path
theorem chownMethod_proven : ChownMethod := by unfold ChownMethod; intros; rfl

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

end JuliaLean.Files.Coverage
