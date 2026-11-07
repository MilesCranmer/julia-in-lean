import JuliaLean.Proofs.base.stat

namespace JuliaLean.Files.Coverage

open JuliaLean.Files

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

def StatValueMethods : Prop :=
  (∀ left right, statEqMethod left right = (statKey left == statKey right)) ∧
  (∀ stat, statHashMethod stat = statKey stat) ∧
  (statEmptyCtorMethod = emptyStat) ∧
  (∀ desc raw ioerrno, statBufferCtorMethod desc raw ioerrno = decodeStat desc raw ioerrno)

theorem statValueMethods : StatValueMethods := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> intros <;> rfl

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

end JuliaLean.Files.Coverage
