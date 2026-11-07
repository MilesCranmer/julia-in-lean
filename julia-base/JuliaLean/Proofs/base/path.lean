import JuliaLean.base.path
import JuliaLean.Proofs.base.path.access_bounds
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.path.Entries


/-!
# Specifications for `base/path.jl`

The registry below records each path specification and its proof or refutation status.
Filesystem and string operations are the typed interfaces of `JuliaLean.base.path`.
-/

namespace JuliaLean.base.path.StringOps

@[simp] theorem fromBytesContent (ops : StringOps) (bytes : List UInt8) :
    ops.fromBytes bytes = Path.mk bytes := by
  rfl

@[simp] theorem fromBytesBytes (ops : StringOps) (bytes : List UInt8) :
    (ops.fromBytes bytes).bytes = bytes := by rw [fromBytesContent]

end JuliaLean.base.path.StringOps

namespace JuliaLean.Proofs.base.path

open JuliaLean.base.path JuliaLean.Registry

abbrev Bytes := List UInt8
def pathStringOps : StringOps where
  toupper := id
  tolower := id
  totitle := id
  category := fun _ => 0
  categoryString := fun _ => ""
  categoryAbbrev := fun _ => ""
  islower := fun _ => 0
  isupper := fun _ => 0
  charwidth := fun _ => 1
  graphemeBreak := fun _ _ => false
  graphemeBreakStateful := fun s _ _ => (false, s)

/-- A component contains no path separators for the selected platform. -/
def NoSeparators (os : Platform) (bs : Bytes) : Prop :=
  ∀ b, b ∈ bs → isseparatorByte os b = false

def NoDots (bs : Bytes) : Prop := ∀ b, b ∈ bs → b ≠ dot

def NoDoubleSeparator (os : Platform) : Bytes → Prop
  | a :: b :: rest => (isseparatorByte os a && isseparatorByte os b) = false ∧ NoDoubleSeparator os (b :: rest)
  | _ => True

def lastPathComponent (os : Platform) (ops : StringOps) (path : Path) : Bytes :=
  let (_, rest) := splitdrive os ops path
  (splitdirNoDrive os ops (emptyPath ops) rest).2.bytes

def dotDotPrefix (parts : List Bytes) : Prop :=
  ∃ n rest, parts = List.replicate n dotdot ++ rest ∧
    ∀ part ∈ rest, part ≠ dotdot

def pathComponentStep (stack : List Bytes) (part : Bytes) : List Bytes :=
  if part.isEmpty || part == [dot] then stack
  else if part == dotdot then stack.dropLast
  else stack ++ [part]

def resolveLexically (os : Platform) (ops : StringOps) (base : List Bytes) (path : Path) :
    Bytes × List Bytes :=
  let (drive, rest) := splitdrive os ops path
  let stack := if isabspath os path then [] else base
  (drive.bytes, (splitAtSeparators os ops rest true).map (·.bytes) |>.foldl pathComponentStep stack)

/-! Nothing to promise: `_split_longunc`, `_split_longdriveletter`, and `_split_uncpath` are private Windows drive-parser helpers; their observable results are covered by `PathDrivePlatformSpec`.
Nothing to promise: `_split_at_separators` is a private normalization helper; the public path-normalization contract is stated by `NormpathCanonical` and `NormpathLexical`.
Nothing to promise: `longpath` is an internal Windows canonical-case helper with no public docstring.
Nothing to promise: `uripath` declares the generic function before its platform-specific methods and has no body.
Nothing to promise: generated `isdirpath(::AbstractString)`, `splitdir(::AbstractString)`, `splitdrive(::AbstractString)`, `splitext(::AbstractString)`, `normpath(::AbstractString)`, `abspath(::AbstractString)`, and `isabspath(::AbstractString)` wrappers only convert to `String` and dispatch to the corresponding `String` method.
-/

def SplitextDotfileDoc : Prop :=
  ∀ (ops : StringOps) (q r : Bytes), NoSeparators .unix r → NoDots r →
    splitext .unix ops (ops.fromBytes (q ++ dot :: r)) =
      (ops.fromBytes q, ops.fromBytes (dot :: r))

def DirnameBasename : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    splitdir os ops path = (dirname os ops path, basename os ops path) ∧
      NoSeparators os (basename os ops path).bytes ∧
      (path.bytes.getLast? = some (separator os) → (basename os ops path).bytes = []) ∧
      ∃ prePath, path.bytes = prePath ++ (basename os ops path).bytes

def JoinSplitdir : Prop :=
  ∀ (ops : StringOps) (path : Path),
    NoDoubleSeparator .unix path.bytes →
    joinpathStrings .unix ops [dirname .unix ops path, basename .unix ops path] = .ok path

def JoinSplitdirWindowsUnrestricted : Prop :=
  ∀ (ops : StringOps) (path : Path),
    NoDoubleSeparator .windows path.bytes →
    joinpathStrings .windows ops [dirname .windows ops path, basename .windows ops path] = .ok path

def JoinSplitdirWindows : Prop :=
  ∀ (path : Path),
    NoDoubleSeparator .windows path.bytes →
    (splitdrive .windows pathStringOps (basename .windows pathStringOps path)).1.bytes = [] →
    joinpathStrings .windows pathStringOps
      [dirname .windows pathStringOps path, basename .windows pathStringOps path] = .ok path

def SplitextConcat : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    let (stem, extension) := splitext os ops path
    stem.bytes ++ extension.bytes = path.bytes ∧
      (extension.bytes = [] ∨
        (extension.bytes.head? = some dot ∧ NoSeparators os extension.bytes ∧
          NoDots (extension.bytes.drop 1)))

def SplitextHiddenName : Prop :=
  ∀ (ops : StringOps) (rest : Bytes),
    NoSeparators .unix rest → NoDots rest →
    splitext .unix ops (ops.fromBytes (dot :: rest)) =
      (ops.fromBytes (dot :: rest), emptyPath ops)

def NormpathIdempotent : Prop :=
  ∀ (os : Platform) (path : Path),
    normpath os pathStringOps (normpath os pathStringOps path) =
      normpath os pathStringOps path

def PathPartUsesCanonicalSeparators (os : Platform) (path : Path) : Prop :=
  let (_, pathPart) := splitdrive os pathStringOps path
  NoDoubleSeparator os pathPart.bytes ∧
    ∀ byte, byte ∈ pathPart.bytes → isSep os byte = true → byte = separator os

def NormpathCanonical : Prop :=
  ∀ (os : Platform) (path : Path),
    let result := normpath os pathStringOps path
    let parts := (splitAtSeparators os pathStringOps result false).map (·.bytes)
    PathPartUsesCanonicalSeparators os result ∧
      (isabspath os path = true →
        isabspath os result = true ∧
          ∀ part, part ∈ parts → part ≠ [dot] ∧ part ≠ dotdot) ∧
      (isabspath os path = false →
        isabspath os result = false ∧
          (result.bytes = [dot] ∨ ∀ part, part ∈ parts → part ≠ [dot]) ∧
          dotDotPrefix parts)

def NormpathLexical : Prop :=
  ∀ (os : Platform) (base : List Bytes) (path : Path),
    resolveLexically os pathStringOps base (normpath os pathStringOps path) =
      resolveLexically os pathStringOps base path

def NormpathIsdirpath : Prop :=
  ∀ (os : Platform) (path : Path),
    isdirpath os pathStringOps (normpath os pathStringOps path) =
      isdirpath os pathStringOps path


def RelpathRoundtrip : Prop :=
  ∀ (World : Type) (files : FileBindings World)
    (os : Platform) (ops : StringOps) (world after : World)
    (cwd : String) (path startpath relative : Path),
    JuliaLean.base.file.pwd files.ops world = some (.ok (cwd, world)) →
    isabspath os ⟨cwd.toUTF8.toList⟩ = true →
    relpath files.ops os ops path startpath world = some (.ok relative, after) →
      isabspath os relative = false ∧
      (∃ absolutePath absoluteStart joined,
        abspath files.ops os ops path world = some (.ok absolutePath, world) ∧
        abspath files.ops os ops startpath world = some (.ok absoluteStart, world) ∧
        joinpathStrings os ops [absoluteStart, relative] = .ok joined ∧
        normpath os ops joined = absolutePath)

/-- A destination ignores redundant separators and trailing slashes; Windows
drive names are compared with the same case mapping used by `relpath`. -/
def SamePathDestination (os : Platform) (ops : StringOps) (a b : Path) : Prop :=
  let (driveA, componentsA) := resolveLexically os ops [] a
  let (driveB, componentsB) := resolveLexically os ops [] b
  isabspath os a = isabspath os b ∧ componentsA = componentsB ∧
    if os = .windows then
      ∃ drive, ops.uppercase ⟨driveA⟩ = .ok drive ∧ ops.uppercase ⟨driveB⟩ = .ok drive
    else driveA = driveB

def RelpathDestinationRoundtrip : Prop :=
  ∀ (World : Type) (files : FileBindings World)
    (os : Platform) (ops : StringOps) (world after : World)
    (cwd : String) (path startpath relative : Path),
    JuliaLean.base.file.pwd files.ops world = some (.ok (cwd, world)) →
    isabspath os ⟨cwd.toUTF8.toList⟩ = true →
    relpath files.ops os ops path startpath world = some (.ok relative, after) →
      ∃ absolutePath absoluteStart joined,
        abspath files.ops os ops path world = some (.ok absolutePath, world) ∧
        abspath files.ops os ops startpath world = some (.ok absoluteStart, world) ∧
        joinpathStrings os ops [absoluteStart, relative] = .ok joined ∧
        SamePathDestination os ops joined absolutePath

def JoinpathAbsoluteComponent : Prop :=
  ∀ (ops : StringOps) (before absolute : Path),
    isabspath .unix absolute = true →
      joinpathStrings .unix ops [before, absolute] = .ok absolute

theorem joinpathAbsoluteComponent_proven : JoinpathAbsoluteComponent := by
  intro ops before absolute habs
  simp [joinpathStrings, joinpath, joinUnixLoop, joinStep, assertstring, pathValueString,
    bind, Except.bind, habs]

def JoinpathLaws : Prop :=
  (∀ (ops : StringOps) (a b : Path),
    isabspath .unix b = true →
      joinpathStrings .unix ops [a, b] = .ok b) ∧
  (∀ (ops : StringOps) (a b c : Path),
    joinpathStrings .unix ops [a, b, c] =
      joinpathStrings .unix ops [joinStep .unix ops a b, c] ∧
    joinpathStrings .unix ops [joinStep .unix ops a b, c] =
      joinpathStrings .unix ops [a, joinStep .unix ops b c])
theorem findFromNoSeparatorPrefix (p : UInt8 → Bool) (start : Nat)
    (segment suffix : Bytes) (h : ∀ b, b ∈ segment → p b = false) :
    findFrom p start (segment ++ suffix) = findFrom p (start + segment.length) suffix := by
  induction segment generalizing start with
  | nil => simp [findFrom]
  | cons byte segment ih =>
    have hByte : p byte = false := h byte (by simp)
    have hTail : ∀ b, b ∈ segment → p b = false := by
      intro b hb
      apply h b
      simp [hb]
    simp [List.cons_append, findFrom, hByte]
    rw [ih (start + 1) hTail]
    have hIndex : start + 1 + segment.length = start + (segment.length + 1) := by omega
    rw [hIndex]

theorem splitAtBytesConcat (ops : StringOps) (bs : Bytes) (i : Nat) :
    (splitAt ops bs i).1.bytes ++ (splitAt ops bs i).2.bytes = bs := by
  simp [splitAt, ops.fromBytesBytes, List.take_append_drop]

theorem splitLongdriveletterBytesConcat (os : Platform) (ops : StringOps) (path : Path) :
    (splitLongdriveletter os ops path).1.bytes ++ (splitLongdriveletter os ops path).2.bytes = path.bytes := by
  unfold splitLongdriveletter
  by_cases h : (((((6 ≤ path.bytes.length ∧ isSep os (path.bytes[0]?.getD default) = true) ∧
      isSep os (path.bytes[1]?.getD default) = true) ∧ path.bytes[2]?.getD default = 63) ∧
      isSep os (path.bytes[3]?.getD default) = true) ∧ isSep os (path.bytes[4]?.getD default) = false) ∧
      path.bytes[5]?.getD default = colon
  · simp [h, splitAt, ops.fromBytesBytes, List.take_append_drop]
  · simp [h, emptyPath, ops.fromBytesBytes]

theorem splitLonguncBytesConcat (os : Platform) (ops : StringOps) (path : Path) :
    (splitLongunc os ops path).1.bytes ++ (splitLongunc os ops path).2.bytes = path.bytes := by
  unfold splitLongunc
  dsimp [Id.run]
  by_cases hOuter :
      (((((((11 ≤ path.bytes.length ∧ isSep os (path.bytes[0]?.getD default) = true) ∧
          isSep os (path.bytes[1]?.getD default) = true) ∧ path.bytes[2]?.getD default = 63) ∧
          isSep os (path.bytes[3]?.getD default) = true) ∧ path.bytes[4]?.getD default = 85) ∧
          path.bytes[5]?.getD default = 78) ∧ path.bytes[6]?.getD default = 67) ∧
          isSep os (path.bytes[7]?.getD default) = true
  · cases hFind : findAtOrAfter (isSep os) path.bytes 8 with
    | none =>
      simp [hOuter, hFind]
      change (ops.fromBytes []).bytes ++ path.bytes = path.bytes
      simp [ops.fromBytesBytes]
    | some i =>
      by_cases hValid : (i ≥ 9 && path.bytes.length > i + 1 &&
        !isSep os (path.bytes[i + 1]?.getD default)) = true
      · simp [hOuter, hFind, hValid]
        change (ops.fromBytes (List.take ((findAtOrAfter (isSep os) path.bytes (i + 1)).getD path.bytes.length) path.bytes)).bytes ++
          (ops.fromBytes (List.drop ((findAtOrAfter (isSep os) path.bytes (i + 1)).getD path.bytes.length) path.bytes)).bytes = path.bytes
        simp [ops.fromBytesBytes, List.take_append_drop]
      · simp [hOuter, hFind, hValid]
        change (ops.fromBytes []).bytes ++ path.bytes = path.bytes
        simp [ops.fromBytesBytes]
  · simp [hOuter]
    change (ops.fromBytes []).bytes ++ path.bytes = path.bytes
    simp [ops.fromBytesBytes]

theorem splitUncpathBytesConcat (os : Platform) (ops : StringOps) (path : Path) :
    (splitUncpath os ops path).1.bytes ++ (splitUncpath os ops path).2.bytes = path.bytes := by
  unfold splitUncpath
  dsimp [Id.run]
  by_cases hOuter : (5 ≤ path.bytes.length ∧ isSep os (path.bytes[0]?.getD default) = true) ∧
      isSep os (path.bytes[1]?.getD default) = true
  · cases hFind : findAtOrAfter (isSep os) path.bytes 2 with
    | none =>
      simp [hOuter, hFind]
      change (ops.fromBytes []).bytes ++ path.bytes = path.bytes
      simp [ops.fromBytesBytes]
    | some i =>
      by_cases hValid : (i ≥ 3 && path.bytes.length > i + 1 &&
        !isSep os (path.bytes[i + 1]?.getD default)) = true
      · simp [hOuter, hFind, hValid]
        change (ops.fromBytes (List.take ((findAtOrAfter (isSep os) path.bytes (i + 1)).getD path.bytes.length) path.bytes)).bytes ++
          (ops.fromBytes (List.drop ((findAtOrAfter (isSep os) path.bytes (i + 1)).getD path.bytes.length) path.bytes)).bytes = path.bytes
        simp [ops.fromBytesBytes, List.take_append_drop]
      · simp [hOuter, hFind, hValid]
        change (ops.fromBytes []).bytes ++ path.bytes = path.bytes
        simp [ops.fromBytesBytes]
  · simp [hOuter]
    change (ops.fromBytes []).bytes ++ path.bytes = path.bytes
    simp [ops.fromBytesBytes]

theorem splitdriveBytesConcat (os : Platform) (ops : StringOps) (path : Path) :
    (splitdrive os ops path).1.bytes ++ (splitdrive os ops path).2.bytes = path.bytes := by
  cases os with
  | unix => simp [splitdrive, emptyPath, ops.fromBytesBytes]
  | windows =>
    unfold splitdrive
    dsimp [Id.run]
    repeat' split
    all_goals
      first
      | change (splitAt ops path.bytes 2).1.bytes ++ (splitAt ops path.bytes 2).2.bytes = path.bytes
        exact splitAtBytesConcat ops path.bytes 2
      | change (splitLongunc .windows ops path).1.bytes ++ (splitLongunc .windows ops path).2.bytes =
          path.bytes
        exact splitLonguncBytesConcat .windows ops path
      | change (splitLongdriveletter .windows ops path).1.bytes ++
          (splitLongdriveletter .windows ops path).2.bytes = path.bytes
        exact splitLongdriveletterBytesConcat .windows ops path
      | change (splitUncpath .windows ops path).1.bytes ++
          (splitUncpath .windows ops path).2.bytes = path.bytes
        exact splitUncpathBytesConcat .windows ops path
      | change (emptyPath ops).bytes ++ path.bytes = path.bytes
        simp [emptyPath, ops.fromBytesBytes]

theorem findLastFrom_some_ge (p : UInt8 → Bool) :
    ∀ (start : Nat) (bs : Bytes) (i : Nat),
      findLastFrom p start bs = some i → start ≤ i := by
  intro start bs
  induction bs generalizing start with
  | nil => intro i h; simp [findLastFrom] at h
  | cons byte bs ih =>
    intro i h
    simp only [findLastFrom] at h
    cases hTail : findLastFrom p (start + 1) bs with
    | some j =>
      simp [hTail] at h
      have hji : j = i := h
      subst i
      have := ih (start + 1) j hTail
      omega
    | none =>
      simp [hTail] at h
      rcases h with ⟨_, rfl⟩
      omega

theorem findLastFrom_none_allFalse (p : UInt8 → Bool) :
    ∀ (start : Nat) (bs : Bytes), findLastFrom p start bs = none →
      ∀ b, b ∈ bs → p b = false := by
  intro start bs
  induction bs generalizing start with
  | nil => intro h b hb; simp at hb
  | cons byte bs ih =>
    intro h b hb
    simp only [findLastFrom] at h
    cases hTail : findLastFrom p (start + 1) bs with
    | some i => simp [hTail] at h
    | none =>
      have hByte : p byte = false := by simpa [hTail] using h
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hByte
      · exact ih (start + 1) hTail b hb

theorem findLastFrom_suffixFalse (p : UInt8 → Bool) :
    ∀ (start : Nat) (bs : Bytes) (i : Nat),
      findLastFrom p start bs = some i →
      ∀ b, b ∈ bs.drop (i - start + 1) → p b = false := by
  intro start bs
  induction bs generalizing start with
  | nil => intro i h; simp [findLastFrom] at h
  | cons byte bs ih =>
    intro i h b hb
    simp only [findLastFrom] at h
    cases hTail : findLastFrom p (start + 1) bs with
    | some j =>
      simp [hTail] at h
      have hji : j = i := h
      subst i
      have hge : start + 1 ≤ j := findLastFrom_some_ge p (start + 1) bs j hTail
      have hDiff : j - start + 1 = (j - (start + 1) + 1) + 1 := by omega
      have hDrop : (byte :: bs).drop (j - start + 1) = bs.drop (j - (start + 1) + 1) := by
        rw [hDiff]
        simp [List.drop]
      rw [hDrop] at hb
      exact ih (start + 1) j hTail b hb
    | none =>
      simp [hTail] at h
      rcases h with ⟨_, rfl⟩
      have hb' : b ∈ bs := by simpa [List.drop] using hb
      exact (findLastFrom_none_allFalse p (start + 1) bs hTail) b hb'

theorem findFromNoneAllFalse (p : UInt8 → Bool) :
    ∀ (start : Nat) (bs : Bytes),
      findFrom p start bs = none → ∀ b, b ∈ bs → p b = false := by
  intro start bs
  induction bs generalizing start with
  | nil =>
      intro h b hb
      simp at hb
  | cons byte bs ih =>
      intro h b hb
      by_cases hp : p byte
      · simp [findFrom, hp] at h
      · simp [findFrom, hp] at h
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simpa using hp
        · exact ih (start + 1) h b hb

theorem findLastFrom_some_atMatch (p : UInt8 → Bool) :
    ∀ (start : Nat) (bs : Bytes) (i : Nat),
      findLastFrom p start bs = some i →
        ∃ b, (bs.drop (i - start)).head? = some b ∧ p b = true := by
  intro start bs
  induction bs generalizing start with
  | nil =>
      intro i h
      simp [findLastFrom] at h
  | cons byte bs ih =>
      intro i h
      simp only [findLastFrom] at h
      cases hTail : findLastFrom p (start + 1) bs with
      | some j =>
          simp [hTail] at h
          subst i
          have hge : start + 1 ≤ j := findLastFrom_some_ge p (start + 1) bs j hTail
          have hOffset : j - start = (j - (start + 1)) + 1 := by omega
          have hDrop : (byte :: bs).drop (j - start) =
              bs.drop (j - (start + 1)) := by
            rw [hOffset]
            simp [List.drop]
          obtain ⟨b, hHead, hp⟩ := ih (start + 1) j hTail
          exact ⟨b, by simpa [hDrop] using hHead, hp⟩
      | none =>
          simp [hTail] at h
          rcases h with ⟨hp, rfl⟩
          exact ⟨byte, by simp, hp⟩

theorem findLastFrom_lastMatches (p : UInt8 → Bool) :
    ∀ (start : Nat) (bs : Bytes) (last : UInt8),
      bs.getLast? = some last → p last = true →
        findLastFrom p start bs = some (start + bs.length - 1) := by
  intro start bs
  induction bs generalizing start with
  | nil => intro last hLast; simp at hLast
  | cons byte bs ih =>
    intro last hLast hPred
    cases bs with
    | nil =>
      simp at hLast
      subst last
      simp [findLastFrom, hPred]
    | cons next rest =>
      have hTail : (next :: rest).getLast? = some last := by simpa using hLast
      have hResult := ih (start + 1) last hTail hPred
      have hIndex : start + 1 + (next :: rest).length - 1 =
          start + (byte :: next :: rest).length - 1 := by
        simp only [List.length_cons]
        omega
      rw [findLastFrom, hResult]
      exact congrArg some hIndex

theorem findLastNoSeparatorAll (os : Platform) (bs : Bytes)
    (h : findLast (isSep os) bs = none) : NoSeparators os bs := by
  intro b hb
  exact findLastFrom_none_allFalse (isSep os) 0 bs (by simpa [findLast] using h) b hb

theorem findLastLastIndex (p : UInt8 → Bool) (bs : Bytes) (last : UInt8)
    (hLast : bs.getLast? = some last) (hPred : p last = true) :
    findLast p bs = some (bs.length - 1) := by
  simpa [findLast] using findLastFrom_lastMatches p 0 bs last hLast hPred

theorem findLastNoSeparatorSuffix (os : Platform) (bs : Bytes) (i : Nat)
    (h : findLast (isSep os) bs = some i) :
    ∀ b, b ∈ bs.drop (i + 1) → isSep os b = false := by
  simpa [findLast] using findLastFrom_suffixFalse (isSep os) 0 bs i h
theorem splitextConcat_proven : SplitextConcat := by
  intro os ops path
  dsimp [SplitextConcat]
  cases hDrive : splitdrive os ops path with
  | mk drive rest =>
      have hParts : drive.bytes ++ rest.bytes = path.bytes := by
        simpa [hDrive] using splitdriveBytesConcat os ops path
      cases hFind : findLast (fun c => c == dot) rest.bytes with
      | none =>
          simp [splitext, hDrive, hFind, emptyPath, ops.fromBytesBytes]
      | some i =>
          let valid :=
            (findAtOrAfter (isSep os) rest.bytes (i + 1)).isNone &&
              i > 0 && !isSep os rest.bytes[i - 1]!
          by_cases hValid : valid
          · have hSepNone : findAtOrAfter (isSep os) rest.bytes (i + 1) = none := by
              cases hSep : findAtOrAfter (isSep os) rest.bytes (i + 1) with
              | none => rfl
              | some j => simp [valid, hSep] at hValid
            have hNoSepTail : ∀ b, b ∈ rest.bytes.drop (i + 1) → isSep os b = false := by
              intro b hb
              exact findFromNoneAllFalse (isSep os) (i + 1) (rest.bytes.drop (i + 1))
                (by simpa [findAtOrAfter] using hSepNone) b hb
            have hMatch : ∃ b, (rest.bytes.drop i).head? = some b ∧ (b == dot) = true := by
              simpa [findLast] using
                findLastFrom_some_atMatch (fun c => c == dot) 0 rest.bytes i hFind
            obtain ⟨first, hHead, hDot⟩ := hMatch
            have hFirst : first = dot := by simpa using hDot
            have hExtHead : (rest.bytes.drop i).head? = some dot := by
              simpa [hFirst] using hHead
            have hCons : ∃ tail, rest.bytes.drop i = dot :: tail := by
              cases hExt : rest.bytes.drop i with
              | nil => simp [hExt] at hExtHead
              | cons byte tail =>
                  have hByte : byte = dot := by simpa [hExt] using hExtHead
                  subst byte
                  exact ⟨tail, rfl⟩
            obtain ⟨tail, hExt⟩ := hCons
            have hTailEq : tail = rest.bytes.drop (i + 1) := by
              have h := congrArg List.tail hExt
              simpa [List.drop_drop] using h.symm
            have hNoSep : NoSeparators os (rest.bytes.drop i) := by
              intro b hb
              have hb' : b = dot ∨ b ∈ tail := by simpa [hExt] using hb
              cases hb' with
              | inl h => subst b; cases os <;> decide
              | inr h =>
                  rw [hTailEq] at h
                  exact hNoSepTail b h
            have hNoDots : NoDots ((rest.bytes.drop i).drop 1) := by
              intro b hb
              have hDotFalse :=
                findLastFrom_suffixFalse (fun c => c == dot) 0 rest.bytes i
                  (by simpa [findLast] using hFind) b (by
                    simpa [List.drop_drop] using hb)
              intro hEq
              subst b
              simp at hDotFalse
            have hConcat : (drive.bytes ++ rest.bytes.take i) ++ rest.bytes.drop i = path.bytes := by
              calc
                (drive.bytes ++ rest.bytes.take i) ++ rest.bytes.drop i =
                    drive.bytes ++ rest.bytes := by
                      rw [List.append_assoc, List.take_append_drop]
                _ = path.bytes := hParts
            have hValid' :
                ((findAtOrAfter (isSep os) rest.bytes (i + 1)).isNone &&
                  decide (i > 0) && !isSep os rest.bytes[i - 1]!) = true := by
              simpa only [valid] using hValid
            have hSplit : splitext os ops path =
                (ops.fromBytes (drive.bytes ++ rest.bytes.take i),
                  ops.fromBytes (rest.bytes.drop i)) := by
              simp only [splitext, Id.run, hDrive, hFind]
              rw [if_pos hValid']
              rfl
            rw [hSplit]
            simp only [ops.fromBytesBytes]
            exact ⟨hConcat, Or.inr ⟨hExtHead, hNoSep, by simpa using hNoDots⟩⟩
          · have hValid' :
                ¬(((findAtOrAfter (isSep os) rest.bytes (i + 1)).isNone &&
                    decide (i > 0) && !isSep os rest.bytes[i - 1]!) = true) := by
              simpa only [valid] using hValid
            simp only [splitext, Id.run, hDrive, hFind, if_neg hValid']
            change path.bytes ++ (emptyPath ops).bytes = path.bytes ∧
              ((emptyPath ops).bytes = [] ∨
                ((emptyPath ops).bytes.head? = some dot ∧
                  NoSeparators os (emptyPath ops).bytes ∧
                    NoDots ((emptyPath ops).bytes.drop 1)))
            simp [emptyPath, ops.fromBytesBytes]

theorem splitdirNoDriveTailNoSeparator (os : Platform) (ops : StringOps)
    (drive path : Path) :
    NoSeparators os (splitdirNoDrive os ops drive path).2.bytes := by
  unfold splitdirNoDrive
  cases hFind : findLast (isSep os) path.bytes with
  | none =>
    simpa [hFind, isSep, ops.fromBytesBytes] using findLastNoSeparatorAll os path.bytes hFind
  | some i =>
    simpa [NoSeparators, hFind, isSep, ops.fromBytesBytes] using
      findLastNoSeparatorSuffix os path.bytes i hFind

theorem splitdirNoDriveTailEmptyOfTrailingSeparator (os : Platform) (ops : StringOps)
    (drive path : Path) (hLast : path.bytes.getLast? = some (separator os)) :
    (splitdirNoDrive os ops drive path).2.bytes = [] := by
  have hSepByte : isseparatorByte os (separator os) = true := by
    cases os <;> simp [separator, isseparatorByte]
  have hSep : isSep os (separator os) = true := by simpa [isSep] using hSepByte
  unfold splitdirNoDrive
  cases hFind : findLast (isSep os) path.bytes with
  | none =>
    have hNo := findLastNoSeparatorAll os path.bytes hFind (separator os)
      (List.mem_of_getLast? hLast)
    rw [hSepByte] at hNo
    simp at hNo
  | some i =>
    have hLastIndex := findLastLastIndex (isSep os) path.bytes (separator os) hLast hSep
    have hi : i = path.bytes.length - 1 := Option.some.inj (hFind.symm.trans hLastIndex)
    have hLength : 0 < path.bytes.length := by
      cases hBytes : path.bytes with
      | nil => simp [hBytes] at hLast
      | cons byte rest => simp
    have hDropIndex : i + 1 = path.bytes.length := by omega
    simp [hFind, hDropIndex, ops.fromBytesBytes]


theorem dirnameBasename_proven : DirnameBasename := by
  intro os ops path
  cases hDrive : splitdrive os ops path with
  | mk drive rest =>
    have hParts : drive.bytes ++ rest.bytes = path.bytes := by
      simpa [hDrive] using splitdriveBytesConcat os ops path
    have hBase :
        (basename os ops path).bytes =
          (splitdirNoDrive os ops drive rest).2.bytes := by
      simp [basename, splitdir, hDrive]
    have hBaseNo : NoSeparators os (basename os ops path).bytes := by
      rw [hBase]
      exact splitdirNoDriveTailNoSeparator os ops drive rest
    refine ⟨rfl, hBaseNo, ?_, ?_⟩
    · intro hLast
      by_cases hRest : rest.bytes = []
      · have hEmpty : (splitdirNoDrive os ops drive rest).2.bytes = [] := by
          simp [splitdirNoDrive, findLast, findLastFrom, hRest, ops.fromBytesBytes]
        simpa [hBase] using hEmpty
      · have hPathLast : (drive.bytes ++ rest.bytes).getLast? = some (separator os) := by
          rw [← hParts] at hLast
          exact hLast
        have hRestLast : rest.bytes.getLast? = some (separator os) := by
          simpa [List.getLast?_append, hRest] using hPathLast
        have hEmpty := splitdirNoDriveTailEmptyOfTrailingSeparator os ops drive rest hRestLast
        simpa [hBase] using hEmpty
    · cases hFind : findLast (isSep os) rest.bytes with
      | none =>
        refine ⟨drive.bytes, ?_⟩
        rw [hBase]
        unfold splitdirNoDrive
        simp [hFind, ops.fromBytesBytes]
        exact hParts.symm
      | some i =>
        refine ⟨drive.bytes ++ rest.bytes.take (i + 1), ?_⟩
        rw [hBase]
        unfold splitdirNoDrive
        simp [hFind, ops.fromBytesBytes]
        exact hParts.symm

def ExpanduserDoc : Prop :=
  ∀ (os : Platform) (ops : StringOps) (fs : FileSystemOps),
    (∀ path, path.bytes.head? ≠ some tilde →
      expanduser os ops fs path = .ok path) ∧
    (∀ suffix home,
      (suffix = [] ∨ suffix.head?.map (isseparatorByte os) = some true) →
      fs.homedir () = .ok home →
      let homeBytes := if os == .windows && !suffix.isEmpty then
        replaceSeparators os home.bytes suffix.head! else home.bytes
      expanduser os ops fs (ops.fromBytes (tilde :: suffix)) =
        .ok (ops.fromBytes (homeBytes ++ suffix))) ∧
    (∀ user rest home, os = .unix → user ≠ [] → NoSeparators .unix user →
      ops.validUsername (ops.fromBytes user) = .ok true →
      (rest = [] ∨ rest.head?.map (isseparatorByte .unix) = some true) →
      fs.homedirUser (ops.fromBytes user) = some home →
      expanduser os ops fs (ops.fromBytes ((tilde :: user) ++ rest)) =
        .ok (ops.fromBytes (home.bytes ++ rest))) ∧
    (∀ user rest, os = .unix → user ≠ [] → NoSeparators .unix user →
      (rest = [] ∨ rest.head?.map (isseparatorByte .unix) = some true) →
      (ops.validUsername (ops.fromBytes user) = .ok false ∨
        (ops.validUsername (ops.fromBytes user) = .ok true ∧
          fs.homedirUser (ops.fromBytes user) = none)) →
      expanduser os ops fs (ops.fromBytes ((tilde :: user) ++ rest)) =
        .ok (ops.fromBytes ((tilde :: user) ++ rest))) ∧
    (∀ user rest, os = .windows → user ≠ [] → NoSeparators .windows user →
      (rest = [] ∨ rest.head?.map (isseparatorByte .windows) = some true) →
      expanduser os ops fs (ops.fromBytes ((tilde :: user) ++ rest)) =
        .ok (ops.fromBytes ((tilde :: user) ++ rest)))


def AbspathLaws : Prop :=
  ∀ (World : Type) (files : FileBindings World)
    (os : Platform) (ops : StringOps) (world after : World)
    (cwd : String) (path absolute : Path),
    JuliaLean.base.file.pwd files.ops world = some (.ok (cwd, after)) →
    isabspath os ⟨cwd.toUTF8.toList⟩ = true →
    abspath files.ops os ops path world = some (.ok absolute, after) →
      isabspath os absolute = true ∧
      abspath files.ops os ops absolute after = some (.ok absolute, after)
def PathDrivePlatformSpec : Prop :=
  (∀ (ops : StringOps) (path : Path),
    (splitdrive .unix ops path).1.bytes = [] ∧
      (splitdrive .unix ops path).2.bytes = path.bytes) ∧
  (∀ (ops : StringOps) (byte : UInt8) (suffix : Bytes),
    isSep .windows byte = false → byte.toNat < 128 →
    splitdrive .windows ops (ops.fromBytes ([byte, colon] ++ suffix)) =
      (ops.fromBytes [byte, colon], ops.fromBytes suffix))

def WindowsAbsoluteDriveShape (bytes : Bytes) : Prop :=
  match findAtOrAfter (isSep .windows) bytes 0 with
  | none => False
  | some firstSeparator =>
      firstSeparator ≥ 2 ∧ bytes[firstSeparator - 1]! = colon ∧
        (bytes.take (firstSeparator - 1)).all isdriveletter = true

def IsabspathDoc : Prop :=
  ∀ (os : Platform) (path : Path),
    isabspath os path = true ↔
      path.bytes.head?.map (isSep os) = some true ∨
        (os = .windows ∧ WindowsAbsoluteDriveShape path.bytes)

def IsdirpathDoc : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    isdirpath os ops path = true ↔
      let last := lastPathComponent os ops path
      (last = [] ∨ last = [dot]) ∨ last = dotdot

def JoinpathDriveReset : Prop :=
  ∀ (ops : StringOps) (before suffix beforeLower suffixLower : Path),
    let beforeDrive := (splitdrive .windows ops before).1
    let beforePath := (splitdrive .windows ops before).2
    let suffixDrive := (splitdrive .windows ops suffix).1
    let suffixPath := (splitdrive .windows ops suffix).2
    suffixDrive.bytes ≠ [] →
    ops.lowercase suffixDrive = .ok suffixLower →
    ops.lowercase beforeDrive = .ok beforeLower →
    beforeLower.bytes ≠ suffixLower.bytes →
      joinWindowsLoop ops [PathValue.string suffix] beforeDrive beforePath (emptyPath ops) =
        .ok (suffixDrive, suffixPath, suffixPath)

theorem path18_bind_ok {E α β : Type} (a : α) (f : α → Except E β) :
    ((.ok a : Except E α) >>= f) = f a := rfl

theorem joinpathDriveReset_proven : JoinpathDriveReset := by
  intro ops before suffix beforeLower suffixLower
  dsimp
  intro hSuffix hSuffixLower hBeforeLower hDrive
  have hRaw : (splitdrive .windows ops suffix).1.bytes ≠
      (splitdrive .windows ops before).1.bytes := by
    intro hBytes
    have hPaths : (splitdrive .windows ops suffix).1 =
        (splitdrive .windows ops before).1 := by
      cases hBefore : (splitdrive .windows ops before).1 with
      | mk beforeBytes =>
        cases hSuffixPath : (splitdrive .windows ops suffix).1 with
        | mk suffixBytes => simp_all
    rw [hPaths, hBeforeLower] at hSuffixLower
    have hLower := Except.ok.inj hSuffixLower
    exact hDrive (congrArg Path.bytes hLower)
  simp [joinWindowsLoop, assertstring, pathValueString, path18_bind_ok,
    hSuffix, hRaw, hSuffixLower, hBeforeLower, Ne.symm hDrive]

/-- The source discards preceding components at an absolute component, and on
Windows also when the new component has a different case-insensitive drive. -/
def JoinpathDocumentedReset : Prop :=
  JoinpathAbsoluteComponent ∧ JoinpathDriveReset ∧
  ∀ (ops : StringOps) (before suffix : Path),
    let suffixDrive := (splitdrive .windows ops suffix).1
    let suffixPath := (splitdrive .windows ops suffix).2
    suffixPath.bytes.isEmpty = false →
    isSep .windows suffixPath.bytes.head! = true →
      joinWindowsLoop ops [PathValue.string suffix]
        (splitdrive .windows ops before).1 (splitdrive .windows ops before).2 (emptyPath ops) =
        .ok (suffixDrive, suffixPath, suffixPath)

set_option maxRecDepth 4096 in
theorem joinpathDocumentedReset_proven : JoinpathDocumentedReset := by
  refine ⟨joinpathAbsoluteComponent_proven, joinpathDriveReset_proven, ?_⟩
  intro ops before suffix
  dsimp
  intro hnonempty hseparator
  have hnonempty' : (splitdrive .windows ops suffix).2.bytes ≠ [] := by
    simpa using hnonempty
  by_cases hsuffix : (splitdrive .windows ops suffix).1.bytes = []
  · by_cases hbefore : (splitdrive .windows ops before).1.bytes = []
    · have heq : (splitdrive .windows ops before).1 = (splitdrive .windows ops suffix).1 := by
        cases h₁ : (splitdrive .windows ops before).1
        cases h₂ : (splitdrive .windows ops suffix).1
        simp_all
      simp [joinWindowsLoop, assertstring, pathValueString, bind, Except.bind, pure, Except.pure,
        hnonempty', hseparator, hsuffix, hbefore, heq]
    · simp [joinWindowsLoop, assertstring, pathValueString, bind, Except.bind, pure, Except.pure,
        hnonempty', hseparator, hsuffix, hbefore]
  · simp [joinWindowsLoop, assertstring, pathValueString, bind, Except.bind, pure, Except.pure,
      hnonempty', hseparator, hsuffix]

def HomedirUserSpec : Prop :=
  ∀ (os : Platform) (ops : StringOps) (fs : FileSystemOps) (username home : Path),
    (os = .unix → fs.homedirUser username = none →
      homedirUsername os ops fs username = .ok none) ∧
    (os = .unix → fs.homedirUser username = some home →
      homedirUsername os ops fs username = .ok (some home)) ∧
    (os = .windows → fs.currentUser () = some username → fs.homedir () = .ok home →
      homedirUsername os ops fs username = .ok (some home))

theorem homedirUserSpec_proven : HomedirUserSpec := by
  intro os ops fs username home
  constructor
  · intro hos huser
    simp [homedirUsername, hos, huser, pure, Except.pure]
  constructor
  · intro hos huser
    simp [homedirUsername, hos, huser, pure, Except.pure]
  · intro hos hcurrent hhome
    simp [homedirUsername, hos, hcurrent, hhome, Functor.map, Except.map]

def ContractuserDoc : Prop :=
  ∀ (os : Platform) (ops : StringOps) (fs : FileSystemOps) (path home : Path)
    (prefixBytes suffixBytes : Bytes) (later : List (Bytes × Bytes)),
    fs.homedir () = .ok home → fs.ispath home = true →
    fs.samefile path home = false →
    contractuserPairs os path.bytes = (prefixBytes, suffixBytes) :: later →
    fs.ispath (ops.fromBytes prefixBytes) = true →
    fs.samefile (ops.fromBytes prefixBytes) home = true →
      contractuser os ops fs path = .ok (ops.fromBytes (tilde :: suffixBytes))

theorem contractuserDoc_proven : ContractuserDoc := by
  intro os ops fs path home prefixBytes suffixBytes later hHome hHomeExists hPathNotHome hPairs hPrefixExists hPrefixSame
  simp only [StringOps.fromBytesContent] at hPrefixExists hPrefixSame
  simp [contractuser, contractuserLoop, bind, Except.bind, pure, Except.pure,
    hHome, hHomeExists, hPathNotHome, hPairs, hPrefixExists, hPrefixSame]

def RealpathLaws (fs : FileSystemOps) : Prop :=
  ∀ path resolved, fs.realpath path = .ok resolved →
    fs.ispath resolved = true ∧ fs.samefile path resolved = true

def RealpathFilesystem : Prop :=
  ∀ fs, RealpathLaws fs →
    ∀ path resolved, fs.realpath path = .ok resolved →
      realpath fs path = .ok resolved ∧
        fs.ispath resolved = true ∧ fs.samefile path resolved = true

theorem realpathFilesystem_proven : RealpathFilesystem := by
  intro fs hfs path resolved h
  exact ⟨by simpa [realpath] using h, hfs path resolved h⟩


theorem isabspathDoc_proven : IsabspathDoc := by
  intro os path
  cases os with
  | unix =>
    cases h : path.bytes with
    | nil => simp [isabspath, h]
    | cons first rest => simp [isabspath, h, isSep, isseparatorByte]
  | windows =>
    cases h : path.bytes with
    | nil => simp [isabspath, h, WindowsAbsoluteDriveShape, findAtOrAfter, findFrom]
    | cons first rest =>
      by_cases hsep : isSep .windows first = true
      · simp [isabspath, h, hsep, WindowsAbsoluteDriveShape, findAtOrAfter, findFrom]
      · cases hfind : findFrom (isSep .windows) 1 rest with
        | none =>
          simp [isabspath, h, hsep, hfind, WindowsAbsoluteDriveShape, findAtOrAfter, findFrom]
        | some firstsep =>
          simp [isabspath, h, hsep, hfind, WindowsAbsoluteDriveShape, findAtOrAfter, findFrom,
            Bool.and_eq_true, List.all_eq_true, and_assoc]

theorem isdirpathDoc_proven : IsdirpathDoc := by
  intro os ops path
  simp [isdirpath, lastPathComponent, or_assoc]
theorem pathDrivePlatformSpec_proven : PathDrivePlatformSpec := by
  constructor
  · intro ops path
    simp [splitdrive, emptyPath, ops.fromBytesBytes]
  · intro ops byte suffix hSep hAscii
    simp [splitdrive, splitAt, ops.fromBytesBytes, hSep, hAscii]


theorem findLastNoDot (i : Nat) (bytes : Bytes) (h : NoDots bytes) :
    findLastFrom (fun c => c == dot) i bytes = none := by
  induction bytes generalizing i with
  | nil => rfl
  | cons byte bytes ih =>
    have hHead : byte ≠ dot := h byte (by simp)
    have hTail : NoDots bytes := by
      intro b hb
      apply h b
      simp [hb]
    simp [findLastFrom, hHead, ih (i + 1) hTail]

theorem splitextHiddenName_proven : SplitextHiddenName := by
  intro ops rest hSep hDots
  have hFind : findLast (fun c => c == dot) (dot :: rest) = some 0 := by
    simp [findLast, findLastFrom, findLastNoDot 1 rest hDots]
  simp [splitext, splitdrive, hFind, ops.fromBytesBytes, emptyPath]

theorem splitextDotfileDoc_refuted : ¬ SplitextDotfileDoc := by
  intro h
  have hSep : NoSeparators .unix [97] := by
    intro byte hb
    have : byte = 97 := by simpa using hb
    subst byte
    decide
  have hDots : NoDots [97] := by
    intro byte hb
    have : byte = 97 := by simpa using hb
    subst byte
    decide
  have hCounter := h pathStringOps [] [97] hSep hDots
  simp [splitext, splitdrive, emptyPath, pathStringOps, findLast, findLastFrom, Id.run, dot] at hCounter
  have hBytes := congrArg (fun result : Path × Path => result.1.bytes) hCounter
  simp at hBytes



/- The model counterexample uses a basename parsed as a drive prefix, which the approved Windows property excludes. -/
theorem joinSplitdirWindowsModelCounterexample : ¬ JoinSplitdirWindowsUnrestricted := by
  intro h
  let path := pathStringOps.fromBytes [47, 67, 58, 102, 111, 111]
  have hNoDouble : NoDoubleSeparator .windows path.bytes := by
    have hPathBytes : path.bytes = [47, 67, 58, 102, 111, 111] := by
      simp [path, pathStringOps]
    rw [hPathBytes]
    simp [NoDoubleSeparator, isseparatorByte, slash, backslash]
  have hDir : dirname .windows pathStringOps path = pathStringOps.fromBytes [47] := by
    simp [dirname, splitdir, splitdrive, splitdirNoDrive, findLast, findLastFrom,
      path, pathStringOps, emptyPath, isSep, isseparatorByte, separator, slash, backslash, colon]
  have hBase :
      basename .windows pathStringOps path =
        pathStringOps.fromBytes [67, 58, 102, 111, 111] := by
    simp [basename, splitdir, splitdrive, splitdirNoDrive, findLast, findLastFrom,
      path, pathStringOps, emptyPath, isSep, isseparatorByte, separator, slash, backslash, colon]
  have hDriveDir :
      splitdrive .windows pathStringOps (pathStringOps.fromBytes [47]) =
        (pathStringOps.fromBytes [], pathStringOps.fromBytes [47]) := by
    simp [splitdrive, splitAt, pathStringOps, emptyPath, isSep, isseparatorByte,
      separator, slash, backslash, colon]
  have hDriveBase :
      splitdrive .windows pathStringOps (pathStringOps.fromBytes [67, 58, 102, 111, 111]) =
        (pathStringOps.fromBytes [67, 58], pathStringOps.fromBytes [102, 111, 111]) := by
    simp [splitdrive, splitAt, pathStringOps, emptyPath, isSep, isseparatorByte,
      separator, slash, backslash, colon]
  have hSuffixDrive :
      (splitdrive .windows pathStringOps (pathStringOps.fromBytes [67, 58, 102, 111, 111])).1.bytes ≠
        [] := by
    rw [hDriveBase]
    simp [pathStringOps]
  have hLoop := joinpathDriveReset_proven pathStringOps
    (pathStringOps.fromBytes [47]) (pathStringOps.fromBytes [67, 58, 102, 111, 111])
    (pathStringOps.fromBytes []) (pathStringOps.fromBytes [99, 58])
    hSuffixDrive (by rw [hDriveBase]; rfl) (by rw [hDriveDir]; rfl) (by decide)
  have hLoop' := hLoop
  rw [hDriveDir, hDriveBase] at hLoop'
  have hLoopFinal : joinWindowsLoop pathStringOps
      [PathValue.string (pathStringOps.fromBytes [67, 58, 102, 111, 111])]
      (pathStringOps.fromBytes []) (pathStringOps.fromBytes [47]) (pathStringOps.fromBytes []) =
        .ok (pathStringOps.fromBytes [67, 58], pathStringOps.fromBytes [102, 111, 111],
          pathStringOps.fromBytes [102, 111, 111]) := by
    simpa [emptyPath] using hLoop'
  have hJoin := h pathStringOps path hNoDouble
  simp only [joinpathStrings, List.map] at hJoin
  rw [hDir, hBase] at hJoin
  simp only [StringOps.fromBytesContent] at hDriveDir hDriveBase hLoopFinal
  have hActual : joinpathStrings .windows pathStringOps
      [pathStringOps.fromBytes [47], pathStringOps.fromBytes [67, 58, 102, 111, 111]] =
        .ok (pathStringOps.fromBytes [67, 58, 102, 111, 111]) := by
    simp [joinpathStrings, joinpath, assertstring, pathValueString, bind, Except.bind,
      pure, Except.pure, hDriveDir, hDriveBase, hLoopFinal, appendPath, emptyPath,
      pathStringOps.fromBytesBytes, isSep, isseparatorByte, separator, slash, backslash, colon]
  simp only [joinpathStrings, List.map] at hActual
  rw [hActual] at hJoin
  injection hJoin with hPath
  have hBytes := congrArg Path.bytes hPath
  have hFalse : False := by simpa [path, pathStringOps] using hBytes
  exact hFalse.elim

theorem noDoubleSeparatorSuffix (os : Platform) :
    ∀ (prePath suffix : Bytes),
      NoDoubleSeparator os (prePath ++ suffix) → NoDoubleSeparator os suffix := by
  intro prePath
  induction prePath with
  | nil =>
    intro suffix h
    simpa using h
  | cons byte prePath ih =>
    intro suffix h
    cases prePath with
    | nil =>
      cases suffix with
      | nil => trivial
      | cons next rest => exact h.2
    | cons next rest => exact ih suffix h.2

theorem bytesNilOrConcat : ∀ bs : Bytes,
    bs = [] ∨ ∃ pre last, bs = pre ++ [last]
  | [] => Or.inl rfl
  | byte :: rest => by
      rcases bytesNilOrConcat rest with hNil | ⟨pre, last, hConcat⟩
      · subst rest
        exact Or.inr ⟨[], byte, by simp⟩
      · exact Or.inr ⟨byte :: pre, last, by simp [hConcat]⟩

theorem path_eq_of_bytes_eq {p q : Path} (h : p.bytes = q.bytes) : p = q := by
  cases p with
  | mk pBytes =>
    cases q with
    | mk qBytes =>
      simpa using h

theorem joinSplitdir_proven : JoinSplitdir := by
  intro ops path hNoDouble
  let parts := splitdirNoDrive .unix ops (emptyPath ops) path
  have hParts : splitdir .unix ops path = parts := by
    simp [parts, splitdir, splitdrive]
  have hDir : dirname .unix ops path = parts.1 := by
    simp [dirname, hParts]
  have hBase : basename .unix ops path = parts.2 := by
    simp [basename, hParts]
  have hBaseNo : NoSeparators .unix parts.2.bytes :=
    splitdirNoDriveTailNoSeparator .unix ops (emptyPath ops) path
  have hBaseAbs : isabspath .unix parts.2 = false := by
    cases hBaseBytes : parts.2.bytes with
    | nil => simp [isabspath, hBaseBytes]
    | cons first rest =>
      have hFirstNo : isseparatorByte .unix first = false :=
        hBaseNo first (by simp [hBaseBytes])
      have hFirstSep : isSep .unix first = false := by
        simpa [isSep] using hFirstNo
      simp [isabspath, hBaseBytes, hFirstSep]
  have hJoinPath : joinpath .unix ops
      [PathValue.string parts.1, PathValue.string parts.2] =
        .ok (joinStep .unix ops parts.1 parts.2) := by
    rfl
  cases hFind : findLast (isSep .unix) path.bytes with
  | none =>
    have hPathNo : NoSeparators .unix path.bytes :=
      findLastNoSeparatorAll .unix path.bytes hFind
    have hPathAbs : isabspath .unix path = false := by
      cases hPathBytes : path.bytes with
      | nil => simp [isabspath, hPathBytes]
      | cons first rest =>
        have hFirstNo : isseparatorByte .unix first = false :=
          hPathNo first (by simp [hPathBytes])
        have hFirstSep : isSep .unix first = false := by
          simpa [isSep] using hFirstNo
        simp [isabspath, hPathBytes, hFirstSep]
    have hParts' : parts = (emptyPath ops, path) := by
      simp [parts, splitdirNoDrive, hFind]
    have hJoinStep : joinStep .unix ops parts.1 parts.2 = path := by
      apply path_eq_of_bytes_eq
      rw [hParts']
      simp [joinStep, hPathAbs, appendPath, emptyPath, ops.fromBytesBytes]
    rw [hDir, hBase]
    simp only [joinpathStrings, List.map]
    rw [hJoinPath, hJoinStep]
  | some i =>
    let prePath := path.bytes.take i
    let tail := path.bytes.drop (i + 1)
    have hFindFrom : findLastFrom (isSep .unix) 0 path.bytes = some i := by
      simpa [findLast] using hFind
    have hMatch : ∃ byte, (path.bytes.drop i).head? = some byte ∧
        isSep .unix byte = true := by
      simpa using
        (findLastFrom_some_atMatch (isSep .unix) 0 path.bytes i hFindFrom)
    obtain ⟨byte, hHead, hSep⟩ := hMatch
    have hByte : byte = slash := by
      simpa [isSep, isseparatorByte] using hSep
    have hDrop : path.bytes.drop i = slash :: tail := by
      cases hDrop : path.bytes.drop i with
      | nil => simp [hDrop] at hHead
      | cons first rest =>
        have hFirst : first = slash := by simpa [hDrop, hByte] using hHead
        subst first
        have hRest : rest = tail := by
          have h := congrArg (List.drop 1) hDrop
          simpa [tail, List.drop_drop] using h.symm
        simp [hDrop, hRest]
    have hDecomp : path.bytes = prePath ++ slash :: tail := by
      calc
        path.bytes = path.bytes.take i ++ path.bytes.drop i :=
          (List.take_append_drop i path.bytes).symm
        _ = prePath ++ slash :: tail := by simp [prePath, hDrop]
    have hBaseBytes : parts.2.bytes = tail := by
      simp [parts, splitdirNoDrive, hFind, tail, ops.fromBytesBytes]
    have hDirBytes :
        parts.1.bytes = if prePath = [] then [slash] else prePath := by
      by_cases hPrefix : prePath = []
      · have hPath : path.bytes = slash :: tail := by
          simpa [hPrefix] using hDecomp
        have hDirTake : parts.1.bytes = path.bytes.take 1 := by
          simp [parts, splitdirNoDrive, findLast, hFindFrom, findLastFrom,
            prePath, hPrefix, emptyPath, ops.fromBytesBytes]
        rw [if_pos hPrefix, hDirTake]
        simpa [hPath]
      · rcases bytesNilOrConcat prePath with hNil | ⟨pre, last, hPrefixLast⟩
        · exact False.elim (hPrefix hNil)
        · have hPathSplit : path.bytes = pre ++ last :: slash :: tail := by
            rw [hDecomp, hPrefixLast]
            simp [List.append_assoc]
          have hSuffixNo : NoDoubleSeparator .unix (last :: slash :: tail) := by
            rw [hPathSplit] at hNoDouble
            exact noDoubleSeparatorSuffix .unix pre (last :: slash :: tail) hNoDouble
          have hSlash : isseparatorByte .unix slash = true := by
            simp [isseparatorByte, slash]
          have hLastByteNo : isseparatorByte .unix last = false := by
            simpa [hSlash] using hSuffixNo.1
          have hLastSepNo : isSep .unix last = false := by
            simpa [isSep] using hLastByteNo
          have hLastPred : (fun byte => !isSep .unix byte) last = true := by
            simp [hLastSepNo]
          have hLastIndex :
              findLast (fun byte => !isSep .unix byte) prePath =
                some (prePath.length - 1) :=
            findLastLastIndex (fun byte => !isSep .unix byte) prePath last
              (by simp [hPrefixLast]) hLastPred
          have hTakePrefix : path.bytes.take prePath.length = prePath := by
            rw [hDecomp]
            simp [List.take_append]
          have hIndex : prePath.length - 1 + 1 = prePath.length := by
            have hPositive : 0 < prePath.length := by simp [hPrefixLast]
            omega
          rw [if_neg hPrefix]
          calc
            parts.1.bytes = path.bytes.take (prePath.length - 1 + 1) := by
              simp [parts, splitdirNoDrive, hFind, hLastIndex, emptyPath,
                ops.fromBytesBytes, prePath, hIndex]
            _ = prePath := by rw [hIndex, hTakePrefix]
    have hJoinStep : joinStep .unix ops parts.1 parts.2 = path := by
      by_cases hPrefix : prePath = []
      · apply path_eq_of_bytes_eq
        simp [joinStep, hBaseAbs, hDirBytes, hPrefix, hBaseBytes, appendPath,
          separator, slash, ops.fromBytesBytes, hDecomp]
      · rcases bytesNilOrConcat prePath with hNil | ⟨pre, last, hPrefixLast⟩
        · exact False.elim (hPrefix hNil)
        · have hPathSplit : path.bytes = pre ++ last :: slash :: tail := by
            rw [hDecomp, hPrefixLast]
            simp [List.append_assoc]
          have hSuffixNo : NoDoubleSeparator .unix (last :: slash :: tail) := by
            rw [hPathSplit] at hNoDouble
            exact noDoubleSeparatorSuffix .unix pre (last :: slash :: tail) hNoDouble
          have hLastByteNo : isseparatorByte .unix last = false := by
            have hSlash : isseparatorByte .unix slash = true := by
              simp [isseparatorByte, slash]
            simpa [hSlash] using hSuffixNo.1
          have hDirNotEmpty : parts.1.bytes.isEmpty = false := by
            rw [hDirBytes]
            simp [hPrefix]
          have hLastNotSlash : last ≠ slash := by
            intro heq
            have hLastByteYes : isseparatorByte .unix last = true := by
              rw [heq]
              simp [isseparatorByte, slash]
            rw [hLastByteYes] at hLastByteNo
            cases hLastByteNo
          have hDirLastValue : parts.1.bytes.getLast? = some last := by
            rw [hDirBytes]
            simp [hPrefix, hPrefixLast]
          have hDirLastBool :
              (parts.1.bytes.getLast? == some (separator .unix)) = false := by
            rw [hDirLastValue]
            have hLastNotSep : last ≠ separator .unix := by
              change last ≠ slash
              exact hLastNotSlash
            simp [hLastNotSep]
          have hJoinCond :
              (parts.1.bytes.isEmpty ||
                parts.1.bytes.getLast? == some (separator .unix)) = false := by
            rw [hDirNotEmpty, hDirLastBool]
            rfl
          apply path_eq_of_bytes_eq
          unfold joinStep
          rw [if_neg (by simp [hBaseAbs])]
          rw [if_neg (by simp [hJoinCond])]
          simp [appendPath, hBaseBytes, hDirBytes, hPrefix, separator, slash,
            ops.fromBytesBytes, hDecomp]
    rw [hDir, hBase]
    simp only [joinpathStrings, List.map]
    rw [hJoinPath, hJoinStep]

namespace Round4

open JuliaLean JuliaLean.base.path

/-- A bound on all byte and index arithmetic used by these String contracts. -/
def FitsPath (path : Path) : Prop := path.bytes.length + 8 < 2 ^ 62

def NoSeparatorBytes (os : Platform) (bytes : List UInt8) : Prop :=
  ∀ byte ∈ bytes, isseparatorByte os byte = false

/-- Absolute String inputs terminate without changing world state and retain their normalized destination.
Julia source: base/path.jl:613-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/path.jl:597-612; doc/src/base/file.md:63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AbspathAbsoluteInputCorrect : Prop :=
  ∀ (World : Type) (files : FileBindings World) (os : Platform) (ops : StringOps)
    (path : Path) (world : World), FitsPath path → isabspath os path = true →
    ∃ result,
      JuliaLean.base.path.abspath files.ops os ops path world = some (.ok result, world) ∧
      isabspath os result = true ∧
      normpath os ops result = result ∧
      JuliaLean.Proofs.base.path.resolveLexically os ops [] result =
        JuliaLean.Proofs.base.path.resolveLexically os ops [] path

/-- Byte strings may contain malformed UTF-8 and embedded NULs: these are lexical
path operations, so no filesystem-path encoding precondition is imposed. -/
def WithinJuliaStringSize (path : Path) : Prop :=
  path.bytes.length < 2 ^ 62

/-- The aggregate includes every input byte and one possible separator per component.
It bounds both the source collection indices and any joined String length. -/
def WithinJuliaComponentSize (parts : List Path) : Prop :=
  parts.length + (parts.map (fun part => part.bytes.length)).sum < 2 ^ 62

def NoPathSeparators (os : Platform) (bytes : List UInt8) : Prop :=
  ∀ byte ∈ bytes,
    byte ≠ slash ∧ (os = .windows → byte ≠ backslash)

def RootComponent (os : Platform) (bytes : List UInt8) : Prop :=
  bytes = [slash] ∨ (os = .windows ∧ bytes = [backslash])

/-- A list of individual path components. The first may include its drive and
root; later components are nonempty names rather than new roots or drive paths.
A bare drive cannot precede another component because it would be joined to that
component without creating a distinct component. The empty path has one empty
component. This is a predicate on supplied bytes, never on splitpath's output. -/
def JoinableComponents (os : Platform) (ops : StringOps) (parts : List Path) : Prop :=
  parts = [⟨[]⟩] ∨
    match parts with
    | [] => False
    | first :: rest =>
        first.bytes ≠ [] ∧
        (if os = .unix then
          RootComponent .unix first.bytes ∨ NoPathSeparators .unix first.bytes
        else
          let (drive, tail) := splitdrive .windows ops first
          (drive.bytes = [] ∧
            (RootComponent .windows first.bytes ∨ NoPathSeparators .windows first.bytes)) ∨
          (drive.bytes ≠ [] ∧
            (RootComponent .windows tail.bytes ∨
              (tail.bytes ≠ [] ∧ NoPathSeparators .windows tail.bytes) ∨
              (tail.bytes = [] ∧ rest = [])))) ∧
        ∀ part ∈ rest,
          part.bytes ≠ [] ∧ NoPathSeparators os part.bytes ∧
            (os = .unix ∨ (splitdrive .windows ops part).1.bytes = [])

/-- Grammar spelling, not a second joinpath algorithm. It only spells a sequence
of individual components with the platform delimiter, preserving any root already
contained in its first component. It contains no reset, validation, case-mapping,
or error-processing branch. Its sole use is defining the input spelling domain. -/
def ComponentSpelling (os : Platform) (ops : StringOps) (parts : List Path) : List UInt8 :=
  match parts with
  | [] => []
  | first :: rest =>
      let firstTail := (splitdrive os ops first).2.bytes
      let suffix := List.intercalate [separator os] (rest.map (fun part => part.bytes))
      if firstTail == [slash] || (os == .windows && firstTail == [backslash]) then
        first.bytes ++ suffix
      else if rest.isEmpty then first.bytes
      else first.bytes ++ [separator os] ++ suffix

/-- Exact spelling permits a root separator of either Windows kind and preserves
the drive spelling, but separators inserted between names use the platform kind.
Thus foo/bar is excluded on Windows while /foo and /foo\\bar are allowed, so root
spellings that the implementation preserves exactly stay in the domain. -/
def CanonicalJoinSpelling (os : Platform) (ops : StringOps) (path : Path) : Prop :=
  ∃ parts : List Path,
    JoinableComponents os ops parts ∧
      WithinJuliaComponentSize parts ∧ path.bytes = ComponentSpelling os ops parts

/-- Splitting and joining are inverse on individual components and their exact
platform-delimited spelling.
Julia source: base/path.jl:373-411,413-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/path.jl:373-392,489-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027

Both directions quantify over the actual Utf8proc interface. No dummy case table
is substituted and no correctness law is assumed: the input grammar excludes a
later drive/reset branch, so these calls never need case mapping. The first
direction has no premise about splitpath's computed output. The second requires
successful execution, rather than assuming success. Both invoke the installed
source-mirrored splitpath and joinpath definitions.

This is the compositional contract for canonical path/component syntax. It does
not claim to cover arbitrary AbstractString conversions or arbitrary-axis
AbstractVector joinpath input, which have separate model gaps.
-/
def SplitpathJoinpathCorrect : Prop :=
  (∀ (os : Platform) (ops : StringOps) (path : Path),
    WithinJuliaStringSize path → CanonicalJoinSpelling os ops path →
      joinpath os ops ((splitpath os ops path).map PathValue.string) = .ok path) ∧
  (∀ (os : Platform) (ops : StringOps) (parts : List Path),
    WithinJuliaComponentSize parts → JoinableComponents os ops parts →
      ∃ path : Path,
        joinpath os ops (parts.map PathValue.string) = .ok path ∧ splitpath os ops path = parts)

/-- Nonempty name components separated by one or more delimiters, optionally
followed by a trailing delimiter run. This is a byte-partition relation, not a
second implementation of the reverse splitdir loop. -/
def NamePartition (os : Platform) (bytes : List UInt8) : List (List UInt8) → Prop
  | [] => bytes = []
  | name :: rest =>
      name ≠ [] ∧ NoSeparatorBytes os name ∧
      ∃ separators suffix,
        (∀ byte ∈ separators, isseparatorByte os byte = true) ∧
        (rest ≠ [] → separators ≠ []) ∧
        bytes = name ++ separators ++ suffix ∧ NamePartition os suffix rest

/-- Empty path, relative names, or a root followed by names; repeated separators
are delimiters and a leading run contributes exactly its first root byte. -/
def ComponentPartition (os : Platform) (bytes : List UInt8)
    (parts : List (List UInt8)) : Prop :=
  (bytes = [] ∧ parts = [[]]) ∨
  (parts ≠ [] ∧ NamePartition os bytes parts) ∨
  ∃ rootRun rootByte suffix names,
    rootRun.head? = some rootByte ∧
    (∀ byte ∈ rootRun, isseparatorByte os byte = true) ∧
    bytes = rootRun ++ suffix ∧ NamePartition os suffix names ∧
    parts = [rootByte] :: names

/-- splitpath returns every component in order, retaining the root and drive,
and ignoring only delimiter multiplicity and trailing delimiters.
Julia source: base/path.jl:395-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/path.jl:373-392; doc/src/base/file.md:73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SplitpathComponentsCorrect : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path), FitsPath path →
    let (drive, tail) := splitdrive os ops path
    ∃ first rest,
      ComponentPartition os tail.bytes (first :: rest) ∧
      (splitpath os ops path).map (fun part => part.bytes) =
        (drive.bytes ++ first) :: rest


end Round4

/-! Property registry -/

end JuliaLean.Proofs.base.path

namespace JuliaLean.ChatGPT.Batch4.Group18

open JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem path18_username_partition (os : Platform) (user suffix : List UInt8)
    (hu : NoSeparators os user)
    (hs : suffix = [] ∨ suffix.head?.map (isseparatorByte os) = some true) :
    (match findFrom (isSep os) 0 (user ++ suffix) with
     | none => user ++ suffix
     | some i => (user ++ suffix).take i) = user ∧
    (match findFrom (isSep os) 0 (user ++ suffix) with
     | none => []
     | some i => (user ++ suffix).drop i) = suffix := by
  have hp : ∀ b, b ∈ user → isSep os b = false := by
    intro b hb
    exact hu b hb
  rw [findFromNoSeparatorPrefix (isSep os) 0 user suffix hp]
  rcases hs with hs | hs
  · subst suffix
    simp only [findFrom, List.append_nil, true_and]
  · cases suffix with
    | nil => simp only [List.head?_nil, Option.map_none, reduceCtorEq] at hs
    | cons first rest =>
      have hsep : isSep os first = true := by simpa only [isSep, List.head?_cons, Option.map_some, Option.some.injEq] using hs
      simp [findFrom, hsep, List.take_append, List.drop_append]

theorem path18_head_cons (a : UInt8) (as : List UInt8) : (a :: as).head! = a := rfl

theorem path18_pure {E α : Type} (a : α) : (pure a : Except E α) = .ok a := rfl

theorem path18_letter_total (ops : StringOps) (c : UInt32) :
    ∃ b, JuliaLean.base.strings.unicode.isletter
      JuliaLean.base.strings.unicode.charOps ops c = .ok b := by
  unfold JuliaLean.base.strings.unicode.isletter
    JuliaLean.base.strings.unicode.category_code_AbstractChar
  split
  · exact ⟨_, rfl⟩
  · unfold JuliaLean.base.strings.unicode.category_code_Integer
    split <;> exact ⟨_, rfl⟩

theorem path18_forIn_total {α β E : Type} (xs : List α)
    (f : α → β → Except E (ForInStep β))
    (hf : ∀ a b, ∃ result, f a b = .ok result) (initial : β) :
    ∃ result, forIn xs initial f = .ok result := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons a xs ih =>
    obtain ⟨step, hs⟩ := hf a initial
    rw [List.forIn_cons, hs]
    cases step with
    | done result => exact ⟨result, rfl⟩
    | yield result => exact ih result

theorem path18_valid_total (ops : StringOps) (path : Path) :
    ∃ b, ops.validUsername path = .ok b := by
  let step : UInt32 → Option Bool × Unit → Except PathError (ForInStep (Option Bool × Unit)) :=
    fun c _ => do
      let letter ← (JuliaLean.base.strings.unicode.isletter
        JuliaLean.base.strings.unicode.charOps ops c).mapError PathError.unicode
      if letter || JuliaLean.base.strings.unicode.isdigit
          JuliaLean.base.strings.unicode.charOps c ||
          c == 0x2e000000 || c == 0x5f000000 || c == 0x2d000000 then
        pure (.yield (none, ()))
      else pure (.done (some false, ()))
  have hs : ∀ c state, ∃ result, step c state = .ok result := by
    intro c state
    obtain ⟨letter, hletter⟩ := path18_letter_total ops c
    dsimp only [step]
    rw [hletter]
    simp only [Except.mapError, path18_bind_ok]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨state, hstate⟩ := path18_forIn_total
    (PathBinding.stringData path).chars step hs (none, ())
  unfold StringOps.validUsername
  dsimp only [step] at hstate
  rw [hstate]
  simp only [path18_bind_ok]
  cases state.1 <;> exact ⟨_, rfl⟩

theorem path18_expand_parsed (os : Platform) (ops : StringOps) (fs : FileSystemOps)
    (user suffix : List UInt8) (hu : NoSeparators os user)
    (hs : suffix = [] ∨ suffix.head?.map (isseparatorByte os) = some true) :
    expanduser os ops fs (ops.fromBytes (tilde :: (user ++ suffix))) = do
      let original := ops.fromBytes (tilde :: (user ++ suffix))
      let username := ops.fromBytes user
      let home ← if user.isEmpty then fs.homedir ()
        else if os == .windows then return original
        else if !(← ops.validUsername username) then return original
        else match ← homedirUsername os ops fs username with
          | none => return original
          | some home => pure home
      let homeBytes := if os == .windows && !suffix.isEmpty then
        replaceSeparators os home.bytes suffix.head! else home.bytes
      return ops.fromBytes (homeBytes ++ suffix) := by
  obtain ⟨huser, hsuffix⟩ := path18_username_partition os user suffix hu hs
  simp only [expanduser, StringOps.fromBytesBytes, List.isEmpty_cons, path18_head_cons,
    bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, List.drop_succ_cons,
    List.drop_zero]
  cases hsep : findFrom (isSep os) 0 (user ++ suffix) <;>
    simp only [hsep] at huser hsuffix ⊢ <;>
    simp only [huser, hsuffix] <;> rfl

theorem path18_homedir_unix (ops : StringOps) (fs : FileSystemOps) (user : Path) :
    homedirUsername .unix ops fs user = .ok (fs.homedirUser user) := by rfl

/-- Tilde expansion preserves unsupported paths and resolves the current or named home. -/
theorem PathsExpanduserDoc_proven : JuliaLean.Proofs.base.path.ExpanduserDoc := by
  intro os ops fs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro path h
    cases path with
    | mk bytes =>
      cases bytes with
      | nil => rfl
      | cons first rest =>
        have hf : first ≠ tilde := by intro he; apply h; rw [he]; rfl
        simp [expanduser, path18_head_cons, hf, pure, Except.pure]
  · intro suffix home hs hh
    have hempty : NoSeparators os [] := by intro b hb; cases hb
    have hparsed := path18_expand_parsed os ops fs [] suffix hempty hs
    simp only [List.nil_append] at hparsed
    rw [hparsed]
    obtain ⟨valid, hvalid⟩ := path18_valid_total ops (ops.fromBytes [])
    rw [hvalid]
    simp only [List.isEmpty_nil, ite_true, path18_bind_ok, hh]
    rfl
  · intro user rest home hos huser hNo hvalid hrest hhome
    subst os
    have hparsed := path18_expand_parsed .unix ops fs user rest hNo hrest
    have he : user.isEmpty = false := List.isEmpty_eq_false_iff.mpr huser
    dsimp only at hparsed
    rw [hvalid] at hparsed
    have hhome' : fs.homedirUser ⟨user⟩ = some home := hhome
    simpa [List.cons_append, path18_homedir_unix, hhome', path18_bind_ok, path18_pure, he] using hparsed
  · intro user rest hos huser hNo hrest hfail
    subst os
    have hparsed := path18_expand_parsed .unix ops fs user rest hNo hrest
    rcases hfail with hbad | ⟨hvalid, hnone⟩
    · have he : user.isEmpty = false := List.isEmpty_eq_false_iff.mpr huser
      dsimp only at hparsed
      rw [hbad] at hparsed
      simpa [List.cons_append, path18_bind_ok, path18_pure, he] using hparsed
    · have he : user.isEmpty = false := List.isEmpty_eq_false_iff.mpr huser
      dsimp only at hparsed
      rw [hvalid] at hparsed
      have hnone' : fs.homedirUser ⟨user⟩ = none := hnone
      simpa [List.cons_append, path18_homedir_unix, hnone', path18_bind_ok, path18_pure, he] using hparsed
  · intro user rest hos huser hNo hrest
    subst os
    have hparsed := path18_expand_parsed .windows ops fs user rest hNo hrest
    obtain ⟨valid, hvalid⟩ := path18_valid_total ops (ops.fromBytes user)
    have he : user.isEmpty = false := List.isEmpty_eq_false_iff.mpr huser
    dsimp only at hparsed
    rw [hvalid] at hparsed
    simpa [List.cons_append, path18_bind_ok, path18_pure, he] using hparsed

open JuliaLean JuliaLean.base.path JuliaLean.Proofs.base.path
open JuliaLean.Proofs.base.path.Round4

/-- A single nonempty name is a byte partition with no delimiters. -/
theorem split_name_single (os : Platform) (name : List UInt8)
    (hne : name ≠ []) (hsep : NoSeparatorBytes os name) :
    NamePartition os name [name] := by
  refine ⟨hne, hsep, [], [], ?_, ?_, ?_, rfl⟩
  · simp only [List.not_mem_nil, false_implies, implies_true]
  · simp only [ne_eq, not_true_eq_false, false_implies]
  · simp only [List.append_nil]

/-- Append a delimiter run and optional final name to a nonempty name partition. -/
theorem split_name_append (os : Platform) (bytes : List UInt8) (names : List (List UInt8))
    (hpart : NamePartition os bytes names) (hnames : names ≠ [])
    (separators tail : List UInt8) (hseps : ∀ byte ∈ separators, isseparatorByte os byte = true)
    (hsepne : separators ≠ []) (htail : NoSeparatorBytes os tail) :
    NamePartition os (bytes ++ separators ++ tail)
      (names ++ if tail = [] then [] else [tail]) := by
  induction names generalizing bytes with
  | nil => exact False.elim (hnames rfl)
  | cons name rest ih =>
    rcases hpart with ⟨hnamene, hname, oldsep, suffix, holdsep, holdne, hbytes, hrest⟩
    cases rest with
    | nil =>
      have hsuffix : suffix = [] := hrest
      subst suffix
      by_cases ht : tail = []
      · subst tail
        simp only [ite_true, List.append_nil]
        refine ⟨hnamene, hname, oldsep ++ separators, [], ?_, ?_, ?_, rfl⟩
        · intro byte hb
          rcases List.mem_append.mp hb with hb | hb
          · exact holdsep byte hb
          · exact hseps byte hb
        · simp only [ne_eq, not_true_eq_false, false_implies]
        · simp only [hbytes, List.append_nil, List.append_assoc]
      · simp only [ht, ↓reduceIte, List.cons_append, List.nil_append]
        refine ⟨hnamene, hname, oldsep ++ separators, tail, ?_, ?_, ?_,
          split_name_single os tail ht htail⟩
        · intro byte hb
          rcases List.mem_append.mp hb with hb | hb
          · exact holdsep byte hb
          · exact hseps byte hb
        · intro _ he
          have := List.append_eq_nil_iff.mp he
          exact hsepne this.2
        · simp only [hbytes, List.append_nil, List.append_assoc]
    | cons next rest =>
      simp only [List.cons_append]
      refine ⟨hnamene, hname, oldsep, suffix ++ separators ++ tail, holdsep, ?_, ?_, ?_⟩
      · intro _
        exact holdne (by intro h; cases h)
      · simp only [hbytes, List.append_assoc]
      · exact ih suffix hrest (by intro h; cases h)

/-- Appending delimiters and an optional final name preserves a nonempty path partition. -/
theorem split_component_append (os : Platform) (bytes : List UInt8) (parts : List (List UInt8))
    (hbytes : bytes ≠ []) (hpart : ComponentPartition os bytes parts)
    (separators tail : List UInt8) (hseps : ∀ byte ∈ separators, isseparatorByte os byte = true)
    (hsepne : separators ≠ []) (htail : NoSeparatorBytes os tail) :
    ComponentPartition os (bytes ++ separators ++ tail)
      (parts ++ if tail = [] then [] else [tail]) := by
  rcases hpart with ⟨hempty, _⟩ | ⟨hnames, hnamespart⟩ | ⟨rootRun, rootByte, suffix, names,
    hroot, hrootsep, hbytespart, hnamespart, hparts⟩
  · exact False.elim (hbytes hempty)
  · apply Or.inr ∘ Or.inl
    refine ⟨?_, split_name_append os bytes parts hnamespart hnames separators tail hseps hsepne htail⟩
    intro h
    exact hnames (List.append_eq_nil_iff.mp h).1
  · apply Or.inr ∘ Or.inr
    by_cases hn : names = []
    · subst names
      have hsuffix : suffix = [] := hnamespart
      subst suffix
      refine ⟨rootRun ++ separators, rootByte, tail,
        (if tail = [] then [] else [tail]), ?_, ?_, ?_, ?_, ?_⟩
      · have hrne : rootRun ≠ [] := by intro h; simp only [h, List.head?_nil] at hroot; cases hroot
        cases rootRun with
        | nil => exact False.elim (hrne rfl)
        | cons first rest => exact hroot
      · intro byte hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hrootsep byte hb
        · exact hseps byte hb
      · simp only [hbytespart, List.append_nil]
      · by_cases ht : tail = []
        · subst tail
          rfl
        · rw [ite_eq_right ht]
          exact split_name_single os tail ht htail
      · simp only [hparts, List.cons_append, List.nil_append]
    · refine ⟨rootRun, rootByte, suffix ++ separators ++ tail,
        names ++ (if tail = [] then [] else [tail]), hroot, hrootsep, ?_, ?_, ?_⟩
      · simp only [hbytespart, List.append_assoc]
      · exact split_name_append os suffix names hnamespart hn separators tail hseps hsepne htail
      · simp only [hparts, List.cons_append]

/-- The final matching byte splits the list into prefix, delimiter and nonmatching suffix. -/
theorem split_findLast_decomp (pred : UInt8 → Bool) (bytes : List UInt8) (index : Nat)
    (h : findLast pred bytes = some index) :
    ∃ pre byte suffix, bytes = pre ++ byte :: suffix ∧ pre.length = index ∧
      pred byte = true ∧ ∀ b ∈ suffix, pred b = false := by
  obtain ⟨byte, hhead, hbyte⟩ := findLastFrom_some_atMatch pred 0 bytes index h
  simp only [Nat.sub_zero] at hhead
  cases hd : bytes.drop index with
  | nil => simp only [hd, List.head?_nil] at hhead; cases hhead
  | cons first suffix =>
    simp only [hd, List.head?_cons, Option.some.injEq] at hhead
    subst first
    have hlen := congrArg List.length hd
    simp only [List.length_drop, List.length_cons] at hlen
    have hlt : index < bytes.length := by omega
    refine ⟨bytes.take index, byte, suffix, ?_, ?_, hbyte, ?_⟩
    · rw [← hd, List.take_append_drop]
    · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
    · have hdrop : bytes.drop (index + 1) = suffix := by
        rw [← List.drop_drop, hd]
        rfl
      intro b hb
      apply findLastFrom_suffixFalse pred 0 bytes index h b
      simpa only [Nat.sub_zero, hdrop] using hb

theorem split_loop_empty (os : Platform) (ops : StringOps) (fuel : Nat) (out : List Path) :
    splitpathLoop os ops fuel ⟨[]⟩ out = out := by
  cases fuel <;> rfl

theorem split_loop_root (os : Platform) (ops : StringOps) (fuel : Nat) (out : List Path)
    (root : UInt8) (hroot : isseparatorByte os root = true) (hfuel : 0 < fuel) :
    splitpathLoop os ops fuel ⟨[root]⟩ out = ⟨[root]⟩ :: out := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [splitpathLoop, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      splitdirNoDrive, findLast, findLastFrom, isSep, hroot, emptyPath,
      StringOps.fromBytes, List.take_zero, Option.getD_none, Nat.zero_add,
      List.take_succ_cons, List.nil_append, List.drop_succ_cons, List.drop_zero,
      List.take_nil, beq_self_eq_true]

/-- The reverse splitdir loop returns a complete, ordered byte partition. -/
theorem split_loop_partition (os : Platform) (ops : StringOps) (fuel : Nat)
    (bytes : List UInt8) (out : List Path) (hne : bytes ≠ []) (hbudget : bytes.length < fuel) :
    ∃ first rest, ComponentPartition os bytes (first :: rest) ∧
      splitpathLoop os ops fuel ⟨bytes⟩ out =
        ((first :: rest).map (fun bs => (⟨bs⟩ : Path))) ++ out := by
  induction fuel generalizing bytes out with
  | zero => omega
  | succ fuel ih =>
    have hisempty : bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
    cases hlast : findLast (isSep os) bytes with
    | none =>
      have hsep : NoSeparatorBytes os bytes := findLastNoSeparatorAll os bytes hlast
      refine ⟨bytes, [], Or.inr (Or.inl ⟨by simp only [ne_eq, List.cons_ne_nil, not_false_eq_true],
        split_name_single os bytes hne hsep⟩), ?_⟩
      simp [splitpathLoop, splitdirNoDrive, hlast, emptyPath, StringOps.fromBytes,
        hisempty, split_loop_empty]
    | some index =>
      obtain ⟨pre, sep, tail, hbytes, hprelen, hsep, htail⟩ :=
        split_findLast_decomp (isSep os) bytes index hlast
      have htake : bytes.take index = pre := by
        rw [hbytes, ← hprelen]
        simp only [List.take_left]
      have hdrop : bytes.drop (index + 1) = tail := by
        rw [hbytes, ← hprelen]
        rw [← List.drop_drop, List.drop_left]
        rfl
      cases hprev : findLast (fun b => !isSep os b) pre with
      | none =>
        have hallpre : ∀ b ∈ pre, isseparatorByte os b = true := by
          intro b hb
          have hh := findLastFrom_none_allFalse (fun b => !isSep os b) 0 pre hprev b hb
          cases hs : isSep os b with
          | false => rw [hs] at hh; cases hh
          | true => exact hs
        have hallrun : ∀ b ∈ pre ++ [sep], isseparatorByte os b = true := by
          intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact hallpre b hb
          · simp only [List.mem_singleton] at hb
            subst b
            exact hsep
        obtain ⟨root, roots, hrootrun⟩ := List.exists_cons_of_ne_nil
          (show pre ++ [sep] ≠ [] from fun h =>
            List.cons_ne_nil sep [] (List.append_eq_nil_iff.mp h).2)
        have hrootsep : isseparatorByte os root = true :=
          hallrun root (by rw [hrootrun]; exact List.mem_cons_self)
        have hbytesrun : bytes = (pre ++ [sep]) ++ tail := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hbytes
        have hdir : splitdirNoDrive os ops (emptyPath ops) ⟨bytes⟩ =
            (⟨[root]⟩, ⟨tail⟩) := by
          simp only [splitdirNoDrive, hlast, htake, hprev, Option.getD_none,
            Nat.zero_add, emptyPath, StringOps.fromBytes, List.nil_append, hdrop]
          rw [hbytesrun, hrootrun]
          rfl
        have hnamepart : NamePartition os tail (if tail = [] then [] else [tail]) := by
          by_cases ht : tail = []
          · rw [ht]
            rfl
          · rw [ite_eq_right ht]
            exact split_name_single os tail ht htail
        refine ⟨[root], (if tail = [] then [] else [tail]),
          Or.inr (Or.inr ⟨pre ++ [sep], root, tail,
            (if tail = [] then [] else [tail]), ?_, hallrun, hbytesrun, hnamepart, rfl⟩), ?_⟩
        · rw [hrootrun]
          rfl
        · simp only [splitpathLoop, hisempty, Bool.false_eq_true, ↓reduceIte, hdir]
          by_cases hsame : [root] = bytes
          · have htailnil : tail = [] := by
              have hl := congrArg List.length hbytesrun
              rw [← hsame, hrootrun] at hl
              simp only [List.length_append, List.length_cons, List.length_nil] at hl
              exact List.eq_nil_of_length_eq_zero (by omega)
            simp only [hsame, beq_self_eq_true, ↓reduceIte, htailnil, List.map_cons,
              List.map_nil, List.nil_append, List.cons_append]
          · rw [beq_eq_false_iff_ne.mpr hsame]
            simp only [Bool.false_eq_true, ↓reduceIte]
            have hfuel : 0 < fuel := by
              have hl := List.length_pos_iff.mpr hne
              omega
            rw [split_loop_root os ops fuel _ root hrootsep hfuel]
            by_cases ht : tail = [] <;>
              simp [ht]
      | some previous =>
        obtain ⟨front, last, between, hpre, hfrontlen, hlastsep, hbetween⟩ :=
          split_findLast_decomp (fun b => !isSep os b) pre previous hprev
        let dir := front ++ [last]
        let separators := between ++ [sep]
        have hdirne : dir ≠ [] := fun h =>
          List.cons_ne_nil last [] (List.append_eq_nil_iff.mp h).2
        have hsepne : separators ≠ [] := fun h =>
          List.cons_ne_nil sep [] (List.append_eq_nil_iff.mp h).2
        have hseparators : ∀ b ∈ separators, isseparatorByte os b = true := by
          intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · have hh := hbetween b hb
            cases hs : isSep os b with
            | false => rw [hs] at hh; cases hh
            | true => exact hs
          · simp only [List.mem_singleton] at hb
            subst b
            exact hsep
        have hdecomp : bytes = dir ++ separators ++ tail := by
          simp only [dir, separators, hbytes, hpre, List.append_assoc, List.cons_append, List.nil_append]
        have hdirlen : dir.length = previous + 1 := by
          simp only [dir, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, hfrontlen]
        have htakeDir : bytes.take (previous + 1) = dir := by
          rw [← hdirlen, hdecomp]
          simp only [List.append_assoc, List.take_left]
        have hdir : splitdirNoDrive os ops (emptyPath ops) ⟨bytes⟩ = (⟨dir⟩, ⟨tail⟩) := by
          simp only [splitdirNoDrive, hlast, htake, hprev, Option.getD_some,
            emptyPath, StringOps.fromBytes, List.nil_append, hdrop, htakeDir]
        have hdirlt : dir.length < bytes.length := by
          have hs := List.length_pos_iff.mpr hsepne
          have hl : bytes.length = dir.length + separators.length + tail.length := by
            rw [hdecomp]
            simp only [List.length_append]
          omega
        obtain ⟨first, rest, hpartition, hloop⟩ := ih dir
          (if tail.isEmpty then out else ⟨tail⟩ :: out) hdirne (by omega)
        refine ⟨first, rest ++ (if tail = [] then [] else [tail]), ?_, ?_⟩
        · rw [hdecomp]
          simpa only [List.cons_append] using
            split_component_append os dir (first :: rest) hdirne hpartition
              separators tail hseparators hsepne htail
        · simp only [splitpathLoop, hisempty, Bool.false_eq_true, ↓reduceIte, hdir]
          have hsame : dir ≠ bytes := by
            intro he
            rw [he] at hdirlt
            exact (Nat.lt_irrefl _) hdirlt
          rw [beq_eq_false_iff_ne.mpr hsame]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hloop]
          by_cases ht : tail = [] <;>
            simp [ht, List.map_append, List.append_assoc]

/-- Every input is split into its drive-prefixed root/name partition. -/
theorem PathsSplitpathComponents_proven :
    JuliaLean.Proofs.base.path.Round4.SplitpathComponentsCorrect := by
  intro os ops path _hfit
  rcases hdrive : splitdrive os ops path with ⟨drive, tail⟩
  dsimp only
  by_cases htail : tail.bytes = []
  · refine ⟨[], [], Or.inl ⟨htail, rfl⟩, ?_⟩
    have heq : tail = (⟨[]⟩ : Path) := path_eq_of_bytes_eq htail
    subst tail
    by_cases hd : drive.bytes = [] <;>
      simp [splitpath, Id.run, hdrive, split_loop_empty, hd, appendPath, StringOps.fromBytes]
  · obtain ⟨first, rest, hpart, hloop⟩ :=
      split_loop_partition os ops (tail.bytes.length + 1) tail.bytes [] htail (by omega)
    refine ⟨first, rest, hpart, ?_⟩
    have hisempty : tail.bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr htail
    by_cases hd : drive.bytes = [] <;>
      simp [splitpath, Id.run, hdrive, hisempty, hloop, hd, appendPath, StringOps.fromBytes,
        List.map_map, Function.comp_def]

end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.ChatGPT.Batch4.Group18

/-! Core path laws -/

open JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- A later differing Windows drive resets the join accumulator. -/
theorem PathJoinpathWindowsDriveReset_proven : JuliaLean.Proofs.base.path.JoinpathDriveReset :=
  JuliaLean.Proofs.base.path.joinpathDriveReset_proven

theorem path18_abs_nil : isabspath .unix ⟨[]⟩ = false := by
  rfl

theorem path18_abs_cons (first : UInt8) (rest : List UInt8) :
    isabspath .unix ⟨first :: rest⟩ = decide (first = slash) := by
  simp [isabspath, isSep, isseparatorByte]

theorem path18_abs_append (a b : List UInt8) (ha : a ≠ []) :
    isabspath .unix ⟨a ++ b⟩ = isabspath .unix ⟨a⟩ := by
  cases a with
  | nil => exact False.elim (ha rfl)
  | cons first rest => simp only [List.cons_append, path18_abs_cons]

theorem path18_join_nil (ops : StringOps) (b : Path) :
    joinStep .unix ops ⟨[]⟩ b = b := by
  cases b with
  | mk bytes =>
    simp [joinStep, appendPath, StringOps.fromBytes]

theorem path18_join_abs (ops : StringOps) (a b : Path) :
    isabspath .unix (joinStep .unix ops a b) =
      (isabspath .unix a || isabspath .unix b) := by
  by_cases hb : isabspath .unix b = true
  · simp [joinStep, hb]
  · have hb' : isabspath .unix b = false := Bool.eq_false_iff.mpr hb
    cases a with
    | mk a =>
      cases a with
      | nil => simp [path18_join_nil, hb', path18_abs_nil]
      | cons first rest =>
        unfold joinStep
        rw [hb']
        simp only [Bool.false_eq_true, if_false, List.isEmpty_cons, Bool.false_or]
        split
        · simp only [appendPath, StringOps.fromBytes]
          rw [path18_abs_append _ _ (by simp)]
          simp [hb']
        · simp only [appendPath, StringOps.fromBytes]
          rw [path18_abs_append _ _ (by simp), path18_abs_append _ _ (by simp)]
          simp [hb']

theorem path18_join_relative (ops : StringOps) (a b : Path)
    (hb : isabspath .unix b = false) :
    joinStep .unix ops a b =
      if a.bytes.isEmpty || a.bytes.getLast? == some (separator .unix) then
        appendPath ops a b
      else appendPath ops (ops.fromBytes (a.bytes ++ [separator .unix])) b := by
  simp only [joinStep, hb, Bool.false_eq_true, ite_false]

theorem path18_join_assoc (ops : StringOps) (a b c : Path) :
    joinStep .unix ops (joinStep .unix ops a b) c =
      joinStep .unix ops a (joinStep .unix ops b c) := by
  by_cases hc : isabspath .unix c = true
  · simp [joinStep, hc]
  · have hc' : isabspath .unix c = false := Bool.eq_false_iff.mpr hc
    by_cases hb : isabspath .unix b = true
    · have hab : joinStep .unix ops a b = b := by simp only [joinStep, hb, ite_true]
      have hbc : isabspath .unix (joinStep .unix ops b c) = true := by
        rw [path18_join_abs, hb]; rfl
      rw [hab]
      exact (if_pos hbc).symm
    · have hb' : isabspath .unix b = false := Bool.eq_false_iff.mpr hb
      have hbc : isabspath .unix (joinStep .unix ops b c) = false := by
        rw [path18_join_abs, hb', hc']; rfl
      rw [path18_join_relative ops a _ hbc,
        path18_join_relative ops b c hc',
        path18_join_relative ops _ c hc',
        path18_join_relative ops a b hb']
      rcases bytesNilOrConcat a.bytes with ha | ⟨ap, al, ha⟩
      · simp [ha, appendPath, StringOps.fromBytes]
      · rcases bytesNilOrConcat b.bytes with hb | ⟨bp, bl, hb⟩
        · by_cases hal : al = slash <;>
            simp [ha, hb, hal, appendPath, StringOps.fromBytes, separator,
              List.getLast?_append, List.getLast?_cons, List.append_assoc]
        · by_cases hal : al = slash <;> by_cases hbl : bl = slash <;>
            simp [ha, hb, hal, hbl, appendPath, StringOps.fromBytes, separator,
              List.getLast?_append, List.getLast?_cons, List.append_assoc]

/-- Unix joins drop an absolute later component and associate. -/
theorem PathsJoinpathLaws_proven : JuliaLean.Proofs.base.path.JoinpathLaws := by
  refine ⟨JuliaLean.Proofs.base.path.joinpathAbsoluteComponent_proven, ?_⟩
  intro ops a b c
  constructor
  · rfl
  · change Except.ok (joinStep .unix ops (joinStep .unix ops a b) c) =
      Except.ok (joinStep .unix ops a (joinStep .unix ops b c))
    rw [path18_join_assoc]


/-- Absolute input bypasses every filesystem operation and returns its normalization. -/
theorem path18_abspath_absolute_run (World : Type) (files : FileBindings World)
    (os : Platform) (ops : StringOps) (path : Path) (world : World)
    (habs : isabspath os path = true) :
    abspath files.ops os ops path world = some (.ok (normpath os ops path), world) := by
  unfold abspath
  rw [habs]
  rfl

/-- Reduction of the absolute-input contract to three pure normalization facts. -/
theorem path18_abspath_absolute_from_normalization
    (habs : ∀ (os : Platform) (ops : StringOps) (path : Path),
      Round4.FitsPath path → isabspath os path = true →
      isabspath os (normpath os ops path) = true)
    (hidem : ∀ (os : Platform) (ops : StringOps) (path : Path),
      Round4.FitsPath path → isabspath os path = true →
      normpath os ops (normpath os ops path) = normpath os ops path)
    (hlex : ∀ (os : Platform) (ops : StringOps) (path : Path),
      Round4.FitsPath path → isabspath os path = true →
      resolveLexically os ops [] (normpath os ops path) = resolveLexically os ops [] path) :
    Round4.AbspathAbsoluteInputCorrect := by
  intro World files os ops path world hsize hpath
  exact ⟨normpath os ops path,
    path18_abspath_absolute_run World files os ops path world hpath,
    habs os ops path hsize hpath, hidem os ops path hsize hpath,
    hlex os ops path hsize hpath⟩

/-! Source splitpath components and Unix inverse -/


open JuliaLean JuliaLean.Proofs.base.path.Round4

theorem split_name_partition_empty (os : Platform) (names : List (List UInt8))
    (h : NamePartition os [] names) : names = [] := by
  cases names with
  | nil => rfl
  | cons name rest =>
    rcases h with ⟨hne, _, seps, suffix, _, _, heq, _⟩
    have hz := List.append_eq_nil_iff.mp heq.symm
    exact False.elim (hne (List.append_eq_nil_iff.mp hz.1).1)

theorem split_name_skip_separators (os : Platform) (bytes : List UInt8)
    (names : List (List UInt8)) (h : NamePartition os bytes names) :
    bytes.takeWhile (isseparatorByte os) = [] ∧ bytes.dropWhile (isseparatorByte os) = bytes := by
  cases names with
  | nil =>
    have heq : bytes = [] := h
    subst bytes
    exact ⟨rfl, rfl⟩
  | cons name rest =>
    rcases h with ⟨hne, hnosep, seps, suffix, _, _, hbytes, _⟩
    obtain ⟨first, tail, hname⟩ := List.exists_cons_of_ne_nil hne
    have hfirst : isseparatorByte os first = false :=
      hnosep first (by rw [hname]; exact List.mem_cons_self)
    rw [hbytes, hname]
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
      hfirst, Bool.false_eq_true, ↓reduceIte, and_self]

theorem split_name_take (os : Platform) (bytes name : List UInt8) (rest : List (List UInt8))
    (h : NamePartition os bytes (name :: rest)) :
    bytes.takeWhile (fun b => !isseparatorByte os b) = name := by
  rcases h with ⟨hne, hnosep, seps, suffix, hseps, hsepne, hbytes, hrest⟩
  have hname : ∀ b ∈ name, (!isseparatorByte os b) = true := by
    intro b hb
    rw [hnosep b hb]
    rfl
  rw [hbytes, List.append_assoc, List.takeWhile_append_of_pos hname]
  have hstop : (seps ++ suffix).takeWhile (fun b => !isseparatorByte os b) = [] := by
    cases seps with
    | nil =>
      have hr : rest = [] := by
        by_cases hh : rest = []
        · exact hh
        · exact False.elim (hsepne hh rfl)
      subst rest
      have hs : suffix = [] := hrest
      rw [hs]
      rfl
    | cons first tail =>
      have hfirst := hseps first List.mem_cons_self
      simp only [List.cons_append, List.takeWhile_cons, hfirst, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
  rw [hstop, List.append_nil]

theorem split_name_tail (os : Platform) (bytes name : List UInt8) (rest : List (List UInt8))
    (h : NamePartition os bytes (name :: rest)) :
    NamePartition os ((bytes.drop name.length).dropWhile (isseparatorByte os)) rest := by
  rcases h with ⟨_, _, seps, suffix, hseps, _, hbytes, hrest⟩
  rw [hbytes, List.append_assoc, List.drop_left,
    List.dropWhile_append_of_pos hseps, (split_name_skip_separators os suffix rest hrest).2]
  exact hrest

theorem split_name_unique (os : Platform) (bytes : List UInt8)
    (names others : List (List UInt8))
    (h : NamePartition os bytes names) (h' : NamePartition os bytes others) : names = others := by
  induction names generalizing bytes others with
  | nil =>
    have hb : bytes = [] := h
    subst bytes
    exact (split_name_partition_empty os others h').symm
  | cons name rest ih =>
    cases others with
    | nil =>
      have hb : bytes = [] := h'
      subst bytes
      exact split_name_partition_empty os (name :: rest) h
    | cons other rest' =>
      have hn : name = other := (split_name_take os bytes name rest h).symm.trans
        (split_name_take os bytes other rest' h')
      subst other
      exact congrArg (List.cons name) (ih _ rest'
        (split_name_tail os bytes name rest h) (split_name_tail os bytes name rest' h'))

theorem split_root_take_drop (os : Platform) (bytes rootRun suffix : List UInt8)
    (names : List (List UInt8))
    (hroot : ∀ b ∈ rootRun, isseparatorByte os b = true)
    (hbytes : bytes = rootRun ++ suffix) (hnames : NamePartition os suffix names) :
    bytes.takeWhile (isseparatorByte os) = rootRun ∧
      bytes.dropWhile (isseparatorByte os) = suffix := by
  rw [hbytes, List.takeWhile_append_of_pos hroot, List.dropWhile_append_of_pos hroot]
  rw [(split_name_skip_separators os suffix names hnames).1,
    (split_name_skip_separators os suffix names hnames).2, List.append_nil]
  exact ⟨rfl, rfl⟩

theorem split_component_empty (os : Platform) (parts : List (List UInt8))
    (h : ComponentPartition os [] parts) : parts = [[]] := by
  rcases h with ⟨_, hp⟩ | ⟨hne, hp⟩ | ⟨rootRun, rootByte, suffix, names, hhead, _, heq, _, _⟩
  · exact hp
  · exact False.elim (hne (split_name_partition_empty os parts hp))
  · have hz := (List.append_eq_nil_iff.mp heq.symm).1
    rw [hz] at hhead
    cases hhead

theorem split_component_unique (os : Platform) (bytes : List UInt8)
    (parts others : List (List UInt8))
    (h : ComponentPartition os bytes parts) (h' : ComponentPartition os bytes others) :
    parts = others := by
  by_cases hb : bytes = []
  · subst bytes
    exact (split_component_empty os parts h).trans (split_component_empty os others h').symm
  rcases h with ⟨hempty, _⟩ | ⟨hnames, hp⟩ |
    ⟨rootRun, rootByte, suffix, names, hhead, hroot, hbytes, hnames, hparts⟩
  · exact False.elim (hb hempty)
  · rcases h' with ⟨hempty, _⟩ | ⟨_, hp'⟩ |
      ⟨rootRun, rootByte, suffix, names, hhead, hroot, hbytes, hnames', hparts⟩
    · exact False.elim (hb hempty)
    · exact split_name_unique os bytes parts others hp hp'
    · have hr := (split_root_take_drop os bytes rootRun suffix names hroot hbytes hnames').1
      rw [(split_name_skip_separators os bytes parts hp).1] at hr
      rw [← hr] at hhead
      cases hhead
  · rcases h' with ⟨hempty, _⟩ | ⟨_, hp'⟩ |
      ⟨rootRun', rootByte', suffix', names', hhead', hroot', hbytes', hnames', hparts'⟩
    · exact False.elim (hb hempty)
    · have hr := (split_root_take_drop os bytes rootRun suffix names hroot hbytes hnames).1
      rw [(split_name_skip_separators os bytes others hp').1] at hr
      rw [← hr] at hhead
      cases hhead
    · obtain ⟨hrt, hrd⟩ := split_root_take_drop os bytes rootRun suffix names hroot hbytes hnames
      obtain ⟨hrt', hrd'⟩ := split_root_take_drop os bytes rootRun' suffix' names' hroot' hbytes' hnames'
      have hrr : rootRun = rootRun' := hrt.symm.trans hrt'
      have hss : suffix = suffix' := hrd.symm.trans hrd'
      rw [← hrr] at hhead'
      rw [← hss] at hnames'
      have hbb : rootByte = rootByte' := Option.some.inj (hhead.symm.trans hhead')
      have hnn : names = names' := split_name_unique os suffix names names' hnames hnames'
      rw [hparts, hparts', hbb, hnn]

/-- A supplied partition determines the exact splitter result once its drive is known. -/
theorem split_from_partition (os : Platform) (ops : StringOps) (path drive tail : Path)
    (first : List UInt8) (rest : List (List UInt8))
    (hdrive : splitdrive os ops path = (drive, tail))
    (hpart : ComponentPartition os tail.bytes (first :: rest)) :
    (splitpath os ops path).map (fun part => part.bytes) = (drive.bytes ++ first) :: rest := by
  have htarget : ∃ first' rest', ComponentPartition os tail.bytes (first' :: rest') ∧
      (splitpath os ops path).map (fun part => part.bytes) = (drive.bytes ++ first') :: rest' := by
    by_cases ht : tail.bytes = []
    · refine ⟨[], [], Or.inl ⟨ht, rfl⟩, ?_⟩
      have heq : tail = (⟨[]⟩ : Path) := path_eq_of_bytes_eq ht
      subst tail
      by_cases hd : drive.bytes = [] <;>
        simp [splitpath, Id.run, hdrive, split_loop_empty, hd, appendPath, StringOps.fromBytes]
    · obtain ⟨first', rest', hpartition, hloop⟩ :=
        split_loop_partition os ops (tail.bytes.length + 1) tail.bytes [] ht (by omega)
      refine ⟨first', rest', hpartition, ?_⟩
      have hisempty : tail.bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr ht
      by_cases hd : drive.bytes = [] <;>
        simp [splitpath, Id.run, hdrive, hisempty, hloop, hd, appendPath, StringOps.fromBytes,
          List.map_map, Function.comp_def]
  obtain ⟨first', rest', hp', heq⟩ := htarget
  have hu := split_component_unique os tail.bytes (first :: rest) (first' :: rest') hpart hp'
  have hfirst := (List.cons.inj hu).1
  have hrest := (List.cons.inj hu).2
  rw [heq, hfirst, hrest]

theorem split_noPath_to_noSeparator (os : Platform) (bytes : List UInt8)
    (h : NoPathSeparators os bytes) : NoSeparatorBytes os bytes := by
  intro b hb
  obtain ⟨hs, hbck⟩ := h b hb
  cases os <;> simp [isseparatorByte, hs, hbck]

theorem split_separator_isSep (os : Platform) : isseparatorByte os (separator os) = true := by
  cases os <;> rfl

theorem split_intercalate_names (os : Platform) (names : List (List UInt8))
    (h : ∀ name ∈ names, name ≠ [] ∧ NoSeparatorBytes os name) :
    NamePartition os (List.intercalate [separator os] names) names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    obtain ⟨hne, hnosep⟩ := h name List.mem_cons_self
    have hrest : ∀ next ∈ rest, next ≠ [] ∧ NoSeparatorBytes os next := by
      intro next hn
      exact h next (List.mem_cons_of_mem name hn)
    cases rest with
    | nil =>
      rw [List.intercalate_singleton]
      exact split_name_single os name hne hnosep
    | cons next rest =>
      rw [List.intercalate_cons_cons]
      refine ⟨hne, hnosep, [separator os], List.intercalate [separator os] (next :: rest),
        ?_, ?_, rfl, ih hrest⟩
      · intro b hb
        simp only [List.mem_singleton] at hb
        subst b
        exact split_separator_isSep os
      · intro _
        exact List.cons_ne_nil _ _

theorem split_unix_spelling_partition (ops : StringOps) (parts : List Path)
    (h : JoinableComponents .unix ops parts) :
    ComponentPartition .unix (ComponentSpelling .unix ops parts) (parts.map Path.bytes) := by
  rcases h with hzero | hnonzero
  · rw [hzero]
    exact Or.inl ⟨rfl, rfl⟩
  · cases parts with
    | nil => exact False.elim hnonzero
    | cons first rest =>
      obtain ⟨hne, hfirst, hrest⟩ := hnonzero
      change RootComponent .unix first.bytes ∨ NoPathSeparators .unix first.bytes at hfirst
      have hnames : ∀ name ∈ rest.map Path.bytes, name ≠ [] ∧ NoSeparatorBytes .unix name := by
        intro name hn
        obtain ⟨part, hp, heq⟩ := List.mem_map.mp hn
        subst name
        obtain ⟨hne, hnosep, _⟩ := hrest part hp
        exact ⟨hne, split_noPath_to_noSeparator .unix part.bytes hnosep⟩
      rcases hfirst with hroot | hname
      · have hroot' : first.bytes = [slash] := by
          rcases hroot with heq | ⟨hos, _⟩
          · exact heq
          · cases hos
        have hspelling : ComponentSpelling .unix ops (first :: rest) =
            [slash] ++ List.intercalate [slash] (rest.map Path.bytes) := by
          simp only [ComponentSpelling, splitdrive, hroot', separator, beq_self_eq_true,
            Bool.true_or, ↓reduceIte]
          rfl
        rw [hspelling]
        apply Or.inr ∘ Or.inr
        refine ⟨[slash], slash, List.intercalate [slash] (rest.map Path.bytes),
          rest.map Path.bytes, rfl, ?_, rfl, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_singleton] at hb
          subst b
          rfl
        · exact split_intercalate_names .unix (rest.map Path.bytes) hnames
        · simp only [List.map_cons, hroot']
      · have hnosep := split_noPath_to_noSeparator .unix first.bytes hname
        have hnotroot : first.bytes ≠ [slash] := by
          intro heq
          have hh := hnosep slash (by rw [heq]; exact List.mem_cons_self)
          have hs : isseparatorByte .unix slash = true := rfl
          rw [hs] at hh
          cases hh
        have hspelling : ComponentSpelling .unix ops (first :: rest) =
            List.intercalate [slash] ((first :: rest).map Path.bytes) := by
          cases rest <;> simp [ComponentSpelling, splitdrive, hnotroot, separator]
        rw [hspelling]
        apply Or.inr ∘ Or.inl
        refine ⟨by simp only [List.map_cons, ne_eq, List.cons_ne_nil, not_false_eq_true], ?_⟩
        apply split_intercalate_names .unix
        intro name hn
        simp only [List.map_cons, List.mem_cons] at hn
        rcases hn with heq | hn
        · subst name
          exact ⟨hne, hnosep⟩
        · exact hnames name hn

theorem split_unix_spelling_split (ops : StringOps) (parts : List Path)
    (h : JoinableComponents .unix ops parts) :
    splitpath .unix ops ⟨ComponentSpelling .unix ops parts⟩ = parts := by
  have hpart := split_unix_spelling_partition ops parts h
  have hne : parts ≠ [] := by
    intro hempty
    subst parts
    rcases h with h | h
    · cases h
    · exact h
  obtain ⟨first, rest, heq⟩ := List.exists_cons_of_ne_nil hne
  rw [heq] at hpart ⊢
  have hout := split_from_partition .unix ops ⟨ComponentSpelling .unix ops (first :: rest)⟩
    (emptyPath ops) ⟨ComponentSpelling .unix ops (first :: rest)⟩ first.bytes (rest.map Path.bytes)
    rfl hpart
  apply (List.map_inj_right (f := Path.bytes) (fun _ _ h => path_eq_of_bytes_eq h)).mp
  simpa only [emptyPath, StringOps.fromBytes, List.nil_append, List.map_cons] using hout

def split_EndsInName (os : Platform) (bytes : List UInt8) : Prop :=
  ∃ last, bytes.getLast? = some last ∧ isseparatorByte os last = false

theorem split_name_ends (os : Platform) (bytes : List UInt8)
    (hne : bytes ≠ []) (h : NoSeparatorBytes os bytes) : split_EndsInName os bytes :=
  ⟨bytes.getLast hne, List.getLast?_eq_some_getLast hne,
    h _ (List.getLast_mem hne)⟩

theorem split_append_ends (os : Platform) (pre tail : List UInt8)
    (h : split_EndsInName os tail) : split_EndsInName os (pre ++ tail) := by
  obtain ⟨last, hlast, hsep⟩ := h
  exact ⟨last, by simp only [List.getLast?_append, hlast, Option.some_or], hsep⟩

theorem split_unix_name_relative (path : Path) (h : NoSeparatorBytes .unix path.bytes) :
    isabspath .unix path = false := by
  cases hb : path.bytes with
  | nil => simp only [isabspath, hb, List.isEmpty_nil, ↓reduceIte]
  | cons first rest =>
    have hf : isSep .unix first = false := h first (by rw [hb]; exact List.mem_cons_self)
    simp [isabspath, hb, hf]

theorem split_unix_joinStep (ops : StringOps) (path name : Path)
    (hend : split_EndsInName .unix path.bytes) (hname : NoSeparatorBytes .unix name.bytes) :
    joinStep .unix ops path name = ⟨path.bytes ++ [slash] ++ name.bytes⟩ := by
  obtain ⟨last, hlast, hsep⟩ := hend
  have hne : path.bytes ≠ [] := by intro h; rw [h] at hlast; cases hlast
  have hlastne : last ≠ slash := by simpa [isseparatorByte] using hsep
  simp [joinStep, split_unix_name_relative name hname,
    List.isEmpty_eq_false_iff.mpr hne, hlast, separator, hlastne, appendPath, StringOps.fromBytes]

theorem split_unix_joinRoot (ops : StringOps) (name : Path)
    (hname : NoSeparatorBytes .unix name.bytes) :
    joinStep .unix ops ⟨[slash]⟩ name = ⟨[slash] ++ name.bytes⟩ := by
  simp [joinStep, split_unix_name_relative name hname, separator, appendPath, StringOps.fromBytes]

theorem split_joinUnix_tail (ops : StringOps) (names : List Path) (path : Path)
    (hend : split_EndsInName .unix path.bytes)
    (hnames : ∀ name ∈ names, name.bytes ≠ [] ∧ NoSeparatorBytes .unix name.bytes) :
    joinUnixLoop ops (names.map PathValue.string) path =
      .ok ⟨path.bytes ++ (if names = [] then [] else
        [slash] ++ List.intercalate [slash] (names.map Path.bytes))⟩ := by
  induction names generalizing path with
  | nil =>
    simp only [List.map_nil, joinUnixLoop, ↓reduceIte, List.append_nil]
  | cons name rest ih =>
    obtain ⟨hnamene, hname⟩ := hnames name List.mem_cons_self
    have hrest : ∀ next ∈ rest, next.bytes ≠ [] ∧ NoSeparatorBytes .unix next.bytes := by
      intro next hnext
      exact hnames next (List.mem_cons_of_mem name hnext)
    simp only [List.map_cons, joinUnixLoop, assertstring, pathValueString,
      bind, Except.bind]
    rw [split_unix_joinStep ops path name hend hname]
    rw [ih _ (split_append_ends .unix _ name.bytes (split_name_ends .unix name.bytes hnamene hname)) hrest]
    cases rest <;> simp [List.append_assoc]

theorem split_unix_join_spelling (ops : StringOps) (parts : List Path)
    (h : JoinableComponents .unix ops parts) :
    joinpath .unix ops (parts.map PathValue.string) = .ok ⟨ComponentSpelling .unix ops parts⟩ := by
  rcases h with hzero | hnonzero
  · rw [hzero]
    rfl
  · cases parts with
    | nil => exact False.elim hnonzero
    | cons first rest =>
      obtain ⟨hne, hfirst, hrest⟩ := hnonzero
      change RootComponent .unix first.bytes ∨ NoPathSeparators .unix first.bytes at hfirst
      have hnames : ∀ name ∈ rest, name.bytes ≠ [] ∧ NoSeparatorBytes .unix name.bytes := by
        intro name hn
        obtain ⟨hne, hnosep, _⟩ := hrest name hn
        exact ⟨hne, split_noPath_to_noSeparator .unix name.bytes hnosep⟩
      change joinUnixLoop ops (rest.map PathValue.string) first = _
      rcases hfirst with hroot | hname
      · have hroot' : first.bytes = [slash] := by
          rcases hroot with heq | ⟨hos, _⟩
          · exact heq
          · cases hos
        have hfirsteq : first = (⟨[slash]⟩ : Path) := path_eq_of_bytes_eq hroot'
        subst first
        cases rest with
        | nil => rfl
        | cons name rest =>
          obtain ⟨hnamene, hname⟩ := hnames name List.mem_cons_self
          have hrest' : ∀ next ∈ rest, next.bytes ≠ [] ∧ NoSeparatorBytes .unix next.bytes := by
            intro next hn
            exact hnames next (List.mem_cons_of_mem name hn)
          simp only [List.map_cons, joinUnixLoop, assertstring, pathValueString,
            bind, Except.bind]
          rw [split_unix_joinRoot ops name hname]
          rw [split_joinUnix_tail ops rest _
            (split_append_ends .unix _ name.bytes (split_name_ends .unix name.bytes hnamene hname)) hrest']
          cases rest <;> simp [ComponentSpelling, splitdrive, separator, List.append_assoc]
      · have hnosep := split_noPath_to_noSeparator .unix first.bytes hname
        have hend := split_name_ends .unix first.bytes hne hnosep
        rw [split_joinUnix_tail ops rest first hend hnames]
        have hnotroot : first.bytes ≠ [slash] := by
          intro heq
          have hh := hnosep slash (by rw [heq]; exact List.mem_cons_self)
          have hs : isseparatorByte .unix slash = true := rfl
          rw [hs] at hh
          cases hh
        cases rest <;> simp [ComponentSpelling, splitdrive, separator, hnotroot, List.append_assoc]

/-- The complete inverse contract specialized to Unix paths, without a size restriction. -/
theorem split_unix_join_inverse (ops : StringOps) :
    (∀ path, CanonicalJoinSpelling .unix ops path →
      joinpath .unix ops ((splitpath .unix ops path).map PathValue.string) = .ok path) ∧
    (∀ parts, JoinableComponents .unix ops parts →
      ∃ path, joinpath .unix ops (parts.map PathValue.string) = .ok path ∧
        splitpath .unix ops path = parts) := by
  constructor
  · intro path hpath
    obtain ⟨parts, hparts, _, hspell⟩ := hpath
    have hp : path = (⟨ComponentSpelling .unix ops parts⟩ : Path) := path_eq_of_bytes_eq hspell
    rw [hp, split_unix_spelling_split ops parts hparts]
    exact split_unix_join_spelling ops parts hparts
  · intro parts hparts
    exact ⟨⟨ComponentSpelling .unix ops parts⟩,
      split_unix_join_spelling ops parts hparts, split_unix_spelling_split ops parts hparts⟩

/-! Normalization cancellation and lexical folding -/

open JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- One source cancellation deletes an adjacent ordinary component and parent component. -/
theorem clean18_remove_structure (parts after : List (List UInt8))
    (h : removeFirstPair parts = some after) :
    ∃ pre component suffix,
      parts = pre ++ component :: dotdot :: suffix ∧
      component ≠ dotdot ∧ after = pre ++ suffix := by
  induction parts generalizing after with
  | nil => cases h
  | cons a tail ih =>
    cases tail with
    | nil => cases h
    | cons b rest =>
      rw [removeFirstPair] at h
      split at h
      · rename_i hc
        have hp : a ≠ dotdot ∧ b = dotdot := by
          simpa only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hc
        obtain ⟨ha, hb⟩ := hp
        subst b
        exact ⟨[], a, rest, rfl, ha, (Option.some.inj h).symm⟩
      · cases hr : removeFirstPair (b :: rest) with
        | none => simp only [hr, Option.map_none, reduceCtorEq] at h
        | some shorter =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          obtain ⟨pre, component, suffix, heq, hn, hafter⟩ := ih shorter hr
          refine ⟨a :: pre, component, suffix, ?_, hn, ?_⟩
          · simp only [List.cons_append, heq]
          · rw [← h, hafter]
            rfl

theorem clean18_remove_length (parts after : List (List UInt8))
    (h : removeFirstPair parts = some after) : after.length + 2 = parts.length := by
  obtain ⟨pre, component, suffix, rfl, _, rfl⟩ := clean18_remove_structure parts after h
  simp only [List.length_append, List.length_cons]
  omega

theorem clean18_remove_mem (parts after : List (List UInt8))
    (h : removeFirstPair parts = some after) (component : (List UInt8))
    (hc : component ∈ after) : component ∈ parts := by
  obtain ⟨pre, removed, suffix, rfl, _, rfl⟩ := clean18_remove_structure parts after h
  simp only [List.mem_append, List.mem_cons] at hc ⊢
  rcases hc with hp | hs
  · exact Or.inl hp
  · exact Or.inr (Or.inr (Or.inr hs))

/-- With the source's fuel, a returned sequence has no remaining cancellable pair. -/
theorem clean18_normal (fuel : Nat) (parts : List (List UInt8)) (h : parts.length < fuel) :
    removeFirstPair (cleanLoop fuel parts) = none := by
  induction fuel generalizing parts with
  | zero => omega
  | succ fuel ih =>
    rw [cleanLoop]
    cases hr : removeFirstPair parts with
    | none => exact hr
    | some after =>
      apply ih
      have := clean18_remove_length parts after hr
      omega

theorem clean18_fixed (fuel : Nat) (parts : List (List UInt8))
    (h : removeFirstPair parts = none) : cleanLoop fuel parts = parts := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [cleanLoop, h]

theorem clean18_idempotent (parts : List (List UInt8)) :
    let normalized := cleanLoop (parts.length + 1) parts
    cleanLoop (normalized.length + 1) normalized = normalized := by
  apply clean18_fixed
  apply clean18_normal
  omega

/-- Cancellation preserves every predicate on individual input components. -/
theorem clean18_preserves (predicate : (List UInt8) → Prop) (fuel : Nat) (parts : List (List UInt8))
    (h : ∀ component ∈ parts, predicate component) :
    ∀ component ∈ cleanLoop fuel parts, predicate component := by
  induction fuel generalizing parts with
  | zero => exact h
  | succ fuel ih =>
    rw [cleanLoop]
    cases hr : removeFirstPair parts with
    | none => exact h
    | some after =>
      apply ih
      intro component hc
      exact h component (clean18_remove_mem parts after hr component hc)

theorem clean18_none_tail (component : (List UInt8)) (parts : List (List UInt8))
    (h : removeFirstPair (component :: parts) = none) : removeFirstPair parts = none := by
  cases parts with
  | nil => rfl
  | cons next rest =>
    rw [removeFirstPair] at h
    split at h
    · cases h
    · cases hr : removeFirstPair (next :: rest) with
      | none => rfl
      | some shorter => simp only [hr, Option.map_some, reduceCtorEq] at h

theorem clean18_no_later_parent (component : (List UInt8)) (parts : List (List UInt8))
    (h : removeFirstPair (component :: parts) = none) (hn : component ≠ dotdot) :
    ∀ later ∈ parts, later ≠ dotdot := by
  induction parts generalizing component with
  | nil => intro later hl; cases hl
  | cons next rest ih =>
    have hnext : next ≠ dotdot := by
      intro he
      subst next
      have hc : (component != dotdot && dotdot == dotdot) = true := by
        simpa only [beq_self_eq_true, Bool.and_true, bne_iff_ne] using hn
      rw [removeFirstPair, ite_eq_left hc] at h
      cases h
    have htail := clean18_none_tail component (next :: rest) h
    intro later hl
    rcases List.mem_cons.mp hl with he | hl
    · exact he ▸ hnext
    · exact ih next htail hnext later hl

/-- Parent components in normal form are exactly a leading run. -/
theorem clean18_parent_prefix (parts : List (List UInt8))
    (h : removeFirstPair parts = none) : dotDotPrefix parts := by
  induction parts with
  | nil => exact ⟨0, [], rfl, by simp⟩
  | cons component parts ih =>
    by_cases hc : component = dotdot
    · subst component
      obtain ⟨n, rest, heq, hrest⟩ := ih (clean18_none_tail dotdot parts h)
      refine ⟨n + 1, rest, ?_, hrest⟩
      rw [List.replicate_succ, List.cons_append, heq]
    · refine ⟨0, component :: parts, rfl, ?_⟩
      intro later hl
      rcases List.mem_cons.mp hl with he | hl
      · exact he ▸ hc
      · exact clean18_no_later_parent component parts h hc later hl

/-- The source loop produces a parent-prefix normal form. -/
theorem clean18_loop_parent_prefix (parts : List (List UInt8)) :
    dotDotPrefix (cleanLoop (parts.length + 1) parts) :=
  clean18_parent_prefix _ (clean18_normal _ _ (by omega))


/-- A parent component removes exactly the final lexical stack element. -/
theorem clean18_step_parent (stack : List (List UInt8)) :
    pathComponentStep stack dotdot = stack.dropLast := by rfl

theorem clean18_step_name (stack : List (List UInt8)) (component : List UInt8)
    (hne : component ≠ []) (hnd : component ≠ [dot]) (hnp : component ≠ dotdot) :
    pathComponentStep stack component = stack ++ [component] := by
  simp only [pathComponentStep, List.isEmpty_eq_false_iff.mpr hne,
    beq_eq_false_iff_ne.mpr hnd, beq_eq_false_iff_ne.mpr hnp,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]

theorem clean18_cancel_step (stack : List (List UInt8)) (component : List UInt8)
    (hne : component ≠ []) (hnd : component ≠ [dot]) (hnp : component ≠ dotdot) :
    pathComponentStep (pathComponentStep stack component) dotdot = stack := by
  rw [clean18_step_name stack component hne hnd hnp, clean18_step_parent,
    List.dropLast_concat]

/-- One adjacent cancellation preserves lexical resolution from every base. -/
theorem clean18_remove_fold (parts after stack : List (List UInt8))
    (hvalid : ∀ component ∈ parts, component ≠ [] ∧ component ≠ [dot])
    (h : removeFirstPair parts = some after) :
    after.foldl pathComponentStep stack = parts.foldl pathComponentStep stack := by
  obtain ⟨pre, component, suffix, rfl, hn, rfl⟩ := clean18_remove_structure parts after h
  have hc := hvalid component (by simp)
  simp only [List.foldl_append, List.foldl_cons]
  rw [clean18_cancel_step _ component hc.1 hc.2 hn]

/-- Every source-loop iteration preserves lexical resolution from every base. -/
theorem clean18_loop_fold (fuel : Nat) (parts stack : List (List UInt8))
    (hvalid : ∀ component ∈ parts, component ≠ [] ∧ component ≠ [dot]) :
    (cleanLoop fuel parts).foldl pathComponentStep stack =
      parts.foldl pathComponentStep stack := by
  induction fuel generalizing parts with
  | zero => rfl
  | succ fuel ih =>
    rw [cleanLoop]
    cases hr : removeFirstPair parts with
    | none => rfl
    | some after =>
      rw [ih after]
      · exact clean18_remove_fold parts after stack hvalid hr
      · intro component hc
        exact hvalid component (clean18_remove_mem parts after hr component hc)

/-- Empty split components have no lexical effect. -/
theorem clean18_filter_empty_fold (parts stack : List (List UInt8)) :
    (parts.filter (· ≠ [])).foldl pathComponentStep stack =
      parts.foldl pathComponentStep stack := by
  induction parts generalizing stack with
  | nil => rfl
  | cons component parts ih =>
    by_cases h : component = []
    · subst component
      simpa only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, List.foldl_cons, pathComponentStep,
        List.isEmpty_nil, Bool.true_or] using ih stack
    · have hb : decide (component ≠ []) = true := decide_eq_true h
      simp only [List.filter_cons, hb, ↓reduceIte, List.foldl_cons, ih]

/-- Dot split components have no lexical effect. -/
theorem clean18_filter_dot_fold (parts stack : List (List UInt8)) :
    (parts.filter (· != [dot])).foldl pathComponentStep stack =
      parts.foldl pathComponentStep stack := by
  induction parts generalizing stack with
  | nil => rfl
  | cons component parts ih =>
    by_cases h : component = [dot]
    · subst component
      simpa only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.foldl_cons, pathComponentStep, beq_self_eq_true, Bool.or_true]
        using ih stack
    · have hb : (component != [dot]) = true := bne_iff_ne.mpr h
      simp only [List.filter_cons, hb, ↓reduceIte, List.foldl_cons, ih]

/-- Leading parents have no effect when resolution starts at the root. -/
theorem clean18_drop_parents_fold (parts : List (List UInt8)) :
    (parts.dropWhile (· == dotdot)).foldl pathComponentStep [] =
      parts.foldl pathComponentStep [] := by
  induction parts with
  | nil => rfl
  | cons component parts ih =>
    by_cases h : component = dotdot
    · subst component
      simpa only [List.dropWhile_cons, beq_self_eq_true, ↓reduceIte,
        List.foldl_cons, clean18_step_parent, List.dropLast_nil] using ih
    · simp only [List.dropWhile_cons, beq_eq_false_iff_ne.mpr h,
        Bool.false_eq_true, ↓reduceIte]

/-- The actual normpath filter-and-cancel stage preserves component resolution. -/
theorem clean18_source_fold (parts stack : List (List UInt8)) :
    let filtered := (parts.filter (· ≠ [])).filter (· != [dot])
    (cleanLoop (filtered.length + 1) filtered).foldl pathComponentStep stack =
      parts.foldl pathComponentStep stack := by
  dsimp only
  have hvalid : ∀ component ∈ (parts.filter (· ≠ [])).filter (· != [dot]),
      component ≠ [] ∧ component ≠ [dot] := by
    intro component hc
    simp only [List.mem_filter, decide_eq_true_eq, bne_iff_ne] at hc
    exact ⟨hc.1.2, hc.2⟩
  rw [clean18_loop_fold _ _ _ hvalid, clean18_filter_dot_fold, clean18_filter_empty_fold]

/-! Concrete working-directory witness -/

open JuliaLean JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Unused callback values return the model's divergence marker.
The absolute-path branch never invokes these callbacks. -/
def path18_unobserved_action {A : Type} : JuliaLean.base.io.M Unit A := fun _ => none

def path18_unit_integer_ops (t : IntTy) : JuliaLean.base.file.IntegerOps Unit (JInt t) where
  value := fun n => n.val
  string := fun _ _ => path18_unobserved_action
  display := fun _ => path18_unobserved_action

def path18_unit_error_ops : JuliaLean.base.filesystem.ErrorOps Unit where
  uvError := fun _ _ => path18_unobserved_action
  systemError := fun _ _ => path18_unobserved_action
  systemErrorCurrent := fun _ => path18_unobserved_action
  windowsError := fun _ _ => path18_unobserved_action
  errno := fun _ => path18_unobserved_action
  eagain := JInt.lit .i32 0

def path18_unit_stat_ops : JuliaLean.base.stat.StatOps Unit Unit Unit Unit Unit Unit Unit Unit where
  errors := path18_unit_error_ops
  uvNoEnt := JInt.lit .i32 0
  uvNoDir := JInt.lit .i32 0
  uvInvalid := JInt.lit .i32 0
  sizeofStat := fun _ => path18_unobserved_action
  i32ToI64 := fun _ => path18_unobserved_action
  allocateStat := fun _ => path18_unobserved_action
  zeroStat := fun _ => path18_unobserved_action
  statCString := fun _ _ => path18_unobserved_action
  lstatCString := fun _ _ => path18_unobserved_action
  fstatHandle := fun _ _ => path18_unobserved_action
  statDevice := fun _ => path18_unobserved_action
  statInode := fun _ => path18_unobserved_action
  statMode := fun _ => path18_unobserved_action
  statNlink := fun _ => path18_unobserved_action
  statUid := fun _ => path18_unobserved_action
  statGid := fun _ => path18_unobserved_action
  statRdev := fun _ => path18_unobserved_action
  statSize := fun _ => path18_unobserved_action
  statBlockSize := fun _ => path18_unobserved_action
  statBlocks := fun _ => path18_unobserved_action
  statMtime := fun _ => path18_unobserved_action
  statCtime := fun _ => path18_unobserved_action
  toCString := fun _ => path18_unobserved_action
  otherString := fun _ => path18_unobserved_action
  unrepresentablePath := path18_unobserved_action
  repr := fun _ => path18_unobserved_action
  reprDesc := fun _ => path18_unobserved_action
  typeName := fun _ => path18_unobserved_action
  sameType := fun _ _ => true
  joinOne := fun _ => path18_unobserved_action
  joinMany := fun _ => path18_unobserved_action
  statDispatch := fun _ => path18_unobserved_action
  lstatDispatch := fun _ => path18_unobserved_action
  pathAccess := fun _ _ => path18_unobserved_action
  newStringBuffer := fun _ => path18_unobserved_action
  writeString := fun _ _ => path18_unobserved_action
  takeString := fun _ => path18_unobserved_action
  getUser := fun {_} _ _ => path18_unobserved_action
  userName := fun _ => path18_unobserved_action
  getGroup := fun {_} _ _ => path18_unobserved_action
  groupName := fun _ => path18_unobserved_action
  isEmpty := fun _ => path18_unobserved_action

def path18_unit_file_ops : JuliaLean.base.file.FileOps Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  stat := path18_unit_stat_ops
  isWindows := true
  uvEnoent := JInt.lit .i32 0
  uvEacces := JInt.lit .i32 0
  uvEnobufs := JInt.lit .i32 0
  uvEof := JInt.lit .i32 0
  ioErrorCode := fun _ => none
  isSystemError := fun _ => false
  isInterruptException := fun _ => false
  errorString := fun _ => path18_unobserved_action
  u64Ops := path18_unit_integer_ops .u64
  i64Ops := path18_unit_integer_ops .i64
  repr := fun _ => path18_unobserved_action
  joinpath := fun _ => path18_unobserved_action
  dirname := fun _ => path18_unobserved_action
  basename := fun _ => path18_unobserved_action
  abspath := fun _ => path18_unobserved_action
  normpath := fun _ => path18_unobserved_action
  realpath := fun _ => path18_unobserved_action
  isabspath := fun _ => path18_unobserved_action
  homedir := fun _ => path18_unobserved_action
  isseparator := fun _ => path18_unobserved_action
  pathSeparator := "\\"
  lastChar := fun _ => path18_unobserved_action
  mallocReq := fun _ => path18_unobserved_action
  freeReq := fun _ => path18_unobserved_action
  reqCleanup := fun _ => path18_unobserved_action
  uvFsMkdir := fun _ _ _ => path18_unobserved_action
  uvFsRmdir := fun _ _ => path18_unobserved_action
  uvFsMkdtemp := fun _ _ => path18_unobserved_action
  uvFsReadlink := fun _ _ => path18_unobserved_action
  uvFsScandir := fun _ _ _ => path18_unobserved_action
  uvFsScandirNext := fun _ _ => path18_unobserved_action
  uvFsTPath := fun _ => path18_unobserved_action
  uvFsTPtr := fun _ => path18_unobserved_action
  newDirent := fun _ => path18_unobserved_action
  direntName := fun _ => path18_unobserved_action
  direntType := fun _ => path18_unobserved_action
  avgPath := JInt.lit .i64 0
  newStringVector := fun _ => path18_unobserved_action
  stringVectorLength := fun _ => path18_unobserved_action
  stringVectorSet := fun _ _ _ => path18_unobserved_action
  resizeStringVector := fun _ _ => path18_unobserved_action
  stringVectorString := fun _ => path18_unobserved_action
  newSizeRef := fun _ => path18_unobserved_action
  getSizeRef := fun _ => path18_unobserved_action
  uvCwd := fun _ _ => path18_unobserved_action
  uvOsTmpdir := fun _ _ => path18_unobserved_action
  uvChdir := fun _ => path18_unobserved_action
  openDot := fun _ => path18_unobserved_action
  fchdir := fun _ => path18_unobserved_action
  closeFd := fun _ => path18_unobserved_action
  fsUnlink := fun _ => path18_unobserved_action
  fsRename := fun _ _ => path18_unobserved_action
  fsCopyfile := fun _ _ _ => path18_unobserved_action
  fsHardlink := fun _ _ => path18_unobserved_action
  fsSymlink := fun _ _ _ => path18_unobserved_action
  fsChmod := fun _ _ => path18_unobserved_action
  fsChown := fun _ _ _ => path18_unobserved_action
  windowsBeforeVista := fun _ => path18_unobserved_action
  jlOWronly := JInt.lit .i64 0
  jlOCreat := JInt.lit .i64 0
  openFlags := fun _ _ _ => path18_unobserved_action
  openMode := fun _ _ => path18_unobserved_action
  touchStream := fun _ => path18_unobserved_action
  closeStream := fun _ => path18_unobserved_action
  printString := fun _ _ => path18_unobserved_action
  fdio := fun _ _ => path18_unobserved_action
  mkstemp := fun _ => path18_unobserved_action
  cstringContents := fun _ => path18_unobserved_action
  cwstring := fun _ => path18_unobserved_action
  getTempFileName := fun _ _ _ => path18_unobserved_action
  getLastError := fun _ => path18_unobserved_action
  utf16String := fun _ => path18_unobserved_action
  logWarn := fun _ => path18_unobserved_action
  logDebug := fun _ => path18_unobserved_action
  logError := fun _ _ => path18_unobserved_action
  newChannel := fun _ => path18_unobserved_action
  channelPush := fun _ _ => path18_unobserved_action
  channelClose := fun _ _ => path18_unobserved_action
  channelForEach := fun _ _ => path18_unobserved_action
  withCleanupLock := fun {_} _ => path18_unobserved_action
  cleanupGet := fun _ _ => path18_unobserved_action
  cleanupSet := fun _ _ => path18_unobserved_action
  cleanupLength := fun _ => path18_unobserved_action
  cleanupDelete := fun _ => path18_unobserved_action
  cleanupKeys := fun _ => path18_unobserved_action
  cleanupFilter := fun {_} _ _ => path18_unobserved_action
  cleanupMinGet := fun _ => path18_unobserved_action
  cleanupMaxGet := fun _ => path18_unobserved_action
  cleanupMaxSet := fun _ => path18_unobserved_action
  gcFull := fun _ => path18_unobserved_action
  atexit := fun _ => path18_unobserved_action
  cleanupCommand := fun _ => path18_unobserved_action
  newPipeEndpoint := fun _ => path18_unobserved_action
  runDetached := fun _ _ => path18_unobserved_action
  joinWrite := fun _ _ _ => path18_unobserved_action
  dupPipe := fun _ => path18_unobserved_action
  closePipe := fun _ => path18_unobserved_action
  libcRand := fun _ => path18_unobserved_action
  islessString := fun _ _ => path18_unobserved_action
  sortBy := fun {_} _ _ => path18_unobserved_action
  hashString := fun _ _ => path18_unobserved_action
  hashI32 := fun _ _ => path18_unobserved_action
  newIterator := fun _ _ => path18_unobserved_action
  iterUvdir := fun _ => path18_unobserved_action
  iterSwapUvdir := fun _ _ => path18_unobserved_action
  iterSetUvdir := fun _ _ => path18_unobserved_action
  iterStatus := fun _ => path18_unobserved_action
  iterClosed := fun _ => path18_unobserved_action
  iterSetClosed := fun _ _ => path18_unobserved_action
  nullDir := ()
  isNullDir := fun _ => true
  uvFsOpendir := fun _ => path18_unobserved_action
  uvFsClosedir := fun _ => path18_unobserved_action
  uvFsReaddir1 := fun _ _ => path18_unobserved_action
  newStatfsBuffer := fun _ => path18_unobserved_action
  uvFsStatfs := fun _ _ => path18_unobserved_action
  loadDiskStat := fun _ => path18_unobserved_action
  diskStatFields := fun _ => ([], [])

/-- A concrete inhabitant of the installed filesystem interface. -/
def path18_unit_file_bindings : FileBindings Unit where
  Handle := Unit
  CString := Unit
  StatMemory := Unit
  IOBuf := Unit
  User := Unit
  Group := Unit
  Req := Unit
  StrBuf := Unit
  SizeRef := Unit
  Dirent := Unit
  Stream := Unit
  WString := Unit
  Chan := Unit
  Cmd := Unit
  Pipe := Unit
  IterObj := Unit
  DirPtr := Unit
  DiskBuf := Unit
  DiskStatRaw := Unit
  PathVal := Unit
  ops := path18_unit_file_ops

/-- A successful callback preserves the Unit world. -/
def path18_unit_return {A : Type} (value : A) : JuliaLean.base.io.M Unit A :=
  fun world => some (.ok (value, world))

/-- The callbacks observed by pwd reproduce a Unix root-directory result.
The initial buffer has 511 bytes and 512 bytes including its terminator; the
successful read reports one byte for the directory spelling. -/
def path18_root_file_ops : JuliaLean.base.file.FileOps Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  { path18_unit_file_ops with
    isWindows := false
    pathSeparator := "/"
    avgPath := JInt.lit .i64 512
    newStringVector := fun _ => path18_unit_return ()
    stringVectorLength := fun _ => path18_unit_return (JInt.lit .i64 511)
    newSizeRef := fun _ => path18_unit_return ()
    uvCwd := fun _ _ => path18_unit_return (JInt.lit .i32 0)
    getSizeRef := fun _ => path18_unit_return (JInt.lit .u64 1)
    resizeStringVector := fun _ _ => path18_unit_return ()
    stringVectorString := fun _ => path18_unit_return "/" }

def path18_root_file_bindings : FileBindings Unit :=
  { path18_unit_file_bindings with ops := path18_root_file_ops }

/-- Only the installed loop's terminating source branch is used. -/
theorem path18_io_loop_done {S A : Type}
    (step : S → JuliaLean.base.io.M Unit (Sum A S)) (state : S) (result : A)
    (hstep : step state () = some (.ok (.inl result, ()))) :
    JuliaLean.base.io.whileLoop step state () = some (.ok (result, ())) := by
  rw [JuliaLean.base.io.whileLoop.eq_def, hstep]

/-- The source pwd function terminates after the fixture's successful read. -/
theorem path18_root_pwd_core_run :
    JuliaLean.base.file.pwd path18_root_file_ops () = some (.ok ("/", ())) := by
  change JuliaLean.base.io.whileLoop
    (fun (_ : Unit) => path18_unit_return (Sum.inl (β := Unit) "/")) () () = _
  exact path18_io_loop_done _ () "/" rfl

/-- The concrete runtime fixture supplies the required pwd premise. -/
theorem path18_root_pwd_run :
    JuliaLean.base.file.pwd path18_root_file_bindings.ops () = some (.ok ("/", ())) :=
  path18_root_pwd_core_run

/-! Exact relpath spelling counterexample -/

open JuliaLean JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- A two-byte, absolute Unix input built directly by the public Julia reproduction. -/
def pathrel18_input : Path := ⟨[47, 97]⟩

/-- Identical nonempty inputs take relpath's immediate dot-result branch. -/
theorem pathrel18_same_run (World : Type) (files : FileBindings World) (world : World) :
    relpath files.ops .unix pathStringOps pathrel18_input pathrel18_input world =
      some (.ok ⟨[46]⟩, world) := by
  rfl

/-- The absolute input is already normalized and invokes no filesystem callback. -/
theorem pathrel18_absolute_run (World : Type) (files : FileBindings World) (world : World) :
    abspath files.ops .unix pathStringOps pathrel18_input world =
      some (.ok pathrel18_input, world) := by
  rfl

/-- Joining the returned dot component preserves the directory marker on normalization. -/
theorem pathrel18_join_run :
    joinpathStrings .unix pathStringOps [pathrel18_input, ⟨[46]⟩] =
      .ok ⟨[47, 97, 47, 46]⟩ := by
  rfl

/-- The resulting directory spelling differs from the original normalized byte string. -/
theorem pathrel18_normalized_join_differs :
    normpath .unix pathStringOps ⟨[47, 97, 47, 46]⟩ ≠ pathrel18_input := by
  decide

/-- The pure path branches violate exact spelling roundtrip for every suitable cwd interface. -/
theorem pathrel18_roundtrip_counterexample (World : Type) (files : FileBindings World)
    (world : World)
    (hpwd : JuliaLean.base.file.pwd files.ops world = some (.ok ("/", world))) :
    ¬ RelpathRoundtrip := by
  intro h
  have hcwd : isabspath .unix ⟨("/" : String).toUTF8.toList⟩ = true := by
    rw [show ("/" : String) = String.singleton '/' from rfl,
      String.toUTF8_eq_toByteArray, String.toByteArray_singleton,
      List.utf8Encode_singleton]
    simp [String.utf8EncodeChar.eq_def, ByteArray.toList, ByteArray.toList.loop.eq_def,
      List.size_toByteArray, List.getElem_toByteArray]
    decide
  obtain ⟨_, absolutePath, absoluteStart, joined, hpath, hstart, hjoin, hnorm⟩ :=
    h World files .unix pathStringOps world world "/" pathrel18_input pathrel18_input
      ⟨[46]⟩ hpwd hcwd (pathrel18_same_run World files world)
  have hpathEq : pathrel18_input = absolutePath :=
    Except.ok.inj (congrArg Prod.fst (Option.some.inj
      ((pathrel18_absolute_run World files world).symm.trans hpath)))
  have hstartEq : pathrel18_input = absoluteStart :=
    Except.ok.inj (congrArg Prod.fst (Option.some.inj
      ((pathrel18_absolute_run World files world).symm.trans hstart)))
  rw [← hpathEq] at hnorm
  rw [← hstartEq] at hjoin
  have hjoined : (⟨[47, 97, 47, 46]⟩ : Path) = joined :=
    Except.ok.inj (pathrel18_join_run.symm.trans hjoin)
  rw [← hjoined] at hnorm
  exact pathrel18_normalized_join_differs hnorm

/-- The public Julia reproduction uses these identical, constructible absolute inputs. -/
theorem PathsRelpathRoundtrip_refuted : ¬ JuliaLean.Proofs.base.path.RelpathRoundtrip :=
  pathrel18_roundtrip_counterexample Unit path18_root_file_bindings () path18_root_pwd_run

/-! Separator-free reconstruction -/

open JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The run splitter always contains at least its terminal component. -/
theorem clean18_runs_nonempty (os : Platform) (bytes : List UInt8) : splitRuns os bytes ≠ [] := by
  induction bytes with
  | nil => simp only [splitRuns, ne_eq, reduceCtorEq, not_false_eq_true]
  | cons first rest ih =>
    cases hr : splitRuns os rest with
    | nil => exact False.elim (ih hr)
    | cons word words =>
      simp only [splitRuns, hr]
      split
      · split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- A byte string without separators is a single run. -/
theorem clean18_runs_name (os : Platform) (bytes : List UInt8)
    (h : ∀ b ∈ bytes, isSep os b = false) : splitRuns os bytes = [bytes] := by
  induction bytes with
  | nil => rfl
  | cons first rest ih =>
    have hf : isSep os first = false := h first (by simp)
    have ht : ∀ b ∈ rest, isSep os b = false := by intro b hb; exact h b (List.mem_cons_of_mem first hb)
    simp only [splitRuns, ih ht, hf, Bool.false_eq_true, ite_false]

/-- Adding a name prefix extends the first run and leaves later runs unchanged. -/
theorem clean18_runs_prefix (os : Platform) (pre suffix : List UInt8)
    (h : ∀ b ∈ pre, isSep os b = false) (word : List UInt8) (words : List (List UInt8))
    (hs : splitRuns os suffix = word :: words) :
    splitRuns os (pre ++ suffix) = (pre ++ word) :: words := by
  induction pre with
  | nil => simpa only [List.nil_append] using hs
  | cons first rest ih =>
    have hf : isSep os first = false := h first (by simp)
    have ht : ∀ b ∈ rest, isSep os b = false := by intro b hb; exact h b (List.mem_cons_of_mem first hb)
    simp only [List.cons_append, splitRuns, ih ht, hf, Bool.false_eq_true, ite_false]


theorem clean18_separator (os : Platform) : isSep os (separator os) = true := by
  cases os <;> rfl

/-- A canonical spelling begins with the first name's nonseparator byte. -/
theorem clean18_join_head (os : Platform) (first : List UInt8) (tail : List (List UInt8))
    (hn : first ≠ []) (hs : ∀ b ∈ first, isSep os b = false) :
    (joinSep os (first :: tail)).head?.map (isSep os) = some false := by
  cases first with
  | nil => exact False.elim (hn rfl)
  | cons byte bytes =>
    have hb : isSep os byte = false := hs byte (List.mem_cons_self)
    cases tail <;> simp only [joinSep, List.cons_append, List.head?_cons, Option.map_some, hb]

/-- Splitting the platform spelling recovers every nonempty separator-free name. -/
theorem clean18_split_join_names (os : Platform) (parts : List (List UInt8))
    (hn : parts ≠ [])
    (hp : ∀ part ∈ parts, part ≠ [] ∧ ∀ b ∈ part, isSep os b = false) :
    splitRuns os (joinSep os parts) = parts := by
  induction parts with
  | nil => exact False.elim (hn rfl)
  | cons first tail ih =>
    have hf := hp first List.mem_cons_self
    cases tail with
    | nil => exact clean18_runs_name os first hf.2
    | cons second rest =>
      have htail : ∀ part ∈ second :: rest, part ≠ [] ∧ ∀ b ∈ part, isSep os b = false := by
        intro part hm
        exact hp part (List.mem_cons_of_mem first hm)
      have ht := ih (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) htail
      have hs := htail second List.mem_cons_self
      have hh := clean18_join_head os second rest hs.1 hs.2
      have hsep : splitRuns os (separator os :: joinSep os (second :: rest)) =
          [] :: second :: rest := by
        simp only [splitRuns, ht, clean18_separator, ite_true, hh]
        rfl
      simpa only [joinSep, List.append_nil] using
        clean18_runs_prefix os first (separator os :: joinSep os (second :: rest)) hf.2 []
          (second :: rest) hsep

/-- Empty-run filtering extends the reconstruction law to the empty name list. -/
theorem clean18_split_join_filtered (os : Platform) (parts : List (List UInt8))
    (hp : ∀ part ∈ parts, part ≠ [] ∧ ∀ b ∈ part, isSep os b = false) :
    (splitRuns os (joinSep os parts)).filter (fun part => part ≠ []) = parts := by
  cases parts with
  | nil => rfl
  | cons first rest =>
    rw [clean18_split_join_names os (first :: rest) (by simp) hp]
    apply List.filter_eq_self.mpr
    intro part hm
    exact decide_eq_true (hp part hm).1

/-- Every emitted run excludes every platform separator. -/
theorem clean18_run_no_separators (os : Platform) (bytes part : List UInt8)
    (hm : part ∈ splitRuns os bytes) : ∀ b ∈ part, isSep os b = false := by
  induction bytes generalizing part with
  | nil =>
    simp only [splitRuns, List.mem_singleton] at hm
    subst part
    intro b hb
    cases hb
  | cons first rest ih =>
    have hn := clean18_runs_nonempty os rest
    cases hr : splitRuns os rest with
    | nil => exact False.elim (hn hr)
    | cons word words =>
      by_cases hs : isSep os first = true
      · simp only [splitRuns, hr, hs, ite_true] at hm
        split at hm
        · exact ih part (by rw [hr]; exact hm)
        · rcases List.mem_cons.mp hm with he | hm
          · subst part
            intro b hb
            cases hb
          · exact ih part (by rw [hr]; exact hm)
      · have hs' : isSep os first = false := Bool.eq_false_iff.mpr hs
        simp only [splitRuns, hr, hs', Bool.false_eq_true, ite_false] at hm
        rcases List.mem_cons.mp hm with he | hm
        · subst part
          intro b hb
          rcases List.mem_cons.mp hb with he | hb
          · simpa only [he] using hs'
          · exact ih word (by rw [hr]; exact List.mem_cons_self) b hb
        · exact ih part (by rw [hr]; exact List.mem_cons_of_mem word hm)

/-- Prefixing any canonical separator does not change the nonempty names. -/
theorem clean18_prepend_separator_filtered (os : Platform) (bytes : List UInt8) :
    (splitRuns os (separator os :: bytes)).filter (fun part => part ≠ []) =
      (splitRuns os bytes).filter (fun part => part ≠ []) := by
  have hn := clean18_runs_nonempty os bytes
  cases hr : splitRuns os bytes with
  | nil => exact False.elim (hn hr)
  | cons word words =>
    simp only [splitRuns, hr, clean18_separator, ite_true]
    split <;> rfl

/-- Appending a separator either preserves the trailing empty run or creates it. -/
theorem clean18_append_separator_runs (os : Platform) (bytes : List UInt8) :
    splitRuns os (bytes ++ [separator os]) =
      if bytes.getLast?.map (isSep os) == some true then splitRuns os bytes
      else splitRuns os bytes ++ [[]] := by
  induction bytes with
  | nil => simp [splitRuns, clean18_separator]
  | cons first rest ih =>
    cases rest with
    | nil =>
      cases hs : isSep os first <;>
        simp [splitRuns, clean18_separator, hs]
    | cons second rest =>
      have hn := clean18_runs_nonempty os (second :: rest)
      cases hr : splitRuns os (second :: rest) with
      | nil => exact False.elim (hn hr)
      | cons word words =>
        simp only [List.cons_append] at ih
        simp only [List.cons_append, List.getLast?_cons_cons]
        rw [splitRuns, ih]
        cases he : ((second :: rest).getLast?.map (isSep os) == some true) <;>
          simp only [he, hr, Bool.false_eq_true, ite_false, ite_true]
        all_goals
          rw [splitRuns]
          simp only [hr, List.head?_cons, Option.map_some]
          by_cases hf : isSep os first = true <;>
            by_cases hs : (some (isSep os second) == some true) = true <;>
            simp only [hf, hs, Bool.false_eq_true, ite_false, ite_true, List.cons_append]


/-- Suffixing a canonical separator does not change the nonempty names. -/
theorem clean18_append_separator_filtered (os : Platform) (bytes : List UInt8) :
    (splitRuns os (bytes ++ [separator os])).filter (fun part => part ≠ []) =
      (splitRuns os bytes).filter (fun part => part ≠ []) := by
  rw [clean18_append_separator_runs]
  split
  · rfl
  · simp only [List.filter_append, List.filter_cons, List.filter_nil,
      ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false,
      List.append_nil]

/-- The nonempty names survive optional root and directory-marker spelling. -/
theorem clean18_optional_boundaries (os : Platform) (bytes : List UInt8)
    (root directory : Bool) :
    (splitRuns os ((if root then [separator os] else []) ++ bytes ++
      (if directory then [separator os] else []))).filter (fun part => part ≠ []) =
      (splitRuns os bytes).filter (fun part => part ≠ []) := by
  cases root <;> cases directory <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, List.nil_append,
      List.append_nil, List.cons_append, clean18_prepend_separator_filtered,
      clean18_append_separator_filtered]

/-- A separator-free prefix cannot introduce adjacent separators. -/
theorem clean18_no_double_prefix (os : Platform) (pre suffix : List UInt8)
    (hp : ∀ b ∈ pre, isSep os b = false) (hs : NoDoubleSeparator os suffix) :
    NoDoubleSeparator os (pre ++ suffix) := by
  induction pre with
  | nil => exact hs
  | cons first rest ih =>
    have hf := hp first List.mem_cons_self
    have ht : ∀ b ∈ rest, isSep os b = false := by
      intro b hb; exact hp b (List.mem_cons_of_mem first hb)
    have hrest := ih ht
    change NoDoubleSeparator os (first :: (rest ++ suffix))
    cases he : rest ++ suffix with
    | nil => trivial
    | cons next tail =>
      change (isSep os first && isSep os next) = false ∧ NoDoubleSeparator os (next :: tail)
      refine ⟨?_, ?_⟩
      · rw [hf]; rfl
      · simpa only [he] using hrest

/-- A root marker is safe when the following byte is not a separator. -/
theorem clean18_no_double_prepend (os : Platform) (bytes : List UInt8)
    (hn : NoDoubleSeparator os bytes)
    (hh : bytes.head?.map (isSep os) ≠ some true) :
    NoDoubleSeparator os (separator os :: bytes) := by
  cases bytes with
  | nil => trivial
  | cons first rest =>
    have hf : isSep os first = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      apply hh
      simp only [List.head?_cons, Option.map_some, ht]
    change (isSep os (separator os) && isSep os first) = false ∧
      NoDoubleSeparator os (first :: rest)
    refine ⟨?_, hn⟩
    rw [hf, Bool.and_false]

/-- A trailing directory marker is safe when the prior final byte is not a separator. -/
theorem clean18_no_double_append (os : Platform) (bytes : List UInt8)
    (hn : NoDoubleSeparator os bytes)
    (hl : bytes.getLast?.map (isSep os) ≠ some true) :
    NoDoubleSeparator os (bytes ++ [separator os]) := by
  induction bytes with
  | nil => trivial
  | cons first rest ih =>
    cases rest with
    | nil =>
      have hf : isSep os first = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        apply hl
        simp only [List.getLast?_cons, List.getLast?_nil, Option.getD_none,
          Option.map_some, ht]
      change (isSep os first && isSep os (separator os)) = false ∧ True
      exact ⟨by rw [hf]; rfl, trivial⟩
    | cons second rest =>
      change (isSep os first && isSep os second) = false ∧
        NoDoubleSeparator os ((second :: rest) ++ [separator os])
      refine ⟨hn.1, ih hn.2 ?_⟩
      simpa only [List.getLast?_cons_cons] using hl

/-- Joining nonempty separator-free names inserts only isolated platform separators. -/
theorem clean18_join_no_double (os : Platform) (parts : List (List UInt8))
    (hp : ∀ part ∈ parts, part ≠ [] ∧ ∀ b ∈ part, isSep os b = false) :
    NoDoubleSeparator os (joinSep os parts) := by
  induction parts with
  | nil => trivial
  | cons first rest ih =>
    have hf := hp first List.mem_cons_self
    cases rest with
    | nil =>
      simpa only [List.append_nil, joinSep] using clean18_no_double_prefix os first [] hf.2 trivial
    | cons second rest =>
      have ht : ∀ part ∈ second :: rest, part ≠ [] ∧ ∀ b ∈ part, isSep os b = false := by
        intro part hm; exact hp part (List.mem_cons_of_mem first hm)
      have hhead := clean18_join_head os second rest (ht second List.mem_cons_self).1
        (ht second List.mem_cons_self).2
      apply clean18_no_double_prefix os first (separator os :: joinSep os (second :: rest)) hf.2
      apply clean18_no_double_prepend os (joinSep os (second :: rest)) (ih ht)
      rw [hhead]
      decide

/-! Source separator-loop bridge -/

open JuliaLean JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The first matching byte decomposes the scanned suffix exactly. -/
theorem pathsep18_find_decomp (p : UInt8 → Bool) (bytes : List UInt8)
    (start index : Nat) (h : findFrom p start bytes = some index) :
    ∃ before byte after, bytes = before ++ byte :: after ∧
      start + before.length = index ∧ p byte = true ∧
      ∀ b ∈ before, p b = false := by
  induction bytes generalizing start with
  | nil => simp only [findFrom] at h; cases h
  | cons first rest ih =>
    by_cases hp : p first = true
    · have hi : start = index := by simpa only [findFrom, hp, ite_true, Option.some.injEq] using h
      refine ⟨[], first, rest, rfl, ?_, hp, ?_⟩
      · simpa only [List.length_nil, Nat.add_zero] using hi
      · intro b hb; cases hb
    · have hp' : p first = false := Bool.eq_false_iff.mpr hp
      have htail : findFrom p (start + 1) rest = some index := by
        simpa only [findFrom, hp', Bool.false_eq_true, ite_false] using h
      obtain ⟨before, byte, after, he, hi, hb, hall⟩ := ih (start + 1) htail
      refine ⟨first :: before, byte, after, ?_, ?_, hb, ?_⟩
      · simp only [List.cons_append, he]
      · simp only [List.length_cons]; omega
      · intro b hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hp'
        · exact hall b hm

/-- The fallback end index is the length of the initial nonmatching run. -/
theorem pathsep18_find_getD (p : UInt8 → Bool) (bytes : List UInt8) (start : Nat) :
    (findFrom p start bytes).getD (start + bytes.length) =
      start + (bytes.takeWhile (fun b => !p b)).length := by
  induction bytes generalizing start with
  | nil => simp only [findFrom, Option.getD_none, List.length_nil, List.takeWhile_nil, Nat.add_zero]
  | cons first rest ih =>
    by_cases hp : p first = true
    · simp [findFrom, hp]
    · have hp' : p first = false := Bool.eq_false_iff.mpr hp
      have he : start + (first :: rest).length = (start + 1) + rest.length := by simp only [List.length_cons]; omega
      simp only [findFrom, hp', Bool.false_eq_true, ite_false, he]
      rw [ih]
      simp [hp', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The head left after dropping a matching run is nonmatching. -/
theorem pathsep18_dropWhile_head (p : UInt8 → Bool) (bytes : List UInt8) :
    (bytes.dropWhile p).head?.map p ≠ some true := by
  induction bytes with
  | nil => simp only [List.dropWhile_nil, List.head?_nil, Option.map_none, ne_eq, reduceCtorEq, not_false_eq_true]
  | cons first rest ih =>
    by_cases hp : p first = true
    · simpa only [List.dropWhile_cons, hp, ite_true] using ih
    · have hp' : p first = false := Bool.eq_false_iff.mpr hp
      simp [List.dropWhile_cons, hp']

/-- Dropping the matching prefix by its length gives dropWhile. -/
theorem pathsep18_drop_takeWhile (p : UInt8 → Bool) (bytes : List UInt8) :
    bytes.drop (bytes.takeWhile p).length = bytes.dropWhile p := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := bytes)
  have hdrop := congrArg (List.drop (bytes.takeWhile p).length) h
  simpa only [List.drop_left] using hdrop.symm

/-- The run splitter always contains at least its terminal component. -/
theorem pathsep18_runs_nonempty (os : Platform) (bytes : List UInt8) : splitRuns os bytes ≠ [] := by
  induction bytes with
  | nil => simp only [splitRuns, ne_eq, reduceCtorEq, not_false_eq_true]
  | cons first rest ih =>
    cases hr : splitRuns os rest with
    | nil => exact False.elim (ih hr)
    | cons word words =>
      simp only [splitRuns, hr]
      split
      · split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- A byte string without separators is a single run. -/
theorem pathsep18_runs_name (os : Platform) (bytes : List UInt8)
    (h : ∀ b ∈ bytes, isSep os b = false) : splitRuns os bytes = [bytes] := by
  induction bytes with
  | nil => rfl
  | cons first rest ih =>
    have hf : isSep os first = false := h first (by simp)
    have ht : ∀ b ∈ rest, isSep os b = false := by intro b hb; exact h b (List.mem_cons_of_mem first hb)
    simp only [splitRuns, ih ht, hf, Bool.false_eq_true, ite_false]

/-- Adding a name prefix extends the first run and leaves later runs unchanged. -/
theorem pathsep18_runs_prefix (os : Platform) (pre suffix : List UInt8)
    (h : ∀ b ∈ pre, isSep os b = false) (word : List UInt8) (words : List (List UInt8))
    (hs : splitRuns os suffix = word :: words) :
    splitRuns os (pre ++ suffix) = (pre ++ word) :: words := by
  induction pre with
  | nil => simpa only [List.nil_append] using hs
  | cons first rest ih =>
    have hf : isSep os first = false := h first (by simp)
    have ht : ∀ b ∈ rest, isSep os b = false := by intro b hb; exact h b (List.mem_cons_of_mem first hb)
    simp only [List.cons_append, splitRuns, ih ht, hf, Bool.false_eq_true, ite_false]


/-- A complete separator run inserts just one boundary. -/
theorem pathsep18_runs_separator (os : Platform) (byte : UInt8) (after : List UInt8)
    (hb : isSep os byte = true) :
    splitRuns os (byte :: after) = [] :: splitRuns os (after.dropWhile (isSep os)) := by
  induction after generalizing byte with
  | nil => simp [splitRuns, hb]
  | cons first rest ih =>
    by_cases hf : isSep os first = true
    · have hi := ih first hf
      have hn := pathsep18_runs_nonempty os (first :: rest)
      cases hr : splitRuns os (first :: rest) with
      | nil => exact False.elim (hn hr)
      | cons word words =>
        rw [splitRuns, hr]
        simp only [hb, ite_true, List.head?_cons, Option.map_some, hf,
          beq_self_eq_true, List.dropWhile_cons]
        simpa only [hr] using hi
    · have hf' : isSep os first = false := Bool.eq_false_iff.mpr hf
      have hn := pathsep18_runs_nonempty os (first :: rest)
      cases hr : splitRuns os (first :: rest) with
      | nil => exact False.elim (hn hr)
      | cons word words =>
        rw [splitRuns, hr]
        simp only [hb, ite_true, List.head?_cons, Option.map_some, hf',
          List.dropWhile_cons, Bool.false_eq_true, ite_false]
        rw [hr]
        rfl

/-- A successful source scan identifies the emitted word and the next remaining runs. -/
theorem pathsep18_scan_some (os : Platform) (bytes : List UInt8) (start index : Nat)
    (h : findAtOrAfter (isSep os) bytes start = some index) :
    let word := (bytes.take index).drop start
    let next := (findAtOrAfter (fun b => !isSep os b) bytes (index + 1)).getD bytes.length
    start < next ∧ next ≤ bytes.length ∧
      splitRuns os (bytes.drop start) = word :: splitRuns os (bytes.drop next) := by
  dsimp only
  obtain ⟨pre, byte, after, hd, hi, hb, hp⟩ :=
    pathsep18_find_decomp (isSep os) (bytes.drop start) start index h
  have hlen := congrArg List.length hd
  simp only [List.length_drop, List.length_append, List.length_cons] at hlen
  have hstart : start ≤ bytes.length := by omega
  have hindex : index < bytes.length := by omega
  have hword : (bytes.take index).drop start = pre := by
    rw [List.drop_take, hd]
    have hsub : index - start = pre.length := by omega
    rw [hsub, List.take_append_length]
  have hafter : bytes.drop (index + 1) = after := by
    have he : index + 1 = start + (pre.length + 1) := by omega
    rw [he, ← List.drop_drop, hd]
    simp only [List.drop_append, List.length_cons, Nat.add_sub_cancel_left,
      List.drop_succ_cons, List.drop_zero]
    have hz : pre.drop (pre.length + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hz, List.nil_append]
  have htotal : bytes.length = (index + 1) + after.length := by
    have he := congrArg List.length hafter
    simp only [List.length_drop] at he
    omega
  have hnext : (findAtOrAfter (fun b => !isSep os b) bytes (index + 1)).getD bytes.length =
      (index + 1) + (after.takeWhile (isSep os)).length := by
    unfold findAtOrAfter
    rw [hafter, htotal, pathsep18_find_getD]
    simp only [Bool.not_not]
  rw [hnext]
  have ht : (after.takeWhile (isSep os)).length ≤ after.length :=
    (List.takeWhile_sublist (isSep os)).length_le
  refine ⟨by omega, by omega, ?_⟩
  have hdrop : bytes.drop ((index + 1) + (after.takeWhile (isSep os)).length) =
      after.dropWhile (isSep os) := by
    rw [← List.drop_drop, hafter, pathsep18_drop_takeWhile]
  rw [hword, hdrop, hd]
  simpa only [List.append_nil] using pathsep18_runs_prefix os pre (byte :: after) hp []
    (splitRuns os (after.dropWhile (isSep os)))
    (pathsep18_runs_separator os byte after hb)


/-- One source iteration, factored for the loop invariant proof. -/
def pathsep18_step (os : Platform) (ops : StringOps) (bytes : List UInt8) (keep : Bool)
    (_ : Unit) (state : Array Path × Nat) : Id (ForInStep (Array Path × Nat)) :=
  let out := state.1
  let start := state.2
  let nextsep := findAtOrAfter (isSep os) bytes start
  let stop := nextsep.getD bytes.length
  let word := ops.fromBytes ((bytes.take stop).drop start)
  let out := if keep || !word.bytes.isEmpty then out.push word else out
  match nextsep with
  | none => .done (out, start)
  | some index =>
    let next := (findAtOrAfter (fun b => !isSep os b) bytes (index + 1)).getD bytes.length
    .yield (out, next)

/-- The source loop with an arbitrary initial accumulator and scan position. -/
def pathsep18_loop (os : Platform) (ops : StringOps) (bytes : List UInt8) (keep : Bool)
    (start : Nat) (out : Array Path) : Id (Array Path × Nat) :=
  Lean.Loop.forIn {} (out, start) (pathsep18_step os ops bytes keep)

theorem pathsep18_id_bind {α β : Type} (a : Id α) (f : α → Id β) :
    (a >>= f) = f a := rfl

theorem pathsep18_id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- The factored iteration has exactly the source body. -/
theorem pathsep18_source_loop (os : Platform) (ops : StringOps) (path : Path) (keep : Bool) :
    splitAtSeparators os ops path keep =
      (pathsep18_loop os ops path.bytes keep 0 #[]).1.toList := by
  unfold splitAtSeparators pathsep18_loop
  simp only [Id.run, pathsep18_id_bind, pathsep18_id_pure]
  apply congrArg (fun state : Array Path × Nat => state.1.toList)
  apply congrArg (fun step => Lean.Loop.forIn ({} : Lean.Loop) (#[], 0) step)
  funext x state
  rcases state with ⟨out, start⟩
  simp only [pathsep18_step, ite_true]
  split <;> split <;> simp_all

/-- One-step equation for the existing Id loop, obtained from Lean's core loop law. -/
theorem pathsep18_loop_unfold (os : Platform) (ops : StringOps) (bytes : List UInt8) (keep : Bool)
    (start : Nat) (out : Array Path) :
    pathsep18_loop os ops bytes keep start out =
      match pathsep18_step os ops bytes keep () (out, start) with
      | .done state => state
      | .yield state => pathsep18_loop os ops bytes keep state.2 state.1 := by
  unfold pathsep18_loop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [pathsep18_id_bind, pathsep18_id_pure]
  cases pathsep18_step os ops bytes keep () (out, start) with
  | done state => rfl
  | yield state => cases state; rfl

/-- The declarative runs retained by keepempty. -/
def pathsep18_kept (os : Platform) (ops : StringOps) (bytes : List UInt8) (keep : Bool) : List Path :=
  ((splitRuns os bytes).filter (fun word => keep || !word.isEmpty)).map ops.fromBytes

/-- Exact loop invariant: output is the prior accumulator followed by all remaining runs. -/
theorem pathsep18_loop_runs (os : Platform) (ops : StringOps) (bytes : List UInt8) (keep : Bool)
    (start : Nat) (out : Array Path) :
    (pathsep18_loop os ops bytes keep start out).1.toList =
      out.toList ++ pathsep18_kept os ops (bytes.drop start) keep := by
  cases hfind : findAtOrAfter (isSep os) bytes start with
  | none =>
    have hn : ∀ byte ∈ bytes.drop start, isSep os byte = false :=
      findFromNoneAllFalse (isSep os) start (bytes.drop start) hfind
    have hruns := pathsep18_runs_name os (bytes.drop start) hn
    rw [pathsep18_loop_unfold]
    simp only [pathsep18_step, hfind, Option.getD_none, List.take_length,
      StringOps.fromBytesBytes, pathsep18_kept, hruns]
    split <;> simp_all [List.filter_cons, Array.toList_push]
  | some index =>
    let word := (bytes.take index).drop start
    let next := (findAtOrAfter (fun b => !isSep os b) bytes (index + 1)).getD bytes.length
    obtain ⟨hnext, hbound, hruns⟩ := pathsep18_scan_some os bytes start index hfind
    change start < next at hnext
    change next ≤ bytes.length at hbound
    change splitRuns os (bytes.drop start) = word :: splitRuns os (bytes.drop next) at hruns
    by_cases hk : (keep || !word.isEmpty) = true
    · calc
        (pathsep18_loop os ops bytes keep start out).1.toList =
            (pathsep18_loop os ops bytes keep next (out.push (ops.fromBytes word))).1.toList := by
          rw [pathsep18_loop_unfold]
          simp only [pathsep18_step, hfind, Option.getD_some, StringOps.fromBytesBytes]
          rw [show (keep || !((bytes.take index).drop start).isEmpty) = true from hk]
          rfl
        _ = (out.push (ops.fromBytes word)).toList ++
            pathsep18_kept os ops (bytes.drop next) keep :=
          pathsep18_loop_runs os ops bytes keep next (out.push (ops.fromBytes word))
        _ = out.toList ++ pathsep18_kept os ops (bytes.drop start) keep := by
          simp only [pathsep18_kept, hruns, List.filter_cons, hk, ite_true,
            List.map_cons, Array.toList_push, List.append_assoc, List.singleton_append]
    · have hk' : (keep || !word.isEmpty) = false := Bool.eq_false_iff.mpr hk
      calc
        (pathsep18_loop os ops bytes keep start out).1.toList =
            (pathsep18_loop os ops bytes keep next out).1.toList := by
          rw [pathsep18_loop_unfold]
          simp only [pathsep18_step, hfind, Option.getD_some, StringOps.fromBytesBytes]
          rw [show (keep || !((bytes.take index).drop start).isEmpty) = false from hk']
          rfl
        _ = out.toList ++ pathsep18_kept os ops (bytes.drop next) keep :=
          pathsep18_loop_runs os ops bytes keep next out
        _ = out.toList ++ pathsep18_kept os ops (bytes.drop start) keep := by
          simp only [pathsep18_kept, hruns, List.filter_cons, hk', Bool.false_eq_true, ite_false]
termination_by bytes.length - start
decreasing_by all_goals omega

/-- The public source splitter equals the model's run decomposition with the specified empty policy. -/
theorem pathsep18_splitAtSeparators_runs (os : Platform) (ops : StringOps) (path : Path) (keep : Bool) :
    splitAtSeparators os ops path keep = pathsep18_kept os ops path.bytes keep := by
  rw [pathsep18_source_loop, pathsep18_loop_runs]
  rfl

/-! Preservation of an ordinary final component -/

open JuliaLean JuliaLean.base.path JuliaLean.Proofs.base.path

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Deleting a name-parent pair preserves an ordinary final component. -/
theorem pathlast18_remove_last (parts after : List (List UInt8)) (name : List UInt8)
    (h : removeFirstPair parts = some after) (hl : parts.getLast? = some name)
    (hn : name ≠ dotdot) : after.getLast? = some name := by
  induction parts generalizing after with
  | nil => cases h
  | cons first tail ih =>
    cases tail with
    | nil => cases h
    | cons second rest =>
      rw [removeFirstPair] at h
      split at h
      · rename_i hc
        have hb : second = dotdot := by
          exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).2
        have he : rest = after := Option.some.inj h
        subst after
        cases rest with
        | nil =>
          have he : second = name := by simpa only [List.getLast?_cons_cons,
            List.getLast?_singleton, Option.some.injEq] using hl
          exact False.elim (hn (he.symm.trans hb))
        | cons third rest =>
          simpa only [List.getLast?_cons_cons] using hl
      · cases hr : removeFirstPair (second :: rest) with
        | none => simp only [hr, Option.map_none, reduceCtorEq] at h
        | some shorter =>
          have he : first :: shorter = after := by
            simpa only [hr, Option.map_some, Option.some.injEq] using h
          have hshort := ih shorter hr (by simpa only [List.getLast?_cons_cons] using hl)
          rw [← he, List.getLast?_cons, hshort, Option.getD_some]

/-- Every cancellation-loop iteration preserves an ordinary final component. -/
theorem pathlast18_clean_last (fuel : Nat) (parts : List (List UInt8)) (name : List UInt8)
    (hl : parts.getLast? = some name) (hn : name ≠ dotdot) :
    (cleanLoop fuel parts).getLast? = some name := by
  induction fuel generalizing parts with
  | zero => exact hl
  | succ fuel ih =>
    rw [cleanLoop]
    cases hr : removeFirstPair parts with
    | none => exact hl
    | some shorter => exact ih shorter (pathlast18_remove_last parts shorter name hr hl hn)

/-- Filtering keeps the last element when that element satisfies the predicate. -/
theorem pathlast18_filter_last {α : Type} (predicate : α → Bool) (parts : List α) (last : α)
    (hl : parts.getLast? = some last) (hp : predicate last = true) :
    (parts.filter predicate).getLast? = some last := by
  obtain ⟨before, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  simp only [List.filter_append, List.filter_cons, hp, ↓reduceIte, List.filter_nil,
    List.getLast?_append, List.getLast?_singleton, Option.some_or]

/-- A final non-parent component remains after dropping leading parents. -/
theorem pathlast18_drop_parents_last (parts : List (List UInt8)) (name : List UInt8)
    (hl : parts.getLast? = some name) (hn : name ≠ dotdot) :
    (parts.dropWhile (· == dotdot)).getLast? = some name := by
  induction parts with
  | nil => cases hl
  | cons first rest ih =>
    by_cases hf : first = dotdot
    · subst first
      cases rest with
      | nil =>
        have he : dotdot = name := Option.some.inj hl
        exact False.elim (hn he.symm)
      | cons second rest =>
        simpa only [List.dropWhile_cons, beq_self_eq_true, ↓reduceIte] using
          ih (by simpa only [List.getLast?_cons_cons] using hl)
    · simp only [List.dropWhile_cons, beq_eq_false_iff_ne.mpr hf,
        Bool.false_eq_true, ↓reduceIte]
      exact hl

/-- The final run of the source split is retained by both normalization filters. -/
theorem pathlast18_filtered_clean_last (parts : List (List UInt8)) (name : List UInt8)
    (hl : parts.getLast? = some name) (he : name ≠ [])
    (hd : name ≠ [dot]) (hp : name ≠ dotdot) :
    let filtered := (parts.filter (· ≠ [])).filter (· != [dot])
    (cleanLoop (filtered.length + 1) filtered).getLast? = some name := by
  dsimp only
  apply pathlast18_clean_last
  · apply pathlast18_filter_last
    · exact pathlast18_filter_last _ parts name hl (by simpa only [decide_eq_true_eq] using he)
    · exact bne_iff_ne.mpr hd
  · exact hp

end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.Proofs.base.path

open JuliaLean.Registry
open JuliaLean.base.path

namespace LegacyWrappers

def NormpathVarargsMethod : Prop :=
  ∀ (World S : Type) (joinPaths : List S → JuliaLean.base.path.M World Path)
    (os : Platform) (ops : StringOps) (first : S) (rest : List S) (world : World),
    normpathManyWith joinPaths os ops first rest world =
      match joinPaths (first :: rest) world with
      | none => none
      | some (.error error, after) => some (.error error, after)
      | some (.ok joined, after) => some (.ok (normpath os ops joined), after)

theorem normpathVarargsMethod : NormpathVarargsMethod := by
  intro World S joinPaths os ops first rest world
  cases joined : joinPaths (first :: rest) world with
  | none => simp [normpathManyWith, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind,
      JuliaLean.base.iterators.ret, joined]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome <;> simp [normpathManyWith, Bind.bind, Pure.pure,
      JuliaLean.base.iterators.bind, JuliaLean.base.iterators.ret, joined]

def AbspathVarargsMethod : Prop :=
  ∀ {World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
      WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal S : Type}
    (files : JuliaLean.base.file.FileOps World Handle CString StatMemory IOBuf User Group Req
      StrBuf SizeRef Dirent Stream WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal)
    (joinPaths : List S → JuliaLean.base.path.M World Path)
    (os : Platform) (ops : StringOps) (first : S) (rest : List S) (world : World),
    abspathManyWith files joinPaths os ops first rest world =
      match joinPaths (first :: rest) world with
      | none => none
      | some (.error error, after) => some (.error error, after)
      | some (.ok joined, after) => abspath files os ops joined after

theorem abspathVarargsMethod : AbspathVarargsMethod := by
  intro World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
    WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal S
    files joinPaths os ops first rest world
  cases joined : joinPaths (first :: rest) world with
  | none => simp [abspathManyWith, Bind.bind, JuliaLean.base.iterators.bind, joined]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome <;> simp [abspathManyWith, Bind.bind, JuliaLean.base.iterators.bind, joined]

theorem normpathMany_strings (os : Platform) (ops : StringOps) (first : Path) (rest : List Path) :
    normpathMany os ops first rest = (do
      let joined ← joinpathStrings os ops (first :: rest)
      pure (normpath os ops joined)) := rfl

theorem abspathMany_strings
    {World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
      WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal : Type}
    (files : JuliaLean.base.file.FileOps World Handle CString StatMemory IOBuf User Group Req
      StrBuf SizeRef Dirent Stream WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal)
    (os : Platform) (ops : StringOps) (first : Path) (rest : List Path) :
    abspathMany files os ops first rest = (do
      let joined ← liftPath (joinpathStrings os ops (first :: rest))
      abspath files os ops joined) := rfl

def checkedStringOutcome {World : Type}
    (result : Option (Except PathError StringConversionResult × World)) :
    Option (Except PathError Path × World) :=
  match result with
  | none => none
  | some (.error error, after) => some (.error error, after)
  | some (.ok (.string path), after) => some (.ok path, after)
  | some (.ok (.other got), after) => some (.error (.stringTypeError got), after)

theorem checkedString_run (World S : Type)
    (convert : S → JuliaLean.base.path.M World StringConversionResult) (value : S) (world : World) :
    checkedString convert value world = checkedStringOutcome (convert value world) := by
  cases converted : convert value world with
  | none => simp [checkedString, checkedStringOutcome, Bind.bind, Pure.pure,
      JuliaLean.base.iterators.bind, JuliaLean.base.iterators.ret, converted]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome with
    | error error => simp [checkedString, checkedStringOutcome, Bind.bind, Pure.pure,
        JuliaLean.base.iterators.bind, JuliaLean.base.iterators.ret, converted]
    | ok result =>
      cases result <;> simp [checkedString, checkedStringOutcome, Bind.bind, Pure.pure,
        JuliaLean.base.iterators.bind, JuliaLean.base.iterators.ret, converted,
        throw, throwThe, MonadExceptOf.throw]

def PurePathWrapperCorrect {World S A : Type}
    (wrapper : (S → JuliaLean.base.path.M World StringConversionResult) → S →
      JuliaLean.base.path.M World A) (method : Path → A) : Prop :=
  ∀ convert value world,
    wrapper convert value world =
      match checkedStringOutcome (convert value world) with
      | none => none
      | some (.error error, after) => some (.error error, after)
      | some (.ok path, after) => some (.ok (method path), after)

theorem checkedPurePathWrapper (World S A : Type) (method : Path → A) :
    PurePathWrapperCorrect (World := World) (S := S) (fun convert value => do
      let path ← checkedString convert value
      pure (method path)) method := by
  intro convert value world
  cases conversion : checkedStringOutcome (convert value world) with
  | none =>
    simp [Bind.bind, Pure.pure, JuliaLean.base.iterators.bind,
      JuliaLean.base.iterators.ret, checkedString_run, conversion]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome <;>
      simp [Bind.bind, Pure.pure, JuliaLean.base.iterators.bind,
        JuliaLean.base.iterators.ret, checkedString_run, conversion]

def PathAbstractWrapperMethod : Prop :=
  ∀ (World S : Type) (os : Platform) (ops : StringOps) (files : FileBindings World),
    PurePathWrapperCorrect (World := World) (S := S)
      (fun convert => isdirpathAbstract convert os ops) (isdirpath os ops) ∧
    PurePathWrapperCorrect (World := World) (S := S)
      (fun convert => splitdirAbstract convert os ops) (splitdir os ops) ∧
    PurePathWrapperCorrect (World := World) (S := S)
      (fun convert => splitdriveAbstract convert os ops) (splitdrive os ops) ∧
    PurePathWrapperCorrect (World := World) (S := S)
      (fun convert => splitextAbstract convert os ops) (splitext os ops) ∧
    PurePathWrapperCorrect (World := World) (S := S)
      (fun convert => normpathAbstract convert os ops) (normpath os ops) ∧
    PurePathWrapperCorrect (World := World) (S := S)
      (fun convert => isabspathAbstract convert os) (isabspath os) ∧
    ∀ (convert : S → JuliaLean.base.path.M World StringConversionResult) value world,
      abspathAbstract files.ops convert os ops value world =
        match checkedStringOutcome (convert value world) with
        | none => none
        | some (.error error, after) => some (.error error, after)
        | some (.ok path, after) => abspath files.ops os ops path after

theorem pathAbstractWrapperMethod : PathAbstractWrapperMethod := by
  intro World S os ops files
  refine ⟨checkedPurePathWrapper World S Bool (isdirpath os ops),
    checkedPurePathWrapper World S (Path × Path) (splitdir os ops),
    checkedPurePathWrapper World S (Path × Path) (splitdrive os ops),
    checkedPurePathWrapper World S (Path × Path) (splitext os ops),
    checkedPurePathWrapper World S Path (normpath os ops),
    checkedPurePathWrapper World S Bool (isabspath os), ?_⟩
  intro convert value world
  cases conversion : checkedStringOutcome (convert value world) with
  | none =>
    simp [abspathAbstract, Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, conversion]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome <;>
      simp [abspathAbstract, Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, conversion]

def JoinpathVarargsMethod : Prop :=
  ∀ (World S : Type) (joinPaths : List S → JuliaLean.base.path.M World StringConversionResult)
    (convertOther : Nat → JuliaLean.base.path.M World StringConversionResult)
    (paths : List S) (world : World),
    joinpathVarargsWith joinPaths convertOther paths world =
      match joinPaths paths world with
      | none => none
      | some (.error error, after) => some (.error error, after)
      | some (.ok (.string path), after) => some (.ok path, after)
      | some (.ok (.other value), after) => checkedStringOutcome (convertOther value after)

theorem joinpathVarargsMethod : JoinpathVarargsMethod := by
  intro World S joinPaths convertOther paths world
  cases joined : joinPaths paths world with
  | none => simp [joinpathVarargsWith, Bind.bind, JuliaLean.base.iterators.bind, joined]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome with
    | error error =>
      simp [joinpathVarargsWith, Bind.bind, JuliaLean.base.iterators.bind, joined]
    | ok result =>
      cases result <;>
        simp [joinpathVarargsWith, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind,
          JuliaLean.base.iterators.ret, joined, checkedString_run, checkedStringOutcome,
          JuliaLean.base.essentials.convertStringRepresentationIdentity]

theorem joinpathVarargs_string_specialization (os : Platform) (ops : StringOps)
    (paths : List Path) (convertOther : Nat → Except PathError StringConversionResult) :
    joinpathVarargsWith
      (fun values => (joinpathStrings os ops values).map StringConversionResult.string)
      convertOther paths = joinpathVarargs os ops paths := by
  cases joined : joinpathStrings os ops paths <;>
    simp only [joinpathVarargsWith, joinpathVarargs, joined] <;> rfl

def SplitpathAbstractMethod : Prop :=
  ∀ (World S : Type) (convert : S → JuliaLean.base.path.M World StringConversionResult)
    (os : Platform) (ops : StringOps) (path : S) (world : World),
    splitpathAbstractWith convert os ops path world =
      match checkedStringOutcome (convert path world) with
      | none => none
      | some (.error error, after) => some (.error error, after)
      | some (.ok converted, after) => some (.ok (splitpath os ops converted), after)

theorem splitpathAbstractMethod : SplitpathAbstractMethod := by
  intro World S convert os ops path world
  cases conversion : checkedStringOutcome (convert path world) with
  | none => simp [splitpathAbstractWith, Bind.bind, Pure.pure,
      JuliaLean.base.iterators.bind, JuliaLean.base.iterators.ret, checkedString_run, conversion]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome <;> simp [splitpathAbstractWith, Bind.bind, Pure.pure,
      JuliaLean.base.iterators.bind, JuliaLean.base.iterators.ret, checkedString_run, conversion]

def ExpanduserAbstractMethod : Prop :=
  ∀ (World S : Type) (convert : S → JuliaLean.base.path.M World StringConversionResult)
    (os : Platform) (ops : StringOps) (fs : FileSystemOps) (path : S) (world : World),
    expanduserAbstractWith convert os ops fs path world =
      match checkedStringOutcome (convert path world) with
      | none => none
      | some (.error error, after) => some (.error error, after)
      | some (.ok converted, after) => some (expanduser os ops fs converted, after)

theorem expanduserAbstractMethod : ExpanduserAbstractMethod := by
  intro World S convert os ops fs path world
  change ((checkedString convert path >>= fun converted => liftPath (expanduser os ops fs converted)) world) = _
  cases conversion : checkedStringOutcome (convert path world) with
  | none => simp [Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, conversion]
  | some result =>
    rcases result with ⟨outcome, after⟩
    cases outcome with
    | error error => simp [Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, conversion]
    | ok converted =>
      cases expanded : expanduser os ops fs converted <;>
        simp [Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, JuliaLean.base.iterators.ret,
          liftPath, checkedString_run, conversion, expanded, throw, throwThe, MonadExceptOf.throw]

def RelpathAbstractMethod : Prop :=
  ∀ {World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
      WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal S T : Type}
    (files : JuliaLean.base.file.FileOps World Handle CString StatMemory IOBuf User Group Req
      StrBuf SizeRef Dirent Stream WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal)
    (toPath : S → JuliaLean.base.path.M World StringConversionResult)
    (toStart : T → JuliaLean.base.path.M World StringConversionResult)
    (os : Platform) (ops : StringOps) (path : S) (startpath : T) (world : World),
    relpathAbstractWith files toPath toStart os ops path startpath world =
      match checkedStringOutcome (toPath path world) with
      | none => none
      | some (.error error, after) => some (.error error, after)
      | some (.ok convertedPath, middle) =>
        match checkedStringOutcome (toStart startpath middle) with
        | none => none
        | some (.error error, after) => some (.error error, after)
        | some (.ok convertedStart, after) => relpath files os ops convertedPath convertedStart after

theorem relpathAbstractMethod : RelpathAbstractMethod := by
  intro World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
    WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal S T
    files toPath toStart os ops path startpath world
  cases first : checkedStringOutcome (toPath path world) with
  | none => simp [relpathAbstractWith, Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, first]
  | some result =>
    rcases result with ⟨outcome, middle⟩
    cases outcome with
    | error error => simp [relpathAbstractWith, Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, first]
    | ok convertedPath =>
      cases second : checkedStringOutcome (toStart startpath middle) with
      | none => simp [relpathAbstractWith, Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, first, second]
      | some result =>
        rcases result with ⟨outcome, after⟩
        cases outcome <;> simp [relpathAbstractWith, Bind.bind, JuliaLean.base.iterators.bind, checkedString_run, first, second]

theorem splitpathAbstract_conversion {S : Type} (convert : S → Path)
    (os : Platform) (ops : StringOps) (path : S) :
    splitpathAbstract convert os ops path = splitpath os ops (convert path) := rfl

theorem expanduserAbstract_conversion {S : Type} (convert : S → Path)
    (os : Platform) (ops : StringOps) (fs : FileSystemOps) (path : S) :
    expanduserAbstract convert os ops fs path = expanduser os ops fs (convert path) := rfl

theorem relpathAbstract_conversion
    {World Handle CString StatMemory IOBuf User Group Req StrBuf SizeRef Dirent Stream
      WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal S : Type}
    (files : JuliaLean.base.file.FileOps World Handle CString StatMemory IOBuf User Group Req
      StrBuf SizeRef Dirent Stream WString Chan Cmd Pipe IterObj DirPtr DiskBuf DiskStatRaw PathVal)
    (convert : S → Path) (os : Platform) (ops : StringOps) (path startpath : S) :
    relpathAbstract files convert os ops path startpath =
      relpath files os ops (convert path) (convert startpath) := rfl

def DirnameAbstractMethod : Prop :=
  ∀ (World S P : Type) (splitDir : S → JuliaLean.base.io.M World (P × P))
    (path : S) (world : World),
    dirnameAbstractWith splitDir path world =
      match splitDir path world with
      | none => none
      | some (.error failure) => some (.error failure)
      | some (.ok ((parent, _), after)) => some (.ok (parent, after))

theorem dirnameAbstractMethod : DirnameAbstractMethod := by
  intro World S P splitDir path world
  cases outcome : splitDir path world with
  | none => simp [dirnameAbstractWith, Bind.bind, Pure.pure, outcome]
  | some result =>
    cases result <;> simp [dirnameAbstractWith, Bind.bind, Pure.pure, outcome]

def BasenameAbstractMethod : Prop :=
  ∀ (World S P : Type) (splitDir : S → JuliaLean.base.io.M World (P × P))
    (path : S) (world : World),
    basenameAbstractWith splitDir path world =
      match splitDir path world with
      | none => none
      | some (.error failure) => some (.error failure)
      | some (.ok ((_, leaf), after)) => some (.ok (leaf, after))

theorem basenameAbstractMethod : BasenameAbstractMethod := by
  intro World S P splitDir path world
  cases outcome : splitDir path world with
  | none => simp [basenameAbstractWith, Bind.bind, Pure.pure, outcome]
  | some result =>
    cases result <;> simp [basenameAbstractWith, Bind.bind, Pure.pure, outcome]

theorem dirnameAbstract_conversion {S : Type} (toString : S → Path)
    (os : Platform) (ops : StringOps) (path : S) :
    dirnameAbstract toString os ops path = (splitdir os ops (toString path)).1 := rfl

theorem basenameAbstract_conversion {S : Type} (toString : S → Path)
    (os : Platform) (ops : StringOps) (path : S) :
    basenameAbstract toString os ops path = (splitdir os ops (toString path)).2 := rfl

end LegacyWrappers

theorem joinUnixLoop_invalid_prefix (ops : StringOps) (before : List Path)
    (path : Path) (representation : Except PathError String) (rest : List PathValue) :
    joinUnixLoop ops (before.map PathValue.string ++ .nonString representation :: rest) path =
      invalidPathComponent representation := by
  induction before generalizing path with
  | nil => cases representation <;> rfl
  | cons first before ih =>
    change joinUnixLoop ops (before.map PathValue.string ++ .nonString representation :: rest)
      (joinStep .unix ops path first) = invalidPathComponent representation
    exact ih (joinStep .unix ops path first)

def PathComponentAssertion : Prop :=
  (∀ value, assertstring (.string value) = .ok true) ∧
  (∀ rendered, assertstring (.nonString (.ok rendered)) =
    .error (.argumentError ("path component is not a string: " ++ rendered))) ∧
  (∀ error, assertstring (.nonString (.error error)) = .error error) ∧
  (∀ os ops, joinpath os ops [] =
    .error (.argumentError "collection of path components must be non-empty")) ∧
  (∀ os ops rendered rest, joinpath os ops (.nonString (.ok rendered) :: rest) =
    .error (.argumentError ("path component is not a string: " ++ rendered))) ∧
  (∀ os ops error rest, joinpath os ops (.nonString (.error error) :: rest) =
    .error error) ∧
  (∀ os ops first rendered rest,
    joinpath os ops (.string first :: .nonString (.ok rendered) :: rest) =
      .error (.argumentError ("path component is not a string: " ++ rendered))) ∧
  (∀ os ops first error rest,
    joinpath os ops (.string first :: .nonString (.error error) :: rest) = .error error) ∧
  (∀ (ops : StringOps) (first : Path) (before : List Path)
    (representation : Except PathError String) (rest : List PathValue),
    joinpath .unix ops (.string first :: before.map PathValue.string ++
      .nonString representation :: rest) = invalidPathComponent representation)

theorem pathComponentAssertion_proven : PathComponentAssertion := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro os ops first rendered rest
    cases os <;> rfl
  · intro os ops first error rest
    cases os <;> rfl
  · intro ops first before representation rest
    exact joinUnixLoop_invalid_prefix ops before first representation rest

namespace LegacyPaths

def IsdirpathTrailing : Prop :=
  ∀ (ops : StringOps) (path : Path),
    isdirpath .unix ops ⟨path.bytes ++ [slash]⟩ = true

theorem isdirpathTrailing_proven : IsdirpathTrailing := by
  intro ops path
  have tailEmpty := splitdirNoDriveTailEmptyOfTrailingSeparator .unix ops (emptyPath ops)
    ⟨path.bytes ++ [slash]⟩ (by simp [separator])
  unfold isdirpath
  simp only [splitdrive]
  rw [tailEmpty]
  rfl

end LegacyPaths

def entries : List Entry := [
  { id := "paths-isdirpath-trailing", juliaFile := "base/path.jl"
    juliaFns := ["isdirpath"]
    statement := "isdirpath(p * \"/\") is true for every p."
    source := "base/path.jl:241-260", status := .proven
    prop := ``LegacyPaths.IsdirpathTrailing, thm := some ``LegacyPaths.isdirpathTrailing_proven },
  { id := "files-method-path-abstract-wrappers", juliaFile := "base/path.jl"
    juliaFns := ["generated AbstractString path wrappers"]
    statement := "Each generated AbstractString wrapper converts to String and delegates to its corresponding POSIX path method, including cwd-sensitive abspath."
    source := "base/path.jl:961-963", status := .proven
    prop := ``LegacyWrappers.PathAbstractWrapperMethod, thm := some ``LegacyWrappers.pathAbstractWrapperMethod },
  { id := "files-method-joinpath-varargs", juliaFile := "base/path.jl"
    juliaFns := ["joinpath(::AbstractString...)"]
    statement := "The AbstractString vararg joinpath overload collects its arguments and delegates to the collection method."
    source := "base/path.jl:487; return conversion base/essentials.jl:480", status := .proven
    prop := ``LegacyWrappers.JoinpathVarargsMethod, thm := some ``LegacyWrappers.joinpathVarargsMethod },
  { id := "files-method-normpath-varargs", juliaFile := "base/path.jl"
    juliaFns := ["normpath(::AbstractString, ::AbstractString...)"]
    statement := "The multiargument normpath overload joins every argument first and normalizes the resulting String."
    source := "base/path.jl:595", status := .proven
    prop := ``LegacyWrappers.NormpathVarargsMethod, thm := some ``LegacyWrappers.normpathVarargsMethod },
  { id := "files-method-abspath-varargs", juliaFile := "base/path.jl"
    juliaFns := ["abspath(::AbstractString, ::AbstractString...)"]
    statement := "The multiargument abspath overload joins every argument first and applies the cwd-sensitive String method."
    source := "base/path.jl:633", status := .proven
    prop := ``LegacyWrappers.AbspathVarargsMethod, thm := some ``LegacyWrappers.abspathVarargsMethod },
  { id := "files-method-splitpath-abstract", juliaFile := "base/path.jl"
    juliaFns := ["splitpath(::AbstractString)"]
    statement := "The AbstractString splitpath overload converts to String and delegates to the String method for every path."
    source := "base/path.jl:393", status := .proven
    prop := ``LegacyWrappers.SplitpathAbstractMethod, thm := some ``LegacyWrappers.splitpathAbstractMethod },
  { id := "files-method-expanduser-abstract", juliaFile := "base/path.jl"
    juliaFns := ["expanduser(::AbstractString)"]
    statement := "The AbstractString expanduser overload converts to String and delegates to the platform String method for every path."
    source := "base/path.jl:896", status := .proven
    prop := ``LegacyWrappers.ExpanduserAbstractMethod, thm := some ``LegacyWrappers.expanduserAbstractMethod },
  { id := "files-method-relpath-abstract", juliaFile := "base/path.jl"
    juliaFns := ["relpath(::AbstractString, ::AbstractString)"]
    statement := "The AbstractString relpath overload converts both arguments to String and delegates to the String method."
    source := "base/path.jl:958-959", status := .proven
    prop := ``LegacyWrappers.RelpathAbstractMethod, thm := some ``LegacyWrappers.relpathAbstractMethod },
  { id := "files-method-dirname-abstract", juliaFile := "base/path.jl"
    juliaFns := ["dirname(::AbstractString)"]
    statement := "The AbstractString dirname overload delegates to splitdir and returns its first component for every converted path."
    source := "base/path.jl:308", status := .proven
    prop := ``LegacyWrappers.DirnameAbstractMethod, thm := some ``LegacyWrappers.dirnameAbstractMethod },
  { id := "files-method-basename-abstract", juliaFile := "base/path.jl"
    juliaFns := ["basename(::AbstractString)"]
    statement := "The AbstractString basename overload delegates to splitdir and returns its second component for every converted path."
    source := "base/path.jl:330", status := .proven
    prop := ``LegacyWrappers.BasenameAbstractMethod, thm := some ``LegacyWrappers.basenameAbstractMethod },
  { id := "path-component-assertion", juliaFile := "base/path.jl",
    juliaFns := ["joinpath(::Union{Tuple, AbstractVector})"],
    statement := "joinpath rejects empty collections; the first nonstring component on Unix reports its complete repr in ArgumentError or propagates its repr error. Both platforms validate their first two components before processing later ones.",
    source := "base/path.jl:415-426,465-475", status := .proven,
    prop := ``PathComponentAssertion, thm := some ``pathComponentAssertion_proven },
  { id := "paths-splitext-dotfile-doc", juliaFile := "base/path.jl",
    juliaFns := ["splitext(::AbstractString)"],
    statement := "The source contract splits p at a dot whenever the remaining suffix has no dot or separator; this remains falsifiable for hidden names.",
    source := "base/path.jl:335-337 (splitext docstring)", status := .refuted,
    refutationEvidence := .runtime, prop := ``SplitextDotfileDoc,
    thm := some ``splitextDotfileDoc_refuted, issue := "none found",
    notes := "Julia splitext(\".bashrc\") returns (\".bashrc\", \"\")." },
  { id := "paths-dirname-basename", juliaFile := "base/path.jl",
    juliaFns := ["dirname", "basename", "splitdir"],
    statement := "splitdir returns (dirname(path), basename(path)); basename contains no separator, is empty for a trailing separator, and is a suffix of the input path.",
    source := "base/path.jl:262-330 (splitdir, dirname, basename docstrings)", status := .proven,
    prop := ``DirnameBasename, thm := some ``dirnameBasename_proven },
  { id := "paths-joinpath-splitdir", juliaFile := "base/path.jl",
    juliaFns := ["joinpath", "splitdir"],
    statement := "For a Unix path without repeated separators, joining dirname(path) and basename(path) reproduces the original path.",
    source := "base/path.jl:262-330; joinpath body base/path.jl:465-483", status := .proven,
    prop := ``JoinSplitdir, thm := some ``joinSplitdir_proven },
  { id := "paths-joinpath-splitdir-windows", juliaFile := "base/path.jl",
    juliaFns := ["joinpath", "splitdir"],
    statement := "For a Windows path with no repeated separators whose basename does not parse as a drive prefix, joining dirname(path) and basename(path) reproduces the original path.",
    source := "base/path.jl:262-330,413-461,494-496", status := .todo,
    prop := ``JoinSplitdirWindows, thm := none, notes := "Statement gap: Windows joinpath canonicalizes separators, so a/b reconstructs as a\\b. Exact original spelling is unsupported by this full String domain. Refutation still needs Windows release/nightly evidence; do not exclude constructible noncanonical spellings to prove the current statement." },
  { id := "paths-splitpath-joinpath", juliaFile := "base/path.jl",
    juliaFns := ["splitpath", "joinpath"],
    statement := "joinpath(splitpath(p)...) equals p when p is the platform spelling of joinable components, and splitpath(joinpath(parts...)) equals parts for joinable component lists, for every string within Julia size limits.",
    source := "base/path.jl:373-411,413-514 (splitpath and joinpath docstrings and methods)", status := .todo,
    prop := ``JuliaLean.Proofs.base.path.Round4.SplitpathJoinpathCorrect, thm := none, notes := "The JoinableComponents grammar admits a partial long-UNC header completed by later components; splitting then returns one drive instead of the original components. Refutation needs a concrete completed-header witness and Windows release/nightly evidence; the statement remains unchanged." },
  { id := "paths-splitpath-components", juliaFile := "base/path.jl",
    juliaFns := ["splitpath"],
    statement := "splitpath returns the drive-prefixed first component and then every nonempty name in order; repeated and trailing separators contribute nothing, a leading separator run contributes its first byte as the root, and the empty path gives one empty component.",
    source := "base/path.jl:373-411 (splitpath docstring and method)", status := .proven,
    prop := ``JuliaLean.Proofs.base.path.Round4.SplitpathComponentsCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.PathsSplitpathComponents_proven },
  { id := "paths-splitext-concat", juliaFile := "base/path.jl",
    juliaFns := ["splitext"],
    statement := "splitext returns two strings whose concatenation is the input; a nonempty extension starts at the final dot of the last component.",
    source := "base/path.jl:335-337 (splitext docstring)", status := .proven,
    prop := ``SplitextConcat, thm := some ``splitextConcat_proven },
  { id := "paths-normpath-idempotent", juliaFile := "base/path.jl",
    juliaFns := ["normpath"],
    statement := "Normalizing a path twice returns the same normalized path as normalizing it once.",
    source := "base/path.jl:543 (normpath docstring)", status := .todo,
    prop := ``NormpathIdempotent, thm := none, notes := "Windows model diagnostic: ./C: normalizes to C: and then C:.; drive interpretation changes after removing dot components. Refutation needs Windows release/nightly evidence and a matching native counterexample. These constructible String inputs cannot be dropped to obtain a proof." },
  { id := "paths-normpath-canonical", juliaFile := "base/path.jl",
    juliaFns := ["normpath"],
    statement := "The normalized path portion uses only the platform separator and has no repeated separators; absolute results contain no dot or dot-dot components, while relative results contain no dot component except dot itself and keep dot-dot only as a leading run.",
    source := "base/path.jl:540-587", status := .todo,
    prop := ``NormpathCanonical, thm := none, notes := "Windows model diagnostic: relative ./C:/x normalizes to absolute C:\\x, contradicting the relative-component clause. The input grammar permits hidden drive prefixes; Windows release/nightly evidence is absent." },
  { id := "paths-normpath-lexical", juliaFile := "base/path.jl",
    juliaFns := ["normpath"],
    statement := "Resolving dot and parent components from any base reaches the same lexical location before and after normalization.",
    source := "base/path.jl:540-543", status := .todo,
    prop := ``NormpathLexical, thm := none, notes := "Windows model diagnostic: ./C: loses its empty-drive interpretation after normalization. Refutation needs Windows release/nightly evidence and a native resolveLexically counterexample for the unchanged complete String domain." },
  { id := "paths-normpath-isdirpath", juliaFile := "base/path.jl",
    juliaFns := ["normpath", "isdirpath"],
    statement := "Normalization preserves whether the final component denotes a directory.",
    source := "base/path.jl:241-260,540-543,959-990", status := .todo,
    prop := ``NormpathIsdirpath, thm := none, notes := "Windows model diagnostic: ./C: changes from a filename to a bare drive after normalization. Refutation needs Windows release/nightly evidence and a native isdirpath counterexample; do not remove these constructible strings from the statement." },
  { id := "paths-relpath-roundtrip", juliaFile := "base/path.jl",
    juliaFns := ["relpath", "abspath"],
    statement := "From an absolute working directory, joining the absolute start path with relpath(path,start) reaches the same lexical destination as abspath(path), ignoring trailing separators and Windows drive casing; a different Windows drive may produce an absolute result."
    source := "base/path.jl:914-919 (relpath docstring)", status := .todo,
    prop := ``RelpathDestinationRoundtrip, thm := none
    notes := "Proof missing: relate relpath's common-prefix removal and parent-component construction to SamePathDestination after abspath/joinpath; cover Unix roots, Windows different-drive absolute results, drive case mapping and trailing separators while retaining the supplied pwd world." },
  { id := "paths-joinpath-laws", juliaFile := "base/path.jl",
    juliaFns := ["joinpath"],
    statement := "An absolute component discards preceding path components; on Windows a different case-insensitive drive also discards them."
    source := "base/path.jl:494-501 (joinpath docstring)", status := .proven,
    prop := ``JoinpathDocumentedReset, thm := some ``joinpathDocumentedReset_proven },
  { id := "path-joinpath-absolute-component", juliaFile := "base/path.jl",
    juliaFns := ["joinpath"],
    statement := "On Unix, an absolute path component discards all earlier path components.",
    source := "base/path.jl:494-496 (joinpath docstring); Unix joinpath body base/path.jl:465-483", status := .proven,
    prop := ``JoinpathAbsoluteComponent, thm := some ``joinpathAbsoluteComponent_proven },
  { id := "paths-expanduser-doc", juliaFile := "base/path.jl",
    juliaFns := ["expanduser"],
    statement := "expanduser replaces a leading tilde with the current home, expands valid Unix ~username paths, and preserves unsupported or unknown-user paths.",
    source := "base/path.jl:887-893 (expanduser docstring)", status := .proven,
    prop := ``ExpanduserDoc, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.PathsExpanduserDoc_proven },
  { id := "paths-abspath-laws", juliaFile := "base/path.jl",
    juliaFns := ["abspath"],
    statement := "With an absolute pwd(), abspath(path) is absolute and abspath(abspath(path)) equals abspath(path).",
    source := "base/path.jl:600-601 (abspath docstring)", status := .todo,
    prop := ``AbspathLaws, thm := none, notes := "Windows model diagnostic: 1:x remains nonabsolute despite an absolute working directory because splitdrive accepts nonletter prefixes. Refutation needs Windows release/nightly evidence and a concrete pwd binding; valid-drive restrictions would exclude constructible String inputs." },
  { id := "path-abspath-absolute-input", juliaFile := "base/path.jl",
    juliaFns := ["abspath"],
    statement := "When the input path is already absolute, abspath terminates normally without changing the world and returns an absolute, normalized path that is lexically the normalized input.",
    source := "base/path.jl:597-625 (abspath docstring and method)", status := .todo,
    prop := ``JuliaLean.Proofs.base.path.Round4.AbspathAbsoluteInputCorrect, thm := none, notes := "Windows model diagnostic: a long-UNC String with a doubled separator after UNC changes drive parsing on normalization and gains a trailing separator on a second pass. Refutation needs the exact native String witness and Windows release/nightly evidence; the complete input domain remains unchanged." },
  { id := "path-splitdrive-platform", juliaFile := "base/path.jl",
    juliaFns := ["splitdrive(::String)"],
    statement := "Unix splitdrive always returns an empty drive; on Windows, a nonseparator ASCII code unit followed by ':' is the drive prefix.",
    source := "base/path.jl:27-30,119-159; splitdrive docstring base/path.jl:152-159", status := .proven,
    prop := ``PathDrivePlatformSpec, thm := some ``pathDrivePlatformSpec_proven },
  { id := "path-isabspath-platform", juliaFile := "base/path.jl",
    juliaFns := ["isabspath(::String)"],
    statement := "Paths beginning with a separator are absolute on both systems; Windows also recognizes a valid drive-letter prefix followed by a separator.",
    source := "base/path.jl:200-223; isabspath docstring base/path.jl:225-239", status := .proven,
    prop := ``IsabspathDoc, thm := some ``isabspathDoc_proven },
  { id := "path-isdirpath-doc", juliaFile := "base/path.jl",
    juliaFns := ["isdirpath(::String)"],
    statement := "isdirpath is true exactly when the last path component is empty, dot, or dot-dot.",
    source := "base/path.jl:241-260 (isdirpath docstring and method)", status := .proven,
    prop := ``IsdirpathDoc, thm := some ``isdirpathDoc_proven },
  { id := "path-splitext-hidden-name", juliaFile := "base/path.jl",
    juliaFns := ["splitext(::String)"],
    statement := "A hidden name with one leading dot and no later dot or separator has no extension; splitext returns the whole name and an empty extension.",
    source := "base/path.jl:335-337; implementation base/path.jl:351-368", status := .proven,
    prop := ``SplitextHiddenName, thm := some ``splitextHiddenName_proven },
  { id := "path-joinpath-windows-drive-reset", juliaFile := "base/path.jl",
    juliaFns := ["joinpath(::AbstractVector)", "joinpath(::Tuple)"],
    statement := "On Windows, a later nonempty drive that differs ignoring letter case resets the join accumulator to that component's drive and remainder.",
    source := "base/path.jl:415-461; joinpath docstring base/path.jl:494-496", status := .proven,
    prop := ``JoinpathDriveReset, thm := some ``JuliaLean.Proofs.base.path.joinpathDriveReset_proven },
  { id := "path-home-lookup", juliaFile := "base/path.jl",
    juliaFns := ["homedir()", "homedir(::AbstractString)"],
    statement := "On Unix, username lookup returns its configured result; on Windows, the current user's name resolves to the current home directory.",
    source := "base/path.jl:165-198,683-808", status := .proven,
    prop := ``HomedirUserSpec, thm := some ``homedirUserSpec_proven },
  { id := "path-contractuser-prefix", juliaFile := "base/path.jl",
    juliaFns := ["contractuser"],
    statement := "When the first existing separator-delimited prefix identifies the current home directory, contractuser replaces it with tilde and preserves the remaining path bytes.",
    source := "base/path.jl:809-850; contractuser docstring base/path.jl:898-906", status := .proven,
    prop := ``ContractuserDoc, thm := some ``contractuserDoc_proven },
  { id := "path-realpath-filesystem", juliaFile := "base/path.jl",
    juliaFns := ["realpath"],
    statement := "When the filesystem resolves a path to an existing path for the same object, realpath returns that resolved path unchanged.",
    source := "base/path.jl:654-679 (realpath docstring and method)", status := .proven,
    prop := ``RealpathFilesystem, thm := some ``realpathFilesystem_proven },
  { id := "memsafety-path-platform-buffers", juliaFile := "base/path.jl",
    juliaFns := ["_win_profile_from_registry", "homedir(::AbstractString)"],
    statement := "The Windows SID wrapper and passwd uid reads stay within their allocated buffers on supported pointer widths.",
    source := "base/path.jl:708-754,781-807", status := .proven,
    prop := ``JuliaLean.MemSafety.G3.PathBufferSafe,
    thm := some ``JuliaLean.MemSafety.G3.pathBufferSafe_proven }
]

end JuliaLean.Proofs.base.path
