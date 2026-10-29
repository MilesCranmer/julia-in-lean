import JuliaLean.base.path
import JuliaLean.Registry.Types

/-!
# Specifications for `base/path.jl`

The entries remain `.todo` until a later pass supplies proofs or confirmed Julia reproducers.
Filesystem and string operations are the typed interfaces of `JuliaLean.base.path`.
-/

namespace JuliaLean.Proofs.base.path

open JuliaLean.base.path JuliaLean.Registry

abbrev Bytes := List UInt8

/-- A component contains no path separators for the selected platform. -/
def NoSeparators (os : Platform) (bs : Bytes) : Prop :=
  ∀ b, b ∈ bs → isseparatorByte os b = false

def NoDots (bs : Bytes) : Prop := ∀ b, b ∈ bs → b ≠ dot

def NoDoubleSeparator (os : Platform) : Bytes → Prop
  | a :: b :: rest => (isseparatorByte os a && isseparatorByte os b = false) ∧ NoDoubleSeparator os (b :: rest)
  | _ => True

def CanonicalPath (os : Platform) (path : Path) : Prop :=
  NoDoubleSeparator os path.bytes ∧
    (path.bytes = [] ∨ path.bytes = [separator os] ∨ path.bytes.getLast? ≠ some (separator os))

def Components (os : Platform) (parts : List Path) : Prop :=
  parts ≠ [] ∧
    (∀ part ∈ parts, part.bytes ≠ [] ∧ NoSeparators os part.bytes)

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
Nothing to promise: `assertstring` only checks dynamically typed collection members before `joinpath` uses them; the public join contract is stated by `JoinpathLaws` and `JoinpathDriveReset`.
Nothing to promise: `longpath` is an internal Windows canonical-case helper with no public docstring.
Nothing to promise: `uripath` declares the generic function before its platform-specific methods and has no body.
-/

def SplitextDotfileDoc : Prop :=
  ∀ (ops : StringOps) (q r : Bytes), NoSeparators .unix r → NoDots r →
    splitext .unix ops (ops.fromBytes (q ++ dot :: r)) =
      (ops.fromBytes q, ops.fromBytes (dot :: r))

def DirnameBasename : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    NoSeparators os (basename os ops path).bytes ∧
    (path.bytes.getLast? = some (separator os) → (basename os ops path).bytes = []) ∧
    ∃ prePath, path.bytes = prePath ++ (basename os ops path).bytes

def JoinSplitdir : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    NoDoubleSeparator os path.bytes →
    joinpathStrings os ops [dirname os ops path, basename os ops path] = .ok path

def SplitpathJoinpath : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    CanonicalPath os path → joinpathStrings os ops (splitpath os ops path) = .ok path

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
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    normpath os ops (normpath os ops path) = normpath os ops path

def NormpathCanonical : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    let result := normpath os ops path
    let parts := (splitAtSeparators os ops result false).map (·.bytes)
    NoDoubleSeparator os result.bytes ∧
      (isabspath os path = true →
        isabspath os result = true ∧ ∀ part ∈ parts, part ≠ [dot] ∧ part ≠ dotdot) ∧
      (isabspath os path = false →
        isabspath os result = false ∧
        (result.bytes = [dot] ∨ ∀ part ∈ parts, part ≠ [dot]) ∧ dotDotPrefix parts)

def NormpathLexical : Prop :=
  ∀ (os : Platform) (ops : StringOps) (base : List Bytes) (path : Path),
    resolveLexically os ops base (normpath os ops path) = resolveLexically os ops base path

def NormpathIsdirpath : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    isdirpath os ops (normpath os ops path) = isdirpath os ops path

def RelpathRoundtrip : Prop :=
  ∀ (os : Platform) (ops : StringOps) (pwd : Unit → Path) (path startpath relative : Path),
    isabspath os (pwd ()) = true →
    relpath os ops pwd path startpath = .ok relative →
      isabspath os relative = false ∧
      (∃ absolutePath absoluteStart joined,
        abspath os ops pwd path = .ok absolutePath ∧
        abspath os ops pwd startpath = .ok absoluteStart ∧
        joinpathStrings os ops [absoluteStart, relative] = .ok joined ∧
        normpath os ops joined = absolutePath)

def JoinpathLaws : Prop :=
  (∀ (os : Platform) (ops : StringOps) (before absolute : Path),
    isabspath os absolute = true →
      joinpathStrings os ops [before, absolute] = .ok absolute) ∧
  (∀ (ops : StringOps) (a b c : Path),
    joinpathStrings .unix ops [a, b, c] =
      (joinpathStrings .unix ops [a, b]).bind (fun first => joinpathStrings .unix ops [first, c]))

def ExpanduserDoc : Prop :=
  ∀ (os : Platform) (ops : StringOps) (fs : FileSystemOps) (path : Path),
    (path.bytes.head? ≠ some tilde → expanduser os ops fs path = .ok path) ∧
    ((path.bytes = [tilde] ||
        (path.bytes.head? = some tilde && path.bytes[1]?.map (isseparatorByte os) = some true)) →
      ∃ home, fs.homedir () = .ok home ∧
        let suffix := path.bytes.drop 1
        let homeBytes := if os == .windows && !suffix.isEmpty then
          replaceSeparators os home.bytes suffix.head! else home.bytes
        expanduser os ops fs path = .ok (ops.fromBytes (homeBytes ++ suffix))) ∧
    (∀ user rest, os = .unix → user ≠ [] → NoSeparators .unix user →
      ops.validUsername (ops.fromBytes user) = true →
      (rest = [] ∨ rest.head?.map (isseparatorByte .unix) = some true) →
      fs.homedirUser (ops.fromBytes user) = some (ops.fromBytes (user ++ [slash])) →
      expanduser os ops fs (ops.fromBytes ((tilde :: user) ++ rest)) =
        .ok (ops.fromBytes (user ++ [slash] ++ rest))) ∧
    (∀ user rest, os = .windows →
      expanduser os ops fs (ops.fromBytes ((tilde :: user) ++ rest)) =
        .ok (ops.fromBytes ((tilde :: user) ++ rest)))

def AbspathLaws : Prop :=
  ∀ (os : Platform) (ops : StringOps) (pwd : Unit → Path) (path absolute : Path),
    isabspath os (pwd ()) = true →
    abspath os ops pwd path = .ok absolute →
      isabspath os absolute = true ∧ abspath os ops pwd absolute = .ok absolute

def PathDrivePlatformSpec : Prop :=
  (∀ (ops : StringOps) (path : Path),
    (splitdrive .unix ops path).1.bytes = [] ∧
      (splitdrive .unix ops path).2.bytes = path.bytes) ∧
  (∀ (ops : StringOps) (letter : UInt8) (suffix : Bytes), isdriveletter letter = true →
    splitdrive .windows ops (ops.fromBytes ([letter, colon] ++ suffix)) =
      (ops.fromBytes [letter, colon], ops.fromBytes suffix)) ∧
  (∀ (ops : StringOps) (server share suffix : Bytes),
    server ≠ [] → share ≠ [] → NoSeparators .windows server → NoSeparators .windows share →
    (suffix = [] ∨ suffix.head?.map (isseparatorByte .windows) = some true) →
    let path := ops.fromBytes ([backslash, backslash] ++ server ++ [backslash] ++ share ++ suffix)
    splitdrive .windows ops path =
      (ops.fromBytes ([backslash, backslash] ++ server ++ [backslash] ++ share), ops.fromBytes suffix))

def WindowsAbsoluteDriveShape (bytes : Bytes) : Bool :=
  match findAtOrAfter (isseparatorByte .windows) bytes 0 with
  | none => false
  | some firstSeparator =>
      if firstSeparator < 2 then false
      else bytes[firstSeparator - 1]? == some colon &&
        (bytes.take (firstSeparator - 1)).all isdriveletter &&
        (bytes[firstSeparator]?.map (isseparatorByte .windows) == some true)

def IsabspathDoc : Prop :=
  ∀ (os : Platform) (path : Path),
    isabspath os path =
      (if path.bytes.head?.map (isseparatorByte os) = some true then true
       else os == .windows && WindowsAbsoluteDriveShape path.bytes)

def IsdirpathDoc : Prop :=
  ∀ (os : Platform) (ops : StringOps) (path : Path),
    isdirpath os ops path =
      decide (let last := lastPathComponent os ops path
        last = [] || last = [dot] || last = dotdot)

def JoinpathDriveReset : Prop :=
  ∀ (ops : StringOps) (before suffix : Path),
    let beforeDrive := (splitdrive .windows ops before).1
    let suffixDrive := (splitdrive .windows ops suffix).1
    suffixDrive.bytes ≠ [] →
    (ops.lowercase beforeDrive).bytes ≠ (ops.lowercase suffixDrive).bytes →
      joinpathStrings .windows ops [before, suffix] = .ok suffix

def HomedirUserSpec : Prop :=
  ∀ (os : Platform) (ops : StringOps) (fs : FileSystemOps) (username home : Path),
    (os = .unix → fs.homedirUser username = none →
      homedirUsername os ops fs username = .ok none) ∧
    (os = .unix → fs.homedirUser username = some home →
      homedirUsername os ops fs username = .ok (some home)) ∧
    (os = .windows → fs.currentUser () = some username → fs.homedir () = .ok home →
      homedirUsername os ops fs username = .ok (some home))

def ContractuserDoc : Prop :=
  ∀ (os : Platform) (ops : StringOps) (fs : FileSystemOps) (path home rootPart suffix : Path),
    fs.homedir () = .ok home → fs.ispath home = true →
    (rootPart.bytes, suffix.bytes) ∈ contractuserPairs os path.bytes →
    fs.ispath rootPart = true → fs.samefile rootPart home = true →
      contractuser os ops fs path = .ok (ops.fromBytes (tilde :: suffix.bytes))

def RealpathFilesystem : Prop :=
  ∀ (fs : FileSystemOps) (path resolved : Path),
    fs.realpath path = .ok resolved →
      fs.ispath resolved = true ∧ fs.samefile path resolved = true

def UriComponentRFC : Prop :=
  ∀ byte, encodeUriBytes [byte] =
    if (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) ||
        (48 ≤ byte && byte ≤ 57) || byte == 45 || byte == 95 || byte == 46 ||
        byte == 126 || byte == 47 then [byte]
    else [37, hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

def UriPathDoc : Prop :=
  ∀ (os : Platform) (ops : StringOps) (fs : FileSystemOps) (pwd : Unit → Path)
      (uriOps : UriOps) (path result : Path),
    uripath os ops fs pwd uriOps path = .ok result →
      result.bytes.take 7 = [102, 105, 108, 101, 58, 47, 47] ∧
      (encodeUriBytes result.bytes).length ≥ result.bytes.length

/-! Property registry -/

def entries : List Entry := [
  { id := "paths-splitext-dotfile-doc", juliaFile := "base/path.jl",
    juliaFns := ["splitext(::AbstractString)"],
    statement := "The source contract splits p at a dot whenever the remaining suffix has no dot or separator; this remains falsifiable for hidden names.",
    source := "base/path.jl:335-337 (splitext docstring)", status := .todo,
    prop := ``SplitextDotfileDoc, thm := none },
  { id := "paths-dirname-basename", juliaFile := "base/path.jl",
    juliaFns := ["dirname", "basename", "splitdir"],
    statement := "basename contains no separator, is empty for a trailing separator, and is a suffix of the input path.",
    source := "base/path.jl:262-330 (splitdir, dirname, basename docstrings)", status := .todo,
    prop := ``DirnameBasename, thm := none },
  { id := "paths-joinpath-splitdir", juliaFile := "base/path.jl",
    juliaFns := ["joinpath", "splitdir"],
    statement := "For a path without repeated separators, joining dirname(path) and basename(path) reproduces the original path.",
    source := "base/path.jl:262-330; joinpath docstring base/path.jl:494-496", status := .todo,
    prop := ``JoinSplitdir, thm := none },
  { id := "paths-splitpath-joinpath", juliaFile := "base/path.jl",
    juliaFns := ["splitpath", "joinpath"],
    statement := "Splitting a canonical path into components and joining those components reconstructs the path.",
    source := "base/path.jl:376-377 (splitpath docstring)", status := .todo,
    prop := ``SplitpathJoinpath, thm := none },
  { id := "paths-splitext-concat", juliaFile := "base/path.jl",
    juliaFns := ["splitext"],
    statement := "splitext returns two strings whose concatenation is the input; a nonempty extension starts at the final dot of the last component.",
    source := "base/path.jl:335-337 (splitext docstring)", status := .todo,
    prop := ``SplitextConcat, thm := none },
  { id := "paths-normpath-idempotent", juliaFile := "base/path.jl",
    juliaFns := ["normpath"],
    statement := "Normalizing a path twice returns the same normalized path as normalizing it once.",
    source := "base/path.jl:543 (normpath docstring)", status := .todo,
    prop := ``NormpathIdempotent, thm := none },
  { id := "paths-normpath-canonical", juliaFile := "base/path.jl",
    juliaFns := ["normpath"],
    statement := "normpath removes dot components, resolves parent components, uses the platform separator, and never moves an absolute path above its root.",
    source := "base/path.jl:543 (normpath docstring)", status := .todo,
    prop := ``NormpathCanonical, thm := none },
  { id := "paths-normpath-lexical", juliaFile := "base/path.jl",
    juliaFns := ["normpath"],
    statement := "Normalization preserves the path reached by resolving dot and parent components from every starting directory.",
    source := "base/path.jl:543 (normpath docstring)", status := .todo,
    prop := ``NormpathLexical, thm := none },
  { id := "paths-normpath-isdirpath", juliaFile := "base/path.jl",
    juliaFns := ["normpath", "isdirpath"],
    statement := "Normalization preserves whether a path syntactically denotes a directory.",
    source := "base/path.jl:543; invariant: normpath preserves isdirpath", status := .todo,
    prop := ``NormpathIsdirpath, thm := none },
  { id := "paths-relpath-roundtrip", juliaFile := "base/path.jl",
    juliaFns := ["relpath", "abspath"],
    statement := "From an absolute working directory, joining the absolute start path with relpath(path,start) and normalizing reaches abspath(path).",
    source := "base/path.jl:914-916 (relpath docstring)", status := .todo,
    prop := ``RelpathRoundtrip, thm := none },
  { id := "paths-joinpath-laws", juliaFile := "base/path.jl",
    juliaFns := ["joinpath"],
    statement := "An absolute component discards earlier components, and Unix path joining is associative.",
    source := "base/path.jl:494-496 (joinpath docstring); Unix joinpath body base/path.jl:465-483", status := .todo,
    prop := ``JoinpathLaws, thm := none },
  { id := "paths-expanduser-doc", juliaFile := "base/path.jl",
    juliaFns := ["expanduser"],
    statement := "expanduser replaces a leading tilde with the current home, expands valid Unix ~username paths, and preserves unsupported or unknown-user paths.",
    source := "base/path.jl:887-893 (expanduser docstring)", status := .todo,
    prop := ``ExpanduserDoc, thm := none },
  { id := "paths-abspath-laws", juliaFile := "base/path.jl",
    juliaFns := ["abspath"],
    statement := "With an absolute working directory, abspath returns an absolute normalized path and is idempotent.",
    source := "base/path.jl:600-601 (abspath docstring)", status := .todo,
    prop := ``AbspathLaws, thm := none },
  { id := "path-splitdrive-platform", juliaFile := "base/path.jl",
    juliaFns := ["splitdrive(::String)"],
    statement := "Unix splitdrive always returns an empty drive; Windows splitdrive separates drive-letter prefixes from the remaining path.",
    source := "base/path.jl:27-30,119-159; splitdrive docstring base/path.jl:152-159", status := .todo,
    prop := ``PathDrivePlatformSpec, thm := none },
  { id := "path-isabspath-platform", juliaFile := "base/path.jl",
    juliaFns := ["isabspath(::String)"],
    statement := "Paths beginning with a separator are absolute on both systems; Windows also recognizes a valid drive-letter prefix followed by a separator.",
    source := "base/path.jl:200-223; isabspath docstring base/path.jl:225-239", status := .todo,
    prop := ``IsabspathDoc, thm := none },
  { id := "path-isdirpath-doc", juliaFile := "base/path.jl",
    juliaFns := ["isdirpath(::String)"],
    statement := "isdirpath is true exactly when the last path component is empty, dot, or dot-dot.",
    source := "base/path.jl:241-260 (isdirpath docstring and method)", status := .todo,
    prop := ``IsdirpathDoc, thm := none },
  { id := "path-splitext-hidden-name", juliaFile := "base/path.jl",
    juliaFns := ["splitext(::String)"],
    statement := "A hidden name with one leading dot and no later dot or separator has no extension; splitext returns the whole name and an empty extension.",
    source := "base/path.jl:335-337; implementation base/path.jl:351-368", status := .todo,
    prop := ``SplitextHiddenName, thm := none },
  { id := "path-joinpath-windows-drive-reset", juliaFile := "base/path.jl",
    juliaFns := ["joinpath(::AbstractVector)", "joinpath(::Tuple)"],
    statement := "On Windows, a later path on a different drive discards the earlier joined path.",
    source := "base/path.jl:415-461; joinpath docstring base/path.jl:494-496", status := .todo,
    prop := ``JoinpathDriveReset, thm := none },
  { id := "path-home-lookup", juliaFile := "base/path.jl",
    juliaFns := ["homedir()", "homedir(::AbstractString)"],
    statement := "homedir returns the current home, and username lookup returns the matching home or nothing for an unknown user.",
    source := "base/path.jl:165-198,683-808", status := .todo,
    prop := ``HomedirUserSpec, thm := none },
  { id := "path-contractuser-prefix", juliaFile := "base/path.jl",
    juliaFns := ["contractuser", "expanduser"],
    statement := "A path identifying the current home contracts to tilde, preserving the suffix after that home prefix.",
    source := "base/path.jl:756-850; contractuser docstring base/path.jl:898-906", status := .todo,
    prop := ``ContractuserDoc, thm := none },
  { id := "path-realpath-filesystem", juliaFile := "base/path.jl",
    juliaFns := ["realpath"],
    statement := "For an existing path, realpath returns an existing path that identifies the same filesystem object after resolving symbolic links and dot components.",
    source := "base/path.jl:654-679 (realpath docstring and method)", status := .todo,
    prop := ``RealpathFilesystem, thm := none },
  { id := "path-uri-component", juliaFile := "base/path.jl",
    juliaFns := ["encode_uri_component"],
    statement := "URI component encoding preserves unreserved ASCII bytes and slash, and percent-encodes every other UTF-8 byte with uppercase hexadecimal digits.",
    source := "base/path.jl:965-982; RFC3986 Sections 2.1 and 2.3", status := .todo,
    prop := ``UriComponentRFC, thm := none },
  { id := "path-uri-format", juliaFile := "base/path.jl",
    juliaFns := ["uripath(::String)"],
    statement := "uripath returns a file URI with an encoded host and normalized absolute path, using Windows drive or UNC syntax on Windows.",
    source := "base/path.jl:984-1030 (uripath docstring and methods)", status := .todo,
    prop := ``UriPathDoc, thm := none }
]

end JuliaLean.Proofs.base.path
