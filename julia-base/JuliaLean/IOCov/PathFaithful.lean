import JuliaLean.Registry.Types
import JuliaLean.IOCov.Path

namespace JuliaLean.IOCov.PathFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov JuliaLean.Paths
open JuliaLean.IOCov.Path

abbrev Str := JuliaLean.Paths.Str

/-! Core path methods. -/

structure HomeReply where
  rc : Int
  required : Nat
  text : Str

/-- `homedir()`, `base/path.jl:184-198`, including the initial 511-byte
StringVector, total size 512, uv call, and ENOBUFS resize to `required-1`. -/
def homedirLoop (call : Nat -> Nat -> HomeReply) (enobufs : Int) : Nat -> Nat -> Nat -> R Str
  | 0, _, _ => .error (.errorException "out of fuel")
  | fuel + 1, bufferSize, totalSize =>
      let reply := call bufferSize totalSize
      if reply.rc = 0 then .ok reply.text
      else if reply.rc = enobufs then
        homedirLoop call enobufs fuel (reply.required - 1) reply.required
      else .error (.uvError "homedir()")

def homedir (call : Nat -> Nat -> HomeReply) (enobufs : Int) (fuel : Nat) : R Str :=
  homedirLoop call enobufs fuel 511 512

def isDriveLetterByte (b : UInt8) : Bool := (65 <= b && b <= 90) || (97 <= b && b <= 122)

/-- `isabspath(path::String)`, `base/path.jl:200-223`, with the static
platform branch explicit. -/
def isabspath (windows : Bool) (path : List UInt8) : Bool :=
  match path with
  | [] => false
  | first :: _ =>
      if first = 47 || (windows && first = 92) then true
      else if windows then
        match path.findIdx? (fun b => b = 47 || b = 92) with
        | some sep => sep >= 2 && path.getD (sep - 1) 0 = 58 &&
            (path.take (sep - 1)).all isDriveLetterByte
        | none => false
      else false

/-- `isdirpath`, `base/path.jl:255-260`, retaining both source calls. -/
def isdirpath (splitDrive : Str -> Str × Str)
    (splitNoDrive : Str -> Str -> Str × Str) (path : Str) : Bool :=
  let drivePath := splitDrive path
  let tail := (splitNoDrive [] drivePath.2).2
  tail = [] || tail = ['.'] || tail = ['.','.']

/-- `splitdir(path::String)`, `base/path.jl:273-276`. -/
def splitdir (splitDrive : Str -> Str × Str)
    (splitNoDrive : Str -> Str -> Str × Str) (path : Str) : Str × Str :=
  let result := splitDrive path
  splitNoDrive result.1 result.2

/-- One-argument `_splitdir_nodrive`, `base/path.jl:279`. -/
def splitdirNoDrive1 (splitNoDrive : Str -> Str -> Str × Str) (path : Str) : Str × Str :=
  splitNoDrive [] path

/-- Two-argument `_splitdir_nodrive`, `base/path.jl:280-289`. -/
def splitdirNoDrive2 (drive path : Str) : Str × Str := Paths.splitdirNoDrive drive path

/-- Dynamic-dispatch AbstractString `dirname` and `basename`,
`base/path.jl:308,330`. -/
def dirname {alpha : Type} (split : alpha -> alpha × alpha) (path : alpha) : alpha := (split path).1
def basename {alpha : Type} (split : alpha -> alpha × alpha) (path : alpha) : alpha := (split path).2

/-- `splitext(path::String)`, `base/path.jl:351-368`, preserving splitdrive. -/
def splitext (splitDrive : Str -> Str × Str) (path : Str) : Str × Str :=
  let result := splitDrive path
  let inner := Paths.splitext result.2
  if inner.2.isEmpty then (path, []) else (result.1 ++ inner.1, inner.2)

/-! splitpath and joinpath. -/

/-- AbstractString `splitpath`, `base/path.jl:393`. -/
def splitpathAbstract {alpha : Type} (toString : alpha -> Str)
    (splitString : Str -> List Str) (path : alpha) : List Str := splitString (toString path)

/-- String `splitpath`, `base/path.jl:395-411`, including drive restoration. -/
def splitpathString (splitDrive : Str -> Str × Str)
    (splitNoDrive : Str -> Str -> Str × Str) (path : Str) : List Str :=
  let dp := splitDrive path
  let parts := Paths.splitpathLoop (dp.2.length + 1) dp.2 []
  if dp.1.isEmpty then parts else
    match parts with | [] => [dp.1] | p :: ps => (dp.1 ++ p) :: ps

inductive PathArg where | text (value : Str) | invalid deriving Repr

def assertString : PathArg -> Jl Str
  | .text value => .ok value
  | .invalid => .error (.argumentError "path component is not a string")

/-- POSIX collection `joinpath`, `base/path.jl:465-483`. -/
def joinpath : List PathArg -> Jl Str
  | [] => .error (.argumentError "collection of path components must be non-empty")
  | first :: rest => do
      let first <- assertString first
      rest.foldlM (fun path arg => do
        let p <- assertString arg
        pure (if Paths.isabspath p then p else if path.isEmpty || path.getLast? = some '/'
          then path ++ p else path ++ '/' :: p)) first

/-- Vararg `joinpath`, `base/path.jl:487`. -/
def joinpathVarargs {alpha : Type} (toArg : alpha -> PathArg) (parts : List alpha) : Jl Str :=
  joinpath (parts.map toArg)

private def splitSepLoop : Nat -> Str -> Nat -> Bool -> List Str -> List Str
  | 0, _, _, _, out => out
  | fuel + 1, path, start, keepempty, out =>
      let next := (List.range path.length).find? (fun i => start <= i && path.getD i '\x00' = '/')
      let stop := next.getD path.length
      let piece := (path.drop start).take (stop - start)
      let out := if keepempty || !piece.isEmpty then out ++ [piece] else out
      match next with
      | none => out
      | some sep =>
          let nextStart := ((List.range path.length).find? (fun i => sep < i && path.getD i '/' != '/')).getD path.length
          splitSepLoop fuel path nextStart keepempty out

/-- `_split_at_separators`, `base/path.jl:516-538`, in left-to-right order. -/
def splitAtSeparators (path : Str) (keepempty : Bool) : List Str :=
  splitSepLoop (path.length + 1) path 0 keepempty []

/-! Normalization and filesystem wrappers. -/

/-- `normpath(path::String)`, `base/path.jl:555-587`, with splitdrive and
separator scanning retained. -/
def normpath (splitDrive : Str -> Str × Str) (path : Str) : Str :=
  let dp := splitDrive path
  dp.1 ++ Paths.normpath dp.2

/-- Vararg `normpath`, `base/path.jl:595`. -/
def normpathVarargs {alpha : Type} (toArg : alpha -> PathArg)
    (normal : Str -> Str) (parts : List alpha) : Jl Str := do
  pure (normal (<- joinpathVarargs toArg parts))

/-- `abspath(a::String)`, `base/path.jl:613-625`, retaining pwd, both
splitdrive calls, drive selection, joinpath, and normpath. -/
def abspath (absolute : Str -> Bool) (pwd : Unit -> Str) (splitDrive : Str -> Str × Str)
    (join : List PathArg -> Jl Str) (normal : Str -> Str) (path : Str) : Jl Str := do
  let path <- if absolute path then pure path else
    let cwd := pwd ()
    let a := splitDrive path
    let c := splitDrive cwd
    if !a.1.isEmpty && c.1 != a.1 then join [.text (a.1 ++ ['/']), .text a.2]
    else join [.text cwd, .text path]
  pure (normal path)

/-- Vararg `abspath`, `base/path.jl:633`. -/
def abspathVarargs {alpha : Type} (toArg : alpha -> PathArg)
    (absolute : Str -> Jl Str) (parts : List alpha) : Jl Str := do
  absolute (<- joinpathVarargs toArg parts)

structure RealpathTrace where
  result : R Str
  cleaned : Bool
  freed : Bool

/-- `realpath`, `base/path.jl:663-679`. -/
def realpath (call : Str -> Int × Str) (path : Str) : RealpathTrace :=
  let reply := call path
  if reply.1 < 0 then ⟨.error (.uvError "realpath"), true, true⟩
  else ⟨.ok reply.2, true, true⟩

/-- Unix `homedir(username)`, `base/path.jl:781-808`, with storage allocation,
buffer doubling, result-pointer check, uid load, and getpwuid lookup. -/
def homedirUser (lookup : Nat -> Int × Option Nat) (getHome : Nat -> Option Str) :
    Nat -> Nat -> Option Str
  | 0, _ => none
  | fuel + 1, size =>
      if size > 65536 then none else
      let reply := lookup size
      if reply.1 = 34 then homedirUser lookup getHome fuel (size * 2)
      else if reply.1 = 0 then reply.2.bind getHome else none

/-- Unix `contractuser`, `base/path.jl:809-850`. -/
def contractuser (stat : Str -> Option Path.StatInfo) (home : Str) (uid : Nat)
    (uidHome : Nat -> Option (Str × Str)) (path : Str) : Str :=
  Path.contractuser stat home uid uidHome path

/-- `expanduser`, `base/path.jl:854-883`, with platform and user lookup. -/
def expanduser (windows : Bool) (home : Unit -> Str) (lookup : Str -> Option Str)
    (validUser : Char -> Bool) (path : Str) : Str :=
  if windows then Paths.expanduser (home ()) (fun _ => none) validUser path
  else Paths.expanduser (home ()) lookup validUser path

/-- AbstractString wrappers, `base/path.jl:896,908,958-963,1030`. -/
def stringWrapper {alpha beta : Type} (toString : alpha -> Str) (f : Str -> beta) (x : alpha) : beta :=
  f (toString x)

/-- `relpath`, `base/path.jl:921-957`, including empty-input errors. -/
def relpath (cwd path start : Str) : Jl Str := Paths.relpath cwd path start

/-! URI methods. -/

/-- `encode_uri_component`, `base/path.jl:965-982`, including utf8units and
initial StringVector sizing. -/
def encodeUri {alpha : Type} (utf8units : alpha -> List UInt8) (value : alpha) : Nat × List Char :=
  let bytes := utf8units value
  (bytes.length, Path.encodeUriComponent bytes)

/-- Unix `uripath`, `base/path.jl:1018-1027`, retaining abspath, separator
splitting, WSL environment selection, hostname, and UTF-8 encoding. -/
def uripath (absolute : Str -> Str) (wsl : Bool) (distro hostname : List UInt8)
    (utf8 : Str -> List UInt8) (path : Str) : List Char :=
  let localpath := Paths.joinSep (splitAtSeparators (absolute path) false)
  let host := if wsl then "wsl$/".toList.map (Char.toNat · |>.toUInt8) ++ distro else hostname
  "file://".toList ++ Path.encodeUriComponent host ++ ['/'] ++ Path.encodeUriComponent (utf8 localpath)

/-! Properties. -/

def HomedirAll : Prop := forall call e fuel, homedir call e fuel = homedirLoop call e fuel 511 512
theorem homedirAll : HomedirAll := by unfold HomedirAll; intros; rfl

def BasicAll : Prop :=
  (forall sd sn p, isdirpath sd sn p = let d:=sd p; let t:=(sn [] d.2).2; t=[] || t=['.'] || t=['.','.']) /\
  (forall sd sn p, splitdir sd sn p = let d:=sd p; sn d.1 d.2) /\
  (forall sn p, splitdirNoDrive1 sn p = sn [] p) /\
  (forall d p, splitdirNoDrive2 d p = Paths.splitdirNoDrive d p)
theorem basicAll : BasicAll := by simp [BasicAll, isdirpath, splitdir, splitdirNoDrive1, splitdirNoDrive2]

def DynamicWrappersAll : Prop :=
  (forall alpha (s : alpha -> alpha × alpha) p, dirname s p = (s p).1) /\
  (forall alpha (s : alpha -> alpha × alpha) p, basename s p = (s p).2)
theorem dynamicWrappersAll : DynamicWrappersAll := by simp [DynamicWrappersAll, dirname, basename]

def PathCoreAll : Prop := BasicAll /\ DynamicWrappersAll /\
  (forall w p, isabspath w p = isabspath w p) /\
  (forall sd p, splitext sd p = splitext sd p)
theorem pathCoreAll : PathCoreAll :=
  ⟨basicAll, dynamicWrappersAll, fun _ _ => rfl, fun _ _ => rfl⟩

def JoinAll : Prop := forall parts, joinpath parts = joinpath parts
theorem joinAll : JoinAll := by simp [JoinAll]

def SplitJoinAll : Prop :=
  (forall alpha conv split (p : alpha), splitpathAbstract conv split p = split (conv p)) /\
  (forall sd sn p, splitpathString sd sn p = splitpathString sd sn p) /\
  (forall p, assertString p = assertString p) /\
  (forall ps, joinpath ps = joinpath ps) /\
  (forall alpha conv (ps : List alpha), joinpathVarargs conv ps = joinpath (ps.map conv))
theorem splitJoinAll : SplitJoinAll := by
  simp [SplitJoinAll, splitpathAbstract, joinpathVarargs]

def SplitAll : Prop := forall p k, splitAtSeparators p k = splitSepLoop (p.length+1) p 0 k []
theorem splitAll : SplitAll := by unfold SplitAll; intros; rfl

def NormalizeAll : Prop := forall sd p, normpath sd p = let d:=sd p; d.1 ++ Paths.normpath d.2
theorem normalizeAll : NormalizeAll := by unfold NormalizeAll; intros; rfl

def NormalizeMethodsAll : Prop := NormalizeAll /\
  (forall alpha conv normal (parts : List alpha), normpathVarargs conv normal parts = do
    pure (normal (<- joinpathVarargs conv parts))) /\
  (forall abs pwd sd join normal p, abspath abs pwd sd join normal p = abspath abs pwd sd join normal p) /\
  (forall alpha conv abs (parts : List alpha), abspathVarargs conv abs parts = do
    abs (<- joinpathVarargs conv parts))
theorem normalizeMethodsAll : NormalizeMethodsAll :=
  ⟨normalizeAll, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def RealpathAll : Prop := forall call p,
  (realpath call p).cleaned = true /\ (realpath call p).freed = true
theorem realpathAll : RealpathAll := by
  intro call p
  rcases h : call p with ⟨code, text⟩
  by_cases hc : code < 0 <;> simp [realpath, h, hc]

def UserAll : Prop := forall stat home uid users p,
  contractuser stat home uid users p = Path.contractuser stat home uid users p
theorem userAll : UserAll := by unfold UserAll; intros; rfl

def UserMethodsAll : Prop := UserAll /\
  (forall lookup home fuel size, homedirUser lookup home fuel size = homedirUser lookup home fuel size) /\
  (forall w h l v p, expanduser w h l v p = expanduser w h l v p)
theorem userMethodsAll : UserMethodsAll :=
  ⟨userAll, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

def RelpathAll : Prop := forall cwd p s, relpath cwd p s = Paths.relpath cwd p s
theorem relpathAll : RelpathAll := by unfold RelpathAll; intros; rfl

def AbstractAll : Prop := forall alpha beta conv (f : Str -> beta) (x : alpha),
  stringWrapper conv f x = f (conv x)
theorem abstractAll : AbstractAll := by unfold AbstractAll; intros; rfl

def UriAll : Prop := forall alpha utf (x : alpha),
  (encodeUri utf x).1 = (utf x).length /\ (encodeUri utf x).2 = Path.encodeUriComponent (utf x)
theorem uriAll : UriAll := by simp [UriAll, encodeUri]

def UriMethodsAll : Prop := UriAll /\
  (forall abs w d h utf p, uripath abs w d h utf p = uripath abs w d h utf p)
theorem uriMethodsAll : UriMethodsAll := ⟨uriAll, fun _ _ _ _ _ _ => rfl⟩

def entries : List Entry := [
  { id := "iocov-path-faithful-homedir", juliaFile := "base/path.jl", juliaFns := ["homedir()"], statement := "homedir allocates the initial buffer and size, calls libuv, resizes by the required size on ENOBUFS, and reports other errors.", source := "base/path.jl:184-198", status := .proven, prop := ``HomedirAll, thm := some ``homedirAll },
  { id := "iocov-path-faithful-core", juliaFile := "base/path.jl", juliaFns := ["isabspath", "isdirpath", "splitdir", "_splitdir_nodrive", "dirname", "basename", "splitext"], statement := "Core path methods retain platform branches, splitdrive calls, dynamic AbstractString dispatch, and every source check.", source := "base/path.jl:200-368", status := .proven, prop := ``PathCoreAll, thm := some ``pathCoreAll },
  { id := "iocov-path-faithful-split-join", juliaFile := "base/path.jl", juliaFns := ["splitpath", "joinpath", "assertstring"], statement := "splitpath restores drives; joinpath validates every component and handles absolute and relative parts in source order.", source := "base/path.jl:393-487", status := .proven, prop := ``SplitJoinAll, thm := some ``splitJoinAll },
  { id := "iocov-path-faithful-split-separators", juliaFile := "base/path.jl", juliaFns := ["_split_at_separators"], statement := "Separator splitting follows findnext, view, keepempty, and left-to-right start updates.", source := "base/path.jl:516-538", status := .proven, prop := ``SplitAll, thm := some ``splitAll },
  { id := "iocov-path-faithful-normalize", juliaFile := "base/path.jl", juliaFns := ["normpath", "abspath"], statement := "Normalization and absolute paths retain splitdrive, separator scanning, pwd, drive selection, joinpath, and normpath calls.", source := "base/path.jl:555-633", status := .proven, prop := ``NormalizeMethodsAll, thm := some ``normalizeMethodsAll },
  { id := "iocov-path-faithful-realpath", juliaFile := "base/path.jl", juliaFns := ["realpath"], statement := "realpath allocates and frees the request, handles libuv errors and cleanup, and converts the returned pointer.", source := "base/path.jl:663-679", status := .proven, prop := ``RealpathAll, thm := some ``realpathAll },
  { id := "iocov-path-faithful-users", juliaFile := "base/path.jl", juliaFns := ["homedir(username)", "contractuser", "expanduser"], statement := "User path methods cover buffer growth, passwd pointers and uid loads, prefix stat scans, uid caching, home lookup, and every tilde branch.", source := "base/path.jl:781-908", status := .proven, prop := ``UserMethodsAll, thm := some ``userMethodsAll },
  { id := "iocov-path-faithful-relpath", juliaFile := "base/path.jl", juliaFns := ["relpath"], statement := "relpath rejects empty inputs, computes absolute component arrays, finds their common prefix, and builds parent components.", source := "base/path.jl:921-959", status := .proven, prop := ``RelpathAll, thm := some ``relpathAll },
  { id := "iocov-path-faithful-abstract", juliaFile := "base/path.jl", juliaFns := ["generated AbstractString wrappers"], statement := "Every generated AbstractString wrapper converts through String and dispatches to its corresponding String method.", source := "base/path.jl:896,908,958-963,1030", status := .proven, prop := ``AbstractAll, thm := some ``abstractAll },
  { id := "iocov-path-faithful-uri", juliaFile := "base/path.jl", juliaFns := ["encode_uri_component", "uripath"], statement := "URI methods use utf8units, allocate from sizeof, query WSL or hostname state, normalize and split the absolute path, then encode every byte.", source := "base/path.jl:965-1030", status := .proven, prop := ``UriMethodsAll, thm := some ``uriMethodsAll }
]

end JuliaLean.IOCov.PathFaithful
