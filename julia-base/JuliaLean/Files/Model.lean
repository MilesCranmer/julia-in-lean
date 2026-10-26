import JuliaLean.Core

/-!
# Filesystem models

The models expose filesystem calls as finite state supplied by the caller. The
Julia control flow around those calls is mirrored from `base/file.jl`,
`base/stat.jl`, and `base/filesystem.jl` on master `bbfa0ce4150`.
-/

namespace JuliaLean.Files

inductive FileError where
  | io
  | argument
  | errorException
  | eof
  | closed
  deriving Repr, DecidableEq

/-- An operation result retains the state at the point of failure. -/
inductive Result (α : Type) where
  | ok (value : α)
  | error (error : FileError) (value : α)
  deriving Repr, DecidableEq

inductive PathShape where
  | relative
  | absolute
  | trailingSlash
  | symlink
  | empty
  deriving Repr, DecidableEq

/-! ## `mkpath`, `base/file.jl:239-256` -/

inductive Component where
  | missing
  | directory
  | file
  | symlinkDirectory
  | symlinkFile
  deriving Repr, DecidableEq

def Component.isDir : Component → Bool
  | .directory | .symlinkDirectory => true
  | _ => false

def Component.create : Component → Result Component
  | .missing => .ok .directory
  | .directory => .ok .directory
  | .symlinkDirectory => .ok .symlinkDirectory
  | c => .error .io c

structure PathState where
  shape : PathShape
  components : List Component
  deriving Repr, DecidableEq

/-- Forward form of the recursive parent-first calls in `mkpath`. -/
def mkpathComponents : List Component → Result (List Component)
  | [] => .ok []
  | c :: cs =>
      match c.create with
      | .error e c' => .error e (c' :: cs)
      | .ok c' =>
          match mkpathComponents cs with
          | .ok cs' => .ok (c' :: cs')
          | .error e cs' => .error e (c' :: cs')

def mkpath (path : PathState) : Result PathState :=
  match mkpathComponents path.components with
  | .ok components => .ok { path with components }
  | .error e components => .error e { path with components }

/-! ## `rm`, `base/file.jl:283-326` -/

inductive RmEntry where
  | missing
  | file
  | link
  | directory (children : Nat)
  /-- A directory link observed through a trailing slash: `islink` is false,
  `isdir` is true, but the final `rmdir` returns `ENOTDIR`. -/
  | trailingDirLink (targetChildren : Nat)
  deriving Repr, DecidableEq

/-- The same branch order as `rm`: link/non-directory first, recursive children
second, and `rmdir` last. -/
def rm (entry : RmEntry) (force recursive : Bool) : Result RmEntry :=
  match entry with
  | .missing => if force then .ok .missing else .error .io .missing
  | .file => .ok .missing
  | .link => .ok .missing
  | .directory children =>
      if recursive || children == 0 then .ok .missing
      else .error .io entry
  | .trailingDirLink targetChildren =>
      if recursive then .error .io (.trailingDirLink 0)
      else .error .io (.trailingDirLink targetChildren)

/-! ## `cp` and `mv`, `base/file.jl:363-390,447-458,505-558` -/

inductive Destination where
  | absent
  | regular
  | directory
  | danglingLink
  deriving Repr, DecidableEq

def Destination.isPath : Destination → Bool
  | .regular | .directory => true
  | .absent | .danglingLink => false

structure CopyState where
  destination : Destination
  targetWritten : Bool := false
  deriving Repr, DecidableEq

/-- `checkfor_mv_cp_cptree` followed by `sendfile`. With a dangling link,
`ispath(dst)` is false; libuv's forced copy follows the link. -/
def cp (state : CopyState) (force : Bool) : Result CopyState :=
  if state.destination.isPath then
    if force then .ok { destination := .regular }
    else .error .argument state
  else
    match state.destination with
    | .absent => .ok { destination := .regular }
    | .danglingLink =>
        if force then .ok { destination := .danglingLink, targetWritten := true }
        else .error .io state
    | _ => .error .io state

/-- Successful rename replaces every distinct destination. The fallback uses
`cp(...; force=true)` and then removes the source. -/
def mv (state : CopyState) (force : Bool) : Result CopyState :=
  if force then .ok { destination := .regular }
  else match state.destination with
    | .absent => .ok { destination := .regular }
    | _ => .error .argument state

/-! ## Temporary names and cleanup, `base/file.jl:765-998` -/

abbrev PathText := List Char

def tempPrefix : PathText := ['j', 'l', '_']

structure TempParent where
  text : PathText
  shape : PathShape
  isDir : Bool
  deriving Repr, DecidableEq

inductive TempKind where
  | name
  | file
  | directory
  deriving Repr, DecidableEq

structure TempObject where
  path : PathText
  kind : TempKind
  present : Bool
  cleanupRegistered : Bool := false
  deriving Repr, DecidableEq

def tempPath (parent namePrefix random suffix : PathText) : PathText :=
  parent ++ namePrefix ++ random ++ suffix

structure TempCandidate where
  random : PathText
  isPath : Bool
  isLink : Bool
  deriving Repr, DecidableEq

/-- The `for _ in 1:max_tries` loop in `_tempname`, returning the first name
that `ispath` reports absent. -/
def chooseTemp : Nat → List TempCandidate → Option PathText
  | 0, _ => none
  | _, [] => none
  | tries + 1, candidate :: candidates =>
      if candidate.isPath then chooseTemp tries candidates else some candidate.random

/-- `_tempname` checks that the parent is a directory, retries existing
candidates, and errors when `max_tries` is exhausted. -/
def tempname (parent : TempParent) (candidates : List TempCandidate) (maxTries : Nat)
    (suffix : PathText) (cleanup : Bool) : Result TempObject :=
  if parent.isDir then
    match chooseTemp maxTries candidates with
    | some random =>
        .ok { path := tempPath parent.text tempPrefix random suffix, kind := .name,
              present := false, cleanupRegistered := cleanup }
    | none => .error .errorException { path := [], kind := .name, present := false }
  else .error .argument { path := [], kind := .name, present := false }

def tempParentUsable (parent : TempParent) : Bool :=
  parent.isDir || parent.shape == .empty

/-- Unix `mkstemp` atomically creates the name. An empty parent constructs a
relative template in the current directory. -/
def mktemp (parent : TempParent) (random : PathText) (cleanup : Bool) : Result TempObject :=
  if tempParentUsable parent then
    .ok { path := tempPath parent.text tempPrefix random [], kind := .file,
          present := true, cleanupRegistered := cleanup }
  else .error .io { path := [], kind := .file, present := false }

/-- `uv_fs_mkdtemp` creates `prefix * random`; the source handles an empty
parent as a relative path in the current directory. -/
def mktempdir (parent : TempParent) (namePrefix random : PathText) (cleanup : Bool) : Result TempObject :=
  if tempParentUsable parent then
    .ok { path := tempPath parent.text namePrefix random [], kind := .directory,
          present := true, cleanupRegistered := cleanup }
  else .error .io { path := [], kind := .directory, present := false }

/-- The function-taking overloads forget the exit hook and remove the object
in `finally`, `base/file.jl:952-998`. -/
def cleanupTemp (object : TempObject) : TempObject :=
  { object with present := false, cleanupRegistered := false }

/-! ## `readdir`, `base/file.jl:1081-1082,1176-1207` -/

def insertName (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertName x ys

def sortNames : List Nat → List Nat
  | [] => []
  | x :: xs => insertName x (sortNames xs)

def renderName (dir : List Nat) (join : Bool) (name : Nat) : List Nat :=
  if join then dir ++ [name] else [name]

def readdir (dir : List Nat) (scan : List Nat) (join sort : Bool) : List (List Nat) :=
  let names := if sort then sortNames scan else scan
  names.map (renderName dir join)

/-! ## `walkdir`, `base/file.jl:1403-1443` -/

mutual
  inductive DirTree where
    | node (name : Nat) (files : List Nat) (children : DirForest)

  inductive DirForest where
    | nil
    | cons (head : DirTree) (tail : DirForest)
end

namespace DirForest

def names : DirForest → List Nat
  | .nil => []
  | .cons (.node name _ _) tail => name :: names tail

end DirForest

structure WalkRow where
  path : List Nat
  dirs : List Nat
  files : List Nat
  deriving Repr, DecidableEq

mutual
  def walkTop (parent : List Nat) : DirTree → List WalkRow
    | .node name files children =>
        let path := parent ++ [name]
        { path, dirs := children.names, files } :: walkTopForest path children

  def walkTopForest (parent : List Nat) : DirForest → List WalkRow
    | .nil => []
    | .cons head tail => walkTop parent head ++ walkTopForest parent tail
end

mutual
  def walkBottom (parent : List Nat) : DirTree → List WalkRow
    | .node name files children =>
        let path := parent ++ [name]
        walkBottomForest path children ++ [{ path, dirs := children.names, files }]

  def walkBottomForest (parent : List Nat) : DirForest → List WalkRow
    | .nil => []
    | .cons head tail => walkBottom parent head ++ walkBottomForest parent tail
end

def walkdir (parent : List Nat) (tree : DirTree) (topdown : Bool) : List WalkRow :=
  if topdown then walkTop parent tree else walkBottom parent tree

/-! ## `touch`, `base/file.jl:586-594` -/

structure TouchState where
  present : Bool
  bytes : List UInt8
  mtime : Nat
  deriving Repr, DecidableEq

def touch (now : Nat) (state : TouchState) : TouchState :=
  { present := true, bytes := if state.present then state.bytes else [], mtime := now }

/-! ## Recursive `chmod`, `base/file.jl:1635-1646` -/

mutual
  inductive ModeTree where
    | directory (mode : Nat) (children : ModeForest)

  inductive ModeEntry where
    | file (mode : Nat)
    | link (mode : Nat)
    | directory (tree : ModeTree)

  inductive ModeForest where
    | nil
    | cons (head : ModeEntry) (tail : ModeForest)
end

mutual
  def chmodChild (mode : Nat) : ModeEntry → ModeEntry
    | .file _ => .file mode
    | .link old => .link old
    | .directory tree => .directory (chmodTree mode true tree)

  def chmodForest (mode : Nat) : ModeForest → ModeForest
    | .nil => .nil
    | .cons head tail => .cons (chmodChild mode head) (chmodForest mode tail)

  def chmodTree (mode : Nat) (recursive : Bool) : ModeTree → ModeTree
    | .directory _ children =>
        .directory mode (if recursive then chmodForest mode children else children)
end

/-! ## `StatStruct`, `base/stat.jl:59-105,310-338,375-566` -/

structure StatStruct where
  mode : Fin 65536
  size : Int
  ioerrno : Int
  deriving Repr, DecidableEq

def filemode (st : StatStruct) : Fin 65536 := st.mode
def modeType (st : StatStruct) : Nat := st.mode.val / 4096 % 16
def isdir (st : StatStruct) : Bool := modeType st == 4
def islink (st : StatStruct) : Bool := modeType st == 10
def ispath (st : StatStruct) : Bool := st.ioerrno == 0
def uperm (st : StatStruct) : Nat := st.mode.val / 64 % 8
def gperm (st : StatStruct) : Nat := st.mode.val / 8 % 8
def operm (st : StatStruct) : Nat := st.mode.val % 8
def filesize (st : StatStruct) : Int := st.size

/-! ## `Filesystem.File`, `base/filesystem.jl:324-445` -/

structure FileState where
  isOpen : Bool
  data : List UInt8
  position : Nat
  deriving Repr, DecidableEq

def bytesavailable (file : FileState) : Nat := file.data.length - file.position

def writeData (data : List UInt8) (offset : Nat) (bytes : List UInt8) : List UInt8 :=
  let headBytes := data.take offset ++ List.replicate (offset - data.length) 0
  headBytes ++ bytes ++ data.drop (offset + bytes.length)

/-- `offset = none` models the `-1` sentinel passed to `write`; an explicit
offset models `pwrite` and leaves the file position unchanged. -/
def unsafeWrite (file : FileState) (bytes : List UInt8) (offset : Option Nat := none) : Result (Nat × FileState) :=
  if !file.isOpen then .error .closed (0, file)
  else
    let offsetPos := offset.getD file.position
    let data := writeData file.data offsetPos bytes
    let position := if offset.isSome then file.position else offsetPos + bytes.length
    .ok (bytes.length, { file with data, position })

def readByte (file : FileState) : Result (Option UInt8 × FileState) :=
  if !file.isOpen then .error .closed (none, file)
  else match file.data[file.position]? with
    | none => .error .eof (none, file)
    | some byte => .ok (some byte, { file with position := file.position + 1 })

def readBytes (file : FileState) (count : Nat) : Result (List UInt8 × FileState) :=
  if !file.isOpen then .error .closed ([], file)
  else
    let bytes := (file.data.drop file.position).take count
    .ok (bytes, { file with position := file.position + bytes.length })

def seek (file : FileState) (position : Nat) : Result FileState :=
  if file.isOpen then .ok { file with position } else .error .closed file

end JuliaLean.Files
