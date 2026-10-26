import JuliaLean.Files.Model

namespace JuliaLean.Files

def Creatable : Component → Prop
  | .missing | .directory | .symlinkDirectory => True
  | .file | .symlinkFile => False

def DirectoryLike (component : Component) : Prop := component.isDir = true

/-- `mkpath` succeeds exactly when every component is creatable, preserves the
path spelling, and leaves every component directory-like. -/
def MkpathPostcondition : Prop :=
  ∀ path,
    ((∀ component ∈ path.components, Creatable component) →
      ∃ out, mkpath path = .ok out ∧ out.shape = path.shape ∧
        ∀ component ∈ out.components, DirectoryLike component) ∧
    (¬(∀ component ∈ path.components, Creatable component) →
      ∃ e out, mkpath path = .error e out)

/-- `force` only suppresses a missing-path error; `recursive` is exactly what
permits removal of a nonempty directory. Files and links are unlinked. -/
def RmFlagsSpec : Prop :=
  ∀ force recursive,
    rm .missing force recursive = (if force then .ok .missing else .error .io .missing) ∧
    rm .file force recursive = .ok .missing ∧
    rm .link force recursive = .ok .missing ∧
    ∀ children,
      rm (.directory children) force recursive =
        (if recursive || children == 0 then .ok .missing else .error .io (.directory children))

def targetChildrenAfter : Result RmEntry → Nat
  | .ok (.trailingDirLink n) | .error _ (.trailingDirLink n) => n
  | _ => 0

/-- Recursive removal of a path that names a symbolic link never removes
entries from the link target, including when the spelling has a trailing slash. -/
def RmSymlinkSafe : Prop :=
  ∀ targetChildren,
    targetChildrenAfter (rm (.trailingDirLink targetChildren) true true) = targetChildren

/-- A forced copy first removes every existing destination, then creates a
regular copy at that path without writing through a symbolic link. -/
def CpForceReplaces : Prop :=
  ∀ destination,
    cp { destination, targetWritten := false } true =
      .ok { destination := .regular, targetWritten := false }

/-- A forced move replaces every distinct destination. Without force, it
succeeds exactly when the destination is absent. -/
def MvForceSpec : Prop :=
  (∀ destination,
    mv { destination, targetWritten := false } true =
      .ok { destination := .regular, targetWritten := false }) ∧
  (mv { destination := .absent } false = .ok { destination := .regular }) ∧
  (∀ destination, destination ≠ .absent →
    mv { destination, targetWritten := false } false =
      .error .argument { destination, targetWritten := false })

/-- `tempname` either rejects a non-directory parent or returns an uncreated
name with the fixed prefix, requested suffix, and requested cleanup hook. -/
def TempnameContract : Prop :=
  ∀ parent candidates maxTries suffix cleanup,
    tempname parent candidates maxTries suffix cleanup =
      if parent.isDir then
        match chooseTemp maxTries candidates with
        | some random =>
            .ok { path := tempPath parent.text tempPrefix random suffix, kind := .name,
                  present := false, cleanupRegistered := cleanup }
        | none => .error .errorException { path := [], kind := .name, present := false }
      else .error .argument { path := [], kind := .name, present := false }

/-- The documented unused-name guarantee treats every existing directory
entry, including a dangling symbolic link, as a collision. -/
def TempnameUnused : Prop :=
  ∀ parent candidate suffix cleanup,
    parent.isDir = true → candidate.isLink = true →
    tempname parent [candidate] 1 suffix cleanup =
      .error .errorException { path := [], kind := .name, present := false }

/-- `mktemp` creates a file atomically for every usable parent and the
function-taking overload removes it even after the callback returns. -/
def MktempContract : Prop :=
  ∀ parent random cleanup,
    (mktemp parent random cleanup =
      if tempParentUsable parent then
        .ok { path := tempPath parent.text tempPrefix random [], kind := .file,
              present := true, cleanupRegistered := cleanup }
      else .error .io { path := [], kind := .file, present := false })
    ∧ ∀ object, (cleanupTemp object).present = false ∧
                  (cleanupTemp object).cleanupRegistered = false

/-- `mktempdir` creates a directory whose name has the requested prefix and
the function-taking overload removes that directory and its contents. -/
def MktempdirContract : Prop :=
  ∀ parent namePrefix random cleanup,
    (mktempdir parent namePrefix random cleanup =
      if tempParentUsable parent then
        .ok { path := tempPath parent.text namePrefix random [], kind := .directory,
              present := true, cleanupRegistered := cleanup }
      else .error .io { path := [], kind := .directory, present := false })
    ∧ ∀ object, (cleanupTemp object).present = false ∧
                  (cleanupTemp object).cleanupRegistered = false

def Ordered : List Nat → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, x ≤ y) ∧ Ordered xs

def occurrences (needle : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if needle == x then 1 else 0) + occurrences needle xs

def SameNames (left right : List Nat) : Prop :=
  ∀ name, occurrences name left = occurrences name right

/-- `readdir` preserves scan order when `sort=false`, sorts names when true,
returns every scanned name once, and applies `joinpath(dir, name)` exactly
when `join=true`. -/
def ReaddirOptions : Prop :=
  ∀ dir scan join sort,
    readdir dir scan join sort =
      (if sort then sortNames scan else scan).map (renderName dir join) ∧
    (sort = true → Ordered (sortNames scan)) ∧
    SameNames (if sort then sortNames scan else scan) scan

mutual
  def directoryCount : DirTree → Nat
    | .node _ _ children => 1 + forestDirectoryCount children

  def forestDirectoryCount : DirForest → Nat
    | .nil => 0
    | .cons head tail => directoryCount head + forestDirectoryCount tail
end

/-- `walkdir(topdown=true)` is preorder, `topdown=false` is postorder, and
both yield one row for every directory in sibling scan order. -/
def WalkdirOrder : Prop :=
  ∀ parent tree,
    walkdir parent tree true = walkTop parent tree ∧
    walkdir parent tree false = walkBottom parent tree ∧
    (walkdir parent tree true).length = directoryCount tree ∧
    (walkdir parent tree false).length = directoryCount tree

/-- `touch` creates a missing empty file, preserves existing contents, updates
the modification time, and returns the same path at the API layer. -/
def TouchPostcondition : Prop :=
  ∀ now state,
    (touch now state).present = true ∧
    (touch now state).mtime = now ∧
    (touch now state).bytes = if state.present then state.bytes else []

mutual
  def NonlinksHaveMode (mode : Nat) : ModeEntry → Prop
    | .file current => current = mode
    | .link _ => True
    | .directory tree => TreeNonlinksHaveMode mode tree

  def ForestNonlinksHaveMode (mode : Nat) : ModeForest → Prop
    | .nil => True
    | .cons head tail => NonlinksHaveMode mode head ∧ ForestNonlinksHaveMode mode tail

  def TreeNonlinksHaveMode (mode : Nat) : ModeTree → Prop
    | .directory current children => current = mode ∧ ForestNonlinksHaveMode mode children
end

mutual
  def LinksPreserved : ModeEntry → ModeEntry → Prop
    | .file _, .file _ => True
    | .link old, .link new => old = new
    | .directory old, .directory new => TreeLinksPreserved old new
    | _, _ => False

  def ForestLinksPreserved : ModeForest → ModeForest → Prop
    | .nil, .nil => True
    | .cons oldHead oldTail, .cons newHead newTail =>
        LinksPreserved oldHead newHead ∧ ForestLinksPreserved oldTail newTail
    | _, _ => False

  def TreeLinksPreserved : ModeTree → ModeTree → Prop
    | .directory _ oldChildren, .directory _ newChildren =>
        ForestLinksPreserved oldChildren newChildren
end

/-- Recursive chmod changes the root and every non-link descendant to the
requested mode, leaves symbolic links untouched, and nonrecursive chmod only
changes the root. -/
def ChmodRecursive : Prop :=
  ∀ mode tree,
    TreeNonlinksHaveMode mode (chmodTree mode true tree) ∧
    TreeLinksPreserved tree (chmodTree mode true tree) ∧
    match tree with
    | .directory _ children => chmodTree mode false tree = .directory mode children

/-- For every 16-bit POSIX mode, the file type and permission accessors decode
the documented fields. `ispath` uses `ioerrno`, and `filesize` returns size. -/
def StatModeLayout : Prop :=
  ∀ mode : Fin 65536, ∀ size errno,
    let st : StatStruct := { mode, size, ioerrno := errno }
    filemode st = mode ∧
    isdir st = (mode.val / 4096 % 16 == 4) ∧
    islink st = (mode.val / 4096 % 16 == 10) ∧
    ispath st = (errno == 0) ∧
    uperm st = mode.val / 64 % 8 ∧
    gperm st = mode.val / 8 % 8 ∧
    operm st = mode.val % 8 ∧
    filesize st = size

/-- Current-offset writes advance by the bytes written, explicit-offset writes
leave the position unchanged, reads advance by bytes returned, and seeking may
position beyond end while bytes available stays zero. -/
def FileOffsetSpec : Prop :=
  (∀ file bytes, file.isOpen = true →
    unsafeWrite file bytes none =
      .ok (bytes.length,
        { file with data := writeData file.data file.position bytes,
                    position := file.position + bytes.length })) ∧
  (∀ file bytes offset, file.isOpen = true →
    unsafeWrite file bytes (some offset) =
      .ok (bytes.length,
        { file with data := writeData file.data offset bytes,
                    position := file.position })) ∧
  (∀ file byte, file.isOpen = true → file.data[file.position]? = some byte →
    readByte file = .ok (some byte, { file with position := file.position + 1 })) ∧
  (∀ file count, file.isOpen = true →
    ∃ bytes out,
      readBytes file count = .ok (bytes, out) ∧
      out.position = file.position + bytes.length ∧
      bytes = (file.data.drop file.position).take count) ∧
  (∀ file position, file.isOpen = true →
    seek file position = .ok { file with position } ∧
    bytesavailable { file with position } = file.data.length - position)

end JuliaLean.Files
