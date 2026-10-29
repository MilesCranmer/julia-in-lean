import JuliaLean.Core
import JuliaLean.Strings.Basic
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.string
import JuliaLean.Registry.Types

/-!
# Model of `base/path.jl`

Path strings are the existing UTF-8 code-unit model `JStr`. `StringOps.fromBytes`, case mapping,
and username classification are the typed string operations supplied by `base/strings`; filesystem
operations are typed inputs because their definitions live outside this file. `Platform` is an
explicit parameter so both Unix and Windows source branches are represented in one model.
-/

namespace JuliaLean.base.path

open JuliaLean

abbrev Path := JuliaLean.Strings.JStr

inductive Platform where
  | unix
  | windows
  deriving DecidableEq, Repr

inductive PathError where
  | argumentError (message : String)
  | ioError (message : String)
  | methodError (message : String)
  deriving DecidableEq, Repr

/-- String operations used by `base/path.jl`; `fromBytes`, case mapping and Unicode predicates
are supplied by the corresponding string models. -/
structure StringOps where
  fromBytes : List UInt8 → Path
  fromBytesBytes : ∀ bytes, (fromBytes bytes).bytes = bytes
  lowercase : Path → Path
  uppercase : Path → Path
  validUsername : Path → Bool

/-- Filesystem operations used by path methods. `pwd` returns an absolute current directory;
`homedir` returns the current user's home; user lookup returns `none` for an unknown user;
`realpath` returns the existing path with symbolic links and dot components resolved, preserving
filesystem case where the filesystem does; `readlink` returns a link target; `ispath` and `isdir`
report current filesystem facts. -/
inductive LongPathReply where
  | failure (error : PathError)
  | result (length : Nat) (path : Path)
  deriving Repr

structure FileSystemOps where
  pwd : Unit → Path
  homedir : Unit → Except PathError Path
  homedirUser : Path → Option Path
  currentUser : Unit → Option Path
  windowsProfile : Path → Option Path
  isdir : Path → Bool
  realpath : Path → Except PathError Path
  readlink : Path → Except PathError Path
  ispath : Path → Bool
  samefile : Path → Path → Bool
  statUid : Path → Option Nat
  currentUid : Nat
  username : Nat → Option Path
  wideLength : Path → Nat
  longPathReplies : Path → List LongPathReply

abbrev Bytes := List UInt8

def slash : UInt8 := 47
def backslash : UInt8 := 92
def colon : UInt8 := 58
def dot : UInt8 := 46
def tilde : UInt8 := 126

def separator (os : Platform) : UInt8 := if os == .windows then backslash else slash

/--
Julia source: base/path.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline isseparator(c::UInt8) = c === UInt8('/')
```

Julia source: base/path.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline isseparator(c::UInt8) = c === UInt8('/') || c === UInt8('\\')
```
-/
def isseparatorByte (os : Platform) (c : UInt8) : Bool :=
  c == slash || (os == .windows && c == backslash)

/--
Julia source: base/path.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline isseparator(c::Char) = c === '/'
```

Julia source: base/path.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline isseparator(c::Char) = c === '/' || c === '\\'
```
-/
def isseparatorChar (os : Platform) (c : UInt32) : Bool :=
  c == 47 || (os == .windows && c == 92)

/--
Julia source: base/path.jl:37-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function isdriveletter(c::UInt8)
        UInt8('A') <= c <= UInt8('Z') ||
        UInt8('a') <= c <= UInt8('z')
    end
```
-/
def isdriveletter (c : UInt8) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)

/--
Julia source: base/path.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline isdriveletter(c::Char) = isascii(c) && isdriveletter(UInt8(c))
```
-/
def isdriveletterChar (c : UInt32) : Bool :=
  c < 128 && isdriveletter (UInt8.ofNat c.toNat)

def findFrom (p : UInt8 → Bool) : Nat → Bytes → Option Nat
  | _, [] => none
  | i, c :: cs => if p c then some i else findFrom p (i + 1) cs

def findAtOrAfter (p : UInt8 → Bool) (bs : Bytes) (start : Nat) : Option Nat :=
  findFrom p start (bs.drop start)

def findLastFrom (p : UInt8 → Bool) : Nat → Bytes → Option Nat
  | _, [] => none
  | i, c :: cs =>
    match findLastFrom p (i + 1) cs with
    | some j => some j
    | none => if p c then some i else none

def findLast (p : UInt8 → Bool) (bs : Bytes) : Option Nat := findLastFrom p 0 bs

def isSep (os : Platform) (c : UInt8) : Bool := isseparatorByte os c

def appendPath (ops : StringOps) (a b : Path) : Path := ops.fromBytes (a.bytes ++ b.bytes)

def emptyPath (ops : StringOps) : Path := ops.fromBytes []


def splitAt (ops : StringOps) (bs : Bytes) (i : Nat) : Path × Path :=
  (ops.fromBytes (bs.take i), ops.fromBytes (bs.drop i))




/--
Julia source: base/path.jl:42-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _split_longunc(s::String)::Tuple{String, String}
        # Long UNC path, e.g. `\\?\UNC\server\share`
        # Based on previous implementation matching with regex
        # S = raw"[\\/]"; N = raw"[^\\/]";
        # r"^$(S)$(S)\?$(S)UNC$(S)$(N)+$(S)$(N)+"sa

        if (ncodeunits(s) >= 11 &&
            isseparator(codeunit(s, 1)) &&
            isseparator(codeunit(s, 2)) &&
            codeunit(s, 3) === UInt8('?') &&
            isseparator(codeunit(s, 4)) &&
            codeunit(s, 5) === UInt8('U') &&
            codeunit(s, 6) === UInt8('N') &&
            codeunit(s, 7) === UInt8('C') &&
            isseparator(codeunit(s, 8))
        )
            # Ensure we have [sequence of non-separator] - single separator - [sequence of non-separator].
            # Since the prefix raw"\\?\UNC\" is always 8 codeunits, we start at index 9.
            i = findnext(isseparator, s, 9)
            if (!isnothing(i) &&
                i >= 10 && # implies !isseparator(s[9])
                ncodeunits(s) > i && # Need something after the separator
                !isseparator(codeunit(s, i+1)) # Consecutive separators does not count
            )
                # Stop just before next separator if it exists,
                # otherwise the whole string is a drive
                j = something(findnext(isseparator, s, i+1), lastindex(s)+1)
                return s[1:prevind(s, j)], s[j:end]
            end
        end
        return "", s
    end
```
-/
def splitLongunc (os : Platform) (ops : StringOps) (s : Path) : Path × Path := Id.run do
  let b := s.bytes
  if b.length ≥ 11 && isSep os (b[0]!) && isSep os (b[1]!) && b[2]! == 63 &&
      isSep os (b[3]!) && b[4]! == 85 && b[5]! == 78 && b[6]! == 67 && isSep os (b[7]!) then
    match findAtOrAfter (isSep os) b 8 with
    | some i =>
      if i ≥ 9 && b.length > i && !isSep os (b[i + 1]!) then
        let j := (findAtOrAfter (isSep os) b (i + 1)).getD b.length
        return (ops.fromBytes (b.take j), ops.fromBytes (b.drop j))
      else return (emptyPath ops, s)
    | none => return (emptyPath ops, s)
  else return (emptyPath ops, s)

/--
Julia source: base/path.jl:75-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _split_longdriveletter(s::String)::Tuple{String, String}
        # Long drive letter, e.g. `\\?\C:`
        # Based on implementation matching with regex
        # S = raw"[\\/]"; N = raw"[^\\/]"; drive = "$(N):";
        # r"$(S)$(S)\?$(S)$(drive)"sa
        if (ncodeunits(s) >= 6 &&
            isseparator(codeunit(s, 1)) &&
            isseparator(codeunit(s, 2)) &&
            codeunit(s, 3) === UInt8('?') &&
            isseparator(codeunit(s, 4)) &&
            !isseparator(codeunit(s, 5)) && # Any ascii char except separators passes as the drive letter
            codeunit(s, 6) == UInt8(':') # This effectively limits codeunit(s, 5) to ascii
        )
            return s[1:6], s[nextind(s, 6):end]
        end
        return "", s
    end
```
-/
def splitLongdriveletter (os : Platform) (ops : StringOps) (s : Path) : Path × Path :=
  let b := s.bytes
  if b.length ≥ 6 && isSep os (b[0]!) && isSep os (b[1]!) && b[2]! == 63 &&
      isSep os (b[3]!) && !isSep os (b[4]!) && b[5]! == colon then
    splitAt ops b 6
  else (emptyPath ops, s)

/--
Julia source: base/path.jl:93-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function _split_uncpath(s::String)::Tuple{String, String}
        # UNC path, e.g. `\\server\share`
        # Based on previous implementation matching with regex
        # S = raw"[\\/]"; N = raw"[^\\/]";
        # r"$(S)$(S)$(N)+$(S)$(N)+"sa
        if (ncodeunits(s) >= 5 && # Not shorter than `\\a\b`
            isseparator(codeunit(s, 1)) &&
            isseparator(codeunit(s, 2))
        )
            # Ensure we have [sequence of non-separator] - single separator - [sequence of non-separator].
            # Since the prefix raw"\\" is always 2 codeunits, we start at index 3.
            i = findnext(isseparator, s, 3)
            if (!isnothing(i) &&
                i >= 4 && # implies !isseparator(s[3])
                ncodeunits(s) > i && # Need something after the separator
                !isseparator(codeunit(s, i+1)) # Consecutive separators does not count
            )
                # Stop just before next separator if it exists,
                # otherwise the whole string is a drive
                j = something(findnext(isseparator, s, i+1), lastindex(s)+1)
                return s[1:prevind(s, j)], s[j:end]
            end
        end
        return "", s
    end
```
-/
def splitUncpath (os : Platform) (ops : StringOps) (s : Path) : Path × Path := Id.run do
  let b := s.bytes
  if b.length ≥ 5 && isSep os (b[0]!) && isSep os (b[1]!) then
    match findAtOrAfter (isSep os) b 2 with
    | some i =>
      if i ≥ 3 && b.length > i && !isSep os (b[i + 1]!) then
        let j := (findAtOrAfter (isSep os) b (i + 1)).getD b.length
        return (ops.fromBytes (b.take j), ops.fromBytes (b.drop j))
      else return (emptyPath ops, s)
    | none => return (emptyPath ops, s)
  else return (emptyPath ops, s)

/--
Julia source: base/path.jl:25-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
if Sys.isunix()
    const path_separator    = "/"
    @inline isseparator(c::Char) = c === '/'
    @inline isseparator(c::UInt8) = c === UInt8('/')

    splitdrive(path::String) = ("",path)
elseif Sys.iswindows()
```

Julia source: base/path.jl:119-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function splitdrive(path::String)::Tuple{String, String}
        if !isempty(path)
            # Fast return if path does not contain a drive
            if !isseparator(codeunit(path, 1)) && (codeunit(path, 1) < 0x80)
                # Drive letter, e.g. `C:`
                # Any ascii char except separators passes as the drive letter
                colonind = nextind(path, 1)
                if checkbounds(Bool, path, colonind) && path[colonind] === ':'
                    return path[1:colonind], path[colonind+1:end]
                end
            elseif ncodeunits(path) >= 2 && isseparator(codeunit(path, 2))
                # All other drive types must start with two separators

                # Long UNC path, e.g. `\\?\UNC\server\share`
                drive, rest = _split_longunc(path)
                !isempty(drive) && return drive, rest

                # Long drive letter, e.g. `\\?\C:`
                drive, rest = _split_longdriveletter(path)
                !isempty(drive) && return drive, rest

                # UNC path, e.g. `\\server\share`
                drive, rest = _split_uncpath(path)
                !isempty(drive) && return drive, rest
            end
        end

        return "", path
    end
else
    error("path primitives for this OS need to be defined")
end


"""
    splitdrive(path::AbstractString) -> (drive::AbstractString, path::AbstractString)

On Windows, split a path into the drive letter part and the path part. On Unix systems, the
first component is always the empty string.
"""
splitdrive(path::AbstractString)
```
-/
def splitdrive (os : Platform) (ops : StringOps) (path : Path) : Path × Path :=
  match os with
  | .unix => (emptyPath ops, path)
  | .windows => Id.run do
      let b := path.bytes
      if !b.isEmpty then
        if !isSep .windows b[0]! && b[0]!.toNat < 128 then
          if b.length ≥ 2 && b[1]! == colon then return splitAt ops b 2
        else if b.length ≥ 2 && isSep .windows b[1]! then
          let (drive, rest) := splitLongunc .windows ops path
          if !drive.bytes.isEmpty then return (drive, rest)
          let (drive, rest) := splitLongdriveletter .windows ops path
          if !drive.bytes.isEmpty then return (drive, rest)
          let (drive, rest) := splitUncpath .windows ops path
          if !drive.bytes.isEmpty then return (drive, rest)
      return (emptyPath ops, path)

/--
Julia source: base/path.jl:200-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
function isabspath(path::String)
    isempty(path) && return false
    # Paths starting with "/" are considered absolute also on windows
    # This captures e.g. UNC paths, but does not guarantee a valid path.
    # Also note that isabspath(x) does not imply !isempty(splitdrive(x)[1])
    isseparator(codeunit(path, 1) ) && return true

    @static if Sys.iswindows()
        # the letter before : in e.g. "C:\" must be a valid drive letter.
        # This differs from `splitdrive`, where any non-separator single codeunit char is
        # accepted.
        firstsep = findfirst(isseparator, codeunits(path))
        if (!isnothing(firstsep) &&
            firstsep >= 3 &&
            codeunit(path, firstsep-1) == UInt(':')
        )
            for b in codeunits(path)[1:firstsep-2]
                !isdriveletter(b) && return false
            end
            return true
        end
    end
    return false
end

"""
    isabspath(path::AbstractString)::Bool

Determine whether a path is absolute (begins at the root directory).

# Examples
```jldoctest
julia> isabspath("/home")
true

julia> isabspath("home")
false
```
"""
isabspath(path::AbstractString)
````
-/
def isabspath (os : Platform) (path : Path) : Bool := Id.run do
  let b := path.bytes
  if b.isEmpty then return false
  if isSep os b[0]! then return true
  if os == .windows then
    match findAtOrAfter (isSep os) b 0 with
    | some firstsep =>
      if firstsep ≥ 2 && b[firstsep - 1]! == colon then
        return (b.take (firstsep - 1)).all isdriveletter
    | none => pure ()
  return false




/--
Julia source: base/path.jl:278-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Common splitdir functionality without splitdrive, needed for splitpath.
_splitdir_nodrive(path::String) = _splitdir_nodrive("", path)
function _splitdir_nodrive(drive::String, path::String)::Tuple{String, String}
    lastsepind = findlast(isseparator, path)

    isnothing(lastsepind) && return drive, path

    dir = path[1:something(findprev(!isseparator, path, lastsepind), 1)]
    tail = path[nextind(path, lastsepind):end]

    return drive * dir, tail
end
```
-/
def splitdirNoDrive (os : Platform) (ops : StringOps) (drive path : Path) : Path × Path :=
  let p := path.bytes
  match findLast (isSep os) p with
  | none => (drive, path)
  | some lastsep =>
    let preceding := p.take lastsep
    let dirEnd := (findLast (fun c => !isSep os c) preceding).getD 0
    (ops.fromBytes (drive.bytes ++ p.take (dirEnd + 1)), ops.fromBytes (p.drop (lastsep + 1)))

/--
Julia source: base/path.jl:262-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    splitdir(path::AbstractString) -> (dir::AbstractString, file::AbstractString)

Split a path into a tuple of the directory name and file name.

# Examples
```jldoctest
julia> splitdir("/home/myuser")
("/home", "myuser")
```
"""
function splitdir(path::String)
    a, b = splitdrive(path)
    _splitdir_nodrive(a,b)
end

````
-/
def splitdir (os : Platform) (ops : StringOps) (path : Path) : Path × Path :=
  let (drive, rest) := splitdrive os ops path
  splitdirNoDrive os ops drive rest




/--
Julia source: base/path.jl:291-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    dirname(path::AbstractString)::String

Get the directory part of a path. Trailing characters ('/' or '\\') in the path are
counted as part of the path.

# Examples
```jldoctest
julia> dirname("/home/myuser")
"/home"

julia> dirname("/home/myuser/")
"/home/myuser"
```

See also [`basename`](@ref).
"""
dirname(path::AbstractString) = splitdir(path)[1]
````
-/
def dirname (os : Platform) (ops : StringOps) (path : Path) : Path := (splitdir os ops path).1

/--
Julia source: base/path.jl:310-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    basename(path::AbstractString)::String

Get the file name part of a path.

!!! note
    This function differs slightly from the Unix `basename` program, where trailing slashes are ignored,
    i.e. `\$ basename /foo/bar/` returns `bar`, whereas `basename` in Julia returns an empty string `""`.

# Examples
```jldoctest
julia> basename("/home/myuser/example.jl")
"example.jl"

julia> basename("/home/myuser/")
""
```

See also [`dirname`](@ref).
"""
basename(path::AbstractString) = splitdir(path)[2]
````
-/
def basename (os : Platform) (ops : StringOps) (path : Path) : Path := (splitdir os ops path).2

/--
Julia source: base/path.jl:332-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    splitext(path::AbstractString) -> (path_without_extension::String, extension::String)

If the last component of a path contains one or more dots, split the path into everything before the
last dot and everything including and after the dot. Otherwise, return a tuple of the argument
unmodified and the empty string. "splitext" is short for "split extension".

# Examples
```jldoctest
julia> splitext("/home/myuser/example.jl")
("/home/myuser/example", ".jl")

julia> splitext("/home/myuser/example.tar.gz")
("/home/myuser/example.tar", ".gz")

julia> splitext("/home/my.user/example")
("/home/my.user/example", "")
```
"""
function splitext(path::String)::Tuple{String, String}
    drive, p = splitdrive(path)
    lastdot = findlast('.', p)
    if !isnothing(lastdot)
        # No separator after the last dot
        if isnothing(findnext(isseparator, p, lastdot))
            # No separator just before the last dot
            prev = prevind(p, lastdot)
            if checkbounds(Bool, p, prev)
                if !isseparator(p[prev])
                    return drive * p[1:prev], p[lastdot:end]
                end
            end
        end
    end

    return (path, "")
end
````
-/
def splitext (os : Platform) (ops : StringOps) (path : Path) : Path × Path := Id.run do
  let (drive, p) := splitdrive os ops path
  let b := p.bytes
  match findLast (fun c => c == dot) b with
  | some lastdot =>
    if (findAtOrAfter (isSep os) b (lastdot + 1)).isNone && lastdot > 0 && !isSep os b[lastdot - 1]! then
      return (ops.fromBytes (drive.bytes ++ b.take lastdot), ops.fromBytes (b.drop lastdot))
    else return (path, emptyPath ops)
  | none => return (path, emptyPath ops)




def splitpathLoop (os : Platform) (ops : StringOps) : Nat → Path → List Path → List Path
  | 0, _, out => out
  | fuel + 1, p, out =>
    if p.bytes.isEmpty then out
    else
      let (dir, base) := splitdirNoDrive os ops (emptyPath ops) p
      if dir.bytes == p.bytes then dir :: out
      else splitpathLoop os ops fuel dir (if base.bytes.isEmpty then out else base :: out)

/--
Julia source: base/path.jl:373-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    splitpath(path::AbstractString)::Vector{String}

Split a file path into all its path components. This is the opposite of
`joinpath`. Returns an array of substrings, one for each directory or file in
the path, including the root directory if present.

!!! compat "Julia 1.1"
    This function requires at least Julia 1.1.

# Examples
```jldoctest
julia> splitpath("/home/myuser/example.jl")
4-element Vector{String}:
 "/"
 "home"
 "myuser"
 "example.jl"
```
"""
splitpath(p::AbstractString) = splitpath(String(p)::String)

function splitpath(p::String)
    drive, p = splitdrive(p)
    out = String[]
    isempty(p) && (pushfirst!(out,p))  # "" means the current directory.
    while !isempty(p)
        dir, base = _splitdir_nodrive(p)
        dir == p && (pushfirst!(out, dir); break)  # Reached root node.
        if !isempty(base)  # Skip trailing '/' in basename
            pushfirst!(out, base)
        end
        p = dir
    end
    if !isempty(drive)  # Tack the drive back on to the first element.
        out[1] = drive*out[1]  # Note that length(out) is always >= 1.
    end
    return out
end
````
-/
def splitpath (os : Platform) (ops : StringOps) (p : Path) : List Path := Id.run do
  let (drive, rest) := splitdrive os ops p
  let out := if rest.bytes.isEmpty then [rest] else []
  let out := splitpathLoop os ops (rest.bytes.length + 1) rest out
  if !drive.bytes.isEmpty then
    match out with
    | [] => [drive]
    | first :: tail => appendPath ops drive first :: tail
  else out




inductive PathValue where
  | string (value : Path)
  | nonString
  deriving DecidableEq, Repr

/--
Julia source: base/path.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    assertstring(x) = x isa AbstractString || throw(ArgumentError("path component is not a string: $(repr(x))"))
```

Julia source: base/path.jl:466-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    assertstring(x) = x isa AbstractString || throw(ArgumentError("path component is not a string: $(repr(x))"))
```
-/
def assertstring : PathValue → Except PathError Bool
  | .string _ => .ok true
  | .nonString => .error (.argumentError "path component is not a string")

def pathValueString : PathValue → Except PathError Path
  | .string value => .ok value
  | .nonString => .error (.argumentError "path component is not a string")

def joinStep (os : Platform) (ops : StringOps) (path p : Path) : Path :=
  if isabspath os p then p
  else if path.bytes.isEmpty || path.bytes.getLast? == some (separator os) then appendPath ops path p
  else appendPath ops (ops.fromBytes (path.bytes ++ [separator os])) p

def joinWindowsLoop (ops : StringOps) : List PathValue → Path → Path → Path → Except PathError (Path × Path × Path)
  | [], resultDrive, resultPath, lastPath => .ok (resultDrive, resultPath, lastPath)
  | value :: rest, resultDrive, resultPath, _ => do
      let _ ← assertstring value
      let p ← pathValueString value
      let (pDrive, pPath) := splitdrive .windows ops p
      if !pPath.bytes.isEmpty && isSep .windows pPath.bytes.head! then
        let resultDrive := if !pDrive.bytes.isEmpty || !resultDrive.bytes.isEmpty then pDrive else resultDrive
        joinWindowsLoop ops rest resultDrive pPath pPath
      else if !pDrive.bytes.isEmpty && pDrive.bytes != resultDrive.bytes &&
          (ops.lowercase pDrive).bytes != (ops.lowercase resultDrive).bytes then
        joinWindowsLoop ops rest pDrive pPath pPath
      else
        let resultPath :=
          if !resultPath.bytes.isEmpty && !isSep .windows resultPath.bytes.getLast! then
            appendPath ops resultPath (ops.fromBytes [backslash])
          else resultPath
        joinWindowsLoop ops rest resultDrive (appendPath ops resultPath pPath) pPath

def joinUnixLoop (ops : StringOps) : List PathValue → Path → Except PathError Path
  | [], path => .ok path
  | value :: rest, path => do
      let _ ← assertstring value
      let p ← pathValueString value
      joinUnixLoop ops rest (joinStep .unix ops path p)

/--
Julia source: base/path.jl:413-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
if Sys.iswindows()

function joinpath(paths::Union{Tuple, AbstractVector})::String
    assertstring(x) = x isa AbstractString || throw(ArgumentError("path component is not a string: $(repr(x))"))

    isempty(paths) && throw(ArgumentError("collection of path components must be non-empty"))
    assertstring(paths[1])
    result_drive, result_path = splitdrive(paths[1])

    p_path = ""
    for i in firstindex(paths)+1:lastindex(paths)
        assertstring(paths[i])
        p_drive, p_path = splitdrive(paths[i])

        if !isempty(p_path) && isseparator(first(p_path))
            # second path is absolute
            if !isempty(p_drive) || !isempty(result_drive)
                result_drive = p_drive
            end
            result_path = p_path
            continue
        elseif !isempty(p_drive) && p_drive != result_drive
            if lowercase(p_drive) != lowercase(result_drive)
                # different drives, ignore the first path entirely
                result_drive = p_drive
                result_path = p_path
                continue
            end
        end

        # second path is relative to the first
        if !isempty(result_path) && !isseparator(result_path[end])
            result_path *= "\\"
        end

        result_path = result_path * p_path
    end

    # add separator between UNC and non-absolute path
    if (!isempty(p_path) &&
        !isseparator(result_path[1]) &&
        !isempty(result_drive) &&
        result_drive[end] != ':'
    )
        return result_drive * "\\" * result_path
    end

    return result_drive * result_path
end

else

function joinpath(paths::Union{Tuple, AbstractVector})::String
    assertstring(x) = x isa AbstractString || throw(ArgumentError("path component is not a string: $(repr(x))"))

    isempty(paths) && throw(ArgumentError("collection of path components must be non-empty"))
    assertstring(paths[1])
    path = paths[1]
    for i in firstindex(paths)+1:lastindex(paths)
        p = paths[i]
        assertstring(p)
        if isabspath(p)
            path = p
        elseif isempty(path) || path[end] == '/'
            path *= p
        else
            path *= "/" * p
        end
    end
    return path
end

end # os-test

joinpath(paths::AbstractString...)::String = joinpath(paths)

"""
    joinpath(parts::AbstractString...)::String
    joinpath(parts::Vector{AbstractString})::String
    joinpath(parts::Tuple{AbstractString})::String

Join path components into a full path. If some argument is an absolute path or
(on Windows) has a drive specification that doesn't match the drive computed for
the join of the preceding paths, then prior components are dropped.

Note on Windows since there is a current directory for each drive, `joinpath("c:", "foo")`
represents a path relative to the current directory on drive "c:" so this is equal to "c:foo",
not "c:\\foo". Furthermore, `joinpath` treats this as a non-absolute path and ignores the drive
letter casing, hence `joinpath("C:\\\\A","c:b") = "C:\\\\A\\\\b"`.

# Examples
```jldoctest
julia> joinpath("/home/myuser", "example.jl")
"/home/myuser/example.jl"
```

```jldoctest
julia> joinpath(["/home/myuser", "example.jl"])
"/home/myuser/example.jl"
```
"""
joinpath
````
-/
def joinpath (os : Platform) (ops : StringOps) (paths : List PathValue) : Except PathError Path := do
  match paths with
  | [] => throw (.argumentError "collection of path components must be non-empty")
  | first :: rest => do
      let _ ← assertstring first
      let first ← pathValueString first
      if os == .unix then joinUnixLoop ops rest first
      else
        let (resultDrive, resultPath) := splitdrive .windows ops first
        let (resultDrive, resultPath, lastPath) ← joinWindowsLoop ops rest resultDrive resultPath (emptyPath ops)
        if !lastPath.bytes.isEmpty && !isSep .windows resultPath.bytes.head! &&
            !resultDrive.bytes.isEmpty && resultDrive.bytes.getLast! != colon then
          return appendPath ops (appendPath ops resultDrive (ops.fromBytes [backslash])) resultPath
        return appendPath ops resultDrive resultPath

def joinpathStrings (os : Platform) (ops : StringOps) (paths : List Path) : Except PathError Path :=
  joinpath os ops (paths.map PathValue.string)




def splitRuns (os : Platform) : Bytes → List Bytes
  | [] => [[]]
  | c :: cs =>
    match splitRuns os cs with
    | [] => [[c]]
    | word :: rest =>
      if isSep os c then
        if cs.head?.map (isSep os) == some true then word :: rest else [] :: word :: rest
      else (c :: word) :: rest

/--
Julia source: base/path.jl:516-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _split_at_separators(path::AbstractString; keepempty = true)
    # Equivalent to Base.split(path, r"/+"sa; keepempty) (r"[\\/]+"sa on windows)
    # Since there is no split between consecutive separators, keepempty
    # only has an effect on strings starting or ending with separators.
    out = String[]
    start = 1

    while true
        nextsep = findnext(isseparator, path, start)

        stop = isnothing(nextsep) ? lastindex(path) : prevind(path, nextsep)

        substr = String(view(path, start:stop))
        if keepempty || !isempty(substr)
            push!(out, substr)
        end

        isnothing(nextsep) && break

        start = something(findnext(!isseparator, path, nextsep+1), nextind(path, lastindex(path)))
    end
    return out
end
```
-/
def splitAtSeparators (os : Platform) (ops : StringOps) (path : Path) (keepempty : Bool := true) : List Path :=
  let runs := splitRuns os path.bytes
  let runs := if keepempty then runs else runs.filter (· ≠ [])
  runs.map ops.fromBytes

def dotdot : Bytes := [dot, dot]

def removeFirstPair : List Bytes → Option (List Bytes)
  | a :: b :: rest =>
    if a != dotdot && b == dotdot then some rest
    else (removeFirstPair (b :: rest)).map (a :: ·)
  | _ => none

def cleanLoop : Nat → List Bytes → List Bytes
  | 0, parts => parts
  | fuel + 1, parts =>
    match removeFirstPair parts with
    | none => parts
    | some parts => cleanLoop fuel parts

def joinSep (os : Platform) : List Bytes → Bytes
  | [] => []
  | [a] => a
  | a :: rest => a ++ separator os :: joinSep os rest

def isdirpath (os : Platform) (ops : StringOps) (path : Path) : Bool :=
  let (_, withoutDrive) := splitdrive os ops path
  let (_, tail) := splitdirNoDrive os ops (emptyPath ops) withoutDrive
  tail.bytes.isEmpty || tail.bytes == [dot] || tail.bytes == dotdot

/--
Julia source: base/path.jl:540-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    normpath(path::AbstractString)::String

Normalize a path, removing "." and ".." entries and changing "/" to the canonical path separator
for the system.

# Examples
```jldoctest
julia> normpath("/home/myuser/../example.jl")
"/home/example.jl"

julia> normpath("Documents/Julia") == joinpath("Documents", "Julia")
true
```
"""
function normpath(path::String)
    isabs = isabspath(path)
    isdir = isdirpath(path)
    drive, path = splitdrive(path)
    parts = _split_at_separators(path, keepempty = false)
    filter!(!=("."), parts)
    while true
        clean = true
        for j = 1:length(parts)-1
            if parts[j] != ".." && parts[j+1] == ".."
                deleteat!(parts, j:j+1)
                clean = false
                break
            end
        end
        clean && break
    end
    if isabs
        while !isempty(parts) && parts[1] == ".."
            popfirst!(parts)
        end
    elseif isempty(parts)
        push!(parts, ".")
    end
    path = join(parts, path_separator)
    if isabs
        path = path_separator*path
    end
    if isdir && !isdirpath(path)
        path *= path_separator
    end
    string(drive,path)
end
````
-/
def normpath (os : Platform) (ops : StringOps) (path : Path) : Path := Id.run do
  let isabs := isabspath os path
  let isdir := isdirpath os ops path
  let (drive, p) := splitdrive os ops path
  let parts := (splitRuns os p.bytes).filter (· ≠ []) |>.filter (· != [dot])
  let parts := cleanLoop (parts.length + 1) parts
  let parts := if isabs then parts.dropWhile (· == dotdot)
    else if parts.isEmpty then [[dot]] else parts
  let normalized := joinSep os parts
  let normalized := if isabs then separator os :: normalized else normalized
  let normalized := if isdir && !(isdirpath os ops (ops.fromBytes normalized)) then normalized ++ [separator os] else normalized
  ops.fromBytes (drive.bytes ++ normalized)

/--
Julia source: base/path.jl:589-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    normpath(path::AbstractString, paths::AbstractString...)::String

Convert a set of paths to a normalized path by joining them together and removing
"." and ".." entries. Equivalent to `normpath(joinpath(path, paths...))`.
"""
normpath(a::AbstractString, b::AbstractString...) = normpath(joinpath(a,b...))
```
-/
def normpathMany (os : Platform) (ops : StringOps) (first : Path) (rest : List Path) : Except PathError Path := do
  let joined ← joinpathStrings os ops (first :: rest)
  return normpath os ops joined




/--
Julia source: base/path.jl:597-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    abspath(path::AbstractString)::String

Convert a path to an absolute path by adding the current directory if necessary.
Also normalizes the path as in [`normpath`](@ref).

# Examples

If you are in a directory called `JuliaExample` and the data you are using is two levels up relative to the `JuliaExample` directory, you could write:

    abspath("../../data")

Which gives a path like `"/home/JuliaUser/data/"`.

See also [`joinpath`](@ref), [`pwd`](@ref), [`expanduser`](@ref).
"""
@noinline function abspath(a::String)::String
    if !isabspath(a)
        cwd = pwd()
        a_drive, a_nodrive = splitdrive(a)
        if a_drive != "" && lowercase(splitdrive(cwd)[1]) != lowercase(a_drive)
            cwd = a_drive * path_separator
            a = joinpath(cwd, a_nodrive)
        else
            a = joinpath(cwd, a)
        end
    end
    return normpath(a)
end
```
-/
def abspath (os : Platform) (ops : StringOps) (pwd : Unit → Path) (a : Path) : Except PathError Path := do
  let a ← if !isabspath os a then do
    let cwd := pwd ()
    let (aDrive, aNoDrive) := splitdrive os ops a
    if os == .windows && !aDrive.bytes.isEmpty &&
        (ops.lowercase (splitdrive .windows ops cwd).1).bytes != (ops.lowercase aDrive).bytes then
      let root := appendPath ops aDrive (ops.fromBytes [separator os])
      joinpathStrings os ops [root, aNoDrive]
    else joinpathStrings os ops [cwd, a]
  else pure a
  return normpath os ops a




/--
Julia source: base/path.jl:165-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    homedir()::String

Return the current user's home directory.

!!! note
    `homedir` determines the home directory via `libuv`'s `uv_os_homedir`. For details
    (for example on how to specify the home directory via environment variables), see the
    [`uv_os_homedir` documentation](http://docs.libuv.org/en/v1.x/misc.html#c.uv_os_homedir).

    homedir(username::AbstractString)::Union{String,Nothing}

Return the home directory for the given `username`, or `nothing` if the user does not exist.
On Unix, this performs a lookup via `getpwnam_r`. On Windows, the user's SID is resolved and
the profile path is read from the registry; if that fails, the profile directory is inferred
from the current user's home directory.

See also [`Sys.username`](@ref).
"""
function homedir()
    buf = Base.StringVector(AVG_PATH - 1) # space for null-terminator implied by StringVector
    sz = Base.RefValue{Csize_t}(length(buf) + 1) # total buffer size including null
    while true
        rc = ccall(:uv_os_homedir, Cint, (Ptr{UInt8}, Ptr{Csize_t}), buf, sz)
        if rc == 0
            resize!(buf, sz[])
            return String(buf)
        elseif rc == Base.UV_ENOBUFS
            resize!(buf, sz[] - 1) # space for null-terminator implied by StringVector
        else
            uv_error("homedir()", rc)
        end
    end
end
```
-/
def homedir (fs : FileSystemOps) : Except PathError Path := fs.homedir ()

/--
Julia source: base/path.jl:371-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pathsep() = path_separator
```
-/
def pathsep (os : Platform) : UInt8 := separator os

/--
Julia source: base/path.jl:654-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    realpath(path::AbstractString)::String

Canonicalize a path by expanding symbolic links and removing "." and ".." entries.
On case-insensitive case-preserving filesystems (typically Mac and Windows), the
filesystem's stored case for the path is returned.

(This function throws an exception if `path` does not exist in the filesystem.)
"""
function realpath(path::AbstractString)
    req = Libc.malloc(_sizeof_uv_fs)
    try
        ret = ccall(:uv_fs_realpath, Cint,
                    (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Ptr{Cvoid}),
                    C_NULL, req, path, C_NULL)
        if ret < 0
            uv_fs_req_cleanup(req)
            uv_error("realpath($(repr(path)))", ret)
        end
        path = unsafe_string(ccall(:jl_uv_fs_t_ptr, Cstring, (Ptr{Cvoid},), req))
        uv_fs_req_cleanup(req)
        return path
    finally
        Libc.free(req)
    end
end
```
-/
def realpath (fs : FileSystemOps) (path : Path) : Except PathError Path := fs.realpath path




def replaceSeparators (os : Platform) (bs : Bytes) (replacement : UInt8) : Bytes :=
  bs.map (fun b => if isSep os b then replacement else b)


/--
Julia source: base/path.jl:708-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _win_profile_from_registry(username::AbstractString)
    # Step 1: Resolve username to a SID via LookupAccountNameW.
    # First call with zero-length buffers to get required sizes.
    wuser = cwstring(username)
    sid_size = Ref{UInt32}(0)
    domain_size = Ref{UInt32}(0)
    use = Ref{Int32}(0)
    ccall((:LookupAccountNameW, "advapi32"), stdcall, Cint,
          (Ptr{UInt16}, Ptr{UInt16}, Ptr{Cvoid}, Ptr{UInt32},
           Ptr{UInt16}, Ptr{UInt32}, Ptr{Int32}),
          C_NULL, wuser, C_NULL, sid_size, C_NULL, domain_size, use)
    sid_size[] == 0 && return nothing
    sid_buf = Vector{UInt8}(undef, sid_size[])
    domain_buf = Vector{UInt16}(undef, domain_size[])
    ret = ccall((:LookupAccountNameW, "advapi32"), stdcall, Cint,
                (Ptr{UInt16}, Ptr{UInt16}, Ptr{UInt8}, Ptr{UInt32},
                 Ptr{UInt16}, Ptr{UInt32}, Ptr{Int32}),
                C_NULL, wuser, sid_buf, sid_size, domain_buf, domain_size, use)
    ret == 0 && return nothing
    # Step 2: Convert SID to string form (e.g. "S-1-5-21-...").
    str_sid_ptr = Ref{Ptr{UInt16}}(C_NULL)
    ret = ccall((:ConvertSidToStringSidW, "advapi32"), stdcall, Cint,
                (Ptr{UInt8}, Ref{Ptr{UInt16}}), sid_buf, str_sid_ptr)
    ret == 0 && return nothing
    len = ccall(:wcslen, Csize_t, (Ptr{UInt16},), str_sid_ptr[])
    sid_str = transcode(String, unsafe_wrap(Array, str_sid_ptr[], len))
    ccall((:LocalFree, "kernel32"), stdcall, Ptr{Cvoid}, (Ptr{Cvoid},), str_sid_ptr[])
    # Step 3: Query the registry for the user's ProfileImagePath.
    subkey = cwstring("SOFTWARE\\Microsoft\\Windows NT\\CurrentVersion\\ProfileList\\$sid_str")
    value = cwstring("ProfileImagePath")
    buf_size = Ref{UInt32}(0)
    # RRF_RT_REG_SZ | RRF_RT_REG_EXPAND_SZ = 0x00000006
    HKEY_LOCAL_MACHINE = 0x80000002 % UInt
    ccall((:RegGetValueW, "advapi32"), stdcall, Clong,
          (UInt, Ptr{UInt16}, Ptr{UInt16}, UInt32, Ptr{UInt32}, Ptr{UInt16}, Ptr{UInt32}),
          HKEY_LOCAL_MACHINE, subkey, value, 0x00000006, C_NULL, C_NULL, buf_size)
    buf_size[] == 0 && return nothing
    buf = Vector{UInt16}(undef, buf_size[] ÷ 2)
    ret = ccall((:RegGetValueW, "advapi32"), stdcall, Clong,
                (UInt, Ptr{UInt16}, Ptr{UInt16}, UInt32, Ptr{UInt32}, Ptr{UInt16}, Ptr{UInt32}),
                HKEY_LOCAL_MACHINE, subkey, value, 0x00000006, C_NULL, buf, buf_size)
    ret != 0 && return nothing
    # Remove trailing null and convert to String.
    n = buf_size[] ÷ 2
    n > 0 && buf[n] == 0 && (n -= 1)
    home = transcode(String, buf[1:n])
    return isdir(home) ? home : nothing
end
```
-/
def winProfileFromRegistry (fs : FileSystemOps) (username : Path) : Option Path :=
  match fs.windowsProfile username with
  | some home => if fs.isdir home then some home else none
  | none => none

/--
Julia source: base/path.jl:683-707 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function homedir(username::AbstractString)
    # For the current user, just return homedir().
    current_user = try
        Sys.username()
    catch err
        err isa IOError || rethrow()
        nothing
    end
    if username == current_user
        return homedir()
    end
    # Look up the user's SID, then query the registry for their profile path.
    # This is the same approach Go uses (os/user.Lookup on Windows).
    home = _win_profile_from_registry(username)
    home !== nothing && return home
    # Fallback: assume profiles are siblings in the same parent directory,
    # but only if the current user's home follows the <parent>/<username>
    # convention. If not, we can't guess reliably.
    userhome = homedir()
    if current_user !== nothing && basename(userhome) == current_user
        home = joinpath(dirname(userhome), username)
        isdir(home) && return home
    end
    return nothing
end
```

Julia source: base/path.jl:781-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function homedir(username::AbstractString)
    # Thread-safe user lookup via getpwnam_r.
    # pwd_storage holds the struct passwd; 256 bytes is a generous upper bound
    # for all supported platforms (Linux x86-64: ~56 bytes, macOS arm64: ~80 bytes).
    pwd_storage = zeros(UInt8, 256)
    # The string buffer holds the pointed-to strings (pw_name, pw_dir, etc.).
    # Start at 1024 and double on ERANGE if any string is unusually long.
    buflen = 1024
    while buflen <= 65536
        str_buf = Vector{UInt8}(undef, buflen)
        result = Ref{Ptr{Cvoid}}(C_NULL)
        ret = ccall(:getpwnam_r, Cint,
                    (Cstring, Ptr{Cvoid}, Ptr{UInt8}, Csize_t, Ptr{Ptr{Cvoid}}),
                    username, pwd_storage, str_buf, Csize_t(buflen), result)
        if ret == 34  # ERANGE: string buffer too small, retry with more space
            buflen *= 2
        elseif ret == 0 && result[] != C_NULL
            # pw_uid sits at offset 2*sizeof(Ptr) in struct passwd on all supported
            # platforms (after pw_name and pw_passwd, which are both pointer-sized)
            uid = unsafe_load(Ptr{Cuint}(pointer(pwd_storage) + 2 * sizeof(Ptr{Cvoid})))
            pd = Libc.getpwuid(uid, false)
            return pd !== nothing ? pd.homedir : nothing
        else
            return nothing  # user not found or error
        end
    end
    return nothing
end
```
-/
def homedirUsername (os : Platform) (ops : StringOps) (fs : FileSystemOps)
    (username : Path) : Except PathError (Option Path) := do
  if os == .unix then return fs.homedirUser username
  let current := fs.currentUser ()
  match current with
  | some name =>
      if name.bytes == username.bytes then return some (← fs.homedir ())
  | none => pure ()
  match winProfileFromRegistry fs username with
  | some home => return some home
  | none => pure ()
  let userhome ← fs.homedir ()
  match current with
  | some name =>
      if (basename .windows ops userhome).bytes == name.bytes then
        let candidate := joinpathStrings .windows ops [dirname .windows ops userhome, username]
        match candidate with
        | .ok home => if fs.isdir home then return some home
        | .error _ => pure ()
  | none => pure ()
  return none



/--
Julia source: base/path.jl:854-883 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expanduser(path::Union{String, SubString{String}})::String
    y = iterate(path)
    y === nothing && return path
    c, i = y::Tuple{eltype(path),Int}
    c != '~' && return path
    # collect username: everything after ~ up to separator or end
    m = findnext(path_separator_re, path, i)
    j = prevind(path, m === nothing ?
        nextind(path, lastindex(path)) : first(m))
    username = SubString(path, i, j)
    # can't use a regex because of bootstrap order
    if isempty(username)
        home = homedir()
    elseif Sys.iswindows() || # ~username not supported on Windows
        !all(c -> isletter(c) || isdigit(c) || c in "._-", username) # invalid
        return path
    else
        home = homedir(username)
        home === nothing && return path
    end
    # use first separator in the rest of path in home
    if m !== nothing
        if Sys.iswindows()
            sep = path[first(m)]
            home = replace(home, path_separator_re => sep)
        end
        return home * SubString(path, first(m))
    end
    return home
end
```
-/
def expanduser (os : Platform) (ops : StringOps) (fs : FileSystemOps) (path : Path) : Except PathError Path := do
  let b := path.bytes
  if b.isEmpty || b.head! != tilde then return path
  let rest := b.drop 1
  let sep := findFrom (isSep os) 0 rest
  let usernameBytes := match sep with | none => rest | some i => rest.take i
  let suffix := match sep with | none => [] | some i => rest.drop i
  let username := ops.fromBytes usernameBytes
  let home ← if usernameBytes.isEmpty then fs.homedir ()
    else if os == .windows || !ops.validUsername username then return path
    else match ← homedirUsername os ops fs username with
      | none => return path
      | some home => pure home
  let homeBytes := if os == .windows && !suffix.isEmpty then
    replaceSeparators os home.bytes suffix.head!
    else home.bytes
  return ops.fromBytes (homeBytes ++ suffix)




def commonLen : List Bytes → List Bytes → Nat
  | a :: as, b :: bs => if a == b then commonLen as bs + 1 else 0
  | _, _ => 0

def lastNonempty (paths : List Bytes) : Nat := go paths 1 0
where
  go : List Bytes → Nat → Nat → Nat
    | [], _, acc => acc
    | p :: rest, i, acc => go rest (i + 1) (if p.isEmpty then acc else i)

def repeatBytes (s : Bytes) : Nat → Bytes
  | 0 => []
  | n + 1 => s ++ repeatBytes s n

def splitPathArrays (os : Platform) (ops : StringOps) (absolutePath absoluteStart : Path) :
    List Path × List Path :=
  (splitAtSeparators os ops absolutePath true, splitAtSeparators os ops absoluteStart true)

/--
Julia source: base/path.jl:921-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function relpath(path::String, startpath::String = ".")
    isempty(path) && throw(ArgumentError("`path` must be non-empty"))
    isempty(startpath) && throw(ArgumentError("`startpath` must be non-empty"))
    curdir = "."
    pardir = ".."
    path == startpath && return curdir
    if Sys.iswindows()
        path_drive, path_without_drive = splitdrive(path)
        startpath_drive, startpath_without_drive = splitdrive(startpath)
        isempty(startpath_drive) && (startpath_drive = path_drive) # by default assume same as path drive
        uppercase(path_drive) == uppercase(startpath_drive) || return abspath(path) # if drives differ return first path
        path_arr  = _split_at_separators(abspath(path_drive * path_without_drive))
        start_arr = _split_at_separators(abspath(path_drive * startpath_without_drive))
    else
        path_arr  = _split_at_separators(abspath(path))
        start_arr = _split_at_separators(abspath(startpath))
    end
    i = 0
    while i < min(length(path_arr), length(start_arr))
        i += 1
        if path_arr[i] != start_arr[i]
            i -= 1
            break
        end
    end
    pathpart = join(path_arr[i+1:something(findlast(x -> !isempty(x), path_arr), 0)], path_separator)
    prefix_num = something(findlast(x -> !isempty(x), start_arr), 0) - i - 1
    if prefix_num >= 0
        prefix = pardir * path_separator
        relpath_ = isempty(pathpart)     ?
            (prefix^prefix_num) * pardir :
            (prefix^prefix_num) * pardir * path_separator * pathpart
    else
        relpath_ = pathpart
    end
    return isempty(relpath_) ? curdir :  relpath_
end
```
-/
def relpath (os : Platform) (ops : StringOps) (pwd : Unit → Path)
    (path : Path) (startpath : Path := ops.fromBytes [dot]) : Except PathError Path := do
  if path.bytes.isEmpty then throw (.argumentError "`path` must be non-empty")
  if startpath.bytes.isEmpty then throw (.argumentError "`startpath` must be non-empty")
  if path.bytes == startpath.bytes then return ops.fromBytes [dot]
  let pathArrays ← if os == .windows then do
    let (pathDrive, pathWithoutDrive) := splitdrive .windows ops path
    let (originalStartDrive, startWithoutDrive) := splitdrive .windows ops startpath
    let startDrive := if originalStartDrive.bytes.isEmpty then pathDrive else originalStartDrive
    if (ops.uppercase pathDrive).bytes != (ops.uppercase startDrive).bytes then
      pure none
    else
      let drivePath := appendPath ops pathDrive pathWithoutDrive
      let driveStart := appendPath ops pathDrive startWithoutDrive
      let absolutePath ← abspath .windows ops pwd drivePath
      let absoluteStart ← abspath .windows ops pwd driveStart
      pure (some (splitPathArrays .windows ops absolutePath absoluteStart))
  else do
    let absolutePath ← abspath .unix ops pwd path
    let absoluteStart ← abspath .unix ops pwd startpath
    pure (some (splitPathArrays .unix ops absolutePath absoluteStart))
  match pathArrays with
  | none => return (← abspath .windows ops pwd path)
  | some (pathArr, startArr) =>
      let pathBytesList := pathArr.map (·.bytes)
      let startBytesList := startArr.map (·.bytes)
      let i := commonLen pathBytesList startBytesList
      let pathBytes := pathBytesList.drop i |>.take (lastNonempty pathBytesList - i)
      let pathpart := joinSep os pathBytes
      let prefixNum : Int := (lastNonempty startBytesList : Int) - i - 1
      let rel := if prefixNum ≥ 0 then
          let parents := dotdot ++ [separator os]
          if pathpart.isEmpty then repeatBytes parents prefixNum.toNat ++ dotdot
          else repeatBytes parents prefixNum.toNat ++ dotdot ++ (separator os :: pathpart)
        else pathpart
      return ops.fromBytes (if rel.isEmpty then [dot] else rel)

/--
Julia source: base/path.jl:627-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    abspath(path::AbstractString, paths::AbstractString...)::String

Convert a set of paths to an absolute path by joining them together and adding the
current directory if necessary. Equivalent to `abspath(joinpath(path, paths...))`.
"""
abspath(a::AbstractString, b::AbstractString...) = abspath(joinpath(a,b...))
```
-/
def abspathMany (os : Platform) (ops : StringOps) (pwd : Unit → Path)
    (first : Path) (rest : List Path) : Except PathError Path := do
  let joined ← joinpathStrings os ops (first :: rest)
  abspath os ops pwd joined

/--
Julia source: base/path.jl:885-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    expanduser(path::AbstractString)::AbstractString

Replace a tilde character at the start of a path with the current user's home directory.
On Unix, `~username` at the start of a path is replaced with that user's home directory;
if the user does not exist the path is returned unchanged. On Windows, only `~` expansion
is supported (not `~username`).

See also: [`contractuser`](@ref).
"""
expanduser(path::AbstractString) = expanduser(String(path)::String)
```
-/
def expanduserAbstract {S : Type} (toString : S → Path) (os : Platform) (ops : StringOps)
    (fs : FileSystemOps) (path : S) : Except PathError Path :=
  expanduser os ops fs (toString path)

/--
Julia source: base/path.jl:958-959 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
relpath(path::AbstractString, startpath::AbstractString) =
    relpath(String(path)::String, String(startpath)::String)
```
-/
def relpathAbstract {S : Type} (toString : S → Path) (os : Platform) (ops : StringOps)
    (pwd : Unit → Path) (path startpath : S) : Except PathError Path :=
  relpath os ops pwd (toString path) (toString startpath)

/--
Julia source: base/path.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
splitpath(p::AbstractString) = splitpath(String(p)::String)
```
-/
def splitpathAbstract {S : Type} (toString : S → Path) (os : Platform) (ops : StringOps)
    (path : S) : List Path :=
  splitpath os ops (toString path)

/--
Julia source: base/path.jl:961-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:isdirpath, :splitdir, :splitdrive, :splitext, :normpath, :abspath, :isabspath)
    @eval $f(path::AbstractString) = $f(String(path)::String)
end
```
-/
def abstractStringWrapper {S α : Type} (toString : S → Path) (f : Path → α) (value : S) : α :=
  f (toString value)


def separatorIndices (os : Platform) : Bytes → List Nat
  | [] => []
  | b :: rest => if isSep os b then 0 :: (separatorIndices os rest).map (· + 1)
      else (separatorIndices os rest).map (· + 1)

def contractuserPairs (os : Platform) (bs : Bytes) : List (Bytes × Bytes) :=
  match separatorIndices os bs with
  | [] => []
  | _ :: later => later.map (fun i => (bs.take i, bs.drop i))



def contractuserLoop (os : Platform) (ops : StringOps) (fs : FileSystemOps)
    (path home : Path) : List (Bytes × Bytes) → Nat → Option Path → Option Path → Path
  | [], _, _, _ => path
  | (prefixBytes, rest) :: later, cacheUid, cacheUser, cacheHome =>
      let prefixPath := ops.fromBytes prefixBytes
      if !fs.ispath prefixPath then path
      else if fs.samefile prefixPath home then ops.fromBytes (tilde :: rest)
      else if os == .windows then contractuserLoop os ops fs path home later cacheUid cacheUser cacheHome
      else
        let uid := (fs.statUid prefixPath).getD cacheUid
        let (nextUid, nextUser, nextHome) :=
          if uid != cacheUid then
            match fs.username uid with
            | none => (uid, none, none)
            | some username => (uid, some username, (fs.homedirUser username).filter fs.ispath)
          else (cacheUid, cacheUser, cacheHome)
        match nextUser, nextHome with
        | some username, some userhome =>
            if fs.ispath userhome && fs.samefile prefixPath userhome then
              ops.fromBytes (tilde :: username.bytes ++ rest)
            else contractuserLoop os ops fs path home later nextUid nextUser nextHome
        | _, _ => contractuserLoop os ops fs path home later nextUid nextUser nextHome

/--
Julia source: base/path.jl:756-777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function contractuser(path::Union{String, SubString{String}})::String
    # Walk prefixes of path, checking if any matches homedir() via inode.
    # Only checks the current user's home (no ~username on Windows).
    # Preserves the original path string after the matched prefix verbatim.
    home_st = stat(homedir())
    ispath(home_st) || return path
    # check the full path (home directory itself, no trailing separator)
    samefile(stat(path), home_st) && return "~"
    # scan for separators; start after the first one to skip the root
    m = findnext(path_separator_re, path, firstindex(path))
    m === nothing && return path
    while true
        m = findnext(path_separator_re, path, nextind(path, last(m)))
        m === nothing && return path
        prefix = SubString(path, 1, prevind(path, first(m)))
        st = stat(prefix)
        ispath(st) || return path
        if samefile(st, home_st)
            return "~" * SubString(path, first(m))
        end
    end
end
```

Julia source: base/path.jl:809-850 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function contractuser(path::Union{String, SubString{String}})::String
    # Walk path prefixes from shortest to longest. At each existing prefix,
    # check against the current user's home first, then the directory owner's
    # home via inode comparison. This handles symlinks transparently.
    # Preserves the original path string after the matched prefix verbatim.
    home_st = stat(homedir())
    ispath(home_st) || return path
    cache_uid = ccall(:getuid, Cuint, ())
    cache_uname = nothing
    cache_home_st = nothing
    # Check the full path (home directory itself, no trailing separator)
    samefile(stat(path), home_st) && return "~"
    # Scan for separators; start after the first one to skip the root
    m = findnext(path_separator_re, path, firstindex(path))
    m === nothing && return path
    while true
        m = findnext(path_separator_re, path, nextind(path, last(m)))
        m === nothing && return path
        prefix = SubString(path, 1, prevind(path, first(m)))
        st = stat(prefix)
        ispath(st) || return path
        rest = SubString(path, first(m))
        if samefile(st, home_st)
            return "~" * rest
        end
        uid = st.uid
        if uid != cache_uid
            cache_uid = uid
            pd = Libc.getpwuid(uid, false)
            cache_uname = pd !== nothing && !isempty(pd.username) ? pd.username : nothing
            if cache_uname !== nothing
                pw_home = homedir(cache_uname)
                cache_home_st = pw_home !== nothing ? stat(pw_home) : nothing
            else
                cache_home_st = nothing
            end
        end
        if cache_home_st !== nothing && ispath(cache_home_st) && samefile(st, cache_home_st)
            return "~$(cache_uname)" * rest
        end
    end
end
```

Julia source: base/path.jl:898-908 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    contractuser(path::AbstractString)::AbstractString

Replace a home directory prefix in `path` with a tilde. If the path starts with the
current user's home directory it is replaced with `~`. On Unix, if it starts with
another user's home directory it is replaced with `~username`. The path is returned
unchanged if no home directory prefix is found.

See also: [`expanduser`](@ref).
"""
contractuser(path::AbstractString) = contractuser(String(path))
```
-/
def contractuser (os : Platform) (ops : StringOps) (fs : FileSystemOps)
    (path : Path) : Except PathError Path := do
  let home ← fs.homedir ()
  if !fs.ispath home then return path
  if fs.samefile path home then return ops.fromBytes [tilde]
  return contractuserLoop os ops fs path home (contractuserPairs os path.bytes)
    fs.currentUid none none

/--
Julia source: base/path.jl:908-908 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
contractuser(path::AbstractString) = contractuser(String(path))
```
-/
def contractuserAbstract {S : Type} (toString : S → Path) (os : Platform)
    (ops : StringOps) (fs : FileSystemOps) (path : S) : Except PathError Path :=
  contractuser os ops fs (toString path)

def hexDigit (n : Nat) : UInt8 := UInt8.ofNat (if n < 10 then 48 + n else 55 + n)

def uriByte (b : UInt8) : Bytes :=
  if (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) ||
      b == 45 || b == 95 || b == 46 || b == 126 || b == 47 then [b]
  else [37, hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def encodeUriBytes (bytes : Bytes) : Bytes := bytes.flatMap uriByte

/--
Julia source: base/path.jl:965-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function encode_uri_component(s::AbstractString)
    out = empty!(StringVector(sizeof(s)))
    for cu in utf8units(s)
        # RFC3986 Section 2.3
        if (UInt8('A') <= cu <= UInt8('Z') ||
            UInt8('a') <= cu <= UInt8('z') ||
            UInt8('0') <= cu <= UInt8('9') ||
            cu in map(UInt8, ('-', '_', '.', '~', '/'))
        )
            push!(out, cu)
        else
            # RFC3986 Section 2.1
            push!(out, UInt8('%'))
            append!(out, codeunits(uppercase(string(cu, base = 16))))
        end
    end
    String(out)
end
```
-/
def encodeUriComponent (ops : StringOps) (value : Path) : Path :=
  ops.fromBytes (encodeUriBytes value.bytes)

def replaceEncodedDrive : Bytes → Bytes
  | 37 :: 51 :: 65 :: rest => colon :: replaceEncodedDrive rest
  | 37 :: 55 :: 67 :: rest => 124 :: replaceEncodedDrive rest
  | b :: rest => b :: replaceEncodedDrive rest
  | [] => []

structure UriOps where
  hostname : Path
  wslDistro : Path

/--
Julia source: base/path.jl:984-1028 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    uripath(path::AbstractString)

Encode `path` as a URI as per [RFC8089: The "file" URI
Scheme](https://www.rfc-editor.org/rfc/rfc8089), [RFC3986: Uniform Resource
Identifier (URI): Generic Syntax](https://www.rfc-editor.org/rfc/rfc3986), and
the [Freedesktop File URI spec](https://www.freedesktop.org/wiki/Specifications/file-uri-spec/).

## Examples

```julia-repl
julia> uripath("/home/user/example file.jl") # On a unix machine
"file://<hostname>/home/user/example%20file.jl"

julia> uripath("C:\\Users\\user\\example file.jl") # On a windows machine
"file:///C:/Users/user/example%20file.jl"
```
"""
function uripath end

@static if Sys.iswindows()
    function uripath(path::String)
        path = abspath(path)
        if startswith(path, "\\\\") # UNC path, RFC8089 Appendix E.3
            unixpath = join(_split_at_separators(path, keepempty=false), '/')
            string("file://", encode_uri_component(unixpath)) # RFC8089 Section 2
        else
            drive, localpath = splitdrive(path) # Assuming that non-UNC absolute paths on Windows always have a drive component
            unixpath = join(_split_at_separators(localpath, keepempty=false), '/')
            encdrive = replace(encode_uri_component(drive), "%3A" => ':', "%7C" => '|') # RFC8089 Appendices D.2, E.2.1, and E.2.2
            string("file:///", encdrive, '/', encode_uri_component(unixpath)) # RFC8089 Section 2
        end
    end
else
    function uripath(path::String)
        localpath = join(_split_at_separators(abspath(path), keepempty=false), '/')
        host = if ispath("/proc/sys/fs/binfmt_misc/WSLInterop") # WSL sigil
            distro = get(ENV, "WSL_DISTRO_NAME", "") # See <https://patrickwu.space/wslconf/>
            "wsl\$/$distro" # See <https://github.com/microsoft/terminal/pull/14993> and <https://learn.microsoft.com/en-us/windows/wsl/filesystems>
        else
            gethostname() # Freedesktop File URI Spec, Hostnames section
        end
        string("file://", encode_uri_component(host), '/', encode_uri_component(localpath)) # RFC8089 Section 2
    end
end
````
-/
def uripath (os : Platform) (ops : StringOps) (fs : FileSystemOps) (pwd : Unit → Path)
    (uriOps : UriOps) (path : Path) : Except PathError Path := do
  let absolute ← abspath os ops pwd path
  if os == .windows then
    let b := absolute.bytes
    if b.length ≥ 2 && b[0]! == backslash && b[1]! == backslash then
      let localBytes := joinSep .unix ((splitRuns .windows b).filter (· ≠ []))
      return ops.fromBytes ([102, 105, 108, 101, 58, 47, 47] ++ encodeUriBytes localBytes)
    let (drive, localPath) := splitdrive .windows ops absolute
    let localBytes := joinSep .unix ((splitRuns .windows localPath.bytes).filter (· ≠ []))
    let encodedDrive := replaceEncodedDrive (encodeUriBytes drive.bytes)
    return ops.fromBytes ([102, 105, 108, 101, 58, 47, 47, 47] ++ encodedDrive ++ [47] ++ encodeUriBytes localBytes)
  let localBytes := joinSep .unix ((splitRuns .unix absolute.bytes).filter (· ≠ []))
  let wslMarker := ops.fromBytes [47, 112, 114, 111, 99, 47, 115, 121, 115, 47, 102, 115, 47, 98, 105, 110, 102, 109, 116, 95, 109, 105, 115, 99, 47, 87, 83, 76, 73, 110, 116, 101, 114, 111, 112]
  let host := if fs.ispath wslMarker then [119, 115, 108, 36, 47] ++ uriOps.wslDistro.bytes else uriOps.hostname.bytes
  return ops.fromBytes ([102, 105, 108, 101, 58, 47, 47] ++ encodeUriBytes host ++ [47] ++ encodeUriBytes localBytes)

/--
Julia source: base/path.jl:1030-1030 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uripath(path::AbstractString) = uripath(String(path)::String)
```
-/
def uripathAbstract {S : Type} (toString : S → Path) (os : Platform) (ops : StringOps)
    (fs : FileSystemOps) (pwd : Unit → Path) (uriOps : UriOps) (path : S) : Except PathError Path :=
  uripath os ops fs pwd uriOps (toString path)


/--
Julia source: base/path.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
splitdrive(path::AbstractString)
```
-/
def splitdriveAbstract {S : Type} (toString : S → Path) (os : Platform) (ops : StringOps)
    (path : S) : Path × Path := splitdrive os ops (toString path)

/--
Julia source: base/path.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_splitdir_nodrive(path::String) = _splitdir_nodrive("", path)
```
-/
def splitdirNoDrivePath (os : Platform) (ops : StringOps) (path : Path) : Path × Path :=
  splitdirNoDrive os ops (emptyPath ops) path

/--
Julia source: base/path.jl:308-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dirname(path::AbstractString) = splitdir(path)[1]
```
-/
def dirnameAbstract {S : Type} (toString : S → Path) (os : Platform) (ops : StringOps)
    (path : S) : Path := dirname os ops (toString path)

/--
Julia source: base/path.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
basename(path::AbstractString) = splitdir(path)[2]
```
-/
def basenameAbstract {S : Type} (toString : S → Path) (os : Platform) (ops : StringOps)
    (path : S) : Path := basename os ops (toString path)

/--
Julia source: base/path.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
joinpath(paths::AbstractString...)::String = joinpath(paths)
```
-/
def joinpathVarargs (os : Platform) (ops : StringOps) (paths : List Path) : Except PathError Path :=
  joinpathStrings os ops paths

/--
Julia source: base/path.jl:683-707 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function homedir(username::AbstractString)
    # For the current user, just return homedir().
    current_user = try
        Sys.username()
    catch err
        err isa IOError || rethrow()
        nothing
    end
    if username == current_user
        return homedir()
    end
    # Look up the user's SID, then query the registry for their profile path.
    # This is the same approach Go uses (os/user.Lookup on Windows).
    home = _win_profile_from_registry(username)
    home !== nothing && return home
    # Fallback: assume profiles are siblings in the same parent directory,
    # but only if the current user's home follows the <parent>/<username>
    # convention. If not, we can't guess reliably.
    userhome = homedir()
    if current_user !== nothing && basename(userhome) == current_user
        home = joinpath(dirname(userhome), username)
        isdir(home) && return home
    end
    return nothing
end
```

Julia source: base/path.jl:781-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function homedir(username::AbstractString)
    # Thread-safe user lookup via getpwnam_r.
    # pwd_storage holds the struct passwd; 256 bytes is a generous upper bound
    # for all supported platforms (Linux x86-64: ~56 bytes, macOS arm64: ~80 bytes).
    pwd_storage = zeros(UInt8, 256)
    # The string buffer holds the pointed-to strings (pw_name, pw_dir, etc.).
    # Start at 1024 and double on ERANGE if any string is unusually long.
    buflen = 1024
    while buflen <= 65536
        str_buf = Vector{UInt8}(undef, buflen)
        result = Ref{Ptr{Cvoid}}(C_NULL)
        ret = ccall(:getpwnam_r, Cint,
                    (Cstring, Ptr{Cvoid}, Ptr{UInt8}, Csize_t, Ptr{Ptr{Cvoid}}),
                    username, pwd_storage, str_buf, Csize_t(buflen), result)
        if ret == 34  # ERANGE: string buffer too small, retry with more space
            buflen *= 2
        elseif ret == 0 && result[] != C_NULL
            # pw_uid sits at offset 2*sizeof(Ptr) in struct passwd on all supported
            # platforms (after pw_name and pw_passwd, which are both pointer-sized)
            uid = unsafe_load(Ptr{Cuint}(pointer(pwd_storage) + 2 * sizeof(Ptr{Cvoid})))
            pd = Libc.getpwuid(uid, false)
            return pd !== nothing ? pd.homedir : nothing
        else
            return nothing  # user not found or error
        end
    end
    return nothing
end
```
-/
def homedirUsernameAbstract {S : Type} (toString : S → Path) (os : Platform)
    (ops : StringOps) (fs : FileSystemOps) (username : S) : Except PathError (Option Path) :=
  homedirUsername os ops fs (toString username)

/--
Julia source: base/path.jl:663-679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function realpath(path::AbstractString)
    req = Libc.malloc(_sizeof_uv_fs)
    try
        ret = ccall(:uv_fs_realpath, Cint,
                    (Ptr{Cvoid}, Ptr{Cvoid}, Cstring, Ptr{Cvoid}),
                    C_NULL, req, path, C_NULL)
        if ret < 0
            uv_fs_req_cleanup(req)
            uv_error("realpath($(repr(path)))", ret)
        end
        path = unsafe_string(ccall(:jl_uv_fs_t_ptr, Cstring, (Ptr{Cvoid},), req))
        uv_fs_req_cleanup(req)
        return path
    finally
        Libc.free(req)
    end
end
```
-/
def realpathAbstract {S : Type} (toString : S → Path) (fs : FileSystemOps)
    (path : S) : Except PathError Path := realpath fs (toString path)

/--
Julia source: base/path.jl:965-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function encode_uri_component(s::AbstractString)
    out = empty!(StringVector(sizeof(s)))
    for cu in utf8units(s)
        # RFC3986 Section 2.3
        if (UInt8('A') <= cu <= UInt8('Z') ||
            UInt8('a') <= cu <= UInt8('z') ||
            UInt8('0') <= cu <= UInt8('9') ||
            cu in map(UInt8, ('-', '_', '.', '~', '/'))
        )
            push!(out, cu)
        else
            # RFC3986 Section 2.1
            push!(out, UInt8('%'))
            append!(out, codeunits(uppercase(string(cu, base = 16))))
        end
    end
    String(out)
end
```
-/
def encodeUriComponentAbstract {S : Type} (toString : S → Path) (ops : StringOps)
    (value : S) : Path := encodeUriComponent ops (toString value)

/--
Julia source: base/path.jl:637-649 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function longpath(path::AbstractString)
    p = cwstring(abspath(path)) # GetLongPathNameW fails on missing directories, even if a later `..` cancels them
    buf = zeros(UInt16, length(p))
    while true
        n = ccall((:GetLongPathNameW, "kernel32"), stdcall,
            UInt32, (Ptr{UInt16}, Ptr{UInt16}, UInt32),
            p, buf, length(buf))
        windowserror(:longpath, n == 0, extrainfo=path)
        x = n < length(buf) # is the buffer big enough?
        resize!(buf, n) # shrink if x, grow if !x
        x && return transcode(String, buf)
    end
end
```
-/
def longpathLoop : List LongPathReply → Nat → Except PathError Path
  | [], _ => .error (.ioError "GetLongPathNameW returned no result")
  | .failure error :: _, _ => .error error
  | .result length path :: replies, bufferLength =>
      if length < bufferLength then .ok path else longpathLoop replies length

def longpath (ops : StringOps) (fs : FileSystemOps) (pwd : Unit → Path)
    (path : Path) : Except PathError Path := do
  let absolute ← abspath .windows ops pwd path
  longpathLoop (fs.longPathReplies absolute) (fs.wideLength absolute)

end JuliaLean.base.path
