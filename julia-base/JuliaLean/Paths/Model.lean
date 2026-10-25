import JuliaLean.Core

/-!
# POSIX paths (`base/path.jl`, master `bbfa0ce4150`)

The Unix branch of `base/path.jl`: the separator is `'/'`, `splitdrive(p)` is
`("", p)` (`base/path.jl:30`), so every drive is empty. A `String` is a list
of characters (valid UTF-8); index arithmetic of the Julia code becomes list
splitting at the same characters. `pwd()`, `homedir()` and `homedir(user)` are
parameters.

Loops are structural recursion on the list, or on a bound on the remaining
iterations that each docstring states.
-/

namespace JuliaLean.Paths

open JuliaLean

deriving instance DecidableEq for Except

abbrev Str := List Char

/-- `isseparator(c::Char) = c === '/'`, `base/path.jl:27`. -/
def isSep (c : Char) : Bool := c == '/'

/-- `isabspath(path::String)`, `base/path.jl:200-223` (Unix branch). -/
def isabspath : Str → Bool
  | [] => false
  | c :: _ => isSep c

/-- `findlast(pred, s)` as a split: `some (before, after)` with
`s = before ++ x :: after`, `pred x`, and no character of `after` satisfying `pred`. -/
def splitLast (pred : Char → Bool) (s : Str) : Option (Str × Str) :=
  match s.reverse.span (fun c => !pred c) with
  | (ra, _ :: rb) => some (rb.reverse, ra.reverse)
  | (_, []) => none

/-- `path[1:something(findprev(!isseparator, path, lastsepind), 1)]` given
`path = before ++ "/" ++ tail`: `before` without its trailing separators, or the
first character of `path` if nothing else remains. -/
def dirPart (path before : Str) : Str :=
  let d := (before.reverse.dropWhile isSep).reverse
  if d.isEmpty then path.take 1 else d

/-- `_splitdir_nodrive(drive, path)`, `base/path.jl:280-289`. -/
def splitdirNoDrive (drive path : Str) : Str × Str :=
  match splitLast isSep path with
  | none => (drive, path)
  | some (before, tail) => (drive ++ dirPart path before, tail)

/-- `splitdir(path)`, `base/path.jl:273-276`. -/
def splitdir (path : Str) : Str × Str := splitdirNoDrive [] path

/-- `dirname`, `base/path.jl:308`. -/
def dirname (path : Str) : Str := (splitdir path).1

/-- `basename`, `base/path.jl:330`. -/
def basename (path : Str) : Str := (splitdir path).2

/-- `isdirpath(path::String)`, `base/path.jl:255-260`. -/
def isdirpath (path : Str) : Bool :=
  let a := (splitdirNoDrive [] path).2
  a == [] || a == ['.'] || a == ['.', '.']

/-- `splitext(path::String)`, `base/path.jl:351-368`. `p = before ++ "." ++ after`
splits at the last dot; `findnext(isseparator, p, lastdot)` looks at `after`
(the dot itself is no separator) and `p[prev]` is the last character of `before`. -/
def splitext (path : Str) : Str × Str :=
  match splitLast (· == '.') path with
  | some (before, after) =>
    if after.any isSep then (path, [])
    else match before.getLast? with
      | some c => if !isSep c then (before, '.' :: after) else (path, [])
      | none => (path, [])
  | none => (path, [])

/-- The `while !isempty(p)` loop of `splitpath`, `base/path.jl:399-406`, with
`n` iterations left. Each iteration that does not stop shortens `p`, so
`n = length(p) + 1` never runs out. -/
def splitpathLoop : Nat → Str → List Str → List Str
  | 0, _, out => out
  | n + 1, p, out =>
    if p.isEmpty then out
    else
      let (dir, base) := splitdirNoDrive [] p
      if dir == p then dir :: out
      else splitpathLoop n dir (if base.isEmpty then out else base :: out)

/-- `splitpath(p::String)`, `base/path.jl:395-411`. -/
def splitpath (p : Str) : List Str :=
  splitpathLoop (p.length + 1) p (if p.isEmpty then [p] else [])

/-- One step of the Unix `joinpath` loop, `base/path.jl:472-480`. -/
def joinStep (path p : Str) : Str :=
  if isabspath p then p
  else if path.isEmpty || path.getLast? == some '/' then path ++ p
  else path ++ '/' :: p

/-- `joinpath(paths)` on Unix, `base/path.jl:465-483`. -/
def joinpath : List Str → Jl Str
  | [] => .error (.argumentError "collection of path components must be non-empty")
  | p0 :: ps => .ok (ps.foldl joinStep p0)

/-- `_split_at_separators(path; keepempty = true)`, `base/path.jl:516-538`
(`split(path, r"/+")`): the maximal separator-free pieces between runs of
separators, including the empty pieces before a leading and after a trailing run. -/
def splitRuns : Str → List Str
  | [] => [[]]
  | c :: cs =>
    match splitRuns cs with
    | [] => [[c]]
    | w :: ws =>
      if isSep c then
        (if cs.head?.map isSep == some true then w :: ws else [] :: w :: ws)
      else (c :: w) :: ws

/-- `_split_at_separators(path; keepempty)`. -/
def splitAtSeps (path : Str) (keepempty : Bool) : List Str :=
  if keepempty then splitRuns path else (splitRuns path).filter (· ≠ [])

def dotdot : Str := ['.', '.']

/-- One pass of the `for j = 1:length(parts)-1` loop of `normpath`,
`base/path.jl:563-569`: delete the first pair `x, ".."` with `x != ".."`. -/
def removeFirstPair : List Str → Option (List Str)
  | a :: b :: rest =>
    if a != dotdot && b == dotdot then some rest
    else (removeFirstPair (b :: rest)).map (a :: ·)
  | _ => none

/-- The `while true` loop of `normpath`, `base/path.jl:561-571`, with `n`
passes left; each pass that changes `parts` removes two elements, so
`n = length(parts) + 1` never runs out. -/
def cleanLoop : Nat → List Str → List Str
  | 0, ps => ps
  | n + 1, ps =>
    match removeFirstPair ps with
    | none => ps
    | some ps' => cleanLoop n ps'

/-- `join(parts, "/")`. -/
def joinSep : List Str → Str
  | [] => []
  | [a] => a
  | a :: as => a ++ '/' :: joinSep as

/-- `normpath(path::String)`, `base/path.jl:555-587`. -/
def normpath (path : Str) : Str :=
  let isabs := isabspath path
  let isdir := isdirpath path
  let parts := (splitAtSeps path false).filter (· != ['.'])
  let parts := cleanLoop (parts.length + 1) parts
  let parts :=
    if isabs then parts.dropWhile (· == dotdot)
    else if parts.isEmpty then [['.']] else parts
  let p := joinSep parts
  let p := if isabs then '/' :: p else p
  if isdir && !isdirpath p then p ++ ['/'] else p

/-- `abspath(a::String)` with `pwd() = cwd`, `base/path.jl:613-625` (the drive
of `a` is empty on Unix, so the `else` branch is taken); `joinpath(cwd, a)`
is one `joinStep`. -/
def abspath (cwd a : Str) : Str :=
  let a := if !isabspath a then joinStep cwd a else a
  normpath a

/-- The common-prefix loop of `relpath`, `base/path.jl:938-945`. -/
def commonLen : List Str → List Str → Nat
  | a :: as, b :: bs => if a == b then commonLen as bs + 1 else 0
  | _, _ => 0

/-- `something(findlast(x -> !isempty(x), arr), 0)`. -/
def lastNonempty (arr : List Str) : Nat := go arr 1 0
where
  go : List Str → Nat → Nat → Nat
    | [], _, acc => acc
    | x :: xs, i, acc => go xs (i + 1) (if x.isEmpty then acc else i)

/-- `prefix^n`. -/
def repeatStr (s : Str) : Nat → Str
  | 0 => []
  | n + 1 => s ++ repeatStr s n

/-- `relpath(path::String, startpath::String)` on Unix with `pwd() = cwd`,
`base/path.jl:921-957`. -/
def relpath (cwd path startpath : Str) : Jl Str := do
  if path.isEmpty then throw (.argumentError "`path` must be non-empty")
  if startpath.isEmpty then throw (.argumentError "`startpath` must be non-empty")
  if path == startpath then return ['.']
  let pathArr := splitAtSeps (abspath cwd path) true
  let startArr := splitAtSeps (abspath cwd startpath) true
  let i := commonLen pathArr startArr
  let pathpart := joinSep ((pathArr.drop i).take (lastNonempty pathArr - i))
  let prefixNum : Int := (lastNonempty startArr : Int) - i - 1
  let rel :=
    if prefixNum ≥ 0 then
      let pre := dotdot ++ ['/']
      if pathpart.isEmpty then repeatStr pre prefixNum.toNat ++ dotdot
      else repeatStr pre prefixNum.toNat ++ dotdot ++ '/' :: pathpart
    else pathpart
  return if rel.isEmpty then ['.'] else rel

/-- `expanduser(path::String)` on Unix, `base/path.jl:854-883`, with
`homedir() = home`, `homedir(username) = lookup username`, and `userChar` the
predicate `c -> isletter(c) || isdigit(c) || c in "._-"`. -/
def expanduser (home : Str) (lookup : Str → Option Str) (userChar : Char → Bool) (path : Str) : Str :=
  match path with
  | [] => path
  | c :: rest =>
    if c != '~' then path
    else
      let (username, after) := rest.span (fun x => !isSep x)
      let h :=
        if username.isEmpty then some home
        else if !username.all userChar then none
        else lookup username
      match h with
      | none => path
      | some home => if after.isEmpty then home else home ++ after

end JuliaLean.Paths
