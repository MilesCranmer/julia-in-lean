import JuliaLean.Paths.Model

/-!
# Properties of POSIX path functions
-/

namespace JuliaLean.Paths

open JuliaLean

/-- No two consecutive separators. -/
def noDoubleSep : Str → Bool
  | a :: b :: r => !(isSep a && isSep b) && noDoubleSep (b :: r)
  | _ => true

/-- No `//` and no trailing `/` except for the root `/`. -/
def Canonical (p : Str) : Prop := noDoubleSep p = true ∧ (p = ['/'] ∨ p.getLast? ≠ some '/')

/-- A list of path components: a first component that is `/` or a nonempty
name without separators, then nonempty names without separators. -/
def ComponentList : List Str → Prop
  | [] => False
  | h :: t => (h = ['/'] ∨ (h ≠ [] ∧ h.all (fun c => !isSep c))) ∧ ∀ x ∈ t, x ≠ [] ∧ x.all (fun c => !isSep c)

/-- Lexical resolution of a path from the directory stack `base` (innermost
last): an absolute path starts at the root `[]`; empty and `.` components are
skipped, `..` leaves a directory (the root is its own parent), any other
component enters it. This is what `.`/`..` mean when no symbolic links are
involved. -/
def resolveStep (st : List Str) (c : Str) : List Str :=
  if c = [] ∨ c = ['.'] then st
  else if c = dotdot then st.dropLast
  else st ++ [c]

def resolve (base : List Str) (p : Str) : List Str :=
  (splitRuns p).foldl resolveStep (if isabspath p then [] else base)

/-- `dirname(p)` and `basename(p)` are the two parts of `splitdir(p)`
(`base/path.jl:294-330`): the base name has no separator and ends `p`. -/
def DirnameBasename : Prop :=
  ∀ p, splitdir p = (dirname p, basename p) ∧ (basename p).all (fun c => !isSep c) = true ∧
    ∃ q, p = q ++ basename p

/-- `joinpath(dirname(p), basename(p)) == p` when `p` has no `//`. -/
def JoinSplitdir : Prop :=
  ∀ p, noDoubleSep p = true → joinpath [dirname p, basename p] = .ok p

/-- `splitpath` is "the opposite of `joinpath`" (`base/path.jl:376-377`):
joining the components of a canonical path gives it back, and splitting the
join of a component list gives the list back. -/
def SplitpathJoinpath : Prop :=
  (∀ p, Canonical p → joinpath (splitpath p) = .ok p) ∧
  (∀ parts, ComponentList parts → ∃ q, joinpath parts = .ok q ∧ splitpath q = parts)

/-- `splitext(p)` splits `p` into two parts that concatenate to `p`; the
extension is empty or a dot followed by neither dots nor separators. -/
def SplitextConcat : Prop :=
  ∀ p, (splitext p).1 ++ (splitext p).2 = p ∧
    ((splitext p).2 = [] ∨ ∃ e, (splitext p).2 = '.' :: e ∧ e.all (fun c => c != '/' && c != '.') = true)

/-- `splitext` docstring (`base/path.jl:335-337`): if the last component contains
a dot, the result is everything before the last dot and everything from it on. -/
def SplitextDoc : Prop :=
  ∀ q r : Str, r.all (fun c => c != '/' && c != '.') = true → splitext (q ++ '.' :: r) = (q, '.' :: r)

/-- `normpath(normpath(p)) == normpath(p)`. -/
def NormpathIdempotent : Prop := ∀ p, normpath (normpath p) = normpath p

/-- `normpath` of an absolute path is absolute, has no `//`, and none of its
components is `.` or `..`; a relative result has `..` components only at its
start and is `.` or has no `.` component. -/
def NormpathCanonical : Prop :=
  ∀ p, noDoubleSep (normpath p) = true ∧
    (isabspath p → isabspath (normpath p) = true ∧ ∀ c ∈ splitRuns (normpath p), c ≠ ['.'] ∧ c ≠ dotdot) ∧
    (isabspath p = false → isabspath (normpath p) = false ∧
      (normpath p = ['.'] ∨ ∀ c ∈ splitRuns (normpath p), c ≠ ['.']) ∧
      ∃ k rest, splitRuns (normpath p) = List.replicate k dotdot ++ rest ∧ ∀ c ∈ rest, c ≠ dotdot)

/-- `normpath` removes `.` and `..` without changing where the path leads
(`base/path.jl:543`), from every starting directory. -/
def NormpathLexical : Prop := ∀ base p, resolve base (normpath p) = resolve base p

/-- `normpath` keeps whether the path denotes a directory. -/
def NormpathIsdirpath : Prop := ∀ p, isdirpath (normpath p) = isdirpath p

/-- With an absolute `pwd()`, `relpath(path, startpath)` is a relative path that
leads from `startpath` to `path` (`base/path.jl:914-916`). -/
def RelpathRoundtrip : Prop :=
  ∀ cwd p s r, isabspath cwd = true → relpath cwd p s = .ok r →
    isabspath r = false ∧ resolve (resolve [] (abspath cwd s)) r = resolve [] (abspath cwd p)

/-- `joinpath` drops the components before an absolute one (`base/path.jl:494-496`)
and is associative. -/
def JoinpathLaws : Prop :=
  (∀ a b, isabspath b = true → joinpath [a, b] = .ok b) ∧
  (∀ a b c, joinpath [a, b, c] = joinpath [joinStep a b, c] ∧
    joinpath [joinStep a b, c] = joinpath [a, joinStep b c])

/-- `expanduser` replaces a leading `~` (followed by `/` or nothing) with
`homedir()` and leaves every other path without a leading `~` unchanged, as
well as `~user` paths of unknown users (`base/path.jl:887-893`). -/
def ExpanduserDoc : Prop :=
  ∀ home lookup userChar p,
    ((p = [] ∨ p.head? = some '/') → expanduser home lookup userChar ('~' :: p) = home ++ p) ∧
    (p.head? ≠ some '~' → expanduser home lookup userChar p = p) ∧
    (∀ user rest, user ≠ [] → user.all (fun c => !isSep c) = true → (rest = [] ∨ rest.head? = some '/') →
      lookup user = none → expanduser home lookup userChar ('~' :: user ++ rest) = '~' :: user ++ rest)

/-- With an absolute `pwd()`, `abspath` returns an absolute path and is idempotent. -/
def AbspathLaws : Prop :=
  ∀ cwd p, isabspath cwd = true →
    isabspath (abspath cwd p) = true ∧ abspath cwd (abspath cwd p) = abspath cwd p

/-- `isdirpath` docstring (`base/path.jl:244`): a path ending with a separator is a directory path. -/
def IsdirpathTrailing : Prop := ∀ p, isdirpath (p ++ ['/']) = true

end JuliaLean.Paths
