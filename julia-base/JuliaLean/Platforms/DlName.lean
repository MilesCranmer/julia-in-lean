import JuliaLean.Platforms.Basic

/-!
# `parse_dl_name_version` (`base/binaryplatforms.jl:868-929`)

The three patterns carry the `a` flag (byte mode: no UTF, no UCP), so `\d`,
`\w` and `[A-Za-z]` are ASCII classes, `.` with `s` matches any byte, and `i`
(Windows) makes letters caseless. Every literal and class in the patterns is
ASCII, so a match can only start or end a capture next to an ASCII byte: on
valid UTF-8 the byte-mode match is the character-level match the model
computes, with a non-ASCII character matching no class.

Each pattern is `^(.*?)REST`. The lazy `(.*?)` tries 0, 1, 2, ... characters,
and for each length the rest is matched with PCRE's backtracking order, so the
match is the first split point at which `REST` matches the remaining suffix.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (Re matchRe capture VersionNumber)
open JuliaLean.VersionNumbers.Re

def isAsciiDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isAsciiAlpha (c : Char) : Bool := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')
/-- `\w` in byte mode. -/
def isWord (c : Char) : Bool := isAsciiDigit c || isAsciiAlpha c || c == '_'

/-- A literal string. -/
def litD (s : Str) : Re := seqs (s.map chr)

/-- A caseless literal (`i` flag). -/
def litCI (s : Str) : Re := seqs (s.map fun c => cls fun d => asciiLower d == asciiLower c)

/-- Group numbers: 2 the version, 3 the trailing tag. -/
def verGroup : Nat := 2

/-- `\.so(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?$`, the part of the Linux/BSD
pattern after `^(.*?)`, `base/binaryplatforms.jl:907`. -/
def soRest : Re :=
  seqs [litD (s% ".so"),
    opt (seq (group verGroup (plus (seq (chr '.') (plus (cls isAsciiDigit)))))
      (opt (group 3 (seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '-')))))),
    eol]

/-- `(?:((?:\.[\d]+)+)([A-Za-z][\w\-]*)?)?\.dylib$`, `base/binaryplatforms.jl:904`. -/
def dylibRest : Re :=
  seqs [opt (seq (group verGroup (plus (seq (chr '.') (plus (cls isAsciiDigit)))))
      (opt (group 3 (seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '-')))))),
    litD (s% ".dylib"), eol]

/-- `(?:-(?:((?:[\.\d]+)+)([A-Za-z][\w\.]*)?)?)?\.dll$` with `i`,
`base/binaryplatforms.jl:901`. -/
def dllRest : Re :=
  seqs [opt (seq (chr '-') (opt (seq (group verGroup (plus (plus (cls fun c => c == '.' || isAsciiDigit c))))
      (opt (group 3 (seq (cls isAsciiAlpha) (star (cls fun c => isWord c || c == '.')))))))),
    litCI (s% ".dll"), eol]

/-- The pattern for `os`, `base/binaryplatforms.jl:896-908`. -/
def dlRest (os : Str) : Re :=
  if os == s% "windows" then dllRest else if os == s% "macos" then dylibRest else soRest

/-- `match(r"^(.*?)REST", s)`: the first split point at which `rest` matches,
with the captured prefix and the captures of `rest`. -/
def lazyMatch (rest : Re) (s : Str) : Option (Str × VersionNumbers.Caps) :=
  go [] s
where
  go (pre : Str) : Str → Option (Str × VersionNumbers.Caps)
    | [] => (matchRe rest []).map (pre, ·)
    | c :: t =>
      match matchRe rest (c :: t) with
      | some m => some (pre, m)
      | none => go (pre ++ [c]) t

/-- `basename(path)` on Unix: the part after the last `/`, `base/path.jl:280-330`. -/
def basename (path : Str) : Str := (path.reverse.takeWhile (· != '/')).reverse

/-- `strip(s, c)`. -/
def stripChar (c : Char) (s : Str) : Str := ((s.dropWhile (· == c)).reverse.dropWhile (· == c)).reverse

/-- `parse_dl_name_version(path::String, os::String)`, `base/binaryplatforms.jl:893-924`. -/
def parseDlNameVersion (path os : Str) : Jl (Str × Option VersionNumber) := do
  match lazyMatch (dlRest os) (basename path) with
  | none => throw (.argumentError "Invalid dynamic library path")
  | some (name, m) =>
    match capture m verGroup with
    | none => return (name, none)
    | some [] => return (name, none)
    | some v => return (name, some (← VersionNumbers.parse (stripChar '.' v)))

end JuliaLean.Platforms
