import JuliaLean.Core
import JuliaLean.Strings.Char
import JuliaLean.ParsePrint.IntParse

/-!
# Strings and characters for `base/shell.jl` and `base/cmd.jl`

Master `bbfa0ce4150`.

* A `Char` is its raw `UInt32` bit pattern, as in `JuliaLean.Strings`
  (`'a'` is `0x61000000`, `'é'` is `0xc3a90000`, the invalid byte `'\xff'` is
  `0xff000000`).
* A Julia string is modelled by the sequence of `Char`s that iterating it
  yields (`JS`). Every function modelled here iterates its input character by
  character and builds its output by concatenating input characters and ASCII
  characters. For a string produced by Julia, the concatenation of the bytes of
  its characters is the string, and inserting ASCII bytes between characters
  never changes how the neighbouring bytes decode (an ASCII byte is neither a
  lead nor a continuation byte). So iterating Julia's output yields exactly the
  modelled character list, including for invalid UTF-8.
* Byte indices are needed where Julia does index arithmetic. `pairsFrom` gives
  each character its byte index (`pairs(s)`), using `ncodeunits(c::Char)` from
  `JuliaLean.Strings.ncodeunitsChar`. Indices stay below `ncodeunits(s) + 2 < 2^62`,
  so `Int` arithmetic on them is `Int64` arithmetic.
-/

namespace JuliaLean.ShellCmd

open JuliaLean

/-- Exceptions thrown by the modelled functions. `error` is the
`ErrorException` thrown by `error(msg)`; `typeError` is the `TypeError` of a
failed `x::T` assertion; `fuel` marks a loop bound that is never reached. -/
inductive ShErr where
  | jl (e : JlError)
  | error (msg : String)
  | stringIndex
  | typeError
  | outOfMemory
  | fuel
  deriving Repr, DecidableEq, Inhabited

abbrev SH (α : Type) := Except ShErr α

deriving instance DecidableEq for Except

/-- A Julia `Char`: its raw bits. -/
abbrev JC := UInt32
/-- A Julia string: the characters iteration yields. -/
abbrev JS := List UInt32

/-- The `Char` literal of an ASCII character: its code in the top byte. -/
def A (c : Char) : JC := c.toNat.toUInt32 <<< 24

/-- An ASCII string literal. -/
def S (s : String) : JS := s.toList.map A

/-- `isspace(c::Char)`, `base/strings/unicode.jl:624-626`, on the raw bits. -/
def isspace (c : JC) : Bool := ParsePrint.IntParse.isspaceChar c.toNat

/-- `ncodeunits(c::Char)`, `base/char.jl:71-78`. -/
def ncuC (c : JC) : Nat := Strings.ncodeunitsChar c

/-- `ncodeunits(s)`: the byte length. -/
def ncu (s : JS) : Nat := (s.map ncuC).sum

/-- `pairs(s)` of a string whose first character is at byte index `p`:
each character with its byte index. -/
def pairsFrom : Nat → JS → List (Nat × JC)
  | _, [] => []
  | p, c :: cs => (p, c) :: pairsFrom (p + ncuC c) cs

/-- `isvalid(s, i)`: `i` is the index of a character of `s`. -/
def isStart (s : JS) (i : Int) : Bool := (pairsFrom 1 s).any (fun q => (q.1 : Int) == i)

/-- `lastindex(s)`: the index of the last character, `0` for `""`. -/
def lastindex (s : JS) : Int := ((pairsFrom 1 s).getLast?.map (fun q => (q.1 : Int))).getD 0

/-- `SubString(s, i, k)` and `s[i:k]` (`base/strings/substring.jl:76-84,114-117,322`):
empty if `k < i`; otherwise a `BoundsError` unless `1 ≤ i` and `k ≤ ncodeunits(s)`,
and a `StringIndexError` unless `i` and `k` are character indices. -/
def slice (s : JS) (i k : Int) : SH JS :=
  if k < i then .ok []
  else if i < 1 ∨ k > ncu s then .error (.jl .boundsError)
  else if !isStart s i then .error .stringIndex
  else if !isStart s k then .error .stringIndex
  else .ok (((pairsFrom 1 s).filter (fun q => i ≤ (q.1 : Int) ∧ (q.1 : Int) ≤ k)).map (·.2))

/-- `prevind(s, j)` for `1 ≤ j ≤ ncodeunits(s) + 1` (`base/strings/basic.jl:540-548`):
the largest character index below `j`, or `0`. -/
def prevind (s : JS) (j : Int) : Int :=
  ((pairsFrom 1 s).filter (fun q => (q.1 : Int) < j)).foldl (fun _ q => (q.1 : Int)) 0

/-- The bytes of a string: the bytes of its characters. -/
def bytesOf (s : JS) : List UInt8 := s.flatMap Strings.charBytes

/-- `nextind(str::String, i)` (`base/strings/string.jl:273-306`) on the bytes of
`str`, via `JuliaLean.Strings.nextind`. -/
def nextindStr (str : JS) (i : Int) : SH Int :=
  match Strings.stringOfChars str with
  | .error _ => .error .outOfMemory
  | .ok js =>
    match Strings.nextind js (Strings.ix i) with
    | .ok r => .ok r.val
    | .error (.jl e) => .error (.jl e)
    | .error _ => .error .stringIndex

/-- `c ∈ s` for a character and a string. -/
def cin (c : JC) (s : JS) : Bool := s.contains c

end JuliaLean.ShellCmd
