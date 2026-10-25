/-!
# Backtracking regular-expression matcher

The fragment of PCRE2 used by `base/version.jl`, with the matching order of
PCRE2's backtracking engine: alternatives are tried left to right, `*` and `?`
are greedy and give back one iteration at a time, a failed branch restores the
captures it set, and a group's capture is the substring of its latest
completed iteration on the successful path.

Strings are lists of characters (valid UTF-8 `String`s). The patterns are
compiled by Julia with `UTF | UCP` (`base/regex.jl:7`), so character classes
are Unicode-aware; each class is given as a predicate (`Re.cls`).

`$` without the `m` flag matches at the end of the subject or before a newline
that is the last character (PCRE2 `DOLLAR_ENDONLY` is not set).
-/

namespace JuliaLean.VersionNumbers

/-- Captures of a match: group number and captured substring, latest first. -/
abbrev Caps := List (Nat × List Char)

/-- Regular expressions: a character class, the empty pattern, concatenation,
ordered alternation, greedy `*`, a numbered capturing group and `$`. -/
inductive Re where
  | cls (p : Char → Bool)
  | eps
  | seq (a b : Re)
  | alt (a b : Re)
  | star (a : Re)
  | group (i : Nat) (a : Re)
  | eol

namespace Re

/-- Greedy `a?`. -/
def opt (a : Re) : Re := alt a eps

/-- Greedy `a+`. -/
def plus (a : Re) : Re := seq a (star a)

/-- A single literal character. -/
def chr (c : Char) : Re := cls (· == c)

/-- Concatenation of a list of patterns. -/
def seqs : List Re → Re
  | [] => eps
  | [a] => a
  | a :: as => seq a (seqs as)

end Re

/-- Continuation: the rest of the subject and the captures so far. -/
abbrev Kont := List Char → Caps → Option Caps

/-- One level of the matcher. `rec` matches a further iteration of a `*`; an
iteration that consumes nothing ends the loop (PCRE2 breaks a loop on an empty
iteration), so every call of `rec` consumes at least one character. -/
def step (rec : Re → List Char → Caps → Kont → Option Caps) :
    Re → List Char → Caps → Kont → Option Caps
  | .cls p, s, c, k =>
    match s with
    | x :: t => if p x then k t c else none
    | [] => none
  | .eps, s, c, k => k s c
  | .seq a b, s, c, k => step rec a s c (fun s' c' => step rec b s' c' k)
  | .alt a b, s, c, k =>
    match step rec a s c k with
    | some r => some r
    | none => step rec b s c k
  | .star a, s, c, k =>
    match step rec a s c (fun s' c' => if s'.length < s.length then rec (.star a) s' c' k else none) with
    | some r => some r
    | none => k s c
  | .group i a, s, c, k => step rec a s c (fun s' c' => k s' ((i, s.take (s.length - s'.length)) :: c'))
  | .eol, s, c, k => if s = [] ∨ s = ['\n'] then k s c else none

/-- The matcher with `n` levels of loop iteration. Each level consumes a
character, so `n = length + 1` levels never run out on a subject of that length. -/
def matchFuel : Nat → Re → List Char → Caps → Kont → Option Caps
  | 0 => fun _ _ _ _ => none
  | n + 1 => step (matchFuel n)

/-- `match(r, s)` for a pattern starting with `^` (no multiline flag): an
anchored match at the start of `s`; the captures of the first match, or
`none` (`nothing`). -/
def matchRe (r : Re) (s : List Char) : Option Caps :=
  matchFuel (s.length + 1) r s [] (fun _ c => some c)

/-- `occursin(r, s)` for a pattern starting with `^`. -/
def occursRe (r : Re) (s : List Char) : Bool := (matchRe r s).isSome

/-- `m.captures[i]`: the latest capture of group `i`, `nothing` if unset. -/
def capture (c : Caps) (i : Nat) : Option (List Char) :=
  (c.find? (·.1 == i)).map (·.2)

end JuliaLean.VersionNumbers
