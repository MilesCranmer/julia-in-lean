import JuliaLean.base.strings.util
import JuliaLean.Proofs.base.strings.string.indices

/-!
# `replace(s, pat => repl, ...)` with fixed replacement strings

Model of `_replace_init`, `_replace_once`, `_replace_finish` and `_replace_`
(String result), `base/strings/util.jl:1035-1131` (master `bbfa0ce4150`), for
`N` pairs `pat => repl` where `repl` is a String or Char (`_replace(io, repl, ...)
= write(io, repl)`, `:1011-1012`) and each pattern is given by its finder
`k ↦ findnext(p, str, k)`. Regex patterns, function replacements and
`AnnotatedString` are out of scope.

* The output `IOBuffer` is the list of bytes written to it: `_replace_` creates
  it empty, only appends (`write`, `unsafe_write`), and `takestring!` returns
  those bytes.
* `_free_pat_replacer` is `nothing` for non-Regex patterns (`:1029`) and is
  omitted.
* `nrep` is instrumentation: the number of `_replace` calls so far. Julia has
  no such variable; it is recorded so the number of replacements can be stated.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings

/-! ## The reference scan of the docstring -/

/-- The bytes of pattern `t` occur in `s` starting at index `p`. -/
def occursAt (s : JStr) (t : List UInt8) (p : Int) : Bool :=
  t.isPrefixOf (s.bytes.drop (p - 1).toNat)

/-- The docstring's scan (`base/strings/util.jl:1152-1157`): "The input string will
be scanned only once from start (left) to end (right), and the first matching
replacement will be applied to each substring. Replacements are applied in the
order of the arguments provided if they match substrings starting at the same
input string position." At a character index `p` (`isvalid(s, p)`), while
replacements remain (`c > 0`), the first pair `(t, r)` in argument order whose
pattern bytes `t` start at `p` is applied: `r` is output and the scan resumes
after the match. Otherwise the byte at `p` is copied (copying a character byte
by byte). Returns the output and the number of replacements. The first argument
bounds the steps; every step advances `p` when patterns are nonempty, so
`ncodeunits(s) + 1` steps from `p = 1` never truncate the scan. -/
def refScan (s : JStr) (prs : List (List UInt8 × List UInt8)) :
    Nat → Int → Nat → List UInt8 × Nat
  | 0, _, _ => ([], 0)
  | f + 1, p, c =>
    if (s.bytes.length : Int) < p then ([], 0)
    else
      let hit := if 0 < c ∧ validZ s p then prs.find? (fun pr => occursAt s pr.1 p) else none
      match hit with
      | some (t, r) =>
        let rest := refScan s prs f (p + t.length) (c - 1)
        (r ++ rest.1, rest.2 + 1)
      | none =>
        let rest := refScan s prs f (p + 1) c
        (s.bytes.getD (p - 1).toNat 0 :: rest.1, rest.2)

/-- The reference result with at most `c` replacements. -/
def refReplace (s : JStr) (prs : List (List UInt8 × List UInt8)) (c : Nat) : List UInt8 × Nat :=
  refScan s prs (s.bytes.length + 1) 1 c

/-! ## The finder contract -/

/-- `t` occurs at no character index `≥ k`. -/
def NoOcc (s : JStr) (t : List UInt8) (k : Int) : Prop :=
  ∀ p, k ≤ p → validZ s p → occursAt s t p = false

/-- `j` is the first character index `≥ k` where `t` occurs. -/
def Least (s : JStr) (t : List UInt8) (k j : Int) : Prop :=
  k ≤ j ∧ validZ s j ∧ occursAt s t j = true ∧
    ∀ p, k ≤ p → p < j → validZ s p → occursAt s t p = false

/-- The range `j:l` is the first occurrence of `t` at a character index `≥ k`,
and `l` is the index of its last character: `nextind(s, l) == j + ncodeunits(t)`. -/
def MatchOk (s : JStr) (t : List UInt8) (k : Int) (j l : JInt64) : Prop :=
  Least s t k j.val ∧ j.val ≤ l.val ∧ ∃ q, nextind s l = .ok q ∧ q.val = j.val + t.length

/-- What `findnext(p, s, k)` may return for a pattern with bytes `t`. -/
def FoundSpec (s : JStr) (t : List UInt8) (k : Int) : Found → Prop
  | .nothing => NoOcc s t k
  | .idx i => MatchOk s t k i i
  | .range a b => MatchOk s t k a b

/-- The finder contract: for every `1 ≤ k ≤ ncodeunits(s) + 1`, `findnext(p, s, k)`
returns without throwing the first occurrence of `t` at a character index `≥ k`
(as an `Int` or a range ending at the index of its last character), or `nothing`. -/
def FinderSpec (s : JStr) (t : List UInt8) (find : JInt64 → SJl Found) : Prop :=
  ∀ k : JInt64, 1 ≤ k.val → k.val ≤ s.bytes.length + 1 →
    ∃ fr, find k = .ok fr ∧ FoundSpec s t k.val fr

/-- The hypotheses of the properties: nonempty patterns `q.1` whose finders meet
the contract. -/
def Contract (s : JStr) (qs : List (List UInt8 × Pair)) : Prop :=
  ∀ q ∈ qs, q.1 ≠ [] ∧ FinderSpec s q.1 q.2.find

/-! ## Properties -/

/-- `replace(s, pat1 => r1, ..., patN => rN; count)` equals the docstring's scan
with at most `count` replacements, for nonempty patterns whose finders meet the
contract. -/
def ReplaceMatchesReference : Prop :=
  ∀ (s : JStr) (qs : List (List UInt8 × Pair)) (count : JInt64), 0 ≤ count.val →
    Contract s qs →
    replace s (qs.map (·.2)) count =
      .ok (refReplace s (qs.map fun q => (q.1, q.2.repl)) count.val.toNat).1

/-- `count == 0` returns `s`; `count < 0` throws `DomainError`. -/
def ReplaceCountEdge : Prop :=
  ∀ (s : JStr) (ps : List Pair) (count : JInt64),
    (count.val = 0 → replace s ps count = .ok s.bytes) ∧
    (count.val < 0 →
      replace s ps count = .error (.jl (.domainError "`count` must be non-negative.")))

/-- The number of replacements made with `count` is `min(count, m)`, where `m`
is the number made by the default `count = typemax(Int)`, which is the number
of matches of the reference scan. -/
def ReplaceCountMin : Prop :=
  ∀ (s : JStr) (qs : List (List UInt8 × Pair)) (count : JInt64), 0 ≤ count.val →
    Contract s qs →
    ∃ out m out' m',
      replaceN s (qs.map (·.2)) count = .ok (out, m) ∧
      replaceN s (qs.map (·.2)) typemaxInt = .ok (out', m') ∧
      m' = (refReplace s (qs.map fun q => (q.1, q.2.repl)) (2 ^ 63 - 1)).2 ∧
      m = min count.val.toNat m'

end JuliaLean.StringUtil
