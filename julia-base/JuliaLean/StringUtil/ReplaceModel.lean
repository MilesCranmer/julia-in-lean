import JuliaLean.Strings.Theory

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

/-- What `findnext(p, str, k)` returns: `nothing`, an `Int` (Char and
character-collection patterns) or a range `first:last` (String patterns). -/
inductive Found where
  | nothing
  | idx (i : JInt64)
  | range (a b : JInt64)
  deriving Repr

/-- A `UnitRange{Int}` `first:last`. -/
abbrev Rng := JInt64 × JInt64

/-- A pair `pat => repl`: the finder `k ↦ findnext(_pat_replacer(pat), str, k)`
for the fixed `str`, and the bytes `write(io, repl)` writes. -/
structure Pair where
  find : JInt64 → SJl Found
  repl : List UInt8

instance : Inhabited Pair := ⟨⟨fun _ => .ok .nothing, []⟩⟩

/-- The body of the `map` closures at `base/strings/util.jl:1042-1047` and
`:1094-1098` after `r = findnext(p, str, k)`:
`r === nothing || first(r) == 0` gives `e1+1:0`, and an `Int` `r` becomes `r:r`. -/
def toRange (e1 : JInt64) : Found → Rng
  | .nothing => (e1 + ix 1, ix 0)
  | .idx i => if i.val = 0 then (e1 + ix 1, ix 0) else (i, i)
  | .range a b => if a.val = 0 then (e1 + ix 1, ix 0) else (a, b)

/-- `findnext(p, str, k)` followed by `toRange`. -/
def findRange (p : Pair) (e1 k : JInt64) : SJl Rng :=
  match p.find k with
  | .error e => .error e
  | .ok f => .ok (toRange e1 f)

/-- `rs = map(patterns) do p ... findnext(p, str, a) ... end`,
`base/strings/util.jl:1041-1048`. -/
def findAll (e1 a : JInt64) : List Pair → SJl (List Rng)
  | [] => .ok []
  | p :: ps =>
    match findRange p e1 a with
    | .error e => .error e
    | .ok r =>
      match findAll e1 a ps with
      | .error e => .error e
      | .ok rs => .ok (r :: rs)

/-- `_replace_init(str, pat_repl, count)`, `base/strings/util.jl:1035-1050`,
returning `(e1, rs, notfound)`; `firstindex(str) = 1`. -/
def replaceInit (s : JStr) (ps : List Pair) (count : JInt64) : SJl (JInt64 × List Rng × Bool) :=
  if count.val < 0 then .error (.jl (.domainError "`count` must be non-negative."))
  else
    match nextind s (lastindex s) with
    | .error e => .error e
    | .ok e1 =>
      match findAll e1 (firstindex s) ps with
      | .error e => .error e
      | .ok rs => .ok (e1, rs, rs.all fun r => decide (r.1.val > e1.val))

/-- The fold of `argmin(itr) = findmin(itr)[2]` (`base/reduce.jl:1060,946-947,917-919`):
`_rf_findmin((fm, im), (fx, ix)) = isgreater(fm, fx) ? (fx, ix) : (fm, im)`, and for
`Int`s `isgreater(fm, fx)` is `fx < fm`, so the first minimal
element wins. Indices are zero-based here. -/
def argminAux : List JInt64 → Nat → Nat → JInt64 → Nat
  | [], _, im, _ => im
  | x :: xs, k, im, fm =>
    if x.val < fm.val then argminAux xs (k + 1) k x else argminAux xs (k + 1) im fm

/-- `argmin(map(first, rs))`, `base/strings/util.jl:1071`. Never called on an
empty tuple: `_replace_` returns before `_replace_finish` when `N = 0`. -/
def argmin : List JInt64 → Nat
  | [] => 0
  | x :: xs => argminAux xs 1 0 x

/-- `GC.@preserve str unsafe_write(io, pointer(str, i), UInt(nb))`,
`base/strings/util.jl:1077`: `UInt(nb)` throws `InexactError` for `nb < 0`; then
`nb` bytes of `str` from index `i`. (Julia reads raw memory; every call made
under the finder contract stays inside `str`.) -/
def copyOut (s : JStr) (i nb : JInt64) : SJl (List UInt8) :=
  if nb.val < 0 then .error (.jl (.inexactError "UInt64"))
  else .ok ((s.bytes.drop (i.val - 1).toNat).take nb.val.toNat)

/-- `rs = map(patterns, rs) do p, r; if first(r) < k; r = findnext(p, str, k); ...`,
`base/strings/util.jl:1091-1102`. -/
def refresh (e1 k : JInt64) : List Pair → List Rng → SJl (List Rng)
  | p :: ps, r :: rs =>
    let r' : SJl Rng := if r.1.val < k.val then findRange p e1 k else .ok r
    match r' with
    | .error e => .error e
    | .ok r' =>
      match refresh e1 k ps rs with
      | .error e => .error e
      | .ok rs' => .ok (r' :: rs')
  | _, _ => .ok []

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1068-1104`, returning `(rs, r, i)` (the caller discards
`x` and `nb`) together with the output bytes `io` and the instrumentation `nrep`. -/
def replaceOnce (s : JStr) (ps : List Pair) (start e1 : JInt64) (rs : List Rng)
    (count n i : JInt64) (io : List UInt8) (nrep : Nat) :
    SJl (List Rng × Rng × JInt64 × List UInt8 × Nat) :=
  let x := argmin (rs.map (·.1))
  let r := rs.getD x (ix 0, ix 0)
  let j := r.1
  let k := r.2
  if j.val > e1.val then .ok (rs, r, i, io, nrep)
  else
    let w : SJl (List UInt8 × Nat) :=
      if i.val = start.val ∨ i.val ≤ k.val then
        match copyOut s i (j - i) with
        | .error e => .error e
        | .ok b => .ok (io ++ b ++ (ps.getD x default).repl, nrep + 1)
      else .ok (io, nrep)
    match w with
    | .error e => .error e
    | .ok (io, nrep) =>
      if k.val < j.val then
        if j.val = e1.val then .ok (rs, r, j, io, nrep)
        else
          match nextind s j with
          | .error e => .error e
          | .ok k =>
            if n.val = count.val then .ok (rs, r, j, io, nrep)
            else
              match refresh e1 k ps rs with
              | .error e => .error e
              | .ok rs => .ok (rs, r, j, io, nrep)
      else
        match nextind s k with
        | .error e => .error e
        | .ok k =>
          if n.val = count.val then .ok (rs, r, k, io, nrep)
          else
            match refresh e1 k ps rs with
            | .error e => .error e
            | .ok rs => .ok (rs, r, k, io, nrep)

/-- The loop `while n <= count ... end` of `_replace_finish`,
`base/strings/util.jl:1057-1062`, returning `(i, io, nrep)`. The first argument
bounds the remaining iterations: it starts at `count` with `n = 1`, so it is
`count - n + 1` and reaches `0` exactly when `n <= count` fails. (`n += 1` could
wrap only after `typemax(Int)` iterations, which needs a finder that keeps
returning ranges before `k`.) -/
def finishLoop (s : JStr) (ps : List Pair) (count start e1 : JInt64) :
    Nat → List Rng → JInt64 → JInt64 → List UInt8 → Nat → SJl (JInt64 × List UInt8 × Nat)
  | 0, _, _, i, io, nrep => .ok (i, io, nrep)
  | f + 1, rs, n, i, io, nrep =>
    if !decide (n.val ≤ count.val) then .ok (i, io, nrep)
    else
      match replaceOnce s ps start e1 rs count n i io nrep with
      | .error e => .error e
      | .ok (rs, r, i, io, nrep) =>
        if r.1.val ≥ e1.val then .ok (i, io, nrep)
        else finishLoop s ps count start e1 f rs (n + ix 1) i io nrep

/-- `write(io, SubString(str, i))` at the end of `_replace_finish`,
`base/strings/util.jl:1064`, with `SubString(str, i) = SubString(str, i, li)` and
`li = lastindex(str)`. -/
def writeRest (s : JStr) (i li : JInt64) (io : List UInt8) (nrep : Nat) :
    SJl (List UInt8 × Nat) :=
  match substring s i li with
  | .error e => .error e
  | .ok sub => .ok (io ++ sub.view.bytes, nrep)

/-- `_replace_finish(io, str, count, e1, patterns, replaces, rs)`,
`base/strings/util.jl:1053-1066`: the loop, then `write(io, SubString(str, i))`. -/
def replaceFinish (s : JStr) (ps : List Pair) (count e1 : JInt64) (rs : List Rng) :
    SJl (List UInt8 × Nat) :=
  let start := firstindex s
  match finishLoop s ps count start e1 count.val.toNat rs (ix 1) start [] 0 with
  | .error e => .error e
  | .ok (i, io, nrep) => writeRest s i (lastindex s) io nrep

/-- `_replace_(str, pat_repl, count)`, `base/strings/util.jl:1122-1131`: the code
units of the returned String, with the number of `_replace` calls. -/
def replaceN (s : JStr) (ps : List Pair) (count : JInt64) : SJl (List UInt8 × Nat) :=
  if count.val = 0 then .ok (s.bytes, 0)
  else
    match replaceInit s ps count with
    | .error e => .error e
    | .ok (e1, rs, notfound) =>
      if notfound then .ok (s.bytes, 0)
      else replaceFinish s ps count e1 rs

/-- `replace(s::String, pat_f::Pair...; count)`, `base/strings/util.jl:1186-1187`:
the code units of the result. -/
def replace (s : JStr) (ps : List Pair) (count : JInt64) : SJl (List UInt8) :=
  match replaceN s ps count with
  | .error e => .error e
  | .ok (out, _) => .ok out

/-- `typemax(Int)`, the default `count`. -/
def typemaxInt : JInt64 := ix (2 ^ 63 - 1)

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
