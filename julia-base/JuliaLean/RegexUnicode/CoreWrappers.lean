import JuliaLean.RegexUnicode.CorePcre
import JuliaLean.Strings.Ops

/-!
# Julia's regex wrappers

Line-by-line models of `match`, `findnext`, `count`, `findall`, `eachmatch` and
single-pattern `replace` for `Regex` on `String` (master `bbfa0ce4150`;
identical in 1.13.2). PCRE2 is the primitive `Pcre` of `CorePcre.lean`.

* Code-unit offsets from the ovector are below `2^62` (the axioms of `Pcre` put
  them inside the subject), so the `Csize_t` arithmetic `unsafe_load(p, 1) + 1`
  and its conversion to `Int` are exact; they are written `ix (v.start + 1)`.
* Julia's `while` loops are structural recursion on an explicit bound; each
  docstring states why the bound is never reached.
* Output written to an `IOBuffer` is the list of its code units.
-/

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- `PCRE.exec(re, subject, offset, options, match_data)`, `base/pcre.jl:205-217`,
with the implicit `Csize_t` conversion of `offset` in the `ccall` (`InexactError`
for a negative offset) and `pcre2_match`'s `PCRE2_ERROR_BADOFFSET` for
`offset > length`, reported by `error("PCRE.exec error: $(err_message(rc))")`. -/
def exec (P : Pcre) (s : JStr) (offset : JInt64) (opts : UInt32) : RJl (Option Ovec) :=
  match JInt.convert .u64 offset.val with
  | .error e => .error (.str (.jl e))
  | .ok off =>
    if off.val > (s.bytes.length : Int) then .error (.errorException "PCRE.exec error: bad offset value")
    else .ok (P.run s off.val.toNat opts)

/-- `RegexMatch` (`base/regex.jl:178-184`) without its `regex` field. -/
structure RegexMatch where
  mat : JSub
  captures : List (Option JSub)
  offset : JInt64
  offsets : List JInt64
  deriving DecidableEq, Repr

/-- `SubString(str, a + 1, prevind(str, b + 1))` for a zero-based ovector pair
`(a, b)`, `base/regex.jl:441` and `:448-449`. -/
def capSub (s : JStr) (a b : Int) : RJl JSub :=
  match prevind s (ix (b + 1)) with
  | .error e => .error (.str e)
  | .ok j => liftS (substring s (ix (a + 1)) j)

/-- `match(re, str, idx, add_opts)`, `base/regex.jl:430-454`. `compile(re)` and
the match-data allocation are not modelled. -/
def regexMatch (re : Regex) (s : JStr) (idx : JInt64) (addOpts : UInt32 := 0) :
    RJl (Option RegexMatch) :=
  match exec re.pcre s (idx - ix 1) (re.matchOptions ||| addOpts) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some v) =>
    match capSub s v.start v.stop with
    | .error e => .error e
    | .ok mat =>
      match v.caps.mapM (fun x => (match x with
          | none => .ok none
          | some (a, b) => some <$> capSub s a b : RJl (Option JSub))) with
      | .error e => .error e
      | .ok cap =>
        let off := v.caps.map (fun x => match x with
          | none => ix 0
          | some (a, _) => ix (a + 1))
        .ok (some ⟨mat, cap, ix (v.start + 1), off⟩)

/-- `UnitRange{Int}(a, b)`: `unitrange_last(a, b) = b >= a ? b : a - 1`,
`base/range.jl:428`, `:439-441`. A range is `(first, last)`. -/
def mkRange (a b : JInt64) : JInt64 × JInt64 := (a, if b.val ≥ a.val then b else a - ix 1)

/-- `_findnext_re(re, str, idx, match_data)`, `base/regex.jl:491-512`, after its
first call: `e1r` is the result of `nextind(str, lastindex(str))` (`:492`). -/
def findnextReFrom (re : Regex) (s : JStr) (idx : JInt64) (e1r : SJl JInt64) :
    RJl (Option (JInt64 × JInt64)) :=
  match e1r with
  | .error e => .error (.str e)
  | .ok e1 =>
    if idx.val > e1.val then .error (.str boundsErr)
    else
      match exec re.pcre s (idx - ix 1) re.matchOptions with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some v) =>
        match prevind s (ix (v.stop + 1)) with
        | .error e => .error (.str e)
        | .ok b => .ok (some (mkRange (ix (v.start + 1)) b))

/-- `_findnext_re(re, str, idx, match_data)`, `base/regex.jl:491-512`; this is
`findnext(re, str, idx)` (`:485-487`) and `findnext(::RegexAndMatchData, ...)`
(`:646`). The range is `(Int(ovec[1]) + 1):prevind(str, Int(ovec[2]) + 1)`. -/
def findnextRe (re : Regex) (s : JStr) (idx : JInt64) : RJl (Option (JInt64 × JInt64)) :=
  findnextReFrom re s idx (nextind s (lastindex s))

/-- The loop of `count(t, s; overlap)`, `base/regex.jl:573-585`, with `find i =
findnext(t, s, i)` and `e = lastindex(s)`. Bound: `i` starts at 1 and every pass
that continues sets `i = nextind(s, j)` with `first(r) ≤ j ≤ e` and `first(r) ≥ i`
(`pcre2_match` starts at or after its offset), so `i` increases strictly and stays
at most `e + 1 ≤ ncodeunits(s) + 1`: at most `ncodeunits(s) + 2` passes. -/
def countLoop (find : JInt64 → RJl (Option (JInt64 × JInt64))) (s : JStr) (overlap : Bool)
    (e : JInt64) : Nat → JInt64 → JInt64 → RJl JInt64
  | 0, _, n => .ok n
  | f + 1, i, n =>
    match find i with
    | .error err => .error err
    | .ok none => .ok n
    | .ok (some r) =>
      let n := n + ix 1
      let j := if overlap || decide (r.2.val < r.1.val) then r.1 else r.2
      if j.val > e.val then .ok n
      else
        match nextind s j with
        | .error err => .error (.str err)
        | .ok i => countLoop find s overlap e f i n

/-- `count(re, s; overlap)`, `base/regex.jl:573-585`. -/
def count (re : Regex) (s : JStr) (overlap : Bool := false) : RJl JInt64 :=
  countLoop (findnextRe re s) s overlap (lastindex s) (s.bytes.length + 2) (ix 1) (ix 0)

/-- The loop of `findall(t, s; overlap)`, `base/strings/search.jl:651-665`, with
`find i = findnext(t, s, i)`; same bound as `countLoop`. -/
def findallLoop (find : JInt64 → RJl (Option (JInt64 × JInt64))) (s : JStr) (overlap : Bool)
    (e : JInt64) : Nat → JInt64 → List (JInt64 × JInt64) → RJl (List (JInt64 × JInt64))
  | 0, _, found => .ok found
  | f + 1, i, found =>
    match find i with
    | .error err => .error err
    | .ok none => .ok found
    | .ok (some r) =>
      let found := found ++ [r]
      let j := if overlap || decide (r.2.val < r.1.val) then r.1 else r.2
      if j.val > e.val then .ok found
      else
        match nextind s j with
        | .error err => .error (.str err)
        | .ok i => findallLoop find s overlap e f i found

/-- `findall(re, s; overlap)`, `base/strings/search.jl:651-665`. -/
def findall (re : Regex) (s : JStr) (overlap : Bool := false) : RJl (List (JInt64 × JInt64)) :=
  findallLoop (findnextRe re s) s overlap (lastindex s) (s.bytes.length + 2) (ix 1) []

/-! ## eachmatch -/

/-- Iterator state `(offset, prevempty)`. -/
abbrev State := JInt64 × Bool

/-- `opts_nonempty = UInt32(PCRE.ANCHORED | PCRE.NOTEMPTY_ATSTART)`, `base/regex.jl:750`. -/
def optsNonempty : UInt32 := ANCHORED ||| NOTEMPTY_ATSTART

/-- The `while true` loop of `iterate(itr::RegexMatchIterator, (offset, prevempty))`,
`base/regex.jl:749-777`. Bound 2: the body continues only when `prevempty` is
true and then sets it to false, so the second pass never continues.
`isempty(mat.match)` is `ncodeunits(mat.match) == 0`. -/
def iterLoop (re : Regex) (s : JStr) (overlap : Bool) :
    Nat → JInt64 → Bool → RJl (Option (RegexMatch × State))
  | 0, _, _ => .ok none
  | f + 1, offset, prevempty =>
    match regexMatch re s offset (if prevempty then optsNonempty else 0) with
    | .error e => .error e
    | .ok none =>
      if prevempty && decide (offset.val ≤ (ncodeunits s).val) then
        match nextind s offset with
        | .error e => .error (.str e)
        | .ok o' => iterLoop re s overlap f o' false
      else .ok none
    | .ok (some mat) =>
      let empty := decide (mat.mat.ncu.val = 0)
      let next : RJl JInt64 :=
        if overlap then
          if !empty then liftS (nextind s mat.offset) else .ok mat.offset
        else .ok (mat.offset + mat.mat.ncu)
      match next with
      | .error e => .error e
      | .ok o' => .ok (some (mat, (o', empty)))

/-- `iterate(eachmatch(re, s; overlap), state)`. -/
def iterate (re : Regex) (s : JStr) (overlap : Bool) (st : State) : RJl (Option (RegexMatch × State)) :=
  iterLoop re s overlap 2 st.1 st.2

/-- The initial state `(1, false)` of `iterate(itr::RegexMatchIterator)`. -/
def startState : State := (ix 1, false)

/-- Complete runs of the iterator from a state: the matches produced until
`iterate` returns `nothing`, or the exception it throws. `collect(eachmatch(re,
s; overlap))` is the run from `startState`. -/
inductive EachTrace (re : Regex) (s : JStr) (ov : Bool) : State → RJl (List RegexMatch) → Prop where
  | done {st} : iterate re s ov st = .ok none → EachTrace re s ov st (.ok [])
  | err {st e} : iterate re s ov st = .error e → EachTrace re s ov st (.error e)
  | step {st m st' r} : iterate re s ov st = .ok (some (m, st')) → EachTrace re s ov st' r →
      EachTrace re s ov st ((m :: ·) <$> r)

/-- The iterator run for at most `k` steps (`none` if not finished). -/
def eachmatchFuel (re : Regex) (s : JStr) (ov : Bool) : Nat → State → Option (RJl (List RegexMatch))
  | 0, _ => none
  | k + 1, st =>
    match iterate re s ov st with
    | .error e => some (.error e)
    | .ok none => some (.ok [])
    | .ok (some (m, st')) => (fun r => (m :: ·) <$> r) <$> eachmatchFuel re s ov k st'

theorem eachmatchFuel_sound (re : Regex) (s : JStr) (ov : Bool) :
    ∀ (k : Nat) (st : State) (r : RJl (List RegexMatch)),
      eachmatchFuel re s ov k st = some r → EachTrace re s ov st r := by
  intro k
  induction k with
  | zero => intro st r h; simp [eachmatchFuel] at h
  | succ k ih =>
    intro st r h
    simp only [eachmatchFuel] at h
    split at h
    · rename_i e he; cases h; exact .err he
    · rename_i he; cases h; exact .done he
    · rename_i m st' he
      cases h' : eachmatchFuel re s ov k st' with
      | none => rw [h'] at h; cases h
      | some r' =>
        rw [h'] at h; cases h
        exact .step he (ih st' r' h')

/-! ## replace -/

/-- `UInt(x)` for an `Int`: `InexactError` when negative. -/
def convU (x : JInt64) : RJl Nat :=
  match JInt.convert .u64 x.val with
  | .error e => .error (.str (.jl e))
  | .ok u => .ok u.val.toNat

/-- The per-pattern search of `_replace_init` (`base/strings/util.jl:1041-1048`) and
`_replace_once` (`:1092-1101`): `findnext(p, str, k)`, with `nothing` or
`first(r) == 0` mapped to `e1+1:0`. -/
def replaceFind (re : Regex) (s : JStr) (e1 k : JInt64) : RJl (JInt64 × JInt64) :=
  match findnextRe re s k with
  | .error e => .error e
  | .ok none => .ok (mkRange (e1 + ix 1) (ix 0))
  | .ok (some r) => if r.1.val = 0 then .ok (mkRange (e1 + ix 1) (ix 0)) else .ok r

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1068-1104`, for one pattern (`N = 1`, so `x = 1` and `rs`
is a single range) with a `String` replacement (`_replace(io, repl::String, ...)
= write(io, repl)`, `:1011-1012`). Returns `(rs, r, i, out)`. `unsafe_write(io,
pointer(str, i), UInt(j-i))` copies `j - i` code units starting at index `i`. -/
def replaceOnce (re : Regex) (s repl : JStr) (start e1 : JInt64) (rs : JInt64 × JInt64)
    (count n i : JInt64) (out : List UInt8) :
    RJl ((JInt64 × JInt64) × (JInt64 × JInt64) × JInt64 × List UInt8) :=
  let r := rs
  let j := r.1
  let k := r.2
  if j.val > e1.val then .ok (rs, r, i, out)
  else
    let written : RJl (List UInt8) :=
      if decide (i.val = start.val) || decide (i.val ≤ k.val) then
        match convU (j - i) with
        | .error e => .error e
        | .ok len => .ok (out ++ (s.bytes.drop (i.val - 1).toNat).take len ++ repl.bytes)
      else .ok out
    match written with
    | .error e => .error e
    | .ok out =>
      -- `some (i, k)` continues; `none` is the `j == e1 && return` after `i = j`
      let step : SJl (Option (JInt64 × JInt64)) :=
        if k.val < j.val then
          if j.val = e1.val then .ok none
          else (fun k' => some (j, k')) <$> nextind s j
        else (fun k' => some (k', k')) <$> nextind s k
      match step with
      | .error e => .error (.str e)
      | .ok none => .ok (rs, r, j, out)
      | .ok (some (i, k)) =>
        if n.val = count.val then .ok (rs, r, i, out)
        else if rs.1.val < k.val then
          match replaceFind re s e1 k with
          | .error e => .error e
          | .ok rs' => .ok (rs', r, i, out)
        else .ok (rs, r, i, out)

/-- The `while n <= count` loop of `_replace_finish`, `base/strings/util.jl:1057-1062`.
Bound `ncodeunits(s) + 3`: the start `j` of the range handled by successive passes
increases strictly (the next search starts at `nextind(str, j)` or later), every
pass that continues has `j < e1 = ncodeunits(s) + 1`, so there are at most
`ncodeunits(s) + 2` passes. -/
def replaceLoop (re : Regex) (s repl : JStr) (start e1 count : JInt64) :
    Nat → (JInt64 × JInt64) → JInt64 → JInt64 → List UInt8 → RJl (JInt64 × List UInt8)
  | 0, _, _, i, out => .ok (i, out)
  | f + 1, rs, n, i, out =>
    if !decide (n.val ≤ count.val) then .ok (i, out)
    else
      match replaceOnce re s repl start e1 rs count n i out with
      | .error e => .error e
      | .ok (rs, r, i, out) =>
        if r.1.val ≥ e1.val then .ok (i, out)
        else replaceLoop re s repl start e1 count f rs (n + ix 1) i out

/-- `_replace_finish(io, str, count, e1, patterns, replaces, rs)`,
`base/strings/util.jl:1053-1066`, ending with `write(io, SubString(str, i))`. -/
def replaceFinish (re : Regex) (s repl : JStr) (count e1 : JInt64) (rs : JInt64 × JInt64) :
    RJl (List UInt8) :=
  match replaceLoop re s repl (ix 1) e1 count (s.bytes.length + 3) rs (ix 1) (ix 1) [] with
  | .error e => .error e
  | .ok (i, out) =>
    match substring s i (lastindex s) with
    | .error e => .error (.str e)
    | .ok ss => .ok (out ++ ss.view.bytes)

/-- `typemax(Int)`, the default `count` of `replace`. -/
def intMax : JInt64 := ix (2 ^ 63 - 1)

/-- `replace(s, re => repl::String; count)` = `_replace_(String(s), (re => repl,), Int(count))`,
`base/strings/util.jl:1186-1187`, `:1122-1131`, `:1035-1050`; the result is the
code units of the returned String. -/
def replace (re : Regex) (s repl : JStr) (count : JInt64 := intMax) : RJl (List UInt8) :=
  if count.val = 0 then .ok s.bytes
  else if count.val < 0 then .error (.str (.jl (.domainError "`count` must be non-negative.")))
  else
    match nextind s (lastindex s) with
    | .error e => .error (.str e)
    | .ok e1 =>
      match replaceFind re s e1 (ix 1) with
      | .error e => .error e
      | .ok rs =>
        if rs.1.val > e1.val then .ok s.bytes
        else replaceFinish re s repl count e1 rs

end JuliaLean.RegexUnicode.Core
