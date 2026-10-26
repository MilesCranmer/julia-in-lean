import JuliaLean.StringsCovB.AIO
import JuliaLean.StringUtil.ReplaceModel
import JuliaLean.RegexUnicode.CoreWrappers

/-!
# `replace` on `AnnotatedString`s, `base/strings/annotated_io.jl:240-338`

Line-by-line model of `replace(out::AnnotatedIOBuffer, str::AnnotatedString,
pat_f::Pair...; count)` together with `_replace_init` and `_replace_once`
(`base/strings/util.jl:1035-1104`, reusing the `StringUtil` replace model for the
pattern search) and the two wrappers.

* A pair `pat => repl` is the finder `k ↦ findnext(_pat_replacer(pat), str, k)`
  (as in `StringUtil.Pair`) and the replacement value: a `String`/`Char`
  (its code units), an `AnnotatedString` or an `AnnotatedChar`.
  `_replace(io, repl, ...)` is `write(io, repl)` (`base/strings/util.jl:1011-1012`),
  which for annotated values writes their unannotated code units and returns
  their number (`base/strings/annotated_io.jl:362-366`).
* Writes into `out.io` are `IOBuffer` writes (`unsafe_write`) at its position.
* `_free_pat_replacer` only frees PCRE match data and is omitted.
-/

namespace JuliaLean.StringsCovB.AIOR

open JuliaLean JuliaLean.Strings JuliaLean.StringsCovB.Ann JuliaLean.StringsCovB.AIO

/-- A replacement value. -/
inductive Repl where
  | plain (bs : List UInt8)
  | astr (a : AS)
  | achar (c : AC)

/-- The code units `write(io, repl)` writes. -/
def Repl.bytes : Repl → List UInt8
  | .plain bs => bs
  | .astr a => a.str.bytes
  | .achar c => charBytes c.char

/-- A pair `pat => repl`. -/
structure APair where
  find : JInt64 → SJl StringUtil.Found
  repl : Repl

instance : Inhabited APair := ⟨⟨fun _ => .ok .nothing, .plain []⟩⟩

def APair.toPair (p : APair) : StringUtil.Pair := ⟨p.find, p.repl.bytes⟩

/-- `write(io, bytes)` into `out.io`. -/
def wIO (bs : List UInt8) : AM JInt64 := onIO (IOBuffers.unsafeWrite bs)

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1068-1104`, writing to `out.io`: returns `(rs, x, r, nb, i)`,
with `x` zero-based and `nb` the result of `_replace` (0 when nothing is written). -/
def replaceOnce (s : JStr) (ps : List APair) (start e1 : JInt64) (rs : List StringUtil.Rng)
    (count n i : JInt64) : AM (List StringUtil.Rng × Nat × StringUtil.Rng × JInt64 × JInt64) := do
  let x := StringUtil.argmin (rs.map (·.1))
  let r := rs.getD x (ix 0, ix 0)
  let j := r.1
  let k := r.2
  if j.val > e1.val then return (rs, x, r, ix 0, i)
  let nb ← if i.val = start.val ∨ i.val ≤ k.val then do
      let b ← liftS (StringUtil.copyOut s i (j - i))
      discard (wIO b)
      wIO (ps.getD x default).repl.bytes
    else pure (ix 0)
  if k.val < j.val then
    if j.val = e1.val then return (rs, x, r, nb, j)
    let k ← liftS (nextind s j)
    if n.val = count.val then return (rs, x, r, nb, j)
    let rs ← liftS (StringUtil.refresh e1 k (ps.map APair.toPair) rs)
    return (rs, x, r, nb, j)
  else
    let k ← liftS (nextind s k)
    if n.val = count.val then return (rs, x, r, nb, k)
    let rs ← liftS (StringUtil.refresh e1 k (ps.map APair.toPair) rs)
    return (rs, x, r, nb, k)

/-- An element `(region, offset)` of `replacements`. -/
structure Rep where
  region : Region
  offset : JInt64

instance : Inhabited Rep := ⟨⟨(ix 0, ix 0), ix 0⟩⟩

/-- The annotations of an annotated replacement in the form `_insert_annotations!`
takes, `base/strings/annotated_io.jl:265-272`: an `AnnotatedChar`'s annotations get
the region `1:newbytes`. `none` for an unannotated replacement (`_isannotated`). -/
def replAnnots (repl : Repl) (newbytes : JInt64) : Option (List RA) :=
  match repl with
  | .plain _ => none
  | .astr a => some a.anns
  | .achar c => some (c.anns.map (RA.ofAnn (urange (ix 1) newbytes)))

/-- The `while nrep <= count` loop of `replace(out::AnnotatedIOBuffer, ...)`,
`base/strings/annotated_io.jl:248-273`. The fuel is `count`: the loop starts with
`nrep = 1` and increments it on every pass that continues. Returns `bytepos`,
`replacements` and `newannots`. -/
def replLoop (s : JStr) (ps : List APair) (bytestart e1 count : JInt64) :
    Nat → List StringUtil.Rng → JInt64 → JInt64 → List Rep → List RA →
      AM (JInt64 × List Rep × List RA)
  | 0, _, _, bytepos, reps, newannots => pure (bytepos, reps, newannots)
  | fuel + 1, repspans, nrep, bytepos, reps, newannots => do
    if !decide (nrep.val ≤ count.val) then return (bytepos, reps, newannots)
    let (repspans, ridx, xspan, newbytes, bytepos) ←
      replaceOnce s ps bytestart e1 repspans count nrep bytepos
    if xspan.1.val ≥ e1.val then return (bytepos, reps, newannots)
    let nrep := nrep + ix 1
    let xspan ← if !isemptyR xspan then do
        let cu ← liftS (codeunit s xspan.2)
        if cu > 0x80 then do
          let nx ← liftS (nextind s xspan.2)
          pure (urange xspan.1 (nx - ix 1))
        else pure xspan
      else pure xspan
    let drift := (reps.getLast?.map (·.offset)).getD (ix 0)
    let thisrep : Rep := ⟨xspan, drift + newbytes - IOBuffers.rangeLength xspan.1 xspan.2⟩
    let destoff := xspan.1 - ix 1 + drift
    let reps := reps ++ [thisrep]
    match replAnnots (ps.getD ridx default).repl newbytes with
    | none => replLoop s ps bytestart e1 count fuel repspans nrep bytepos reps newannots
    | some annots' =>
      replLoop s ps bytestart e1 count fuel repspans nrep bytepos reps (insertAnns newannots annots' destoff)

/-- `searchsortedlast(replacements, (region = x:x, offset = 0), by = r -> first(r.region))`:
the number of leading replacements with `first(region) ≤ x` (one-based index). -/
def ssLast (reps : List Rep) (x : JInt64) : Nat := (reps.takeWhile fun r => decide (r.region.1.val ≤ x.val)).length

/-- `searchsortedfirst(replacements, (region = x:x, offset = 0), by = ...)`: one plus
the number of leading replacements with `first(region) < x`. -/
def ssFirst (reps : List Rep) (x : JInt64) : Nat :=
  (reps.takeWhile fun r => decide (r.region.1.val < x.val)).length + 1

/-- Checked `replacements[k]` (one-based). -/
def repAt (reps : List Rep) (k : Nat) : SJl Rep :=
  if 1 ≤ k ∧ k ≤ reps.length then .ok (reps.getD (k - 1) default) else .error boundsErr

/-- The "split between replacements" loop, `base/strings/annotated_io.jl:311-323`. -/
def gapLoop (start stop : JInt64) (label : Nat) (value : Val) : Rep → List Rep → List RA
  | _, [] => []
  | prevrep, rep :: rest =>
    let gap := urange (imax start (prevrep.region.2 + ix 1)) (imin stop (rep.region.1 - ix 1))
    let here := if !isemptyR gap then
        let r := urange (gap.1 + prevrep.offset) (gap.2 + prevrep.offset)
        [⟨r.1, r.2, label, value⟩]
      else []
    here ++ gapLoop start stop label value rep rest

/-- The annotations pushed for one annotation of `str`,
`base/strings/annotated_io.jl:288-325`. -/
def placeAnn (reps : List Rep) (a : RA) : SJl (List RA) := do
  let start := a.lo
  let stop := a.hi
  let prioridx := ssLast reps start
  let postidx := ssFirst reps stop
  let priorrep ← repAt reps prioridx
  let postrep ← repAt reps postidx
  if prioridx = postidx ∧ start.val ≥ priorrep.region.1.val ∧ stop.val ≤ priorrep.region.2.val then
    pure []
  else if (postidx : Int) - prioridx ≤ 1 ∧ start.val > priorrep.region.2.val ∧
      stop.val < postrep.region.1.val then
    let r := urange (start + priorrep.offset) (stop + priorrep.offset)
    pure [⟨r.1, r.2, a.label, a.value⟩]
  else
    let lo := max 1 (prioridx - 1)
    let hi := min reps.length (postidx + 1)
    let prevrep ← repAt reps lo
    pure (gapLoop start stop a.label a.value prevrep ((reps.drop (lo - 1)).take (hi + 1 - lo)))

/-- The `for (; region, label, value) in str.annotations` loop. -/
def placeAll (reps : List Rep) : List RA → SJl (List RA)
  | [] => .ok []
  | a :: rest => do
    let h ← placeAnn reps a
    let t ← placeAll reps rest
    pure (h ++ t)

/-- `replace(out::AnnotatedIOBuffer, str::AnnotatedString, pat_f::Pair...; count)`,
`base/strings/annotated_io.jl:240-328`. -/
def replaceAIO (str : AS) (ps : List APair) (count : JInt64) : AM Unit := do
  if count.val = 0 ∨ ps.isEmpty then
    discard (writeW (.str str))
    return
  let (e1, repspans, notfound) ← liftS (StringUtil.replaceInit str.str (ps.map APair.toPair) count)
  if notfound then
    discard (writeW (.str str))
    return
  let out ← get
  let isappending := eofA out
  let bytestart := firstindex str.str
  let reps0 : List Rep := [⟨urange (bytestart - ix 1) (bytestart - ix 1), position out⟩]
  let (bytepos, reps, newannots) ←
    replLoop str.str ps bytestart e1 count count.val.toNat repspans (ix 1) bytestart reps0 []
  let lastoff := (reps.getLast?.map (·.offset)).getD (ix 0)
  let reps := reps ++ [⟨urange e1 (e1 - ix 1), lastoff⟩]
  let rest ← liftS (substring str.str bytepos (lastindex str.str))
  discard (wIO rest.view.bytes)
  let out ← get
  if !isappending then
    setAnns (clearRegion out.anns (urange (reps.headD default).offset (position out)))
  let placed ← liftS (placeAll reps str.anns)
  let out ← get
  setAnns (out.anns ++ placed ++ newannots)

/-- `replace(out::IO, str::AnnotatedString, pat_f::Pair...; count) =
replace(out, str.string, pat_f...; count)`, `base/strings/annotated_io.jl:330-331`:
the plain `replace` of the underlying `String` written to `out` (a byte sink;
`_replace_(io, ...)` writes what `_replace_(str, ...)` returns,
`base/strings/util.jl:1107-1131`). -/
def replaceIO (out : List UInt8) (str : AS) (ps : List APair) (count : JInt64) : SJl (List UInt8) :=
  (StringUtil.replace str.str (ps.map APair.toPair) count).map (out ++ ·)

/-- `replace(str::AnnotatedString, pat_f::Pair...; count)`,
`base/strings/annotated_io.jl:333-338`. `isempty(pat_f) || iszero(count) && return str`
parses as `isempty(pat_f) || (iszero(count) && return str)`. -/
def replaceAS (str : AS) (ps : List APair) (count : JInt64) : Except AErr AS :=
  if !ps.isEmpty ∧ count.val = 0 then .ok str
  else
    match IOBuffers.iobuffer with
    | .error e => .error (.io e)
    | .ok io =>
      match (do replaceAIO str ps count; AIO.seek 0; readASAny).run (ofIO io) with
      | .ok r _ => .ok r
      | .error e _ => .error e

/-- `typemax(Int)`, the default `count`. -/
def intMax : JInt64 := ix (2 ^ 63 - 1)

/-! ## Finders -/

/-- `findnext(RegexAndMatchData(re), str, k)` with the regex model of
`RegexUnicode.Core` (`_findnext_re`, `base/regex.jl:491-512`): a range or
`nothing`. An `ErrorException` from PCRE (not reached in the examples below) is
reported as an `ArgumentError`. -/
def regexFinder (re : RegexUnicode.Core.Regex) (s : JStr) (k : JInt64) : SJl StringUtil.Found :=
  match RegexUnicode.Core.findnextRe re s k with
  | .ok none => .ok .nothing
  | .ok (some (a, b)) => .ok (.range a b)
  | .error (.str e) => .error e
  | .error (.errorException m) => .error (.jl (.argumentError m))

end JuliaLean.StringsCovB.AIOR
