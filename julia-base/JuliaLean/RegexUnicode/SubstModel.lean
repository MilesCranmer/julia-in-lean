import JuliaLean.Core
import JuliaLean.IOBuffers.Model

/-!
# Regex substitution: `replace([io], s, r => s"...")`

Model of the substitution-string path of `replace` with a `Regex` pattern (master
`bbfa0ce4150`):

* `_replace(io, repl_s::SubstitutionString, str, r, re)`, `base/regex.jl:675-733`, walking
  `repl = unescape_string(repl_s.string, KEEP_ESC)` (the model input is the unescaped
  text) byte by byte. `write(io, c::Char)` (`base/io.jl:973-980`) writes the bytes of `c`
  one at a time with `write(io, ::UInt8)` and sums the counts, so for valid UTF-8 the
  byte walk issues exactly the same writes; the model is stated for ASCII text.
* `_write_capture(io, group, str, r, re::RegexAndMatchData)`, `base/regex.jl:654-664`,
  on the `IOBuffer` model of `JuliaLean.IOBuffers.Model`: `ensureroom(io, len+1)`, then
  `PCRE.substring_copy_bynumber` copies `len` bytes and a NUL terminator through
  `pointer(io.data, io.ptr)` (unchecked: `writeAt` with `isMem = true`), then
  `io.ptr += len; io.size = max(io.size, io.ptr - 1)`.
* the `replace` driver `_replace_`, `_replace_init`, `_replace_finish`, `_replace_once`
  (`base/strings/util.jl:1036-1131`) for one `Regex => SubstitutionString` pair and the
  default `count = typemax(Int)`, both into an `io` and into a fresh `IOBuffer`
  (`replace(s, pat => r)`, `takestring!`).

The `io` argument is an `IOBuffer` state or another `IO` (an `IOContext`, `IOStream` or
`devnull`), modelled as a byte sink: `write`/`unsafe_write` append, while `ensureroom` and
the field `io.data` exist only for `GenericIOBuffer` (`MethodError` otherwise).

PCRE2 is a primitive. Matching is a leftmost-first backtracking interpreter for the
fragment literals, concatenation, alternation, greedy `+` and numbered capture groups,
which is how PCRE2 matches that fragment. `pcre2_substring_length_bynumber`,
`pcre2_substring_copy_bynumber` and `pcre2_substring_number_from_name` follow the PCRE2
API documentation (`pcre2api(3)`, "Extracting captured substrings by number/name"):
a group number above the highest group is `PCRE2_ERROR_NOSUBSTRING` ("unknown
substring"), an unset group is `PCRE2_ERROR_UNSET`, an unknown name is
`PCRE2_ERROR_NOSUBSTRING` (-49) and a name used by several groups is
`PCRE2_ERROR_NOUNIQUESUBSTRING` (-50).

Subjects are ASCII, so `nextind(str, k) = k + 1` and `prevind(str, k) = k - 1`.
Exception messages are modelled only as far as the properties need them: the text that
Julia interpolates into `replace_err` messages is omitted.
-/

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## The `io` argument -/

/-- The `io` argument of `replace(io, ...)`. -/
inductive Sink where
  /-- An `IOBuffer` (`GenericIOBuffer`). -/
  | buf (io : IOBuf)
  /-- Any other `IO`: the bytes written to it so far. -/
  | other (out : List UInt8)
  deriving DecidableEq

/-- Mutating calls on the `io` argument; state changes made before an exception persist. -/
abbrev SM := EStateM IOErr Sink

def liftE {α} : Except IOErr α → SM α
  | .ok a => pure a
  | .error e => throw e

/-- A method or field that exists only for `GenericIOBuffer`: on another `IO` it is a
`MethodError` (`ensureroom`) or a missing field (`io.data`). -/
def onBuf {α} (f : String) (x : M α) : SM α := fun s =>
  match s with
  | .buf io =>
    match x io with
    | .ok a io' => .ok a (.buf io')
    | .error e io' => .error e (.buf io')
  | .other _ => .error (.jl (.methodError f)) s

/-- `write(io, b::UInt8)`: `base/iobuffer.jl:948-963` for an `IOBuffer`; one byte for a
sink. -/
def writeU8 (b : UInt8) : SM I := fun s =>
  match s with
  | .buf io => onBuf "write" (writeByte b) (.buf io)
  | .other out => .ok (i 1) (.other (out ++ [b]))

/-- `unsafe_write(io, p, n)` of the bytes `bs`: `base/iobuffer.jl:902-921` for an
`IOBuffer`; `write(io, ::String)` and `write(io, ::SubString{String})` call it. -/
def unsafeWriteIO (bs : List UInt8) : SM I := fun s =>
  match s with
  | .buf io => onBuf "unsafe_write" (unsafeWrite bs) (.buf io)
  | .other out => .ok (i bs.length) (.other (out ++ bs))

/-! ## PCRE2 match data -/

/-- The ovector of a match: for each group `0..top`, its 0-based byte range `[start, end)`,
or `none` (`PCRE2_UNSET`) when the group did not participate. -/
abbrev Ovec := List (Option (Nat × Nat))

/-- `PCRE.substring_length_bynumber(match_data, number)`, `base/pcre.jl:245-254`. The
`Cint` argument converts the `Int` (`InexactError` outside `Int32`); PCRE2 reads it as a
`uint32_t`. `PCRE2_ERROR_UNSET` gives 0; other errors throw
`ErrorException("PCRE error: ...")`. -/
def substringLengthBynumber (md : Ovec) (g : I) : Except IOErr I :=
  if g.val < -2 ^ 31 ∨ 2 ^ 31 ≤ g.val then .error (.jl (.inexactError "Int32"))
  else
    let n : Int := if g.val < 0 then g.val + 2 ^ 32 else g.val
    if (md.length : Int) ≤ n then .error (.errorException "PCRE error: unknown substring")
    else match md.getD n.toNat none with
      | none => .ok (i 0)
      | some (a, b) => .ok (i (b - a : Nat))

/-- `PCRE.substring_copy_bynumber(match_data, number, buf, buf_size)`,
`base/pcre.jl:256-263`: the bytes PCRE2 stores at `buf` (the group and a NUL). The
`UInt32` argument converts the `Int`. -/
def substringCopyBynumber (md : Ovec) (subj : List UInt8) (g : I) (bufSize : I) :
    Except IOErr (List UInt8) :=
  if g.val < 0 ∨ 2 ^ 32 ≤ g.val then .error (.jl (.inexactError "UInt32"))
  else if (md.length : Int) ≤ g.val then .error (.errorException "PCRE error: unknown substring")
  else match md.getD g.val.toNat none with
    | none => .error (.errorException "PCRE error: requested value is not set")
    | some (a, b) =>
      if bufSize.val ≤ (b - a : Nat) then .error (.errorException "PCRE error: no more memory")
      else .ok ((subj.drop a).take (b - a) ++ [0])

/-- A PCRE2 name table: `(group number, name)` entries. -/
abbrev NameTable := List (Nat × List UInt8)

/-- `pcre2_substring_number_from_name`: the number of the unique group called `name`,
`PCRE2_ERROR_NOSUBSTRING` (-49) if none, `PCRE2_ERROR_NOUNIQUESUBSTRING` (-50) if several. -/
def numberFromName (tbl : NameTable) (name : List UInt8) : Int :=
  match tbl.filter (fun e => e.2 == name) with
  | [] => -49
  | [e] => e.1
  | _ => -50

/-- `PCRE.substring_number_from_name(re, name)`, `base/pcre.jl:239-243`: the `Cstring`
conversion rejects an embedded NUL. -/
def substringNumberFromName (tbl : NameTable) (name : List UInt8) : Except IOErr I :=
  if name.contains 0 then .error (.jl (.argumentError "embedded NULs are not allowed in C strings"))
  else .ok (i (numberFromName tbl name))

/-! ## `_write_capture` and `_replace` -/

/-- `_write_capture(io, group, str, r, re::RegexAndMatchData)`, `base/regex.jl:654-664`. -/
def writeCapture (md : Ovec) (subj : List UInt8) (group : I) : SM I := do
  let len ← liftE (substringLengthBynumber md group)
  -- regex.jl:657: an optional group that does not match has length 0
  if len.val = 0 then return len
  -- regex.jl:658, `ensureroom(io::GenericIOBuffer, nshort::Int)` (iobuffer.jl:597)
  onBuf "ensureroom" (do let n ← lift (toU (len + i 1).val); ensureroom n)
  -- regex.jl:659-660: copy `len + 1` bytes to `pointer(io.data, io.ptr)`
  let bytes ← liftE (substringCopyBynumber md subj group (len + i 1))
  onBuf "getproperty" (do
    let io ← get
    let data ← lift (writeAt true io.data io.ptr bytes)
    -- regex.jl:661-662
    let ptr := io.ptr + len
    set { io with data, ptr, size := imax io.size (ptr - i 1) })
  return len

/-- `SUB_CHAR = '\\'`, `base/regex.jl:671`. -/
def SUB : UInt8 := 92
/-- `GROUP_CHAR = 'g'`, `base/regex.jl:672`. -/
def GRP : UInt8 := 103
/-- `LBRACKET = '<'`, `base/regex.jl:676`. -/
def LB : UInt8 := 60
/-- `RBRACKET = '>'`, `base/regex.jl:677`. -/
def RB : UInt8 := 62

/-- `isdigit(c)`: `'0' <= c <= '9'`. -/
def isDigitB (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- Value of a decimal digit string as a mathematical number. -/
def digitsValue (ds : List UInt8) : Nat := ds.foldl (fun acc d => 10 * acc + (d.toNat - 48)) 0

/-- `parse(Int, s)` for a string of ASCII digits: empty is an `ArgumentError`, a value above
`typemax(Int)` an `OverflowError`. -/
def parseIntDigits (ds : List UInt8) : Except IOErr I :=
  if ds = [] then .error (.jl (.argumentError "input string is empty or only contains whitespace"))
  else if 2 ^ 63 - 1 < digitsValue ds then .error (.jl (.overflowError "overflow parsing"))
  else .ok (i (digitsValue ds))

/-- `replace_err(repl)`, `base/regex.jl:652`. -/
def replaceErr {α} (what : String) : SM α :=
  throw (.errorException ("Bad replacement string: " ++ what))

/-- What `_write_capture` needs from the match: the subject, the match data and the
regex's name table. -/
structure Ctx where
  subj : List UInt8
  md : Ovec
  names : NameTable

/-- The digit loop `group = 10group + parse(Int, repl[i])`, `base/regex.jl:692-699`, with
Julia's wrapping `Int` arithmetic: the final `group` and index. -/
def digitsLoop (repl : List UInt8) : Nat → Nat → I → I × Nat
  | 0, p, g => (g, p)
  | f + 1, p, g =>
    if p < repl.length ∧ isDigitB (repl.getD p 0) = true then
      digitsLoop repl f (p + 1) (i 10 * g + i ((repl.getD p 0).toNat - 48))
    else (g, p)

/-- `while repl[i] != RBRACKET; i = nextind(repl, i); i > e && replace_err(repl); end`,
`base/regex.jl:708-711`: the index of the closing `>`, or `none` for `replace_err`. -/
def scanName (repl : List UInt8) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, q =>
    if repl.getD q 0 = RB then some q
    else if repl.length ≤ q + 1 then none
    else scanName repl f (q + 1)

/-- The `while i <= e` loop of `_replace(io, repl_s::SubstitutionString, str, r, re)`,
`base/regex.jl:683-731`, over 0-based index `p` of the unescaped `repl`, with running count
`nb`. -/
def substLoop (ctx : Ctx) (repl : List UInt8) : Nat → Nat → I → SM I
  | 0, _, nb => pure nb
  | fuel + 1, p, nb =>
    if repl.length ≤ p then pure nb
    else if repl.getD p 0 = SUB then
      let nx := p + 1
      -- regex.jl:686
      if repl.length ≤ nx then replaceErr "repl"
      -- regex.jl:687-689
      else if repl.getD nx 0 = SUB then do
        let w ← writeU8 SUB
        substLoop ctx repl fuel (nx + 1) (nb + w)
      -- regex.jl:690-700
      else if isDigitB (repl.getD nx 0) then do
        let (group, q) := digitsLoop repl repl.length (nx + 1) (i ((repl.getD nx 0).toNat - 48))
        let w ← writeCapture ctx.md ctx.subj group
        substLoop ctx repl fuel q (nb + w)
      -- regex.jl:701-723
      else if repl.getD nx 0 = GRP then do
        let q := nx + 1
        if repl.length ≤ q ∨ repl.getD q 0 ≠ LB then replaceErr "repl"
        let q := q + 1
        if repl.length ≤ q then replaceErr "repl"
        let gs := q
        match scanName repl repl.length q with
        | none => replaceErr "repl"
        | some q' =>
          let name := (repl.drop gs).take (q' - gs)
          let group ←
            if name.all isDigitB then liftE (parseIntDigits name)
            else do
              let g ← liftE (substringNumberFromName ctx.names name)
              if g.val < 0 then replaceErr "Group not found in regex"
              pure g
          let w ← writeCapture ctx.md ctx.subj group
          substLoop ctx repl fuel (q' + 1) (nb + w)
      -- regex.jl:724-726
      else replaceErr "repl"
    else do
      -- regex.jl:727-730
      let w ← writeU8 (repl.getD p 0)
      substLoop ctx repl fuel (p + 1) (nb + w)

/-- `_replace(io, repl_s::SubstitutionString, str, r, re)`, `base/regex.jl:675-733`, on the
unescaped replacement `repl`; returns `nb`. -/
def substStep (ctx : Ctx) (repl : List UInt8) : SM I :=
  substLoop ctx repl (repl.length + 1) 0 (i 0)

/-- `nb += write(io, c)` for each character `c` of `cs`, in order. -/
def writeChars : List UInt8 → I → SM I
  | [], nb => pure nb
  | c :: t, nb => do
    let w ← writeU8 c
    writeChars t (nb + w)

/-! ## PCRE2 matching for a pattern fragment -/

/-- Regex fragment: a byte, concatenation, alternation, greedy `+`, numbered capture group. -/
inductive Pat where
  | lit (b : UInt8)
  | seq (a b : Pat)
  | alt (a b : Pat)
  | plus (a : Pat)
  | grp (n : Nat) (a : Pat)
  deriving DecidableEq, Repr

/-- Highest capture group number (`PCRE2_INFO_CAPTURECOUNT`). -/
def Pat.top : Pat → Nat
  | .lit _ => 0
  | .seq a b | .alt a b => max a.top b.top
  | .plus a => a.top
  | .grp n a => max n a.top

def Pat.size : Pat → Nat
  | .lit _ => 1
  | .seq a b | .alt a b => a.size + b.size + 1
  | .plus a | .grp _ a => a.size + 1

/-- Backtracking matcher in continuation-passing style: match `p` at byte `pos` with
captures `ov`, then run the continuation `k`. Alternatives are tried left to right, `+`
is greedy and stops on an empty iteration. -/
def mt (s : List UInt8) : Nat → Pat → Nat → Ovec → (Nat → Ovec → Option Ovec) → Option Ovec
  | 0, _, _, _, _ => none
  | _ + 1, .lit b, pos, ov, k => if pos < s.length ∧ s.getD pos 0 = b then k (pos + 1) ov else none
  | f + 1, .seq a b, pos, ov, k => mt s f a pos ov (fun q ov' => mt s f b q ov' k)
  | f + 1, .alt a b, pos, ov, k =>
    match mt s f a pos ov k with
    | some r => some r
    | none => mt s f b pos ov k
  | f + 1, .grp n a, pos, ov, k => mt s f a pos ov (fun q ov' => k q (ov'.set n (some (pos, q))))
  | f + 1, .plus a, pos, ov, k =>
    mt s f a pos ov (fun q ov' =>
      match (if pos < q then mt s f (.plus a) q ov' k else none) with
      | some r => some r
      | none => k q ov')

/-- Leftmost match starting at a byte offset `≥ st`. -/
def execFrom (p : Pat) (s : List UInt8) (fuel : Nat) : Nat → Nat → Option Ovec
  | 0, _ => none
  | n + 1, st =>
    if s.length < st then none
    else
      match mt s fuel p st (List.replicate (p.top + 1) none)
          (fun q ov => some (ov.set 0 (some (st, q)))) with
      | some ov => some ov
      | none => execFrom p s fuel n (st + 1)

/-- `pcre2_match(re, subject, length, offset, NO_UTF_CHECK, match_data)` for a fragment
pattern: the ovector of the leftmost match at or after `offset`. -/
def exec (p : Pat) (s : List UInt8) (offset : Nat) : Option Ovec :=
  execFrom p s ((s.length + 2) * (p.size + 2)) (s.length + 1) offset

/-! ## The `replace` driver, `base/strings/util.jl` -/

/-- A match `j:k` (1-based, inclusive) with its match data. -/
structure Rng where
  j : I
  k : I
  md : Ovec

/-- `findnext(pat::RegexAndMatchData, str, i)`, `base/regex.jl:646`, i.e. `_findnext_re`
(`base/regex.jl:491-512`), followed by the `r === nothing || first(r) == 0` sentinel
`e1+1:0` of `_replace_init`/`_replace_once` (`base/strings/util.jl:1044-1049, 1095-1098`).
The range is `(start+1):prevind(str, end+1)`. -/
def findnextRe (p : Pat) (s : List UInt8) (e1 idx : I) : Except IOErr Rng :=
  if (s.length + 1 : Int) < idx.val then .error (.jl .boundsError)
  else
    match exec p s (idx.val - 1).toNat with
    | some ov =>
      match ov.getD 0 none with
      | some (a, b) => if a + 1 = 0 then .ok ⟨e1 + i 1, i 0, []⟩ else .ok ⟨i (a + 1), i b, ov⟩
      | none => .ok ⟨e1 + i 1, i 0, []⟩
    | none => .ok ⟨e1 + i 1, i 0, []⟩

/-- `typemax(Int)`, the default `count`. -/
def countMax : I := imaxval

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1067-1102`, for one pattern: the new `rs`, the processed `r`, and
the new `i`. -/
def replaceOnce (p : Pat) (s repl : List UInt8) (start e1 count n : I) (r : Rng) (i0 : I) :
    SM (Rng × Rng × I) := do
  let j := r.j
  let k := r.k
  if e1.val < j.val then return (r, r, i0)
  if i0 = start ∨ i0.val ≤ k.val then
    -- copy out preserved portion: unsafe_write(io, pointer(str, i), UInt(j-i))
    let nbytes ← liftE (toU (j - i0).val)
    let _ ← unsafeWriteIO ((s.drop (i0.val - 1).toNat).take nbytes.val.toNat)
    -- copy out replacement string
    let _ ← substStep ⟨s, r.md, []⟩ repl
  let (i1, k1) ←
    if k.val < j.val then
      if j = e1 then return (r, r, j)
      pure (j, j + i 1)
    else pure (k + i 1, k + i 1)
  if n = count then return (r, r, i1)
  let r' ← if j.val < k1.val then liftE (findnextRe p s e1 k1) else pure r
  return (r', r, i1)

/-- The loop of `_replace_finish`, `base/strings/util.jl:1052-1063`; returns `i`. -/
def finishLoop (p : Pat) (s repl : List UInt8) (start e1 count : I) : Nat → I → Rng → I → SM I
  | 0, _, _, i0 => pure i0
  | f + 1, n, r, i0 => do
    if count.val < n.val then return i0
    let (r', rr, i1) ← replaceOnce p s repl start e1 count n r i0
    if e1.val ≤ rr.j.val then return i1
    finishLoop p s repl start e1 count f (n + i 1) r' i1

/-- `_replace_finish(io, str, count, e1, patterns, replaces, rs)`,
`base/strings/util.jl:1052-1064`. -/
def replaceFinish (p : Pat) (s repl : List UInt8) (e1 : I) (r : Rng) : SM Unit := do
  let i1 ← finishLoop p s repl (i 1) e1 countMax (s.length + 2) (i 1) r (i 1)
  -- write(io, SubString(str, i))
  let _ ← unsafeWriteIO (s.drop (i1.val - 1).toNat)

/-- `replace(io, s, r => repl)` with `count = typemax(Int)`: `base/strings/util.jl:1183`,
`_replace_(io, str, pat_repl, count)` (`1105-1116`). -/
def replaceIO (p : Pat) (s repl : List UInt8) : SM Unit := do
  let e1 := i (s.length + 1)
  let r ← liftE (findnextRe p s e1 (i 1))
  if e1.val < r.j.val then
    let _ ← unsafeWriteIO s
    return
  replaceFinish p s repl e1 r

/-- `floor(Int, 1.2 * n)` in `Float64` arithmetic for `0 ≤ n < 2^53`: the double `1.2` is
`5404319552844595 / 2^52`, and the product is rounded to 53 significant bits, ties to
even. -/
def floor12 (n : Nat) : Nat :=
  let p := n * 5404319552844595
  let b := bitLength 128 p
  if b ≤ 53 then p / 2 ^ 52
  else
    let sh := b - 53
    let q := p / 2 ^ sh
    let rm := p % 2 ^ sh
    let half := 2 ^ (sh - 1)
    let q := if half < rm ∨ (rm = half ∧ q % 2 = 1) then q + 1 else q
    q * 2 ^ sh / 2 ^ 52

/-- `replace(s, r => repl)`: `base/strings/util.jl:1186`, `_replace_(str, pat_repl, count)`
(`1119-1131`): the bytes of the returned `String`. -/
def replaceStr (p : Pat) (s repl : List UInt8) : Except IOErr (List UInt8) := do
  let e1 := i (s.length + 1)
  let r ← findnextRe p s e1 (i 1)
  if e1.val < r.j.val then return s
  let out ← iobufferEmpty (some true) (some true) none (some true) (2 ^ 63 - 1)
    (some (floor12 s.length))
  match (replaceFinish p s repl e1 r) (.buf out) with
  | .error e _ => .error e
  | .ok _ (.other _) => .error (.jl (.methodError "takestring!"))
  | .ok _ (.buf io) =>
    match takestring io with
    | .ok bs _ => .ok bs
    | .error e _ => .error e

/-- ASCII text. -/
def isAscii (s : List UInt8) : Bool := s.all (· < 128)

end JuliaLean.RegexUnicode.Subst
