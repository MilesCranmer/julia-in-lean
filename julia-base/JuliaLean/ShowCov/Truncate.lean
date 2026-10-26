import JuliaLean.ShowCov.Basic

/-!
# ANSI-aware truncation: `ANSIIterator`, `_truncate_at_width_or_chars`,
# `type_depth_limit` (`base/show.jl:79-135, 2726-2816`)

Strings are valid UTF-8 `String`s, modelled as their `Char` lists; a
character's string index is its 1-based byte offset (`Char.utf8Size` bytes
per character). `tw` is `textwidth(::Char)` (a Unicode table, so a
parameter).
-/

namespace JuliaLean.ShowCov.Truncate

open JuliaLean.ShowCov

/-- An element produced by `ANSIIterator`: a character or an `ANSIDelimiter`
holding the matched escape sequence. -/
inductive Tok where
  | ch (c : Char)
  | ansi (del : List Char)
  deriving DecidableEq, Repr

/-- `ncodeunits` of a token (`ncodeunits(c::ANSIDelimiter) = ncodeunits(c.del)`,
`base/show.jl:85`). -/
def Tok.ncu : Tok → Nat
  | .ch c => c.utf8Size
  | .ansi d => (d.map Char.utf8Size).sum

/-- `textwidth(::ANSIDelimiter) = 0`, `base/show.jl:86`. -/
def Tok.width (tw : Char → Nat) : Tok → Nat
  | .ch c => tw c
  | .ansi _ => 0

def inRange (c : Char) (lo hi : Nat) : Bool := lo ≤ c.toNat && c.toNat ≤ hi

/-- Longest run of characters in `[lo, hi]` at the front. -/
def spanRange (lo hi : Nat) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if inRange c lo hi then
      let (a, b) := spanRange lo hi cs
      (c :: a, b)
    else ([], c :: cs)

/-- One match of `ansi_regex` (`base/show.jl:79`) at the front of a nonempty
string: ESC followed by one of `@`..`Z` or `\`..`_`; or ESC `[`, parameter bytes
0x30-0x3F, intermediate bytes 0x20-0x2F and a final byte 0x40-0x7E; otherwise
any single character (`(?s).`). Returns the matched token and the rest. -/
def ansiMatch : List Char → Option (Tok × List Char)
  | [] => none
  | c :: cs =>
    let single := some (Tok.ch c, cs)
    if c.toNat = 0x1B then
      match cs with
      | d :: ds =>
        if inRange d 0x40 0x5A || inRange d 0x5C 0x5F then some (.ansi [c, d], ds)
        else if d = '[' then
          let (p, r1) := spanRange 0x30 0x3F ds
          let (q, r2) := spanRange 0x20 0x2F r1
          match r2 with
          | f :: r3 => if inRange f 0x40 0x7E then some (.ansi ([c, d] ++ p ++ q ++ [f]), r3) else single
          | [] => single
        else single
      | [] => single
    else single

/-- `ANSIIterator(s)` (`base/show.jl:92-101`): the regex matches of `s` in
order; every character belongs to exactly one match. Each match consumes at
least one character, so `length(s)` rounds suffice. -/
def ansiTokensF : Nat → List Char → List Tok
  | 0, _ => []
  | fuel + 1, s =>
    match ansiMatch s with
    | some (t, r) => t :: ansiTokensF fuel r
    | none => []

def ansiTokens (s : List Char) : List Tok := ansiTokensF s.length s

/-- `IteratorSize(::Type{<:ANSIIterator}) = SizeUnknown()` and
`eltype(::Type{<:ANSIIterator}) = Pair{Int, Union{Char,ANSIDelimiter}}`,
`base/show.jl:94-95`. -/
def iteratorSizeANSI : String := "SizeUnknown"
def eltypeANSI : String := "Pair{Int, Union{Char,ANSIDelimiter}}"

/-- Pair each token with its 1-based starting byte index (`i => c`). -/
def indexed : Nat → List Tok → List (Nat × Tok)
  | _, [] => []
  | i, t :: ts => (i, t) :: indexed (i + t.ncu) ts

/-- `pairs(str)` as tokens: every character on its own. -/
def charTokens (s : List Char) : List Tok := s.map Tok.ch

/-- `textwidth(I::ANSIIterator) = mapreduce(textwidth∘last, +, I; init=0)`,
`base/show.jl:102`. -/
def ansiWidth (tw : Char → Nat) (s : List Char) : Nat :=
  ((ansiTokens s).map (Tok.width tw)).sum

/-- `textwidth(s)` of a plain string. -/
def textwidth (tw : Char → Nat) (s : List Char) : Nat := (s.map tw).sum

/-- The characters of `str` whose start index is at most `idx`
(`SubString(str, 1, idx)` when `idx` is a character start or `0`). -/
def prefixUpTo (str : List Char) (idx : Nat) : List Char :=
  let rec go : Nat → List Char → List Char
    | _, [] => []
    | i, c :: cs => if i ≤ idx then c :: go (i + c.utf8Size) cs else []
  go 1 str

/-- The character starting at byte index `idx`, if any. -/
def charAt (str : List Char) (idx : Nat) : Option Char :=
  let rec go : Nat → List Char → Option Char
    | _, [] => none
    | i, c :: cs => if i = idx then some c else go (i + c.utf8Size) cs
  go 1 str

/-- `prevind(str, idx)`: the start of the character before the one at `idx`
(0 if none). -/
def prevind (str : List Char) (idx : Nat) : Nat :=
  let rec go : Nat → Nat → List Char → Nat
    | _, prev, [] => prev
    | i, prev, c :: cs => if i ≥ idx then prev else go (i + c.utf8Size) i cs
  go 1 0 str

/-- `lastindex(str)`: start of the last character (0 for `""`). -/
def lastindex (str : List Char) : Nat :=
  let rec go : Nat → Nat → List Char → Nat
    | _, last, [] => last
    | i, _, c :: cs => go (i + c.utf8Size) i cs
  go 1 0 str

/-- The reset sequence `"\033[0m"`. -/
def resetSeq : List Char := ['\x1b', '[', '0', 'm']

/-- Loop state of `_truncate_at_width_or_chars`. -/
structure TState where
  wid : Nat
  truncidx : Nat
  lastidx : Nat
  stop : Bool
  needANSIend : Bool
  deriving DecidableEq, Repr

/-- `c != "\033[0m"` for an `ANSIDelimiter` `c` (`base/show.jl:114`):
`ANSIDelimiter` is not an `AbstractString` and has no `==` method with
`String`, so `==` falls back to `===`, which is `false`. -/
def ansiDelimNeString (_del : List Char) : Bool := true

/-- The `for (i, c) in I` loop of `_truncate_at_width_or_chars`,
`base/show.jl:112-124`. -/
def truncLoop (tw : Char → Nat) (width truncwidth : Int) (chars : List Char) :
    TState → List (Nat × Tok) → TState
  | st, [] => st
  | st, (i, t) :: rest =>
    match t with
    | .ansi del =>
      let st := { st with
        needANSIend := if st.truncidx = 0 then ansiDelimNeString del else st.needANSIend
        lastidx := i + t.ncu - 1 }
      truncLoop tw width truncwidth chars st rest
    | .ch c =>
      if st.stop then st else
      let wid := st.wid + tw c
      let truncidx := if st.truncidx = 0 ∧ (wid : Int) > width - truncwidth then st.lastidx else st.truncidx
      let st := { st with wid := wid, truncidx := truncidx, lastidx := i }
      if c ∈ chars then st else
      truncLoop tw width truncwidth chars { st with stop := decide ((wid : Int) ≥ width) } rest

/-- `_truncate_at_width_or_chars(ignore_ANSI, str, width, rpad, chars, truncmark)`,
`base/show.jl:104-135`. -/
def truncateAt (tw : Char → Nat) (ignoreANSI : Bool) (str : List Char) (width : Int)
    (rpad : Bool := false) (chars : List Char := ['\r', '\n']) (truncmark : List Char := ['…']) :
    List Char :=
  let truncwidth : Int := textwidth tw truncmark
  if width ≤ 0 ∨ width < truncwidth then [] else
  let toks := if ignoreANSI then ansiTokens str else charTokens str
  let st := truncLoop tw width truncwidth chars ⟨0, 0, 0, false, false⟩ (indexed 1 toks)
  if st.lastidx = 0 then (if rpad then List.replicate width.toNat ' ' else []) else
  let lastidx := match charAt str st.lastidx with
    | some c => if c ∈ chars then prevind str st.lastidx else st.lastidx
    | none => st.lastidx
  let ansiEnd := if st.needANSIend then resetSeq else []
  let pad := if rpad then List.replicate (width - st.wid).toNat ' ' else []
  let truncidx := if st.truncidx = 0 then lastidx else st.truncidx
  if lastidx < lastindex str then prefixUpTo str truncidx ++ ansiEnd ++ truncmark ++ pad
  else str ++ ansiEnd ++ pad

/-! ## `type_depth_limit` -/

/-- Quote state bits: `st_backslash = 1`, `st_squote = 2`, `st_dquote = 4`
(`base/show.jl:2732`), with `stateis`, `quoted`, `enter`, `leave`
(`base/show.jl:2734-2737`). -/
structure QState where
  backslash : Bool
  squote : Bool
  dquote : Bool
  deriving DecidableEq, Repr

def QState.quoted (q : QState) : Bool := q.squote || q.dquote

/-- First pass: depth at each token (in order), per-level widths and counts,
and the total width, `base/show.jl:2738-2783`. `widthAt` and `levelcount` are
indexed from depth 1. Depths are `Int` (Julia stores them as `Int16`). A
`levelcount[depth]` update at depth `< 1` is a `BoundsError`. -/
structure Pass1 where
  depth : Int
  widthAt : List Nat
  levelcount : List Nat
  strwid : Nat
  q : QState
  depths : List Int
  deriving DecidableEq, Repr

def bumpAt (l : List Nat) (k : Nat) (d : Nat) : List Nat :=
  l.modify k (· + d)

def pass1Step (tw : Char → Nat) (s : Pass1) : Tok → R Pass1
  | .ansi _ => .ok { s with depths := s.depths ++ [s.depth] }
  | .ch c => do
    let q := s.q
    let q :=
      if c = '\\' ∧ q.quoted then { q with backslash := true }
      else if c = '\'' then
        (if q.backslash || q.dquote then q
         else if q.squote then { q with squote := false }
         else { q with squote := true })
      else if c = '"' then
        (if q.backslash || q.squote then q
         else if q.dquote then { q with dquote := false }
         else { q with dquote := true })
      else q
    let depth := if c = '}' ∧ !q.quoted then s.depth - 1 else s.depth
    let wid := tw c
    let strwid := s.strwid + wid
    let widthAt := if depth > 0 then bumpAt s.widthAt (depth.toNat - 1) wid else s.widthAt
    let depths := s.depths ++ [depth]
    let (depth, widthAt, levelcount) ←
      if c = '{' ∧ !q.quoted then do
        let depth := depth + 1
        let (widthAt, levelcount) :=
          if depth > (widthAt.length : Int) then (widthAt ++ [0], s.levelcount ++ [0]) else (widthAt, s.levelcount)
        if depth < 1 then .error .boundsError else
        pure (depth, widthAt, bumpAt levelcount (depth.toNat - 1) 1)
      else pure (depth, widthAt, s.levelcount)
    let q := if c ≠ '\\' ∧ q.backslash then { q with backslash := false } else q
    pure ⟨depth, widthAt, levelcount, strwid, q, depths⟩

def pass1 (tw : Char → Nat) (toks : List Tok) : R Pass1 :=
  toks.foldlM (pass1Step tw) ⟨0, [], [], 0, ⟨false, false, false⟩, []⟩

/-- The `while strwid > n` search for `limit_at`, `base/show.jl:2784-2795`, with
fuel `length(width_at) + 1` (each iteration lowers `limit_at`). -/
def limitSearch (widthAt levelcount : List Nat) (n : Int) : Nat → Int → Int → Int
  | 0, limitAt, _ => limitAt
  | fuel + 1, limitAt, strwid =>
    if strwid > n then
      let limitAt := limitAt - 1
      if limitAt ≤ 1 then limitAt else
      let strwid := strwid - widthAt.getD (limitAt.toNat - 1) 0 + levelcount.getD (limitAt.toNat - 1) 0
      let strwid := if limitAt < widthAt.length then strwid - levelcount.getD limitAt.toNat 0 else strwid
      limitSearch widthAt levelcount n fuel limitAt strwid
    else limitAt

/-- Second pass: keep tokens shallower than `limit_at`, writing `…` on entering
`limit_at`, `base/show.jl:2799-2815`. -/
def pass2 (limitAt : Int) : Int → List (Tok × Int) → List Char
  | _, [] => []
  | prev, (t, di) :: rest =>
    let kept := if di < limitAt then (match t with | .ansi d => d | .ch c => [c]) else []
    let mark := if di > prev ∧ di = limitAt then ['…'] else []
    kept ++ mark ++ pass2 limitAt di rest

/-- `type_depth_limit(str, n; maxdepth)`, `base/show.jl:2726-2816`. -/
def typeDepthLimit (tw : Char → Nat) (str : List Char) (n : Int) (maxdepth : Option Int := none) :
    R (List Char) := do
  let toks := ansiTokens str
  let p ← pass1 tw toks
  let limitAt := match maxdepth with
    | none => limitSearch p.widthAt p.levelcount n (p.widthAt.length + 1) (p.widthAt.length + 1) p.strwid
    | some d => d
  pure (pass2 limitAt 0 (toks.zip p.depths))

end JuliaLean.ShowCov.Truncate
