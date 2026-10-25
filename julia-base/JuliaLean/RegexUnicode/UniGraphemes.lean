import JuliaLean.RegexUnicode.UniBasic
import JuliaLean.Strings.Theory

/-!
# Grapheme segmentation and `titlecase`, `base/strings/unicode.jl:723-890` and
`stdlib/Unicode/src/Unicode.jl:186-216`

Models of `isgraphemebreak!`, `titlecase(s; wordsep, strict)`, the
`GraphemeIterator` (`iterate`, `length`, `collect`) and `graphemes(s, m:n)`
(master `bbfa0ce4150`). `utf8proc_grapheme_break_stateful` is the primitive
`Utf8proc.gbStateful`. `for c in s` in `titlecase` iterates `chars s`; the grapheme
loops call `iterate(s, i)` directly.

Every loop takes the functions it calls (`isgraphemebreak!`, `titlecase(c)`,
`iterate(s, i)`, `s[i]`, ...) as arguments, and the Julia-level definitions apply it
to the concrete ones. The loops then unfold without evaluating those calls.
-/

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-- `isgraphemebreak!(state, c1, c2)`, `base/strings/unicode.jl:844-851`: a malformed
character resets the state and breaks; otherwise the `ccall` converts both characters
with `UInt32(c)` (`base/char.jl:158-171`, which on master converts overlong encodings;
1.13.2 throws `InvalidCharError` for them). Returns the result and the new `state[]`. -/
def isgraphemebreakBang (P : Utf8proc) (st : Int32) (c1 c2 : UInt32) : UJl (Bool × Int32) :=
  if ismalformed c1 || ismalformed c2 then .ok (true, 0)
  else
    match codepoint c1 with
    | .error e => .error (.str e)
    | .ok u1 =>
      match codepoint c2 with
      | .error e => .error (.str e)
      | .ok u2 => .ok (P.gbStateful st u1 u2)

/-- Prepend to a result. -/
def consM {α : Type} (c : α) : UJl (List α) → UJl (List α)
  | .ok r => .ok (c :: r)
  | .error e => .error e

/-- The type of `isgraphemebreak!(state, c1, c2)`: old `state[]`, `c1`, `c2` to the
result and the new `state[]`. -/
abbrev GbFn := Int32 → UInt32 → UInt32 → UJl (Bool × Int32)

/-! ## `titlecase` -/

/-- The loop of `titlecase(s; wordsep, strict)`, `base/strings/unicode.jl:723-741`:
the characters printed to `b`. `gb` is `isgraphemebreak!`, `tc` is `titlecase(c)`,
`lc` is `lowercase(c)`. `wordsep` is a pure predicate (any Julia function returning
`Bool` without side effects). -/
def titleLoop (gb : GbFn) (tc lc : UInt32 → UJl UInt32) (wordsep : UInt32 → Bool)
    (strict : Bool) : List UInt32 → Bool → Int32 → UInt32 → UJl (List UInt32)
  | [], _, _, _ => .ok []
  | c :: cs, startword, st, c0 =>
    match gb st c0 c with
    | .error e => .error e
    | .ok (b, st) =>
      if b && wordsep c then consM c (titleLoop gb tc lc wordsep strict cs true st c)
      else
        let out : UJl UInt32 := if startword then tc c else if strict then lc c else .ok c
        match out with
        | .error e => .error e
        | .ok c' => consM c' (titleLoop gb tc lc wordsep strict cs false st c)

/-- `titlecase` on the characters `cs` of `s`: `print(b, c)` writes the bytes of `c`
and `takestring!(b)` returns them. `c0 = eltype(s)(0x00000000)` is the bit pattern `0`. -/
def titlecaseOf (gb : GbFn) (tc lc : UInt32 → UJl UInt32) (wordsep : UInt32 → Bool)
    (strict : Bool) (cs : List UInt32) : UJl JStr :=
  match titleLoop gb tc lc wordsep strict cs true 0 0 with
  | .error e => .error e
  | .ok cs => liftS (stringOfChars cs)

/-- `titlecase(s; wordsep, strict)`, `base/strings/unicode.jl:723-741`. -/
def titlecaseStr (P : Utf8proc) (wordsep : UInt32 → Bool) (strict : Bool) (s : JStr) :
    UJl JStr :=
  titlecaseOf (isgraphemebreakBang P) (titlecaseChar P) (lowercaseChar P) wordsep strict
    (chars s)

/-- The word separators of the docstring (`base/strings/unicode.jl:700-704`): character
`k` is a separator when it begins a new grapheme (`isgraphemebreak!` along the string)
and `wordsep` holds for it. -/
def sepFlags (gb : GbFn) (wordsep : UInt32 → Bool) :
    List UInt32 → Int32 → UInt32 → UJl (List Bool)
  | [], _, _ => .ok []
  | c :: cs, st, c0 =>
    match gb st c0 c with
    | .error e => .error e
    | .ok (b, st) => consM (b && wordsep c) (sepFlags gb wordsep cs st c)

/-- The documented result: a character that is not a separator and is first or follows a
separator starts a word and becomes `titlecase(c)` (`tc`); every other character is
kept. `prev` is "first, or after a separator". -/
def wordStartMap (tc : UInt32 → UJl UInt32) : List UInt32 → List Bool → Bool → UJl (List UInt32)
  | c :: cs, f :: fs, prev =>
    if f then consM c (wordStartMap tc cs fs true)
    else if prev then
      match tc c with
      | .error e => .error e
      | .ok c' => consM c' (wordStartMap tc cs fs false)
    else consM c (wordStartMap tc cs fs false)
  | _, _, _ => .ok []

/-- `wordStartMap` applied to the separators of the characters `cs`, as a String. -/
def titleSpecOf (gb : GbFn) (tc : UInt32 → UJl UInt32) (wordsep : UInt32 → Bool)
    (cs : List UInt32) : UJl JStr :=
  match sepFlags gb wordsep cs 0 0 with
  | .error e => .error e
  | .ok fl =>
    match wordStartMap tc cs fl true with
    | .error e => .error e
    | .ok cs => liftS (stringOfChars cs)

/-- The documented `titlecase(s; wordsep, strict=false)`. -/
def titleSpec (P : Utf8proc) (wordsep : UInt32 → Bool) (s : JStr) : UJl JStr :=
  titleSpecOf (isgraphemebreakBang P) (titlecaseChar P) wordsep (chars s)

/-- Property (`titlecase` docstring, `base/strings/unicode.jl:697-722`: with
`strict=false` the characters other than the first of each word are left unchanged):
for every utf8proc table, every `wordsep` and every string, `titlecase(s; wordsep,
strict=false)` is `s` with exactly the word-initial characters replaced by
`titlecase(c)`. -/
def TitlecaseNonstrict : Prop :=
  ∀ (P : Utf8proc) (wordsep : UInt32 → Bool) (s : JStr),
    titlecaseStr P wordsep false s = titleSpec P wordsep s

/-! ## Grapheme iteration -/

/-- The calls the grapheme functions make on one string `s`. -/
structure GOps where
  /-- `iterate(s, i)` -/
  it : JInt64 → Option (UInt32 × JInt64)
  /-- `s[i]` -/
  gi : JInt64 → SJl UInt32
  /-- `nextind(s, i)` -/
  nx : JInt64 → SJl JInt64
  /-- `SubString(s, i, j)` -/
  sub : JInt64 → JInt64 → SJl JSub
  /-- `isgraphemebreak!` -/
  gb : GbFn
  /-- `ncodeunits(s)` -/
  ncu : JInt64
  /-- `lastindex(s)` -/
  ilast : JInt64
  /-- Iteration bound: every loop advances the index, so `ncodeunits(s) + 1` steps
  reach the end. -/
  fuel : Nat

/-- `lastindex(s::String) = thisind(s, ncodeunits(s))`, `base/strings/string.jl:249`:
the index `thisind` returns (it cannot throw: `ncodeunits(s)` is in bounds or `0`). -/
def lastOf : SJl JInt64 → JInt64
  | .ok j => j
  | .error _ => ix 0

/-- The calls on a `String` `s` with utf8proc table `P`. -/
def gops (P : Utf8proc) (s : JStr) : GOps where
  it := iterate s
  gi := getindex s
  nx := nextind s
  sub := fun i j => substring s i j
  gb := isgraphemebreakBang P
  ncu := ncodeunits s
  ilast := lastOf (thisind s (ncodeunits s))
  fuel := s.bytes.length + 1

/-- The `while` loop of `iterate(g::GraphemeIterator, i_)`,
`base/strings/unicode.jl:882-887`, from `j`, `k` with previous character `c0`. The
`::NTuple{2,Any}` assertion throws `TypeError` when `iterate` returns `nothing`.
Returns `state[]`, `j`, `k`. -/
def gIterLoop (O : GOps) : Nat → Int32 → UInt32 → JInt64 → JInt64 →
    UJl (Int32 × JInt64 × JInt64)
  | 0, _, _, _, _ => .error .fuel
  | f + 1, st, c0, j, k =>
    if k.val ≤ O.ncu.val then
      match O.it k with
      | none => .error .typeError
      | some (c, l) =>
        match O.gb st c0 c with
        | .error e => .error e
        | .ok (true, st) => .ok (st, j, k)
        | .ok (false, st) => gIterLoop O f st c k l
    else .ok (st, j, k)

/-- `iterate(g::GraphemeIterator, (statei, i))`, `base/strings/unicode.jl:874-890`. -/
def gIterate (O : GOps) (st : Int32) (i : JInt64) : UJl (Option (JSub × Int32 × JInt64)) :=
  match O.it i with
  | none => .ok none
  | some (c0, k) =>
    match gIterLoop O O.fuel st c0 i k with
    | .error e => .error e
    | .ok (st, j, k) =>
      match O.sub i j with
      | .error e => .error (.str e)
      | .ok g => .ok (some (g, st, k))

/-- The elements of `collect(graphemes(s))`: `iterate` from `(Int32(0), firstindex(s))`
until `nothing`. -/
def gCollectFrom (O : GOps) : Nat → Int32 → JInt64 → UJl (List JSub)
  | 0, _, _ => .error .fuel
  | f + 1, st, i =>
    match gIterate O st i with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (g, st, i)) => consM g (gCollectFrom O f st i)

/-- `collect(graphemes(s))`. -/
def gCollect (P : Utf8proc) (s : JStr) : UJl (List JSub) :=
  gCollectFrom (gops P s) (s.bytes.length + 1) 0 (ix 1)

/-- The loop of `length(g::GraphemeIterator)`, `base/strings/unicode.jl:863-871`:
`for c in g.s` calls `iterate(s, i)` from `firstindex(s) = 1` until `nothing`. -/
def gLengthLoop (O : GOps) : Nat → Int32 → UInt32 → JInt64 → JInt64 → UJl JInt64
  | 0, _, _, _, _ => .error .fuel
  | f + 1, st, c0, i, n =>
    match O.it i with
    | none => .ok n
    | some (c, i) =>
      match O.gb st c0 c with
      | .error e => .error e
      | .ok (b, st) => gLengthLoop O f st c i (n + bInt b)

/-- `length(graphemes(s))`. -/
def gLength (P : Utf8proc) (s : JStr) : UJl JInt64 :=
  gLengthLoop (gops P s) (s.bytes.length + 1) 0 0 (ix 1) (ix 0)

/-! ## `graphemes(s, m:n)`, `stdlib/Unicode/src/Unicode.jl:186-216` -/

/-- The first `while` loop (`:194-200`): `i ≤ ilast && count < m`. `@inbounds s[i]` reads
a valid index (every `i` is reached by `nextind` from `1`). Returns `state[]`, `c0`,
`count`, `i`, `iprev`. -/
def gFirst (O : GOps) (m : JInt64) :
    Nat → Int32 → UInt32 → JInt64 → JInt64 → JInt64 →
    UJl (Int32 × UInt32 × JInt64 × JInt64 × JInt64)
  | 0, _, _, _, _, _ => .error .fuel
  | f + 1, st, c0, count, i, iprev =>
    if decide (i.val ≤ O.ilast.val) && decide (count.val < m.val) then
      match O.gi i with
      | .error e => .error (.str e)
      | .ok c =>
        match O.gb st c0 c with
        | .error e => .error e
        | .ok (b, st) =>
          let count := count + bInt b
          match O.nx i with
          | .error e => .error (.str e)
          | .ok i' => gFirst O m f st c count i' i
    else .ok (st, c0, count, i, iprev)

/-- The second `while` loop (`:203-209`). Returns `count` and `iprev`. -/
def gSecond (O : GOps) (n : JInt64) :
    Nat → Int32 → UInt32 → JInt64 → JInt64 → JInt64 → UJl (JInt64 × JInt64)
  | 0, _, _, _, _, _ => .error .fuel
  | f + 1, st, c0, count, i, iprev =>
    if i.val ≤ O.ilast.val then
      match O.gi i with
      | .error e => .error (.str e)
      | .ok c =>
        match O.gb st c0 c with
        | .error e => .error e
        | .ok (b, st) =>
          let count := count + bInt b
          if count.val > n.val then .ok (count, iprev)
          else
            match O.nx i with
            | .error e => .error (.str e)
            | .ok i' => gSecond O n f st c count i' i
    else .ok (count, iprev)

/-- The body of `graphemes(s, m:n)` for `m, n = Int(first(r)), Int(last(r))`. `@view
s[a:b]` is `SubString(s, a, b)`. -/
def graphemesRangeOf (O : GOps) (m n : JInt64) : UJl JSub :=
  if !decide (m.val > 0) then .error (.str (.jl (.argumentError "starting index is not ≥ 1")))
  else if n.val < m.val then liftS (O.sub (ix 1) (ix 0))
  else
    match gFirst O m O.fuel 0 0 (ix 0) (ix 1) (ix 1) with
    | .error e => .error e
    | .ok (st, c0, count, i, iprev) =>
      let start := iprev
      if count.val < m.val then .error (.str boundsErr)
      else
        match gSecond O n O.fuel st c0 count i iprev with
        | .error e => .error e
        | .ok (count, iprev) =>
          if count.val < n.val then .error (.str boundsErr)
          else liftS (O.sub start iprev)

/-- `graphemes(s, m:n)`, `stdlib/Unicode/src/Unicode.jl:186-216`. -/
def graphemesRange (P : Utf8proc) (s : JStr) (m n : JInt64) : UJl JSub :=
  graphemesRangeOf (gops P s) m n

/-- Documented behaviour of `utf8proc_grapheme_break_stateful` with state initialized
to `0` (`base/strings/unicode.jl:839-843`): a grapheme boundary follows a control
character (rule GB4), so there is one between `'\0'` and any `c`, and the state that
call leaves is the initial state for `c`. -/
def GbInit (P : Utf8proc) : Prop :=
  ∀ u : UInt32, (P.gbStateful 0 0 u).1 = true ∧
    ∀ v, P.gbStateful (P.gbStateful 0 0 u).2 u v = P.gbStateful 0 u v

/-- Property (`graphemes(s, m:n)` docstring, `stdlib/Unicode/src/Unicode.jl:152-185`: the
`m`-th through `n`-th graphemes of `s`): for `1 ≤ m ≤ n ≤ length(graphemes(s))` the
result is a SubString of `s` whose bytes are the concatenation of elements `m` to `n`
of `collect(graphemes(s))`; for `n > length(graphemes(s))` it throws `BoundsError`. -/
def GraphemesRangeProp : Prop :=
  ∀ P : Utf8proc, GbInit P → ∀ (s : JStr) (m n : JInt64), 1 ≤ m.val → m.val ≤ n.val →
    ∃ G len, gCollect P s = .ok G ∧ gLength P s = .ok len ∧ len.val = G.length ∧
      (n.val ≤ len.val → ∃ r, graphemesRange P s m n = .ok r ∧ r.str = s ∧
        r.view.bytes = (((G.drop (m.val.toNat - 1)).take ((n.val - m.val).toNat + 1)).map
          (fun g => g.view.bytes)).flatten) ∧
      (len.val < n.val → graphemesRange P s m n = .error (.str boundsErr))

/-! ## Observed behaviour -/

/-- Letters `a`–`z`, `A`–`Z` have category `Ll` (2); every pair is a grapheme break. -/
def letterTbl : Utf8proc :=
  { idCase with
    category := fun u => if (0x61 ≤ u.toNat ∧ u.toNat ≤ 0x7a) ∨ (0x41 ≤ u.toNat ∧ u.toNat ≤ 0x5a)
      then 2 else 0 }

/-- `titlecase("a\xffb") == "A\xffB"` (default `wordsep = !isletter`, `strict = true`):
the malformed character is a separator, so `titlecase` never converts it, whereas
`uppercase("a\xffb")` throws. -/
theorem titlecase_affb :
    titlecaseStr letterTbl (fun c => !isletterChar letterTbl c) true strAffB =
      .ok ⟨[0x41, 0xff, 0x42], by decide⟩ := by rfl

end JuliaLean.RegexUnicode.Uni
