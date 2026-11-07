import JuliaLean.Proofs.base.strings.unicode.functions
import JuliaLean.stdlib.Unicode.src.Unicode
import JuliaLean.Proofs.base.strings.string.indices

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
