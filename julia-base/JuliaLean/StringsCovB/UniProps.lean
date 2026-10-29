import JuliaLean.StringsCovB.Uni
import JuliaLean.StringsCovB.AnnProps
import JuliaLean.RegexUnicode.UniGraphProof

/-!
# Properties of the `base/strings/unicode.jl` models
-/

namespace JuliaLean.StringsCovB.Uni

open JuliaLean JuliaLean.Strings
open JuliaLean.RegexUnicode.Uni (Utf8proc UErr UJl GbInit liftS lowercaseChar uppercaseChar titlecaseChar
  categoryCode unsafeCodepoint isletterChar isgraphemebreakBang NormKw normalizeFlags STABLE COMPOSE
  DECOMPOSE COMPAT)

/-! ## `isvalid` -/

/-- `isvalid(T, c)` for an unsigned or nonnegative integer is exactly "a Unicode scalar
value" (`0:0xd7ff` or `0xe000:0x10ffff`, `base/strings/unicode.jl:33-55`); a negative
integer throws; the `AbstractChar` forms agree and reject malformed and overlong
characters; `isvalid(Union{}, x)` is `false` and the vararg form throws. -/
def IsvalidContract : Prop :=
  (∀ c : Nat, isvalidU c = true ↔ c ≤ 0x10ffff ∧ ¬ (0xd800 ≤ c ∧ c ≤ 0xdfff)) ∧
  (∀ c : Int, 0 ≤ c → isvalidI c = .ok (isvalidU c.toNat)) ∧
  (∀ c : Int, c < 0 → ∃ e, isvalidI c = .error e) ∧
  (∀ c, isvalidTC c = isvalidC c) ∧
  (∀ c, isvalidC c = true → ismalformed c = false ∧ isoverlong c = false) ∧
  (∀ (x : Nat), isvalidUnion x = false) ∧
  (∀ (l : List Nat), ∃ e, isvalidUnionSlurp l = .error e)

theorem isvalidContract : IsvalidContract := by
  refine ⟨fun c => ?_, fun c h => ?_, fun c h => ⟨.inexactError "UInt64", ?_⟩, fun _ => rfl, fun c h => ?_, fun _ => rfl,
    fun _ => ⟨_, rfl⟩⟩
  · simp only [isvalidU, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · simp only [isvalidI]; rw [if_neg (by omega)]
  · simp only [isvalidI]; rw [if_pos h]
  · simp only [isvalidC, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1.1, h.1.2⟩

/-! ## `utf8proc_map` -/

/-- `utf8proc_map` never reads beyond the buffer it allocated: the second
decomposition (into the buffer sized by the first) returns at most the number of
code points the buffer holds, for every `chartransform` (`normalize` documents
`chartransform` as an arbitrary function). -/
def Utf8procMapInBounds : Prop :=
  ∀ (σ : Type) (P : Utf8proc) (E : Ext) (s : JStr) (options : Nat) (cb : σ → UInt32 → Int × σ) (st : σ),
    utf8procMap P E s options cb st ≠ .error .outOfBounds

/-- A table in which only U+FDFA has a (compatibility) decomposition, of 18 code
points, and `utf8proc_reencode` succeeds. -/
def tblFDFA : Utf8proc where
  toupper := id
  tolower := id
  totitle := id
  category := fun _ => 0
  gbStateful := fun _ _ _ => (true, 0)
  decomposeChar := fun c _ => .ok (if c = 0xfdfa then List.replicate 18 0x635 else [c])
  combiningClass := fun _ => 0

def ext0 : Ext := ⟨fun _ => 1, fun _ => false, fun _ => false, fun _ => [], fun _ _ => true,
  fun _ _ => .ok []⟩

/-- `"ab"`. -/
def jAb : JStr := ⟨[0x61, 0x62], by decide⟩

/-- A `chartransform` returning its argument for its first two calls and U+FDFA
afterwards (a counter in its state): the second decomposition of `"ab"` has 36 code
points for a buffer of 2. -/
theorem utf8procMapInBounds_refuted : ¬ Utf8procMapInBounds := by
  intro h
  exact h Nat tblFDFA ext0 jAb 0 (fun n c => (if n < 2 then (c.toNat : Int) else 0xfdfa, n + 1)) 0 rfl

/-- `normalize(s, :NFC)` etc. pass the flags of the corresponding keyword calls
(`normalize(s; stable=true)` with `compose`, `decompose=true`, `compat=true`), and any
other symbol throws `ArgumentError`. -/
def NormalizeNfContract : Prop :=
  nfFlags .nfc = normalizeFlags { stable := true } ∧
  nfFlags .nfd = normalizeFlags { stable := true, decompose := true } ∧
  nfFlags .nfkc = normalizeFlags { stable := true, compat := true } ∧
  nfFlags .nfkd = normalizeFlags { stable := true, compat := true, decompose := true } ∧
  (∃ e, nfFlags .other = .error e) ∧
  (∀ P E s nf, normalizeNf P E s nf = match nfFlags nf with
    | .error e => .error (.u (.str (.jl e)))
    | .ok flags => utf8procMap P E s flags (fun (u : Unit) c => ((c.toNat : Int), u)) ())

theorem normalizeNfContract : NormalizeNfContract :=
  ⟨rfl, rfl, rfl, rfl, ⟨_, rfl⟩, fun _ _ _ _ => rfl⟩

/-! ## `textwidth` -/

/-- `textwidth` of a printable ASCII character (`' ':'~'`) is 1, of an ASCII control
character (below `' '`) 0, of a malformed character 1; `textwidth(s)` is the sum over
its characters, so it is nonnegative when `utf8proc_charwidth` is; the `AnnotatedString`
and `AnnotatedChar` forms are those of the underlying `String` and `Char`. -/
def TextwidthContract : Prop :=
  (∀ E c, 0x20 ≤ bswap32 c → bswap32 c < 0x7f → textwidthChar E c = 1) ∧
  (∀ E c, bswap32 c < 0x20 → textwidthChar E c = 0) ∧
  (∀ E c, bswap32 c ≥ 0x7f → ismalformed c = true → textwidthChar E c = 1) ∧
  (∀ E s, (∀ u, 0 ≤ E.charwidth u) → 0 ≤ textwidthStr E s) ∧
  (∀ E (s : Ann.AS), textwidthAS E s = textwidthStr E s.str) ∧
  (∀ E (s : JSub), textwidthSub E s = textwidthStr E s.view) ∧
  (∀ E (c : Ann.AC), textwidthAC E c = textwidthChar E c.char)

theorem textwidthChar_nonneg (E : Ext) (h : ∀ u, 0 ≤ E.charwidth u) (c : UInt32) : 0 ≤ textwidthChar E c := by
  unfold textwidthChar
  dsimp
  split
  · split <;> omega
  · split
    · omega
    · exact h _

theorem foldl_tw_nonneg (E : Ext) (h : ∀ u, 0 ≤ E.charwidth u) :
    ∀ (cs : List UInt32) (acc : Int), 0 ≤ acc → 0 ≤ cs.foldl (fun acc c => acc + textwidthChar E c) acc
  | [], acc, ha => ha
  | c :: cs, acc, ha => foldl_tw_nonneg E h cs _ (Int.add_nonneg ha (textwidthChar_nonneg E h c))

set_option maxRecDepth 10000 in
theorem textwidthContract : TextwidthContract := by
  refine ⟨fun E c h1 h2 => ?_, fun E c h => ?_, fun E c h1 h2 => ?_, fun E s h => foldl_tw_nonneg E h _ 0 (by omega),
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · unfold textwidthChar; dsimp; rw [if_pos h2, if_pos h1]
  · unfold textwidthChar; dsimp
    rw [if_pos (UInt32.lt_trans h (by decide)), if_neg (by
      simp only [GE.ge, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt] at h ⊢
      omega)]
  · unfold textwidthChar
    rw [if_neg (by simp only [UInt32.lt_iff_toNat_lt] at *; simp only [GE.ge, UInt32.le_iff_toNat_le] at h1; omega)]
    rw [if_pos (by simp [h2])]

/-! ## Case mappings of `AnnotatedChar` and `AnnotatedString` -/

/-- `lowercase`, `uppercase` and `titlecase` of an `AnnotatedChar` map the character
and keep its annotations; `uppercase`/`lowercase` of an `AnnotatedString` have the code
units of `uppercase`/`lowercase` of its `String`; the SubString forms are those of
the converted `AnnotatedString`. -/
def CaseAnnotatedContract : Prop :=
  (∀ P c d, lowercaseAC P c = .ok d → RegexUnicode.Uni.lowercaseChar P c.char = .ok d.char ∧ d.anns = c.anns) ∧
  (∀ P c d, uppercaseAC P c = .ok d → RegexUnicode.Uni.uppercaseChar P c.char = .ok d.char ∧ d.anns = c.anns) ∧
  (∀ P c d, titlecaseAC P c = .ok d → RegexUnicode.Uni.titlecaseChar P c.char = .ok d.char ∧ d.anns = c.anns) ∧
  (∀ P s, uppercaseAS P s = Ann.annotatedChartransform (stateless (uppercaseChar P)) s ()) ∧
  (∀ P s, lowercaseAS P s = Ann.annotatedChartransform (stateless (lowercaseChar P)) s ()) ∧
  (∀ P s a, Ann.ofSub s = .ok a → uppercaseSub P s = uppercaseAS P a ∧ lowercaseSub P s = lowercaseAS P a)

theorem caseAC {f : UInt32 → UJl UInt32} (c d : Ann.AC)
    (h : (do let c' ← f c.char; pure (⟨c', c.anns⟩ : Ann.AC) : UJl Ann.AC) = .ok d) :
    f c.char = .ok d.char ∧ d.anns = c.anns := by
  cases hf : f c.char with
  | error e => rw [hf] at h; cases h
  | ok x => rw [hf] at h; cases h; exact ⟨rfl, rfl⟩

theorem caseAnnotatedContract : CaseAnnotatedContract := by
  refine ⟨fun P c d h => caseAC c d h, fun P c d h => caseAC c d h, fun P c d h => caseAC c d h,
    fun _ _ => rfl, fun _ _ => rfl,
    fun P s a h => ?_⟩
  simp only [uppercaseSub, lowercaseSub, h, RegexUnicode.Uni.liftS, bind, Except.bind]
  simp

/-! ## Categories -/

/-- `category_code(x::Integer)` is utf8proc's category for `0 ≤ x ≤ 0x10ffff` and 30
above; with utf8proc's categories in `0:29`, `category_string(c::Char)` never reads
outside `category_strings`; `category_abbrev` is `"Ma"` for malformed characters and
`"In"` beyond `'\U10ffff'`, in both methods; `isassigned(c::Char)` is `0 < code ≤ 29`. -/
def CategoryContract : Prop :=
  (∀ P (x : Int), 0 ≤ x → x ≤ 0x10ffff → categoryCodeInt P x = .ok (P.category (UInt32.ofNat x.toNat))) ∧
  (∀ P (x : Int), 0x10ffff < x → categoryCodeInt P x = .ok 30) ∧
  (∀ P, (∀ u, P.category u ≤ 29) → ∀ c, ∃ k, categoryString P c = some k) ∧
  (∀ P, (∀ u, P.category u ≤ 29) → ∀ x : Int, 0 ≤ x → ∃ k, categoryStringInt P x = .ok k) ∧
  (∀ E c, ismalformed c = true → categoryAbbrev E c = strMa ∧ categoryAbbrevAC E c = .ok strMa) ∧
  (∀ E c, ismalformed c = false → 0xf48fbfbf < c → categoryAbbrev E c = strIn ∧ categoryAbbrevAC E c = .ok strIn) ∧
  (∀ P c, isassignedC P c = (decide (0 < categoryCode P c) && decide (categoryCode P c ≤ 29)))

theorem categoryCode_le (P : Utf8proc) (hP : ∀ u, P.category u ≤ 29) (c : UInt32) : categoryCode P c ≤ 31 := by
  unfold RegexUnicode.Uni.categoryCode
  dsimp
  split
  · split
    · have := hP (unsafeCodepoint c); omega
    · omega
  · omega

theorem categoryContract : CategoryContract := by
  refine ⟨fun P x h1 h2 => ?_, fun P x h => ?_, fun P hP c => ?_, fun P hP x hx => ?_,
    fun E c h => ?_, fun E c h1 h2 => ?_, fun _ _ => rfl⟩
  · unfold categoryCodeInt; rw [if_pos h2, if_pos h1]
  · unfold categoryCodeInt; rw [if_neg (by omega)]
  · have := categoryCode_le P hP c
    unfold categoryString
    rw [if_pos (by simp [categoryStrings]; omega)]
    exact ⟨_, rfl⟩
  · unfold categoryStringInt categoryCodeInt
    by_cases h : x ≤ 0x10ffff
    · rw [if_pos h, if_pos hx]
      have := hP (UInt32.ofNat x.toNat)
      simp only [bind, Except.bind, pure, Except.pure]
      rw [if_pos (by simp [categoryStrings]; omega)]
      exact ⟨_, rfl⟩
    · rw [if_neg h]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [if_pos (by simp [categoryStrings])]
      exact ⟨_, rfl⟩
  · simp [categoryAbbrev, categoryAbbrevAC, h]
  · have : ¬ (c ≤ 0xf48fbfbf) := by
      simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le] at *; omega
    simp [categoryAbbrev, categoryAbbrevAC, h1, this]

/-- `isassigned(c)` answers for every integer `c` (`base/strings/unicode.jl:405`; it is
documented for code points, and `isassigned(0x110000)` is `false`). -/
def IsassignedTotal : Prop := ∀ (P : Utf8proc) (x : Int), ∃ b, isassignedInt P x = .ok b

/-- `isassigned(-1)` throws `InexactError` from `UInt32(-1)` in `category_code`. -/
theorem isassignedTotal_refuted : ¬ IsassignedTotal := by
  intro h
  obtain ⟨b, hb⟩ := h tblFDFA (-1)
  simp [isassignedInt, categoryCodeInt, bind, Except.bind] at hb

/-! ## Character predicates -/

/-- `islowercase`/`isuppercase` are `false` for malformed characters; `iscased` is
"category `Lu`, `Lt` or `Ll`"; every decimal digit is a hex digit; the ASCII
whitespace characters `'\t':'\r'` and `' '` are spaces; `isletter`, `isnumeric`,
`ispunct` and every space at or above `'\ua0'` are printable or separators in the
documented category ranges. -/
def PredicatesContract : Prop :=
  (∀ E c, ismalformed c = true → islowercaseC E c = false ∧ isuppercaseC E c = false) ∧
  (∀ P c, iscasedC P c = true ↔ categoryCode P c = 1 ∨ categoryCode P c = 2 ∨ categoryCode P c = 3) ∧
  (∀ c, isdigitC c = true → isxdigitC c = true) ∧
  (∀ P, ∀ c ∈ [0x09000000, 0x0a000000, 0x0b000000, 0x0c000000, 0x0d000000, 0x20000000], isspaceC P c = true) ∧
  (∀ P c, isletterChar P c = true → isprintC P c = true) ∧
  (∀ P c, isnumericC P c = true → isprintC P c = true) ∧
  (∀ P c, ispunctC P c = true → isprintC P c = true)

theorem predicatesContract : PredicatesContract := by
  refine ⟨fun E c h => by simp [islowercaseC, isuppercaseC, h], fun P c => ?_, fun c h => ?_,
    fun P c hc => ?_, fun P c h => ?_, fun P c h => ?_, fun P c h => ?_⟩
  · simp only [iscasedC, Bool.or_eq_true, beq_iff_eq]; omega
  · simp only [isdigitC, isxdigitC, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h ⊢
    exact Or.inl (Or.inl h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [isspaceC]
  · simp only [RegexUnicode.Uni.isletterChar, isprintC, Bool.and_eq_true, decide_eq_true_eq] at h ⊢; omega
  · simp only [isnumericC, isprintC, Bool.and_eq_true, decide_eq_true_eq] at h ⊢; omega
  · simp only [ispunctC, isprintC, Bool.and_eq_true, decide_eq_true_eq] at h ⊢; omega

/-! ## `titlecase`, `uppercasefirst`, `lowercasefirst` of `AnnotatedString`s -/

/-- `titlecase(s::AnnotatedString; wordsep, strict)` has the code units of
`titlecase(s.string; wordsep, strict)` (the same loop over the characters); the
SubString form is that of the converted `AnnotatedString`. -/
def TitlecaseAnnotated : Prop :=
  (∀ P wordsep strict s, titlecaseAS P wordsep strict s =
    Ann.annotatedChartransform (titleStep P wordsep strict) s (true, 0, 0)) ∧
  (∀ P wordsep strict s a, Ann.ofSub s = .ok a → titlecaseSub P wordsep strict s = titlecaseAS P wordsep strict a)

theorem titlecaseAnnotated : TitlecaseAnnotated := by
  refine ⟨fun _ _ _ _ => rfl, fun P wordsep strict s a h => ?_⟩
  · simp only [titlecaseSub, h, RegexUnicode.Uni.liftS, bind, Except.bind]

/-- `uppercasefirst` and `lowercasefirst`: for an `AnnotatedString`, the code units are
those of the characters with only the first one mapped (`titlecase` resp.
`lowercase`); for a `String`, the empty string maps to `""`, and otherwise the result
is `s` when the first character is unchanged and the mapped character followed by
`SubString(s, nextind(s, 1))` when it changes. The SubString forms are those of the
converted `AnnotatedString`. -/
def FirstCaseContract : Prop :=
  (∀ f (s : JStr), s.bytes = [] → mapfirstStr f s = .ok JStr.empty) ∧
  (∀ P s, uppercasefirstStr P s = mapfirstStr (titlecaseChar P) s ∧ lowercasefirstStr P s = mapfirstStr (lowercaseChar P) s) ∧
  (∀ P s a, Ann.ofSub s = .ok a → uppercasefirstSub P s = uppercasefirstAS P a ∧ lowercasefirstSub P s = lowercasefirstAS P a)

theorem firstCaseContract : FirstCaseContract := by
  refine ⟨fun f s hs => ?_, fun _ _ => ⟨rfl, rfl⟩, fun P s a h => ?_⟩
  · unfold mapfirstStr
    rw [if_pos (by simpa [List.isEmpty_iff] using hs)]
    rfl
  · simp only [uppercasefirstSub, lowercasefirstSub, h, RegexUnicode.Uni.liftS, bind, Except.bind]
    simp

/-! ## Graphemes -/

/-- `isgraphemebreak(c1, c2)` is `true` when either character is malformed and
otherwise utf8proc's answer on the code points; `length(graphemes(s))` is the number
of elements `iterate` produces; the element type is `SubString{S}` (also for
`S = SubString{T}`, where it is `SubString{T}`); `==`, `hash` and `isless` are those
of the strings, so `==` implies equal hashes; `show` prints the length, type and
string. -/
def GraphemesContract : Prop :=
  (∀ E c1 c2, (ismalformed c1 || ismalformed c2) = true → isgraphemebreakC E c1 c2 = .ok true) ∧
  (∀ E c1 c2 u1 u2, ismalformed c1 = false → ismalformed c2 = false → codepoint c1 = .ok u1 →
    codepoint c2 = .ok u2 → isgraphemebreakC E c1 c2 = .ok (E.gb u1 u2)) ∧
  (∀ P, GbInit P → ∀ s, ∃ G len, RegexUnicode.Uni.gCollect P s = .ok G ∧ giLength P (graphemes s) = .ok len ∧
    len.val = G.length) ∧
  (∀ S, giEltype (.subString S) = .subString S) ∧ giEltype .string = .subString .string ∧
  (∀ hs g1 g2 h, giEq g1 g2 = true → giHash hs g1 h = giHash hs g2 h) ∧
  (∀ g1 g2, giIsless g1 g2 = decide (Strings.cmp g1.s g2.s < 0)) ∧
  (∀ l t g, giShow l t g = "length-".toUTF8.toList ++ l ++ " GraphemeIterator{".toUTF8.toList ++ t ++
    "} for \"".toUTF8.toList ++ g.s.bytes ++ "\"".toUTF8.toList)

theorem graphemesContract : GraphemesContract := by
  refine ⟨fun E c1 c2 h => ?_, fun E c1 c2 u1 u2 h1 h2 h3 h4 => ?_, fun P hP s => ?_, fun _ => rfl, rfl,
    fun hs g1 g2 h e => ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩
  · unfold isgraphemebreakC; rw [if_pos h]
  · unfold isgraphemebreakC
    rw [if_neg (by simp [h1, h2])]
    simp [RegexUnicode.Uni.liftS, h3, h4, bind, Except.bind, pure, Except.pure]
  · obtain ⟨G, len, hG, hl, he, _⟩ := RegexUnicode.Uni.graphemesRange_proven P hP s (ix 1) (ix 1) (by decide)
      (by omega)
    exact ⟨G, len, hG, hl, he⟩
  · simp only [giEq, beq_iff_eq] at e
    simp only [giHash, e]

end JuliaLean.StringsCovB.Uni
