import JuliaLean.Strings.Theory

/-!
# PCRE2 matching as a primitive

`pcre2_match` (PCRE2 10.46 in Julia 1.13.2, 10.49 on master) is modelled by its
documented behaviour only: a `Pcre` bundles a matching function with the
documented facts about the offsets it returns. Properties of the Julia wrappers
quantify over every `Pcre`; refutations use a concrete instance.

* `interp` is a leftmost-first backtracking interpreter for a small pattern
  fragment (literals, concatenation, alternation, greedy star, empty, capture
  groups) and is proven to satisfy the documented facts.
* `emptyAt` is a primitive that reports empty matches at a fixed list of
  positions; it describes patterns made only of assertions, such as
  `r"(?<!a)(?!a)"`, on one subject.
-/

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-! ## Errors -/

/-- Exceptions thrown by the modelled regex functions: those of the String model
(`BoundsError`, `InexactError`, `StringIndexError`, ...) and `ErrorException`
from `error(msg)` (`base/error.jl:35-44`). -/
inductive RErr where
  | str (e : SErr)
  | errorException (msg : String)
  deriving Repr, DecidableEq, Inhabited

abbrev RJl (α : Type) := Except RErr α

/-- A String-model call inside a regex function. -/
def liftS {α : Type} (x : SJl α) : RJl α := x.mapError .str

/-! ## Match options (`pcre2.h`) -/

/-- `PCRE2_ANCHORED`. -/
def ANCHORED : UInt32 := 0x80000000
/-- `PCRE2_NO_UTF_CHECK`. -/
def NO_UTF_CHECK : UInt32 := 0x40000000
/-- `PCRE2_NOTEMPTY_ATSTART`. -/
def NOTEMPTY_ATSTART : UInt32 := 0x00000008

/-- `opts & bit != 0`. -/
def hasOpt (opts bit : UInt32) : Bool := (opts &&& bit) != 0

/-- `DEFAULT_MATCH_OPTS = PCRE.NO_UTF_CHECK`, `base/regex.jl:8`. -/
def DEFAULT_MATCH_OPTS : UInt32 := NO_UTF_CHECK

/-! ## The primitive -/

/-- The output vector of a successful `pcre2_match`: zero-based code-unit
offsets of the whole match (`start`, `stop`) and one pair per capture group
(`none` is the pair `(PCRE2_UNSET, PCRE2_UNSET)`). The `Csize_t` offsets are
held as integers; the axioms of `Pcre` make them nonnegative. -/
structure Ovec where
  start : Int
  stop : Int
  caps : List (Option (Int × Int))
  deriving Repr, DecidableEq

/-- `pcre2_match(code, subject, length, startoffset, options, ...)` for a fixed
compiled pattern, for `startoffset ≤ length`, returning `none` for
`PCRE2_ERROR_NOMATCH` (and partial matches, which `PCRE.exec` also reports as
no match, `base/pcre.jl:214-216`).

Documented facts (pcre2api, "The string to be matched by pcre2_match()",
"Option bits for pcre2_match()", "How pcre2_match() returns a string and captured
substrings"):
* the match starts at or after `startoffset`, and `start ≤ stop ≤ length`
  (`\K` inside lookarounds, the only way to get `start > stop`, is disabled by
  default since 10.38);
* captured substrings lie within the subject;
* `PCRE2_ANCHORED`: the match is constrained to start at `startoffset`;
* `PCRE2_NOTEMPTY_ATSTART`: an empty string at the start of the subject
  (`startoffset`) is not a valid match.
With `PCRE2_NO_UTF_CHECK` (Julia's default) the start offset is not checked, so
it may point inside a character; `run` is defined for every `startoffset ≤ length`.
Other errors (match limits, out of memory) are not modelled. -/
structure Pcre where
  run : JStr → Nat → UInt32 → Option Ovec
  start_ge : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v → (o : Int) ≤ v.start
  start_le_stop : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v → v.start ≤ v.stop
  stop_le : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    v.stop ≤ (s.bytes.length : Int)
  caps_le : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    ∀ x ∈ v.caps, ∀ a b, x = some (a, b) →
      0 ≤ a ∧ a ≤ (s.bytes.length : Int) ∧ 0 ≤ b ∧ b ≤ (s.bytes.length : Int)
  anchored : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    hasOpt opts ANCHORED = true → v.start = o
  notempty_atstart : ∀ s o opts v, o ≤ s.bytes.length → run s o opts = some v →
    hasOpt opts NOTEMPTY_ATSTART = true → ¬ (v.start = o ∧ v.stop = o)

/-- A compiled `Regex` (`base/regex.jl:22-27`): the compiled pattern and its
`match_options`. Compile options only influence `pcre`. -/
structure Regex where
  pcre : Pcre
  matchOptions : UInt32

/-! ## A backtracking interpreter -/

/-- Pattern fragment. `lit bs` matches the code units `bs` (a character literal
is its UTF-8 bytes); `group k r` is capture group `k + 1`. -/
inductive Re where
  | empty
  | lit (bs : List UInt8)
  | seq (a b : Re)
  | alt (a b : Re)
  | star (a : Re)
  | group (k : Nat) (a : Re)
  deriving Repr, DecidableEq

def Re.size : Re → Nat
  | .empty => 1
  | .lit _ => 1
  | .seq a b => a.size + b.size + 1
  | .alt a b => a.size + b.size + 1
  | .star a => a.size + 1
  | .group _ a => a.size + 1

/-- A pattern with its number of capture groups. -/
structure Pattern where
  re : Re
  ngroups : Nat

abbrev Caps := List (Option (Nat × Nat))

/-- Match the literal `l` at zero-based position `p`; the end position. -/
def litAt (bs : List UInt8) : Nat → List UInt8 → Option Nat
  | p, [] => some p
  | p, b :: rest => if bs[p]? = some b then litAt bs (p + 1) rest else none

/-- Leftmost-first backtracking in continuation-passing style: run `r` at `p`
with captures `c`, calling `k` on each candidate end position in priority order
and returning the first result `k` accepts. Alternation tries the left branch
first; star is greedy, and an iteration that matches the empty string ends the
repetition (as in PCRE). `fuel` bounds the recursion depth. -/
def runRe {β : Type} (bs : List UInt8) : Nat → Re → Nat → Caps → (Nat → Caps → Option β) → Option β
  | 0, _, _, _, _ => none
  | _ + 1, .empty, p, c, k => k p c
  | _ + 1, .lit l, p, c, k =>
    match litAt bs p l with
    | some q => k q c
    | none => none
  | f + 1, .seq a b, p, c, k => runRe bs f a p c (fun q c' => runRe bs f b q c' k)
  | f + 1, .alt a b, p, c, k =>
    match runRe bs f a p c k with
    | some x => some x
    | none => runRe bs f b p c k
  | f + 1, .star a, p, c, k =>
    match runRe bs f a p c (fun q c' => if q = p then k q c' else runRe bs f (.star a) q c' k) with
    | some x => some x
    | none => k p c
  | f + 1, .group i a, p, c, k => runRe bs f a p c (fun q c' => k q (c'.set i (some (p, q))))

/-- Skip continuation bytes starting at `p`. -/
def skipCont (bs : List UInt8) : Nat → Nat → Nat
  | 0, p => p
  | f + 1, p =>
    match bs[p]? with
    | some b => if isCont b then skipCont bs f (p + 1) else p
    | none => p

/-- PCRE2's advance of the start position in UTF mode after a failed attempt at
`p`: one code unit, then past continuation bytes (`ACROSSCHAR`). On a valid
string this is the next character boundary. -/
def advance (bs : List UInt8) (p : Nat) : Nat := skipCont bs bs.length (p + 1)

/-- One anchored attempt at `p` for start offset `o`, honouring
`PCRE2_NOTEMPTY_ATSTART`. -/
def attempt (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) (p : Nat) : Option (Nat × Caps) :=
  runRe s.bytes ((s.bytes.length + 2) * (pat.re.size + 1)) pat.re p (List.replicate pat.ngroups none)
    (fun q c => if hasOpt opts NOTEMPTY_ATSTART && decide (p = o) && decide (q = o) then none
      else some (q, c))

/-- Try start positions `p, advance p, ...` up to the end of the subject (only
`p = o` when anchored); the result is `(start, stop, captures)`. The fuel is
`length + 1 - o`: positions increase. -/
def searchFrom (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) :
    Nat → Nat → Option (Nat × Nat × Caps)
  | 0, _ => none
  | f + 1, p =>
    match attempt s pat o opts p with
    | some (q, c) => some (p, q, c)
    | none =>
      if hasOpt opts ANCHORED || decide (s.bytes.length ≤ p) then none
      else searchFrom s pat o opts f (advance s.bytes p)

def capInt : Option (Nat × Nat) → Option (Int × Int)
  | none => none
  | some (a, b) => some (a, b)

def interpRun (pat : Pattern) (s : JStr) (o : Nat) (opts : UInt32) : Option Ovec :=
  (searchFrom s pat o opts (s.bytes.length + 1 - o) o).map
    (fun t => ⟨t.1, t.2.1, t.2.2.map capInt⟩)

/-! ### The interpreter satisfies the documented facts -/

def CapsOk (n : Nat) (c : Caps) : Prop := ∀ x ∈ c, ∀ a b, x = some (a, b) → a ≤ n ∧ b ≤ n

theorem capsOk_replicate (n k : Nat) : CapsOk n (List.replicate k none) := by
  intro x hx a b h
  rw [List.eq_of_mem_replicate hx] at h; cases h

theorem capsOk_set (n : Nat) (c : Caps) (i a b : Nat) (hc : CapsOk n c) (ha : a ≤ n) (hb : b ≤ n) :
    CapsOk n (c.set i (some (a, b))) := by
  intro x hx a' b' h
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact hc x hx a' b' h
  · subst hx; cases h; exact ⟨ha, hb⟩

theorem litAt_spec (bs : List UInt8) : ∀ (l : List UInt8) (p q : Nat), p ≤ bs.length →
    litAt bs p l = some q → p ≤ q ∧ q ≤ bs.length := by
  intro l
  induction l with
  | nil => intro p q hp h; simp [litAt] at h; omega
  | cons b rest ih =>
    intro p q hp h
    simp only [litAt] at h
    split at h
    · rename_i hb
      have hlt : p < bs.length := by
        rcases Nat.lt_or_ge p bs.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none_iff.mpr h'] at hb; cases hb
      have := ih (p + 1) q (by omega) h
      omega
    · cases h

theorem runRe_spec {β : Type} (bs : List UInt8) : ∀ (f : Nat) (r : Re) (p : Nat) (c : Caps)
    (k : Nat → Caps → Option β) (res : β), p ≤ bs.length → CapsOk bs.length c →
    runRe bs f r p c k = some res →
    ∃ q c', p ≤ q ∧ q ≤ bs.length ∧ CapsOk bs.length c' ∧ k q c' = some res := by
  intro f
  induction f with
  | zero => intro r p c k res _ _ h; simp [runRe] at h
  | succ f ih =>
    intro r p c k res hp hc h
    cases r with
    | empty => exact ⟨p, c, Nat.le_refl p, hp, hc, h⟩
    | lit l =>
      simp only [runRe] at h
      split at h
      · rename_i q hq
        have := litAt_spec bs l p q hp hq
        exact ⟨q, c, this.1, this.2, hc, h⟩
      · cases h
    | seq a b =>
      simp only [runRe] at h
      obtain ⟨q1, c1, h1, h2, h3, h4⟩ := ih a p c _ res hp hc h
      obtain ⟨q2, c2, g1, g2, g3, g4⟩ := ih b q1 c1 k res h2 h3 h4
      exact ⟨q2, c2, by omega, g2, g3, g4⟩
    | alt a b =>
      simp only [runRe] at h
      split at h
      · rename_i x hx
        cases h
        exact ih a p c k _ hp hc hx
      · exact ih b p c k res hp hc h
    | star a =>
      simp only [runRe] at h
      split at h
      · rename_i x hx
        cases h
        obtain ⟨q1, c1, h1, h2, h3, h4⟩ := ih a p c _ _ hp hc hx
        try simp only at h4
        split at h4
        · exact ⟨q1, c1, h1, h2, h3, h4⟩
        · obtain ⟨q2, c2, g1, g2, g3, g4⟩ := ih (.star a) q1 c1 k _ h2 h3 h4
          exact ⟨q2, c2, by omega, g2, g3, g4⟩
      · exact ⟨p, c, Nat.le_refl p, hp, hc, h⟩
    | group i a =>
      simp only [runRe] at h
      obtain ⟨q1, c1, h1, h2, h3, h4⟩ := ih a p c _ res hp hc h
      exact ⟨q1, _, h1, h2, capsOk_set _ c1 i p q1 h3 hp h2, h4⟩

theorem skipCont_spec (bs : List UInt8) : ∀ (f p : Nat), p ≤ bs.length →
    p ≤ skipCont bs f p ∧ skipCont bs f p ≤ bs.length := by
  intro f
  induction f with
  | zero => intro p hp; simp [skipCont]; omega
  | succ f ih =>
    intro p hp
    simp only [skipCont]
    split
    · rename_i b hb
      have hlt : p < bs.length := by
        rcases Nat.lt_or_ge p bs.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none_iff.mpr h'] at hb; cases hb
      split
      · have := ih (p + 1) (by omega); omega
      · omega
    · omega

theorem attempt_spec (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) (p q : Nat) (c : Caps)
    (hp : p ≤ s.bytes.length) (h : attempt s pat o opts p = some (q, c)) :
    p ≤ q ∧ q ≤ s.bytes.length ∧ CapsOk s.bytes.length c ∧
      ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ p = o ∧ q = o) := by
  unfold attempt at h
  obtain ⟨q', c', h1, h2, h3, h4⟩ :=
    runRe_spec s.bytes _ pat.re p _ _ _ hp (capsOk_replicate _ _) h
  try simp only at h4
  split at h4
  · cases h4
  · rename_i hne
    cases h4
    refine ⟨h1, h2, h3, fun ⟨a, b, d⟩ => hne ?_⟩
    simp [a, b, d]

/-- Every result of `searchFrom` started at a position `p` with `o ≤ p ≤ length`
(and `p = o` when anchored). -/
theorem searchFrom_spec (s : JStr) (pat : Pattern) (o : Nat) (opts : UInt32) :
    ∀ (f p p' q : Nat) (c : Caps), o ≤ p → p ≤ s.bytes.length →
      (hasOpt opts ANCHORED = true → p = o) → searchFrom s pat o opts f p = some (p', q, c) →
      o ≤ p' ∧ p' ≤ q ∧ q ≤ s.bytes.length ∧ CapsOk s.bytes.length c ∧
        (hasOpt opts ANCHORED = true → p' = o) ∧
        ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ p' = o ∧ q = o) := by
  intro f
  induction f with
  | zero => intro p p' q c _ _ _ h; simp [searchFrom] at h
  | succ f ih =>
    intro p p' q c h1 h2 ha h
    simp only [searchFrom] at h
    split at h
    · rename_i q' c' hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have := attempt_spec s pat o opts p q' c' h2 hq
      exact ⟨h1, this.1, this.2.1, this.2.2.1, ha, this.2.2.2⟩
    · split at h
      · cases h
      · rename_i hn
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hn
        have hs := skipCont_spec s.bytes s.bytes.length (p + 1) (by omega)
        exact ih _ p' q c (by unfold advance; omega) (by unfold advance; omega)
          (fun h' => absurd h' hn.1) h

theorem interpRun_spec (pat : Pattern) (s : JStr) (o : Nat) (opts : UInt32) (v : Ovec)
    (ho : o ≤ s.bytes.length) (h : interpRun pat s o opts = some v) :
    (o : Int) ≤ v.start ∧ v.start ≤ v.stop ∧ v.stop ≤ (s.bytes.length : Int) ∧
      (∀ x ∈ v.caps, ∀ a b, x = some (a, b) →
        0 ≤ a ∧ a ≤ (s.bytes.length : Int) ∧ 0 ≤ b ∧ b ≤ (s.bytes.length : Int)) ∧
      (hasOpt opts ANCHORED = true → v.start = o) ∧
      ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ v.start = o ∧ v.stop = o) := by
  unfold interpRun at h
  cases hs : searchFrom s pat o opts (s.bytes.length + 1 - o) o with
  | none => rw [hs] at h; cases h
  | some t =>
    rw [hs] at h
    obtain ⟨p, q, c⟩ := t
    simp only [Option.map, Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      searchFrom_spec s pat o opts _ o p q c (Nat.le_refl o) ho (fun _ => rfl) hs
    refine ⟨by simp only; omega, by simp only; omega, by simp only; omega, ?_,
      fun ha => by simp only; rw [h5 ha], fun ⟨a, b, d⟩ => h6 ⟨a, ?_, ?_⟩⟩
    · intro x hx a b hx'
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      cases y with
      | none => simp [capInt] at hx'
      | some ab =>
        obtain ⟨a', b'⟩ := ab
        simp only [capInt, Option.some.injEq, Prod.mk.injEq] at hx'
        obtain ⟨rfl, rfl⟩ := hx'
        have := h4 _ hy a' b' rfl
        omega
    · simp only at b; omega
    · simp only at d; omega

/-- The interpreter as a `Pcre` primitive. -/
def interp (pat : Pattern) : Pcre where
  run := interpRun pat
  start_ge s o opts v ho h := (interpRun_spec pat s o opts v ho h).1
  start_le_stop s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.1
  stop_le s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.2.1
  caps_le s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.2.2.1
  anchored s o opts v ho h := (interpRun_spec pat s o opts v ho h).2.2.2.2.1
  notempty_atstart s o opts v ho h ha := fun h' =>
    (interpRun_spec pat s o opts v ho h).2.2.2.2.2 ⟨ha, h'⟩

/-- `Regex(pattern)` with the default match options (`base/regex.jl:68`). -/
def mkRegex (pat : Pattern) : Regex := ⟨interp pat, DEFAULT_MATCH_OPTS⟩

/-! ## A primitive given by its empty matches -/

/-- The leftmost position of `ps` (listed in increasing order) that is an
admissible empty match for start offset `o`. -/
def emptyAtRun (ps : List Nat) (s : JStr) (o : Nat) (opts : UInt32) : Option Ovec :=
  match ps.find? (fun p => decide (o ≤ p) && decide (p ≤ s.bytes.length) &&
      !(hasOpt opts NOTEMPTY_ATSTART && decide (p = o)) &&
      (!hasOpt opts ANCHORED || decide (p = o))) with
  | some p => some ⟨p, p, []⟩
  | none => none

theorem emptyAtRun_spec (ps : List Nat) (s : JStr) (o : Nat) (opts : UInt32) (v : Ovec)
    (h : emptyAtRun ps s o opts = some v) :
    (o : Int) ≤ v.start ∧ v.start = v.stop ∧ v.stop ≤ (s.bytes.length : Int) ∧ v.caps = [] ∧
      (hasOpt opts ANCHORED = true → v.start = o) ∧
      ¬ (hasOpt opts NOTEMPTY_ATSTART = true ∧ v.start = o ∧ v.stop = o) := by
  unfold emptyAtRun at h
  split at h
  · rename_i p hp
    cases h
    have hc := List.find?_some hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    refine ⟨by simp only; omega, rfl, by simp only; omega, rfl, fun ha => ?_,
      fun ⟨hn, hpo, _⟩ => ?_⟩
    · rcases h4 with h4 | h4
      · rw [ha] at h4; cases h4
      · simp only; rw [h4]
    · rcases h3 with h3 | h3
      · rw [hn] at h3; cases h3
      · simp only at hpo; exact h3 (by omega)
  · cases h

/-- A primitive reporting the empty matches of an assertion-only pattern at the
zero-based positions `ps` (in increasing order). -/
def emptyAt (ps : List Nat) : Pcre where
  run := emptyAtRun ps
  start_ge s o opts v _ h := (emptyAtRun_spec ps s o opts v h).1
  start_le_stop s o opts v _ h := Int.le_of_eq (emptyAtRun_spec ps s o opts v h).2.1
  stop_le s o opts v _ h := (emptyAtRun_spec ps s o opts v h).2.2.1
  caps_le s o opts v _ h := by
    rw [(emptyAtRun_spec ps s o opts v h).2.2.2.1]; intro x hx; cases hx
  anchored s o opts v _ h := (emptyAtRun_spec ps s o opts v h).2.2.2.2.1
  notempty_atstart s o opts v _ h ha := fun h' =>
    (emptyAtRun_spec ps s o opts v h).2.2.2.2.2 ⟨ha, h'⟩

end JuliaLean.RegexUnicode.Core
