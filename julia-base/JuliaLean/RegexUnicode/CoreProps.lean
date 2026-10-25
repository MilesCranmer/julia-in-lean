import JuliaLean.RegexUnicode.CoreWrappers

/-!
# Properties of the regex wrappers

Refutations evaluate the wrappers on a concrete primitive (the interpreter of
`CorePcre.lean`, or `emptyAt` for an assertion-only pattern) on the inputs of the
reproducers `repro/regexunicode-<id>.jl`; the `*_agrees` theorems check the model
against the outputs Julia printed for those reproducers.
-/

set_option maxRecDepth 100000

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- `x` succeeded with value `a`. -/
def isOkOf {α : Type} [DecidableEq α] (x : RJl α) (a : α) : Bool :=
  match x with
  | .ok b => decide (b = a)
  | .error _ => false

theorem eq_of_isOkOf {α : Type} [DecidableEq α] (x : RJl α) (a : α) (h : isOkOf x a = true) :
    x = .ok a := by
  cases x with
  | error e => simp [isOkOf] at h
  | ok b => simp [isOkOf] at h; rw [h]

theorem ne_of_isOkOf {α : Type} [DecidableEq α] (x : RJl α) (a : α) (h : isOkOf x a = false) :
    x ≠ .ok a := by
  intro e; subst e; simp [isOkOf] at h

/-- `x` threw `e`. -/
def isErrOf {α : Type} (x : RJl α) (e : RErr) : Bool :=
  match x with
  | .ok _ => false
  | .error e' => decide (e' = e)

theorem ne_of_isErrOf {α : Type} (x : RJl α) (e : RErr) (h : isErrOf x e = false) :
    x ≠ .error e := by
  intro h'; subst h'; simp [isErrOf] at h

/-- The finished iterator run `ms`. -/
def traceIs (x : Option (RJl (List RegexMatch))) (ms : List RegexMatch) : Bool :=
  match x with
  | some (.ok l) => decide (l = ms)
  | _ => false

theorem trace_of_traceIs (re : Regex) (s : JStr) (ov : Bool) (k : Nat) (st : State)
    (ms : List RegexMatch) (h : traceIs (eachmatchFuel re s ov k st) ms = true) :
    EachTrace re s ov st (.ok ms) := by
  apply eachmatchFuel_sound re s ov k st
  revert h
  cases eachmatchFuel re s ov k st with
  | none => simp [traceIs]
  | some r =>
    cases r with
    | error e => simp [traceIs]
    | ok l => simp [traceIs]

/-! ## Concrete inputs -/

/-- A match of `s` without captures: `offset`, and its SubString `(off, ncu)`. -/
def rm (s : JStr) (offset off ncu : Int) : RegexMatch := ⟨⟨s, ix off, ix ncu⟩, [], ix offset, []⟩

/-- `"abxd"` -/
def sABXD : JStr := ⟨[0x61, 0x62, 0x78, 0x64], by decide⟩
/-- `"-"` -/
def sDash : JStr := ⟨[0x2d], by decide⟩
/-- `"b"` -/
def sB : JStr := ⟨[0x62], by decide⟩
/-- `"abc"` -/
def sABC : JStr := ⟨[0x61, 0x62, 0x63], by decide⟩
/-- `"éa"` -/
def sEA : JStr := ⟨[0xc3, 0xa9, 0x61], by decide⟩
/-- `"a\xe2\x82"`: `'a'` at 1 and the malformed character `"\xe2\x82"` at 2:3. -/
def sAMal : JStr := ⟨[0x61, 0xe2, 0x82], by decide⟩

/-- `r"x*"` -/
def reXStar : Regex := mkRegex ⟨.star (.lit [0x78]), 0⟩
/-- `r"|b"` -/
def reEmptyOrB : Regex := mkRegex ⟨.alt .empty (.lit [0x62]), 0⟩
/-- `r"a"` -/
def reA : Regex := mkRegex ⟨.lit [0x61], 0⟩
/-- `r""` -/
def reEmpty : Regex := mkRegex ⟨.empty, 0⟩
/-- `r"(?<!a)(?!a)"` on `"a\xe2\x82"` as PCRE2 10.49 (master) matches it: empty
matches at the zero-based positions 2 and 3. -/
def reLookMal : Regex := ⟨emptyAt [2, 3], DEFAULT_MATCH_OPTS⟩

/-- `collect(eachmatch(r"x*", "abxd"))`: offsets 1, 2, 3 (`"x"`), 4, 5. -/
def msXStar : List RegexMatch :=
  [rm sABXD 1 0 0, rm sABXD 2 0 0, rm sABXD 3 2 1, rm sABXD 4 0 0, rm sABXD 5 0 0]

/-- `collect(eachmatch(r"|b", "b"))`: `(1, "")`, `(1, "b")`, `(2, "")`. -/
def msEmptyOrB : List RegexMatch := [rm sB 1 0 0, rm sB 1 0 1, rm sB 2 0 0]

/-- `collect(eachmatch(r"(?<!a)(?!a)", "a\xe2\x82"))` on master: offsets 3, 4. -/
def msLookMal : List RegexMatch := [rm sAMal 3 0 0, rm sAMal 4 0 0]

theorem eachXStar_agrees : EachTrace reXStar sABXD false startState (.ok msXStar) :=
  trace_of_traceIs _ _ _ 10 _ _ (by decide +kernel)

theorem eachEmptyOrB_agrees : EachTrace reEmptyOrB sB false startState (.ok msEmptyOrB) :=
  trace_of_traceIs _ _ _ 10 _ _ (by decide +kernel)

theorem eachLookMal_agrees : EachTrace reLookMal sAMal false startState (.ok msLookMal) :=
  trace_of_traceIs _ _ _ 10 _ _ (by decide +kernel)

/-- `replace("abxd", r"x*" => "-") == "-a-b-d-"`. -/
theorem replaceXStar_agrees :
    replace reXStar sABXD sDash = .ok [0x2d, 0x61, 0x2d, 0x62, 0x2d, 0x64, 0x2d] :=
  eq_of_isOkOf _ _ (by decide +kernel)

/-- `findall(r"x*", "abxd") == [1:0, 2:1, 3:3, 4:3, 5:4]`, `count == 5`. -/
theorem findallXStar_agrees :
    findall reXStar sABXD = .ok [(ix 1, ix 0), (ix 2, ix 1), (ix 3, ix 3), (ix 4, ix 3), (ix 5, ix 4)] ∧
    count reXStar sABXD = .ok (ix 5) :=
  ⟨eq_of_isOkOf _ _ (by decide +kernel), eq_of_isOkOf _ _ (by decide +kernel)⟩

/-- `findall(r"|b", "b") == [1:0, 2:1]`, `count == 2`. -/
theorem findallEmptyOrB_agrees :
    findall reEmptyOrB sB = .ok [(ix 1, ix 0), (ix 2, ix 1)] ∧ count reEmptyOrB sB = .ok (ix 2) :=
  ⟨eq_of_isOkOf _ _ (by decide +kernel), eq_of_isOkOf _ _ (by decide +kernel)⟩

/-- On master: `findfirst(r, "a\xe2\x82") == 3:2` and
`replace(s, r => "-") == "a\xe2-\x82-"`. -/
theorem lookMal_agrees :
    findnextRe reLookMal sAMal (ix 1) = .ok (some (ix 3, ix 2)) ∧
    replace reLookMal sAMal sDash = .ok [0x61, 0xe2, 0x2d, 0x82, 0x2d] :=
  ⟨eq_of_isOkOf _ _ (by decide +kernel), eq_of_isOkOf _ _ (by decide +kernel)⟩

/-- `match(r"", "éa", 2).offset == 2` and `findnext(r"", "éa", 2) == 2:1`. -/
theorem emptyEA_agrees :
    (regexMatch reEmpty sEA (ix 2)).map (fun m => m.map (·.offset)) = .ok (some (ix 2)) ∧
    findnextRe reEmpty sEA (ix 2) = .ok (some (ix 2, ix 1)) :=
  ⟨eq_of_isOkOf _ _ (by decide +kernel), eq_of_isOkOf _ _ (by decide +kernel)⟩

/-- `findnext(r"a", "abc", 0)` and `match(r"a", "abc", 0)` throw `InexactError`;
`findnext(r"a", "abc", 5)` throws `BoundsError`; `match(r"a", "abc", 5)` throws
`ErrorException("PCRE.exec error: bad offset value")`. -/
theorem startBelow_agrees :
    isErrOf (findnextRe reA sABC (ix 0)) (.str (.jl (.inexactError "UInt64"))) = true ∧
    isErrOf (regexMatch reA sABC (ix 0)) (.str (.jl (.inexactError "UInt64"))) = true ∧
    isErrOf (findnextRe reA sABC (ix 5)) (.str boundsErr) = true ∧
    isErrOf (regexMatch reA sABC (ix 5)) (.errorException "PCRE.exec error: bad offset value") = true := by
  decide +kernel

/-! ## Refuted properties -/

/-- The text of `s` with every match of the run `ms` replaced by `t`: the code
units between consecutive matches (from `m.offset + ncodeunits(m.match)` of the
previous match), then `t` for each match, then the rest of `s`. -/
def assembleFrom (s : JStr) (t : List UInt8) : Int → List RegexMatch → List UInt8
  | prev, [] => s.bytes.drop (prev - 1).toNat
  | prev, m :: ms =>
    (s.bytes.drop (prev - 1).toNat).take (m.offset.val - prev).toNat ++ t ++
      assembleFrom s t (m.offset.val + m.mat.ncu.val) ms

def assemble (s : JStr) (ms : List RegexMatch) (t : JStr) : List UInt8 := assembleFrom s t.bytes 1 ms

/-- `replace(s, r => t)` replaces exactly the matches `eachmatch(r, s)` yields:
it equals the text between those matches with `t` inserted for each match. -/
def ReplaceAssemblesEachmatch : Prop :=
  ∀ (re : Regex) (s t : JStr) (ms : List RegexMatch),
    EachTrace re s false startState (.ok ms) → replace re s t = .ok (assemble s ms t)

theorem replaceAssemblesEachmatch_refuted : ¬ ReplaceAssemblesEachmatch := by
  intro h
  exact ne_of_isOkOf _ _ (by decide +kernel) (h reXStar sABXD sDash msXStar eachXStar_agrees)

/-- The range of a match: `m.offset:(m.offset + ncodeunits(m.match) - 1)`. -/
def matchRange (m : RegexMatch) : JInt64 × JInt64 :=
  mkRange m.offset (m.offset + m.mat.ncu - ix 1)

/-- `findall(r, s)` returns the ranges of the matches `eachmatch(r, s)` yields. -/
def FindallRangesOfEachmatch : Prop :=
  ∀ (re : Regex) (s : JStr) (ms : List RegexMatch),
    EachTrace re s false startState (.ok ms) → findall re s = .ok (ms.map matchRange)

theorem findallRangesOfEachmatch_refuted : ¬ FindallRangesOfEachmatch := by
  intro h
  exact ne_of_isOkOf _ _ (by decide +kernel) (h reEmptyOrB sB msEmptyOrB eachEmptyOrB_agrees)

/-- `findnext(r, s, i)` throws `BoundsError` for every start `i < 1`, as
`findnext(::AbstractString, ::String, i)` does. -/
def FindnextBelowBoundsError : Prop :=
  ∀ (re : Regex) (s : JStr) (i : JInt64), i.val < 1 → findnextRe re s i = .error (.str boundsErr)

theorem findnextBelowBoundsError_refuted : ¬ FindnextBelowBoundsError := by
  intro h
  exact ne_of_isErrOf _ _ (by decide +kernel) (h reA sABC (ix 0) (by decide +kernel))

/-- On a valid string, `match(r, s, i)` for `i in 1:ncodeunits(s)+1` returns a
match whose offset is a valid index or `ncodeunits(s) + 1`. -/
def MatchOffsetValid : Prop :=
  ∀ (re : Regex) (s : JStr) (i : JInt64) (m : RegexMatch),
    isvalidStr s = true → 1 ≤ i.val → i.val ≤ s.bytes.length + 1 →
    regexMatch re s i = .ok (some m) →
    isvalidAt s m.offset = true ∨ m.offset.val = s.bytes.length + 1

theorem matchOffsetValid_refuted : ¬ MatchOffsetValid := by
  intro h
  have hm : regexMatch reEmpty sEA (ix 2) = .ok (some (rm sEA 2 0 0)) := eq_of_isOkOf _ _ (by decide +kernel)
  have := h reEmpty sEA (ix 2) _ (by decide +kernel) (by decide +kernel) (by decide +kernel) hm
  revert this; decide +kernel

/-- Every offset `≤ ncodeunits(s)` of a match yielded by `eachmatch(r, s)` is a
valid index of `s`, for every byte string `s`. -/
def EachmatchOffsetsValid : Prop :=
  ∀ (re : Regex) (s : JStr) (ms : List RegexMatch),
    EachTrace re s false startState (.ok ms) →
    ∀ m ∈ ms, m.offset.val ≤ s.bytes.length → isvalidAt s m.offset = true

theorem eachmatchOffsetsValid_refuted : ¬ EachmatchOffsetsValid := by
  intro h
  have := h reLookMal sAMal msLookMal eachLookMal_agrees (rm sAMal 3 0 0) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

end JuliaLean.RegexUnicode.Core
