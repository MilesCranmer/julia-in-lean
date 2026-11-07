import JuliaLean.stdlib.Unicode.src.Unicode
import JuliaLean.Proofs.base.strings.unicode.functions

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-! ## Specification: canonical decomposition -/

/-- Decompose every character with `utf8proc_decompose_char` and concatenate. -/
def decompAll (P : Utf8proc) (options : Nat) : List UInt32 → UJl (List UInt32)
  | [] => .ok []
  | ch :: cs =>
    match codepoint ch with
    | .error e => .error (.str e)
    | .ok u =>
      match P.decomposeChar u options with
      | .error _ => .error .errorException
      | .ok l =>
        match decompAll P options cs with
        | .error e => .error e
        | .ok rest => .ok (l ++ rest)

/-- Canonical ordering (Unicode §3.11): stable sort of every maximal run of code points
with nonzero combining class. `run` is the current run. -/
def canonAux (P : Utf8proc) (run : List UInt32) : List UInt32 → List UInt32
  | [] => stableSortBy (ccOf P) run
  | x :: xs =>
    if ccOf P x == 0 then stableSortBy (ccOf P) run ++ x :: canonAux P [] xs
    else canonAux P (run ++ [x]) xs

/-- `normalize(s; decompose=true, casefold, stripmark)` as code points: per-character
decomposition concatenated, then canonical ordering. -/
def nfdSpec (P : Utf8proc) (casefold stripmark : Bool) (s : JStr) : UJl (List UInt32) :=
  match decompAll P (eqOptions casefold stripmark) (chars s) with
  | .error e => .error e
  | .ok l => .ok (canonAux P [] l)

/-- Every character converts to a code point below `0x110000`. -/
def validCps (s : JStr) : Bool :=
  (chars s).all fun c => match codepoint c with
    | .ok u => decide (u < 0x110000)
    | .error _ => false

/-- Documented behaviour of `utf8proc_decompose_char` used here: without `REJECTNA` it
succeeds on every code point; without `STRIPMARK` the decomposition is nonempty; an
ASCII code point decomposes to itself, lowercased under `CASEFOLD`. -/
structure Utf8proc.DecompAxioms (P : Utf8proc) : Prop where
  ok : ∀ u opts, u < 0x110000 → opts.testBit 6 = false → ∃ l, P.decomposeChar u opts = .ok l
  nonempty : ∀ u opts l, opts.testBit 13 = false → P.decomposeChar u opts = .ok l → l ≠ []
  ascii : ∀ u opts, u < 0x80 →
    P.decomposeChar u opts = .ok [if opts.testBit 10 && inRange 0x41 0x5a u then u + 0x20 else u]

/-- Property (`isequal_normalized` docstring, `stdlib/Unicode/src/Unicode.jl:230-268`:
whether `s1` and `s2` are canonically equivalent, with case folding and mark stripping
as in `normalize`): for strings of code points, the result is the comparison of the
canonical decompositions. -/
def IsequalNormalizedSpec : Prop :=
  ∀ P : Utf8proc, P.DecompAxioms → ∀ (mem1 mem2 : Nat → UInt32) (s1 s2 : JStr)
    (casefold stripmark : Bool), validCps s1 = true → validCps s2 = true →
    ∃ a b, nfdSpec P casefold stripmark s1 = .ok a ∧ nfdSpec P casefold stripmark s2 = .ok b ∧
      isequalNormalized P mem1 mem2 s1 s2 casefold stripmark = .ok (decide (a = b))

/-! ## A utf8proc table for `a`, `e`, `s`, `ß`, `é` and U+0301 -/

/-- `é = U+00E9 ↦ e U+0301`; U+0301 (combining acute, class 230) is stripped by
`STRIPMARK`; `ß = U+00DF ↦ ss` under `CASEFOLD`; other code points map to themselves;
code points from `0x110000` are rejected (`UTF8PROC_ERROR_NOTASSIGNED = -4`). -/
def tblDecompose (u : UInt32) (opts : Nat) : Except Int (List UInt32) :=
  let n := u.toNat
  if n ≥ 0x110000 then .error (-4)
  else if n < 0x80 then .ok [if opts.testBit 10 && inRange 0x41 0x5a u then u + 0x20 else u]
  else if n = 0xE9 then .ok (if opts.testBit 13 then [0x65] else [0x65, 0x301])
  else if n = 0x301 then .ok (if opts.testBit 13 then [] else [0x301])
  else if n = 0xDF then .ok (if opts.testBit 10 then [0x73, 0x73] else [0xDF])
  else .ok [u]

def tbl : Utf8proc where
  toupper := id
  tolower := id
  totitle := id
  category := fun _ => 0
  gbStateful := fun _ _ _ => (true, 0)
  decomposeChar := tblDecompose
  combiningClass := fun u => if u.toNat = 0x301 then 230 else 0

theorem tbl_axioms : tbl.DecompAxioms where
  ok u opts h _ := by
    have h' : ¬ u.toNat ≥ 0x110000 := by rw [UInt32.lt_iff_toNat_lt] at h; simpa using h
    simp only [tbl, tblDecompose, h', if_false]
    repeat (first | exact ⟨_, rfl⟩ | split)
  nonempty u opts l h hl := by
    intro hnil
    subst hnil
    simp only [tbl, tblDecompose] at hl
    repeat' split at hl
    all_goals simp_all
  ascii u opts h := by
    have h' : u.toNat < 0x80 := by rw [UInt32.lt_iff_toNat_lt] at h; simpa using h
    have h'' : ¬ u.toNat ≥ 0x110000 := by omega
    simp only [tbl, tblDecompose, h', h'', if_false, if_true]

/-- `"a\u0301"` and `"aa"`. -/
def strAacute : JStr := ⟨[0x61, 0xcc, 0x81], by decide⟩
def strAA : JStr := ⟨[0x61, 0x61], by decide⟩

/-- `r` returned `b`. -/
def resIs (r : UJl Bool) (b : Bool) : Bool :=
  match r with
  | .ok x => x == b
  | .error _ => false

theorem resIs_eq {r : UJl Bool} {b : Bool} (h : resIs r b = true) : r = .ok b := by
  unfold resIs at h
  split at h
  · simp at h; subst h; rfl
  · cases h

/-- With `stripmark=true`, U+0301 decomposes to nothing: `decompose_next_chars!` returns
`n = 0`, the main loop compares the stale `d1[1] = 'a'` with the second `'a'` of `"aa"`
and returns `true`; the decompositions are `"a"` and `"aa"`. -/
theorem isequalNormalizedSpec_refuted : ¬ IsequalNormalizedSpec := by
  intro h
  obtain ⟨a, b, ha, hb, he⟩ :=
    h tbl tbl_axioms (fun _ => 0) (fun _ => 0) strAacute strAA false true (by decide) (by decide)
  have ea : nfdSpec tbl false true strAacute = .ok [0x61] := by rfl
  have eb : nfdSpec tbl false true strAA = .ok [0x61, 0x61] := by rfl
  have ee : isequalNormalized tbl (fun _ => 0) (fun _ => 0) strAacute strAA false true = .ok true :=
    resIs_eq (by decide +kernel)
  rw [ea] at ha; rw [eb] at hb; rw [ee] at he
  cases ha; cases hb
  simp at he

/-! ## The other observed cases (`regexunicode-isequal-normalized-stripmark` reproducer) -/

def strCafeAcute : JStr := ⟨[0x63, 0x61, 0x66, 0x65, 0xcc, 0x81], by decide⟩
def strCafe : JStr := ⟨[0x63, 0x61, 0x66, 0x65], by decide⟩
def strCafee : JStr := ⟨[0x63, 0x61, 0x66, 0x65, 0x65], by decide⟩
def strAcute : JStr := ⟨[0xcc, 0x81], by decide⟩
def strEmpty : JStr := ⟨[], by decide⟩

/-- `isequal_normalized("cafe\u0301", "cafe"; stripmark=true) == false`,
`isequal_normalized("cafe\u0301", "cafee"; stripmark=true) == true`,
`isequal_normalized("\u0301", ""; stripmark=true) == false`, as Julia prints. -/
theorem stripmark_observed :
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strCafeAcute strCafe false true = .ok false ∧
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strCafeAcute strCafee false true = .ok true ∧
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strAcute strEmpty false true = .ok false :=
  ⟨resIs_eq (by decide +kernel), resIs_eq (by decide +kernel), resIs_eq (by decide +kernel)⟩

/-- `isequal_normalized("\u0301", "\u0301"; stripmark=true)` compares `d1[1]` and `d2[1]`,
which no call wrote: the result depends on the uninitialized buffer contents. -/
theorem stripmark_uninit :
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strAcute strAcute false true = .ok true ∧
    isequalNormalized tbl (fun _ => 0) (fun _ => 1) strAcute strAcute false true = .ok false :=
  ⟨resIs_eq (by decide +kernel), resIs_eq (by decide +kernel)⟩

end JuliaLean.RegexUnicode.Uni
