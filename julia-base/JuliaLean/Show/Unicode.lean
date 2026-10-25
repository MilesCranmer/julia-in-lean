import JuliaLean.Strings.Char

/-!
# Unicode character classes used by the printers

`isprint`, `jl_id_start_char` and `jl_id_char` consult the utf8proc tables for
non-ASCII code points. Those tables are data, not code, so the model takes
them as a parameter `UData`; every property quantifies over all tables. The
ASCII part of each predicate and the out-of-range behaviour are fixed by the
Julia and C sources and are modelled exactly.
-/

namespace JuliaLean.Show

open JuliaLean.Strings

/-- The Unicode data the printers consult for code points `≥ 0x80`.
* `cat u` is `utf8proc_category(u)` (`base/strings/unicode.jl:379-381`) for
  `0x80 ≤ u ≤ 0x10ffff`;
* `idStart u` is `is_wc_cat_id_start(u, utf8proc_category(u))`
  (`src/flisp/julia_extensions.c:67-125`) for `0xa1 ≤ u ≤ 0x10ffff`;
* `idChar u` is the non-ASCII disjunction of `jl_id_char`
  (`src/flisp/julia_extensions.c:139-155`) for `0xa1 ≤ u ≤ 0x10ffff`. -/
structure UData where
  cat : UInt32 → Nat
  idStart : UInt32 → Bool
  idChar : UInt32 → Bool

/-- `utf8proc_category(u)` for the 128 ASCII code points, as printed by
`[Base.Unicode.category_code(Char(i)) for i in 0:127]` on Julia 1.13.2 and
master. -/
def asciiCats : List Nat :=
  [26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,
   23,18,18,18,20,18,18,18,14,15,18,19,18,13,18,18,9,9,9,9,9,9,9,9,9,9,18,18,19,19,19,18,
   18,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,14,18,15,21,12,
   21,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,14,19,15,19,26]

/-- `utf8proc_category(u)` for `u ≤ 0x10ffff`. -/
def utf8procCategory (d : UData) (u : UInt32) : Nat :=
  if u < 0x80 then asciiCats.getD u.toNat 0 else d.cat u

/-- `category_code(c::Char)`, `base/strings/unicode.jl:372-381`: 31 for
malformed chars, 30 for code points above `0x10ffff`. -/
def categoryCode (d : UData) (c : UInt32) : Nat :=
  if ismalformed c then 31
  else match codepoint c with
    | .ok u => if u ≤ 0x10ffff then utf8procCategory d u else 30
    | .error _ => 31

/-- `isprint(c) = UTF8PROC_CATEGORY_LU <= category_code(c) <= UTF8PROC_CATEGORY_ZS`,
`base/strings/unicode.jl:642` (`LU = 1`, `ZS = 23`). -/
def isprint (d : UData) (c : UInt32) : Bool :=
  decide (1 ≤ categoryCode d c) && decide (categoryCode d c ≤ 23)

/-- `jl_id_start_char(wc)`, `src/flisp/julia_extensions.c:127-137`. -/
def idStartChar (d : UData) (wc : UInt32) : Bool :=
  if (decide (65 ≤ wc) && decide (wc ≤ 90)) || (decide (97 ≤ wc) && decide (wc ≤ 122)) || wc == 95 then true
  else if decide (wc < 0xa1) || decide (wc > 0x10ffff) then false
  else if wc == 0x1f8b2 then true
  else d.idStart wc

/-- `jl_id_char(wc)`, `src/flisp/julia_extensions.c:139-157`. -/
def idChar (d : UData) (wc : UInt32) : Bool :=
  if (decide (65 ≤ wc) && decide (wc ≤ 90)) || (decide (97 ≤ wc) && decide (wc ≤ 122)) || wc == 95 ||
      (decide (48 ≤ wc) && decide (wc ≤ 57)) || wc == 33 then true
  else if decide (wc < 0xa1) || decide (wc > 0x10ffff) then false
  else d.idChar wc

/-- The Unicode data that classifies every non-ASCII code point as unassigned
(category `Cn = 0`) and not an identifier character; used to instantiate
counterexamples whose behaviour does not depend on the tables. -/
def UData.empty : UData := ⟨fun _ => 0, fun _ => false, fun _ => false⟩

end JuliaLean.Show
