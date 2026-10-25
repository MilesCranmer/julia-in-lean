import JuliaLean.VersionNumbers.Model

/-!
# Properties of `VersionNumber`
-/

namespace JuliaLean.VersionNumbers

open JuliaLean

/-- The values the inner constructor returns (`base/version.jl:56-82`). -/
def Constructible (v : VersionNumber) : Prop :=
  newVersion v.major v.minor v.patch v.pre v.build = .ok v

/-- Major, minor and patch of `a` precede those of `b` lexicographically. -/
def mmpLt (a b : VersionNumber) : Prop :=
  a.major.val < b.major.val ∨ (a.major.val = b.major.val ∧ (a.minor.val < b.minor.val ∨
    (a.minor.val = b.minor.val ∧ a.patch.val < b.patch.val)))

def sameMmp (a b : VersionNumber) : Prop :=
  a.major = b.major ∧ a.minor = b.minor ∧ a.patch = b.patch

/-- A version without pre-release and build annotations. -/
def Plain (u : VersionNumber) : Prop := u.pre = [] ∧ u.build = []

/-- Lexicographic order of strings by code point (ASCII order on ASCII strings),
a shorter prefix first. -/
def strLt : List Char → List Char → Prop
  | [], _ :: _ => True
  | a :: as, b :: bs => a.val < b.val ∨ (a = b ∧ strLt as bs)
  | _, _ => False

/-- semver 2.0.0-rc.2 precedence of two pre-release identifiers: numeric ones
numerically, alphanumeric ones lexically in ASCII order, numeric before
alphanumeric. -/
def identPrecedes : Ident → Ident → Prop
  | .num m, .num n => m.val < n.val
  | .num _, .str t => t ≠ []
  | .str s, .str t => s ≠ [] ∧ strLt s t
  | .str _, .num _ => False

/-- `tryparse(VersionNumber, s)` returns a `VersionNumber` or `nothing` and never
throws (`tryparse` docstring, `base/parse.jl`). -/
def TryparseNothrow : Prop := ∀ s : List Char, ∃ r, tryparse s = .ok r

/-- `parse(VersionNumber, string(v)) == v` for every `VersionNumber` `v`. -/
def PrintParseRoundtrip : Prop :=
  ∀ v, Constructible v → ∃ w, parse (vprint v) = .ok w ∧ veq w v = true

/-- `[0-9A-Za-z-]`, the semver identifier alphabet. -/
def isSemverChar (c : Char) : Bool := isAsciiDigit c || isAsciiLetter c || c == '-'

def identSemver : Ident → Bool
  | .num _ => true
  | .str s => s.all isSemverChar

/-- Every identifier `parse(VersionNumber, s)` produces is made of `[0-9A-Za-z-]`
(semver 2.0.0-rc.2, cited by the `VersionNumber` docstring). -/
def ParseIdentCharset : Prop :=
  ∀ s v, tryparse s = .ok (some v) → (v.pre ++ v.build).all identSemver = true

def IdentArg.negative : IdentArg → Bool
  | .int x => x.val < 0
  | .str _ => false

/-- `VersionNumber(major, minor, patch, pre, bld)` with a negative integer
component or identifier throws an `ArgumentError` (`base/version.jl:58-60,63,73`). -/
def NegativeArgumentError : Prop :=
  ∀ (ma mi pa : JInt .i64) (pre bld : List IdentArg),
    (ma.val < 0 ∨ mi.val < 0 ∨ pa.val < 0 ∨ (pre ++ bld).any IdentArg.negative) →
    ∃ msg, versionNumber ma mi pa pre bld = .error (.argumentError msg)

/-- `==` on `VersionNumber` is equality of all five fields. -/
def EqStructural : Prop := ∀ a b, veq a b = true ↔ a = b

/-- `a == b` implies `hash(a, h) == hash(b, h)`, whatever the `hash` methods of the fields. -/
def HashConsistent : Prop :=
  ∀ (hu : JInt .u32 → UInt64 → UInt64) (ht : List Ident → UInt64 → UInt64) (h : UInt64) a b,
    veq a b = true → vhash hu ht a h = vhash hu ht b h

/-- `isless` is a strict total order whose incomparable pairs are exactly the `==` pairs. -/
def IslessTotalOrder : Prop :=
  (∀ a, vless a a = false) ∧
  (∀ a b c, vless a b = true → vless b c = true → vless a c = true) ∧
  (∀ a b, vless a b = true ∨ veq a b = true ∨ vless b a = true) ∧
  (∀ a b, vless a b = true → veq a b = false ∧ vless b a = false)

/-- semver 2.0.0-rc.2 precedence (`VersionNumber` docstring, `base/version.jl:18-20`):
a pre-release precedes the release; a build follows the normal version; the
first differing pre-release identifiers decide; a longer pre-release with equal
leading identifiers comes later. -/
def SemverPrecedence : Prop :=
  (∀ a b, sameMmp a b → a.pre ≠ [] → b.pre = [] → vless a b = true) ∧
  (∀ a b, sameMmp a b → a.pre = b.pre → a.build = [] → b.build ≠ [] → vless a b = true) ∧
  (∀ a b p x y q r, sameMmp a b → a.pre = p ++ x :: q → b.pre = p ++ y :: r →
    identPrecedes x y → vless a b = true) ∧
  (∀ a b p q, sameMmp a b → a.pre = p → b.pre = p ++ q → p ≠ [] → q ≠ [] → vless a b = true)

/-- `typemin(VersionNumber) <= v <= typemax(VersionNumber)` for every `v`, and
`typemin(VersionNumber) == v"0-"`. -/
def TypeminTypemax : Prop :=
  parse ['0', '-'] = .ok typeminV ∧ Constructible typemaxV ∧
  ∀ v, Constructible v → vless v typeminV = false ∧ vless typemaxV v = false

/-- `lowerbound(v)` precedes exactly the versions whose major.minor.patch is at
least that of `v` (all their pre-releases included), `upperbound(v)` follows
exactly those whose major.minor.patch is at most that of `v` (manual,
"Version Number Literals"). -/
def BoundsBracket : Prop :=
  ∀ v, ∃ lo hi, lowerbound v = .ok lo ∧ upperbound v = .ok hi ∧
    ∀ w, Constructible w → (vless w lo = true ↔ mmpLt w v) ∧ (vless hi w = true ↔ mmpLt v w)

/-- Below `typemax(UInt32)`, `nextpatch(v)` is the least plain version above `v`,
`nextminor(v)` the least plain `x.y.0` above `v`, `nextmajor(v)` the least
plain `x.0.0` above `v`. -/
def NextLeast : Prop :=
  ∀ v : VersionNumber,
    (v.patch.val < vmax.val → ∃ w, nextpatch v = .ok w ∧ Plain w ∧ vless v w = true ∧
      ∀ u, Plain u → vless v u = true → vless u w = false) ∧
    (v.minor.val < vmax.val → ∃ w, nextminor v = .ok w ∧ Plain w ∧ w.patch.val = 0 ∧ vless v w = true ∧
      ∀ u, Plain u → u.patch.val = 0 → vless v u = true → vless u w = false) ∧
    (v.major.val < vmax.val → ∃ w, nextmajor v = .ok w ∧ Plain w ∧ w.minor.val = 0 ∧ w.patch.val = 0 ∧
      vless v w = true ∧ ∀ u, Plain u → u.minor.val = 0 → u.patch.val = 0 → vless v u = true → vless u w = false)

/-- When the component to increment is `typemax(UInt32)` and `v` is no
pre-release, `nextpatch`/`nextminor`/`nextmajor` throw `InexactError` instead of
wrapping around. -/
def NextOverflow : Prop :=
  ∀ v : VersionNumber, v.pre = [] →
    (v.patch = vmax → ∃ e, nextpatch v = .error (.inexactError e)) ∧
    (v.minor = vmax → ∃ e, nextminor v = .error (.inexactError e)) ∧
    (v.major = vmax → ∃ e, nextmajor v = .error (.inexactError e))

/-- `thispatch`, `thisminor`, `thismajor` always succeed, drop the annotations
and the lower components, and are monotone. -/
def ThisMonotone : Prop :=
  (∀ v, thispatch v = .ok ⟨v.major, v.minor, v.patch, [], []⟩ ∧
        thisminor v = .ok ⟨v.major, v.minor, u32 0, [], []⟩ ∧
        thismajor v = .ok ⟨v.major, u32 0, u32 0, [], []⟩) ∧
  ∀ v w, vless w v = false →
    (∀ a b, thispatch v = .ok a → thispatch w = .ok b → vless b a = false) ∧
    (∀ a b, thisminor v = .ok a → thisminor w = .ok b → vless b a = false) ∧
    (∀ a b, thismajor v = .ok a → thismajor w = .ok b → vless b a = false)

end JuliaLean.VersionNumbers
