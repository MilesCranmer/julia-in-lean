import JuliaLean.ParsePrint.Ryu
import JuliaLean.Registry.Types

/-!
Properties of Float64 printing (`base/ryu/shortest.jl`).

`decimalRat` reads back a printed decimal `[-]d+[.d*][e[-]d+]` as an exact
rational `num/den`; every finite Float64 is printed in this form.
-/

namespace JuliaLean.ParsePrint.Ryu

open JuliaLean JuliaLean.Float

/-- `'0' ≤ c ≤ '9'`. -/
def isDigitCh (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- The value of a list of decimal digit characters. -/
def digitsValue (ds : List Nat) : Nat := ds.foldl (fun acc c => acc * 10 + (c - 48)) 0

/-- Exact value of a decimal literal `[-]d+[.d*][e[+-]d+]`, as `(num, den)`. -/
def decimalRat (s : List Nat) : Option (Int × Nat) :=
  let (neg, s) := match s with | 45 :: r => (true, r) | r => (false, r)
  let ip := s.takeWhile isDigitCh
  let s := s.dropWhile isDigitCh
  let (fp, s) := match s with
    | 46 :: r => (r.takeWhile isDigitCh, r.dropWhile isDigitCh)
    | r => ([], r)
  let (eneg, ep, s) := match s with
    | 101 :: 45 :: r => (true, r.takeWhile isDigitCh, r.dropWhile isDigitCh)
    | 101 :: 43 :: r => (false, r.takeWhile isDigitCh, r.dropWhile isDigitCh)
    | 101 :: r => (false, r.takeWhile isDigitCh, r.dropWhile isDigitCh)
    | r => (false, [48], r)
  if ip.isEmpty || ep.isEmpty || !s.isEmpty then none else
    let m : Int := digitsValue (ip ++ fp)
    let m := if neg then -m else m
    let scale : Int := (if eneg then -(digitsValue ep : Int) else digitsValue ep) - fp.length
    if scale ≥ 0 then some (m * 10 ^ scale.toNat, 1) else some (m, 10 ^ (-scale).toNat)

/-- The number of decimal digits of `n` (one for zero). -/
def decLen : Nat → Nat → Nat
  | 0, _ => 1
  | f+1, n => if n < 10 then 1 else decLen f (n / 10) + 1

/-- `floor(log10(n/d))` for positive `n` and `d`, by exact comparison. -/
def floorLog10 (n d : Nat) : Int :=
  let e : Int := (decLen 400 n : Int) - decLen 400 d
  -- `10^e ≤ n/d` decides between `e` and `e - 1`
  let ge := if e ≥ 0 then d * 10 ^ e.toNat ≤ n else d ≤ n * 10 ^ (-e).toNat
  if ge then e else e - 1

/-- `10^k` for an integer `k`, as `(num, den)`. -/
def pow10Rat (k : Int) : Nat × Nat := if k ≥ 0 then (10 ^ k.toNat, 1) else (1, 10 ^ (-k).toNat)

/-- The compact (`:compact => true`) display `D` of `x` rounds `x` to six
significant digits: with `10^E ≤ |x| < 10^(E+1)`, `|D - x|` is at most half a unit in
the sixth digit, `5·10^(E-6)`, plus `10^(E-15)` for the first rounding to the
shortest representation (at most half an ulp, below `1.2·10^(E-16)`). -/
def compactClose (x : F64) : Bool :=
  match decimalRat (showFloat true x) with
  | some (n, d) =>
    let (xn, xd) := F64.toRat x
    let (pn, pd) := pow10Rat (floorLog10 xn.natAbs xd - 15)
    decide ((n * xd - xn * d).natAbs * pd ≤ (5 * 10 ^ 9 + 1) * pn * d * xd)
  | none => false

/-- `show(IOContext(io, :compact => true), x)` writes a finite nonzero Float64 rounded
to six significant digits (`base/ryu/Ryu.jl:128-136`, `compact` in the docstring of
`Ryu.writeshortest`, `base/ryu/Ryu.jl:46`). -/
def CompactSixDigits : Prop := ∀ x : F64,
  F64.isfinite x = true → F64.iszero x = false → compactClose x = true

/-- `1.7562091489257724e16`. -/
def compactLostDigit : F64 := F64.ofBits 0x434f3250885d747e

set_option maxRecDepth 8192 in
theorem compactSixDigits_refuted : ¬ CompactSixDigits := by
  intro h
  have bad := h compactLostDigit (by decide) (by decide)
  have : compactClose compactLostDigit = false := by decide
  rw [this] at bad
  exact absurd bad (by decide)

/-- The even neighbour of the six leading digits of a seven-digit tie `k`. -/
def tieEven (k : Nat) : Nat := if (k / 10) % 2 = 0 then k / 10 else k / 10 + 1

/-- When a Float64 is exactly a seven-significant-digit integer `k·10^e` whose last
digit is 5, the compact display rounds the tie to the even six-digit neighbour,
as `reduce_shortest` intends (`base/ryu/shortest.jl:131-133,174,209`). -/
def CompactTiesToEven : Prop := ∀ (x : F64) (k e : Nat),
  F64.toRat x = (((k * 10 ^ e : Nat) : Int), 1) →
  10 ^ 6 ≤ k → k < 10 ^ 7 → k % 10 = 5 →
  decimalRat (showFloat true x) = some (((tieEven k * 10 ^ (e + 1) : Nat) : Int), 1)

/-- `1.234565e17 == 1234565 * 10^11` exactly. -/
def compactTie : F64 := F64.ofBits 0x437b69b085bb6880

set_option maxRecDepth 8192 in
theorem compactTiesToEven_refuted : ¬ CompactTiesToEven := by
  intro h
  have bad := h compactTie 1234565 11 (by decide) (by decide) (by decide) (by decide)
  have : decimalRat (showFloat true compactTie) ≠
      some (((tieEven 1234565 * 10 ^ (11 + 1) : Nat) : Int), 1) := by decide
  exact this bad

/-- `writeshortest(x, ..., precision)` with `precision ≥ 0` chooses fixed notation
when the decimal point position `pt` satisfies `-4 < pt ≤ precision` and `x` is an
integer multiple of the power of ten its shortest digits leave out
(`base/ryu/shortest.jl:337-338`); for `x = 10^k` exactly, that is `k < precision`. -/
def PrecisionFixedPowersOfTen : Prop := ∀ (x : F64) (k : Nat) (p : Int),
  F64.toRat x = (((10 ^ k : Nat) : Int), 1) → (k : Int) < p →
  (writeshortest x false false true p chE false chDot false).contains chE = false

/-- `1e20`, exactly `10^20`. -/
def tenPow20 : F64 := F64.ofBits 0x4415af1d78b58c40

set_option maxRecDepth 8192 in
theorem precisionFixedPowersOfTen_refuted : ¬ PrecisionFixedPowersOfTen := by
  intro h
  have bad := h tenPow20 20 30 (by decide) (by decide)
  have : (writeshortest tenPow20 false false true 30 chE false chDot false).contains chE = true := by
    decide
  rw [this] at bad
  exact absurd bad (by decide)

end JuliaLean.ParsePrint.Ryu
