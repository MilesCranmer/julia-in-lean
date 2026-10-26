import JuliaLean.MiscCov.RyuUtils
import JuliaLean.MiscCov.UNat

/-!
Properties of `base/ryu/utils.jl`, stated from its docstrings and comments.
-/

namespace JuliaLean.MiscCov.RyuUtils

open JuliaLean JuliaLean.ParsePrint JuliaLean.MiscCov

/-- `a^r ≤ b^e` for integer exponents, cleared of denominators. -/
def PowLe (a : Nat) (r : Int) (b : Nat) (e : Int) : Prop :=
  a ^ (max r 0).toNat * b ^ (max (-e) 0).toNat ≤ b ^ (max e 0).toNat * a ^ (max (-r) 0).toNat

/-- `b^e < a^r` for integer exponents. -/
def PowLt (b : Nat) (e : Int) (a : Nat) (r : Int) : Prop :=
  b ^ (max e 0).toNat * a ^ (max (-r) 0).toNat < a ^ (max r 0).toNat * b ^ (max (-e) 0).toNat

instance : Decidable (PowLe a r b e) := by unfold PowLe; infer_instance
instance : Decidable (PowLt b e a r) := by unfold PowLt; infer_instance

/-- `r == floor(log10(b^e))`: `10^r ≤ b^e < 10^(r+1)`. -/
def FloorLog10 (b : Nat) (e r : Int) : Prop := PowLe 10 r b e ∧ PowLt b e 10 (r + 1)

instance : Decidable (FloorLog10 b e r) := by unfold FloorLog10; infer_instance

/-- `k == (e == 0 ? 1 : ceil(log2(5^e)))` for `e ≥ 0`. -/
def CeilLog2Pow5 (e : Nat) (k : Int) : Prop :=
  (e = 0 ∧ k = 1) ∨ (0 < e ∧ 1 ≤ k ∧ 2 ^ (k.toNat - 1) < 5 ^ e ∧ 5 ^ e ≤ 2 ^ k.toNat)

instance : Decidable (CeilLog2Pow5 e k) := by unfold CeilLog2Pow5; infer_instance

/-- The docstrings of `log10pow2`, `log10pow5` and `pow5bits`
(`base/ryu/utils.jl:22-42`) on the nonnegative exponents Ryu uses. -/
def LogApproxRange : Prop :=
  (∀ e : JInt .i64, 0 ≤ e.val → e.val < 1651 → FloorLog10 2 e.val (log10pow2 e).val) ∧
  (∀ e : JInt .i64, 0 ≤ e.val → e.val < 2621 → FloorLog10 5 e.val (log10pow5 e).val) ∧
  (∀ e : JInt .i64, 0 ≤ e.val → e.val < 3529 → CeilLog2Pow5 e.val.toNat (pow5bits e).val)

/-- The docstrings as written: "valid for all `e < 1651`" and "valid for all `e < 2621`". -/
def LogApproxDoc : Prop :=
  (∀ e : JInt .i64, e.val < 1651 → FloorLog10 2 e.val (log10pow2 e).val) ∧
  (∀ e : JInt .i64, e.val < 2621 → FloorLog10 5 e.val (log10pow5 e).val)

/-- The `mulshift` docstring (`base/ryu/utils.jl:44-48`): for `j ≥ 8*sizeof(U)` the
result is `(m * mul) >> j` reduced to `promote_type(U, UInt32)`. -/
def MulshiftExact : Prop :=
  ∀ u : IntTy, u ∈ [IntTy.u16, .u32, .u64] →
    ∀ (m : JInt u) (mul : JInt (widenTy u)) (j : Int), (u.bits : Int) ≤ j →
      (mulshift u m mul j).val = (m.val * mul.val / 2 ^ j.toNat) % 2 ^ (promU32 u).bits ∧
      (mulshiftinvsplit u mul m m m j).1 = mulshift u m mul j ∧
      (mulshiftsplit u mul m m m j).2.2 = mulshift u m mul j

/-- `n` decimal digits: `v < 10^n` and, unless `n == 1`, `10^(n-1) ≤ v`. -/
def IsNDigits (v : Int) (n : Nat) : Prop := 1 ≤ n ∧ v < 10 ^ n ∧ (n = 1 ∨ 10 ^ (n - 1) ≤ v)

instance : Decidable (IsNDigits v n) := by unfold IsNDigits; infer_instance

/-- The docstring "The number of decimal digits of the integer `v`"
(`base/ryu/utils.jl:89-93`) for every `UInt64` and `UInt32`. -/
def DecimallengthDoc : Prop :=
  (∀ v : JInt .u64, IsNDigits v.val (decimallength v.val)) ∧
  (∀ v : JInt .u32, IsNDigits v.val (decimallength32 v))

/-- `decimallength` counts digits on every value its callers pass: below `10^17`
(the at most 17-digit Float64 significands, `base/ryu/shortest.jl:334`) for the
generic method, below `10^9` (`mod1e9` results) for `UInt32`, and every `UInt16`. -/
def DecimallengthRange : Prop :=
  (∀ v : JInt .u64, v.val < 10 ^ 17 → IsNDigits v.val (decimallength v.val)) ∧
  (∀ v : JInt .u32, v.val < 10 ^ 9 → IsNDigits v.val (decimallength32 v)) ∧
  (∀ v : JInt .u16, IsNDigits v.val (decimallength16 v))

/-- The `umul256` docstring (`base/ryu/utils.jl:148-152`): `pLo + pHi<<128 == a * b`
with `b = bLo + bHi<<64`; `umul256_hi` is `(a*b) >> 128`. `nv` is the value of an
unsigned integer as a natural number. -/
def Umul256Exact : Prop :=
  ∀ (a : JInt .u128) (bHi bLo : JInt .u64),
    nv (umul256 a bHi bLo).1 + 2 ^ 128 * nv (umul256 a bHi bLo).2 = nv a * (nv bLo + 2 ^ 64 * nv bHi) ∧
    nv (umul256Hi a bHi bLo) = nv a * (nv bLo + 2 ^ 64 * nv bHi) / 2 ^ 128

/-- `mod1e9(v) == (v % 10^9) % UInt32` (the comment at `base/ryu/utils.jl:186-187`) and
the `mulshiftmod1e9` docstring: `((m * mul) >> j) % 10^9` for `j ≥ 128`. -/
def Mod1e9Exact : Prop :=
  (∀ v : JInt .u128, nv (mod1e9 v) = nv v % 10 ^ 9) ∧
  (∀ (m mula mulb mulc : JInt .u64) (j : Int), 128 ≤ j →
    nv (mulshiftmod1e9 m mula mulb mulc j) =
      nv m * (nv mula + 2 ^ 64 * nv mulb + 2 ^ 128 * nv mulc) / 2 ^ j.toNat % 10 ^ 9)

/-- `pow5` (`base/ryu/utils.jl:59-80`) answers "`5^p` divides `x`" under its stated
assumptions `0 < x < 2^53`, `0 ≤ p ≤ 308`, and for every `x` when `p ≤ qinvbound(T)`
(the guard at `base/ryu/shortest.jl:58`); `pow2` answers "`2^p` divides `x`" for every
unsigned `x` and `p ≥ 0`, so in particular for `p < qbound(T)`. -/
def Pow5Pow2Exact : Prop :=
  (∀ (x : JInt .u64) (p : JInt .i64), 0 < x.val → x.val < 2 ^ 53 → 0 ≤ p.val → p.val ≤ 308 →
    (pow5 x p = true ↔ (5 ^ p.val.toNat : Int) ∣ x.val)) ∧
  (∀ (T : FT) (x : JInt .u64) (p : JInt .i64), 0 ≤ p.val → p.val ≤ qinvbound T →
    (pow5 x p = true ↔ (5 ^ p.val.toNat : Int) ∣ x.val)) ∧
  (∀ (x : JInt .u64) (p : Nat), pow2 x p = true ↔ (2 ^ p : Int) ∣ x.val) ∧
  (∀ (x : JInt .u32) (p : Nat), pow2 x p = true ↔ (2 ^ p : Int) ∣ x.val) ∧
  (∀ T : FT, qbound T < 64 ∧ qinvbound T < qbound T)

/-- The index helpers of `base/ryu/utils.jl:55-57`: `indexforexp(e)` is
`ceil(e / 16)` for `e ≥ 0`, `pow10bitsforindex(idx) == 16idx + 120`, and for every
table index `idx < 64`, `lengthforindex(idx) == div(log10pow2(16idx) + 25, 9)` and the
hard-coded `POW10_OFFSET[idx + 1]` (`base/ryu/utils.jl:330-338`) is the sum of
`lengthforindex` over the earlier indices, 1224 in total (the length of `POW10_SPLIT`). -/
def IndexHelpers : Prop :=
  (∀ e : JInt .i64, 0 ≤ e.val → e.val < 2 ^ 62 →
    ∃ k, indexforexp e = .ok k ∧ e.val ≤ 16 * k.val ∧ 16 * k.val < e.val + 16) ∧
  (∀ idx : JInt .i64, 0 ≤ idx.val → idx.val < 2 ^ 58 → (pow10bitsforindex idx).val = 16 * idx.val + 120) ∧
  (∀ idx : Nat, idx < 64 →
    (lengthforindex (JInt.lit .i64 idx)).toOption.map (·.val) =
      some (((log10pow2 (JInt.lit .i64 (16 * idx))).val + 25) / 9) ∧
    pow10Offset.getD idx 0 =
      ((List.range idx).map (fun (k : Nat) => ((lengthforindex (JInt.lit .i64 k)).toOption.map (·.val)).getD 0)).sum) ∧
  ((List.range 64).map (fun (k : Nat) => ((lengthforindex (JInt.lit .i64 k)).toOption.map (·.val)).getD 0)).sum = 1224
where
  /-- `POW10_OFFSET`, `base/ryu/utils.jl:330-338`. -/
  pow10Offset : List Int := [
    0, 2, 5, 8, 12, 16, 21, 26, 32, 39,
    46, 54, 62, 71, 80, 90, 100, 111, 122, 134,
    146, 159, 173, 187, 202, 217, 233, 249, 266, 283,
    301, 319, 338, 357, 377, 397, 418, 440, 462, 485,
    508, 532, 556, 581, 606, 632, 658, 685, 712, 740,
    769, 798, 828, 858, 889, 920, 952, 984, 1017, 1050,
    1084, 1118, 1153, 1188]

/-- `append_sign` writes `'-'` exactly for a set sign bit of a non-NaN, else `'+'` for
`plus`, else `' '` for `space`, and advances `pos` by the bytes written;
`append_d_digits` writes the first digit, `decchar`, then the other `olength - 1`
digits, and returns `pos + olength + 1` (the comment at `base/ryu/utils.jl:229`). -/
def AppendSignDigits : Prop :=
  (∀ (x : FloatBits) (plus space : Bool) (pos : Int),
    let (c, p) := appendSign x plus space pos
    (c = some 45 ↔ x.signbit ∧ !x.isnan) ∧
    (c = some 43 ↔ ¬ (x.signbit ∧ !x.isnan) ∧ plus) ∧
    (c = some 32 ↔ ¬ (x.signbit ∧ !x.isnan) ∧ !plus ∧ space) ∧
    p = pos + (if c.isSome then 1 else 0)) ∧
  (∀ (olength : Nat) (digits : Nat) (buf : Buf) (pos : Int) (decchar : Nat), 1 ≤ olength →
    let (b, p) := appendDDigits olength digits buf pos decchar
    p = pos + olength + 1 ∧
    b pos = 48 + digits / 10 ^ (olength - 1) % 10 ∧
    b (pos + 1) = decchar ∧
    (∀ k : Nat, 1 ≤ k → k < olength → b (pos + 1 + k) = 48 + digits / 10 ^ (olength - 1 - k) % 10) ∧
    (∀ i, (i < pos ∨ pos + olength + 1 ≤ i) → b i = buf i))

/-- The docstrings of `pow5invsplit` and `pow5split` (`base/ryu/utils.jl:271-312`): for
every `0 ≤ i < 3529` (where `pow5bits` is valid) the value is `floor(2^k/5^i) + 1` with
`k = pow5bits(i) - 1 + pow5_inv_bitcount(T)`, resp. `floor(5^i/2^k)` with
`k = pow5bits(i) - pow5_bitcount(T)` (shifting left for negative `k`), and it fits the
unsigned type twice as wide as `T`; `pow5split` has exactly `pow5_bitcount(T)`
significant bits. -/
def Pow5SplitFormulas : Prop :=
  ∀ (T : FT) (i : Nat), i < 3529 →
    (∃ v, pow5invsplit T i = .ok v ∧
      v.val = 2 ^ ((pow5bits (JInt.lit .i64 i)).val - 1 + pow5InvBitcount T).toNat / 5 ^ i + 1) ∧
    (∃ v, pow5split T i = .ok v ∧
      (let k := (pow5bits (JInt.lit .i64 i)).val - pow5Bitcount T
       v.val = if k ≥ 0 then 5 ^ i / 2 ^ k.toNat else 5 ^ i * 2 ^ (-k).toNat) ∧
      2 ^ (pow5Bitcount T - 1) ≤ v.val ∧ v.val < 2 ^ pow5Bitcount T)

/-- The docstring of `pow5invsplit`: "with `pow5_inv_bitcount(T)` significant bits". -/
def Pow5InvsplitBitcount : Prop :=
  ∀ (T : FT) (i : Nat), (i : Int) ≤ invImax T →
    ∃ v, pow5invsplit T i = .ok v ∧ 2 ^ (pow5InvBitcount T - 1) ≤ v.val ∧ v.val < 2 ^ pow5InvBitcount T

/-- The lookup docstrings (`base/ryu/utils.jl:286-290,314-318`): within the generated
tables, `pow5invsplit_lookup(T, i) == pow5invsplit(T, i)` and
`pow5split_lookup(T, i) == pow5split(T, i)`; the table sizes are those of the loop at
`base/ryu/utils.jl:292-298,320-326` (`i_max` 291, 30, 0 and 325, 47, 9). -/
def LookupTables : Prop :=
  (∀ (T : FT) (i : Int), 0 ≤ i → i ≤ invImax T → pow5invsplitLookup T i = some (pow5invsplit T i.toNat)) ∧
  (∀ (T : FT) (i : Int), 0 ≤ i → i ≤ splitImax T → pow5splitLookup T i = some (pow5split T i.toNat)) ∧
  (invImax .f64 = 291 ∧ invImax .f32 = 30 ∧ invImax .f16 = 0) ∧
  (splitImax .f64 = 325 ∧ splitImax .f32 = 47 ∧ splitImax .f16 = 9)

/-- `generateinversetables()` (`base/ryu/utils.jl:242-268`), for any number `n` of
indices and any loop bound: `POW10_OFFSET_2` has `n + 1` nondecreasing entries
starting at 0 and ending at `length(POW10_SPLIT_2)`, `MIN_BLOCK_2` has `n + 1` entries
ending in 0, and every stored limb is below `2^64`. -/
def InverseTablesShape : Prop :=
  ∀ n fuel : Nat,
    let (offs, mins, split) := generateinversetables n fuel
    offs.length = n + 1 ∧ mins.length = n + 1 ∧ mins.getLast? = some 0 ∧
    offs.head? = some 0 ∧ offs.getLast? = some split.length ∧
    offs.Pairwise (· ≤ ·) ∧
    (∀ t ∈ split, t.1 < 2 ^ 64 ∧ t.2.1 < 2 ^ 64 ∧ t.2.2 < 2 ^ 64)

end JuliaLean.MiscCov.RyuUtils
