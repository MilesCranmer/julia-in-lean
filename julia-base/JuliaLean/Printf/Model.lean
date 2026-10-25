import JuliaLean.Printf.Parser
import JuliaLean.Float
import JuliaLean.Float.Extras
import JuliaLean.ParsePrint.Ryu

/-!
`Printf.format(f::Format, args...)`, `stdlib/Printf/src/Printf.jl:284-950` at
master `bbfa0ce4150`.

**Buffer.** `format` allocates `computelen(...)` bytes and stores into them in
order. All stores except the `BigFloat` NUL terminator land at the current
position, so the buffer is modelled by the bytes written so far (`St.out`, whose
length is `pos - 1`) and its length (`St.cap`). A store past the end throws
`BoundsError` when Julia checks bounds; the digit stores at `Printf.jl:441-443`
are `@inbounds` and `mpfr_snprintf` is C, so those overrun the buffer silently
(`Error.unsafeWrite`). The first such store ends the model's run.

**Primitives taken by their specification.**
* `ndigits(x, base=b, pad=1)` for `b ∈ {8, 10, 16}` is the exact number of
  base-`b` digits of `|x|`, at least one; the digit loop at `Printf.jl:440-452`
  then writes exactly the base-`b` digits of `|x|`.
* `Ryu.writefixed`/`Ryu.writeexp` (`base/ryu/fixed.jl`, `base/ryu/exp.jl`):
  their argument checks, sign and special cases (zero, NaN, Inf) and the trimming
  of trailing zeros are mirrored; the digits of a finite nonzero value are the
  exact binary value rounded to the requested decimal place, ties to even.
* `mpfr_snprintf` (`Printf.jl:490-492`) prints the exact `BigFloat` value by the
  C99 rules (`c99Float`), returning the full length and storing at most `size - 1`
  characters followed by NUL.
* `textwidth(c)` and the UTF-8 code units of each character are the `Glyph`
  fields; `textwidth(s)` is their sum.

`Ryu.writeshortest` (the `%g` path for Inf and NaN), `frexp`, `ldexp`, `round`
and IEEE multiplication are the ParsePrint and Float areas' line-by-line models.
Argument and conversion combinations outside this list are `Error.unmodelled`.
-/

namespace JuliaLean.Printf

open JuliaLean JuliaLean.Float

/-! ## Integers and buffers -/

/-- `Base.checked_add` on `Int`. -/
def cadd (a b : I) : Result I :=
  let s := a.val + b.val
  if IntTy.min .i64 ≤ s ∧ s ≤ IntTy.max .i64 then .ok (ix s)
  else .error (.julia (.overflowError "checked_add"))

/-- `max(a, b)` on `Int`. -/
def imax (a b : I) : I := if a.val < b.val then b else a

/-- `min(a, b)` on `Int`. -/
def imin (a b : I) : I := if b.val < a.val then b else a

/-- `n` copies of byte `b`: the loops `for _ = 1:n`. -/
def rep (b : Nat) (n : Int) : Bytes := List.replicate n.toNat b

/-- The buffer: the bytes before `pos`, and `length(buf)`. -/
structure St where
  out : Bytes
  cap : Nat
  deriving DecidableEq, Repr

/-- Consecutive stores at `pos`, `pos + 1`, ...; `checked` is false under `@inbounds`. -/
def put (checked : Bool) (bs : Bytes) (st : St) : Result St :=
  if st.out.length + bs.length ≤ st.cap then .ok {st with out := st.out ++ bs}
  else .error (if checked then .julia .boundsError else .unsafeWrite)

/-- A digit of `b"0123456789abcdef"` or `b"0123456789ABCDEF"`, `Printf.jl:281-282`. -/
def hexdig (upper : Bool) (d : Nat) : Nat := if d < 10 then 48 + d else (if upper then 55 else 87) + d

/-- The `k` low base-`b` digits of `m`, most significant first. -/
def lowDigits (b : Nat) (upper : Bool) : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, m => lowDigits b upper k (m / b) ++ [hexdig upper (m % b)]

/-- Number of base-`b` digits of `m`, at least one (`fuel` bounds the recursion). -/
def ndig (b : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, m => if m < b then 1 else 1 + ndig b fuel (m / b)

/-- `ndigits(m, base=b, pad=1)` for `b ≥ 2`. -/
def ndigits (b m : Nat) : Nat := ndig b m m

/-- `string(m, base=b)` digits. -/
def digits (b : Nat) (upper : Bool) (m : Nat) : Bytes := lowDigits b upper (ndigits b m) m

/-! ## Arguments -/

/-- A character: its UTF-8 code units (`ncodeunits`, `writechar`) and `textwidth`. -/
structure Glyph where
  bytes : Bytes
  width : Nat
  deriving DecidableEq, Repr

/-- `Integer` arguments: `BitInteger`s, `BigInt` and `Bool`. -/
inductive IntegerValue where
  | bits (t : IntTy) (x : JInt t)
  | big (x : Int)
  | bool (b : Bool)

/-- The mathematical value. -/
def IntegerValue.value : IntegerValue → Int
  | .bits _ x => x.val
  | .big x => x
  | .bool b => if b then 1 else 0

/-- `BigFloat`: an exact finite value `(-1)^neg * num / den`, or a nonfinite value
(which `Printf.jl:520` converts to `Float64`). -/
inductive BigVal where
  | finite (neg : Bool) (num den : Nat)
  | nonfinite (x : F64)

/-- The modelled argument types. -/
inductive Arg where
  | int (v : IntegerValue)
  | f64 (x : F64)
  | big (x : BigVal)
  | str (gs : List Glyph)
  | sym (gs : List Glyph)
  | chr (g : Glyph)

/-- `textwidth` of a glyph list. -/
def textwidth (gs : List Glyph) : Nat := (gs.map Glyph.width).sum

/-- `sizeof(string(x))`. -/
def sizeofGlyphs (gs : List Glyph) : Nat := (gs.map (·.bytes.length)).sum

/-! ## Dynamic width and precision -/

/-- `x::Integer` and the conversion to `Int` in the `Spec` constructor. -/
def toInt : Arg → Result I
  | .int v => match JInt.convert .i64 v.value with
    | .ok n => .ok n
    | .error e => .error (.julia e)
  | _ => .error .typeError

/-- `rmdynamic`, `Printf.jl:297-311`. -/
def rmdynamic (s : Spec) (args : List Arg) : Result (Spec × List Arg) := do
  let (w, args) ← if s.dynamicWidth then match args with
    | [] => .error (.julia .boundsError)
    | a :: r => do pure (← toInt a, r)
    else pure (s.width, args)
  let (p, zero, args) ← if s.dynamicPrecision then match args with
    | [] => .error (.julia .boundsError)
    | a :: r => do
      let p ← toInt a
      pure (p, if s.zero && isInts s.conv && p.val > 0 then false else s.zero, r)
    else pure (s.precision, s.zero, args)
  pure ({s with width := w, precision := p, zero := zero,
                dynamicWidth := false, dynamicPrecision := false}, args)

/-! ## Characters and strings, `Printf.jl:318-377` -/

/-- `fmt(buf, pos, arg, spec::Spec{<:Chars})`. -/
def fmtChar (s : Spec) (g : Glyph) (st : St) : Result St := do
  let w : Int := g.width
  let st ← if !s.leftalign && s.width.val > w then put true (rep 32 (s.width.val - w)) st else pure st
  let st ← put true g.bytes st
  if s.leftalign && s.width.val > w then put true (rep 32 (s.width.val - w)) st else pure st

/-- What `fmt` knows about the argument of a string conversion. -/
inductive StrKind where
  | string | symbol | other
  deriving DecidableEq

/-- The character loop of `Printf.jl:361-365`: subtract the width, stop when negative. -/
def strLoop : Int → List Glyph → Bytes × Int
  | p, [] => ([], p)
  | p, g :: gs =>
    let p := p - g.width
    if p < 0 then ([], p) else
      let (out, p) := strLoop p gs
      (g.bytes ++ out, p)

/-- `fmt(buf, pos, arg, spec::Spec{<:Strings})`, `Printf.jl:339-377`. -/
def fmtString (s : Spec) (kind : StrKind) (gs : List Glyph) (st : St) : Result St := do
  let slen : Int := textwidth gs + (if s.hash then (if kind == .string then 2 else 1) else 0)
  let op : Int := if s.precision.val == -1 then slen else min slen s.precision.val
  let st ← if !s.leftalign && s.width.val > op then put true (rep 32 (s.width.val - op)) st else pure st
  let (st, p) ← if s.hash && kind == .symbol then do pure (← put true [58] st, op - 1)
    else if s.hash && kind == .string then do pure (← put true [34] st, op - 1)
    else pure (st, op)
  let (body, p) := strLoop p gs
  let st ← put true body st
  let st ← if s.hash && kind == .string && p > 0 then put true [34] st else pure st
  if s.leftalign && s.width.val > op then put true (rep 32 (s.width.val - op)) st else pure st

/-! ## Integers, `Printf.jl:386-462` -/

/-- `fmt(buf, pos, arg, spec::Spec{<:Ints})` for an `Integer` argument. -/
def fmtInt (s : Spec) (v : IntegerValue) (st : St) : Result St := do
  let c := s.conv
  let bs := base c
  let mag := v.value.natAbs
  let n := ix (ndigits bs mag)
  let neg := decide (v.value < 0)
  let width := s.width
  let prec := s.precision
  let arglen := n + ix (if neg || (s.plus || s.space) then 1 else 0) +
    ix (if c == co && s.hash then 1 else 0) +
    ix (if c == cx && s.hash then 2 else 0) + ix (if c == cX && s.hash then 2 else 0)
  let arglen2 := if arglen.val < width.val && prec.val > 0 then
      arglen + imin (imax (ix 0) (prec - n)) (width - arglen) else arglen
  let st ← if !s.leftalign && !s.zero && arglen2.val < width.val then
      put true (rep 32 (width - arglen2).val) st else pure st
  let st ← if neg then put true [45] st else if s.plus then put true [43] st
    else if s.space then put true [32] st else pure st
  let st ← if c == co && s.hash then put true [48] st
    else if c == cx && s.hash then put true [48, 120] st
    else if c == cX && s.hash then put true [48, 88] st else pure st
  let st ← if s.zero && arglen2.val < width.val then put true (rep 48 (width - arglen2).val) st
    else if n.val < prec.val then put true (rep 48 (prec - n).val) st
    else if arglen.val < arglen2.val then put true (rep 48 (arglen2 - arglen).val) st
    else pure st
  let st ← put false (lowDigits bs (c != cx) (ndigits bs mag) mag) st
  if s.leftalign && arglen2.val < width.val then put true (rep 32 (width - arglen2).val) st
  else pure st

/-! ## Decimal rounding of exact values (the specification of Ryu and MPFR digits) -/

/-- `n / d` rounded to an integer, ties to even. -/
def rhe (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- `n / d * 10^k` rounded to an integer, ties to even. -/
def rheScaled (n d : Nat) (k : Int) : Nat :=
  if k ≥ 0 then rhe (n * 10 ^ k.toNat) d else rhe n (d * 10 ^ (-k).toNat)

/-- `floor(log10(n / d))` for positive `n`, `d`. -/
def flog10 (n d : Nat) : Int :=
  let k : Int := (ndigits 10 n : Int) - (ndigits 10 d : Int)
  let below := if k ≥ 0 then decide (n < d * 10 ^ k.toNat) else decide (n * 10 ^ (-k).toNat < d)
  if below then k - 1 else k

/-- Positive `n / d` rounded to `prec + 1` significant digits: `(m, e)` with
`10^prec ≤ m < 10^(prec+1)` and value `≈ m * 10^(e - prec)`. -/
def sci (n d prec : Nat) : Nat × Int :=
  let e := flog10 n d
  let m := rheScaled n d ((prec : Int) - e)
  if m == 10 ^ (prec + 1) then (10 ^ prec, e + 1) else (m, e)

/-- Zero characters. -/
def zeros (n : Nat) : Bytes := List.replicate n 48

/-- `m` written with at least `k` digits. -/
def padDigits (k m : Nat) : Bytes := let ds := digits 10 false m; zeros (k - ds.length) ++ ds

/-- The trailing-zero loop of `base/ryu/fixed.jl:176-183` / `exp.jl:150-157`. -/
def trimZeros (hash : Bool) (bs : Bytes) : Bytes :=
  let r := bs.reverse.dropWhile (· == 48)
  (if r.head? == some 46 && !hash then r.tail else r).reverse

/-- The exponent part after the exponent character, `base/ryu/exp.jl:160-180`. -/
def expPart (e : Int) : Bytes := (if e < 0 then [45] else [43]) ++ padDigits 2 e.natAbs

/-- `Ryu.writefixed(buf, pos, x, precision, plus, space, hash, '.', trim)`. -/
def writefixed (x : F64) (prec : Int) (plus space hash trim : Bool) : Result Bytes :=
  if prec < 0 then .error (.julia (.argumentError "precision must be non-negative")) else
  let sign := ParsePrint.Ryu.appendSign x plus space
  if F64.iszero x then
    .ok (sign ++ [48] ++ (if prec > 0 && !trim then 46 :: zeros prec.toNat else if hash then [46] else []))
  else if F64.isnan x then .ok (sign ++ [78, 97, 78])
  else if !F64.isfinite x then .ok (sign ++ [73, 110, 102])
  else
    let (num, den) := F64.toRat x
    let p := prec.toNat
    let m := rheScaled num.natAbs den prec
    let frac := prec > 0 || hash
    let body := sign ++ digits 10 false (m / 10 ^ p) ++
      (if frac then 46 :: (if p = 0 then [] else padDigits p (m % 10 ^ p)) else [])
    .ok (if trim && frac then trimZeros hash body else body)

/-- `Ryu.writeexp(buf, pos, x, precision, plus, space, hash, expchar, '.', trim)`. -/
def writeexp (x : F64) (prec : Int) (plus space hash : Bool) (expchar : Nat) (trim : Bool) :
    Result Bytes :=
  if prec < 0 then .error (.julia (.argumentError "precision must be non-negative")) else
  let sign := ParsePrint.Ryu.appendSign x plus space
  if F64.iszero x then
    .ok (sign ++ [48] ++ (if prec > 0 && !trim then 46 :: zeros prec.toNat else if hash then [46] else []) ++
      [expchar, 43, 48, 48])
  else if F64.isnan x then .ok (sign ++ [78, 97, 78])
  else if !F64.isfinite x then .ok (sign ++ [73, 110, 102])
  else
    let (num, den) := F64.toRat x
    let (m, e) := sci num.natAbs den prec.toNat
    let ds := digits 10 false m
    let mant := ds.take 1 ++ (if prec > 0 then 46 :: ds.drop 1 else if hash then [46] else [])
    .ok (sign ++ (if trim then trimZeros hash mant else mant) ++ [expchar] ++ expPart e)

/-! ## Floats, `Printf.jl:500-678` -/

/-- Number of bits of `u` (`64 - leading_zeros(u)` for a `UInt64`). -/
def bitlen : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, u => if u == 0 then 0 else 1 + bitlen fuel (u / 2)

/-- `trailing_zeros(u)` for a nonzero `UInt64`. -/
def tzeros : Nat → Nat → Nat
  | 0, _ => 64
  | fuel + 1, u => if u % 2 == 1 then 0 else 1 + tzeros fuel (u / 2)

/-- The `%a`/`%A` branch, `Printf.jl:553-646`, for `x::Float64`. -/
def fmtHex (x : F64) (s : Spec) (upper : Bool) : Bytes :=
  let neg := F64.lt x (F64.zero false) || x == F64.zero true
  let x := if neg then F64.neg x else x
  let sign := if neg then [45] else if s.plus then [43] else if s.space then [32] else []
  let pch := if upper then 80 else 112
  if F64.isnan x then sign ++ [78, 97, 78]
  else if !F64.isfinite x then sign ++ [73, 110, 102]
  else
    let lead := [48, if upper then 88 else 120]
    let prec := s.precision.val
    if F64.iszero x then
      sign ++ lead ++ [48] ++ (if prec > 0 then 46 :: zeros prec.toNat else []) ++ [pch, 43, 48]
    else
      let (u, n, p) :=
        if prec > -1 then
          let (sf, p) := F64.frexp x
          let sigbits := 4 * min prec 13
          let sf := F64.mul (F64.ofBits 0x3FD0000000000000) (F64.round (F64.ldexp sf (1 + sigbits)))
          let u := (F64.toBits sf % 2 ^ 54) / 2 ^ (52 - sigbits).toNat
          (u, (bitlen 64 u + 3) / 4, p)
        else
          let (sf, p) := F64.frexp x
          let sf := F64.mul sf (F64.ofBits 0x4000000000000000)
          let u := F64.toBits sf % 2 ^ 53
          let t := tzeros 64 u / 4
          (u / 2 ^ (4 * t), 14 - t, p)
      let frac := u > 9 || s.hash || prec > 0
      let ds := lowDigits 16 upper n u
      let e := p - 1
      sign ++ lead ++ ds.take 1 ++ (if frac then [46] else []) ++ ds.drop 1 ++
        zeros (prec - (n - 1 : Int)).toNat ++ [pch] ++ (if e < 0 then [45] else [43]) ++
        digits 10 false e.natAbs

/-- `Printf.tofloat` followed by the `BigFloat` test of `Printf.jl:503-521`. -/
inductive FloatArg where
  | f64 (x : F64)
  | bigFinite (neg : Bool) (num den : Nat)

def toFloat : Arg → Result FloatArg
  | .f64 x => .ok (.f64 x)
  | .int v => .ok (.f64 (F64.ofInt v.value))
  | .big (.finite neg n d) => .ok (.bigFinite neg n d)
  | .big (.nonfinite x) => .ok (.f64 x)
  | _ => .error (.julia (.methodError "Float64"))

/-- The width padding of `Printf.jl:647-676` around the bytes of the number. -/
def padFloat (s : Spec) (x : F64) (num : Bytes) : Bytes :=
  let len : Int := num.length
  if len < s.width.val then
    let n := s.width.val - len
    if s.leftalign then num ++ rep 32 n
    else if s.zero && F64.isfinite x then
      let ex := (if num.head? == some 45 || (s.plus || s.space) then 1 else 0) +
        (if isHexA s.conv then 2 else 0)
      num.take ex ++ rep 48 n ++ num.drop ex
    else rep 32 n ++ num
  else num

/-- The Float64 branches of `fmt(buf, pos, arg, spec::Spec{<:Floats})`. -/
def floatBytes (s : Spec) (x : F64) : Result Bytes := do
  let c := s.conv
  let prec := s.precision.val
  if c == ce || c == cE then writeexp x prec s.plus s.space s.hash c false
  else if c == cf || c == cF then writefixed x prec s.plus s.space s.hash false
  else if c == cg || c == cG then
    if F64.isinf x || F64.isnan x then
      pure (ParsePrint.Ryu.writeshortest x s.plus s.space true (-1) ParsePrint.Ryu.chE false
        ParsePrint.Ryu.chDot false)
    else
      let prec := if prec == 0 then 1 else prec
      let b ← writeexp x prec false false false ce false
      let k := b.length
      let at_ (i : Nat) : Int := b.getD (k - i) 0
      let z : Int := 48
      let exp : Int := if at_ 4 == 101 then
          (if at_ 3 == 43 then 1 else -1) * (10 * (at_ 2 - z) + (at_ 1 - z))
        else (if at_ 4 == 43 then 1 else -1) * (100 * (at_ 3 - z) + 10 * (at_ 2 - z) + (at_ 1 - z))
      if -4 ≤ exp ∧ exp < prec then writefixed x (prec - (exp + 1)) s.plus s.space s.hash (!s.hash)
      else writeexp x (prec - 1) s.plus s.space s.hash (if c == cg then ce else cE) (!s.hash)
  else pure (fmtHex x s (c == cA))

/-! ## C99 7.19.6.1 reference for floating conversions of exact values -/

/-- C99 `e`/`E`/`f`/`F`/`g`/`G` (and `a`/`A` are not used here) of the finite value
`(-1)^neg * num / den`, without the field width: sign, digits, exponent. -/
def c99FloatBody (s : Spec) (neg : Bool) (num den : Nat) (prec : Nat) : Bytes :=
  let sign := if neg then [45] else if s.plus then [43] else if s.space then [32] else []
  let c := s.conv
  let fixed (p : Nat) : Bytes :=
    let m := rheScaled num den p
    digits 10 false (m / 10 ^ p) ++
      (if p > 0 || s.hash then 46 :: (if p = 0 then [] else padDigits p (m % 10 ^ p)) else [])
  let expo (p : Nat) (ech : Nat) : Bytes × Int :=
    let (m, e) := if num = 0 then (0, 0) else sci num den p
    let ds := if num = 0 then zeros (p + 1) else digits 10 false m
    (ds.take 1 ++ (if p > 0 || s.hash then 46 :: ds.drop 1 else []) ++ [ech] ++ expPart e, e)
  if c == cf || c == cF then sign ++ fixed prec
  else if c == ce || c == cE then sign ++ (expo prec c).1
  else
    let P := if prec = 0 then 1 else prec
    let (eb, X) := expo (P - 1) (if c == cg then ce else cE)
    let isFixed := decide ((P : Int) > X ∧ X ≥ -4)
    let body := if isFixed then fixed (P - (X + 1)).toNat else eb
    -- unless `#`, remove trailing zeros of the fraction, and the point if nothing follows it
    let body := if s.hash then body
      else if isFixed then (if body.contains 46 then trimZeros false body else body)
      else
        let mant := body.takeWhile (fun b => b != ce && b != cE)
        (if mant.contains 46 then trimZeros false mant else mant) ++ body.drop mant.length
    sign ++ body

/-- C99 field width: left adjustment, zero padding after the sign, or spaces. -/
def c99Pad (s : Spec) (body : Bytes) : Bytes :=
  let n : Int := s.width.val - body.length
  if n ≤ 0 then body
  else if s.leftalign then body ++ rep 32 n
  else if s.zero then
    let ex := if body.head? == some 45 || body.head? == some 43 || body.head? == some 32 then 1 else 0
    body.take ex ++ rep 48 n ++ body.drop ex
  else rep 32 n ++ body

/-- `string(spec; modifier="R")` interpreted by MPFR: C99 with the default
precision 6 when the precision is negative (`Printf.jl:46-56`). -/
def c99Float (s : Spec) (neg : Bool) (num den : Nat) : Result Bytes :=
  if isHexA s.conv then .error .unmodelled
  else
    let prec := if s.precision.val < 0 then 6 else s.precision.val.toNat
    .ok (c99Pad s (c99FloatBody s neg num den prec))

/-- `__BIG_FLOAT_MAX__`, `Printf.jl:498`. -/
def bigFloatMax : Nat := 8192

/-- The finite `BigFloat` branch, `Printf.jl:504-519`: `mpfr_snprintf` into the
`siz` bytes left; if the output needs more, `resize!(buf, required_length + 1)`
and print again at `pos`. -/
def fmtBigFloat (s : Spec) (neg : Bool) (num den : Nat) (st : St) : Result St := do
  let out ← c99Float s neg num den
  let pos := st.out.length + 1
  let siz : Int := (st.cap : Int) - pos + 1
  let r := out.length
  if (r : Int) > siz then
    if r > bigFloatMax then .error (.julia (.argumentError "BigFloat too large")) else
    -- resize!(buf, r + 1); mpfr writes r characters and NUL at pos
    let st := {out := st.out.take (r + 1), cap := r + 1 : St}
    if pos + r ≤ r + 1 ∧ st.out.length = pos - 1 then .ok {st with out := st.out ++ out}
    else .error .unsafeWrite
  else if (r : Int) < siz then .ok {st with out := st.out ++ out}
  else
    -- exactly `siz` characters: snprintf stores siz - 1 of them and NUL
    .ok {st with out := st.out ++ out.take (r - 1) ++ [0]}

/-- `fmt(buf, pos, arg, spec::Spec{<:Floats})`. -/
def fmtFloat (s : Spec) (a : Arg) (st : St) : Result St := do
  match ← toFloat a with
  | .bigFinite neg n d => fmtBigFloat s neg n d st
  | .f64 x => put true (padFloat s x (← floatBytes s x)) st

/-- `floatfmt(s)`, `Printf.jl:60-61`. -/
def floatfmt (s : Spec) : Spec := {s with conv := cf, precision := ix 0}

/-! ## Dispatch, `plength` and `format` -/

/-- `fmt(buf, pos, arg, spec)` after `rmdynamic`. -/
def fmtArg (s : Spec) (a : Arg) (st : St) : Result St :=
  if isChars s.conv then match a with
    | .chr g => fmtChar s g st
    | .str (g :: _) => fmtChar s g st
    | _ => .error .unmodelled
  else if isStrings s.conv then match a with
    | .str gs => fmtString s .string gs st
    | .sym gs => fmtString s .symbol gs st
    | .chr g => fmtString s .other [g] st
    | _ => .error .unmodelled
  else if isInts s.conv then match a with
    | .int v => fmtInt s v st
    | .f64 _ | .big _ => fmtFloat (floatfmt s) a st
    | _ => .error (.julia (.methodError "ndigits"))
  else if isFloats s.conv then fmtFloat s a st
  else .error .unmodelled

/-- `plength(f, x)`, `Printf.jl:874-901`; `D`, `O`, `U` have no method. -/
def plengthArg (s : Spec) (a : Arg) : Result I := do
  if isChars s.conv then
    let g ← match a with
      | .chr g => pure g
      | .str (g :: _) => pure g
      | _ => .error .unmodelled
    cadd (imax s.width (ix g.width)) (ix g.bytes.length - ix g.width)
  else if isStrings s.conv then
    let (gs, isSym) ← match a with
      | .str gs => pure (gs, false)
      | .sym gs => pure (gs, true)
      | .chr g => pure ([g], false)
      | _ => .error .unmodelled
    let sw := ix (textwidth gs)
    let p ← if s.precision.val == -1 then cadd sw (ix (if s.hash then (if isSym then 1 else 2) else 0))
      else pure s.precision
    cadd (imax s.width p) (ix (sizeofGlyphs gs) - sw)
  else if isInts s.conv then match a with
    | .int v => do
      let l ← cadd s.precision (ix (ndigits (base s.conv) v.value.natAbs))
      pure (imax s.width (← cadd l (ix 5)))
    | .f64 _ | .big _ => do
      let l ← cadd (ix (if s.hash then 1 else 0)) (ix 309)
      pure (imax s.width (← cadd l (ix 5)))
    | _ => .error (.julia (.methodError "ndigits"))
  else if isFloats s.conv then do
    let l ← cadd (ix (if s.hash then 1 else 0)) (ix 309)
    let l ← cadd l s.precision
    pure (imax s.width (← cadd l (ix 5)))
  else if s.conv == 112 || s.conv == 110 then .error .unmodelled
  else .error (.julia (.methodError "plength"))

/-- `computelen`, `Printf.jl:903-921` (checked additions as on master). -/
def computelen (f : Format) (args : List Arg) : Result I := do
  let rec go : List Spec → List Arg → I → Result I
    | [], _, len => pure len
    | s :: ss, args, len => do
      let (s, args) ← rmdynamic s args
      match args with
      | [] => .error (.julia .boundsError)
      | a :: rest => go ss rest (← cadd len (← plengthArg s a))
  go f.formats args (ix ((f.substrings.map List.length).sum))

/-- Writing a substring range with the `escapechar` state, `Printf.jl:822-831`. -/
def litBytes : Bool → Bytes → Bytes × Bool
  | esc, [] => ([], esc)
  | esc, b :: r =>
    if !esc then let (o, e) := litBytes (b == 37) r; (b :: o, e)
    else litBytes false r

/-- The loop of `format(buf, pos, f, args...)`, `Printf.jl:836-866`. -/
def formatLoop : List Spec → List Bytes → List Arg → Bool → St → Result St
  | [], _, _, _, st => .ok st
  | s :: ss, lit :: lits, args, esc, st => do
    let (s, args) ← rmdynamic s args
    match args with
    | [] => .error (.julia .boundsError)
    | a :: rest =>
      let st ← fmtArg s a st
      let (o, esc) := litBytes esc lit
      let st ← put true o st
      formatLoop ss lits rest esc st
  | _ :: _, [], _, _, _ => .error (.julia .boundsError)

/-- `Printf.format(f::Format, args...)`, `Printf.jl:945-950`. -/
def format (f : Format) (args : List Arg) : Result Bytes := do
  if f.numarguments != args.length then .error (.julia (.argumentError "argmismatch")) else
  let len ← computelen f args
  -- `StringVector(n)` converts `n` to `Csize_t`
  if len.val < 0 then .error (.julia (.inexactError "convert")) else
  let st : St := ⟨[], len.val.toNat⟩
  let (o, esc) := litBytes false (f.substrings.headD [])
  let st ← put true o st
  let st ← formatLoop f.formats f.substrings.tail args esc st
  pure st.out

/-- `@sprintf(fmt, args...)`: parse, then format. -/
def sprintf (fmt : String) (args : List Arg) : Result Bytes := do format (← parse fmt) args

end JuliaLean.Printf
