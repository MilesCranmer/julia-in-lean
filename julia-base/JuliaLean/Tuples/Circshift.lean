import JuliaLean.Tuples.Lemmas

/-!
`circshift` on tuples (`base/tuple.jl:717-724`) and on vectors
(`base/abstractarraymath.jl:335-337`, `base/multidimensional.jl:1257-1298`) for a
shift of any `BitInteger` type, and the proof that both rotate a tuple and the
vector of its elements in the same way (`circshiftAgrees`).
-/

namespace JuliaLean.Tuples

variable {α : Type}

/-- A `BitInteger` value together with its type. -/
abbrev AnyInt := (u : IntTy) × JInt u

/-- `promote(x, y)` for two `BitInteger`s, `base/promotion.jl:397-401,423-428` with the
rules of `base/int.jl:809-822`: `convert` both to the promoted type. -/
def promoteInts {s t : IntTy} (x : JInt s) (y : JInt t) :
    R (JInt (IntTy.promote s t) × JInt (IntTy.promote s t)) := do
  let a ← liftJ (JInt.convert (IntTy.promote s t) x.val)
  let b ← liftJ (JInt.convert (IntTy.promote s t) y.val)
  pure (a, b)

/-- `a - b` for `BitInteger`s, `base/int.jl:1092-1099`: both operands are wrapped
into `promote_type` (`a % T`), then the wrapping same-type `-`. -/
def subMixed {s t : IntTy} (a : JInt s) (b : JInt t) : JInt (IntTy.promote s t) :=
  JInt.rem (IntTy.promote s t) a - JInt.rem (IntTy.promote s t) b

/-- `a + b` for `BitInteger`s, `base/int.jl:1092-1099`. -/
def addMixed {s t : IntTy} (a : JInt s) (b : JInt t) : JInt (IntTy.promote s t) :=
  JInt.rem (IntTy.promote s t) a + JInt.rem (IntTy.promote s t) b

/-- `abs(y) = flipsign(y, y)` for a signed integer, `base/int.jl:234` (wraps at `typemin`). -/
def absSigned {t : IntTy} (y : JInt t) : JInt t := if y.val < 0 then -y else y

/-- `rem(x, y)` for `y::Int`. An unsigned `x` takes `rem(x::Unsigned, y::BitSigned) =
rem(x, unsigned(abs(y)))` (`base/int.jl:279`, `unsigned` reinterprets, `:262`); otherwise,
and then, `rem(x::Real, y::Real) = rem(promote(x, y)...)` (`base/promotion.jl:520`) and the
checked intrinsic (`base/int.jl:355-358`). -/
def remByInt {s : IntTy} (x : JInt s) (y : JInt64) : R AnyInt :=
  if s.signed then do
    let p ← promoteInts x y
    let r ← liftJ (JInt.remInt p.1 p.2)
    pure ⟨_, r⟩
  else do
    let u : JInt .u64 := JInt.rem .u64 (absSigned y)
    let p ← promoteInts x u
    let r ← liftJ (JInt.remInt p.1 p.2)
    pure ⟨_, r⟩

/-- `iseven(n::Real) = isinteger(n) && iszero(rem(Integer(n), 2))`, `base/int.jl:181`. -/
def iseven {s : IntTy} (n : JInt s) : R Bool := do
  let r ← remByInt n (JInt.lit .i64 2)
  pure (decide (r.2.val = 0))

/-- `mod1(x::Real, y::Real) = mod1(promote(x, y)...)` (`base/promotion.jl:522`), then
`mod1(x::T, y::T) = (m = mod(x, y); iszero(m) ? y : m)` (`base/operators.jl:914`) with the
same-type `mod` of `base/int.jl:331-351`. -/
def mod1 {s t : IntTy} (x : JInt s) (y : JInt t) : R (JInt (IntTy.promote s t)) := do
  let p ← promoteInts x y
  let m ← liftJ (JInt.mod p.1 p.2)
  pure (if m.val = 0 then p.2 else m)

/-- `mod(x, y)` for `y::Int`: `mod(x::Unsigned, y::Signed)` (`base/int.jl:347-350`:
`remval = signed(rem(x, y))`, then `remval + (!iszero(remval) && y < zero(y))*y`, the
`Bool*Int` product being `0` or `y`), otherwise `mod(x::Real, y::Real) =
mod(promote(x, y)...)` (`base/promotion.jl:521`) and the same-type method. -/
def modByInt {s : IntTy} (x : JInt s) (y : JInt64) : R AnyInt :=
  if s.signed then do
    let p ← promoteInts x y
    let m ← liftJ (JInt.mod p.1 p.2)
    pure ⟨_, m⟩
  else do
    let r ← remByInt x y
    let remval := JInt.rem r.1.toSigned r.2
    let c : JInt64 := if remval.val ≠ 0 ∧ y.val < 0 then y else JInt.lit .i64 0
    pure ⟨_, addMixed remval c⟩

/-- `circshift(t::Tuple, shift::Integer)`, `base/tuple.jl:717-724`: tuples of length 0
and 1 are returned; length 2 gives `iseven(shift) ? t : reverse(t)` (`reverse(t::Tuple) =
revargs(t...)`, `base/tuple.jl:671`); longer tuples use `len = N + 3`,
`j = mod1(shift, len)` and `ntuple(k -> getindex(x, k-j+ifelse(k>j,0,len)), Val(len))`
(`base/ntuple.jl:65-72`), with `k::Int`, the exact mixed comparison `k > j`
(`base/int.jl:578`, `base/promotion.jl`) and the wrapping mixed `-` and `+`. -/
def circshiftTuple (t : List α) (ty : IntTy) (shift : JInt ty) : R (List α) :=
  match t with
  | [] => .ok []
  | [a] => .ok [a]
  | [a, b] => do
    let e ← iseven shift
    pure (if e then [a, b] else revargs [a, b])
  | t@(_ :: _ :: _ :: _) => do
    let len : JInt64 := JInt.lit .i64 t.length
    let j ← mod1 shift len
    (List.range len.val.toNat).mapM fun (k : Nat) =>
      let kI : JInt64 := JInt.lit .i64 ((k : Int) + 1)
      let off : JInt64 := if kI.val > j.val then JInt.lit .i64 0 else len
      getindex t (.int _ (addMixed (subMixed kI j) off))

/-- `unitrange_last(start, stop)`, `base/range.jl:439-441`: `stop` when `stop >= start`,
else `start - 1` (wrapping). -/
def unitrangeLast {t : IntTy} (start stop : JInt t) : JInt t :=
  if stop.val ≥ start.val then stop else start - JInt.lit t 1

/-- `start:stop` for `BitInteger`s (`(:)(a::Real, b::Real) = (:)(promote(a, b)...)` and
`UnitRange{T}(start, stop)`, `base/range.jl:3,5,428`), then `convert(OrdinalRangeInt, r)`
in `CartesianIndices` (`base/multidimensional.jl:299-301`, `base/range.jl:1341`): the
`Int` endpoints `(first, last)`. -/
def unitRangeInt {s t : IntTy} (a : JInt s) (b : JInt t) : R (Int × Int) := do
  let p ← promoteInts a b
  let f ← liftJ (JInt.convert .i64 p.1.val)
  let l ← liftJ (JInt.convert .i64 (unitrangeLast p.1 p.2).val)
  pure (f.val, l.val)

/-- `length(r::UnitRange{Int})`, `base/range.jl:820-833`: `0` when empty, else
`(last -% first) + 1`. -/
def rangeLength (r : Int × Int) : Int :=
  if r.1 > r.2 then 0 else (JInt.wrap .i64 (r.2 - r.1 + 1)).val

/-- `checkbounds(A, I::CartesianIndex{1})` for a vector. -/
def checkIndex (v : List α) (i : Int) : R Unit :=
  if 1 ≤ i ∧ i ≤ v.length then .ok () else bounds

/-- `for I in CRsrc; @inbounds dest[I + ΔI] = src′[I]; end`
(`base/multidimensional.jl:1211-1213`, one dimension) over the source indices
`i, i+1, ..., i+k-1`; `I + ΔI` is `Int` addition. The bounds were checked before the
loop, so the `none` branch is never taken. -/
def copyLoop (src : List α) (delta : Int) : Int → Nat → List α → List α
  | _, 0, dest => dest
  | i, k + 1, dest =>
    match src[(i - 1).toNat]? with
    | some x => copyLoop src delta (i + 1) k (dest.set ((JInt.wrap .i64 (i + delta)).val - 1).toNat x)
    | none => dest

/-- `copyto!(dest, Rdest::CartesianIndices, src, Rsrc::CartesianIndices)`,
`base/multidimensional.jl:1190-1214`, for vectors; `src′ = unalias(dest, src)` is `src`
(the arrays are distinct) and `ΔI = first(Rdest) - first(Rsrc)`. -/
def copytoCartesian (dest src : List α) (rd rs : Int × Int) : R (List α) :=
  if rd.1 > rd.2 then .ok dest
  else if rangeLength rd ≠ rangeLength rs then
    argErr "source and destination must have same size"
  else do
    checkIndex dest rd.1
    checkIndex dest rd.2
    checkIndex src rs.1
    checkIndex src rs.2
    pure (copyLoop src (JInt.wrap .i64 (rd.1 - rs.1)).val rs.1 (rangeLength rs).toNat dest)

/-- `circshift!(dest, src, (shift,))`, `base/multidimensional.jl:1257-1263` (`dest` and
`src` are distinct with equal axes; `isempty(src) && return dest`;
`fill_to_length((shift,), 0, Val(1)) = (shift,)`), and `_circshift!`,
`base/multidimensional.jl:1284-1299`: `s = mod(d, length(ind1))`,
`sf, sl = first(ind1)+s, last(ind1)-s`, `r1, r2 = first(ind1):sf-1, sf:last(ind1)`,
`r3, r4 = first(ind1):sl, sl+1:last(ind1)`, then `copyto!` of `src[r4]` into `dest[r1]`
and of `src[r3]` into `dest[r2]`. `dest` holds the initial contents of `similar(a)`. -/
def circshiftVectorInto (dest src : List α) (ty : IntTy) (shift : JInt ty) : R (List α) :=
  if src.isEmpty then .ok dest
  else do
    let first : JInt64 := JInt.lit .i64 1
    let last : JInt64 := JInt.lit .i64 src.length
    let s ← modByInt shift (JInt.lit .i64 src.length)
    let sf := addMixed first s.2
    let sl := subMixed last s.2
    let r1 ← unitRangeInt first (subMixed sf (JInt.lit .i64 1))
    let r2 ← unitRangeInt sf last
    let r3 ← unitRangeInt first sl
    let r4 ← unitRangeInt (addMixed sl (JInt.lit .i64 1)) last
    let dest ← copytoCartesian dest src r1 r4
    copytoCartesian dest src r2 r3

/-- `circshift(a::AbstractArray, shiftamt::Real) = circshift!(similar(a), a,
(Integer(shiftamt),))`, `base/abstractarraymath.jl:335-337` (`Integer(x::Integer) = x`).
The contents of `similar(a)` are unspecified; this takes `a` itself, and
`circshiftVectorInto_spec` shows that every initial content gives the same result. -/
def circshiftVector (v : List α) (ty : IntTy) (shift : JInt ty) : R (List α) :=
  circshiftVectorInto v v ty shift

/-- `circshift(t, shift)` on a tuple and `circshift(collect(t), shift)` on the vector of
its elements agree for a shift of every `BitInteger` type. -/
def CircshiftAgrees : Prop :=
  ∀ (α : Type) [DecidableEq α] (t : List α) (ty : IntTy) (shift : JInt ty), t.length < 2 ^ 62 →
    SameOutcome (circshiftTuple t ty shift) (circshiftVector t ty shift)

/-! ## Proof -/

/-- Rotation to the right by `s ≤ length(t)` positions. -/
def rotateRight (t : List α) (s : Nat) : List α := t.drop (t.length - s) ++ t.take (t.length - s)

section Arith

private theorem i64_min : IntTy.i64.min = -9223372036854775808 := by decide
private theorem i64_max : IntTy.i64.max = 9223372036854775807 := by decide

private theorem wrapInt_emod (t : IntTy) (x : Int) : wrapInt t x % 2 ^ t.bits = x % 2 ^ t.bits := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

private theorem wrapInt_congr (t : IntTy) (x y : Int) (h : x % 2 ^ t.bits = y % 2 ^ t.bits) :
    wrapInt t x = wrapInt t y := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> omega

private theorem wrap_add_l (t : IntTy) (x y : Int) : wrapInt t (wrapInt t x + y) = wrapInt t (x + y) := by
  apply wrapInt_congr; rw [Int.add_emod, wrapInt_emod, ← Int.add_emod]

private theorem wrap_sub_l (t : IntTy) (x y : Int) : wrapInt t (wrapInt t x - y) = wrapInt t (x - y) := by
  apply wrapInt_congr; rw [Int.sub_emod, wrapInt_emod, ← Int.sub_emod]

private theorem wrap_sub_r (t : IntTy) (x y : Int) : wrapInt t (x - wrapInt t y) = wrapInt t (x - y) := by
  apply wrapInt_congr; rw [Int.sub_emod, wrapInt_emod, ← Int.sub_emod]

private theorem wrap_mul_l (t : IntTy) (x y : Int) : wrapInt t (wrapInt t x * y) = wrapInt t (x * y) := by
  apply wrapInt_congr; rw [Int.mul_emod, wrapInt_emod, ← Int.mul_emod]

private theorem add_val' {t : IntTy} (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
private theorem sub_val' {t : IntTy} (a b : JInt t) : (a - b).val = wrapInt t (a.val - b.val) := rfl
private theorem mul_val' {t : IntTy} (a b : JInt t) : (a * b).val = wrapInt t (a.val * b.val) := rfl
private theorem rem_val' {t u : IntTy} (a : JInt t) : (JInt.rem u a).val = wrapInt u a.val := rfl
private theorem lit_val' (t : IntTy) (x : Int) : (JInt.lit t x).val = wrapInt t x := rfl

private theorem bits_promote (s t : IntTy) : (IntTy.promote s t).bits = max s.bits t.bits := by
  unfold IntTy.promote
  split
  · omega
  · split
    · omega
    · split <;> omega

private theorem bits_toSigned (u : IntTy) : u.toSigned.bits = u.bits := by cases u <;> rfl

private theorem tmin_nonpos (t : IntTy) : t.min ≤ 0 := by cases t <;> decide

private theorem signed_min (t : IntTy) (h : t.signed = true) : t.min = -t.max - 1 := by
  cases t <;> first | decide | exact absurd h (by decide)

private theorem unsigned_min (t : IntTy) (h : t.signed = false) : t.min = 0 := by
  cases t <;> first | decide | exact absurd h (by decide)

private theorem wide {u : IntTy} (h : 64 ≤ u.bits) : u.min ≤ 0 ∧ 4611686018427387905 ≤ u.max := by
  cases u <;> first | decide | exact absurd h (by decide)

private theorem inr {u : IntTy} (h : 64 ≤ u.bits) {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 4611686018427387905) :
    u.min ≤ x ∧ x ≤ u.max := by
  have := wide h; exact ⟨by omega, by omega⟩

private theorem wrap_small {u : IntTy} (h : 64 ≤ u.bits) {x : Int} (h0 : 0 ≤ x)
    (h1 : x ≤ 4611686018427387905) : wrapInt u x = x :=
  wrapInt_of_inRange u x (inr h h0 h1)

private theorem i64_wrap {x : Int} (h0 : -4611686018427387905 ≤ x) (h1 : x ≤ 4611686018427387905) :
    wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x ⟨by rw [i64_min]; omega, by rw [i64_max]; omega⟩

private theorem signed_wide (ty : IntTy) (h : ty.signed = true) :
    (IntTy.promote ty .i64).min ≤ -4611686018427387905 := by
  cases ty <;> first | decide | exact absurd h (by decide)

private theorem contains_i64 (ty : IntTy) :
    (IntTy.promote ty .i64).min ≤ ty.min ∧ ty.max ≤ (IntTy.promote ty .i64).max := by
  cases ty <;> decide

private theorem contains_u64 (ty : IntTy) (h : ty.signed = false) :
    (IntTy.promote ty .u64).min ≤ ty.min ∧ ty.max ≤ (IntTy.promote ty .u64).max := by
  cases ty <;> first | decide | exact absurd h (by decide)

private theorem in_i64 {ty : IntTy} (x : JInt ty) :
    (IntTy.promote ty .i64).min ≤ x.val ∧ x.val ≤ (IntTy.promote ty .i64).max := by
  have := contains_i64 ty; have := x.property; exact ⟨by omega, by omega⟩

private theorem in_u64 {ty : IntTy} (h : ty.signed = false) (x : JInt ty) :
    (IntTy.promote ty .u64).min ≤ x.val ∧ x.val ≤ (IntTy.promote ty .u64).max := by
  have := contains_u64 ty h; have := x.property; exact ⟨by omega, by omega⟩

private theorem promote_i64_right {u : IntTy} (h : 64 ≤ u.bits) : IntTy.promote u .i64 = u := by
  cases u <;> first | decide | exact absurd h (by decide)

private theorem bits_ge (s t : IntTy) (h : 64 ≤ t.bits) : 64 ≤ (IntTy.promote s t).bits := by
  rw [bits_promote]; omega

private theorem bits_ge' (s t : IntTy) (h : 64 ≤ s.bits) : 64 ≤ (IntTy.promote s t).bits := by
  rw [bits_promote]; omega

private theorem convert_ok (u : IntTy) (x : Int) (h : u.min ≤ x ∧ x ≤ u.max) :
    JInt.convert u x = .ok ⟨x, h⟩ := dif_pos h

private theorem promoteInts_ok {s t : IntTy} (x : JInt s) (y : JInt t)
    (hx : (IntTy.promote s t).min ≤ x.val ∧ x.val ≤ (IntTy.promote s t).max)
    (hy : (IntTy.promote s t).min ≤ y.val ∧ y.val ≤ (IntTy.promote s t).max) :
    promoteInts x y = .ok (⟨x.val, hx⟩, ⟨y.val, hy⟩) := by
  unfold promoteInts
  rw [convert_ok _ _ hx, convert_ok _ _ hy]
  rfl

private theorem addMixed_val {s t : IntTy} (a : JInt s) (b : JInt t)
    (hw : 64 ≤ (IntTy.promote s t).bits) (ha : 0 ≤ a.val) (ha' : a.val ≤ 4611686018427387905)
    (hb : 0 ≤ b.val) (hb' : b.val ≤ 4611686018427387905) (hr : a.val + b.val ≤ 4611686018427387905) :
    (addMixed a b).val = a.val + b.val := by
  simp only [addMixed, add_val', rem_val']
  rw [wrap_small hw ha ha', wrap_small hw hb hb', wrap_small hw (by omega) hr]

private theorem subMixed_val {s t : IntTy} (a : JInt s) (b : JInt t)
    (hw : 64 ≤ (IntTy.promote s t).bits) (ha : 0 ≤ a.val) (ha' : a.val ≤ 4611686018427387905)
    (hb : 0 ≤ b.val) (hb' : b.val ≤ 4611686018427387905) (hr : b.val ≤ a.val) :
    (subMixed a b).val = a.val - b.val := by
  simp only [subMixed, sub_val', rem_val']
  rw [wrap_small hw ha ha', wrap_small hw hb hb', wrap_small hw (by omega) (by omega)]

/-- The tuple index `k - j + off`: the subtraction may wrap (unsigned `j`), the sum does not. -/
private theorem addSub_val {s t u : IntTy} (a : JInt s) (b : JInt t) (c : JInt u)
    (hw : 64 ≤ (IntTy.promote s t).bits)
    (hP : IntTy.promote (IntTy.promote s t) u = IntTy.promote s t)
    (ha : 0 ≤ a.val) (ha' : a.val ≤ 4611686018427387905)
    (hb : 0 ≤ b.val) (hb' : b.val ≤ 4611686018427387905)
    (hc : 0 ≤ c.val) (hc' : c.val ≤ 4611686018427387905)
    (hr : 0 ≤ a.val - b.val + c.val) (hr' : a.val - b.val + c.val ≤ 4611686018427387905) :
    (addMixed (subMixed a b) c).val = a.val - b.val + c.val := by
  simp only [addMixed, subMixed, add_val', sub_val', rem_val']
  rw [hP, wrap_small hw ha ha', wrap_small hw hb hb', wrap_small hw hc hc', wrap_add_l, wrap_add_l,
    wrap_small hw hr hr']

private theorem remInt_ok {P : IntTy} (a b : JInt P) (hb : b.val ≠ 0) :
    JInt.remInt a b = .ok (JInt.wrap P (a.val.tmod b.val)) := by
  unfold JInt.remInt; rw [if_neg hb]

private theorem mod_value (P : IntTy) (a b q c : Int) :
    wrapInt P (a - wrapInt P (wrapInt P (wrapInt P q - wrapInt P c) * b)) =
      wrapInt P (a - (q - c) * b) := by
  rw [wrap_sub_l P q, wrap_sub_r P q c, wrap_mul_l P (q - c), wrap_sub_r P a]

/-- `mod(a, b)` of two values of the same type is the floored remainder for `b > 0`,
including the wrapping `a -% fld(a, b) *% b` at `typemin`. -/
private theorem mod_ok {P : IntTy} (a b : JInt P) (hb : 0 < b.val) :
    ∃ r, JInt.mod a b = .ok r ∧ r.val = a.val % b.val := by
  have hbmax := b.property.2
  have hamin := a.property.1
  have hamax := a.property.2
  have hm := tmin_nonpos P
  have hr0 := Int.emod_nonneg a.val (show b.val ≠ 0 by omega)
  have hr1 := Int.emod_lt_of_pos a.val hb
  have hin : P.min ≤ a.val % b.val ∧ a.val % b.val ≤ P.max := ⟨by omega, by omega⟩
  cases hs : P.signed
  · have ha : 0 ≤ a.val := by have := unsigned_min P hs; omega
    refine ⟨JInt.wrap P (a.val.tmod b.val), ?_, ?_⟩
    · unfold JInt.mod
      rw [hs, if_neg Bool.false_ne_true]
      exact remInt_ok a b (by omega)
    · show wrapInt P (a.val.tmod b.val) = _
      rw [Int.tmod_eq_emod_of_nonneg ha]
      exact wrapInt_of_inRange P _ hin
  · have hsm := signed_min P hs
    have hb1 : b.val ≠ -1 := by omega
    have hb0 : b.val ≠ 0 := by omega
    have hdiv : JInt.div a b = .ok (JInt.wrap P (a.val.tdiv b.val)) := by
      unfold JInt.div
      rw [if_neg hb0, if_neg (show ¬ (P.signed = true ∧ a.val = P.min ∧ b.val = -1) from
        fun h => hb1 h.2.2)]
    generalize hq : a.val.tdiv b.val = q at hdiv
    have hfld : JInt.fld a b = .ok (JInt.wrap P q - JInt.lit P
        (if ((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
          (JInt.wrap P q * b).val ≠ a.val then 1 else 0)) := by
      unfold JInt.fld; rw [hdiv, hs]; rfl
    have hmod : JInt.mod a b = .ok (a - (JInt.wrap P q - JInt.lit P
        (if ((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
          (JInt.wrap P q * b).val ≠ a.val then 1 else 0)) * b) := by
      unfold JInt.mod; rw [hs, if_pos rfl, if_neg hb1, hfld]; rfl
    have hqe : q = a.val / b.val + (if 0 ≤ a.val ∨ b.val ∣ a.val then 0 else 1) := by
      rw [← hq, Int.tdiv_eq_ediv, Int.sign_eq_one_of_pos hb]
    have hdef : a.val % b.val = a.val - b.val * (a.val / b.val) := Int.emod_def _ _
    generalize he : a.val / b.val = e at hqe hdef
    have hcomm : e * b.val = b.val * e := Int.mul_comm _ _
    have hprod : (JInt.wrap P q * b).val = wrapInt P (q * b.val) := by
      rw [mul_val']; exact wrap_mul_l P q b.val
    by_cases h1 : 0 ≤ a.val ∨ b.val ∣ a.val
    · rw [if_pos h1, Int.add_zero] at hqe
      have hqb : q * b.val = e * b.val := by rw [hqe]
      have hr : 0 ≤ a.val ∨ a.val % b.val = 0 := h1.imp id Int.emod_eq_zero_of_dvd
      clear h1
      have hp : (JInt.wrap P q * b).val = q * b.val := by
        rw [hprod]; exact wrapInt_of_inRange P _ ⟨by omega, by omega⟩
      have hc : ¬ (((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
          (JInt.wrap P q * b).val ≠ a.val) := by rw [hp]; omega
      rw [if_neg hc] at hmod
      refine ⟨_, hmod, ?_⟩
      show wrapInt P (a.val - wrapInt P (wrapInt P (wrapInt P q - wrapInt P 0) * b.val)) = _
      rw [mod_value, Int.sub_zero]
      have hv : a.val - q * b.val = a.val % b.val := by omega
      rw [hv]; exact wrapInt_of_inRange P _ hin
    · rw [if_neg h1] at hqe
      have hneg : a.val < 0 := by
        rcases Int.lt_or_le a.val 0 with h | h
        · exact h
        · exact absurd (Or.inl h) h1
      have hr : a.val % b.val ≠ 0 := fun h => h1 (Or.inr (Int.dvd_of_emod_eq_zero h))
      clear h1
      have hqb : q * b.val = e * b.val + b.val := by rw [hqe, Int.add_mul, Int.one_mul]
      have hp : (JInt.wrap P q * b).val = q * b.val := by
        rw [hprod]; exact wrapInt_of_inRange P _ ⟨by omega, by omega⟩
      have hc : ((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
          (JInt.wrap P q * b).val ≠ a.val := by rw [hp]; omega
      rw [if_pos hc] at hmod
      refine ⟨_, hmod, ?_⟩
      show wrapInt P (a.val - wrapInt P (wrapInt P (wrapInt P q - wrapInt P 1) * b.val)) = _
      rw [mod_value, hqe, Int.add_sub_cancel]
      have hv : a.val - e * b.val = a.val % b.val := by omega
      rw [hv]; exact wrapInt_of_inRange P _ hin

private theorem absSigned_val (y : JInt64) (hy : 0 < y.val) (hy' : y.val ≤ 4611686018427387905) :
    (JInt.rem .u64 (absSigned y)).val = y.val := by
  unfold absSigned
  rw [if_neg (by omega), rem_val']
  exact wrap_small (by decide) (by omega) hy'

private theorem remByInt_ok {s : IntTy} (x : JInt s) (y : JInt64) (hy : 0 < y.val)
    (hy' : y.val ≤ 4611686018427387905) :
    ∃ r : AnyInt, remByInt x y = .ok r ∧ r.2.val = wrapInt r.1 (x.val.tmod y.val) ∧
      64 ≤ r.1.bits ∧ (s.signed = true → r.1 = IntTy.promote s .i64) := by
  unfold remByInt
  cases hs : s.signed
  · rw [if_neg Bool.false_ne_true]
    dsimp only
    have hw : 64 ≤ (IntTy.promote s .u64).bits := bits_ge s .u64 (by decide)
    have hu := absSigned_val y hy hy'
    have hyr : (IntTy.promote s .u64).min ≤ (JInt.rem .u64 (absSigned y)).val ∧
        (JInt.rem .u64 (absSigned y)).val ≤ (IntTy.promote s .u64).max := by
      rw [hu]; exact inr hw (by omega) hy'
    rw [promoteInts_ok x _ (in_u64 hs x) hyr]
    simp only [R.bind_ok, JInt.remInt]
    rw [if_neg (show ¬ ((JInt.rem .u64 (absSigned y)).val = 0) by omega)]
    simp only [liftJ_ok', R.bind_ok]
    refine ⟨_, rfl, ?_, hw, fun h => absurd h Bool.false_ne_true⟩
    show wrapInt _ (x.val.tmod (JInt.rem .u64 (absSigned y)).val) = _
    rw [hu]
  · rw [if_pos rfl]
    have hw : 64 ≤ (IntTy.promote s .i64).bits := bits_ge s .i64 (by decide)
    have hyr := inr hw (Int.le_of_lt hy) hy'
    rw [promoteInts_ok x y (in_i64 x) hyr]
    simp only [R.bind_ok, JInt.remInt]
    rw [if_neg (show ¬ (y.val = 0) by omega)]
    simp only [liftJ_ok', R.bind_ok]
    exact ⟨_, rfl, rfl, hw, fun _ => rfl⟩

private theorem iseven_ok {ty : IntTy} (shift : JInt ty) :
    ∃ e, iseven shift = .ok e ∧ (e = true ↔ shift.val % 2 = 0) := by
  obtain ⟨r, hr, hrv, hrb, hsg⟩ := remByInt_ok shift (JInt.lit .i64 2) (by decide) (by decide)
  have h2 : (JInt.lit .i64 2).val = 2 := by decide
  rw [h2] at hrv
  refine ⟨decide (r.2.val = 0), ?_, ?_⟩
  · unfold iseven; rw [hr]; rfl
  · rw [decide_eq_true_iff, hrv]
    have ht : shift.val.tmod 2 = if 0 ≤ shift.val then shift.val % 2 else -((-shift.val) % 2) := by
      split
      · exact Int.tmod_eq_emod_of_nonneg ‹_›
      · have h := Int.neg_tmod (-shift.val) 2
        rw [Int.neg_neg] at h
        rw [h, Int.tmod_eq_emod_of_nonneg (by omega)]
    cases hs : ty.signed
    · have h0 : 0 ≤ shift.val := by
        have := shift.property.1; have := unsigned_min ty hs; omega
      rw [ht, if_pos h0, wrap_small hrb (x := shift.val % 2) (Int.emod_nonneg _ (by decide))
        (by omega)]
    · rw [hsg hs] at hrb ⊢
      have hmin := signed_wide ty hs
      have hmax := (wide hrb).2
      rw [wrapInt_of_inRange (IntTy.promote ty .i64) (shift.val.tmod 2)
        ⟨by rw [ht]; split <;> omega, by rw [ht]; split <;> omega⟩, ht]
      split <;> constructor <;> intro h <;> omega

private theorem mod1_ok {ty : IntTy} (shift : JInt ty) (y : JInt64) (hy : 0 < y.val)
    (hy' : y.val ≤ 4611686018427387905) :
    ∃ j : JInt (IntTy.promote ty .i64), mod1 shift y = .ok j ∧
      j.val = if shift.val % y.val = 0 then y.val else shift.val % y.val := by
  have hw : 64 ≤ (IntTy.promote ty .i64).bits := bits_ge ty .i64 (by decide)
  have hx := in_i64 shift
  have hyr := inr hw (Int.le_of_lt hy) hy'
  obtain ⟨m, hm, hmv⟩ := mod_ok (⟨shift.val, hx⟩ : JInt _) ⟨y.val, hyr⟩ hy
  have hmv' : m.val = shift.val % y.val := hmv
  refine ⟨if m.val = 0 then ⟨y.val, hyr⟩ else m, ?_, ?_⟩
  · unfold mod1
    rw [promoteInts_ok shift y hx hyr]
    simp only [R.bind_ok]
    rw [hm]
    rfl
  · by_cases hz : m.val = 0
    · have hz' : shift.val % y.val = 0 := by rw [← hmv']; exact hz
      rw [if_pos hz, if_pos hz']
    · have hz' : ¬ shift.val % y.val = 0 := by rw [← hmv']; exact hz
      rw [if_neg hz, if_neg hz', hmv']

private theorem modByInt_ok {ty : IntTy} (shift : JInt ty) (y : JInt64) (hy : 0 < y.val)
    (hy' : y.val ≤ 4611686018427387905) :
    ∃ s : AnyInt, modByInt shift y = .ok s ∧ s.2.val = shift.val % y.val ∧ 64 ≤ s.1.bits := by
  have hr0 := Int.emod_nonneg shift.val (show y.val ≠ 0 by omega)
  have hr1 := Int.emod_lt_of_pos shift.val hy
  unfold modByInt
  cases hs : ty.signed
  · rw [if_neg Bool.false_ne_true]
    obtain ⟨r, hr, hrv, hrb, _⟩ := remByInt_ok shift y hy hy'
    have ha : 0 ≤ shift.val := by
      have := shift.property.1; have := unsigned_min ty hs; omega
    rw [Int.tmod_eq_emod_of_nonneg ha, wrap_small hrb hr0 (by omega)] at hrv
    have hw1 : 64 ≤ r.1.toSigned.bits := by rw [bits_toSigned]; exact hrb
    have hrem : (JInt.rem r.1.toSigned r.2).val = shift.val % y.val := by
      rw [rem_val', hrv]; exact wrap_small hw1 hr0 (by omega)
    have hc : ¬ ((JInt.rem r.1.toSigned r.2).val ≠ 0 ∧ y.val < 0) := fun h => by omega
    rw [hr]
    simp only [R.bind_ok]
    refine ⟨_, rfl, ?_, bits_ge' _ _ hw1⟩
    show (addMixed (JInt.rem r.1.toSigned r.2)
      (if (JInt.rem r.1.toSigned r.2).val ≠ 0 ∧ y.val < 0 then y else JInt.lit .i64 0)).val = _
    have hl0 : (JInt.lit .i64 0).val = 0 := by decide
    rw [if_neg hc, addMixed_val _ _ (bits_ge' _ _ hw1) (by omega) (by omega) (by decide) (by decide)
      (by omega), hrem, hl0, Int.add_zero]
  · rw [if_pos rfl]
    have hw : 64 ≤ (IntTy.promote ty .i64).bits := bits_ge ty .i64 (by decide)
    have hx := in_i64 shift
    have hyr := inr hw (Int.le_of_lt hy) hy'
    obtain ⟨m, hm, hmv⟩ := mod_ok (⟨shift.val, hx⟩ : JInt _) ⟨y.val, hyr⟩ hy
    rw [promoteInts_ok shift y hx hyr]
    simp only [R.bind_ok]
    rw [hm]
    exact ⟨_, rfl, hmv, hw⟩

private theorem unitrangeLast_val {u : IntTy} (a b : JInt u) (hw : 64 ≤ u.bits) (ha : 1 ≤ a.val) :
    (unitrangeLast a b).val = if a.val ≤ b.val then b.val else a.val - 1 := by
  unfold unitrangeLast
  by_cases h : a.val ≤ b.val
  · rw [if_pos (show b.val ≥ a.val from h), if_pos h]
  · rw [if_neg (show ¬ b.val ≥ a.val from h), if_neg h, sub_val', lit_val',
      wrap_small hw (x := 1) (by decide) (by decide)]
    have := a.property.2; have := wide hw
    exact wrapInt_of_inRange u _ ⟨by omega, by omega⟩

end Arith

private theorem i64_bits : 64 ≤ IntTy.i64.bits := by decide

private theorem litI64 {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 4611686018427387905) :
    (JInt.lit .i64 x).val = x := wrap_small i64_bits h0 h1

private theorem unitRangeInt_ok {s t : IntTy} (a : JInt s) (b : JInt t) (x y z : Int)
    (hw : 64 ≤ (IntTy.promote s t).bits) (hax : a.val = x) (hby : b.val = y)
    (hx : 1 ≤ x) (hx' : x ≤ 4611686018427387905) (hy : 0 ≤ y) (hy' : y ≤ 4611686018427387905)
    (hz : z = if x ≤ y then y else x - 1) :
    unitRangeInt a b = .ok (x, z) := by
  subst hax hby
  have hxr := inr hw (by omega) hx'
  have hyr := inr hw hy hy'
  unfold unitRangeInt
  rw [promoteInts_ok a b hxr hyr]
  simp only [R.bind_ok]
  have hl := unitrangeLast_val (⟨a.val, hxr⟩ : JInt _) ⟨b.val, hyr⟩ hw hx
  have hzr : IntTy.i64.min ≤ z ∧ z ≤ IntTy.i64.max := by
    rw [hz]; exact inr i64_bits (by split <;> omega) (by split <;> omega)
  rw [hl, ← hz, convert_ok _ _ (inr i64_bits (by omega) hx'), convert_ok _ _ hzr]
  rfl

private theorem checkIndex_ok (v : List α) (i : Int) (h1 : 1 ≤ i) (h2 : i ≤ v.length) :
    checkIndex v i = .ok () := by
  unfold checkIndex; rw [if_pos ⟨h1, h2⟩]

private theorem copyto_empty (dest src : List α) (rd rs : Int × Int) (h : rd.1 > rd.2) :
    copytoCartesian dest src rd rs = .ok dest := by
  unfold copytoCartesian; rw [if_pos h]

private theorem copyto_ok (dest src : List α) (x1 x2 y1 y2 : Int) (L : Nat) (hL : 1 ≤ L)
    (hx : x2 = x1 + L - 1) (hy : y2 = y1 + L - 1)
    (hx1 : 1 ≤ x1) (hx2 : x2 ≤ dest.length) (hy1 : 1 ≤ y1) (hy2 : y2 ≤ src.length)
    (hd : dest.length < 4611686018427387904) (hs : src.length < 4611686018427387904) :
    copytoCartesian dest src (x1, x2) (y1, y2) = .ok (copyLoop src (x1 - y1) y1 L dest) := by
  have hlen : ∀ a b : Int, b = a + L - 1 → 1 ≤ a → b < 4611686018427387904 →
      rangeLength (a, b) = L := by
    intro a b h1 h2 h3
    unfold rangeLength
    rw [if_neg (show ¬ (a > b) by omega)]
    show wrapInt .i64 (b - a + 1) = _
    rw [wrap_small i64_bits (x := b - a + 1) (by omega) (by omega)]
    omega
  unfold copytoCartesian
  rw [if_neg (show ¬ (x1 > x2) by omega),
    hlen x1 x2 hx hx1 (by omega), hlen y1 y2 hy hy1 (by omega), if_neg (fun h => h rfl)]
  rw [checkIndex_ok dest x1 hx1 (by omega), R.bind_ok, checkIndex_ok dest x2 (by omega) hx2,
    R.bind_ok, checkIndex_ok src y1 hy1 (by omega), R.bind_ok,
    checkIndex_ok src y2 (by omega) hy2, R.bind_ok]
  have hdelta : (JInt.wrap .i64 (x1 - y1)).val = x1 - y1 := i64_wrap (by omega) (by omega)
  rw [hdelta, show ((L : Int)).toNat = L by omega]
  rfl

private theorem copyLoop_spec (src : List α) (δ : Int) : ∀ (k : Nat) (i : Int) (dest : List α),
    1 ≤ i → i + k ≤ src.length + 1 → 1 ≤ i + δ → i + δ + k ≤ dest.length + 1 →
    dest.length < 4611686018427387904 →
    (copyLoop src δ i k dest).length = dest.length ∧
    ∀ p : Nat, (copyLoop src δ i k dest)[p]? =
      if i + δ ≤ (p : Int) + 1 ∧ (p : Int) + 1 < i + δ + k then src[((p : Int) - δ).toNat]?
      else dest[p]? := by
  intro k
  induction k with
  | zero =>
    intro i dest _ _ _ _ _
    refine ⟨rfl, fun p => ?_⟩
    rw [if_neg (by omega)]
    rfl
  | succ k ih =>
    intro i dest h1 h2 h3 h4 h5
    have hi : (i - 1).toNat < src.length := by omega
    have hw : (JInt.wrap .i64 (i + δ)).val = i + δ := i64_wrap (by omega) (by omega)
    have hstep : copyLoop src δ i (k + 1) dest =
        copyLoop src δ (i + 1) k (dest.set (i + δ - 1).toNat src[(i - 1).toNat]) := by
      simp only [copyLoop, List.getElem?_eq_getElem hi, hw]
    obtain ⟨hl, hp⟩ := ih (i + 1) (dest.set (i + δ - 1).toNat src[(i - 1).toNat])
      (by omega) (by omega) (by omega) (by rw [List.length_set]; omega)
      (by rw [List.length_set]; omega)
    rw [hstep]
    refine ⟨by rw [hl, List.length_set], fun p => ?_⟩
    rw [hp p]
    by_cases hpe : (p : Int) + 1 = i + δ
    · have hpn : (i + δ - 1).toNat = p := by omega
      have hsrc : ((p : Int) - δ).toNat = (i - 1).toNat := by omega
      rw [if_neg (by omega), if_pos (by omega), hpn, List.getElem?_set_self (by omega), hsrc,
        List.getElem?_eq_getElem hi]
    · have hpn : (i + δ - 1).toNat ≠ p := by omega
      rw [List.getElem?_set_ne hpn]
      by_cases hc : i + δ ≤ (p : Int) + 1 ∧ (p : Int) + 1 < i + δ + ((k + 1 : Nat) : Int)
      · rw [if_pos (by omega), if_pos hc]
      · rw [if_neg (by omega), if_neg hc]

private theorem list_eq_of_get? {l₁ l₂ : List α} (h : ∀ p : Nat, l₁[p]? = l₂[p]?) : l₁ = l₂ := by
  have hlen : l₁.length = l₂.length := by
    rcases Nat.lt_trichotomy l₁.length l₂.length with hl | hl | hl
    · have := h l₁.length
      rw [List.getElem?_eq_none (Nat.le_refl _), List.getElem?_eq_getElem hl] at this
      cases this
    · exact hl
    · have := h l₂.length
      rw [List.getElem?_eq_getElem hl, List.getElem?_eq_none (Nat.le_refl _)] at this
      cases this
  apply List.ext_getElem hlen
  intro p h1 h2
  have := h p
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
  exact Option.some.inj this

private theorem rotateRight_length (t : List α) (s : Nat) (hs : s ≤ t.length) :
    (rotateRight t s).length = t.length := by
  simp only [rotateRight, List.length_append, List.length_drop, List.length_take]; omega

private theorem rotateRight_get? (t : List α) (s : Nat) (hs : s ≤ t.length) (p : Nat) :
    (rotateRight t s)[p]? =
      if p < s then t[p + (t.length - s)]? else if p < t.length then t[p - s]? else none := by
  have hlen := rotateRight_length t s hs
  have hd : (t.drop (t.length - s)).length = s := by rw [List.length_drop]; omega
  by_cases hp : p < t.length
  · rw [List.getElem?_eq_getElem (show p < (rotateRight t s).length by omega)]
    by_cases h1 : p < s
    · rw [if_pos h1, List.getElem?_eq_getElem (show p + (t.length - s) < t.length by omega)]
      simp only [rotateRight]
      rw [List.getElem_append_left (by omega), List.getElem_drop]
      have e : t.length - s + p = p + (t.length - s) := by omega
      simp only [e]
    · rw [if_neg h1, if_pos hp, List.getElem?_eq_getElem (show p - s < t.length by omega)]
      simp only [rotateRight]
      rw [List.getElem_append_right (by omega), List.getElem_take]
      simp only [hd]
  · rw [List.getElem?_eq_none (by omega), if_neg (by omega), if_neg hp]

private theorem elem_close (T L : List α) (k idx : Nat) (hidx : idx < T.length)
    (hk : k < L.length) (h : L[k]? = T[idx]?) : getfield T ((idx : Int) + 1) = .ok L[k] := by
  rw [getfield_ok T idx hidx]
  rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hidx] at h
  rw [Option.some.inj h]

private theorem getindex_int (t : List α) {u : IntTy} (i : JInt u) (h0 : 0 ≤ i.val)
    (h1 : i.val ≤ 4611686018427387905) : getindex t (.int u i) = getfield t i.val := by
  simp only [getindex]
  split
  · rfl
  · rw [convert_ok _ _ (inr i64_bits h0 h1)]
    rfl

/-- Element `k` of the `ntuple` in the long-tuple method. -/
private theorem tuple_elem (T : List α) {ty : IntTy} (j : JInt (IntTy.promote ty .i64)) (s0 : Int)
    (lenJ : JInt64) (hlen' : lenJ.val = T.length)
    (k : Nat) (ht' : T.length < 4611686018427387904) (hs0 : 0 ≤ s0) (hs1 : s0 < T.length)
    (hjv : j.val = if s0 = 0 then (T.length : Int) else s0)
    (hk : k < (rotateRight T s0.toNat).length) :
    getindex T (.int _ (addMixed (subMixed (JInt.lit .i64 ((k : Int) + 1)) j)
      (if (JInt.lit .i64 ((k : Int) + 1)).val > j.val then JInt.lit .i64 0 else lenJ))) =
      .ok (rotateRight T s0.toNat)[k] := by
  have hsN : s0.toNat ≤ T.length := by omega
  have hkn : k < T.length := by rw [rotateRight_length T _ hsN] at hk; exact hk
  have hget := rotateRight_get? T s0.toNat hsN k
  -- Opaque names for the `Int` literals, so that `omega` never unfolds `wrapInt`.
  generalize hKI : JInt.lit .i64 ((k : Int) + 1) = kI
  generalize hZ : JInt.lit .i64 0 = z0
  have hk1 : kI.val = (k : Int) + 1 := by rw [← hKI]; exact litI64 (by omega) (by omega)
  have h0 : z0.val = 0 := by rw [← hZ]; decide
  clear hKI hZ
  have hw : 64 ≤ (IntTy.promote .i64 (IntTy.promote ty .i64)).bits :=
    bits_ge' _ _ i64_bits
  have hP : IntTy.promote (IntTy.promote .i64 (IntTy.promote ty .i64)) .i64 =
      IntTy.promote .i64 (IntTy.promote ty .i64) := promote_i64_right hw
  have hjr : 1 ≤ j.val ∧ j.val ≤ (T.length : Int) := by rw [hjv]; split <;> omega
  by_cases hc : (k : Int) + 1 > j.val
  · rw [if_pos (by rw [hk1]; exact hc)]
    have hv := addSub_val kI j z0 hw hP
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hnz : s0 ≠ 0 := by intro h; rw [h, if_pos rfl] at hjv; omega
    rw [if_neg hnz] at hjv
    rw [getindex_int T _ (by rw [hv]; omega) (by rw [hv]; omega), hv, hk1, h0,
      show (k : Int) + 1 - j.val + 0 = ((k - s0.toNat : Nat) : Int) + 1 by omega]
    refine elem_close T _ k (k - s0.toNat) (by omega) hk ?_
    rw [hget, if_neg (by omega), if_pos hkn]
  · rw [if_neg (by rw [hk1]; exact hc)]
    have hv := addSub_val kI j lenJ hw hP
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [getindex_int T _ (by rw [hv]; omega) (by rw [hv]; omega), hv, hk1, hlen']
    by_cases hz : s0 = 0
    · rw [if_pos hz] at hjv
      rw [show (k : Int) + 1 - j.val + T.length = ((k : Nat) : Int) + 1 by omega]
      refine elem_close T _ k k hkn hk ?_
      rw [hget, if_neg (by omega), if_pos hkn, show k - s0.toNat = k by omega]
    · rw [if_neg hz] at hjv
      rw [show (k : Int) + 1 - j.val + T.length =
        ((k + (T.length - s0.toNat) : Nat) : Int) + 1 by omega]
      refine elem_close T _ k (k + (T.length - s0.toNat)) (by omega) hk ?_
      rw [hget, if_pos (by omega)]

private theorem tuple_map (T : List α) {ty : IntTy} (j : JInt (IntTy.promote ty .i64)) (s0 : Int)
    (lenJ : JInt64) (hlen' : lenJ.val = T.length)
    (ht' : T.length < 4611686018427387904) (hs0 : 0 ≤ s0) (hs1 : s0 < T.length)
    (hjv : j.val = if s0 = 0 then (T.length : Int) else s0) :
    ((List.range T.length).mapM fun (k : Nat) =>
        getindex T (.int _ (addMixed (subMixed (JInt.lit .i64 ((k : Int) + 1)) j)
          (if (JInt.lit .i64 ((k : Int) + 1)).val > j.val then JInt.lit .i64 0 else lenJ)))) =
      .ok (rotateRight T s0.toNat) :=
  mapM_range_ok _ _ _ (rotateRight_length T s0.toNat (by omega))
    (fun k hk => tuple_elem T j s0 lenJ hlen' k ht' hs0 hs1 hjv hk)

private theorem circshiftTuple_body (T : List α) (ty : IntTy) (shift : JInt ty)
    (hT3 : 3 ≤ T.length) (ht' : T.length < 4611686018427387904) :
    (do
      let j ← mod1 shift (JInt.lit .i64 (T.length : Int))
      (List.range (JInt.lit .i64 (T.length : Int)).val.toNat).mapM fun (k : Nat) =>
        getindex T (.int _ (addMixed (subMixed (JInt.lit .i64 ((k : Int) + 1)) j)
          (if (JInt.lit .i64 ((k : Int) + 1)).val > j.val then JInt.lit .i64 0
            else JInt.lit .i64 (T.length : Int))))) =
      (.ok (rotateRight T (shift.val % T.length).toNat) : R (List α)) := by
  generalize hX : JInt.lit .i64 (T.length : Int) = lenJ
  have hlen : lenJ.val = T.length := by rw [← hX]; exact litI64 (by omega) (by omega)
  clear hX
  obtain ⟨j, hj, hjv⟩ := mod1_ok shift lenJ (by omega) (by omega)
  rw [hlen] at hjv
  have hs0 := Int.emod_nonneg shift.val (show (T.length : Int) ≠ 0 by omega)
  have hs1 := Int.emod_lt_of_pos shift.val (show (0 : Int) < T.length by omega)
  generalize hS : shift.val % (T.length : Int) = s0 at hjv hs0 hs1 ⊢
  rw [hj, R.bind_ok, hlen, show ((T.length : Int)).toNat = T.length by omega]
  exact tuple_map T j s0 lenJ hlen ht' hs0 hs1 hjv

private theorem circshiftTuple_long (a b c : α) (rest : List α) (ty : IntTy) (shift : JInt ty)
    (ht' : (a :: b :: c :: rest).length < 4611686018427387904) :
    circshiftTuple (a :: b :: c :: rest) ty shift =
      .ok (rotateRight (a :: b :: c :: rest) (shift.val % (a :: b :: c :: rest).length).toNat) :=
  circshiftTuple_body (a :: b :: c :: rest) ty shift (by simp) ht'

private theorem circshiftTuple_two (a b : α) (ty : IntTy) (shift : JInt ty) :
    circshiftTuple [a, b] ty shift = .ok (rotateRight [a, b] (shift.val % [a, b].length).toNat) := by
  obtain ⟨e, he, hiff⟩ := iseven_ok shift
  have h2 : (([a, b] : List α).length : Int) = 2 := rfl
  simp only [circshiftTuple, he, R.bind_ok, R.pure_eq]
  rw [h2]
  cases e
  · have hz : shift.val % 2 = 1 := by
      have := Int.emod_nonneg shift.val (show (2 : Int) ≠ 0 by decide)
      have := Int.emod_lt_of_pos shift.val (show (0 : Int) < 2 by decide)
      have : ¬ shift.val % 2 = 0 := fun h => absurd (hiff.mpr h) (by decide)
      omega
    rw [hz]
    rfl
  · rw [hiff.mp rfl]
    rfl

private theorem circshiftTuple_one (a : α) (ty : IntTy) (shift : JInt ty) :
    circshiftTuple [a] ty shift = .ok (rotateRight [a] (shift.val % [a].length).toNat) := by
  have h1 : (([a] : List α).length : Int) = 1 := rfl
  rw [h1, Int.emod_one]
  rfl

/-- The tuple method rotates right by `mod(shift, length(t))`. -/
theorem circshiftTuple_spec (t : List α) (ty : IntTy) (shift : JInt ty) (ht : t.length < 2 ^ 62) :
    circshiftTuple t ty shift = .ok (rotateRight t (shift.val % t.length).toNat) := by
  have ht' : t.length < 4611686018427387904 := ht
  rcases t with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [circshiftTuple, rotateRight]
  · exact circshiftTuple_one a ty shift
  · exact circshiftTuple_two a b ty shift
  · exact circshiftTuple_long a b c rest ty shift ht'

/-- The vector method rotates right by `mod(shift, length(v))`, whatever the initial
contents of the destination. -/
theorem circshiftVectorInto_spec (junk t : List α) (ty : IntTy) (shift : JInt ty)
    (hj : junk.length = t.length) (ht : t.length < 2 ^ 62) :
    circshiftVectorInto junk t ty shift = .ok (rotateRight t (shift.val % t.length).toNat) := by
  have ht' : t.length < 4611686018427387904 := ht
  by_cases hne : t = []
  · subst hne
    cases junk with
    | nil => simp [circshiftVectorInto, rotateRight]
    | cons _ _ => simp at hj
  have hpos : 0 < t.length := by
    cases t with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hemp : ¬ (t.isEmpty = true) := by
    cases t with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  unfold circshiftVectorInto
  rw [if_neg hemp]
  have hlen : (JInt.lit .i64 (t.length : Int)).val = t.length := litI64 (by omega) (by omega)
  obtain ⟨s, hs, hsv, hsb⟩ := modByInt_ok shift (JInt.lit .i64 t.length) (by rw [hlen]; omega)
    (by rw [hlen]; omega)
  rw [hlen] at hsv
  have hs0 := Int.emod_nonneg shift.val (show (t.length : Int) ≠ 0 by omega)
  have hs1 := Int.emod_lt_of_pos shift.val (show (0 : Int) < t.length by omega)
  generalize hS : shift.val % (t.length : Int) = s0 at hsv hs0 hs1 ⊢
  have h1 : (JInt.lit .i64 1).val = 1 := by decide
  have hw1 : 64 ≤ (IntTy.promote .i64 s.1).bits := bits_ge' _ _ i64_bits
  have hw2 : 64 ≤ (IntTy.promote (IntTy.promote .i64 s.1) .i64).bits := bits_ge' _ _ hw1
  have hsf : (addMixed (JInt.lit .i64 1) s.2).val = 1 + s0 := by
    rw [addMixed_val _ _ hw1 (by rw [h1]; decide) (by rw [h1]; decide) (by omega) (by omega)
      (by rw [h1]; omega), h1, hsv]
  have hsl : (subMixed (JInt.lit .i64 t.length) s.2).val = t.length - s0 := by
    rw [subMixed_val _ _ hw1 (by omega) (by omega) (by omega) (by omega) (by omega), hlen, hsv]
  have hsf1 : (subMixed (addMixed (JInt.lit .i64 1) s.2) (JInt.lit .i64 1)).val = s0 := by
    rw [subMixed_val _ _ hw2 (by omega) (by omega) (by rw [h1]; decide) (by rw [h1]; decide)
      (by omega), hsf, h1]
    omega
  have hsl1 : (addMixed (subMixed (JInt.lit .i64 t.length) s.2) (JInt.lit .i64 1)).val =
      t.length - s0 + 1 := by
    rw [addMixed_val _ _ hw2 (by omega) (by omega) (by rw [h1]; decide) (by rw [h1]; decide)
      (by omega), hsl, h1]
  have hr1 : unitRangeInt (JInt.lit .i64 1) (subMixed (addMixed (JInt.lit .i64 1) s.2)
      (JInt.lit .i64 1)) = .ok (1, s0) :=
    unitRangeInt_ok _ _ 1 s0 s0 (bits_ge _ _ hw2) h1 hsf1 (by decide) (by decide) hs0 (by omega)
      (by split <;> omega)
  have hr2 : unitRangeInt (addMixed (JInt.lit .i64 1) s.2) (JInt.lit .i64 t.length) =
      .ok (1 + s0, t.length) :=
    unitRangeInt_ok _ _ (1 + s0) t.length t.length (bits_ge' _ _ hw1) hsf hlen (by omega)
      (by omega) (by omega) (by omega) (by split <;> omega)
  have hr3 : unitRangeInt (JInt.lit .i64 1) (subMixed (JInt.lit .i64 t.length) s.2) =
      .ok (1, t.length - s0) :=
    unitRangeInt_ok _ _ 1 (t.length - s0) (t.length - s0) (bits_ge _ _ hw1) h1 hsl (by decide)
      (by decide) (by omega) (by omega) (by split <;> omega)
  have hr4 : unitRangeInt (addMixed (subMixed (JInt.lit .i64 t.length) s.2) (JInt.lit .i64 1))
      (JInt.lit .i64 t.length) = .ok (t.length - s0 + 1, t.length) :=
    unitRangeInt_ok _ _ (t.length - s0 + 1) t.length t.length (bits_ge' _ _ hw2) hsl1 hlen
      (by omega) (by omega) (by omega) (by omega) (by split <;> omega)
  simp only [hs, R.bind_ok, hr1, hr2, hr3, hr4]
  have hsN : s0.toNat ≤ t.length := by omega
  obtain ⟨d1, hd1, hd1l, hd1g⟩ : ∃ d1, copytoCartesian junk t (1, s0) (t.length - s0 + 1, t.length) =
      .ok d1 ∧ d1.length = t.length ∧
      ∀ p : Nat, d1[p]? = if p < s0.toNat then t[p + (t.length - s0.toNat)]? else junk[p]? := by
    by_cases hz : s0 = 0
    · refine ⟨junk, copyto_empty _ _ _ _ (show (1 : Int) > s0 by omega), hj, fun p => ?_⟩
      rw [if_neg (by omega)]
    · refine ⟨_, copyto_ok junk t 1 s0 (t.length - s0 + 1) t.length s0.toNat (by omega)
        (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) ht', ?_⟩
      obtain ⟨hl, hg⟩ := copyLoop_spec t (1 - (t.length - s0 + 1)) s0.toNat (t.length - s0 + 1)
        junk (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨by rw [hl, hj], fun p => ?_⟩
      rw [hg p]
      by_cases hp : p < s0.toNat
      · rw [if_pos (by omega), if_pos hp,
          show ((p : Int) - (1 - (t.length - s0 + 1))).toNat = p + (t.length - s0.toNat) by omega]
      · rw [if_neg (by omega), if_neg hp]
  rw [hd1, R.bind_ok,
    copyto_ok d1 t (1 + s0) t.length 1 (t.length - s0) (t.length - s0.toNat) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by decide) (by omega) (by omega) ht']
  obtain ⟨_, hg⟩ := copyLoop_spec t (1 + s0 - 1) (t.length - s0.toNat) 1 d1
    (by decide) (by omega) (by omega) (by omega) (by omega)
  refine congrArg Except.ok ?_
  apply list_eq_of_get?
  intro p
  rw [hg p, hd1g p, rotateRight_get? t s0.toNat hsN p]
  by_cases hp1 : p < s0.toNat
  · rw [if_neg (by omega)]
    simp only [if_pos hp1]
  · by_cases hp2 : p < t.length
    · rw [if_pos (by omega)]
      simp only [if_neg hp1, if_pos hp2]
      rw [show ((p : Int) - (1 + s0 - 1)).toNat = p - s0.toNat by omega]
    · rw [if_neg (by omega)]
      simp only [if_neg hp1, if_neg hp2]
      exact List.getElem?_eq_none (by omega)

theorem circshiftAgrees : CircshiftAgrees := by
  intro α _ t ty shift ht
  rw [circshiftTuple_spec t ty shift ht, circshiftVector, circshiftVectorInto_spec t t ty shift rfl ht]
  exact sameOutcome_refl _

end JuliaLean.Tuples
