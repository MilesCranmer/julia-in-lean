import JuliaLean.RangesCov.Convert

/-!
Linear operations, sorting and modular arithmetic on ranges, `base/range.jl`
(master `bbfa0ce4150`, lines 1312-1318, 1435-1456, 1490-1549).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

set_option linter.unusedSimpArgs false

namespace Ops

/-! ### Negation -/

/-- `-(r::StepRangeLen{T,R,S,L}) = StepRangeLen{T,R,S,L}(-r.ref, -r.step, r.len, r.offset)`,
base/range.jl:1313-1314, for integer `StepRangeLen` (the inner checks pass unchanged). -/
def negCounted (r : Ranges.RngLen) : Ranges.RngLen :=
  ⟨Ranges.Num.neg r.ref, Ranges.Num.neg r.stride, r.len, r.offset, r.elementTy⟩

/-! ### `+` and `-` between ranges, base/range.jl:1490-1524 -/

/-- The two operators that `_define_range_op` defines methods for, base/range.jl:1514-1515. -/
inductive RangeOp where
  | add | sub
  deriving DecidableEq, Repr

/-- The scalar operation of a `RangeOp` on integers. -/
def RangeOp.num : RangeOp → Num → Num → Num
  | .add => Ranges.Num.add
  | .sub => Ranges.Num.sub

/-- The scalar operation of a `RangeOp` on Float64. -/
def RangeOp.flt : RangeOp → F64 → F64 → F64
  | .add => Float.F64.add
  | .sub => Float.F64.sub

/-- `$f(r1::OrdinalRange, r2::OrdinalRange)`, base/range.jl:1494-1499:
`StepRangeLen($f(first(r1), first(r2)), $f(step(r1), step(r2)), r1l)`. -/
def ordinalOp (f : RangeOp) (r1 r2 : Rng) : JlX Ranges.ResultRng := do
  let r1l ← lift (Ranges.length r1)
  let r2l ← lift (Ranges.length r2)
  if r1l.val ≠ r2l.val then throw (.dimensionMismatch "argument dimensions must match")
  let ref := f.num (Ranges.first r1) (Ranges.first r2)
  let st := f.num (Ranges.step r1) (Ranges.step r2)
  lift (Ranges.countedRange (Ranges.Num.add ref (Ranges.Num.zero st.ty)).ty ref st r1l)

/-- `$f(r1::LinRange{T}, r2::LinRange{T})`, base/range.jl:1501-1507, for Float64. -/
def linOp (f : RangeOp) (r1 r2 : FloatRanges.Lin) : JlX FloatRanges.Lin :=
  if r1.len ≠ r2.len then .error (.dimensionMismatch "argument dimensions must match")
  else lift (FloatRanges.Lin.mk' (f.flt r1.first r2.first) (f.flt r1.last r2.last) r1.len)

/-- `$f(r1::Union{StepRangeLen, OrdinalRange, LinRange}, r2::...) = $f(promote(r1, r2)...)`,
base/range.jl:1509-1511. -/
def promotedOp {α β γ : Type} (promote : α → β → JlX (γ × γ)) (op : γ → γ → JlX γ) (r1 : α) (r2 : β) :
    JlX γ := do
  let (a, b) ← promote r1 r2
  op a b

/-- `_define_range_op(@nospecialize f)`, base/range.jl:1492-1513: the ordinal and LinRange
methods it evaluates for `f`. -/
def defineRangeOp (f : RangeOp) :
    (Rng → Rng → JlX Ranges.ResultRng) × (FloatRanges.Lin → FloatRanges.Lin → JlX FloatRanges.Lin) :=
  (ordinalOp f, linOp f)

/-- `+(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S})`, base/range.jl:1517-1522, for integer
`StepRangeLen`: `StepRangeLen(first(r1)+first(r2), step(r1)+step(r2), len)`. -/
def addCounted (r1 r2 : Ranges.RngLen) : JlX Ranges.ResultRng := do
  if r1.len.val ≠ r2.len.val then throw (.dimensionMismatch "argument dimensions must match")
  let f1 ← lift (Ranges.countedFirst r1)
  let f2 ← lift (Ranges.countedFirst r2)
  let ref := Ranges.Num.add f1 f2
  let st := Ranges.Num.add r1.stride r2.stride
  lift (Ranges.countedRange (Ranges.Num.add ref (Ranges.Num.zero st.ty)).ty ref st r1.len)

/-- `-(r1::StepRangeLen, r2::StepRangeLen) = +(r1, -r2)`, base/range.jl:1524. -/
def subCounted (r1 r2 : Ranges.RngLen) : JlX Ranges.ResultRng := addCounted r1 (negCounted r2)

/-! ### Sorting, base/range.jl:1447-1456 -/

/-- `issorted(r::AbstractUnitRange) = true`, base/range.jl:1447. -/
def issortedUnit (_ : Rng) : Bool := true

/-- `issorted(r::AbstractRange) = length(r) <= 1 || step(r) >= zero(step(r))`, base/range.jl:1448. -/
def issortedRange (r : Rng) : Jl Bool := do
  let n ← Ranges.length r
  pure (decide (n.val ≤ 1) || decide ((Ranges.step r).val ≥ 0))

/-- `sort(r::AbstractUnitRange) = r`, base/range.jl:1450. -/
def sortUnit (r : Rng) : Rng := r

/-- `sort!(r::AbstractUnitRange) = r`, base/range.jl:1451. -/
def sortBangUnit (r : Rng) : Rng := r

/-- `sortperm(r::AbstractUnitRange) = eachindex(r)`, base/range.jl:1455: `OneTo(length(r))`. -/
def sortpermUnit (r : Rng) : Jl Rng := do
  let n ← Ranges.length r
  Colon.oneTo n

/-- `sortperm(r::AbstractRange)`, base/range.jl:1456:
`issorted(r) ? (firstindex(r):1:lastindex(r)) : (lastindex(r):-1:firstindex(r))`. -/
def sortpermRange (r : Rng) : Jl Rng := do
  let s ← issortedRange r
  let n ← Ranges.length r
  let one := Ranges.Num.lit (.bit .i64) 1
  if s then Colon.colonPromote3 one one n else Colon.colonPromote3 n (Ranges.Num.lit (.bit .i64) (-1)) one

/-! ### Modular arithmetic, base/range.jl:1526-1549 -/

/-- `mod1(x, y)`, base/operators.jl: `m = mod(x, y); m == 0 ? y : m` on promoted integers. -/
def mod1 (i n : Num) : Jl Num := do
  let ty := Ranges.Num.promote i.ty n.ty
  let i ← Ranges.Num.cast ty i
  let n ← Ranges.Num.cast ty n
  let m ← Ranges.Num.mod i n
  pure (if m.val = 0 then n else m)

/-- `mod(i::Integer, r::OneTo) = mod1(i, last(r))`, base/range.jl:1548. -/
def modOneTo (i : Num) (r : Rng) : Jl Num := mod1 i (Ranges.last r)

/-- `mod(i::Integer, r::AbstractUnitRange{<:Integer}) = mod(i-first(r), length(r)) + first(r)`,
base/range.jl:1549. -/
def modUnit (i : Num) (r : Rng) : Jl Num := do
  let n ← Ranges.length r
  let m ← Ranges.Num.mod (Ranges.Num.sub i (Ranges.first r)) n
  pure (Ranges.Num.add m (Ranges.first r))

/-! ### Properties -/

/-- Negation of ranges: negating an integer `StepRangeLen` keeps its length, offset and
element type and negates `ref` and `step`; negating a Float64 `StepRangeLen` twice gives
back its fields (base/range.jl:1313-1314). -/
def NegationMethods : Prop :=
  (∀ r : Ranges.RngLen, (negCounted r).len = r.len ∧ (negCounted r).offset = r.offset ∧
    (negCounted r).elementTy = r.elementTy ∧ (negCounted r).ref = Ranges.Num.neg r.ref) ∧
  (∀ r : FloatRanges.SRL, 0 ≤ r.len.val → 1 ≤ r.offset.val → r.offset.val ≤ max 1 r.len.val →
    ((r.neg).bind FloatRanges.SRL.neg) = .ok r)

theorem srl_neg_neg (r : FloatRanges.SRL) (h0 : 0 ≤ r.len.val) (h1 : 1 ≤ r.offset.val)
    (h2 : r.offset.val ≤ max 1 r.len.val) : ((r.neg).bind FloatRanges.SRL.neg) = .ok r := by
  have hmk : ∀ a b, FloatRanges.SRL.mk' a b r.len r.offset = .ok ⟨a, b, r.len, r.offset⟩ := by
    intro a b
    simp [FloatRanges.SRL.mk', show ¬ r.len.val < 0 by omega, h1, h2]
  simp only [FloatRanges.SRL.neg, hmk, Except.bind]
  rcases r with ⟨⟨a, b⟩, ⟨c, d⟩, len, off⟩
  simp [FloatRanges.TP.neg, FloatRanges.F64.neg_neg]

theorem negationMethods_proven : NegationMethods :=
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, srl_neg_neg⟩

/-- Range `+`/`-` (base/range.jl:1490-1524): operands of different lengths throw
`DimensionMismatch`; `_define_range_op` defines the ordinal and LinRange methods; the
promoting method applies the operator to the promoted operands; LinRange sums add the
endpoints; integer `StepRangeLen` subtraction is addition of the negation. -/
def RangeArithmetic : Prop :=
  (∀ f r1 r2 n1 n2, Ranges.length r1 = .ok n1 → Ranges.length r2 = .ok n2 → n1.val ≠ n2.val →
    ordinalOp f r1 r2 = .error (.dimensionMismatch "argument dimensions must match")) ∧
  (∀ f (r1 r2 : FloatRanges.Lin), r1.len ≠ r2.len →
    linOp f r1 r2 = .error (.dimensionMismatch "argument dimensions must match")) ∧
  (∀ f, defineRangeOp f = (ordinalOp f, linOp f)) ∧
  (∀ (α β γ : Type) (p : α → β → JlX (γ × γ)) (op : γ → γ → JlX γ) r1 r2 a b,
    p r1 r2 = .ok (a, b) → promotedOp p op r1 r2 = op a b) ∧
  (∀ f (r1 r2 : FloatRanges.Lin) out, linOp f r1 r2 = .ok out →
    out.start = f.flt r1.start r2.start ∧ out.stop = f.flt r1.stop r2.stop ∧ out.len = r1.len) ∧
  (∀ r1 r2 : Ranges.RngLen, r1.len.val ≠ r2.len.val →
    addCounted r1 r2 = .error (.dimensionMismatch "argument dimensions must match")) ∧
  (∀ r1 r2, subCounted r1 r2 = addCounted r1 (negCounted r2))

theorem lift_ok {α : Type} {x : Jl α} {a : α} (h : lift x = .ok a) : x = .ok a := by
  cases x with
  | error e => simp [lift] at h
  | ok v => simp [lift] at h; simp [h]

theorem linMk_fields {a b : F64} {n : I64} {out : FloatRanges.Lin}
    (h : FloatRanges.Lin.mk' a b n = .ok out) : out.start = a ∧ out.stop = b ∧ out.len = n := by
  unfold FloatRanges.Lin.mk' at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; exact ⟨rfl, rfl, rfl⟩
      · cases h
    · cases h; exact ⟨rfl, rfl, rfl⟩

theorem rangeArithmetic_proven : RangeArithmetic := by
  refine ⟨?_, ?_, fun _ => rfl, ?_, ?_, ?_, fun _ _ => rfl⟩
  · intro f r1 r2 n1 n2 h1 h2 hn
    simp [ordinalOp, lift, h1, h2, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · intro f r1 r2 h
    simp [linOp, h]
  · intro α β γ p op r1 r2 a b h
    simp [promotedOp, h, bind, Except.bind]
  · intro f r1 r2 out h
    unfold linOp at h
    split at h
    · cases h
    · exact linMk_fields (lift_ok h)
  · intro r1 r2 h
    simp [addCounted, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- `(r1 + r2)[i] == r1[i] + r2[i]` for integer unit ranges of equal length (`+` on arrays
is elementwise). -/
def OrdinalAddElementwise : Prop :=
  ∀ (a b c d : Num) (r s : Rng) (out : Ranges.ResultRng) (i x y : Num),
    Ranges.unit a b = .ok r → Ranges.unit c d = .ok s → ordinalOp .add r s = .ok out →
    Ranges.getindex r i = .ok x → Ranges.getindex s i = .ok y →
    Ranges.resultGetindex out i = .ok (Ranges.Num.add x y)

theorem ordinalAddElementwise_refuted : ¬ OrdinalAddElementwise := by
  intro h
  let i8 := fun v : Int => Ranges.Num.lit (.bit .i8) v
  let i64 := fun v : Int => Ranges.Num.lit (.bit .i64) v
  let r : Rng := ⟨.unit, i8 126, Ranges.Num.one (.bit .i8), i8 127⟩
  let s : Rng := ⟨.unit, i8 1, Ranges.Num.one (.bit .i8), i8 2⟩
  let out : Ranges.ResultRng := .counted ⟨i8 127, i8 2, i64 2, i64 1, .bit .i8⟩
  have hr : Ranges.unit (i8 126) (i8 127) = .ok r := by decide
  have hs : Ranges.unit (i8 1) (i8 2) = .ok s := by decide
  have ho : ordinalOp .add r s = .ok out := by decide
  have hx : Ranges.getindex r (i64 2) = .ok (i8 127) := by decide
  have hy : Ranges.getindex s (i64 2) = .ok (i8 2) := by decide
  have bad := h _ _ _ _ r s out _ _ _ hr hs ho hx hy
  exact absurd bad (by decide)

/-- Sorting unit ranges: `issorted` is true, `sort`/`sort!` return the range, and
`sortperm(r)` of a nonempty unit range with a nonnegative length is `OneTo(length(r))`,
the identity permutation; for any range, `sortperm` agrees with `issorted`. -/
def SortingMethods : Prop :=
  (∀ r, issortedUnit r = true ∧ sortUnit r = r ∧ sortBangUnit r = r) ∧
  (∀ r n, Ranges.length r = .ok n → sortpermUnit r = Colon.oneTo n) ∧
  (∀ r n, Ranges.length r = .ok n → issortedRange r = .ok true →
    sortpermRange r = Colon.colonPromote3 (Ranges.Num.lit (.bit .i64) 1) (Ranges.Num.lit (.bit .i64) 1) n) ∧
  (∀ r n, Ranges.length r = .ok n → issortedRange r = .ok false →
    sortpermRange r = Colon.colonPromote3 n (Ranges.Num.lit (.bit .i64) (-1)) (Ranges.Num.lit (.bit .i64) 1))

theorem sortingMethods_proven : SortingMethods := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro r n h; simp [sortpermUnit, h, bind, Except.bind]
  · intro r n h hs; simp [sortpermRange, h, hs, bind, Except.bind]
  · intro r n h hs; simp [sortpermRange, h, hs, bind, Except.bind]

/-- `issorted(r)` for a constructed integer `StepRange` implies its elements do not
decrease: the step is nonnegative or there is at most one element. -/
def IssortedSound : Prop :=
  ∀ (a s b : Num) (r : Rng), Ranges.stepRange a s b = .ok r → issortedRange r = .ok true →
    (Ranges.step r).val ≥ 0 ∨ Ranges.trueCount r ≤ 1

theorem issortedSound_refuted : ¬ IssortedSound := by
  intro h
  let i64 := fun v : Int => Ranges.Num.lit (.bit .i64) v
  let r : Rng := ⟨.step, i64 IntTy.i64.max, i64 (-1), i64 IntTy.i64.min⟩
  have hr : Ranges.stepRange (i64 IntTy.i64.max) (i64 (-1)) (i64 IntTy.i64.min) = .ok r := by decide
  have hs : issortedRange r = .ok true := by decide
  have bad := h _ _ _ r hr hs
  have hst : (Ranges.step r).val = -1 := by decide
  have hc : Ranges.trueCount r = 2 ^ 64 := by decide
  rw [hst, hc] at bad
  omega

/-- `mod(i, OneTo(n))` is `mod1(i, n)` and `mod(i, r)` on unit ranges is
`mod(i - first(r), length(r)) + first(r)`; the docstring examples of
`mod(x::Integer, r::AbstractUnitRange)` (base/range.jl:1528-1543) hold:
`mod(0, Base.OneTo(3)) == 3` and `mod(3, 0:2) == 0`. -/
def ModMethods : Prop :=
  (∀ i r, modOneTo i r = mod1 i (Ranges.last r)) ∧
  (∀ (r : Rng), Ranges.oneTo (Ranges.Num.lit (.bit .i64) 3) = .ok r →
    modOneTo (Ranges.Num.lit (.bit .i64) 0) r = .ok (Ranges.Num.lit (.bit .i64) 3)) ∧
  (∀ (r : Rng), Ranges.unit (Ranges.Num.lit (.bit .i64) 0) (Ranges.Num.lit (.bit .i64) 2) = .ok r →
    modUnit (Ranges.Num.lit (.bit .i64) 3) r = .ok (Ranges.Num.lit (.bit .i64) 0)) ∧
  (∀ i r n, Ranges.length r = .ok n →
    modUnit i r = (Ranges.Num.mod (Ranges.Num.sub i (Ranges.first r)) n).map
      (fun m => Ranges.Num.add m (Ranges.first r)))

theorem modMethods_proven : ModMethods := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro r h
    have : r = ⟨.oneTo, Ranges.Num.lit (.bit .i64) 1, Ranges.Num.lit (.bit .i64) 1,
        Ranges.Num.lit (.bit .i64) 3⟩ := by
      have h' : Ranges.oneTo (Ranges.Num.lit (.bit .i64) 3) = .ok ⟨.oneTo, Ranges.Num.lit (.bit .i64) 1,
          Ranges.Num.lit (.bit .i64) 1, Ranges.Num.lit (.bit .i64) 3⟩ := by decide
      rw [h'] at h; cases h; rfl
    subst this; decide
  · intro r h
    have : r = ⟨.unit, Ranges.Num.lit (.bit .i64) 0, Ranges.Num.lit (.bit .i64) 1,
        Ranges.Num.lit (.bit .i64) 2⟩ := by
      have h' : Ranges.unit (Ranges.Num.lit (.bit .i64) 0) (Ranges.Num.lit (.bit .i64) 2) =
          .ok ⟨.unit, Ranges.Num.lit (.bit .i64) 0, Ranges.Num.lit (.bit .i64) 1,
            Ranges.Num.lit (.bit .i64) 2⟩ := by decide
      rw [h'] at h; cases h; rfl
    subst this; decide
  · intro i r n h
    cases h2 : Ranges.Num.mod (Ranges.Num.sub i (Ranges.first r)) n <;>
      simp [modUnit, h, h2, bind, Except.bind, pure, Except.pure, Except.map]

def entries : List Entry := [
  { id := "rangescov-negation-methods", juliaFile := "base/range.jl"
    juliaFns := ["-(::StepRangeLen{T,R,S,L})"]
    statement := "Negating an integer StepRangeLen negates ref and step and keeps len, offset and element type; negating a valid Float64 StepRangeLen twice gives back its fields."
    source := "base/range.jl:1313-1314; linear range-operation invariant"
    status := .proven, prop := ``NegationMethods, thm := some ``negationMethods_proven },
  { id := "rangescov-range-arithmetic", juliaFile := "base/range.jl"
    juliaFns := ["_define_range_op", "+(::OrdinalRange, ::OrdinalRange)", "-(::OrdinalRange, ::OrdinalRange)",
      "+(::LinRange{T}, ::LinRange{T})", "-(::LinRange{T}, ::LinRange{T})",
      "+(::Union{StepRangeLen,OrdinalRange,LinRange}, ::Union{...})", "+(::StepRangeLen{T,S}, ::StepRangeLen{T,S})",
      "-(::StepRangeLen, ::StepRangeLen)"]
    statement := "Range +/- throw DimensionMismatch for different lengths; _define_range_op defines the ordinal and LinRange methods; the promoting method applies the operator to the promoted operands; LinRange sums add endpoints; StepRangeLen subtraction adds the negation."
    source := "base/range.jl:1490-1524 (argument dimensions must match)"
    status := .proven, prop := ``RangeArithmetic, thm := some ``rangeArithmetic_proven },
  { id := "rangescov-ordinal-add-small-int", juliaFile := "base/range.jl"
    juliaFns := ["+(::OrdinalRange, ::OrdinalRange)"]
    statement := "(r1 + r2)[i] == r1[i] + r2[i] for integer unit ranges of equal length."
    source := "+ on arrays is elementwise (base/arraymath.jl)"
    status := .refuted, prop := ``OrdinalAddElementwise, thm := some ``ordinalAddElementwise_refuted
    issue := "none found; related #64133 (queries: issues range addition Int8 InexactError; prs range addition Int8 InexactError)"
    notes := "(Int8(126):Int8(127)) + (Int8(1):Int8(2)) is StepRangeLen{Int8}(127, 2, 2); its second element 129 is computed in Int and convert(Int8, 129) throws." },
  { id := "rangescov-sorting-methods", juliaFile := "base/range.jl"
    juliaFns := ["issorted(::AbstractUnitRange)", "sort(::AbstractUnitRange)", "sort!(::AbstractUnitRange)",
      "sortperm(::AbstractUnitRange)", "sortperm(::AbstractRange)"]
    statement := "Unit ranges are sorted and sort/sort! return them; sortperm of a unit range is OneTo(length(r)); sortperm of a range is firstindex:1:lastindex when issorted and the reverse otherwise."
    source := "issorted/sort/sortperm docstrings (base/sort.jl); base/range.jl:1445-1456"
    status := .proven, prop := ``SortingMethods, thm := some ``sortingMethods_proven },
  { id := "rangescov-issorted-full-width", juliaFile := "base/range.jl"
    juliaFns := ["issorted(::AbstractRange)"]
    statement := "issorted(r) of a constructed integer StepRange implies a nonnegative step or at most one element."
    source := "issorted docstring (base/sort.jl)"
    status := .refuted, prop := ``IssortedSound, thm := some ``issortedSound_refuted
    issue := "none found; related #45389 (queries: issues issorted range overflow; issues sort range typemin typemax; prs issorted range overflow; prs sort range typemin typemax)"
    notes := "typemax(Int):-1:typemin(Int) has 2^64 elements; length wraps to 0 (same cause as ranges-length-overflow-silent), so issorted is true and sort returns the descending range." },
  { id := "rangescov-mod-methods", juliaFile := "base/range.jl"
    juliaFns := ["mod(::Integer, ::OneTo)", "mod(::Integer, ::AbstractUnitRange{<:Integer})"]
    statement := "mod(i, OneTo(n)) is mod1(i, n) and mod(i, r) on unit ranges is mod(i - first(r), length(r)) + first(r); the docstring examples mod(0, OneTo(3)) == 3 and mod(3, 0:2) == 0 hold."
    source := "mod(x::Integer, r::AbstractUnitRange) docstring base/range.jl:1528-1543"
    status := .proven, prop := ``ModMethods, thm := some ``modMethods_proven }
]

end Ops

end JuliaLean.RangesCov
