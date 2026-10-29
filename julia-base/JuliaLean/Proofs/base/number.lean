import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.number

open JuliaLean JuliaLean.Registry

/-- A Number's scalar length equals the length of its one-element key axis. -/
def ScalarShape : Prop :=
  ∀ (α τ κ : Type) (x : α) (tag : τ) (hasShapeZero : Unit → κ),
  JuliaLean.base.number.size x = () ∧
  JuliaLean.base.number.axes x = () ∧
  JuliaLean.base.number.ndimsValue x = JInt.lit .i64 0 ∧
  JuliaLean.base.number.ndimsType tag = JuliaLean.base.number.ndimsValue x ∧
  JuliaLean.base.number.length x = JInt.lit .i64 1 ∧
  JuliaLean.base.number.firstindex x = JuliaLean.base.number.lastindex x ∧
  JuliaLean.base.number.firstindex x = JInt.lit .i64 1 ∧
  JuliaLean.base.number.eltype tag = tag ∧
  JuliaLean.base.number.iteratorSize tag hasShapeZero = hasShapeZero () ∧
  JuliaLean.base.number.keys x JuliaLean.base.range.unchecked_oneto =
    JuliaLean.base.range.unchecked_oneto (JuliaLean.base.number.firstindex x) ∧
  JuliaLean.base.number.length x =
    JuliaLean.base.range.length_OneTo_bigints
      (JuliaLean.base.number.keys x JuliaLean.base.range.unchecked_oneto)

theorem scalarShape_proven : ScalarShape := by
  intro α τ κ x tag hasShapeZero
  simp [JuliaLean.base.number.size, JuliaLean.base.number.axes,
    JuliaLean.base.number.ndimsValue, JuliaLean.base.number.ndimsType,
    JuliaLean.base.number.length, JuliaLean.base.number.firstindex,
    JuliaLean.base.number.lastindex, JuliaLean.base.number.eltype,
    JuliaLean.base.number.iteratorSize, JuliaLean.base.number.keys,
    JuliaLean.base.range.unchecked_oneto, JuliaLean.base.range.length_OneTo_bigints]

/-- Dimension queries reject dimensions below 1, return singleton size and `OneTo(1)` for all positive integer dimensions (across generic `Integer` types and every `BitInteger` width), and agree with `firstindex`/`lastindex` on `Int`. -/
def ScalarDimensions : Prop :=
  ∀ (α δ : Type) (x : α) (d : δ) (dVal : δ → Int) (lessThanOne : δ → Jl Bool)
    (t : IntTy) (bitDim : JInt t) (machineDim : JInt64),
  let ltBit : JInt t → Jl Bool :=
    fun idx => .ok (JuliaLean.base.int.lt idx (JInt.lit .i64 1))
  let ltMachine : JInt64 → Jl Bool :=
    fun idx => .ok (JuliaLean.base.int.lt idx (JInt.lit .i64 1))
  let oneToJl := fun axis => (.ok (JuliaLean.base.range.unchecked_oneto axis) : Jl (JuliaLean.base.range.OneTo JInt64))
  (∀ idx : δ, lessThanOne idx = .ok (decide (dVal idx < 1))) →
  ((JuliaLean.base.number.sizeDim lessThanOne x d = .error .boundsError ↔ dVal d < 1) ∧
   (JuliaLean.base.number.axesDim lessThanOne oneToJl x d = .error .boundsError ↔ dVal d < 1) ∧
   (JuliaLean.base.number.sizeDim lessThanOne x d = .ok (JuliaLean.base.number.length x) ↔ 1 ≤ dVal d) ∧
   (JuliaLean.base.number.axesDim lessThanOne oneToJl x d =
      .ok (JuliaLean.base.number.keys x JuliaLean.base.range.unchecked_oneto) ↔ 1 ≤ dVal d)) ∧
  ((JuliaLean.base.number.sizeDim ltBit x bitDim = .error .boundsError ↔ bitDim.val < 1) ∧
   (JuliaLean.base.number.axesDim ltBit oneToJl x bitDim = .error .boundsError ↔ bitDim.val < 1) ∧
   (JuliaLean.base.number.sizeDim ltBit x bitDim = .ok (JuliaLean.base.number.length x) ↔ 1 ≤ bitDim.val) ∧
   (JuliaLean.base.number.axesDim ltBit oneToJl x bitDim =
      .ok (JuliaLean.base.number.keys x JuliaLean.base.range.unchecked_oneto) ↔ 1 ≤ bitDim.val)) ∧
  ((JuliaLean.base.number.firstindexDim x machineDim = .error .boundsError ↔ machineDim.val < 1) ∧
   (JuliaLean.base.number.lastindexDim x machineDim = .error .boundsError ↔ machineDim.val < 1) ∧
   (JuliaLean.base.number.firstindexDim x machineDim = .ok (JuliaLean.base.number.firstindex x) ↔
      1 ≤ machineDim.val) ∧
   (JuliaLean.base.number.lastindexDim x machineDim = .ok (JuliaLean.base.number.lastindex x) ↔
      1 ≤ machineDim.val) ∧
   JuliaLean.base.number.firstindexDim x machineDim =
     JuliaLean.base.number.lastindexDim x machineDim ∧
   JuliaLean.base.number.firstindexDim x machineDim =
     JuliaLean.base.number.sizeDim ltMachine x machineDim)

theorem scalarDimensions_proven : ScalarDimensions := by
  intro α δ x d dVal lessThanOne t bitDim machineDim ltBit ltMachine oneToJl hLt
  have hLit1 : (JInt.lit .i64 1).val = 1 := by decide
  have hLtBit : JuliaLean.base.int.lt bitDim (JInt.lit .i64 1) = decide (bitDim.val < 1) := by
    rw [JuliaLean.Proofs.base.int.lt_eq, hLit1]
  have hLtMachine : JuliaLean.base.int.lt machineDim (JInt.lit .i64 1) = decide (machineDim.val < 1) := by
    rw [JuliaLean.Proofs.base.int.lt_eq, hLit1]
  refine ⟨?_, ?_, ?_⟩
  · by_cases hd : dVal d < 1 <;>
      simp [JuliaLean.base.number.sizeDim, JuliaLean.base.number.axesDim,
        JuliaLean.base.number.length, JuliaLean.base.number.keys,
        oneToJl, hLt d, hd, Bind.bind, Except.bind, Pure.pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] <;> omega
  · by_cases hb : bitDim.val < 1 <;>
      simp [JuliaLean.base.number.sizeDim, JuliaLean.base.number.axesDim,
        JuliaLean.base.number.length, JuliaLean.base.number.keys,
        ltBit, oneToJl, hLtBit, hb, Bind.bind, Except.bind, Pure.pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] <;> omega
  · by_cases hm : machineDim.val < 1 <;>
      simp [JuliaLean.base.number.firstindexDim, JuliaLean.base.number.lastindexDim,
        JuliaLean.base.number.firstindex, JuliaLean.base.number.lastindex,
        JuliaLean.base.number.sizeDim, ltMachine, hLtMachine, hm,
        Bind.bind, Except.bind, Pure.pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] <;> omega

/-- Scalar indexing and `get` over any `Number` accept unit indices across arbitrary integer/boolean/mixed-tuple index types and every `BitInteger` width, and collection/iteration operations treat every `Number` as a 1-element container. -/
def ScalarCollection : Prop :=
  ∀ (α β γ τ σ : Type) (t : IntTy) (x default : α) (state : σ)
    (i : β) (indices : γ) (typeOf : β → τ)
    (constructor : τ → Int → Jl β) (equalIndex : β → β → Jl Bool)
    (equalOneLit : β → Jl Bool) (isUnitIndex : β → Bool)
    (tupleElements : γ → List β)
    (all : (β → Jl Bool) → γ → Jl Bool)
    (bitIdx : JInt t) (bitIndices : List (JInt t))
    (allBit : (JInt t → Jl Bool) → List (JInt t) → Jl Bool)
    (fallback : Unit → Jl α),
  let convert : τ → Int → Jl β :=
    fun tag value => JuliaLean.base.number.convertNumber (constructor tag) value
  let oneType : τ → Jl β := JuliaLean.base.number.oneType convert
  let one : β → Jl β := JuliaLean.base.number.oneValue typeOf oneType
  let isOne : β → Jl Bool := JuliaLean.base.number.isone one equalIndex
  let allOne : Bool := (tupleElements indices).all isUnitIndex
  let convertBit : IntTy → Int → Jl (JInt t) :=
    fun _ value => JuliaLean.base.number.convertNumber
      (fun v => JuliaLean.base.int.convert t (JInt.lit .i64 v)) value
  let oneTypeBit : IntTy → Jl (JInt t) := JuliaLean.base.number.oneType convertBit
  let oneBit : JInt t → Jl (JInt t) := JuliaLean.base.number.oneValue (fun _ => t) oneTypeBit
  let isOneBit : JInt t → Jl Bool :=
    JuliaLean.base.number.isone oneBit (fun a b => .ok (JuliaLean.base.int.eqSame a b))
  let eqOneBit : JInt t → Jl Bool :=
    fun idx => .ok (JuliaLean.base.int.eq idx (JInt.lit .i64 1))
  let allOneBit : Prop := ∀ idx, idx ∈ bitIndices → idx.val = 1
  (∀ idx : β, ∃ u : β, constructor (typeOf idx) 1 = .ok u ∧
    equalIndex idx u = .ok (isUnitIndex idx)) →
  (∀ idx : β, equalOneLit idx = .ok (isUnitIndex idx)) →
  all isOne indices = .ok allOne →
  allBit isOneBit bitIndices = .ok (decide allOneBit) →
  (∀ idx : β, isOne idx = .ok (isUnitIndex idx)) ∧
  JuliaLean.base.number.getindex0 x = x ∧
  JuliaLean.base.number.getindexOne equalOneLit x i =
    (if isUnitIndex i then .ok x else .error .boundsError) ∧
  JuliaLean.base.number.getindexMany all isOne x indices =
    (if allOne then .ok x else .error .boundsError) ∧
  JuliaLean.base.number.getDefaultIndex isOne x default i =
    .ok (if isUnitIndex i then x else default) ∧
  JuliaLean.base.number.getDefaultTuple all isOne x default indices =
    .ok (if allOne then x else default) ∧
  JuliaLean.base.number.getThunkIndex isOne fallback x i =
    (if isUnitIndex i then .ok x else fallback ()) ∧
  JuliaLean.base.number.getThunkTuple all isOne fallback x indices =
    (if allOne then .ok x else fallback ()) ∧
  isOneBit (JInt.lit t 1) = .ok true ∧
  (∀ idx : JInt t, isOneBit idx = .ok (decide (idx.val = 1))) ∧
  JuliaLean.base.number.getindexOne eqOneBit x bitIdx =
    (if bitIdx.val = 1 then .ok x else .error .boundsError) ∧
  JuliaLean.base.number.getindexMany allBit isOneBit x bitIndices =
    (if allOneBit then .ok x else .error .boundsError) ∧
  JuliaLean.base.number.getDefaultIndex isOneBit x default bitIdx =
    .ok (if bitIdx.val = 1 then x else default) ∧
  JuliaLean.base.number.getDefaultTuple allBit isOneBit x default bitIndices =
    .ok (if allOneBit then x else default) ∧
  JuliaLean.base.number.getThunkIndex isOneBit fallback x bitIdx =
    (if bitIdx.val = 1 then .ok x else fallback ()) ∧
  JuliaLean.base.number.getThunkTuple allBit isOneBit fallback x bitIndices =
    (if allOneBit then .ok x else fallback ()) ∧
  JuliaLean.base.number.first x = JuliaLean.base.number.getindex0 x ∧
  JuliaLean.base.number.last x = JuliaLean.base.number.first x ∧
  JuliaLean.base.number.copy x = JuliaLean.base.number.first x ∧
  JuliaLean.base.number.iterate x = some (JuliaLean.base.number.first x, none) ∧
  JuliaLean.base.number.iterateNext x state = none ∧
  JuliaLean.base.number.isempty x = false

theorem scalarCollection_proven : ScalarCollection := by
  intro α β γ τ σ t x default state i indices typeOf constructor equalIndex equalOneLit
    isUnitIndex tupleElements all bitIdx bitIndices allBit fallback
    convert oneType one isOne allOne convertBit oneTypeBit oneBit isOneBit eqOneBit allOneBit
    hOneGeneric hEqOneLit hAllGeneric hAllBit
  have hIsOneGeneric : ∀ idx : β, isOne idx = .ok (isUnitIndex idx) := by
    intro idx
    rcases hOneGeneric idx with ⟨u, hu, heq⟩
    simp [isOne, JuliaLean.base.number.isone, one, JuliaLean.base.number.oneValue,
      oneType, JuliaLean.base.number.oneType, convert, JuliaLean.base.number.convertNumber,
      Bind.bind, Except.bind, hu, heq]
  have hOneValueBit : ∀ value : JInt t, oneBit value = .ok (JInt.lit t 1) := by
    intro value
    cases t <;>
      simp [oneBit, JuliaLean.base.number.oneValue, oneTypeBit,
        JuliaLean.base.number.oneType, convertBit, JuliaLean.base.number.convertNumber,
        JuliaLean.base.int.convert, JInt.convert, JInt.lit, JInt.wrap, wrapInt,
        IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  have hLitOne : (JInt.lit t 1).val = 1 := by
    cases t <;> simp [JInt.lit, JInt.wrap, wrapInt, IntTy.min,
      IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  have hLitOneI64 : (JInt.lit .i64 1).val = 1 := by decide
  have hIsOneBit : ∀ idx : JInt t, isOneBit idx = .ok (decide (idx.val = 1)) := by
    intro idx
    simp only [isOneBit, JuliaLean.base.number.isone, Bind.bind, Except.bind, hOneValueBit]
    simp [JuliaLean.base.int.eqSame, JuliaLean.Proofs.base.int.eq_int_eq, hLitOne]
  have hEqOneBit : ∀ idx : JInt t, eqOneBit idx = .ok (decide (idx.val = 1)) := by
    intro idx
    simp [eqOneBit, JuliaLean.Proofs.base.int.eq_eq, hLitOneI64]
  refine ⟨hIsOneGeneric, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hIsOneBit, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h : isUnitIndex i <;>
      simp [JuliaLean.base.number.getindexOne, hEqOneLit, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · cases h : allOne <;>
      simp [JuliaLean.base.number.getindexMany, hAllGeneric, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · cases h : isUnitIndex i <;>
      simp [JuliaLean.base.number.getDefaultIndex, hIsOneGeneric, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · cases h : allOne <;>
      simp [JuliaLean.base.number.getDefaultTuple, hAllGeneric, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · cases h : isUnitIndex i <;>
      simp [JuliaLean.base.number.getThunkIndex, hIsOneGeneric, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · cases h : allOne <;>
      simp [JuliaLean.base.number.getThunkTuple, hAllGeneric, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa [hLitOne] using hIsOneBit (JInt.lit t 1)
  · by_cases h : bitIdx.val = 1 <;>
      simp [JuliaLean.base.number.getindexOne, hEqOneBit, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · simp [JuliaLean.base.number.getindexMany, hAllBit,
      Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · by_cases h : bitIdx.val = 1 <;>
      simp [JuliaLean.base.number.getDefaultIndex, hIsOneBit, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [JuliaLean.base.number.getDefaultTuple, hAllBit,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · by_cases h : bitIdx.val = 1 <;>
      simp [JuliaLean.base.number.getThunkIndex, hIsOneBit, h,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [JuliaLean.base.number.getThunkTuple, hAllBit,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Equality on BitIntegers is equality of their represented integer values. -/
theorem bitIntegerEqSame {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.eqSame x y = decide (x.val = y.val) := by
  change JuliaLean.base.int.eq_int x y = decide (x.val = y.val)
  exact JuliaLean.Proofs.base.int.eq_int_eq x y

/-- Scalar membership `in(x::Number, y::Number)` tests equality against the unique iterated element of `y`, inherits reflexivity and symmetry of `==` across arbitrary `Number` types, and compares represented integer values across all mixed-width `BitInteger` pairs. -/
def IntegerMembership : Prop :=
  ∀ (α β : Type) (x a b : α) (y : β) (equal : α → β → Jl Bool) (eqSameType : α → α → Jl Bool)
    (s t : IntTy) (bx : JInt s) (by_ : JInt t),
  (∃ elem, JuliaLean.base.number.iterate y = some (elem, none) ∧
    JuliaLean.base.number.iterateNext y () = none ∧
    JuliaLean.base.number.isempty y = false ∧
    JuliaLean.base.number.inNumber equal x y = equal x elem) ∧
  ((∀ z : α, eqSameType z z = .ok true) →
    JuliaLean.base.number.inNumber eqSameType (JuliaLean.base.number.first x) x = .ok true ∧
    JuliaLean.base.number.inNumber eqSameType (JuliaLean.base.number.last x) x = .ok true) ∧
  ((∀ u v : α, eqSameType u v = eqSameType v u) →
    JuliaLean.base.number.inNumber eqSameType a b =
      JuliaLean.base.number.inNumber eqSameType b a) ∧
  JuliaLean.base.number.inNumber
    (fun u v => .ok (JuliaLean.base.int.eq u v)) bx by_ = .ok (decide (bx.val = by_.val)) ∧
  (JuliaLean.base.number.inNumber
    (fun u v => .ok (JuliaLean.base.int.eq u v)) bx by_ = .ok true ↔
    bx.val = by_.val)

theorem integerMembership_proven : IntegerMembership := by
  intro α β x a b y equal eqSameType s t bx by_
  refine ⟨⟨y, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro hRefl
    exact ⟨hRefl x, hRefl x⟩
  · intro hSymm
    exact hSymm a b
  · simp [JuliaLean.base.number.inNumber, JuliaLean.Proofs.base.int.eq_eq]
  · simp [JuliaLean.base.number.inNumber, JuliaLean.Proofs.base.int.eq_eq]

/-- Across all `Number` and `Integer` types (including generic integers, `BigInt`/`Int`, and every `BitInteger` width), `isinteger` holds on all integers, `iszero` and `isone` identify additive and multiplicative identities via the `Number` fallbacks, and `isfinite` holds iff `x - x` equals zero. -/
def IntegerPredicates : Prop :=
  ∀ (α τ ι τi : Type) (x z0 u1 d : α) (n : ι) (t : IntTy) (bx : JInt t) (ix : Int)
    (typeOf : α → τ) (constructor : τ → Int → Jl α)
    (equal : α → α → Jl Bool) (sub : α → α → Jl α)
    (typeOfI : ι → τi) (constructorI : τi → Int → Jl ι)
    (equalI : ι → ι → Jl Bool) (subI : ι → ι → Jl ι) (intVal : ι → Int),
  let convert : τ → Int → Jl α :=
    fun tag value => JuliaLean.base.number.convertNumber (constructor tag) value
  let oftype : α → Int → Jl α := fun y value => convert (typeOf y) value
  let zero : α → Jl α := JuliaLean.base.number.zeroValue oftype
  let oneT : τ → Jl α := JuliaLean.base.number.oneType convert
  let one : α → Jl α := JuliaLean.base.number.oneValue typeOf oneT
  let iszeroN : α → Jl Bool := JuliaLean.base.number.iszero zero equal
  let isoneN : α → Jl Bool := JuliaLean.base.number.isone one equal
  let isfiniteN : α → Jl Bool := JuliaLean.base.number.isfinite iszeroN sub
  let convertI : τi → Int → Jl ι :=
    fun tag value => JuliaLean.base.number.convertNumber (constructorI tag) value
  let oftypeI : ι → Int → Jl ι := fun y value => convertI (typeOfI y) value
  let zeroI : ι → Jl ι := JuliaLean.base.number.zeroValue oftypeI
  let oneTI : τi → Jl ι := JuliaLean.base.number.oneType convertI
  let oneI : ι → Jl ι := JuliaLean.base.number.oneValue typeOfI oneTI
  let iszeroI : ι → Jl Bool := JuliaLean.base.number.iszero zeroI equalI
  let isoneI : ι → Jl Bool := JuliaLean.base.number.isone oneI equalI
  let isfiniteI : ι → Jl Bool := JuliaLean.base.number.isfinite iszeroI subI
  let oftypeBit : JInt t → Int → Jl (JInt t) :=
    fun _ value => JuliaLean.base.number.convertNumber (fun v => .ok (JInt.lit t v)) value
  let convertBit : IntTy → Int → Jl (JInt t) :=
    fun _ value => JuliaLean.base.number.convertNumber (fun v => .ok (JInt.lit t v)) value
  let zeroBit : JInt t → Jl (JInt t) := JuliaLean.base.number.zeroValue oftypeBit
  let oneTypeBit : IntTy → Jl (JInt t) := JuliaLean.base.number.oneType convertBit
  let oneBit : JInt t → Jl (JInt t) := JuliaLean.base.number.oneValue (fun _ => t) oneTypeBit
  let equalBit : JInt t → JInt t → Jl Bool := fun a b => .ok (JuliaLean.base.int.eqSame a b)
  let iszeroBit : JInt t → Jl Bool := JuliaLean.base.number.iszero zeroBit equalBit
  let oftypeInt : Int → Int → Jl Int :=
    fun _ value => JuliaLean.base.number.convertNumber
      (fun v => .ok (JuliaLean.base.number.convertSame v)) value
  let convertInt : Unit → Int → Jl Int :=
    fun _ value => JuliaLean.base.number.convertNumber
      (fun v => .ok (JuliaLean.base.number.convertSame v)) value
  let zeroInt : Int → Jl Int := JuliaLean.base.number.zeroValue oftypeInt
  let oneTypeInt : Unit → Jl Int := JuliaLean.base.number.oneType convertInt
  let oneInt : Int → Jl Int := JuliaLean.base.number.oneValue (fun _ => ()) oneTypeInt
  let equalInt : Int → Int → Jl Bool := fun a b => .ok (decide (a = b))
  let iszeroInt : Int → Jl Bool := JuliaLean.base.number.iszero zeroInt equalInt
  ((sub x x = .ok z0 ∧ constructor (typeOf z0) 0 = .ok z0 ∧ equal z0 z0 = .ok true ∧
    constructor (typeOf u1) 1 = .ok u1 ∧ equal u1 u1 = .ok true →
      iszeroN z0 = .ok true ∧ isoneN u1 = .ok true ∧ isfiniteN x = .ok true) ∧
   (sub x x = .ok d ∧ constructor (typeOf d) 0 = .ok z0 ∧ equal d z0 = .ok false →
      isfiniteN x = .ok false)) ∧
  ((∀ v : ι, ∃ z : ι, constructorI (typeOfI v) 0 = .ok z ∧ intVal z = 0) →
   (∀ v : ι, ∃ o : ι, constructorI (typeOfI v) 1 = .ok o ∧ intVal o = 1) →
   (∀ a b : ι, equalI a b = .ok (decide (intVal a = intVal b))) →
   (∀ a b : ι, ∃ diff : ι, subI a b = .ok diff ∧ intVal diff = intVal a - intVal b) →
   JuliaLean.base.number.isintegerInteger n = true ∧
   iszeroI n = .ok (decide (intVal n = 0)) ∧
   isoneI n = .ok (decide (intVal n = 1)) ∧
   isfiniteI n = .ok true ∧
   ¬(iszeroI n = .ok true ∧ isoneI n = .ok true)) ∧
  (JuliaLean.base.number.isintegerInteger bx = true ∧
   JuliaLean.base.number.iszero zeroBit equalBit bx = .ok (decide (bx.val = 0)) ∧
   JuliaLean.base.number.isone oneBit equalBit bx = .ok (decide (bx.val = 1)) ∧
   JuliaLean.base.number.isfinite iszeroBit
     (fun a b => .ok (JuliaLean.base.int.sub a b)) bx = .ok true) ∧
  (JuliaLean.base.number.isintegerInteger ix = true ∧
   JuliaLean.base.number.iszero zeroInt equalInt ix = .ok (decide (ix = 0)) ∧
   JuliaLean.base.number.isone oneInt equalInt ix = .ok (decide (ix = 1)) ∧
   JuliaLean.base.number.isfinite iszeroInt (fun a b => .ok (a - b)) ix = .ok true)

theorem integerPredicates_proven : IntegerPredicates := by
  intro α τ ι τi x z0 u1 d n t bx ix typeOf constructor equal sub
    typeOfI constructorI equalI subI intVal
    convert oftype zero oneT one iszeroN isoneN isfiniteN
    convertI oftypeI zeroI oneTI oneI iszeroI isoneI isfiniteI
    oftypeBit convertBit zeroBit oneTypeBit oneBit equalBit iszeroBit
    oftypeInt convertInt zeroInt oneTypeInt oneInt equalInt iszeroInt
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hSub, hZ0, hEq0, hU1, hEq1⟩
      simp [iszeroN, isoneN, isfiniteN, JuliaLean.base.number.iszero,
        JuliaLean.base.number.isone, JuliaLean.base.number.isfinite,
        zero, one, oneT, JuliaLean.base.number.zeroValue,
        JuliaLean.base.number.oneValue, JuliaLean.base.number.oneType,
        oftype, convert, JuliaLean.base.number.convertNumber,
        hSub, hZ0, hEq0, hU1, hEq1, Bind.bind, Except.bind]
    · rintro ⟨hSub, hZ0, hEqFalse⟩
      simp [isfiniteN, iszeroN, JuliaLean.base.number.isfinite, JuliaLean.base.number.iszero,
        zero, JuliaLean.base.number.zeroValue, oftype, convert,
        JuliaLean.base.number.convertNumber, hSub, hZ0, hEqFalse,
        Bind.bind, Except.bind]
  · intro hZeroI hOneI hEqI hSubI
    rcases hZeroI n with ⟨z, hz, hzVal⟩
    rcases hOneI n with ⟨o, ho, hoVal⟩
    rcases hSubI n n with ⟨diff, hdiff, hdiffVal⟩
    rcases hZeroI diff with ⟨zd, hzd, hzdVal⟩
    have hIsZeroN : iszeroI n = .ok (decide (intVal n = 0)) := by
      simp [iszeroI, JuliaLean.base.number.iszero, zeroI, JuliaLean.base.number.zeroValue,
        oftypeI, convertI, JuliaLean.base.number.convertNumber,
        Bind.bind, Except.bind, hz, hEqI, hzVal]
    have hIsOneN : isoneI n = .ok (decide (intVal n = 1)) := by
      simp [isoneI, JuliaLean.base.number.isone, oneI, JuliaLean.base.number.oneValue,
        oneTI, JuliaLean.base.number.oneType, convertI, JuliaLean.base.number.convertNumber,
        Bind.bind, Except.bind, ho, hEqI, hoVal]
    have hIsFiniteN : isfiniteI n = .ok true := by
      have hDiffZero : intVal diff = intVal zd := by omega
      simp [isfiniteI, JuliaLean.base.number.isfinite, iszeroI, JuliaLean.base.number.iszero,
        zeroI, JuliaLean.base.number.zeroValue, oftypeI, convertI,
        JuliaLean.base.number.convertNumber, Bind.bind, Except.bind,
        hdiff, hzd, hEqI, hDiffZero]
    refine ⟨rfl, hIsZeroN, hIsOneN, hIsFiniteN, ?_⟩
    rw [hIsZeroN, hIsOneN]
    simp
    omega
  · cases t <;>
      simp only [oftypeBit, convertBit, zeroBit, oneTypeBit, oneBit, equalBit, iszeroBit,
        JuliaLean.base.number.convertNumber, JuliaLean.base.number.zeroValue,
        JuliaLean.base.number.oneType, JuliaLean.base.number.oneValue,
        JuliaLean.base.number.iszero, JuliaLean.base.number.isone,
        JuliaLean.base.number.isfinite, JuliaLean.base.number.isintegerInteger,
        JuliaLean.base.int.sub, Bind.bind, Except.bind]
    all_goals
      rw [bitIntegerEqSame, bitIntegerEqSame, bitIntegerEqSame]
      simp [JInt.lit, JInt.wrap, wrapInt, IntTy.min, IntTy.max,
        IntTy.signed, IntTy.bits, JuliaLean.Proofs.base.int.sub_int_val]
  · simp [oftypeInt, convertInt, zeroInt, oneTypeInt, oneInt, equalInt, iszeroInt,
      JuliaLean.base.number.convertNumber, JuliaLean.base.number.convertSame,
      JuliaLean.base.number.zeroValue, JuliaLean.base.number.oneType,
      JuliaLean.base.number.oneValue, JuliaLean.base.number.iszero,
      JuliaLean.base.number.isone, JuliaLean.base.number.isfinite,
      JuliaLean.base.number.isintegerInteger, Bind.bind, Except.bind]

/-- Across all `Number` types (and concretely on every `BitInteger` width and `Int`), `zero`, `one`, and `oneunit` agree between value and type overloads, `oneunit` coincides with `one` under identity self-conversion, and `zero`/`one`/`oneunit` yield additive and multiplicative identities. -/
def IntegerZeroOneUnits : Prop :=
  ∀ (α τ : Type) (x z0 u1 : α) (typeOf : α → τ)
    (constructor : τ → Int → Jl α) (constructT : α → Jl α)
    (add mul : α → α → Jl α)
    (t : IntTy) (bx : JInt t) (ix : Int),
  let convert : τ → Int → Jl α :=
    fun tag value => JuliaLean.base.number.convertNumber (constructor tag) value
  let oftype : α → Int → Jl α := fun y value => convert (typeOf y) value
  let zeroVal : α → Jl α := JuliaLean.base.number.zeroValue oftype
  let zeroTyp : τ → Jl α := JuliaLean.base.number.zeroType convert
  let oneTyp : τ → Jl α := JuliaLean.base.number.oneType convert
  let oneVal : α → Jl α := JuliaLean.base.number.oneValue typeOf oneTyp
  let oneunitVal : α → Jl α := JuliaLean.base.number.oneunitValue oneVal constructT
  let oneunitTyp : τ → Jl α := JuliaLean.base.number.oneunitType oneTyp constructT
  let convertBit : IntTy → Int → Jl (JInt t) :=
    fun _ value => JuliaLean.base.number.convertNumber
      (fun v => JuliaLean.base.int.convert t (JInt.lit .i64 v)) value
  let oftypeBit : JInt t → Int → Jl (JInt t) := fun _ value => convertBit t value
  let oneTypeBit : IntTy → Jl (JInt t) := JuliaLean.base.number.oneType convertBit
  let oneValueBit : JInt t → Jl (JInt t) := JuliaLean.base.number.oneValue (fun _ => t) oneTypeBit
  let constructBit : JInt t → Jl (JInt t) :=
    fun v => .ok (JuliaLean.base.number.convertSame v)
  let sameConversion : Int → Jl Int :=
    fun value => JuliaLean.base.number.convertNumber
      (fun value => .ok (JuliaLean.base.number.convertSame value)) value
  let oftypeInt : Int → Int → Jl Int := fun _ value => sameConversion value
  let convertInt : Unit → Int → Jl Int := fun _ value => sameConversion value
  let typeOneInt : Unit → Jl Int := JuliaLean.base.number.oneType convertInt
  let valueOneInt : Int → Jl Int := JuliaLean.base.number.oneValue (fun _ => ()) typeOneInt
  let constructInt : Int → Jl Int := sameConversion
  (zeroVal x = zeroTyp (typeOf x) ∧
   oneVal x = oneTyp (typeOf x) ∧
   oneunitVal x = oneunitTyp (typeOf x) ∧
   ((∀ y : α, constructT y = .ok (JuliaLean.base.number.convertSame y)) →
      oneunitVal x = oneVal x ∧ oneunitTyp (typeOf x) = oneTyp (typeOf x)) ∧
   (constructor (typeOf x) 0 = .ok z0 →
    constructor (typeOf x) 1 = .ok u1 →
    constructT u1 = .ok (JuliaLean.base.number.convertSame u1) →
    add z0 x = .ok x → add x z0 = .ok x →
    mul u1 x = .ok x → mul x u1 = .ok x →
      zeroVal x = .ok z0 ∧ zeroTyp (typeOf x) = .ok z0 ∧
      oneVal x = .ok u1 ∧ oneTyp (typeOf x) = .ok u1 ∧
      oneunitVal x = .ok u1 ∧ oneunitTyp (typeOf x) = .ok u1 ∧
      add z0 x = .ok x ∧ add x z0 = .ok x ∧
      mul u1 x = .ok x ∧ mul x u1 = .ok x)) ∧
  (JuliaLean.base.number.zeroValue oftypeBit bx = .ok (JInt.lit t 0) ∧
   JuliaLean.base.number.zeroType convertBit t = .ok (JInt.lit t 0) ∧
   oneTypeBit t = .ok (JInt.lit t 1) ∧
   oneValueBit bx = .ok (JInt.lit t 1) ∧
   JuliaLean.base.number.oneunitValue oneValueBit constructBit bx = .ok (JInt.lit t 1) ∧
   JuliaLean.base.number.oneunitType oneTypeBit constructBit t = .ok (JInt.lit t 1) ∧
   JuliaLean.base.int.add (JInt.lit t 0) bx = bx ∧
   JuliaLean.base.int.add bx (JInt.lit t 0) = bx ∧
   JuliaLean.base.int.mul (JInt.lit t 1) bx = bx ∧
   JuliaLean.base.int.mul bx (JInt.lit t 1) = bx) ∧
  (JuliaLean.base.number.zeroValue oftypeInt ix = .ok 0 ∧
   JuliaLean.base.number.zeroType convertInt () = .ok 0 ∧
   typeOneInt () = .ok 1 ∧
   valueOneInt ix = .ok 1 ∧
   JuliaLean.base.number.oneunitValue valueOneInt constructInt ix = .ok 1 ∧
   JuliaLean.base.number.oneunitType typeOneInt constructInt () = .ok 1 ∧
   (∀ zero, JuliaLean.base.number.zeroValue oftypeInt ix = .ok zero → zero + ix = ix ∧ ix + zero = ix) ∧
   (∀ unit, JuliaLean.base.number.oneunitValue valueOneInt constructInt ix = .ok unit →
      unit * ix = ix ∧ ix * unit = ix))

theorem integerZeroOneUnits_proven : IntegerZeroOneUnits := by
  intro α τ x z0 u1 typeOf constructor constructT add mul t bx ix
    convert oftype zeroVal zeroTyp oneTyp oneVal oneunitVal oneunitTyp
    convertBit oftypeBit oneTypeBit oneValueBit constructBit
    sameConversion oftypeInt convertInt typeOneInt valueOneInt constructInt
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro hConstructId
      constructor <;>
        (cases h : oneTyp (typeOf x) <;>
          simp [oneunitVal, oneunitTyp, oneVal, oneTyp,
            JuliaLean.base.number.oneunitValue, JuliaLean.base.number.oneunitType,
            JuliaLean.base.number.oneValue, JuliaLean.base.number.convertSame,
            Bind.bind, Except.bind, h, hConstructId])
    · intro hz0 hu1 hConstructU1 hAddL hAddR hMulL hMulR
      simp [zeroVal, zeroTyp, oneVal, oneTyp, oneunitVal, oneunitTyp,
        JuliaLean.base.number.zeroValue, JuliaLean.base.number.zeroType,
        JuliaLean.base.number.oneValue, JuliaLean.base.number.oneType,
        JuliaLean.base.number.oneunitValue, JuliaLean.base.number.oneunitType,
        oftype, convert, JuliaLean.base.number.convertNumber,
        JuliaLean.base.number.convertSame, Bind.bind, Except.bind,
        hz0, hu1, hConstructU1, hAddL, hAddR, hMulL, hMulR]
  · have hLit0 : (JInt.lit t 0).val = wrapInt t 0 := rfl
    have hLit1 : (JInt.lit t 1).val = wrapInt t 1 := rfl
    have hAddL : JuliaLean.base.int.add (JInt.lit t 0) bx = bx := by
      apply JuliaLean.Proofs.base.int.jint_eq
      simp only [JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val, hLit0]
      rw [JuliaLean.Proofs.base.int.wrapInt_add_left, Int.zero_add,
        JuliaLean.Proofs.base.int.wrapInt_val]
    have hAddR : JuliaLean.base.int.add bx (JInt.lit t 0) = bx := by
      apply JuliaLean.Proofs.base.int.jint_eq
      simp only [JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val, hLit0]
      rw [JuliaLean.Proofs.base.int.wrapInt_add_right, Int.add_zero,
        JuliaLean.Proofs.base.int.wrapInt_val]
    have hMulL : JuliaLean.base.int.mul (JInt.lit t 1) bx = bx := by
      apply JuliaLean.Proofs.base.int.jint_eq
      simp only [JuliaLean.base.int.mul, JuliaLean.Proofs.base.int.mul_int_val, hLit1]
      rw [JuliaLean.Proofs.base.int.wrapInt_mul_left, Int.one_mul,
        JuliaLean.Proofs.base.int.wrapInt_val]
    have hMulR : JuliaLean.base.int.mul bx (JInt.lit t 1) = bx := by
      apply JuliaLean.Proofs.base.int.jint_eq
      simp only [JuliaLean.base.int.mul, JuliaLean.Proofs.base.int.mul_int_val, hLit1]
      rw [JuliaLean.Proofs.base.int.wrapInt_mul_right, Int.mul_one,
        JuliaLean.Proofs.base.int.wrapInt_val]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hAddL, hAddR, hMulL, hMulR⟩
    all_goals
      cases t <;>
        simp [oftypeBit, convertBit, oneTypeBit, oneValueBit, constructBit,
          JuliaLean.base.number.zeroValue, JuliaLean.base.number.zeroType,
          JuliaLean.base.number.oneType, JuliaLean.base.number.oneValue,
          JuliaLean.base.number.oneunitValue, JuliaLean.base.number.oneunitType,
          JuliaLean.base.number.convertNumber, JuliaLean.base.number.convertSame,
          JuliaLean.base.int.convert, JInt.convert, JInt.lit, JInt.wrap, wrapInt,
          IntTy.min, IntTy.max, IntTy.signed, IntTy.bits,
          Bind.bind, Except.bind] <;> omega
  · simp [oftypeInt, convertInt, typeOneInt, valueOneInt, constructInt, sameConversion,
      JuliaLean.base.number.zeroValue, JuliaLean.base.number.zeroType,
      JuliaLean.base.number.oneType, JuliaLean.base.number.oneValue,
      JuliaLean.base.number.oneunitValue, JuliaLean.base.number.oneunitType,
      JuliaLean.base.number.convertNumber, JuliaLean.base.number.convertSame,
      Bind.bind, Except.bind]
/-- For real integers, absolute value is nonnegative and sign copies preserve magnitude. -/
def IntegerMagnitudeSigns : Prop := ∀ x y : Int,
  let signbit := fun z : Int => JuliaLean.base.number.signbit
    (fun w : Int => .ok (decide (w < 0))) z
  let negate := fun z : Int => .ok (-z)
  let positive := fun z : Int => .ok z
  let ifelse := fun (condition : Bool) (yes no : Int) => if condition then yes else no
  let magnitude := if x < 0 then -x else x
  let flipped := if y < 0 then -x else x
  let copied := if decide (x < 0) != decide (y < 0) then -x else x
  JuliaLean.base.number.absReal signbit negate ifelse x = .ok magnitude ∧
  0 ≤ magnitude ∧
  JuliaLean.base.number.flipsign signbit negate positive ifelse x y = .ok flipped ∧
  JuliaLean.base.number.copysign signbit signbit negate positive ifelse x y = .ok copied ∧
  copied * copied = x * x ∧
  (x ≠ 0 → (copied < 0 ↔ y < 0))

theorem integerMagnitudeSigns_proven : IntegerMagnitudeSigns := by
  intro x y
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;>
    simp [JuliaLean.base.number.absReal,
      JuliaLean.base.number.flipsign, JuliaLean.base.number.copysign,
      JuliaLean.base.number.signbit, hx, hy, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Int.neg_mul_neg] <;> omega


/-- A successful generic Number sign quotient times its selected magnitude recovers the input under exact division. -/
def NumberSignMagnitude : Prop :=
  ∀ (α τ β γ : Type) (x : α) (typeOf : α → τ)
    (constructor : Int → Jl α) (equal : α → α → Jl Bool)
    (constructT : α → Jl α) (magnitude : α → Jl β)
    (divide : α → β → Jl γ) (multiply : γ → β → Jl α),
  let oftype : α → Int → Jl α :=
    fun _ value => JuliaLean.base.number.convertNumber constructor value
  let convert : τ → Int → Jl α :=
    fun _ value => JuliaLean.base.number.convertNumber constructor value
  let zero : α → Jl α := JuliaLean.base.number.zeroValue oftype
  let iszero : α → Jl Bool := JuliaLean.base.number.iszero zero equal
  let oneType : τ → Jl α := JuliaLean.base.number.oneType convert
  let one : α → Jl α := JuliaLean.base.number.oneValue typeOf oneType
  let oneunit : α → Jl α := JuliaLean.base.number.oneunitValue one constructT
  (∀ a b q, divide a b = .ok q → multiply q b = .ok a) →
  ∀ r, JuliaLean.base.number.signNumber iszero oneunit magnitude divide x = .ok r →
    (iszero x = .ok true →
      ∃ u m, oneunit x = .ok u ∧ magnitude u = .ok m ∧ multiply r m = .ok x) ∧
    (iszero x = .ok false →
      ∃ m, magnitude x = .ok m ∧ multiply r m = .ok x)

theorem numberSignMagnitude_proven : NumberSignMagnitude := by
  intro α τ β γ x typeOf constructor equal constructT magnitude divide multiply
    oftype convert zero iszero oneType one oneunit divisionLaw r signResult
  cases hzero : iszero x with
  | error err =>
      simp [JuliaLean.base.number.signNumber, hzero,
        Bind.bind, Except.bind] at signResult
  | ok isZero =>
      cases isZero with
      | false =>
          constructor
          · intro htrue
            simp at htrue
          · intro hfalse
            cases hm : magnitude x with
            | error err =>
                simp [JuliaLean.base.number.signNumber, hzero, hm,
                  Bind.bind, Except.bind] at signResult
            | ok m =>
                have hquot := signResult
                simp [JuliaLean.base.number.signNumber, hzero, hm,
                  Bind.bind, Except.bind] at hquot
                exact ⟨m, rfl, divisionLaw x m r hquot⟩
      | true =>
          constructor
          · intro htrue
            cases hu : oneunit x with
            | error err =>
                simp [JuliaLean.base.number.signNumber, hzero, hu,
                  Bind.bind, Except.bind] at signResult
            | ok u =>
                cases hm : magnitude u with
                | error err =>
                    simp [JuliaLean.base.number.signNumber, hzero, hu, hm,
                      Bind.bind, Except.bind] at signResult
                | ok m =>
                    have hquot := signResult
                    simp [JuliaLean.base.number.signNumber, hzero, hu, hm,
                      Bind.bind, Except.bind] at hquot
                    exact ⟨u, m, rfl, hm, divisionLaw x m r hquot⟩
          · intro hfalse
            simp at hfalse
/-- Unsigned integer sign uses the Number zero/one fallbacks and preserves multiplication by input. -/
def UnsignedSignIdentity : Prop := ∀ n : Nat,
  let convertNumber : Int → Jl Nat :=
    fun value => JuliaLean.base.number.convertNumber
      (fun value => .ok value.toNat) value
  let oftype : Nat → Int → Jl Nat := fun _ value => convertNumber value
  let convert : Unit → Int → Jl Nat := fun _ value => convertNumber value
  let zero : Nat → Jl Nat := JuliaLean.base.number.zeroValue oftype
  let oneType : Unit → Jl Nat := JuliaLean.base.number.oneType convert
  let one : Nat → Jl Nat := JuliaLean.base.number.oneValue (fun _ => ()) oneType
  let greater : Nat → Nat → Jl Bool := fun a b => .ok (decide (a > b))
  let result := if 0 < n then 1 else 0
  JuliaLean.base.number.signUnsigned zero greater one oftype
    JuliaLean.base.int.ifelse n = .ok result ∧
  (result = 0 ↔ n = 0) ∧
  (result = 1 ↔ 0 < n) ∧
  result * n = n

theorem unsignedSignIdentity_proven : UnsignedSignIdentity := by
  intro n
  by_cases hn : n = 0
  · simp [JuliaLean.base.number.signUnsigned,
      JuliaLean.base.number.zeroValue, JuliaLean.base.number.oneType,
      JuliaLean.base.number.oneValue, JuliaLean.base.number.convertNumber,
      JuliaLean.base.int.ifelse, Bind.bind, Except.bind, Pure.pure,
      Except.pure, hn]
  · have hpositive : 0 < n := Nat.pos_of_ne_zero hn
    simp [JuliaLean.base.number.signUnsigned,
      JuliaLean.base.number.zeroValue, JuliaLean.base.number.oneType,
      JuliaLean.base.number.oneValue, JuliaLean.base.number.convertNumber,
      JuliaLean.base.int.ifelse, Bind.bind, Except.bind, Pure.pure,
      Except.pure, hn, hpositive]
/-- Under exact division, the Number inverse fallback returns a multiplicative inverse. -/
def NumberInverseLaw : Prop :=
  ∀ (α γ τ : Type) (x : α) (typeOf : α → τ)
    (constructor : Int → Jl α) (divide : α → α → Jl γ)
    (multiply : γ → α → Jl α) (unit : α) (reciprocal : γ),
  let convert : τ → Int → Jl α :=
    fun _ value => JuliaLean.base.number.convertNumber constructor value
  let oneType : τ → Jl α := JuliaLean.base.number.oneType convert
  let one : α → Jl α := JuliaLean.base.number.oneValue typeOf oneType
  (∀ a b q, divide a b = .ok q → multiply q b = .ok a) →
  one x = .ok unit → divide unit x = .ok reciprocal →
    JuliaLean.base.number.inv one divide x = .ok reciprocal ∧
    multiply reciprocal x = .ok unit

theorem numberInverseLaw_proven : NumberInverseLaw := by
  intro α γ τ x typeOf constructor divide multiply unit reciprocal convert oneType one
    divisionLaw hOne hDivide
  constructor
  · simp [JuliaLean.base.number.inv, hOne, hDivide,
      Bind.bind, Except.bind]
  · exact divisionLaw unit x reciprocal hDivide

/-- `big(T)` has the widened runtime type shared by every widened value of `T`. -/
def BigTypeStable : Prop :=
  ∀ (α β γ δ : Type) (tag : α) (constructor : Int → Jl β)
    (big : β → Jl γ) (typeOf : γ → δ) (zeroValue : β) (bigZero : γ)
    (x : β) (bigX : γ),
  let convert : α → Int → Jl β :=
    fun _ value => JuliaLean.base.number.convertNumber constructor value
  let zero : α → Jl β := JuliaLean.base.number.zeroType convert
  zero tag = .ok zeroValue → big zeroValue = .ok bigZero → big x = .ok bigX →
  typeOf bigZero = typeOf bigX →
    JuliaLean.base.number.bigType zero big typeOf tag = .ok (typeOf bigX)

theorem bigTypeStable_proven : BigTypeStable := by
  intro α β γ δ tag constructor big typeOf zeroValue bigZero x bigX convert zero
    hZero hBigZero hBigX hType
  simp [JuliaLean.base.number.bigType, hZero, hBigZero, hType,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Widened multiplication is exact for every BitInteger width with a wider type. -/
def IntegerWideMulExact : Prop :=
  ∀ t w : IntTy, JuliaLean.base.int.widenType t = some w → ∀ x y : JInt t,
  match JuliaLean.base.number.widemul
    (fun value : JInt t => .ok (JuliaLean.base.int.widenTo w value))
    (fun value : JInt t => .ok (JuliaLean.base.int.widenTo w value))
    (fun a b : JInt w => .ok (JuliaLean.base.int.mul a b)) x y with
  | .ok product => product.val = x.val * y.val
  | .error _ => False

theorem integerWideMulExact_proven : IntegerWideMulExact := by
  intro t w hWiden x y
  have hproduct : JuliaLean.Proofs.base.int.fits w (x.val * y.val) := by
    cases t with
    | i8 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_Int8] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenInt8_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenInt8,
        JuliaLean.Proofs.base.int.WidenSignedHolds, JuliaLean.base.int.widen_Int8] using hwide.2.2
    | i16 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_Int16] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenInt16_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenInt16,
        JuliaLean.Proofs.base.int.WidenSignedHolds, JuliaLean.base.int.widen_Int16] using hwide.2.2
    | i32 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_Int32] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenInt32_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenInt32,
        JuliaLean.Proofs.base.int.WidenSignedHolds, JuliaLean.base.int.widen_Int32] using hwide.2.2
    | i64 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_Int64] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenInt64_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenInt64,
        JuliaLean.Proofs.base.int.WidenSignedHolds, JuliaLean.base.int.widen_Int64] using hwide.2.2
    | i128 => simp_all [JuliaLean.base.int.widenType]
    | u8 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_UInt8] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenUInt8_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenUInt8,
        JuliaLean.Proofs.base.int.WidenUnsignedHolds, JuliaLean.base.int.widen_UInt8] using hwide.2
    | u16 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_UInt16] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenUInt16_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenUInt16,
        JuliaLean.Proofs.base.int.WidenUnsignedHolds, JuliaLean.base.int.widen_UInt16] using hwide.2
    | u32 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_UInt32] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenUInt32_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenUInt32,
        JuliaLean.Proofs.base.int.WidenUnsignedHolds, JuliaLean.base.int.widen_UInt32] using hwide.2
    | u64 =>
      simp [JuliaLean.base.int.widenType, JuliaLean.base.int.widen_UInt64] at hWiden
      subst w
      have hwide := JuliaLean.Proofs.base.int.widenUInt64_proven x y
      simpa [JuliaLean.Proofs.base.int.WidenUInt64,
        JuliaLean.Proofs.base.int.WidenUnsignedHolds, JuliaLean.base.int.widen_UInt64] using hwide.2
    | u128 => simp_all [JuliaLean.base.int.widenType]
  simp only [JuliaLean.base.number.widemul, Bind.bind, Except.bind]
  change (JuliaLean.base.int.mul
    (JuliaLean.base.int.widenTo w x)
    (JuliaLean.base.int.widenTo w y)).val = x.val * y.val
  rw [JuliaLean.base.int.mul, JuliaLean.Proofs.base.int.mul_int_val,
    JuliaLean.Proofs.base.int.widenTo_val, JuliaLean.Proofs.base.int.widenTo_val,
    JuliaLean.Proofs.base.int.wrapInt_mul_left, JuliaLean.Proofs.base.int.wrapInt_mul_right]
  exact wrapInt_of_inRange w _ hproduct

/-- Strict positivity and negativity partition integers around zero; zero has neither sign. -/
def IntegerStrictSigns : Prop := ∀ x : Int,
  (JuliaLean.base.number.signbit
    (fun y : Int => .ok (decide (y < 0))) x = .ok true ↔ x < 0) ∧
  (JuliaLean.base.number.ispositive
    (fun y : Int => .ok (decide (0 < y))) x = .ok true ↔ 0 < x) ∧
  (JuliaLean.base.number.isnegative
    (fun y : Int => .ok (decide (y < 0))) x = .ok true ↔ x < 0) ∧
  ((JuliaLean.base.number.ispositive
      (fun y : Int => .ok (decide (0 < y))) x = .ok false ∧
    JuliaLean.base.number.isnegative
      (fun y : Int => .ok (decide (y < 0))) x = .ok false) ↔ x = 0)

theorem integerStrictSigns_proven : IntegerStrictSigns := by
  intro x
  simp [JuliaLean.base.number.signbit, JuliaLean.base.number.ispositive,
    JuliaLean.base.number.isnegative]
  omega
/-- Both abs2 overloads square integer magnitudes; the Number power callback implements exponent two. -/
def IntegerAbs2Square : Prop := ∀ x : Int,
  let magnitude := if x < 0 then -x else x
  let absolute : Int → Jl Int := fun value =>
    JuliaLean.base.number.absReal
      (fun z : Int => JuliaLean.base.number.signbit
        (fun w : Int => .ok (decide (w < 0))) z)
      (fun z => .ok (-z))
      (fun condition a b => if condition then a else b) value
  JuliaLean.base.number.abs2Real (fun a b : Int => .ok (a * b)) x =
    .ok (magnitude * magnitude) ∧
  ∀ power : Int → Int → Jl Int,
    (∀ value, power value 2 = .ok (value * value)) →
    JuliaLean.base.number.abs2Number absolute power x =
      .ok (magnitude * magnitude)

theorem integerAbs2Square_proven : IntegerAbs2Square := by
  intro x
  by_cases h : x < 0
  · constructor
    · simp [JuliaLean.base.number.abs2Real, h, Int.neg_mul_neg]
    · intro power hpower
      simp [JuliaLean.base.number.abs2Number,
        JuliaLean.base.number.absReal, JuliaLean.base.number.signbit, h, hpower,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Int.neg_mul_neg]
  · constructor
    · simp [JuliaLean.base.number.abs2Real, h]
    · intro power hpower
      simp [JuliaLean.base.number.abs2Number,
        JuliaLean.base.number.absReal, JuliaLean.base.number.signbit, h, hpower,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Real integer sign uses the Number zero/one fallbacks and multiplies the input to its magnitude. -/
def IntegerRealSign : Prop := ∀ x : Int,
  let convert : Int → Int → Jl Int :=
    fun _ value => JuliaLean.base.number.convertNumber
      (fun value => .ok (JuliaLean.base.number.convertSame value)) value
  let zero : Int → Jl Int := JuliaLean.base.number.zeroValue convert
  let oneType : Unit → Jl Int := JuliaLean.base.number.oneType
    (fun _ value => JuliaLean.base.number.convertNumber
      (fun value => .ok (JuliaLean.base.number.convertSame value)) value)
  let one : Int → Jl Int :=
    JuliaLean.base.number.oneValue (fun _ => ()) oneType
  let result := if x < 0 then -1 else if 0 < x then 1 else x
  let magnitude := if x < 0 then -x else x
  JuliaLean.base.number.signReal
    zero
    (fun a b : Int => .ok (decide (a < b)))
    (fun a b : Int => .ok (decide (a > b)))
    one
    convert
    (fun _ value => .ok (JuliaLean.base.number.convertSame value))
    JuliaLean.base.int.ifelse x =
      .ok result ∧
  (result = -1 ↔ x < 0) ∧
  (result = 1 ↔ 0 < x) ∧
  (x = 0 → result = 0) ∧
  result * x = magnitude

theorem integerRealSign_proven : IntegerRealSign := by
  intro x
  by_cases hneg : x < 0
  · simp [JuliaLean.base.number.signReal,
      JuliaLean.base.number.zeroValue, JuliaLean.base.number.oneType,
      JuliaLean.base.number.oneValue, JuliaLean.base.number.convertNumber,
      JuliaLean.base.number.convertSame, JuliaLean.base.int.ifelse, hneg,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Int.neg_one_mul] <;> omega
  · by_cases hpos : 0 < x
    · simp [JuliaLean.base.number.signReal,
        JuliaLean.base.number.zeroValue, JuliaLean.base.number.oneType,
        JuliaLean.base.number.oneValue, JuliaLean.base.number.convertNumber,
        JuliaLean.base.number.convertSame, JuliaLean.base.int.ifelse, hneg, hpos,
        Bind.bind, Except.bind, Pure.pure, Except.pure] <;> omega
    · have hzero : x = 0 := by omega
      simp [JuliaLean.base.number.signReal,
        JuliaLean.base.number.zeroValue, JuliaLean.base.number.oneType,
        JuliaLean.base.number.oneValue, JuliaLean.base.number.convertNumber,
        JuliaLean.base.number.convertSame, JuliaLean.base.int.ifelse, hzero,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

open JuliaLean.Registry

def entries : List Entry := [
  { id := "number-scalar-shape", juliaFile := "base/number.jl"
    juliaFns := ["size(x::Number)", "axes(x::Number)", "eltype(::Type{T})",
      "ndims(x::Number)", "ndims(::Type{<:Number})", "length(x::Number)",
      "firstindex(x::Number)", "lastindex(x::Number)", "IteratorSize(::Type{<:Number})",
      "keys(::Number)"]
    statement := "Numbers have zero-dimensional size and axes, rank zero, and one element; their key axis is OneTo(firstindex), whose length equals the scalar length."
    source := "base/number.jl:86,88,90-94,96,98-99; scalar shape invariant"
    status := .proven, prop := ``ScalarShape, thm := some ``scalarShape_proven },
  { id := "number-scalar-dimensions", juliaFile := "base/number.jl"
    juliaFns := ["size(x::Number,d::Integer)", "axes(x::Number,d::Integer)",
      "firstindex(x::Number,d::Int)", "lastindex(x::Number,d::Int)"]
    statement := "Dimension queries reject d < 1, return singleton size and OneTo(1) for all positive integer dimensions across arbitrary Integer types and every BitInteger width, and agree with firstindex and lastindex on machine Int."
    source := "base/number.jl:87,89,95,97; scalar dimension invariant"
    status := .proven, prop := ``ScalarDimensions, thm := some ``scalarDimensions_proven },
  { id := "number-scalar-collection", juliaFile := "base/number.jl"
    juliaFns := ["getindex(x::Number)", "getindex(x::Number,i::Integer)",
      "getindex(x::Number,I::Integer...)", "get(x::Number,i::Integer,default)",
      "get(x::Number,ind::Tuple,default)", "get(f::Callable,x::Number,i::Integer)",
      "get(f::Callable,x::Number,ind::Tuple)", "first(x::Number)", "last(x::Number)",
      "copy(x::Number)", "iterate(x::Number)", "iterate(x::Number,::Any)",
      "isempty(x::Number)"]
    statement := "A Number acts as a 1-element container: valid scalar or tuple lookups across arbitrary integer, boolean, mixed-tuple, and BitInteger indices return its value, and iteration yields the value once."
    source := "base/number.jl:101-119,329-331; scalar collection invariant"
    status := .proven, prop := ``ScalarCollection, thm := some ``scalarCollection_proven },
  { id := "number-integer-membership", juliaFile := "base/number.jl"
    juliaFns := ["in(x::Number,y::Number)"]
    statement := "Scalar membership agrees with equality against the unique iterated element of a Number, is reflexive and symmetric when equality is, and compares represented integer values across all mixed-width BitInteger pairs."
    source := "base/number.jl:332; membership and equality"
    status := .proven, prop := ``IntegerMembership,
      thm := some ``integerMembership_proven },
  { id := "number-integer-predicates", juliaFile := "base/number.jl"
    juliaFns := ["isinteger(x::Integer)", "isfinite(x::Number)", "iszero(x::Number)",
      "isone(x::Number)"]
    statement := "Across all Number and Integer types (including arbitrary integers, BigInt, and every BitInteger width), isinteger holds on all integers, iszero and isone identify additive and multiplicative identities, and isfinite holds iff x - x is zero."
    source := "base/number.jl:22,44,66,84; integer, zero, one and finite predicates"
    status := .proven, prop := ``IntegerPredicates, thm := some ``integerPredicates_proven },
  { id := "number-integer-strict-signs", juliaFile := "base/number.jl"
    juliaFns := ["signbit(x::Real)", "ispositive(x::Real)", "isnegative(x::Real)"]
    statement := "Integer values have a negative sign bit exactly below zero, are positive exactly above zero, and zero is neither positive nor negative."
    source := "base/number.jl:143,165,187; signbit, ispositive and isnegative"
    status := .proven, prop := ``IntegerStrictSigns, thm := some ``integerStrictSigns_proven },
  { id := "number-integer-magnitude-signs", juliaFile := "base/number.jl"
    juliaFns := ["abs(x::Real)", "flipsign(x::Real,y::Real)", "copysign(x::Real,y::Real)"]
    statement := "Integer absolute values are nonnegative; flipsign follows the second input's sign, and copysign preserves the first input's magnitude while taking the second input's sign."
    source := "base/number.jl:214,255,271; absolute-value and sign-copy methods"
    status := .proven, prop := ``IntegerMagnitudeSigns,
      thm := some ``integerMagnitudeSigns_proven },
  { id := "number-integer-abs2-square", juliaFile := "base/number.jl"
    juliaFns := ["abs2(x::Number)", "abs2(x::Real)"]
    statement := "For integer inputs, abs2Real squares the value; abs2Number returns the square of the magnitude when its power operation squares at exponent two."
    source := "base/number.jl:216-239; abs2 docstring and overloads"
    status := .proven, prop := ``IntegerAbs2Square, thm := some ``integerAbs2Square_proven },
  { id := "number-integer-real-sign", juliaFile := "base/number.jl"
    juliaFns := ["sign(x::Real)"]
    statement := "For every integer, real sign returns -1 below zero, 1 above zero, and zero at zero; multiplying the sign by the input gives its magnitude."
    source := "base/number.jl:211-212; sign docstring and real method"
    status := .proven, prop := ``IntegerRealSign, thm := some ``integerRealSign_proven },
  { id := "number-unsigned-sign-identity", juliaFile := "base/number.jl"
    juliaFns := ["sign(x::Unsigned)"]
    statement := "Unsigned sign is zero at zero and one for positive values, so multiplying it by the input preserves the input."
    source := "base/number.jl:213; unsigned sign method"
    status := .proven, prop := ``UnsignedSignIdentity,
      thm := some ``unsignedSignIdentity_proven },
  { id := "number-number-sign-magnitude", juliaFile := "base/number.jl"
    juliaFns := ["sign(x::Number)"]
    statement := "If every successful division quotient times its denominator recovers its numerator, each successful Number sign result times the magnitude selected by the actual zero and oneunit fallbacks recovers the input."
    source := "base/number.jl:211; Number sign fallback"
    status := .proven, prop := ``NumberSignMagnitude, thm := some ``numberSignMagnitude_proven },
  { id := "number-inverse-law", juliaFile := "base/number.jl"
    juliaFns := ["inv(x::Number)"]
    statement := "When successful division quotients multiply back to their numerators, inv(x) returns one(x)/x and that quotient multiplies by x to one(x)."
    source := "base/number.jl:305; inverse fallback"
    status := .proven, prop := ``NumberInverseLaw, thm := some ``numberInverseLaw_proven },
  { id := "number-bitinteger-widemul-exact", juliaFile := "base/number.jl"
    juliaFns := ["widemul(x::Number,y::Number)"]
    statement := "For every signed or unsigned BitInteger width below 128 bits, widemul returns the exact product when a wider type exists."
    source := "base/number.jl:327; widemul docstring"
    status := .proven, prop := ``IntegerWideMulExact,
      thm := some ``integerWideMulExact_proven },
  { id := "number-integer-zero-one-units", juliaFile := "base/number.jl"
    juliaFns := ["zero(x::Number)", "zero(::Type{T})", "one(::Type{T})", "one(x::T)",
      "oneunit(x::T)", "oneunit(::Type{T})"]
    statement := "Across all Number types (and concretely on every BitInteger width and Int), zero, one, and oneunit agree between value and type overloads, oneunit coincides with one under identity self-conversion, and zero/one/oneunit yield additive and multiplicative identities."
    source := "base/number.jl:363-364,405-406,430-431; zero, one and oneunit"
    status := .proven, prop := ``IntegerZeroOneUnits,
      thm := some ``integerZeroOneUnits_proven },
  { id := "number-big-type-stability", juliaFile := "base/number.jl"
    juliaFns := ["big(::Type{T})"]
    statement := "When widening preserves a type across values, big(T) returns that widened runtime type."
    source := "base/number.jl:452; type-level big method"
    status := .proven, prop := ``BigTypeStable, thm := some ``bigTypeStable_proven }
]

/-! Nothing to promise:
convertSame@6 (`convert(::Type{T},x::T)`): identical-type conversion returns its input.
convertNumber@7 (`convert(::Type{T},x::Number)`): delegates conversion to the target type's constructor.
angle@276 (`angle(z::Real)`): forwards to atan(zero(z),z).
map@334 (`map(f,x::Number,ys::Number...)`): forwards the scalar and tuple of arguments to f.
zeroBottom@365 (`zero(::Type{Union{}},slurp...)`): delegates construction to the uninhabited target type.
oneBottom@407 (`one(::Type{Union{}},slurp...)`): delegates construction to the uninhabited target type.
oneunitBottom@432 (`oneunit(::Type{Union{}},slurp...)`): delegates construction to the uninhabited target type.
bigBottom@453 (`big(::Type{Union{}},slurp...)`): delegates construction to the uninhabited target type.
conj@273 (`conj(x::Real)`): forwards the real value unchanged.
transpose@274 (`transpose(x::Number)`): forwards the number unchanged.
adjoint@275 (`adjoint(x::Number)`): forwards to `conj(x)`.
-/

end JuliaLean.Proofs.base.number
