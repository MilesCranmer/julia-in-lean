import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.Proofs.base.int
import JuliaLean.base.ntuple
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.ntuple

open JuliaLean JuliaLean.base.int JuliaLean.base.ntuple JuliaLean.Registry

abbrev I64 := JuliaLean.base.ntuple.I64
abbrev TupleField := JuliaLean.base.ntuple.TupleField
abbrev TupleValue := JuliaLean.base.ntuple.TupleValue
abbrev NtupleResult (α : Type u) := JuliaLean.base.ntuple.NtupleResult α

abbrev Lifted (α : Type) := ULift.{1,0} α
abbrev LiftedResult (α : Type) := NtupleResult.{1} (Lifted α)

def indicesFromOne (n : I64) : List I64 :=
  (List.range n.val.toNat).map fun k => lit .i64 (Int.ofNat (k + 1))

def OneToLaw (oneTo : I64 → LiftedResult (List I64)) : Prop :=
  ∀ n, 0 ≤ n.val → oneTo n = .ok (.up (indicesFromOne n))

def GeneratedNtupleLaw
    (generatedNtuple : I64 → (I64 → NtupleResult TupleField) → NtupleResult TupleValue) : Prop :=
  ∀ n f, 0 ≤ n.val → generatedNtuple n f = List.mapM f (indicesFromOne n)

/-- Integer-length `ntuple` preserves the documented order and negative-length error. -/
def NtupleIntSpec : Prop :=
  ∀ f n oneTo, OneToLaw oneTo →
    ntupleInt f n oneTo =
      if n.val < 0 then
        .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString n.val)))
      else List.mapM f (indicesFromOne n)

/-- The generic `Integer` overload converts to `Int` before constructing the tuple. -/
def NtupleIntegerSpec : Prop :=
  ∀ {I : Type} (f : I64 → NtupleResult TupleField) (convertInt : I → Jl I64)
    (n : I) (oneTo : I64 → LiftedResult (List I64)),
    OneToLaw oneTo →
      ntupleInteger f convertInt n oneTo =
        match convertInt n with
        | .error e => .error (.base e)
        | .ok size =>
            if size.val < 0 then
              .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString size.val)))
            else List.mapM f (indicesFromOne size)

/-- `Val{N}` rejects non-`Int` type parameters and negative lengths, otherwise it visits 1:N. -/
def NtupleValSpec : Prop :=
  ∀ {N : Type} (f : I64 → NtupleResult TupleField) (n : N)
    (assertInt : N → LiftedResult I64) (generated : Bool)
    (generatedNtuple : I64 → (I64 → NtupleResult TupleField) → NtupleResult TupleValue)
    (oneTo : I64 → LiftedResult (List I64)),
    OneToLaw oneTo → GeneratedNtupleLaw generatedNtuple →
      ntupleVal f n assertInt generated generatedNtuple oneTo =
        match assertInt n with
        | .error e => .error e
        | .ok sizeLift =>
            let size := sizeLift.down
            if size.val < 0 then
              .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString size.val)))
            else List.mapM f (indicesFromOne size)

def NtupleBitIntegerSpec : Prop :=
  ∀ {t : IntTy} (f : I64 → NtupleResult TupleField) (n : JInt t)
    (oneTo : I64 → LiftedResult (List I64)),
    OneToLaw oneTo →
      ntupleInteger f (JuliaLean.base.int.convert .i64) n oneTo =
        match JuliaLean.base.int.convert .i64 n with
        | .error e => .error (.base e)
        | .ok size =>
            if size.val < 0 then
              .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString size.val)))
            else List.mapM f (indicesFromOne size)

def NtupleBitIntegerInexactSpec : Prop :=
  ∀ {t : IntTy} (f : I64 → NtupleResult TupleField) (n : JInt t)
    (oneTo : I64 → LiftedResult (List I64)),
    (n.val < IntTy.i64.min ∨ IntTy.i64.max < n.val) →
      ∃ message, ntupleInteger f (JuliaLean.base.int.convert .i64) n oneTo =
        .error (.base (.inexactError message))

def NtupleSpec : Prop :=
  NtupleIntSpec ∧ NtupleIntegerSpec ∧ NtupleValSpec ∧
    NtupleBitIntegerSpec ∧ NtupleBitIntegerInexactSpec

/-- `ntupleany` preserves ordered traversal for generic inputs and agrees with `ntuple` on Int lengths. -/
def NtupleAnyGenericSpec : Prop :=
  ∀ {N I : Type} (f : I → NtupleResult TupleField) (n : N)
    (isNonnegative : N → LiftedResult Bool)
    (oneTo : N → LiftedResult (List I)) (showValue : N → String),
    (∀ indices, isNonnegative n = .ok (.up true) →
      oneTo n = .ok (.up indices) →
      ntupleAny f n isNonnegative oneTo showValue = List.mapM f indices) ∧
    (isNonnegative n = .ok (.up false) →
      ntupleAny f n isNonnegative oneTo showValue =
        .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ showValue n))))

def NtupleAnyIntAgreementSpec : Prop :=
  ∀ (f : I64 → NtupleResult TupleField) (n : I64)
    (oneTo : I64 → LiftedResult (List I64)),
    OneToLaw oneTo →
      ntupleAny f n (fun x => .ok (.up (decide (0 ≤ x.val)))) oneTo
        (fun x => toString x.val) = ntupleInt f n oneTo

def NtupleAnySpec : Prop :=
  NtupleAnyGenericSpec ∧ NtupleIntSpec ∧ NtupleAnyIntAgreementSpec

def TupleLengthLaw (length : TupleValue → LiftedResult I64) : Prop :=
  ∀ t, length t = .ok (.up (lit .i64 (Int.ofNat t.length)))

def FillLaw (fill : TupleField → I64 → NtupleResult TupleValue) : Prop :=
  ∀ val n, 0 ≤ n.val → fill val n = .ok (List.replicate n.val.toNat val)

/-- `fill_to_length` preserves the input prefix, pads to N, and rejects shorter requests. -/
def FillToLengthSpec : Prop :=
  ∀ (t : TupleValue) (val : TupleField) {N : Type} (n : N)
    (length : TupleValue → LiftedResult I64)
    (assertInt : N → LiftedResult I64)
    (fill : TupleField → I64 → NtupleResult TupleValue) (generated : Bool),
    Int.ofNat t.length ≤ IntTy.i64.max →
    TupleLengthLaw length → FillLaw fill →
      fillToLength t val n length assertInt fill generated =
        match length t with
        | .error e => .error e
        | .ok lengthLift =>
            let m := lengthLift.down
            match assertInt n with
            | .error e => .error e
            | .ok requestedLift =>
                let requested := requestedLift.down
                if m.val > requested.val then
                  .error (.base (.argumentError ("input tuple of length " ++ toString m.val ++
                    ", requested " ++ toString requested.val)))
                else
                  .ok (t ++ List.replicate (sub_int requested m).val.toNat val)

def tupleIndexOutcome {α : Type} (t : List α) (i : I64) : LiftedResult α :=
  if i.val < 1 ∨ (Int.ofNat t.length) < i.val then
    .error (.base .boundsError)
  else
    match (t[i.val.toNat - 1]?) with
    | some value => .ok (.up value)
    | none => .error (.base .boundsError)

private theorem reverseIndexValue {α : Type} (t : List α) (n : I64)
    (endIndex : List α → I64) (k : Nat)
    (hn : n.val = Int.ofNat t.length)
    (hend : endIndex t = lit .i64 (Int.ofNat t.length))
    (hk : k < t.length) :
    (sub_int (add_int (endIndex t) (lit .i64 1))
      (lit .i64 (Int.ofNat (k + 1)))).val = Int.ofNat (t.length - k) := by
  have hfitsLength : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat t.length) := by
    unfold JuliaLean.Proofs.base.int.fits
    simpa [hn] using n.property
  have hmin : IntTy.i64.min ≤ 0 := by decide
  have hOneFits : JuliaLean.Proofs.base.int.fits .i64 1 := by
    unfold JuliaLean.Proofs.base.int.fits
    exact ⟨Int.le_trans hmin (by decide), by decide⟩
  have hPositionFits : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat (k + 1)) := by
    unfold JuliaLean.Proofs.base.int.fits
    constructor
    · exact Int.le_trans hmin (Int.natCast_nonneg _)
    · have hle : Int.ofNat (k + 1) ≤ Int.ofNat t.length :=
        Int.ofNat_le.mpr (Nat.succ_le_of_lt hk)
      exact Int.le_trans hle hfitsLength.2
  have hDifferenceFits : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat (t.length - k)) := by
    unfold JuliaLean.Proofs.base.int.fits
    constructor
    · exact Int.le_trans hmin (Int.natCast_nonneg _)
    · have hle : Int.ofNat (t.length - k) ≤ Int.ofNat t.length :=
        Int.ofNat_le.mpr (Nat.sub_le _ _)
      exact Int.le_trans hle hfitsLength.2
  rw [JuliaLean.Proofs.base.int.sub_int_val, JuliaLean.Proofs.base.int.add_int_val, hend,
    JuliaLean.Proofs.base.int.lit_of_fits hfitsLength,
    JuliaLean.Proofs.base.int.lit_of_fits hOneFits,
    JuliaLean.Proofs.base.int.lit_of_fits hPositionFits,
    JuliaLean.Proofs.base.int.wrapInt_sub_left]
  have hNat : t.length + 1 - (k + 1) = t.length - k := by omega
  have hsum : Int.ofNat t.length + 1 = Int.ofNat (t.length + 1) := by simp
  have hsub : Int.ofNat (t.length + 1 - (k + 1)) =
      Int.ofNat (t.length + 1) - Int.ofNat (k + 1) := Int.ofNat_sub (by omega)
  have harithmetic : Int.ofNat t.length + 1 - Int.ofNat (k + 1) =
      Int.ofNat (t.length - k) := by
    calc
      Int.ofNat t.length + 1 - Int.ofNat (k + 1) =
          Int.ofNat (t.length + 1) - Int.ofNat (k + 1) := by rw [hsum]
      _ = Int.ofNat (t.length + 1 - (k + 1)) := hsub.symm
      _ = Int.ofNat (t.length - k) := by rw [hNat]
  rw [harithmetic, wrapInt_of_inRange .i64 _ hDifferenceFits]

private theorem tupleIndexOutcome_reverse {α : Type} (t : List α) (k : Nat)
    (hk : k < t.length)
    (hfitsLength : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat t.length)) :
    tupleIndexOutcome t (lit .i64 (Int.ofNat (t.length - k))) =
      .ok (.up (t.reverse[k]'(by simpa [List.length_reverse] using hk))) := by
  have hmin : IntTy.i64.min ≤ 0 := by decide
  have hNatLower : 1 ≤ t.length - k := by omega
  have hNatUpper : t.length - k ≤ t.length := Nat.sub_le _ _
  have hfitsIndex : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat (t.length - k)) := by
    unfold JuliaLean.Proofs.base.int.fits
    exact ⟨Int.le_trans hmin (Int.natCast_nonneg _),
      Int.le_trans (Int.ofNat_le.mpr hNatUpper) hfitsLength.2⟩
  have hindex := JuliaLean.Proofs.base.int.lit_of_fits hfitsIndex
  have hnat : (Int.ofNat (t.length - k)).toNat - 1 = t.length - 1 - k := by
    change t.length - k - 1 = t.length - 1 - k
    omega
  have hkReverse : k < t.reverse.length := by simpa [List.length_reverse] using hk
  have hget : t[(Int.ofNat (t.length - k)).toNat - 1]? =
      some (t.reverse[k]'hkReverse) := by
    rw [hnat, ← List.getElem?_eq_getElem hkReverse, List.getElem?_reverse hk]
  unfold tupleIndexOutcome
  have hposition : ¬ (Int.ofNat (t.length - k) < 1 ∨
      Int.ofNat t.length < Int.ofNat (t.length - k)) := by
    have hLower : 1 ≤ Int.ofNat (t.length - k) := Int.ofNat_le.mpr hNatLower
    have hUpper : Int.ofNat (t.length - k) ≤ Int.ofNat t.length :=
      Int.ofNat_le.mpr hNatUpper
    omega
  rw [hindex, if_neg hposition, hget]

private theorem reverseMapRangePrefix {α : Type}
    (step : I64 → NtupleResult TupleField) (reversed : List α)
    (hstep : ∀ k (hk : k < reversed.length),
      step (lit .i64 (Int.ofNat (k + 1))) =
        .ok (⟨α, reversed[k]'hk⟩ : TupleField)) :
    ∀ k, k ≤ reversed.length →
      List.mapM step ((List.range k).map (fun j => lit .i64 (Int.ofNat (j + 1)))) =
        .ok ((reversed.take k).map fun x => (⟨α, x⟩ : TupleField)) := by
  intro k hk
  induction k with
  | zero => change Except.ok [] = Except.ok []; rfl
  | succ k ih =>
      have hklt : k < reversed.length := by omega
      have hprev := ih (by omega)
      rw [List.range_succ, List.map_append, List.map_singleton, List.mapM_append, hprev]
      rw [List.take_succ_eq_append_getElem hklt]
      simp only [List.mapM_cons, List.mapM_nil, hstep k hklt, Bind.bind, Except.bind,
        Pure.pure, Except.pure, List.map_append, List.map_singleton]

/-- The `NTuple` method uses the documented one-based index operation and preserves its type. -/
def NtupleReverseSpec : Prop :=
  ∀ {α : Type} (t : List α) (n : I64)
    (oneTo : I64 → LiftedResult (List I64)) (generated : Bool)
    (generatedNtuple : I64 → (I64 → NtupleResult TupleField) → NtupleResult TupleValue)
    (endIndex : List α → I64)
    (getindex : List α → I64 → LiftedResult α)
    (asNTuple : TupleValue → LiftedResult (List α)),
    n.val = Int.ofNat t.length →
    OneToLaw oneTo → GeneratedNtupleLaw generatedNtuple →
    endIndex t = lit .i64 (Int.ofNat t.length) →
    (∀ i, getindex t i = tupleIndexOutcome t i) →
    (∀ xs : List α,
      asNTuple (xs.map fun x => (⟨α, x⟩ : TupleField)) = .ok (.up xs)) →
      reverseNTuple t n oneTo generated generatedNtuple endIndex getindex asNTuple =
        .ok (.up t.reverse)


theorem ntupleInt_spec_proven : NtupleIntSpec := by
  intro f n oneTo oneToLaw
  by_cases hneg : n.val < 0
  · have hnonneg : ¬ 0 ≤ n.val := by omega
    have h0 : n.val ≠ 0 := by omega
    have h1 : n.val ≠ 1 := by omega
    have h2 : n.val ≠ 2 := by omega
    have h3 : n.val ≠ 3 := by omega
    have h4 : n.val ≠ 4 := by omega
    have h5 : n.val ≠ 5 := by omega
    have h6 : n.val ≠ 6 := by omega
    have h7 : n.val ≠ 7 := by omega
    have h8 : n.val ≠ 8 := by omega
    have h9 : n.val ≠ 9 := by omega
    have h10 : n.val ≠ 10 := by omega
    simp [ntupleInt, _ntuple, hneg, hnonneg, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · have hnonneg : 0 ≤ n.val := by omega
    by_cases hlarge : 10 < n.val
    · have h0 : n.val ≠ 0 := by omega
      have h1 : n.val ≠ 1 := by omega
      have h2 : n.val ≠ 2 := by omega
      have h3 : n.val ≠ 3 := by omega
      have h4 : n.val ≠ 4 := by omega
      have h5 : n.val ≠ 5 := by omega
      have h6 : n.val ≠ 6 := by omega
      have h7 : n.val ≠ 7 := by omega
      have h8 : n.val ≠ 8 := by omega
      have h9 : n.val ≠ 9 := by omega
      have h10 : n.val ≠ 10 := by omega
      have hOne := oneToLaw n hnonneg
      simp [ntupleInt, _ntuple, indicesFromOne, hneg, hlarge, hOne, h0, h1, h2, h3,
        h4, h5, h6, h7, h8, h9, h10, hnonneg]
    · have hcases : n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨
        n.val = 4 ∨ n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨
        n.val = 9 ∨ n.val = 10 := by omega
      rcases hcases with h | h | h | h | h | h | h | h | h | h | h
      all_goals simp [ntupleInt, indicesFromOne, h, hneg, hnonneg, List.range_succ,
        Pure.pure, Except.pure] <;> rfl
theorem ntupleAnyGeneric_spec_proven : NtupleAnyGenericSpec := by
  intro N I f n isNonnegative oneTo showValue
  constructor
  · intro indices hnonnegative hindices
    simp [ntupleAny, hnonnegative, hindices, Bind.bind, Except.bind]
  · intro hnegative
    simp [ntupleAny, hnegative, Bind.bind, Except.bind]

theorem ntupleAnyIntAgreement_spec_proven : NtupleAnyIntAgreementSpec := by
  intro f n oneTo oneToLaw
  have anyResult :
      ntupleAny f n (fun x => .ok (.up (decide (0 ≤ x.val)))) oneTo
        (fun x => toString x.val) =
        if n.val < 0 then
          .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString n.val)))
        else List.mapM f (indicesFromOne n) := by
    by_cases hnegative : n.val < 0
    · have hnonnegative : ¬ 0 ≤ n.val := by omega
      simp [ntupleAny, hnegative, hnonnegative, Bind.bind, Except.bind]
    · have hnonnegative : 0 ≤ n.val := by omega
      have hOne := oneToLaw n hnonnegative
      simp [ntupleAny, hnegative, hnonnegative, hOne, Bind.bind, Except.bind]
  rw [anyResult, ntupleInt_spec_proven f n oneTo oneToLaw]

theorem ntupleAny_spec_proven : NtupleAnySpec :=
  ⟨ntupleAnyGeneric_spec_proven, ntupleInt_spec_proven,
    ntupleAnyIntAgreement_spec_proven⟩

theorem ntupleInteger_spec_proven : NtupleIntegerSpec := by
  intro I f convertInt n oneTo oneToLaw
  cases hconvert : convertInt n with
  | error e => simp [ntupleInteger, hconvert]
  | ok size =>
      simpa [ntupleInteger, hconvert] using
        ntupleInt_spec_proven f size oneTo oneToLaw

theorem ntupleVal_spec_proven : NtupleValSpec := by
  intro N f n assertInt generated generatedNtuple oneTo oneToLaw generatedLaw
  cases hassert : assertInt n with
  | error e => simp [ntupleVal, hassert, Bind.bind, Except.bind]
  | ok sizeLift =>
      by_cases hn : 0 ≤ sizeLift.down.val
      · have hnegative : ¬ sizeLift.down.val < 0 := by omega
        have hOne := oneToLaw sizeLift.down hn
        have hGenerated := generatedLaw sizeLift.down f hn
        cases generated
        · simp [ntupleVal, hassert, hn, hnegative, hOne, Bind.bind, Except.bind]
        · simp [ntupleVal, hassert, hn, hnegative, hGenerated, Bind.bind, Except.bind]
      · have hnegative : sizeLift.down.val < 0 := by omega
        simp [ntupleVal, hassert, hn, hnegative, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem ntupleReverse_spec_proven : NtupleReverseSpec := by
  intro α t n oneTo generated generatedNtuple endIndex getindex asNTuple hn hOne hGenerated hEnd hGet hAs
  have hfitsLength : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat t.length) := by
    unfold JuliaLean.Proofs.base.int.fits
    simpa [hn] using n.property
  let step : I64 → NtupleResult TupleField := fun i => do
    let last := endIndex t
    let endPlusOne := add_int last (lit .i64 1)
    let index := sub_int endPlusOne i
    let value ← getindex t index
    pure ⟨α, value.down⟩
  have hstep : ∀ k (hk : k < t.reverse.length),
      step (lit .i64 (Int.ofNat (k + 1))) =
        .ok (⟨α, t.reverse[k]'hk⟩ : TupleField) := by
    intro k hk
    have hk' : k < t.length := by simpa using hk
    have hindexValue := reverseIndexValue t n endIndex k hn hEnd hk'
    have hfitsIndex : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat (t.length - k)) := by
      unfold JuliaLean.Proofs.base.int.fits
      constructor
      · exact Int.le_trans (by decide : IntTy.i64.min ≤ 0) (Int.natCast_nonneg _)
      · exact Int.le_trans (Int.ofNat_le.mpr (Nat.sub_le _ _)) hfitsLength.2
    have hindex : sub_int (add_int (endIndex t) (lit .i64 1))
        (lit .i64 (Int.ofNat (k + 1))) = lit .i64 (Int.ofNat (t.length - k)) := by
      apply JuliaLean.Proofs.base.int.jint_eq
      rw [hindexValue, JuliaLean.Proofs.base.int.lit_of_fits hfitsIndex]
    have hgetResult :
        getindex t (sub_int (add_int (endIndex t) (lit .i64 1))
          (lit .i64 (Int.ofNat (k + 1)))) =
          .ok (.up (t.reverse[k]'hk)) := by
      rw [hGet, hindex, tupleIndexOutcome_reverse t k hk' hfitsLength]
    have hcast : (↑k + 1 : Int) = Int.ofNat (k + 1) := by simp
    dsimp [step]
    rw [hcast, hgetResult]
    rfl
  have hprefix := reverseMapRangePrefix step t.reverse hstep t.length (by simp)
  have hnNat : n.val.toNat = t.length := by rw [hn]; simp
  have hmap : List.mapM step (indicesFromOne n) =
      .ok ((t.reverse).map fun x => (⟨α, x⟩ : TupleField)) := by
    have htake : t.reverse.take t.length = t.reverse := List.take_of_length_le (by simp)
    simpa [indicesFromOne, hnNat, htake] using hprefix
  have hnnegative : ¬ n.val < 0 := by
    rw [hn]
    have hlenNonneg : 0 ≤ Int.ofNat t.length := Int.natCast_nonneg _
    omega
  have hvalueSpec := ntupleVal_spec_proven step n (fun size => .ok (.up size))
    generated generatedNtuple oneTo hOne hGenerated
  have hvalue : ntupleVal step n (fun size => .ok (.up size))
      generated generatedNtuple oneTo = List.mapM step (indicesFromOne n) := by
    simpa [hnnegative, Bind.bind, Except.bind] using hvalueSpec
  change (ntupleVal step n (fun size => .ok (.up size))
      generated generatedNtuple oneTo >>= asNTuple) = .ok (.up t.reverse)
  rw [hvalue, hmap]
  simpa [Bind.bind, Except.bind] using hAs t.reverse
theorem ntupleBitInteger_spec_proven : NtupleBitIntegerSpec := by
  intro t f n oneTo oneToLaw
  exact ntupleInteger_spec_proven f (JuliaLean.base.int.convert .i64) n oneTo oneToLaw

theorem ntupleBitIntegerInexact_spec_proven : NtupleBitIntegerInexactSpec := by
  intro t f n oneTo houtside
  have hbad : ¬ (IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max) := by omega
  refine ⟨IntTy.i64.name, ?_⟩
  simp [ntupleInteger, JuliaLean.base.int.convert, JInt.convert, hbad]

theorem ntuple_spec_proven : NtupleSpec :=
  ⟨ntupleInt_spec_proven, ntupleInteger_spec_proven, ntupleVal_spec_proven,
    ntupleBitInteger_spec_proven, ntupleBitIntegerInexact_spec_proven⟩

theorem fillToLength_spec_proven : FillToLengthSpec := by
  intro t val N n length assertInt fill generated hfits lengthLaw fillLaw
  cases hLength : length t with
  | error e => simp [fillToLength, hLength, Bind.bind, Except.bind]
  | ok lengthLift =>
      cases hAssert : assertInt n with
      | error e => simp [fillToLength, hLength, hAssert, Bind.bind, Except.bind]
      | ok requestedLift =>
          let m := lengthLift.down
          let requested := requestedLift.down
          have hLengthLaw := lengthLaw t
          rw [hLength] at hLengthLaw
          have hLengthValue : m = lit .i64 (Int.ofNat t.length) := by
            have hLift : lengthLift = .up (lit .i64 (Int.ofNat t.length)) := by
              injection hLengthLaw
            simpa [m] using congrArg ULift.down hLift
          have hfitsLength : JuliaLean.Proofs.base.int.fits .i64 (Int.ofNat t.length) := by
            unfold JuliaLean.Proofs.base.int.fits
            constructor
            · simp [IntTy.min, IntTy.signed, IntTy.bits]
            · exact hfits
          have hmval : m.val = Int.ofNat t.length := by
            rw [hLengthValue]
            exact JuliaLean.Proofs.base.int.lit_of_fits hfitsLength
          by_cases htooLong : m.val > requested.val
          · have hlengthTooLong :
                requestedLift.down.val < lengthLift.down.val := by
              simpa [m, requested] using htooLong
            simp [fillToLength, hLength, hAssert, hmval, hlengthTooLong,
              Bind.bind, Except.bind]
          · have hle : m.val ≤ requested.val := by omega
            have hmnonnegative : 0 ≤ m.val := by rw [hmval]; exact Int.ofNat_nonneg _
            have hrequestedMin : IntTy.i64.min ≤ requested.val := requested.property.1
            have hrequestedMax : requested.val ≤ IntTy.i64.max := requested.property.2
            have hmin : IntTy.i64.min ≤ 0 := by decide
            have hrange : IntTy.i64.min ≤ requested.val - m.val ∧
                requested.val - m.val ≤ IntTy.i64.max := by
              constructor <;> omega
            have hsub : (sub_int requested m).val = requested.val - m.val := by
              rw [JuliaLean.Proofs.base.int.sub_int_val]
              exact wrapInt_of_inRange .i64 _ hrange
            have hsubNonnegative : 0 ≤ (sub_int requested m).val := by rw [hsub]; omega
            have hfill := fillLaw val (sub_int requested m) hsubNonnegative
            have hnotLength : ¬ requestedLift.down.val < lengthLift.down.val := by
              simpa [m, requested] using htooLong
            have hfillOrdinary :
                fill val (sub_int requestedLift.down lengthLift.down) =
                  .ok (List.replicate (sub_int requestedLift.down lengthLift.down).val.toNat val) := by
              simpa [m, requested] using hfill
            have hfillGenerated :
                fill val (sub_int requestedLift.down (lit .i64 (Int.ofNat t.length))) =
                  .ok (List.replicate
                    (sub_int requestedLift.down (lit .i64 (Int.ofNat t.length))).val.toNat val) := by
              simpa [m, requested, hLengthValue] using hfill
            cases generated
            · simp only [fillToLength, Bind.bind, Except.bind, hLength, hAssert, hnotLength]
              rw [hfillOrdinary]
              simp [Pure.pure, Except.pure]
            · simp only [fillToLength, Bind.bind, Except.bind, hLength, hAssert, hnotLength]
              rw [hfillGenerated]
              simp [m, hLengthValue, Pure.pure, Except.pure]

/-! Registry entries. -/
def entries : List Entry := [
  { id := "tuples-ntuple", juliaFile := "base/ntuple.jl"
    juliaFns := ["ntuple(f, n::Int)", "ntuple(f, n::Integer)", "ntuple(f, ::Val{N})", "_ntuple"]
    statement := "Integer-length and Val forms call f on every one-based position in order; negative lengths throw ArgumentError, Integer conversion throws InexactError when n does not fit Int, and Val requires an Int length."
    source := "base/ntuple.jl:5-16,36-40,48-72"
    status := .proven, prop := ``NtupleSpec, thm := some ``ntuple_spec_proven },
  { id := "tuples-fill-to-length", juliaFile := "base/ntuple.jl"
    juliaFns := ["fill_to_length(t, val, ::Val{N})"]
    statement := "fill_to_length preserves the input tuple as a prefix, repeats val until the requested length, and throws ArgumentError when the input is longer."
    source := "base/ntuple.jl:74-85; tuple length and padding invariants"
    status := .proven, prop := ``FillToLengthSpec, thm := some ``fillToLength_spec_proven },
  { id := "sorttuplescov-ntuple-any", juliaFile := "base/ntuple.jl"
    juliaFns := ["ntupleany(f, n)", "ntuple(f, n::Int)"]
    statement := "ntupleany applies f to the values in 1:n in order, rejects negative lengths, and agrees with ntuple(f,n::Int) for every Int length."
    source := "base/ntuple.jl:17-46"
    status := .proven, prop := ``NtupleAnySpec, thm := some ``ntupleAny_spec_proven },
  { id := "sorttuplescov-ntuple-reverse", juliaFile := "base/ntuple.jl"
    juliaFns := ["reverse(t::NTuple{N})"]
    statement := "For every homogeneous tuple, reverse returns the elements in reverse order and preserves the NTuple element type."
    source := "base/ntuple.jl:89-93; reverse invariant"
    status := .proven, prop := ``NtupleReverseSpec, thm := some ``ntupleReverse_spec_proven }
]

end JuliaLean.Proofs.base.ntuple
