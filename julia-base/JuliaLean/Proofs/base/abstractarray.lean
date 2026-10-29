import JuliaLean.base.abstractarray
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.array

/-!
# Properties of `base/abstractarray.jl`

Specifications refer to the typed source mirrors. Callee laws below are the
contracts of tuple indexing, array axes, and integer conversion.
-/

namespace JuliaLean.Proofs.base.abstractarray

open JuliaLean JuliaLean.base.abstractarray

attribute [local simp] pure Except.pure bind Except.bind throw throwThe

local instance resultDecidableEq {α : Type} [DecidableEq α] : DecidableEq (Result α) :=
  fun a b => by
    cases a with
    | error e =>
      cases b with
      | error f => exact decidable_of_iff (e = f) (by simp)
      | ok x => exact isFalse (by intro h; cases h)
    | ok x =>
      cases b with
      | error f => exact isFalse (by intro h; cases h)
      | ok y => exact decidable_of_iff (x = y) (by simp)


/-! ## Concrete interface instances and independent specifications -/

/-- Conventional axis vocabulary: first index and number of indices. -/
def oneBasedAxis (n : I64) : I64 × Nat := (int 1, n.val.toNat)

/-- The rank equals the number of stored dimensions; valid dimensions select
that dimension, trailing dimensions are singleton, and nonpositive indices fail. -/
def SizeAxesDim : Prop :=
  let size := sizeDim (fun x : I64 => pure x) (fun xs : List I64 => pure xs)
  let axes := fun sizes n d => axesDim (fun d n : I64 => decide (d.val ≤ n.val))
    (fun xs : List I64 => pure (xs.map oneBasedAxis)) tupleGet oneBasedAxis n sizes d
  ∀ (sizes : List I64) (n d : I64), n.val = sizes.length →
    (d.val < 1 → size sizes d = .error (.julia .boundsError) ∧
      axes sizes n d = .error (.julia .boundsError)) ∧
    (∀ (k : Nat) (hk : k < sizes.length), d.val = (k : Int) + 1 →
      size sizes d = .ok sizes[k] ∧ axes sizes n d = .ok (oneBasedAxis sizes[k])) ∧
    ((sizes.length : Int) < d.val → size sizes d = .ok (int 1) ∧
      axes sizes n d = .ok (oneBasedAxis (int 1)))

theorem sizeAxesDim_proven : SizeAxesDim := by
  intro sizes n d hn
  constructor
  · intro hd
    have hle : d.val ≤ (sizes.length : Int) := by omega
    simp [sizeDim, axesDim, tupleGet, hn, hd, hle]
  constructor
  · intro k hk hd
    have hle : d.val ≤ (sizes.length : Int) := by omega
    have hpos : ¬ d.val < 1 := by omega
    have hi : (d.val - 1).toNat = k := by omega
    simp [sizeDim, axesDim, tupleGet, hn, hle, hpos, hi, hk]
  · intro hd
    have hle : ¬ d.val ≤ (sizes.length : Int) := by omega
    simp [sizeDim, axesDim, hn, hle]

def SizeAllIntegerDims : Prop := ∀ (sizes : List I64) (t : IntTy) (d : JInt t),
  (sizes.length : Int) < d.val →
    sizeDim (fun x : JInt t => liftJulia (JInt.convert .i64 x.val))
      (fun xs : List I64 => pure xs) sizes d = .ok (int 1)

theorem sizeAllIntegerDims_refuted : ¬ SizeAllIntegerDims := by
  intro h
  have bad := h [] .u64 (JInt.lit .u64 (2^63)) (by decide)
  revert bad
  decide

theorem anyTupleM_pure (p : α → Bool) (xs : List α) :
    anyTupleM (fun x => pure (p x)) false xs = .ok (xs.any p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ih' : anyTupleM (fun x => Except.ok (p x)) false xs = .ok (xs.any p) := ih
    cases hx : p x <;> simp [anyTupleM, hx, ih', List.any_cons]

/-- The interface instance uses Int-valued axis starts, as permitted by the
AbstractArray interface. Axis lengths do not affect one-basedness. -/
def offsetAxes (starts : List I64) : Result Bool :=
  hasOffset (fun xs : List I64 => pure xs) (fun x : I64 => pure x)
    (fun x : I64 => pure x) starts

def offsetArrayTuple : List (List I64) → Result Bool
  | [] => pure hasOffsetNone
  | axes :: rest => hasOffsetMany offsetAxes (fun _ : Unit => offsetArrayTuple rest) axes ()
def requireAxes (starts : List I64) : Result Bool :=
  requireOneBased offsetArrayTuple [starts]

theorem offsetAxes_eq (starts : List I64) :
    offsetAxes starts = .ok (starts.any (fun i => i.val != 1)) := by
  simpa [offsetAxes, hasOffset] using anyTupleM_pure (fun i : I64 => i.val != 1) starts
theorem offsetArrayTuple_eq (arrays : List (List I64)) :
    offsetArrayTuple arrays =
      .ok ((arrays.flatten).any (fun i => i.val != 1)) := by
  induction arrays with
  | nil => rfl
  | cons axes rest ih =>
    simp only [offsetArrayTuple, hasOffsetMany, offsetAxes_eq]
    cases h : axes.any (fun i => i.val != 1) <;>
      simp [h, ih, List.flatten_cons, List.any_append]

def RequireOneBased : Prop := ∀ starts : List I64,
  let result := requireOneBased offsetArrayTuple [starts]
  (result = .ok true ↔ ∀ i ∈ starts, i.val = 1) ∧
  ((∃ i ∈ starts, i.val ≠ 1) → ∃ m, result = .error (.julia (.argumentError m)))

theorem requireAxes_eq (starts : List I64) :
    requireAxes starts =
      if starts.any (fun i => i.val != 1) then
        .error (.julia (.argumentError "offset arrays are not supported but got an array with index other than 1"))
      else .ok true := by
  simp only [requireAxes, requireOneBased, offsetArrayTuple_eq,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  cases starts.any (fun i => i.val != 1) <;> rfl

theorem requireOneBased_proven : RequireOneBased := by
  intro starts
  change (requireAxes starts = .ok true ↔ ∀ i ∈ starts, i.val = 1) ∧
    ((∃ i ∈ starts, i.val ≠ 1) → ∃ m,
      requireAxes starts = .error (.julia (.argumentError m)))
  rw [requireAxes_eq]
  constructor
  · by_cases h : starts.any (fun i => i.val != 1) = true
    · constructor
      · intro impossible
        simp [h] at impossible
      · intro hall
        obtain ⟨i, hi, hne⟩ := List.any_eq_true.mp h
        have heq := hall i hi
        simp [heq] at hne
    · have hf : starts.any (fun i => i.val != 1) = false := Bool.eq_false_iff.mpr h
      simp only [hf, Bool.false_eq_true, ite_false, true_iff]
      intro i hi
      have hnot := (List.any_eq_false.mp hf) i hi
      simpa using hnot
  · rintro ⟨i, hi, hne⟩
    have ht : starts.any (fun i => i.val != 1) = true :=
      List.any_eq_true.mpr ⟨i, hi, by simp [hne]⟩
    exact ⟨"offset arrays are not supported but got an array with index other than 1", by simp [ht]⟩

def requireIntegerStart {t : IntTy} (first : JInt t) : Result Bool :=
  requireOneBased (fun _ : List Unit => hasOffsetVector
    (fun _ : Unit => pure first)
    (fun x : JInt t => liftJulia (JInt.convert .i64 x.val)) ()) [()]

def RequireOneBasedAllIntegerAxes : Prop := ∀ (t : IntTy) (first : JInt t),
  first.val ≠ 1 → ∃ m,
    requireOneBased (fun _ : List Unit => hasOffsetVector
      (fun _ : Unit => pure first)
      (fun x : JInt t => liftJulia (JInt.convert .i64 x.val)) ()) [()] =
        .error (.julia (.argumentError m))

theorem requireOneBasedAllIntegerAxes_refuted : ¬ RequireOneBasedAllIntegerAxes := by
  intro h
  obtain ⟨m, bad⟩ := h .u64 (JInt.typemax .u64) (by decide)
  have actual : requireIntegerStart (JInt.typemax .u64) =
      .error (.julia (.inexactError "Int64")) := by decide
  change requireIntegerStart (JInt.typemax .u64) =
    .error (.julia (.argumentError m)) at bad
  rw [actual] at bad
  cases bad

/-- A typed family of scalar indices, including the unsupported Bool index. -/
inductive ScalarIndex where
  | integer (i : I64)
  | boolean (b : Bool)
  | rational (numerator : Int) (denominator : Nat) (positive : 0 < denominator)

namespace ScalarIndex

def scaledValue : ScalarIndex → Int × Nat
  | .integer i => (i.val, 1)
  | .boolean b => (if b then 1 else 0, 1)
  | .rational n d _ => (n, d)

/-- The to_index interface accepts integers and rejects Bool/noninteger types. -/
def toIndex : ScalarIndex → Result I64
  | .integer i => .ok i
  | .boolean _ | .rational _ _ _ => .error (.julia (.argumentError "invalid index"))

end ScalarIndex

def CheckboundsAgreesGetindex : Prop := ∀ (lo hi : I64) (i : ScalarIndex),
  checkindexReal (fun p : I64 × I64 => pure p.1) (fun p => pure p.2)
    (fun a i => pure (decide (a.val * i.scaledValue.2 ≤ i.scaledValue.1)))
    (fun i a => pure (decide (i.scaledValue.1 ≤ a.val * i.scaledValue.2))) (lo, hi) i =
      .ok true ↔ ∃ j,
    i.toIndex = .ok j ∧ lo.val ≤ j.val ∧ j.val ≤ hi.val

theorem checkboundsAgreesGetindex_refuted : ¬ CheckboundsAgreesGetindex := by
  intro h
  have bad := (h (int 1) (int 3) (.boolean true)).mp (by decide)
  obtain ⟨j, hj, _⟩ := bad
  cases hj

/-- Scalar endpoint checks cannot accept an index below the first endpoint
or above the last endpoint. This includes every rational and Bool value. -/
def ScalarBoundsSound : Prop := ∀ (lo hi : I64) (i : ScalarIndex),
  checkindexReal (fun p : I64 × I64 => pure p.1) (fun p => pure p.2)
    (fun a i => pure (decide (a.val * i.scaledValue.2 ≤ i.scaledValue.1)))
    (fun i a => pure (decide (i.scaledValue.1 ≤ a.val * i.scaledValue.2))) (lo, hi) i =
      .ok true ↔
    lo.val * i.scaledValue.2 ≤ i.scaledValue.1 ∧
    i.scaledValue.1 ≤ hi.val * i.scaledValue.2

theorem scalarBoundsSound_proven : ScalarBoundsSound := by
  intro lo hi i
  simp [checkindexReal, Bool.and_eq_true]

/-- Every caller-visible conversion failure is preserved even if the
requested dimension would be trailing. -/
def SizeConversionFailure : Prop := ∀ (A D : Type) (cast : D → Result I64)
    (size : A → Result (List I64)) (a : A) (d : D) (e : ArrayError),
  cast d = .error e → sizeDim cast size a d = .error e

theorem sizeConversionFailure_proven : SizeConversionFailure := by
  intro A D cast size a d e h
  simp [sizeDim, h]

/-- The first-element operation rejects an iterator that has no elements. -/
def FirstEmptyError : Prop := ∀ (A E S : Type)
    (iterate : A → Result (Option (E × S))) (a : A),
  iterate a = .ok none → ∃ m,
    firstIterator iterate a = .error (.julia (.argumentError m))

theorem firstEmptyError_proven : FirstEmptyError := by
  intro A E S iterate a h
  exact ⟨"collection must be non-empty", by simp [firstIterator, h]; rfl⟩

/-- Checking a Cartesian scalar tuple cannot evaluate later coordinates
once an earlier coordinate has failed. -/
def CoordinateFailureStops : Prop := ∀ (R I : Type) (defaultAxis : R)
    (check : R → I → Result Bool) (rest : List R → List I → Result Bool)
    (axes : List R) (i : I) (is : List I),
  check (axes.headD defaultAxis) i = .ok false →
    checkboundsIndicesCons defaultAxis check rest axes i is = .ok false

theorem coordinateFailureStops_proven : CoordinateFailureStops := by
  intro R I defaultAxis check rest axes i is h
  cases axes <;> simp_all [checkboundsIndicesCons]

/-! ## Copying into an arbitrary finite index space -/

/-- A heap is observed at arbitrary typed indices. Offset and Cartesian indices
are instances of `I`; no one-based representation is assumed. -/
abbrev Heap (I E : Type) := I → E

def cursor (is : List I) : Option (I × List I) :=
  match is with
  | [] => none
  | i :: is => some (i, is)

def store {I E : Type} [DecidableEq I] (i : I) (x : E)
    (h : Heap I E) : Heap I E := fun q => if q = i then x else h q

def heapSet {I E : Type} [DecidableEq I] (_ : Unit) (i : I) (x : E) :
    StateT (Heap I E) Result Unit := fun h => .ok ((), store i x h)

def copyHeap {I E : Type} [DecidableEq I] (is : List I) (xs : List E) :
    StateT (Heap I E) Result Unit :=
  copytoIterable (fun _ : Unit => pure is) (fun is => pure (cursor is))
    (fun _ is => pure (cursor is)) heapSet () xs

/-- Reference assignment semantics, independent of the source method's iterator state. -/
def prefixWrite {I E : Type} [DecidableEq I] (is : List I) :
    List E → Heap I E → Result (Heap I E)
  | [], h => .ok h
  | x :: xs, h => match is with
    | [] => .error (.julia (.argumentError "destination has fewer elements than required"))
    | i :: is => prefixWrite is xs (store i x h)

def heapCopyStep {I E : Type} [DecidableEq I] (x : E)
    (y : Option (I × List I)) :
    StateT (Heap I E) Result (ForInStep (Option (I × List I))) := do
  match y with
  | none =>
    throw (.julia (.argumentError "destination has fewer elements than required"))
    return .yield y
  | some (i, st) =>
    heapSet () i x
    return .yield (cursor st)

theorem heapCopyLoop_eq {I E : Type} [DecidableEq I] (xs : List E)
    (is : List I) (h : Heap I E) :
    (do
      let _ ← forIn xs (cursor is) heapCopyStep
      pure () : StateT (Heap I E) Result Unit).run h =
      (prefixWrite is xs h).map (fun h => ((), h)) := by
  induction xs generalizing is h with
  | nil =>
    simp [List.forIn_nil, StateT.run, StateT.bind, StateT.pure, prefixWrite, Except.map]
  | cons x xs ih =>
    cases is with
    | nil =>
      simp [List.forIn_cons, cursor, heapCopyStep, StateT.run,
        prefixWrite, StateT.bind, StateT.pure, Except.map]
      rfl
    | cons i is =>
      simpa [List.forIn_cons, cursor, heapCopyStep, StateT.run,
        heapSet, prefixWrite, StateT.bind, StateT.pure] using
        ih is (store i x h)

theorem copytoIterable_heap_reference_equivalence {I E : Type} [DecidableEq I]
    (is : List I) (xs : List E) (h : Heap I E) :
    (copytoIterable (fun _ : Unit => pure is) (fun is => pure (cursor is))
      (fun _ is => pure (cursor is)) heapSet () xs).run h =
      (prefixWrite is xs h).map (fun h => ((), h)) := by
  simp only [copytoIterable, pure_bind]
  refine Eq.trans ?_ (heapCopyLoop_eq xs is h)
  apply congrArg (fun loop : StateT (Heap I E) Result (Option (I × List I)) =>
    (do let _ ← loop; pure () : StateT (Heap I E) Result Unit).run h)
  apply congrArg (fun step => forIn xs (cursor is) step)
  funext x y state
  cases y with
  | none => rfl
  | some p => cases p; rfl

theorem prefixWrite_success {I E : Type} [DecidableEq I] (is : List I) (xs : List E)
    (h : Heap I E) (fit : xs.length ≤ is.length) :
    ∃ h', prefixWrite is xs h = .ok h' ∧
      (∀ q, q ∉ is.take xs.length → h' q = h q) := by
  induction xs generalizing is h with
  | nil =>
    refine ⟨h, ?_, by simp⟩
    cases is <;> rfl
  | cons x xs ih =>
    cases is with
    | nil => simp at fit
    | cons i is =>
      obtain ⟨h', hc, hu⟩ := ih is (store i x h) (by simpa using fit)
      refine ⟨h', hc, ?_⟩
      intro q hq
      have hqi : q ≠ i := by
        intro heq
        apply hq
        simp [heq]
      have hrest : q ∉ is.take xs.length := by
        intro hm
        apply hq
        simp [hm]
      rw [hu q hrest]
      simp [store, hqi]

theorem prefixWrite_outOfSpace {I E : Type} [DecidableEq I]
    (is : List I) (xs : List E) (h : Heap I E) (short : is.length < xs.length) :
    prefixWrite is xs h =
      .error (.julia (.argumentError "destination has fewer elements than required")) := by
  induction xs generalizing is h with
  | nil => simp at short
  | cons x xs ih =>
    cases is with
    | nil => rfl
    | cons i is => exact ih is (store i x h) (by simpa using short)

theorem prefixWrite_at {I E : Type} [DecidableEq I] (is : List I) (xs : List E)
    (h h' : Heap I E) (distinct : is.Nodup) (fit : xs.length ≤ is.length)
    (hc : prefixWrite is xs h = .ok h') :
    ∀ (k : Nat) (hk : k < xs.length), h' (is[k]'(by omega)) = xs[k] := by
  induction xs generalizing is h h' with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    cases is with
    | nil => simp at fit
    | cons i is =>
      have hd := List.nodup_cons.mp distinct
      have hf : xs.length ≤ is.length := by simpa using fit
      intro k hk
      cases k with
      | zero =>
        obtain ⟨out, hout, unchanged⟩ := prefixWrite_success is xs (store i x h) hf
        have heq : out = h' := by
          have hc' : prefixWrite is xs (store i x h) = .ok h' := hc
          rw [hout] at hc'
          exact Except.ok.inj hc'
        subst out
        have hi : i ∉ is.take xs.length := fun hm => hd.1 (List.mem_of_mem_take hm)
        simpa [store] using unchanged i hi
      | succ k =>
        simpa using ih is (store i x h) h' hd.2 hf hc k (by simpa using hk)

/-- Copying any iterable writes exactly its values at the first destination
indices, leaves all other cells unchanged, and rejects a short destination. -/
def CopytoIterablePrefix : Prop :=
  ∀ (I E : Type) [DecidableEq I] (is : List I) (xs : List E) (h : Heap I E),
    let operation := copytoIterable (fun _ : Unit => pure is) (fun is => pure (cursor is))
      (fun _ is => pure (cursor is)) heapSet () xs
    is.Nodup →
    (∀ fit : xs.length ≤ is.length,
      ∃ h', operation.run h = .ok ((), h') ∧
        (∀ (k : Nat) (hk : k < xs.length), h' (is[k]'(by omega)) = xs[k]) ∧
        (∀ q, q ∉ is.take xs.length → h' q = h q)) ∧
    (is.length < xs.length →
      operation.run h =
        .error (.julia (.argumentError "destination has fewer elements than required")))

theorem copytoIterablePrefix_proven : CopytoIterablePrefix := by
  intro I E _ is xs h
  dsimp only
  intro hd
  constructor
  · intro fit
    obtain ⟨h', hc, hu⟩ := prefixWrite_success is xs h fit
    exact ⟨h', by rw [copytoIterable_heap_reference_equivalence, hc]; rfl,
      prefixWrite_at is xs h h' hd fit hc, hu⟩
  · intro short
    rw [copytoIterable_heap_reference_equivalence, prefixWrite_outOfSpace is xs h short]
    rfl

/-! ## Axis validation and caller-visible copy contracts -/

def CheckAxesExact : Prop := ∀ (Ax : Type) [DecidableEq Ax]
    (showAxes : Ax → String) (a b : Ax),
  let result : Result Bool := checkAxes (fun x y => decide (x = y)) showAxes a b
  (result = .ok true ↔ a = b) ∧
  (a ≠ b → ∃ message, result = .error (.dimensionMismatch message))

theorem checkAxesExact_proven : CheckAxesExact := by
  intro Ax _ showAxes a b
  by_cases h : a = b
  · simp [checkAxes, h]
  · exact ⟨by simp [checkAxes, h],
      fun _ => ⟨"axes must agree, got " ++ showAxes a ++ " and " ++ showAxes b,
        by simp [checkAxes, h]; rfl⟩⟩

/-- All destination elements equal the source elements in order, and copying
does not modify memory outside the destination's indices. -/
def ArrayContentsCopied {I E : Type} (is : List I) (xs : List E)
    (h h' : Heap I E) : Prop :=
  (∀ (k : Nat) (hi : k < is.length) (hx : k < xs.length), h' is[k] = xs[k]) ∧
  (∀ q, q ∉ is → h' q = h q)

theorem copyHeap_full {I E : Type} [DecidableEq I] (is : List I) (xs : List E)
    (h : Heap I E) (hd : is.Nodup) (len : xs.length = is.length) :
    ∃ h', (copyHeap is xs).run h = .ok ((), h') ∧ ArrayContentsCopied is xs h h' := by
  obtain ⟨h', hc, hv, hu⟩ :=
    (copytoIterablePrefix_proven I E is xs h hd).1 (by omega)
  refine ⟨h', hc, ?_, ?_⟩
  · intro k hi hx
    exact hv k hx
  · intro q hq
    apply hu q
    simpa [len] using hq

abbrev SingletonCopyDataids := {ids : List (JInt .u64) // ids.length = 1}

def copyArrayDataids {A : Type} (objectid : A → JInt .u64) (a : A) :
    SingletonCopyDataids :=
  ⟨dataidsArray objectid a, rfl⟩

def copyDataidsFirst (ids : SingletonCopyDataids) : JInt .u64 :=
  ids.val[0]'(by have := ids.property; omega)

/-- Source copying for disjoint, Cartesian-indexed storage. Source index
tokens carry the immutable value they address; destination indices are arbitrary.
The scalar memory read, BitArray specialization and dense copying are external
interfaces. The source alias test, unalias dispatcher and copy loop are concrete. -/
def sourceCopyHeap {I E Ax : Type} [DecidableEq I]
    (is : List I) (read : List E → I64 → StateT (Heap I E) Result E)
    (copy : List E → StateT (Heap I E) Result (List E))
    (copyBits : Ax → List E → StateT (Heap I E) Result Ax) :
    Ax → List E → StateT (Heap I E) Result Ax :=
  copytoArray (fun xs => pure xs.isEmpty) (fun _ => false) copyBits
    (unaliasArray
      (mightaliasArray (fun _ => pure false) (fun _ => pure false)
        (fun _ => pure is.isEmpty) (fun xs => pure xs.isEmpty)
        (fun a => pure (copyArrayDataids (fun _ => JInt.lit .u64 0) a))
        (fun xs => pure (copyArrayDataids (fun _ => JInt.lit .u64 1) xs))
        (fun destids srcids => pure
          (isdisjointOneOne (copyDataidsFirst destids) (copyDataidsFirst srcids))))
      (unaliascopyDense copy))
    (fun _ => pure false) (fun _ => pure false)
    (copytoUnaliased
      (fun xs => pure xs.isEmpty)
      (fun _ => pure ((List.range is.length).map (fun (k : Nat) => int ((k : Int) + 1))))
      (fun xs => pure ((List.range xs.length).map (fun (k : Nat) => int ((k : Int) + 1))))
      (fun js => pure (js.headD (int 1))) (fun js => pure (js.headD (int 1)))
      (fun js => pure (js.getLastD (int 0)))
      (fun i j => pure (i - j)) (fun i d => pure (i + d))
      (fun _ _ => pure true) id read
      (fun _ _ _ => pure ())
      (fun i => pure (i - int 1)) (fun i => pure (i + int 1))
      (fun _ _ _ => pure ())
      (fun _ => pure is) (fun xs => pure (is.zip xs))
      (fun _ _ => false) (fun ds ss => pure (ds.zip ss))
      (fun _ _ => throw (.julia .boundsError)) (fun _ i => pure i.2)
      (fun _ i e => heapSet () i e))

theorem zippedCopyLoop {I E : Type} [DecidableEq I] (is js : List I)
    (xs : List E) (h : Heap I E) (fit : min xs.length js.length ≤ is.length) :
    (do
      for (i, s) in is.zip (js.zip xs) do heapSet () i s.2
      pure () : StateT (Heap I E) Result Unit).run h =
      (prefixWrite is (xs.take js.length) h).map (fun h => ((), h)) := by
  induction is generalizing js xs h with
  | nil =>
    have empty : xs.take js.length = [] := List.length_eq_zero_iff.mp (by
      rw [List.length_take]
      simpa [Nat.min_comm] using fit)
    simp [empty, List.forIn_nil, prefixWrite, StateT.run, StateT.bind,
      StateT.pure, Except.map]
  | cons i is ih =>
    cases js with
    | nil =>
      simp [List.forIn_nil, prefixWrite, StateT.run, StateT.bind, StateT.pure, Except.map]
    | cons j js =>
      cases xs with
      | nil =>
        simp [List.forIn_nil, prefixWrite, StateT.run, StateT.bind, StateT.pure, Except.map]
      | cons x xs =>
        simpa [List.forIn_cons, heapSet, StateT.run, StateT.bind, StateT.pure,
          prefixWrite, Except.map] using ih js xs (store i x h) (by simpa using fit)

theorem stateReturnRetarget {S R B : Type} (action : StateT S Result R)
    (state : S) (b : B) :
    (do let _ ← action; pure b : StateT S Result B).run state =
      ((do let _ ← action; pure () : StateT S Result Unit).run state).map
        (fun p => (b, p.2)) := by
  cases heq : action state <;>
    simp [StateT.run, StateT.bind, StateT.pure, heq, Except.map]

theorem sourceCopyHeap_full {I E Ax : Type} [DecidableEq I]
    (is : List I) (xs : List E) (h : Heap I E) (ax : Ax)
    (read : List E → I64 → StateT (Heap I E) Result E)
    (copy : List E → StateT (Heap I E) Result (List E))
    (copyBits : Ax → List E → StateT (Heap I E) Result Ax)
    (hd : is.Nodup) (len : xs.length = is.length) :
    ∃ h', (sourceCopyHeap is read copy copyBits ax xs).run h = .ok (ax, h') ∧
      ArrayContentsCopied is xs h h' := by
  obtain ⟨h', hc, hp⟩ := copyHeap_full is xs h hd len
  refine ⟨h', ?_, hp⟩
  have loop := zippedCopyLoop is is xs h (by omega)
  have take : xs.take is.length = xs := List.take_of_length_le (by omega)
  rw [take] at loop
  have ref : (prefixWrite is xs h).map (fun h => ((), h)) = .ok ((), h') := by
    rw [← copytoIterable_heap_reference_equivalence is xs h]
    exact hc
  rw [ref] at loop
  cases xs with
  | nil =>
    have empty : is = [] := List.length_eq_zero_iff.mp (by simpa using len.symm)
    subst is
    have hh : h' = h := by
      have heq : h = h' := by simpa [copyHeap, copytoIterable, StateT.run,
        StateT.bind, StateT.pure, List.forIn_nil] using hc
      exact heq.symm
    subst h'
    simp [sourceCopyHeap, copytoArray, StateT.run, StateT.bind, StateT.pure]
  | cons x xs =>
    cases is with
    | nil => simp at len
    | cons i is =>
      change (do
        let _ ← forIn ((i :: is).zip ((i :: is).zip (x :: xs))) PUnit.unit
          (fun p _ => do heapSet () p.1 p.2.2; pure (.yield PUnit.unit))
        pure ax : StateT (Heap I E) Result Ax).run h = .ok (ax, h')
      rw [stateReturnRetarget, loop]
      rfl

def CopyBangArrayContents : Prop :=
  ∀ (I E Ax : Type) [DecidableEq I] [DecidableEq Ax] (axd axs : Ax)
    (is : List I) (xs : List E) (h : Heap I E)
    (read : List E → I64 → StateT (Heap I E) Result E)
    (copy : List E → StateT (Heap I E) Result (List E))
    (copyBits : Ax → List E → StateT (Heap I E) Result Ax),
    is.Nodup → xs.length = is.length →
    let operation := copyBangArray (fun a : Ax => pure a)
      (fun _ : List E => pure axs) (fun a b => decide (a = b))
      (sourceCopyHeap is read copy copyBits) axd xs
    (axd = axs → ∃ h', operation.run h = .ok (axd, h') ∧
      ArrayContentsCopied is xs h h') ∧
    (axd ≠ axs → ∃ message, operation.run h =
      .error (.julia (.argumentError message)))

theorem copyBangArrayContents_proven : CopyBangArrayContents := by
  intro I E Ax _ _ axd axs is xs h read copy copyBits hd len
  constructor
  · intro heq
    obtain ⟨h', hc, hp⟩ := sourceCopyHeap_full is xs h axd read copy copyBits hd len
    refine ⟨h', ?_, hp⟩
    simpa [copyBangArray, heq, StateT.run, StateT.bind, StateT.pure] using hc
  · intro hne
    refine ⟨"arrays must have the same axes for copy! (consider using `copyto!`)", ?_⟩
    simp [copyBangArray, hne, StateT.run, StateT.bind, StateT.pure]
    rfl

def CopyAxesContents : Prop :=
  ∀ (I E Ax : Type) [DecidableEq I] [DecidableEq Ax]
    (showAxes : Ax → String) (axd axs : Ax) (is : List I) (xs : List E) (h : Heap I E)
    (read : List E → I64 → StateT (Heap I E) Result E)
    (copy : List E → StateT (Heap I E) Result (List E))
    (copyBits : Ax → List E → StateT (Heap I E) Result Ax),
    is.Nodup → xs.length = is.length →
    let operation := copytoAxesCheck (fun a : Ax => pure a)
      (fun _ : List E => pure axs)
      (checkAxes (fun a b => decide (a = b)) showAxes)
      (sourceCopyHeap is read copy copyBits) axd xs
    (axd = axs → ∃ h', operation.run h = .ok (axd, h') ∧
      ArrayContentsCopied is xs h h') ∧
    (axd ≠ axs → ∃ message, operation.run h =
      .error (.dimensionMismatch message))

theorem copyAxesContents_proven : CopyAxesContents := by
  intro I E Ax _ _ showAxes axd axs is xs h read copy copyBits hd len
  constructor
  · intro heq
    obtain ⟨h', hc, hp⟩ := sourceCopyHeap_full is xs h axd read copy copyBits hd len
    refine ⟨h', ?_, hp⟩
    simpa [copytoAxesCheck, checkAxes, heq, StateT.run,
      StateT.bind, StateT.pure] using hc
  · intro hne
    refine ⟨"axes must agree, got " ++ showAxes axd ++ " and " ++ showAxes axs, ?_⟩
    simp [copytoAxesCheck, checkAxes, hne, StateT.run, StateT.bind, StateT.pure]
    rfl

/-! ## Source snapshots and overlapping views -/

inductive ReadView (I E : Type) where
  | live (indices : List I)
  | snapshot (values : List E)

def ReadView.values (h : Heap I E) : ReadView I E → List E
  | .live is => is.map h
  | .snapshot xs => xs

def ReadView.isEmpty : ReadView I E → Bool
  | .live is => is.isEmpty
  | .snapshot xs => xs.isEmpty

def captureView (_ : Unit) (src : ReadView I E) :
    StateT (Heap I E) Result (ReadView I E) :=
  fun h => .ok (.snapshot (src.values h), h)

def copyView {I E : Type} [DecidableEq I] (is : List I) (src : ReadView I E) :
    StateT (Heap I E) Result Unit := fun h => (copyHeap is (src.values h)).run h

/-- The explicit-style source method captures aliased source values before
calling the copy primitive. This equality is proved, rather than assumed. -/
theorem copytoStyles_snapshot_reference_equivalence {I E Style : Type} [DecidableEq I]
    (ds ss : Style) (is js : List I) (h : Heap I E) :
    (copytoStyles (fun s => pure s.isEmpty) captureView
      (fun _ _ _ s => copyView is s) ds () ss (.live js)).run h =
      (copyHeap is (js.map h)).run h := by
  cases js with
  | nil =>
    simp [copytoStyles, ReadView.isEmpty, copyHeap, copytoIterable,
      List.forIn_nil, StateT.run, StateT.bind, StateT.pure]
  | cons j js =>
    simp [copytoStyles, ReadView.isEmpty, captureView, copyView,
      ReadView.values, StateT.run, StateT.bind, StateT.pure]

/-- Overlapping source and destination views copy entry-state source values;
the result is independent of the explicit index-style arguments. -/
def CopytoAliasedSnapshot : Prop :=
  ∀ (I E Style : Type) [DecidableEq I] (ds ss : Style)
    (is js : List I) (h : Heap I E), is.Nodup → ∀ fit : js.length ≤ is.length,
    ∃ h',
      (copytoStyles (fun s => pure s.isEmpty) captureView
        (fun _ _ _ s => copyView is s) ds () ss (.live js)).run h = .ok ((), h') ∧
      (∀ (k : Nat) (hk : k < js.length),
        h' (is[k]'(by omega)) = h js[k]) ∧
      (∀ q, q ∉ is.take js.length → h' q = h q)

theorem copytoAliasedSnapshot_proven : CopytoAliasedSnapshot := by
  intro I E Style _ ds ss is js h hd fit
  obtain ⟨h', hc, hv, hu⟩ :=
    (copytoIterablePrefix_proven I E is (js.map h) h hd).1 (by simpa using fit)
  refine ⟨h', ?_, ?_, ?_⟩
  · rw [copytoStyles_snapshot_reference_equivalence]
    exact hc
  · intro k hk
    have value := hv k (by simpa using hk)
    rw [List.getElem_map] at value
    exact value
  · simpa using hu

/-! ## Allocation, zero filling, and iterator protocol -/

/-- The allocation and fill interfaces have their documented shape and
element contracts. Both zero-array dispatches preserve that shape. -/
def ZeroShapeContents : Prop :=
  ∀ (A B E Ty Shape : Type) (shapeA : A → Shape) (shapeB : B → Shape)
    (contents : B → List E) (z : E) (typeof : E → Ty)
    (similar : A → Ty → B) (fill : B → E → B),
    (∀ a t, shapeB (similar a t) = shapeA a) →
    (∀ b x, shapeB (fill b x) = shapeB b ∧ ∀ v ∈ contents (fill b x), v = x) →
    ∀ (t : Ty) (a : A),
      ∃ b, zeroNumericArray (m := Result) (fun _ => pure z) typeof
          (fun a t => pure (similar a t)) (fun b x => pure (fill b x)) t a = .ok b ∧
        zeroMissingArray (m := Result) (fun _ => pure z) typeof
          (fun a t => pure (similar a t)) (fun b x => pure (fill b x)) t a = .ok b ∧
        shapeB b = shapeA a ∧ ∀ v ∈ contents b, v = z

theorem zeroShapeContents_proven : ZeroShapeContents := by
  intro A B E Ty Shape shapeA shapeB contents z typeof similar fill hs hf t a
  refine ⟨fill (similar a (typeof z)) z, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rw [(hf _ _).1, hs]
  · exact (hf _ _).2

def IsEmptyContents : Prop :=
  ∀ (A E : Type) (contents : A → List E) (length : A → I64) (a : A),
    (length a).val = (contents a).length →
      isemptyArray (m := Result) (fun a => pure (length a)) a = .ok ((contents a).isEmpty)

theorem isemptyContents_proven : IsEmptyContents := by
  intro A E contents length a hn
  cases hc : contents a <;> simp [isemptyArray, hn, hc]
  omega

/-! Nothing to promise:
copy@1154: forwards the array unchanged to copymutable; allocation and copying belong to that method.
copymutable@1215: forwards the iterator unchanged to collect.
copymutable@1216: forwards a dense array unchanged to its copy method.
zero@1220: forwards elementwise zeroing to map.
one@1236: forwards the element-type unit to the matrix-identity implementation.
oneunit@1237: forwards the element-type unit to the matrix-identity implementation.
iterate_starting_state@1245: selects the starting-state implementation by index style.
iterate_starting_state@1246: forwards to the array's firstindex.
iterate_starting_state@1247: packages eachindex as the iterator's initial tuple state.
iterate@1250: forwards the supplied or default state to _iterate_abstractarray.
map@1269: forwards StepRangeLen conversion to convert.
pointer@1279: composes cconvert and unsafe_convert without pointer arithmetic.
-/

/-! ## Index conversion and checked reads -/

/-- The canonical guard must run before conversion or element access. Bounds
failure must likewise prevent either index conversion or element access. -/
def IndexingChecks : Prop :=
  (∀ (A E : Type) (typeof : A → String) (convert : A → I64 → Result I64)
    (get : A → I64 → Result E) (a : A) (i : I64),
    getindexArray (fun _ => pure ())
      (fun _ => errorCanonicalGetindexLinear typeof) convert
      (fun _ => getindexLinearScalar get) a i =
      .error (.canonicalIndex "getindex" (typeof a))) ∧
  (∀ (A E Lin Axis : Type) (check : A → List I64 → Result Unit)
    (linearIndices : A → Result Lin) (firstLinear : Lin → Result I64)
    (axes : A → Result (List Axis)) (firstAxis : Axis → Result I64)
    (getLinear : A → I64 → Result E)
    (getCartesian : A → List I64 → Result E)
    (a : A) (e : ArrayError), check a [] = .error e →
    getindexLinear check (fun a _ => toLinearEmpty linearIndices firstLinear a)
      getLinear a [] = .error e ∧
    getindexCartesian check (fun a _ => toSubscriptsEmpty axes firstAxis a)
      getCartesian a [] = .error e)

theorem indexingChecks_proven : IndexingChecks := by
  constructor
  · intro A E typeof convert get a i
    rfl
  · intro A E Lin Axis check linearIndices firstLinear axes firstAxis getLinear
      getCartesian a e h
    simp [getindexLinear, getindexCartesian, h]

/-- Canonical methods that the array subtype has failed to provide raise the
dedicated exception, independently of indices, rank and element type. -/
def CanonicalGetindexRejected : Prop :=
  ∀ (A : Type) (typeof : A → String) (a : A) (i : I64) (n : Nat)
    (is : Fin n → I64),
    errorCanonicalGetindexLinear typeof a i = .error (.canonicalIndex "getindex" (typeof a)) ∧
    errorCanonicalGetindexCartesian typeof a is = .error (.canonicalIndex "getindex" (typeof a))

theorem canonicalGetindexRejected_proven : CanonicalGetindexRejected := by
  intro A typeof a i n is
  exact ⟨rfl, rfl⟩

def UnsupportedGetindexRejected : Prop :=
  ∀ (S A I E : Type) (ta : A → String) (ti : I → String) (s : S) (a : A) (is : I),
    ∃ message, getindexUnsupported (E := E) ta ti s a is = .error (.errorException message)

theorem unsupportedGetindexRejected_proven : UnsupportedGetindexRejected := by
  intro S A I E ta ti s a is
  exact ⟨_, rfl⟩

/-- A lawful coordinate conversion and canonical element reader determine the
element selected by either checked indexing path. Invalid coordinates fail.
The coordinate conversion uses the later `_sub2ind` interface. -/
def LinearReadValues : Prop :=
  ∀ (A E : Type) (valid : A → List I64 → Bool) (position : A → List I64 → I64)
    (elements : A → I64 → E) (sub2ind : A → List I64 → Result I64),
    (∀ a is, valid a is = true → sub2ind a is = .ok (position a is)) →
    ∀ a is,
      getindexLinear
        (fun a is => if valid a is then pure () else throw (.julia .boundsError))
        (toLinearMany sub2ind)
        (getindexLinearScalar (fun a i => pure (elements a i))) a is =
        if valid a is then .ok (elements a (position a is)) else .error (.julia .boundsError)

theorem linearReadValues_proven : LinearReadValues := by
  intro A E valid position elements sub2ind hc a is
  cases hv : valid a is with
  | false => simp [getindexLinear, hv]; rfl
  | true => simp [getindexLinear, toLinearMany, getindexLinearScalar, hv, hc a is hv]

/-- Mapping axis starts preserves rank and every coordinate's position. The
same statement applies when axis integer types differ from machine Int. -/
def AxisStartCoordinates : Prop :=
  ∀ (Axis I : Type) (first : Axis → I) (axes : List Axis),
    ∃ coordinates,
      toSubscriptsEmpty (fun xs : List Axis => pure xs) (fun ax => pure (first ax)) axes =
        .ok coordinates ∧
      coordinates.length = axes.length ∧
      ∀ k : Nat, coordinates[k]? = (axes[k]?).map first

theorem mapM_pure_result {A B : Type} (f : A → B) (xs : List A) :
    xs.mapM (m := Result) (fun x => .ok (f x)) = .ok (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, ih]
    rfl

theorem axisStartCoordinates_proven : AxisStartCoordinates := by
  intro Axis I first axes
  refine ⟨axes.map first, ?_, List.length_map first, ?_⟩
  · change axes.mapM (m := Result) (fun ax => .ok (first ax)) = _
    exact mapM_pure_result first axes
  · intro k
    exact List.getElem?_map

/-- With no explicit indices, every omitted dimension must be singleton. -/
def OmittedSingletonBounds : Prop :=
  ∀ (Axis : Type) (length : Axis → I64) (axes : List Axis),
    checkboundsIndicesNil (fun ax => pure (length ax)) axes =
      .ok (decide (∀ ax ∈ axes, (length ax).val = 1))

theorem omittedSingletonBounds_proven : OmittedSingletonBounds := by
  intro Axis length axes
  induction axes with
  | nil => simp [checkboundsIndicesNil, allTupleM]
  | cons a axes ih =>
    by_cases h : (length a).val = 1
    · simpa [checkboundsIndicesNil, allTupleM, h] using ih
    · simp [checkboundsIndicesNil, allTupleM, h]

/-! ## Shape and omitted-coordinate invariants -/

def DefaultAxesShape : Prop :=
  ∀ sizes : List I64,
    ∃ axes,
      axesDefault (fun xs : List I64 => pure xs) oneBasedAxis sizes = .ok axes ∧
      axes.length = sizes.length ∧
      ∀ k : Nat, (axes[k]?).map Prod.fst = (sizes[k]?).map (fun _ => int 1) ∧
        (axes[k]?).map Prod.snd = (sizes[k]?).map (fun n => n.val.toNat)

theorem defaultAxesShape_proven : DefaultAxesShape := by
  intro sizes
  refine ⟨sizes.map oneBasedAxis, rfl, List.length_map _, ?_⟩
  intro k
  rw [List.getElem?_map]
  cases sizes[k]? <;> exact ⟨rfl, rfl⟩

/-- Repeated dispatch through the two source `_remaining_size` methods. -/
def remainingSizeCalls {I Axis : Type} : List I → List Axis → Result (List Axis)
  | [], _ => throw (.julia (.argumentError "empty tuple has no tail"))
  | [i], axes => pure (remainingSizeSingle i axes)
  | i :: k :: is, axes =>
    remainingSizeMany
      (fun xs : List I => pure xs.tail)
      (fun xs : List Axis => match xs with
        | [] => throw (.julia (.argumentError "empty tuple has no tail"))
        | _ :: xs => pure xs)
      (fun _ axes => remainingSizeCalls (k :: is) axes) (i :: k :: is) axes

theorem remainingSizeCalls_reference {I Axis : Type} (j : List I) (axes : List Axis)
    (nonempty : j ≠ []) (fit : j.length ≤ axes.length) :
    remainingSizeCalls j axes = .ok (axes.drop (j.length - 1)) := by
  induction j generalizing axes with
  | nil => exact False.elim (nonempty rfl)
  | cons i is ih =>
    cases is with
    | nil => rfl
    | cons k ks =>
      cases axes with
      | nil => simp at fit
      | cons a axes =>
        have hf : (k :: ks).length ≤ axes.length := by simpa using fit
        have hr := ih axes (by simp) hf
        simpa [remainingSizeCalls, remainingSizeMany, List.drop_succ_cons] using hr

/-- After bounds checking, omitted axes are filled with their first indices.
The already supplied coordinates retain their positions and values. -/
def OmittedCoordinatePositions : Prop :=
  ∀ (Axis I : Type) (first : Axis → I) (axes : List Axis)
    (head : Axis) (omitted : List Axis) (j : List I),
    j ≠ [] → j.length ≤ axes.length →
    axes.drop (j.length - 1) = head :: omitted →
    ∃ coordinates,
      toSubscriptsFill (fun xs : List Axis => pure xs) remainingSizeCalls
        (fun xs => match xs with
          | [] => throw (.julia (.argumentError "empty tuple has no tail"))
          | _ :: xs => pure xs)
        (fun ax => pure (first ax)) axes (head, omitted) j = .ok coordinates ∧
      coordinates.length = j.length + omitted.length ∧
      coordinates.take j.length = j ∧
      coordinates.drop j.length = omitted.map first

theorem omittedCoordinatePositions_proven : OmittedCoordinatePositions := by
  intro Axis I first axes head omitted j hn hf hd
  have hr := remainingSizeCalls_reference j axes hn hf
  rw [hd] at hr
  refine ⟨j ++ omitted.map first, ?_, ?_, ?_, ?_⟩
  · simp only [toSubscriptsFill]
    simp [hr, mapM_pure_result]
  · simp
  · simp
  · simp

/-- The index-list view supports arbitrary index types and offset axes. The
expected answers are the ends of the element sequence, including empty arrays. -/
def FirstLastElements : Prop :=
  ∀ (I E : Type) (indices : List I) (element : I → E),
    firstArray (fun _ : Unit => pure indices)
      (fun xs => match xs.head? with
        | none => throw (.julia .boundsError)
        | some i => pure i)
      (fun _ i => pure (element i)) () =
      (match (indices.map element).head? with
        | none => .error (.julia .boundsError)
        | some x => .ok x) ∧
    last (lastindexArray (fun _ : Unit => pure indices)
      (fun xs => match xs.getLast? with
        | none => throw (.julia .boundsError)
        | some i => pure i))
      (fun _ i => pure (element i)) () =
      (match (indices.map element).getLast? with
        | none => .error (.julia .boundsError)
        | some x => .ok x)

theorem firstLastElements_proven : FirstLastElements := by
  intro I E indices element
  constructor
  · rw [List.head?_map]
    cases hi : indices.head? <;> simp [firstArray, hi] <;> rfl
  · rw [List.getLast?_map]
    cases hi : indices.getLast? <;> simp [last, lastindexArray, hi] <;> rfl

def FixedOneBasedKinds : Prop :=
  ∀ (A : Type) (a : A),
    hasOffsetNone = false ∧ hasOffsetColon = false ∧ hasOffsetArray a = false

theorem fixedOneBasedKinds_proven : FixedOneBasedKinds := by
  intro A a
  exact ⟨rfl, rfl, rfl⟩

/-! Nothing to promise:
_to_subscript_indices@1417: packages the empty tuple for a scalar rank-zero read.
_to_subscript_indices@1418: packages the empty tuple for a rank-zero read.
_to_subscript_indices@1419: delegates tuple splitting and forwards both resulting tuples.
_to_subscript_indices@1424: selects the axes-dependent omitted-coordinate method.
_to_subscript_indices@1431: projects the retained coordinates after bounds checking.
_to_subscript_indices@1432: returns the exact-rank index tuple unchanged.
_remaining_size@1433: returns the remaining axes tuple at the terminal recursive case.
_remaining_size@1434: forwards both tuple tails to the recursive method.
_unsafe_ind2sub@1435: packages the empty coordinate tuple for rank zero.
_unsafe_ind2sub@1436: forwards to _ind2sub.
-/

/-! Nothing to promise:
convert@16: returns the same array for an identical target type.
convert@17: forwards to the target AbstractArray constructor.
convert@18: forwards to the target rank-constrained AbstractArray constructor.
axes1@140: supplies the singleton axis for rank zero.
axes1@141: selects the first axes tuple field.
axes1@142: delegates axis construction to oneto and iterator length.
keys@169: delegates the Cartesian index space to CartesianIndices and axes.
keys@170: forwards to LinearIndices.
keytype@192: delegates value keytype to its type.
keytype@193: delegates the bottom-type result to eltype.
keytype@195: constructs the CartesianIndex type for the array rank.
keytype@196: supplies the machine integer key type for vectors.
valtype@198: delegates value valtype to its type.
valtype@199: delegates the bottom-type result to eltype.
valtype@217: delegates to the array element type.
eltype@243: supplies Any for a type without an element-type specialization.
eltype@245: delegates the value element type to its type.
elsize@261: delegates storage size to the array type.
ndims@278: projects the rank type parameter.
ndims@279: projects the rank type parameter.
eachindex@322: forwards to keys.
eachindex@325: forwards vector indexing to axes1.
eachindex@394: constructs the unchecked one-based index range from dense storage length.
eachindex@395: constructs the one-based index range from length.
eachindex@396: forwards vector indexing to axes1.
keys@407: forwards explicit style and arrays to eachindex.
getindex@1369: converts the integer index tuple then delegates to the concrete reader.
unsafe_getindex@1371: forwards to getindex with bounds-check elision metadata.
CanonicalIndexError@1376: constructs the two exception fields without computation.
error_if_canonical_getindex@1383: the noncanonical guard has no action.
_getindex@1390: resolves dispatch ambiguity by forwarding the scalar read.
_getindex@1391: forwards the canonical scalar read.
_to_linear_index@1398: forwards the scalar index unchanged.
_to_linear_index@1399: projects the vector's first coordinate after bounds checking.
_to_linear_index@1400: delegates the starting linear index to LinearIndices and first.
_to_linear_index@1401: forwards coordinate conversion to _sub2ind.
_getindex@1410: forwards the exact-rank canonical read.
_to_subscript_indices@1414: forwards scalar decomposition to _unsafe_ind2sub.
_to_subscript_indices@1416: packages the empty coordinate tuple for rank zero.
-/

/-! ## Checked writes and alias prevention -/

/-- Rejected canonical signatures and invalid coordinates cannot reach a write. -/
def WriteChecks : Prop :=
  (∀ (A V I J S R : Type) (style : A → Result S)
    (guard : S → A → I → Result Unit) (convert : A → I → Result J)
    (set : S → A → V → J → Result R) (a : A) (v : V) (is : I)
    (s : S) (e : ArrayError), style a = .ok s → guard s a is = .error e →
      setindexArray style guard convert set a v is = .error e) ∧
  (∀ (A V J R : Type) (check : A → List I64 → Result Unit)
    (linear : A → List I64 → Result I64) (cartesian : A → List I64 → Result J)
    (setLinear : A → V → I64 → Result R) (setCartesian : A → V → J → Result R)
    (a : A) (v : V) (is : List I64) (e : ArrayError), check a is = .error e →
      setindexLinear check linear setLinear a v is = .error e ∧
      setindexCartesian check cartesian setCartesian a v is = .error e)

theorem writeChecks_proven : WriteChecks := by
  constructor
  · intro A V I J S R style guard convert set a v is s e hs hg
    simp [setindexArray, hs, hg]
  · intro A V J R check linear cartesian setLinear setCartesian a v is e h
    simp [setindexLinear, setindexCartesian, h]

def CanonicalSetindexRejected : Prop :=
  ∀ (A : Type) (typeof : A → String) (a : A) (i : I64) (n : Nat)
    (is : Fin n → I64),
    errorCanonicalSetindexLinear typeof a i = .error (.canonicalIndex "setindex!" (typeof a)) ∧
    errorCanonicalSetindexCartesian typeof a is = .error (.canonicalIndex "setindex!" (typeof a))

theorem canonicalSetindexRejected_proven : CanonicalSetindexRejected := by
  intro A typeof a i n is
  exact ⟨rfl, rfl⟩

def UnsupportedSetindexRejected : Prop :=
  ∀ (S A V I R : Type) (ta : A → String) (ti : I → String)
    (s : S) (a : A) (v : V) (is : I),
    ∃ message, setindexUnsupported (R := R) ta ti s a v is = .error (.errorException message)

theorem unsupportedSetindexRejected_proven : UnsupportedSetindexRejected := by
  intro S A V I R ta ti s a v is
  exact ⟨_, rfl⟩

/-- A same-type copy retains every element and its independent-storage
guarantee when the generic unaliascopy path checks its type. -/
def UnaliascopyContents : Prop :=
  ∀ (A E : Type) (values : A → List E) (shares : A → A → Prop)
    (copy : A → Result A),
    (∀ a, ∃ c, copy a = .ok c ∧ values c = values a ∧ ¬ shares a c) →
    ∀ a, ∃ c,
      unaliascopyArray copy (fun a c => pure (unaliascopySame a c))
        (fun c => pure c) a = .ok c ∧
      values c = values a ∧ ¬ shares a c

theorem unaliascopyContents_proven : UnaliascopyContents := by
  intro A E values shares copy hc a
  obtain ⟨c, hr, hv, hs⟩ := hc a
  exact ⟨c, by simp [unaliascopyArray, unaliascopySame, hr], hv, hs⟩

def UnaliascopyMismatchRejected : Prop :=
  ∀ (A C : Type) (ta : A → String) (tc : C → String)
    (wrapper : String → String) (a : A) (c : C),
    ∃ message, unaliascopyMismatch ta tc wrapper (fun xs => pure (String.join xs)) a c =
      .error (.julia (.argumentError message))

theorem unaliascopyMismatchRejected_proven : UnaliascopyMismatchRejected := by
  intro A C ta tc wrapper a c
  exact ⟨_, rfl⟩

/-! Nothing to promise:
unsafe_setindex!@1469: forwards to the supplied canonical writer with bounds-check elision metadata.
error_if_canonical_setindex@1479: the noncanonical guard has no action.
_setindex!@1486: forwards the canonical scalar write.
_setindex!@1495: forwards the exact-rank canonical write.
parent@1548: returns the input when the array has no wrapper parent.
unalias@1567: returns immutable range storage unchanged.
unalias@1568: returns the nonarray argument unchanged.
unaliascopy@1582: forwards dense-array copying to copy.
_unaliascopy@1584: returns the already type-matched copy unchanged.
unaliascopy@1593: returns the nonarray argument unchanged.
-/

/-- Dispatch among the nine source methods for valid data-id tuples. -/
def disjointCalls : List (JInt .u64) → List (JInt .u64) → Bool
  | [], [] => isdisjointEmptyEmpty
  | [], [b] => isdisjointEmptyOne b
  | [], bs => isdisjointEmptyMany bs
  | [a], [] => isdisjointOneEmpty a
  | [a], [b] => isdisjointOneOne a b
  | [a], bs => isdisjointOneMany (fun x xs => decide (x ∈ xs)) a bs
  | as, [] => isdisjointManyEmpty as
  | as, [b] => isdisjointManyOne (fun x xs => decide (x ∈ xs)) as b
  | a :: as, bs => isdisjointMany (fun x xs => decide (x ∈ xs))
      (fun _ _ => disjointCalls as bs) (a, as) bs

theorem disjointCalls_correct (as bs : List (JInt .u64)) :
    disjointCalls as bs = true ↔ ∀ x ∈ as, x ∉ bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [disjointCalls, isdisjointEmptyEmpty]
    | cons b bs =>
      cases bs <;> simp [disjointCalls, isdisjointEmptyOne, isdisjointEmptyMany]
  | cons a as ih =>
    cases as with
    | nil =>
      cases bs with
      | nil => simp [disjointCalls, isdisjointOneEmpty]
      | cons b bs =>
        cases bs <;>
          simp [disjointCalls, isdisjointOneOne, isdisjointOneMany]
    | cons a' as =>
      cases bs with
      | nil => simp [disjointCalls, isdisjointManyEmpty]
      | cons b bs =>
        cases bs with
        | nil =>
          simp [disjointCalls, isdisjointManyOne]
          grind
        | cons b' bs =>
          simpa [disjointCalls, isdisjointMany, Bool.and_eq_true] using
            (and_congr (show (!(decide (a ∈ b :: b' :: bs))) = true ↔
              a ∉ b :: b' :: bs by simp) (ih (b :: b' :: bs)))

/-- The recursive predicate recognizes exactly disjoint mutable data segments. -/
def DataidsDisjoint : Prop :=
  ∀ as bs, disjointCalls as bs = true ↔ ∀ x ∈ as, x ∉ bs

theorem dataidsDisjoint_proven : DataidsDisjoint := disjointCalls_correct

/-- For nonempty mutable arrays, alias detection agrees with intersection of
the complete data-id tuples. Empty or immutable arrays cannot alias. -/
def MightaliasSegments : Prop :=
  ∀ (A B : Type) (idsA : A → List (JInt .u64)) (idsB : B → List (JInt .u64))
    (bitsA : A → Bool) (bitsB : B → Bool)
    (emptyA : A → Bool) (emptyB : B → Bool) (a : A) (b : B),
    mightaliasArray (m := Result) (fun a => pure (bitsA a)) (fun b => pure (bitsB b))
      (fun a => pure (emptyA a)) (fun b => pure (emptyB b))
      (fun a => pure (idsA a)) (fun b => pure (idsB b))
      (fun as bs => pure (disjointCalls as bs)) a b = .ok true ↔
      bitsA a = false ∧ bitsB b = false ∧ emptyA a = false ∧ emptyB b = false ∧
        ∃ id, id ∈ idsA a ∧ id ∈ idsB b

theorem mightaliasSegments_proven : MightaliasSegments := by
  classical
  intro A B idsA idsB bitsA bitsB emptyA emptyB a b
  have hd := disjointCalls_correct (idsA a) (idsB b)
  cases hb₁ : bitsA a <;> cases hb₂ : bitsB b <;>
    cases he₁ : emptyA a <;> cases he₂ : emptyB b <;>
    simp [mightaliasArray, hb₁, hb₂, he₁, he₂]
  cases hr : disjointCalls (idsA a) (idsB b) with
  | false =>
    simp [hr] at hd ⊢
    exact hd
  | true =>
    simp [hr] at hd ⊢
    intro id ha hb
    exact hd id ha hb

/-! Nothing to promise:
mightalias@1604: the nonarray fallback has no mutable storage to compare.
dataids@1626: packages the supplied object identity as a singleton tuple.
dataids@1627: packages the converted storage pointer as a singleton tuple.
dataids@1628: forwards storage identity to the array's backing Memory object.
dataids@1629: ranges have no mutable data segments to list.
dataids@1630: the nonarray fallback has no mutable data segments to list.
-/

/-! ## Range defaults and element-type promotion -/

/-- Primitive adapters for one-based vector storage and UnitRange iteration.
The range positions returned by findall are themselves a UnitRange. -/
abbrev DefaultRange := I64 × I64
abbrev DefaultRangeM := StateT (List I64) Result

def rangeElements (r : DefaultRange) : List I64 :=
  (List.range (r.2.val - r.1.val + 1).toNat).map (fun k : Nat => int (r.1.val + (k : Int)))

def rangeAxes (a : List I64) : Result (List DefaultRange) :=
  pure [(int 1, int a.length)]

def rangePositions (test : I64 → DefaultRangeM Bool) (r : DefaultRange) :
    DefaultRangeM DefaultRange := do
  let indexed := (rangeElements r).zipIdx
  let matched ← indexed.filterM (fun p => test p.1)
  let positions := matched.map (fun p => int (p.2 + 1))
  return (positions.headD (int 1), positions.getLastD (int 0))

def rangeSelect (a : List I64) (r : DefaultRange) : Result (List I64) :=
  (rangeElements r).mapM (tupleGet a)

def rangeAssign (_ : Unit) (r : DefaultRange) (values : List I64) : DefaultRangeM Unit :=
  modify fun a => ((rangeElements r).zip values).foldl
    (fun a p => a.set (p.1.val - 1).toNat p.2) a

/-- The external scalar-to-range assignment primitive rejects indexed
assignment of a single Int to many locations, including an empty range. -/
def scalarRangeAssign (_ : Unit) (_r : DefaultRange) (_x : I64) : DefaultRangeM Unit :=
  throw (.julia (.argumentError
    "indexed assignment with a single value to possibly many locations is not supported; perhaps use broadcasting `.=` instead?"))

def defaultVectorGet (x : Unit) (a : List I64) (r : DefaultRange) (d : I64) :
    DefaultRangeM Unit :=
  getVectorRange
    (fun a => StateT.lift (axes1 rangeAxes a))
    (fun ax i => pure (decide (ax.1.val ≤ i.val ∧ i.val ≤ ax.2.val)))
    rangePositions
    (fun r positions => StateT.lift (rangeSelect (rangeElements r) positions))
    (fun a selected => StateT.lift (selected.mapM (tupleGet a)))
    rangeAssign
    (fun _ => do StateT.lift (axes1 rangeAxes (← get)))
    (fun ax => pure ax.1) (fun ax => pure ax.2)
    (fun ind => pure ind.1) (fun ind => pure ind.2)
    (fun lo hi => pure (lo, hi)) scalarRangeAssign x a r d

def defaultVectorRange (a : List I64) (r : DefaultRange) (d : I64) :
    Result (List I64) :=
  ((getRangeDefault (fun _ : I64 => ()) (fun r => pure (rangeElements r).length)
    (fun _ _ n => do set (List.replicate n (int 0)); pure ())
    defaultVectorGet a r d).run []).map Prod.snd

/-- Range reads return one value per requested index, using the default
exactly at out-of-bounds positions. This includes ordinary dense vectors. -/
def RangeDefaultValues : Prop :=
  ∀ (a : List I64) (r : DefaultRange) (d : I64),
    defaultVectorRange a r d = .ok ((rangeElements r).map fun i =>
      if 1 ≤ i.val then a[(i.val - 1).toNat]?.getD d else d)

set_option maxRecDepth 4096 in
theorem rangeDefaultValues_refuted : ¬ RangeDefaultValues := by
  intro h
  have bad := h [int 10, int 20] (int 0, int 3) (int 99)
  have error : defaultVectorRange [int 10, int 20] (int 0, int 3) (int 99) =
      .error (.julia (.argumentError
        "indexed assignment with a single value to possibly many locations is not supported; perhaps use broadcasting `.=` instead?")) := by decide
  rw [error] at bad
  cases bad

/-- The failure also affects a wholly in-bounds range on an ordinary vector. -/
def RangeDefaultOrdinaryValues : Prop :=
  ∀ (a : List I64) (d : I64),
    defaultVectorRange a (int 1, int a.length) d = .ok a

set_option maxRecDepth 4096 in
theorem rangeDefaultOrdinaryValues_refuted : ¬ RangeDefaultOrdinaryValues := by
  intro h
  have bad := h [int 10, int 20] (int 99)
  change defaultVectorRange [int 10, int 20] (int 1, int 2) (int 99) = .ok [int 10, int 20] at bad
  have error : defaultVectorRange [int 10, int 20] (int 1, int 2) (int 99) =
      .error (.julia (.argumentError
        "indexed assignment with a single value to possibly many locations is not supported; perhaps use broadcasting `.=` instead?")) := by decide
  rw [error] at bad
  cases bad

def EmptyPromotionRejected : Prop :=
  ∀ Ty : Type,
    promoteEltypeofEmpty (Ty := Ty) = .error (.errorException "") ∧
    promoteEltypeEmpty (Ty := Ty) = .error (.errorException "")

theorem emptyPromotionRejected_proven : EmptyPromotionRejected := by
  intro Ty
  exact ⟨rfl, rfl⟩

/-! Nothing to promise:
get@1662: delegates shape calculation and allocation, then forwards to the appropriate get! method.
get@1671: delegates shape calculation and allocation, then forwards to the appropriate get! method.
replace_in_print_matrix@1675: supplies the unchanged string when no matrix display substitution is needed.
replace_in_print_matrix@1676: supplies the unchanged string when no vector display substitution is needed.
eltypeof@1679: forwards scalar type selection to typeof.
eltypeof@1680: forwards array element-type selection to eltype.
promote_eltypeof@1683: forwards the single argument to eltypeof.
promote_eltypeof@1684: delegates both type queries and their promotion.
promote_eltypeof@1685: delegates the promotion fold and each type query to afoldl and promote_type.
promote_eltypeof@1686: forwards the shared concrete type's element-type query once.
promote_eltypeof@1687: supplies the shared element-type parameter.
promote_eltype@1690: forwards the single argument to eltype.
promote_eltype@1691: delegates both type queries and their promotion.
promote_eltype@1692: delegates the promotion fold and each type query to afoldl and promote_type.
promote_eltype@1693: forwards the shared concrete type's element-type query once.
promote_eltype@1694: supplies the shared element-type parameter.
_cat@1697: delegates construction of an empty Any vector.
-/

def vectorFirst (a : List I64) : Result I64 :=
  firstArray (eachindexVector (axes1 rangeAxes)) (fun r => pure r.1) tupleGet a

def vectorLast (a : List I64) : Result I64 :=
  last (lastindexArray (eachindexLinearVector (axes1 rangeAxes)) (fun r => pure r.2)) tupleGet a

def vectorPositions (test : I64 → DefaultRangeM Bool) (is : List I64) :
    DefaultRangeM (List I64) := do
  let matched ← is.zipIdx.filterM (fun p => test p.1)
  return matched.map (fun p => int (p.2 + 1))

def vectorAssign (_ : Unit) (indices values : List I64) : DefaultRangeM Unit :=
  modify fun a => (indices.zip values).foldl
    (fun a p => a.set (p.1.val - 1).toNat p.2) a

def arrayScatteredGet (a is : List I64) (d : I64) : DefaultRangeM Unit :=
  getArrayRange
    (fun a => pure (int a.length)) (fun lo hi => pure (lo, hi))
    (fun r i => pure (decide (r.1.val ≤ i.val ∧ i.val ≤ r.2.val)))
    vectorPositions
    (fun is positions => StateT.lift (positions.mapM (tupleGet is)))
    (fun a selected => StateT.lift (selected.mapM (tupleGet a))) vectorAssign
    (fun positions => StateT.lift (vectorFirst positions))
    (fun positions => StateT.lift (vectorLast positions))
    (fun _ => do return int (← get).length)
    (fun _ r => pure r)
    (fun r d => rangeAssign () r (List.replicate (rangeElements r).length d))
    () a is d

def scatteredDefaultResult (a is : List I64) (d : I64) (initial : List I64) :
    Result (List I64) := ((arrayScatteredGet a is d).run initial).map Prod.snd

def ScatteredDefaultValues : Prop :=
  ∀ (a is : List I64) (d : I64) (initial : List I64), initial.length = is.length →
    scatteredDefaultResult a is d initial = .ok (is.map fun i =>
      if 1 ≤ i.val then a[(i.val - 1).toNat]?.getD d else d)

set_option maxRecDepth 4096 in
theorem scatteredDefaultValues_refuted : ¬ ScatteredDefaultValues := by
  intro h
  have bad := h [int 10, int 20] [int 1, int 5, int 2] (int 99)
    [int (-1), int (-1), int (-1)] rfl
  have actual : scatteredDefaultResult [int 10, int 20] [int 1, int 5, int 2] (int 99)
      [int (-1), int (-1), int (-1)] = .ok [int 10, int (-1), int 20] := by decide
  rw [actual] at bad
  have expected : ([int 1, int 5, int 2].map fun i =>
      if 1 ≤ i.val then [int 10, int 20][(i.val - 1).toNat]?.getD (int 99) else int 99) =
      [int 10, int 99, int 20] := by decide
  rw [expected] at bad
  have different : (Except.ok [int 10, int (-1), int 20] : Result (List I64)) ≠
      .ok [int 10, int 99, int 20] := by decide
  exact different bad

/-- A bulk indexed read fills every destination cell with either its matched
source value or the default. The laws describe the external indcopy, read,
fill, and assignment operations, with no condition on where matches occur. -/
def IndexListDefaultContents : Prop :=
  ∀ (Q E A I Shape Dst Src Values : Type)
    (size : A → Result Shape) (indcopy : Shape → I → Result (Dst × Src))
    (read : A → Src → Result Values)
    (fill : Unit → E → StateT (Heap Q E) Result Unit)
    (assign : Unit → Dst → Values → StateT (Heap Q E) Result Unit)
    (a : A) (is : I) (shape : Shape) (dst : Dst) (src : Src) (values : Values)
    (reference : Q → Option E) (default : E) (h : Heap Q E),
    size a = .ok shape → indcopy shape is = .ok (dst, src) → read a src = .ok values →
    (∀ heap, (fill () default).run heap = .ok ((), fun _ => default)) →
    (∀ heap, (assign () dst values).run heap =
      .ok ((), fun q => (reference q).getD (heap q))) →
    ∃ h', (getIndexList fill (fun a => StateT.lift (size a))
      (fun shape is => StateT.lift (indcopy shape is))
      (fun a src => StateT.lift (read a src)) assign () a is default).run h =
      .ok ((), h') ∧ ∀ q, h' q = (reference q).getD default

theorem indexListDefaultContents_proven : IndexListDefaultContents := by
  intro Q E A I Shape Dst Src Values size indcopy read fill assign a is shape dst src
    values reference default h hs hi hr hf ha
  simp only [StateT.run] at hf ha
  refine ⟨fun q => (reference q).getD default, ?_, fun _ => rfl⟩
  simp [getIndexList, StateT.run, StateT.bind, StateT.pure, StateT.lift, hf, hs, hi, hr, ha]

def sourceMightalias {D A : Type} (bitsD emptyD : D → Bool) (bitsA emptyA : A → Bool)
    (idsD : D → List (JInt .u64)) (idsA : A → List (JInt .u64)) : D → A → Result Bool :=
  mightaliasArray (fun d => pure (bitsD d)) (fun a => pure (bitsA a))
    (fun d => pure (emptyD d)) (fun a => pure (emptyA a))
    (fun d => pure (idsD d)) (fun a => pure (idsA a))
    (fun ds as => pure (disjointCalls ds as))

def aliasingSegments {D A : Type} (bitsD emptyD : D → Bool) (bitsA emptyA : A → Bool)
    (idsD : D → List (JInt .u64)) (idsA : A → List (JInt .u64)) (d : D) (a : A) : Prop :=
  bitsD d = false ∧ bitsA a = false ∧ emptyD d = false ∧ emptyA a = false ∧
    ∃ id, id ∈ idsD d ∧ id ∈ idsA a

def SourceUnaliasSeparation : Prop :=
  ∀ (D A E : Type) (values : A → List E)
    (bitsD emptyD : D → Bool) (bitsA emptyA : A → Bool)
    (idsD : D → List (JInt .u64)) (idsA : A → List (JInt .u64))
    (copy : A → Result A),
    (∀ d a, aliasingSegments bitsD emptyD bitsA emptyA idsD idsA d a →
      ∃ b, copy a = .ok b ∧ values b = values a ∧
        ¬ aliasingSegments bitsD emptyD bitsA emptyA idsD idsA d b) →
    ∀ d a, ∃ b,
      unaliasArray (sourceMightalias bitsD emptyD bitsA emptyA idsD idsA)
        (unaliascopyArray copy (fun a c => pure (unaliascopySame a c)) (fun c => pure c)) d a =
        .ok b ∧ values b = values a ∧
        ¬ aliasingSegments bitsD emptyD bitsA emptyA idsD idsA d b ∧
        (¬ aliasingSegments bitsD emptyD bitsA emptyA idsD idsA d a → b = a)

theorem sourceUnaliasSeparation_proven : SourceUnaliasSeparation := by
  intro D A E values bitsD emptyD bitsA emptyA idsD idsA copy hc d a
  have iffAlias : sourceMightalias bitsD emptyD bitsA emptyA idsD idsA d a = .ok true ↔
      aliasingSegments bitsD emptyD bitsA emptyA idsD idsA d a :=
    mightaliasSegments_proven D A idsD idsA bitsD bitsA emptyD emptyA d a
  have total : ∃ bit,
      sourceMightalias bitsD emptyD bitsA emptyA idsD idsA d a = .ok bit := by
    cases hd : bitsD d <;> cases ha : bitsA a <;>
      cases heD : emptyD d <;> cases heA : emptyA a <;>
      simp [sourceMightalias, mightaliasArray, hd, ha, heD, heA]
  obtain ⟨bit, hb⟩ := total
  cases bit with
  | false =>
    have hn : ¬ aliasingSegments bitsD emptyD bitsA emptyA idsD idsA d a := by
      intro h
      have := iffAlias.mpr h
      rw [hb] at this
      cases this
    exact ⟨a, by simp [unaliasArray, hb], rfl, hn, fun _ => rfl⟩
  | true =>
    have h := iffAlias.mp hb
    obtain ⟨b, hr, hv, hn⟩ := hc d a h
    refine ⟨b, ?_, hv, hn, fun hnot => False.elim (hnot h)⟩
    simp [unaliasArray, hb, unaliascopyArray, unaliascopySame, hr]

def sourceZeroLinearRead {A Lin E : Type} (check : A → List I64 → Result Unit)
    (linearIndices : A → Result Lin) (first : Lin → Result I64)
    (get : A → I64 → Result E) (a : A) : Result E :=
  getindexArray (fun _ => pure ()) errorCanonicalGetindexOther
    (fun _ (_ : Unit) => pure ([] : List I64))
    (fun _ a is => getindexLinear check
      (fun a _ => toLinearEmpty linearIndices first a) get a is) a ()

def sourceZeroLinearWrite {A Lin E R : Type} (check : A → List I64 → Result Unit)
    (linearIndices : A → Result Lin) (first : Lin → Result I64)
    (set : A → E → I64 → Result R) (a : A) (v : E) : Result R :=
  setindexArray (fun _ => pure ()) errorCanonicalSetindexOther
    (fun _ (_ : Unit) => pure ([] : List I64))
    (fun _ a v is => setindexLinear check
      (fun a _ => toLinearEmpty linearIndices first a) set a v is) a v ()

/-- Ordinary singleton linear arrays select their sole element at index one.
The external LinearIndices, throwing bounds check, and canonical accesses obey
their documented interfaces; all AbstractArray forwarding is the source code. -/
def OrdinaryLinearZero : Prop :=
  ∀ (A Axis Lin E R : Type) (axes : A → Result (List Axis)) (length : Axis → I64)
    (linearIndices : A → Result Lin) (first : Lin → Result I64)
    (check : A → List I64 → Result Unit) (valid : A → I64 → Prop)
    (element : A → I64 → E) (updated : A → E → I64 → R)
    (get : A → I64 → Result E) (set : A → E → I64 → Result R),
    (∀ a i, valid a i → get a i = .ok (element a i)) →
    (∀ a v i, valid a i → set a v i = .ok (updated a v i)) →
    ∀ (a : A) (axs : List Axis) (lin : Lin),
    axes a = .ok axs → (∀ ax ∈ axs, (length ax).val = 1) →
    linearIndices a = .ok lin → first lin = .ok (int 1) →
    valid a (int 1) → check a [] = .ok () →
    sourceZeroLinearRead check linearIndices first get a = .ok (element a (int 1)) ∧
    (∀ d, getDefaultEmpty
      (fun a => checkboundsMany axes
        (fun axs (_ : List I64) => checkboundsIndicesNil (fun ax => pure (length ax)) axs) a [])
      (sourceZeroLinearRead check linearIndices first get) a d =
      .ok (element a (int 1))) ∧
    (∀ v, sourceZeroLinearWrite check linearIndices first set a v =
      .ok (updated a v (int 1))) ∧
    (∀ (typeof : A → String) (i : I64),
      errorCanonicalSetindexLinear typeof a i = .error (.canonicalIndex "setindex!" (typeof a)))

theorem ordinaryLinearZero_proven : OrdinaryLinearZero := by
  intro A Axis Lin E R axes length linearIndices first check valid element updated
    get set hg hs a axs lin ha hsingle hl hf hv hc
  have hget := hg a (int 1) hv
  have hbounds := omittedSingletonBounds_proven Axis length axs
  have hdec : decide (∀ ax ∈ axs, (length ax).val = 1) = true := by
    simp only [decide_eq_true_eq]
    exact hsingle
  have hb : checkboundsIndicesNil (fun ax => Except.ok (length ax)) axs = .ok true := by
    rw [hdec] at hbounds
    exact hbounds
  have hr : sourceZeroLinearRead check linearIndices first get a =
      .ok (element a (int 1)) := by
    simp [sourceZeroLinearRead, getindexArray, errorCanonicalGetindexOther,
      getindexLinear, toLinearEmpty, hc, hl, hf, hget]
  refine ⟨hr, ?_, ?_, ?_⟩
  · intro d
    simp [getDefaultEmpty, checkboundsMany, ha, hb, hr]
  · intro v
    simp [sourceZeroLinearWrite, setindexArray, errorCanonicalSetindexOther,
      setindexLinear, toLinearEmpty, hc, hl, hf, hs a v (int 1) hv]
  · intro typeof i
    rfl

/-- These instances use the actual canonical guard and both zero-coordinate
conversion methods. The throwing bounds checker is an external interface. -/
def SourceWriteChecks : Prop :=
  (∀ (A V R : Type) (typeof : A → String) (convert : A → I64 → Result I64)
    (set : A → V → I64 → Result R) (a : A) (v : V) (i : I64),
    setindexArray (fun _ => pure ())
      (fun _ => errorCanonicalSetindexLinear typeof) convert
      (fun _ => setindexLinearScalar set) a v i =
      .error (.canonicalIndex "setindex!" (typeof a))) ∧
  (∀ (A V R Lin Axis : Type) (check : A → List I64 → Result Unit)
    (linearIndices : A → Result Lin) (firstLinear : Lin → Result I64)
    (axes : A → Result (List Axis)) (firstAxis : Axis → Result I64)
    (setLinear : A → V → I64 → Result R)
    (setCartesian : A → V → List I64 → Result R)
    (a : A) (v : V) (e : ArrayError), check a [] = .error e →
    setindexLinear check (fun a _ => toLinearEmpty linearIndices firstLinear a)
      setLinear a v [] = .error e ∧
    setindexCartesian check (fun a _ => toSubscriptsEmpty axes firstAxis a)
      setCartesian a v [] = .error e)

theorem sourceWriteChecks_proven : SourceWriteChecks := by
  constructor
  · intro A V R typeof convert set a v i
    rfl
  · intro A V R Lin Axis check linearIndices firstLinear axes firstAxis setLinear
      setCartesian a v e h
    exact writeChecks_proven.2 A V (List I64) R check
      (fun a _ => toLinearEmpty linearIndices firstLinear a)
      (fun a _ => toSubscriptsEmpty axes firstAxis a) setLinear setCartesian a v [] e h

/-! ## Scalar concatenation and fill order -/

theorem tupleMapM_values {X E : Type} (get : X → I64 → Result E)
    (x : X) (value : I64 → E) (is : List I64)
    (law : ∀ i, get x i = .ok (value i)) :
    is.mapM (get x) = .ok (is.map value) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [List.mapM_cons, law, ih]

/-- Homogeneous scalar concatenation preserves the argument order, including
empty argument tuples, with one row for horizontal concatenation. -/
def ScalarComprehensionContents : Prop :=
  ∀ (X E A Ty : Type) (eachindex : X → Result (List I64))
    (get : X → I64 → Result E) (vector : Ty → List E → Result A)
    (matrix : Ty → I64 → List E → Result A) (contents : A → List E)
    (rows : A → I64) (makeV : Ty → List E → A) (makeH : Ty → List E → A),
    (∀ t es, vector t es = .ok (makeV t es)) →
    (∀ t es, matrix t (int 1) es = .ok (makeH t es)) →
    (∀ t es, contents (makeV t es) = es) →
    (∀ t es, contents (makeH t es) = es ∧ rows (makeH t es) = int 1) →
    ∀ (t : Ty) (x : X) (is : List I64) (value : I64 → E),
    eachindex x = .ok is → (∀ i, get x i = .ok (value i)) →
    (vcatSame eachindex get vector t x).map contents = .ok (is.map value) ∧
    (vcatSameNumbers eachindex get vector t x).map contents = .ok (is.map value) ∧
    (hcatSame eachindex get matrix t x).map (fun a => (rows a, contents a)) =
      .ok (int 1, is.map value) ∧
    (hcatSameNumbers eachindex get matrix t x).map (fun a => (rows a, contents a)) =
      .ok (int 1, is.map value)

theorem scalarComprehensionContents_proven : ScalarComprehensionContents := by
  intro X E A Ty eachindex get vector matrix contents rows makeV makeH hv hh cv ch
    t x is value hi hg
  have hm := tupleMapM_values get x value is hg
  simp [vcatSame, vcatSameNumbers, hcatSame, hcatSameNumbers, hi, hm, hv, hh,
    cv, (ch t (is.map value)).1, (ch t (is.map value)).2, Except.map]

def TypedEmptyContents : Prop :=
  ∀ (A Ty E : Type) (vector : Ty → Result A) (contents : A → List E),
    (∀ t, (vector t).map contents = .ok []) →
    ∀ t, (typedVcatEmpty vector t).map contents = .ok [] ∧
      (typedHcatEmpty vector t).map contents = .ok []

theorem typedEmptyContents_proven : TypedEmptyContents := by
  intro A Ty E vector contents law t
  exact ⟨law t, law t⟩

def TypedHcatRequiresType : Prop :=
  ∀ (A Other B : Type) (a : A) (other : Other),
    ∃ message, typedHcatNotType (B := B) a other =
      .error (.julia (.argumentError message))

theorem typedHcatRequiresType_proven : TypedHcatRequiresType := by
  intro A Other B a other
  exact ⟨_, rfl⟩

abbrev WriteTrace (E : Type) := List (I64 × E)

def traceWrite {E : Type} (_ : A) (i : I64) (e : E) :
    StateT (WriteTrace E) Result Unit := fun log => .ok ((), log ++ [(i, e)])

theorem traceWriteLoop {E : Type} (is : List I64) (value : I64 → E)
    (log : WriteTrace E) :
    (do
      for i in is do traceWrite () i (value i)
      pure () : StateT (WriteTrace E) Result Unit).run log =
      .ok ((), log ++ is.map (fun i => (i, value i))) := by
  induction is generalizing log with
  | nil => simp [List.forIn_nil, StateT.run, StateT.pure, StateT.bind]
  | cons i is ih =>
    simpa [List.forIn_cons, traceWrite, StateT.run, StateT.bind, StateT.pure,
      List.append_assoc] using ih (log ++ [(i, value i)])

def concatRange (lo hi : I64) : List I64 :=
  (List.range (hi.val - lo.val + 1).toNat).map fun (k : Nat) => int (lo.val + k)

/-- These external Array operations record writes without hiding a source
loop. Both the generated and interpreter paths call the source fill bodies. -/
def sourceTraceFill {E : Type} (generated : Bool) (count rank : Nat)
    (size : Unit → I64 → I64) (tailProduct : Unit → I64)
    (len : I64) (is : List I64) (value : I64 → E) :
    Unit → Bool → Unit → StateT (WriteTrace E) Result Unit :=
  hvncatFill generated count rank
    (fun a i => pure (size a i)) (fun a => pure (tailProduct a))
    (fun _ => pure "") (fun _ i => pure (value i)) traceWrite
    (fun _ i j e => traceWrite () (i + (j - int 1) * size () (int 1)) e)
    (hvncatFillLoop (fun a i => pure (size a i)) (fun a => pure (tailProduct a))
      (fun _ => pure len) (fun _ => pure "") (fun lo hi => pure (concatRange lo hi))
      (fun _ => pure is) (fun _ i => pure (value i)) traceWrite)

def ScalarFillOrder : Prop :=
  ∀ (E : Type) (size : Unit → I64 → I64) (tailProduct : Unit → I64)
    (len : I64) (is : List I64) (value : I64 → E) (log : WriteTrace E)
    (count rank : Nat),
    ((size () (int 1) * size () (int 2)) * tailProduct ()).val = len.val →
    (sourceTraceFill false count rank size tailProduct len is value () false ()).run log =
      .ok ((), log ++ is.map (fun i => (i, value i)))

theorem scalarFillOrder_proven : ScalarFillOrder := by
  intro E size tailProduct len is value log count rank shape
  simp only [sourceTraceFill, hvncatFill, hvncatFillLoop, pure_bind]
  simpa [shape, StateT.run, StateT.bind, StateT.pure] using traceWriteLoop is value log

/-- Numeric vcat/hcat, including explicitly typed variants, write the scalar
tuple once in order. Allocators supply the specified shape and native length;
all filling runs through both source-mirrored fill methods. -/
def NumericConcatOrder : Prop :=
  ∀ (E Ty : Type) (t : Ty) (size : Unit → I64 → I64)
    (tailProduct : Unit → I64) (len : I64) (is : List I64)
    (value : I64 → E) (log : WriteTrace E),
    ((size () (int 1) * size () (int 2)) * tailProduct ()).val = len.val →
    let fill := sourceTraceFill false is.length 2 size tailProduct len is value
    let vector : Ty → I64 → StateT (WriteTrace E) Result Unit := fun _ _ => pure ()
    let matrix : Ty → I64 → I64 → StateT (WriteTrace E) Result Unit := fun _ _ _ => pure ()
    let expected : Result (Unit × WriteTrace E) :=
      .ok ((), log ++ is.map (fun i => (i, value i)))
    (vcatNumbers (fun _ : Unit => pure t) (fun _ => pure len)
      vector fill ()).run log = expected ∧
    (hcatNumbers (fun _ : Unit => pure t) (fun _ => pure len)
      matrix fill ()).run log = expected ∧
    (typedVcatNumbers (fun _ : Unit => pure len) vector fill t ()).run log = expected ∧
    (typedHcatNumbers (fun _ : Unit => pure len) matrix fill t ()).run log = expected

theorem numericConcatOrder_proven : NumericConcatOrder := by
  intro E Ty t size tailProduct len is value log shape
  have hf := scalarFillOrder_proven E size tailProduct len is value log is.length 2 shape
  simp only [StateT.run] at hf
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [vcatNumbers, hcatNumbers, typedVcatNumbers, typedHcatNumbers,
      StateT.run, StateT.bind, StateT.pure, hf]

/-- For dense Array interfaces, a differing second block is rejected before
allocation or copying. Rank comes from the source ndims method. -/
def ConcatMismatchRejected : Prop :=
  (∀ (V A B Ty R : Type) (length : V → Result I64)
    (get : V → I64 → Result A) (size : A → I64 → Result I64)
    (rank : A → I64) (isArray isMatrix : A → Bool)
    (range : I64 → I64 → Result (List I64)) (showRows : V → Result String)
    (similar : A → Ty → I64 → I64 → Result B)
    (lengthA : A → Result I64)
    (copyDense : B → I64 → A → I64 → I64 → Result B)
    (slice : I64 → I64 → Result R) (setDense : B → R → A → Result Unit)
    (t : Ty) (as : V) (n j rows otherRows cols : I64) (rest : List I64)
    (a b : A) (message : String),
    length as = .ok n → get as (int 1) = .ok a →
    size a (int 1) = .ok rows → size a (int 2) = .ok cols →
    range (int 1) n = .ok (int 1 :: j :: rest) →
    get as j = .ok b → size b (int 1) = .ok otherRows →
    otherRows.val ≠ rows.val → showRows as = .ok message →
    typedHcat length get size (fun a => pure (ndimsValue (rank a) a))
      isArray isMatrix range showRows similar lengthA copyDense slice setDense t as =
      .error (.dimensionMismatch
        ("number of rows of each array must match (got " ++ message ++ ")"))) ∧
  (∀ (V A B Ty R : Type) (length : V → Result I64)
    (get : V → I64 → Result A) (size : A → I64 → Result I64)
    (sum : (A → Result I64) → V → Result I64)
    (range : I64 → I64 → Result (List I64)) (showCols : V → Result String)
    (similar : A → Ty → I64 → I64 → Result B)
    (slice : I64 → I64 → Result R) (setDense : B → R → A → Result Unit)
    (t : Ty) (as : V) (n j rows cols otherCols : I64) (rest : List I64)
    (a b : A) (message : String),
    length as = .ok n → sum (fun a => size a (int 1)) as = .ok rows →
    get as (int 1) = .ok a → size a (int 2) = .ok cols →
    range (int 2) n = .ok (j :: rest) → get as j = .ok b →
    size b (int 2) = .ok otherCols → otherCols.val ≠ cols.val →
    showCols as = .ok message →
    typedVcat length get size sum range showCols similar slice setDense t as =
      .error (.dimensionMismatch
        ("number of columns of each array must match (got " ++ message ++ ")")))

theorem concatMismatchRejected_proven : ConcatMismatchRejected := by
  constructor
  · intro V A B Ty R length get size rank isArray isMatrix range showRows similar
      lengthA copyDense slice setDense t as n j rows otherRows cols rest a b message
      hn ha hrows hcols hr hb hother hne hm
    by_cases two : (rank a).val = 2
    · simp [typedHcat, hn, ha, hrows, hcols, hr, hb, hother, hne, hm,
        List.forIn_cons, ndimsValue, two]
      rfl
    · simp [typedHcat, hn, ha, hrows, hcols, hr, hb, hother, hne, hm,
        List.forIn_cons, ndimsValue, two]
      rfl
  · intro V A B Ty R length get size sum range showCols similar slice setDense
      t as n j rows cols otherCols rest a b message hn hs ha hcols hr hb hother hne hm
    simp [typedVcat, hn, hs, ha, hcols, hr, hb, hother, hne, hm, List.forIn_cons]
    rfl

/-- Dispatch by tuple emptiness, invoking each source _cshp method. Recursive
closures call only this dispatcher on the tails supplied by the source body. -/
def cshpCalls (ndim : I64) (dims : List Bool) (shape nshape : List I64) :
    Result (List I64) :=
  match dims, shape, nshape with
  | [], [], [] => pure (cshpEmpty ndim)
  | [], [], nshape => pure (cshpInitial ndim nshape)
  | dims, [], [] => pure (cshpPad ndim dims)
  | d :: ds, a :: as, [] =>
      cshpTrailing (fun n _ _ _ => cshpCalls n ds as []) ndim (d, ds) (a, as)
  | d :: ds, [], b :: bs =>
      cshpLeading (fun n _ _ _ => cshpCalls n ds [] bs) ndim (d, ds) (b, bs)
  | [], a :: as, [] =>
      cshpMissing catCheckDim (fun n _ _ _ => cshpCalls n [] as []) ndim (a, as)
  | [], a :: as, b :: bs =>
      cshpEqual catCheckDim (fun n _ _ _ => cshpCalls n [] as bs) ndim (a, as) (b, bs)
  | d :: ds, a :: as, b :: bs =>
      cshpMerge catCheckDim (fun n _ _ _ => cshpCalls n ds as bs)
        ndim (d, ds) (a, as) (b, bs)
termination_by dims.length + shape.length + nshape.length

theorem cshpCalls_rank (ndim : I64) (dims : List Bool) (shape nshape out : List I64)
    (h : cshpCalls ndim dims shape nshape = .ok out) :
    out.length = max dims.length (max shape.length nshape.length) := by
  cases dims with
  | nil =>
    cases shape with
    | nil =>
      cases nshape with
      | nil =>
        simp [cshpCalls, cshpEmpty] at h
        subst out
        rfl
      | cons b bs =>
        simp [cshpCalls, cshpInitial] at h
        subst out
        simp
    | cons a as =>
      cases nshape with
      | nil =>
        cases hr : cshpCalls (ndim + int 1) [] as [] with
        | error e => simp [cshpCalls, cshpMissing, catCheckDim, hr] at h; split at h <;> cases h
        | ok tail =>
          have ih := cshpCalls_rank (ndim + int 1) [] as [] tail hr
          simp [cshpCalls, cshpMissing, catCheckDim, hr] at h
          split at h <;> cases h <;> simp_all
      | cons b bs =>
        cases hr : cshpCalls (ndim + int 1) [] as bs with
        | error e => simp [cshpCalls, cshpEqual, catCheckDim, hr] at h; split at h <;> cases h
        | ok tail =>
          have ih := cshpCalls_rank (ndim + int 1) [] as bs tail hr
          simp [cshpCalls, cshpEqual, catCheckDim, hr] at h
          split at h <;> cases h <;> simp_all
  | cons d ds =>
    cases shape with
    | nil =>
      cases nshape with
      | nil =>
        simp [cshpCalls, cshpPad] at h
        subst out
        simp
      | cons b bs =>
        cases hr : cshpCalls (ndim + int 1) ds [] bs with
        | error e => simp [cshpCalls, cshpLeading, hr] at h
        | ok tail =>
          have ih := cshpCalls_rank (ndim + int 1) ds [] bs tail hr
          simp [cshpCalls, cshpLeading, hr] at h
          subst out
          simp_all [Nat.succ_max_succ]
    | cons a as =>
      cases nshape with
      | nil =>
        cases hr : cshpCalls (ndim + int 1) ds as [] with
        | error e => simp [cshpCalls, cshpTrailing, hr] at h
        | ok tail =>
          have ih := cshpCalls_rank (ndim + int 1) ds as [] tail hr
          simp [cshpCalls, cshpTrailing, hr] at h
          subst out
          simp_all [Nat.succ_max_succ]
      | cons b bs =>
        cases hr : cshpCalls (ndim + int 1) ds as bs with
        | error e =>
          cases d <;> simp [cshpCalls, cshpMerge, catCheckDim, hr] at h
          split at h <;> cases h
        | ok tail =>
          have ih := cshpCalls_rank (ndim + int 1) ds as bs tail hr
          cases d <;> simp [cshpCalls, cshpMerge, catCheckDim, hr] at h
          · split at h <;> cases h <;> simp_all [Nat.succ_max_succ]
          · subst out; simp_all [Nat.succ_max_succ]
termination_by dims.length + shape.length + nshape.length

def ConcatShapeRank : Prop :=
  ∀ (ndim : I64) (dims : List Bool) (shape nshape out : List I64),
    cshpCalls ndim dims shape nshape = .ok out →
      out.length = max dims.length (max shape.length nshape.length)

theorem concatShapeRank_proven : ConcatShapeRank := cshpCalls_rank

def ConcatShapeMismatch : Prop :=
  ∀ (ndim : I64) (dims : List Bool) (a b : I64) (as bs : List I64),
    a ≠ b → ∃ message,
      cshpCalls ndim (false :: dims) (a :: as) (b :: bs) =
        .error (.dimensionMismatch message)

theorem concatShapeMismatch_proven : ConcatShapeMismatch := by
  intro ndim dims a b as bs h
  have ne : a.val ≠ b.val := fun e => h (Subtype.ext e)
  exact ⟨_, by simp [cshpCalls, cshpMerge, catCheckDim, ne]; rfl⟩

def InvalidCatDimensions : Prop :=
  ∀ (maximum : List I64 → Result I64)
    (ntuple : (I64 → Bool) → I64 → Result (List Bool)) (showDims : List I64 → String)
    (dims : List I64), (∃ d ∈ dims, d.val ≤ 0) →
    ∃ message, dimsToCat (fun p ds => pure (ds.any p)) maximum
      (fun i ds => decide (i ∈ ds)) ntuple showDims dims =
      .error (.julia (.argumentError message))

theorem invalidCatDimensions_proven : InvalidCatDimensions := by
  intro maximum ntuple showDims dims h
  have any : dims.any (fun d => decide (d.val ≤ 0)) = true := by
    rcases h with ⟨d, hd, hnonpos⟩
    exact List.any_eq_true.mpr ⟨d, hd, by simp [hnonpos]⟩
  exact ⟨_, by simp [dimsToCat, any]; rfl⟩

/-- On dimensions excluded from concatenation, every input shape (with
implicit singleton trailing dimensions) must equal the result shape. Scalar
arguments have the source cat_size shape [1]. -/
def CatShapeChecked : Prop :=
  ∀ (dims : List Bool) (shapes : List (List I64)) (out : List I64),
    catShape cshpCalls dims shapes = .ok out →
    ∀ shape ∈ shapes, ∀ i < out.length, dims[i]?.getD false = false →
      shape[i]?.getD (int 1) = out[i]?.getD (int 1)

set_option maxRecDepth 4096 in
theorem catShapeChecked_refuted : ¬ CatShapeChecked := by
  intro h
  have actual : catShape cshpCalls [true] [[int 1], [int 1, int 2]] =
      .ok [int 2, int 2] := by
    simp [catShape, cshpCalls, cshpLeading, cshpMerge, cshpInitial, cshpEmpty,
      List.forIn_cons, List.forIn_nil]
    rfl
  have bad := h [true] [[int 1], [int 1, int 2]] [int 2, int 2] actual
    [int 1] (by simp) 1 (by decide) (by decide)
  exact (by decide : int 1 ≠ int 2) bad

def dimensionErrorClass : ArrayError → Bool
  | .dimensionMismatch _ => true
  | _ => false

/-- Independent coordinatewise contract: absent dimensions are singleton,
concatenated coordinates add, and all other coordinates must agree. -/
def referenceCatShape (dims : List Bool) (shapes : List (List I64)) :
    Except Bool (List I64) :=
  let rank := max dims.length ((shapes.map List.length).foldl max 0)
  let first := shapes.headD []
  let compatible := (List.range rank).all fun i =>
    dims[i]?.getD false || shapes.all (fun shape =>
      decide (shape[i]?.getD (int 1) = first[i]?.getD (int 1)))
  if compatible then
    .ok ((List.range rank).map fun i =>
      if dims[i]?.getD false then
        int ((shapes.map (fun shape => (shape[i]?.getD (int 1)).val)).sum)
      else first[i]?.getD (int 1))
  else .error true

def CatShapeSpec : Prop :=
  ∀ (dims : List Bool) (shapes : List (List I64)), shapes ≠ [] →
    (∀ shape ∈ shapes, ∀ n ∈ shape, 0 ≤ n.val) →
    (catShape cshpCalls dims shapes).mapError dimensionErrorClass =
      referenceCatShape dims shapes

set_option maxRecDepth 4096 in
theorem catShapeSpec_refuted : ¬ CatShapeSpec := by
  intro h
  have bad := h [true] [[int 1], [int 1, int 2]] (by simp) (by decide)
  have actual : catShape cshpCalls [true] [[int 1], [int 1, int 2]] =
      .ok [int 2, int 2] := by
    simp [catShape, cshpCalls, cshpLeading, cshpMerge, cshpInitial, cshpEmpty,
      List.forIn_cons, List.forIn_nil]
    rfl
  have expected : referenceCatShape [true] [[int 1], [int 1, int 2]] =
      .error true := by rfl
  rw [actual, expected] at bad
  cases bad

def sourceShapeFrom (dims : List Bool) (shape : List I64) (shapes : List (List I64)) :
    Result (List I64) :=
  match shapes with
  | [] => pure (catSizeShapeDone dims shape)
  | next :: rest =>
      catSizeShapeMore (catSizeArray (fun shape : List I64 => pure shape)) cshpCalls
        (fun ds current _ => sourceShapeFrom ds current rest) dims shape next rest
termination_by shapes.length

def CatSizeShapeFromSpec : Prop :=
  ∀ (dims : List Bool) (shape : List I64) (shapes : List (List I64)),
    shapes ≠ [] → (∀ s ∈ shape :: shapes, ∀ n ∈ s, 0 ≤ n.val) →
    (sourceShapeFrom dims shape shapes).mapError dimensionErrorClass =
      referenceCatShape dims (shape :: shapes)

set_option maxRecDepth 4096 in
theorem catSizeShapeFromSpec_refuted : ¬ CatSizeShapeFromSpec := by
  intro h
  have bad := h [true] [int 1] [[int 1, int 2]] (by simp) (by decide)
  have actual : sourceShapeFrom [true] [int 1] [[int 1, int 2]] =
      .ok [int 2, int 2] := by
    simp [sourceShapeFrom, catSizeShapeMore, catSizeShapeDone, catSizeArray,
      cshpCalls, cshpMerge, cshpInitial]
    rfl
  have expected : referenceCatShape [true] [[int 1], [int 1, int 2]] =
      .error true := by rfl
  rw [actual, expected] at bad
  cases bad

def CatSizeAllIntegerSpec : Prop :=
  ∀ (shape : List I64) (d : Int), 1 ≤ d →
    catSizeDimArray
      (sizeDim (fun z : Int => liftJulia (JInt.convert .i64 z))
        (fun shape : List I64 => pure shape)) shape d =
      .ok (shape[(d - 1).toNat]?.getD (int 1))

theorem catSizeAllIntegerSpec_refuted : ¬ CatSizeAllIntegerSpec := by
  intro h
  have bad := h [] 9223372036854775808 (by decide)
  have actual : catSizeDimArray
      (sizeDim (fun z : Int => liftJulia (JInt.convert .i64 z))
        (fun shape : List I64 => pure shape)) [] 9223372036854775808 =
      .error (.julia (.inexactError "Int64")) := by decide
  rw [actual] at bad
  cases bad

structure ShapeAxis where
  last : I64

def sourceSimilarVarargs {A B : Type} (size : A → Result (List I64))
    (allocate : Type → List I64 → Result B) (a : A) (t : Type)
    (dims : List I64) : Result B :=
  match dims with
  | [] => similarType (axesDefault size (fun n => ShapeAxis.mk n))
      (similarOneTo
        (toShapeMixed (toShapeOneTo (fun ax : ShapeAxis => pure ax.last)
          (fun n => pure (toShapeInt n))))
        (similarFallback allocate)) a t
  | _ :: _ => similarTypeVarargs (similarFallback allocate) a t dims

def CatSimilarAbsVectorSpec : Prop :=
  ∀ (shape requested : List I64),
    (∀ n ∈ shape, 0 ≤ n.val) → (∀ n ∈ requested, 0 ≤ n.val) →
    catSimilarAbstractVector
      (sourceSimilarVarargs (fun shape : List I64 => pure shape)
        (fun _ dims => pure dims)) shape Unit requested = .ok requested

theorem catSimilarAbsVectorSpec_refuted : ¬ CatSimilarAbsVectorSpec := by
  intro h
  have bad := h [int 3] [] (by decide) (by simp)
  have actual : catSimilarAbstractVector
      (sourceSimilarVarargs (fun shape : List I64 => pure shape)
        (fun _ dims => pure dims)) [int 3] Unit [] = .ok [int 3] := by decide
  rw [actual] at bad
  cases bad

def PositiveDims2catValSpec : Prop :=
  ∀ (maximum : List I64 → Result I64)
    (ntuple : (I64 → Bool) → I64 → Result (List Bool)),
    (∀ f n, 0 ≤ n.val → ntuple f n =
      .ok ((List.range n.val.toNat).map (fun (k : Nat) => f (int ((k : Int) + 1))))) →
    ∀ (dims : List I64) (m : I64), maximum dims = .ok m → m ∈ dims →
    (∀ d ∈ dims, d.val ≤ m.val) → (∀ d ∈ dims, 1 ≤ d.val) →
    ∃ flags, dimsToCatVal
      (dimsToCat (fun p ds => pure (ds.any p)) maximum
        (fun i ds => decide (i ∈ ds)) ntuple (fun _ => "")) dims = .ok flags ∧
      (∀ d ∈ dims, d.val ≤ (flags.length : Int)) ∧
      (∃ d ∈ dims, d.val = (flags.length : Int)) ∧
      ∀ k : Nat, k < flags.length →
        flags[k]? = some (decide (int ((k : Int) + 1) ∈ dims))

theorem positiveDims2catValSpec_proven : PositiveDims2catValSpec := by
  intro maximum ntuple ht dims m hm hmem hmax hpos
  have mn : 0 ≤ m.val := by have := hpos m hmem; omega
  have any : dims.any (fun d => decide (d.val ≤ 0)) = false := by
    apply List.any_eq_false.mpr
    intro d hd
    have := hpos d hd
    simp only [decide_eq_true_eq]
    omega
  refine ⟨(List.range m.val.toNat).map (fun (k : Nat) => decide (int ((k : Int) + 1) ∈ dims)),
    ?_, ?_, ?_, ?_⟩
  · simp [dimsToCatVal, dimsToCat, any, hm, ht _ m mn]
  · intro d hd
    simpa [Int.toNat_of_nonneg mn] using hmax d hd
  · exact ⟨m, hmem, by simp [Int.toNat_of_nonneg mn]⟩
  · intro k hk
    simp only [List.length_map, List.length_range] at hk
    simp [List.getElem?_map, List.getElem?_range hk]

def Dims2catValSpec : Prop := InvalidCatDimensions ∧ PositiveDims2catValSpec

theorem dims2catValSpec_proven : Dims2catValSpec :=
  ⟨invalidCatDimensions_proven, positiveDims2catValSpec_proven⟩

def AllocationShapeContract {B : Type} (shapeOf : B → List I64)
    (cells : B → Nat) (shape : List I64) (result : Result B) : Prop :=
  ((∀ n ∈ shape, 0 ≤ n.val) → ∃ out, result = .ok out ∧
    shapeOf out = shape ∧ cells out = (shape.map (fun n => n.val.toNat)).prod) ∧
  ((∃ n ∈ shape, n.val < 0) → ∃ message,
    result = .error (.julia (.argumentError message)))

def CatSimilarAllocationShapes : Prop :=
  ∀ (A B Ty : Type) (allocateTuple allocateVector : Ty → List I64 → Result B)
    (shapeOf : B → List I64) (cells : B → Nat),
    (∀ t shape, AllocationShapeContract shapeOf cells shape (allocateTuple t shape)) →
    (∀ t shape, AllocationShapeContract shapeOf cells shape (allocateVector t shape)) →
    ∀ (a : A) (t : Ty) (shape : List I64),
    AllocationShapeContract shapeOf cells shape (catSimilarTuple allocateTuple a t shape) ∧
    AllocationShapeContract shapeOf cells shape (catSimilarVector allocateVector a t shape) ∧
    AllocationShapeContract shapeOf cells shape (catSimilarArrayTuple allocateTuple a t shape) ∧
    AllocationShapeContract shapeOf cells shape (catSimilarArrayVector allocateVector a t shape)

theorem catSimilarAllocationShapes_proven : CatSimilarAllocationShapes := by
  intro A B Ty allocateTuple allocateVector shapeOf cells ht hv a t shape
  exact ⟨ht t shape, hv t shape, ht t shape, hv t shape⟩

def CatMetadataInvariants : Prop :=
  (∀ (A : Type) (axes : A → List (Int × Int)) (size : A → Result (List I64)),
    (∀ a, (size a).map (List.map Subtype.val) =
      .ok ((axes a).map (fun axis => max 0 (axis.2 - axis.1 + 1)))) →
    ∀ a, (catSizeArray size a).map (List.map Subtype.val) =
      .ok ((axes a).map (fun axis => max 0 (axis.2 - axis.1 + 1)))) ∧
  (∀ (A E : Type) (values : A → List E) (length : A → Result I64),
    (∀ a, (length a).map Subtype.val = .ok (values a).length) →
    ∀ a, (catLengthArray length a).map Subtype.val = .ok (values a).length) ∧
  (∀ (A Axis : Type) (axes : A → List Axis) (rank : A → I64),
    (∀ a, (rank a).val = (axes a).length) →
    ∀ a, (catNdimsArray (fun a => pure (ndimsValue (rank a) a)) a).map Subtype.val =
      .ok (axes a).length)

theorem catMetadataInvariants_proven : CatMetadataInvariants := by
  refine ⟨?_, ?_, ?_⟩
  · intro A axes size law a
    exact law a
  · intro A E values length law a
    exact law a
  · intro A Axis axes rank law a
    simp [catNdimsArray, ndimsValue, Except.map, law]

def EmptyConcatShapeZeros : Prop :=
  ∀ dims : List Bool, (catSizeShapeEmpty dims).length = dims.length ∧
    ∀ i, i < dims.length → (catSizeShapeEmpty dims)[i]? = some (int 0)

theorem emptyConcatShapeZeros_proven : EmptyConcatShapeZeros := by
  intro dims
  constructor
  · simp [catSizeShapeEmpty]
  · intro i hi
    simp [catSizeShapeEmpty, hi]

/-- Native unit-range axes are represented by their first index and length. -/
def sourceSubscriptRanges (axes : List (I64 × I64)) (stride index : I64)
    (is : List I64) : Result I64 :=
  match axes, is with
  | _, [] => pure (sub2indRecurseDone axes stride index)
  | [], i :: is =>
      sub2indRecurseEmpty (fun a b : I64 => pure (a - b))
        (fun a b : I64 => pure (a * b)) (fun a b : I64 => pure (a + b))
        (fun _ l j _ => sourceSubscriptRanges [] l j is) stride index i is
  | r :: rs, i :: is =>
      sub2indRecurse (fun xs => tupleGet xs (int 1)) (fun xs => pure xs.tail)
        (nextLRange (fun r : I64 × I64 => pure r.2) (fun a b : I64 => pure (a * b)))
        (offsetinRange (fun r : I64 × I64 => pure r.1)
          (fun a b : I64 => pure (a - b)))
        (fun a b : I64 => pure (a * b)) (fun a b : I64 => pure (a + b))
        (fun ds l j _ => sourceSubscriptRanges ds l j is) (r :: rs) stride index i is
termination_by is.length

theorem native_sub_self (x : I64) : x - x = int 0 := by
  apply Subtype.ext
  change wrapInt .i64 (x.val - x.val) = _
  simp only [Int.sub_self]
  rfl

theorem native_zero_mul (x : I64) : int 0 * x = int 0 := by
  apply Subtype.ext
  change wrapInt .i64 (0 * x.val) = _
  simp only [Int.zero_mul]
  rfl

theorem native_add_zero (x : I64) : x + int 0 = x := by
  apply Subtype.ext
  change wrapInt .i64 (x.val + 0) = x.val
  simpa using wrapInt_of_inRange .i64 x.val x.property

theorem sourceSubscriptRanges_first (axes : List (I64 × I64)) (stride index : I64) :
    sourceSubscriptRanges axes stride index (axes.map Prod.fst) = .ok index := by
  induction axes generalizing stride index with
  | nil => simp [sourceSubscriptRanges, sub2indRecurseDone]
  | cons r rs ih =>
    have one : (int 1).val = 1 := rfl
    simpa [-JuliaLean.Proofs.base.array.jint_i64_sub_self,
      sourceSubscriptRanges, sub2indRecurse, tupleGet, nextLRange, offsetinRange,
      one, native_sub_self, native_zero_mul, native_add_zero] using
      ih (stride * r.2) index

/-- The first Cartesian coordinate has linear position one, regardless of
axis offsets and even when intermediate native strides wrap. -/
def SubscriptFirstPosition : Prop :=
  ∀ axes : List (I64 × I64),
    sub2indAxes sourceSubscriptRanges axes (axes.map Prod.fst) = .ok (int 1)

theorem subscriptFirstPosition_proven : SubscriptFirstPosition := by
  intro axes
  exact sourceSubscriptRanges_first axes (int 1) (int 1)

def AmbiguousLinearIndexRejected : Prop :=
  ∀ (Ax I R : Type) (axes : Ax) (is : I),
    ∃ message, sub2indAmbiguousOneDim (R := R) axes is =
      .error (.julia (.argumentError message))

theorem ambiguousLinearIndexRejected_proven : AmbiguousLinearIndexRejected := by
  intro Ax I R axes is
  exact ⟨_, rfl⟩

def NativeIndexArithmetic : Prop :=
  (∀ stride count : I64,
    (IntTy.i64.min ≤ stride.val * count.val ∧ stride.val * count.val ≤ IntTy.i64.max) →
    (nextLInteger (fun a b : I64 => pure (a * b)) stride count).map Subtype.val =
      .ok (stride.val * count.val)) ∧
  (∀ (Slice Axis : Type) (indices : Slice → Axis) (length : Axis → I64)
    (stride : I64) (r : Slice),
    (IntTy.i64.min ≤ stride.val * (length (indices r)).val ∧
      stride.val * (length (indices r)).val ≤ IntTy.i64.max) →
    (nextLSlice indices (fun r => pure (length r)) (fun a b : I64 => pure (a * b))
      stride r).map Subtype.val = .ok (stride.val * (length (indices r)).val)) ∧
  (∀ index count : I64,
    (IntTy.i64.min ≤ index.val - 1 ∧ index.val - 1 ≤ IntTy.i64.max) →
    (offsetinInteger (fun a b : I64 => pure (a - b)) index count).map Subtype.val =
      .ok (index.val - 1))

theorem nativeIndexArithmetic_proven : NativeIndexArithmetic := by
  refine ⟨?_, ?_, ?_⟩
  · intro stride count fit
    change (Except.ok (wrapInt .i64 (stride.val * count.val)) : Result Int) = _
    rw [wrapInt_of_inRange .i64 _ fit]
  · intro Slice Axis indices length stride r fit
    change (Except.ok (wrapInt .i64 (stride.val * (length (indices r)).val)) : Result Int) = _
    rw [wrapInt_of_inRange .i64 _ fit]
  · intro index count fit
    change (Except.ok (wrapInt .i64 (index.val - 1)) : Result Int) = _
    rw [wrapInt_of_inRange .i64 _ fit]

theorem sourceSubscriptRanges_extra_ones (count : Nat) (stride index : I64) :
    sourceSubscriptRanges [] stride index (List.replicate count (int 1)) = .ok index := by
  induction count with
  | zero => simp [sourceSubscriptRanges, sub2indRecurseDone]
  | succ count ih =>
    simpa [-JuliaLean.Proofs.base.array.jint_i64_sub_self,
      List.replicate_succ, sourceSubscriptRanges, sub2indRecurseEmpty,
      native_sub_self, native_zero_mul, native_add_zero] using ih

def EmptyRankExtraSingletons : Prop :=
  ∀ count : Nat, sub2indEmptyIndices
    (fun _ stride index is => sourceSubscriptRanges [] stride index is)
    (List.replicate count (int 1)) = .ok (int 1)

theorem emptyRankExtraSingletons_proven : EmptyRankExtraSingletons := by
  intro count
  exact sourceSubscriptRanges_extra_ones count (int 1) (int 1)

/-- External array storage used to exercise the complete concatenation chain. -/
structure ConcatArray (E : Type) where
  axes : List (I64 × I64)
  values : List E

inductive ConcatArg (E : Type) where
  | scalar (value : E)
  | array (array : ConcatArray E)

def ConcatArg.shape : ConcatArg E → List I64
  | .scalar _ => []
  | .array a => a.axes.map Prod.snd

def ConcatArg.values : ConcatArg E → List E
  | .scalar e => [e]
  | .array a => a.values

structure ConcatBuffer (E : Type) where
  shape : List I64
  cells : List (Option E)
  deriving DecidableEq

local instance concatExceptDecidableEq {α : Type} [DecidableEq α] :
    DecidableEq (Except Bool α) := fun a b => by
  cases a with
  | error e =>
    cases b with
    | error f => exact decidable_of_iff (e = f) (by simp)
    | ok x => exact isFalse (by intro h; cases h)
  | ok x =>
    cases b with
    | error f => exact isFalse (by intro h; cases h)
    | ok y => exact decidable_of_iff (x = y) (by simp)

def concatCoordinates : List Nat → List (List Nat)
  | [] => [[]]
  | n :: ns => (concatCoordinates ns).flatMap fun tail =>
      (List.range n).map (· :: tail)

def concatPosition : List Nat → List Nat → Nat
  | [], _ => 0
  | i :: is, n :: ns => i + n * concatPosition is ns
  | i :: is, [] => i + concatPosition is []

def concatNtuple {m : Type → Type} [Monad m] (f : I64 → m A) (n : Nat) : m (List A) :=
  (List.range n).mapM fun (k : Nat) => f (int ((k : Int) + 1))

def concatArgSize (x : ConcatArg E) : Result (List I64) :=
  match x with
  | .scalar e => pure (catSizeScalar e)
  | .array a => catSizeArray (fun a : ConcatArray E => pure (a.axes.map Prod.snd)) a

def concatArgSizeDim (x : ConcatArg E) (d : I64) : Result I64 :=
  match x with
  | .scalar e => pure (catSizeDimScalar e d)
  | .array a =>
      catSizeDimArray
        (sizeDim (fun i : I64 => pure i)
          (fun a : ConcatArray E => pure (a.axes.map Prod.snd))) a d

def concatArgIndices (x : ConcatArg E) (d : I64) : Result (List I64) :=
  match x with
  | .scalar e => catIndicesScalar (fun n => pure (concatRange (int 1) n)) e d
  | .array a =>
    let axes := axesDim (fun d n : I64 => decide (d.val ≤ n.val))
      (fun a : ConcatArray E => pure a.axes) tupleGet (fun n => (int 1, n))
      (ndimsValue (int a.axes.length) a)
    let result := catIndicesArray (fun a d => axes a d) a d
    result.map fun axis => concatRange axis.1 (axis.1 + axis.2 - int 1)

def concatShapeRest (dims : List Bool) (shape : List I64) (xs : List (ConcatArg E)) :
    Result (List I64) :=
  match xs with
  | [] => pure (catSizeShapeDone dims shape)
  | x :: rest => catSizeShapeMore concatArgSize cshpCalls
      (fun ds sh _ => concatShapeRest ds sh rest) dims shape x rest
termination_by xs.length

def concatShapeAll (dims : List Bool) (xs : List (ConcatArg E)) : Result (List I64) :=
  match xs with
  | [] => pure (catSizeShapeEmpty dims)
  | x :: rest => catSizeShape concatArgSize cshpCalls concatShapeRest dims x rest

def concatDims (ds : List I64) : Result (List Bool) :=
  dimsToCatVal
    (dimsToCat (fun p (ds : List I64) => pure (ds.any p))
      (fun ds => match ds with
        | [] => throw (.julia (.argumentError "reducing over an empty collection is not allowed"))
        | _ => pure (int ((ds.map Subtype.val).foldl max 0)))
      (fun i ds => decide (i ∈ ds))
      (fun f n => pure ((List.range n.val.toNat).map fun (k : Nat) =>
        f (int ((k : Int) + 1))))
      (fun _ => "")) ds

def concatAssign {E F : Type} (convert : E → Result F)
    (_a : List I64) (inds : List (List I64)) (x : ConcatArg E) :
    StateT (ConcatBuffer F) Result Unit := fun buffer => do
  let coords := concatCoordinates (inds.map List.length)
  let dest := coords.map fun p => p.zipWith (fun k axis => axis[k]?.getD (int 1)) inds
  if !(dest.all fun p => (p.zip buffer.shape).all fun q =>
      decide (1 ≤ q.1.val ∧ q.1.val ≤ q.2.val)) then
    throw (.julia .boundsError)
  let values ← match x with
    | .scalar e => pure (List.replicate dest.length e)
    | .array a =>
      if a.values.length = dest.length then pure a.values
      else throw (.dimensionMismatch "assignment shape mismatch")
  let values ← values.mapM convert
  let cells := (dest.zip values).foldl (fun cells entry =>
    cells.set (concatPosition (entry.1.map fun i => (i.val - 1).toNat)
      (buffer.shape.map fun n => n.val.toNat)) (some entry.2)) buffer.cells
  return ((), { buffer with cells := cells })

def concatSourceSet {E F : Type} (convert : E → Result F)
    (a : List I64) (inds : List (List I64)) (x : ConcatArg E) :
    StateT (ConcatBuffer F) Result Unit :=
  setindexArray (fun _ => pure ())
    (fun style a inds => StateT.lift (errorCanonicalSetindexOther style a inds))
    (fun _ inds => pure inds)
    (fun _ a x inds => concatAssign convert a inds x) a x inds

def concatWrite {E F : Type} (convert : E → Result F)
    (a : List I64) (inds : List (List I64)) (x : ConcatArg E) :
    StateT (ConcatBuffer F) Result Unit :=
  match x with
  | .scalar e =>
    copyOrFillScalar (fun a inds => pure (a, inds))
      (fun view e => concatAssign convert view.1 view.2 (.scalar e)) a inds e
  | .array array => copyOrFillArray
      (fun a inds array => concatSourceSet convert a inds (.array array)) a inds array

def concatOffset {E F : Type} (convert : E → Result F) (a shape : List I64)
    (dims : List Bool) (offsets : List I64) (xs : List (ConcatArg E)) :
    StateT (ConcatBuffer F) Result (List I64) :=
  match xs with
  | [] => pure (catOffsetDone a shape dims offsets)
  | x :: rest =>
    catOffsetMore
      (catOffsetOne (fun ds i => StateT.lift (tupleGet ds i))
        (fun ns i => StateT.lift (tupleGet ns i)) concatNtuple concatNtuple
        (fun x i => StateT.lift (concatArgIndices x i))
        (fun offset axis => pure (axis.map (offset + ·)))
        (fun lo hi => pure (concatRange lo hi))
        (fun x i => StateT.lift (concatArgSizeDim x i)) (concatWrite convert))
      (fun a sh ds off _ => concatOffset convert a sh ds off rest) a shape dims offsets x rest
termination_by xs.length

def concatInnerSource {E F : Type} (convert : E → Result F)
    (a shape : List I64) (dims : List Bool) (xs : List (ConcatArg E)) :
    StateT (ConcatBuffer F) Result (List I64) :=
  catInner (concatOffset convert) a shape dims xs

def concatAllocate {F : Type} (_ : Unit) (shape : List I64) : Result (ConcatBuffer F) :=
  if shape.all (fun n => decide (0 ≤ n.val)) ∧
      ((shape.map fun n => n.val.toNat).prod) ≤ 9223372036854775807 then
    .ok ⟨shape, List.replicate ((shape.map fun n => n.val.toNat).prod) none⟩
  else .error (.julia (.argumentError "invalid Array dimensions"))

def concatTypedSource {E F : Type} (convert : E → Result F) (zero : F)
    (dims : List I64) (t : Unit) (xs : List (ConcatArg E)) :
    StateT (ConcatBuffer F) Result (List I64) :=
  catTyped (fun ds => StateT.lift (concatDims ds))
    (fun ds xs => StateT.lift (concatShapeAll ds xs))
    (fun xs => StateT.lift (tupleGet xs (int 1)))
    (fun exemplar t shape => fun _ => do
      let buffer ← match exemplar with
        | .scalar e => catSimilarTuple concatAllocate e t shape
        | .array a => catSimilarAbstractTuple (similarFallback concatAllocate) a t shape
      return (shape, buffer))
    (fun p ds => pure (int (ds.filter p).length)) (fun _ => pure zero)
    (fun _ zero => fun buffer =>
      .ok ((), { buffer with cells := buffer.cells.map fun _ => some zero }))
    (concatInnerSource convert) dims t xs

def ConcatArg.isArray : ConcatArg E → Bool
  | .array _ => true
  | .scalar _ => false

def concatPromotionGeneral : List (ConcatArg E) → Result Unit
  | [] => promoteEltypeofEmpty
  | [x] => promoteEltypeofOne (fun _ => pure ()) x
  | [x, y] => promoteEltypeofTwo (fun _ => pure ()) (fun _ => pure ())
      (fun _ _ => pure ()) x y
  | x :: y :: rest =>
      promoteEltypeofMany (fun _ => pure ()) (fun _ _ => pure ())
        (promoteEltypeofTwo (fun _ => pure ()) (fun _ => pure ()) (fun _ _ => pure ()))
        (fun combine initial values => values.foldlM combine initial) x y rest

def concatPromotionSource : List (ConcatArg E) → Result Unit
  | [] => promoteEltypeofEmpty
  | .array a :: rest =>
      if rest.all ConcatArg.isArray then pure (promoteEltypeofArrays () a rest)
      else concatPromotionGeneral (.array a :: rest)
  | .scalar e :: rest =>
      if rest.all (fun x => !x.isArray) then
        promoteEltypeofSame (fun _ => pure ()) e rest
      else concatPromotionGeneral (.scalar e :: rest)

def concatPromoteSource {E F : Type} (convert : E → Result F) (zero : F)
    (dims : List I64) (xs : List (ConcatArg E)) :
    StateT (ConcatBuffer F) Result (List I64) :=
  catPromote (fun xs => StateT.lift (concatPromotionSource xs))
    (concatTypedSource convert zero) dims xs

def concatKeywordSource {E F : Type} (convert : E → Result F) (zero : F)
    (xs : List (ConcatArg E)) (dims : List I64) :
    StateT (ConcatBuffer F) Result (List I64) :=
  catKeyword (fun dims xs => match xs with
    | .array _ :: rest =>
        if rest.all ConcatArg.isArray then
          catSameArrays (concatTypedSource convert zero) dims () xs
        else concatPromoteSource convert zero dims xs
    | _ => concatPromoteSource convert zero dims xs) xs dims

/-- The reference depends only on sizes and element order, so translating an
input's axis origins cannot move its output block. -/
def concatReferenceCell (dims : List Bool) (p : List Nat) (xs : List (ConcatArg E))
    (offsets : List Nat) : Option E :=
  match xs with
  | [] => none
  | x :: rest =>
    let sizes := p.zipIdx.map fun (_, d) => ((x.shape[d]?.getD (int 1)).val).toNat
    let inside := (List.range p.length).all fun d =>
      let start := if dims[d]?.getD false then offsets[d]?.getD 0 else 0
      decide (start ≤ p[d]?.getD 0 ∧ p[d]?.getD 0 < start + sizes[d]?.getD 0)
    if inside then
      x.values[concatPosition ((List.range p.length).map fun d =>
        p[d]?.getD 0 - (if dims[d]?.getD false then offsets[d]?.getD 0 else 0)) sizes]?
    else concatReferenceCell dims p rest ((List.range p.length).map fun d =>
      offsets[d]?.getD 0 + (if dims[d]?.getD false then sizes[d]?.getD 0 else 0))

def concatReference {E F : Type} (g : E → F) (zero : F) (dims : List Bool)
    (xs : List (ConcatArg E)) : Except Bool (ConcatBuffer F) := do
  let shape ← referenceCatShape dims (xs.map ConcatArg.shape)
  return ⟨shape, (concatCoordinates (shape.map fun n => n.val.toNat)).map fun p =>
    some ((concatReferenceCell dims p xs (List.replicate shape.length 0)).map g |>.getD zero)⟩

def concatObserved {F : Type} (operation : StateT (ConcatBuffer F) Result (List I64)) :
    Except Bool (ConcatBuffer F) :=
  ((operation.run ⟨[], []⟩).map Prod.snd).mapError dimensionErrorClass

def concatFlags (dims : List I64) : List Bool :=
  (List.range ((dims.map Subtype.val).foldl max 0).toNat).map
    fun (k : Nat) => decide (int ((k : Int) + 1) ∈ dims)

/-- Mathematical extents retain the representability precondition of the
concatenation contract before converting sums to native dimensions. -/
def referenceCatExtents (dims : List Bool) (xs : List (ConcatArg E)) :
    Except Bool (List Int) := do
  let shape ← referenceCatShape dims (xs.map ConcatArg.shape)
  return (List.range shape.length).map fun i =>
    if dims[i]?.getD false then
      (xs.map fun x => (x.shape[i]?.getD (int 1)).val).sum
    else (shape[i]?.getD (int 1)).val

def ConcatShapeFits (dims : List I64) (xs : List (ConcatArg E)) : Prop :=
  ∀ shape, referenceCatExtents (concatFlags dims) xs = .ok shape →
    (∀ n ∈ shape, 0 ≤ n ∧ n ≤ 9223372036854775807) ∧
      ((shape.map Int.toNat).prod) ≤ 9223372036854775807

def ConcatArrayValid (a : ConcatArray E) : Prop :=
  a.values.length = ((a.axes.map fun axis => axis.2.val.toNat).prod) ∧
    a.values.length ≤ 9223372036854775807 ∧
    a.axes.all (fun axis => decide
      (IntTy.i64.min ≤ axis.1.val + axis.2.val - 1 ∧
        axis.1.val + axis.2.val - 1 ≤ IntTy.i64.max)) = true

local instance concatArrayValidDecidable (a : ConcatArray E) : Decidable (ConcatArrayValid a) := by
  unfold ConcatArrayValid
  infer_instance

def ConcatInputValid (dims : List I64) (xs : List (ConcatArg E)) : Prop :=
  dims ≠ [] ∧ (∀ d ∈ dims, 1 ≤ d.val) ∧ xs ≠ [] ∧
  (∀ x ∈ xs, ∀ n ∈ x.shape, 0 ≤ n.val) ∧
  (∀ a, ConcatArg.array a ∈ xs → ConcatArrayValid a) ∧ ConcatShapeFits dims xs

def ConcatArgumentRejected (xs : List (ConcatArg E))
    (operation : StateT (ConcatBuffer F) Result (List I64))
    (initial : ConcatBuffer F := ⟨[], []⟩) : Prop :=
  xs.any (fun x => match x with
    | .scalar _ => false
    | .array a => a.axes.any (fun axis => axis.1.val != 1)) = true ∧
  ∃ message, ((operation.run initial).map Prod.snd) =
    .error (.julia (.argumentError message))

def CatPromoteComplete : Prop :=
  ∀ (E F : Type) (convert : E → Result F) (g : E → F) (zero : F)
    (dims : List I64) (xs : List (ConcatArg E)),
    ConcatInputValid dims xs → (∀ x ∈ xs, ∀ e ∈ x.values, convert e = .ok (g e)) →
    concatObserved (concatPromoteSource convert zero dims xs) =
      concatReference g zero ((List.range ((dims.map Subtype.val).foldl max 0).toNat).map
        fun (k : Nat) => decide (int ((k : Int) + 1) ∈ dims)) xs ∨
      ConcatArgumentRejected xs (concatPromoteSource convert zero dims xs)

theorem concatOffset_shifted_singleton :
    (concatOffset (fun n : Nat => pure n) [int 1] [int 1] [true] [int 0]
      [.array ⟨[(int 3, int 1)], [20]⟩]).run ⟨[int 1], [none]⟩ =
      .error (.julia .boundsError) := by
  simp only [concatOffset, catOffsetMore]
  rfl

set_option maxRecDepth 8192 in
theorem catPromoteComplete_refuted : ¬ CatPromoteComplete := by
  intro h
  have bad := h Nat Nat (fun n => pure n) id 0 [int 1]
    [.array ⟨[(int 3, int 1)], [20]⟩]
    (by
      refine ⟨by simp, ?_, by simp, ?_, ?_, ?_⟩
      · intro d hd
        have : d = int 1 := List.mem_singleton.mp hd
        subst d
        decide
      · intro x hx n hn
        have : x = .array ⟨[(int 3, int 1)], [20]⟩ := List.mem_singleton.mp hx
        subst x
        have : n = int 1 := List.mem_singleton.mp hn
        subst n
        decide
      · intro a ha
        have eq : a = ⟨[(int 3, int 1)], [20]⟩ := by
          simpa only [List.mem_singleton, ConcatArg.array.injEq] using ha
        subst a
        decide
      · intro shape hshape
        change (Except.ok [1] : Except Bool (List Int)) = .ok shape at hshape
        cases hshape
        constructor
        · intro n hn
          have : n = 1 := List.mem_singleton.mp hn
          subst n
          decide
        · decide) (by simp [ConcatArg.values])
  have actualRaw : (concatPromoteSource (fun n : Nat => pure n) 0 [int 1]
      [.array ⟨[(int 3, int 1)], [20]⟩]).run ⟨[], []⟩ = .error (.julia .boundsError) := by
    have hd : concatDims [int 1] = .ok [true] := by decide
    have hs : concatShapeAll [true]
        [ConcatArg.array (E := Nat) ⟨[(int 3, int 1)], [20]⟩] = .ok [int 1] := by
      simp [concatShapeAll, catSizeShape, concatArgSize, catSizeArray,
        concatShapeRest, catSizeShapeDone, cshpCalls, cshpLeading, cshpEmpty]
    have hi := concatOffset_shifted_singleton
    simp only [concatPromoteSource, catPromote, concatTypedSource, catTyped,
      hd, hs, concatInnerSource, catInner, concatPromotionSource, promoteEltypeofArrays,
      bind, pure, Except.bind, Except.pure, StateT.run, StateT.bind, StateT.pure,
      StateT.lift]
    change (concatOffset (fun n : Nat => pure n) [int 1] [int 1] [true] [int 0]
      [.array ⟨[(int 3, int 1)], [20]⟩]).run ⟨[int 1], [none]⟩ = _
    exact hi
  rcases bad with equal | ⟨_, message, rejected⟩
  · have actual : concatObserved (concatPromoteSource (fun n : Nat => pure n) 0 [int 1]
        [.array ⟨[(int 3, int 1)], [20]⟩]) = .error false := by
      exact congrArg (fun r => (r.map Prod.snd).mapError dimensionErrorClass) actualRaw
    rw [actual] at equal
    cases equal
  · rw [actualRaw] at rejected
    cases rejected

/-- The entry method computes the same full shape contract as the helper:
omitted dimensions are singleton and incompatible non-cat coordinates fail. -/
def CatSizeShapeEntrySpec : Prop :=
  ∀ (E : Type) (dims : List Bool) (x : ConcatArg E) (xs : List (ConcatArg E)),
    (∀ y ∈ x :: xs, ∀ n ∈ y.shape, 0 ≤ n.val) →
    (catSizeShape concatArgSize cshpCalls concatShapeRest dims x xs).mapError
      dimensionErrorClass = referenceCatShape dims ((x :: xs).map ConcatArg.shape)

set_option maxRecDepth 8192 in
theorem catSizeShapeEntrySpec_refuted : ¬ CatSizeShapeEntrySpec := by
  intro h
  have bad := h Nat [true] (.array ⟨[(int 1, int 1)], [1]⟩)
    [.array ⟨[(int 1, int 1), (int 1, int 2)], [2, 3]⟩] (by decide)
  have actual : (catSizeShape concatArgSize cshpCalls concatShapeRest [true]
      (ConcatArg.array (E := Nat) ⟨[(int 1, int 1)], [1]⟩)
      [.array ⟨[(int 1, int 1), (int 1, int 2)], [2, 3]⟩]).mapError dimensionErrorClass =
      .ok [int 2, int 2] := by
    simp [catSizeShape, concatShapeRest, catSizeShapeMore, catSizeShapeDone,
      concatArgSize, catSizeArray, cshpCalls, cshpLeading, cshpMerge, cshpInitial,
      cshpEmpty, Except.mapError]
    rfl
  rw [actual] at bad
  cases bad

inductive ConcatFront where
  | promote | typedKeyword | keyword | sameArrays
  | vcat | hcat | typedVcat | typedHcat
  | vcatOne | vcatTwo | vcatArrays | vcatMixed
  | hcatOne | hcatTwo | hcatArrays | hcatMixed
  | typedVcatOne | typedVcatTwo | typedVcatArrays
  | typedHcatOne | typedHcatTwo | typedHcatArrays
  deriving DecidableEq

def ConcatFront.horizontal : ConcatFront → Bool
  | .hcat | .typedHcat | .hcatOne | .hcatTwo | .hcatArrays | .hcatMixed
  | .typedHcatOne | .typedHcatTwo | .typedHcatArrays => true
  | _ => false

def ConcatFront.two : ConcatFront → Bool
  | .vcatTwo | .hcatTwo | .typedVcatTwo | .typedHcatTwo => true
  | _ => false

def ConcatFront.dimensions (front : ConcatFront) (dims : List I64) : List I64 :=
  match front with
  | .promote | .typedKeyword | .keyword | .sameArrays => dims
  | _ => [int (if front.horizontal then 2 else 1)]


def concatFrontSource {E F : Type} (front : ConcatFront) (convert : E → Result F)
    (zero : F) (dims : List I64) (xs : List (ConcatArg E)) :
    StateT (ConcatBuffer F) Result (List I64) :=
  let cat := fun xs d => concatKeywordSource convert zero xs [d]
  let typed := fun d t xs => concatTypedSource convert zero [d] t xs
  match front with
  | .promote => concatPromoteSource convert zero dims xs
  | .typedKeyword => catTypedKeyword (concatTypedSource convert zero) () xs dims
  | .keyword => concatKeywordSource convert zero xs dims
  | .sameArrays => catSameArrays (concatTypedSource convert zero) dims () xs
  | .vcat => vcatAny cat xs
  | .hcat => hcatAny cat xs
  | .typedVcat => typedVcatAny typed () xs
  | .typedHcat => typedHcatAny typed () xs
  | .vcatOne => do
    vcatOneArray cat (← StateT.lift (tupleGet xs (int 1)))
  | .vcatTwo => do
    let a ← StateT.lift (tupleGet xs (int 1))
    let b ← StateT.lift (tupleGet xs (int 2))
    vcatTwoArrays (fun pair d => cat [pair.1, pair.2] d) a b
  | .vcatArrays => vcatArrayVarargs cat xs
  | .vcatMixed => vcatMixed cat xs
  | .hcatOne => do
    hcatOneArray cat (← StateT.lift (tupleGet xs (int 1)))
  | .hcatTwo => do
    let a ← StateT.lift (tupleGet xs (int 1))
    let b ← StateT.lift (tupleGet xs (int 2))
    hcatTwoArrays (fun pair d => cat [pair.1, pair.2] d) a b
  | .hcatArrays => hcatArrayVarargs cat xs
  | .hcatMixed => hcatMixed cat xs
  | .typedVcatOne => do
    typedVcatOneArray typed () (← StateT.lift (tupleGet xs (int 1)))
  | .typedVcatTwo => do
    let a ← StateT.lift (tupleGet xs (int 1))
    let b ← StateT.lift (tupleGet xs (int 2))
    typedVcatTwoArrays (fun d t pair => typed d t [pair.1, pair.2]) () a b
  | .typedVcatArrays => typedVcatArrayVarargs typed () xs
  | .typedHcatOne => do
    typedHcatOneArray typed () (← StateT.lift (tupleGet xs (int 1)))
  | .typedHcatTwo => do
    let a ← StateT.lift (tupleGet xs (int 1))
    let b ← StateT.lift (tupleGet xs (int 2))
    typedHcatTwoArrays (fun d t pair => typed d t [pair.1, pair.2]) () a b
  | .typedHcatArrays => typedHcatArrayVarargs typed () xs

def ConcatFront.accepts (front : ConcatFront) (xs : List (ConcatArg E)) : Prop :=
  match front with
  | .vcatOne | .hcatOne | .typedVcatOne | .typedHcatOne => xs.length = 1
  | .vcatTwo | .hcatTwo | .typedVcatTwo | .typedHcatTwo => xs.length = 2
  | _ => True

/-- The same elementwise, zero-background contract is asserted separately for
each source front end, with only its argument-count dispatch precondition. -/
def ConcatFrontendComplete (front : ConcatFront) (ordinary : Bool := false) : Prop :=
  ∀ (E F : Type) (convert : E → Result F) (g : E → F) (zero : F)
    (dims : List I64) (xs : List (ConcatArg E)),
    front.accepts xs →
    ConcatInputValid (front.dimensions dims) xs →
    (ordinary = true → ∀ a, ConcatArg.array a ∈ xs → ∀ axis ∈ a.axes, axis.1 = int 1) →
    (∀ x ∈ xs, ∀ e ∈ x.values, convert e = .ok (g e)) →
    concatObserved (concatFrontSource front convert zero dims xs) =
      concatReference g zero (concatFlags (front.dimensions dims)) xs ∨
      ConcatArgumentRejected xs (concatFrontSource front convert zero dims xs)

def concatShiftedWitness (two : Bool) : List (ConcatArg Nat) :=
  let x := ConcatArg.array (E := Nat)
    ⟨[(int 3, int 1), (int 3, int 1), (int 3, int 1)], [20]⟩
  if two then [x, x] else [x]

def concatWitnessShape (horizontal two : Bool) : List I64 :=
  if horizontal then [int 1, int (if two then 2 else 1), int 1]
  else [int (if two then 2 else 1), int 1, int 1]

theorem concatShifted_shape (horizontal two : Bool) :
    concatShapeAll (if horizontal then [false, true] else [true])
      (concatShiftedWitness two) = .ok (concatWitnessShape horizontal two) := by
  cases horizontal <;> cases two <;>
    simp [concatShiftedWitness, concatWitnessShape, concatShapeAll, catSizeShape,
      concatShapeRest, catSizeShapeDone, catSizeShapeMore, concatArgSize, catSizeArray,
      cshpCalls, cshpLeading, cshpInitial, cshpMerge, cshpEqual, cshpEmpty, catCheckDim] <;> decide

theorem concatShifted_offset (horizontal two : Bool) :
    (concatOffset (fun n : Nat => pure n) (concatWitnessShape horizontal two)
      (concatWitnessShape horizontal two) (if horizontal then [false, true] else [true])
      [int 0, int 0, int 0] (concatShiftedWitness two)).run
        ⟨concatWitnessShape horizontal two,
          List.replicate ((concatWitnessShape horizontal two).map fun n => n.val.toNat).prod none⟩ =
      .error (.julia .boundsError) := by
  cases horizontal <;> cases two <;>
    simp only [concatShiftedWitness, concatWitnessShape, Bool.false_eq_true, ↓reduceIte,
      concatOffset, catOffsetMore] <;> rfl

theorem concatShifted_typed (horizontal two : Bool) :
    (concatTypedSource (fun n : Nat => pure n) 0
      [int (if horizontal then 2 else 1)] () (concatShiftedWitness two)).run ⟨[], []⟩ =
        .error (.julia .boundsError) := by
  have hd : concatDims [int (if horizontal then 2 else 1)] =
      .ok (if horizontal then [false, true] else [true]) := by cases horizontal <;> decide
  have hs := concatShifted_shape horizontal two
  have ho := concatShifted_offset horizontal two
  have hfirst : tupleGet (concatShiftedWitness two) (int 1) =
      .ok (.array ⟨[(int 3, int 1), (int 3, int 1), (int 3, int 1)], [20]⟩) := by
    cases two <;> rfl
  cases horizontal <;> cases two <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hd hs ho hfirst ⊢ <;>
    simp only [concatTypedSource, catTyped, hd, hs, hfirst, concatInnerSource, catInner,
      bind, pure, Except.bind, Except.pure, StateT.run, StateT.bind, StateT.pure, StateT.lift] <;>
    exact ho

theorem concatShifted_front_raw (front : ConcatFront) :
    (concatFrontSource front (fun n : Nat => pure n) 0 [int 1]
      (concatShiftedWitness front.two)).run ⟨[], []⟩ = .error (.julia .boundsError) := by
  have hf := concatShifted_typed front.horizontal front.two
  have one : (int 1).val = 1 := rfl
  have two : (int 2).val = 2 := rfl
  cases front <;>
    simpa [concatFrontSource, ConcatFront.horizontal, ConcatFront.two,
      catTypedKeyword, catKeyword, catSameArrays, vcatAny, hcatAny,
      typedVcatAny, typedHcatAny, vcatOneArray, vcatTwoArrays, vcatArrayVarargs,
      vcatMixed, hcatOneArray, hcatTwoArrays, hcatArrayVarargs, hcatMixed,
      typedVcatOneArray, typedVcatTwoArrays, typedVcatArrayVarargs, typedHcatOneArray,
      typedHcatTwoArrays, typedHcatArrayVarargs, concatPromoteSource, catPromote,
      concatKeywordSource, ConcatArg.isArray, concatPromotionSource, promoteEltypeofArrays,
      concatShiftedWitness, tupleGet, one, two,
      bind, pure, Except.bind, Except.pure, StateT.run, StateT.bind, StateT.pure, StateT.lift,
      Except.map, Except.mapError] using hf

theorem concatShifted_front (front : ConcatFront) :
    concatObserved (concatFrontSource front (fun n : Nat => pure n) 0 [int 1]
      (concatShiftedWitness front.two)) = .error false := by
  exact congrArg (fun r => (r.map Prod.snd).mapError dimensionErrorClass) (concatShifted_front_raw front)

theorem concatFrontendComplete_refuted (front : ConcatFront) :
    ¬ ConcatFrontendComplete front := by
  intro h
  have pre : ConcatInputValid [int (if front.horizontal then 2 else 1)]
      (concatShiftedWitness front.two) := by
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      have : d = int (if front.horizontal then 2 else 1) := List.mem_singleton.mp hd
      subst d
      cases front.horizontal <;> decide
    · cases front.two <;> simp [concatShiftedWitness]
    · intro x hx n hn
      have eq : x = ConcatArg.array
          ⟨[(int 3, int 1), (int 3, int 1), (int 3, int 1)], [20]⟩ := by
        cases ht : front.two <;> simpa [concatShiftedWitness, ht] using hx
      subst x
      have eqn : n = int 1 := by simpa [ConcatArg.shape] using hn
      subst n
      decide
    · intro a ha
      have eq : a = ⟨[(int 3, int 1), (int 3, int 1), (int 3, int 1)], [20]⟩ := by
        cases ht : front.two <;> simpa [concatShiftedWitness, ht] using ha
      subst a
      decide
    · intro shape hshape
      have expected : ∃ ns, referenceCatExtents
          (concatFlags [int (if front.horizontal then 2 else 1)])
          (concatShiftedWitness front.two) = .ok ns ∧
          (∀ n ∈ ns, 0 ≤ n ∧ n ≤ 9223372036854775807) ∧
          ((ns.map Int.toNat).prod) ≤ 9223372036854775807 := by
        cases front <;> refine ⟨_, rfl, ?_, by decide⟩ <;> simp <;> decide
      obtain ⟨ns, actual, extents, cells⟩ := expected
      rw [actual] at hshape
      cases hshape
      exact ⟨extents, cells⟩
  have pre' : ConcatInputValid (front.dimensions [int 1])
      (concatShiftedWitness front.two) := by
    cases front <;> exact pre
  have arity : front.accepts (concatShiftedWitness front.two) := by
    cases front <;> simp [ConcatFront.accepts, ConcatFront.two, concatShiftedWitness]
  have conv : ∀ x ∈ concatShiftedWitness front.two, ∀ e ∈ x.values,
      (pure e : Result Nat) = .ok (id e) := by intros; rfl
  have bad := h Nat Nat (fun n => pure n) id 0 [int 1] (concatShiftedWitness front.two)
    arity pre' (by intro impossible; cases impossible) conv
  rw [concatShifted_front] at bad
  have expected : ∃ buffer, concatReference id 0
      (concatFlags (front.dimensions [int 1]))
      (concatShiftedWitness front.two) = .ok buffer := by
    cases front <;> exact ⟨_, rfl⟩
  obtain ⟨buffer, he⟩ := expected
  rw [he] at bad
  rcases bad with impossible | ⟨_, message, rejected⟩
  · cases impossible
  · rw [concatShifted_front_raw] at rejected
    cases rejected

theorem traceNatWriteLoop {E : Type} (ks : List Nat) (value : I64 → E)
    (log : WriteTrace E) :
    (do
      for k in ks do
        let e ← pure (value (int ((k : Int) + 1)))
        traceWrite () (int ((k : Int) + 1)) e
      pure () : StateT (WriteTrace E) Result Unit).run log =
      .ok ((), log ++ ks.map (fun (k : Nat) => (int ((k : Int) + 1), value (int ((k : Int) + 1))))) := by
  induction ks generalizing log with
  | nil => simp [List.forIn_nil, StateT.run, StateT.bind, StateT.pure]
  | cons k ks ih =>
    simpa [List.forIn_cons, traceWrite, StateT.run, StateT.bind, StateT.pure,
      List.append_assoc] using
      ih (log ++ [(int ((k : Int) + 1), value (int ((k : Int) + 1)))])

def GeneratedColumnFillOrder : Prop :=
  ∀ (E : Type) (count rank : Nat) (size : Unit → I64 → I64)
    (tailProduct : Unit → I64) (len : I64) (is : List I64)
    (value : I64 → E) (log : WriteTrace E),
    count ≤ 32 →
    (rank ≤ 2 → (size () (int 1) * size () (int 2)).val = (count : Int)) →
    (2 < rank → ((size () (int 1) * size () (int 2)) * tailProduct ()).val = (count : Int)) →
    (sourceTraceFill true count rank size tailProduct len is value () false ()).run log =
      .ok ((), log ++ (List.range count).map
        (fun (k : Nat) => (int ((k : Int) + 1), value (int ((k : Int) + 1)))))

theorem generatedColumnFillOrder_proven : GeneratedColumnFillOrder := by
  intro E count rank size tailProduct len is value log countBound small large
  have few : ¬ count > 32 := by omega
  by_cases rankBound : rank ≤ 2
  · have shape := small rankBound
    simpa [sourceTraceFill, hvncatFill, few, rankBound, shape,
      bind, pure, StateT.run, StateT.bind, StateT.pure] using traceNatWriteLoop (List.range count) value log
  · have shape := large (by omega)
    dsimp at shape
    simpa [sourceTraceFill, hvncatFill, few, rankBound, shape,
      bind, pure, StateT.run, StateT.bind, StateT.pure] using traceNatWriteLoop (List.range count) value log

theorem traceStateWriteLoop {E S : Type} (ks : List Nat)
    (index : Nat → S → I64) (value : Nat → E)
    (next : Nat → S → StateT (WriteTrace E) Result (ForInStep S))
    (nextPure : ∀ k s log, ∃ s', (next k s).run log = .ok (.yield s', log))
    (s : S) (log : WriteTrace E) :
    ((do
      let _ ← forIn ks s (fun k state => do
        let e ← pure (value k)
        traceWrite () (index k state) e
        next k state)
      pure () : StateT (WriteTrace E) Result Unit).run log).map
        (fun p => p.2.map Prod.snd) = .ok (log.map Prod.snd ++ ks.map value) := by
  induction ks generalizing s log with
  | nil => simp [List.forIn_nil, StateT.run, StateT.bind, StateT.pure, Except.map]
  | cons k ks ih =>
    obtain ⟨s', hn⟩ := nextPure k s (log ++ [(index k s, value k)])
    simp only [StateT.run] at hn
    simpa [List.forIn_cons, traceWrite, bind, pure, StateT.run, StateT.bind,
      StateT.pure, hn, Except.map, List.map_append, List.append_assoc] using
      ih s' (log ++ [(index k s, value k)])

def GeneratedRowFillValues : Prop :=
  ∀ (E : Type) (count rank : Nat) (size : Unit → I64 → I64)
    (tailProduct : Unit → I64) (len : I64) (is : List I64)
    (value : I64 → E) (log : WriteTrace E),
    count ≤ 32 →
    (rank ≤ 2 → (size () (int 1) * size () (int 2)).val = (count : Int)) →
    (2 < rank → ((size () (int 1) * size () (int 2)) * tailProduct ()).val = (count : Int)) →
    ((sourceTraceFill true count rank size tailProduct len is value () true ()).run log).map
      (fun p => p.2.map Prod.snd) =
        .ok (log.map Prod.snd ++ (List.range count).map (fun (k : Nat) => value (int ((k : Int) + 1))))

theorem generatedRowFillValues_proven : GeneratedRowFillValues := by
  intro E count rank size tailProduct len is value log countBound small large
  have few : ¬ count > 32 := by omega
  let nr := size () (int 1)
  let nc := size () (int 2)
  by_cases rankBound : rank ≤ 2
  · have shape := small rankBound
    dsimp at shape
    let next : Nat → I64 × I64 → StateT (WriteTrace E) Result (ForInStep (I64 × I64)) :=
      fun _ state =>
        let j := state.2 + int 1
        if j.val > nc.val then pure (.yield (state.1 + int 1, int 1))
        else pure (.yield (state.1, j))
    have hp : ∀ k s log, ∃ s', (next k s).run log = .ok (.yield s', log) := by
      intro k s log
      dsimp only [next]
      split <;> exact ⟨_, rfl⟩
    have loop := traceStateWriteLoop (List.range count)
      (fun (_ : Nat) (state : I64 × I64) => state.1 + (state.2 - int 1) * nr)
      (fun (k : Nat) => value (int ((k : Int) + 1))) next hp (int 1, int 1) log
    simpa [sourceTraceFill, hvncatFill, few, rankBound, shape, next, nr, nc,
      bind, pure, StateT.run, StateT.bind, StateT.pure] using loop
  · have shape := large (by omega)
    dsimp at shape
    let next : Nat → I64 × I64 × I64 × I64 × I64 →
        StateT (WriteTrace E) Result (ForInStep (I64 × I64 × I64 × I64 × I64)) :=
      fun _ state =>
        let d := state.1
        let i := state.2.1
        let dd := state.2.2.1
        let ai := state.2.2.2.1 + nr
        let j := state.2.2.2.2 + int 1
        if j.val > nc.val then
          let i := i + int 1
          if i.val > nr.val then
            let d := d + int 1
            let dd := (nr * nc) * (d - int 1)
            pure (.yield (d, int 1, dd, dd + int 1, int 1))
          else pure (.yield (d, i, dd, dd + i, int 1))
        else pure (.yield (d, i, dd, ai, j))
    have hp : ∀ k s log, ∃ s', (next k s).run log = .ok (.yield s', log) := by
      intro k s log
      dsimp only [next]
      split
      · split <;> exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    have loop := traceStateWriteLoop (List.range count)
      (fun (_ : Nat) (state : I64 × I64 × I64 × I64 × I64) => state.2.2.2.1)
      (fun (k : Nat) => value (int ((k : Int) + 1))) next hp
      (int 1, int 1, int 0, int 0 + int 1, int 1) log
    simpa [sourceTraceFill, hvncatFill, few, rankBound, shape, next, nr, nc,
      bind, pure, StateT.run, StateT.bind, StateT.pure] using loop

def GeneratedFillRejectsShape : Prop :=
  ∀ (E : Type) (count rank : Nat) (size : Unit → I64 → I64)
    (tailProduct : Unit → I64) (len : I64) (is : List I64)
    (value : I64 → E) (log : WriteTrace E) (rowFirst : Bool),
    count ≤ 32 →
    (rank ≤ 2 → (size () (int 1) * size () (int 2)).val ≠ (count : Int)) →
    (2 < rank → ((size () (int 1) * size () (int 2)) * tailProduct ()).val ≠ (count : Int)) →
    ∃ message, (sourceTraceFill true count rank size tailProduct len is value () rowFirst ()).run log =
      .error (.julia (.argumentError message))

theorem generatedFillRejectsShape_proven : GeneratedFillRejectsShape := by
  intro E count rank size tailProduct len is value log rowFirst countBound small large
  have few : ¬ count > 32 := by omega
  by_cases rankBound : rank ≤ 2
  · have shape := small rankBound
    dsimp at shape
    exact ⟨_, by simp [sourceTraceFill, hvncatFill, few, rankBound, shape,
      StateT.run, StateT.bind, StateT.pure]; rfl⟩
  · have shape := large (by omega)
    dsimp at shape
    exact ⟨_, by simp [sourceTraceFill, hvncatFill, few, rankBound, shape,
      StateT.run, StateT.bind, StateT.pure]; rfl⟩

def numericMatrix (_ : Unit) (nr nc : I64) :
    StateT (WriteTrace E) Result (I64 × I64) :=
  if 0 ≤ nr.val ∧ 0 ≤ nc.val ∧ nr.val * nc.val ≤ 9223372036854775807 then
    pure (nr, nc)
  else throw (.julia (.argumentError "invalid Array dimensions"))

def numericSize (shape : I64 × I64) (d : I64) :
    StateT (WriteTrace E) Result I64 :=
  pure (if d.val = 1 then shape.1 else if d.val = 2 then shape.2 else int 1)

def numericSet2 (shape : I64 × I64) (i j : I64) (e : E) :
    StateT (WriteTrace E) Result Unit :=
  traceWrite shape (i + (j - int 1) * shape.1) e

def numericFill (generated : Bool) (shape : I64 × I64) (rowFirst : Bool) (xs : List E) :
    StateT (WriteTrace E) Result Unit :=
  hvncatFill generated xs.length 2 numericSize (fun _ => pure (int 1))
    (fun _ => pure "") (fun xs i => StateT.lift (tupleGet xs i)) traceWrite numericSet2
    (hvncatFillLoop numericSize (fun _ => pure (int 1))
      (fun xs => pure (int xs.length)) (fun _ => pure "")
      (fun lo hi => pure (concatRange lo hi))
      (fun xs => pure ((List.range xs.length).map fun (k : Nat) => int ((k : Int) + 1)))
      (fun xs i => StateT.lift (tupleGet xs i)) traceWrite)
    shape rowFirst xs

def numericHvcatSame (rows : List I64) (xs : List E) :
    StateT (WriteTrace E) Result (I64 × I64) :=
  hvcatSameNumbers (fun rows => pure (int rows.length))
    (fun rows i => StateT.lift (tupleGet rows i)) numericMatrix
    (fun shape => pure (shape.1 * shape.2)) (fun xs => pure (int xs.length))
    (fun lo hi => pure (concatRange lo hi))
    (fun xs i => StateT.lift (tupleGet xs i)) numericSet2 () rows xs

def numericHvcatTyped (rows : List I64) (xs : List E) :
    StateT (WriteTrace E) Result (I64 × I64) :=
  typedHvcatNumbers (fun rows => pure (int rows.length))
    (fun rows i => StateT.lift (tupleGet rows i))
    (fun lo hi => pure (concatRange lo hi)) numericMatrix (numericFill false) () rows xs

def numericHvcatColumns (columns : I64) (xs : List E) :
    StateT (WriteTrace E) Result (I64 × I64) :=
  hvcatColumns (fun xs => pure (int xs.length))
    (fun n d => StateT.lift (liftJulia (JInt.mod n d)))
    (fun n d => StateT.lift (liftJulia (JInt.div n d)))
    (fun width n =>
      if n.val < 0 then
        throw (.julia (.argumentError ("tuple length should be ≥ 0, got " ++ toString n.val)))
      else pure (List.replicate n.val.toNat width)) numericHvcatSame columns xs

def numericExceptionClass : ArrayError → Nat
  | .julia (.argumentError _) => 1
  | .dimensionMismatch _ => 2
  | .julia .divideError => 3
  | .julia .boundsError => 4
  | _ => 5

def numericError {A : Type} : Result A → Option Nat
  | .ok _ => none
  | .error e => some (numericExceptionClass e)

def HvcatNumbersErrorAgreement : Prop :=
  ∀ (E : Type) (rows : List I64) (xs : List E) (log : WriteTrace E),
    numericError ((numericHvcatSame rows xs).run log) =
      numericError ((numericHvcatTyped rows xs).run log)

theorem hvcatNumbersErrorAgreement_refuted : ¬ HvcatNumbersErrorAgreement := by
  intro h
  have bad := h Nat [int 2, int 1] [1, 2, 3] []
  have ha : numericError ((numericHvcatSame [int 2, int 1] [1, 2, 3]).run []) = some 1 := by decide
  have hb : numericError ((numericHvcatTyped [int 2, int 1] [1, 2, 3]).run []) = some 2 := by decide
  rw [ha, hb] at bad
  cases bad

def HvcatNonpositiveColumns : Prop :=
  ∀ (E : Type) (columns : I64) (xs : List E) (log : WriteTrace E),
    columns.val ≤ 0 → xs ≠ [] → ∃ message,
      (numericHvcatColumns columns xs).run log = .error (.julia (.argumentError message))

theorem hvcatNonpositiveColumns_refuted : ¬ HvcatNonpositiveColumns := by
  intro h
  obtain ⟨message, bad⟩ := h Nat (int 0) [1] [] (by decide) (by simp)
  have actual : (numericHvcatColumns (int 0) ([1] : List Nat)).run [] =
      .error (.julia .divideError) := by decide
  rw [actual] at bad
  cases bad

theorem nativeLength_value (n : Nat) (h : n ≤ 9223372036854775807) :
    (int n).val = (n : Int) := by
  change wrapInt .i64 (n : Int) = (n : Int)
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  omega

theorem list_eq_replicate {E : Type} (xs : List E) (e : E)
    (h : ∀ x ∈ xs, x = e) : xs = List.replicate xs.length e := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    change x :: xs = e :: List.replicate xs.length e
    subst x
    exact congrArg (List.cons e) ht

def decodeRowShape : Sum (I64 × I64) (List I64 × List I64) → List I64
  | .inl pair => List.replicate pair.1.val.toNat pair.2
  | .inr pair => pair.1

/-- The optimized rectangular form and ragged form both retain every row's
column count and its position. -/
def RowShapePreservesRows : Prop :=
  ∀ (sum : List I64 → Result I64) (rows : List I64) (total : I64),
    rows ≠ [] → rows.length ≤ 9223372036854775807 → sum rows = .ok total →
    (rowsToDimshape tupleGet sum rows).map decodeRowShape = .ok rows

theorem rowShapePreservesRows_proven : RowShapePreservesRows := by
  intro sum rows total nonempty fit hs
  cases rows with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs =>
    have one : (int 1).val = 1 := rfl
    have len := nativeLength_value (x :: xs).length fit
    by_cases uniform : (x :: xs).all (fun n => n.val == x.val) = true
    · have equal : ∀ n ∈ x :: xs, n = x := by
        intro n hn
        apply Subtype.ext
        simpa using List.all_eq_true.mp uniform n hn
      have repeated := list_eq_replicate (x :: xs) x equal
      have get : tupleGet (x :: xs) (int 1) = .ok x := by
        simp [tupleGet, one]
      have actual : rowsToDimshape tupleGet sum (x :: xs) =
          .ok (.inl (int (x :: xs).length, x)) := by
        simp only [rowsToDimshape, get, bind, pure, Except.bind, Except.pure]
        change (if (x :: xs).all (fun n => n.val == x.val) then
          (Except.ok (Sum.inl (int (x :: xs).length, x)) :
            Result (Sum (I64 × I64) (List I64 × List I64)))
          else (sum (x :: xs)).map (fun n => Sum.inr (x :: xs, [n]))) = _
        rw [uniform]
        rfl
      rw [actual]
      change Except.ok (List.replicate (int (x :: xs).length).val.toNat x) = _
      rw [len]
      exact congrArg Except.ok repeated.symm
    · have hn : (x :: xs).all (fun n => n.val == x.val) = false := by
        cases h : (x :: xs).all (fun n => n.val == x.val) <;> simp_all
      simp [rowsToDimshape, tupleGet, one, hn, hs, Except.map, decodeRowShape]

def HvcatEmptyContents : Prop :=
  ∀ (Rows A Ty E : Type) (rows : Rows) (t : Ty)
    (vectorAny : Result A) (vector : Ty → Result A) (values : A → List E),
    vectorAny.map values = .ok [] → (∀ t, (vector t).map values = .ok []) →
    (hvcatEmpty vectorAny rows).map values = .ok [] ∧
      (typedHvcatEmpty vector t rows).map values = .ok []

theorem hvcatEmptyContents_proven : HvcatEmptyContents := by
  intro Rows A Ty E rows t vectorAny vector values anylaw typedlaw
  exact ⟨anylaw, typedlaw t⟩

structure TypedRankArray (Ty E : Type) where
  elementType : Ty
  shape : List I64
  cells : List E

/-- Conversion may return a proper subtype of the requested storage type.
The no-dimensions fill constructor uses the converted value's runtime type. -/
def ZeroDimScalarFull : Prop :=
  ∀ (Ty X E : Type) (accepts : Ty → Ty → Prop)
    (runtimeType : E → Ty) (convert : Ty → X → Result E)
    (fill : E → Result (TypedRankArray Ty E)),
    (∀ e, fill e = .ok ⟨runtimeType e, [], [e]⟩) →
    ∀ t x,
      (∀ e, convert t x = .ok e → accepts t (runtimeType e) →
        typedHvncatZeroScalar convert fill t x = .ok ⟨t, [], [e]⟩) ∧
      (∀ error, convert t x = .error error →
        typedHvncatZeroScalar convert fill t x = .error error)

def ZeroDimNumberFull : Prop :=
  ∀ (Ty X E : Type) (accepts : Ty → Ty → Prop)
    (runtimeType : E → Ty) (convert : Ty → X → Result E)
    (fill : E → Result (TypedRankArray Ty E)),
    (∀ e, fill e = .ok ⟨runtimeType e, [], [e]⟩) →
    ∀ t x,
      (∀ e, convert t x = .ok e → accepts t (runtimeType e) →
        typedHvncatZeroNumber convert fill t x = .ok ⟨t, [], [e]⟩) ∧
      (∀ error, convert t x = .error error →
        typedHvncatZeroNumber convert fill t x = .error error)

theorem zeroDimScalarFull_refuted : ¬ ZeroDimScalarFull := by
  intro h
  have bad := (h Bool I64 I64 (fun target actual => target = false ∨ target = actual)
    (fun _ => true) (fun _ x => pure x) (fun x => pure ⟨true, [], [x]⟩)
    (fun _ => rfl) false (int 1)).1 (int 1) rfl (Or.inl rfl)
  have typeEquality : (Except.ok true : Result Bool) = .ok false :=
    congrArg (fun r => r.map TypedRankArray.elementType) bad
  cases typeEquality

theorem zeroDimNumberFull_refuted : ¬ ZeroDimNumberFull := by
  intro h
  have bad := (h Bool I64 I64 (fun target actual => target = false ∨ target = actual)
    (fun _ => true) (fun _ x => pure x) (fun x => pure ⟨true, [], [x]⟩)
    (fun _ => rfl) false (int 1)).1 (int 1) rfl (Or.inl rfl)
  have typeEquality : (Except.ok true : Result Bool) = .ok false :=
    congrArg (fun r => r.map TypedRankArray.elementType) bad
  cases typeEquality

def ZeroDimConcreteContents : Prop :=
  ∀ (Ty X E : Type) (runtimeType : E → Ty) (convert : Ty → X → Result E)
    (fill : E → Result (TypedRankArray Ty E)),
    (∀ e, fill e = .ok ⟨runtimeType e, [], [e]⟩) →
    ∀ t x e, convert t x = .ok e → runtimeType e = t →
      typedHvncatZeroScalar convert fill t x = .ok ⟨t, [], [e]⟩ ∧
      typedHvncatZeroNumber convert fill t x = .ok ⟨t, [], [e]⟩

theorem zeroDimConcreteContents_proven : ZeroDimConcreteContents := by
  intro Ty X E runtimeType convert fill law t x e hc ht
  simp [typedHvncatZeroScalar, typedHvncatZeroNumber, hc, law, ht]

def ZeroDimWrongCountRejected : Prop :=
  ∀ (Ty X A : Type) (t : Ty) (xs : X),
    ∃ message,
      typedHvncatZeroEmpty (typedHvncatZeroOnlyOne (A := A)) t =
        .error (.julia (.argumentError message)) ∧
      typedHvncatZeroAnyMany (typedHvncatZeroOnlyOne (A := A)) t xs =
        .error (.julia (.argumentError message)) ∧
      typedHvncatZeroNumbersMany (typedHvncatZeroOnlyOne (A := A)) t xs =
        .error (.julia (.argumentError message)) ∧
      typedHvncatZeroArraysMany (typedHvncatZeroOnlyOne (A := A)) t xs =
        .error (.julia (.argumentError message))

theorem zeroDimWrongCountRejected_proven : ZeroDimWrongCountRejected := by
  intro Ty X A t xs
  exact ⟨_, rfl, rfl, rfl, rfl⟩

def HvnEmptyRankSpec : Prop :=
  ∀ (Ty E : Type) (allocate : Ty → Int → List I64 → Result (TypedRankArray Ty E)),
    (∀ t n shape, (∀ d ∈ shape, 0 ≤ d.val) → int 0 ∈ shape →
      allocate t n shape = .ok ⟨t, shape, []⟩) →
    ∀ t n,
      (n < 0 → typedHvncatEmptyVal (fun n : Int => pure (decide (n < 0)))
        (fun n => pure (List.replicate n.toNat (int 0))) allocate t n =
          .error (.julia (.argumentError "concatenation dimension must be non-negative"))) ∧
      (0 < n → typedHvncatEmptyVal (fun n : Int => pure (decide (n < 0)))
        (fun n => pure (List.replicate n.toNat (int 0))) allocate t n =
          .ok ⟨t, List.replicate n.toNat (int 0), []⟩)

theorem hvnEmptyRankSpec_proven : HvnEmptyRankSpec := by
  intro Ty E allocate law t n
  constructor
  · intro hn
    simp [typedHvncatEmptyVal, hn]
    rfl
  · intro hn
    have hnot : ¬ n < 0 := by omega
    have positive : n.toNat ≠ 0 := by omega
    have valid : ∀ d ∈ List.replicate n.toNat (int 0), 0 ≤ d.val := by
      intro d hd
      have eq := (List.mem_replicate.mp hd).2
      subst d
      decide
    have alloc := law t n (List.replicate n.toNat (int 0)) valid (by simp [positive])
    simp [typedHvncatEmptyVal, hnot, alloc]

theorem typedTupleMapValues {E F : Type} (convert : E → Result F) (g : E → F)
    (xs : List E) (hc : ∀ x ∈ xs, convert x = .ok (g x)) :
    xs.mapM convert = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.mapM_cons, hc x (by simp), ih (fun y hy => hc y (by simp [hy]))]

def HvnNumbersRankSpec : Prop :=
  ∀ (Ty E F : Type) (convert : Ty → E → Result F)
    (vector : Ty → List E → Result (Ty × List F))
    (reshape : Ty × List F → List I64 → Result (TypedRankArray Ty F)),
    (∀ t xs ys, xs.mapM (convert t) = .ok ys → vector t xs = .ok (t, ys)) →
    (∀ values shape, ((shape.map fun d => d.val.toNat).prod) = values.2.length →
      reshape values shape = .ok ⟨values.1, shape, values.2⟩) →
    ∀ t n xs g,
      (n < 0 → typedHvncatNumbersVal (fun n : Int => pure (decide (n < 0)))
        (fun n => pure (n - 1)) (fun n => pure (List.replicate n.toNat (int 1)))
        (fun xs => pure (int xs.length)) vector reshape t n xs =
          .error (.julia (.argumentError "concatenation dimension must be non-negative"))) ∧
      (0 < n → xs ≠ [] → xs.length ≤ 9223372036854775807 →
        (∀ x ∈ xs, convert t x = .ok (g x)) →
        typedHvncatNumbersVal (fun n : Int => pure (decide (n < 0)))
          (fun n => pure (n - 1)) (fun n => pure (List.replicate n.toNat (int 1)))
          (fun xs => pure (int xs.length)) vector reshape t n xs =
            .ok ⟨t, List.replicate (n.toNat - 1) (int 1) ++ [int xs.length], xs.map g⟩)

theorem hvnNumbersRankSpec_proven : HvnNumbersRankSpec := by
  intro Ty E F convert vector reshape hv hr t n xs g
  constructor
  · intro hn
    simp [typedHvncatNumbersVal, hn]
    rfl
  · intro hn _ fit hc
    have hnot : ¬ n < 0 := by omega
    have nv := hv t xs (xs.map g) (typedTupleMapValues (convert t) g xs hc)
    have len := nativeLength_value xs.length fit
    have prod : ((List.replicate (n - 1).toNat (int 1) ++ [int xs.length]).map
        fun d => d.val.toNat).prod = (xs.map g).length := by
      have one : (int 1).val = 1 := rfl
      simp [List.map_append, List.map_replicate, List.prod_append, one, len]
    have reshaped := hr (t, xs.map g) _ prod
    have sub : (n - 1).toNat = n.toNat - 1 := by omega
    simpa [typedHvncatNumbersVal, hnot, nv, sub] using reshaped

/-- Independent reference for copying into a preallocated array: only cells
belonging to an argument block are overwritten. -/
def concatReferenceInto {E F : Type} (g : E → F) (background : ConcatBuffer F)
    (dims : List Bool) (xs : List (ConcatArg E)) : Except Bool (ConcatBuffer F) := do
  let shape ← referenceCatShape dims (xs.map ConcatArg.shape)
  let cells := (concatCoordinates (shape.map fun n => n.val.toNat)).zipIdx.map fun (p, k) =>
    match concatReferenceCell dims p xs (List.replicate shape.length 0) with
    | some e => some (g e)
    | none => (background.cells[k]?).join
  return ⟨shape, cells⟩

def CatInnerComplete : Prop :=
  ∀ (E F : Type) (convert : E → Result F) (g : E → F)
    (buffer : ConcatBuffer F) (dims : List Bool) (xs : List (ConcatArg E)),
    xs ≠ [] →
    referenceCatShape dims (xs.map ConcatArg.shape) = .ok buffer.shape →
    buffer.cells.length = ((buffer.shape.map fun n => n.val.toNat).prod) →
    buffer.cells.length ≤ 9223372036854775807 →
    (∀ a, ConcatArg.array a ∈ xs → ConcatArrayValid a) →
    (∀ x ∈ xs, ∀ e ∈ x.values, convert e = .ok (g e)) →
    (((concatInnerSource convert buffer.shape buffer.shape dims xs).run buffer).map Prod.snd).mapError
      dimensionErrorClass = concatReferenceInto g buffer dims xs ∨
      ConcatArgumentRejected xs (concatInnerSource convert buffer.shape buffer.shape dims xs) buffer

theorem catInnerComplete_refuted : ¬ CatInnerComplete := by
  intro h
  have bad := h Nat Nat (fun n => pure n) id ⟨[int 1], [none]⟩ [true]
    [.array ⟨[(int 3, int 1)], [20]⟩] (by simp) (by rfl) (by decide) (by decide)
    (by
      intro a ha
      have eq : a = ⟨[(int 3, int 1)], [20]⟩ := by simpa using ha
      subst a
      decide) (by intros; rfl)
  rcases bad with bad | ⟨_, message, rejected⟩
  · change (((concatOffset (fun n : Nat => pure n) [int 1] [int 1] [true] [int 0]
      [.array ⟨[(int 3, int 1)], [20]⟩]).run ⟨[int 1], [none]⟩).map Prod.snd).mapError
        dimensionErrorClass = _ at bad
    rw [concatOffset_shifted_singleton] at bad
    cases bad
  · change ((concatOffset (fun n : Nat => pure n) [int 1] [int 1] [true] [int 0]
      [.array ⟨[(int 3, int 1)], [20]⟩]).run ⟨[int 1], [none]⟩).map Prod.snd =
        .error (.julia (.argumentError message)) at rejected
    rw [concatOffset_shifted_singleton] at rejected
    cases rejected

inductive OrdinaryConcatFront where
  | promote | typedKeyword | vcat | typedVcat | vcatTwo | typedVcatTwo

def OrdinaryConcatFront.front : OrdinaryConcatFront → ConcatFront
  | .promote => .promote
  | .typedKeyword => .typedKeyword
  | .vcat => .vcat
  | .typedVcat => .typedVcat
  | .vcatTwo => .vcatTwo
  | .typedVcatTwo => .typedVcatTwo

def concatOrdinaryWitness : List (ConcatArg Nat) :=
  [.array ⟨[(int 1, int 0)], []⟩,
    .array ⟨[(int 1, int 2), (int 1, int 2)], [1, 2, 3, 4]⟩]

theorem concatOrdinary_shape : concatShapeAll [true] concatOrdinaryWitness =
    .ok [int 2, int 2] := by
  simp [concatOrdinaryWitness, concatShapeAll, catSizeShape, concatShapeRest,
    catSizeShapeMore, catSizeShapeDone, concatArgSize, catSizeArray, cshpCalls,
    cshpLeading, cshpMerge, cshpInitial, cshpEmpty]
  rfl

theorem concatOrdinary_offset :
    (concatOffset (fun n : Nat => pure n) [int 2, int 2] [int 2, int 2]
      [true] [int 0, int 0] concatOrdinaryWitness).run
        ⟨[int 2, int 2], [none, none, none, none]⟩ =
      .ok ([int 2, int 2], ⟨[int 2, int 2], [some 1, some 2, some 3, some 4]⟩) := by
  simp only [concatOrdinaryWitness, concatOffset, catOffsetMore, catOffsetDone]
  rfl

theorem concatOrdinary_typed :
    concatObserved (concatTypedSource (fun n : Nat => pure n) 0 [int 1] ()
      concatOrdinaryWitness) =
      .ok ⟨[int 2, int 2], [some 1, some 2, some 3, some 4]⟩ := by
  have hd : concatDims [int 1] = .ok [true] := by decide
  have first : tupleGet concatOrdinaryWitness (int 1) =
      .ok (.array ⟨[(int 1, int 0)], []⟩) := rfl
  simp only [concatObserved, concatTypedSource, catTyped, hd, concatOrdinary_shape, first,
    concatInnerSource, catInner, bind, pure, Except.bind, Except.pure, StateT.run,
    StateT.bind, StateT.pure, StateT.lift]
  change (((concatOffset (fun n : Nat => pure n) [int 2, int 2] [int 2, int 2]
    [true] [int 0, int 0] concatOrdinaryWitness).run
      ⟨[int 2, int 2], [none, none, none, none]⟩).map Prod.snd).mapError dimensionErrorClass = _
  rw [concatOrdinary_offset]
  rfl

theorem concatOrdinary_front (front : OrdinaryConcatFront) :
    concatObserved (concatFrontSource front.front (fun n : Nat => pure n) 0 [int 1]
      concatOrdinaryWitness) =
      .ok ⟨[int 2, int 2], [some 1, some 2, some 3, some 4]⟩ := by
  have one : (int 1).val = 1 := rfl
  have two : (int 2).val = 2 := rfl
  cases front <;>
    simpa [concatFrontSource, OrdinaryConcatFront.front, catTypedKeyword,
      vcatAny, typedVcatAny, vcatTwoArrays, typedVcatTwoArrays, catKeyword,
      concatKeywordSource, catSameArrays, ConcatArg.isArray,
      concatPromoteSource, catPromote, concatPromotionSource, promoteEltypeofArrays, concatOrdinaryWitness,
      tupleGet, one, two, concatObserved, bind, pure, Except.bind, Except.pure, StateT.run,
      StateT.bind, StateT.pure, StateT.lift] using concatOrdinary_typed

theorem concatOrdinaryComplete_refuted (front : OrdinaryConcatFront) :
    ¬ ConcatFrontendComplete front.front true := by
  intro h
  have pre : ConcatInputValid [int 1] concatOrdinaryWitness := by
    refine ⟨by simp, ?_, by simp [concatOrdinaryWitness], ?_, ?_, ?_⟩
    · intro d hd
      have : d = int 1 := List.mem_singleton.mp hd
      subst d
      decide
    · intro x hx n hn
      simp only [concatOrdinaryWitness, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · have hn : n = int 0 := by simpa [ConcatArg.shape] using hn
        subst n
        decide
      · have hn : n = int 2 := by simpa [ConcatArg.shape] using hn
        subst n
        decide
    · intro a ha
      simp only [concatOrdinaryWitness, List.mem_cons, List.not_mem_nil, or_false,
        ConcatArg.array.injEq] at ha
      rcases ha with rfl | rfl <;> decide
    · intro shape hshape
      change (Except.error true : Except Bool (List Int)) = .ok shape at hshape
      cases hshape
  have pre' : ConcatInputValid (front.front.dimensions [int 1]) concatOrdinaryWitness := by
    cases front <;> exact pre
  have arity : front.front.accepts concatOrdinaryWitness := by
    cases front <;> simp [OrdinaryConcatFront.front, ConcatFront.accepts, concatOrdinaryWitness]
  have axes : ∀ a, ConcatArg.array a ∈ concatOrdinaryWitness →
      ∀ axis ∈ a.axes, axis.1 = int 1 := by
    intro a ha
    simp only [concatOrdinaryWitness, List.mem_cons, List.not_mem_nil, or_false,
      ConcatArg.array.injEq] at ha
    rcases ha with rfl | rfl <;> simp
  have bad := h Nat Nat (fun n => pure n) id 0 [int 1] concatOrdinaryWitness arity pre'
    (fun _ => axes) (by intros; rfl)
  rw [concatOrdinary_front] at bad
  have reference : concatReference id 0 (concatFlags (front.front.dimensions [int 1]))
      concatOrdinaryWitness = .error true := by cases front <;> rfl
  rw [reference] at bad
  rcases bad with impossible | ⟨_, message, rejected⟩
  · cases impossible
  · have actual := concatOrdinary_front front
    unfold concatObserved at actual
    rw [rejected] at actual
    cases actual

def CatRow1905Ordinary : Prop := ConcatFrontendComplete .promote true
theorem catRow1905Ordinary_refuted : ¬ CatRow1905Ordinary := concatOrdinaryComplete_refuted .promote
def CatRow1918Ordinary : Prop := ConcatFrontendComplete .typedKeyword true
theorem catRow1918Ordinary_refuted : ¬ CatRow1918Ordinary := concatOrdinaryComplete_refuted .typedKeyword
def CatRow2003Ordinary : Prop := ConcatFrontendComplete .vcat true
theorem catRow2003Ordinary_refuted : ¬ CatRow2003Ordinary := concatOrdinaryComplete_refuted .vcat
def CatRow2055Ordinary : Prop := ConcatFrontendComplete .typedVcat true
theorem catRow2055Ordinary_refuted : ¬ CatRow2055Ordinary := concatOrdinaryComplete_refuted .typedVcat
def CatRow2176Ordinary : Prop := ConcatFrontendComplete .vcatTwo true
theorem catRow2176Ordinary_refuted : ¬ CatRow2176Ordinary := concatOrdinaryComplete_refuted .vcatTwo
def CatRow2185Ordinary : Prop := ConcatFrontendComplete .typedVcatTwo true
theorem catRow2185Ordinary_refuted : ¬ CatRow2185Ordinary := concatOrdinaryComplete_refuted .typedVcatTwo

def CatRow1918 : Prop := ConcatFrontendComplete .typedKeyword
theorem catRow1918_refuted : ¬ CatRow1918 := concatFrontendComplete_refuted .typedKeyword
def CatRow2003 : Prop := ConcatFrontendComplete .vcat
theorem catRow2003_refuted : ¬ CatRow2003 := concatFrontendComplete_refuted .vcat
def CatRow2053 : Prop := ConcatFrontendComplete .hcat
theorem catRow2053_refuted : ¬ CatRow2053 := concatFrontendComplete_refuted .hcat
def CatRow2055 : Prop := ConcatFrontendComplete .typedVcat
theorem catRow2055_refuted : ¬ CatRow2055 := concatFrontendComplete_refuted .typedVcat
def CatRow2056 : Prop := ConcatFrontendComplete .typedHcat
theorem catRow2056_refuted : ¬ CatRow2056 := concatFrontendComplete_refuted .typedHcat
def CatRow2175 : Prop := ConcatFrontendComplete .vcatOne
theorem catRow2175_refuted : ¬ CatRow2175 := concatFrontendComplete_refuted .vcatOne
def CatRow2176 : Prop := ConcatFrontendComplete .vcatTwo
theorem catRow2176_refuted : ¬ CatRow2176 := concatFrontendComplete_refuted .vcatTwo
def CatRow2177 : Prop := ConcatFrontendComplete .vcatArrays
theorem catRow2177_refuted : ¬ CatRow2177 := concatFrontendComplete_refuted .vcatArrays
def CatRow2178 : Prop := ConcatFrontendComplete .vcatMixed
theorem catRow2178_refuted : ¬ CatRow2178 := concatFrontendComplete_refuted .vcatMixed
def CatRow2179 : Prop := ConcatFrontendComplete .hcatOne
theorem catRow2179_refuted : ¬ CatRow2179 := concatFrontendComplete_refuted .hcatOne
def CatRow2180 : Prop := ConcatFrontendComplete .hcatTwo
theorem catRow2180_refuted : ¬ CatRow2180 := concatFrontendComplete_refuted .hcatTwo
def CatRow2181 : Prop := ConcatFrontendComplete .hcatArrays
theorem catRow2181_refuted : ¬ CatRow2181 := concatFrontendComplete_refuted .hcatArrays
def CatRow2182 : Prop := ConcatFrontendComplete .hcatMixed
theorem catRow2182_refuted : ¬ CatRow2182 := concatFrontendComplete_refuted .hcatMixed
def CatRow2184 : Prop := ConcatFrontendComplete .typedVcatOne
theorem catRow2184_refuted : ¬ CatRow2184 := concatFrontendComplete_refuted .typedVcatOne
def CatRow2185 : Prop := ConcatFrontendComplete .typedVcatTwo
theorem catRow2185_refuted : ¬ CatRow2185 := concatFrontendComplete_refuted .typedVcatTwo
def CatRow2186 : Prop := ConcatFrontendComplete .typedVcatArrays
theorem catRow2186_refuted : ¬ CatRow2186 := concatFrontendComplete_refuted .typedVcatArrays
def CatRow2187 : Prop := ConcatFrontendComplete .typedHcatOne
theorem catRow2187_refuted : ¬ CatRow2187 := concatFrontendComplete_refuted .typedHcatOne
def CatRow2188 : Prop := ConcatFrontendComplete .typedHcatTwo
theorem catRow2188_refuted : ¬ CatRow2188 := concatFrontendComplete_refuted .typedHcatTwo
def CatRow2189 : Prop := ConcatFrontendComplete .typedHcatArrays
theorem catRow2189_refuted : ¬ CatRow2189 := concatFrontendComplete_refuted .typedHcatArrays
def CatPublicComplete : Prop := ConcatFrontendComplete .keyword
theorem catPublicComplete_refuted : ¬ CatPublicComplete := concatFrontendComplete_refuted .keyword
def CatSameArraysComplete : Prop := ConcatFrontendComplete .sameArrays
theorem catSameArraysComplete_refuted : ¬ CatSameArraysComplete := concatFrontendComplete_refuted .sameArrays

/-! Nothing to promise:
vcat@1732: forwards element-type promotion and the tuple to typed_vcat.
vcat@1733: forwards the known element type and vector tuple to typed_vcat.
_typed_vcat_similar@1740: forwards the first vector exemplar and requested length to similar.
typed_hcat@1755: packages varargs into the tuple passed to _typed_hcat.
hcat@1765: forwards element-type promotion and the tuple to typed_hcat.
hcat@1766: forwards the known element type and array tuple to typed_hcat.
vcat@1802: forwards element-type promotion and the tuple to typed_vcat.
vcat@1803: forwards the known element type and array tuple to typed_vcat.
typed_vcat@1825: packages varargs into the tuple passed to _typed_vcat.
reduce@1827: computes the promoted element type and forwards to _typed_vcat.
reduce@1830: computes the promoted element type and forwards to _typed_hcat.
cat_size@1836: supplies the fixed scalar size tuple used by shape concatenation.
cat_size@1837: forwards array size to size.
cat_size@1838: supplies scalar singleton dimensions.
cat_size@1839: forwards array dimension size to size.
cat_length@1841: supplies the fixed scalar element count.
cat_length@1842: forwards array element count to length.
cat_ndims@1844: supplies the fixed scalar rank.
cat_ndims@1845: forwards array rank to ndims.
cat_indices@1847: constructs the singleton scalar axis through OneTo.
cat_indices@1848: forwards array axes to axes.
cat_similar@1850: forwards tuple shape to Array allocation.
cat_similar@1851: splats vector shape into Array allocation.
cat_similar@1852: forwards tuple shape to Array allocation.
cat_similar@1853: splats vector shape into Array allocation.
cat_similar@1854: forwards abstract array allocation to similar.
cat_similar@1855: splats vector shape into similar.
cat_shape@1858: returns an already-computed native integer shape.
_cat_size_shape@1869: returns the completed shape once the operand tuple is empty.
hvcat_rows@2194: packages row lengths and flattened row tuples for hvcat.
typed_hvcat_rows@2195: forwards the type, row lengths and flattened values to typed_hvcat.
hvcat@2244: forwards promoted array element type and the unchanged operands to typed_hvcat.
hvcat@2245: forwards the known array element type and unchanged operands to typed_hvcat.
typed_hvcat@2248: forwards the dimension shape and row-first flag to typed_hvncat.
hvcat@2274: forwards numeric type promotion and unchanged operands to typed_hvcat.
hvcat@2275: forwards element-type promotion and unchanged operands to typed_hvcat.
hvcat@2277: forwards element-type promotion and unchanged mixed operands to typed_hvcat.
typed_hvcat@2292: forwards the dimension shape and row-first flag to typed_hvncat.
hvncat@2381: forwards the supplied shape, order and operands to _hvncat.
hvncat@2382: forwards the dimension and operands with the row-first dispatch flag.
_hvncat@2384: forwards the Any type token and empty operand tuple to _typed_hvncat.
_hvncat@2385: forwards element-type promotion, shape, order and operands to _typed_hvncat.
_hvncat@2386: forwards the homogeneous numeric type, shape, order and operands.
_hvncat@2387: forwards numeric type promotion, shape, order and operands.
_hvncat@2388: forwards array element-type promotion, shape, order and operands.
_hvncat@2389: forwards the homogeneous array element type, shape, order and operands.
typed_hvncat@2392: forwards explicit type, tuple shape, order and operands to _typed_hvncat.
typed_hvncat@2393: packages the supplied native dimension as a Val dispatch argument.
_typed_hvncat@2400: forwards array conversion to broadcast, preserving its result and errors.
_typed_hvncat@2409: packages the native dimension as Val and forwards the unchanged operands.
_sub2ind@3167: forwards the array's axes and unchanged subscript tuple.
_sub2ind@3178: packages the initial one-based linear position for an empty subscript tuple.
_sub2ind@3179: packages the initial one-based linear position for an empty subscript tuple.
_sub2ind@3180: packages the initial one-based linear position for an empty subscript tuple.
_sub2ind@3184: forwards dimension metadata and initializes the recursion's stride and position.
_sub2ind@3190: forwards the OneTo axis and initializes the recursion's stride and position.
_sub2ind@3191: forwards an already canonical OneTo scalar coordinate unchanged.
-/


/-- Canonical scalar readers may be supplied by the array implementation.
Tuple access and recursion follow the source `ith_all` methods. -/
def sourceIthAll {m : Type → Type} [Monad m] [MonadExceptOf ArrayError m]
    {I A E : Type} (read : A → I → m E) (i : I) (arrays : List A) : m (List E) :=
  match arrays with
  | [] => pure (ithAllEmpty (E := E) i)
  | _ :: rest =>
    ithAll
      (fun xs : List A => match xs with
        | [] => throw (.julia .boundsError)
        | x :: _ => pure x)
      read (fun xs => pure xs.tail)
      (fun j _ => sourceIthAll read j rest) i arrays
termination_by arrays.length

theorem sourceIthAll_mapM {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadExceptOf ArrayError m] {I A E : Type} (read : A → I → m E)
    (i : I) (arrays : List A) :
    sourceIthAll read i arrays = arrays.mapM (fun a => read a i) := by
  induction arrays with
  | nil => simp [sourceIthAll, ithAllEmpty]
  | cons a arrays ih =>
    simp [sourceIthAll, ithAll, ih, List.mapM_cons]

def IthAllContents : Prop :=
  ∀ (I A E : Type) (read : A → I → Result E) (i : I) (arrays : List A),
  sourceIthAll read i arrays = arrays.mapM (fun a => read a i) ∧
  (∀ (value : A → E), (∀ a ∈ arrays, read a i = .ok (value a)) →
    sourceIthAll read i arrays = .ok (arrays.map value)) ∧
  (∀ (before after : List A) (a : A) (error : ArrayError),
    (∀ x ∈ before, ∃ e, read x i = .ok e) → read a i = .error error →
    sourceIthAll read i (before ++ a :: after) = .error error)

theorem ithAllContents_proven : IthAllContents := by
  intro I A E read i arrays
  refine ⟨sourceIthAll_mapM read i arrays, ?_, ?_⟩
  · intro value law
    rw [sourceIthAll_mapM]
    induction arrays with
    | nil => rfl
    | cons a arrays ih =>
      simp only [List.mapM_cons, List.map_cons]
      rw [law a (by simp)]
      rw [ih (fun x hx => law x (by simp [hx]))]
      rfl
  · intro before after a error hp failed
    rw [sourceIthAll_mapM]
    induction before with
    | nil => simp [failed]
    | cons x before ih =>
      obtain ⟨e, he⟩ := hp x (by simp)
      simp only [List.cons_append, List.mapM_cons]
      rw [he]
      rw [ih (fun x hx => hp x (by simp [hx]))]
      rfl

def foreachLog {E F : Type} (value : E → F) (x : E) :
    StateT (List F) Result Unit :=
  fun log => .ok ((), log ++ [value x])

theorem foreach_log {E F : Type} (value : E → F) (xs : List E) (log : List F) :
    (JuliaLean.base.abstractarray.foreach (foreachLog value) xs).run log =
      .ok ((), log ++ xs.map value) := by
  induction xs generalizing log with
  | nil =>
    simp [JuliaLean.base.abstractarray.foreach, List.forIn_nil,
      bind, pure, StateT.run, StateT.bind, StateT.pure]
  | cons x xs ih =>
    simpa [JuliaLean.base.abstractarray.foreach, List.forIn_cons, foreachLog,
      StateT.run, StateT.bind, StateT.pure, List.append_assoc] using ih (log ++ [value x])

def ForeachIterationOrder : Prop :=
  ∀ (E F : Type) (value : E → F) (xs : List E) (log : List F),
    (JuliaLean.base.abstractarray.foreach (foreachLog value) xs).run log =
      .ok ((), log ++ xs.map value)

theorem foreachIterationOrder_proven : ForeachIterationOrder := by
  intro E F value xs log
  exact foreach_log value xs log

def ForeachZipIterationOrder : Prop :=
  ∀ (E F G : Type) (value : E × F → G) (xs : List E) (ys : List F) (log : List G),
    (foreachZip (fun xs ys => pure (xs.zip ys)) (foreachLog value) xs ys).run log =
      .ok ((), log ++ (xs.zip ys).map value)

theorem foreachZipIterationOrder_proven : ForeachZipIterationOrder := by
  intro E F G value xs ys log
  simpa [foreachZip, JuliaLean.base.abstractarray.foreach,
    bind, pure, StateT.run, StateT.bind, StateT.pure]
    using foreach_log value (xs.zip ys) log

def UnsupportedMapRejected : Prop :=
  ∀ (F D S R : Type) (f : F) (dict : D) (set : S),
    (∃ message, mapDictionary (R := R) f dict = .error (.errorException message)) ∧
    (∃ message, mapSet (R := R) f set = .error (.errorException message))

theorem unsupportedMapRejected_proven : UnsupportedMapRejected := by
  intro F D S R f dict set
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

def indexedWrite {I E : Type} (_ : Unit) (i : I) (value : E) :
    StateT (List (I × E)) Result Unit :=
  fun log => .ok ((), log ++ [(i, value)])

def sourceIndexedWrite {I E : Type} (dest : Unit) (i : I) (value : E) :
    StateT (List (I × E)) Result Unit :=
  setindexArray (fun _ => pure ())
    (fun style a indices => StateT.lift (errorCanonicalSetindexOther style a indices))
    (fun _ indices => pure indices)
    (fun _ dest value i => indexedWrite dest i value) dest value i

def mapPairsAction {I J E F : Type} (read : J → E) (f : E → Result F)
    (pairs : List (I × J)) : StateT (List (I × F)) Result Unit := do
  for (i, j) in pairs do
    let value ← StateT.lift (f (read j))
    sourceIndexedWrite () i value

theorem mapPairsAction_reference {I J E F : Type} (read : J → E) (f : E → Result F)
    (pairs : List (I × J)) (log : List (I × F)) :
    (mapPairsAction read f pairs).run log =
      (pairs.mapM (fun pair => (f (read pair.2)).map (fun v => (pair.1, v)))).map
        (fun writes => ((), log ++ writes)) := by
  induction pairs generalizing log with
  | nil =>
    simp [mapPairsAction, List.forIn_nil, StateT.run, StateT.bind, StateT.pure, Except.map]
  | cons pair pairs ih =>
    rcases pair with ⟨i, j⟩
    cases call : f (read j) with
    | error error =>
      simp [mapPairsAction, List.forIn_cons, sourceIndexedWrite, setindexArray,
        call, StateT.run, StateT.bind, StateT.lift, Except.map]
    | ok value =>
      have next := ih (log ++ [(i, value)])
      cases tailResult : pairs.mapM
          (fun pair => (f (read pair.2)).map (fun v => (pair.1, v))) with
      | error error =>
        rw [tailResult] at next
        simp only [Except.map] at tailResult
        simpa [mapPairsAction, List.forIn_cons, sourceIndexedWrite, setindexArray,
          errorCanonicalSetindexOther, indexedWrite, call, StateT.run, StateT.bind,
          StateT.lift, StateT.pure, List.mapM_cons, tailResult, Except.map] using next
      | ok writes =>
        rw [tailResult] at next
        simp only [Except.map] at tailResult
        simpa [mapPairsAction, List.forIn_cons, sourceIndexedWrite, setindexArray,
          errorCanonicalSetindexOther, indexedWrite, call, StateT.run, StateT.bind,
          StateT.lift, StateT.pure, List.append_assoc, List.mapM_cons, tailResult,
          Except.map] using next

def sourceMapOne {A I J E F : Type} (source : A) (destIndices : List I)
    (sourceIndices : List J) (read : A → J → E) (f : E → Result F) :
    StateT (List (I × F)) Result Unit :=
  mapInplaceOne (fun dest : Unit => StateT.lift (eachindexArray (fun _ : Unit => pure ())
      (fun _ _ => pure destIndices) dest))
    (fun a => StateT.lift (eachindexArray (fun _ : A => pure ())
      (fun _ _a => pure sourceIndices) a))
    (fun is js => pure (is.zip js))
    (fun a j => pure (read a j)) sourceIndexedWrite
    (fun e => StateT.lift (f e)) () source

def MapOneContents : Prop :=
  ∀ (A I J E F : Type) (source : A) (destIndices : List I) (sourceIndices : List J)
    (read : A → J → E) (f : E → Result F) (log : List (I × F)),
    (sourceMapOne source destIndices sourceIndices read f).run log =
      ((destIndices.zip sourceIndices).mapM fun pair =>
        (f (read source pair.2)).map (fun value => (pair.1, value))).map
        (fun writes => ((), log ++ writes))

theorem state_pure_bind {S A B : Type} (a : A) (f : A → StateT S Result B) :
    (StateT.pure a).bind f = f a := by
  funext state
  rfl

theorem mapOneContents_proven : MapOneContents := by
  intro A I J E F source destIndices sourceIndices read f log
  simpa [sourceMapOne, mapInplaceOne, eachindexArray, mapPairsAction,
    bind, pure, state_pure_bind, StateT.run, StateT.bind, StateT.lift, StateT.pure]
    using mapPairsAction_reference (read source) f (destIndices.zip sourceIndices) log

def MapInplaceContents : Prop :=
  ∀ (I E : Type) (indices : List I) (read : I → E)
    (f : E → Result E) (log : List (I × E)),
    (mapInplace
      (fun mapF (dest : Unit) source =>
        mapInplaceOne
          (fun dest : Unit => StateT.lift (eachindexArray (fun _ : Unit => pure ())
            (fun _ _ => pure indices) dest))
          (fun source : Unit => StateT.lift (eachindexArray (fun _ : Unit => pure ())
            (fun _ _ => pure indices) source))
          (fun is js => pure (is.zip js))
          (fun (_ : Unit) i => pure (read i)) sourceIndexedWrite mapF dest source)
      (fun e => StateT.lift (f e)) ()).run log =
      (indices.mapM fun i => (f (read i)).map (fun value => (i, value))).map
        (fun writes => ((), log ++ writes))

theorem mapInplaceContents_proven : MapInplaceContents := by
  intro I E indices read f log
  have operation := mapOneContents_proven Unit I I E E () indices indices
    (fun _ i => read i) f log
  have zipped : ∀ xs : List I,
      (xs.zip xs).mapM (fun pair => (f (read pair.2)).map (fun value => (pair.1, value))) =
      xs.mapM (fun i => (f (read i)).map (fun value => (i, value))) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.zip_cons_cons, List.mapM_cons, ih]
  simpa only [mapInplace, sourceMapOne, zipped] using operation

def sourceIterationIndices {A I : Type} (indices : List I) (a : A) : Result (List I) :=
  eachindexArray (fun _ : A => pure ()) (fun _ _ => pure indices) a

def sourceMapTwo {A B I J K E F G : Type} (a : A) (b : B)
    (destIndices : List I) (indicesA : List J) (indicesB : List K)
    (readA : A → J → E) (readB : B → K → F) (f : E → F → Result G) :
    StateT (List (I × G)) Result Unit :=
  mapInplaceTwo
    (fun dest : Unit => StateT.lift (sourceIterationIndices destIndices dest))
    (fun a => StateT.lift (sourceIterationIndices indicesA a))
    (fun b => StateT.lift (sourceIterationIndices indicesB b))
    (fun is js ks => pure (is.zip (js.zip ks)))
    (fun a j => pure (readA a j)) (fun b k => pure (readB b k))
    sourceIndexedWrite (fun e f' => StateT.lift (f e f')) () a b

def MapTwoContents : Prop :=
  ∀ (A B I J K E F G : Type) (a : A) (b : B)
    (destIndices : List I) (indicesA : List J) (indicesB : List K)
    (readA : A → J → E) (readB : B → K → F) (f : E → F → Result G)
    (log : List (I × G)),
    (sourceMapTwo a b destIndices indicesA indicesB readA readB f).run log =
      ((destIndices.zip (indicesA.zip indicesB)).mapM fun entry =>
        (f (readA a entry.2.1) (readB b entry.2.2)).map
          (fun value => (entry.1, value))).map (fun writes => ((), log ++ writes))

theorem mapTwoContents_proven : MapTwoContents := by
  intro A B I J K E F G a b destIndices indicesA indicesB readA readB f log
  have operation := mapPairsAction_reference
    (fun indices : J × K => (readA a indices.1, readB b indices.2))
    (fun values => f values.1 values.2) (destIndices.zip (indicesA.zip indicesB)) log
  simpa [sourceMapTwo, sourceIterationIndices, mapInplaceTwo, eachindexArray, mapPairsAction,
    bind, pure, state_pure_bind, StateT.run, StateT.bind, StateT.lift, StateT.pure]
    using operation

def denseIterationUpper (shape : List Nat) : Result I64 :=
  eachindexDense (fun shape : List Nat => pure (int shape.prod)) id shape

def sourceEachindexTwo (a b : List Nat) : Result I64 :=
  eachindexTwo (fun _ _ => pure ())
    (fun _ a b =>
      eachindexLinearMany (n := 1) (B := fun _ => List Nat)
        denseIterationUpper (fun _ => denseIterationUpper)
        (fun a b => decide (a = b))
        (fun a bs => throwEachindexMismatch
          (fun a bs => joinCommaAndTwo a (bs.headD ""))
          "indices" (toString a.val) (bs.map fun b => toString b.val))
        a (fun _ => b)) a b

def EachindexSizeMismatch : Prop :=
  ∀ a b : List Nat, a.prod ≤ 9223372036854775807 → b.prod ≤ 9223372036854775807 →
    a ≠ b → ∃ message, sourceEachindexTwo a b = .error (.dimensionMismatch message)

theorem eachindexSizeMismatch_refuted : ¬ EachindexSizeMismatch := by
  intro promise
  obtain ⟨message, rejected⟩ := promise [2, 3] [3, 2] (by decide) (by decide) (by decide)
  have actual : sourceEachindexTwo [2, 3] [3, 2] = .ok (int 6) := by rfl
  rw [actual] at rejected
  cases rejected

def sourceAxisCheck (axis : I64 × I64) (i : I64) : Result Bool :=
  checkindexReal (fun axis : I64 × I64 => pure axis.1) (fun axis => pure axis.2)
    (fun lo i => pure (decide (lo.val ≤ i.val)))
    (fun i hi => pure (decide (i.val ≤ hi.val))) axis i

def sourceNumericAxisCheck {I : Type} (value : I → Int)
    (axis : I64 × I64) (i : I) : Result Bool :=
  checkindexReal (fun axis : I64 × I64 => pure axis.1) (fun axis => pure axis.2)
    (fun lo i => pure (decide (lo.val ≤ value i)))
    (fun i hi => pure (decide (value i ≤ hi.val))) axis i

def sourceCoordinateBounds {I : Type} (value : I → Int)
    (length : I64 × I64 → I64)
    (axes : List (I64 × I64)) (indices : List I) : Result Bool :=
  match indices with
  | [] => checkboundsIndicesNil (fun axis => pure (length axis)) axes
  | i :: rest =>
    checkboundsIndicesCons (int 1, int 1) (sourceNumericAxisCheck value)
      (fun axes _ => sourceCoordinateBounds value length axes rest) axes i rest
termination_by indices.length

def coordinateBoundsReference {I : Type} (value : I → Int)
    (length : I64 × I64 → I64)
    (axes : List (I64 × I64)) (indices : List I) : Bool :=
  ((axes.zip indices).all fun pair =>
    decide (pair.1.1.val ≤ value pair.2 ∧ value pair.2 ≤ pair.1.2.val)) &&
  ((indices.drop axes.length).all fun i => decide (value i = 1)) &&
  ((axes.drop indices.length).all fun axis => decide ((length axis).val = 1))

theorem sourceCoordinateBounds_reference {I : Type} (value : I → Int)
    (length : I64 × I64 → I64) (axes : List (I64 × I64)) (indices : List I) :
    sourceCoordinateBounds value length axes indices =
      .ok (coordinateBoundsReference value length axes indices) := by
  induction indices generalizing axes with
  | nil =>
    have result := omittedSingletonBounds_proven (I64 × I64) length axes
    have allEq : axes.all (fun axis => decide ((length axis).val = 1)) =
        decide (∀ axis ∈ axes, (length axis).val = 1) := by
      apply Bool.eq_iff_iff.mpr
      simp
    simpa [sourceCoordinateBounds, coordinateBoundsReference, allEq] using result
  | cons i indices ih =>
    cases axes with
    | nil =>
      have oneValue : (int 1).val = 1 := rfl
      by_cases equal : value i = 1
      · simp [sourceCoordinateBounds, checkboundsIndicesCons, sourceNumericAxisCheck,
          checkindexReal, ih, coordinateBoundsReference, oneValue, equal]
      · have rejected : (decide (1 ≤ value i) && decide (value i ≤ 1)) = false := by
          by_cases lower : 1 ≤ value i <;> by_cases upper : value i ≤ 1 <;>
            simp_all <;> omega
        simp [sourceCoordinateBounds, checkboundsIndicesCons, sourceNumericAxisCheck,
          checkindexReal, coordinateBoundsReference, oneValue, equal, rejected]
    | cons axis axes =>
      by_cases valid : axis.1.val ≤ value i ∧ value i ≤ axis.2.val
      · have lo := valid.1
        have hi := valid.2
        simp [sourceCoordinateBounds, checkboundsIndicesCons, sourceNumericAxisCheck,
          checkindexReal, ih, coordinateBoundsReference, lo, hi]
      · have invalid :
            (decide (axis.1.val ≤ value i) && decide (value i ≤ axis.2.val)) = false := by
          by_cases lower : axis.1.val ≤ value i <;>
            by_cases upper : value i ≤ axis.2.val <;> simp_all
        simp [sourceCoordinateBounds, checkboundsIndicesCons, sourceNumericAxisCheck,
          checkindexReal, coordinateBoundsReference, invalid]

def CartesianCoordinateBounds : Prop :=
  ∀ (I : Type) (value : I → Int) (length : I64 × I64 → I64)
    (axes : List (I64 × I64)) (indices : List I),
    checkboundsMany (fun axes => pure axes)
      (sourceCoordinateBounds value length) axes indices =
      .ok (coordinateBoundsReference value length axes indices)

theorem cartesianCoordinateBounds_proven : CartesianCoordinateBounds := by
  intro I value length axes indices
  simpa [checkboundsMany] using sourceCoordinateBounds_reference value length axes indices

def CheckIndexForms : Prop :=
  ∀ (lo hi i first last : I64) (empty : Bool),
    sourceAxisCheck (lo, hi) i = .ok (decide (lo.val ≤ i.val ∧ i.val ≤ hi.val)) ∧
    checkindexColon (lo, hi) = true ∧
    (checkindexRange
      (fun range : Bool × I64 × I64 => pure range.1)
      (fun range => pure range.2.1) (fun range => pure range.2.2)
      sourceAxisCheck (lo, hi) (empty, first, last)) =
        .ok (empty || decide
          (lo.val ≤ first.val ∧ first.val ≤ hi.val ∧
            lo.val ≤ last.val ∧ last.val ≤ hi.val))

theorem checkIndexForms_proven : CheckIndexForms := by
  intro lo hi i first last empty
  simp [sourceAxisCheck, checkindexReal, checkindexColon, checkindexRange,
    Bool.and_assoc]

noncomputable def axes1Ok {A R : Type} (axes : A → Result (List R))
    (a : {a : A // ∃ r, axes1 axes a = .ok r}) : R :=
  Classical.choose a.property

theorem axes1Ok_spec {A R : Type} (axes : A → Result (List R))
    (a : {a : A // ∃ r, axes1 axes a = .ok r}) :
    axes1 axes a.val = .ok (axes1Ok axes a) :=
  Classical.choose_spec a.property

def nativeUnitRangeAxes (range : I64 × I64) : Result (List (I64 × I64)) :=
  axesDefault (fun range : I64 × I64 =>
    pure [int (max 0 (range.2.val - range.1.val + 1))])
    (fun n => (int 1, n)) range

theorem nativeUnitRangeAxes1_success (range : I64 × I64) :
    ∃ r, axes1 nativeUnitRangeAxes range = .ok r := by
  exact ⟨(int 1, int (max 0 (range.2.val - range.1.val + 1))), rfl⟩

abbrev ReadyUnitRange :=
  {range : I64 × I64 // ∃ r, axes1 nativeUnitRangeAxes range = .ok r}

def readyUnitRange (range : I64 × I64) : ReadyUnitRange :=
  ⟨range, nativeUnitRangeAxes1_success range⟩

local instance : Inhabited ReadyUnitRange := ⟨readyUnitRange (int 1, int 0)⟩

noncomputable def readyUnitRangeAxis (range : ReadyUnitRange) : I64 × I64 :=
  axes1Ok nativeUnitRangeAxes range

theorem readyUnitRangeAxis_value (range : ReadyUnitRange) :
    readyUnitRangeAxis range =
      (int 1, int (max 0 (range.val.2.val - range.val.1.val + 1))) := by
  have expected :
      axes1 nativeUnitRangeAxes range.val =
        .ok (int 1, int (max 0 (range.val.2.val - range.val.1.val + 1))) := rfl
  exact Except.ok.inj ((axes1Ok_spec nativeUnitRangeAxes range).symm.trans expected)

def indexErrorToArray : JuliaLean.base.indices.IndexError → ArrayError
  | .methodError fn _ => .julia (.methodError fn)
  | .argumentError message => .julia (.argumentError message)
  | .dimensionMismatch message => .dimensionMismatch message
  | .boundsError => .julia .boundsError
  | .core error => .julia error

def nativeLinearIndices {A : Type} (axes : A → List ReadyUnitRange) (a : A) :
    Result (JuliaLean.base.indices.LinearIndices ReadyUnitRange) :=
  (JuliaLean.base.indices.LinearIndices_AbstractArray axes
    (JuliaLean.base.indices.LinearIndices_AbstractUnitRanges (fun range => .ok range)) a).mapError
      indexErrorToArray

noncomputable def nativeLinearFirst
    (linear : JuliaLean.base.indices.LinearIndices ReadyUnitRange) : Result I64 :=
  pure (JuliaLean.base.indices.first_LinearIndices_1 readyUnitRangeAxis Prod.fst linear)

def NativeUnitRangeLinearZeroPromise : Prop :=
  ∀ (E R : Type) (first : I64) (element : E) (updated : E → R)
    (get : I64 → Result E) (set : E → I64 → Result R),
    get first = .ok element → (∀ value, set value first = .ok (updated value)) →
    let axes := fun _ : Unit => [readyUnitRange (first, first)]
    sourceZeroLinearRead (fun _ _ => pure ())
      (nativeLinearIndices axes) nativeLinearFirst (fun _ => get) () = .ok element ∧
    (∀ default, getDefaultEmpty
      (fun a => checkboundsMany (fun a => pure (axes a))
        (fun ranges (_ : List I64) =>
          checkboundsIndicesNil (fun range =>
            pure (int (range.val.2.val - range.val.1.val + 1))) ranges) a [])
      (sourceZeroLinearRead (fun _ _ => pure ())
        (nativeLinearIndices axes) nativeLinearFirst (fun _ => get)) () default =
        .ok element) ∧
    (∀ value, sourceZeroLinearWrite (fun _ _ => pure ())
      (nativeLinearIndices axes) nativeLinearFirst (fun _ => set) () value =
      .ok (updated value))

theorem nativeLinearFirst_singleton (range : I64 × I64) :
    nativeLinearFirst ⟨[readyUnitRange range]⟩ = .ok (int 1) := by
  simp [nativeLinearFirst, JuliaLean.base.indices.first_LinearIndices_1,
    readyUnitRangeAxis_value]

theorem nativeLinearIndices_singleton (range : I64 × I64) :
    nativeLinearIndices (fun _ : Unit => [readyUnitRange range]) () =
      .ok ⟨[readyUnitRange range]⟩ := rfl

theorem nativeUnitRangeLinearZeroPromise_refuted : ¬ NativeUnitRangeLinearZeroPromise := by
  intro claim
  have bad := claim I64 I64 (int 3) (int 7) id
    (fun i => if i = int 3 then .ok (int 7) else .error (.julia .boundsError))
    (fun value i => if i = int 3 then .ok value else .error (.julia .boundsError))
    (by simp) (by intro value; simp)
  have actual :
      sourceZeroLinearRead (fun _ _ => pure ())
        (nativeLinearIndices (fun _ : Unit => [readyUnitRange (int 3, int 3)]))
        nativeLinearFirst
        (fun _ i => if i = int 3 then .ok (int 7) else .error (.julia .boundsError)) () =
      .error (.julia .boundsError) := by
    simp [sourceZeroLinearRead, getindexArray, errorCanonicalGetindexOther,
      getindexLinear, toLinearEmpty, nativeLinearIndices_singleton,
      nativeLinearFirst_singleton]
    decide
  have read := bad.1
  rw [actual] at read
  cases read

def sourceCartesianStart {A I E : Type} (indices : A → List I)
    (read : A → I → Result E) (a : A) :
    Result (Option (E × (List I × List I))) := do
  let state ← iterateStartingState (fun _ => pure ())
    (fun a _ => iterateStartingCartesian
      (eachindexArray (fun _ => pure ()) (fun _ a => pure (indices a))) a) a
  iterateArray (iterateCartesian
    (fun is (_ : Unit) => pure (cursor is)) read) a state

def sourceCartesianNext {A I E : Type} (read : A → I → Result E)
    (a : A) (state : List I × List I) :
    Result (Option (E × (List I × List I))) :=
  iterateArray (iterateCartesian (fun _ rest => pure (cursor rest)) read) a state

def collectCartesianSteps {A I E : Type} (read : A → I → Result E) (a : A) :
    Nat → (List I × List I) → Result (List E)
  | 0, _ => pure []
  | fuel + 1, state => do
    match ← sourceCartesianNext read a state with
    | none => pure []
    | some (value, next) =>
      return value :: (← collectCartesianSteps read a fuel next)

def sourceCartesianCollect {A I E : Type} (indices : A → List I)
    (read : A → I → Result E) (a : A) (fuel : Nat) : Result (List E) := do
  match ← sourceCartesianStart indices read a with
  | none => pure []
  | some (value, next) =>
    return value :: (← collectCartesianSteps read a fuel next)

theorem collectCartesianSteps_values {A I E : Type} (read : A → I → Result E)
    (a : A) (original rest : List I) (fuel : Nat) (enough : rest.length ≤ fuel) :
    collectCartesianSteps read a fuel (original, rest) = rest.mapM (read a) := by
  induction rest generalizing fuel with
  | nil =>
    cases fuel <;>
      simp [collectCartesianSteps, sourceCartesianNext, iterateArray,
        iterateCartesian, cursor]
  | cons i rest ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have remaining : rest.length ≤ fuel := by simpa using enough
      cases first : read a i with
      | error error =>
        simp [collectCartesianSteps, sourceCartesianNext, iterateArray,
          iterateCartesian, cursor, first]
      | ok value =>
        simp [collectCartesianSteps, sourceCartesianNext, iterateArray,
          iterateCartesian, cursor, first, ih fuel remaining]

def CartesianIterationOrder : Prop :=
  ∀ (A I E : Type) (indices : A → List I) (read : A → I → Result E)
    (a : A) (fuel : Nat), (indices a).length ≤ fuel →
    sourceCartesianCollect indices read a fuel = (indices a).mapM (read a)

theorem cartesianIterationOrder_proven : CartesianIterationOrder := by
  intro A I E indices read a fuel enough
  cases shape : indices a with
  | nil =>
    simp [sourceCartesianCollect, sourceCartesianStart, iterateStartingState,
      iterateStartingCartesian, eachindexArray, iterateArray, iterateCartesian, cursor, shape]
  | cons i rest =>
    have remaining : rest.length ≤ fuel := by simp [shape] at enough; omega
    cases first : read a i with
    | error error =>
      simp [sourceCartesianCollect, sourceCartesianStart, iterateStartingState,
        iterateStartingCartesian, eachindexArray, iterateArray, iterateCartesian,
        cursor, shape, first]
    | ok value =>
      simp [sourceCartesianCollect, sourceCartesianStart, iterateStartingState,
        iterateStartingCartesian, eachindexArray, iterateArray, iterateCartesian,
        cursor, shape, first, collectCartesianSteps_values read a (i :: rest) rest fuel remaining]

def sourceLinearAxis (axis : I64 × I64) : Result (I64 × I64) :=
  eachindexLinearVector (axes1 (fun axis : I64 × I64 => pure [axis])) axis

def sourceLinearStart (axis : I64 × I64) : Result I64 :=
  iterateStartingState (fun _ => pure ())
    (fun axis _ => iterateStartingLinear
      (firstindexArray sourceLinearAxis (fun axis => pure axis.1)) axis) axis

def sourceLinearNext {E : Type} (read : (I64 × I64) → I64 → Result E)
    (axis : I64 × I64) (state : I64) : Result (Option (E × I64)) :=
  iterateArray (iterateInteger
    (checkboundsOne sourceLinearAxis sourceAxisCheck) read
    (fun _ => pure (int 1)) (fun a b => pure (a + b))) axis state

def LinearIterationPositions : Prop :=
  ∀ (E : Type) (read : (I64 × I64) → I64 → Result E)
    (lo hi state : I64),
    sourceLinearStart (lo, hi) = .ok lo ∧
    sourceLinearNext read (lo, hi) state =
      if 0 ≤ state.val - lo.val ∧ state.val - lo.val ≤ hi.val - lo.val then
        (read (lo, hi) state).map (fun value => some (value, int (state.val + 1)))
      else .ok none

theorem linearIterationPositions_proven : LinearIterationPositions := by
  intro E read lo hi state
  constructor
  · rfl
  · have next : state + int 1 = int (state.val + 1) := rfl
    have axisResult : sourceLinearAxis (lo, hi) = .ok (lo, hi) := rfl
    by_cases lower : lo.val ≤ state.val <;>
      by_cases upper : state.val ≤ hi.val <;>
      cases value : read (lo, hi) state <;>
      simp [sourceLinearNext, iterateArray, iterateInteger, checkboundsOne,
        axisResult, sourceAxisCheck, checkindexReal, lower, upper,
        next, value, Except.map]

theorem vcatNativeAdd (a b : Int) : int a + int b = int (a + b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a + wrapInt .i64 b) = wrapInt .i64 (a + b)
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem vcatNativeSub (a b : Int) : int a - int b = int (a - b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a - wrapInt .i64 b) = wrapInt .i64 (a - b)
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

def vcatReferenceBlocks {E : Type} (start : Int) :
    List (List E) → List ((I64 × I64) × List E)
  | [] => []
  | values :: rest =>
    ((int start, int (start + values.length - 1)), values) ::
      vcatReferenceBlocks (start + values.length) rest

def vcatTraceStep {E : Type} (values : I64 → List E) (k pos : I64) :
    StateT (List ((I64 × I64) × List E)) Result (ForInStep I64) := do
  let vector ← pure (values k)
  let last := pos + int vector.length - int 1
  sourceIndexedWrite () (pos, last) vector
  return .yield (last + int 1)

theorem vcatTraceLoop {E : Type} (values : I64 → List E) (keys : List I64)
    (start : Int) (log : List ((I64 × I64) × List E)) :
    (forIn keys (int start) (vcatTraceStep values)).run log =
      .ok (int (start + ((keys.map fun k => ((values k).length : Int)).sum)),
        log ++ vcatReferenceBlocks start (keys.map values)) := by
  induction keys generalizing start log with
  | nil => simp [List.forIn_nil, StateT.run, StateT.pure, vcatReferenceBlocks]
  | cons k keys ih =>
    have advance : start + (values k).length - 1 + 1 =
        start + (values k).length := by omega
    simpa [List.forIn_cons, vcatTraceStep, sourceIndexedWrite, setindexArray,
      errorCanonicalSetindexOther, indexedWrite, StateT.run, StateT.bind,
      StateT.pure, StateT.lift, pure_bind, vcatNativeAdd, vcatNativeSub,
      advance, vcatReferenceBlocks, List.append_assoc, Int.add_assoc] using
      ih (start + (values k).length)
        (log ++ [((int start, int (start + (values k).length - 1)), values k)])

def sourceVcatVectorFill {B E : Type} (dest : B) (count : I64) (values : I64 → List E) :
    StateT (List ((I64 × I64) × List E)) Result B :=
  typedVcatFill (fun _ => pure count)
    (fun lo hi => pure (concatRange lo hi))
    (fun vectors k => pure (vectors k))
    (fun vector => pure (int vector.length))
    (fun lo hi => pure (lo, hi))
    (fun _ slice vector => sourceIndexedWrite () slice vector) dest values

def TypedVcatVectorBlocks : Prop :=
  ∀ (B E : Type) (dest : B) (count : I64) (values : I64 → List E)
    (log : List ((I64 × I64) × List E)),
    (sourceVcatVectorFill dest count values).run log =
      .ok (dest, log ++
        vcatReferenceBlocks 1 ((concatRange (int 1) count).map values))

theorem typedVcatVectorBlocks_proven : TypedVcatVectorBlocks := by
  intro B E dest count values log
  have loop := vcatTraceLoop values (concatRange (int 1) count) 1 log
  change (do
    let _ ← forIn (concatRange (int 1) count) (int 1) (vcatTraceStep values)
    pure dest : StateT (List ((I64 × I64) × List E)) Result B).run log = _
  simp only [StateT.run, StateT.bind, StateT.pure, bind, pure]
  simp only [StateT.run] at loop
  rw [loop]
  rfl

theorem vcatNativeSum (sizes : List Int) (start : Int) :
    (sizes.map int).foldl (fun total n => total + n) (int start) =
      int (start + sizes.sum) := by
  induction sizes generalizing start with
  | nil => simp
  | cons size sizes ih =>
    simpa [vcatNativeAdd, Int.add_assoc] using ih (start + size)

theorem vcatMapLengths {E : Type} (keys : List I64) (values : I64 → List E) :
    (keys.mapM (fun k => pure (int (values k).length)) :
      StateT (List ((I64 × I64) × List E)) Result (List I64)) =
      pure (keys.map fun k => int (values k).length) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    simp only [pure] at ih ⊢
    simp only [List.mapM_cons]
    rw [ih]
    rfl

def sourceVcatVectors {E Ty : Type} (count : I64) (values : I64 → List E)
    (allocate : Ty → List I64 → Result I64) (t : Ty) :
    StateT (List ((I64 × I64) × List E)) Result I64 :=
  typedVcatVectors (A := List E) (V := I64 → List E)
    (N := I64) (Sizes := List I64) (B := I64)
    (fun vector => pure (int vector.length))
    (fun length vectors =>
      mapArray (A := I64 → List E) (E := List E) (F := I64)
        (fun f vectors => pure (f, vectors))
        (fun _ generator => (concatRange (int 1) count).mapM
          (fun k => generator.1 (generator.2 k))) length vectors)
    (fun sizes => pure (sizes.foldl (fun total n => total + n) (int 0)))
    (fun vectors t n =>
      typedVcatSimilar (fun vectors k => pure (vectors k))
        (fun exemplar t n => StateT.lift
          (similarTypeVarargs (similarFallback allocate) exemplar t [n]))
        vectors t n)
    (fun dest vectors => sourceVcatVectorFill dest count vectors) t values

def TypedVcatVectorAllocation : Prop :=
  ∀ (E Ty : Type) (count : I64) (values : I64 → List E)
    (allocate : Ty → List I64 → Result I64) (t : Ty)
    (log : List ((I64 × I64) × List E)),
    0 < count.val →
    (sourceVcatVectors count values allocate t).run log =
      (allocate t
        [int (((concatRange (int 1) count).map
          (fun k => ((values k).length : Int))).sum)]).map
        (fun dest => (dest, log ++
          vcatReferenceBlocks 1 ((concatRange (int 1) count).map values)))

theorem typedVcatVectorAllocation_proven : TypedVcatVectorAllocation := by
  intro E Ty count values allocate t log positive
  let keys := concatRange (int 1) count
  have sum := vcatNativeSum
    (keys.map fun k => ((values k).length : Int)) 0
  have mapLengths := vcatMapLengths keys values
  have normalized :
      (keys.map fun k => int (values k).length).foldl
        (fun total n => total + n) (int 0) =
      int ((keys.map fun k => ((values k).length : Int)).sum) := by
    simpa [List.map_map, Function.comp_def] using sum
  unfold sourceVcatVectors typedVcatVectors
  simp only [mapArray, pure_bind]
  rw [show concatRange (int 1) count = keys from rfl]
  rw [mapLengths]
  simp only [pure_bind, normalized, typedVcatSimilar, similarTypeVarargs,
    similarFallback, pure_bind]
  cases result : allocate t
      [int ((keys.map fun k => ((values k).length : Int)).sum)] with
  | error error =>
    simp [StateT.run, StateT.bind, StateT.lift, bind, Except.map]
  | ok dest =>
    simpa [StateT.run, StateT.bind, StateT.pure, StateT.lift, bind, pure,
      result, Except.map, keys] using
      typedVcatVectorBlocks_proven I64 E dest count values log

def EmptyStackRejected : Prop :=
  ∀ (Args R : Type) (args : Args), ∃ message,
    emptyStack (m := Result) (A := R) args = .error (.julia (.argumentError message))

theorem emptyStackRejected_proven : EmptyStackRejected := by
  intro Args R args
  exact ⟨_, rfl⟩

def vectorAxisIndices {I : Type} (first : I) (count : Nat) : Result (I × Nat) :=
  eachindexLinearVector
    (axes1 (fun axis : I × Nat => pure [axis])) (first, count)

def vectorFirstIndex {I : Type} (first : I) (count : Nat) : Result I :=
  firstindexArray (fun axis : I × Nat => vectorAxisIndices axis.1 axis.2)
    (fun axis => pure axis.1) (first, count)

def vectorLastIndex {I : Type} (last : I) (count : Nat) : Result I :=
  lastindexArray (fun axis : I × Nat => vectorAxisIndices axis.1 axis.2)
    (fun axis => pure axis.1) (last, count)

def vectorSliceRead {E I : Type} (xs : List E) (slice : I × Nat × Bool) :
    Result (List E) :=
  getindexArray (fun _ : List E => pure ())
    (fun style a indices => errorCanonicalGetindexOther style a indices)
    (fun _ indices => pure indices)
    (fun _ xs slice => pure (if slice.2.2 then
      xs.drop (xs.length - slice.2.1) else xs.take slice.2.1)) xs slice

def FirstLastVectorContents : Prop :=
  ∀ (E I : Type) (t : IntTy) (xs : List E) (first last : I) (n : JInt t)
    (length : List E → Result I64),
    (∀ xs, (length xs).map Subtype.val = .ok (xs.length : Int)) →
    (firstVectorN (fun n : JInt t => decide (n.val < 0))
      (fun xs => vectorFirstIndex first xs.length) length
      (fun n len => pure (min n.val.toNat len.val.toNat))
      (fun first count => pure (first, count, false))
      vectorSliceRead xs n =
        if n.val < 0 then .error (.julia (.argumentError "Number of elements must be non-negative"))
        else .ok (xs.take n.val.toNat)) ∧
    (lastVectorN (fun n : JInt t => decide (n.val < 0))
      (fun xs => vectorLastIndex last xs.length) length
      (fun n len => pure (min n.val.toNat len.val.toNat))
      (fun last count => pure (last, count, true))
      vectorSliceRead xs n =
        if n.val < 0 then .error (.julia (.argumentError "Number of elements must be non-negative"))
        else .ok (xs.drop (xs.length - n.val.toNat)))

theorem firstLastVectorContents_proven : FirstLastVectorContents := by
  intro E I t xs first last n length law
  have count := law xs
  cases step : length xs with
  | error error =>
    rw [step] at count
    cases count
  | ok len =>
    rw [step] at count
    have exactLength : len.val.toNat = xs.length := by
      have h := Except.ok.inj count
      rw [h]
      simp
    have clip : xs.take (min n.val.toNat xs.length) = xs.take n.val.toNat := by
      by_cases h : n.val.toNat ≤ xs.length
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right (by omega), List.take_length,
          List.take_of_length_le (by omega)]
    have suffix : xs.length - min n.val.toNat xs.length = xs.length - n.val.toNat := by omega
    have firstIndex : vectorFirstIndex first xs.length = .ok first := rfl
    have lastIndex : vectorLastIndex last xs.length = .ok last := rfl
    constructor
    · by_cases hn : n.val < 0
      · simp only [firstVectorN, hn, decide_true, ite_true]
        rfl
      · simp [firstVectorN, firstIndex, step, vectorSliceRead, getindexArray,
          errorCanonicalGetindexOther, exactLength, clip, hn]
    · by_cases hn : n.val < 0
      · simp only [lastVectorN, hn, decide_true, ite_true]
        rfl
      · simp [lastVectorN, lastIndex, step, vectorSliceRead, getindexArray,
          errorCanonicalGetindexOther, exactLength, suffix, hn]

def FirstNTupleContents : Prop :=
  ∀ (E A Taken Out : Type) (values : A → List E) (takenValues : Taken → List E)
    (outValues : Out → List E) (take : A → I64 → Result Taken)
    (collect : Taken → Result Out),
    (∀ a n, 0 ≤ n.val →
      (take a n).map takenValues = .ok ((values a).take n.val.toNat)) →
    (∀ xs, (collect xs).map outValues = .ok (takenValues xs)) →
    ∀ a n, 0 ≤ n.val →
      (firstN take collect a n).map outValues = .ok ((values a).take n.val.toNat)

theorem firstNTupleContents_proven : FirstNTupleContents := by
  intro E A Taken Out values takenValues outValues take collect ht hc a n hn
  have law := ht a n hn
  cases step : take a n with
  | error error =>
    rw [step] at law
    cases law
  | ok xs =>
    rw [step] at law
    have contents : takenValues xs = (values a).take n.val.toNat := Except.ok.inj law
    simpa [firstN, step, bind, pure, Except.bind, contents] using hc xs

def LengthIsemptyCount : Prop :=
  ∀ (A E : Type) (sizes : A → List Nat) (values : A → List E) (length : A → I64),
    (∀ a, (length a).val = (sizes a).prod) →
    (∀ a, (values a).length = (sizes a).prod) →
    ∀ a, (length a).val = (values a).length ∧
      isemptyArray (m := Result) (fun a => pure (length a)) a = .ok (values a).isEmpty

theorem lengthIsemptyCount_proven : LengthIsemptyCount := by
  intro A E sizes values length hl hv a
  have count : (length a).val = (values a).length := by rw [hl a, hv a]
  exact ⟨count, isemptyContents_proven A E values length a count⟩

/-- Julia's default axes method is instantiated directly. A custom axes
method is an interface supplied by an AbstractArray implementation. -/
inductive ComparisonAxes (A : Type) where
  | standard (sizes : A → List I64)
  | custom (axes : A → List (I64 × Nat))

def ComparisonAxes.expected : ComparisonAxes A → A → List (I64 × Nat)
  | .standard sizes, a => (sizes a).map oneBasedAxis
  | .custom axes, a => axes a

def ComparisonAxes.read : ComparisonAxes A → A → Result (List (I64 × Nat))
  | .standard sizes => axesDefault (fun a => pure (sizes a)) oneBasedAxis
  | .custom axes => fun a => pure (axes a)

theorem ComparisonAxes.read_expected (axes : ComparisonAxes A) (a : A) :
    axes.read a = .ok (axes.expected a) := by
  cases axes <;> rfl

theorem result_option_finish {B S : Type}
    (action : Result (Option B × S)) (fallback : S → B) :
    (do
      let state ← action
      match state.1 with
      | some value => pure value
      | none => pure (fallback state.2) : Result B) =
    (do let state ← action; pure (state.1.getD (fallback state.2))) := by
  cases action with
  | error _ => rfl
  | ok state =>
    rcases state with ⟨value, state⟩
    cases value <;> rfl

def isequalLoopStep {E F : Type} (compare : E × F → Bool)
    (pair : E × F) (_state : Option Bool × Unit) :
    Result (ForInStep (Option Bool × Unit)) :=
  match pair with
  | (x, y) => do
    if !compare (x, y) then pure (.done (some false, ()))
    else pure (.yield (none, ()))

theorem isequal_loop_all {E F : Type} (compare : E × F → Bool)
    (pairs : List (E × F)) :
    (do
      let result ← forIn pairs (none, ()) (isequalLoopStep compare)
      pure (result.1.getD true) : Result Bool) = .ok (pairs.all compare) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    rcases pair with ⟨x, y⟩
    cases head : compare (x, y) with
    | false => simp [List.forIn_cons, isequalLoopStep, head, List.all_cons]
    | true => simpa [List.forIn_cons, isequalLoopStep, head, List.all_cons] using ih

theorem zip_self_all_reflexive {E : Type} (compare : E → E → Bool)
    (reflexive : ∀ e, compare e e = true) (xs : List E) :
    (xs.zip xs).all (fun pair => compare pair.1 pair.2) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [reflexive x, ih]

def ArrayIsequalContents : Prop :=
  ∀ (A E : Type) (axes : ComparisonAxes A) (values : A → List E)
    (identical : A → A → Bool) (compare : E → E → Bool),
    (∀ e, compare e e = true) →
    (∀ a b, identical a b = true →
      axes.expected a = axes.expected b ∧ values a = values b) →
    (∀ a, (values a).length = ((axes.expected a).map Prod.snd).prod) →
    ∀ a b,
      arrayIsequal identical axes.read axes.read
        (fun a b => pure ((values a).zip (values b)))
        (fun x y => pure (compare x y)) a b =
      .ok (decide (axes.expected a = axes.expected b) &&
        (decide ((values a).length = (values b).length) &&
          ((values a).zip (values b)).all (fun pair => compare pair.1 pair.2)))

theorem arrayIsequalContents_proven : ArrayIsequalContents := by
  intro A E axes values identical compare reflexive identitySound wellFormed a b
  cases identity : identical a b with
  | true =>
    obtain ⟨axeq, elements⟩ := identitySound a b identity
    have allPairs := zip_self_all_reflexive compare reflexive (values b)
    simp [arrayIsequal, identity, axeq, elements, allPairs]
  | false =>
    by_cases axeq : axes.expected a = axes.expected b
    · have lengths : (values a).length = (values b).length := by
        rw [wellFormed a, wellFormed b, axeq]
      have loop := isequal_loop_all (fun pair : E × E => compare pair.1 pair.2)
        ((values a).zip (values b))
      rw [← result_option_finish (fallback := fun _ => true)] at loop
      delta isequalLoopStep at loop
      simp [arrayIsequal, ComparisonAxes.read_expected, identity, axeq, lengths] at loop ⊢
      delta concatReferenceInto.match_1 at loop
      delta Break.runK.match_1
      exact loop
    · simp [arrayIsequal, ComparisonAxes.read_expected, identity, axeq]

def comparisonNot : Option Bool → Result Bool
  | some value => pure (!value)
  | none => throw (.errorException "missing comparison has no Boolean negation")

def comparisonTruth (missing : Bool) (results : List (Option Bool)) : Option Bool :=
  if results.any (· == some false) then some false
  else if missing || results.any Option.isNone then none else some true

theorem comparisonTruth_cons (missing : Bool) (result : Option Bool)
    (results : List (Option Bool)) :
    comparisonTruth missing (result :: results) =
      match result with
      | none => comparisonTruth true results
      | some false => some false
      | some true => comparisonTruth missing results := by
  cases result with
  | none => simp [comparisonTruth, List.any_cons]
  | some value => cases value <;> simp [comparisonTruth, List.any_cons]

def equalityLoopStep {E F : Type} (compare : E × F → Option Bool)
    (pair : E × F) (state : Option (Option Bool) × Bool) :
    Result (ForInStep (Option (Option Bool) × Bool)) :=
  match pair with
  | (x, y) => do
    let eq := compare (x, y)
    if eq.isNone then pure (.yield (none, true))
    else
      let notEqual ← comparisonNot eq
      if notEqual then pure (.done (some (some false), state.2))
      else pure (.yield (none, state.2))

theorem equality_loop_truth {E F : Type} (compare : E × F → Option Bool)
    (pairs : List (E × F)) (missing : Bool) :
    (do
      let result ← forIn pairs (none, missing) (equalityLoopStep compare)
      pure (result.1.getD (if result.2 then none else some true)) :
        Result (Option Bool)) = .ok (comparisonTruth missing (pairs.map compare)) := by
  induction pairs generalizing missing with
  | nil => simp [comparisonTruth, List.forIn_nil]
  | cons pair pairs ih =>
    rcases pair with ⟨x, y⟩
    rw [List.map_cons, comparisonTruth_cons]
    cases head : compare (x, y) with
    | none =>
      simpa [List.forIn_cons, equalityLoopStep, head] using ih true
    | some value =>
      cases value with
      | false =>
        simp [List.forIn_cons, equalityLoopStep, comparisonNot, head]
      | true =>
        simpa [List.forIn_cons, equalityLoopStep, comparisonNot, head] using ih missing

def ArrayEqualityContents : Prop :=
  ∀ (A E : Type) (axes : ComparisonAxes A) (values : A → List E)
    (compare : E → E → Option Bool),
    (∀ a, (values a).length = ((axes.expected a).map Prod.snd).prod) →
    ∀ a b,
      arrayEqual axes.read axes.read
        (fun a b => pure ((values a).zip (values b)))
        (fun x y => pure (compare x y)) Option.isNone comparisonNot a b =
      .ok (if axes.expected a = axes.expected b then
        comparisonTruth false (((values a).zip (values b)).map fun pair =>
          compare pair.1 pair.2)
        else some false)

theorem arrayEqualityContents_proven : ArrayEqualityContents := by
  intro A E axes values compare wellFormed a b
  by_cases axeq : axes.expected a = axes.expected b
  · have loop := equality_loop_truth
      (fun pair : E × E => compare pair.1 pair.2) ((values a).zip (values b)) false
    rw [← result_option_finish
      (fallback := fun (missing : Bool) => if missing then none else some true)] at loop
    delta equalityLoopStep at loop
    simp [arrayEqual, ComparisonAxes.read_expected, axeq] at loop ⊢
    delta concatReferenceInto.match_1 at loop
    delta Break.runK.match_1
    exact loop
  · simp [arrayEqual, ComparisonAxes.read_expected, axeq]

/-! ## Ordered coverage continuation -/



def TupleOffsetDetection : Prop :=
  ∀ arrays : List (List I64),
    (offsetArrayTuple arrays = .ok false ↔
      ∀ axes ∈ arrays, ∀ i ∈ axes, i.val = 1) ∧
    (offsetArrayTuple arrays = .ok true ↔
      ∃ axes ∈ arrays, ∃ i ∈ axes, i.val ≠ 1)

theorem tupleOffsetDetection_proven : TupleOffsetDetection := by
  intro arrays
  rw [offsetArrayTuple_eq]
  constructor
  · constructor
    · intro h axes ha i hi
      have hn := List.any_eq_false.mp (Except.ok.inj h) i
        (List.mem_flatten.mpr ⟨axes, ha, hi⟩)
      simpa using hn
    · intro h
      congr 1
      apply List.any_eq_false.mpr
      intro i hi
      obtain ⟨axes, ha, hin⟩ := List.mem_flatten.mp hi
      simp [h axes ha i hin]
  · simp only [Except.ok.injEq, List.any_eq_true, bne_iff_ne, List.mem_flatten]
    constructor
    · rintro ⟨i, ⟨axes, ha, hi⟩, hn⟩
      exact ⟨axes, ha, i, hi, hn⟩
    · rintro ⟨axes, ha, i, hi, hn⟩
      exact ⟨i, ⟨axes, ha, hi⟩, hn⟩

def NeighborIndexPositions : Prop :=
  ∀ (A D : Type) (convert : D → Result I64) (a : A) (i : D),
    (∀ j, convert i = .ok j →
      ((IntTy.i64.min ≤ j.val - 1 ∧ j.val - 1 ≤ IntTy.i64.max) →
        (prevind convert a i).map Subtype.val = .ok (j.val - 1)) ∧
      ((IntTy.i64.min ≤ j.val + 1 ∧ j.val + 1 ≤ IntTy.i64.max) →
        (nextind convert a i).map Subtype.val = .ok (j.val + 1))) ∧
    (∀ e, convert i = .error e →
      prevind convert a i = .error e ∧ nextind convert a i = .error e)

theorem neighborIndexPositions_proven : NeighborIndexPositions := by
  intro A D convert a i
  constructor
  · intro j hj
    constructor
    · intro fit
      simp only [prevind, hj]
      change (Except.ok (wrapInt .i64 (j.val - 1)) : Result Int) = _
      rw [wrapInt_of_inRange .i64 _ fit]
    · intro fit
      simp only [nextind, hj]
      change (Except.ok (wrapInt .i64 (j.val + 1)) : Result Int) = _
      rw [wrapInt_of_inRange .i64 _ fit]
  · intro e he
    simp [prevind, nextind, he]

def BottomArrayMetadataRejected : Prop :=
  ∀ α : Type,
    (¬ ∃ value : α, eltypeBottom = .ok value) ∧
    (¬ ∃ value : α, ndimsBottom = .ok value) ∧
    (∃ message, (eltypeBottom : Result α) =
      .error (.julia (.argumentError message))) ∧
    (∃ message, (ndimsBottom : Result α) =
      .error (.julia (.argumentError message)))

theorem bottomArrayMetadataRejected_proven : BottomArrayMetadataRejected := by
  intro α
  refine ⟨?_, ?_, ⟨"Union{} does not have elements", rfl⟩,
    ⟨"Union{} does not have elements", rfl⟩⟩
  · rintro ⟨v, h⟩
    cases h
  · rintro ⟨v, h⟩
    cases h

def LastIteratorSuffix : Prop :=
  ∀ (E : Type) (Rev Taken : Type)
    (reverseIterator : List E → Result Rev)
    (take : Rev → I64 → Result Taken)
    (collect : Taken → Result (List E))
    (reverseBang : List E → Result (List E)),
    (∀ xs n, 0 ≤ n.val →
      (do collect (← take (← reverseIterator xs) n)) =
        .ok (xs.reverse.take n.val.toNat)) →
    (∀ xs, reverseBang xs = .ok xs.reverse) →
    ∀ xs n, 0 ≤ n.val →
      lastN reverseIterator take collect reverseBang xs n =
        .ok (xs.drop (xs.length - n.val.toNat))

theorem lastIteratorSuffix_proven : LastIteratorSuffix := by
  intro E Rev Taken reverseIterator take collect reverseBang ht hr xs n hn
  have h := ht xs n hn
  cases hrev : reverseIterator xs with
  | error e => simp [hrev] at h
  | ok rev =>
    cases htake : take rev n with
    | error e => simp [hrev, htake] at h
    | ok taken =>
      cases hcollect : collect taken with
      | error e => simp [hrev, htake, hcollect] at h
      | ok out =>
        have hout : out = xs.reverse.take n.val.toNat := by
          simpa [hrev, htake, hcollect] using h
        simp [lastN, hrev, htake, hcollect, hr, hout, List.reverse_take]

def TrailingStrideContiguous : Prop :=
  ∀ m n k : I64, 0 < m.val → 0 < n.val → 2 < k.val →
    stride (fun _ : Unit => pure [int 1, m])
      (fun a => pure (ndimsValue (int 2) a))
      (fun d rank : I64 => decide (d.val ≤ rank.val))
      tupleGet (fun _ : Unit => pure [m, n]) () k = .ok (m * n)

theorem trailingStrideContiguous_refuted : ¬ TrailingStrideContiguous := by
  intro h
  have bad := h (int 2) (int 3) (int 3) (by decide) (by decide) (by decide)
  revert bad
  decide

def diagnosticIndices (a b : String) : List String → String
  | [] => joinCommaAndTwo a b
  | c :: cs => joinCommaAndMany (fun _ _ => diagnosticIndices b c cs) a b (c :: cs)

def UnsupportedBoundsRejected : Prop :=
  (∀ (R I : Type) (typeName : I → String) (axis : R) (index : I),
    (¬ ∃ accepted : Bool, checkindexUnsupported typeName axis index = .ok accepted) ∧
    ∃ message, checkindexUnsupported typeName axis index =
      .error (.julia (.argumentError message))) ∧
  (∀ (Out : Type) (label a b : String) (rest : List String),
    (¬ ∃ out : Out,
      throwEachindexMismatch (fun first _ => diagnosticIndices first b rest)
        label a (b :: rest) = .ok out) ∧
    ∃ message, (throwEachindexMismatch (fun first _ => diagnosticIndices first b rest)
      label a (b :: rest) : Result Out) = .error (.dimensionMismatch message))

theorem unsupportedBoundsRejected_proven : UnsupportedBoundsRejected := by
  constructor
  · intro R I typeName axis index
    refine ⟨?_, ⟨_, rfl⟩⟩
    rintro ⟨accepted, h⟩
    cases h
  · intro Out label a b rest
    refine ⟨?_, ⟨_, rfl⟩⟩
    rintro ⟨out, h⟩
    cases h

def allocationResult {B : Type} (shape : B → List I64) (elementType : B → Type)
    (assigned : B → I64 → Bool) (t : Type) (dims : List I64)
    (operation : Result B) : Prop :=
  ∃ array, operation = .ok array ∧ shape array = dims ∧ elementType array = t ∧
    ∀ index, assigned array index = false

def allocationMetadata {B : Type} (shape : B → List I64) (elementType : B → Type)
    (t : Type) (dims : List I64) (operation : Result B) : Prop :=
  ∃ array, operation = .ok array ∧ shape array = dims ∧ elementType array = t

def SimilarFallbackAllocation : Prop :=
  ∀ (A B : Type) (construct : Type → List I64 → Result B)
    (shape : B → List I64) (elementType : B → Type) (a : A) t dims,
    (allocationMetadata shape elementType t dims (construct t dims) →
      allocationMetadata shape elementType t dims (similarFallback construct a t dims) ∧
      allocationMetadata shape elementType t dims
        (similarTypeVarargs (similarFallback construct) a t dims) ∧
      allocationMetadata shape elementType t dims
        (similarDims (similarFallback construct) t a dims) ∧
      allocationMetadata shape elementType t dims
        (similarVarargs (similarFallback construct) t a dims)) ∧
    (∀ error, construct t dims = .error error →
      similarFallback construct a t dims = .error error ∧
      similarTypeVarargs (similarFallback construct) a t dims = .error error ∧
      similarDims (similarFallback construct) t a dims = .error error ∧
      similarVarargs (similarFallback construct) t a dims = .error error)

theorem similarFallbackAllocation_proven : SimilarFallbackAllocation := by
  intro A B construct shape elementType a t dims
  constructor
  · intro allocated
    exact ⟨allocated, allocated, allocated, allocated⟩
  · intro error failed
    exact ⟨failed, failed, failed, failed⟩

def EmptyAllocationContents : Prop :=
  ∀ (A B : Type) (construct : Type → List I64 → Result B)
    (vectorEmpty : Type → Result B) (shape : B → List I64)
    (elementType : B → Type) (assigned : B → I64 → Bool) (a : A) t,
    (allocationResult shape elementType assigned t [int 0] (construct t [int 0]) →
      allocationResult shape elementType assigned t [int 0]
        (emptyVector (fun a t n =>
          similarTypeVarargs (similarFallback construct) a t [n]) a t)) ∧
    (allocationResult shape elementType assigned t [int 0] (vectorEmpty t) →
      allocationResult shape elementType assigned t [int 0]
        (emptyMutableVector vectorEmpty a t) ∧
      allocationResult shape elementType assigned t [int 0]
        (emptyMutableIterator vectorEmpty a t)) ∧
    (∀ error, construct t [int 0] = .error error →
      emptyVector (fun a t n =>
        similarTypeVarargs (similarFallback construct) a t [n]) a t = .error error) ∧
    (∀ error, vectorEmpty t = .error error →
      emptyMutableVector vectorEmpty a t = .error error ∧
      emptyMutableIterator vectorEmpty a t = .error error)

theorem emptyAllocationContents_proven : EmptyAllocationContents := by
  intro A B construct vectorEmpty shape elementType assigned a t
  refine ⟨fun allocated => allocated, fun allocated => ⟨allocated, allocated⟩, ?_, ?_⟩
  · intro error failed
    exact failed
  · intro error failed
    exact ⟨failed, failed⟩

def strideTuple {S D : Type} (mul : S → D → S) (s : S) : List D → List S
  | [] => sizeToStridesEmpty s
  | [d] => sizeToStridesLast s d
  | d :: e :: ds =>
    let result := sizeToStrides mul
      (fun next (_ : Unit) => strideTuple mul next (e :: ds)) s d ()
    result.1 :: result.2

theorem strideTuple_cons {S D : Type} (mul : S → D → S)
    (s : S) (d : D) (ds : List D) :
    strideTuple mul s (d :: ds) = s :: strideTuple mul (mul s d) ds := by
  cases ds <;> rfl

def StridePrefixPositions : Prop :=
  ∀ (S D : Type) (mul : S → D → S) (dims : List D) (start : S),
    (strideTuple mul start dims).length = dims.length ∧
    ∀ k, k < dims.length →
      (strideTuple mul start dims)[k]? = some ((dims.take k).foldl mul start)

theorem stridePrefixPositions_proven : StridePrefixPositions := by
  intro S D mul dims
  induction dims with
  | nil => intro start; exact ⟨rfl, by intro k hk; simp at hk⟩
  | cons d ds ih =>
    intro start
    have tail := ih (mul start d)
    constructor
    · simpa only [strideTuple_cons, List.length_cons] using congrArg Nat.succ tail.1
    · intro k hk
      cases k with
      | zero => simp [strideTuple_cons]
      | succ k =>
        simpa only [strideTuple_cons, List.getElem?_cons_succ,
          List.take_succ_cons, List.foldl_cons] using tail.2 k (by simpa using hk)

theorem storedBounds_total {I : Type} (value : I → Int)
    (length : I64 × I64 → I64) (axes : List (I64 × I64)) (indices : List I) :
    ∃ b, checkboundsMany (fun axes => pure axes)
      (sourceCoordinateBounds value length) axes indices = .ok b := by
  exact ⟨coordinateBoundsReference value length axes indices, by
    simpa [checkboundsMany] using sourceCoordinateBounds_reference value length axes indices⟩

noncomputable def storedBoundsBit {I : Type} (value : I → Int)
    (length : I64 × I64 → I64) (axes : List (I64 × I64)) (indices : List I) : Bool :=
  Classical.choose (storedBounds_total value length axes indices)

theorem storedBoundsBit_eq {I : Type} (value : I → Int)
    (length : I64 × I64 → I64) (axes : List (I64 × I64)) (indices : List I) :
    storedBoundsBit value length axes indices =
      coordinateBoundsReference value length axes indices := by
  have extracted := Classical.choose_spec (storedBounds_total value length axes indices)
  have actual : checkboundsMany (fun axes => pure axes)
      (sourceCoordinateBounds value length) axes indices =
        .ok (coordinateBoundsReference value length axes indices) := by
    simpa [checkboundsMany] using sourceCoordinateBounds_reference value length axes indices
  exact Except.ok.inj (extracted.symm.trans actual)

noncomputable def sourceCanonicalStored {I : Type} (value : I → Int)
    (length : I64 × I64 → I64) (axes : List (I64 × I64)) (indices : List I) :
    Except JuliaLean.BootCov.Exc Bool :=
  isstored
    (JuliaLean.base.essentials.checkboundsGeneric (storedBoundsBit value length)
      (fun _ _ => .error .bounds)) axes indices

def CanonicalStoredCoordinates : Prop :=
  ∀ (I : Type) (value : I → Int) (length : I64 × I64 → I64)
    (axes : List (I64 × I64)) (indices : List I),
    indices.length = axes.length →
    sourceCanonicalStored value length axes indices =
      if coordinateBoundsReference value length axes indices then .ok true
      else .error .bounds

theorem canonicalStoredCoordinates_proven : CanonicalStoredCoordinates := by
  intro I value length axes indices _rank
  simp only [sourceCanonicalStored, isstored, JuliaLean.base.essentials.checkboundsGeneric,
    storedBoundsBit_eq]
  cases coordinateBoundsReference value length axes indices <;> rfl

theorem nativeWrap_mod (z : Int) :
    wrapInt .i64 z % 18446744073709551616 = z % 18446744073709551616 := by
  simp only [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem nativeWrap_eq (a b : Int)
    (same : a % 18446744073709551616 = b % 18446744073709551616) :
    wrapInt .i64 a = wrapInt .i64 b := by
  have arange := wrapInt_bounds .i64 a
  have brange := wrapInt_bounds .i64 b
  have residues : wrapInt .i64 a % 18446744073709551616 =
      wrapInt .i64 b % 18446744073709551616 := by
    rw [nativeWrap_mod, nativeWrap_mod, same]
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at arange brange
  omega

theorem nativeStrideMul (a b : Int) : int a * int b = int (a * b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a * wrapInt .i64 b) = wrapInt .i64 (a * b)
  apply nativeWrap_eq
  rw [Int.mul_emod, nativeWrap_mod, nativeWrap_mod, ← Int.mul_emod]

theorem nativeProductLoop {I : Type} (read : I → Result I64)
    (keys : List I) (start : Int) :
    (do
      let result ← forIn keys (int start) (fun key product => do
        return .yield (product * (← read key)))
      pure result : Result I64) =
      (keys.mapM read).map (fun values => int (start * (values.map Subtype.val).prod)) := by
  induction keys generalizing start with
  | nil =>
    simp [List.forIn_nil, Except.map]
  | cons key keys ih =>
    cases hread : read key with
    | error error => simp [List.forIn_cons, hread, Except.map]
    | ok value =>
      have rewrap : value = int value.val := by
        apply Subtype.ext
        exact (wrapInt_of_inRange .i64 value.val value.property).symm
      have product : int start * value = int (start * value.val) := by
        calc
          int start * value = int start * int value.val :=
            congrArg (fun x => int start * x) rewrap
          _ = int (start * value.val) := nativeStrideMul start value.val
      simp only [List.forIn_cons, hread, bind, pure, Except.bind, Except.pure, product]
      simp only [bind, pure, Except.bind, Except.pure] at ih
      rw [ih]
      cases hrest : keys.mapM read with
      | error error => simp [List.mapM_cons, hread, hrest, Except.map]
      | ok values => simp [List.mapM_cons, hread, hrest, Except.map, Int.mul_assoc]

def TrailingDimensionProducts : Prop :=
  (∀ (A D : Type) (indices : D → I64 → List D)
    (convert : D → Result I64) (sizes : A → Result (List I64))
    (rank : I64) (a : A) (start : D),
    trailingSize indices (fun a => pure (ndimsValue rank a))
      (sizeDim convert sizes) a start =
      ((indices start rank).mapM (sizeDim convert sizes a)).map
        (fun dims => int ((dims.map Subtype.val).prod))) ∧
  (∀ (R D : Type) (indices : D → I64 → List D)
    (tupleLength : List R → I64) (get : List R → D → Result R)
    (length : R → Result I64) (axes : List R) (start : D),
    trailingSizeIndices indices tupleLength get length axes start =
      ((indices start (tupleLength axes)).mapM (fun i => do length (← get axes i))).map
        (fun dims : List I64 => int ((dims.map Subtype.val).prod))) ∧
  (∀ (R : Type) (length : R → Result I64) (product : List I64 → Result I64),
    (∀ dims, product dims = .ok (int ((dims.map Subtype.val).prod))) →
    ∀ axes, trailingSizeAll length product axes =
      (axes.mapM length).map (fun dims => int ((dims.map Subtype.val).prod)))

theorem trailingDimensionProducts_proven : TrailingDimensionProducts := by
  refine ⟨?_, ?_, ?_⟩
  · intro A D indices convert sizes rank a start
    have loop := nativeProductLoop (sizeDim convert sizes a) (indices start rank) 1
    simp only [bind, pure, Except.bind, Except.pure] at loop
    unfold trailingSize
    simp only [ndimsValue, bind, pure, Except.bind, Except.pure]
    rw [loop]
    cases (indices start rank).mapM (sizeDim convert sizes a) <;>
      simp [Except.map, Int.one_mul]
  · intro R D indices tupleLength get length axes start
    have loop := nativeProductLoop (fun i => do length (← get axes i))
      (indices start (tupleLength axes)) 1
    have steps :
        (fun i product => do
          let axis ← get axes i
          let n ← length axis
          pure (.yield (product * n)) : D → I64 → Result (ForInStep I64)) =
        (fun i product => do
          let n ← (do length (← get axes i))
          pure (.yield (product * n))) := by
      funext i product
      cases get axes i <;> rfl
    unfold trailingSizeIndices
    change (forIn (indices start (tupleLength axes)) (int 1)
      (fun i product => do
        let axis ← get axes i
        let n ← length axis
        pure (.yield (product * n))) >>= (fun result => .ok result) : Result I64) = _
    rw [steps]
    simp only [bind, pure, Except.bind, Except.pure] at loop ⊢
    rw [loop]
    simp only [Int.one_mul]
    change (id <$> (_ : Result I64)) = _
    exact id_map _
  · intro R length product law axes
    cases h : axes.mapM length with
    | error error => simp [trailingSizeAll, h, Except.map]
    | ok dims => simp [trailingSizeAll, h, law, Except.map]

def OneToBoundsAllWidths : Prop :=
  ∀ (t : IntTy) (last index : JInt t), 0 ≤ last.val →
    (checkindexOneTo last index = true ↔ 1 ≤ index.val ∧ index.val ≤ last.val)

theorem oneToBoundsAllWidths_proven : OneToBoundsAllWidths := by
  intro t last index nonnegative
  have indexRange := index.property
  have lastRange := last.property
  change
    (decide (wrapInt t.toUnsigned (wrapInt t (index.val - wrapInt t 1)) <
      wrapInt t.toUnsigned last.val) = true ↔ _)
  simp only [decide_eq_true_eq]
  cases t <;>
    simp [wrapInt, IntTy.toUnsigned, IntTy.min, IntTy.max,
      IntTy.signed, IntTy.bits] at indexRange lastRange ⊢ <;> omega

theorem scalarBoundsArrayLoop {I : Type} (value : I → Int)
    (axis : I64 × I64) (indices : List I) (initial : Bool) :
    (forIn indices initial (fun index accepted => do
      let valid ← sourceNumericAxisCheck value axis index
      pure (.yield (accepted && valid))) : Result Bool) =
    .ok (initial && indices.all (fun i =>
      decide (axis.1.val ≤ value i ∧ value i ≤ axis.2.val))) := by
  induction indices generalizing initial with
  | nil => simp [List.forIn_nil]
  | cons index indices ih =>
    simp only [List.forIn_cons, sourceNumericAxisCheck, checkindexReal,
      bind, pure, Except.bind, Except.pure]
    simp only [sourceNumericAxisCheck, checkindexReal,
      bind, pure, Except.bind, Except.pure] at ih
    rw [ih]
    simp [List.all_cons, Bool.and_assoc]

def ArrayIndexBoundsAll : Prop :=
  ∀ (I : Type) (value : I → Int) (lo hi : I64) (indices : List I),
    checkindexArray (sourceNumericAxisCheck value) (lo, hi) indices = .ok true ↔
      ∀ i ∈ indices, lo.val ≤ value i ∧ value i ≤ hi.val

theorem arrayIndexBoundsAll_proven : ArrayIndexBoundsAll := by
  intro I value lo hi indices
  have loop := scalarBoundsArrayLoop value (lo, hi) indices true
  simp only [bind, pure, Except.bind, Except.pure] at loop
  unfold checkindexArray
  simp only [bind, pure, Except.bind, Except.pure]
  rw [loop]
  simp

def LinearBoundsCoordinates : Prop :=
  (∀ (lo hi index : I64),
    checkboundsOne
      (eachindexLinearVector (axes1 (fun axis : I64 × I64 => pure [axis])))
      sourceAxisCheck (lo, hi) index = .ok true ↔
        lo.val ≤ index.val ∧ index.val ≤ hi.val) ∧
  (∀ (count index : I64), 0 ≤ count.val →
    (checkboundsOne
      (eachindexLinear (fun _ : Unit => pure count) (fun n => pure n))
      (fun n i => pure (checkindexOneTo n i)) () index = .ok true ↔
        1 ≤ index.val ∧ index.val ≤ count.val))

theorem linearBoundsCoordinates_proven : LinearBoundsCoordinates := by
  constructor
  · intro lo hi index
    have one : (int 1).val = 1 := rfl
    simp [checkboundsOne, eachindexLinearVector, axes1, tupleGet,
      sourceAxisCheck, checkindexReal, one, Bool.and_eq_true]
  · intro count index nonnegative
    simpa [checkboundsOne, eachindexLinear] using
      oneToBoundsAllWidths_proven .i64 count index nonnegative

/-! Nothing to promise:
eltype@246: selects the supplied element-type parameter or the unconstrained Any type token.
_join_comma_and@329: assembles the two preformatted index descriptions for a diagnostic.
_join_comma_and@330: recursively assembles preformatted index descriptions for a diagnostic.
eachindex@390: selects IndexStyle and forwards all arrays to the corresponding eachindex method.
lastindex@430: delegates the requested dimension to axes and its terminal index to last.
firstindex@453: delegates the requested dimension to axes and its initial index to first.
size_to_strides@610: packages the final accumulated stride as the singleton result tuple.
size_to_strides@611: terminates tuple construction without emitting another stride.
checkindex@752: unwraps IdentityUnitRange and forwards to the underlying range bounds method.
checkindex@755: accepts the canonical full-axis Slice marker; scalar-coordinate validation belongs to the index methods.
similar@819: forwards the array and its element-type parameter to the typed allocation method.
similar@821: forwards explicit dimensions and the array's element-type parameter.
similar@822: packages the dimension varargs and forwards to the tuple allocation method.
similar@832: delegates dimension normalization to to_shape and allocation to similar.
to_shape@836: returns the empty dimension tuple unchanged.
to_shape@837: returns a native dimension tuple unchanged.
to_shape@841: delegates checked conversion to the native integer constructor.
_to_shape@843: forwards an integer to to_shape.
_to_shape@844: delegates checked conversion to the native integer constructor.
to_shape@845: returns an AbstractUnitRange dimension token unchanged.
similar@869: packages dimension varargs for the storage-type tuple allocation method.
similar@870: delegates dimension normalization and forwards to the storage-type allocator.
similar@872: delegates legacy OneTo dimension normalization and forwards to the storage-type allocator.
similar@873: forwards storage type and dimensions to its undef constructor.
-/

/-! ## Registry -/

abbrev LawfulLinearAxis {R Ax : Type} (axes : R → Result (List Ax)) :=
  {r : R // ∃ axis, axes1 axes r = .ok axis}

noncomputable def sourceLinearFirstGeneric {R Ax : Type}
    (axes : R → Result (List Ax)) [Inhabited (LawfulLinearAxis axes)]
    (first : Ax → I64)
    (linear : JuliaLean.base.indices.LinearIndices (LawfulLinearAxis axes)) : I64 :=
  if linear.indices.length = 1 then
    JuliaLean.base.indices.first_LinearIndices_1 (axes1Ok axes) first linear
  else JuliaLean.base.indices.first_LinearIndices linear

noncomputable def sourceLinearLastGeneric {R Ax : Type}
    (axes : R → Result (List Ax)) [Inhabited (LawfulLinearAxis axes)]
    (last : Ax → I64)
    (length : JuliaLean.base.indices.LinearIndices (LawfulLinearAxis axes) → I64)
    (linear : JuliaLean.base.indices.LinearIndices (LawfulLinearAxis axes)) : I64 :=
  if linear.indices.length = 1 then
    JuliaLean.base.indices.last_LinearIndices_1 (axes1Ok axes) last linear
  else JuliaLean.base.indices.last_LinearIndices length linear

def LinearIndicesBoundsContents : Prop :=
  ∀ (R Ax : Type) (axes : R → Result (List Ax))
    [Inhabited (LawfulLinearAxis axes)] (first last : Ax → I64)
    (length : JuliaLean.base.indices.LinearIndices (LawfulLinearAxis axes) → I64)
    (positions : JuliaLean.base.indices.LinearIndices (LawfulLinearAxis axes) → List I64),
    (∀ linear, (length linear).val = 0 ↔ positions linear = []) →
    (∀ linear, positions linear ≠ [] →
      sourceLinearFirstGeneric axes first linear ∈ positions linear ∧
      sourceLinearLastGeneric axes last length linear ∈ positions linear) →
    (∀ linear p, p ∈ positions linear →
      (sourceLinearFirstGeneric axes first linear).val ≤ p.val ∧
      p.val ≤ (sourceLinearLastGeneric axes last length linear).val) →
    ∀ linear lo hi,
      (checkindexLinearIndices
        (isemptyArray (fun linear => pure (length linear)))
        (fun linear => pure (sourceLinearFirstGeneric axes first linear))
        (fun linear => pure (sourceLinearLastGeneric axes last length linear))
        sourceAxisCheck (lo, hi) linear = .ok true ↔
        ∀ p ∈ positions linear, lo.val ≤ p.val ∧ p.val ≤ hi.val)

theorem linearIndicesBoundsContents_proven : LinearIndicesBoundsContents := by
  intro R Ax axes _ first last length positions empty endpoints interval linear lo hi
  by_cases isEmpty : positions linear = []
  · have zero := (empty linear).mpr isEmpty
    simp [checkindexLinearIndices, isemptyArray, zero, isEmpty,
      sourceAxisCheck, checkindexReal]
  · have nonzero : (length linear).val ≠ 0 := by
      intro zero
      exact isEmpty ((empty linear).mp zero)
    have endpoints := endpoints linear isEmpty
    have noEmpty : ((length linear).val == 0) = false := by simp [nonzero]
    simp only [checkindexLinearIndices, isemptyArray, sourceAxisCheck, checkindexReal,
      bind, pure, Except.bind, Except.pure, noEmpty, Bool.false_or,
      Bool.and_eq_true, decide_eq_true_eq, Except.ok.injEq]
    constructor
    · rintro ⟨⟨lower, _⟩, ⟨_, upper⟩⟩ p hp
      have between := interval linear p hp
      exact ⟨Int.le_trans lower between.1, Int.le_trans between.2 upper⟩
    · intro all
      exact ⟨all _ endpoints.1, all _ endpoints.2⟩

def liftCopyHeap {I E A : Type} (operation : StateT (Heap I E) Result A) :
    StateT (I64 × Heap I E) Result A :=
  fun state => (operation.run state.2).map
    (fun result => (result.1, (state.1, result.2)))

def sourceVectorCopy {I E : Type} [DecidableEq I]
    (indices : List I) (sourceFirst : I64) (sourceCount : I64)
    (read : List E → I64 → StateT (Heap I E) Result E)
    (copy : List E → StateT (Heap I E) Result (List E))
    (copyBits : I64 → List E → StateT (Heap I E) Result I64)
    (resize : I64 → I64 → StateT (I64 × Heap I E) Result Unit)
    (dest : I64) (values : List E) : StateT (I64 × Heap I E) Result I64 :=
  copyBangVector
    (fun dest state =>
      (vectorFirstIndex dest state.1.val.toNat).map (fun first => (first, state)))
    (fun values => StateT.lift (vectorFirstIndex sourceFirst values.length))
    (fun a b : I64 => decide (a = b))
    (fun _ state => .ok (state.1, state))
    (fun _ => pure sourceCount) resize
    (fun dest values => liftCopyHeap (sourceCopyHeap indices read copy copyBits dest values))
    dest values

def VectorCopyResizeContents : Prop :=
  ∀ (I E : Type) [DecidableEq I] (indices : List I) (values : List E)
    (read : List E → I64 → StateT (Heap I E) Result E)
    (copy : List E → StateT (Heap I E) Result (List E))
    (copyBits : I64 → List E → StateT (Heap I E) Result I64)
    (resize : I64 → I64 → StateT (I64 × Heap I E) Result Unit)
    (dest sourceFirst initialCount sourceCount : I64) (heap : Heap I E),
    indices.Nodup → values.length = indices.length →
    sourceCount.val = values.length →
    (dest ≠ sourceFirst →
      ∃ message, (sourceVectorCopy indices sourceFirst sourceCount read copy copyBits
        resize dest values).run (initialCount, heap) =
          .error (.julia (.argumentError message))) ∧
    (dest = sourceFirst →
      ∀ resizedHeap,
      (if initialCount = sourceCount then .ok ((), (initialCount, heap))
        else (resize dest sourceCount).run (initialCount, heap)) =
          .ok ((), (sourceCount, resizedHeap)) →
      ∃ resultHeap, (sourceVectorCopy indices sourceFirst sourceCount read copy copyBits
        resize dest values).run (initialCount, heap) =
          .ok (dest, (sourceCount, resultHeap)) ∧
        ArrayContentsCopied indices values resizedHeap resultHeap)

theorem vectorCopyResizeContents_proven : VectorCopyResizeContents := by
  intro I E _ indices values read copy copyBits resize dest sourceFirst initialCount
    sourceCount heap distinct count _nativeCount
  have one : (int 1).val = 1 := rfl
  constructor
  · intro different
    refine ⟨"vectors must have the same offset for copy! (consider using `copyto!`)", ?_⟩
    simp [sourceVectorCopy, copyBangVector, vectorFirstIndex, vectorAxisIndices,
      firstindexArray, eachindexLinearVector, axes1, tupleGet, StateT.run,
      StateT.bind, StateT.pure, StateT.lift, different, one, Except.map] <;> rfl
  · intro same resizedHeap resized
    subst sourceFirst
    obtain ⟨resultHeap, copied, contents⟩ :=
      sourceCopyHeap_full indices values resizedHeap dest read copy copyBits distinct count
    simp only [StateT.run] at copied
    refine ⟨resultHeap, ?_, contents⟩
    by_cases equalCount : initialCount = sourceCount
    · have stateEqual : heap = resizedHeap := by
        simpa [equalCount] using resized
      subst initialCount
      subst resizedHeap
      simp [sourceVectorCopy, copyBangVector, vectorFirstIndex, vectorAxisIndices,
        firstindexArray, eachindexLinearVector, axes1, tupleGet, one, liftCopyHeap,
        copied, StateT.run, StateT.bind, StateT.pure, StateT.lift, Except.map] <;> rfl
    · have resizeRun := resized
      simp only [equalCount, ite_false] at resizeRun
      simp only [StateT.run] at resizeRun
      simp [sourceVectorCopy, copyBangVector, vectorFirstIndex, vectorAxisIndices,
        firstindexArray, eachindexLinearVector, axes1, tupleGet, one, equalCount,
        resizeRun, liftCopyHeap, copied, StateT.run, StateT.bind, StateT.pure,
        StateT.lift, Except.map] <;> rfl

def copyPositions (start : Int) : Nat → List I64
  | 0 => []
  | n + 1 => int start :: copyPositions (start + 1) n

theorem copyPositions_length (start : Int) (count : Nat) :
    (copyPositions start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [copyPositions, ih]

theorem copyPositions_get (start : Int) (count k : Nat) (hk : k < count) :
    (copyPositions start count)[k]'(by simpa [copyPositions_length] using hk) =
      int (start + k) := by
  induction count generalizing start k with
  | zero => omega
  | succ count ih =>
    cases k with
    | zero => simp [copyPositions]
    | succ k =>
      simpa [copyPositions, Int.add_assoc, Int.add_left_comm, Int.add_comm] using
        ih (start + 1) k (by omega)

def copyAtStep {D E : Type}
    (write : Bool → D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (value : E) (index : I64) : StateT (Heap I64 E) Result (ForInStep I64) := do
  write true dest index value
  pure (.yield (index + int 1))

theorem copyAtLoop {D E : Type}
    (write : Bool → D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (values : List E) (start : Int) (heap : Heap I64 E)
    (law : ∀ index ∈ copyPositions start values.length, ∀ value heap,
      (write true dest index value).run heap = .ok ((), store index value heap)) :
    (forIn values (int start) (copyAtStep write dest)).run heap =
      (prefixWrite (copyPositions start values.length) values heap).map
        (fun out => (int (start + values.length), out)) := by
  induction values generalizing start heap with
  | nil =>
    simp [List.forIn_nil, copyPositions, prefixWrite, StateT.run, StateT.pure, Except.map]
  | cons value values ih =>
    have head := law (int start) (by simp [copyPositions]) value heap
    simp only [StateT.run] at head
    have tailLaw : ∀ index ∈ copyPositions (start + 1) values.length, ∀ value heap,
        (write true dest index value).run heap = .ok ((), store index value heap) := by
      intro index member value heap
      exact law index (by simp [copyPositions, member]) value heap
    have tail := ih (start + 1) (store (int start) value heap) tailLaw
    simp only [List.forIn_cons, copyAtStep, StateT.run, StateT.bind,
      head, bind, pure, Except.bind, Except.pure, StateT.pure, vcatNativeAdd] at ⊢
    simpa [copyPositions, prefixWrite, StateT.run, Int.add_assoc, Int.add_left_comm,
      Int.add_comm] using tail

/-- The scalar writer is the destination's canonical array or user-extension
method, implemented outside this file. Its storage law is explicit in the
specification. Axis selection and lastindex use this file's source methods. -/
def sourceIterableCopyAt {D E Start Range End Difference Span : Type}
    (knownLength : Bool) (cast : Start → Result I64)
    (length : D → Result I64) (sourceCount : I64)
    (axes : D → Result (List Range)) (last : Range → Result End)
    (checked : D → I64 → Result Unit)
    (sub : End → I64 → Result Difference) (addOne : Difference → Result Span)
    (le : I64 → Span → Result Bool)
    (write : Bool → D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (start : Start) (values : List E) : StateT (Heap I64 E) Result D :=
  copytoIterableAt
    (fun i => StateT.lift (cast i)) (fun _ => pure knownLength)
    (fun dest => StateT.lift (length dest)) (fun _ => pure sourceCount)
    (fun dest => StateT.lift
      (lastindexArray (eachindexLinearVector (axes1 axes)) last dest))
    (fun dest i => StateT.lift (checked dest i))
    (fun a b => StateT.lift (sub a b)) (fun n => StateT.lift (addOne n))
    (fun a b => StateT.lift (le a b)) write dest start values

def IterableCopyAtContents : Prop :=
  ∀ (D E Start Range End Difference Span : Type)
    (cast : Start → Result I64) (length : D → Result I64) (sourceCount : I64)
    (axes : D → Result (List Range)) (last : Range → Result End)
    (checked : D → I64 → Result Unit)
    (sub : End → I64 → Result Difference) (addOne : Difference → Result Span)
    (le : I64 → Span → Result Bool)
    (write : Bool → D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (rawStart : Start) (values : List E) (start : Int)
    (destCount : I64) (range : Range) (endIndex : End) (difference : Difference)
    (span : Span) (heap : Heap I64 E),
    cast rawStart = .ok (int start) → length dest = .ok destCount →
    0 < destCount.val → sourceCount.val = values.length →
    axes dest = .ok [range] → last range = .ok endIndex →
    checked dest (int start) = .ok () →
    sub endIndex (int start) = .ok difference → addOne difference = .ok span →
    le sourceCount span = .ok true →
    (copyPositions start values.length).Nodup →
    (∀ index ∈ copyPositions start values.length, ∀ value heap,
      (write true dest index value).run heap = .ok ((), store index value heap)) →
    ∃ out, (sourceIterableCopyAt true cast length sourceCount axes last checked sub addOne le
      write dest rawStart values).run heap = .ok (dest, out) ∧
      (∀ (k : Nat) (hk : k < values.length), out (int (start + k)) = values[k]) ∧
      (∀ q, q ∉ copyPositions start values.length → out q = heap q)

theorem iterableCopyAtContents_proven : IterableCopyAtContents := by
  intro D E Start Range End Difference Span cast length sourceCount axes last checked sub
    addOne le write dest rawStart values start destCount range endIndex difference span heap
    converted sized positive count axesLaw lastLaw boundsLaw subLaw addLaw fits distinct writeLaw
  have positionsLength := copyPositions_length start values.length
  obtain ⟨out, output, unchanged⟩ :=
    prefixWrite_success (copyPositions start values.length) values heap (by omega)
  have contents := prefixWrite_at (copyPositions start values.length) values heap out
    distinct (by omega) output
  refine ⟨out, ?_, ?_, ?_⟩
  · have loop := copyAtLoop write dest values start heap writeLaw
    rw [output] at loop
    have one : (int 1).val = 1 := rfl
    cases values with
    | nil =>
      simp [sourceIterableCopyAt, copytoIterableAt, converted, sized, positive, count,
        StateT.run, StateT.bind, StateT.pure, StateT.lift] at ⊢
      have outEq : out = heap := by simpa [copyPositions, prefixWrite] using output.symm
      subst out
      rfl
    | cons value values =>
      have nonzero : sourceCount.val ≠ 0 := by
        rw [count]
        simp only [List.length_cons]
        omega
      change (forIn (value :: values) (int start) (copyAtStep write dest)).run heap =
        .ok (int (start + (value :: values).length), out) at loop
      simp only [StateT.run] at loop
      have returned : (do
          let _ ← forIn (value :: values) (int start) (copyAtStep write dest)
          pure dest : StateT (Heap I64 E) Result D).run heap = .ok (dest, out) := by
        simp only [StateT.run, bind, pure, StateT.bind, StateT.pure]
        rw [loop]
        rfl
      have stepEq :
          (fun (x : E) (i : I64) =>
            (write true dest i x).bind (fun _ => StateT.pure (.yield (i + int 1)))) =
          copyAtStep write dest := rfl
      rw [← stepEq] at returned
      simpa [sourceIterableCopyAt, copytoIterableAt, converted, sized, positive, nonzero,
        axesLaw, lastLaw, boundsLaw, subLaw, addLaw, fits, lastindexArray,
        eachindexLinearVector, axes1, tupleGet, one, List.forIn_cons, copyAtStep,
        StateT.run, StateT.bind, StateT.pure, StateT.lift] using returned
  · intro k hk
    have position := copyPositions_get start values.length k hk
    rw [← position]
    exact contents k hk
  · intro q outside
    apply unchanged q
    have allPositions : (copyPositions start values.length).take values.length =
        copyPositions start values.length := List.take_of_length_le (by omega)
    simpa [allPositions] using outside

def IterableCopyAtUnknownLength : Prop :=
  ∀ (D E Start Range End Difference Span : Type)
    (cast : Start → Result I64) (length : D → Result I64) (sourceCount : I64)
    (axes : D → Result (List Range)) (last : Range → Result End)
    (checked : D → I64 → Result Unit)
    (sub : End → I64 → Result Difference) (addOne : Difference → Result Span)
    (le : I64 → Span → Result Bool)
    (write : Bool → D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (rawStart : Start) (values : List E) (heap : Heap I64 E),
    (∀ knownLength error, cast rawStart = .error error →
      (sourceIterableCopyAt knownLength cast length sourceCount axes last checked sub addOne
        le write dest rawStart values).run heap = .error error) ∧
    (∀ start : Int, cast rawStart = .ok (int start) →
      (copyPositions start values.length).Nodup →
      (∀ index ∈ copyPositions start values.length, ∀ value heap,
        (write false dest index value).run heap = .ok ((), store index value heap)) →
      ∃ out, (sourceIterableCopyAt false cast length sourceCount axes last checked sub addOne
        le write dest rawStart values).run heap = .ok (dest, out) ∧
        (∀ (k : Nat) (hk : k < values.length), out (int (start + k)) = values[k]) ∧
        (∀ q, q ∉ copyPositions start values.length → out q = heap q))

theorem iterableCopyAtUnknownLength_proven : IterableCopyAtUnknownLength := by
  intro D E Start Range End Difference Span cast length sourceCount axes last checked sub
    addOne le write dest rawStart values heap
  constructor
  · intro knownLength error failed
    simp [sourceIterableCopyAt, copytoIterableAt, failed,
      StateT.run, StateT.bind, StateT.lift] <;> rfl
  · intro start converted distinct writeLaw
    let checkedWrite := fun (_ : Bool) d i value => write false d i value
    have positionsLength := copyPositions_length start values.length
    obtain ⟨out, output, unchanged⟩ :=
      prefixWrite_success (copyPositions start values.length) values heap (by omega)
    have contents := prefixWrite_at (copyPositions start values.length) values heap out
      distinct (by omega) output
    refine ⟨out, ?_, ?_, ?_⟩
    · have loop := copyAtLoop checkedWrite dest values start heap writeLaw
      rw [output] at loop
      change (forIn values (int start) (copyAtStep checkedWrite dest)).run heap =
        .ok (int (start + values.length), out) at loop
      simp only [StateT.run] at loop
      have returned : (do
          let _ ← forIn values (int start) (copyAtStep checkedWrite dest)
          pure dest : StateT (Heap I64 E) Result D).run heap = .ok (dest, out) := by
        simp only [StateT.run, bind, pure, StateT.bind, StateT.pure]
        rw [loop]
        rfl
      have stepEq :
          (fun (x : E) (i : I64) =>
            (write false dest i x).bind (fun _ => StateT.pure (.yield (i + int 1)))) =
          copyAtStep checkedWrite dest := rfl
      rw [← stepEq] at returned
      simpa [sourceIterableCopyAt, copytoIterableAt, converted,
        StateT.run, StateT.bind, StateT.pure, StateT.lift] using returned
    · intro k hk
      rw [← copyPositions_get start values.length k hk]
      exact contents k hk
    · intro q outside
      apply unchanged q
      have allPositions : (copyPositions start values.length).take values.length =
          copyPositions start values.length := List.take_of_length_le (by omega)
      simpa [allPositions] using outside

structure SkipSteps where
  count : Nat

def runSkipSteps {m : Type → Type} [Monad m] {β : Type}
    (body : Unit → β → m (ForInStep β)) : Nat → β → m β
  | 0, state => pure state
  | n + 1, state => do
    match ← body () state with
    | .done out => pure out
    | .yield next => runSkipSteps body n next

instance {m : Type → Type} [Monad m] : ForIn m SkipSteps Unit where
  forIn steps initial body := runSkipSteps body steps.count initial

theorem forInSkipSteps {m : Type → Type} [Monad m] {β : Type}
    (count : Nat) (initial : β) (body : Unit → β → m (ForInStep β)) :
    forIn (⟨count⟩ : SkipSteps) initial body = runSkipSteps body count initial := rfl

def skipCursorStep {E : Type} (_ : Unit) (state : Option (E × List E)) :
    Result (ForInStep (Option (E × List E))) :=
  match state with
  | none => .error (.julia (.argumentError "source has fewer elements than required"))
  | some (_, rest) => .ok (.yield (cursor rest))

theorem skipCursorSteps {E : Type} (count : Nat) (values : List E) :
    runSkipSteps skipCursorStep count (cursor values) =
      if count ≤ values.length then .ok (cursor (values.drop count))
      else .error (.julia (.argumentError "source has fewer elements than required")) := by
  induction count generalizing values with
  | zero => simp [runSkipSteps]
  | succ count ih =>
    cases values with
    | nil => simp [runSkipSteps, skipCursorStep, cursor]
    | cons value values =>
      simpa [runSkipSteps, skipCursorStep, cursor] using ih values

theorem liftSkipSteps {E β : Type}
    (body : Unit → β → Result (ForInStep β)) (count : Nat) (initial : β) :
    (runSkipSteps (fun i state => StateT.lift (body i state)) count initial :
      StateT (Heap I64 E) Result β) =
      StateT.lift (runSkipSteps body count initial) := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
    funext heap
    cases outcome : body () initial with
    | error error =>
      simp [runSkipSteps, outcome, StateT.bind, StateT.lift]
    | ok step =>
      cases step with
      | done out =>
        simp [runSkipSteps, outcome, StateT.bind, StateT.pure, StateT.lift]
      | yield next =>
        have tail := congrArg (fun action : StateT (Heap I64 E) Result β => action.run heap)
          (ih next)
        simpa [runSkipSteps, outcome, StateT.run, StateT.bind, StateT.pure, StateT.lift]
          using tail

def copySkipCount {t : IntTy} (offset : JInt t) : JInt (IntTy.promote t .i64) :=
  JInt.rem (IntTy.promote t .i64) offset - JInt.lit (IntTy.promote t .i64) 1

theorem copySkipCount_value {t : IntTy} (offset : JInt t) (positive : 1 ≤ offset.val) :
    (copySkipCount offset).val = offset.val - 1 := by
  let p := IntTy.promote t .i64
  have sourceRange := offset.property
  have convertedRange : p.min ≤ offset.val ∧ offset.val ≤ p.max := by
    cases t <;> simp [p, IntTy.promote, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] at * <;>
      omega
  have differenceRange : p.min ≤ offset.val - 1 ∧ offset.val - 1 ≤ p.max := by
    cases t <;> simp [p, IntTy.promote, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] at * <;>
      omega
  have oneRange : p.min ≤ 1 ∧ (1 : Int) ≤ p.max := by
    cases t <;> decide
  change wrapInt p (wrapInt p offset.val - wrapInt p 1) = _
  rw [wrapInt_of_inRange p _ convertedRange, wrapInt_of_inRange p 1 oneRange]
  exact wrapInt_of_inRange p _ differenceRange

def WhileEquation {m : Type → Type} [Monad m]
    (whileLoop : (β : Type) → β → (β → m (ForInStep β)) → m β) : Prop :=
  ∀ (β : Type) (initial : β) (body : β → m (ForInStep β)),
    whileLoop β initial body = do
      match ← body initial with
      | .done out => pure out
      | .yield next => whileLoop β next body

def copyFromBody {m : Type → Type} [Monad m] {D E : Type}
    (write : D → I64 → E → m Unit) (dest : D)
    (state : I64 × Option (E × List E)) :
    m (ForInStep (I64 × Option (E × List E))) := do
  match state.2 with
  | none => pure (.done state)
  | some (value, rest) =>
    write dest state.1 value
    pure (.yield (state.1 + int 1, cursor rest))

def copyFromForStep {m : Type → Type} [Monad m] {D E : Type}
    (write : D → I64 → E → m Unit) (dest : D) (value : E) (index : I64) :
    m (ForInStep I64) := do
  write dest index value
  pure (.yield (index + int 1))

theorem copyFromWhileForIn {m : Type → Type} [Monad m] [LawfulMonad m] {D E : Type}
    (whileLoop : (β : Type) → β → (β → m (ForInStep β)) → m β)
    (equation : WhileEquation whileLoop) (write : D → I64 → E → m Unit)
    (dest : D) (values : List E) (index : I64) :
    whileLoop (I64 × Option (E × List E)) (index, cursor values) (copyFromBody write dest) =
      (do
        let final ← forIn values index (copyFromForStep write dest)
        pure (final, none)) := by
  induction values generalizing index with
  | nil =>
    rw [equation (I64 × Option (E × List E)) (index, cursor []) (copyFromBody write dest)]
    simp [copyFromBody, cursor, List.forIn_nil]
  | cons value values ih =>
    rw [equation (I64 × Option (E × List E)) (index, cursor (value :: values))
      (copyFromBody write dest)]
    simp only [show cursor (value :: values) = some (value, values) from rfl,
      copyFromBody, bind_assoc, pure_bind]
    rw [ih]
    simp [List.forIn_cons, copyFromForStep]

def sourceIterableCopyFrom {D E Start Offset PrefixOffset : Type}
    (value : Offset → Int) (subOne : Offset → PrefixOffset)
    (cast : Start → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (whileLoop : (β : Type) → β →
      (β → StateT (Heap I64 E) Result (ForInStep β)) → StateT (Heap I64 E) Result β)
    (dest : D) (rawStart : Start) (values : List E) (offset : Offset) :
    StateT (Heap I64 E) Result D :=
  copytoIterableFrom (fun n => decide (value n < 1)) subOne oneTo
    startIter nextIter (fun raw => StateT.lift (cast raw)) write (fun {β} => whileLoop β)
    dest rawStart values offset

theorem sourceIterableCopyFrom_stages {D E Start Offset PrefixOffset : Type}
    (value : Offset → Int) (prefixValue : PrefixOffset → Int) (subOne : Offset → PrefixOffset)
    (cast : Start → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (whileLoop : (β : Type) → β →
      (β → StateT (Heap I64 E) Result (ForInStep β)) → StateT (Heap I64 E) Result β)
    (rangeLaw : ∀ n, oneTo n = pure ⟨(prefixValue n).toNat⟩)
    (startLaw : ∀ xs, startIter xs = pure (cursor xs))
    (nextLaw : ∀ xs rest, nextIter xs rest = pure (cursor rest))
    (dest : D) (rawStart : Start) (values : List E) (offset : Offset) :
    sourceIterableCopyFrom value subOne cast oneTo startIter nextIter write whileLoop
      dest rawStart values offset =
      (if value offset < 1 then
        throw (.julia (.argumentError "source start offset is < 1"))
      else do
        let y ← StateT.lift
          (runSkipSteps skipCursorStep (prefixValue (subOne offset)).toNat (cursor values))
        if y.isNone then throw (.julia (.argumentError "source has fewer elements than required"))
        let index ← StateT.lift (cast rawStart)
        let _ ← whileLoop (I64 × Option (E × List E)) (index, y) (copyFromBody write dest)
        pure dest) := by
  have rangeEq : oneTo = (fun n => pure ⟨(prefixValue n).toNat⟩) := funext rangeLaw
  have startEq : startIter = (fun xs => pure (cursor xs)) := funext startLaw
  have nextEq : nextIter = (fun _ rest => pure (cursor rest)) := by
    funext xs rest
    exact nextLaw xs rest
  rw [rangeEq, startEq, nextEq]
  by_cases invalid : value offset < 1
  · funext heap
    simp [sourceIterableCopyFrom, copytoIterableFrom, invalid,
      StateT.bind, StateT.pure] <;> rfl
  · simp only [sourceIterableCopyFrom, copytoIterableFrom, invalid, decide_false,
      Bool.false_eq_true, ite_false, pure_bind]
    rw [forInSkipSteps, ← liftSkipSteps]
    congr 1
    · congr 1
      funext i y heap
      cases y with
      | none =>
        simp [skipCursorStep, StateT.bind, StateT.pure, StateT.lift] <;> rfl
      | some pair => cases pair; rfl
    · funext y
      by_cases missing : y.isNone = true
      · funext heap
        simp [missing, StateT.bind, StateT.pure, StateT.lift] <;> rfl
      · simp only [missing]
        apply congrArg (fun next : I64 → StateT (Heap I64 E) Result D =>
          StateT.lift (cast rawStart) >>= next)
        funext index
        apply congrArg (fun action :
            StateT (Heap I64 E) Result (I64 × Option (E × List E)) =>
          (action >>= (fun _ => pure dest) : StateT (Heap I64 E) Result D))
        apply congrArg (whileLoop (I64 × Option (E × List E)) (index, y))
        funext state
        rcases state with ⟨i, next⟩
        cases next with
        | none => rfl
        | some pair => cases pair; rfl

theorem sourceIterableCopyFrom_reference {D E Start Offset PrefixOffset : Type}
    (value : Offset → Int) (prefixValue : PrefixOffset → Int) (subOne : Offset → PrefixOffset)
    (cast : Start → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (whileLoop : (β : Type) → β →
      (β → StateT (Heap I64 E) Result (ForInStep β)) → StateT (Heap I64 E) Result β)
    (subLaw : ∀ offset, 1 ≤ value offset →
      prefixValue (subOne offset) = value offset - 1)
    (rangeLaw : ∀ n, oneTo n = pure ⟨(prefixValue n).toNat⟩)
    (startLaw : ∀ xs, startIter xs = pure (cursor xs))
    (nextLaw : ∀ xs rest, nextIter xs rest = pure (cursor rest))
    (equation : WhileEquation whileLoop)
    (dest : D) (rawStart : Start) (values : List E) (offset : Offset) :
    sourceIterableCopyFrom value subOne cast oneTo startIter nextIter write whileLoop
      dest rawStart values offset =
      (if value offset < 1 then
        throw (.julia (.argumentError "source start offset is < 1"))
      else if (values.length : Int) < value offset then
        throw (.julia (.argumentError "source has fewer elements than required"))
      else do
        let index ← StateT.lift (cast rawStart)
        let _ ← forIn (values.drop (value offset - 1).toNat) index (copyFromForStep write dest)
        pure dest) := by
  rw [sourceIterableCopyFrom_stages value prefixValue subOne cast oneTo startIter nextIter
    write whileLoop rangeLaw startLaw nextLaw]
  by_cases invalid : value offset < 1
  · simp [invalid]
  · have positive : 1 ≤ value offset := by omega
    simp only [invalid, ite_false, subLaw offset positive, skipCursorSteps]
    let count := (value offset - 1).toNat
    have countValue : (count : Int) = value offset - 1 := by
      dsimp [count]
      omega
    by_cases short : (values.length : Int) < value offset
    · by_cases prefixFits : count ≤ values.length
      · have countEq : count = values.length := by omega
        simp only [show (value offset - 1).toNat = count from rfl,
          countEq, List.drop_length, cursor]
        funext heap
        simp [short, StateT.bind, StateT.pure, StateT.lift] <;> rfl
      · simp only [show (value offset - 1).toNat = count from rfl, prefixFits, ite_false]
        funext heap
        simp [short, StateT.bind, StateT.lift] <;> rfl
    · have prefixFits : count ≤ values.length := by omega
      have notEmpty : values.drop count ≠ [] := by
        intro empty
        have lengthZero : (values.drop count).length = 0 := by rw [empty]; rfl
        rw [List.length_drop] at lengthZero
        omega
      have present : (cursor (values.drop count)).isNone = false := by
        cases remaining : values.drop count with
        | nil => exact False.elim (notEmpty remaining)
        | cons item rest => rfl
      simp only [show (value offset - 1).toNat = count from rfl, prefixFits, ite_true,
        short, ite_false]
      have lifted : (StateT.lift (.ok (cursor (values.drop count))) :
          StateT (Heap I64 E) Result (Option (E × List E))) =
          pure (cursor (values.drop count)) := rfl
      rw [lifted]
      simp only [pure_bind, present, Bool.false_eq_true, ite_false]
      simp only [copyFromWhileForIn whileLoop equation write dest (values.drop count),
        bind_assoc, pure_bind]

theorem copyFromLoop_boundsFailure {D E : Type}
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (values : List E) (lo hi : I64) (start : Int) (heap : Heap I64 E)
    (law : ∀ index ∈ copyPositions start values.length, ∀ value heap,
      ((lo.val ≤ index.val ∧ index.val ≤ hi.val) →
        (write dest index value).run heap = .ok ((), store index value heap)) ∧
      (¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val) →
        (write dest index value).run heap = .error (.julia .boundsError)))
    (outside : ∃ index ∈ copyPositions start values.length,
      ¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val)) :
    (forIn values (int start) (copyFromForStep write dest)).run heap =
      .error (.julia .boundsError) := by
  induction values generalizing start heap with
  | nil =>
    simp [copyPositions] at outside
  | cons value values ih =>
    have headLaw := law (int start) (by simp [copyPositions]) value heap
    by_cases valid : lo.val ≤ (int start).val ∧ (int start).val ≤ hi.val
    · have head := headLaw.1 valid
      have tailLaw : ∀ index ∈ copyPositions (start + 1) values.length, ∀ value heap,
          ((lo.val ≤ index.val ∧ index.val ≤ hi.val) →
            (write dest index value).run heap = .ok ((), store index value heap)) ∧
          (¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val) →
            (write dest index value).run heap = .error (.julia .boundsError)) := by
        intro index member item state
        exact law index (by simp [copyPositions, member]) item state
      have tailOutside : ∃ index ∈ copyPositions (start + 1) values.length,
          ¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val) := by
        obtain ⟨index, member, bad⟩ := outside
        simp only [List.length_cons, copyPositions, List.mem_cons] at member
        rcases member with same | member
        · subst index
          exact False.elim (bad valid)
        · exact ⟨index, member, bad⟩
      have tail := ih (start + 1) (store (int start) value heap) tailLaw tailOutside
      simp only [StateT.run] at head
      simpa [List.forIn_cons, copyFromForStep, StateT.run, StateT.bind, StateT.pure,
        head, vcatNativeAdd] using tail
    · have head := headLaw.2 valid
      simp only [StateT.run] at head
      simp [List.forIn_cons, copyFromForStep, StateT.run, StateT.bind, head]

def IterableCopyFromContents : Prop :=
  ∀ (D E Start Offset PrefixOffset : Type)
    (value : Offset → Int) (prefixValue : PrefixOffset → Int) (subOne : Offset → PrefixOffset)
    (cast : Start → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (whileLoop : (β : Type) → β →
      (β → StateT (Heap I64 E) Result (ForInStep β)) → StateT (Heap I64 E) Result β),
    (∀ offset, 1 ≤ value offset → prefixValue (subOne offset) = value offset - 1) →
    (∀ n, oneTo n = pure ⟨(prefixValue n).toNat⟩) →
    (∀ xs, startIter xs = pure (cursor xs)) →
    (∀ xs rest, nextIter xs rest = pure (cursor rest)) →
    WhileEquation whileLoop →
    ∀ (dest : D) (rawStart : Start) (values : List E) (offset : Offset) (heap : Heap I64 E),
    (value offset < 1 →
      (sourceIterableCopyFrom value subOne cast oneTo startIter nextIter write whileLoop
        dest rawStart values offset).run heap =
          .error (.julia (.argumentError "source start offset is < 1"))) ∧
    (1 ≤ value offset → (values.length : Int) < value offset →
      (sourceIterableCopyFrom value subOne cast oneTo startIter nextIter write whileLoop
        dest rawStart values offset).run heap =
          .error (.julia (.argumentError "source has fewer elements than required"))) ∧
    (1 ≤ value offset → value offset ≤ (values.length : Int) →
      (∀ error, cast rawStart = .error error →
        (sourceIterableCopyFrom value subOne cast oneTo startIter nextIter write whileLoop
          dest rawStart values offset).run heap = .error error) ∧
      (∀ start : Int, cast rawStart = .ok (int start) →
        let suffix := values.drop (value offset - 1).toNat
        (copyPositions start suffix.length).Nodup →
        (∀ index ∈ copyPositions start suffix.length, ∀ value heap,
          (write dest index value).run heap = .ok ((), store index value heap)) →
        ∃ out,
          (sourceIterableCopyFrom value subOne cast oneTo startIter nextIter write whileLoop
            dest rawStart values offset).run heap = .ok (dest, out) ∧
          (∀ (k : Nat) (hk : k < suffix.length), out (int (start + k)) = suffix[k]) ∧
          (∀ q, q ∉ copyPositions start suffix.length → out q = heap q)) ∧
      (∀ (start : Int) (lo hi : I64), cast rawStart = .ok (int start) →
        let suffix := values.drop (value offset - 1).toNat
        (∀ index ∈ copyPositions start suffix.length, ∀ value heap,
          ((lo.val ≤ index.val ∧ index.val ≤ hi.val) →
            (write dest index value).run heap = .ok ((), store index value heap)) ∧
          (¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val) →
            (write dest index value).run heap = .error (.julia .boundsError))) →
        (∃ index ∈ copyPositions start suffix.length,
          ¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val)) →
        (sourceIterableCopyFrom value subOne cast oneTo startIter nextIter write whileLoop
          dest rawStart values offset).run heap = .error (.julia .boundsError)))

theorem iterableCopyFromContents_proven : IterableCopyFromContents := by
  intro D E Start Offset PrefixOffset value prefixValue subOne cast oneTo startIter nextIter
    write whileLoop subLaw rangeLaw startLaw nextLaw equation dest rawStart values offset heap
  have reference := sourceIterableCopyFrom_reference value prefixValue subOne cast oneTo
    startIter nextIter write whileLoop subLaw rangeLaw startLaw nextLaw equation
    dest rawStart values offset
  refine ⟨?_, ?_, ?_⟩
  · intro invalid
    rw [reference]
    simp [invalid, StateT.run] <;> rfl
  · intro positive short
    have valid : ¬ value offset < 1 := by omega
    rw [reference]
    simp [valid, short, StateT.run] <;> rfl
  · intro positive enough
    have valid : ¬ value offset < 1 := by omega
    have notShort : ¬ (values.length : Int) < value offset := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro error failed
      rw [reference]
      simp [valid, notShort, failed, StateT.run, StateT.bind, StateT.lift]
    · intro start converted
      dsimp only
      intro distinct writeLaw
      let suffix := values.drop (value offset - 1).toNat
      let boolWrite := fun (_ : Bool) d index item => write d index item
      have positionsLength := copyPositions_length start suffix.length
      obtain ⟨out, output, unchanged⟩ :=
        prefixWrite_success (copyPositions start suffix.length) suffix heap (by omega)
      have contents := prefixWrite_at (copyPositions start suffix.length) suffix heap out
        distinct (by omega) output
      refine ⟨out, ?_, ?_, ?_⟩
      · have loop := copyAtLoop boolWrite dest suffix start heap writeLaw
        rw [output] at loop
        change (forIn suffix (int start) (copyFromForStep write dest)).run heap =
          .ok (int (start + suffix.length), out) at loop
        simp only [StateT.run] at loop
        have returned : (do
            let _ ← forIn suffix (int start) (copyFromForStep write dest)
            pure dest : StateT (Heap I64 E) Result D).run heap = .ok (dest, out) := by
          simp only [StateT.run, bind, pure, StateT.bind, StateT.pure]
          rw [loop]
          rfl
        rw [reference]
        simpa [suffix, valid, notShort, converted, StateT.run, StateT.bind, StateT.pure,
          StateT.lift] using returned
      · intro k hk
        rw [← copyPositions_get start suffix.length k hk]
        exact contents k hk
      · intro q outside
        apply unchanged q
        have allPositions : (copyPositions start suffix.length).take suffix.length =
            copyPositions start suffix.length := List.take_of_length_le (by omega)
        rw [allPositions]
        simpa [suffix] using outside
    · intro start lo hi converted
      dsimp only
      intro writeLaw outside
      let suffix := values.drop (value offset - 1).toNat
      have failed := copyFromLoop_boundsFailure write dest suffix lo hi start heap
        writeLaw outside
      simp only [StateT.run] at failed
      have returned : (do
          let _ ← forIn suffix (int start) (copyFromForStep write dest)
          pure dest : StateT (Heap I64 E) Result D).run heap =
            .error (.julia .boundsError) := by
        simp only [StateT.run, bind, pure, StateT.bind, StateT.pure]
        rw [failed]
        rfl
      rw [reference]
      simpa [suffix, valid, notShort, converted, StateT.run, StateT.bind, StateT.pure,
        StateT.lift] using returned

theorem copyPositions_nodup (start : Int) (count : Nat)
    (lower : IntTy.i64.min ≤ start)
    (upper : start + count ≤ IntTy.i64.max + 1) :
    (copyPositions start count).Nodup := by
  induction count generalizing start with
  | zero => simp [copyPositions]
  | succ count ih =>
    rw [copyPositions]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨k, hk, equal⟩ := List.mem_iff_getElem.mp member
      have bound : k < count := by simpa [copyPositions_length] using hk
      rw [copyPositions_get (start + 1) count k bound] at equal
      have firstValue : (int start).val = start :=
        wrapInt_of_inRange .i64 start ⟨lower, by omega⟩
      have nextValue : (int (start + 1 + k)).val = start + 1 + k :=
        wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
      have valuesEqual := congrArg Subtype.val equal
      rw [firstValue, nextValue] at valuesEqual
      omega
    · exact ih (start + 1) (by omega) (by omega)

theorem copyPositions_in_interval (start : Int) (count : Nat) (lo hi : I64)
    (lower : lo.val ≤ start) (upper : start + count ≤ hi.val + 1) :
    ∀ index ∈ copyPositions start count, lo.val ≤ index.val ∧ index.val ≤ hi.val := by
  intro index member
  obtain ⟨k, hk, equal⟩ := List.mem_iff_getElem.mp member
  have bound : k < count := by simpa [copyPositions_length] using hk
  rw [copyPositions_get start count k bound] at equal
  have nativeLower := lo.property.1
  have nativeUpper := hi.property.2
  have value : (int (start + k)).val = start + k :=
    wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
  subst index
  rw [value]
  constructor <;> omega

theorem copyPositions_outside_interval (start lo hi : I64) (count : Nat)
    (nonempty : 0 < count)
    (capacity : hi.val - lo.val + 1 ≤ IntTy.i64.max)
    (doesNotFit : ¬ (lo.val ≤ start.val ∧ start.val + count ≤ hi.val + 1)) :
    ∃ index ∈ copyPositions start.val count,
      ¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val) := by
  have firstValue : (int start.val).val = start.val :=
    wrapInt_of_inRange .i64 start.val start.property
  by_cases startsInBounds : lo.val ≤ start.val ∧ start.val ≤ hi.val
  · have overflows : hi.val + 1 < start.val + count := by omega
    let k := (hi.val - start.val + 1).toNat
    have kValue : (k : Int) = hi.val - start.val + 1 := by
      dsimp [k]
      omega
    have kBound : k < count := by omega
    have position : int (hi.val + 1) ∈ copyPositions start.val count := by
      have member := List.getElem_mem
        (show k < (copyPositions start.val count).length by
          simpa [copyPositions_length] using kBound)
      rw [copyPositions_get start.val count k kBound] at member
      have same : start.val + (k : Int) = hi.val + 1 := by omega
      simpa [same] using member
    refine ⟨int (hi.val + 1), position, ?_⟩
    by_cases maximal : hi.val = IntTy.i64.max
    · have wrapped : (int (hi.val + 1)).val = IntTy.i64.min := by
        rw [maximal]
        decide
      have positiveLo : 0 < lo.val := by
        rw [maximal] at capacity
        omega
      have negativeMin : IntTy.i64.min < 0 := by decide
      rw [wrapped]
      omega
    · have nativeLower := hi.property.1
      have nativeUpper := hi.property.2
      have value : (int (hi.val + 1)).val = hi.val + 1 :=
        wrapInt_of_inRange .i64 _ ⟨by omega, by omega⟩
      rw [value]
      omega
  · refine ⟨int start.val, ?_, ?_⟩
    · cases count with
      | zero => omega
      | succ count => simp [copyPositions]
    · simpa [firstValue] using startsInBounds

theorem nativeCopyCast_same (index : I64) :
    liftJulia (JuliaLean.base.int.convert .i64 index) = .ok index := by
  simp [liftJulia, JuliaLean.base.int.convert, JInt.convert, index.property, Except.mapError]

def IterableCopyFromBoundsAndContents : Prop :=
  ∀ (D E Offset PrefixOffset : Type)
    (value : Offset → Int) (prefixValue : PrefixOffset → Int) (subOne : Offset → PrefixOffset)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (whileLoop : (β : Type) → β →
      (β → StateT (Heap I64 E) Result (ForInStep β)) → StateT (Heap I64 E) Result β),
    (∀ offset, 1 ≤ value offset → prefixValue (subOne offset) = value offset - 1) →
    (∀ n, oneTo n = pure ⟨(prefixValue n).toNat⟩) →
    (∀ xs, startIter xs = pure (cursor xs)) →
    (∀ xs rest, nextIter xs rest = pure (cursor rest)) →
    WhileEquation whileLoop →
    ∀ (dest : D) (start lo hi : I64) (values : List E) (offset : Offset) (heap : Heap I64 E),
    hi.val - lo.val + 1 ≤ IntTy.i64.max →
    (∀ (index : I64) (item : E) (heap : Heap I64 E),
      ((lo.val ≤ index.val ∧ index.val ≤ hi.val) →
        (write dest index item).run heap = .ok ((), store index item heap)) ∧
      (¬ (lo.val ≤ index.val ∧ index.val ≤ hi.val) →
        (write dest index item).run heap = .error (.julia .boundsError))) →
    let operation := sourceIterableCopyFrom value subOne
      (fun index => liftJulia (JuliaLean.base.int.convert .i64 index))
      oneTo startIter nextIter write whileLoop dest start values offset
    let suffix := values.drop (value offset - 1).toNat
    (value offset < 1 →
      operation.run heap = .error (.julia (.argumentError "source start offset is < 1"))) ∧
    (1 ≤ value offset → (values.length : Int) < value offset →
      operation.run heap = .error (.julia (.argumentError "source has fewer elements than required"))) ∧
    (1 ≤ value offset → value offset ≤ (values.length : Int) →
      ((lo.val ≤ start.val ∧ start.val + suffix.length ≤ hi.val + 1) →
        ∃ out, operation.run heap = .ok (dest, out) ∧
          (∀ (k : Nat) (hk : k < suffix.length), out (int (start.val + k)) = suffix[k]) ∧
          (∀ q, q ∉ copyPositions start.val suffix.length → out q = heap q)) ∧
      (¬ (lo.val ≤ start.val ∧ start.val + suffix.length ≤ hi.val + 1) →
        operation.run heap = .error (.julia .boundsError)))

theorem iterableCopyFromBoundsAndContents_proven : IterableCopyFromBoundsAndContents := by
  intro D E Offset PrefixOffset value prefixValue subOne oneTo startIter nextIter write
    whileLoop subLaw rangeLaw startLaw nextLaw equation dest start lo hi values offset heap
    capacity writeLaw
  have detailed := iterableCopyFromContents_proven D E I64 Offset PrefixOffset
    value prefixValue subOne (fun index => liftJulia (JuliaLean.base.int.convert .i64 index))
    oneTo startIter nextIter write whileLoop subLaw rangeLaw startLaw nextLaw equation
    dest start values offset heap
  refine ⟨detailed.1, detailed.2.1, ?_⟩
  intro positive enough
  have sufficient := detailed.2.2 positive enough
  let suffix := values.drop (value offset - 1).toNat
  have converted : liftJulia (JuliaLean.base.int.convert .i64 start) = .ok (int start.val) := by
    rw [nativeCopyCast_same]
    apply congrArg Except.ok
    apply Subtype.ext
    exact (wrapInt_of_inRange .i64 start.val start.property).symm
  constructor
  · intro fits
    change lo.val ≤ start.val ∧ start.val + suffix.length ≤ hi.val + 1 at fits
    have nativeLower := lo.property.1
    have nativeUpper := hi.property.2
    have distinct := copyPositions_nodup start.val suffix.length (by omega) (by omega)
    have positions := copyPositions_in_interval start.val suffix.length lo hi fits.1 fits.2
    apply sufficient.2.1 start.val converted distinct
    intro index member item state
    exact (writeLaw index item state).1 (positions index member)
  · intro doesNotFit
    have nonempty : 0 < suffix.length := by
      have count : ((value offset - 1).toNat : Int) = value offset - 1 := by omega
      dsimp [suffix]
      rw [List.length_drop]
      omega
    have outside := copyPositions_outside_interval start lo hi suffix.length
      nonempty capacity doesNotFit
    apply sufficient.2.2 start.val lo hi converted
    · intro index _ item state
      exact writeLaw index item state
    · exact outside

def sourceIterableCopyN {D E Offset PrefixOffset Lin : Type}
    (value : Offset → Int) (subOne : Offset → PrefixOffset)
    (linearIndices : D → Result Lin) (contains : Lin → I64 → Result Bool)
    (last : Lin → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (rest : List E → List E → StateT (Heap I64 E) Result (List E))
    (take : List E → I64 → StateT (Heap I64 E) Result (List E))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (dstart : I64) (values : List E) (sstart : Offset) (n : I64) :
    StateT (Heap I64 E) Result D :=
  copytoIterableN
    (fun n => JuliaLean.base.int.ltSame n (int 0))
    (fun n => JuliaLean.base.int.eqSame n (int 0))
    (fun dest => StateT.lift (linearIndices dest)) (fun offset => decide (value offset < 1))
    (fun indices index => StateT.lift (contains indices index))
    (fun indices => StateT.lift (last indices))
    (fun last first => pure (JuliaLean.base.int.sub last first))
    (fun difference => pure (JuliaLean.base.int.add difference (int 1)))
    (fun count span => pure (JuliaLean.base.int.leSame count span))
    (fun index => StateT.lift (liftJulia (JuliaLean.base.int.convert .i64 index)))
    (fun count => StateT.lift (liftJulia (JuliaLean.base.int.convert .i64 count)))
    startIter subOne oneTo nextIter rest take write dest dstart values sstart n

def CountedIterableCopyEarlyExits : Prop :=
  ∀ (D E Offset PrefixOffset Lin : Type)
    (value : Offset → Int) (subOne : Offset → PrefixOffset)
    (linearIndices : D → Result Lin) (contains : Lin → I64 → Result Bool)
    (last : Lin → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (rest : List E → List E → StateT (Heap I64 E) Result (List E))
    (take : List E → I64 → StateT (Heap I64 E) Result (List E))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (dstart : I64) (values : List E) (sstart : Offset) (n : I64) (heap : Heap I64 E),
    (n.val < 0 →
      (sourceIterableCopyN value subOne linearIndices contains last oneTo startIter nextIter
        rest take write dest dstart values sstart n).run heap =
          .error (.julia (.argumentError "n should be non-negative"))) ∧
    (n.val = 0 →
      (sourceIterableCopyN value subOne linearIndices contains last oneTo startIter nextIter
        rest take write dest dstart values sstart n).run heap = .ok (dest, heap))

theorem countedIterableCopyEarlyExits_proven : CountedIterableCopyEarlyExits := by
  intro D E Offset PrefixOffset Lin value subOne linearIndices contains last oneTo startIter
    nextIter rest take write dest dstart values sstart n heap
  have zero : (int 0).val = 0 := rfl
  constructor
  · intro negative
    simp [sourceIterableCopyN, copytoIterableN, JuliaLean.Proofs.base.int.ltSame_eq,
      zero, negative, StateT.run] <;> rfl
  · intro empty
    simp [sourceIterableCopyN, copytoIterableN, JuliaLean.Proofs.base.int.ltSame_eq,
      JuliaLean.Proofs.base.int.eqSame_eq, zero, empty, StateT.run] <;> rfl

def copyNForStep {D E : Type}
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (value : E) (previous : I64) : StateT (Heap I64 E) Result (ForInStep I64) := do
  let index := previous + int 1
  write dest index value
  pure (.yield index)

theorem sourceIterableCopyN_normalized {D E Offset PrefixOffset Lin : Type}
    (value : Offset → Int) (prefixValue : PrefixOffset → Int) (subOne : Offset → PrefixOffset)
    (linearIndices : D → Result Lin) (contains : Lin → I64 → Result Bool)
    (last : Lin → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (rest : List E → List E → StateT (Heap I64 E) Result (List E))
    (take : List E → I64 → StateT (Heap I64 E) Result (List E))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (rangeLaw : ∀ n, oneTo n = pure ⟨(prefixValue n).toNat⟩)
    (startLaw : ∀ xs, startIter xs = pure (cursor xs))
    (nextLaw : ∀ xs remaining, nextIter xs remaining = pure (cursor remaining))
    (restLaw : ∀ xs remaining, rest xs remaining = pure remaining)
    (takeLaw : ∀ remaining count, 0 ≤ count.val →
      take remaining count = pure (remaining.take count.val.toNat))
    (dest : D) (dstart : I64) (values : List E) (sstart : Offset) (n : I64)
    (indices : Lin) (endpoint : I64)
    (positive : 0 < n.val) (validOffset : ¬ value sstart < 1)
    (indicesLaw : linearIndices dest = .ok indices)
    (containsLaw : contains indices dstart = .ok true)
    (lastLaw : last indices = .ok endpoint)
    (fits : n.val ≤ (JuliaLean.base.int.add
      (JuliaLean.base.int.sub endpoint dstart) (int 1)).val) :
    sourceIterableCopyN value subOne linearIndices contains last oneTo startIter nextIter
      rest take write dest dstart values sstart n =
      (do
        let y ← StateT.lift
          (runSkipSteps skipCursorStep (prefixValue (subOne sstart)).toNat (cursor values))
        match y with
        | none => throw (.julia (.argumentError "source has fewer elements than required"))
        | some (first, remaining) =>
          write dest dstart first
          let final ← forIn (remaining.take (n - int 1).val.toNat) dstart
            (copyNForStep write dest)
          if final.val < (dstart + n - int 1).val then throw (.julia .boundsError)
          pure dest) := by
  have rangeEq : oneTo = (fun n => pure ⟨(prefixValue n).toNat⟩) := funext rangeLaw
  have startEq : startIter = (fun xs => pure (cursor xs)) := funext startLaw
  have nextEq : nextIter = (fun _ remaining => pure (cursor remaining)) := by
    funext xs remaining
    exact nextLaw xs remaining
  have restEq : rest = (fun _ remaining => pure remaining) := by
    funext xs remaining
    exact restLaw xs remaining
  have takeNonnegative : 0 ≤ (n - int 1).val := by
    change 0 ≤ wrapInt .i64 (n.val - (int 1).val)
    rw [show (int 1).val = 1 from rfl]
    have range := n.property
    have minimum : IntTy.i64.min ≤ 0 := by decide
    rw [wrapInt_of_inRange .i64 _ (by constructor <;> omega)]
    omega
  have takeEq : ∀ remaining, take remaining (n - int 1) =
      pure (remaining.take (n - int 1).val.toNat) :=
    fun remaining => takeLaw remaining (n - int 1) takeNonnegative
  have liftOk {α : Type} (x : α) :
      (StateT.lift (.ok x) : StateT (Heap I64 E) Result α) = pure x := rfl
  have zero : (int 0).val = 0 := rfl
  have nonnegative : ¬ n.val < 0 := by omega
  have nonzero : ¬ n.val = 0 := by omega
  rw [rangeEq, startEq, nextEq, restEq]
  simp only [sourceIterableCopyN, copytoIterableN, JuliaLean.Proofs.base.int.ltSame_eq,
    JuliaLean.Proofs.base.int.eqSame_eq, JuliaLean.Proofs.base.int.leSame_eq,
    zero, nonnegative, nonzero, validOffset, decide_false, decide_true, fits,
    Bool.false_eq_true, Bool.not_true, ite_false,
    indicesLaw, containsLaw, lastLaw, nativeCopyCast_same, liftOk, pure_bind]
  simp only [takeEq, pure_bind]
  rw [forInSkipSteps, ← liftSkipSteps]
  congr 1
  · congr 1
    funext i y heap
    cases y with
    | none => simp [skipCursorStep, StateT.bind, StateT.pure, StateT.lift] <;> rfl
    | some pair => cases pair; rfl
  · funext y
    cases y with
    | none => rfl
    | some pair => cases pair; rfl

theorem copyNLoop {D E : Type}
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (values : List E) (previous : Int) (heap : Heap I64 E)
    (law : ∀ index ∈ copyPositions (previous + 1) values.length, ∀ value heap,
      (write dest index value).run heap = .ok ((), store index value heap)) :
    (forIn values (int previous) (copyNForStep write dest)).run heap =
      (prefixWrite (copyPositions (previous + 1) values.length) values heap).map
        (fun out => (int (previous + values.length), out)) := by
  induction values generalizing previous heap with
  | nil =>
    simp [List.forIn_nil, copyPositions, prefixWrite, StateT.run, StateT.pure, Except.map]
  | cons value values ih =>
    have head := law (int (previous + 1)) (by simp [copyPositions]) value heap
    simp only [StateT.run] at head
    have tailLaw : ∀ index ∈ copyPositions (previous + 1 + 1) values.length, ∀ value heap,
        (write dest index value).run heap = .ok ((), store index value heap) := by
      intro index member item state
      exact law index (by simp [copyPositions, member]) item state
    have tail := ih (previous + 1) (store (int (previous + 1)) value heap) tailLaw
    simp only [List.forIn_cons, copyNForStep, StateT.run, StateT.bind, vcatNativeAdd,
      head, bind, pure, Except.bind, Except.pure, StateT.pure] at ⊢
    simpa [copyPositions, prefixWrite, StateT.run, Int.add_assoc, Int.add_left_comm,
      Int.add_comm] using tail

theorem nativeCopySpan_value (lo hi start : I64)
    (capacity : hi.val - lo.val + 1 ≤ IntTy.i64.max)
    (inside : lo.val ≤ start.val ∧ start.val ≤ hi.val) :
    (JuliaLean.base.int.add (JuliaLean.base.int.sub hi start) (int 1)).val =
      hi.val - start.val + 1 := by
  have minimum : IntTy.i64.min ≤ 0 := by decide
  have difference : IntTy.i64.min ≤ hi.val - start.val ∧
      hi.val - start.val ≤ IntTy.i64.max := by constructor <;> omega
  have span : IntTy.i64.min ≤ hi.val - start.val + 1 ∧
      hi.val - start.val + 1 ≤ IntTy.i64.max := by constructor <;> omega
  simp only [JuliaLean.base.int.add, JuliaLean.base.int.sub,
    JuliaLean.Proofs.base.int.add_int_val, JuliaLean.Proofs.base.int.sub_int_val]
  rw [show (int 1).val = 1 from rfl, wrapInt_of_inRange .i64 _ difference]
  exact wrapInt_of_inRange .i64 _ span

theorem requiredSkipCursor_reference {E β : Type}
    (offset : Int) (positive : 1 ≤ offset) (values : List E)
    (finish : E → List E → StateT (Heap I64 E) Result β) :
    (do
      let y ← StateT.lift
        (runSkipSteps skipCursorStep (offset - 1).toNat (cursor values))
      match y with
      | none => throw (ArrayError.julia (.argumentError "source has fewer elements than required"))
      | some (first, remaining) => finish first remaining) =
    (if (values.length : Int) < offset then
      throw (ArrayError.julia (.argumentError "source has fewer elements than required"))
    else
      match cursor (values.drop (offset - 1).toNat) with
      | none => throw (ArrayError.julia (.argumentError "source has fewer elements than required"))
      | some (first, remaining) => finish first remaining) := by
  rw [skipCursorSteps]
  let count := (offset - 1).toNat
  have countValue : (count : Int) = offset - 1 := by dsimp [count]; omega
  by_cases short : (values.length : Int) < offset
  · by_cases prefixFits : count ≤ values.length
    · have countEq : count = values.length := by omega
      simp only [show (offset - 1).toNat = count from rfl,
        countEq, List.drop_length, cursor]
      funext heap
      simp [short, StateT.bind, StateT.lift] <;> rfl
    · simp only [show (offset - 1).toNat = count from rfl, prefixFits, ite_false]
      funext heap
      simp [short, StateT.bind, StateT.lift] <;> rfl
  · have prefixFits : count ≤ values.length := by omega
    simp only [show (offset - 1).toNat = count from rfl, prefixFits, ite_true,
      short, ite_false]
    have lifted : (StateT.lift (.ok (cursor (values.drop count))) :
        StateT (Heap I64 E) Result (Option (E × List E))) =
        pure (cursor (values.drop count)) := rfl
    rw [lifted]
    simp only [pure_bind]

theorem countedCopyBlock_contents {D E : Type}
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit) (dest : D)
    (start lo hi n : I64) (first : E) (remaining : List E) (heap : Heap I64 E)
    (positive : 0 < n.val)
    (fits : lo.val ≤ start.val ∧ start.val + n.val ≤ hi.val + 1)
    (law : ∀ (index : I64) (value : E) (heap : Heap I64 E),
      lo.val ≤ index.val ∧ index.val ≤ hi.val →
      (write dest index value).run heap = .ok ((), store index value heap)) :
    let copied := first :: remaining.take (n.val - 1).toNat
    ∃ out,
      (do
        write dest start first
        let final ← forIn (remaining.take (n - int 1).val.toNat) start
          (copyNForStep write dest)
        if final.val < (start + n - int 1).val then throw (.julia .boundsError)
        pure dest : StateT (Heap I64 E) Result D).run heap =
          (if copied.length < n.val then .error (.julia .boundsError) else .ok (dest, out)) ∧
      (∀ (k : Nat) (hk : k < copied.length), out (int (start.val + k)) = copied[k]) ∧
      (∀ q, q ∉ copyPositions start.val copied.length → out q = heap q) := by
  dsimp only
  let tail := remaining.take (n.val - 1).toNat
  let copied := first :: tail
  have countValue : ((n.val - 1).toNat : Int) = n.val - 1 := by omega
  have copiedPositive : 0 < copied.length := by simp [copied]
  have copiedBound : (copied.length : Int) ≤ n.val := by
    have lengthBound := List.length_take_le (n.val - 1).toNat remaining
    change tail.length ≤ (n.val - 1).toNat at lengthBound
    change (tail.length : Int) + 1 ≤ n.val
    omega
  have firstValue : int start.val = start := by
    apply Subtype.ext
    exact wrapInt_of_inRange .i64 start.val start.property
  have nValue : int n.val = n := by
    apply Subtype.ext
    exact wrapInt_of_inRange .i64 n.val n.property
  have subValue : (n - int 1).val = n.val - 1 := by
    change wrapInt .i64 (n.val - (int 1).val) = _
    rw [show (int 1).val = 1 from rfl]
    apply wrapInt_of_inRange
    have range := n.property
    have minimum : IntTy.i64.min ≤ 0 := by decide
    constructor <;> omega
  have maximum : start + n - int 1 = int (start.val + n.val - 1) := by
    calc
      start + n - int 1 = int start.val + int n.val - int 1 := by rw [firstValue, nValue]
      _ = int (start.val + n.val - 1) := by rw [vcatNativeAdd, vcatNativeSub]
  have indices := copyPositions_in_interval start.val copied.length lo hi fits.1 (by omega)
  have distinct := copyPositions_nodup start.val copied.length
    (by have lower := lo.property.1; omega) (by have upper := hi.property.2; omega)
  have positionsLength := copyPositions_length start.val copied.length
  obtain ⟨out, output, unchanged⟩ :=
    prefixWrite_success (copyPositions start.val copied.length) copied heap (by omega)
  have contents := prefixWrite_at (copyPositions start.val copied.length) copied heap out
    distinct (by omega) output
  have head := law start first heap (by have upper := hi.property.2; constructor <;> omega)
  have tailLaw : ∀ index ∈ copyPositions (start.val + 1) tail.length, ∀ value heap,
      (write dest index value).run heap = .ok ((), store index value heap) := by
    intro index member value state
    apply law index value state
    apply indices index
    simpa [copied, copyPositions] using (Or.inr member :
      index = int start.val ∨ index ∈ copyPositions (start.val + 1) tail.length)
  have tailOutput : prefixWrite (copyPositions (start.val + 1) tail.length)
      tail (store start first heap) = .ok out := by
    simpa [copied, copyPositions, prefixWrite, firstValue] using output
  have loop := copyNLoop write dest tail start.val (store start first heap) tailLaw
  rw [tailOutput] at loop
  simp only [StateT.run] at head loop
  rw [firstValue] at loop
  have lastValue : (int (start.val + tail.length)).val = start.val + tail.length := by
    change wrapInt .i64 (start.val + tail.length) = start.val + tail.length
    apply wrapInt_of_inRange
    have lower := start.property.1
    have upper := hi.property.2
    have length : (tail.length : Int) + 1 ≤ n.val := by
      simpa [copied] using copiedBound
    constructor <;> omega
  have maximumValue : (int (start.val + n.val - 1)).val = start.val + n.val - 1 := by
    change wrapInt .i64 (start.val + n.val - 1) = start.val + n.val - 1
    apply wrapInt_of_inRange
    have lower := start.property.1
    have upper := hi.property.2
    constructor <;> omega
  refine ⟨out, ?_, ?_, ?_⟩
  · simp only [subValue]
    change (do
      write dest start first
      let final ← forIn tail start (copyNForStep write dest)
      if final.val < (start + n - int 1).val then throw (.julia .boundsError)
      pure dest : StateT (Heap I64 E) Result D).run heap = _
    simp only [StateT.run, bind, pure, StateT.bind, head, loop,
      Except.bind, Except.map, maximum, lastValue, maximumValue]
    have less : start.val + (tail.length : Int) < start.val + n.val - 1 ↔
        (copied.length : Int) < n.val := by
      change start.val + (tail.length : Int) < start.val + n.val - 1 ↔
        (tail.length : Int) + 1 < n.val
      omega
    simp only [less]
    split <;> rfl
  · intro k hk
    rw [← copyPositions_get start.val copied.length k hk]
    exact contents k hk
  · intro q outside
    apply unchanged q
    have allPositions : (copyPositions start.val copied.length).take copied.length =
        copyPositions start.val copied.length := List.take_of_length_le (by omega)
    rw [allPositions]
    simpa [copied, tail] using outside

theorem sourceIterableCopyN_destinationErrors {D E Offset PrefixOffset Lin : Type}
    (value : Offset → Int) (subOne : Offset → PrefixOffset)
    (linearIndices : D → Result Lin) (contains : Lin → I64 → Result Bool)
    (last : Lin → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (rest : List E → List E → StateT (Heap I64 E) Result (List E))
    (take : List E → I64 → StateT (Heap I64 E) Result (List E))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (start lo hi n : I64) (values : List E) (offset : Offset)
    (heap : Heap I64 E) (indices : Lin)
    (positive : 0 < n.val)
    (indicesLaw : linearIndices dest = .ok indices)
    (containsLaw : contains indices start =
      .ok (decide (lo.val ≤ start.val ∧ start.val ≤ hi.val)))
    (lastLaw : last indices = .ok hi)
    (capacity : hi.val - lo.val + 1 ≤ IntTy.i64.max) :
    (value offset < 1 →
      (sourceIterableCopyN value subOne linearIndices contains last oneTo startIter nextIter
        rest take write dest start values offset n).run heap =
          .error (.julia (.argumentError "source start offset is < 1"))) ∧
    (1 ≤ value offset → ¬ (lo.val ≤ start.val ∧ start.val + n.val ≤ hi.val + 1) →
      (sourceIterableCopyN value subOne linearIndices contains last oneTo startIter nextIter
        rest take write dest start values offset n).run heap = .error (.julia .boundsError)) := by
  have zero : (int 0).val = 0 := rfl
  have nonnegative : ¬ n.val < 0 := by omega
  have nonzero : ¬ n.val = 0 := by omega
  constructor
  · intro invalid
    simp [sourceIterableCopyN, copytoIterableN, JuliaLean.Proofs.base.int.ltSame_eq,
      JuliaLean.Proofs.base.int.eqSame_eq, zero, nonnegative, nonzero, indicesLaw,
      invalid, StateT.run, StateT.bind, StateT.lift] <;> rfl
  · intro validOffset doesNotFit
    have valid : ¬ value offset < 1 := by omega
    by_cases inside : lo.val ≤ start.val ∧ start.val ≤ hi.val
    · have span := nativeCopySpan_value lo hi start capacity inside
      have tooMany : ¬ n.val ≤ (JuliaLean.base.int.add
          (JuliaLean.base.int.sub hi start) (int 1)).val := by rw [span]; omega
      simp [sourceIterableCopyN, copytoIterableN, JuliaLean.Proofs.base.int.ltSame_eq,
        JuliaLean.Proofs.base.int.eqSame_eq, JuliaLean.Proofs.base.int.leSame_eq,
        zero, nonnegative, nonzero, valid, indicesLaw, containsLaw, lastLaw, inside,
        tooMany, StateT.run, StateT.bind, StateT.pure, StateT.lift] <;> rfl
    · simp [sourceIterableCopyN, copytoIterableN, JuliaLean.Proofs.base.int.ltSame_eq,
        JuliaLean.Proofs.base.int.eqSame_eq, zero, nonnegative, nonzero, valid,
        indicesLaw, containsLaw, inside, StateT.run, StateT.bind, StateT.pure,
        StateT.lift] <;> rfl

def CountedIterableCopyPositive : Prop :=
  ∀ (D E Offset PrefixOffset Lin : Type)
    (value : Offset → Int) (prefixValue : PrefixOffset → Int) (subOne : Offset → PrefixOffset)
    (linearIndices : D → Result Lin) (contains : Lin → I64 → Result Bool)
    (last : Lin → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (rest : List E → List E → StateT (Heap I64 E) Result (List E))
    (take : List E → I64 → StateT (Heap I64 E) Result (List E))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit),
    (∀ offset, 1 ≤ value offset → prefixValue (subOne offset) = value offset - 1) →
    (∀ n, oneTo n = pure ⟨(prefixValue n).toNat⟩) →
    (∀ xs, startIter xs = pure (cursor xs)) →
    (∀ xs remaining, nextIter xs remaining = pure (cursor remaining)) →
    (∀ xs remaining, rest xs remaining = pure remaining) →
    (∀ remaining count, 0 ≤ count.val →
      take remaining count = pure (remaining.take count.val.toNat)) →
    ∀ (dest : D) (start lo hi n : I64) (values : List E) (offset : Offset)
      (heap : Heap I64 E) (indices : Lin),
    0 < n.val → 1 ≤ value offset →
    (lo.val ≤ start.val ∧ start.val + n.val ≤ hi.val + 1) →
    hi.val - lo.val + 1 ≤ IntTy.i64.max →
    linearIndices dest = .ok indices → contains indices start = .ok true →
    last indices = .ok hi →
    (∀ (index : I64) (item : E) (state : Heap I64 E),
      lo.val ≤ index.val ∧ index.val ≤ hi.val →
      (write dest index item).run state = .ok ((), store index item state)) →
    let operation := sourceIterableCopyN value subOne linearIndices contains last oneTo
      startIter nextIter rest take write dest start values offset n
    let suffix := values.drop (value offset - 1).toNat
    ((values.length : Int) < value offset →
      operation.run heap = .error (.julia (.argumentError "source has fewer elements than required"))) ∧
    (value offset ≤ (values.length : Int) →
      ((suffix.length : Int) < n.val → operation.run heap = .error (.julia .boundsError)) ∧
      (n.val ≤ (suffix.length : Int) →
        let copied := suffix.take n.val.toNat
        ∃ out, operation.run heap = .ok (dest, out) ∧ copied.length = n.val.toNat ∧
          (∀ (k : Nat) (hk : k < copied.length), out (int (start.val + k)) = copied[k]) ∧
          (∀ q, q ∉ copyPositions start.val copied.length → out q = heap q)))

theorem countedIterableCopyPositive_proven : CountedIterableCopyPositive := by
  intro D E Offset PrefixOffset Lin value prefixValue subOne linearIndices contains last oneTo
    startIter nextIter rest take write subLaw rangeLaw startLaw nextLaw restLaw takeLaw
    dest start lo hi n values offset heap indices positive positiveOffset fits capacity
    indicesLaw containsLaw lastLaw writeLaw
  have inside : lo.val ≤ start.val ∧ start.val ≤ hi.val := by constructor <;> omega
  have span := nativeCopySpan_value lo hi start capacity inside
  have enough : n.val ≤ (JuliaLean.base.int.add
      (JuliaLean.base.int.sub hi start) (int 1)).val := by rw [span]; omega
  have normalized := sourceIterableCopyN_normalized value prefixValue subOne linearIndices
    contains last oneTo startIter nextIter rest take write rangeLaw startLaw nextLaw
    restLaw takeLaw dest start values offset n indices hi positive (by omega)
    indicesLaw containsLaw lastLaw enough
  rw [subLaw offset positiveOffset] at normalized
  rw [requiredSkipCursor_reference (value offset) positiveOffset values] at normalized
  constructor
  · intro short
    rw [normalized]
    simp [short, StateT.run] <;> rfl
  · intro available
    have notShort : ¬ (values.length : Int) < value offset := by omega
    have countValue : ((value offset - 1).toNat : Int) = value offset - 1 := by omega
    have nonempty : values.drop (value offset - 1).toNat ≠ [] := by
      intro empty
      have length : (values.drop (value offset - 1).toNat).length = 0 := by rw [empty]; rfl
      rw [List.length_drop] at length
      omega
    cases suffixEq : values.drop (value offset - 1).toNat with
    | nil => exact False.elim (nonempty suffixEq)
    | cons first remaining =>
      have block := normalized
      simp only [notShort, ite_false, suffixEq, cursor] at block
      obtain ⟨out, output, contents, unchanged⟩ :=
        countedCopyBlock_contents write dest start lo hi n first remaining heap positive
          fits writeLaw
      have nValue : (n.val.toNat : Int) = n.val := by omega
      have nSplit : n.val.toNat = (n.val - 1).toNat + 1 := by omega
      have copiedEq : first :: remaining.take (n.val - 1).toNat =
          (first :: remaining).take n.val.toNat := by rw [nSplit]; rfl
      have copiedLength : (first :: remaining.take (n.val - 1).toNat).length =
          min n.val.toNat (first :: remaining).length := by
        rw [copiedEq, List.length_take]
      constructor
      · intro short
        have actualShort : ((first :: remaining.take (n.val - 1).toNat).length : Int) <
            n.val := by rw [copiedLength]; omega
        rw [block]
        simpa only [actualShort, ite_true] using output
      · intro sufficient
        have length : (first :: remaining.take (n.val - 1).toNat).length = n.val.toNat := by
          rw [copiedLength]
          omega
        have notActualShort :
            ¬ ((first :: remaining.take (n.val - 1).toNat).length : Int) < n.val := by
          rw [length]
          omega
        dsimp only
        refine ⟨out, ?_, ?_, ?_, ?_⟩
        · rw [block]
          simpa only [notActualShort, ite_false] using output
        · simpa only [suffixEq, copiedEq] using length
        · simpa only [suffixEq, copiedEq] using contents
        · simpa only [suffixEq, copiedEq] using unchanged

def CountedIterableCopyDestinationErrors : Prop :=
  ∀ (D E Offset PrefixOffset Lin : Type)
    (value : Offset → Int) (subOne : Offset → PrefixOffset)
    (linearIndices : D → Result Lin) (contains : Lin → I64 → Result Bool)
    (last : Lin → Result I64)
    (oneTo : PrefixOffset → StateT (Heap I64 E) Result SkipSteps)
    (startIter : List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (nextIter : List E → List E → StateT (Heap I64 E) Result (Option (E × List E)))
    (rest : List E → List E → StateT (Heap I64 E) Result (List E))
    (take : List E → I64 → StateT (Heap I64 E) Result (List E))
    (write : D → I64 → E → StateT (Heap I64 E) Result Unit)
    (dest : D) (start lo hi n : I64) (values : List E) (offset : Offset)
    (heap : Heap I64 E) (indices : Lin),
    0 < n.val → linearIndices dest = .ok indices →
    contains indices start = .ok (decide (lo.val ≤ start.val ∧ start.val ≤ hi.val)) →
    last indices = .ok hi → hi.val - lo.val + 1 ≤ IntTy.i64.max →
    (value offset < 1 →
      (sourceIterableCopyN value subOne linearIndices contains last oneTo startIter nextIter
        rest take write dest start values offset n).run heap =
          .error (.julia (.argumentError "source start offset is < 1"))) ∧
    (1 ≤ value offset → ¬ (lo.val ≤ start.val ∧ start.val + n.val ≤ hi.val + 1) →
      (sourceIterableCopyN value subOne linearIndices contains last oneTo startIter nextIter
        rest take write dest start values offset n).run heap = .error (.julia .boundsError))

theorem countedIterableCopyDestinationErrors_proven : CountedIterableCopyDestinationErrors := by
  intro D E Offset PrefixOffset Lin
  exact sourceIterableCopyN_destinationErrors

def CountedIterableCopySpecification : Prop :=
  CountedIterableCopyEarlyExits ∧ CountedIterableCopyDestinationErrors ∧
    CountedIterableCopyPositive

theorem countedIterableCopySpecification_proven : CountedIterableCopySpecification :=
  ⟨countedIterableCopyEarlyExits_proven, countedIterableCopyDestinationErrors_proven,
    countedIterableCopyPositive_proven⟩

def CountedIterableCopyGenericEarlyExits : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m] [MonadExceptOf ArrayError m]
    (_throwBind : ∀ (α β : Type) (error : ArrayError) (next : α → m β),
      ((throw error : m α) >>= next) = (throw error : m β))
    (D Src E Start Offset PrefixOffset Count Lin End Difference Span Prefix J St Rest Taken : Type)
    [ForIn m Prefix J] [ForIn m Taken E]
    (value : Count → Int) (negative isZero : Count → Bool)
    (linearIndices : D → m Lin) (lessOne : Offset → Bool)
    (contains : Lin → Start → m Bool) (last : Lin → m End)
    (sub : End → Start → m Difference) (addOne : Difference → m Span)
    (le : Count → Span → m Bool)
    (toIntStart : Start → m I64) (toIntCount : Count → m I64)
    (startIter : Src → m (Option (E × St))) (subOne : Offset → PrefixOffset)
    (oneTo : PrefixOffset → m Prefix) (nextIter : Src → St → m (Option (E × St)))
    (rest : Src → St → m Rest) (take : Rest → I64 → m Taken)
    (write : D → I64 → E → m Unit)
    (dest : D) (dstart : Start) (src : Src) (sstart : Offset) (n : Count),
    negative n = decide (value n < 0) → isZero n = decide (value n = 0) →
    let operation := copytoIterableN negative isZero linearIndices lessOne contains last
      sub addOne le toIntStart toIntCount startIter subOne oneTo nextIter rest take write
      dest dstart src sstart n
    (value n < 0 →
      operation = throw (ArrayError.julia (.argumentError "n should be non-negative"))) ∧
    (value n = 0 → operation = pure dest)

theorem countedIterableCopyGenericEarlyExits_proven : CountedIterableCopyGenericEarlyExits := by
  intro m _ _ _ throwBind D Src E Start Offset PrefixOffset Count Lin End Difference Span Prefix J St
    Rest Taken _ _ value negative isZero linearIndices lessOne contains last sub addOne le
    toIntStart toIntCount startIter subOne oneTo nextIter rest take write dest dstart src
    sstart n negativeLaw zeroLaw
  constructor
  · intro negativeCount
    simp only [copytoIterableN, negativeLaw, negativeCount, decide_true, ite_true]
    exact throwBind _ _ _ _
  · intro zeroCount
    simp [copytoIterableN, negativeLaw, zeroLaw, zeroCount]

/-- The canonical scalar reader belongs to the concrete array type; the generic
dispatch and linear forwarding methods are the source definitions. -/
def defaultScalarRead {A E I : Type} (convert : A → I → Result I64)
    (read : A → I64 → Result E) : A → I → Result E :=
  getindexArray (fun _ => pure ()) errorCanonicalGetindexOther convert
    (fun _ => getindexLinearScalar read)

def defaultCoordinateRead {A E : Type} {n : Nat}
    (convert : A → List I64 → Result (Fin n → I64))
    (read : A → (Fin n → I64) → Result E) : A → List I64 → Result E :=
  getindexArray (fun _ => pure ()) errorCanonicalGetindexOther convert
    (fun _ => getindexCartesianExact read)

def defaultScalarBounds {A I : Type} (value : I → Int) (vector : Bool)
    (axis : A → I64 × I64) (count : A → I64) : A → I → Result Bool :=
  checkboundsOne
    (if vector then eachindexLinearVector (axes1 (fun a => pure [axis a]))
     else eachindexLinear (fun a => pure (count a)) (fun n => pure (int 1, n)))
    (sourceNumericAxisCheck value)

/-- Both eager and lazy scalar defaults use the array's linear index interval.
An in-bounds access returns the stored element for any default computation;
an out-of-bounds access returns exactly the default, including its error. -/
def ScalarDefaultGetContents : Prop :=
  ∀ (A E I : Type) (value : I → Int) (vector : Bool) (axis : A → I64 × I64)
    (count : A → I64) (convert : A → I → Result I64) (read : A → I64 → Result E)
    (element : A → I → E),
    let interval := fun a => if vector then axis a else (int 1, count a)
    (∀ a i, (interval a).1.val ≤ value i ∧ value i ≤ (interval a).2.val →
      ∃ j, convert a i = .ok j ∧ read a j = .ok (element a i)) →
    ∀ (a : A) (i : I) (default : E) (fallback : Unit → Result E),
    let bounds := defaultScalarBounds value vector axis count
    let get := defaultScalarRead convert read
    getDefaultScalar bounds get a i default =
      (if (interval a).1.val ≤ value i ∧ value i ≤ (interval a).2.val
       then .ok (element a i) else .ok default) ∧
    getLazyScalar bounds get fallback a i =
      (if (interval a).1.val ≤ value i ∧ value i ≤ (interval a).2.val
       then .ok (element a i) else fallback ())

theorem scalarDefaultGetContents_proven : ScalarDefaultGetContents := by
  intro A E I value vector axis count convert read element
  let interval := fun a => if vector then axis a else (int 1, count a)
  change (∀ a i, (interval a).1.val ≤ value i ∧ value i ≤ (interval a).2.val →
    ∃ j, convert a i = .ok j ∧ read a j = .ok (element a i)) → _
  intro lawful a i default fallback
  have one : (int 1).val = 1 := rfl
  have bounds : defaultScalarBounds value vector axis count a i =
      .ok (decide ((interval a).1.val ≤ value i ∧ value i ≤ (interval a).2.val)) := by
    cases vector <;>
      simp [defaultScalarBounds, checkboundsOne, eachindexLinearVector,
        eachindexLinear, axes1, tupleGet, sourceNumericAxisCheck, checkindexReal,
        interval, one, Bool.decide_and]
  by_cases valid : (interval a).1.val ≤ value i ∧ value i ≤ (interval a).2.val
  · obtain ⟨j, converted, stored⟩ := lawful a i valid
    simp [getDefaultScalar, getLazyScalar, bounds, defaultScalarRead,
      getindexArray, errorCanonicalGetindexOther, getindexLinearScalar,
      show (if vector = true then axis a else (int 1, count a)) = interval a from rfl,
      valid, converted, stored]
  · simp [getDefaultScalar, getLazyScalar, bounds,
      show (if vector = true then axis a else (int 1, count a)) = interval a from rfl, valid]

/-- Tuple defaults use all coordinates, including omitted singleton axes and
extra singleton coordinates. The canonical tuple reader is a concrete array
type's interface, with its usual in-bounds content law. -/
def CoordinateDefaultGetContents : Prop :=
  ∀ (A E : Type) (n : Nat) (axes : A → List (I64 × I64))
    (length : I64 × I64 → I64)
    (convert : A → List I64 → Result (Fin n → I64))
    (read : A → (Fin n → I64) → Result E)
    (element : A → List I64 → E),
    (∀ a indices, coordinateBoundsReference Subtype.val length (axes a) indices = true →
      ∃ js, convert a indices = .ok js ∧ read a js = .ok (element a indices)) →
    ∀ (a : A) (indices : List I64) (default : E) (fallback : Unit → Result E),
    let bounds := checkboundsMany (fun a => pure (axes a))
      (sourceCoordinateBounds Subtype.val length)
    let get := defaultCoordinateRead convert read
    getDefaultDims bounds get a indices default =
      (if coordinateBoundsReference Subtype.val length (axes a) indices
       then .ok (element a indices) else .ok default) ∧
    getLazyDims bounds get fallback a indices =
      (if coordinateBoundsReference Subtype.val length (axes a) indices
       then .ok (element a indices) else fallback ()) ∧
    getDefaultEmpty (fun a => bounds a []) (fun a => get a []) a default =
      (if coordinateBoundsReference (fun i : I64 => i.val) length (axes a) []
       then .ok (element a []) else .ok default) ∧
    getLazyEmpty (fun a => bounds a []) (fun a => get a []) fallback a =
      (if coordinateBoundsReference (fun i : I64 => i.val) length (axes a) []
       then .ok (element a []) else fallback ())

theorem coordinateDefaultGetContents_proven : CoordinateDefaultGetContents := by
  intro A E n axes length convert read element lawful a indices default fallback
  have bounds (js : List I64) :
      checkboundsMany (fun a => pure (axes a))
          (sourceCoordinateBounds Subtype.val length) a js =
        .ok (coordinateBoundsReference Subtype.val length (axes a) js) := by
    simpa [checkboundsMany] using
      sourceCoordinateBounds_reference Subtype.val length (axes a) js
  have reading (js : List I64)
      (valid : coordinateBoundsReference Subtype.val length (axes a) js = true) :
      defaultCoordinateRead convert read a js = .ok (element a js) := by
    obtain ⟨canonical, converted, stored⟩ := lawful a js valid
    simp [defaultCoordinateRead, getindexArray, errorCanonicalGetindexOther,
      getindexCartesianExact, converted, stored]
  dsimp only
  simp only [getDefaultDims, getLazyDims, getDefaultEmpty, getLazyEmpty, bounds]
  cases valid : coordinateBoundsReference Subtype.val length (axes a) indices <;>
    cases emptyValid : coordinateBoundsReference (fun i : I64 => i.val) length (axes a) [] <;>
    simp [valid, emptyValid, reading]

/-- Constructors of foreign range types expose their documented element sequence.
The reference sequence is mathematical range semantics, independent of mapping. -/
def RangeMapConstructedContents : Prop :=
  (∀ (A S D E F R : Type) (start : A → S) (step : A → D) (last : A → Result E)
    (castStart : S → Result F) (castStep : D → Result F) (castLast : E → Result F)
    (build : F → F → F → Result R) (contents : R → List F)
    (progression : F → F → F → List F),
    (∀ first stride stop out, build first stride stop = .ok out →
      contents out = progression first stride stop) →
    ∀ (a : A) (first stride stop : F) (endpoint : E),
    castStart (start a) = .ok first → castStep (step a) = .ok stride →
    last a = .ok endpoint → castLast endpoint = .ok stop →
    ∀ out, mapStepRange start step last castStart castStep castLast build a = .ok out →
      contents out = progression first stride stop) ∧
  (∀ (A E F R : Type) (start : A → E) (last : A → Result E)
    (cast : E → Result F) (build : F → F → Result R) (contents : R → List F)
    (unitProgression : F → F → List F),
    (∀ first stop out, build first stop = .ok out →
      contents out = unitProgression first stop) →
    ∀ (a : A) (first stop : F) (endpoint : E),
    cast (start a) = .ok first → last a = .ok endpoint → cast endpoint = .ok stop →
    ∀ out, mapUnitRange start last cast build a = .ok out →
      contents out = unitProgression first stop) ∧
  (∀ (A E F R : Type) (start stop : A → E) (cast : E → Result F)
    (length : A → Result I64) (build : F → F → I64 → Result R)
    (contents : R → List F) (linProgression : F → F → I64 → List F),
    (∀ first last count out, build first last count = .ok out →
      contents out = linProgression first last count) →
    ∀ (a : A) (first last : F) (count : I64),
    cast (start a) = .ok first → cast (stop a) = .ok last → length a = .ok count →
    ∀ out, mapLinRange start stop cast length build a = .ok out →
      contents out = linProgression first last count)

theorem rangeMapConstructedContents_proven : RangeMapConstructedContents := by
  refine ⟨?_, ?_, ?_⟩
  · intro A S D E F R start step last castStart castStep castLast build contents
      progression buildLaw a first stride stop endpoint hfirst hstride hlast hstop out result
    apply buildLaw first stride stop out
    simpa [mapStepRange, hfirst, hstride, hlast, hstop] using result
  · intro A E F R start last cast build contents progression buildLaw a first stop endpoint
      hfirst hlast hstop out result
    apply buildLaw first stop out
    simpa [mapUnitRange, hfirst, hlast, hstop] using result
  · intro A E F R start stop cast length build contents progression buildLaw a first last count
      hfirst hlast hcount out result
    apply buildLaw first last count out
    simpa [mapLinRange, hfirst, hlast, hcount] using result

def denseScalarOffset {A Lin : Type}
    (linear : A → Result Lin) (first : Lin → Result I64)
    (typeof : A → Type) (bytes : Type → Result I64) : A → I64 → Result I64 :=
  memoryOffsetDense (fun a i => pure (toLinearScalar a i)) linear first
    (fun a b => pure (a - b)) (elsize typeof bytes) (fun a b => pure (a * b))

/-- Native byte arithmetic wraps modulo the address width. This statement also
covers overflow in the intermediate index subtraction and byte multiplication. -/
def DensePointerBytePositions : Prop :=
  ∀ (A Lin Converted Ptr : Type) (linear : A → Result Lin) (first : Lin → Result I64)
    (typeof : A → Type) (bytes : Type → Result I64) (cconvert : A → Result Converted)
    (unsafeConvert : Converted → Result Ptr) (add : Ptr → I64 → Result Ptr)
    (address : Ptr → Int),
    (∀ p offset, ∃ out, add p offset = .ok out ∧
      address out = (address p + offset.val) % 18446744073709551616) →
    ∀ (a : A) (i origin width : I64) (lin : Lin) (converted : Converted) (base : Ptr),
    linear a = .ok lin → first lin = .ok origin → bytes (typeof a) = .ok width →
    denseScalarOffset linear first typeof bytes a i =
      .ok (int ((i.val - origin.val) * width.val)) ∧
    (cconvert a = .ok converted → unsafeConvert converted = .ok base →
      ∃ out, pointerIndex (pointerArray cconvert unsafeConvert)
          (denseScalarOffset linear first typeof bytes) (fun n => pure n) add a i = .ok out ∧
        address out = (address base + (i.val - origin.val) * width.val) % 18446744073709551616)

theorem densePointerBytePositions_proven : DensePointerBytePositions := by
  intro A Lin Converted Ptr linear first typeof bytes cconvert unsafeConvert add address
    addLaw a i origin width lin converted base hlin horigin hwidth
  have widthEq : width = int width.val := by
    apply Subtype.ext
    exact (wrapInt_of_inRange .i64 width.val width.property).symm
  have product : (i - origin) * width = int ((i.val - origin.val) * width.val) := by
    change int (i.val - origin.val) * width = _
    calc
      _ = int (i.val - origin.val) * int width.val :=
        congrArg (fun w => int (i.val - origin.val) * w) widthEq
      _ = _ := nativeStrideMul _ _
  have offset : denseScalarOffset linear first typeof bytes a i =
      .ok (int ((i.val - origin.val) * width.val)) := by
    simp [denseScalarOffset, memoryOffsetDense, toLinearScalar, elsize,
      hlin, horigin, hwidth, product]
  refine ⟨offset, ?_⟩
  intro hconvert hbase
  obtain ⟨out, added, location⟩ :=
    addLaw base (int ((i.val - origin.val) * width.val))
  refine ⟨out, ?_, ?_⟩
  · simp [pointerIndex, pointerArray, hconvert, hbase, offset, added]
  · have residue : (int ((i.val - origin.val) * width.val)).val %
        18446744073709551616 =
        ((i.val - origin.val) * width.val) % 18446744073709551616 :=
      nativeWrap_mod _
    rw [location, Int.add_emod, residue, ← Int.add_emod]

/-! Nothing to promise:
stack@2967: forwards the keyword dimension and iterator unchanged to the positional implementation.
_stack@2999: selects the positional implementation from the foreign IteratorSize trait.
_iterator_axes@3034: selects the axis implementation from the foreign IteratorSize trait.
_iterator_axes@3036: forwards the object unchanged to its axes interface.
_typed_stack@3039: adds the foreign IteratorSize trait to the unchanged type and iterator arguments.
_typed_stack@3048: forwards the unchanged dimension, types, and iterator to _dim_stack.
_ensure_array@3098: returns the existing array exemplar unchanged.
OrderStyle@3147: forwards the element type to its foreign ordering-style interface.
_ind2sub@3172: forwards the array axes and unchanged linear index to the tuple implementation.
_indexlength@3229: returns the dimension length unchanged.
_indexlength@3230: forwards the range unchanged to its length interface.
-/

/-- Only the single-item prepend method is foreign: abstractarray.jl defines
the two-item and variadic dispatches, and both are used at every recursive call. -/
def sourcePrependItems {C E : Type} (prepend : C → E → Result C) :
    List E → C → Result C
  | [], a => pure a
  | [x], a => prepend a x
  | [x, y], a => pushfirstTwo prepend prepend a x y
  | x :: y :: z :: rest, a =>
    pushfirstMany (fun a _ => sourcePrependItems prepend (z :: rest) a)
      (pushfirstTwo prepend prepend) a x y (z :: rest)
termination_by items _ => items.length

def PrependTwoContents : Prop :=
  ∀ (C E : Type) (elements : C → List E) (prepend : C → E → Result C),
    (∀ a x, ∃ out, prepend a x = .ok out ∧ elements out = x :: elements a) →
    ∀ a x y, ∃ out, pushfirstTwo prepend prepend a x y = .ok out ∧
      elements out = [x, y] ++ elements a

theorem prependTwoContents_proven : PrependTwoContents := by
  intro C E elements prepend lawful a x y
  obtain ⟨b, first, byValues⟩ := lawful a y
  obtain ⟨out, second, outValues⟩ := lawful b x
  refine ⟨out, ?_, ?_⟩
  · simp [pushfirstTwo, first, second]
  · simp [outValues, byValues]

def PrependVariadicContents : Prop :=
  ∀ (C E : Type) (elements : C → List E) (prepend : C → E → Result C),
    (∀ a x, ∃ out, prepend a x = .ok out ∧ elements out = x :: elements a) →
    ∀ items a, ∃ out, sourcePrependItems prepend items a = .ok out ∧
      elements out = items ++ elements a

theorem sourcePrependItems_contents {C E : Type} (elements : C → List E)
    (prepend : C → E → Result C)
    (lawful : ∀ a x, ∃ out, prepend a x = .ok out ∧ elements out = x :: elements a)
    (items : List E) (a : C) :
    ∃ out, sourcePrependItems prepend items a = .ok out ∧
      elements out = items ++ elements a := by
  cases items with
  | nil => exact ⟨a, by simp [sourcePrependItems], rfl⟩
  | cons x items =>
    cases items with
    | nil =>
      obtain ⟨out, run, values⟩ := lawful a x
      exact ⟨out, by simpa [sourcePrependItems] using run, by simpa using values⟩
    | cons y rest =>
      cases rest with
      | nil =>
        simpa [sourcePrependItems] using
          prependTwoContents_proven C E elements prepend lawful a x y
      | cons z zs =>
        obtain ⟨b, runRest, bValues⟩ :=
          sourcePrependItems_contents elements prepend lawful (z :: zs) a
        obtain ⟨out, runTwo, outValues⟩ :=
          prependTwoContents_proven C E elements prepend lawful b x y
        refine ⟨out, ?_, ?_⟩
        · simp [sourcePrependItems, pushfirstMany, runRest, runTwo]
        · simp [outValues, bValues]
termination_by items.length

theorem prependVariadicContents_proven : PrependVariadicContents := by
  intro C E elements prepend lawful items a
  exact sourcePrependItems_contents elements prepend lawful items a

def StackAxisMetadata : Prop :=
  (∀ (X Ax : Type) (length : X → Result I64) (oneTo : I64 → Result Ax)
    (first : Ax → I64) (count : Ax → Nat),
    (∀ n ax, 0 ≤ n.val → oneTo n = .ok ax →
      first ax = int 1 ∧ count ax = n.val.toNat) →
    ∀ x n, length x = .ok n → 0 ≤ n.val →
      ∀ axes, iteratorAxesLength length oneTo x = .ok axes →
        axes.length = 1 ∧ ∀ ax ∈ axes, first ax = int 1 ∧ count ax = n.val.toNat) ∧
  (∀ (Ax : Type) (only : List Ax → Result Ax)
    (product : List Ax → Result I64) (oneTo : I64 → Result Ax)
    (first : Ax → I64) (count : Ax → Nat),
    (∀ ax, only [ax] = .ok ax) →
    (∀ axes, product axes = .ok (int ((axes.map (fun ax => (count ax : Int))).prod))) →
    (∀ n ax, oneTo n = .ok ax → first ax = int 1 ∧ count ax = n.val.toNat) →
    ∀ axes out, vecAxis only product oneTo axes = .ok out →
      (axes.length = 1 → axes = [out]) ∧
      (axes.length ≠ 1 → first out = int 1 ∧
        count out = (int ((axes.map (fun ax => (count ax : Int))).prod)).val.toNat)) ∧
  (∀ (A Ax : Type) (range : I64 → I64 → Result Ax) (count : Ax → Nat),
    (∀ ax, range (int 1) (int 0) = .ok ax → count ax = 0) →
    ∀ x out, ensureArrayOther range (x : A) = .ok out → count out = 0)

theorem stackAxisMetadata_proven : StackAxisMetadata := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Ax length oneTo first count constructorLaw x n lengthLaw nonnegative axes result
    cases built : oneTo n with
    | error error => simp [iteratorAxesLength, lengthLaw, built] at result
    | ok ax =>
      have axesEq : axes = [ax] := by
        simpa [iteratorAxesLength, lengthLaw, built] using result.symm
      subst axes
      exact ⟨rfl, by simpa using constructorLaw n ax nonnegative built⟩
  · intro Ax only product oneTo first count onlyLaw productLaw constructorLaw axes out result
    constructor
    · intro singleton
      obtain ⟨ax, same⟩ := List.length_eq_one_iff.mp singleton
      subst axes
      have : ax = out := by simpa [vecAxis, onlyLaw] using result
      simp [this]
    · intro multiple
      exact constructorLaw _ _ (by simpa [vecAxis, multiple, productLaw] using result)
  · intro A Ax range count constructorLaw x out result
    exact constructorLaw out result

def StackUniformSlices : Prop :=
  ∀ (X Ax Range : Type) [DecidableEq Ax]
    (axes : X → Result (List Ax)) (unitRange : Ax → Range)
    (showAxes : List Range → String) (x : X) (actual expected : List Ax),
    axes x = .ok actual →
    (stackSizeCheck
      (iteratorAxes (fun _ => pure ()) (fun x _ => iteratorAxesShape axes x))
      (fun ax => pure (unitRange ax)) showAxes x expected = .ok () ↔ actual = expected) ∧
    (actual ≠ expected → ∃ message,
      stackSizeCheck
        (iteratorAxes (fun _ => pure ()) (fun x _ => iteratorAxesShape axes x))
        (fun ax => pure (unitRange ax)) showAxes x expected =
          .error (.dimensionMismatch message))

theorem stackUniformSlices_proven : StackUniformSlices := by
  intro X Ax Range _ axes unitRange showAxes x actual expected axesLaw
  by_cases equal : actual = expected
  · subst expected
    simp [stackSizeCheck, iteratorAxes, iteratorAxesShape, axesLaw]
  · simp [stackSizeCheck, iteratorAxes, iteratorAxesShape, axesLaw, equal,
      mapM_pure_result]
    exact ⟨_, rfl⟩

def EmptyRankInverseBounds : Prop :=
  ∀ (I : Type) (value : I → Int) (isOne : I → Bool),
    (∀ i, isOne i = decide (value i = 1)) →
    ∀ i, (ind2subEmpty isOne i = .ok [] ↔ value i = 1) ∧
      (value i ≠ 1 → ind2subEmpty isOne i = .error (.julia .boundsError))

theorem emptyRankInverseBounds_proven : EmptyRankInverseBounds := by
  intro I value isOne integerLaw i
  by_cases one : value i = 1 <;> simp [ind2subEmpty, integerLaw, one] <;> rfl

def AmbiguousInverseRejected : Prop :=
  ∀ (Ax I R : Type) (axes : Ax) (index : I) (rest : List I), ∃ message,
    ind2subAmbiguousOneDim (R := R) axes index = .error (.julia (.argumentError message)) ∧
    sub2indVectorsAmbiguous (R := R) axes index rest =
      .error (.julia (.argumentError message))

theorem ambiguousInverseRejected_proven : AmbiguousInverseRejected := by
  intro Ax I R axes index rest
  exact ⟨"Linear indexing is not defined for one-dimensional arrays", rfl, rfl⟩

/-! Nothing to promise:
sizehint!@3685: the abstract-vector fallback returns the identical vector without changing storage.
-/

theorem nativeSumResidue (xs : List Int) :
    ((xs.map (wrapInt .i64)).sum) % 18446744073709551616 =
      xs.sum % 18446744073709551616 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Int.add_emod, nativeWrap_mod, ih, ← Int.add_emod]

/-- Exact-rank strided offsets equal the coordinate/stride dot product in
native byte arithmetic, including all intermediate overflow. Tuple map and
sum are foreign tuple/reduction interfaces with their usual laws. -/
def StridedMemoryBytePositions : Prop :=
  ∀ (A : Type) (n : Nat) (strides origins : A → Result (Fin n → I64))
    (typeof : A → Type) (bytes : Type → Result I64)
    (map3 : (I64 → I64 → I64 → Result I64) →
      (Fin n → I64) → (Fin n → I64) → (Fin n → I64) → Result (List I64))
    (sum : List I64 → Result I64),
    (∀ f is ss os, map3 f is ss os =
      (List.finRange n).mapM (fun k => f (is k) (ss k) (os k))) →
    (∀ values, sum values = .ok (int ((values.map Subtype.val).sum))) →
    ∀ (a : A) (indices ss os : Fin n → I64) (width : I64),
    strides a = .ok ss → origins a = .ok os → bytes (typeof a) = .ok width →
    memoryOffsetArray (fun a is => pure (toSubscriptsExact a is)) strides origins
      (fun i o : I64 => pure (i - o)) (fun s d : I64 => pure (s * d))
      map3 sum (elsize typeof bytes) (fun total width : I64 => pure (total * width))
      a indices =
        .ok (int (((List.finRange n).map
          (fun k => (ss k).val * ((indices k).val - (os k).val))).sum * width.val))

theorem stridedMemoryBytePositions_proven : StridedMemoryBytePositions := by
  intro A n strides origins typeof bytes map3 sum mapLaw sumLaw a indices ss os width
    strideLaw originLaw widthLaw
  let products := (List.finRange n).map
    (fun k => (ss k).val * ((indices k).val - (os k).val))
  have pointwise (k : Fin n) :
      ss k * (indices k - os k) =
        int ((ss k).val * ((indices k).val - (os k).val)) := by
    have rewrap : ss k = int (ss k).val := by
      apply Subtype.ext
      exact (wrapInt_of_inRange .i64 _ (ss k).property).symm
    change ss k * int ((indices k).val - (os k).val) = _
    calc
      _ = int (ss k).val * int ((indices k).val - (os k).val) :=
        congrArg (fun s => s * int ((indices k).val - (os k).val)) rewrap
      _ = _ := nativeStrideMul _ _
  have mapped :
      map3 (fun i s o => .ok (s * (i - o))) indices ss os =
        .ok (products.map int) := by
    rw [mapLaw]
    simp [pointwise, mapM_pure_result, products, List.map_map]
  have summed : sum (products.map int) = .ok (int products.sum) := by
    rw [sumLaw]
    congr 1
    apply Subtype.ext
    apply nativeWrap_eq
    simpa only [List.map_map, Function.comp_def, int, JInt.lit, JInt.wrap] using
      nativeSumResidue products
  have rewrap : width = int width.val := by
    apply Subtype.ext
    exact (wrapInt_of_inRange .i64 _ width.property).symm
  have multiplied : int products.sum * width = int (products.sum * width.val) := by
    calc
      _ = int products.sum * int width.val :=
        congrArg (fun w => int products.sum * w) rewrap
      _ = _ := nativeStrideMul _ _
  change memoryOffsetArray _ _ _ _ _ _ _ _ _ a indices =
    .ok (int (products.sum * width.val))
  simp [memoryOffsetArray, toSubscriptsExact, strideLaw, originLaw, elsize, widthLaw,
    mapped, summed, multiplied]

def lexicalElements {E : Type} (equal less : E → E → Bool) : List E → List E → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    if equal x y then lexicalElements equal less xs ys else if less x y then -1 else 1

def signedComparison (x y : Int) : I64 :=
  if x < y then int (-1) else if y < x then int 1 else int 0

def lexicalLoopStep {E : Type} (equal less : E → E → Bool)
    (pair : E × E) (_state : Option I64 × Unit) :
    Result (ForInStep (Option I64 × Unit)) :=
  if !(equal pair.1 pair.2) then
    pure (.done (some (if less pair.1 pair.2 then int (-1) else int 1), ()))
  else pure (.yield (none, ()))

theorem lexicalLoop_reference {E : Type} (equal less : E → E → Bool) (xs ys : List E) :
    (do
      let result ← forIn (xs.zip ys) (none, ()) (lexicalLoopStep equal less)
      pure (result.1.getD (signedComparison xs.length ys.length)) : Result I64) =
        .ok (int (lexicalElements equal less xs ys)) := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> simp [lexicalElements, List.forIn_nil, signedComparison]
  | cons x xs ih =>
    cases ys with
    | nil => simp [lexicalElements, List.forIn_nil, signedComparison] <;> omega
    | cons y ys =>
      have lengthCmp :
          signedComparison ((xs.length : Int) + 1) ((ys.length : Int) + 1) =
            signedComparison xs.length ys.length := by
        simp [signedComparison]
      cases eqHead : equal x y with
      | false =>
        cases lessHead : less x y <;>
          simp [List.forIn_cons, lexicalLoopStep, lexicalElements, eqHead, lessHead]
      | true =>
        simpa [List.forIn_cons, lexicalLoopStep, lexicalElements, eqHead, lengthCmp] using ih ys

def sourceVectorComparison {A E : Type} (first : A → I64) (values : A → List E)
    (equal less : E → E → Bool) (compareNative : I64 → I64 → Result I64) :
    A → A → Result I64 :=
  vectorCmp
    (fun a => vectorFirstIndex (first a) (values a).length)
    (fun a => vectorFirstIndex (first a) (values a).length)
    (fun i j => pure (decide (i = j))) compareNative
    (fun a b => pure ((values a).zip (values b)))
    (fun a b => pure (equal a b)) (fun a b => pure (less a b))
    (fun a => pure (int (values a).length)) (fun a => pure (int (values a).length))
    compareNative

theorem vectorFirstIndex_value {I : Type} (first : I) (count : Nat) :
    vectorFirstIndex first count = .ok first := by rfl

theorem sourceVectorComparison_reference {A E : Type} (first : A → I64)
    (values : A → List E) (equal less : E → E → Bool)
    (compareNative : I64 → I64 → Result I64)
    (compareLaw : ∀ i j, compareNative i j = .ok (signedComparison i.val j.val))
    (a b : A) (fitA : (values a).length ≤ IntTy.i64.max)
    (fitB : (values b).length ≤ IntTy.i64.max) :
    sourceVectorComparison first values equal less compareNative a b =
      .ok (if (first a).val < (first b).val then int (-1)
        else if (first b).val < (first a).val then int 1
        else int (lexicalElements equal less (values a) (values b))) := by
  have lengthA : (int (values a).length).val = (values a).length :=
    wrapInt_of_inRange .i64 _ ⟨by
      have lower : IntTy.i64.min ≤ 0 := by decide
      omega, fitA⟩
  have lengthB : (int (values b).length).val = (values b).length :=
    wrapInt_of_inRange .i64 _ ⟨by
      have lower : IntTy.i64.min ≤ 0 := by decide
      omega, fitB⟩
  by_cases same : first a = first b
  · have loop := lexicalLoop_reference equal less (values a) (values b)
    rw [← result_option_finish
      (fallback := fun _ => signedComparison (values a).length (values b).length)] at loop
    delta lexicalLoopStep at loop
    simp [sourceVectorComparison, vectorCmp, vectorFirstIndex_value, same,
      compareLaw, lengthA, lengthB] at loop ⊢
    exact loop
  · have different : (first a).val ≠ (first b).val := by
      intro h; exact same (Subtype.ext h)
    by_cases lower : (first a).val < (first b).val
    · simp [sourceVectorComparison, vectorCmp, vectorFirstIndex_value, same,
        compareLaw, signedComparison, lower]
    · have upper : (first b).val < (first a).val := by omega
      simp [sourceVectorComparison, vectorCmp, vectorFirstIndex_value, same,
        compareLaw, signedComparison, lower, upper]

def VectorLexicalOrder : Prop :=
  ∀ (A E : Type) (first : A → I64) (values : A → List E)
    (equal less : E → E → Bool) (compareNative : I64 → I64 → Result I64),
    (∀ i j, compareNative i j = .ok (signedComparison i.val j.val)) →
    ∀ a b, (values a).length ≤ IntTy.i64.max → (values b).length ≤ IntTy.i64.max →
    let expected := if (first a).val < (first b).val then int (-1)
      else if (first b).val < (first a).val then int 1
      else int (lexicalElements equal less (values a) (values b))
    sourceVectorComparison first values equal less compareNative a b = .ok expected ∧
    vectorIsless (sourceVectorComparison first values equal less compareNative) a b =
      .ok (decide (expected.val < 0))

theorem vectorLexicalOrder_proven : VectorLexicalOrder := by
  intro A E first values equal less compareNative compareLaw a b fitA fitB
  have result := sourceVectorComparison_reference first values equal less compareNative
    compareLaw a b fitA fitB
  exact ⟨result, by simp [vectorIsless, result]⟩

def ScalarArrayOrder : Prop :=
  ∀ (A B E F : Type) (onlyA : A → Result E) (onlyB : B → Result F)
    (less : E → F → Result Bool) (a : A) (b : B) (x : E) (y : F),
    onlyA a = .ok x → onlyB b = .ok y →
    ∀ (order : E → F → Bool), (∀ x y, less x y = .ok (order x y)) →
      arrayIslessZeroDim onlyA onlyB less a b = .ok (order x y)

theorem scalarArrayOrder_proven : ScalarArrayOrder := by
  intro A B E F onlyA onlyB less a b x y readA readB order lawful
  simp [arrayIslessZeroDim, readA, readB, lawful]

theorem nativeAddSubCancel (a b : I64) : (a + b) - b = a := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 (a.val + b.val) - b.val) = a.val
  calc
    _ = wrapInt .i64 a.val := by
      apply nativeWrap_eq
      rw [Int.sub_emod, nativeWrap_mod, ← Int.sub_emod]
      congr 1
      omega
    _ = _ := wrapInt_of_inRange .i64 _ a.property

theorem nativeSubAddCancel (a b : I64) : (a - b) + b = a := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 (a.val - b.val) + b.val) = a.val
  calc
    _ = wrapInt .i64 a.val := by
      apply nativeWrap_eq
      rw [Int.add_emod, nativeWrap_mod, ← Int.add_emod]
      congr 1
      omega
    _ = _ := wrapInt_of_inRange .i64 _ a.property

/-- Range-relative offsets and coordinate lookup undo each other even at
native overflow boundaries. Terminal inverse tuples retain that offset. -/
def NativeCoordinateLookupInverse : Prop :=
  (∀ (Axis : Type) (first : Axis → Result I64) (axis : Axis)
    (origin offset index : I64), first axis = .ok origin →
    (do
      let coordinate ← lookupRange first (fun i o => pure (i + o)) offset axis
      offsetinRange first (fun i o => pure (i - o)) coordinate axis) = .ok offset ∧
    (do
      let displacement ← offsetinRange first (fun i o => pure (i - o)) index axis
      lookupRange first (fun i o => pure (i + o)) displacement axis) = .ok index ∧
    (do
      let coordinates ← ind2subRecurseLast (fun _ : Unit => pure axis)
        (lookupRange first (fun i o => pure (i + o))) () offset
      coordinates.mapM (fun i => offsetinRange first (fun i o => pure (i - o)) i axis)) =
        .ok [offset]) ∧
  (∀ (D : Type) (dimension : D) (offset : I64),
    (do
      let coordinate ← lookupInteger (fun i => pure (i + int 1)) offset dimension
      offsetinInteger (fun i o => pure (i - o)) coordinate dimension) = .ok offset ∧
    (do
      let coordinates ← ind2subRecurseEmpty (fun i => pure (i + int 1)) offset
      coordinates.mapM (fun i => offsetinInteger (fun i o => pure (i - o)) i dimension)) =
        .ok [offset])

theorem nativeCoordinateLookupInverse_proven : NativeCoordinateLookupInverse := by
  constructor
  · intro Axis first axis origin offset index firstLaw
    simp [lookupRange, offsetinRange, firstLaw, nativeAddSubCancel,
      nativeSubAddCancel, ind2subRecurseLast]
  · intro D dimension offset
    simp [lookupInteger, offsetinInteger, ind2subRecurseEmpty, nativeAddSubCancel]

/-- The scalar getindex method of each concrete input vector is a foreign
canonical interface; tuple traversal itself uses both source dispatches. -/
def sourceVectorCoordinates {V E : Type} (get : V → I64 → Result E)
    (i : I64) : List V → Result (List E)
  | [] => pure (sub2indVecEmpty i)
  | v :: vs =>
    sub2indVecMore get (fun _ _ => sourceVectorCoordinates get i vs) i v vs

def VectorCoordinateTupleContents : Prop :=
  ∀ (V E : Type) (get : V → I64 → Result E) (element : V → I64 → E)
    (i : I64) (vectors : List V),
    (∀ v ∈ vectors, get v i = .ok (element v i)) →
    sourceVectorCoordinates get i vectors = .ok (vectors.map (fun v => element v i))

theorem vectorCoordinateTupleContents_proven : VectorCoordinateTupleContents := by
  intro V E get element i vectors
  induction vectors with
  | nil => intro _; rfl
  | cons v vs ih =>
    intro lawful
    have head := lawful v (by simp)
    have tail := ih (fun v hv => lawful v (by simp [hv]))
    simp [sourceVectorCoordinates, sub2indVecMore, head, tail]

/-! Nothing to promise:
_ind2sub@3215: packages the already linear OneTo coordinate in a singleton tuple.
_sub2ind@3238: forwards the axis tuple and unchanged index-vector tuple to _sub2ind_vecs.
_sub2ind@3240: forwards the dimensions or axes and unchanged index-vector tuple to _sub2ind_vecs.
-/

open JuliaLean.base.array (VectorHeap HeapArray VectorM heapAllocate heapCopyReferences)

/-- The dense Julia copy method runs on the same heap as all live destinations.
Its allocator appends a distinct memory object; it does not fabricate a snapshot. -/
def denseSharedCopy {Tag E : Type} (a : HeapArray Tag) : VectorM E (HeapArray Tag) :=
  JuliaLean.base.array.copyArray
    (fun a => pure (a.handle, int 1))
    (fun a => pure (int a.dimensions.prod))
    (fun _ n => heapAllocate n.val.toNat)
    (fun handle => pure (handle, int 1))
    (heapCopyReferences (fun value => pure value))
    (fun a => pure a.dimensions)
    (fun ref dimensions =>
      pure ⟨ref.1, a.elementType, dimensions, dimensions.map (fun n => (1, n))⟩) a

theorem densePureMap {E : Type} (values : List (Option E)) :
    values.mapM (fun value => (pure value : Except JuliaLean.base.array.Error (Option E))) =
      .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have tail : values.mapM (fun value => Except.ok value) =
        (Except.ok values : Except JuliaLean.base.array.Error (List (Option E))) := by
      simpa only [pure, Except.pure] using ih
    simp only [List.mapM_cons, pure, Except.pure, bind, Except.bind]
    rw [tail]

theorem nativeArrayCountValue (count : Nat) (fit : count < 2 ^ 63) :
    (int count).val = count := by
  change wrapInt .i64 (count : Int) = (count : Int)
  apply wrapInt_of_inRange
  constructor
  · have lower : IntTy.i64.min ≤ 0 := by decide
    omega
  · change (count : Int) ≤ 9223372036854775807
    have upper : count < 9223372036854775808 := fit
    omega

theorem denseSharedCopy_run {Tag E : Type} (heap : VectorHeap E) (src : HeapArray Tag)
    (slots : List (Option E)) (present : heap[src.handle]? = some slots)
    (shape : src.dimensions.prod = slots.length) (fit : slots.length < 2 ^ 63) :
    (denseSharedCopy src).run heap =
      .ok (⟨heap.length, src.elementType, src.dimensions,
        src.dimensions.map (fun n => (1, n))⟩, heap ++ [slots]) := by
  let fresh := heap ++ [List.replicate slots.length none]
  have sourceBound : src.handle < heap.length :=
    (List.getElem?_eq_some_iff.mp present).choose
  have sourcePresent : fresh[src.handle]? = some slots := by
    simp [fresh, List.getElem?_append_left sourceBound, present]
  have freshPresent : fresh[heap.length]? = some (List.replicate slots.length none) := by
    simp [fresh]
  have countValue : (int slots.length).val = slots.length := by
    change wrapInt .i64 (slots.length : Int) = (slots.length : Int)
    apply wrapInt_of_inRange
    constructor
    · have lower : IntTy.i64.min ≤ 0 := by decide
      omega
    · change (slots.length : Int) ≤ 9223372036854775807
      have upper : slots.length < 9223372036854775808 := fit
      omega
  have copied := JuliaLean.Proofs.base.array.heapCopyReferences_whole_run
    (fun value : Option E => pure value) fresh heap.length src.handle slots
    (List.replicate slots.length none) sourcePresent freshPresent
    (by simp) fit
  have replaced : fresh.set heap.length slots = heap ++ [slots] := by
    simp [fresh]
  have copyResult :
      (heapCopyReferences (fun value : Option E => pure value)
        (heap.length, int 1) (src.handle, int 1) (int slots.length)).run fresh =
          .ok ((), heap ++ [slots]) := by
    change (heapCopyReferences (fun value : Option E => pure value)
      (heap.length, JuliaLean.base.array.one) (src.handle, JuliaLean.base.array.one)
      (JInt.wrap .i64 slots.length)).run fresh = _
    rw [copied, densePureMap]
    simp [Except.map, replaced]
  simp only [denseSharedCopy, JuliaLean.base.array.copyArray,
    JuliaLean.Proofs.base.array.vector_bind_run, JuliaLean.Proofs.base.array.vector_pure_run,
    shape, countValue, Int.toNat_natCast, JuliaLean.Proofs.base.array.heapAllocate_run]
  rw [copyResult]

def denseHeapDataids {Tag E : Type} (pointer : Nat → JInt .u64) :
    HeapArray Tag → VectorM E (List (JInt .u64)) :=
  dataidsDense (fun a => a.handle) id
    (dataidsMemory id (fun handle => pure (pointer handle)))

def denseHeapEmpty {Tag E : Type} : HeapArray Tag → VectorM E Bool :=
  isemptyArray (fun a => pure (int a.dimensions.prod))

def denseHeapMightalias {Tag E : Type} (pointer : Nat → JInt .u64) :
    HeapArray Tag → HeapArray Tag → VectorM E Bool :=
  mightaliasArray (fun _ => pure false) (fun _ => pure false)
    denseHeapEmpty denseHeapEmpty
    (denseHeapDataids pointer) (denseHeapDataids pointer)
    (fun ds ss => pure (disjointCalls ds ss))

def denseHeapUnalias {Tag E : Type} (pointer : Nat → JInt .u64) :
    HeapArray Tag → HeapArray Tag → VectorM E (HeapArray Tag) :=
  unaliasArray (denseHeapMightalias pointer) (unaliascopyDense denseSharedCopy)

def DenseHeapUnaliasSeparation : Prop :=
  ∀ (Tag E : Type) (pointer : Nat → JInt .u64) (heap : VectorHeap E)
    (dest src : HeapArray Tag) (slots : List (Option E)),
    heap[src.handle]? = some slots → src.dimensions.prod = slots.length →
    slots.length < 2 ^ 63 → dest.dimensions.prod < 2 ^ 63 → dest.handle < heap.length →
    (dest.dimensions.prod ≠ 0 → src.dimensions.prod ≠ 0 →
      pointer dest.handle = pointer src.handle → dest.handle = src.handle) →
    ∃ out next, (denseHeapUnalias pointer dest src).run heap = .ok (out, next) ∧
      next[out.handle]? = some slots ∧ out.dimensions = src.dimensions ∧
      out.elementType = src.elementType ∧
      (∀ old, old < heap.length → next[old]? = heap[old]?) ∧
      (out.handle ≠ dest.handle ∨ src.dimensions.prod = 0 ∨ dest.dimensions.prod = 0) ∧
      ((dest.handle ≠ src.handle ∨ src.dimensions.prod = 0 ∨ dest.dimensions.prod = 0) →
        out = src ∧ next = heap)

theorem denseHeapUnaliasSeparation_proven : DenseHeapUnaliasSeparation := by
  intro Tag E pointer heap dest src slots present shape fit destFit destLive injective
  have srcValue : (int src.dimensions.prod).val = src.dimensions.prod :=
    nativeArrayCountValue _ (by omega)
  have destValue : (int dest.dimensions.prod).val = dest.dimensions.prod :=
    nativeArrayCountValue _ destFit
  have zeroValue : (int 0).val = 0 := rfl
  have program :
      (denseHeapUnalias pointer dest src).run heap =
        if dest.handle ≠ src.handle ∨ src.dimensions.prod = 0 ∨ dest.dimensions.prod = 0
        then .ok (src, heap) else (denseSharedCopy src).run heap := by
    simp only [denseHeapUnalias, unaliasArray, denseHeapMightalias, mightaliasArray,
      denseHeapEmpty, isemptyArray, denseHeapDataids, dataidsDense, dataidsMemory,
      unaliascopyDense, pure_bind]
    by_cases same : dest.handle = src.handle
    · by_cases srcEmpty : src.dimensions.prod = 0 <;>
        by_cases destEmpty : dest.dimensions.prod = 0 <;>
        simp [disjointCalls, isdisjointOneOne, srcValue, destValue,
          zeroValue, same, srcEmpty, destEmpty] <;> rfl
    · have pointerNe (nonemptySrc : src.dimensions.prod ≠ 0)
          (nonemptyDest : dest.dimensions.prod ≠ 0) :
          pointer dest.handle ≠ pointer src.handle := by
        intro equal
        exact same (injective nonemptyDest nonemptySrc equal)
      by_cases srcEmpty : src.dimensions.prod = 0 <;>
        by_cases destEmpty : dest.dimensions.prod = 0 <;>
        simp [disjointCalls, isdisjointOneOne, srcValue, destValue,
          zeroValue, same, pointerNe, srcEmpty, destEmpty] <;> rfl
  by_cases unchanged : dest.handle ≠ src.handle ∨ src.dimensions.prod = 0 ∨ dest.dimensions.prod = 0
  · refine ⟨src, heap, by simpa [unchanged] using program, present, rfl, rfl,
      fun _ _ => rfl, ?_, fun _ => ⟨rfl, rfl⟩⟩
    rcases unchanged with different | emptySource | emptyDest
    · exact Or.inl (Ne.symm different)
    · exact Or.inr (Or.inl emptySource)
    · exact Or.inr (Or.inr emptyDest)
  · let out : HeapArray Tag :=
      ⟨heap.length, src.elementType, src.dimensions, src.dimensions.map (fun n => (1, n))⟩
    refine ⟨out, heap ++ [slots], ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · rw [program, if_neg unchanged]
      exact denseSharedCopy_run heap src slots present shape fit
    · simp [out]
    · intro old bound
      exact List.getElem?_append_left bound
    · exact Or.inl (by dsimp [out]; omega)
    · intro impossible
      exact False.elim (unchanged impossible)

/-- LinearIndices supplies endpoints and its ordered native indices. -/
structure CopyLinearIndices where
  first : I64
  last : I64
  indices : List I64

instance copyLinearForIn {m : Type → Type} [Monad m] : ForIn m CopyLinearIndices I64 where
  forIn indices initial step := forIn indices.indices initial step

def copyLinearBounds (indices : CopyLinearIndices) (i : I64) : Result Bool :=
  checkboundsOne
    (eachindexLinearVector (axes1 (fun indices : CopyLinearIndices =>
      pure [(indices.first, indices.last)])))
    sourceAxisCheck indices i


def copyIndexSpace {A I : Type} (style : Bool) (indices : List I) (a : A) :
    Result (List I) :=
  eachindexArray (fun _ => pure style)
    (fun selected a =>
      if selected then eachindexLinearVector (axes1 (fun _ => pure [indices])) a
      else pure indices) a

@[local simp] theorem copyIndexSpace_value {A I : Type} (style : Bool)
    (indices : List I) (a : A) : copyIndexSpace style indices a = .ok indices := by
  have one : (int 1).val = 1 := rfl
  cases style <;>
    simp [copyIndexSpace, eachindexArray, eachindexLinearVector, axes1, tupleGet, one]

/-- Canonical getindex and setindex extensions own the scalar accesses;
the generic array dispatch and metadata operations are source methods. -/
def unaliasedCopyTrace {I E : Type} [DecidableEq I]
    (destLinear srcLinear : CopyLinearIndices) (destIndices srcIndices : List I)
    (readLinear : List E → I64 → E) (readCartesian : List E → I → E)
    (destStyle srcStyle : Bool) (values : List E) :
    StateT (List (Sum I64 I × E)) Result Unit :=
  copytoUnaliased
    (isemptyArray (fun values => pure (int values.length)))
    (fun _ => pure destLinear) (fun _ => pure srcLinear)
    (fun indices => pure indices.first) (fun indices => pure indices.first)
    (fun indices => pure indices.last)
    (fun i j => pure (i - j)) (fun i j => pure (i + j))
    (fun indices i => StateT.lift (copyLinearBounds indices i))
    id
    (fun a i => StateT.lift (getindexArray (fun _ => pure ())
      errorCanonicalGetindexOther (fun _ i => pure i)
      (fun _ => getindexLinearScalar (fun a i => pure (readLinear a i))) a i))
    (fun _ i value => sourceIndexedWrite () (.inl i) value)
    (fun i => pure (i - int 1)) (fun i => pure (i + int 1))
    (fun _ i value => sourceIndexedWrite () (.inl i) value)
    (fun a => StateT.lift (copyIndexSpace destStyle destIndices a))
    (fun a => StateT.lift (copyIndexSpace srcStyle srcIndices a))
    (fun is js => decide (is = js)) (fun is js => pure (is.zip js))
    (fun a i => StateT.lift (getindexArray (fun _ => pure ())
      errorCanonicalGetindexOther (fun _ i => pure i)
      (fun _ a i => pure (readCartesian a i)) a i))
    (fun a i => StateT.lift (getindexArray (fun _ => pure ())
      errorCanonicalGetindexOther (fun _ i => pure i)
      (fun _ a i => pure (readCartesian a i)) a i))
    (fun _ i value => sourceIndexedWrite () (.inr i) value)
    destStyle () srcStyle values

@[local simp] theorem copyStateLiftOk {S A : Type} (a : A) :
    (StateT.lift (Except.ok a) : StateT S Result A) = StateT.pure a := rfl

@[local simp] theorem copyStatePureBind {S A B : Type} (a : A)
    (next : A → StateT S Result B) :
    (StateT.pure a).bind next = next a := rfl

@[local simp] theorem copyStatePureBindM {S A B : Type} (a : A)
    (next : A → StateT S Result B) :
    ((StateT.pure a : StateT S Result A) >>= next) = next a := rfl

@[local simp] theorem copyStateLiftPure {S A : Type} (a : A) :
    (StateT.lift (pure a : Result A) : StateT S Result A) = StateT.pure a := rfl

@[local simp] theorem copyStateThrowBind {S A B : Type} (error : ArrayError)
    (next : A → StateT S Result B) :
    ((throw error : StateT S Result A) >>= next) =
      (throw error : StateT S Result B) := rfl

theorem copyStateIgnore {S A : Type} (action : StateT S Result A) (state : S) :
    (do let _ ← action; pure () : StateT S Result Unit).run state =
      (action.run state).map (fun result => ((), result.2)) := by
  cases equation : action state <;>
    simp [StateT.run, StateT.bind, StateT.pure, equation, Except.map]

theorem copyLinearForIn_eq {m : Type → Type} [Monad m] {A : Type}
    (indices : CopyLinearIndices) (initial : A)
    (step : I64 → A → m (ForInStep A)) :
    forIn indices initial step = forIn indices.indices initial step := rfl

@[local simp] theorem copyAppendSingleton {A : Type} (xs : List A) (x : A) (ys : List A) :
    (xs ++ [x]) ++ ys = xs ++ x :: ys := by
  induction xs <;> simp_all

theorem copyTraceLoop {K I E : Type} (keys : List K) (index : K → I)
    (value : K → E) (log : List (I × E)) :
    (do
      for key in keys do sourceIndexedWrite () (index key) (value key)
      pure () : StateT (List (I × E)) Result Unit).run log =
        .ok ((), log ++ keys.map (fun key => (index key, value key))) := by
  induction keys generalizing log with
  | nil => simp [List.forIn_nil, StateT.run, StateT.bind, StateT.pure]
  | cons key keys ih =>
    simpa [List.forIn_cons, sourceIndexedWrite, setindexArray,
      errorCanonicalSetindexOther, indexedWrite, StateT.run, StateT.bind,
      StateT.pure, StateT.lift, List.append_assoc] using
      ih (log ++ [(index key, value key)])

theorem copyCounterTrace {I E : Type} (values : List E) (previous : Int)
    (log : List (Sum I64 I × E)) :
    (forIn values (int previous) (fun value counter => do
      let counter := counter + int 1
      sourceIndexedWrite () (Sum.inl (β := I) counter) value
      pure (.yield counter))).run log =
        .ok (int (previous + values.length),
          log ++ ((copyPositions (previous + 1) values.length).map Sum.inl).zip values) := by
  induction values generalizing previous log with
  | nil => simp [List.forIn_nil, copyPositions, StateT.run, StateT.pure]
  | cons value values ih =>
    have tail := ih (previous + 1) (log ++ [(.inl (int (previous + 1)), value)])
    simp [List.forIn_cons, sourceIndexedWrite, setindexArray,
      errorCanonicalSetindexOther, indexedWrite, StateT.run, StateT.bind,
      StateT.pure, StateT.lift, copyPositions, vcatNativeAdd,
      Int.add_assoc, Int.add_left_comm, Int.add_comm] at tail ⊢
    exact tail

theorem copyCounterTraceWrites {I E : Type} (values : List E) (previous : Int)
    (log : List (Sum I64 I × E)) :
    (do
      let _ ← forIn values (int previous) (fun value counter => do
        let counter := counter + int 1
        sourceIndexedWrite () (Sum.inl (β := I) counter) value
        pure (.yield counter))
      pure () : StateT (List (Sum I64 I × E)) Result Unit).run log =
        .ok ((), log ++ ((copyPositions (previous + 1) values.length).map Sum.inl).zip values) := by
  rw [copyStateIgnore, copyCounterTrace]
  rfl

/-- The four index-style branches all perform exactly the ordered scalar
assignments. Invalid endpoint translations fail before the first write. -/
def UnaliasedCopyAssignments : Prop :=
  ∀ (I E : Type) [DecidableEq I]
    (destLinear srcLinear : CopyLinearIndices) (destIndices srcIndices : List I)
    (readLinear : List E → I64 → E) (readCartesian : List E → I → E)
    (destStyle srcStyle : Bool) (values : List E)
    (log : List (Sum I64 I × E)),
    values.length < 2 ^ 63 →
    let delta := destLinear.first - srcLinear.first
    let fits := destLinear.first.val ≤ (srcLinear.first + delta).val ∧
      (srcLinear.first + delta).val ≤ destLinear.last.val ∧
      destLinear.first.val ≤ (srcLinear.last + delta).val ∧
      (srcLinear.last + delta).val ≤ destLinear.last.val
    let assignments :=
      if destStyle then
        if srcStyle then srcLinear.indices.map
          (fun i => (Sum.inl (i + delta), readLinear values i))
        else ((copyPositions destLinear.first.val values.length).map Sum.inl).zip values
      else
        if destIndices = srcIndices then
          destIndices.map (fun i => (Sum.inr i, readCartesian values i))
        else (destIndices.zip srcIndices).map
          (fun pair => (Sum.inr pair.1, readCartesian values pair.2))
    (unaliasedCopyTrace destLinear srcLinear destIndices srcIndices
      readLinear readCartesian destStyle srcStyle values).run log =
      if values = [] then .ok ((), log)
      else if fits then .ok ((), log ++ assignments)
      else .error (.julia .boundsError)

set_option maxRecDepth 4096 in
theorem unaliasedCopyAssignments_proven : UnaliasedCopyAssignments := by
  intro I E _ destLinear srcLinear destIndices srcIndices readLinear readCartesian
    destStyle srcStyle values log fit
  have count := nativeArrayCountValue values.length fit
  have bounds (indices : CopyLinearIndices) (i : I64) :
      copyLinearBounds indices i =
        .ok (decide (indices.first.val ≤ i.val ∧ i.val ≤ indices.last.val)) := by
    have one : (int 1).val = 1 := rfl
    simp [copyLinearBounds, checkboundsOne, eachindexLinearVector, axes1, tupleGet,
      sourceAxisCheck, checkindexReal, Bool.decide_and, one]
  by_cases empty : values = []
  · simp [unaliasedCopyTrace, copytoUnaliased, isemptyArray, empty]
    rfl
  · have nonzero : values.length ≠ 0 := by simpa using empty
    by_cases valid :
      destLinear.first.val ≤ (srcLinear.first + (destLinear.first - srcLinear.first)).val ∧
      (srcLinear.first + (destLinear.first - srcLinear.first)).val ≤ destLinear.last.val ∧
      destLinear.first.val ≤ (srcLinear.last + (destLinear.first - srcLinear.first)).val ∧
      (srcLinear.last + (destLinear.first - srcLinear.first)).val ≤ destLinear.last.val
    · have noHighFirst :
          ¬ destLinear.last.val < (srcLinear.first + (destLinear.first - srcLinear.first)).val := by omega
      have noHighLast :
          ¬ destLinear.last.val < (srcLinear.last + (destLinear.first - srcLinear.first)).val := by omega
      dsimp at valid noHighFirst noHighLast
      cases destStyle <;> cases srcStyle
      · by_cases same : destIndices = srcIndices
        · simpa [unaliasedCopyTrace, copytoUnaliased, isemptyArray, count, nonzero,
            bounds, eachindexArray, getindexArray, errorCanonicalGetindexOther,
            StateT.run, ← Bool.decide_and, and_assoc, valid, noHighFirst, noHighLast, empty, same] using
            copyTraceLoop srcIndices Sum.inr (readCartesian values) log
        · simpa [unaliasedCopyTrace, copytoUnaliased, isemptyArray, count, nonzero,
            bounds, eachindexArray, getindexArray, errorCanonicalGetindexOther,
            StateT.run, ← Bool.decide_and, and_assoc, valid, noHighFirst, noHighLast, empty, same] using
            copyTraceLoop (destIndices.zip srcIndices) (fun pair => Sum.inr pair.1)
              (fun pair => readCartesian values pair.2) log
      · by_cases same : destIndices = srcIndices
        · simpa [unaliasedCopyTrace, copytoUnaliased, isemptyArray, count, nonzero,
            bounds, eachindexArray, getindexArray, errorCanonicalGetindexOther,
            StateT.run, ← Bool.decide_and, and_assoc, valid, noHighFirst, noHighLast, empty, same] using
            copyTraceLoop srcIndices Sum.inr (readCartesian values) log
        · simpa [unaliasedCopyTrace, copytoUnaliased, isemptyArray, count, nonzero,
            bounds, eachindexArray, getindexArray, errorCanonicalGetindexOther,
            StateT.run, ← Bool.decide_and, and_assoc, valid, noHighFirst, noHighLast, empty, same] using
            copyTraceLoop (destIndices.zip srcIndices) (fun pair => Sum.inr pair.1)
              (fun pair => readCartesian values pair.2) log
      · have firstValue : int destLinear.first.val = destLinear.first := by
          apply Subtype.ext
          exact wrapInt_of_inRange .i64 _ destLinear.first.property
        have previous : destLinear.first - int 1 = int (destLinear.first.val - 1) := by
          calc
            _ = int destLinear.first.val - int 1 := by rw [firstValue]
            _ = _ := vcatNativeSub _ _
        simpa [unaliasedCopyTrace, copytoUnaliased, isemptyArray, count, nonzero,
          bounds, eachindexArray, getindexArray, errorCanonicalGetindexOther,
          StateT.run, ← Bool.decide_and, and_assoc, valid, noHighFirst, noHighLast, empty, previous] using
          copyCounterTraceWrites (I := I) values (destLinear.first.val - 1) log
      · simpa [unaliasedCopyTrace, copytoUnaliased, isemptyArray, count, nonzero,
          bounds, eachindexArray, getindexArray, errorCanonicalGetindexOther,
          getindexLinearScalar, StateT.run, ← Bool.decide_and, and_assoc,
          valid, noHighFirst, noHighLast, empty, copyLinearForIn_eq] using
          copyTraceLoop srcLinear.indices
            (fun i => Sum.inl (β := I) (i + (destLinear.first - srcLinear.first)))
            (readLinear values) log
    · have failed :
          (destLinear.first.val ≤ (srcLinear.first + (destLinear.first - srcLinear.first)).val →
            destLinear.last.val < (srcLinear.first + (destLinear.first - srcLinear.first)).val) ∨
          (destLinear.first.val ≤ (srcLinear.last + (destLinear.first - srcLinear.first)).val →
            destLinear.last.val < (srcLinear.last + (destLinear.first - srcLinear.first)).val) := by omega
      dsimp at valid failed
      simp [unaliasedCopyTrace, copytoUnaliased, isemptyArray, count, nonzero,
        bounds, StateT.run, ← Bool.decide_and, and_assoc, valid, failed, empty]
      rfl


theorem copyMapPairs {K I E : Type} (keys : List K) (index : K → I) (value : K → E) :
    keys.map (fun key => (index key, value key)) =
      (keys.map index).zip (keys.map value) := by
  induction keys <;> simp_all

theorem copyZipPairs {I E : Type} (is js : List I) (read : I → E)
    (fit : js.length ≤ is.length) :
    (is.zip js).map (fun pair => (Sum.inr (α := I64) pair.1, read pair.2)) =
      ((is.take js.length).map Sum.inr).zip (js.map read) := by
  induction is generalizing js with
  | nil =>
    have empty : js = [] := List.length_eq_zero_iff.mp (by simpa using fit)
    simp [empty]
  | cons i is ih =>
    cases js with
    | nil => simp
    | cons j js => simpa using ih js (by simpa using fit)

/-- With lawful scalar reads and ordered index spaces, every index-style
combination overwrites exactly the destination prefix with all source values.
The write trace contains no assignment outside that prefix. -/
def UnaliasedCopyPreservesElements : Prop :=
  ∀ (I E : Type) [DecidableEq I]
    (destLinear srcLinear : CopyLinearIndices) (destIndices srcIndices : List I)
    (readLinear : List E → I64 → E) (readCartesian : List E → I → E)
    (destStyle srcStyle : Bool) (values : List E)
    (log : List (Sum I64 I × E)),
    values.length < 2 ^ 63 →
    let delta := destLinear.first - srcLinear.first
    destLinear.first.val ≤ (srcLinear.first + delta).val →
    (srcLinear.first + delta).val ≤ destLinear.last.val →
    destLinear.first.val ≤ (srcLinear.last + delta).val →
    (srcLinear.last + delta).val ≤ destLinear.last.val →
    srcLinear.indices.map (fun i => i + delta) =
      copyPositions destLinear.first.val values.length →
    srcLinear.indices.map (readLinear values) = values →
    srcIndices.map (readCartesian values) = values →
    srcIndices.length ≤ destIndices.length →
    (unaliasedCopyTrace destLinear srcLinear destIndices srcIndices
      readLinear readCartesian destStyle srcStyle values).run log =
      .ok ((), log ++
        ((if destStyle then (copyPositions destLinear.first.val values.length).map Sum.inl
          else (destIndices.take values.length).map Sum.inr).zip values))

set_option maxRecDepth 4096 in
theorem unaliasedCopyPreservesElements_proven : UnaliasedCopyPreservesElements := by
  intro I E _ destLinear srcLinear destIndices srcIndices readLinear readCartesian
    destStyle srcStyle values log native
  dsimp only
  intro lo lo' hi hi' positions linearRead cartesianRead fit
  have reference := unaliasedCopyAssignments_proven I E destLinear srcLinear
    destIndices srcIndices readLinear readCartesian destStyle srcStyle values log native
  have count : srcIndices.length = values.length := by
    have := congrArg List.length cartesianRead
    simpa using this
  by_cases empty : values = []
  · simpa [empty] using reference
  · simp only [empty, ↓reduceIte, lo, lo', hi, hi', and_self] at reference
    rw [reference]
    apply congrArg (fun writes =>
      (Except.ok ((), log ++ writes) : Result (Unit × List (Sum I64 I × E))))
    cases destStyle <;> cases srcStyle
    · by_cases same : destIndices = srcIndices
      · simp only [Bool.false_eq_true, ↓reduceIte, same]
        rw [copyMapPairs, cartesianRead]
        simp [← count]
      · simp only [Bool.false_eq_true, ↓reduceIte, same]
        rw [copyZipPairs _ _ _ fit, cartesianRead, count]
    · by_cases same : destIndices = srcIndices
      · simp only [Bool.false_eq_true, ↓reduceIte, same]
        rw [copyMapPairs, cartesianRead]
        simp [← count]
      · simp only [Bool.false_eq_true, ↓reduceIte, same]
        rw [copyZipPairs _ _ _ fit, cartesianRead, count]
    · rfl
    · simp only [↓reduceIte]
      rw [copyMapPairs, linearRead]
      have shifted := congrArg (List.map (Sum.inl (β := I))) positions
      rw [List.map_map] at shifted
      change srcLinear.indices.map
        (fun i => Sum.inl (β := I) (i + (destLinear.first - srcLinear.first))) =
        (copyPositions destLinear.first.val values.length).map Sum.inl at shifted
      exact congrArg (fun is => is.zip values) shifted

def UnaliasedCopySpecification : Prop :=
  UnaliasedCopyAssignments ∧ UnaliasedCopyPreservesElements

theorem unaliasedCopySpecification_proven : UnaliasedCopySpecification :=
  ⟨unaliasedCopyAssignments_proven, unaliasedCopyPreservesElements_proven⟩

/-- The foreign dense-array copy preserves contents and the assignment log.
The alias decision itself runs the source data-identity and disjointness methods. -/
def copyTraceUnalias {I E : Type}
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 I × E)) Result (List E)) :
    Unit → List E → StateT (List (Sum I64 I × E)) Result (List E) :=
  unaliasArray
    (mightaliasArray (fun _ => pure false) (fun _ => pure false)
      (isemptyArray (fun _ => pure (int 1)))
      (isemptyArray (fun values => pure (int values.length)))
      (fun dest => pure (dataidsArray (fun _ => destinationId) dest))
      (dataidsDense id id (dataidsMemory sourcePointer (fun ptr => pure ptr)))
      (fun ds ss => pure (disjointCalls ds ss)))
    (unaliascopyDense copy)

set_option maxRecDepth 4096 in
theorem copyTraceUnalias_contents {I E : Type}
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 I × E)) Result (List E))
    (law : ∀ values log, (copy values).run log = .ok (values, log))
    (values : List E) (log : List (Sum I64 I × E)) :
    (copyTraceUnalias destinationId sourcePointer copy () values).run log =
      .ok (values, log) := by
  have copyPure : copy = fun values => pure values := by
    funext values log
    exact law values log
  rw [copyPure]
  simp only [copyTraceUnalias, unaliasArray, mightaliasArray, isemptyArray,
    dataidsArray, dataidsDense, dataidsMemory, unaliascopyDense, pure_bind,
    Bool.false_eq_true, ↓reduceIte, id_eq]
  split <;> (try simp only [pure_bind])
  · rfl
  · split <;> (try simp only [pure_bind])
    · rfl
    · split <;> rfl

def arrayCopyTrace {I E : Type} [DecidableEq I]
    (destLinear srcLinear : CopyLinearIndices) (destIndices srcIndices : List I)
    (readLinear : List E → I64 → E) (readCartesian : List E → I → E)
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 I × E)) Result (List E))
    (explicitStyles destStyle srcStyle : Bool) (values : List E) :
    StateT (List (Sum I64 I × E)) Result Unit :=
  let empty := isemptyArray (fun values => pure (int values.length))
  let alias := copyTraceUnalias destinationId sourcePointer copy
  let assign := fun ds (_ : Unit) ss values =>
    unaliasedCopyTrace destLinear srcLinear destIndices srcIndices
      readLinear readCartesian ds ss values
  if explicitStyles then
    copytoStyles empty alias assign destStyle () srcStyle values
  else
    copytoArray empty (fun _ => false) (fun _ _ => pure ()) alias
      (fun _ => pure destStyle) (fun _ => pure srcStyle) assign () values

/-- Both public array-copy entry points obey the complete scalar-assignment
contract, including the checked failure before any destination assignment. -/
def ArrayCopyAssignments : Prop :=
  ∀ (I E : Type) [DecidableEq I]
    (destLinear srcLinear : CopyLinearIndices) (destIndices srcIndices : List I)
    (readLinear : List E → I64 → E) (readCartesian : List E → I → E)
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 I × E)) Result (List E)),
    (∀ values log, (copy values).run log = .ok (values, log)) →
    ∀ (explicitStyles destStyle srcStyle : Bool) (values : List E)
      (log : List (Sum I64 I × E)),
    (arrayCopyTrace destLinear srcLinear destIndices srcIndices
      readLinear readCartesian destinationId sourcePointer copy
      explicitStyles destStyle srcStyle values).run log =
    (unaliasedCopyTrace destLinear srcLinear destIndices srcIndices
      readLinear readCartesian destStyle srcStyle values).run log

set_option maxRecDepth 4096 in
theorem arrayCopyAssignments_proven : ArrayCopyAssignments := by
  intro I E _ destLinear srcLinear destIndices srcIndices readLinear readCartesian
    destinationId sourcePointer copy law explicitStyles destStyle srcStyle values log
  have aliasPure : copyTraceUnalias destinationId sourcePointer copy =
      fun _ values => pure values := by
    funext destination values log
    cases destination
    exact copyTraceUnalias_contents destinationId sourcePointer copy law values log
  cases explicitStyles <;>
    simp only [arrayCopyTrace, Bool.false_eq_true, ↓reduceIte, copytoArray,
      copytoStyles, aliasPure, isemptyArray, pure_bind]
  all_goals
    split
    · simp only [unaliasedCopyTrace, copytoUnaliased, isemptyArray, pure_bind, *]
      rfl
    · rfl

/-- Public array copying preserves source order in the destination prefix. -/
def ArrayCopyPreservesElements : Prop :=
  ∀ (I E : Type) [DecidableEq I]
    (destLinear srcLinear : CopyLinearIndices) (destIndices srcIndices : List I)
    (readLinear : List E → I64 → E) (readCartesian : List E → I → E)
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 I × E)) Result (List E)),
    (∀ values log, (copy values).run log = .ok (values, log)) →
    ∀ (explicitStyles destStyle srcStyle : Bool) (values : List E)
      (log : List (Sum I64 I × E)),
    values.length < 2 ^ 63 →
    let delta := destLinear.first - srcLinear.first
    destLinear.first.val ≤ (srcLinear.first + delta).val →
    (srcLinear.first + delta).val ≤ destLinear.last.val →
    destLinear.first.val ≤ (srcLinear.last + delta).val →
    (srcLinear.last + delta).val ≤ destLinear.last.val →
    srcLinear.indices.map (fun i => i + delta) =
      copyPositions destLinear.first.val values.length →
    srcLinear.indices.map (readLinear values) = values →
    srcIndices.map (readCartesian values) = values →
    srcIndices.length ≤ destIndices.length →
    (arrayCopyTrace destLinear srcLinear destIndices srcIndices
      readLinear readCartesian destinationId sourcePointer copy
      explicitStyles destStyle srcStyle values).run log =
      .ok ((), log ++
        ((if destStyle then (copyPositions destLinear.first.val values.length).map Sum.inl
          else (destIndices.take values.length).map Sum.inr).zip values))

theorem arrayCopyPreservesElements_proven : ArrayCopyPreservesElements := by
  intro I E _ destLinear srcLinear destIndices srcIndices readLinear readCartesian
    destinationId sourcePointer copy law explicitStyles destStyle srcStyle values log hlen
  dsimp only
  intro hfirstlo hfirsthi hlastlo hlasthi hpositions hlinear hcartesian hcount
  rw [arrayCopyAssignments_proven I E destLinear srcLinear destIndices srcIndices
    readLinear readCartesian destinationId sourcePointer copy law
    explicitStyles destStyle srcStyle values log]
  exact unaliasedCopyPreservesElements_proven I E destLinear srcLinear
    destIndices srcIndices readLinear readCartesian destStyle srcStyle values log
    hlen hfirstlo hfirsthi hlastlo hlasthi hpositions hlinear hcartesian hcount

def countedArrayCopyTrace {E : Type}
    (destIndices srcIndices : CopyLinearIndices)
    (read : List E → I64 → E)
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 Unit × E)) Result (List E))
    (dstart sstart n : I64) (values : List E) :
    StateT (List (Sum I64 Unit × E)) Result Unit :=
  copytoArrayN
    (fun count => JuliaLean.base.int.eqSame count (int 0))
    (fun count => JuliaLean.base.int.ltSame count (int 0))
    (fun _ => pure destIndices) (fun _ => pure srcIndices)
    (fun indices index => StateT.lift (copyLinearBounds indices index))
    (fun indices index => StateT.lift (copyLinearBounds indices index))
    (fun indices => pure indices.last)
    (fun stop start => pure (stop - start)) (fun difference => pure (difference + int 1))
    (fun count span => pure (JuliaLean.base.int.leSame count span))
    (fun stop start => pure (stop - start)) (fun difference => pure (difference + int 1))
    (fun count span => pure (JuliaLean.base.int.leSame count span))
    (fun index => StateT.lift (liftJulia (JuliaLean.base.int.convert .i64 index)))
    (fun index => StateT.lift (liftJulia (JuliaLean.base.int.convert .i64 index)))
    (fun count => StateT.lift (liftJulia (JuliaLean.base.int.convert .i64 count)))
    (copyTraceUnalias destinationId sourcePointer copy)
    (fun a index => StateT.lift (getindexArray (fun _ => pure ())
      errorCanonicalGetindexOther (fun _ index => pure index)
      (fun _ => getindexLinearScalar (fun a index => pure (read a index))) a index))
    (fun _ index value => sourceIndexedWrite () (.inl index) value)
    () dstart values sstart n

def CountedArrayCopyContents : Prop :=
  ∀ (E : Type) (destIndices srcIndices : CopyLinearIndices)
    (read : List E → I64 → E)
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 Unit × E)) Result (List E))
    (law : ∀ values log, (copy values).run log = .ok (values, log))
    (dstart sstart n : I64) (values : List E) (log : List (Sum I64 Unit × E)),
    0 < n.val →
    copyLinearBounds destIndices dstart = .ok true →
    n.val ≤ (destIndices.last - dstart + int 1).val →
    copyLinearBounds srcIndices sstart = .ok true →
    n.val ≤ (srcIndices.last - sstart + int 1).val →
    (countedArrayCopyTrace destIndices srcIndices read destinationId sourcePointer
      copy dstart sstart n values).run log =
      .ok ((), log ++
        ((List.range n.val.toNat).map (fun (j : Nat) => Sum.inl (β := Unit) (dstart + int j))).zip
          ((List.range n.val.toNat).map (fun (j : Nat) => read values (sstart + int j))))

theorem countedArrayCopyContents_proven : CountedArrayCopyContents := by
  intro E destIndices srcIndices read destinationId sourcePointer copy law
    dstart sstart n values log positive destBound destSpan srcBound srcSpan
  have zero : (int 0).val = 0 := rfl
  have one : (int 1).val = 1 := rfl
  have nonzero : n.val ≠ 0 := by omega
  have nonnegative : ¬ n.val < 0 := by omega
  have countRange : ((n - int 1).val + 1).toNat = n.val.toNat := by
    change (wrapInt .i64 (n.val - (int 1).val) + 1).toNat = _
    rw [one, wrapInt_of_inRange .i64 _ (by
      have range := n.property
      have minimum : IntTy.i64.min ≤ 0 := by decide
      constructor <;> omega)]
    congr 1
    omega
  have aliasPure : copyTraceUnalias destinationId sourcePointer copy =
      fun _ values => pure values := by
    funext destination values log
    cases destination
    exact copyTraceUnalias_contents destinationId sourcePointer copy law values log
  simp only [countedArrayCopyTrace, copytoArrayN,
    JuliaLean.Proofs.base.int.eqSame_eq, JuliaLean.Proofs.base.int.ltSame_eq,
    JuliaLean.Proofs.base.int.leSame_eq, zero, nonzero, nonnegative,
    decide_false, Bool.false_eq_true, ↓reduceIte, pure_bind, destBound, srcBound,
    copyStateLiftOk, copyStatePureBindM, destSpan, srcSpan, decide_true, Bool.not_true,
    nativeCopyCast_same, aliasPure, getindexArray, errorCanonicalGetindexOther,
    getindexLinearScalar, pure_bind, copyStateLiftPure, countRange]
  rw [copyTraceLoop, copyMapPairs]

theorem copyLinearBounds_formula (indices : CopyLinearIndices) (i : I64) :
    copyLinearBounds indices i =
      .ok (decide (indices.first.val ≤ i.val ∧ i.val ≤ indices.last.val)) := by
  have one : (int 1).val = 1 := rfl
  simp [copyLinearBounds, checkboundsOne, eachindexLinearVector, axes1, tupleGet,
    sourceAxisCheck, checkindexReal, Bool.decide_and, one]

def ArrayCopyFromRejectsInvalidStart : Prop :=
  ∀ (D S : Type) (indices : CopyLinearIndices)
    (copy : D → I64 → S → I64 → I64 → Result D)
    (dest : D) (dstart : I64) (src : S) (sstart : I64),
    (sstart.val < indices.first.val ∨ indices.last.val < sstart.val) →
    copytoArrayFrom (fun _ => pure indices) copyLinearBounds
      (fun indices => pure indices.last) (fun stop start => pure (stop - start))
      (fun difference => pure (difference + int 1)) copy dest dstart src sstart =
      .error (.julia .boundsError)

theorem arrayCopyFromRejectsInvalidStart_proven : ArrayCopyFromRejectsInvalidStart := by
  intro D S indices copy dest dstart src sstart invalid
  have outside : ¬ (indices.first.val ≤ sstart.val ∧ sstart.val ≤ indices.last.val) := by omega
  simp [copytoArrayFrom, copyLinearBounds_formula, outside]
  rfl

/-! Nothing to promise: copy@1154: this overload forwards its argument unchanged
to the mutable-copy dispatch; it introduces no indexing or allocation behavior. -/

/-! Nothing to promise: copyto!@1125: this overload forwards the source's
first linear index and length to counted copying; its element and bounds
guarantees are the counted operation's guarantees. -/

/-! Nothing to promise: _typed_hvncat@2492: the empty shape overload forwards
the type and elements to _typed_hvncat with dimension zero. -/

/-! Nothing to promise: _typed_hvncat@2493: the numeric empty shape overload
forwards the type and elements to _typed_hvncat with dimension zero. -/

/-! Nothing to promise: _typed_hvncat@2498: the singleton shape overload forwards
its sole dimension with column-first order to _typed_hvncat. -/

/-! Nothing to promise: _typed_hvncat@2499: the numeric singleton shape overload
forwards its sole dimension with column-first order to _typed_hvncat. -/

/-! Nothing to promise: stack@2996: this overload forwards the mapped generator
to stack with the requested dimension. Generator evaluation belongs to iteration. -/

/-! Nothing to promise: stack@2997: this overload zips the input iterators and
forwards their mapped generator to stack with the requested dimension. -/

/-! Nothing to promise: _stack@3001: the unknown-size overload collects its
iterator and forwards that collection to the known-size stack dispatch. -/

/-! Nothing to promise: mapany@3494: this overload collects the mapped generator
with Any element type. It introduces no independent indexing behavior. -/

/-! Nothing to promise: map@3521: this iterator overload collects the mapped
generator. Evaluation and termination are the iterator's behavior. -/

/-! Nothing to promise:
strides@577: declares the generic function `strides` without defining any method, so it has no behaviour of its own.
copyto!@939: sets compiler method-table metadata (`max_methods`) for `copyto!`; it defines no callable method.
getindex@1293: sets the compiler constant-propagation heuristic for `getindex`; it defines no callable method.
setindex!@1294: sets the compiler constant-propagation heuristic for `setindex!`; it defines no callable method.
unsetindex!@1518: declares the generic function `unsetindex!` without defining any method.
parent@1546: declares the generic function `parent` without defining any method; its fallback method at line 1548 is modelled separately.
-/

private theorem mutableCopy_pureSimilar {S A B : Type}
    (copy : B → A → StateT S Result B) (destination : B) (source : A) :
    copyMutableArray (fun _ => pure destination) copy source = copy destination source := by
  simp only [copyMutableArray, pure_bind]

private theorem oneMatrix_nonsquare {A B E Ax : Type} [ForIn Result Ax I64]
    (rows cols : Ax) (size : Ax → I64) (zero : E → Result E)
    (require : A → Result Unit) (similar : A → Result B)
    (fill : B → E → Result Unit) (set : B → I64 → I64 → E → Result Unit)
    (unit : E) (mat : A) (h : size rows ≠ size cols) :
    oneMatrix (fun _ => pure (rows, cols)) (fun axis => pure (size axis))
      zero require similar fill set unit mat =
      .error (.dimensionMismatch "multiplicative identity defined only for square matrices") := by
  simp only [oneMatrix, pure_bind]
  rw [if_pos (bne_iff_ne.mpr h)]
  rfl

def MutableArrayCopyContents : Prop :=
  ∀ (I E : Type) [DecidableEq I]
    (destLinear srcLinear : CopyLinearIndices) (destIndices srcIndices : List I)
    (readLinear : List E → I64 → E) (readCartesian : List E → I → E)
    (destinationId : JInt .u64) (sourcePointer : List E → JInt .u64)
    (copy : List E → StateT (List (Sum I64 I × E)) Result (List E)),
    (∀ values log, (copy values).run log = .ok (values, log)) →
    ∀ (destStyle srcStyle : Bool) (values : List E) (log : List (Sum I64 I × E)),
    values.length < 2 ^ 63 →
    let delta := destLinear.first - srcLinear.first
    destLinear.first.val ≤ (srcLinear.first + delta).val →
    (srcLinear.first + delta).val ≤ destLinear.last.val →
    destLinear.first.val ≤ (srcLinear.last + delta).val →
    (srcLinear.last + delta).val ≤ destLinear.last.val →
    srcLinear.indices.map (fun i => i + delta) =
      copyPositions destLinear.first.val values.length →
    srcLinear.indices.map (readLinear values) = values →
    srcIndices.map (readCartesian values) = values →
    srcIndices.length ≤ destIndices.length →
    (copyMutableArray (fun _ => pure ()) (fun _ source => do
      arrayCopyTrace destLinear srcLinear destIndices srcIndices
        readLinear readCartesian destinationId sourcePointer copy
        false destStyle srcStyle source
      pure ()) values).run log =
      .ok ((), log ++
        ((if destStyle then (copyPositions destLinear.first.val values.length).map Sum.inl
          else (destIndices.take values.length).map Sum.inr).zip values))

set_option maxRecDepth 100000 in
theorem mutableArrayCopyContents_proven : MutableArrayCopyContents := by
  intro I E _ destLinear srcLinear destIndices srcIndices readLinear readCartesian
    destinationId sourcePointer copy law destStyle srcStyle values log hlen
  dsimp only
  intro hfirstlo hfirsthi hlastlo hlasthi hpositions hlinear hcartesian hcount
  have contents := arrayCopyPreservesElements_proven I E destLinear srcLinear
    destIndices srcIndices readLinear readCartesian destinationId sourcePointer copy law
    false destStyle srcStyle values log hlen
    hfirstlo hfirsthi hlastlo hlasthi hpositions hlinear hcartesian hcount
  rw [mutableCopy_pureSimilar]
  rw [copyStateIgnore, contents]
  rfl

def OneMatrixRejectsNonsquare : Prop :=
  ∀ (A B E : Type) (rows cols : List I64)
    (zero : E → Result E)
    (similar : A → Result B) (fill : B → E → Result Unit)
    (set : B → I64 → I64 → E → Result Unit) (unit : E) (mat : A),
    int rows.length ≠ int cols.length →
    oneMatrix (fun _ => pure (rows, cols)) (fun axis => pure (int axis.length))
      zero (fun a => do
        let _ ← requireOneBased
          (hasOffset (fun _ => pure [rows, cols])
            (fun axis => pure (axis.headD (int 1))) pure) a
        pure ()) similar fill set unit mat =
      .error (.dimensionMismatch "multiplicative identity defined only for square matrices")

set_option maxRecDepth 100000 in
theorem oneMatrixRejectsNonsquare_proven : OneMatrixRejectsNonsquare := by
  intro A B E rows cols zero similar fill set unit mat nonsquare
  exact oneMatrix_nonsquare rows cols (fun axis => int axis.length) zero
    (fun a => do
      let _ ← requireOneBased
        (hasOffset (fun _ => pure [rows, cols])
          (fun axis => pure (axis.headD (int 1))) pure) a
      pure ()) similar fill set unit mat nonsquare

def blockCopySource {D S E : Type}
    (checkDest : D → List I64 → List I64 → Result Unit)
    (checkSrc : S → List I64 → List I64 → Result Unit)
    (destLength : D → Result I64) (srcLength : S → Result I64)
    (destPointer : D → JInt .u64)
    (srcPointer : S → JInt .u64) (copy : S → Result S)
    (first step : List I64 → Result I64)
    (read : S → (Fin 2 → I64) → Result E)
    (write : D → E → (Fin 2 → I64) → Result Unit)
    (dest : D) (irDest jrDest : List I64) (src : S) (irSrc jrSrc : List I64) :
    Result D :=
  copytoBlock (fun axis => pure (int axis.length)) checkDest checkSrc
    (unaliasArray
      (mightaliasArray (fun _ => pure false) (fun _ => pure false)
        (isemptyArray destLength) (isemptyArray srcLength)
        (fun a => pure (dataidsArray destPointer a))
        (fun a => pure (dataidsArray srcPointer a))
        (fun ds ss => pure (disjointCalls ds ss)))
      (unaliascopyDense copy))
    first step
    (fun a i j => getindexCartesianExact read a (fun k => if k.val = 0 then i else j))
    (fun a i j value =>
      setindexCartesianExact write a value (fun k => if k.val = 0 then i else j))
    dest irDest jrDest src irSrc jrSrc

def BlockCopyRejectsSizeMismatch : Prop :=
  ∀ (D S E : Type)
    (checkDest : D → List I64 → List I64 → Result Unit)
    (checkSrc : S → List I64 → List I64 → Result Unit)
    (destLength : D → Result I64) (srcLength : S → Result I64)
    (destPointer : D → JInt .u64)
    (srcPointer : S → JInt .u64) (copy : S → Result S)
    (first step : List I64 → Result I64)
    (read : S → (Fin 2 → I64) → Result E)
    (write : D → E → (Fin 2 → I64) → Result Unit)
    (dest : D) (irDest jrDest : List I64) (src : S) (irSrc jrSrc : List I64),
    int irDest.length ≠ int irSrc.length ∨ int jrDest.length ≠ int jrSrc.length →
    blockCopySource checkDest checkSrc destLength srcLength destPointer srcPointer copy
      first step read write dest irDest jrDest src irSrc jrSrc =
      .error (.julia (.argumentError "source and destination must have same size"))

set_option maxRecDepth 100000 in
theorem blockCopyRejectsSizeMismatch_proven : BlockCopyRejectsSizeMismatch := by
  intro D S E checkDest checkSrc destLength srcLength destPointer srcPointer copy
    first step read write dest irDest jrDest src irSrc jrSrc mismatch
  unfold blockCopySource copytoBlock
  simp only [pure_bind]
  by_cases rows : int irDest.length = int irSrc.length
  · have cols : int jrDest.length ≠ int jrSrc.length := mismatch.resolve_left (fun h => h rows)
    simp only [rows, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [if_pos (bne_iff_ne.mpr cols)]
    rfl
  · rw [if_pos (bne_iff_ne.mpr rows)]
    rfl

def hvncatOneDimNumbersSource {Ty E F : Type}
    (vector : Ty → List E → Result (Ty × List F))
    (reshape : Ty × List F → List I64 → Result (TypedRankArray Ty F))
    (t : Ty) (ds : I64) (rowFirst : Bool) (xs : List E) :
    Result (TypedRankArray Ty F) :=
  typedHvncatOneDim (fun xs => pure (int xs.length))
    (fun t n xs =>
      typedHvncatNumbersVal (fun n : Int => pure (decide (n < 0)))
        (fun n => pure (n - 1)) (fun n => pure (List.replicate n.toNat (int 1)))
        (fun xs => pure (int xs.length)) vector reshape t n.val xs)
    t ds rowFirst xs

def HvncatOneDimNumbersContents : Prop :=
  ∀ (Ty E F : Type) (convert : Ty → E → Result F)
    (vector : Ty → List E → Result (Ty × List F))
    (reshape : Ty × List F → List I64 → Result (TypedRankArray Ty F)),
    (∀ t xs ys, xs.mapM (convert t) = .ok ys → vector t xs = .ok (t, ys)) →
    (∀ values shape, ((shape.map fun d => d.val.toNat).prod) = values.2.length →
      reshape values shape = .ok ⟨values.1, shape, values.2⟩) →
    ∀ t ds rowFirst xs g,
      0 < ds.val → int xs.length = ds → xs.length ≤ 9223372036854775807 →
      (∀ x ∈ xs, convert t x = .ok (g x)) →
      hvncatOneDimNumbersSource vector reshape t ds rowFirst xs =
        .ok ⟨t, (if rowFirst then [int 1, ds] else [ds]), xs.map g⟩

theorem hvncatOneDimNumbersContents_proven : HvncatOneDimNumbersContents := by
  intro Ty E F convert vector reshape hv hr t ds rowFirst xs g positive count fit hc
  have nonempty : xs ≠ [] := by
    intro empty
    subst xs
    have : (int 0).val = ds.val := congrArg Subtype.val count
    change 0 = ds.val at this
    omega
  have notzero : ¬ ds.val ≤ 0 := by omega
  have rankOne := (hvnNumbersRankSpec_proven Ty E F convert vector reshape hv hr
    t 1 xs g).2 (by omega) nonempty fit hc
  have rankTwo := (hvnNumbersRankSpec_proven Ty E F convert vector reshape hv hr
    t 2 xs g).2 (by omega) nonempty fit hc
  have oneValue : (int 1).val = 1 := by decide
  have twoValue : (int 2).val = 2 := by decide
  have oneShape : List.replicate ((1 : Int).toNat - 1) (int 1) = [] := rfl
  have twoShape : List.replicate ((2 : Int).toNat - 1) (int 1) = [int 1] := rfl
  cases rowFirst
  · simpa only [hvncatOneDimNumbersSource, typedHvncatOneDim, notzero, count,
      pure_bind, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true, oneValue,
      oneShape, List.nil_append] using rankOne
  · simpa only [hvncatOneDimNumbersSource, typedHvncatOneDim, notzero, count,
      pure_bind, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true, twoValue,
      twoShape, List.cons_append, List.nil_append] using rankTwo

set_option linter.unusedSimpArgs false

/-! ## Vector growth: push!, rest -/

theorem native_int_val (x : I64) : int x.val = x := by
  apply Subtype.ext
  change wrapInt .i64 x.val = x.val
  exact wrapInt_of_inRange .i64 x.val x.property

theorem native_val_int (z : Int) (lo : -9223372036854775808 ≤ z)
    (hi : z ≤ 9223372036854775807) : (int z).val = z := by
  change wrapInt .i64 z = z
  apply wrapInt_of_inRange
  constructor <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

/-- Running a bind whose first action is known to succeed. Stepping through a
source `do` block with these lemmas keeps each rewrite small. -/
theorem vrun_bind {σ α β : Type} {x : StateT σ Result α} {f : α → StateT σ Result β}
    {s s' : σ} {a : α} (h : x s = .ok (a, s')) : (x >>= f) s = f a s' := by
  show StateT.bind x f s = f a s'
  unfold StateT.bind
  rw [h]
  rfl

theorem vrun_pure {σ α : Type} (a : α) (s : σ) :
    (pure a : StateT σ Result α) s = .ok (a, s) := rfl

theorem vrun_pure_bind {σ α β : Type} (a : α) (f : α → StateT σ Result β) (s : σ) :
    (pure a >>= f : StateT σ Result β) s = f a s := rfl

theorem vrun_lift {σ α : Type} {x : Result α} {a : α} (s : σ) (h : x = .ok a) :
    (StateT.lift x : StateT σ Result α) s = .ok (a, s) := by
  rw [h]
  rfl

/-- Observable state of a one-dimensional array: its first index and its
elements in linear order. -/
structure OffsetVector (E : Type) where
  first : I64
  values : List E

abbrev VectorRun (E : Type) := StateT (OffsetVector E) Result

def offsetVectorAxis {E : Type} (v : OffsetVector E) : I64 × I64 :=
  (v.first, v.first + int v.values.length - int 1)

/-- The foreign `length` interface: the number of stored elements. -/
def offsetVectorLength {E : Type} (_ : Unit) : VectorRun E I64 :=
  fun v => .ok (int v.values.length, v)

/-- Source `lastindex` through `eachindex(IndexLinear(), a)` and `axes1`; the
foreign `axes` interface reports the vector's current unit range. -/
def offsetVectorLastindex {E : Type} (a : Unit) : VectorRun E I64 := fun v =>
  (lastindexArray (eachindexLinearVector (axes1 (fun _ : Unit => pure [offsetVectorAxis v])))
    (fun axis => pure axis.2) a).map (·, v)

/-- Source `firstindex` through `eachindex(IndexLinear(), a)` and `axes1`. -/
def offsetVectorFirstindex {E : Type} (a : Unit) : VectorRun E I64 := fun v =>
  (firstindexArray (eachindexLinearVector (axes1 (fun _ : Unit => pure [offsetVectorAxis v])))
    (fun axis => pure axis.1) a).map (·, v)

/-- The foreign `resize!` implementation applied to the stored elements. -/
def offsetVectorResize {E : Type} (resize : List E → I64 → Result (List E))
    (_ : Unit) (n : I64) : VectorRun E Unit := fun v =>
  (resize v.values n).map fun ys => ((), { v with values := ys })

/-- The foreign scalar `setindex!` interface: checked assignment at a linear index. -/
def offsetVectorSet {E : Type} (_ : Unit) (i : I64) (x : E) : VectorRun E Unit := fun v =>
  if v.first.val ≤ i.val ∧ i.val < v.first.val + v.values.length then
    .ok ((), { v with values := v.values.set (i.val - v.first.val).toNat x })
  else .error (.julia .boundsError)

/-- The documented `resize!` contract: the requested length, keeping the
leading elements that survive. Newly exposed slots are unconstrained. -/
def ResizeKeepsPrefix {E : Type} (resize : List E → I64 → Result (List E)) : Prop :=
  ∀ xs n, 0 ≤ n.val → ∃ ys, resize xs n = .ok ys ∧ ys.length = n.val.toNat ∧
    ys.take xs.length = xs.take n.val.toNat

/-- Room for `extra` more elements with native lengths and indices. -/
def OffsetVector.Room {E : Type} (v : OffsetVector E) (extra : Nat) : Prop :=
  (v.values.length : Int) + extra ≤ 9223372036854775807 ∧
    v.first.val + v.values.length + extra ≤ 9223372036854775808

theorem offsetVectorAxis_last {E : Type} (v : OffsetVector E) :
    (offsetVectorAxis v).2 = int (v.first.val + v.values.length - 1) := by
  simp only [offsetVectorAxis]
  rw [← native_int_val v.first, vcatNativeAdd, vcatNativeSub]
  simp [native_int_val]

theorem offsetVectorLastindex_run {E : Type} (v : OffsetVector E) :
    (offsetVectorLastindex () : VectorRun E I64).run v =
      .ok (int (v.first.val + v.values.length - 1), v) := by
  have one : (int 1).val = 1 := rfl
  simp [offsetVectorLastindex, lastindexArray, eachindexLinearVector, axes1, tupleGet,
    one, StateT.run, Except.map, offsetVectorAxis_last]

theorem offsetVectorFirstindex_run {E : Type} (v : OffsetVector E) :
    (offsetVectorFirstindex () : VectorRun E I64).run v = .ok (v.first, v) := by
  have one : (int 1).val = 1 := rfl
  simp [offsetVectorFirstindex, firstindexArray, eachindexLinearVector, axes1, tupleGet,
    one, StateT.run, Except.map, offsetVectorAxis]

theorem resized_append {E : Type} (xs ys : List E) (k : Nat)
    (length : ys.length = xs.length + k) (keep : ys.take xs.length = xs) :
    ∃ zs, ys = xs ++ zs ∧ zs.length = k := by
  refine ⟨ys.drop xs.length, ?_, by simp [length]⟩
  conv => lhs; rw [← List.take_append_drop xs.length ys]
  rw [keep]

theorem set_after_prefix {E : Type} (xs : List E) (y x : E) :
    (xs ++ [y]).set xs.length x = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simpa using ih

theorem resizeGrow {E : Type} (resize : List E → I64 → Result (List E))
    (lawful : ResizeKeepsPrefix resize) (xs : List E) (k : Nat)
    (fits : (xs.length : Int) + k ≤ 9223372036854775807) :
    ∃ zs, resize xs (int ((xs.length : Int) + k)) = .ok (xs ++ zs) ∧ zs.length = k := by
  have value : (int ((xs.length : Int) + k)).val = xs.length + k :=
    native_val_int _ (by omega) fits
  obtain ⟨ys, run, length, keep⟩ := lawful xs (int ((xs.length : Int) + k)) (by omega)
  rw [value] at length keep
  have keep' : ys.take xs.length = xs := by
    rw [keep]; exact List.take_of_length_le (by omega)
  obtain ⟨zs, shape, count⟩ := resized_append xs ys k (by omega) keep'
  exact ⟨zs, by rw [run, shape], count⟩

/-- `push!(a::AbstractVector{Any}, x)`: growth by one element followed by
assignment at the new last index appends `x` and keeps the first index. -/
def PushAnyOneAppends : Prop :=
  ∀ (E : Type) (resize : List E → I64 → Result (List E)), ResizeKeepsPrefix resize →
  ∀ (v : OffsetVector E) (x : E), v.Room 1 →
    (pushOneAny offsetVectorLength (offsetVectorResize resize) offsetVectorLastindex
      offsetVectorSet () x).run v = .ok ((), { v with values := v.values ++ [x] })

theorem pushAnyOneAppends_proven : PushAnyOneAppends := by
  intro E resize lawful v x room
  obtain ⟨lenFits, lastFits⟩ := room
  obtain ⟨zs, grow, count⟩ := resizeGrow resize lawful v.values 1 (by simpa using lenFits)
  obtain ⟨y, rfl⟩ : ∃ y, zs = [y] := List.length_eq_one_iff.mp count
  have newLength : int (v.values.length : Int) + int 1 =
      int ((v.values.length : Int) + ((1 : Nat) : Int)) := by
    rw [vcatNativeAdd]; rfl
  have last := offsetVectorLastindex_run ({ v with values := v.values ++ [y] } : OffsetVector E)
  simp only [List.length_append, List.length_singleton] at last
  have firstRange := v.first.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at firstRange
  have lastValue : (int (v.first.val + ((v.values.length : Int) + 1) - 1)).val =
      v.first.val + v.values.length := by
    rw [native_val_int _ (by simp at lenFits lastFits; omega) (by simp at lenFits lastFits; omega)]
    omega
  have position : (v.first.val + v.values.length - v.first.val).toNat = v.values.length := by
    omega
  have inBounds : v.first.val ≤ v.first.val + v.values.length ∧
      v.first.val + v.values.length < v.first.val + ((v.values.length : Int) + 1) := by
    constructor <;> omega
  simp only [StateT.run] at last
  simp only [pushOneAny, StateT.run, StateT.bind, StateT.pure, offsetVectorLength,
    offsetVectorResize, Except.bind, Except.pure, bind, pure, newLength, grow, Except.map]
  rw [last]
  simp [offsetVectorSet, lastValue, position, inBounds, set_after_prefix]

/-- `push!(a::AbstractVector{T}, item)` converts before growing; it appends the
converted item and keeps the first index, and a failed conversion is thrown. -/
def PushConvertedAppends : Prop :=
  ∀ (E Raw C : Type) (isTarget : Raw → Bool) (asTarget : Raw → E)
    (convert : Raw → Result C) (assertType : C → Result E)
    (resize : List E → I64 → Result (List E)), ResizeKeepsPrefix resize →
  ∀ (v : OffsetVector E) (item : Raw), v.Room 1 →
    (pushOne isTarget asTarget (fun x => StateT.lift (convert x))
      (fun c => StateT.lift (assertType c)) offsetVectorLength (offsetVectorResize resize)
      offsetVectorLastindex offsetVectorSet () item).run v =
    ((if isTarget item then .ok (asTarget item) else convert item >>= assertType).map
      fun x => ((), { v with values := v.values ++ [x] }))

theorem pushOne_converted {m : Type → Type} [Monad m] {A Raw Converted E Ret : Type}
    (isTarget : Raw → Bool) (asTarget : Raw → E)
    (convert : Raw → m Converted) (assertType : Converted → m E)
    (length : A → m I64) (resize : A → I64 → m Ret)
    (lastindex : A → m I64) (set : A → I64 → E → m Unit) (a : A) (item : Raw) :
    pushOne isTarget asTarget convert assertType length resize lastindex set a item =
      (do
        let x ← if isTarget item then pure (asTarget item) else do assertType (← convert item)
        pushOneAny length resize lastindex set a x) := rfl

theorem pushConvertedAppends_proven : PushConvertedAppends := by
  intro E Raw C isTarget asTarget convert assertType resize lawful v item room
  have tail := pushAnyOneAppends_proven E resize lawful v
  simp only [StateT.run] at tail
  rw [pushOne_converted]
  cases target : isTarget item
  · cases converted : convert item with
    | error e =>
      simp [target, converted, StateT.run, StateT.lift, StateT.bind, Except.map]
    | ok c =>
      cases asserted : assertType c with
      | error e =>
        simp [target, converted, asserted, StateT.run, StateT.lift, StateT.bind, Except.map]
      | ok x =>
        simp [target, converted, asserted, StateT.run, StateT.lift, StateT.bind, Except.map,
          tail x room]
  · simp [target, StateT.run, StateT.bind, StateT.pure, Except.map, tail (asTarget item) room]

/-- Loop rule for a state-threading `for` loop over a list: if every element
advances the expected state of the already processed prefix by one element,
the loop ends in the expected state of the whole list. -/
theorem forIn_target {S α β : Type} (xs : List α)
    (f : α → β → StateT S Result (ForInStep β)) (target : List α → β × S)
    (step : ∀ pre x post, xs = pre ++ x :: post →
      f x (target pre).1 (target pre).2 =
        .ok (.yield (target (pre ++ [x])).1, (target (pre ++ [x])).2))
    (b : β) (s : S) (start : target [] = (b, s)) :
    forIn xs b f s = .ok (target xs) := by
  have general : ∀ post pre, xs = pre ++ post →
      forIn post (target pre).1 f (target pre).2 = .ok (target xs) := by
    intro post
    induction post with
    | nil =>
      intro pre split
      simp [List.forIn_nil, StateT.pure, split]
    | cons x post ih =>
      intro pre split
      have rest := ih (pre ++ [x]) (by simp [split])
      simp only [List.forIn_cons, StateT.bind, bind, step pre x post split]
      exact rest
  have := general xs [] (by simp)
  rwa [start] at this

theorem range_map_split {α : Type} (n : Nat) (g : Nat → α) (pre post : List α) (x : α)
    (split : (List.range n).map g = pre ++ x :: post) :
    pre.length < n ∧ x = g pre.length := by
  have length := congrArg List.length split
  simp only [List.length_map, List.length_range, List.length_append, List.length_cons] at length
  refine ⟨by omega, ?_⟩
  have entry := congrArg (fun xs => xs[pre.length]?) split
  simp only [List.getElem?_map, List.getElem?_range (by omega : pre.length < n),
    Option.map_some, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero] at entry
  exact (Option.some.inj entry).symm

theorem set_middle {E : Type} (pre post : List E) (z x : E) :
    (pre ++ z :: post).set pre.length x = pre ++ x :: post := by
  induction pre with
  | nil => rfl
  | cons a as ih => simpa using ih

theorem concatRange_one (n : Nat) (fits : (n : Int) ≤ 9223372036854775807) :
    concatRange (int 1) (int n) = (List.range n).map fun (k : Nat) => int (1 + (k : Int)) := by
  have one : (int 1).val = 1 := rfl
  have value : (int n).val = n := native_val_int _ (by omega) fits
  simp [concatRange, one, value]

/-- `push!(a::AbstractVector{Any}, x...)` appends the items in the given order
and keeps the first index: it grows once, then assigns from `lastindex(a) - nx + 1`. -/
def PushAnyManyAppends : Prop :=
  ∀ (E : Type) (resize : List E → I64 → Result (List E)), ResizeKeepsPrefix resize →
  ∀ (v : OffsetVector E) (items : List E), v.Room items.length →
    (pushManyAny offsetVectorLength (offsetVectorResize resize) offsetVectorLastindex
      (fun lo hi => pure (concatRange lo hi)) (fun xs i => StateT.lift (tupleGet xs i))
      offsetVectorSet () items).run v = .ok ((), { v with values := v.values ++ items })

theorem pushAnyManyAppends_proven : PushAnyManyAppends := by
  intro E resize lawful v items room
  obtain ⟨lenFits, lastFits⟩ := room
  have firstRange := v.first.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at firstRange
  obtain ⟨zs, grow, count⟩ := resizeGrow resize lawful v.values items.length lenFits
  have newLength : int (v.values.length : Int) + int (items.length : Int) =
      int ((v.values.length : Int) + (items.length : Int)) := vcatNativeAdd _ _
  have lengthRun : (offsetVectorLength () : VectorRun E I64) v =
      .ok (int (v.values.length : Int), v) := rfl
  have resizeRun : (offsetVectorResize resize ()
      (int (v.values.length : Int) + int (items.length : Int)) : VectorRun E Unit) v =
      .ok ((), ({ v with values := v.values ++ zs } : OffsetVector E)) := by
    rw [newLength]
    simp only [offsetVectorResize, grow]
    rfl
  have last := offsetVectorLastindex_run ({ v with values := v.values ++ zs } : OffsetVector E)
  simp only [List.length_append, count, StateT.run] at last
  have start : int (v.first.val + ↑(v.values.length + items.length) - 1) - int items.length =
      int (v.first.val + v.values.length - 1) := by
    rw [vcatNativeSub, show v.first.val + ((v.values.length + items.length : Nat) : Int) - 1 -
      (items.length : Int) = v.first.val + v.values.length - 1 by push_cast; omega]
  have range := concatRange_one items.length (by omega)
  simp only [pushManyAny, StateT.run, vrun_bind lengthRun, vrun_bind resizeRun, vrun_bind last,
    start, vrun_pure_bind, range]
  rw [vrun_bind (forIn_target _ _ (fun pre => (PUnit.unit, ({ v with values := (v.values ++
      items.take pre.length ++ zs.drop pre.length) } : OffsetVector E))) ?step _ _ ?start)]
  · simp only [vrun_pure]
    simp [List.take_of_length_le (Nat.le_refl _), count]
  case start => simp
  case step =>
  intro pre x post split
  obtain ⟨small, rfl⟩ := range_map_split _ _ pre post x split
  have index : (int (1 + (pre.length : Int))).val = 1 + pre.length :=
    native_val_int _ (by omega) (by omega)
  have read : tupleGet items (int (1 + (pre.length : Int))) = .ok items[pre.length] := by
    have positive : ¬ (1 + (pre.length : Int) < 1) := by omega
    have offset : (1 + (pre.length : Int)).toNat - 1 = pre.length := by omega
    simp [tupleGet, index, positive, offset, List.getElem?_eq_getElem small]
  have target : int (v.first.val + v.values.length - 1) + int (1 + (pre.length : Int)) =
      int (v.first.val + v.values.length + pre.length) := by
    rw [vcatNativeAdd, show v.first.val + (v.values.length : Int) - 1 + (1 + (pre.length : Int)) =
      v.first.val + v.values.length + pre.length by omega]
  have targetValue : (int (v.first.val + v.values.length + pre.length)).val =
      v.first.val + v.values.length + pre.length :=
    native_val_int _ (by omega) (by omega)
  have tailSplit : zs.drop pre.length = zs[pre.length]'(by omega) :: zs.drop (pre.length + 1) :=
    (List.drop_eq_getElem_cons (by omega))
  have lengthState : (v.values ++ List.take pre.length items ++
      List.drop pre.length zs).length = v.values.length + items.length := by
    simp [List.length_take, count]; omega
  have position : (v.first.val + v.values.length + pre.length - v.first.val).toNat =
      (v.values ++ List.take pre.length items).length := by
    simp [List.length_take]; omega
  have bounds : v.first.val ≤ v.first.val + v.values.length + pre.length ∧
      v.first.val + v.values.length + pre.length <
        v.first.val + ((v.values ++ List.take pre.length items ++
          List.drop pre.length zs).length : Int) := by
    rw [lengthState]; constructor <;> push_cast <;> omega
  have readRun : (StateT.lift (tupleGet items (int (1 + (pre.length : Int)))) : VectorRun E E)
      ({ v with values := v.values ++ items.take pre.length ++ zs.drop pre.length }) =
      .ok (items[pre.length],
        { v with values := v.values ++ items.take pre.length ++ zs.drop pre.length }) :=
    vrun_lift _ read
  have setRun : (offsetVectorSet () (int (v.first.val + v.values.length - 1) +
      int (1 + (pre.length : Int))) items[pre.length] : VectorRun E Unit)
      ({ v with values := v.values ++ items.take pre.length ++ zs.drop pre.length }) =
      .ok ((), { v with
        values := v.values ++ items.take (pre.length + 1) ++ zs.drop (pre.length + 1) }) := by
    rw [target]
    simp only [offsetVectorSet, targetValue, bounds, and_self, ↓reduceIte]
    rw [position, tailSplit, set_middle, List.take_succ, List.getElem?_eq_getElem small]
    simp only [Option.toList_some, List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append]
  dsimp only
  rw [vrun_bind readRun, vrun_bind setRun, vrun_pure]
  simp only [List.length_append, List.length_singleton]

/-- Every multi-item `push!` call made by abstractarray.jl dispatches to the
two-item or variadic method; only the single-item push is foreign. -/
def sourcePushItems {C E : Type} (push : C → E → Result C) : List E → C → Result C
  | [], a => pure a
  | [x], a => push a x
  | [x, y], a => pushTwo push push a x y
  | x :: y :: z :: rest, a =>
    pushMany (pushTwo push push) (fun b _ => sourcePushItems push (z :: rest) b) a x y (z :: rest)
termination_by items _ => items.length

/-- `push!(A, a, b)` for any collection whose one-item `push!` appends. -/
def PushTwoAppends : Prop :=
  ∀ (C E : Type) (elements : C → List E) (push : C → E → Result C),
    (∀ a x, ∃ out, push a x = .ok out ∧ elements out = elements a ++ [x]) →
    ∀ a x y, ∃ out, pushTwo push push a x y = .ok out ∧ elements out = elements a ++ [x, y]

theorem pushTwoAppends_proven : PushTwoAppends := by
  intro C E elements push lawful a x y
  obtain ⟨b, first, bValues⟩ := lawful a x
  obtain ⟨out, second, outValues⟩ := lawful b y
  exact ⟨out, by simp [pushTwo, first, second], by simp [outValues, bValues]⟩

/-- `push!(A, items...)` for any number of items, through the source two-item
and variadic dispatches, appends all items in the given order. -/
def PushVariadicAppends : Prop :=
  ∀ (C E : Type) (elements : C → List E) (push : C → E → Result C),
    (∀ a x, ∃ out, push a x = .ok out ∧ elements out = elements a ++ [x]) →
    ∀ items a, ∃ out, sourcePushItems push items a = .ok out ∧
      elements out = elements a ++ items

theorem sourcePushItems_contents {C E : Type} (elements : C → List E)
    (push : C → E → Result C)
    (lawful : ∀ a x, ∃ out, push a x = .ok out ∧ elements out = elements a ++ [x])
    (items : List E) (a : C) :
    ∃ out, sourcePushItems push items a = .ok out ∧ elements out = elements a ++ items := by
  match items with
  | [] => exact ⟨a, by simp [sourcePushItems], by simp⟩
  | [x] =>
    obtain ⟨out, run, values⟩ := lawful a x
    exact ⟨out, by simpa [sourcePushItems] using run, values⟩
  | [x, y] =>
    simpa [sourcePushItems] using pushTwoAppends_proven C E elements push lawful a x y
  | x :: y :: z :: rest =>
    obtain ⟨b, runTwo, bValues⟩ := pushTwoAppends_proven C E elements push lawful a x y
    obtain ⟨out, runRest, outValues⟩ := sourcePushItems_contents elements push lawful (z :: rest) b
    refine ⟨out, ?_, ?_⟩
    · simp [sourcePushItems, pushMany, runTwo, runRest]
    · simp [outValues, bValues]
termination_by items.length

theorem pushVariadicAppends_proven : PushVariadicAppends := by
  intro C E elements push lawful items a
  exact sourcePushItems_contents elements push lawful items a

/-- The foreign left fold over an iterator visits its elements in order. -/
def iteratorFoldl {V It E : Type} (remaining : It → List E) :
    (V → E → Result V) → It → V → Result V :=
  fun op it init => (remaining it).foldlM op init

/-- `rest(a, state...)` collects exactly the elements remaining after the
iteration state into a fresh empty vector, in order, whatever the size hint does. -/
def RestCollectsRemaining : Prop :=
  ∀ (A Ty State V It E Ret : Type) (elements : V → List E)
    (vector : Ty → I64 → Result V) (length : A → Result I64)
    (sizehint : V → I64 → Result Ret) (rest : A → State → Result It)
    (remaining : It → List E) (push : V → E → Result V),
    (∀ t v, vector t (int 0) = .ok v → elements v = []) →
    (∀ v x, ∃ w, push v x = .ok w ∧ elements w = elements v ++ [x]) →
    ∀ t a state v n r it, vector t (int 0) = .ok v → length a = .ok n →
      sizehint v n = .ok r → rest a state = .ok it →
      ∃ out, restArray vector length sizehint rest (iteratorFoldl remaining) push t a state =
        .ok out ∧ elements out = remaining it

theorem foldlM_push_contents {V E : Type} (elements : V → List E) (push : V → E → Result V)
    (lawful : ∀ v x, ∃ w, push v x = .ok w ∧ elements w = elements v ++ [x])
    (xs : List E) (v : V) :
    ∃ out, xs.foldlM push v = .ok out ∧ elements out = elements v ++ xs := by
  induction xs generalizing v with
  | nil => exact ⟨v, rfl, by simp⟩
  | cons x xs ih =>
    obtain ⟨w, run, values⟩ := lawful v x
    obtain ⟨out, rest, outValues⟩ := ih w
    exact ⟨out, by simp [List.foldlM_cons, run, rest], by simp [outValues, values]⟩

theorem restCollectsRemaining_proven : RestCollectsRemaining := by
  intro A Ty State V It E Ret elements vector length sizehint rest remaining push empty lawful
    t a state v n r it made counted hinted remainder
  obtain ⟨out, run, values⟩ := foldlM_push_contents elements push lawful (remaining it) v
  refine ⟨out, ?_, by simp [values, empty t v made]⟩
  simp [restArray, made, counted, hinted, remainder, iteratorFoldl, run]

/-! ## keepat! -/

/-- The foreign scalar `getindex` interface: checked read at a linear index. -/
def offsetVectorGet {E : Type} (_ : Unit) (i : I64) : VectorRun E E := fun v =>
  if v.first.val ≤ i.val then
    match v.values[(i.val - v.first.val).toNat]? with
    | some x => .ok (x, v)
    | none => .error (.julia .boundsError)
  else .error (.julia .boundsError)

/-- The foreign `deleteat!(a, lo:hi)` for a unit range of linear indices. -/
def offsetVectorDeleteRange {E : Type} (_ : Unit) (r : I64 × I64) : VectorRun E Unit :=
  fun v =>
    if r.2.val < r.1.val then .ok ((), v)
    else if v.first.val ≤ r.1.val ∧ r.2.val < v.first.val + v.values.length then
      .ok ((), { v with values := (v.values.take (r.1.val - v.first.val).toNat ++
        v.values.drop (r.2.val - v.first.val + 1).toNat) })
    else .error (.julia .boundsError)

/-- Source `nextind(::AbstractArray, i)`, with the identity `Int` conversion. -/
def offsetVectorNextind {E : Type} (a : Unit) (i : I64) : VectorRun E I64 :=
  StateT.lift (nextind (fun i : I64 => pure i) a i)

/-- The elements at the given linear indices, in index order. -/
def keepSelected {E : Type} (v : OffsetVector E) (inds : List I64) : List E :=
  inds.filterMap fun k => v.values[(k.val - v.first.val).toNat]?

def sourceKeepAtIndices {E : Type} (inds : List I64) : VectorRun E Unit :=
  keepAtIndices offsetVectorFirstindex offsetVectorLastindex
    (fun j k => pure (JuliaLean.base.int.ltSame j k))
    (fun i k => pure (JuliaLean.base.int.eqSame i k))
    offsetVectorGet offsetVectorSet offsetVectorNextind
    (fun lo hi => pure (lo, hi)) offsetVectorDeleteRange () inds

/-- `keepat!(a, inds)` for sorted, unique, in-bounds indices leaves exactly
`a[inds]`, keeping the first index. -/
def KeepAtSortedSelects : Prop :=
  ∀ (E : Type) (v : OffsetVector E) (inds : List I64), v.Room 1 →
    -9223372036854775808 ≤ v.first.val + v.values.length - 1 →
    inds.Pairwise (fun j k => j.val < k.val) →
    (∀ k ∈ inds, v.first.val ≤ k.val ∧ k.val < v.first.val + v.values.length) →
    (sourceKeepAtIndices inds).run v = .ok ((), { v with values := keepSelected v inds })

theorem increasing_count (lo hi : Int) : ∀ (xs : List I64),
    xs.Pairwise (fun j k => j.val < k.val) → (∀ k ∈ xs, lo ≤ k.val ∧ k.val < hi) →
    lo + xs.length ≤ hi ∨ xs = []
  | [], _, _ => Or.inr rfl
  | a :: as, sorted, bounds => by
    have head := bounds a (by simp)
    have rest := increasing_count (a.val + 1) hi as (List.Pairwise.of_cons sorted) (by
      intro b hb
      have := List.rel_of_pairwise_cons sorted hb
      exact ⟨by omega, (bounds b (by simp [hb])).2⟩)
    left
    rcases rest with rest | rfl
    · simp; omega
    · simp; omega

theorem keepSelected_append {E : Type} (v : OffsetVector E) (pre : List I64) (k : I64)
    (x : E) (read : v.values[(k.val - v.first.val).toNat]? = some x) :
    keepSelected v (pre ++ [k]) = keepSelected v pre ++ [x] := by
  simp [keepSelected, List.filterMap_append, read]

theorem keepSelected_length {E : Type} (v : OffsetVector E) : ∀ (inds : List I64),
    (∀ k ∈ inds, v.first.val ≤ k.val ∧ k.val < v.first.val + v.values.length) →
    (keepSelected v inds).length = inds.length
  | [], _ => rfl
  | k :: ks, bounds => by
    have here := bounds k (by simp)
    have small : (k.val - v.first.val).toNat < v.values.length := by omega
    have rest := keepSelected_length v ks (fun j hj => bounds j (by simp [hj]))
    show (List.filterMap _ (k :: ks)).length = _
    rw [List.filterMap_cons, List.getElem?_eq_getElem small, List.length_cons, List.length_cons]
    exact congrArg (· + 1) rest

set_option maxRecDepth 4096 in
theorem keepAtSortedSelects_proven : KeepAtSortedSelects := by
  intro E v inds room lastLow sorted bounds
  obtain ⟨lenFits, lastFits⟩ := room
  have firstRange := v.first.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at firstRange
  have countFits : inds.length ≤ v.values.length := by
    rcases increasing_count v.first.val (v.first.val + v.values.length) inds sorted bounds with
      h | h
    · omega
    · simp [h]
  have first := offsetVectorFirstindex_run v
  simp only [StateT.run] at first
  simp only [sourceKeepAtIndices, keepAtIndices, StateT.run, StateT.bind, bind, Except.bind,
    first]
  rw [forIn_target inds _ (fun pre =>
      (((pre.getLast?, int (v.first.val + pre.length)) : Option I64 × I64),
        ({ v with values := (keepSelected v pre ++ v.values.drop pre.length) } :
          OffsetVector E))) ?step _ _ (by simp [native_int_val, keepSelected])]
  · have selected := keepSelected_length v inds bounds
    have last := offsetVectorLastindex_run
      ({ v with values := (keepSelected v inds ++ v.values.drop inds.length) } : OffsetVector E)
    simp only [StateT.run, List.length_append, List.length_drop, selected] at last
    have total : inds.length + (v.values.length - inds.length) = v.values.length := by omega
    rw [total] at last
    have lowValue : (int (v.first.val + inds.length)).val = v.first.val + inds.length :=
      native_val_int _ (by omega) (by omega)
    have highValue : (int (v.first.val + v.values.length - 1)).val =
        v.first.val + v.values.length - 1 := native_val_int _ lastLow (by omega)
    have stateLen : (keepSelected v inds ++ List.drop inds.length v.values).length =
        v.values.length := by simp [selected]; omega
    simp only [last, pure, StateT.pure, Except.pure, offsetVectorDeleteRange, lowValue,
      highValue, stateLen]
    by_cases full : inds.length = v.values.length
    · have empty : v.values.drop inds.length = [] := by simp [full]
      have skip : v.first.val + v.values.length - 1 < v.first.val + inds.length := by omega
      simp [skip, empty]
    · have inside : ¬ (v.first.val + v.values.length - 1 < v.first.val + inds.length) := by
        omega
      have valid : v.first.val ≤ v.first.val + inds.length ∧
          v.first.val + v.values.length - 1 < v.first.val + v.values.length := by omega
      have takeLength : (v.first.val + inds.length - v.first.val).toNat =
          (keepSelected v inds).length := by rw [selected]; omega
      have dropLength : (v.first.val + v.values.length - 1 - v.first.val + 1).toNat =
          (keepSelected v inds ++ List.drop inds.length v.values).length := by
        rw [stateLen]; omega
      simp only [inside, ↓reduceIte, valid, and_self]
      rw [takeLength, dropLength, List.take_left, List.drop_length, List.append_nil]
  intro pre k post split
  have sub : (pre ++ [k]).Sublist inds := by
    rw [split]; exact List.Sublist.append_left (List.singleton_sublist.mpr (by simp)) pre
  have sortedPre := sorted.sublist sub
  have before : ∀ a ∈ pre, a.val < k.val :=
    fun a ha => (List.pairwise_append.mp sortedPre).2.2 a ha k (by simp)
  have inPre : ∀ a ∈ pre, v.first.val ≤ a.val ∧ a.val < v.first.val + v.values.length :=
    fun a ha => bounds a (sub.subset (by simp [ha]))
  have kBound := bounds k (sub.subset (by simp))
  have lower : v.first.val + pre.length ≤ k.val := by
    rcases increasing_count v.first.val k.val pre (List.pairwise_append.mp sortedPre).1
      (fun a ha => ⟨(inPre a ha).1, before a ha⟩) with h | h
    · exact h
    · simp [h]; omega
  have selLen := keepSelected_length v pre inPre
  have posSmall : (k.val - v.first.val).toNat < v.values.length := by omega
  have readState : (keepSelected v pre ++ v.values.drop pre.length)[(k.val - v.first.val).toNat]? =
      some v.values[(k.val - v.first.val).toNat] := by
    rw [List.getElem?_append_right (by omega), List.getElem?_drop, selLen,
      show pre.length + ((k.val - v.first.val).toNat - pre.length) =
        (k.val - v.first.val).toNat by omega, List.getElem?_eq_getElem posSmall]
  have selNext := keepSelected_append v pre k _ (List.getElem?_eq_getElem posSmall)
  have iValue : (int (v.first.val + pre.length)).val = v.first.val + pre.length :=
    native_val_int _ (by omega) (by omega)
  have nextValue : int (v.first.val + pre.length) + int 1 =
      int (v.first.val + ((pre ++ [k]).length : Nat)) := by
    rw [vcatNativeAdd, List.length_append, List.length_singleton,
      show v.first.val + (pre.length : Int) + 1 = v.first.val + ((pre.length + 1 : Nat) : Int) by
        push_cast; omega]
  have jSmall : pre.length < v.values.length := by omega
  have tailSplit : v.values.drop pre.length =
      v.values[pre.length] :: v.values.drop (pre.length + 1) :=
    List.drop_eq_getElem_cons jSmall
  have lessOk : ∀ p, pre.getLast? = some p → JuliaLean.base.int.ltSame p k = true := by
    intro p hp
    rw [JuliaLean.Proofs.base.int.ltSame_eq]
    simpa using before p (List.mem_of_getLast? hp)
  have stateLength : (keepSelected v pre ++ List.drop pre.length v.values).length =
      v.values.length := by simp [selLen]; omega
  have setBounds : v.first.val ≤ (int (v.first.val + pre.length)).val ∧
      (int (v.first.val + pre.length)).val <
        v.first.val + ((keepSelected v pre ++ List.drop pre.length v.values).length : Int) := by
    rw [iValue, stateLength]; omega
  have setPosition : ((int (v.first.val + pre.length)).val - v.first.val).toNat =
      (keepSelected v pre).length := by rw [iValue, selLen]; omega
  have eqValue : JuliaLean.base.int.eqSame (int (v.first.val + pre.length)) k =
      decide (v.first.val + pre.length = k.val) := by
    rw [JuliaLean.Proofs.base.int.eqSame_eq, iValue]
  have lastK : (pre ++ [k]).getLast? = some k := by simp
  by_cases same : v.first.val + pre.length = k.val
  · have samePos : (k.val - v.first.val).toNat = pre.length := by omega
    have eqTrue : JuliaLean.base.int.eqSame (int (v.first.val + pre.length)) k = true := by
      rw [eqValue]; exact decide_eq_true same
    have readSame : (keepSelected v pre ++ v.values.drop pre.length)[(k.val -
        v.first.val).toNat]? = some v.values[pre.length] := by
      rw [samePos, List.getElem?_append_right (by omega), List.getElem?_drop, selLen,
        Nat.sub_self, Nat.add_zero, List.getElem?_eq_getElem jSmall]
    have selSame := keepSelected_append v pre k v.values[pre.length]
      (by rw [samePos]; exact List.getElem?_eq_getElem jSmall)
    cases lastPrev : pre.getLast? <;>
      simp only [offsetVectorGet, offsetVectorNextind, nextind, StateT.lift, StateT.bind,
        StateT.pure, pure, bind, Except.bind, Except.pure, kBound.1, ↓reduceIte, readSame,
        eqTrue, Bool.not_true, lessOk, lastPrev, Bool.false_eq_true, nextValue, lastK,
        selSame] <;>
      rw [tailSplit] <;>
      simp only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
  · have eqFalse : JuliaLean.base.int.eqSame (int (v.first.val + pre.length)) k = false := by
      rw [eqValue]; exact decide_eq_false same
    cases lastPrev : pre.getLast? <;>
      simp only [offsetVectorGet, offsetVectorNextind, nextind, StateT.lift, StateT.bind,
        StateT.pure, pure, bind, Except.bind, Except.pure, kBound.1, ↓reduceIte, readState,
        eqFalse, Bool.not_false, Bool.not_true, lessOk, lastPrev, Bool.false_eq_true,
        nextValue, lastK, selNext, offsetVectorSet, setBounds, and_self, setPosition] <;>
      rw [tailSplit, set_middle] <;>
      simp only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]

/-! ## circshift! -/

/-- The foreign `reverse!(v, start, stop)`: a no-op when `stop ≤ start`, and
otherwise reverses the elements between the two checked linear indices. -/
def offsetVectorReverseRange {E : Type} (_ : Unit) (lo hi : I64) : VectorRun E Unit :=
  fun v =>
    if hi.val ≤ lo.val then .ok ((), v)
    else if v.first.val ≤ lo.val ∧ hi.val < v.first.val + v.values.length then
      .ok ((), { v with values := (v.values.take (lo.val - v.first.val).toNat ++
        ((v.values.take ((hi.val - v.first.val).toNat + 1)).drop
          (lo.val - v.first.val).toNat).reverse ++
        v.values.drop ((hi.val - v.first.val).toNat + 1)) })
    else .error (.julia .boundsError)

/-- The foreign `reverse!(v)`. -/
def offsetVectorReverse {E : Type} (_ : Unit) : VectorRun E Unit :=
  fun v => .ok ((), { v with values := v.values.reverse })

def sourceCircshift {E Shift : Type} (mod : Shift → I64 → Result I64) (shift : Shift) :
    VectorRun E Unit :=
  circshiftInplace offsetVectorLength (fun n => JuliaLean.base.int.eqSame n (int 0))
    (fun s n => StateT.lift (mod s n)) (fun r => JuliaLean.base.int.eqSame r (int 0))
    offsetVectorFirstindex offsetVectorLastindex (fun i r => pure (i - r))
    (fun i => pure (i + int 1)) offsetVectorReverseRange offsetVectorReverse () shift

/-- `circshift!(a, shift)` rotates the elements right by `mod(shift, length(a))`
positions (the last `mod(shift, n)` elements come first) and keeps the first
index, for any integer shift type whose `mod` has its documented value. -/
def CircshiftRotates : Prop :=
  ∀ (E Shift : Type) (shiftValue : Shift → Int) (mod : Shift → I64 → Result I64),
    (∀ s n, 0 < n.val → mod s n = .ok (int (shiftValue s % n.val))) →
    ∀ (v : OffsetVector E) (shift : Shift), v.Room 1 →
      -9223372036854775808 ≤ v.first.val + v.values.length - 1 →
      (sourceCircshift mod shift).run v =
        .ok ((), { v with values := (v.values.drop
          (v.values.length - (shiftValue shift % v.values.length).toNat) ++
          v.values.take (v.values.length - (shiftValue shift % v.values.length).toNat)) })

theorem take_drop_short {E : Type} (xs : List E) (p q : Nat) (short : q ≤ p + 1) :
    ((xs.take q).drop p).reverse = (xs.take q).drop p := by
  have : ((xs.take q).drop p).length ≤ 1 := by simp; omega
  match h : (xs.take q).drop p, this with
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, small => simp [h] at small

theorem offsetVectorReverseRange_run {E : Type} (v : OffsetVector E) (p q : Nat)
    (order : p ≤ q) (fits : q ≤ v.values.length) (lo hi : I64)
    (loValue : lo.val = v.first.val + p) (hiValue : hi.val = v.first.val + q - 1) :
    (offsetVectorReverseRange () lo hi : VectorRun E Unit).run v =
      .ok ((), { v with values := (v.values.take p ++ ((v.values.take q).drop p).reverse ++
        v.values.drop q) }) := by
  simp only [StateT.run, offsetVectorReverseRange]
  by_cases small : hi.val ≤ lo.val
  · rw [if_pos small, take_drop_short _ _ _ (by omega)]
    have whole : v.values.take p ++ (v.values.take q).drop p = v.values.take q := by
      conv => rhs; rw [← List.take_append_drop p (v.values.take q)]
      rw [List.take_take, Nat.min_eq_left order]
    rw [whole, List.take_append_drop]
  · rw [if_neg small]
    have inside : v.first.val ≤ lo.val ∧ hi.val < v.first.val + v.values.length := by
      constructor <;> omega
    rw [if_pos inside]
    have pValue : (lo.val - v.first.val).toNat = p := by omega
    have qValue : (hi.val - v.first.val).toNat + 1 = q := by omega
    rw [pValue, qValue]

theorem vrun_bind_reverse {E β : Type} (w : OffsetVector E) (f : Unit → VectorRun E β) :
    (offsetVectorReverse () >>= f) w = f () { w with values := w.values.reverse } :=
  vrun_bind rfl

theorem circshiftRotates_proven : CircshiftRotates := by
  intro E Shift shiftValue mod lawful v shift room lastLow
  obtain ⟨lenFits, lastFits⟩ := room
  have firstRange := v.first.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at firstRange
  have zeroVal : (int 0).val = 0 := rfl
  have lengthValue : (int (v.values.length : Int)).val = v.values.length :=
    native_val_int _ (by omega) (by omega)
  have lengthRun : (offsetVectorLength () : VectorRun E I64) v =
      .ok (int (v.values.length : Int), v) := rfl
  by_cases empty : v.values.length = 0
  · have zero : JuliaLean.base.int.eqSame (int (v.values.length : Int)) (int 0) = true := by
      rw [JuliaLean.Proofs.base.int.eqSame_eq, lengthValue, empty]; decide
    simp only [sourceCircshift, circshiftInplace, StateT.run, vrun_bind lengthRun, zero,
      ↓reduceIte, vrun_pure]
    simp [empty]
  have positive : 0 < (int (v.values.length : Int)).val := by rw [lengthValue]; omega
  have nonzero : JuliaLean.base.int.eqSame (int (v.values.length : Int)) (int 0) = false := by
    rw [JuliaLean.Proofs.base.int.eqSame_eq, lengthValue, zeroVal]; exact decide_eq_false (by omega)
  have reduced := lawful shift (int (v.values.length : Int)) positive
  rw [lengthValue] at reduced
  have rRange : 0 ≤ shiftValue shift % v.values.length ∧
      shiftValue shift % v.values.length < v.values.length :=
    ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have rValue : (int (shiftValue shift % v.values.length)).val =
      shiftValue shift % v.values.length := native_val_int _ (by omega) (by omega)
  have modRun : (StateT.lift (mod shift (int (v.values.length : Int))) : VectorRun E I64) v =
      .ok (int (shiftValue shift % v.values.length), v) := vrun_lift v reduced
  by_cases noShift : shiftValue shift % v.values.length = 0
  · have zero : JuliaLean.base.int.eqSame (int (shiftValue shift % v.values.length)) (int 0) =
        true := by rw [JuliaLean.Proofs.base.int.eqSame_eq, rValue, noShift]; decide
    simp only [sourceCircshift, circshiftInplace, StateT.run, vrun_bind lengthRun, nonzero,
      Bool.false_eq_true, ↓reduceIte, vrun_bind modRun, zero, vrun_pure]
    simp [noShift]
  have shiftNonzero : JuliaLean.base.int.eqSame (int (shiftValue shift % v.values.length))
      (int 0) = false := by
    rw [JuliaLean.Proofs.base.int.eqSame_eq, rValue, zeroVal]; exact decide_eq_false noShift
  obtain ⟨d, hd⟩ : ∃ d, d = v.values.length - (shiftValue shift % v.values.length).toNat :=
    ⟨_, rfl⟩
  rw [← hd]
  have dPos : 0 < d := by omega
  have dLt : d < v.values.length := by omega
  have last1 := offsetVectorLastindex_run v
  simp only [StateT.run] at last1
  have first1 := offsetVectorFirstindex_run v
  simp only [StateT.run] at first1
  have subEq : int (v.first.val + v.values.length - 1) - int (shiftValue shift %
      v.values.length) = int (v.first.val + d - 1) := by
    rw [vcatNativeSub, show v.first.val + (v.values.length : Int) - 1 - shiftValue shift %
      (v.values.length : Int) = v.first.val + d - 1 by omega]
  have hi1 : (int (v.first.val + d - 1)).val = v.first.val + d - 1 :=
    native_val_int _ (by omega) (by omega)
  have rev1 := offsetVectorReverseRange_run v 0 d (by omega) (by omega) v.first
    (int (v.first.val + d - 1)) (by simp) hi1
  simp only [StateT.run, List.take_zero, List.drop_zero, List.nil_append] at rev1
  have len1 : ((v.values.take d).reverse ++ v.values.drop d).length = v.values.length := by
    simp; omega
  have addEq : int (v.first.val + d - 1) + int 1 = int (v.first.val + d) := by
    rw [vcatNativeAdd, show v.first.val + (d : Int) - 1 + 1 = v.first.val + d by omega]
  have last2 := offsetVectorLastindex_run
    ({ v with values := ((v.values.take d).reverse ++ v.values.drop d) } : OffsetVector E)
  simp only [StateT.run, len1] at last2
  have lo2 : (int (v.first.val + d)).val = v.first.val + d :=
    native_val_int _ (by omega) (by omega)
  have hi2 : (int (v.first.val + v.values.length - 1)).val =
      v.first.val + v.values.length - 1 := native_val_int _ lastLow (by omega)
  have rev2 := offsetVectorReverseRange_run
    ({ v with values := ((v.values.take d).reverse ++ v.values.drop d) } : OffsetVector E)
    d v.values.length (by omega) (by rw [len1]; exact Nat.le_refl _) (int (v.first.val + d))
    (int (v.first.val + v.values.length - 1)) lo2 (by rw [hi2])
  simp only [StateT.run] at rev2
  have leftLength : (v.values.take d).reverse.length = d := by simp; omega
  have v1take : ((v.values.take d).reverse ++ v.values.drop d).take d =
      (v.values.take d).reverse := by
    have := List.take_left (l₁ := (v.values.take d).reverse) (l₂ := v.values.drop d)
    rwa [leftLength] at this
  have v1drop : ((v.values.take d).reverse ++ v.values.drop d).drop d = v.values.drop d := by
    have := List.drop_left (l₁ := (v.values.take d).reverse) (l₂ := v.values.drop d)
    rwa [leftLength] at this
  have v1takeAll : ((v.values.take d).reverse ++ v.values.drop d).take v.values.length =
      (v.values.take d).reverse ++ v.values.drop d :=
    List.take_of_length_le (by rw [len1]; exact Nat.le_refl _)
  have v1dropAll : ((v.values.take d).reverse ++ v.values.drop d).drop v.values.length = [] :=
    List.drop_of_length_le (by rw [len1]; exact Nat.le_refl _)
  rw [v1takeAll, v1take, v1drop, v1dropAll] at rev2
  simp only [sourceCircshift, circshiftInplace, StateT.run, vrun_bind lengthRun, nonzero,
    Bool.false_eq_true, ↓reduceIte, vrun_bind modRun, shiftNonzero, vrun_bind last1,
    vrun_bind first1, vrun_pure_bind, subEq, vrun_bind rev1, addEq, vrun_bind last2,
    vrun_bind rev2, vrun_bind_reverse, vrun_pure]
  simp


def entries : List JuliaLean.Registry.Entry := [
  { id := "abstractarrayspecs-push-one", juliaFile := "base/abstractarray.jl"
    juliaFns := ["push!@3649"]
    statement := "push!(a::AbstractVector{T}, item) for a vector whose resize! keeps its first elements appends convert(T, item) after the existing elements and keeps the first index; a failed conversion or type assertion is thrown and the vector is untouched."
    source := "base/abstractarray.jl:3649-3656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PushConvertedAppends, thm := some ``pushConvertedAppends_proven },
  { id := "abstractarrayspecs-push-one-any", juliaFile := "base/abstractarray.jl"
    juliaFns := ["push!@3659"]
    statement := "push!(a::AbstractVector{Any}, x) for a vector whose resize! keeps its first elements appends x and keeps the first index, at any first index whose last index fits Int."
    source := "base/abstractarray.jl:3659-3664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PushAnyOneAppends, thm := some ``pushAnyOneAppends_proven },
  { id := "abstractarrayspecs-push-any", juliaFile := "base/abstractarray.jl"
    juliaFns := ["push!@3665"]
    statement := "push!(a::AbstractVector{Any}, x...) for a vector whose resize! keeps its first elements appends the items in the given order and keeps the first index, at any first index whose new last index fits Int."
    source := "base/abstractarray.jl:3665-3675 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PushAnyManyAppends, thm := some ``pushAnyManyAppends_proven },
  { id := "abstractarrayspecs-push-two", juliaFile := "base/abstractarray.jl"
    juliaFns := ["push!@3679"]
    statement := "push!(A, a, b) for any collection whose one-item push! appends, appends a and then b."
    source := "base/abstractarray.jl:3679-3679 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PushTwoAppends, thm := some ``pushTwoAppends_proven },
  { id := "abstractarrayspecs-push-vararg", juliaFile := "base/abstractarray.jl"
    juliaFns := ["push!@3679", "push!@3680"]
    statement := "push!(A, items...) with any number of items, dispatched through the two-item and variadic methods, appends all items in the given order for any collection whose one-item push! appends."
    source := "base/abstractarray.jl:3679-3680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PushVariadicAppends, thm := some ``pushVariadicAppends_proven },
  { id := "abstractarrays-source-rest-remaining", juliaFile := "base/abstractarray.jl"
    juliaFns := ["rest@3688"]
    statement := "rest(a::AbstractArray, state) collects exactly the elements remaining after the iteration state, in iteration order, into a fresh vector, whatever the size hint does, when the foreign one-item push! appends."
    source := "base/abstractarray.jl:3688-3693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``RestCollectsRemaining, thm := some ``restCollectsRemaining_proven },
  { id := "arrayops-keepat-sorted", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_keepat!@3699"]
    statement := "keepat!(a, inds) for sorted, unique, in-bounds Int indices leaves exactly a[inds] and keeps the first index, at any first index."
    source := "base/abstractarray.jl:3699-3715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``KeepAtSortedSelects, thm := some ``keepAtSortedSelects_proven },
  { id := "abstractarrayspecs-circshift", juliaFile := "base/abstractarray.jl"
    juliaFns := ["circshift!@3756"]
    statement := "circshift!(a::AbstractVector, shift) rotates the elements by mod(shift, length(a)) positions, so the last mod(shift, n) elements come first, and keeps the first index, for any integer shift (including typemin) whose mod has its documented value; empty vectors are unchanged."
    source := "base/abstractarray.jl:3756-3766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CircshiftRotates, thm := some ``circshiftRotates_proven },
  { id := "arrayops-circshift", juliaFile := "base/abstractarray.jl"
    juliaFns := ["circshift!@3756"]
    statement := "circshift!(v, k) rotates right by mod(k, length(v)) for every integer shift value, including typemin and typemax, at any first index."
    source := "base/abstractarray.jl:3756-3766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CircshiftRotates, thm := some ``circshiftRotates_proven },
  { id := "abstractarrays-source-hvncat-one-dimension-elements", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hvncat@2501"]
    statement := "The one-dimensional numeric shape dispatcher preserves every converted argument in order and produces a vector for column-first input or a one-row matrix for row-first input. Foreign typed-vector conversion and reshape satisfy their element and allocation contracts."
    source := "base/abstractarray.jl:2501-2512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``HvncatOneDimNumbersContents,
    thm := some ``hvncatOneDimNumbersContents_proven },
  { id := "abstractarrays-source-block-copy-size-mismatch", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@1159"]
    statement := "Rectangular block copying rejects unequal source and destination row or column counts before checking bounds, resolving dense-array aliases, reading, or writing. Throwing bounds checks and canonical scalar indexing are foreign array interfaces."
    source := "base/abstractarray.jl:1159-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``BlockCopyRejectsSizeMismatch,
    thm := some ``blockCopyRejectsSizeMismatch_proven },
  { id := "abstractarrays-source-mutable-copy-elements", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copymutable@1211"]
    statement := "Mutable copying into the destination supplied by similar preserves every source element in order, for all source and destination index styles, under the foreign allocation and dense-copy content contracts."
    source := "base/abstractarray.jl:1211-1213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``MutableArrayCopyContents,
    thm := some ``mutableArrayCopyContents_proven },
  { id := "abstractarrays-source-one-nonsquare", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_one@1222"]
    statement := "Constructing a matrix multiplicative identity rejects unequal axis lengths before evaluating zero, checking offset axes, allocating, filling, or assigning diagonal elements."
    source := "base/abstractarray.jl:1222-1234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``OneMatrixRejectsNonsquare,
    thm := some ``oneMatrixRejectsNonsquare_proven },
  { id := "abstractarrays-source-counted-array-copy-elements", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@1135"]
    statement := "Positive counted array copying assigns exactly n source elements in order at the requested destination offset, with no other writes, after the native source and destination extent checks and dense source unaliasing."
    source := "base/abstractarray.jl:1135-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CountedArrayCopyContents,
    thm := some ``countedArrayCopyContents_proven },
  { id := "abstractarrays-source-copy-from-invalid-start", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@1129"]
    statement := "Array copying from a source offset outside its actual linear axis throws BoundsError before invoking counted copying, regardless of the destination or copy implementation."
    source := "base/abstractarray.jl:1129-1133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ArrayCopyFromRejectsInvalidStart,
    thm := some ``arrayCopyFromRejectsInvalidStart_proven },
  { id := "abstractarrays-source-array-copy-elements", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@1072", "copyto!@1082"]
    statement := "Both array-copy entry points preserve every source element in order in the destination prefix, for all linear and Cartesian index-style combinations, with no extra scalar assignments. Aliasing uses source data identities and dense unaliasing under the documented foreign copy-content contract."
    source := "base/abstractarray.jl:1072-1123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ArrayCopyPreservesElements,
    thm := some ``arrayCopyPreservesElements_proven },
  { id := "multidimcov-abstract-l1088-copy-unalias", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto_unaliased!@1088"]
    statement := "For every destination/source index-style combination with lawful ordered scalar access, unaliased copying assigns every source value to the destination prefix in order and performs no other assignment. Native endpoint checks reject non-fitting translations before any write."
    source := "base/abstractarray.jl:1042-1123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnaliasedCopySpecification,
    thm := some ``unaliasedCopySpecification_proven },
  { id := "abstractarrays-source-dense-shared-heap-unalias", juliaFile := "base/abstractarray.jl"
    juliaFns := ["unalias@1566", "unaliascopy@1582", "mightalias@1603", "dataids@1627", "dataids@1628"]
    statement := "Dense unaliasing uses the actual dense array copy and shared heap allocator: it preserves every source slot and every old heap object, allocates a new handle distinct from every old destination exactly when nonempty inputs alias, and otherwise returns the original source without changing the heap."
    source := "base/abstractarray.jl:1566-1628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``DenseHeapUnaliasSeparation, thm := some ``denseHeapUnaliasSeparation_proven },
  { id := "abstractarrays-source-native-coordinate-lookup-inverse", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_lookup@3231", "_lookup@3232", "_ind2sub_recurse@3217", "_ind2sub_recurse@3218"]
    statement := "Native integer- and range-relative coordinate lookup and offset extraction undo each other for every native integer, including overflow boundaries; terminal inverse-coordinate tuples preserve the original displacement."
    source := "base/abstractarray.jl:3207-3232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``NativeCoordinateLookupInverse, thm := some ``nativeCoordinateLookupInverse_proven },
  { id := "abstractarrays-source-vector-coordinate-tuple-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_sub2ind_vec@3263", "_sub2ind_vec@3264"]
    statement := "The coordinate tuple assembled from an arbitrary family of input vectors contains each vector's selected scalar value in exactly the original vector order, under the foreign canonical scalar-read contract."
    source := "base/abstractarray.jl:3263-3264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``VectorCoordinateTupleContents, thm := some ``vectorCoordinateTupleContents_proven },
  { id := "abstractarrayspecs-cmp-isless", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cmp@3119", "isless@3145"]
    statement := "For arbitrary element comparisons and either storage style, vectors compare their starting indices first and then their complete element sequences lexicographically, with shorter equal-prefix sequences ordered first; vector isless has the corresponding negative comparison sign."
    source := "base/abstractarray.jl:3119-3145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``VectorLexicalOrder, thm := some ``vectorLexicalOrder_proven },
  { id := "abstractarrays-source-scalar-array-order", juliaFile := "base/abstractarray.jl"
    juliaFns := ["isless@3135"]
    statement := "Ordering two zero-dimensional arrays compares their sole stored scalar values using the element ordering relation."
    source := "base/abstractarray.jl:3135-3137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ScalarArrayOrder, thm := some ``scalarArrayOrder_proven },
  { id := "abstractarrays-source-strided-memory-byte-positions", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_memory_offset@1287"]
    statement := "For arbitrary exact-rank native coordinates and strides, the strided-array byte offset equals the mathematical coordinate-displacement/stride dot product times element size, wrapped to native width, including every intermediate overflow."
    source := "base/abstractarray.jl:1287-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``StridedMemoryBytePositions, thm := some ``stridedMemoryBytePositions_proven },
  { id := "abstractarrayspecs-pushfirst-two", juliaFile := "base/abstractarray.jl"
    juliaFns := ["pushfirst!@3681"]
    statement := "Two-item prepending puts the supplied items, in their original order, before all existing collection elements, for every collection satisfying its foreign single-item prepend contract."
    source := "base/abstractarray.jl:3681 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PrependTwoContents, thm := some ``prependTwoContents_proven },
  { id := "abstractarrayspecs-pushfirst-vararg", juliaFile := "base/abstractarray.jl"
    juliaFns := ["pushfirst!@3681", "pushfirst!@3682"]
    statement := "Variadic prepending preserves the complete supplied item order before all existing collection elements; every two-item and variadic recursive call uses the corresponding source definition."
    source := "base/abstractarray.jl:3681-3682 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``PrependVariadicContents, thm := some ``prependVariadicContents_proven },
  { id := "abstractarrays-source-stack-axis-metadata", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_iterator_axes@3035", "_vec_axis@3051", "_ensure_array@3099"]
    statement := "Length-only iterators get one one-based axis of their length; flattening preserves an existing singleton axis or gives a one-based axis of the native product length; the nonarray allocation exemplar is empty."
    source := "base/abstractarray.jl:3035-3099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``StackAxisMetadata, thm := some ``stackAxisMetadata_proven },
  { id := "abstractarrays-source-stack-uniform-slices", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_stack_size_check@3089"]
    statement := "Stack's slice check succeeds exactly for equal slice axes and throws DimensionMismatch for unequal axes, using the source iterator-size and iterator-axes dispatch."
    source := "base/abstractarray.jl:3089-3096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``StackUniformSlices, thm := some ``stackUniformSlices_proven },
  { id := "abstractarrays-source-empty-rank-inverse-bounds", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_ind2sub@3210"]
    statement := "A rank-zero shape has precisely one linear position: position one returns its empty coordinate tuple, and every other integer raises BoundsError."
    source := "base/abstractarray.jl:3210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``EmptyRankInverseBounds, thm := some ``emptyRankInverseBounds_proven },
  { id := "abstractarrays-source-ambiguous-inverse-rejected", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_ind2sub@3213", "_sub2ind@3235"]
    statement := "The inverse scalar and forward vector coordinate interfaces reject an ambiguous one-dimensional non-OneTo axis with ArgumentError for every index representation."
    source := "base/abstractarray.jl:3213-3237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``AmbiguousInverseRejected, thm := some ``ambiguousInverseRejected_proven },
  { id := "abstractarrays-source-scalar-default-get-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["get@1637", "get@1640"]
    statement := "Scalar eager and lazy defaults return the stored element inside the linear index interval, and exactly the supplied default value or computation outside it, using the concrete bounds and generic canonical-read source chains."
    source := "base/abstractarray.jl:1637-1642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ScalarDefaultGetContents, thm := some ``scalarDefaultGetContents_proven },
  { id := "abstractarrays-source-coordinate-default-get-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["get@1638", "get@1639", "get@1641", "get@1642"]
    statement := "Eager and lazy tuple defaults, including the empty tuple, return canonical stored contents exactly when every coordinate is valid under omitted and extra singleton rules; otherwise they return exactly the supplied fallback."
    source := "base/abstractarray.jl:1638-1642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CoordinateDefaultGetContents, thm := some ``coordinateDefaultGetContents_proven },
  { id := "abstractarrays-source-range-map-constructed-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["map@1267", "map@1268", "map@1270"]
    statement := "Mapping a target real type over step, unit, and linear ranges constructs the documented sequence from the converted original start, step, and endpoint, retaining the original linear-range count, under the foreign range constructors' sequence laws."
    source := "base/abstractarray.jl:1267-1272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``RangeMapConstructedContents, thm := some ``rangeMapConstructedContents_proven },
  { id := "abstractarrays-source-dense-pointer-byte-positions", juliaFile := "base/abstractarray.jl"
    juliaFns := ["pointer@1280", "_memory_offset@1286"]
    statement := "For every native linear index, a dense-array byte offset is distance from the first linear index times element size modulo native width, including intermediate overflow; pointer indexing adds the same mathematical byte count modulo address width."
    source := "base/abstractarray.jl:1280-1286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``DensePointerBytePositions, thm := some ``densePointerBytePositions_proven },
  { id := "abstractarrayspecs-copyto-iter-n", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@1003"]
    statement := "Counted iterable copying rejects negative counts, leaves all state unchanged for zero, validates source and destination offsets in source order, rejects unavailable or too-short source suffixes, and otherwise writes exactly the requested number of suffix values while preserving every other cell, for all native counts and destination indices."
    source := "base/abstractarray.jl:1003-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CountedIterableCopySpecification, thm := some ``countedIterableCopySpecification_proven },
  { id := "multidimcov-abstract-l1003-copy-count", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@1003"]
    statement := "Negative integer counts reject and zero count leaves the entire computation unchanged before metadata access, offset validation, conversion, or iteration, for arbitrary count representations and effect types satisfying the documented integer comparison laws."
    source := "base/abstractarray.jl:1003-1037 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CountedIterableCopyGenericEarlyExits, thm := some ``countedIterableCopyGenericEarlyExits_proven },
  { id := "abstractarrayspecs-copyto-iter-from", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@974"]
    statement := "For every native destination index and well-formed native destination axis, iterable suffix copying rejects unavailable source offsets, throws BoundsError exactly when the requested nonempty suffix does not fit the destination, and otherwise copies every suffix element in order while preserving all other cells."
    source := "base/abstractarray.jl:974-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IterableCopyFromBoundsAndContents, thm := some ``iterableCopyFromBoundsAndContents_proven },
  { id := "abstractarrays-source-iterable-copy-from-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@974"]
    statement := "Copying an iterable suffix rejects nonpositive or unavailable source offsets before converting the destination index; otherwise conversion errors propagate, an out-of-bounds destination write throws BoundsError, and successful writes copy the complete suffix in order while preserving every other cell."
    source := "base/abstractarray.jl:974-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IterableCopyFromContents, thm := some ``iterableCopyFromContents_proven },
  { id := "abstractarrays-source-iterable-copy-at-unknown-length", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@953"]
    statement := "An unknown-length iterable copies all values into consecutive native positions through the checked scalar writer and preserves other cells; conversion failures propagate before any iteration or destination metadata access, for both length traits."
    source := "base/abstractarray.jl:953-971 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IterableCopyAtUnknownLength, thm := some ``iterableCopyAtUnknownLength_proven },
  { id := "abstractarrays-source-iterable-copy-at-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!@953", "lastindex@429", "eachindex@396", "axes1@141"]
    statement := "A sized iterable copied into a positive-length destination at a checked, sufficiently large linear block writes every source element to its consecutive native position and preserves all other cells, for arbitrary promoted endpoint arithmetic and lawful canonical scalar storage."
    source := "base/abstractarray.jl:141,396,429,953-971 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IterableCopyAtContents, thm := some ``iterableCopyAtContents_proven },
  { id := "abstractarrays-source-vector-copy-resize-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copy!@920", "firstindex@452", "eachindex@396", "axes1@141"]
    statement := "Vector copy! rejects unequal starting indices before copying; for equal offsets it copies all source contents and returns the same destination with source length after the optional successful resize, leaving cells outside the copied destination unchanged relative to the resized storage."
    source := "base/abstractarray.jl:141,396,452,920-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``VectorCopyResizeContents, thm := some ``vectorCopyResizeContents_proven },
  { id := "abstractarrays-source-linear-indices-bounds-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex@759", "isempty@1262", "axes1@141", "checkindex@751"]
    statement := "LinearIndices-valued indexing is in bounds exactly when every linear index lies within the outer axis, using the source first/last LinearIndices methods and the documented contiguous-range endpoint and emptiness laws."
    source := "base/abstractarray.jl:141,751,759-760,1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LinearIndicesBoundsContents, thm := some ``linearIndicesBoundsContents_proven },
  { id := "abstractarrays-checkbounds-linear", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds@690", "eachindex@395", "eachindex@396", "axes1@141", "checkindex@751", "checkindex@753"]
    statement := "A scalar integer index is valid precisely between a vector's actual offset endpoints; for a nonvector linear-indexed array it is valid precisely from one through the array's nonnegative element count, using native OneTo bounds at every Int64 extremum."
    source := "base/abstractarray.jl:141,395-396,690-693,751-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LinearBoundsCoordinates, thm := some ``linearBoundsCoordinates_proven },
  { id := "abstractarrays-source-oneto-bounds-all-widths", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex@753"]
    statement := "For every signed and unsigned native integer width, OneTo bounds accept exactly the mathematical integer positions from one through the nonnegative upper endpoint, including zero-length ranges and native extrema."
    source := "base/abstractarray.jl:753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``OneToBoundsAllWidths, thm := some ``oneToBoundsAllWidths_proven },
  { id := "abstractarrays-source-array-index-bounds-all", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex@762", "checkindex@751"]
    statement := "Array-valued numeric indices pass bounds validation exactly when every element lies between the range's endpoints, including empty index arrays and arbitrary integer-valued scalar types."
    source := "base/abstractarray.jl:751,762-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ArrayIndexBoundsAll, thm := some ``arrayIndexBoundsAll_proven },
  { id := "abstractarrays-source-trailing-dimension-products", juliaFile := "base/abstractarray.jl"
    juliaFns := ["trailingsize@619", "trailingsize@626", "trailingsize@634", "size@42", "ndims@278"]
    statement := "Trailing array sizes and trailing index-axis lengths equal the mathematical product of all selected dimension lengths reduced to the native integer range, including the empty product one; the first failed dimension or axis read propagates."
    source := "base/abstractarray.jl:42-46,278,619-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TrailingDimensionProducts, thm := some ``trailingDimensionProducts_proven },
  { id := "abstractarrays-source-canonical-stored-coordinates", juliaFile := "base/abstractarray.jl"
    juliaFns := ["isstored@613", "checkbounds@682", "checkbounds_indices@722", "checkbounds_indices@728", "checkindex@751"]
    statement := "For a canonical AbstractArray with exactly its rank's integer coordinates, every independently in-bounds coordinate is stored and every out-of-bounds coordinate throws BoundsError, through the actual throwing checkbounds definition from essentials.jl."
    source := "base/abstractarray.jl:613-616,682-685,722-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CanonicalStoredCoordinates, thm := some ``canonicalStoredCoordinates_proven },
  { id := "abstractarrays-source-stride-prefix-positions", juliaFile := "base/abstractarray.jl"
    juliaFns := ["size_to_strides@609", "size_to_strides@610", "size_to_strides@611"]
    statement := "The stride tuple has exactly one entry per dimension, and entry k is the product accumulated from exactly the preceding k dimension factors in source arithmetic order, for every typed accumulator and factor multiplication."
    source := "base/abstractarray.jl:609-611 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``StridePrefixPositions, thm := some ``stridePrefixPositions_proven },
  { id := "abstractarrays-source-bounds-interface-rejections", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex@750", "throw_eachindex_mismatch_indices@331"]
    statement := "Unsupported scalar bounds types never produce a bounds result and reject with ArgumentError; an eachindex index mismatch never returns an index range and rejects with DimensionMismatch."
    source := "base/abstractarray.jl:331-335,750 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnsupportedBoundsRejected, thm := some ``unsupportedBoundsRejected_proven },
  { id := "abstractarrays-similar-fallback", juliaFile := "base/abstractarray.jl"
    juliaFns := ["similar@821", "similar@822", "similar@823", "similar@834"]
    statement := "The generic native-dimension similar fallbacks preserve the requested dimensions and element type when the external Array constructor succeeds, and propagate its allocation errors unchanged."
    source := "base/abstractarray.jl:821-834 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``SimilarFallbackAllocation, thm := some ``similarFallbackAllocation_proven },
  { id := "abstractarrays-source-empty-allocation-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["empty@892", "emptymutable@895", "emptymutable@896"]
    statement := "When their external constructors succeed, empty array constructors produce zero-length vectors at the requested element type with no assigned entries; allocation errors propagate unchanged."
    source := "base/abstractarray.jl:892-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``EmptyAllocationContents, thm := some ``emptyAllocationContents_proven },
  { id := "abstractarrays-source-tuple-offset-detection", juliaFile := "base/abstractarray.jl"
    juliaFns := ["has_offset_axes@114", "has_offset_axes@115", "has_offset_axes@122"]
    statement := "Offset detection over every tuple of arrays is false exactly when every axis begins at one and true exactly when some input axis begins elsewhere."
    source := "base/abstractarray.jl:114-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TupleOffsetDetection, thm := some ``tupleOffsetDetection_proven },
  { id := "abstractarrays-source-neighbor-index-positions", juliaFile := "base/abstractarray.jl"
    juliaFns := ["prevind@219", "nextind@220"]
    statement := "Neighbor indices have the preceding and succeeding mathematical integer positions whenever representable; failed conversion to the native index type propagates unchanged."
    source := "base/abstractarray.jl:219-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``NeighborIndexPositions, thm := some ``neighborIndexPositions_proven },
  { id := "abstractarrays-source-bottom-metadata-rejected", juliaFile := "base/abstractarray.jl"
    juliaFns := ["eltype@244", "ndims@280"]
    statement := "The uninhabited Union{} type has no successful element-type or rank query; both reject with ArgumentError."
    source := "base/abstractarray.jl:244,280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``BottomArrayMetadataRejected, thm := some ``bottomArrayMetadataRejected_proven },
  { id := "abstractarrays-source-last-iterator-suffix", juliaFile := "base/abstractarray.jl"
    juliaFns := ["last@555"]
    statement := "With the iterator reverse, take, collection and in-place reversal content interfaces, last(itr,n) preserves original element order and returns the complete clipped suffix for every nonnegative native count."
    source := "base/abstractarray.jl:555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LastIteratorSuffix, thm := some ``lastIteratorSuffix_proven },
  { id := "abstractarrays-stride-trailing-dimension", juliaFile := "base/abstractarray.jl"
    juliaFns := ["stride@597", "ndims@278"]
    statement := "For a contiguous column-major two-dimensional AbstractArray, the stride of a trailing singleton dimension equals its element count."
    source := "base/abstractarray.jl:278,597-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``TrailingStrideContiguous, thm := some ``trailingStrideContiguous_refuted
    issue := "#58403" },
  { id := "abstractarrays-source-typed-vcat-vector-blocks", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_vcat!@1744", "setindex!@1464"]
    statement := "Typed vector filling places every source vector into its consecutive destination slice in input order, computes every slice endpoint from cumulative element counts using native arithmetic, and returns the supplied destination."
    source := "base/abstractarray.jl:1464-1468,1744-1753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TypedVcatVectorBlocks,
    thm := some ``typedVcatVectorBlocks_proven },
  { id := "abstractarrays-source-typed-vcat-vector-allocation", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_vcat@1741", "_typed_vcat_similar@1740", "map@3491", "similar@823", "similar@834"]
    statement := "Nonempty typed vector concatenation requests the native sum of all input lengths at the requested element type, propagates allocation failures, and fills all consecutive slices with the original vector payloads."
    source := "base/abstractarray.jl:823,834,1740-1753,3491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TypedVcatVectorAllocation,
    thm := some ``typedVcatVectorAllocation_proven },
  { id := "abstractarrays-source-linear-iteration-positions", juliaFile := "base/abstractarray.jl"
    juliaFns := ["axes1@141", "eachindex@396", "firstindex@452", "iterate_starting_state@1245", "iterate_starting_state@1246", "iterate@1250", "_iterate_abstractarray@1256", "checkbounds@690"]
    statement := "Linear iteration starts at the first axis index, visits the element at each nonnegative zero-based axis position, advances by one with native wrapping, and terminates outside the axis."
    source := "base/abstractarray.jl:141,396,452,690-693,1245-1246,1250,1256-1259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LinearIterationPositions,
    thm := some ``linearIterationPositions_proven },
  { id := "abstractarrays-source-cartesian-iteration-order", juliaFile := "base/abstractarray.jl"
    juliaFns := ["eachindex@384", "iterate_starting_state@1245", "iterate_starting_state@1247", "iterate@1250", "_iterate_abstractarray@1251"]
    statement := "Starting and repeatedly advancing Cartesian array iteration yields exactly the elements at its typed index sequence in order and propagates the first failed read, for every sufficient collection step count with no upper bound."
    source := "base/abstractarray.jl:384,1245-1247,1250-1255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CartesianIterationOrder,
    thm := some ``cartesianIterationOrder_proven },
  { id := "abstractarrays-source-unitrange-zero-index", juliaFile := "base/abstractarray.jl"
    juliaFns := ["getindex@1363", "_getindex@1392", "_to_linear_index@1400", "get@1638", "setindex!@1464", "_setindex!@1487"]
    statement := "A singleton IndexLinear vector with native UnitRange axes selects its sole element for zero-index reads, defaulted reads, and supported writes."
    source := "base/abstractarray.jl:1363-1367,1392-1400,1464-1468,1487-1492,1638; base/indices.jl:483-486,506,527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``NativeUnitRangeLinearZeroPromise,
    thm := some ``nativeUnitRangeLinearZeroPromise_refuted,
    issue := "none found (same root as abstractarrayspecs-linear-zero-unitrange)" },
  { id := "abstractarrays-checkbounds-cartesian", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds@682", "checkbounds_indices@722", "checkbounds_indices@728", "checkindex@751"]
    statement := "Cartesian scalar bounds consume axes in order for arbitrary integer-valued scalar types, require omitted dimensions to be singleton, and accept extra coordinates exactly at one."
    source := "base/abstractarray.jl:682-685,722-728,751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CartesianCoordinateBounds, thm := some ``cartesianCoordinateBounds_proven },
  { id := "abstractarrays-checkindex-forms", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex@751", "checkindex@754", "checkindex@756"]
    statement := "Integer scalar bounds require both endpoints; Colon always passes; a range passes exactly when empty or both endpoints lie in bounds."
    source := "base/abstractarray.jl:751-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CheckIndexForms, thm := some ``checkIndexForms_proven },
  { id := "abstractarrayspecs-eachindex-size-mismatch", juliaFile := "base/abstractarray.jl"
    juliaFns := ["eachindex@386", "eachindex@394", "eachindex@397"]
    statement := "Joint eachindex rejects two arrays with different shapes, even when their total lengths agree."
    source := "base/abstractarray.jl:356-360,386-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``EachindexSizeMismatch, thm := some ``eachindexSizeMismatch_refuted
    issue := "none found (retained reproducer)" },
  { id := "abstractarrayspecs-map2", juliaFile := "base/abstractarray.jl"
    juliaFns := ["map!@3527"]
    statement := "Binary map! writes f of the paired source values to each destination iteration index, stops at the shortest input, and propagates mapping failures."
    source := "base/abstractarray.jl:3527-3534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``MapTwoContents, thm := some ``mapTwoContents_proven },
  { id := "abstractarrayspecs-map-inplace", juliaFile := "base/abstractarray.jl"
    juliaFns := ["map!@3618", "map!@3482"]
    statement := "In-place unary mapping writes f of each element at the same iteration index and propagates mapping failures."
    source := "base/abstractarray.jl:3618-3618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``MapInplaceContents, thm := some ``mapInplaceContents_proven },
  { id := "abstractarrayspecs-map-bang", juliaFile := "base/abstractarray.jl"
    juliaFns := ["map!@3482", "setindex!@1464"]
    statement := "Unary map! writes exactly the mapped source values to the corresponding destination iteration indices, stops at the shorter index sequence, and propagates mapping failures."
    source := "base/abstractarray.jl:3482-3488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``MapOneContents, thm := some ``mapOneContents_proven },
  { id := "iterators-first-last-vector", juliaFile := "base/abstractarray.jl"
    juliaFns := ["first@507", "last@557", "firstindex@452", "lastindex@429"]
    statement := "For every integer count type and lawful vector, first and last return the requested clipped prefix and suffix, and negative counts reject before slicing."
    source := "base/abstractarray.jl:507-510,557-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``FirstLastVectorContents, thm := some ``firstLastVectorContents_proven },
  { id := "abstractarrayspecs-isequal", juliaFile := "base/abstractarray.jl"
    juliaFns := ["isequal@3106"]
    statement := "For lawful arrays, isequal is true exactly when axes agree and their elements are pairwise isequal in iteration order; object identity short-circuits consistently with isequal reflexivity."
    source := "base/abstractarray.jl:3106-3117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ArrayIsequalContents, thm := some ``arrayIsequalContents_proven },
  { id := "abstractarrayspecs-eq", juliaFile := "base/abstractarray.jl"
    juliaFns := ["==@3149"]
    statement := "Array equality is false for differing axes; otherwise any false element comparison wins, then missing, then true, for all element comparisons and axes."
    source := "base/abstractarray.jl:3149-3163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ArrayEqualityContents, thm := some ``arrayEqualityContents_proven },
  { id := "iterators-first-n-tuple", juliaFile := "base/abstractarray.jl"
    juliaFns := ["first@505"]
    statement := "For every nonnegative native integer count, first of a finite tuple collects exactly its first min(n,length) elements, with no execution-fuel restriction."
    source := "base/abstractarray.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``FirstNTupleContents, thm := some ``firstNTupleContents_proven },
  { id := "abstractarrayspecs-length-isempty", juliaFile := "base/abstractarray.jl"
    juliaFns := ["isempty@1262"]
    statement := "For every lawful array, the documented length interface agrees with its element count, and isempty is true exactly when no elements exist."
    source := "base/abstractarray.jl:306-319,1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LengthIsemptyCount, thm := some ``lengthIsemptyCount_proven },
  { id := "abstractarrayspecs-ith-all", juliaFile := "base/abstractarray.jl"
    juliaFns := ["ith_all@3538", "ith_all@3539"]
    statement := "Tuple element gathering preserves every array's scalar element in tuple order, and propagates the first reader failure without reading later arrays."
    source := "base/abstractarray.jl:3538-3542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IthAllContents, thm := some ``ithAllContents_proven },
  { id := "abstractarrays-source-foreach-order", juliaFile := "base/abstractarray.jl"
    juliaFns := ["foreach@3307"]
    statement := "foreach calls its function once per finite input element in iteration order and returns nothing."
    source := "base/abstractarray.jl:3307-3307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ForeachIterationOrder, thm := some ``foreachIterationOrder_proven },
  { id := "abstractarrays-source-foreach-zip-order", juliaFile := "base/abstractarray.jl"
    juliaFns := ["foreach@3308"]
    statement := "Multiple-input foreach visits zipped argument pairs in order, stopping at the shorter input, and returns nothing."
    source := "base/abstractarray.jl:3308-3308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ForeachZipIterationOrder, thm := some ``foreachZipIterationOrder_proven },
  { id := "abstractarrays-source-map-unsupported", juliaFile := "base/abstractarray.jl"
    juliaFns := ["map@3523", "map@3524"]
    statement := "Mapping dictionaries or sets raises ErrorException for every function and collection."
    source := "base/abstractarray.jl:3523-3524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnsupportedMapRejected, thm := some ``unsupportedMapRejected_proven },
  { id := "abstractarrays-source-stack-empty", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_empty_stack@3101"]
    statement := "The empty stack path rejects every collection with ArgumentError."
    source := "base/abstractarray.jl:3101-3101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``EmptyStackRejected, thm := some ``emptyStackRejected_proven },
  { id := "abstractarrays-source-native-index-arithmetic", juliaFile := "base/abstractarray.jl"
    juliaFns := ["nextL@3204", "nextL@3206", "offsetin@3207"]
    statement := "Representable native index arithmetic multiplies a stride by the dimension length and converts a one-based integer coordinate to its zero-based offset exactly."
    source := "base/abstractarray.jl:3204-3207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``NativeIndexArithmetic, thm := some ``nativeIndexArithmetic_proven },
  { id := "abstractarrays-source-empty-rank-singletons", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_sub2ind@3181", "_sub2ind_recurse@3194", "_sub2ind_recurse@3193"]
    statement := "Every number of trailing singleton coordinates on a zero-dimensional array maps to linear position one."
    source := "base/abstractarray.jl:3181-3197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``EmptyRankExtraSingletons, thm := some ``emptyRankExtraSingletons_proven },
  { id := "abstractarrays-source-generated-row-fill-values", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvncat_fill!@2556"]
    statement := "For every generated tuple of at most 32 fields and every rank, valid row-first filling writes every scalar once in tuple order, including transitions between planes."
    source := "base/abstractarray.jl:2556-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``GeneratedRowFillValues, thm := some ``generatedRowFillValues_proven },
  { id := "abstractarrays-source-generated-fill-order", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvncat_fill!@2556"]
    statement := "For every generated tuple of at most 32 fields and every rank, valid column-first filling writes each scalar once at consecutive linear indices in tuple order."
    source := "base/abstractarray.jl:2556-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``GeneratedColumnFillOrder, thm := some ``generatedColumnFillOrder_proven },
  { id := "abstractarrays-source-generated-fill-shape-error", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvncat_fill!@2556"]
    statement := "For both generated fill orders and all ranks, a field count different from the allocated array length raises ArgumentError before writes."
    source := "base/abstractarray.jl:2556-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``GeneratedFillRejectsShape, thm := some ``generatedFillRejectsShape_proven },
  { id := "abstractarrayspecs-hvncat-zero-d-eltype", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hvncat@2398"]
    statement := "Zero-dimensional typed scalar concatenation stores its converted value in one cell with the requested storage element type and propagates conversion errors."
    source := "base/abstractarray.jl:2398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``ZeroDimScalarFull, thm := some ``zeroDimScalarFull_refuted
    issue := "none found (retained searches in existing bug report)" },
  { id := "abstractarrayspecs-hvncat-row2399", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hvncat@2399"]
    statement := "Zero-dimensional typed numeric concatenation stores its converted value with the requested element type, including abstract target types, and propagates conversion errors."
    source := "base/abstractarray.jl:2399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``ZeroDimNumberFull, thm := some ``zeroDimNumberFull_refuted
    issue := "none found (retained searches in existing bug report)" },
  { id := "abstractarrays-source-hvncat-zero-concrete", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hvncat@2398", "_typed_hvncat@2399"]
    statement := "When conversion produces the requested concrete type, zero-dimensional scalar and numeric concatenation preserve that storage type and the sole converted value."
    source := "base/abstractarray.jl:2398-2399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ZeroDimConcreteContents, thm := some ``zeroDimConcreteContents_proven },
  { id := "abstractarrays-source-hvncat-zero-count", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hvncat@2397", "_typed_hvncat@2401", "_typed_hvncat@2402",
      "_typed_hvncat@2403", "_typed_hvncat_0d_only_one@2405"]
    statement := "Every zero-dimensional overload for zero or multiple supplied elements raises ArgumentError."
    source := "base/abstractarray.jl:2397-2406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ZeroDimWrongCountRejected, thm := some ``zeroDimWrongCountRejected_proven },
  { id := "abstractarrayspecs-hvncat-row2411", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hvncat@2411"]
    statement := "Negative ranks raise ArgumentError; a positive empty concatenation has the requested element type, N zero extents, and no cells under the Array constructor contract."
    source := "base/abstractarray.jl:2411-2415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``HvnEmptyRankSpec, thm := some ``hvnEmptyRankSpec_proven },
  { id := "abstractarrayspecs-hvncat-row2417", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hvncat@2417"]
    statement := "Negative ranks raise ArgumentError; positive-rank numeric concatenation preserves converted tuple order and storage type in shape (1,...,1,length(xs)) under the typed constructor and reshape contracts."
    source := "base/abstractarray.jl:2417-2421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``HvnNumbersRankSpec, thm := some ``hvnNumbersRankSpec_proven },
  { id := "multidim-hvcat-row-mismatch", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvcat@2253", "typed_hvcat@2279"]
    statement := "Homogeneous numeric hvcat and explicitly typed numeric hvcat agree on whether an error occurs and on its exception class."
    source := "base/abstractarray.jl:2253-2290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``HvcatNumbersErrorAgreement, thm := some ``hvcatNumbersErrorAgreement_refuted
    issue := "none found (retained searches in existing bug report)" },
  { id := "multidim-hvcat-zero-columns", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvcat@2197"]
    statement := "For a nonempty value tuple, a nonpositive requested column count raises ArgumentError."
    source := "base/abstractarray.jl:2197-2204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``HvcatNonpositiveColumns, thm := some ``hvcatNonpositiveColumns_refuted
    issue := "none found (retained searches in existing bug report)" },
  { id := "abstractarrays-source-row-shape-preserves-rows", juliaFile := "base/abstractarray.jl"
    juliaFns := ["rows_to_dimshape@2247"]
    statement := "Decoding either rectangular or ragged dimension-shape output recovers every original row width in order."
    source := "base/abstractarray.jl:2247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``RowShapePreservesRows, thm := some ``rowShapePreservesRows_proven },
  { id := "abstractarrays-source-hvcat-empty-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hvcat@2250", "typed_hvcat@2251"]
    statement := "With the external vector constructors' empty-storage laws, zero-value hvcat and typed_hvcat both return empty contents."
    source := "base/abstractarray.jl:2250-2251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``HvcatEmptyContents, thm := some ``hvcatEmptyContents_proven },
  { id := "abstractarrayspecs-cat-row1905-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_cat@1905"]
    statement := "On ordinary one-based inputs, _cat checks non-cat dimensions and preserves the requested concatenation contents."
    source := "base/abstractarray.jl:1905 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow1905Ordinary, thm := some ``catRow1905Ordinary_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row1918-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_t@1918"]
    statement := "On ordinary one-based inputs, cat_t checks non-cat dimensions and preserves converted concatenation contents."
    source := "base/abstractarray.jl:1918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow1918Ordinary, thm := some ``catRow1918Ordinary_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row2003-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@2003"]
    statement := "On ordinary one-based inputs, generic vcat rejects unequal non-cat dimensions and preserves vertical element order."
    source := "base/abstractarray.jl:2003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2003Ordinary, thm := some ``catRow2003Ordinary_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row2055-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_vcat@2055"]
    statement := "On ordinary one-based inputs, generic typed_vcat rejects unequal non-cat dimensions and preserves converted elements."
    source := "base/abstractarray.jl:2055 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2055Ordinary, thm := some ``catRow2055Ordinary_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row2176-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@2176"]
    statement := "On ordinary one-based inputs, two-array vcat rejects unequal non-cat dimensions and preserves vertical contents."
    source := "base/abstractarray.jl:2176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2176Ordinary, thm := some ``catRow2176Ordinary_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row2185-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_vcat@2185"]
    statement := "On ordinary one-based inputs, two-array typed_vcat rejects unequal non-cat dimensions and preserves converted contents."
    source := "base/abstractarray.jl:2185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2185Ordinary, thm := some ``catRow2185Ordinary_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row1921", juliaFile := "base/abstractarray.jl"
    juliaFns := ["__cat@1921", "__cat_offset!@1923", "__cat_offset1!@1930"]
    statement := "Preallocated concatenation writes each converted argument into its next positional block and preserves every cell outside those blocks."
    source := "base/abstractarray.jl:1921-1939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatInnerComplete, thm := some ``catInnerComplete_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-offset-axes", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat@2169", "_cat@1905", "_cat_t@1907", "__cat_offset1!@1930"]
    statement := "Concatenation preserves positional shape and contents independently of input axis origins."
    source := "base/abstractarray.jl:1905-2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatPublicComplete, thm := some ``catPublicComplete_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row1918", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_t@1918"]
    statement := "cat_t checks all non-cat dimensions and concatenates converted elements positionally for arbitrary dimension lists, with zero outside diagonal blocks."
    source := "base/abstractarray.jl:1918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow1918, thm := some ``catRow1918_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2003", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@2003"]
    statement := "Generic vcat preserves argument elements in vertical order and checks all other dimension sizes."
    source := "base/abstractarray.jl:2003 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2003, thm := some ``catRow2003_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2053", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hcat@2053"]
    statement := "Generic hcat preserves argument elements in horizontal order and checks all other dimension sizes."
    source := "base/abstractarray.jl:2053 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2053, thm := some ``catRow2053_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2055", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_vcat@2055"]
    statement := "Generic typed_vcat converts and places elements vertically, checking non-cat dimensions."
    source := "base/abstractarray.jl:2055 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2055, thm := some ``catRow2055_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2056", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_hcat@2056"]
    statement := "Generic typed_hcat converts and places elements horizontally, checking non-cat dimensions."
    source := "base/abstractarray.jl:2056 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2056, thm := some ``catRow2056_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2175", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@2175"]
    statement := "One-array vcat preserves every input element in a fresh one-based array of the same shape."
    source := "base/abstractarray.jl:2175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2175, thm := some ``catRow2175_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2176", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@2176"]
    statement := "Two-array vcat stacks elements vertically, independently of axis origins, and checks other sizes."
    source := "base/abstractarray.jl:2176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2176, thm := some ``catRow2176_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2177", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@2177"]
    statement := "Array-varargs vcat stacks input elements vertically and checks non-cat dimensions."
    source := "base/abstractarray.jl:2177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2177, thm := some ``catRow2177_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2178", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@2178"]
    statement := "Mixed array-and-number vcat stacks elements vertically and checks non-cat dimensions."
    source := "base/abstractarray.jl:2178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2178, thm := some ``catRow2178_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2179", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hcat@2179"]
    statement := "One-array hcat preserves every element and pads a missing second dimension with a singleton."
    source := "base/abstractarray.jl:2179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2179, thm := some ``catRow2179_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2180", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hcat@2180"]
    statement := "Two-array hcat places the second input after the first along dimension two and checks other sizes."
    source := "base/abstractarray.jl:2180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2180, thm := some ``catRow2180_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2181", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hcat@2181"]
    statement := "Array-varargs hcat places elements horizontally and checks non-cat dimensions."
    source := "base/abstractarray.jl:2181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2181, thm := some ``catRow2181_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2182", juliaFile := "base/abstractarray.jl"
    juliaFns := ["hcat@2182"]
    statement := "Mixed array-and-number hcat places elements horizontally and checks non-cat dimensions."
    source := "base/abstractarray.jl:2182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2182, thm := some ``catRow2182_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2184", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_vcat@2184"]
    statement := "One-array typed_vcat preserves shape and writes every converted element positionally."
    source := "base/abstractarray.jl:2184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2184, thm := some ``catRow2184_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2185", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_vcat@2185"]
    statement := "Two-array typed_vcat converts and stacks elements vertically, checking all other sizes."
    source := "base/abstractarray.jl:2185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2185, thm := some ``catRow2185_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2186", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_vcat@2186"]
    statement := "Array-varargs typed_vcat converts and stacks elements vertically, checking non-cat dimensions."
    source := "base/abstractarray.jl:2186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2186, thm := some ``catRow2186_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2187", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_hcat@2187"]
    statement := "One-array typed_hcat writes every converted element and pads a missing second dimension."
    source := "base/abstractarray.jl:2187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2187, thm := some ``catRow2187_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2188", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_hcat@2188"]
    statement := "Two-array typed_hcat converts and places elements horizontally, checking all other sizes."
    source := "base/abstractarray.jl:2188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2188, thm := some ``catRow2188_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrayspecs-cat-row2189", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_hcat@2189"]
    statement := "Array-varargs typed_hcat converts and places elements horizontally, checking non-cat dimensions."
    source := "base/abstractarray.jl:2189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatRow2189, thm := some ``catRow2189_refuted
    issue := "none found (retained offset-axis bug searches)" },
  { id := "abstractarrays-source-cat-public-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat@2169"]
    statement := "Public cat checks non-cat dimensions, writes argument blocks consecutively along every requested dimension, and zeroes off-block cells."
    source := "base/abstractarray.jl:2169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatPublicComplete, thm := some ``catPublicComplete_refuted
    issue := "none found (same retained offset-axis defect)" },
  { id := "abstractarrays-source-cat-same-array-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_cat@2171"]
    statement := "Same-element-type array concatenation preserves every element and dimension invariant independently of axis origins."
    source := "base/abstractarray.jl:2171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatSameArraysComplete, thm := some ``catSameArraysComplete_refuted
    issue := "none found (same retained offset-axis defect)" },
  { id := "abstractarrays-source-subscript-first-position", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_sub2ind@3185", "_sub2ind_recurse@3193", "_sub2ind_recurse@3198",
      "nextL@3205", "offsetin@3208"]
    statement := "The first coordinate of every native unit-range axis maps to linear position one, including offset axes and wrapped intermediate strides."
    source := "base/abstractarray.jl:3185-3208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``SubscriptFirstPosition, thm := some ``subscriptFirstPosition_proven },
  { id := "abstractarrays-source-ambiguous-linear-index", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_sub2ind@3188"]
    statement := "A one-dimensional axis that is not OneTo rejects ambiguous linear indexing with ArgumentError."
    source := "base/abstractarray.jl:3188-3189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``AmbiguousLinearIndexRejected, thm := some ``ambiguousLinearIndexRejected_proven },
  { id := "abstractarrayspecs-cat-row1905", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_cat@1905", "_cat_t@1907", "__cat@1921", "__cat_offset!@1923",
      "__cat_offset!@1928", "__cat_offset1!@1930", "_copy_or_fill!@1941", "_copy_or_fill!@1942"]
    statement := "Concatenation checks non-cat dimensions, places converted elements consecutively by position regardless of input axis origins, and fills off-block cells with zero."
    source := "base/abstractarray.jl:1905-1942 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatPromoteComplete, thm := some ``catPromoteComplete_refuted
    issue := "none found (retained searches in abstractarrayspecs-cat-offset-axes)" },
  { id := "abstractarrays-source-cat-size-shape-entry", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_size_shape@1868"]
    statement := "The entry shape calculation sums cat dimensions and checks all others with omitted dimensions treated as singleton."
    source := "base/abstractarray.jl:1868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatSizeShapeEntrySpec, thm := some ``catSizeShapeEntrySpec_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row1859", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_shape@1859"]
    statement := "cat_shape adds concatenated coordinates and checks other coordinates, with singleton padding for omitted dimensions."
    source := "base/abstractarray.jl:1859-1865 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatShapeSpec, thm := some ``catShapeSpec_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrayspecs-cat-row1870", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_cat_size_shape@1870", "_cat_size_shape@1869"]
    statement := "The running shape and remaining arrays obey coordinatewise concatenation with singleton padding and non-concatenated dimension checks."
    source := "base/abstractarray.jl:1869-1870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatSizeShapeFromSpec, thm := some ``catSizeShapeFromSpec_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrays-source-empty-concat-shape", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_size_shape@1867"]
    statement := "An empty concatenation has one zero extent per dimension-mask coordinate."
    source := "base/abstractarray.jl:1867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``EmptyConcatShapeZeros, thm := some ``emptyConcatShapeZeros_proven },
  { id := "abstractarrayspecs-cat-row1837", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_size@1837", "cat_length@1842", "cat_ndims@1845"]
    statement := "Concatenation metadata agrees with axis cardinalities, element count and rank for lawful external size and length interfaces."
    source := "base/abstractarray.jl:1837-1845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CatMetadataInvariants, thm := some ``catMetadataInvariants_proven },
  { id := "abstractarrayspecs-cat-row1842", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_length@1842"]
    statement := "Concatenation element count equals the number of stored values."
    source := "base/abstractarray.jl:1842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CatMetadataInvariants, thm := some ``catMetadataInvariants_proven },
  { id := "abstractarrayspecs-cat-row1845", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_ndims@1845", "ndims@278"]
    statement := "Concatenation rank equals the number of independent axes."
    source := "base/abstractarray.jl:1845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CatMetadataInvariants, thm := some ``catMetadataInvariants_proven },
  { id := "abstractarrayspecs-cat-row1850", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_similar@1850", "cat_similar@1851", "cat_similar@1852", "cat_similar@1853"]
    statement := "Tuple and vector shape allocation preserves the requested dimensions and cell count and rejects negative dimensions."
    source := "base/abstractarray.jl:1850-1853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CatSimilarAllocationShapes, thm := some ``catSimilarAllocationShapes_proven },
  { id := "abstractarrayspecs-cat-row1851", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_similar@1851"]
    statement := "Vector shape allocation preserves the requested dimensions and cell count and rejects negative dimensions."
    source := "base/abstractarray.jl:1851 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CatSimilarAllocationShapes, thm := some ``catSimilarAllocationShapes_proven },
  { id := "abstractarrayspecs-cat-row1852", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_similar@1852"]
    statement := "An Array exemplar with tuple shape preserves the requested dimensions and cell count and rejects negative dimensions."
    source := "base/abstractarray.jl:1852 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CatSimilarAllocationShapes, thm := some ``catSimilarAllocationShapes_proven },
  { id := "abstractarrayspecs-cat-row1853", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_similar@1853"]
    statement := "An Array exemplar with vector shape preserves the requested dimensions and cell count and rejects negative dimensions."
    source := "base/abstractarray.jl:1853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CatSimilarAllocationShapes, thm := some ``catSimilarAllocationShapes_proven },
  { id := "abstractarrayspecs-cat-row1839", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_size@1839", "size@42"]
    statement := "For every positive integer dimension, cat_size returns the explicit dimension or a trailing singleton."
    source := "base/abstractarray.jl:1839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatSizeAllIntegerSpec, thm := some ``catSizeAllIntegerSpec_refuted
    issue := "none found (inherited size-conversion bug)" },
  { id := "abstractarrayspecs-cat-similar-empty-vector", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_similar@1855", "similar@820", "similar@823", "similar@829",
      "similar@834", "axes@100", "to_shape@838", "to_shape@842", "to_shape@840"]
    statement := "An AbstractArray exemplar and vector shape allocate exactly that shape, including rank zero for an empty vector."
    source := "base/abstractarray.jl:1855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatSimilarAbsVectorSpec, thm := some ``catSimilarAbsVectorSpec_refuted
    issue := "none found (inherited empty-shape bug)" },
  { id := "abstractarrayspecs-cat-row1897", juliaFile := "base/abstractarray.jl"
    juliaFns := ["dims2cat@1897", "dims2cat@1898"]
    statement := "Positive concatenation dimensions produce exactly their membership mask through the largest requested dimension, through the Val wrapper."
    source := "base/abstractarray.jl:1897-1903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``Dims2catValSpec, thm := some ``dims2catValSpec_proven },
  { id := "multidim-cat-scalar-shape", juliaFile := "base/abstractarray.jl"
    juliaFns := ["cat_shape@1859", "_cshp@1877"]
    statement := "Along dimensions excluded from concatenation, every input shape, including scalar singleton dimensions, agrees with the result."
    source := "base/abstractarray.jl:1836-1892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CatShapeChecked, thm := some ``catShapeChecked_refuted
    issue := "#38019 (open duplicate), #48468 (closed duplicate)" },
  { id := "abstractarrays-source-concat-shape-rank", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_cshp@1872", "_cshp@1873", "_cshp@1874", "_cshp@1875",
      "_cshp@1877", "_cshp@1879", "_cshp@1883", "_cshp@1887"]
    statement := "A successful concatenation shape has exactly the maximum rank of the dimension mask and the two input shapes."
    source := "base/abstractarray.jl:1872-1892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ConcatShapeRank, thm := some ``concatShapeRank_proven },
  { id := "abstractarrays-source-concat-shape-mismatch", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_cshp@1887", "_cs@1894"]
    statement := "Unequal sizes outside the concatenation dimensions raise DimensionMismatch before later coordinates are examined."
    source := "base/abstractarray.jl:1887-1895 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ConcatShapeMismatch, thm := some ``concatShapeMismatch_proven },
  { id := "abstractarrays-source-invalid-cat-dimensions", juliaFile := "base/abstractarray.jl"
    juliaFns := ["dims2cat@1898"]
    statement := "A concatenation dimension tuple containing zero or a negative dimension raises ArgumentError."
    source := "base/abstractarray.jl:1898-1903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``InvalidCatDimensions, thm := some ``invalidCatDimensions_proven },
  { id := "abstractarrays-source-concat-dimension-mismatch", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_typed_hcat@1768", "_typed_vcat@1805"]
    statement := "Dense horizontal and vertical concatenation reject a differing second block's row or column count before allocating the result."
    source := "base/abstractarray.jl:1768-1823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ConcatMismatchRejected, thm := some ``concatMismatchRejected_proven },
  { id := "abstractarrays-source-empty-typed-concat", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_vcat@1699", "typed_hcat@1700"]
    statement := "Both empty typed concatenations return a vector with no elements for every element type."
    source := "base/abstractarray.jl:1699-1700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TypedEmptyContents, thm := some ``typedEmptyContents_proven },
  { id := "abstractarrays-source-scalar-comprehension-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@1703", "vcat@1704", "hcat@1705", "hcat@1706"]
    statement := "Homogeneous scalar concatenation preserves tuple order; horizontal concatenation has one row, for numeric and arbitrary element types."
    source := "base/abstractarray.jl:1703-1706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ScalarComprehensionContents, thm := some ``scalarComprehensionContents_proven },
  { id := "abstractarrays-source-typed-hcat-requires-type", juliaFile := "base/abstractarray.jl"
    juliaFns := ["typed_hcat@1759"]
    statement := "An array in the type position of typed_hcat raises ArgumentError."
    source := "base/abstractarray.jl:1759-1762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``TypedHcatRequiresType, thm := some ``typedHcatRequiresType_proven },
  { id := "abstractarrays-source-scalar-fill-order", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_hvncat_fill_loop!@2527", "hvncat_fill!@2556"]
    statement := "The interpreter path of scalar fill, when dimensions match, writes every tuple element once in tuple order."
    source := "base/abstractarray.jl:2527-2627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ScalarFillOrder, thm := some ``scalarFillOrder_proven },
  { id := "abstractarrays-source-numeric-concat-order", juliaFile := "base/abstractarray.jl"
    juliaFns := ["vcat@1708", "hcat@1714", "typed_vcat@1720", "typed_hcat@1726"]
    statement := "Numeric concatenation writes its scalar arguments exactly once in tuple order through the source scalar-fill chain."
    source := "base/abstractarray.jl:1708-1730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``NumericConcatOrder, thm := some ``numericConcatOrder_proven },
  { id := "abstractarrayspecs-linear-zero-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["getindex@1363", "_getindex@1392", "_to_linear_index@1400",
      "setindex!@1464", "_setindex!@1487", "get@1638"]
    statement := "For lawful ordinary singleton linear arrays, zero-coordinate reads and defaulted reads select index one, supported writes update that element, and missing canonical writers raise CanonicalIndexError."
    source := "base/abstractarray.jl:1363-1642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``OrdinaryLinearZero, thm := some ``ordinaryLinearZero_proven },
  { id := "abstractarrays-get-scattered-default", juliaFile := "base/abstractarray.jl"
    juliaFns := ["get!@1653"]
    statement := "For arbitrary requested index vectors, get! fills every out-of-bounds requested position with the default, including positions between two valid requested indices."
    source := "base/abstractarray.jl:1653-1660 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``ScatteredDefaultValues, thm := some ``scatteredDefaultValues_refuted
    issue := "none found (BugWriter searched JuliaLang/julia issues and pull requests)" },
  { id := "abstractarrays-source-index-list-default", juliaFile := "base/abstractarray.jl"
    juliaFns := ["get!@1664"]
    statement := "Under the external indcopy and bulk-memory operation contracts, indexed default reads overwrite every destination cell with its matching source value or the default."
    source := "base/abstractarray.jl:1664-1669 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IndexListDefaultContents, thm := some ``indexListDefaultContents_proven },
  { id := "abstractarrays-get-range-default", juliaFile := "base/abstractarray.jl"
    juliaFns := ["get!@1644", "get@1662"]
    statement := "Range reads on dense vectors return one element per requested index, using the default for every out-of-bounds position."
    source := "base/abstractarray.jl:1644-1662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``RangeDefaultValues, thm := some ``rangeDefaultValues_refuted
    issue := "none found (BugWriter searched JuliaLang/julia issues and pull requests)" },
  { id := "abstractarrays-get-range-default-ordinary", juliaFile := "base/abstractarray.jl"
    juliaFns := ["get!@1644", "get@1662"]
    statement := "Reading the entire ordinary dense vector through a range and a default returns the vector's values."
    source := "base/abstractarray.jl:1644-1662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``RangeDefaultOrdinaryValues, thm := some ``rangeDefaultOrdinaryValues_refuted
    issue := "none found (same scalar-to-range assignment defect as abstractarrays-get-range-default)" },
  { id := "abstractarrays-source-empty-promotion", juliaFile := "base/abstractarray.jl"
    juliaFns := ["promote_eltypeof@1682", "promote_eltype@1689"]
    statement := "Element-type promotion without any argument raises ErrorException."
    source := "base/abstractarray.jl:1682-1689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``EmptyPromotionRejected, thm := some ``emptyPromotionRejected_proven },
  { id := "abstractarrays-source-disjoint-segments", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_isdisjoint@1606", "_isdisjoint@1607", "_isdisjoint@1608",
      "_isdisjoint@1609", "_isdisjoint@1610", "_isdisjoint@1611",
      "_isdisjoint@1612", "_isdisjoint@1613", "_isdisjoint@1614"]
    statement := "The source overloads for UInt data-id tuples return true exactly when the tuples have no data segment in common."
    source := "base/abstractarray.jl:1606-1614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``DataidsDisjoint, thm := some ``dataidsDisjoint_proven },
  { id := "abstractarrays-source-mightalias-segments", juliaFile := "base/abstractarray.jl"
    juliaFns := ["mightalias@1603"]
    statement := "Alias detection succeeds exactly for nonempty mutable arrays whose data-id tuples intersect."
    source := "base/abstractarray.jl:1603-1614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``MightaliasSegments, thm := some ``mightaliasSegments_proven },
  { id := "abstractarrays-source-write-checks", juliaFile := "base/abstractarray.jl"
    juliaFns := ["setindex!@1464", "_setindex!@1487", "_setindex!@1499"]
    statement := "Canonical linear rejection and failed zero-coordinate bounds checks prevent conversion and element writes."
    source := "base/abstractarray.jl:1464-1504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``SourceWriteChecks, thm := some ``sourceWriteChecks_proven },
  { id := "abstractarrays-source-canonical-setindex", juliaFile := "base/abstractarray.jl"
    juliaFns := ["error_if_canonical_setindex@1475", "error_if_canonical_setindex@1477"]
    statement := "Missing canonical linear and Cartesian writers raise CanonicalIndexError for every array type and rank."
    source := "base/abstractarray.jl:1475-1478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CanonicalSetindexRejected, thm := some ``canonicalSetindexRejected_proven },
  { id := "abstractarrays-source-unsupported-setindex", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_setindex!@1482"]
    statement := "An unsupported assignment signature raises ErrorException for every value, input type, and index style."
    source := "base/abstractarray.jl:1482-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnsupportedSetindexRejected, thm := some ``unsupportedSetindexRejected_proven },
  { id := "abstractarrays-source-unalias-separation", juliaFile := "base/abstractarray.jl"
    juliaFns := ["unalias@1566"]
    statement := "With lawful alias detection and independent copying, unalias preserves every source value, removes sharing with the destination, and leaves nonaliasing sources unchanged."
    source := "base/abstractarray.jl:1566-1566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``SourceUnaliasSeparation, thm := some ``sourceUnaliasSeparation_proven },
  { id := "abstractarrays-source-unaliascopy-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["unaliascopy@1583"]
    statement := "For a lawful same-type copy operation, generic unaliascopy preserves the contents and independence of the copy."
    source := "base/abstractarray.jl:1583-1584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnaliascopyContents, thm := some ``unaliascopyContents_proven },
  { id := "abstractarrays-source-unaliascopy-mismatch", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_unaliascopy@1585"]
    statement := "A copy whose type differs from the source type is rejected with ArgumentError."
    source := "base/abstractarray.jl:1585-1592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnaliascopyMismatchRejected, thm := some ``unaliascopyMismatchRejected_proven },
  { id := "abstractarrayspecs-first-last", juliaFile := "base/abstractarray.jl"
    juliaFns := ["first@455", "last@530", "lastindex@429"]
    statement := "For arbitrary index spaces and element types, first and last select the ends of the element sequence, and empty arrays raise BoundsError."
    source := "base/abstractarray.jl:429-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``FirstLastElements, thm := some ``firstLastElements_proven },
  { id := "abstractarrays-source-fixed-one-based", juliaFile := "base/abstractarray.jl"
    juliaFns := ["has_offset_axes@114", "has_offset_axes@117", "has_offset_axes@118"]
    statement := "Empty argument lists, Colon, and dense Array storage never have offset axes."
    source := "base/abstractarray.jl:114-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``FixedOneBasedKinds, thm := some ``fixedOneBasedKinds_proven },
  { id := "abstractarrays-source-default-axes-shape", juliaFile := "base/abstractarray.jl"
    juliaFns := ["axes@100"]
    statement := "Default axes preserve the number of dimensions, start every axis at one, and give each axis its corresponding dimension length."
    source := "base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``DefaultAxesShape, thm := some ``defaultAxesShape_proven },
  { id := "abstractarrays-source-omitted-coordinate-positions", juliaFile := "base/abstractarray.jl"
    juliaFns := ["__to_subscript_indices@1426", "_remaining_size@1433", "_remaining_size@1434"]
    statement := "For checked indices with a remaining-axes decomposition, omitted-coordinate completion preserves all supplied coordinates and appends the first index of every omitted axis."
    source := "base/abstractarray.jl:1426-1430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``OmittedCoordinatePositions, thm := some ``omittedCoordinatePositions_proven },
  { id := "abstractarrays-source-indexing-checks", juliaFile := "base/abstractarray.jl"
    juliaFns := ["getindex@1363", "_getindex@1392", "_getindex@1404"]
    statement := "Canonical-method rejection and failed bounds checks stop indexing before conversion or element access."
    source := "base/abstractarray.jl:1363-1409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IndexingChecks, thm := some ``indexingChecks_proven },
  { id := "abstractarrays-source-canonical-getindex", juliaFile := "base/abstractarray.jl"
    juliaFns := ["error_if_canonical_getindex@1379", "error_if_canonical_getindex@1381"]
    statement := "Missing canonical linear and Cartesian readers raise CanonicalIndexError for every array type and rank."
    source := "base/abstractarray.jl:1379-1382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CanonicalGetindexRejected, thm := some ``canonicalGetindexRejected_proven },
  { id := "abstractarrays-source-unsupported-getindex", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_getindex@1386"]
    statement := "An unsupported indexing signature raises ErrorException for every input type and index style."
    source := "base/abstractarray.jl:1386-1387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``UnsupportedGetindexRejected, thm := some ``unsupportedGetindexRejected_proven },
  { id := "abstractarrays-source-linear-read-values", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_getindex@1392", "_getindex@1391", "_to_linear_index@1401"]
    statement := "With a lawful coordinate conversion, checked linear indexing reads the value at the reference linear position and rejects invalid coordinates."
    source := "base/abstractarray.jl:1391-1401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LinearReadValues, thm := some ``linearReadValues_proven },
  { id := "abstractarrayspecs-axis-starts", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_to_subscript_indices@1415"]
    statement := "Zero-index Cartesian coordinate conversion preserves rank and places each axis's first index at the matching coordinate, retaining its integer type."
    source := "base/abstractarray.jl:1415-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``AxisStartCoordinates, thm := some ``axisStartCoordinates_proven },
  { id := "abstractarrays-source-omitted-singletons", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds_indices@728"]
    statement := "With no explicit indices, bounds checking accepts exactly when every omitted axis has length one."
    source := "base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``OmittedSingletonBounds, thm := some ``omittedSingletonBounds_proven },
  { id := "abstractarrayspecs-copyto-iter", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(::AbstractArray, src)@941"]
    statement := "For any duplicate-free destination index space and any source element type, iterable copying writes precisely the source prefix, preserves every other heap cell, and raises ArgumentError if the destination is too short."
    source := "base/abstractarray.jl:941-951 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CopytoIterablePrefix, thm := some ``copytoIterablePrefix_proven },
  { id := "multidimcov-abstract-l941-copy-iterable", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(::AbstractArray, src)@941"]
    statement := "An iterable that fits overwrites the destination prefix in iteration order, returns the destination, and preserves all other cells; a short destination raises ArgumentError."
    source := "base/abstractarray.jl:941-951 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CopytoIterablePrefix, thm := some ``copytoIterablePrefix_proven },
  { id := "abstractarrayspecs-checkaxs", juliaFile := "base/abstractarray.jl"
    juliaFns := ["_checkaxs@1184"]
    statement := "Axis checking succeeds exactly for equal typed axes and raises DimensionMismatch for unequal axes."
    source := "base/abstractarray.jl:1184-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CheckAxesExact, thm := some ``checkAxesExact_proven },
  { id := "abstractarrays-source-copy-bang-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copy!(::AbstractArray, ::AbstractArray)@929"]
    statement := "With the verified iterable copy primitive, equal axes produce the source contents at every destination index and preserve outside memory; unequal axes raise ArgumentError."
    source := "base/abstractarray.jl:929-933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CopyBangArrayContents, thm := some ``copyBangArrayContents_proven },
  { id := "abstractarrays-source-copy-axes-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto_axcheck!@1186"]
    statement := "With the verified iterable copy primitive, equal axes copy every source value and preserve outside memory; unequal axes raise DimensionMismatch."
    source := "base/abstractarray.jl:1186-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CopyAxesContents, thm := some ``copyAxesContents_proven },
  { id := "abstractarrays-source-copyto-snapshot", juliaFile := "base/abstractarray.jl"
    juliaFns := ["copyto!(::IndexStyle, ::AbstractArray, ::IndexStyle, ::AbstractArray)@1082"]
    statement := "Using source-preserving unaliasing and the verified iterable copy primitive, overlapping views copy the source's entry-state values for every explicit style pair, without modifying other cells."
    source := "base/abstractarray.jl:1082-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CopytoAliasedSnapshot, thm := some ``copytoAliasedSnapshot_proven },
  { id := "abstractarrays-source-zero-shape-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["zero(::AbstractArray{<:Number})@1218", "zero(::AbstractArray{<:Union{Missing,Number}})@1219"]
    statement := "Under the allocation and fill interface contracts, both numeric zero-array methods preserve the input shape and fill every output element with the element-type zero."
    source := "base/abstractarray.jl:1218-1219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ZeroShapeContents, thm := some ``zeroShapeContents_proven },
  { id := "abstractarrays-source-isempty-contents", juliaFile := "base/abstractarray.jl"
    juliaFns := ["isempty(::AbstractArray)@1262"]
    statement := "For an array whose length counts its elements, isempty is true exactly when its element list is empty."
    source := "base/abstractarray.jl:1262-1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``IsEmptyContents, thm := some ``isemptyContents_proven },
  { id := "abstractarrays-source-size-conversion-error", juliaFile := "base/abstractarray.jl"
    juliaFns := ["size(::AbstractArray, dim)@42"]
    statement := "A dimension-conversion error is preserved even when the requested dimension would lie beyond the rank."
    source := "base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``SizeConversionFailure, thm := some ``sizeConversionFailure_proven },
  { id := "abstractarrays-source-first-empty-error", juliaFile := "base/abstractarray.jl"
    juliaFns := ["first(itr)@474"]
    statement := "The first-element operation raises ArgumentError for an iterator with no elements."
    source := "base/abstractarray.jl:474-478 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``FirstEmptyError, thm := some ``firstEmptyError_proven },
  { id := "abstractarrays-source-coordinate-failure", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkbounds_indices(::Type{Bool}, ::Tuple, ::Tuple)@722"]
    statement := "A failed earlier coordinate rejects Cartesian bounds checking without evaluating later coordinates."
    source := "base/abstractarray.jl:722-726 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``CoordinateFailureStops, thm := some ``coordinateFailureStops_proven },
  { id := "abstractarrays-size-axes-dim", juliaFile := "base/abstractarray.jl"
    juliaFns := ["size(::AbstractArray, d), axes(::AbstractArray, d)"]
    statement := "For a rank matching the stored dimensions, positive dimensions select their stored size and axis, trailing dimensions are singleton, and nonpositive dimensions raise BoundsError."
    source := "base/abstractarray.jl:42-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``SizeAxesDim, thm := some ``sizeAxesDim_proven },
  { id := "abstractarrays-size-large-dim", juliaFile := "base/abstractarray.jl"
    juliaFns := ["size(::AbstractArray, dim)"]
    statement := "Every positive Integer dimension beyond the rank has size one."
    source := "base/abstractarray.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``SizeAllIntegerDims, thm := some ``sizeAllIntegerDims_refuted
    issue := "none found (retained issue searches in the existing bug report)" },
  { id := "abstractarrays-require-one-based", juliaFile := "base/abstractarray.jl"
    juliaFns := ["has_offset_axes, require_one_based_indexing"]
    statement := "For Int-valued axes, requiring one-based indexing succeeds exactly when every axis starts at one; any offset axis raises ArgumentError."
    source := "base/abstractarray.jl:114-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``RequireOneBased, thm := some ``requireOneBased_proven },
  { id := "abstractarrays-require-one-based-large-axis", juliaFile := "base/abstractarray.jl"
    juliaFns := ["has_offset_axes(::AbstractVector), require_one_based_indexing"]
    statement := "For every integer-valued axis not starting at one, requiring one-based indexing raises ArgumentError."
    source := "base/abstractarray.jl:116-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``RequireOneBasedAllIntegerAxes, thm := some ``requireOneBasedAllIntegerAxes_refuted
    issue := "none found (retained issue searches in the existing bug report)" },
  { id := "abstractarrays-checkbounds-real-index", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex(::Type{Bool}, ::AbstractUnitRange, ::Real)"]
    statement := "A scalar passing bounds checking is a supported in-bounds index, including integer, Bool and rational scalar types."
    source := "base/abstractarray.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted, prop := ``CheckboundsAgreesGetindex, thm := some ``checkboundsAgreesGetindex_refuted
    issue := "none found (retained issue searches in the existing bug report)" },
  { id := "abstractarrays-checkindex-numeric-endpoints", juliaFile := "base/abstractarray.jl"
    juliaFns := ["checkindex(::Type{Bool}, ::AbstractUnitRange, ::Real)"]
    statement := "Real scalar bounds checking accepts exactly the numeric values between both axis endpoints, including mixed-type rational and Bool comparisons."
    source := "base/abstractarray.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``ScalarBoundsSound, thm := some ``scalarBoundsSound_proven }
]

end JuliaLean.Proofs.base.abstractarray
