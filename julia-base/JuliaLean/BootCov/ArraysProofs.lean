import JuliaLean.BootCov.Arrays
import JuliaLean.BootCov.IntConvProofs

/-!
Properties of the memory, array, `SimpleVector` and `Symbol` primitives.
-/

namespace JuliaLean.BootCov.Arrays

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv
open JuliaLean.ReinterpretArrays

/-- `checkbounds(Bool, A, i)` for an `Array` or `Memory` (`base/essentials.jl:385-388`) is
true exactly when `i` is in `1:length(A)`, for every `Int` index and every length. -/
def CheckboundsBoolCorrect : Prop :=
  ∀ len i : JInt64, 0 ≤ len.val →
    (checkboundsBool len i = true ↔ 1 ≤ i.val ∧ i.val ≤ len.val)

theorem i64_bounds (x : JInt64) : -(2:Int) ^ 63 ≤ x.val ∧ x.val < 2 ^ 63 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem wrapU64_nonneg (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 64) : wrapInt .u64 v = v := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega

theorem wrapU64_neg (v : Int) (h0 : -(2:Int) ^ 64 < v) (h1 : v < 0) :
    wrapInt .u64 v = v + 2 ^ 64 := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega

theorem wrapI64_small (v : Int) (h0 : -(2:Int) ^ 63 ≤ v) (h1 : v < 2 ^ 63) : wrapInt .i64 v = v := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega

theorem lit1_val : (JInt.lit .i64 1).val = 1 := rfl

theorem sub_lit1_val (i : JInt64) : (i - JInt.lit .i64 1).val = wrapInt .i64 (i.val - 1) := by
  show wrapInt .i64 (i.val - (JInt.lit .i64 1).val) = _
  rw [lit1_val]

theorem checkboundsBoolCorrect : CheckboundsBoolCorrect := by
  intro len i h0
  have hl := i64_bounds len
  have hi := i64_bounds i
  simp only [checkboundsBool, JInt.rem, JInt.wrap, sub_lit1_val, decide_eq_true_eq]
  by_cases hi0 : i.val = -(2:Int) ^ 63
  · have hw : wrapInt .i64 (i.val - 1) = 2 ^ 63 - 1 := by
      rw [hi0]; decide
    rw [hw, wrapU64_nonneg (2 ^ 63 - 1) (by omega) (by omega),
      wrapU64_nonneg len.val h0 (by omega)]
    omega
  · rw [wrapI64_small (i.val - 1) (by omega) (by omega)]
    rw [wrapU64_nonneg len.val h0 (by omega)]
    by_cases hp : 0 ≤ i.val - 1
    · rw [wrapU64_nonneg (i.val - 1) hp (by omega)]; omega
    · rw [wrapU64_neg (i.val - 1) (by omega) (by omega)]; omega

/-- `GenericMemory{...}(undef, m)` (`base/boot.jl:762-765`) allocates exactly `m`
undefined slots when `0 ≤ m ≤ maxLen` and throws `ArgumentError` otherwise, for any
runtime limit below `typemax(Int)`; the tuple and empty forms agree. -/
def MemoryCtorCorrect : Prop :=
  ∀ maxLen : Nat, maxLen < 2 ^ 63 → ∀ m : JInt64,
    (0 ≤ m.val ∧ m.val ≤ maxLen → memoryUndef maxLen m = .ok (List.replicate m.val.toNat none)) ∧
    (¬(0 ≤ m.val ∧ m.val ≤ maxLen) → ∃ msg, memoryUndef maxLen m = .error (.argument msg)) ∧
    memoryUndefTuple maxLen m = memoryUndef maxLen m ∧
    memoryEmpty maxLen = .ok []

theorem memoryCtorCorrect : MemoryCtorCorrect := by
  intro maxLen hmax m
  have hm := i64_bounds m
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro ⟨h1, h2⟩
    simp only [memoryUndef, memorynew, wrapU64_nonneg m.val h1 (by omega)]
    rw [if_neg (by omega)]
  · intro h
    refine ⟨"invalid GenericMemory size", ?_⟩
    simp only [memoryUndef, memorynew]
    rw [if_pos]
    by_cases h0 : 0 ≤ m.val
    · rw [wrapU64_nonneg m.val h0 (by omega)]; omega
    · rw [wrapU64_neg m.val (by omega) (by omega)]; omega
  · simp only [memoryEmpty, memoryUndef, memorynew]
    rfl

/-- `memoryref(mem, i)` (`base/boot.jl:769`) for an index of any built-in integer type
returns the reference to slot `i` exactly when `Int(i)` succeeds and `1 ≤ i ≤ length(mem)`,
throws `BoundsError` for other representable indices, and `memoryref(ref, i)`
(`base/boot.jl:770`) moves a valid reference by `i - 1` slots, negative shifts included,
throwing `BoundsError` exactly when the target is outside the memory. -/
def MemoryrefCorrect : Prop :=
  (∀ (mem : Mem) (i : JInt64), mem.length < 2 ^ 63 →
    (1 ≤ i.val ∧ i.val ≤ mem.length → memoryref2 mem (.int .i64 i) = .ok ⟨mem, (i.val - 1).toNat⟩) ∧
    (¬(1 ≤ i.val ∧ i.val ≤ mem.length) → memoryref2 mem (.int .i64 i) = .error .bounds)) ∧
  (∀ (r : MRef) (i : JInt64), r.mem.length < 2 ^ 63 → r.off ≤ r.mem.length →
    (0 ≤ r.off + i.val - 1 ∧ r.off + i.val - 1 < r.mem.length →
      memoryrefRef r (.int .i64 i) = .ok ⟨r.mem, (r.off + i.val - 1).toNat⟩) ∧
    (¬(0 ≤ r.off + i.val - 1 ∧ r.off + i.val - 1 < r.mem.length) →
      memoryrefRef r (.int .i64 i) = .error .bounds)) ∧
  (∀ mem, memoryref1 mem = ⟨mem, 0⟩ ∧ genericMemoryRef1 mem = memoryref1 mem) ∧
  (∀ mem i, genericMemoryRef2 mem i = memoryref2 mem i) ∧
  (∀ r i, genericMemoryRefRef r i = memoryrefRef r i)

theorem memoryrefCorrect : MemoryrefCorrect := by
  refine ⟨?_, ?_, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro mem i hlen
    have hi := i64_bounds i
    have hc : ctor .i64 (.int .i64 i) = .ok i := rfl
    simp only [memoryref2, hc, bind, Except.bind, memoryrefnewMem]
    constructor
    · intro h
      rw [wrapU64_nonneg (i.val - 1) (by omega) (by omega), if_neg (by omega)]
    · intro h
      rw [if_pos]
      by_cases hp : 0 ≤ i.val - 1
      · rw [wrapU64_nonneg (i.val - 1) hp (by omega)]; omega
      · rw [wrapU64_neg (i.val - 1) (by omega) (by omega)]; omega
  · intro r i hlen hoff
    have hi := i64_bounds i
    have hc : ctor .i64 (.int .i64 i) = .ok i := rfl
    simp only [memoryrefRef, hc, bind, Except.bind, memoryrefnewRef]
    by_cases hp : 0 ≤ i.val - 1
    · rw [wrapU64_nonneg (i.val - 1) hp (by omega)]
      rw [wrapU64_nonneg ((r.off : Int) + (i.val - 1)) (by omega) (by omega)]
      rw [show (r.off : Int) + (i.val - 1) = r.off + i.val - 1 by omega]
      constructor
      · intro h; rw [if_neg (by omega)]
      · intro h; rw [if_pos (by omega)]
    · rw [wrapU64_neg (i.val - 1) (by omega) (by omega)]
      by_cases hq : 0 ≤ (r.off : Int) + i.val - 1
      · have : wrapInt .u64 (↑r.off + (i.val - 1 + 2 ^ 64)) = ↑r.off + i.val - 1 := by
          simp [wrapInt, IntTy.signed, IntTy.bits]; omega
        rw [this]
        constructor
        · intro h; rw [if_neg (by omega)]
        · intro h; rw [if_pos (by omega)]
      · have : wrapInt .u64 (↑r.off + (i.val - 1 + 2 ^ 64)) = ↑r.off + i.val - 1 + 2 ^ 64 := by
          simp [wrapInt, IntTy.signed, IntTy.bits]; omega
        rw [this]
        constructor
        · intro h; omega
        · intro h; rw [if_pos (by omega)]

/-- Exact product of `Int` dimensions. -/
def prodVals : List JInt64 → Int
  | [] => 1
  | x :: xs => x.val * prodVals xs

theorem uleTypemax_false {x : JInt64} (h : uleTypemax x = false) :
    0 ≤ x.val ∧ x.val < IntTy.max .i64 := by
  simp only [uleTypemax, decide_eq_false_iff_not, not_or] at h
  have := x.property.2
  have h1 := h.1
  have h2 := h.2
  constructor <;> omega

theorem loop_sound : ∀ (d : List JInt64) (a : JInt64) (ovflw neg zero : Bool) (P : Int),
    (zero = true → a.val = 0 ∧ P = 0) → (ovflw = false → a.val = P) →
    (checkedMulDimsLoop d a ovflw neg zero).2 = false →
    (checkedMulDimsLoop d a ovflw neg zero).1.val = P * prodVals d ∧ neg = false ∧
      ∀ x ∈ d, uleTypemax x = false := by
  intro d
  induction d with
  | nil =>
    intro a ovflw neg zero P hz ho h
    simp only [checkedMulDimsLoop, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      Bool.not_eq_false'] at h
    refine ⟨?_, h.1, by simp⟩
    simp only [checkedMulDimsLoop, prodVals, Int.mul_one]
    rcases h.2 with h2 | h2
    · exact ho h2
    · rw [(hz h2).1, (hz h2).2]
  | cons di d ih =>
    intro a ovflw neg zero P hz ho h
    simp only [checkedMulDimsLoop] at h ⊢
    have hmul : (checkedSmul a di).1.val = wrapInt .i64 (a.val * di.val) := rfl
    have hov : (checkedSmul a di).2 = false →
        IntTy.min .i64 ≤ a.val * di.val ∧ a.val * di.val ≤ IntTy.max .i64 := by
      intro h'
      simp only [checkedSmul, decide_eq_false_iff_not, Decidable.not_not] at h'
      exact h'
    have r := ih (checkedSmul a di).1 (ovflw || (checkedSmul a di).2) (neg || uleTypemax di)
      (zero || decide (di.val = 0)) (P * di.val) ?_ ?_ h
    · simp only [Bool.or_eq_false_iff] at r
      refine ⟨?_, r.2.1.1, ?_⟩
      · rw [r.1, prodVals, Int.mul_assoc]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · rw [hx]; exact r.2.1.2
        · exact r.2.2 x hx
    · intro hz'
      rw [hmul]
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hz'
      rcases hz' with hz' | hz'
      · obtain ⟨ha, hP⟩ := hz hz'
        rw [ha, hP]; simp [wrapInt, IntTy.signed, IntTy.bits]
      · rw [hz']; simp [wrapInt, IntTy.signed, IntTy.bits]
    · intro ho'
      simp only [Bool.or_eq_false_iff] at ho'
      rw [hmul, wrapInt_of_inRange .i64 _ (hov ho'.2), ho ho'.1]

theorem checkedDims_ge2 (d : List JInt64) (hd : 2 ≤ d.length) :
    checkedDims d = if (checkedMulDims d).2 then .error (.argumentError "invalid Array dimensions")
      else .ok (checkedMulDims d).1 := by
  match d, hd with
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _, _ => rfl

theorem checkedMulDims_two (m n : JInt64) :
    checkedMulDims [m, n] = ((checkedSmul m n).1,
      (checkedSmul m n).2 || uleTypemax m || uleTypemax n) := rfl

theorem checkedMulDims_three (m n o : JInt64) (rest : List JInt64) :
    checkedMulDims (m :: n :: o :: rest) =
      checkedMulDimsLoop (n :: o :: rest) m false (uleTypemax m) false := rfl

/-- `Core.checked_dims(d...)` (`base/boot.jl:811-818`, through `_checked_mul_dims` at
lines 782-809) never returns a wrong length: with two or more dimensions it either throws
`ArgumentError` or returns the exact product of the dimensions, all of which are then
nonnegative and below `typemax(Int)`; `checked_dims()` is 1 and `checked_dims(m)` is `m`. -/
def CheckedDimsSound : Prop :=
  (checkedDims [] = .ok (JInt.lit .i64 1)) ∧
  (∀ m, checkedDims [m] = .ok m) ∧
  (∀ d : List JInt64, 2 ≤ d.length →
    (∀ p, checkedDims d = .ok p → p.val = prodVals d ∧
        ∀ x ∈ d, 0 ≤ x.val ∧ x.val < IntTy.max .i64) ∧
    (∀ e, checkedDims d = .error e → e = .argumentError "invalid Array dimensions"))

theorem checkedDimsSound : CheckedDimsSound := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro d hd
  rw [checkedDims_ge2 d hd]
  refine ⟨?_, ?_⟩
  · intro p hp
    split at hp
    · cases hp
    · rename_i hb
      cases hp
      match d, hd with
      | [m, n], _ =>
        rw [checkedMulDims_two] at hb ⊢
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hb
        have hm := uleTypemax_false hb.1.2
        have hn := uleTypemax_false hb.2
        have hov : IntTy.min .i64 ≤ m.val * n.val ∧ m.val * n.val ≤ IntTy.max .i64 := by
          have h1 := hb.1.1
          simp only [checkedSmul, decide_eq_false_iff_not, Decidable.not_not] at h1
          exact h1
        refine ⟨?_, ?_⟩
        · show wrapInt .i64 (m.val * n.val) = _
          rw [wrapInt_of_inRange .i64 _ hov]
          simp [prodVals]
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx <;> rw [hx] <;> assumption
      | m :: n :: o :: rest, _ =>
        rw [checkedMulDims_three] at hb ⊢
        have r := loop_sound (n :: o :: rest) m false (uleTypemax m) false m.val
          (by simp) (fun _ => rfl) (by simpa using hb)
        refine ⟨by rw [r.1]; simp only [prodVals], ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · rw [hx]; exact uleTypemax_false r.2.1
        · exact uleTypemax_false (r.2.2 x (by simpa using hx))
  · intro e he
    split at he <;> cases he <;> rfl

/-- The `Array{T,N}(undef, dims...)` constructors (`base/boot.jl:821-847`, every
dimension count, the tuple forms and the `Array{T}` and `Vector{T}()` forms) either throw
`ArgumentError` or build an array with exactly the requested dimensions whose memory has
exactly the product of the dimensions as length. -/
def ArrayCtorShape : Prop :=
  ∀ maxLen : Nat, maxLen < 2 ^ 63 → ∀ d : List JInt64,
    (∀ A, arrayUndef maxLen d = .ok A →
      A.dims = d ∧ (A.ref.mem.length : Int) = prodVals d ∧ A.ref.off = 0 ∧ ∀ x ∈ d, 0 ≤ x.val) ∧
    (∀ e, arrayUndef maxLen d = .error e → ∃ msg, e = .argument msg) ∧
    arrayUndefTuple maxLen d = arrayUndef maxLen d ∧ arrayTUndef maxLen d = arrayUndef maxLen d ∧
    arrayTUndefTuple maxLen d = arrayUndef maxLen d ∧
    vectorEmpty maxLen = arrayUndef maxLen [JInt.lit .i64 0]

theorem memoryUndef_ok {maxLen : Nat} (h : maxLen < 2 ^ 63) {m : JInt64} {mem : Mem}
    (hm : memoryUndef maxLen m = .ok mem) : (mem.length : Int) = m.val ∧ 0 ≤ m.val := by
  have c := memoryCtorCorrect maxLen h m
  by_cases hr : 0 ≤ m.val ∧ m.val ≤ maxLen
  · rw [c.1 hr] at hm
    cases hm
    simp
    omega
  · obtain ⟨msg, hmsg⟩ := c.2.1 hr
    rw [hmsg] at hm
    cases hm

theorem memoryUndef_err {maxLen : Nat} (h : maxLen < 2 ^ 63) {m : JInt64} {e : Exc}
    (hm : memoryUndef maxLen m = .error e) : ∃ msg, e = .argument msg := by
  have c := memoryCtorCorrect maxLen h m
  by_cases hr : 0 ≤ m.val ∧ m.val ≤ maxLen
  · rw [c.1 hr] at hm; cases hm
  · obtain ⟨msg, hmsg⟩ := c.2.1 hr
    rw [hmsg] at hm; cases hm; exact ⟨msg, rfl⟩

theorem viaDims_ok {maxLen : Nat} (h : maxLen < 2 ^ 63) {d : List JInt64} (hd : 2 ≤ d.length)
    {A : Arr} (hA : arrayN maxLen d = .ok A) :
    A.dims = d ∧ (A.ref.mem.length : Int) = prodVals d ∧ A.ref.off = 0 ∧ ∀ x ∈ d, 0 ≤ x.val := by
  have s := checkedDimsSound.2.2 d hd
  unfold arrayN at hA
  cases hc : checkedDims d with
  | error e =>
    rw [hc] at hA
    have := s.2 e hc
    subst this
    cases hA
  | ok p =>
    rw [hc] at hA
    simp only [ofJl, bind, Except.bind, newAsMemoryref] at hA
    cases hm : memoryUndef maxLen p with
    | error e => rw [hm] at hA; cases hA
    | ok mem =>
      rw [hm] at hA
      cases hA
      have hp := s.1 p hc
      have hl := memoryUndef_ok h hm
      exact ⟨rfl, by simp [memoryref1, memoryrefnew1]; rw [hl.1, hp.1], rfl,
        fun x hx => (hp.2 x hx).1⟩

theorem viaDims_err {maxLen : Nat} (h : maxLen < 2 ^ 63) {d : List JInt64} (hd : 2 ≤ d.length)
    {e : Exc} (hA : arrayN maxLen d = .error e) : ∃ msg, e = .argument msg := by
  have s := checkedDimsSound.2.2 d hd
  unfold arrayN at hA
  cases hc : checkedDims d with
  | error e' =>
    rw [hc] at hA
    have := s.2 e' hc
    subst this
    simp only [ofJl, bind, Except.bind] at hA
    cases hA
    exact ⟨_, rfl⟩
  | ok p =>
    rw [hc] at hA
    simp only [ofJl, bind, Except.bind, newAsMemoryref] at hA
    cases hm : memoryUndef maxLen p with
    | error e' => rw [hm] at hA; cases hA; exact memoryUndef_err h hm
    | ok mem => rw [hm] at hA; cases hA

theorem arrayCtorShape : ArrayCtorShape := by
  intro maxLen h d
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro A hA
    match d with
    | [] =>
      simp only [arrayUndef, arrayN, checkedDims, ofJl, bind, Except.bind, newAsMemoryref] at hA
      cases hm : memoryUndef maxLen (JInt.lit .i64 1) with
      | error e => rw [hm] at hA; cases hA
      | ok mem =>
        rw [hm] at hA; cases hA
        have hl := memoryUndef_ok h hm
        refine ⟨rfl, ?_, rfl, by simp⟩
        simp only [memoryref1, memoryrefnew1, prodVals]
        rw [hl.1]; rfl
    | [m] =>
      simp only [arrayUndef, array1, bind, Except.bind] at hA
      cases hm : memoryUndef maxLen m with
      | error e => rw [hm] at hA; cases hA
      | ok mem =>
        rw [hm] at hA; cases hA
        have hl := memoryUndef_ok h hm
        refine ⟨rfl, ?_, rfl, ?_⟩
        · simp [memoryref1, memoryrefnew1, prodVals, hl.1]
        · simp [hl.2]
    | [m, n] => exact viaDims_ok h (by simp) hA
    | m :: n :: o :: rest =>
      cases rest with
      | nil => exact viaDims_ok h (by simp) hA
      | cons q rest => exact viaDims_ok h (by simp) hA
  · intro e hA
    match d with
    | [] =>
      simp only [arrayUndef, arrayN, checkedDims, ofJl, bind, Except.bind, newAsMemoryref] at hA
      cases hm : memoryUndef maxLen (JInt.lit .i64 1) with
      | error e' => rw [hm] at hA; cases hA; exact memoryUndef_err h hm
      | ok mem => rw [hm] at hA; cases hA
    | [m] =>
      simp only [arrayUndef, array1, bind, Except.bind] at hA
      cases hm : memoryUndef maxLen m with
      | error e' => rw [hm] at hA; cases hA; exact memoryUndef_err h hm
      | ok mem => rw [hm] at hA; cases hA
    | [m, n] => exact viaDims_err h (by simp) hA
    | m :: n :: o :: rest =>
      cases rest with
      | nil => exact viaDims_err h (by simp) hA
      | cons q rest => exact viaDims_err h (by simp) hA

/-- Element access on `Memory`, `MemoryRef` and `Array` (`base/essentials.jl:395-406`,
1063-1082): `A[i]` throws `BoundsError` outside `1:length(A)`, otherwise reads the slot
(`UndefRefError` for an undefined one); `A[i] = x` then `A[i]` returns `x`;
`setindex!` returns its array; the `MemoryRef{T}` method converts first; and the access
order is `:monotonic` exactly for atomic memory. -/
def AccessSemantics : Prop :=
  (∀ (mem : Mem) (i : JInt64), mem.length < 2 ^ 63 →
    (¬(1 ≤ i.val ∧ i.val ≤ mem.length) → getindexMem mem i = .error .bounds) ∧
    (1 ≤ i.val ∧ i.val ≤ mem.length →
      getindexMem mem i = memoryrefget ⟨mem, (i.val - 1).toNat⟩ ∧
      ∀ x, (setindexMem mem x i >>= fun m => getindexMem m i) = .ok x)) ∧
  (∀ (len : JInt64) (a : Arr) (i : JInt64), 0 ≤ len.val →
    (¬(1 ≤ i.val ∧ i.val ≤ len.val) → getindexArr len a i = .error .bounds) ∧
    (1 ≤ i.val ∧ i.val ≤ len.val →
      getindexArr len a i = memoryrefget ⟨a.ref.mem, a.ref.off + (i.val - 1).toNat⟩)) ∧
  (∀ (len : JInt64) (a : Arr) (x : JVal) (i : JInt64), 0 ≤ len.val →
    ¬(1 ≤ i.val ∧ i.val ≤ len.val) → setindexArr len a x i = .error .bounds) ∧
  (∀ r, getindexRef r = memoryrefget r) ∧
  (∀ (conv : JVal → R JVal) r x e, conv x = .error e → setindexRefT conv r x = .error e) ∧
  (∀ (conv : JVal → R JVal) r x y, conv x = .ok y → setindexRefT conv r x = setindexRefAny r y) ∧
  defaultAccessOrder true = "monotonic" ∧ defaultAccessOrder false = "not_atomic" ∧
  (∀ mem : Mem, sizeMem mem = [mem.length]) ∧
  (∀ a : Arr, sizeArr a = a.dims ∧ ∀ m rest, a.dims = m :: rest → lengthVec a = .ok m)

theorem lit_len_val {n : Nat} (hl : n < 2 ^ 63) : (JInt.lit .i64 (n : Int)).val = n :=
  wrapI64_small _ (by omega) (by omega)

theorem getindexMem_oob {mem : Mem} {i : JInt64} (hl : mem.length < 2 ^ 63)
    (h : ¬(1 ≤ i.val ∧ i.val ≤ mem.length)) : getindexMem mem i = .error .bounds := by
  have hv : (JInt.lit .i64 mem.length).val = mem.length := lit_len_val hl
  have c := checkboundsBoolCorrect (JInt.lit .i64 mem.length) i (by rw [hv]; omega)
  rw [hv] at c
  have hf : checkboundsBool (JInt.lit .i64 mem.length) i = false := by
    cases hc : checkboundsBool (JInt.lit .i64 mem.length) i
    · rfl
    · exact absurd (c.1 hc) h
  unfold getindexMem checkbounds
  rw [hf]
  rfl

theorem getindexMem_in {mem : Mem} {i : JInt64} (hl : mem.length < 2 ^ 63)
    (h : 1 ≤ i.val ∧ i.val ≤ mem.length) :
    getindexMem mem i = memoryrefget ⟨mem, (i.val - 1).toNat⟩ := by
  have hv : (JInt.lit .i64 mem.length).val = mem.length := lit_len_val hl
  have c := checkboundsBoolCorrect (JInt.lit .i64 mem.length) i (by rw [hv]; omega)
  rw [hv] at c
  unfold getindexMem checkbounds
  rw [c.2 h]
  rfl

theorem setindexMem_in {mem : Mem} {i : JInt64} (x : JVal) (hl : mem.length < 2 ^ 63)
    (h : 1 ≤ i.val ∧ i.val ≤ mem.length) :
    setindexMem mem x i = .ok (mem.set (i.val - 1).toNat (some x)) := by
  have hv : (JInt.lit .i64 mem.length).val = mem.length := lit_len_val hl
  have c := checkboundsBoolCorrect (JInt.lit .i64 mem.length) i (by rw [hv]; omega)
  rw [hv] at c
  have hk : (i.val - 1).toNat < mem.length := by omega
  have e1 : checkbounds (checkboundsBool (JInt.lit .i64 mem.length)) i = .ok () := by
    unfold checkbounds; rw [c.2 h]; rfl
  have e2 : memoryrefset ⟨mem, (i.val - 1).toNat⟩ x =
      .ok ⟨mem.set (i.val - 1).toNat (some x), (i.val - 1).toNat⟩ := by
    unfold memoryrefset; exact if_pos hk
  unfold setindexMem
  rw [e1, e2]
  rfl

theorem accessSemantics : AccessSemantics := by
  refine ⟨?_, ?_, ?_, fun _ => rfl, ?_, ?_, rfl, rfl, fun _ => rfl, ?_⟩
  · intro mem i hl
    refine ⟨getindexMem_oob hl, fun h => ⟨getindexMem_in hl h, ?_⟩⟩
    intro x
    have hk : (i.val - 1).toNat < mem.length := by omega
    rw [setindexMem_in x hl h]
    rw [show ∀ (m : Mem) (f : Mem → R JVal), (Except.ok m >>= f) = f m from fun _ _ => rfl]
    have hl' : (mem.set (i.val - 1).toNat (some x)).length < 2 ^ 63 := by simp; exact hl
    rw [getindexMem_in hl' (by simp; omega)]
    generalize (i.val - 1).toNat = k at hk ⊢
    simp [memoryrefget, hk]
  · intro len a i h0
    have c := checkboundsBoolCorrect len i h0
    constructor
    · intro h
      have hf : checkboundsBool len i = false := by
        cases hc : checkboundsBool len i
        · rfl
        · exact absurd (c.1 hc) h
      simp [getindexArr, checkbounds, hf, bind, Except.bind]
    · intro h
      simp [getindexArr, checkbounds, c.2 h, bind, Except.bind]
  · intro len a x i h0 h
    have c := checkboundsBoolCorrect len i h0
    have hf : checkboundsBool len i = false := by
      cases hc : checkboundsBool len i
      · rfl
      · exact absurd (c.1 hc) h
    simp [setindexArr, checkbounds, hf, bind, Except.bind]
  · intro conv r x e h
    simp [setindexRefT, h, bind, Except.bind]
  · intro conv r x y h
    simp [setindexRefT, setindexRefAny, h, bind, Except.bind]
  · intro a
    refine ⟨rfl, fun m rest h => ?_⟩
    simp [lengthVec, h]

/-- `SimpleVector` indexing and iteration (`base/essentials.jl:1086-1109`): `v[i]` throws
`BoundsError` outside `1:length(v)`; `iterate(v, i)` yields `(v[i], i + 1)` for
`1 ≤ i ≤ length(v)` and `nothing` past the end; `firstindex`, `lastindex`, `keys`,
`axes`, `isempty` and `eltype` describe `1:length(v)`; `axes(v, d)` is `1:1` for `d > 1`;
`map` applies `f` to every element in order; `v[I]` collects `v[i]` for `i` in `I`;
equal svecs compare equal and svecs of different lengths compare unequal. -/
def SvecSemantics : Prop :=
  (∀ (v : SVec) (i : Int), (i < 1 ∨ i > v.length) → svecRef v i = .error .bounds) ∧
  (∀ (v : SVec) (i : Nat) (h : i < v.length), svecRef v (i + 1) = .ok v[i]) ∧
  (∀ (v : SVec) (i : Nat) (h : i < v.length),
    svecIterate v (i + 1) = .ok (some (v[i], (i : Int) + 2))) ∧
  (∀ (v : SVec) (i : Int), (v.length : Int) < i → svecIterate v i = .ok none) ∧
  (∀ v : SVec, svecFirstindex v = 1 ∧ svecLastindex v = v.length ∧ svecKeys v = v.length ∧
    svecAxes v = [v.length] ∧ (svecIsempty v = true ↔ v = []) ∧ svecEltype = "Any" ∧
    svecAxesD v 1 = .ok v.length ∧ (∀ d, d > 1 → svecAxesD v d = .ok 1) ∧
    (∀ d, d < 1 → svecAxesD v d = .error .bounds)) ∧
  (∀ {β : Type} (f : Option JVal → β) (v : SVec), svecMap f v = v.map f) ∧
  (∀ (v : SVec) (I : List Nat), (∀ i ∈ I, i < v.length) →
    svecGetindexArray v (I.map fun (i : Nat) => (i : Int) + 1) = .ok (I.map fun (i : Nat) => v[i]?.join)) ∧
  (∀ (eq : Option JVal → Option JVal → Bool) (v1 v2 : SVec),
    v1.length ≠ v2.length → svecEq eq v1 v2 = false) ∧
  (∀ (eq : Option JVal → Option JVal → Bool) (v : SVec), (∀ x, eq x x = true) →
    svecEq eq v v = true) ∧
  (∀ a, svecUnsafeConvert a = a + 8)

theorem svecRef_in (v : SVec) (i : Nat) (h : i < v.length) : svecRef v (i + 1) = .ok v[i] := by
  simp only [svecRef]
  rw [if_neg (by omega)]
  simp [h]

theorem svecGetindexArray_in (v : SVec) : ∀ I : List Nat, (∀ i ∈ I, i < v.length) →
    svecGetindexArray v (I.map fun (i : Nat) => (i : Int) + 1) = .ok (I.map fun (i : Nat) => v[i]?.join) := by
  intro I
  induction I with
  | nil => intro _; rfl
  | cons i I ih =>
    intro h
    have hi := h i (by simp)
    simp only [List.map_cons, svecGetindexArray]
    rw [svecRef_in v i hi, ih (fun j hj => h j (by simp [hj]))]
    simp [bind, Except.bind, pure, Except.pure, hi]

theorem svecEqLoop_refl (eq : Option JVal → Option JVal → Bool) (h : ∀ x, eq x x = true) :
    ∀ v : SVec, svecEqLoop eq v v = true := by
  intro v
  induction v with
  | nil => rfl
  | cons a v ih => simp [svecEqLoop, h, ih]

theorem svecSemantics : SvecSemantics := by
  refine ⟨?_, svecRef_in, ?_, ?_, ?_, fun _ _ => rfl, svecGetindexArray_in, ?_, ?_, fun _ => rfl⟩
  · intro v i h
    simp [svecRef, h]
  · intro v i h
    simp only [svecIterate]
    split
    · rename_i hc; simp only [svecLength] at hc; omega
    · rw [svecRef_in v i h]
      show Except.ok (some (v[i], (i : Int) + 1 + 1)) = Except.ok (some (v[i], (i : Int) + 2))
      rw [show (i : Int) + 1 + 1 = i + 2 by omega]
  · intro v i h
    simp [svecIterate, svecLength, h]
  · intro v
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · simp [svecIsempty, svecLength]
    · simp [svecAxesD, svecLength]
    · intro d hd
      simp only [svecAxesD]
      rw [if_neg (by omega)]
    · intro d hd
      simp only [svecAxesD]
      rw [if_pos (by omega), if_neg (by omega)]
  · intro eq v1 v2 h
    simp [svecEq, svecLength, h]
  · intro eq v h
    simp [svecEq, svecLength, svecEqLoop_refl eq h]

/-- `isassigned(v::SimpleVector, i)` returns `true` exactly when `i` is in bounds and slot
`i` holds a value, as the `isassigned` docstring promises ("Return `false` if the index is
out of bounds, or has an undefined reference", `base/essentials.jl:1116-1117`). -/
def SvecIsassignedCorrect : Prop :=
  ∀ (v : SVec) (i : Int),
    svecIsassigned v i = true ↔ (1 ≤ i ∧ i ≤ v.length ∧ ∃ x, v[(i - 1).toNat]? = some (some x))

theorem svecIsassignedCorrect_refuted : ¬ SvecIsassignedCorrect := by
  intro h
  have := (h [none] 1).1 (by decide)
  obtain ⟨_, _, x, hx⟩ := this
  simp at hx

/-- The `Symbol` constructors (`base/boot.jl:858-873`): `Symbol(s::String)` and
`Symbol(a::Vector{UInt8})` build the symbol with exactly the given bytes (for a vector,
the bytes visible through its reference), throw `ArgumentError` when a byte is `0x00`,
and `Symbol(s::Symbol)` is `s`. -/
def SymbolCtors : Prop :=
  (∀ b : List Nat, 0 ∉ b → symbolOfString b = .ok b) ∧
  (∀ b : List Nat, 0 ∈ b → ∃ msg, symbolOfString b = .error (.argument msg)) ∧
  (∀ (a : List Nat) (off len : Nat), symbolOfVector a off len = symbolOfString ((a.drop off).take len)) ∧
  (∀ s, symbolOfSymbol s = s)

theorem symbolCtors : SymbolCtors := by
  refine ⟨?_, ?_, ?_, fun _ => rfl⟩
  · intro b h
    simp [symbolOfString, symbolN, h]
  · intro b h
    exact ⟨"Symbol name may not contain \\0", by simp [symbolOfString, symbolN, h]⟩
  · intro a off len
    simp only [symbolOfVector, symbolOfString]
    rw [List.take_of_length_le (Nat.le_refl _)]

/-- The converting `Array` constructors (`base/boot.jl:849-854`) call the full constructor
with the element type and dimensionality the method signature fixes: the source element
type `S` for `Array{T,N} where T` and for `Array(A)` (with `T = S`), the requested `T` for
`Array{T}(A)` and `AbstractArray{T}(A)`, and always the source dimensionality `N`. -/
def ArrayConversions : Prop :=
  ∀ {A B : Type} (conv : String → Nat → A → B) (elt : String) (N : Nat) (x : A),
    arrayFromAbstract conv elt N x = conv elt N x ∧ arrayOf conv elt N x = conv elt N x ∧
    arrayTOf conv elt N x = conv elt N x ∧ abstractArrayTOf conv elt N x = conv elt N x

theorem arrayConversions : ArrayConversions := fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

end JuliaLean.BootCov.Arrays
